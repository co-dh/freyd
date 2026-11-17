# Incremental port of qlean's C kernels to Rust — design

Scope: data structures, signatures, build, order and gates. No function body is designed here; a cheaper model
fills bodies against the tests. Sources read: `/home/dh/repo/qlean/c` at 369841b, `doc/c2rust.md`,
`doc/rust-vs-c-kernels.md` §2–§7, the trial crate `/data/tmp/c2rust/wt/rust` (read only). Every number below is
tagged (m) measured today, (t) measured by the c2rust trial, or (e) estimated.

## 1. Decisions

- Migration unit: one C function (or one `static inline` family), not one file.
- Crate: `qlean/rust`, name `qrs`, `staticlib`, `#![no_std]` + `alloc`, `panic = "abort"`, no dependencies.
- Exported symbols: every Rust export is `qrs_<c name>`; nothing else leaves the object (`objcopy -G`).
- Replacing a twin. A `static` function in a `.c`: body deleted, call sites call `qrs_*` (git keeps the C).
  A `static inline` in a header: body replaced by the call to `qrs_*` (git keeps the C), because
  `tools/coc/coc.c` links `rust/qrs.o` and builds with `-DQLEAN_RS` like lake does.
- Lean boundary, phase 1: stays in C. The 266 (m) `LEAN_EXPORT` entries keep unpacking `lean_object*` into
  pointer + length and allocating results. Rust never sees `lean.h`, so there is no object-layout mirror.
- Lean boundary, phase 2 (after the last kernel): one hand-written `lean.rs` (unsafe). `lean-sys` 0.0.9 is not
  used: its docs name no Lean version and I could not verify it against Lean 4.28.
- OS shell (open, mmap, dlopen, pread, the pthread pool): stays in C in phase 1; Rust gets bytes, returns bytes.
- Rust calling not-yet-ported C: only through exported C symbols declared in `c.rs`. A `static inline` C helper
  has no symbol, so its Rust port must land first — hence the leaf-first order.
- `unsafe` is allowed only in `rt.rs`, `ffi.rs`, `c.rs`, `pod.rs`, `simd.rs`; every other module starts with
  `#![forbid(unsafe_code)]`, so the compiler is the gate.
- Toolchain: stable, pinned `1.93.1` in `rust/rust-toolchain.toml` (installed here; the design needs >= 1.89).

Why `no_std` + `alloc` and not `std` (probe in `/data/tmp/qrs-probe`, stable 1.93.1, all (m)):

| build                                              | text of the object | `ldd` of a C exe linking it      |
|----------------------------------------------------|--------------------|----------------------------------|
| `std`                                              | 863 KB             | adds `libgcc_s.so.1`             |
| `no_std` + `alloc`                                 | 235 KB             | adds `libgcc_s.so.1`             |
| same + `_Unwind_Resume` stub + `objcopy -G 'qrs_*'` | 235 KB             | libc only; `-shared` also links  |

The last row keeps gate 1 of `rel-native-design.md` (libc/libm/libpthread only). The stub is local after
`objcopy`, so it cannot interpose the Lean runtime's unwinder. Undefined symbols left: `abort aligned_alloc bcmp
free memcmp memcpy memmove memset strlen write`.

## 2. Rust facts checked online (2026-11-15)

| claim                                                              | since | status                          |
|--------------------------------------------------------------------|-------|---------------------------------|
| `#[target_feature]` on safe fns (target_feature 1.1)               | 1.86  | verified [1]                    |
| intrinsics safe to call inside a fn that enables their feature     | 1.87  | verified [2], and (m) on 1.93.1 |
| AVX-512 intrinsics and target features stable                      | 1.89  | verified [3]; no list of names  |
| `std::simd` (portable SIMD)                                        | —     | nightly only, verified [4]      |

- [1]: a safe `#[target_feature]` fn is called without `unsafe` only from a fn enabling the same features; from
  any other fn the call needs `unsafe` (after `is_x86_feature_detected!` or a `cfg`).
- [2] says "most": intrinsics that take pointers (load, store, gather) stay unsafe. (m): `_mm512_add_epi64` and
  `_mm512_reduce_add_epi64` compile with no `unsafe` in an `avx512f` fn; `_mm512_loadu_si512` needs it.
- [4]: feature `portable_simd`, tracking issue #86656, read on the 1.100.0-nightly docs of 2026-11-09.

Not verified: the current stable version number (the docs show nightly 1.100.0, so stable is about 1.98); whether
each of the 143 intrinsic uses in qlean is stable — those of `res_unpack` and `res_unpack_add` (VBMI2
`_mm512_shrdv_epi{16,32,64}`, VBMI `_mm512_permutex2var_epi8`, the masked loads and stores) are, (m) by task S's
`simd::v` skeleton on 1.93.1; the rest is found out by the task that first names them; whether `-C target-cpu=native` alone makes intrinsics safe in a fn with no attribute (the design does not
rely on it: every SIMD fn carries the attribute). Consequence: no `std::simd`, no nightly. The c2rust output's
nightly-2023-04-15 is dropped with the c2rust output.

[1] https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/ [2] https://blog.rust-lang.org/2025/05/15/Rust-1.87.0/
[3] https://blog.rust-lang.org/2025/08/07/Rust-1.89.0/ [4] https://doc.rust-lang.org/std/simd/index.html

## 3. Types

`coc` (`c/coc.h:103-120`) has 12 pointers by my count (the handover says 13): 7 into the metadata buffer, `pack`,
3 into the patch list, `fdelta`. It splits into three borrowed views. `'a` is always the duration of one extern
call: a `@&` ByteArray argument, or the mapping while `qlean_own_map` validates it. Nothing is `'static`.

```rust
pub const BLK: usize = 1024;

// why.rs — replaces snprintf(why, cap, ...); NUL-terminates, truncates, never fails
pub struct Why<'a> { buf: &'a mut [u8], at: usize }
impl<'a> Why<'a> { pub fn new(buf: &'a mut [u8]) -> Self; pub fn say(&mut self, a: core::fmt::Arguments) }

// pod.rs — the one checked reinterpretation; None when misaligned or len % size_of::<T>() != 0
pub trait Pod: Copy {}                       // impl for u8 i8 u16 i16 u32 i32 u64 i64 f32 f64
pub fn cast<T: Pod>(b: &[u8]) -> Option<&[T]>;
pub fn cast_mut<T: Pod>(b: &mut [u8]) -> Option<&mut [T]>;

// layout.rs — exc_layout / for_layout / alp_layout (coc.h:199, 209, 1518) as one function
pub enum Tail { None, Frames, Exps }          // for_layout frm=0, frm=1, alp_layout
pub struct ExcLayout { pub raw: usize, pub off: usize, pub pos: usize, pub tail: usize, pub size: usize }
pub fn exc_layout(nblk: usize, nexc: usize, esz: usize, tail: Tail) -> Option<ExcLayout>;  // None = overflow
pub fn exc_ok(t: &[u8], nblk: usize, nexc: u64, esz: usize, part: i32, tail: Tail, why: &mut Why) -> bool;

// bits.rs, ids.rs — coc.h:425, 429; ids.h:19, 25, 40; own.c:231, 245
pub fn width_for(range: u64) -> u8;           pub fn lane_width(w: u8) -> u8;
pub fn id_width(nd: usize) -> u32;            pub fn ids_bytes(n: usize, w: u32) -> usize;
pub fn id_at(p: &[u8], w: u32, i: usize) -> usize;
pub fn ids_max(p: &[u8], w: u32, n: usize) -> usize;

// coc.rs — the read views
#[derive(Clone, Copy)]
pub struct Meta<'a> {                         // coc_meta_view: the 33*mblk + 16 byte buffer
    pub base: &'a [i64], pub maxv: &'a [i64], pub off: &'a [u64], pub bsum: &'a [i64], pub width: &'a [u8],
    pub sumnul: i64, pub sumn: u64,           // one slot each, read by value
    pub n: usize, pub nblk: usize, pub mblk: usize,   // slices are mblk long; nblk <= mblk is what n reaches
}
#[derive(Clone, Copy)]
pub struct Exc<'a> { pub off: &'a [u32], pub pos: &'a [u16], pub raw: &'a [u8], pub esz: usize } // nexc = pos.len()
#[derive(Clone, Copy)]
pub struct Coc<'a> { pub meta: Meta<'a>, pub pack: &'a [u8], pub exc: Option<Exc<'a>>, pub fdelta: Option<&'a [u64]> }
impl<'a> Meta<'a> {
    pub fn new(m: &'a [u8], n: usize) -> Option<Self>;     // coc.h:133; None = misaligned buffer
    pub fn res_end(&self) -> usize;                        // coc.h:222
    pub fn grid(&self, n: usize) -> bool;                  // coc.h:233
}
impl<'a> Coc<'a> {
    pub fn attach(meta: Meta<'a>, pack: &'a [u8]) -> Option<Self>;   // coc.h:245; None where C aborts
    pub fn std(&self, n: usize) -> bool;                   // coc.h:234
    pub fn blocks(&self, b0: usize, b1: usize) -> Coc<'a>; // coc.h:155; off stays absolute into pack
    pub fn frame(&self, b: usize) -> u64;                  // coc.h:217
}

// own.rs — own.c:263 and the header checks of own.c:366-394
pub const OWN_MAXPARTS: usize = 3;
#[repr(C)] pub struct OwnHead { pub n: u64, pub hdr: usize, pub np: usize,
                                pub off: [usize; OWN_MAXPARTS], pub len: [usize; OWN_MAXPARTS], pub kind: u8 }
pub fn head(m: &[u8], why: &mut Why) -> Option<OwnHead>;   // m = the whole mapping
pub fn check(kind: u8, n: u64, part: &[&[u8]], why: &mut Why) -> bool;

// zip.rs — zip.c:141 and the pure parts of zopen (zip.c:185-250)
pub fn zq(b: &[u8], dst: &mut [u8]) -> Result<(), &'static core::ffi::CStr>;  // dst = 8 zero bytes + `want`
#[repr(C)] pub struct ZTrailer { pub ulen: u64, pub cend: u64, pub l: u64 }
pub fn trailer(hdr: &[u8; 32], size: u64, nblk: u64, hat: u64, why: &mut Why) -> Option<ZTrailer>;
pub fn table(ent: &[u8], at: &mut [u64], algo: &mut [u32]) -> usize;          // returns maxc; at[0] = 8

// unpack.rs (safe) and simd.rs (unsafe allowed) — coc.h:547, 598, 646; reduce.c:261 
pub fn res_unpack_scalar(p: &[u8], w: u8, nb: usize, out: &mut [u8]);         // out.len() == BLK * 8
pub fn u8_sum(p: &[u8]) -> i64;                                                // simd.rs, dispatches by cfg
pub fn res_unpack(p: &[u8], w: u8, nb: usize, out: &mut [u8]);                 // simd.rs
pub fn res_unpack_add(p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8], tw: u32) -> bool;  // simd.rs
```

Mirrors (`ffi.rs`, `#[repr(C)]`, each with a `const _: () = assert!(size_of::<..>() == N)` and a matching
`_Static_assert` on `sizeof` and every `offsetof` in `c/rs.h`, written in `rust/cbindgen.toml`'s `trailer`):

| mirror  | of                      | bytes (e) | needed while                     | retired when                    |
|---------|-------------------------|-----------|----------------------------------|---------------------------------|
| `CCoc`  | `coc`, coc.h:103        | 144       | C hands a `coc *` to a `qrs_*`   | no C file includes `coc.h`      |
| `CSrc`  | `coc_src`, coc.h:2010   | 40        | the source callback has a C side | the encoder and `zat` are Rust  |
| `CPass` | `qlean_pass`, pass.h:74 | 72        | Rust workers run on the C pool   | `pass.h`'s pool is ported, last |

`OwnHead` and `ZTrailer` are new `#[repr(C)]` structs defined on the Rust side; they live while `own.c` and `zip.c`
keep the OS shell (until phase 2). `CSrc` and `CPass` are declared by the first task that needs them, after 10.

`unsafe fn CCoc::view<'a>(&self) -> Coc<'a>` is the only place raw `coc` pointers become slices. The writer side
(`coc_enc`, coc.h:2038, 17 mutable pointers and three `lean_object*`) is NOT designed here: it needs a `CocMut`
with per-block `split_at_mut` for the parallel passes, and no task below touches it.

No duplication during the transition: `tools/coc` links `rust/qrs.o`, so a ported `static inline` helper
keeps no C copy. Exception (§5): a per-element inline (`id_at`, `key_at`, `width_for`) keeps its C body until
its last C caller is ported.

### Types added for the Rel-first order (§5) — missing above, fixed by task S

The block above has no type for a sort key, a group table, the C pool or the key window; tasks B1–B11 need them.
Task S (§7) changed the spellings marked `S:` below; they are now fixed like the rest (landed on `rust-rel-S`).

```rust
// key.rs — key_at (sort.c:132) with the kind switch hoisted by monomorphisation (SK_EACH, sort.c:1697)
pub const SK_BIT: u8 = 0; /* … */ pub const SK_KEY: u8 = 8; pub const SK_WIN: u8 = 9;  // S: coc.h:347, sort.c:59, 65
pub trait Keys: Sync { fn at(&mut self, i: usize) -> u64; fn fork(&self) -> Self where Self: Sized; }
// impls: Bit(&[u8]) U8(&[u8]) I16(&[u16]) I32(&[u32]) I64(&[u64]) F32(&[u32]) F64(&[u64]) Key(&[u64]), Copy, fork = *self;
// Kwin (kwin.rs) directly, no `Win` wrapper (S)
pub trait Pass { type Out; fn run<K: Keys>(self, k: K, n: usize) -> Self::Out; }
pub fn each<P: Pass>(kind: u8, p: &[u8], n: usize, pass: P) -> Option<P::Out>;   // None = unknown kind, misaligned
pub fn rank32(b: u32) -> u64;                 pub fn rank64(b: u64) -> u64;      // sort.c:100, 106
pub fn range(kind: u8, p: &[u8], n: usize) -> Option<(u64, u64)>;                // range_of, sort.c:1969
pub fn bytes(kind: u8, n: usize) -> Option<usize>;   // S, written: a dense payload's length, what the shims cut `p` at

// group.rs — dedup's groupIds arm only (sort.c:2025, gid != NULL, cnt == NULL) and ids_run (sort.c:2006)
// S: borrowed (Cow) so qrs_group_fill hands C's tables in without a copy; `number` builds owned ones
pub enum Table<'a> { Direct { tab: Cow<'a, [u32]>, mn: u64 },
                     Hashed { slot: Cow<'a, [usize]>, gkey: Cow<'a, [u64]>, sh: u32 } }
pub fn number(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, first: &mut [usize])
    -> Option<(usize, Table<'static>)>;
pub fn fill(kind: u8, p: &[u8], n: usize, t: &Table, lane: u32, gid: &mut [u8]) -> bool;
pub fn group_ids(kind: u8, p: &[u8], n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize])
    -> Option<usize>;                                                            // ng; gid at max(8, id_width(ng))
pub fn group_ids_win(kind: u8, c: Coc, n: usize, mn: u64, mx: u64, gid: &mut [u8], first: &mut [usize])
    -> usize;                                     // S: B11's entry, the same passes over a Kwin

// ids.rs — ids.h:271, sort.c:3283-3415, IDS_PACK (ids.h:167) with VAL = the byte lane itself
pub fn firsts(ids: &[u8], n: usize, w: u32, nd: usize, slot: &mut [usize], first: &mut [usize]) -> usize;
pub fn map(ids: &[u8], n: usize, w: u32, nd: usize, slot: &[usize], wo: u32, out: &mut [u8]);
pub fn pack_in_place(g: &mut [u8], w: u32, n: usize);

// own.rs — qlean_own_write (own.c:147-179) without the file: the header bytes and each part's offset
pub fn write_head(code: u8, attr: u8, kind: u8, count: u64, nl: usize, len: &[usize],
                  head: &mut [u8], off: &mut [usize], why: &mut Why) -> Option<usize>;   // header length

// c.rs — the C pool (pass.h:415) behind one safe call; `out` is cut at the slices qlean_slice (pass.h:243) makes
pub fn run_map<F: Fn(usize, usize, &mut [u8]) + Sync>(out: &mut [u8], units: usize, unit: usize, cost: u32,
                                                      wide: usize, f: &F) -> u32;   // S: written and unit-tested

// coc.rs, pod.rs, kwin.rs — coc.h:277, 293, 819, 2633; sort.c:212-334
impl<'a> Coc<'a> { pub fn exc(&self, j: usize) -> i64; pub fn blk_nexc(&self, b: usize) -> usize;
                   pub fn decode_blk<T: Lane>(&self, b: usize, nb: usize, out: &mut [T]); }
pub trait Lane: Pod { fn wrap(v: u64) -> Self; }   // S, written: u8 i16 i32 i64, `as` (COC_T's truncating cast)
pub fn lanes<'b>(p: &'b [u8], w: &mut u8, nb: usize, buf: &'b mut [u8]) -> &'b [u8];
pub struct Kwin<'a> { kind: u8, c: Coc<'a>, lo: usize, len: usize, key: Box<[u64; 2 * BLK]> }
impl<'a> Kwin<'a> { pub fn new(kind: u8, c: Coc<'a>) -> Self; }                   // kwin_init
pub fn key_flip(kind: u8) -> u64;                                                  // sort.c:212
pub fn keys_blk(kind: u8, c: &Coc, b: usize, k: &mut [u64]);                       // keys_blk_foR, cnt = k.len()
pub fn range(kind: u8, c: &Coc) -> (u64, u64);                                     // range_foR (S: named here)

// simd.rs, mod v — one #[target_feature(enable = "avx512f,avx512bw,avx512dq,avx512vbmi,avx512vbmi2")] fn per
// RES_VUNPACK instance; every intrinsic the C instance uses is named in it and compiles on 1.93.1 (S: none unstable)
pub fn unpack16_u8 / unpack16 / unpack32 / unpack64(p: &[u8], w: u8, nb: usize, out: &mut [u8]);   // res_unpack
pub fn add16_u8 / add16_i16 / add16_i32 / add16_i64 / add32_i32 / add32_i64 / add64_i64
       (p: &[u8], w: u8, nb: usize, base: u64, out: &mut [u8]);                                     // res_unpack_add
```

`CPass` (the table above) is declared in S, not "after 10": `ffi.rs`, 72 bytes, the field `r#priv` (C `priv`);
cbindgen emits it by `[export] include`, and since `coc.h` includes `rs.h` before `pass.h` exists, its offset checks
are the trailer macro `QRS_ASSERT_CPASS`, expanded in `sort.c` beside `qlean_run_c`. The `SK_*` constants are in
cbindgen's `exclude` (they would redefine `coc.h`'s enum). `res_vcmp`'s three `RES_VUNPACK` instances are not
skeletoned: no Rel entry reaches them. No `Cocf`/`CSrc`/`CocMut` here: the ALP window
(`kwin.f`, sort.c:2618) and the encoder are column (a) and get their types in task A0.

## 4. Build and linking

How qlean builds today (`lakefile.lean:119-176`): `kernelObjWith` compiles each `c/<name>.c` with
`-O3 -march=native -fPIC -fno-trapping-math` into `.lake/build/c/<name>.o`; `extern_lib qleankernel` archives 15
objects into `libqleankernel.a`; `precompileModules := true` makes lake also link `libqleankernel.so`.

- `rust/build.sh`: `cargo build --release --lib` with `RUSTFLAGS="-C target-cpu=native -D warnings"` and
  `CARGO_TARGET_DIR=/data/tmp/qrs/target/<worktree dir name>` (one per worktree: parallel tasks sharing one
  would queue on cargo's lock and rebuild each other's crate); then `cbindgen` regenerates `c/rs.h` (written
  only when it changed); then `ld -r` with one `-u <sym>` per `qrs_*` symbol that `nm -g --defined-only` finds
  in the archive (derived, so adding a function edits no script); then `objcopy --wildcard -G 'qrs_*'` into
  `rust/qrs.o`. Any failing step stops the script (`set -eu`), a missing `cbindgen` included.
- lakefile (landed in task 0, the first choice, not the fallback): `target qrs.o` runs `build.sh` through
  `buildFileAfterDep`, keyed by `inputDir rust/src` plus `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml`,
  `cbindgen.toml`, `build.sh`; `qrs.o` is in the `extern_lib` list. `kernelObjWith` reads the headers only after
  `qrs.o` is built, so no C object compiles against an `rs.h` older than `ffi.rs`. `passFlags` and
  `recurrenceFlags` gain `-DQLEAN_RS`.
- `c/rs.h`: GENERATED by cbindgen 0.29.4 (`cargo install --locked cbindgen`, a CLI in `~/.cargo/bin`, not a
  build-dependency, so the crate keeps no dependencies) from the `qrs_*` shims and the `#[repr(C)]` types they
  name; `rt` and `c` are `/// cbindgen:ignore`. Never edited by hand; a changed `rs.h` is committed with the
  `ffi.rs` change that made it. Included by `coc.h` under `#ifdef QLEAN_RS`, after the `coc` typedef its
  mirror asserts name.
- `tools/coc/coc.c`: `sh rust/build.sh && gcc ... -DQLEAN_RS ... tools/coc/coc.c rust/qrs.o -lm`. From the first
  task whose kept code calls `run_map` (B2, B4), `qrs.o` needs `qlean_run_c` (sort.c), which this line does not
  link: that task adds it to the tool's link line or reports the failure.
- C calls Rust by plain call. Rust calls C only through `c.rs` (`extern "C"` declarations); the first use will be
  a non-`static` wrapper `qlean_run_c` around `qlean_run` (pass.h:415), not needed before task 10.
- Each relink rebuilds all 547 precompiled-module jobs, about 5 min (t). A task costs two such builds.

## 5. Order (the C that Rel reaches first, leaf first inside it)

Re-planned 2026-11-15 on his instruction "work on the c code used by rel_language first, not generic q". The
scope is `doc/rel-c-kernels.md`: column (b), the native ABI (`qlean_own_write`, `qlean_sort_group_ids`,
`qlean_sort_id_groups`, 817 lines), then column (a), all of `LeetQ.Run` (77 entries, 5924 lines). Nothing outside
(a) ∪ (b) is ported until both are done. After S, `sort.c` lines from 56 on are 9 further down (S's `qlean_run_c`
at sort.c:56-64: `range_of` 1969 → 1978); the anchors below are the d428fd5 numbers. Line anchors are `rust-port-0`
at d428fd5 (`/data/tmp/qrs/wt0`): `coc.h`
is master + 6 from line 124 on, `sort.c`, `ids.h`, `pass.h` are master's.

State of the earlier order (briefs kept at the end of §7):

| old # | port                         | state              | on Rel's path                                        |
|-------|------------------------------|--------------------|------------------------------------------------------|
| 0     | scaffold                     | landed             | —                                                    |
| 1     | `exc_ok`, `exc_layout`       | landed             | `exc_ok` no; the three layouts are (a), see A1       |
| 2     | `width_for`…`ids_max`        | landed             | `id_width`, `ids_bytes`, `id_at`, `width_for`: (b)   |
| 3     | own header check             | landed             | no (`own_map`)                                       |
| 6     | `zq`                         | landed             | no (`zip.c`)                                         |
| 4     | `Meta`, `own_check`          | deferred           | `own_check` no; `Meta` moves to A1                   |
| 5     | `Coc`, `CCoc`, `coc_std`     | superseded         | views → B8; `coc_std`, `attach` → A1                 |
| 7     | zip trailer and table        | stopped, deferred  | no                                                   |
| 8     | `over_u8_sum`                | superseded by A12  | (a)                                                  |
| 9, 10 | `res_unpack*`                | superseded by B8–B10 | (b), reached only through `SK_WIN`                 |

Deferred, not scheduled: Rust `exc_ok` maps a float column at 1.38× C (`rust/BENCH.md`); it is off Rel's path.

What "reached" means for (b). The call graph is static. Reading the three entries, 263 of the 817 lines cannot
run from them (read off the code, not measured; B11's reach proof is the measurement):

- `qlean_sort_group_ids` clamps through `sk_avail` (coc.h:377), which exits on any kind past the seven of
  `Scan.lean`, so `SK_WIN` never arrives: the key window and the block decode behind it (`keys_blk_foR`, `kwin_*`,
  `range_foR`, `key_flip`, `coc_lanes`, `res_unpack*`, `decode_blk_i64`, `coc_exc`…; 186 lines, both AVX functions)
  first run from `qlean_sort_group_ids_foR`, a column (a) entry.
- `keys_blk_alp` and `cocf_load_*` (42 lines) need `kwin.f`, set only at sort.c:2618 by an entry outside (a).
- `part_dedup` (35 lines) needs `!gid || cnt` (sort.c:2049); `groupIds` passes `gid` and no `cnt`. The same test
  keeps `dedup`'s bitmap, estimate and bucket arms (`distinct`, `group`) off every Rel entry of both columns.

So (b) is ordered live part first (S, B1–B7: 554 lines), then the `SK_WIN` part (B8–B11), which is also the
first block of column (a). Not ported in B, with the reason:

| C                                                          | lines | stays C because                      |
|------------------------------------------------------------|-------|--------------------------------------|
| the pool: `qlean_run`, `qlean_threads`… (pass.h:219-458)   | 113   | OS shell (§1): pthread, futex        |
| `own_errno`, `own_write_all`, `own_replace` (own.c:78-126) | 40    | OS shell (§1): open, write, rename   |
| `dedup`'s `!gid` and `cnt` arms, `part_dedup`              | ~80   | generic q; no Rel entry reaches them |
| `mk_pair`, `ids_alloc`, `ids_avail`, the two entries       | ~30   | Lean boundary (§1, phase 1)          |
| `keys_blk_alp`, `cocf_load_*`                              | 42    | moved to A5 (ALP read)               |

Rust replaces about 510 of the 817 lines (e). A hot per-element inline (`id_at`, `key_at`, `width_for`,
`lane_width`, `group_find`) keeps its C body while a C caller remains: a call per element would fail the
benchmark gate. Its Rust twin is unit-tested against vectors dumped from the C, and the C body goes with its
last caller.

Column (b):

| #   | port                                                   | from (d428fd5)                         | after   |
|-----|--------------------------------------------------------|----------------------------------------|---------|
| S   | scaffold: types of §3's added block, shims, bench rows | —                                      | —       |
| B1  | `ids_firsts`                                           | ids.h:271-317                          | S       |
| B2  | `ids_map_run`, the map of `id_groups_of`               | sort.c:3270-3315, 3400-3414            | S       |
| B3  | `rank32/64`, dense `key_at`, `range_of`                | sort.c:100-144, 1697-1719, 1969-1975   | S       |
| B4  | `ids_run`, `group_find`                                | sort.c:1981-2023, 2103-2111            | S       |
| B5  | `dedup`'s `groupIds` arm, `group_probe/prefetch`       | sort.c:1655-1671, 1752-1778, 2025-2118 | B3, B4  |
| B6  | `IDS_PACK` in place                                    | ids.h:117-175; sort.c:2254             | B5      |
| B7  | `qlean_own_write`'s header                             | own.c:135-137, 147-179                 | S       |
| B8  | views `coc_frame/exc/blk_nexc`, `res_unpack_scalar`    | coc.h:222, 277-295, 534-568            | S       |
| B9  | `res_unpack`, `coc_lanes`                              | coc.h:570-619, 819-824                 | B8      |
| B10 | `res_unpack_add`, `decode_blk_{u8,i16,i32,i64}`        | coc.h:652-695, 2633-2654               | B9      |
| B11 | `key_flip`, `keys_blk_foR`, `kwin_*`, `range_foR`      | sort.c:212-334                         | B5, B10 |

Column (a), after B11 is merged, by file, leaf first. A0 is a scaffold (signatures, the encoder's `CocMut`,
`Cocf`, the symbol views, one bench row per task) and is the only step that may change a type. Spans are
function definitions of `/data/tmp/relc-audit/graph.out`; templates and macros come on top.

| #   | file          | port                                                            | lines (d428fd5)       | span |
|-----|---------------|-----------------------------------------------------------------|-----------------------|------|
| A0  | —             | scaffold for A1–A46                                             | —                     | —    |
| A1  | coc.h         | meta, views `bit_at`…`width_exc`, `coc_get*`, `coc_load_run`    | 104-303, 2131-2277    | 190  |
| A2  | coc.h         | `res_get/put`, `res_pack_scalar`, `res_lanes*`, `res_pack`      | 447-518, 743-763      | 60   |
| A3  | coc.h         | `res_sum8`, `res_sum`, `coc_sum*`, `coc_sums_*`                 | 858-995               | 95   |
| A4  | coc.h         | `coc_prd/any/all`, `res_min_nonzero`, `coc_min/max`             | 1002-1103             | 70   |
| A5  | coc.h         | `alp_offsets`, `cocf_*`, `alp_fin_blk`, `keys_blk_alp`          | 1532-1629, 1899       | 90   |
| A6  | coc.h         | `coc_blk_allnul`, `coc_shift_ok`, `coc_shift`                   | 1372-1463             | 32   |
| A7  | coc.h         | FoR encode: `pack_block`, `encode_meta_blk`, `frame_pick`       | 2405-2533             | 78   |
| A8  | coc.h         | `encode_meta_exc_blk`, `pack_exc_blk`, whole-column `decode`    | 2540-2595, 2656       | 60   |
| A9  | coc.h         | ALP encode: `bits/dec/dat`, `alp_meta_blk`…`alp_pack_blk`       | 2677-2908             | 120  |
| A10 | ids.h         | `id_put`, `ids_bitcopy`, `ids_unpack16`, `ids_runs`             | 56-355                | 75   |
| A11 | sym.h         | `off_at`…`sym_packs`                                            | 28-156                | 69   |
| A12 | reduce.c      | `over_u8_sum`, `qlean_over_bytes`                               | 261-298               | 37   |
| A13 | reduce.c      | `seg_at`, `br_load/store`, `bit_rows_pass`, `bit_rows_over`     | 488-619               | 59   |
| A14 | scan.c        | `scan_fill`, `scan_any_null`, `scan_run`, `qlean_scan`          | 309-505               | 91   |
| A15 | coc.c         | `qlean_coc_{decode,block_start,over,shift}`, `coc_decode_run_*` | 592-837               | 95   |
| A16 | coc.c         | encoder source and plan: `cocf_view`, `src_*`, `coc_enc_*`      | 95-316                | 175  |
| A17 | coc.c         | `qlean_coc_encode_src`, `coc_narrow`, `fill_*`, `move_*`        | 318-655               | 205  |
| A18 | coc.c         | ALP entries: `alp_decode_run`, `qlean_alp_*`, `alp_gather_run`  | 1015-1149             | 55   |
| A19 | sort.c        | `keys_of`, `keys_range`, `ksrc_blk`, `ksrc_range`               | 176-392               | 48   |
| A20 | sort.c        | `grade_runs/count/perm`, `sk_digit`, `grade_radix`              | 410-721               | 66   |
| A21 | sort.c        | `grade_bits`, `narrow_*_run`, `grade_narrow`                    | 727-842               | 66   |
| A22 | sort.c        | `ascending*`, `invert`, `order_*`, the grade and ranks entries  | 887-1109              | 150  |
| A23 | sort.c        | `group_bound`, `pair_*`, `ids_keys`, the two pair entries       | 1624, 2273-2378, 3432 | 96   |
| A24 | sort.c        | `rank_slices`, `group_sizes`, `id_longs`                        | 2455-2523             | 48   |
| A25 | sort.c        | `sym_whole`…`sym_ranks`, `qlean_sort_grade_syms`                | 2798-2960             | 104  |
| A26 | sort.c        | `id_rank`, `grade_ids`, `syms_at`, `distinct/intern_syms`       | 3044-3488             | 105  |
| A27 | sort.c        | `guid_words`, `qlean_sort_grade_guid`                           | 3517-3552             | 35   |
| A28 | search.c      | operands: `opnd_*`, `coc_srange`, `sext`, `kind_*`              | 53-420, 818           | 80   |
| A29 | search.c      | the probe-table template (7 element types × 7 functions)        | 190-399               | 49+  |
| A30 | search.c      | `find_run`, `member_run`, `search`, the four vec entries        | 829-965               | 75   |
| A31 | search.c      | `find_bit`, `member_bits`, `where_bits`, `find_sym_scalar`      | 974-1272              | 110  |
| A32 | search.c      | `bin_*`, `kcur_*`, `qlean_search_bin`                           | 1497-1716             | 150  |
| A33 | search.c      | `run_starts*`                                                   | 731-740, 2004-2099    | 72   |
| A34 | structural.c  | bit and row helpers, `trailer_ok`, `res_bytes`, `unpack_run`    | 56-374                | 99   |
| A35 | structural.c  | `concat_foR_move`, `shift_fill`…`cat_ints`                      | 270-610               | 85   |
| A36 | structural.c  | `alp_view`…`concat_foR`, `qlean_structural_concat_{foR,alp}`    | 655-856               | 145  |
| A37 | structural.c  | `gather*` dense, FoR, bits; `all_below`                         | 926-1146              | 116  |
| A38 | structural.c  | `expand`, `rows_of`, `gather_syms`, `gather_ids*`, `cycle_ids`  | 1278-1608             | 170  |
| A39 | structural.c  | `cycle_bits`, `concat*`, `enum_ids*`, `ids_place`, `concat_ids` | 1792-2008             | 165  |
| A40 | structural.c  | `symview_at`, `symtab_*`, `sd_*`, `symdict_{hold,probe,drop}`   | 2046-2192             | 110  |
| A41 | structural.c  | `symdict_concat`, `take_ids0`, `til`, `scatter`                 | 2203-2384, 3005-3030  | 197  |
| A42 | elementwise.c | scalar helpers `ew_width`…`ew_fdiv_magic`                       | 140-299               | 75   |
| A43 | elementwise.c | `ew_val*`, `ew_cmp*`, `ew_eq_ids*` (two AVX functions)          | 482-1092              | 126  |
| A44 | elementwise.c | `ew_bit*`, `ew_mon_run`, `ew_floor_run`                         | 1569-1813             | 91   |
| A45 | elementwise.c | `ew_cast*`, `ew_tick_run`, the date helpers                     | 1843-1981             | 92   |
| A46 | elementwise.c | `ew_widen*`, `ew_stage_*`, `ew_chain*`, pass.h's chain runner   | 2007-2394; 511-561    | 330  |

A41 and A46 are over the 60-call size as they stand; A0 splits each in two when it fixes their signatures.
`qlean_stop` (env.c:23, 5 lines) is Lean glue and stays. Not planned at all: `handle.c`, `interp.c`, `time.c`,
`zip.c`, the rest of `own.c`, and every entry outside the 77.

Decisions this order takes by default, his to overturn:

- The pool. P (default): `qlean_run` and the futex/pthread pool stay C as OS shell, Rust reaches them through
  `c::run_map`. Q: port the pool too, which needs a seventh `unsafe` module for pthread and futex.
- The `SK_WIN` part of (b). R (default): B8–B11 right after the live part, before column (a), because the
  static table counts them in (b). T: move them behind A1, since no native entry can run them.
- Column (a)'s scaffold. U (default): one opus step A0 after B11, so opus tasks are S then A0, never two at once.
  V: split A0 per file (seven smaller opus steps, one before each file's tasks).

## 6. Gates

Per task, in this order; a red gate stops the task and is reported, never worked around.

| gate         | pass                                                                                     |
|--------------|------------------------------------------------------------------------------------------|
| crate        | exit 0, no warning                                                                       |
| unit         | exit 0                                                                                   |
| build        | exit 0; the ~1,800 `#guard`s run inside it (`Kernel.SortTest` OOM predates the port (t)) |
| differential | last line `all suites passed` (17 suites, the q corpus among them; needs q's licence)    |
| symbols      | only `qrs_*` defined; undefined = the 10 libc names of §1, plus `qlean_run_c` once B2/B4 call `run_map` |
| unsafe       | prints exactly `c.rs ffi.rs lib.rs pod.rs rt.rs simd.rs`                                 |
| rel          | both exes exit 0, `nm -u` no `lean_`, `cmp` of `out/key`, `out/val` with the base is 0   |
| benchmark    | min of 3 Rust medians / min of 3 C medians <= the task's threshold                       |

Commands (`W` = the task's worktree, `T` = `/data/tmp/qrs/<task>`, `CAP` = `/home/dh/repo/freyd/scripts/cap`):

```
crate         env CAP_MEM_MB=8000 CAP sh W/rust/build.sh > T/cargo.log 2>&1
unit          cd W/rust; env CAP_MEM_MB=8000 RUSTFLAGS="-C target-cpu=native" CAP cargo test > T/unit.log 2>&1;
              env CAP_MEM_MB=8000 CAP cargo test > T/unit-plain.log 2>&1   # native = what build.sh ships
build         cd W; env CAP_MEM_MB=24576 CAP lake build QLean qlean-test > T/lake.log 2>&1
              (Kernel.SortTest needs more than 13000 MB of address space; at 24576 it builds)
differential  W/.lake/build/bin/qlean-test > T/test.log 2>&1   (outside the sandbox: qipc spawns q on a socket)
symbols       nm -g --defined-only W/rust/qrs.o; nm -u W/rust/qrs.o
unsafe        grep -L 'forbid(unsafe_code)' W/rust/src/*.rs
rel           link /data/tmp/qrs/rel/{c,g}.c by the cc line in W/rust/BENCH.md, run both in T with a fresh out/,
              cmp T/out/key T/out/val against /data/tmp/qrs/rel/base/run/out   # every task, whatever it touches
benchmark     the task's bench binary and its baseline in /data/tmp/qrs/base/, alternately R C R C R C,
              each under env CAP_MEM_MB=8000 CAP, command lines from W/rust/BENCH.md
```

Thresholds (e, chosen here): 1.10 for tasks 1–7 (I/O bound; the trial saw run-to-run spread above 1.5x (t)), 1.05
for tasks 8–10. Go/no-go for the whole port, read after task 10: ratio <= 1.05 on `bench-coc` and `bench-kernel`,
and lines in the five unsafe modules <= 20% of `wc -l rust/src/*.rs` (e). Never
`|| true` a gate, never pipe one through `tail` (the pipe hides the exit status).

## 7. Task briefs

Common protocol, part of every brief:

- Loop speed (the user's choice A, 2026-11-15). While editing: `cargo test` plus a differential harness under
  `/data/tmp/qrs/<task>/` that links the original C function and the Rust one and compares them on a few thousand
  random inputs, seconds per round. Once at the end of the task: lake build, qlean-test, the Rel gate, `reach.sh`
  on the bench row (hit count only, no timing). The benchmark runs only on `rust-port-0` after a wave is merged,
  only the rows that wave touched, 3 alternating runs; a task brief's "benchmark" item below is deferred to that run.

- Worktree: `git -C /home/dh/repo/qlean worktree add --lock /data/tmp/qrs/wt-<task> -b rs-<task> rust-port-0`
  (outside the sandbox), then `cp -a /data/tmp/qrs/wt0/.lake /data/tmp/qrs/wt-<task>/.lake`. Work only there.
  Never touch `/data/tmp/c2rust/wt`. Commit on `rs-<task>`; do not push; do not merge.
- Fill bodies only. The signatures of §3, `ffi.rs` and every `struct` are fixed by the scaffold step (0, S, A0);
  `c/rs.h` is generated from them and is never edited. If a body cannot be written against them, stop and report
  the exact obstacle; do not change a type or add one. Delete the `#![allow(unused_variables)]` scaffold line at
  the top of each module the task fills completely.
- Translate from the C at the anchors; keep the error-message text byte for byte (tests compare it).
- Unit tests: at least the edge cases the C comments name; expected values come from running the C, not from
  reasoning. No `unsafe` outside the six modules of §6's `unsafe` gate. Run every gate of §6; report each
  command's exit status.
- C side: exactly the removal named in the brief, nothing else in that file.
- Reach proof, before any timing. Two earlier benchmarks never ran the ported code (a 4-symbol dictionary skipped
  `ids_max`; `bench-zip` never met an algorithm-1 block), so a ratio counts only after
  `sh W/rust/reach.sh <the timing command> -- <the task's qrs_* symbols>` exits 0. `reach.sh` (written by S) runs
  the command under `gdb -batch` with a breakpoint on each symbol and `ignore <k> 2000000000`, reads `info
  breakpoints`, prints `qrs_x hit N` per symbol, and exits 1 when a symbol has no `already hit` line. The command
  and input are the timing run's own. Report every `N`. A symbol with `N = 0` is a red gate: report it, do not
  swap the input.
- Benchmark: the row and input the task's table line names, nothing substituted. `bench-kernel` runs as
  `bench-kernel 10000000 5` (n = 1e7, median of 5) and prints ms; report ms with two decimals, never µs. A row
  under 1 ms is not a measurement: stop and report. Baseline `C` is `/data/tmp/qrs/base/<bench>`, built by S from
  the unmodified C with the same bench source.
- Rel gate, after §6's: S generates `/data/tmp/qrs/rel/{c,g}.c` once (`relc-1a c` and `relc-1a g`, leetq's
  `LeetQ/Rel/Lang/TestNative.lean`). Per task, link each with `W/c/rt.c` and `W/.lake/build/lib/libqleankernel.a`
  by the `cc` line `rust/BENCH.md` gives; both exit 0, `nm -u` shows no `lean_`, `ldd` shows libc/libm/libpthread
  only, and the `out` directory `c` writes is byte-equal (`cmp`) to the one in `/data/tmp/qrs/rel/base/`.

Models: one opus task at a time, three sonnet at most. S is the only opus task of column (b); A0 is the only one
of column (a) and starts after B11 is merged. Every other task is sonnet, the SIMD ones included: S compiles
their skeleton.

| task | model  | after   | Rust it fills                                   | C section it edits                 |
|------|--------|---------|-------------------------------------------------|------------------------------------|
| S    | opus   | —       | scaffold (below)                                | sort.c exports; bench sources      |
| B1   | sonnet | S       | `ids::firsts`                                   | ids.h:271-317                      |
| B2   | sonnet | S       | `ids::map`                                      | sort.c:3270-3315, 3400-3414        |
| B3   | sonnet | S       | `key.rs`: `rank32/64`, dense `Keys`, `each`, `range` | sort.c:1969-1975              |
| B4   | sonnet | S       | `group::fill`                                   | sort.c:2103-2111                   |
| B5   | sonnet | B3, B4  | `group::number`, `group::group_ids`             | sort.c:2252                        |
| B6   | sonnet | B5      | `ids::pack_in_place`                            | sort.c:2254                        |
| B7   | sonnet | S       | `own::write_head`                               | own.c:147-179                      |
| B8   | sonnet | S       | `pod::cast*`, `CCoc::view`, `Coc::{frame,exc,blk_nexc}`, `unpack.rs` | none          |
| B9   | sonnet | B8      | `simd::res_unpack`, `coc::lanes`                | coc.h:604-619, 819-824             |
| B10  | sonnet | B9      | `simd::res_unpack_add`, `Coc::decode_blk`       | coc.h:652-695, 2633-2654           |
| B11  | sonnet | B5, B10 | `kwin.rs`, `Keys for Win`                       | sort.c:212-334, 1973, 2006-2018    |

Benchmarks (all `bench-kernel 10000000 5` unless stated; ratio = min of 3 R medians / min of 3 C medians):

| task | row to read                                             | reach symbols                              | max  |
|------|---------------------------------------------------------|--------------------------------------------|------|
| B1   | `idGroups 2b d=3`, `idGroups 4b d=11`: `idGroups`       | `qrs_ids_firsts`                           | 1.05 |
| B2   | all seven `idGroups` rows: `idGroups`                   | `qrs_ids_map`                              | 1.05 |
| B3   | the five `groupIds` rows                                | `qrs_key_range`                            | 1.05 |
| B4   | the five `groupIds` rows                                | `qrs_group_fill`                           | 1.05 |
| B5   | the five `groupIds` rows                                | `qrs_group_ids`                            | 1.05 |
| B6   | `u8 groupIds` of `idGroups` rows `d` = 2, 4, 3, 16, 11  | `qrs_ids_pack`                             | 1.05 |
| B7   | `bench-own`: `write` of `til 8`, 10,000 writes a timing | `qrs_own_write_head`                       | 1.10 |
| B8   | none: unit vectors from the C                           | —                                          | —    |
| B9   | `foR i64 ng=100 scale=1`, `foR i32 ng=100 scale=1`      | `qrs_res_unpack`, `qrs_coc_lanes`          | 1.05 |
| B10  | `foR i64 exc`: `groupIds`                               | `qrs_decode_blk_i64`, `qrs_res_unpack_add` | 1.05 |
| B11  | all `foR` rows: `groupIds`                              | `qrs_group_ids_win`                        | 1.05 |

Why each row runs the ported code (the reach proof confirms it; this is what to check when `N = 0`):

- B1: `d < 2^w`, so after `d` groups the walk scans the whole column for an id ≥ `d`. At `d = 2^w` (the rows
  `1b d=2`, `2b d=4`, `4b d=16`) it stops after a few rows and times nothing.
- B2: the map is one pass over 1e7 ids. `8b d=4` is byte in, 2 bits out; `8b d=200` is the whole-lane arm; the
  sub-byte rows are the 256-entry table.
- B3–B5, the five `groupIds` rows: `groupIds bit`; `u8 groupIds` in `idGroups 8b d=200`; `groupIds i64 direct`
  (span 999 < 4n + 1024, the direct table); `groupIds i64 hashed 1e3` and `hashed n` (span ≈ 1e9 ≥ 4n + 1024, the
  hashed table with 1e3 and ≈ 1e7 groups). `range_of` is the first pass, numbering the second, the fill the
  threaded third. No existing row took the hashed arm through `groupIds`; S adds them.
- B6: `ng ≤ 16` gives `w < 8`, so the byte lane is packed in place; `d=200` skips it.
- B7: every write builds the header. The syscalls are nearly all of the time, so the row bounds a regression and
  measures nothing finer; 10,000 writes a timing keep it in ms.
- B8: on an AVX-512 host `res_unpack_scalar` runs only inside the self-check `res_unpack_agrees` (coc.h:783) and
  for the widths `res_unpack` refuses; the views get their first C caller in B10. No row can time them.
- B9: residuals of `ng=100` are 7 bits, not a power of two, so `coc_lanes` unpacks every block. The other `foR`
  rows may land on 16 or 32 bits and skip it.
- B10: `keys_blk_foR` decodes a block through `decode_blk_i64` only when it has a patch (sort.c:252). The existing
  `foR` rows have none; the row prints `nexc`, which must be > 0.
- B11: `groupIdsFoR` is the one entry of (a) that makes a `kwin`.

Parallel worktrees (three sonnet at most; merge into `rust-port-0` in task order, one full gate run per merge):

| wave | tasks          | why they do not collide                                                          |
|------|----------------|----------------------------------------------------------------------------------|
| 0    | S              | alone: it fixes every signature                                                  |
| 1    | B1, B3, B4     | `ids.rs`/ids.h; `key.rs`/`range_of`; `group.rs`/`dedup`'s tail                   |
| 2    | B2, B5, B8     | `id_groups_of`; `group_ids_of`; no C edit                                        |
| 3    | B6, B7, B9     | sort.c:2254; own.c; coc.h                                                        |
| 4    | B10            | needs B9's `lanes`                                                               |
| 5    | B11            | needs B5 and B10; then A0 (opus), then column (a) three at a time in §5's order  |

**Task S — scaffold for column (b) (opus: the pool call, the `Keys` monomorphisation and the SIMD skeleton have
open ends; it is the only step of column (b) that may change a type).** On `rust-port-0`.
- Rust: every signature of §3's added block with `unimplemented!()` bodies in `key.rs`, `group.rs`, `kwin.rs`,
  `ids.rs`, `own.rs`, `coc.rs`; `c.rs`: `run_map` complete over `CPass` and the extern `qlean_run_c`; `simd.rs`:
  one `#[target_feature]` fn per `RES_UNPACK*` macro instance of coc.h:570-760 with every intrinsic the C uses
  named in it and compiling on 1.93.1 (an unstable one is reported by name; this is the check §2 left open), bodies
  `unimplemented!()`.
- Shims in `ffi.rs` (slices only, as task 0's rule): `qrs_ids_firsts`, `qrs_ids_map`, `qrs_ids_pack`,
  `qrs_key_range`, `qrs_group_fill`, `qrs_group_ids`, `qrs_group_ids_win`, `qrs_own_write_head`, `qrs_coc_lanes`,
  `qrs_decode_blk_{u8,i16,i32,i64}`; `qrs_res_unpack*` exist.
- C: `qlean_run_c`, a non-`static` wrapper of `qlean_run` in sort.c; no other C change.
- Bench: add to `tools/bench-kernel.lean` the rows `groupIds bit` (bits of `i * 2654435761 % 2`), `groupIds i64
  direct` (`payload n 8 1000`), `groupIds i64 hashed 1e3` (`payload n 8 1000 1000000`), `groupIds i64 hashed n`
  (`payload n 8 1000000007`), each `Order.groupIds` at n; `foR i64 exc` (`payload n 8 100` with element `i` replaced
  by `2^40 + i` where `i % 1000 = 7`, through `Coc.encode 8`, printing `nexc`). In `tools/bench-own.lean` time the
  `write` as B7's row says and print ms. Build both from the unmodified C (`/data/tmp/qrs/wtc` plus the two bench
  sources) into `/data/tmp/qrs/base/`.
- `rust/reach.sh` as the common protocol states; prove it on what is landed: `qrs_ids_max` reads `N > 0` on
  `bench-own`'s 5-symbol source.
- Rel gate files and the baseline `out` directory; the exact `cc`, `nm`, `ldd`, `cmp` lines into `rust/BENCH.md`,
  whose `Pending` paragraph is replaced. If `relc-1a g`'s C does not link without Lean at leetq's HEAD, report it
  and keep the `c` half.
- Pass: every gate of §6 except benchmark; every bench row ≥ 1 ms on the baseline, each printed in ms.

**B1 — `ids_firsts`.** Fill `ids::firsts` from ids.h:271-317: the walk to the first `top` groups, then the
word-at-a-time search for an id ≥ `nd` (the `e`/`c`/`k` masks, 32 words a step, then a word, then a field). Reads
of 8 bytes at `ids[i * w / 8]` become a checked `get(..8)` with the field walk for the tail. C: the body of
`ids_firsts` becomes `return qrs_ids_firsts(ids, ids_bytes(n, w), n, w, nd, slot, first);` (one call a column,
so the header body goes). Unit: w ∈ {1, 2, 4, 8, 16, 32, 64}, `nd` ∈ {2^w, 2^w − 1}, the first id ≥ `nd` at
positions 0, 63, 64, n − 1, none.

**B2 — the id map.** Fill `ids::map`: `ids_map_run` (sort.c:3283-3315: whole lanes by `IDS_UNPACK`; below a byte
the 256-entry table) and the table build and tail mask of `id_groups_of` (sort.c:3400-3414), threaded by
`c::run_map` with `units = wo >= 8 ? n : ob`, cost 4, wide 8. C: in `id_groups_of` those lines become one
`qrs_ids_map(ids, n, w, d, slot, wo, out)`; `ids_map_job`, `ids_slot`, `ids_map_run` and their macros are deleted
if sort.c:3432-3460 (`pair_ids_narrow`) does not use them, else kept and reported.

**B3 — keys and the range.** Fill `rank32`, `rank64` (sort.c:100-110), the eight dense `Keys` impls (`key_at`,
sort.c:132-144; `Win` stays `unimplemented!()` until B11), `each` (`SK_EACH`, sort.c:1697), `range`
(`SK_RANGE`, sort.c:1710: one min and one max per kind). C: `range_of` keeps its `SK_WIN` line and calls
`qrs_key_range` for the rest; `key_at` stays (per-element inline, §5).

**B4 — the fill.** Fill `group::fill` from `ids_run` (sort.c:1992-2018): lanes 8/16/32/64 × `Table::Direct`
(`tab[key − mn] − 1`) / `Table::Hashed` (`group_find`, sort.c:1985), one monomorphic loop per kind through `each`,
threaded by `c::run_map` (cost 4, wide 8). C: at sort.c:2103-2111 `dedup` calls `qrs_group_fill(kind, p, n, mn,
dtab, slots, htab, gkey, ng, cap, sh, gid, lane)` when `kind != SK_WIN` and keeps `qlean_run(ids_run, …)` for `SK_WIN`
(S: `ng` added, the length of `gkey` — `xalloc`'s entries past it are uninitialised; 0 answered = refused).

**B5 — numbering.** Fill `group::number` — the `direct` test (sort.c:2046), `SK_DIRECT_NONE` and `SK_HASHED_NONE`
(sort.c:1752-1778) with `group_probe`, `group_prefetch` at `SK_AHEAD = 32`, `cap_for`, `hash_shift`; no bitmap,
no estimate, no `part_dedup`: those need `!gid || cnt` — and `group::group_ids` = `number`, then `fill` at
`max(8, id_width(ng))`. C: `group_ids_of` (sort.c:2252) calls `qrs_group_ids(kind, p, m, mn, mx, g, m * (cw / 8),
first)` when `kind != SK_WIN` (`SIZE_MAX` answered = refused), else `dedup` as now; `dedup` itself is not edited.

**B6 — pack in place.** Fill `ids::pack_in_place` from `IDS_PACK`/`IDS_PACK_SUB`/`IDS_PACK_BYTES`
(ids.h:117-175) with `VAL(i) = g[i]`; a byte is stored after the ids it packs are read. C: sort.c:2254 becomes
`if (w < 8) qrs_ids_pack(g, m, w);`. The macros stay (other C users).

**B7 — own header.** Fill `own::write_head` from own.c:147-179: the kind/part-count/name-length check with its
message, magic, version, `code`, `attr`, `kind`, the three little-endian fields, each part's 8-aligned offset
after `OWN_ROOM`. C: `qlean_own_write` keeps `lean_*` accessors, the `own_seg` list and `own_replace`; the check
and the `put_le` lines become one `qrs_own_write_head(code, attr, kind, count, nl, len, np, head, sizeof head, off,
why, sizeof why)` (`len`, `off`: `np` entries; 0 answered = refused, `why` filled). `put_le` stays if another C
caller remains.

**B8 — views and the scalar unpack.** Fill `pod::cast`, `pod::cast_mut` (one `from_raw_parts` each after the
alignment and length test), `CCoc::view` (lengths: metadata `mblk`, `exc.off` `mblk + 1`, `pos` `nexc`, `raw`
`nexc * exc_esz`; null `exc_off` or `fdelta` gives `None`), `Coc::frame` (coc.h:222), `exc` (277), `blk_nexc`
(293), `unpack::res_unpack_scalar` (coc.h:534-566; the tail is read through a zero-padded 16-byte copy). No C
edit, no benchmark (table above). Unit: every width 1..64 × nb ∈ {1, 7, 1023, 1024} against vectors dumped from
the C; a `coc` built by the C encoder viewed and read back.

**B9 — `res_unpack`, `coc_lanes`.** Fill `simd::res_unpack` in S's skeleton, intrinsic for intrinsic from
coc.h:570-619 into `simd::v::unpack16_u8`…`unpack64`, falling back to B8 where the C does (coc.h:606, 768), and
`coc::lanes` (coc.h:819-824). C: both bodies become the `qrs_*` call (one call a block; `qrs_coc_lanes(p, w, nb,
buf)`). `res_unpack_agrees` stays and now compares the two Rust ports.

**B10 — `res_unpack_add`, `decode_blk`.** Fill `simd::res_unpack_add` (coc.h:652-695) and the generic
`Coc::decode_blk<T>` (coc.h:2633-2654: frame, the eight width arms, `COC_LOAD_SUB`, the patch overwrite). C: the
body of `COC_FN(decode_blk)` becomes the call to `qrs_decode_blk_<T>((const CCoc *)c, b, nb, out)`.

**B11 — the key window.** Fill `kwin.rs` (`key_flip`, `keys_blk_foR`, `kwin_blk`, `kwin_miss`, `kwin_at`,
`range_foR`; sort.c:212-334, the ALP arm `w->f` left to A5 behind an `Option` that is `None`) as `Kwin::new`,
`kwin::key_flip`, `kwin::keys_blk`, `kwin::range`, `Keys for Kwin` with `fork` = a fresh window on the same `Coc`,
and `group::group_ids_win` (B5's passes over a `Kwin`). C: `qlean_sort_group_ids_foR` (sort.c:2685) calls
`qrs_key_range_win(kind, (const CCoc *)&c, &mn, &mx)` where it called `range_of(SK_WIN, …)`, then
`qrs_group_ids_win(kind, (const CCoc *)&c, m, mn, mx, gid, gcap, first)` in `group_ids_of`'s shape; B4's and B5's `SK_WIN`
branches stay for the callers outside (a). This row is the measurement of §5's claim that the three native
entries never reach the window: run the Rel gate's two exes under `reach.sh` with `qrs_group_ids_win` and report
`N` (expected 0 there, > 0 on the `foR` rows).

Column (a), from A0 (branch `rs-A0`). Every Rust function below exists on `rs-A0` with its final signature and a
body `unimplemented!("A<n>: <C name>")`; the task replaces the body, deletes the module's
`#![allow(unused_variables)]` once no stub is left, and points the C call site at the `qrs_*` shim. Phase-1 rules:
a function that allocates or unboxes a `lean_object` stays C; a threaded pass is a Rust fn over `run: Runner` and
slices with a `qrs_*` shim; a per-element helper (`coc_get`, `res_get`, `sym_eq`, the `ew_*` scalars, …) gets a
`pub fn` only, and its C body stays while a C caller remains; the encoder orchestration (`coc_enc_open/plan/layout/
pair`, `src_pass`, `qlean_coc_encode_src`, `fill_*`) stays C and calls the A16/A17 steps through `CEnc`. Lines are
the HEAD (`rs-A0`) starts of the task's functions; `after` lists only Rust-to-Rust calls (an edge through C glue,
e.g. A15→A16, A23→A26, A43→A42, does not order the tasks). All tasks are sonnet.

| task | after       | its `A<n>:` stubs in             | C section it edits                      |
|------|-------------|----------------------------------|-----------------------------------------|
| A1   | A2          | `cocops.rs`                      | coc.h:139-303, 2043-2165                |
| A2   | —           | `res.rs`, `simd.rs`              | coc.h:446-503, 678-690                  |
| A3   | A1 A2       | `cocops.rs`, `res.rs`, `simd.rs` | coc.h:790-910                           |
| A4   | A1 A2       | `cocops.rs`, `res.rs`            | coc.h:934-1031                          |
| A5   | A1          | `alp.rs`, `kwin.rs`              | coc.h:1463-1554, 1811; sort.c:281       |
| A6   | A3          | `cocops.rs`                      | coc.h:1304-1382                         |
| A7   | A1 A2       | `enc.rs`                         | coc.h:2317-2401                         |
| A8   | A1 A7       | `enc.rs`                         | coc.h:2452-2546                         |
| A9   | A5          | `alp.rs`                         | coc.h:2567-2785                         |
| A10  | —           | `ids.rs`                         | ids.h:56-99, 201-281                    |
| A11  | —           | `sym.rs`                         | sym.h:28-146                            |
| A12  | —           | `reduce.rs`                      | reduce.c:261-277                        |
| A13  | —           | `reduce.rs`                      | reduce.c:488-606                        |
| A14  | A1          | `scan.rs`, `simd.rs`             | scan.c:309-491                          |
| A15  | —           | `codec.rs`                       | coc.c:592-820                           |
| A16  | A1 A5 A8 A9 | `enc.rs`, `ffi.rs`               | coc.c:95-313                            |
| A17  | A1 A5 A8 A9 | `enc.rs`                         | coc.c:318-643                           |
| A18  | A5          | `codec.rs`                       | coc.c:1015-1139                         |
| A19  | A1 A5       | `sort.rs`                        | sort.c:183-394 (not B11's)              |
| A20  | A19         | `sort.rs`                        | sort.c:417-555, 682-724                 |
| A21  | —           | `sort.rs`                        | sort.c:734-831                          |
| A22  | A1          | `sort.rs`                        | sort.c:894-1113                         |
| A23  | —           | `sort.rs`                        | sort.c:1631, 2293-2385, 3386            |
| A24  | —           | `sort.rs`                        | sort.c:2475-2536                        |
| A25  | A11         | `sort.rs`                        | sort.c:2814-2964                        |
| A26  | —           | `sort.rs`                        | sort.c:3060-3423                        |
| A27  | —           | `sort.rs`                        | sort.c:3471-3483                        |
| A28  | A1          | `search.rs`                      | search.c:53-179, 407, 818               |
| A29  | A28         | `search.rs`                      | search.c:251-399                        |
| A30  | A29         | `search.rs`                      | search.c:829-961                        |
| A31  | A11         | `search.rs`                      | search.c:974-1266                       |
| A32  | A1          | `search.rs`                      | search.c:1497-1706                      |
| A33  | A28         | `search.rs`                      | search.c:731, 2004-2078                 |
| A34  | A1 A2       | `structural.rs`                  | structural.c:56-343                     |
| A35  | A1 A5 A34   | `structural.rs`                  | structural.c:270-602                    |
| A36  | A2 A34      | `structural.rs`                  | structural.c:655-828                    |
| A37  | —           | `structural.rs`                  | structural.c:926-944, 1045-1134         |
| A38  | —           | `structural.rs`                  | structural.c:1278-1586                  |
| A39  | A10         | `structural.rs`                  | structural.c:1792-1969                  |
| A40  | A11         | `structural.rs`                  | structural.c:2046-2185                  |
| A41a | A40         | `structural.rs`                  | structural.c:2203-2223                  |
| A41b | —           | `structural.rs`                  | structural.c:2373-2378, 3005            |
| A42  | —           | `ew.rs`                          | elementwise.c:140-293                   |
| A43  | —           | `ew.rs`, `simd.rs`               | elementwise.c:482-1079                  |
| A44  | —           | `ew.rs`                          | elementwise.c:1569-1789                 |
| A45  | —           | `ew.rs`                          | elementwise.c:1843-1951                 |
| A46a | A42         | `ew.rs`                          | elementwise.c:2007-2108                 |
| A46b | A42         | `c.rs`, `ew.rs`                  | elementwise.c:2150-2372; pass.h:502-530 |

Waves of 3 (critical path A2→A1→A5→A9→A16 first; every task's `after` is in an earlier wave):
1 A2 A10 A11 · 2 A1 A40 A42 · 3 A5 A7 A34 · 4 A3 A8 A9 · 5 A4 A16 A17 · 6 A19 A35 A36 · 7 A6 A18 A20 ·
8 A14 A22 A28 · 9 A29 A32 A33 · 10 A25 A30 A31 · 11 A39 A41a A46a · 12 A43 A44 A46b · 13 A12 A13 A45 ·
14 A15 A21 A23 · 15 A24 A26 A27 · 16 A37 A38 A41b.

Benchmarks. No Rel program qualifies: the Rel gate's two exes (`/data/tmp/qrs/rel/base/{c,g}`) take 0.28 and
0.44 ms of task-clock in all, under 1 ms in any task's symbols. So every row is `bench-kernel 10000000 5` or
`bench-coc 10000000 5` (n = 1e7, 5 reps); "new row" means the task adds it to tools/bench-*.lean with the input
given. Max 1.05, or 1.10 where the time is allocation or I/O. A task with only per-element helpers is measured
through its first caller's shim.

| task | row to read (input)                                          | reach symbols                          | max  |
|------|--------------------------------------------------------------|----------------------------------------|------|
| A1   | `foR` rows, `groupIds`                                       | `qrs_group_ids_win`                    | 1.05 |
| A2   | new row `bench-coc encode i64`: `til n` mod 1000 + 1e9       | `qrs_res_pack`                         | 1.05 |
| A3   | `bench-coc` `sum=` (i64 FoR, nulls 0 and 1%)                 | `qrs_coc_sum`                          | 1.05 |
| A4   | `bench-coc` `min=` (same input)                              | `qrs_coc_prd`                          | 1.05 |
| A5   | new row `alp decode f64`: `0.01 * til n`                     | `qrs_cocf_decode`                      | 1.05 |
| A6   | new row `foR shift i64`: `prev` of `til n` encoded           | `qrs_coc_shift`                        | 1.05 |
| A7   | A2's row                                                     | `qrs_enc_for_meta`                     | 1.05 |
| A8   | new row `encode i64 exc`: `til n`, every 1000th + 2^40       | `qrs_enc_for_pack`                     | 1.05 |
| A9   | new row `alp encode f64`: `0.01 * til n`                     | `qrs_enc_alp_meta`                     | 1.05 |
| A10  | `idGroups` rows, `distinctIds`                               | `qrs_ids_runs`                         | 1.05 |
| A11  | new row `sym msort`: 1e6 symbols, `string` of shuffled `til` | `qrs_sym_msort`                        | 1.05 |
| A12  | the `sum`/`min`/`max` `over` rows (u8 i16 i32 i64)           | `qrs_over_bytes`                       | 1.05 |
| A13  | new row `over segments sum i64`: `til n` in 1000 segments    | `qrs_segments`                         | 1.05 |
| A14  | new row `sums i64`: `til n`                                  | `qrs_scan_run`                         | 1.05 |
| A15  | new row `decode i64 FoR`: `til n` encoded                    | `qrs_coc_decode`                       | 1.05 |
| A16  | A2's and A9's rows                                           | `qrs_enc_for_pack`, `qrs_enc_alp_pack` | 1.05 |
| A17  | new row `encode narrow i16`: `til n` mod 30000               | `qrs_enc_blk_meta`                     | 1.05 |
| A18  | new row `alp sum f64`: `0.01 * til n`                        | `qrs_alp_decode`                       | 1.05 |
| A19  | `grade` rows (u8)                                            | `qrs_grade_keys`                       | 1.05 |
| A20  | `grade` rows (u8)                                            | `qrs_grade_keys`                       | 1.05 |
| A21  | `grade {w}b` rows: `u8`                                      | `qrs_grade_narrow`                     | 1.05 |
| A22  | `grade {w}b` rows: `lane`; `ids {w}b`: `grade lane`          | `qrs_order`                            | 1.05 |
| A23  | `composeKey ids` rows: `ids`                                 | `qrs_pair_ids_narrow`                  | 1.05 |
| A24  | `rankSlices` rows                                            | `qrs_rank_slices`                      | 1.05 |
| A25  | new row `grade syms`: 1e6 symbols, 1000 distinct             | `qrs_grade_syms`                       | 1.05 |
| A26  | `idGroups` rows: `groupIdsSyms`, `partedIds`                 | `qrs_grade_ids`, `qrs_intern_syms`     | 1.10 |
| A27  | new row `grade guid`: n/10 guids from `til`                  | `qrs_grade_guid`                       | 1.05 |
| A28  | `keyOperand` rows                                            | `qrs_coc_srange`                       | 1.05 |
| A29  | `ids {w}b` rows: `find u8`, `member u8`                      | `qrs_coc_srange`                       | 1.05 |
| A30  | `ids {w}b` rows: `find ids`, `member ids`                    | `qrs_coc_srange`                       | 1.05 |
| A31  | new row `find sym`: 1e6 symbols, 1000 probes                 | `qrs_sym_scan`                         | 1.05 |
| A32  | new row `bin i64`: `til n` haystack, n/10 keys               | `qrs_bin`                              | 1.05 |
| A33  | `runStarts` rows; `ids {w}b`: `runStarts`                    | `qrs_coc_srange`                       | 1.05 |
| A34  | new row `reverse foR i64`: `til n` encoded                   | `qrs_reverse_enc`                      | 1.05 |
| A35  | new row `concat foR i64`: two `til n/2` encoded              | `qrs_put_res`                          | 1.05 |
| A36  | A35's row                                                    | `qrs_put_res`                          | 1.10 |
| A37  | new row `gather i64`: `til n` at `n?n`                       | `qrs_gather`, `qrs_gather_enc`         | 1.05 |
| A38  | new row `where i64`: `til n` with weights `n#0 1`            | `qrs_expand`, `qrs_gather_ids`         | 1.05 |
| A39  | new row `concat i64`: 10 parts of `til n/10`                 | `qrs_concat`                           | 1.10 |
| A40  | new row `symdict ,`: two 1e6-symbol dicts, half shared       | `qrs_symtab_fill`                      | 1.10 |
| A41a | A40's row                                                    | `qrs_symtab_fill`                      | 1.10 |
| A41b | `bench-own` `til 8`; new row `scatter`: `n?n` into `til n`   | `qrs_til`, `qrs_scatter`               | 1.10 |
| A42  | A43's row (`div`)                                            | `qrs_ew_val`                           | 1.05 |
| A43  | new rows `ew +`, `ew div`, `ew <` i64: `til n`, `n?1000`     | `qrs_ew_val`, `qrs_ew_cmp`             | 1.05 |
| A44  | new row `ew neg i64`, `ew not bits`: `til n`                 | `qrs_ew_mon`                           | 1.05 |
| A45  | new rows `cast f64→i32`, `ew month date`: `til n`            | `qrs_ew_cast`                          | 1.05 |
| A46a | new row `widen i16→i64`: `til n` mod 30000                   | `qrs_ew_widen`                         | 1.05 |
| A46b | new row `chain a+b*c i64`: three `til n`                     | `qrs_run_chain`                        | 1.05 |

### Earlier briefs (tasks 0–10): landed or deferred — not dispatched

Tasks 0, 1, 2, 3, 6 are merged in `rust-port-0`; 4, 5, 7, 8, 9, 10 are deferred or superseded (§5). Their
table and briefs are kept as the record of what landed.

| task | model  | after | parallel with | Rust it fills                            | C section it edits  |
|------|--------|-------|---------------|------------------------------------------|---------------------|
| 0    | opus   | —     | —             | whole scaffold                           | lakefile; `c/rs.h`  |
| 1    | sonnet | 0     | 2 3 6 7 8 9   | `why.rs`, `layout.rs`                    | own.c:189-227       |
| 2    | sonnet | 0     | 1 3 6 7 8 9   | `bits.rs`, `ids.rs`                      | own.c:229-261       |
| 3    | sonnet | 0     | 1 2 6 7 8 9   | `own.rs`: `head`                         | own.c:364-394       |
| 4    | sonnet | 1, 2  | 6 7 8 9       | `pod.rs`, `coc.rs`: `Meta`, `own.rs`: `check` | own.c:263-340  |
| 5    | sonnet | 4     | 6 7 8 9       | `coc.rs`: `Coc`, `ffi.rs`: `CCoc::view`  | coc.h:234-241       |
| 6    | sonnet | 0     | 1 2 3 7 8 9   | `zip.rs`: `zq`                           | zip.c:141-175       |
| 7    | sonnet | 0     | 1 2 3 6 8 9   | `zip.rs`: `trailer`, `table`             | zip.c:204-246       |
| 8    | sonnet | 0     | 1 2 3 6 7 9   | `simd.rs`: `u8_sum`                      | reduce.c:258-275    |
| 9    | sonnet | 0     | 1 2 3 6 7 8   | `unpack.rs`                              | coc.h:528-562       |
| 10   | opus   | 9     | 4 5           | `simd.rs`: `res_unpack`, `res_unpack_add` | coc.h:564-764      |

**Task 0 — scaffold (opus: the lake target and the link check have open ends a paste-only brief cannot close).**
Branch `rust-port` from qlean 369841b. Creates: `rust/Cargo.toml` (no dependencies; release profile
`opt-level = 3, panic = "abort", codegen-units = 1`), `rust/rust-toolchain.toml` (`1.93.1`), `rust/build.sh` (§4),
`rust/src/lib.rs` (`#![cfg_attr(not(test), no_std)]`, `#![deny(unsafe_op_in_unsafe_fn)]`, `extern crate alloc`),
`rt.rs` (the allocator over `aligned_alloc`/`free`, the panic handler writing the message to fd 2 then `abort`,
the `rust_eh_personality` and `_Unwind_Resume` stubs — copy `/data/tmp/qrs-probe/src/lib.rs`, gate it
`#[cfg(not(test))]`), `pod.rs`, `c.rs` (empty), every module of §3 with the signatures verbatim and
`unimplemented!()` bodies, `ffi.rs` with all shims and mirrors complete, `c/rs.h` generated by cbindgen (§4).
Shim rule: null-or-zero length becomes an empty slice; a shim does nothing but build slices and call. Shims:
`qrs_exc_ok(t, len, nblk, nexc, esz, part, alp, why, cap) -> c_int` (`alp` 0/1/2 = `Tail::None/Exps/Frames`),
`qrs_ids_max(p, bytes, w, n) -> usize`, `qrs_own_head(m, size, *mut OwnHead, why,
cap) -> c_int`, `qrs_own_check(kind, n, p: *const *const u8, len: *const usize, np, why, cap) -> c_int`,
`qrs_coc_std(*const CCoc, n) -> c_int`, `qrs_zq(b, n, dst, want) -> *const c_char` (null = ok; `dst` is the
pointer C passes, 8 bytes before the block), `qrs_ztrailer(hdr, size, nblk, hat, *mut ZTrailer, why, cap) ->
c_int`, `qrs_ztable(ent, nblk, at, algo) -> usize`, `qrs_u8_sum(p, n) -> i64`, `qrs_res_unpack_scalar(p, w, nb,
out)`, `qrs_res_unpack(p, w, nb, out)`, `qrs_res_unpack_add(p, w, nb, base, out, tw) -> c_int`; the `p` slice of
the three unpack shims is `BLK * w / 8` bytes. Lakefile: §4. Also copies `tools/bench-own.lean` and its `lean_exe`
stanza from `/data/tmp/c2rust/wt` (read only), builds the four baseline benchmarks from the unmodified C into
`/data/tmp/qrs/base/bench-{own,zip,coc,kernel}` BEFORE linking `qrs.o`, and writes the exact command line of each
into `rust/BENCH.md`. Pass: all gates of §6 except benchmark; `sizeof` asserts hold on both sides; `nm` shows the
12 `qrs_*` symbols; `ldd` of `qlean-test` gains no library.

**Task 1 — `exc_ok`.** Fill `Why::new`, `Why::say`, `exc_layout`, `exc_ok`. Model: `/data/tmp/c2rust/wt/rust/
own.rs:1120-1170` (the trial's safe port; replace its two `unsafe` layout calls with `exc_layout`). ALP
(`Tail::Exps`) accepts `size <= len`, the other two require `size == len` (own.c:198). C: delete the body of
`exc_ok` (own.c:192-227); the two calls at own.c:301 and :312 become `qrs_exc_ok` with the same arguments.
Bench: `bench-own`, threshold 1.10.

**Task 2 — ids.** Fill `width_for`, `lane_width` (coc.h:425-435), `id_width`, `ids_bytes`, `id_at` (ids.h:19-50),
`ids_max` with `narrow_max` as a private fn (own.c:231-261). C: delete `narrow_max` and `ids_max` from own.c; the
call at own.c:333 becomes `qrs_ids_max(p[1], len[1], wd, n)`. `ids.h` and `coc.h` are not edited. Bench:
`bench-own` on a symbol column (add the source `` `u#10000000?`3 `` to the binary's argument list as
`rust/BENCH.md` describes), threshold 1.10.

**Task 3 — own header.** Fill `own::head`: the magic, version, kind/part-count, header-end and part-table checks of
own.c:366-394, messages unchanged, little-endian reads by `u64::from_le_bytes`. C: in `qlean_own_map` replace
own.c:366-394 by one `qrs_own_head(m, size, &h, why, sizeof why)` and set `part[k] = m + h.off[k]`, `len[k] =
h.len[k]`; `put_le`/`get_le` stay (the writer uses them). Bench: `bench-own` map column, threshold 1.10.

**Task 4 — `Meta` and `own_check`.** Fill `pod::cast`, `pod::cast_mut` (the only `unsafe`: one
`slice::from_raw_parts` each, after the alignment and length test), `Meta::new`, `res_end`, `grid`, and
`own::check` for kinds 1–4 (own.c:263-340) using tasks 1 and 2. Keep the branch-free first pass over the blocks
(own.c:274-278) as one iterator fold so it still vectorises. C: delete the body of `own_check`; own.c:395 calls
`qrs_own_check(kind, n, part, len, np, why, sizeof why)`. Bench: `bench-own` map column, threshold 1.10.

**Task 5 — `Coc`, `CCoc::view`, `coc_std`.** Fill `Coc::attach`, `std`, `blocks`, `frame` and `CCoc::view` (null
`exc_off` gives `exc: None`; null `fdelta` gives `None`; slice lengths: metadata `mblk`, `exc.off` `mblk + 1`,
`pos` `nexc`, `raw` `nexc * exc_esz`). C: in coc.h replace the body of `coc_std` (coc.h:234-241) by
`return qrs_coc_std((const CCoc *)c, n);`. `attach` and `blocks` get unit tests only; their first C
caller comes with step 11. Bench: `bench-coc`, threshold 1.05.

**Task 6 — `zq`.** Fill `zip::zq` from zip.c:141-175; `dst[..8]` is the zero prefix the algorithm's back
references may reach, output starts at `dst[8]`; every index is a checked slice index (a malformed stream must
return `Err`, never panic: add the bound tests the C lacks and return the nearest existing message). Messages are
`c"..."` literals. C: delete the body of `zq`; zip.c:299 calls `qrs_zq(c->cbuf, n, c->buf - 8, want)`. Bench:
`bench-zip` on a file compressed with algorithm 1, threshold 1.10.

**Task 7 — zip trailer and table.** Fill `zip::trailer` (the five checks of zip.c:212-232, messages unchanged) and
`zip::table` (zip.c:238-246 without `zlib_load`). C: zopen keeps `open`, `fstat`, the three `zpread`s and the
allocations; the checks become one `qrs_ztrailer`, the fill loop one `qrs_ztable`, followed by a C loop over
`algo[k]` that keeps the `seen`/`zlib_load` logic. Bench: `bench-zip`, threshold 1.10.

**Task 8 — `u8_sum` (first SIMD).** In `simd.rs`: `#[target_feature(enable = "avx512f,avx512bw")] fn u8_sum512`
translating reduce.c:264-271 intrinsic for intrinsic, compiled under `#[cfg(target_feature = "avx512bw")]`; a
scalar `u8_sum_scalar`; `u8_sum` picks by the same `cfg` (the C picks by `#if defined(__AVX512BW__)`). `unsafe`
only for the two loads and the call into the attributed fn. Unit test: both paths agree on lengths 0..300. C:
delete `over_u8_sum`; reduce.c:281 calls `qrs_u8_sum`. Bench: `bench-kernel` rows for `sum` over a byte payload,
threshold 1.05 (the C comment records 0.6 ms per 20M bytes as the target).

**Task 9 — `res_unpack_scalar`.** Fill `unpack::res_unpack_scalar` from the `RES_UNPACK_W` macro family
(coc.h:528-562): lanes of `lane_width(w)` bits, little-endian, into `out`. The C reads 8 bytes at every field
start, which runs past the block's `BLK * w / 8` bytes for the last fields (not confirmed as a live over-read in
C; report what you find); the Rust reads the tail through a zero-padded 16-byte copy instead. C: replace the body of
`res_unpack_scalar` by the call to `qrs_res_unpack_scalar`. Unit test: every width 1..64
and nb in {1, 7, 1023, 1024} against vectors dumped from the C. Bench: `bench-coc`, threshold 1.05.

**Task 10 — SIMD decode (opus: about 200 lines of AVX-512 VBMI2 macros, the go/no-go measurement).** Fill
`simd::res_unpack` and `simd::res_unpack_add` from coc.h:564-760 with `#[target_feature]` fns, falling back to
task 9 where the C does (`#else` at coc.h:762). The C self-check `res_unpack_agrees` (coc.h:770) stays and now
compares the two Rust ports. C: both bodies replaced by the calls to `qrs_*`. If an intrinsic is
not stable on 1.93.1, stop and report its name. Bench: `bench-coc` and `bench-kernel`, threshold 1.05; this
result and the unsafe share decide whether steps 11+ are planned.

## 8. Decisions on the open questions, and what is still open

- Phase 2 (the `LEAN_EXPORT` wrappers into `lean.rs`): deferred until task 10's result; Rust never touches `lean.h`.
- cbindgen: yes — `c/rs.h` is generated from `ffi.rs` by the cbindgen CLI inside `build.sh` (§4), since task 0.
- Thresholds 1.10 (I/O, tasks 1–7) / 1.05 (SIMD, tasks 8–10) / 20% unsafe lines: accepted.
- `tools/coc` links `rust/qrs.o`: yes — ported header helpers keep no C copy (§1, §4).
- Open: task 9's suspected read past the block in `RES_UNPACK_W`: if confirmed, fix the C on `master` now or let the
  port be the fix?
