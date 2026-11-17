# qlean C to Rust, phase 2 — inventory, design, order, task briefs

Read: qlean tree `rust-port-0` at 2a5b97f (`/data/tmp/qrs/wt0`), its objects under `.lake/build/c`, `rust/qrs.o`, Lean
4.28.0's `lean.h`, phase-1 design `doc/qlean-rust-design.md` §1, §4, §6, §7. Tags: (m) measured today, (e) estimated.
Phase 2 scope: every `c/*.c`, `c/*.h` except the generated `c/rs.h` — 15,632 lines (m) — the thread pool included.

## 1. Inventory

Method (m): `/data/tmp/qrs/phase2/inv2.py` parses all 16 translation units (the three `EW_PART` thirds of
`elementwise.c` separately) with libclang and `-DQLEAN_RS`, and records per function definition its extent, loops,
callees and references. Roots are the 260 distinct `@[extern "…"]` names in `QLean/`. Output: `fns.tsv` (one row a
function), `macros.tsv`, `lean.tsv`, `segments.txt` (appendix A) in the same directory. Rerun after any wave.

Class rules, applied in this order (mechanical; a function gets the first that matches):

| class | rule                                                                                              |
|-------|---------------------------------------------------------------------------------------------------|
| r     | defined in `rt.c`: the Lean-runtime stand-in of the Rel native build (not one of the six classes) |
| d     | not reachable from any Lean extern, nor from `tools/coc/coc.c`                                    |
| t     | reachable only from `tools/coc/coc.c` (dead to the library)                                       |
| b     | a Lean extern; or not exported, takes or returns `lean_object*`, has no loop (boundary helper)    |
| p     | defined in `pass.h`, or `qlean_run_c`                                                             |
| o     | calls open, mmap, pread, dlopen, rename, socket … and is not an extern                            |
| w     | no loop, calls at least one `qrs_*`, touches no Lean object                                       |
| k     | everything else: C that still computes (has a loop, or is a loop-free helper of such code)        |

A function-like macro counts toward the class of the functions it expands in (priority k, p, o, b, w).

| class      | functions | function lines | macro lines | lines |
|------------|-----------|----------------|-------------|-------|
| k          | 270       | 3428           | 541         | 3969  |
| w          | 78        | 376            | 6           | 382   |
| b          | 315       | 4050           | 97          | 4147  |
| o          | 6         | 124            | 0           | 124   |
| p          | 12        | 127            | 2           | 129   |
| d          | 20        | 140            | 16          | 156   |
| t          | 36        | 280            | 2           | 282   |
| r          | 20        | 101            | 0           | 101   |
| classified | 757       | 8626           | 664         | 9290  |
| rest       |           |                |             | 6342  |
| total      |           |                |             | 15632 |

`rest` is comments, types, includes, blank lines and object macros. Cells below are `functions/lines` (macros in).

| file          | lines | k      | w     | b      | o    | p      | d      | t      | r      | rest |
|---------------|-------|--------|-------|--------|------|--------|--------|--------|--------|------|
| coc.c         | 1015  | 16/222 | 10/57 | 41/283 |      |        |        |        |        | 453  |
| coc.h         | 1816  | 54/562 | 26/59 | 4/21   |      |        | 14/120 | 36/282 |        | 772  |
| elementwise.c | 2146  | 45/786 | 10/60 | 28/557 |      |        |        |        |        | 743  |
| env.c         | 39    |        |       | 2/8    |      |        | 1/5    |        |        | 26   |
| handle.c      | 99    |        |       | 5/60   |      |        |        |        |        | 39   |
| ids.h         | 267   | 6/110  |       | 2/10   |      |        | 2/14   |        |        | 133  |
| interp.c      | 47    | 1/1    |       | 2/21   |      |        |        |        |        | 25   |
| own.c         | 297   | 1/78   |       | 4/79   | 2/37 |        | 1/5    |        |        | 98   |
| pass.h        | 505   | 0/1    |       |        |      | 11/126 |        |        |        | 378  |
| reduce.c      | 891   | 18/212 |       | 11/189 |      |        |        |        |        | 490  |
| rt.c          | 146   |        |       |        |      |        |        |        | 20/101 | 45   |
| scan.c        | 925   | 8/112  | 1/8   | 12/241 |      |        |        |        |        | 564  |
| search.c      | 1626  | 12/115 | 3/5   | 71/926 |      |        |        |        |        | 580  |
| sort.c        | 2556  | 45/858 | 7/50  | 58/666 |      | 1/3    |        |        |        | 979  |
| structural.c  | 2665  | 55/803 | 19/89 | 66/982 |      |        | 1/1    |        |        | 790  |
| sym.h         | 155   | 4/27   | 1/3   | 3/18   |      |        | 1/11   |        |        | 96   |
| time.c        | 24    |        |       | 1/7    |      |        |        |        |        | 17   |
| zip.c         | 413   | 5/82   | 1/51  | 5/79   | 4/87 |        |        |        |        | 114  |

Findings the plan rests on (all (m)):

- **Compute is still in C.** Class k is 270 functions, 3969 lines. 147 of them have a loop (2653 function lines);
  123 are loop-free helpers (775 lines: `id_at`, `ew_width`, `coc_frame`, …) that die with their last C caller.
  "Every kernel of phase 1 is ported" holds for the functions phase 1 listed, not for the files.
- Largest remaining C by object code (`nm -S`, bytes): `ids_place` 79433, `over_groups` 60194, `ew_pack_run`
  60113, `remap_ids_run` 45506, `ew_cmp_ids_run` 40747, `mw_run` 35569, `ew_eq_ids_run` 19951, `fsc_meta` 18352,
  `dedup` 15351, `ew_cmp_key_run` 14325, `move_meta` 14024, `ids_run` 14012, `ew_ids_run` 12931. All are
  width-by-verb macro expansions (`IDS_WIDTHS`, `OG_VERBS`, `EW_PACK_FROM`).
- **Exports: 260** distinct extern names, all defined in C, none missing (the design's 266 counted `LEAN_EXPORT`
  tokens). 92 have a loop of their own; 176 call no `qrs_*`; 17 call `qlean_run` directly; 8 call the OS.
  Plus 55 boundary helpers (`mk_pair`, `coc_view`, `opnd_of`, `ixcell_alloc`, …).
- **libm stayed in C because of the symbol gate**, not by design: float `pow` (`elementwise.c:516`, `ew.rs:236`)
  and the nine float maps (`elementwise.c:1340-1392`: sin cos tan asin acos atan exp log sqrt).
- `qrs.o` defines 215 `qrs_*`; the C objects use 188. 27 are unused by the library (`qrs_decode_*`,
  `qrs_encode_meta_*`, `qrs_pack_block_*`, `qrs_frame_pick_*`, `qrs_coc_sum_blk`, `qrs_u8_sum`, …).
- `tools/coc/coc.c` does not compile at 2a5b97f (clang: 17 errors, undeclared `res_sum8`, `cocf_decode`,
  `dat_f32`, `dat_f64`). Class t (36 functions, 282 lines of `coc.h`) is reachable only from it.
- Pool: 12 live functions, 129 lines, in a 505-line header nine translation units include; `qlean_pool_thread`
  and `qlean_threads` are compiled into each of the nine objects, the pool object itself is one
  (`QLEAN_POOL_OWNER`, `elementwise.c:66`). One C reader of `qlean_me`: `reduce.c:318` (`over_groups_pass`).
  C calls `qlean_run` at 33 sites; 48 `qrs_*` shims take the runner as a `void (*)(void)` and `transmute` it.
- `rust/src/c.rs:15` — under `cargo test` the runner is a fake that runs three slices **in turn on one thread**. No
  unit test can see a pass that fails to spread.
- `pass.h:406-449` has no guard against two threads entering `qlean_run` at once: both write `pool->job`.

`lean.h` surface the C uses (the number is call sites over all 16 units, so header code counts once a unit):

- Inline in `lean.h`, 43 — `lean.rs` reimplements exactly these: `lean_sarray_cptr` 659, `lean_sarray_size` 319,
  `lean_alloc_sarray` 197, `lean_array_cptr` 77, `lean_ctor_set` 58, `lean_box` 51, `lean_alloc_ctor` 43,
  `lean_array_size` 39, `lean_dec` 29, `lean_unbox` 20, `lean_inc` 19, `lean_alloc_array` 16, `lean_string_cstr` 15,
  `lean_array_get_core` 15, `lean_ctor_get` 12, `lean_box_usize` 11, `lean_is_scalar` 10, `lean_is_exclusive` 10,
  `lean_io_result_mk_ok` 9, `lean_sarray_set_size` 7, `lean_io_result_mk_error` 6, `lean_sarray_capacity` 4,
  `lean_array_set_core` 3, `lean_to_sarray` 3, `lean_usize_to_nat` 2, `lean_string_size` 2, `lean_ptr_tag` 2,
  `lean_get_external_data` 2; once each: `lean_box_uint64`, `lean_box_uint32`, `lean_set_non_heap_header_for_big`,
  `lean_is_ctor`, `lean_ctor_num_objs`, `lean_set_st_header`, `lean_io_result_is_error`,
  `lean_io_result_get_error`, `lean_io_result_get_value`, `lean_alloc_external`, `lean_is_mt`, `lean_obj_tag`,
  `lean_unbox_usize`, `lean_array_capacity`, `lean_to_array`.
- Runtime symbols (`nm -u` of the C objects), 17: `lean_alloc_object`, `mi_malloc_small`, `lean_inc_heartbeat`,
  `lean_internal_panic_out_of_memory`, `lean_dec_ref_cold`, `lean_mk_string`, `lean_mk_io_user_error`,
  `lean_decode_io_error`, `lean_copy_byte_array`, `lean_big_usize_to_nat`, `lean_apply_1`, `lean_apply_2`,
  `lean_apply_5`, `lean_mark_mt`, `lean_mark_persistent`, `lean_register_external_class`, `lean_notify_assert`
  (asserts only; Rust needs 16).
- OS and libc beyond the 12 names `qrs.o` already leaves undefined: `open close pread fstat stat mmap munmap rename
  unlink realpath fchmod getpid dlopen dlsym dlerror __errno_location strerror strerror_r socket connect
  getaddrinfo freeaddrinfo setenv tzset localtime_r getrusage getenv sysconf syscall pthread_create pthread_detach
  pthread_mutex_lock pthread_mutex_unlock pthread_once snprintf vsnprintf fprintf fwrite exit`.
- libm: `pow sin cos tan asin acos atan exp log sqrt`.

`rt.c` defines exactly the 17 runtime symbols (plus `qlean_rt_io`); that equality becomes a gate (§2.8).

Limit of the count: 44 multi-line macros (479 lines: `MW_*` in `scan.c` 138, `sort.c` 115, `OG_*` in `reduce.c`
111, `elementwise.c` 53, `IDS_*` in `ids.h` 42) expand only inside other macros and sit in `rest`. They are loop
bodies, so class k is about 4450 lines, not 3969.

## 2. Design decisions

### 2.1 `lean.rs` — the object mirror

- One module `rust/src/lean.rs`, hand-written, unsafe allowed; nothing else names an object field. Reason: one place to
  re-verify on a toolchain bump
- `#[repr(C)]` mirrors: `Object { rc: i32, cs_sz: u16, other: u8, tag: u8 }`, `Ctor`, `Array`, `SArray`, `Str`,
  `External`, `ExternalClass`; every tag and size constant a `pub const`. Reason: 4.28 `lean.h:` `int m_rc; unsigned
  m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8` — three bit-fields in one 32-bit unit, little-endian x86-64
- The build is `LEAN_MIMALLOC` (`config.h:10`): small objects (ctor, external) go `lean_inc_heartbeat();
  mi_malloc_small(align8(sz)); cs_sz = sz`, the ctor path zeroes the last word when rounded; arrays and scalar arrays
  always call `lean_alloc_object`. Reason: `lean.h:347-402, 763, 937`; `lean_set_st_header` leaves `cs_sz` alone under
  mimalloc (`lean.h:566-574`)
- Refcount: inc `rc > 0 → rc += 1`, `rc < 0 → atomic fetch_sub`, `rc == 0 →` nothing; dec `rc > 1 → rc -= 1`, `rc != 0 →
  lean_dec_ref_cold`; exclusive `rc == 1`. Reason: `lean.h:487-512, 543-549`; multi-threaded and persistent objects
  reach kernels from Lean tasks
- Out-of-line runtime functions are called by symbol, never reimplemented. Reason: they are the 16 names `rt.c` stands
  in for; a 17th would break the Rel link, and the gate says so
- Safe types over the mirror: `B<'a>` (borrowed argument, `repr(transparent)`), `O` (owned, `Drop` = dec), `Bytes<'a>` →
  `&[u8]`, `SArr::new(elem, n)` → `&mut [u8]` then `.into()`, `Arr`, `ctor(tag, [O; N])`, `boxed(usize)`, `Io::ok/err`,
  `O::exclusive() -> Option<&mut [u8]>`. Reason: an export body then holds no pointer arithmetic; ownership errors
  become type errors
- Layout is verified by the C compiler: `c/abi.c` includes `lean.h` and `rs.h` and holds only `_Static_assert`s —
  `sizeof`/`offsetof` of each mirror, each tag constant, `LEAN_VERSION_MAJOR == 4 && LEAN_VERSION_MINOR == 28`,
  `LEAN_MIMALLOC` defined, `LEAN_OBJECT_SIZE_DELTA`, `LEAN_MAX_SMALL_OBJECT_SIZE`; lake compiles it into the library.
  Reason: a toolchain bump fails the build naming the field; no code is generated from it
- Bit-fields and inline behaviour cannot be static-asserted: gate `abi` runs `test/abi.c` (links `rt.c` + `qrs.o` built
  with feature `abi`), which calls each of the 43 inlines from `lean.h` and its Rust twin on the same objects and
  compares header bytes, sizes, results, and `rc` after inc/dec at `rc` = 1, 2, 0, −1, −2. Reason: `offsetof` of a
  bit-field is ill-formed; behaviour is the contract

### 2.2 The 260 exports

- A Rust export keeps Lean's symbol name (`qlean_sort_grade`); no Lean edit. Reason: `@[extern]` names are the interface
- Exports live in `rust/src/ffi/<file>.rs` under `#![deny(unsafe_code)]`, written with `lean::export! { fn qlean_x(a: B,
  n: usize) -> O { … } }`; the macro adds `#[allow(unsafe_code)] #[unsafe(no_mangle)] pub extern "C"`. Reason: probed on
  1.93.1 (m): `forbid(unsafe_code)` rejects `#[unsafe(no_mangle)]`; `deny` plus the macro compiles and exports. The
  export files hold no `unsafe` token
- Body shape: unpack with `lean.rs` types → one safe kernel call → pack. Reason: the kernel modules stay
  `forbid(unsafe_code)` and Lean-free
- A moved export deletes its C definition in the same commit; the `qrs_*` shim it was the only caller of is deleted too.
  Reason: no twin; the symbol gate lists what is left
- Prototype check, gate `proto`: cbindgen writes the `qlean_*` prototypes into `rs.h` (with `B`/`O` renamed to
  `lean_object *`); `cc -fsyntax-only -include c/rs.h` over each `.lake/build/ir/QLean/Kernel/*.c` fails on a
  conflicting declaration (e — L0 settles the cbindgen rename). Reason: arity and scalar types of 260 signatures are
  checked against what Lean's compiler emits, not against a hand copy

### 2.3 The thread pool

- `rust/src/pool.rs` (unsafe allowed) is a port of `pass.h:210-449`, same algorithm and constants: generation/left
  counters, `QLEAN_SPIN` 1024 then futex park, slice 0 on the caller, width from `QLEAN_THREADS` or `sched_getaffinity`,
  at most 64, split when `n·cost·wide ≥ 8388608`, fusing at 33554432. Reason: every number in that header was measured;
  a redesign would need them all again
- Threads through libc FFI: `pthread_create`, `pthread_detach`; futex, `sched_getaffinity`, `sched_yield` through
  `syscall`; `getenv`, `sysconf`. One-time start by an atomic compare-exchange, so no `pthread_mutex_*`. Reason:
  `std::thread` needs `std` (863 KB and `libgcc_s`, phase-1 §1). Raw `clone` leaves glibc's per-thread state unset, and
  `malloc` is then undefined. Five new undefined names
- No thread-local: the slice index is an argument. `pool::run(n, cost, wide, f(k, lo, hi))`, `pool::map`, `pool::slices
  -> Vec<T>` indexed by `k`. Reason: `#[thread_local]` is unstable on 1.93.1 (m). It also removes `run_slices`'
  lock-and-sort
- Transition: `pass.h`'s `qlean_run` body becomes a call to `qrs_pool_run(f, n, cost, wide, p)`; `qlean_run_c` and the C
  pool are deleted. The 33 C call sites do not change. Reason: one pool for C and Rust from the first commit
- `K1` (port `over_groups`, the only `qlean_me` reader) lands before the pool. Reason: Rust cannot set a C
  `_Thread_local`
- The runner parameter goes: the 48 `run: void (*)(void)` shim arguments and their `transmute`s are deleted, kernels
  call `pool::run`. Reason: a function pointer can carry a serial runner, and nothing shows it
- Serial is a named choice: `Par::Here` at the call site (a chain stage already inside a slice), `Par::Pool` otherwise.
  Gate `serial`: the `Par::Here` sites equal the list in `rust/SERIAL.md`, each with its reason. Reason: the serial
  sites are enumerable and reviewed
- A pass entered while another is in flight runs serially on its own thread and counts in `contended`. Reason: today
  that is a data race on `pool->job`; defined, and visible to the gate
- Always-on counters: `passes, split, declined, contended, slices, busy_ticks, wall_ticks` (`_rdtsc` around each slice
  and each split pass), read by `qrs_pool_stats`. Reason: two `rdtsc` a slice; ratios need no calibration and add no
  symbol

Gates that make lost parallelism fail (the class the perf investigation is chasing):

- **unit `pool_spreads`** — width forced to 4; four slices each record `gettid` and wait until all four are inside (2 s
  limit). A runner that runs slices in turn never fills the barrier. The `#[cfg(test)]` fake at `c.rs:15` is deleted
- **unit `pool_parts`** — for each kernel that calls the pool, a 2^24-element input must return `parts > 1` at width 4
- `spread`, per bench row, after each wave. What fails it: `bench-kernel` prints `split` and `busy_ticks / wall_ticks`
  per row. Red when: `split` is below the C pool's count for that row (baseline `/data/tmp/qrs/base/spread.tsv`, from
  P0), or `contended > 0`, or `busy/wall < 0.5 · parts` on a row with `split > 0`. Run as `env QLEAN_THREADS=8 taskset
  -c 0-7`
- **`serial`** — a new `Par::Here` not in `rust/SERIAL.md`

Limit of these gates: they see the pool, not serial work a kernel does around its pool call; that is the timing
ratio's job.

### 2.4 OS shell

- `rust/src/os.rs` (unsafe allowed): `extern "C"` declarations of the libc names of §1's table, and safe wrappers `File`
  (`Drop` = close), `Map`, `Lib` (dlopen), `errno()`, `Sock`. Reason: bytes in, bytes out for every caller
- Foreign structs (`stat`, `addrinfo`, `tm`, `rusage`) and constants (`O_*`, `PROT_*`, `MAP_*`, `RTLD_*`, `SYS_futex`,
  …) are mirrored and asserted in `c/abi.c` like the Lean objects. Reason: one mechanism for every layout Rust copies
  from a C header
- Messages are built with `core::fmt` and written with `write(2)`; `exit(1)` sites keep their text byte for byte.
  Reason: drops `snprintf`, `vsnprintf`, `fprintf`, `fwrite` from the list
- The non-heap `ByteArray` over a mapping (`own.c:254-297`, `lean_set_non_heap_header_for_big`) gets one `lean.rs`
  constructor; `Map` given to it is never unmapped. Reason: the mapping lives as long as the process, as today

### 2.5 What C stays

- **`c/abi.c`** · lines: ~80 (e) · reason: static asserts only; the layout check has to be compiled by a C compiler
- **`c/rs.h`** · lines: generated · reason: input of `abi.c` and of gate `proto`
- **`c/rt.c`** · lines: 146 · reason: open question A/B; recommended: port last as a second crate `rust/rt` →
  `rust/qrt.o`, never in the library
- **`tools/coc/coc.c`** · lines: — · reason: open question C/D; it is already broken

`pass.h`, `coc.h`, `ids.h`, `sym.h` and all fourteen `.c` files go. libm is called from Rust (`rust/src/m.rs`, ten
declarations): the Rel gate already allows libm, and a C file kept for ten calls would keep `lean.h` in the build.

### 2.6 `unsafe`

- **modules allowed `unsafe`** · phase 1 (m): `c ffi lib pod rt simd` = 2783 of 11938 lines, 23.3% (over the 20%
  go/no-go) · phase 2: `lean lib m os pod pool rt simd` (+ `ffi.rs`, `c.rs` until F3 deletes them)
- **lines holding `unsafe`** · phase 1 (m): `ffi` 702, `simd` 32, `c` 24, `pod` 19, `rt` 14 · phase 2: `ffi/*.rs`: 0.
  New go/no-go: lines holding `unsafe` ≤ 300 (e) outside `ffi.rs`
- **gate** · phase 1 (m): `grep -L 'forbid(unsafe_code)'` · phase 2: `grep -L 'forbid(unsafe_code)|deny(unsafe_code)'`
  prints the allowed list; `grep -l 'allow(unsafe_code)'` prints `lean.rs`; `grep -c unsafe rust/src/ffi/*.rs` is 0
  everywhere

### 2.7 Build

- `build.sh`: `-u` and `objcopy -G` take `qlean_*` beside `qrs_*`; feature `abi` builds the test twins into a
  separate object for `test/abi.c` only.
- lakefile: a task that empties a `.c` deletes its `target` and its `extern_lib` entry; `abi.o` is added by L0;
  the `EW_PART` split goes with `elementwise.c`. End state: `extern_lib qleankernel = #[qrs.o, abi.o]`.
- gcc flags that were per file become properties of the Rust code: `-ffp-contract=off` (`scan.c`) — Rust never
  contracts; `-fno-math-errno` — `m.rs` calls are plain calls, so `mdev`'s root uses `_mm_sqrt_pd`/`_mm512_sqrt_pd`
  from `simd.rs`; `-fno-trapping-math` — LLVM does not assume trapping.

### 2.8 Gates: what changes against phase-1 §6

- **symbols, defined** — every Lean extern is defined exactly once in `libqleankernel.a` (loop over the 260 names from
  `QLean/`, report the missing and the doubled: `nm -g --defined-only … | sort | uniq -d` empty); besides them only
  `qrs_*`, whose count may only fall
- **symbols, undefined** — `nm -u rust/qrs.o` ⊆ `rust/UNDEF.txt`: today's 12, the ten libm names, the `os.rs` names, the
  five pool names, and the Lean runtime names
- **rel** — command unchanged. Added: every `lean_*`/`mi_*` name undefined in `qrs.o` is defined in `rt.o` (`nm`), so an
  export that pulls a 17th runtime function is red before the Rel link
- **abi** — new (§2.1): `c/abi.c` compiles; `test/abi` exits 0
- **proto** — new (§2.2)
- **spread, serial** — new (§2.3)
- **unsafe** — §2.6
- **differential, Lean-level** — new harness for B tasks: the old C export (compiled from the base sha with
  `-Dqlean_x=old_qlean_x`) and the Rust one, both over `rt.c`, on random objects; compares results with `objeq` (ctor,
  array, scalar array, string, boxed), the `rc` of every argument after the call, and the live-object count
  (`rtcount.c`)

## 3. Order

```
K1 ──► P1 ─────────────────────────────────────────────┐
P0 ──► P1                                               ├─► F1 ─► F2 ─► F3
L0 ─► L1 ─► O0 ─► B1..B4                                │
L0 ─────────► B5..B35  (each after the K tasks of its lines)
K2..K26 (parallel, three at a time, no dependency on L0) ┘
```

- Leaf first: K tasks need no `lean.rs`, so they start at once and run beside L0 (opus) and P0.
- P0 (baselines) before anything changes the pool or the bench. K1 before P1 (`qlean_me`). P1 before the B wave's
  benchmark, so every ratio is read on the pool that will ship.
- L0 before any B. L1 (IO results, strings, external objects, closures, non-heap arrays) before B1–B4, B20, B21.
- A B task starts when the K tasks listed in its row are merged; then its region holds only b and w.
- F1 (headers, lakefile) after the last B; F2 (`rt.c`) and F3 (runner parameter, `c.rs`, last `qrs_*`) last.
- Benchmarks: after each merged wave, on `rust-port-0`, only the rows the wave's exports reach, three alternating
  runs. No K/B ratio is read before the open phase-1 regression (geomean 1.60) is explained: a ratio against a
  baseline with an unknown defect in it measures nothing.

## 4. Task briefs

Common protocol: phase-1 §7's, with these changes.

- Base: branch `rust-port-0`; worktree `/data/tmp/qrs/wt-<task>`, branch `rs2-<task>`; `.lake` copied from `wt0`.
- Gates: phase-1 §6 as changed by §2.8 here. Never piped, never `|| true`.
- K task, differential: phase 1's — the C function cut from the base sha against the Rust one, a few thousand
  random inputs, under `/data/tmp/qrs/<task>/`. The C adapter left behind calls `qrs_*`; nothing else in the file
  changes. If a Rust twin already exists (27 unused `qrs_*`, §1), re-point the callers and delete the C; do not
  write a second one.
- B task, differential: the Lean-level harness of §2.8 (`rust/testdata/objeq.h`, `rtcount.c`, both from L0), every
  export of the brief. Then `qlean-test`. Export files use `export!` and `lean.rs` types only; an export that needs
  a `lean.rs` function that does not exist is reported, not added.
- Reach: `sh W/rust/reach.sh W/.lake/build/bin/qlean-test -- <the brief's symbols>`; every `N` reported; `N = 0`
  is reported with the symbol, not papered over with another input.
- Rows: the rows `/data/tmp/qrs/base/rows.tsv` (P0) lists for the brief's exports; a brief with no row says so.
  Timing is deferred to the post-wave run; threshold 1.05.
- Error text stays byte for byte. Lines are those of 2a5b97f; anchor on the function names.

### Scaffold, pool, finish

- **P0** · model: sonnet · after: — · work: baselines, C untouched in behaviour: counters `passes/split/slices` in
  `pass.h:406-449` behind `qlean_pool_stats`; `bench-kernel` prints `split` per row; write
  `/data/tmp/qrs/base/spread.tsv` at `QLEAN_THREADS=8`; write `rows.tsv` (export → rows) with `reach.sh` per row filter
- **L0** · model: opus · after: — · work: `lean.rs` core (objects, arrays, scalar arrays, ctors, boxes, inc/dec, the
  mimalloc allocation paths), `export!`, `c/abi.c`, `test/abi.c`, `objeq.h`, `rtcount.c`, `build.sh`/lakefile/cbindgen
  changes, gates `abi`, `proto`, symbols, unsafe; proves the path by moving `qlean_structural_til`
  (`structural.c:1734-1738`) and `qlean_utc_offset` (`time.c:18-24`)
- **L1** · model: opus · after: L0 · work: `lean.rs` rest: `Io::ok/err`, `lean_mk_string`, `lean_decode_io_error`,
  external objects and their class (`search.c:1157-1224`), `lean_apply_n`, `lean_mark_mt/persistent`, `O::exclusive`
  with `lean_copy_byte_array`, the non-heap array over a mapping, `lean_usize_to_nat`; `abi` cases for each
- **O0** · model: sonnet · after: L1 · work: `os.rs`: the declarations and wrappers of §2.4, mirrors and constants
  asserted in `c/abi.c`; `m.rs`: the ten libm declarations; `rust/UNDEF.txt`
- **P1** · model: opus · after: P0, K1 · work: `pool.rs` (§2.3), `qrs_pool_run`, `qrs_pool_stats`; `pass.h` `qlean_run`
  → the call, C pool and `sort.c:57-59` deleted; unit `pool_spreads`, `pool_parts`; `c.rs` fake deleted and
  `run_map`/`run_slices`/`run_chain` moved onto `pool`; gate `spread` green against `spread.tsv` on every row
- **F1** · model: sonnet · after: all B · work: delete `pass.h`, `coc.h`, `ids.h`, `sym.h` and classes d, t; lakefile
  end state; rerun `inv2.py`: no class but r
- **F2** · model: sonnet · after: F1, answer A · work: `rt.c` → crate `rust/rt` over `lean.rs`, object `rust/qrt.o`;
  `BENCH.md` cc lines; Rel gate
- **F3** · model: sonnet · after: F1 · work: delete the runner parameter and `Par` plumbing left in signatures, `c.rs`,
  `ffi.rs`, unused `qrs_*`; symbols gate: defined = the Lean externs and nothing else; `rust/SERIAL.md` final

### K — kernel remnants (sonnet; lean-free; differential against the C)

`functions` are the class-k functions with a loop and the macros they expand; `reach` names the exports that call them.

- **K1** · lines: reduce.c:271-349 · functions: `over_groups` (`OG_*` macros), `over_groups_pass`, `over_groups_merge` ·
  Rust: `reduce.rs` · reach: `qlean_over_groups`
- **K2** · lines: reduce.c:69-107, 395-397, 531-545, 771-876 · functions: `md5_block`, `seg_at`, `gc_*`,
  `qlean_f32/f64_sum_src`, `over_f32/f64[_sum]`, `add_f64` · Rust: `reduce.rs` · reach: `qlean_md5`,
  `qlean_group_cells`, `qlean_over_f64`
- **K3** · lines: scan.c:174-187, 389-390, 535-562, 789-832 · functions: `sc_bits_run`, `ema_*`, `mw_sent`, `mw_seed`,
  `mw_open`, `mw_close` · Rust: `scan.rs` · reach: `qlean_scan_bits`, `qlean_mwin`
- **K4** · lines: scan.c:572-783 · functions: `mw_run` and its window macros · Rust: `scan.rs` · reach: `qlean_mwin`,
  `_bits`, `_foR`, `_alp`
- **K5** · lines: elementwise.c:140-509 · functions: `ew_val_run`, `ew_val_avx`, `ew_magic_of`, helpers; float `pow`
  through `m.rs` · Rust: `ew.rs` · reach: `qlean_ew_val`
- **K6** · lines: elementwise.c:529-568, 644-650, 665-682, 704-712 · functions: `ew_val_foR_run`, `ew_val_foR_atom_run`,
  `ew_low_zero[_foR]_run`, `ew_bitw_run` · Rust: `ew.rs` · reach: `qlean_coc_ew_val`, `qlean_ew_low_zero`,
  `qlean_ew_bitw`
- **K7** · lines: elementwise.c:782-921 · functions: `ew_cmp_ids_run`, `ew_eq_ids_run`, `ew_cmp_key_run` · Rust: `ew.rs`
  · reach: `qlean_ew_cmp_ids`, `qlean_ew_eq_ids`, `qlean_ew_cmp_ids_key`
- **K8** · lines: elementwise.c:961-1160 · functions: `ew_cmp_syms_run`, `like_*`, `fixed_*`, `all_lit`, `eq_run`,
  `copy_run` · Rust: `ew.rs` · reach: `qlean_ew_like_syms`, `qlean_ew_fixed_hits`, `qlean_ew_cmp_syms`
- **K9** · lines: elementwise.c:1350-1378, 1503-1660 · functions: `ew_mon_run` (nine maps through `m.rs`), `ew_serial`,
  `ew_widen_stage`, `ew_decode/alp/ids/pack/encmeta/encpack_run` · Rust: `ew.rs` · reach: `qlean_ew_mon`,
  `qlean_ew_chain`
- **K10** · lines: elementwise.c:1699-1785, 1962-2032 · functions: `ew_stage_worker`, `ew_chain_build`, `ew_stats_run`,
  `ew_stats_sum` · Rust: `ew.rs` · reach: `qlean_ew_chain[_enc]`, `qlean_stats_chain`
- **K11** · lines: sort.c:83-267 · functions: `key_at`, `keys_blk_foR`, `keys_blk_alp`, `kwin_*`, `range_foR` · Rust:
  `kwin.rs`, `key.rs` · reach: `qlean_sort_grade_foR`
- **K12** · lines: sort.c:426-468, 547-622 · functions: `hist_find`, `select_keys`, `xr_floor`, `xrank_src` · Rust:
  `sort.rs` · reach: `qlean_sort_middle`, `qlean_sort_xrank`
- **K13** · lines: sort.c:716-898 · functions: `radix_values`, `take_graded`, `sort_values` · Rust: `sort.rs` · reach:
  `qlean_sort_values`
- **K14** · lines: sort.c:949-1449 · functions: `group_probe`, `group_prefetch`, `part_dedup`, `group_find`, `ids_run`,
  `dedup`, `gather` · Rust: `group.rs` · reach: `qlean_sort_distinct`, `qlean_sort_group`
- **K15** · lines: sort.c:1486-1501, 1723-1770, 1802-1817, 1892-1915 · functions: `buckets`, `distinct_fill[_alp]`,
  `keys_gather_foR`, `parted_of` · Rust: `sort.rs` · reach: `qlean_sort_group`, `qlean_sort_distinct_foR`,
  `qlean_sort_parted`
- **K16** · lines: sort.c:1973-1989, 2085-2104, 2152-2157, 2340-2504 · functions: `asc_syms`, `syms_at`, `ids_slots`,
  `guid_cmp`, `ts_*` · Rust: `sort.rs` · reach: `qlean_sort_ascending_syms`, `qlean_sort_thin_sweep`
- **K17** · lines: search.c:113-118, 198-221, 355-369, 693-714, 1233-1259, 1324-1326, 1422-1443 · functions:
  `coc_may_hold64`, `remap_ids_run`, `sym_search`, `ix_slot`, `ix_alloc`, `ix_room` · Rust: `search.rs` · reach:
  `qlean_search_remap_ids`, `qlean_index_hash_build`
- **K18** · lines: structural.c:72-252, 469-503 · functions: bit helpers, `rows_at`, `reverse_foR_move`,
  `concat_foR_move`, `concat_foR` · Rust: `structural.rs` · reach: `qlean_structural_concat_foR`
- **K19** · lines: structural.c:702-722, 1025-1029, 1113-1118, 1158-1162, 1279-1284, 1343-1354; ids.h:40-224 ·
  functions: `next_byte`, `copy_piece`, `reverse_run`, `shift_run`, `translate_run`, `ids_place`; `id_put`, `ids_fill`,
  `ids_bitcopy`, `IDS_*` macros · Rust: `structural.rs`, `ids.rs` · reach: `qlean_structural_concat_ids`, `_reverse`,
  `_shift`
- **K20** · lines: structural.c:1442-1727 · functions: `symtab_fit`, `sd_*`, `symdict_concat` (the Lean-object helpers
  `symdict_hold/probe`, `sd_part`, `take_ids0` stay for B32) · Rust: `sym.rs` · reach: `qlean_symdict_concat`
- **K21** · lines: structural.c:1740-1743, 1777-1864, 1924-1941, 1979-1996 · functions: `til_fill`, `str_*`,
  `mmu_block`, `transpose_cells`, `transpose_rows` · Rust: `structural.rs` · reach: `qlean_structural_string_digits`,
  `_mmu`, `_transpose`
- **K22** · lines: structural.c:2115-2333 · functions: `amx_*`, `amix_run`, `amend_index` · Rust: `structural.rs` ·
  reach: `qlean_structural_amend_index`
- **K23** · lines: structural.c:2499-2651 · functions: `fsc_*`, `fsx_check` · Rust: `structural.rs` · reach:
  `qlean_structural_scatter_for`, `_alp`
- **K24** · lines: coc.c:138-448, 764-816 · functions: `src_run`, `src_pass`, `coc_enc_*`, `qlean_coc_encode_src`,
  `fill_*`, `move_pack`, `vv_fill`, `scale_fill` · Rust: `enc.rs`, `cocops.rs` · reach: `qlean_coc_encode`,
  `qlean_coc_val_vv`, `qlean_coc_scale`
- **K25** · lines: coc.h:516-985 · functions: `res_unpack_agrees`, `res_count_lt`, `coc_count_lt[_blk]`, `coc_any_null`,
  `alp_offsets`, `cocf_load_range`, `alp_thresh`, `cocf_min/max/mask_lt` · Rust: `coc.rs`, `alp.rs`, `res.rs` · reach:
  `qlean_coc_unpack_agrees`, `qlean_alp_min`, `qlean_alp_mask_lt`
- **K26** · lines: coc.h:1046-1765; own.c:173-250; sym.h:69-115 · functions: `coc_popcount`, `alp_fin_blk`, `coc_get`,
  `coc_load_run`, `coc_shift_bounds`, `coc_vv_ok`, `coc_scale_ok`, `alp_meta_*`, `alp_patch_pack_*`; `own_check`;
  `sym_eq/cmp/slices/hash` · Rust: `coc.rs`, `alp.rs`, `own.rs`, `sym.rs` · reach: `qlean_coc_popcount`,
  `qlean_own_map`, `qlean_sort_grade_syms`

`zip.c`'s class k (`zfail`, `zlib_load`, `zcur_*`, `zat`) depends on `dlopen` and moves with B4.

### B — the Lean boundary (sonnet; each moves every b, w and o function of its lines to `rust/src/ffi/<file>.rs`)

`x` = exports in the lines (m), `*` = those with a loop of their own (m), `h` = boundary helpers (m).

- **B1** · lines: time.c, env.c, interp.c · x: 5 · *: 2 · h: 0 · after: O0 · notes: `tzset`, `localtime_r`, `setenv`,
  `getrusage`; `qlean_stop` (class d) is deleted
- **B2** · lines: handle.c:1-99 · x: 5 · *: 3 · h: 0 · after: O0 · notes: `socket`, `connect`, `getaddrinfo`; `Io`
  results
- **B3** · lines: own.c:1-297 · x: 3 · *: 2 · h: 1 · after: O0, K26 · notes: plus class o `own_write_all`,
  `own_replace`; the non-heap array over `mmap`
- **B4** · lines: zip.c:1-413 · x: 4 · *: 1 · h: 1 · after: O0 · notes: plus class o `zopen`, `zpread`, `zsym`, `zclose`
  and class k `zlib_load`, `zat`, `zcur_*`, `zfail`
- **B5** · lines: reduce.c:1-545 · x: 8 · *: 4 · h: 0 · after: L0, K1, K2
- **B6** · lines: reduce.c:546-891 · x: 3 · *: 1 · h: 0 · after: L0, K2 · notes: deletes `reduce.c`
- **B7** · lines: scan.c:1-437 · x: 8 · *: 5 · h: 0 · after: L0, K3
- **B8** · lines: scan.c:438-925 · x: 4 · *: 3 · h: 0 · after: L0, K3, K4 · notes: deletes `scan.c`
- **B9** · lines: coc.c:1-760 · x: 10 · *: 0 · h: 12 · after: L0, K24 · notes: `cocf_view`, `mask_alloc`,
  `coc_enc_pair`; `coc.h:1182-1209` `coc_view`, `mk_pair`, `mk_some[_pair]` become `lean.rs` uses
- **B10** · lines: coc.c:761-1015 · x: 18 · *: 1 · h: 1 · after: B9, K25, K26 · notes: deletes `coc.c`
- **B11** · lines: elementwise.c:1-634 · x: 4 · *: 0 · h: 0 · after: L0, K5, K6
- **B12** · lines: elementwise.c:635-959 · x: 7 · *: 2 · h: 0 · after: L0, K6, K7
- **B13** · lines: elementwise.c:960-1336 · x: 6 · *: 3 · h: 0 · after: L0, K8
- **B14** · lines: elementwise.c:1337-1561 · x: 6 · *: 0 · h: 0 · after: L0, K9
- **B15** · lines: elementwise.c:1562-1896 · x: 2 · *: 0 · h: 0 · after: L0, K9, K10 · notes: `qlean_ew_chain`,
  `qlean_ew_chain_enc` (80 lines)
- **B16** · lines: elementwise.c:1897-2146 · x: 3 · *: 3 · h: 0 · after: L0, K10 · notes: deletes `elementwise.c` and
  its three `EW_PART` targets
- **B17** · lines: search.c:1-342 · x: 5 · *: 4 · h: 2 · after: L0, K17 · notes: `opnd_of`, `opnd_ids`
- **B18** · lines: search.c:343-688 · x: 20 · *: 7 · h: 1 · after: B17
- **B19** · lines: search.c:689-1145 · x: 21 · *: 4 · h: 2 · after: B17
- **B20** · lines: search.c:1146-1414 · x: 8 · *: 5 · h: 4 · after: L1, B17 · notes: index cells: external class,
  finalizer, `lean_apply_n`; `pthread_once` → an atomic once
- **B21** · lines: search.c:1415-1626 · x: 8 · *: 8 · h: 0 · after: B20 · notes: deletes `search.c`
- **B22** · lines: sort.c:1-415 · x: 8 · *: 0 · h: 2 · after: L0, K11 · notes: `order_dense`, `order_foR`
- **B23** · lines: sort.c:416-916 · x: 6 · *: 1 · h: 0 · after: L0, K12, K13
- **B24** · lines: sort.c:917-1474 · x: 1 · *: 0 · h: 1 · after: L0, K14 · notes: `qlean_sort_distinct`, `empty_bounds`
- **B25** · lines: sort.c:1475-1856 · x: 13 · *: 2 · h: 3 · after: L0, K14, K15 · notes: `group_answer`, `group_ids_of`,
  `pair_ids`
- **B26** · lines: sort.c:1857-2157 · x: 9 · *: 1 · h: 1 · after: L0, K15, K16
- **B27** · lines: sort.c:2158-2556 · x: 11 · *: 4 · h: 3 · after: L0, K16 · notes: deletes `sort.c`
- **B28** · lines: structural.c:1-467 · x: 2 · *: 0 · h: 8 · after: L0, K18 · notes: `count_at`, `row_at`, `alp_view`,
  `take_first`, `sarray_room`, 17 class-w fills; `sym.h:29-51`, `ids.h:34-36, 99-105`
- **B29** · lines: structural.c:468-680 · x: 11 · *: 1 · h: 0 · after: B28
- **B30** · lines: structural.c:681-1015 · x: 12 · *: 7 · h: 0 · after: B28, K19
- **B31** · lines: structural.c:1016-1337 · x: 12 · *: 8 · h: 0 · after: B28, K19
- **B32** · lines: structural.c:1338-1752 · x: 4 · *: 1 · h: 4 · after: B28, K19, K20 · notes: `symdict_hold`,
  `symdict_probe`, `sd_part`, `take_ids0`
- **B33** · lines: structural.c:1753-2102 · x: 5 · *: 5 · h: 0 · after: B28, K21
- **B34** · lines: structural.c:2103-2481 · x: 6 · *: 4 · h: 0 · after: B28, K22
- **B35** · lines: structural.c:2482-2665 · x: 2 · *: 0 · h: 0 · after: B28, K23 · notes: deletes `structural.c`

Sums: 260 exports, 92 with a loop. A B task moves such a loop into the kernel module as a safe function, never
into the export file. Appendix A, not the counts, is the anchor.

Totals: 69 tasks — 66 sonnet (P0, O0, F1–F3, K1–K26, B1–B35), 3 opus (L0, L1, P1). One opus at a time, three sonnet.

### Three briefs in full

**P1 (opus) — the pool.** After P0, K1. Fills `rust/src/pool.rs`. Anchors: `pass.h:210-212` `qlean_futex_wake`,
`218-230` `qlean_await`, `234-238` `qlean_slice`, `248-261` `qlean_priv_*`, `284-290` `qlean_cpu_count`, `292-310`
`qlean_pool_thread`, `314-332` `qlean_threads`, `355-357` `qlean_worth_splitting`, `398` `qlean_worth_fusing`,
`406-449` `qlean_run`; `sort.c:57-59`; `c.rs:13-96, 160-198`. Decisions of §2.3 are fixed. C side: `qlean_run`'s
body becomes `return qrs_pool_run(f, n, cost, wide, p);`, the pool object, `qlean_me`, `QLEAN_POOL_OWNER` and
`qlean_run_c` are deleted, `QLEAN_RUN_C` names `qrs_pool_run`. Gates: all of §2.8; unit `pool_spreads` and
`pool_parts`; `spread` over the whole of `bench-kernel 10000000 5` against `/data/tmp/qrs/base/spread.tsv`; the
hand-off cost — a worker that returns at once, width 4, 8, 16, 24, minimum of six launches — within 1.2 of the C
figures measured the same day (`pass.h` records 360, 230, 460, 490 ns). Reach: `qrs_pool_run` on the rows of
`rows.tsv` with `split > 0`. Report `nm -u rust/qrs.o` against `rust/UNDEF.txt`.

**K1 (sonnet) — `over_groups`.** Fills `reduce::over_groups` and its slice and merge. Anchors: `reduce.c:271-349`
(`OG_LOOP`, `OG_VERBS`, `OG_CLASSES`, `over_groups` 306-310, `over_groups_pass` 314-319, `over_groups_merge`
339-349); `ids.h` `IDS_WIDTHS`, `id_at`. The Rust slice takes its block index as an argument (`c::run_slices`
today), never `qlean_me`. C side: `qlean_over_groups` (358-386) calls one new `qrs_over_groups`; the three
functions and the `OG_*` macros are deleted. Differential: `/data/tmp/qrs/K1/diff.c`, the C cut at 2a5b97f against
`qrs_over_groups`, every verb × class × id width 1–64 bits, sizes that give 1 and several slices. Reach:
`qrs_over_groups` on the rows `rows.tsv` lists for `qlean_over_groups`. After merge `grep -c qlean_me c/` is 0
outside `pass.h`.

**B5 (sonnet) — `reduce.c:1-545` to `rust/src/ffi/reduce.rs`.** After L0, K1, K2. Exports: `qlean_md5`,
`qlean_over_sv`, `qlean_over_bytes`, `qlean_over_groups`, `qlean_over_segments`, `qlean_bit_rows_over`,
`qlean_over_groups_float`, `qlean_over_segments_float` (appendix A, `reduce.c:114-515`). Each is `export!` over
`lean.rs` types and one call into `reduce.rs`; the loops of the four `*`-marked exports become safe functions in
`reduce.rs`. C side: those definitions and the `qrs_*` shims only they called are deleted. Differential: the
Lean-level harness of §2.8, every export, 2000 random inputs each, arguments shared (`rc` 2) and exclusive (`rc`
1). Gates: all; `proto` over `.lake/build/ir/QLean/Kernel/Reduce.c`. Reach: the eight symbols under `qlean-test`.

## 5. Risks and open questions

Risks:

- The phase-1 regression (R/C geomean 1.60, rows 3–9 times slower at equal CPU) is unexplained. P0 and P1 give it a
  gate; until it is closed, no K or B ratio is evidence.
- Class k is larger than the brief assumed (3969 lines). K is 26 of the 69 tasks.
- Ownership: `proto` checks types, not `@&`. A borrowed argument decremented, or an owned one leaked, is caught
  only by the harness's `rc` and live-count comparison — it must run on every export.
- Objects from Lean tasks have `rc < 0`; persistent ones `rc == 0`. Both paths are in `test/abi.c` or they are
  untested.
- `scan.c` is built without `-fno-trapping-math` because if-conversion on the carried chain cost 4× (`sums xf`
  2.00 ms against 0.47). LLVM may if-convert the Rust loop too: K3/K4 read that row first.
- gcc expands the width macros into 60–80 KB specialised loops; the Rust generics must monomorphise the same
  cases, or the row is slower with correct answers.
- Each task pays two relinks of 547 precompiled modules, about 5 min each: about 12 hours of builds over 69 tasks.
- The Lean-level harness links the old C export beside the new object; the old C calls `qrs_*` shims the task
  deletes. The harness therefore links the base sha's `qrs.o` with its `qrs_*` renamed (`objcopy --prefix-symbols`
  on a copy); L0 has to prove this on its two exports, or B has no differential.
- A symbol defined in both C and Rust may link without an error; the `uniq -d` line of the symbols gate is the check.
- A Lean toolchain bump stops the build in `c/abi.c`. That is intended and costs one L0-sized review per bump.

Decided (user, 2026-11-16): A, D, E, G, I, K, M — every recommendation. The phase-1 regression is explained and
fixed by P3 (`0fddfcf`, geomean 1.60 → 1.05: a serial O(n) assert in `run_map`, and per-element `memcpy` /
out-of-line width accessors); per-kernel rows above 1.05 are P4/P5.

Open questions (answered above):

1. `c/rt.c`: **A** port to a crate `rust/rt` at the end (recommended: no C then includes `lean.h` but `abi.c`) /
   **B** leave it in C.
2. `tools/coc/coc.c`, already not compiling: **C** repair it to call `qrs_*` / **D** delete it with the 36
   functions of `coc.h` only it reaches (recommended).
3. K and B: **E** separate waves as planned — K is checked without Lean, 69 tasks / **F** one task a region does
   both — about 43 tasks, larger briefs, differential only through Lean objects.
4. libm from Rust: **G** allow the ten names in `qrs.o` (recommended) / **H** keep a ten-line C shim.
5. Pool counters reach the bench through: **I** one new Lean extern `qlean_pool_stats` (recommended) / **J** an
   environment variable that prints them at exit, no Lean edit.
6. Two Lean threads in the pool at once: **K** the second runs serially and is counted (recommended) / **L** it
   waits for the pool.
7. P1's place: **M** before the B wave (recommended, the investigation needs its gates) / **N** last, as the
   phase-1 design implied.

## Appendix A — segments (generated by `inv2.py`; `file:lo-hi class n=functions fl=function lines names`)

`*` after an export: it has a loop of its own.

```
coc.c:95-107 b n=2 fl=9 cocf_view mask_alloc
coc.c:138-163 k n=1 fl=26 src_run
coc.c:165-179 w n=6 fl=8 coc_enc_for_meta coc_enc_for_pack coc_enc_alp_meta coc_enc_alp_pack src_copy src_bits
coc.c:181-279 k n=5 fl=92 src_pass coc_enc_open coc_enc_plan coc_enc_layout coc_enc_free
coc.c:281-284 b n=1 fl=4 coc_enc_pair
coc.c:286-341 k n=3 fl=49 qlean_coc_encode_src fill_open fill_taken
coc.c:343-352 w n=1 fl=10 fill_at
coc.c:354-357 k n=1 fl=4 fill_close
coc.c:362-386 w n=1 fl=25 move_meta
coc.c:389-413 k n=1 fl=25 move_pack
coc.c:415-436 b n=2 fl=21 qlean_coc_encode_move qlean_coc_encode_fill
coc.c:438-448 k n=2 fl=8 dense_at coc_encode_dense
coc.c:455-690 b n=15 fl=88 qlean_coc_encode_raw qlean_coc_encode_i16 qlean_coc_encode_i32 qlean_coc_encode_i64
    qlean_coc_decode_i16 qlean_coc_decode_i32 qlean_coc_decode_i64 qlean_coc_block_start qlean_coc_encode
    qlean_coc_encode_below qlean_coc_decode qlean_coc_over qlean_coc_count_lt qlean_coc_any_null qlean_coc_mask_cmp
coc.c:705-708 w n=1 fl=4 shift_fill
coc.c:710-760 b n=2 fl=36 qlean_coc_shift qlean_coc_mask_cmp_vv
coc.c:764-772 k n=1 fl=9 vv_fill
coc.c:781-810 b n=3 fl=18 coc_val_vv qlean_coc_val_vv qlean_coc_val_prior
coc.c:812-816 k n=1 fl=5 scale_fill
coc.c:822-917 b n=10 fl=31 qlean_coc_scale qlean_coc_unpack_agrees qlean_coc_popcount qlean_coc_some_bit*
    qlean_alp_encode_f64 qlean_alp_encode_below_f64 qlean_alp_encode_f32 qlean_alp_encode_below_f32 qlean_alp_decode_f64
    qlean_alp_decode_f32
coc.c:933-942 w n=1 fl=10 alp_f64_blk
coc.c:943-953 b n=1 fl=11 qlean_alp_sum_f64
coc.c:961-964 k n=1 fl=4 alp_f32_blk
coc.c:965-1015 b n=5 fl=28 qlean_alp_sum_f32 qlean_alp_gather qlean_alp_min qlean_alp_max qlean_alp_mask_lt
coc.h:98-101 d n=1 fl=4 bit_at
coc.h:137-154 k n=1 fl=18 coc_meta_view
coc.h:160-169 d n=1 fl=10 coc_blocks
coc.h:174-228 k n=5 fl=24 coc_offsets exc_layout for_layout coc_frame coc_res_end
coc.h:236-236 w n=1 fl=1 coc_std
coc.h:240-438 k n=14 fl=97 coc_attach coc_exc coc_blk_nexc xalloc xcalloc sk_dense_width sk_avail cap_for hash_shift
    coc_alloc width_for lane_width res_get res_get_in
coc.h:441-489 d n=2 fl=18 res_put res_unpack_scalar
coc.h:500-510 w n=3 fl=5 res_unpack res_vcmp res_pack
coc.h:516-554 k n=1 fl=39 res_unpack_agrees
coc.h:559-561 w n=1 fl=3 coc_lanes
coc.h:563-585 t n=2 fl=20 coc_free coc_new
coc.h:590-590 w n=1 fl=1 res_count_lt8
coc.h:594-594 t n=1 fl=1 coc_sum_blk
coc.h:608-608 d n=1 fl=1 coc_sums_ok
coc.h:609-609 t n=1 fl=1 coc_sums_drop
coc.h:610-618 w n=6 fl=6 coc_sum coc_prd coc_any coc_all coc_min coc_max
coc.h:622-697 k n=5 fl=47 res_count_lt coc_count_lt_blk coc_count_lt coc_any_null coc_blk_allnul
coc.h:703-703 w n=1 fl=1 coc_shift
coc.h:763-894 k n=9 fl=82 alp_layout alp_offsets cocf_meta_view cocf_load_range cocf_lanes cocf_load_blk exc_val alp_dec
    alp_thresh
coc.h:905-917 t n=1 fl=13 cocf_sum
coc.h:925-947 k n=2 fl=22 cocf_min cocf_max
coc.h:953-967 t n=1 fl=15 cocf_count_lt
coc.h:969-985 k n=1 fl=17 cocf_mask_lt
coc.h:994-1024 t n=2 fl=30 cocf_add_const cocf_free
coc.h:1046-1164 k n=3 fl=32 coc_popcount alp_fin_blk coc_load_blk_at
coc.h:1182-1209 b n=4 fl=21 coc_view mk_pair mk_some mk_some_pair
coc.h:1283-1283 w n=1 fl=1 coc_sumnul
coc.h:1326-1331 k n=1 fl=6 coc_get
coc.h:1335-1421 d n=5 fl=59 coc_prefetch coc_one_width coc_get_w res_cmp2 coc_cmp2_res
coc.h:1448-1556 k n=4 fl=82 coc_load_run coc_shift_bounds coc_vv_ok coc_scale_ok
coc.h:1567-1569 t n=3 fl=9 pack_block_u8 pack_block_i16 pack_block_i32
coc.h:1567-1569 w n=1 fl=3 pack_block_i64
coc.h:1607-1609 t n=3 fl=9 encode_meta_blk_u8 encode_meta_blk_i16 encode_meta_blk_i32
coc.h:1607-1609 w n=1 fl=3 encode_meta_blk_i64
coc.h:1616-1618 d n=4 fl=12 encode_meta_exc_blk_u8 encode_meta_exc_blk_i16 encode_meta_exc_blk_i32
    encode_meta_exc_blk_i64
coc.h:1620-1646 t n=12 fl=84 encode_meta_u8 encode_meta_i16 encode_meta_i32 encode_meta_i64 encode_pack_u8
    encode_pack_i16 encode_pack_i32 encode_pack_i64 encode_u8 encode_i16 encode_i32 encode_i64
coc.h:1652-1654 w n=4 fl=12 decode_blk_u8 decode_blk_i16 decode_blk_i32 decode_blk_i64
coc.h:1656-1658 t n=4 fl=12 decode_u8 decode_i16 decode_i32 decode_i64
coc.h:1674-1674 k n=2 fl=2 bits_f64 bits_f32
coc.h:1690-1694 t n=2 fl=10 alp_meta_blk_f64 alp_meta_blk_f32
coc.h:1700-1702 w n=2 fl=6 dat_blk_f64 dat_blk_f32
coc.h:1704-1711 k n=2 fl=16 alp_meta_at_f64 alp_meta_at_f32
coc.h:1715-1717 w n=2 fl=6 alp_exc_at_f64 alp_exc_at_f32
coc.h:1720-1724 k n=2 fl=10 alp_meta_exp_f64 alp_meta_exp_f32
coc.h:1743-1746 w n=2 fl=8 alp_patch_blk_f64 alp_patch_blk_f32
coc.h:1751-1765 k n=2 fl=30 alp_patch_pack_f64 alp_patch_pack_f32
coc.h:1770-1809 t n=4 fl=76 alp_pack_blk_f64 alp_pack_blk_f32 encode_f64 encode_f32
elementwise.c:140-509 k n=14 fl=109 ew_unsupported ew_width ew_dbl ew_flt ew_bits64 ew_bits32 ew_ord64 ew_ord32
    ew_outside_long ew_fdiv ew_magic_of ew_fdiv_magic ew_val_avx ew_val_run
elementwise.c:511-523 b n=1 fl=13 qlean_ew_val
elementwise.c:529-568 k n=2 fl=36 ew_val_foR_run ew_val_foR_atom_run
elementwise.c:573-634 b n=3 fl=34 qlean_coc_ew_val_atom qlean_coc_ew_val qlean_ew_cmp
elementwise.c:644-650 k n=1 fl=7 ew_low_zero_run
elementwise.c:652-660 b n=1 fl=9 qlean_ew_low_zero
elementwise.c:665-682 k n=1 fl=18 ew_low_zero_foR_run
elementwise.c:685-695 b n=1 fl=11 qlean_coc_low_zero
elementwise.c:704-712 k n=1 fl=9 ew_bitw_run
elementwise.c:714-772 b n=2 fl=35 qlean_ew_bitw qlean_ew_rank_pair*
elementwise.c:817-851 k n=2 fl=19 ew_cmp_ids_run ew_eq_ids_run
elementwise.c:856-891 b n=2 fl=35 qlean_ew_eq_ids qlean_ew_cmp_ids
elementwise.c:912-921 k n=1 fl=10 ew_cmp_key_run
elementwise.c:926-959 b n=1 fl=34 qlean_ew_cmp_ids_key*
elementwise.c:961-1160 k n=10 fl=138 ew_cmp_syms_run like_parse like_hit like_match fixed_items fixed_width all_lit
    eq_run copy_run fixed_scan
elementwise.c:1162-1336 b n=6 fl=146 qlean_ew_fixed_hits qlean_ew_ssr* qlean_ew_like_syms* qlean_ew_translate_syms*
    qlean_ew_cmp_syms qlean_ew_bit
elementwise.c:1361-1378 k n=1 fl=18 ew_mon_run
elementwise.c:1380-1392 b n=1 fl=13 qlean_ew_mon
elementwise.c:1397-1400 w n=1 fl=4 ew_mon_fill
elementwise.c:1409-1473 b n=4 fl=31 qlean_coc_ew_mon_enc qlean_coc_ew_mon qlean_ew_floor qlean_ew_cast
elementwise.c:1503-1507 k n=1 fl=5 ew_serial
elementwise.c:1511-1533 w n=3 fl=19 ew_run_chain ew_val_stage ew_cmp_stage
elementwise.c:1537-1552 k n=1 fl=16 ew_widen_stage
elementwise.c:1554-1561 b n=1 fl=8 qlean_ew_widen
elementwise.c:1592-1660 k n=6 fl=32 ew_decode_run ew_alp_run ew_ids_run ew_pack_run ew_encmeta_run ew_encpack_run
elementwise.c:1663-1697 w n=5 fl=26 ew_mon_stage ew_floor_stage ew_bit_stage ew_cast_stage ew_tick_stage
elementwise.c:1699-1785 k n=2 fl=78 ew_stage_worker ew_chain_build
elementwise.c:1790-1896 b n=2 fl=80 qlean_ew_chain qlean_ew_chain_enc
elementwise.c:1962-2009 k n=1 fl=48 ew_stats_run
elementwise.c:2013-2023 w n=1 fl=11 ew_stats_pass
elementwise.c:2026-2032 k n=1 fl=7 ew_stats_sum
elementwise.c:2038-2145 b n=3 fl=102 qlean_stats_chain* qlean_guid_eq* qlean_guid_fill*
env.c:14-16 b n=1 fl=3 qlean_setenv
env.c:23-27 d n=1 fl=5 qlean_stop
env.c:35-39 b n=1 fl=5 qlean_peak_rss
handle.c:28-99 b n=5 fl=59 qlean_handle_open* qlean_handle_connect* qlean_handle_write* qlean_handle_close
    qlean_handle_error
ids.h:19-25 k n=2 fl=4 id_width ids_bytes
ids.h:34-36 b n=1 fl=3 ids_avail
ids.h:40-94 k n=3 fl=46 id_at id_put ids_fill
ids.h:99-105 b n=1 fl=7 ids_alloc
ids.h:201-224 k n=1 fl=24 ids_bitcopy
ids.h:230-263 d n=2 fl=14 ids_slice_elems ids_unpack16
interp.c:20-27 b n=1 fl=8 qlean_str_key7*
interp.c:33-33 k n=1 fl=1 xorshift32
interp.c:35-47 b n=1 fl=13 qlean_draw_guids*
own.c:75-77 b n=1 fl=3 own_errno
own.c:83-123 o n=2 fl=37 own_write_all own_replace
own.c:126-130 b n=1 fl=5 qlean_file_replace
own.c:132-136 d n=1 fl=5 get_le
own.c:140-164 b n=1 fl=25 qlean_own_write*
own.c:173-250 k n=1 fl=78 own_check
own.c:254-297 b n=1 fl=44 qlean_own_map*
pass.h:210-449 p n=11 fl=124 qlean_futex_wake qlean_await qlean_slice qlean_priv_stride qlean_priv_alloc qlean_cpu_count
    qlean_pool_thread qlean_threads qlean_worth_splitting qlean_worth_fusing qlean_run
reduce.c:69-107 k n=1 fl=39 md5_block
reduce.c:114-205 b n=3 fl=40 qlean_md5* qlean_over_sv* qlean_over_bytes
reduce.c:306-349 k n=3 fl=22 over_groups over_groups_pass over_groups_merge
reduce.c:358-386 b n=1 fl=29 qlean_over_groups
reduce.c:395-397 k n=1 fl=3 seg_at
reduce.c:399-515 b n=4 fl=57 qlean_over_segments qlean_bit_rows_over qlean_over_groups_float* qlean_over_segments_float*
reduce.c:531-545 k n=3 fl=15 gc_avg_float gc_avg_int gc_real
reduce.c:548-579 b n=1 fl=32 qlean_group_cells*
reduce.c:771-876 k n=10 fl=88 qlean_f32_sum_src dense_f32_blk over_f32_sum qlean_over_f32_sum qlean_f64_sum_src
    dense_f64_blk add_f64 over_f64 qlean_over_f64_sum over_f32
reduce.c:878-890 b n=2 fl=12 qlean_over_f64 qlean_over_f32
rt.c:13-146 r n=20 fl=101 rt_die mi_malloc_small lean_alloc_object lean_internal_panic_out_of_memory lean_inc_heartbeat
    lean_notify_assert rt_free lean_dec_ref_cold lean_copy_byte_array lean_mk_string lean_mk_io_user_error
    lean_decode_io_error qlean_rt_io lean_big_usize_to_nat lean_apply_1 lean_apply_2 lean_apply_5
    lean_register_external_class lean_mark_mt lean_mark_persistent
scan.c:144-163 b n=2 fl=19 qlean_scan_any_null qlean_scan
scan.c:174-187 k n=1 fl=14 sc_bits_run
scan.c:192-360 b n=4 fl=102 qlean_scan_bits qlean_scan_foR* qlean_scan_alp* qlean_scan_avg*
scan.c:389-390 k n=2 fl=2 ema_mul ema_add
scan.c:392-437 b n=2 fl=34 qlean_scan_ema* qlean_scan_ema_v*
scan.c:506-513 w n=1 fl=8 mw_out_width
scan.c:535-832 k n=5 fl=84 mw_sent mw_seed mw_run mw_open mw_close
scan.c:836-925 b n=4 fl=77 qlean_mwin qlean_mwin_bits* qlean_mwin_foR* qlean_mwin_alp*
search.c:53-53 w n=1 fl=1 coc_exc_within
search.c:113-118 k n=1 fl=6 opnd_dense
search.c:122-136 b n=2 fl=13 opnd_of opnd_ids
search.c:141-175 w n=2 fl=4 opnd_blk kind_of
search.c:181-189 b n=1 fl=9 qlean_search_find_scalar
search.c:198-221 k n=2 fl=18 coc_needle coc_may_hold64
search.c:238-342 b n=4 fl=89 qlean_coc_find_scalar* qlean_coc_span* qlean_coc_rows_eq* qlean_search_mask_by_ids*
search.c:355-369 k n=1 fl=15 remap_ids_run
search.c:371-688 b n=21 fl=218 qlean_search_remap_ids* qlean_search_find_ids* qlean_search_longs_by_ids*
    qlean_search_below_bits* qlean_search_run_starts_ids qlean_match_bytes* qlean_coc_match* qlean_match_syms* search
    qlean_search_find_vec qlean_search_member_vec qlean_coc_find_vec qlean_coc_member_vec qlean_search_find_ids_vec
    qlean_search_member_ids_vec qlean_search_find_bit qlean_search_find_bit_vec qlean_search_bin_bits
    qlean_search_member_bits qlean_search_where_bits qlean_search_find_sym_scalar
search.c:693-714 k n=1 fl=22 sym_search
search.c:718-1145 b n=23 fl=257 qlean_search_find_sym_vec qlean_search_match_ids* qlean_search_match_syms_ids*
    qlean_search_find_sym_ids_vec* qlean_search_member_sym_vec qlean_search_bin qlean_bin_operands
    qlean_search_bin_wide* qlean_coc_bin qlean_search_bin_ids qlean_search_find_sorted qlean_search_member_sorted
    qlean_coc_find_sorted qlean_coc_member_sorted bin_rows qlean_search_bin_rows qlean_coc_bin_rows run_starts
    qlean_search_run_starts qlean_coc_run_starts qlean_search_run_starts_syms qlean_search_run_starts_bits
    qlean_index_register
search.c:1157-1162 k n=1 fl=6 ixcell_finalize
search.c:1164-1169 b n=1 fl=6 ixcell_foreach
search.c:1173-1175 k n=1 fl=3 ixcell_register
search.c:1177-1224 b n=4 fl=37 ixcell_alloc qlean_ixcell_new qlean_ixcell_ready qlean_ixcell_extend
search.c:1233-1252 k n=2 fl=19 ix_slot ix_alloc
search.c:1255-1257 b n=1 fl=3 ix_rows
search.c:1259-1259 k n=1 fl=1 ix_shift
search.c:1262-1317 b n=2 fl=52 qlean_index_hash_build* qlean_index_hash_find*
search.c:1324-1326 k n=1 fl=3 ixs_at
search.c:1328-1414 b n=4 fl=77 ixs_of qlean_index_hash_build_syms* qlean_index_hash_find_syms* qlean_index_by_ids*
search.c:1422-1443 k n=1 fl=22 ix_room
search.c:1447-1626 b n=8 fl=152 qlean_index_hash_extend* qlean_index_hash_extend_syms* qlean_index_splice*
    qlean_index_pick* qlean_index_unedit* qlean_index_first_clean* qlean_index_unedit_rows* qlean_index_rows*
sort.c:57-59 p n=1 fl=3 qlean_run_c
sort.c:83-132 k n=4 fl=34 sk_write_width rank32 rank64 key_at
sort.c:135-139 w n=1 fl=5 keys_of
sort.c:145-267 k n=9 fl=78 key_flip keys_blk_foR keys_blk_alp kwin_blk kwin_miss kwin_init kwin_new kwin_at range_foR
sort.c:276-322 w n=4 fl=7 ksrc_blk ksrc_range sk_digit grade_keys
sort.c:332-335 b n=1 fl=4 qlean_sort_ascending
sort.c:339-345 k n=1 fl=7 foR_kind
sort.c:346-415 b n=9 fl=51 qlean_sort_ascending_foR qlean_sort_invert order_dense qlean_sort_grade qlean_sort_ranks
    order_foR qlean_sort_grade_foR qlean_sort_grade_lane qlean_sort_ranks_foR
sort.c:426-468 k n=2 fl=41 hist_find select_keys
sort.c:473-500 w n=1 fl=28 middle_of
sort.c:504-540 b n=3 fl=31 qlean_sort_middle qlean_sort_middle_foR qlean_sort_bits_sorted*
sort.c:547-622 k n=2 fl=53 xr_floor xrank_src
sort.c:626-641 b n=2 fl=14 qlean_sort_xrank qlean_sort_xrank_foR
sort.c:716-898 k n=3 fl=112 radix_values take_graded sort_values
sort.c:906-916 b n=1 fl=11 qlean_sort_values
sort.c:949-1238 k n=3 fl=45 group_probe group_prefetch part_dedup
sort.c:1262-1269 w n=1 fl=8 range_of
sort.c:1279-1449 k n=4 fl=136 group_find ids_run dedup gather
sort.c:1452-1474 b n=2 fl=20 qlean_sort_distinct empty_bounds
sort.c:1486-1501 k n=1 fl=16 buckets
sort.c:1506-1711 b n=12 fl=153 qlean_sort_group group_answer group_ids_of qlean_sort_group_ids pair_ids
    qlean_sort_group_ids_pair qlean_sort_group_ids_pair_ids qlean_sort_rank_slices* qlean_sort_group_sizes
    qlean_sort_group_lasts qlean_sort_id_longs qlean_sort_seg_ids*
sort.c:1723-1734 k n=1 fl=12 distinct_fill
sort.c:1736-1750 b n=1 fl=15 qlean_sort_distinct_foR
sort.c:1760-1770 k n=1 fl=11 distinct_fill_alp
sort.c:1772-1790 b n=1 fl=19 qlean_sort_distinct_alp
sort.c:1802-1817 k n=1 fl=16 keys_gather_foR
sort.c:1820-1856 b n=2 fl=36 qlean_sort_group_foR qlean_sort_group_ids_foR
sort.c:1892-1915 k n=1 fl=24 parted_of
sort.c:1917-1947 b n=3 fl=20 qlean_sort_parted qlean_sort_parted_foR qlean_sort_grade_syms
sort.c:1973-1989 k n=1 fl=17 asc_syms
sort.c:1992-2080 b n=5 fl=51 qlean_sort_ascending_syms qlean_sort_ascending_ids qlean_sort_parted_syms*
    qlean_sort_grade_ids qlean_sort_sorted_ids
sort.c:2085-2104 k n=1 fl=20 syms_at
sort.c:2107-2137 b n=2 fl=20 empty_syms qlean_sort_distinct_syms
sort.c:2152-2157 k n=1 fl=6 ids_slots
sort.c:2161-2336 b n=10 fl=131 ids_heads qlean_sort_distinct_ids qlean_sort_group_ids_syms id_groups_of
    qlean_sort_id_groups pair_ids_narrow qlean_sort_parted_ids qlean_sort_intern_syms qlean_sort_group_syms
    qlean_sort_grade_guid
sort.c:2340-2346 k n=1 fl=7 guid_cmp
sort.c:2348-2402 b n=3 fl=44 qlean_sort_ascending_guid* qlean_sort_parted_guid* qlean_sort_sym_offs*
sort.c:2406-2504 k n=8 fl=82 ts_alloc ts_key ts_dom ts_lt ts_sort ts_set ts_group ts_free_at
sort.c:2511-2556 b n=1 fl=46 qlean_sort_thin_sweep*
structural.c:56-56 d n=1 fl=1 bit_set
structural.c:61-67 b n=1 fl=7 zeroed_bits
structural.c:72-117 k n=5 fl=36 bits64_at or_bits copy_bits set_bits bitrev64
structural.c:123-159 b n=3 fl=21 count_at row_copy row_at
structural.c:163-252 k n=3 fl=62 rows_at reverse_foR_move concat_foR_move
structural.c:282-359 w n=16 fl=68 rev_fill cycle_fill shift_fill cat_fill cat_fill_alp rev_fill_alp cycle_fill_alp
    shift_fill_alp cat_hint rev_hint cycle_hint shift_hint cat_ints rev_ints cycle_ints shift_ints
structural.c:362-389 b n=3 fl=19 alp_view take_first sarray_room
structural.c:392-395 w n=1 fl=4 cat_take
structural.c:414-467 b n=3 fl=47 concat_foR_append qlean_structural_reverse_foR qlean_structural_concat_foR
structural.c:469-503 k n=1 fl=35 concat_foR
structural.c:510-680 b n=11 fl=102 qlean_structural_concat_alp* qlean_structural_cycle_foR qlean_structural_shift_foR
    qlean_structural_reverse_alp qlean_structural_cycle_alp qlean_structural_shift_alp qlean_structural_all_below
    qlean_structural_gather qlean_structural_gather_foR qlean_structural_gather_foR_idx qlean_structural_gather_bits
structural.c:702-722 k n=2 fl=18 next_byte copy_piece
structural.c:724-1015 b n=12 fl=225 qlean_structural_split* qlean_structural_longs_of* qlean_structural_spread*
    qlean_structural_expand* qlean_structural_gauss_jordan* qlean_structural_complement* qlean_structural_rows_of
    qlean_structural_gather_syms qlean_structural_gather_ids qlean_structural_gather_ids_foR
    qlean_structural_reverse_ids* qlean_structural_cycle_ids
structural.c:1025-1029 k n=1 fl=5 reverse_run
structural.c:1031-1094 b n=3 fl=54 qlean_structural_reverse qlean_structural_reverse_segs*
    qlean_structural_reverse_bits*
structural.c:1113-1118 k n=1 fl=6 shift_run
structural.c:1120-1149 b n=2 fl=26 qlean_structural_shift qlean_structural_shift_bits
structural.c:1158-1162 k n=1 fl=5 translate_run
structural.c:1170-1274 b n=5 fl=78 qlean_structural_trim_bounds* qlean_structural_translate qlean_structural_cycle_bits*
    qlean_structural_concat* qlean_structural_concat_bits*
structural.c:1279-1284 k n=1 fl=6 enum_at
structural.c:1292-1337 b n=2 fl=38 qlean_structural_enum_ids* qlean_structural_enum_ids_for*
structural.c:1343-1354 k n=1 fl=12 ids_place
structural.c:1363-1402 b n=1 fl=40 qlean_structural_concat_ids*
structural.c:1442-1452 k n=1 fl=11 symtab_fit
structural.c:1456-1479 w n=2 fl=16 symtab_build symtab_fork
structural.c:1486-1534 k n=6 fl=39 sd_free sd_alone sd_mine sd_find sd_spare sd_put
structural.c:1538-1549 b n=2 fl=11 symdict_hold symdict_probe
structural.c:1551-1551 k n=1 fl=1 symdict_drop
structural.c:1553-1589 b n=3 fl=24 sd_part qlean_symdict_concat take_ids0
structural.c:1591-1727 k n=1 fl=137 symdict_concat
structural.c:1734-1738 b n=1 fl=5 qlean_structural_til
structural.c:1740-1743 k n=1 fl=4 til_fill
structural.c:1750-1752 b n=1 fl=3 qlean_structural_til_foR
structural.c:1777-1864 k n=5 fl=47 str_len str_one str_blk_count str_count_run str_write_run
structural.c:1870-1901 b n=1 fl=32 qlean_structural_string_digits*
structural.c:1924-1941 k n=1 fl=18 mmu_block
structural.c:1954-1974 b n=1 fl=21 qlean_structural_mmu*
structural.c:1979-1996 k n=2 fl=12 transpose_cells transpose_rows
structural.c:1998-2102 b n=3 fl=92 qlean_structural_transpose* qlean_structural_untranspose* qlean_structural_cross*
structural.c:2115-2333 k n=13 fl=180 atomic_min_size amx_hi amx_read amx_mark amx_wcount amx_wfill amix_run amx_isdup
    amx_dcount amx_dfill amx_pfill amx_scan amend_index
structural.c:2335-2481 b n=6 fl=119 qlean_structural_amend_rounds qlean_structural_amend_index qlean_structural_scatter*
    qlean_structural_scatter_ids* qlean_structural_scatter_syms* qlean_structural_amend_compact*
structural.c:2499-2651 k n=8 fl=137 fsc_patch fsc_kept fsc_exc fsc_load fsc_meta fsc_pack fsx_check fsc_scatter
structural.c:2653-2662 b n=2 fl=9 qlean_structural_scatter_for qlean_structural_scatter_alp
sym.h:29-51 b n=3 fl=18 off_at sym_at sym_count
sym.h:69-83 k n=2 fl=11 sym_eq sym_cmp
sym.h:90-92 w n=1 fl=3 sym_msort
sym.h:97-115 k n=2 fl=16 sym_slices sym_hash
sym.h:137-147 d n=1 fl=11 sym_packs
time.c:18-24 b n=1 fl=7 qlean_utc_offset
zip.c:61-70 k n=1 fl=10 zfail
zip.c:72-101 o n=2 fl=16 zpread zsym
zip.c:105-135 k n=1 fl=31 zlib_load
zip.c:139-210 o n=2 fl=71 zclose zopen
zip.c:222-240 k n=2 fl=18 zcur_close zcur_open
zip.c:243-293 w n=1 fl=51 zload
zip.c:295-317 k n=1 fl=23 zat
zip.c:321-413 b n=5 fl=78 zio_error qlean_zip_head qlean_zip_size qlean_zip_bytes* qlean_zip_parts
```
