# c2rust trial on qlean's C kernels

Question: can qlean's C (`/home/dh/repo/qlean/c`, 21,170 lines) move to Rust by running c2rust first and then
removing the `unsafe` parts one function at a time?

Answer: no. c2rust handled 1 of the 3 files tried. The hot AVX kernels give it nothing to start from, and the one
file it did translate became all-`unsafe` Rust with the same speed as the C.

Branch `c2rust-trial` in qlean (worktree `/data/tmp/c2rust/wt`, HEAD 62cddac, not pushed). Logs and benchmark
output: `/data/tmp/c2rust/`. As committed, the branch links the Rust `own.o`; to go back to C set
`target own.o pkg : System.FilePath := kernelObj "own" pkg` in the lakefile.

## Measured

### Tooling

- c2rust 0.22.1 from crates.io does not build against clang 23:
  `use of deleted function 'const clang::Type* clang::TagDecl::getTypeForDecl() const'`. Git master 5f197024 builds.
- Its output compiles only on nightly-2023-04-15 (it calls `core::ptr::from_exposed_addr_mut` and
  `core::intrinsics::atomic_xadd_seqcst`) with c2rust's own bitfields crate. On stable 1.91.1 with bitfields 0.20
  it gives 11 errors, among them `` proc-macro derive panicked: `""` is not a valid identifier `` on `lean_object`.

### Transpile

| file     | C lines | result                                                                                   |
|----------|---------|------------------------------------------------------------------------------------------|
| own.c    | 410     | translated                                                                               |
| zip.c    | 453     | OOM-killed by the kernel at 21 GB RSS; perf: all time in `convert_function_inner`        |
|          |         | (`DFExpr::next` 50% inclusive, `hash_one`, `contains_node`)                              |
| reduce.c | 1,084   | `Unsupported type Vector(…)` for `__m512`, `__m512d`, `__m512i`, `__v16sf`, …; then       |
|          |         | OOM-killed at 13 GB RSS                                                                  |

Both OOM runs went without `scripts/cap`. The likely cause, inferred and not proven, is the AVX intrinsics and the
macro expansion from `coc.h`.

### own.c in Rust

- 1,910 lines of Rust from 410 lines of C: 63 `unsafe extern "C" fn`, 127 `.offset(` calls, about 404 raw-pointer
  dereferences.
- `lean.h` came across as 43 private copies of `lean_*` inline functions; `lean_alloc_object`, `mi_malloc_small`
  stay extern imports.
- Built `no_std` with an aborting panic handler and a `rust_eh_personality` stub, partial-linked with `ld -r` into
  `rust/own_rs.o` under the same symbols (`qlean_own_map`, `qlean_own_write`, `qlean_file_replace`). Text 290 KB
  against C's 20 KB.
- `qlean-test db` passes ("all suites passed"): 39 own-format round trips, overwrite and corruption-message cases,
  and the comparison against q.
- Each kernel swap rebuilds all 547 precompiled-module jobs, about 5 min per test cycle.

### Speed

`tools/bench-own.lean`, 10^7 elements, median µs, runs in the order Rust, C, Rust, C:

| column         | write Rust | write C    | map Rust | map C |
|----------------|------------|------------|----------|-------|
| `til 1e7`      | 666, 1115  | 1438, 1086 | 7, 9     | 9, 7  |
| `1e7?100`      | 271, 315   | 520, 388   | 6, 7     | 10, 7 |
| `0.25*til 1e7` | 1098, 1670 | 1510, 1800 | 9, 9     | 9, 9  |

The spread between runs is larger than any C/Rust gap; own.c is bound by write and mmap. No compute kernel could be
compared, because reduce.c did not translate.

### Hand port to safe Rust

- `exc_ok` (checks the exception sections read from disk): 36 lines of C, 154 lines of c2rust output, 61 lines of
  safe Rust (32 for the function, 10 for a writer replacing `snprintf`, 2 read helpers, a 6-line C-ABI shim).
- Cost: 6 tool calls plus one 5-min rebuild and test; compiled first time; `qlean-test db` passes.
- 3 `unsafe` remain: the slice built in the shim and two calls into helpers still in c2rust output.
- `coc_meta_view` cannot be made safe alone: it returns `coc`, a struct of 13 raw pointers into the mapped file, so
  `coc` and every function reading it must change together.

### Side finding

`QLean.Kernel.SortTest` panics with `INTERNAL PANIC: out of memory` under `CAP_MEM_MB=13000` with the original C
kernel too; the failure predates the trial.

## Estimated (not measured)

- About 1,000 functions in qlean/c. At 6 tool calls each, the hand ports alone are about 6,000 tool calls, plus
  rewriting the shared pointer structs such as `coc`, plus one 5-min rebuild per kernel swap.
- The AVX code is in `coc.h` (89 intrinsic uses), `elementwise.c` (33), `reduce.c` (12), `scan.c` (9). Expect the
  same "Unsupported type Vector" or OOM; `coc.h` is included by own.c, zip.c and reduce.c.
- The "weeks" in `doc/rust-vs-c-kernels.md` §7 are an unstated unit. In tool calls: A about 300–600, B about
  10,000–20,000 (porting, AVX kernels written from scratch, tests, benchmarks), C about 100. At about 450 calls/h
  and about 18k units per call, B is tens of hours of agent time and 200–400 M units.

## Handover: how to continue the trial

Everything below is the exact command set the trial used; run from the paths given, never from `/tmp`.

### State on disk

| what                         | where                                                                            |
|------------------------------|----------------------------------------------------------------------------------|
| qlean worktree, branch       | `/data/tmp/c2rust/wt`, branch `c2rust-trial`, base e9e00e2, HEAD 62cddac         |
| short status note            | `/data/tmp/c2rust/wt/tmp/handoff.md`                                             |
| Rust crate                   | `/data/tmp/c2rust/wt/rust/` (`Cargo.toml`, `lib.rs`, `own.rs`, `build.sh`, `rust-toolchain.toml`) |
| raw c2rust output            | `/data/tmp/c2rust/out/src` (own.c), `out-zip/`, `out-reduce/` (empty: OOM)       |
| one-file compile databases   | `/data/tmp/c2rust/cc-zip/compile_commands.json`, `cc-reduce/…`                   |
| logs                         | `transpile.log`, `zip*.log`, `reduce*.log`, `zip.perf`, `test-*.log`, `bench-*.txt` in `/data/tmp/c2rust/` |
| cargo target dirs            | `/data/tmp/c2rust/target-crate` (the crate), `target-git` (c2rust itself)        |

### 1. Tool install (already done; redo only on a new machine)

```
cargo install --locked --git https://github.com/immunant/c2rust c2rust > /data/tmp/c2rust/install-git.log 2>&1
rustup toolchain install nightly-2023-04-15
```

`rust-toolchain.toml` in the crate pins the nightly. `Cargo.toml` takes `c2rust-bitfields` by path from the
git checkout (`~/.cargo/git/checkouts/c2rust-2471865f8518dc65/5f19702/c2rust-bitfields`, feature `no_std`); the
crates.io bitfields 0.20 fails on `lean_object`. If clang/LLVM dev files are missing, ask the user for
`! sudo pacman -S …`; never run sudo.

### 2. Transpile one C file

A compile database with ONE entry per file, flags copied from the lakefile's `kernelObj`:

```
[{"directory": "/data/tmp/c2rust/wt/c", "file": "zip.c",
  "arguments": ["cc", "-c", "-O3", "-march=native", "-fPIC", "-fno-trapping-math",
                "-I", "/home/dh/.elan/toolchains/leanprover--lean4---v4.28.0/include", "zip.c"]}]
```

Then, ALWAYS under the memory cap (the two uncapped runs took the machine to 21 GB and 13 GB):

```
cd /data/tmp/c2rust; env CAP_MEM_MB=8000 /home/dh/repo/freyd/scripts/cap c2rust transpile cc-zip/compile_commands.json -o /data/tmp/c2rust/out-zip --overwrite-existing > zip4.log 2>&1; echo EXIT $? >> zip4.log
```

For own.c the trial ran `c2rust transpile compile_commands.json -o /data/tmp/c2rust/out --emit-build-files
--overwrite-existing` from `wt/c`. If a file blows up, profile it with `perf record -g -o zip.perf -- <same command>`
before changing anything. Untried ideas for zip.c/reduce.c: preprocess with `-mno-avx512f` (loses the AVX
path), or split the AVX kernels out of the file so c2rust sees only the scalar part.

### 3. Put a translated file into the crate

- Copy the module from `out*/src/<file>.rs` into `wt/rust/<file>.rs` and add `pub mod <file>;` to `lib.rs`.
- `lib.rs` is `#![no_std]` with an aborting `panic_handler` and a `rust_eh_personality` stub; keep that.
- In `build.sh`, add every exported C symbol of the new file as another `-u <symbol>` to the `ld -r` line, else the
  partial link drops it.
- Build: `sh /data/tmp/c2rust/wt/rust/build.sh` (writes `wt/rust/own_rs.o`; with a second file, rename the
  output to something general, e.g. `kernels_rs.o`, and point every replaced target at it).

### 4. Link it in place of the C object

In `wt/lakefile.lean`, the replaced target becomes

```
target own.o pkg : System.FilePath := inputBinFile <| pkg.dir / "rust" / "own_rs.o"
```

and going back to C is `target own.o pkg : System.FilePath := kernelObj "own" pkg`. Remove the C file's own
`target` from `extern_lib qleankernel` only if its symbols would clash; for own.c they were replaced one for one.

### 5. Test and benchmark

```
cd /data/tmp/c2rust/wt; env CAP_MEM_MB=13000 /home/dh/repo/freyd/scripts/cap lake build > /data/tmp/c2rust/lake-N.log 2>&1; echo exit=$? >> /data/tmp/c2rust/lake-N.log
cd /data/tmp/c2rust/wt; ./.lake/build/bin/qlean-test db > /data/tmp/c2rust/test-N.log 2>&1; echo exit=$? >> /data/tmp/c2rust/test-N.log
```

- Every swap rebuilds all 547 jobs (about 5 min): run it in the background and wait with `Monitor`.
- `qlean-test` compares against live q 4.1, so it needs the licence daemon's network.
- `QLean.Kernel.SortTest` OOMs under the cap with the C kernel too; ignore it.
- Benchmark: `lake build bench-own`, copy `.lake/build/bin/bench-own` to `/data/tmp/c2rust/bench-own.<c|rs>` for
  each kernel, then run them alternately (`bench-own.rs /data/tmp/c2rust/bench/col`, then `.c`, then again) and
  compare medians; one run each is inside the noise.

### 6. Hand-port a function to safe Rust

The pattern, as done for `exc_ok` (`wt/rust/own.rs:1132-1170`):

- write `fn <name>_safe(&[u8], …) -> …` taking slices and `&mut` instead of pointers and lengths;
- keep the original `unsafe extern "C" fn <name>` as a shim that builds the slices with
  `core::slice::from_raw_parts` and calls the safe one, so the callers stay unchanged;
- rebuild (step 3), relink (step 4), run `qlean-test db` (step 5); count the `unsafe` left.

Port leaf functions first. A function returning or reading `coc` (13 raw pointers into the mapped file,
`coc.h`) cannot be ported alone: `coc` must first become a struct of slices and every reader changes with it.

### Rules for the next agent

- Work only in `/data/tmp/c2rust/wt`; do not push `c2rust-trial`; no edits in `/home/dh/repo/qlean` itself.
- Every `c2rust transpile`, `cargo build` and `lake build` goes under `scripts/cap`.
- Log each measured result into this file's tables, marking measured against estimated.

## Conclusion

"c2rust first" covers only the I/O-shaped files c2rust accepts, where Rust brings no speed gain; for the AVX kernels
there is nothing to start from. Recommendation: options A + C of `doc/rust-vs-c-kernels.md` — keep the C under
ASan/UBSan and fuzzing, write new code (csv/txt readers and writers) in Rust.
