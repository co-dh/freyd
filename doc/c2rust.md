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

## Conclusion

"c2rust first" covers only the I/O-shaped files c2rust accepts, where Rust brings no speed gain; for the AVX kernels
there is nothing to start from. Recommendation: options A + C of `doc/rust-vs-c-kernels.md` — keep the C under
ASan/UBSan and fuzzing, write new code (csv/txt readers and writers) in Rust.
