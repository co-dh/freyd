# Rust vs C under Lean and Rel: re-evaluation (2026-11-15)

## 0. Verdict on the earlier answer

"Lean works well with C" is true and does not answer the concern. Lean's FFI is "any language that supports the C
ABI" ([reference][ffi]), so Rust is as callable as C; the earlier dismissal had no FFI ground. What is true:

- Rust removes memory-unsafety inside the kernels. It does not close the larger hole qlean already names: the Lean
  body and the native code can disagree and `#print axioms` stays silent (`/home/dh/repo/qlean/PLAN.ckernel.md:314`).
- The qlean kernels are tuned to gcc with measured flags (`/home/dh/repo/qlean/lakefile.lean:64-93`); a port changes
  the optimiser (LLVM), so every benchmark number has to be re-measured.

## 1. Facts measured today

| fact                                                         | value                                              |
|--------------------------------------------------------------|----------------------------------------------------|
| C in `/home/dh/repo/qlean/c`                                 | 21,024 lines, 266 `LEAN_EXPORT` entries            |
| lines that touch a `lean_*` API (the Lean boundary)          | 2,180 (10%); `structural.c` 538, `search.c` 430    |
| lines with AVX2/AVX-512 intrinsics                           | 143 (`coc.h` 89, `elementwise.c` 33, `reduce.c` 12) |
| in-place update on `lean_is_exclusive`                       | `structural.c:666,677,1845,2217,3008`              |
| mmap of column files, `m_rc = 0` objects                     | `own.c:361`; header layout dependence, design §3   |
| hand-written thread pool (pthread + futex)                   | `pass.h:129-219`                                   |
| `lean.h`                                                     | 3,180 lines, 545 `static inline` functions         |
| non-inline Lean symbols the kernel objects need              | 16 (`doc/rel-native-design.md:76-92`)              |
| `#guard`s in `QLean/Kernel/*Test.lean`                       | about 1,800, plus the `qlean-test` corpus against q |
| sanitizer or fuzz target in `lakefile.lean`                  | none                                               |
| `gcc -fsanitize=address,undefined -c` on `sort.c`, `search.c` | compiles unchanged (compile only, not run)         |

## 2. Q1 — Rust as the language under Lean

| item                         | state                                                                                      |
|------------------------------|--------------------------------------------------------------------------------------------|
| `lean-sys` 0.0.9             | raw bindings; the `lean.h` inlines re-written by hand / from bindgen ([docs.rs][leansys])   |
| `lean-rs-sys`, `lean-rs` 0.9.9 (2026-11-14) | maintained; aimed at embedding Lean in a Rust host; supports a window of Lean versions and fails the build on an unknown `lean.h` SHA-256 ([sys][leanrssys], [lean-rs][leanrs]) |
| lake + cargo                 | `lean4_sys` documents a `buildCargo` target feeding an `extern_lib` ([docs.rs][lean4sys]); `hashbrown4lean` is a working example ([Zulip][zulip]) |
| Lean -> Rust backend, Rust runtime | none found; Lean 4.31 notes show C-level runtime work and an LLVM 22 bump only ([notes][l431]) |
| FFI stability                | "designed for internal use ... should be considered unstable" ([reference][ffi])           |

`@[extern]` can name a Rust `extern "C"` function. What stays `unsafe` whatever the crate:

- every read of a `lean_object` header or payload (`lean_sarray_cptr`, `m_size`, `m_rc`), and the object layout
  itself, re-declared in Rust and able to drift at a toolchain bump;
- the owned/borrowed contract: `@&` is a promise in the Lean signature that no compiler checks against the Rust side;
- allocation of results and the exclusivity test for in-place update;
- a `&[u8]` over an mmapped file (truncation by another process is a fault in both languages).

A safe layer is feasible: one module turns a borrowed `ByteArray` into `&[u8]` for the call and an owned result into
a `Vec`-like writer. The 2,180 boundary lines shrink into that module; they do not become safe.

## 3. Q2 — Rust kernels behind the same extern ABI

| aspect                | finding                                                                                          |
|-----------------------|--------------------------------------------------------------------------------------------------|
| safety inside kernels | slice bounds checks turn an out-of-range read/write (a bad `foR` width, offset or count read from a mapped file) into an abort; no use-after-free; the pool's sharing is checked by `Send`/`Sync` |
| safety at boundary    | none beyond section 2; a wrong `@&` or a wrong `dec` is still silent                              |
| functional correctness | unchanged: `3*n` against a Lean `2*n` passes in Rust as in C (`PLAN.ckernel.md:314-317`)         |
| bounds checks         | free when loops are `chunks_exact`/iterators; bit-packed gather/scatter with computed indices keeps the check or goes back to `get_unchecked` (unsafe) |
| SIMD                  | `core::arch` intrinsics are stable (AVX-512 since 1.89, from memory); `std::simd` is still nightly ([docs][stdsimd]); the 143 intrinsic lines port one to one |
| autovectorisation     | gcc -> LLVM; `-fno-trapping-math`, `-ffp-contract=off`, `-fno-math-errno` choices and their measured numbers (`lakefile.lean:64-93`) must be re-derived |
| build                 | cargo `staticlib` -> `libqleankernel.a` from a lake target; `precompileModules` also needs the shared form |
| native exe            | with `panic=abort` and no extra crates, `ldd` stays libc/libm/libpthread and `nm -u` has no `lean_`; gates 1 and 2 of `rel-native-design.md:381-386` hold |
| shared header         | `tools/coc/coc.c` includes `coc.h` so the benchmark measures the shipped code (`lakefile.lean:108-110`); a port must keep one source |

## 4. Q3 — `rt.c` and the emitted code

| candidate                         | finding                                                                              |
|-----------------------------------|--------------------------------------------------------------------------------------|
| `rt.c` in Rust                    | no gain: it is 16 allocator/abort shims defining `lean_*` symbols, all unsafe by nature |
| emit Rust that calls C kernels    | no gain: every call passes raw `lean_object*`; the emitted body is one `unsafe` block |
| emit Rust over typed kernel signatures (`&Col` borrowed, `Col` owned, `Drop` = `lean_dec`) | real gain: rustc checks the emitter's last-use and hand-over placement (design §8) on every program, for all inputs. Needs the 266-entry owned/borrowed table, which the design's ABI table needs anyway |
| emit C, check the plan in Lean    | a decidable `Plan` ownership check run by `relc` gives the same static guarantee with no second toolchain, and can be proved; ASan + LSan on the emitted exe inside gate 3 checks the C that was actually produced |

Recommendation for the native backend: keep `rt.c` and emitted C for stage 1a (in progress, depends on the unchanged
`libqleankernel.a`), add the Lean-side ownership check and an ASan build of gate 3. Emitting Rust becomes worth
reopening only if option B lands, because only then are there typed signatures to emit against.

## 5. Q4 — trusting the C without changing language

| approach                             | precedent at this scale                                              | fit here                       |
|--------------------------------------|----------------------------------------------------------------------|--------------------------------|
| Lean body as spec + differential test | qlean today: about 1,800 `#guard`s and the q corpus                  | in place; samples inputs only  |
| ASan/UBSan/LSan build of the kernels | standard practice; compiles unchanged here                           | cheap, not done yet            |
| fuzzing malformed encoded columns    | standard for parsers (libFuzzer, AFL)                                | targets `own.c`, `zip.c`, `coc` decode: the bytes-from-disk code |
| Fil-C (memory-safe C compiler)       | used on real C programs ([fil-c.org](https://fil-c.org), not re-checked today) | a stronger dynamic check for the test run; not for the shipped binary |
| CN / VST / Frama-C WP                | CN: pKVM buddy allocator, a few hundred lines ([POPL'23][cn]); seL4 about 9k lines of C at about 20 proof lines per line (from memory) | no precedent for 21k lines with intrinsics and bit-packing; out of reach |
| CompCert                             | verified compiler, no vectorisation                                  | removes compiler trust only and gives up the speed the design is built on |
| Low*/KaRaMeL: verified DSL -> C      | HACL* past 100k verified lines, vectorised code included ([paper][hacl]) | the only large precedent; nothing equivalent exists for Lean; a research project |
| Aeneas: safe Rust -> Lean 4          | Plonky3 field arithmetic verified; fails on raw-pointer code ([RV][rvbinder], [arXiv][aeneasrep]) | the one route that could prove a kernel equal to its Lean body; needs safe Rust first, and is immature for SIMD loops |

## 6. Q5 — C -> Rust conversion tools

| tool                   | what it gives                                                                                     |
|------------------------|---------------------------------------------------------------------------------------------------|
| c2rust                 | compiles-and-runs Rust that is "unsafe and unidiomatic"; ships a nightly-pinned `refactor` and an LLM `postprocess` that "can introduce errors" ([README][c2rust]) |
| Laertes, CROWN, CRustS | post-passes on c2rust output; CROWN retypes pointers by ownership analysis ([arXiv][crown]); each lifts a minority of pointers, numbers not re-checked |
| C2SaferRust (2025)     | LLM over c2rust output: raw pointers down by up to 38%, unsafe code by up to 28% ([arXiv][c2safer]) |
| C2RustXW (2026-03)     | unsafe usage down to 5.75%; project-level semantic correctness 78.87% ([arXiv][xw])               |
| SACTOR (ACL 2026)      | 85% success for interface-preserving unsafe Rust, 52% for idiomatic, on CRUST-Bench ([arXiv][sactor]) |
| ORBIT (2026-04)        | agentic; 24 CRUST-Bench programs, 91.7% pass tests, 0.06% unsafe lines ([arXiv][orbit])            |
| CRUST-Bench            | 100 repos with safe-Rust interfaces; best single-shot model solved 15 ([arXiv][crust])            |
| DARPA TRACTOR          | benchmark public (2 batteries, 3 milestone projects by 2026-09; correctness, safety, idiomaticity, performance); no performer results found ([arXiv][tractor]) |

How the 21k lines would fare:

- c2rust would expand the macros (`EW_PART` makes three objects from one file, `pass.h` generics), inline the
  `lean.h` accessors into every file, and emit near-100% unsafe Rust. That is worse than the C: same risk, less readable.
- The LLM pipelines report on small self-contained programs with their own tests; none has SIMD kernels, a foreign
  runtime header or a performance gate. Their 50–90% success rates do not transfer.
- The asset that makes a port tractable is qlean's own: every entry has a Lean body and `#guard`s. An agent
  re-writing one family in safe Rust against those gates is the realistic method; a converter adds nothing to it.

## 7. Options (costs are estimates in agent-weeks, not measurements)

| option | what                                                              | cost                         | buys                                                      | breaks / risks                                   |
|--------|-------------------------------------------------------------------|------------------------------|-----------------------------------------------------------|--------------------------------------------------|
| A      | keep C; ASan/UBSan kernel build under all `#guard`s and the corpus; fuzz the column readers; `Plan` ownership check in Lean; ASan in gate 3 | about 800 lines, 1–2 weeks   | detection of memory errors on every tested input; a static check of the emitter's `inc`/`dec` | nothing; no guarantee on untested inputs         |
| B      | Rust kernels behind the same `@[extern]` names, one family at a time, each gated by its `#guard`s, the corpus and the benchmarks | about 21k lines, 10–16 weeks | static memory safety for the roughly 90% of lines off the boundary; opens typed emit (section 4) and Aeneas (section 5) | cargo in the build; all tuning re-measured; boundary and intrinsics stay unsafe; `lean.h` layout copied; collides with stage 1a if started now |
| C      | Rust for new code only: stage 2 csv/txt readers and writers, later kernels; existing C stays under A | 0 extra lines, cargo setup about 0.5 week | new parsers of untrusted text are safe from the start; no growth of the C | two languages for good; old 21k unchanged        |
| D      | verified route: proofs of the C (CN/VST) or a Lean DSL extracting C | unbounded                    | functional correctness, the only option that gives it     | no precedent at this scale; not a plan           |

Recommendation: A now, then a B pilot, with C as the rule for new code.

- A is needed under every other option: the sanitizer build and the fuzzers are the oracle a port is checked against.
- B pilot: port `own.c` + `zip.c` (863 lines, the code that reads bytes from disk) and one hot family (`reduce.c`,
  1,084 lines, 12 intrinsic lines). Decide B from two measurements: benchmark ratio against the C, and the share of
  lines left in `unsafe`. About 2 weeks. Start after stage 1a has linked against the unchanged `libqleankernel.a`.
- Do not run c2rust or any converter over the kernels.
- Rust does not answer "can't trust them 100%": it removes one bug class. Trust in the answers still comes from the
  Lean bodies and the differential gates, in either language.

[ffi]: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/
[leansys]: https://docs.rs/lean-sys/0.0.9/lean_sys/
[leanrssys]: https://docs.rs/lean-rs-sys
[leanrs]: https://docs.rs/lean-rs/latest/lean_rs/
[lean4sys]: https://docs.rs/crate/lean4_sys/0.1.0
[zulip]: https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Help.20with.20FFI.20to.20Rust.html
[l431]: https://lean-lang.org/doc/reference/latest/releases/v4.31.0/
[stdsimd]: https://doc.rust-lang.org/std/simd/index.html
[cn]: https://www.cl.cam.ac.uk/~cp526/popl23.html
[hacl]: https://ar5iv.labs.arxiv.org/html/2102.01644
[rvbinder]: https://runtimeverification.com/blog/verifying-linux-rust-code-from-binder-to-lean4
[aeneasrep]: https://arxiv.org/abs/2605.30106
[c2rust]: https://github.com/immunant/c2rust
[crown]: https://arxiv.org/abs/2303.10515
[c2safer]: https://arxiv.org/abs/2501.14257
[xw]: https://arxiv.org/abs/2603.28686
[sactor]: https://arxiv.org/abs/2503.12511
[orbit]: https://arxiv.org/abs/2604.12048
[crust]: https://arxiv.org/abs/2504.15254
[tractor]: https://arxiv.org/abs/2609.25121
