# Rel architecture review

Read-only review of `/home/dh/repo/freyd/leetq/LeetQ/Rel` at `7d6fac3` (2026-11-14), against the layer picture in
`/home/dh/repo/freyd/doc/rel-architecture.typ`. No `.lean` file was edited and nothing was built: every number below
is a line count, an index query or a source read; build-time effects are stated as module counts, not seconds.

Caveat on the index: `/home/dh/repo/freyd/.lake/build/refactor-index.db` was written at 18:36, four hours before
HEAD. It has no `Lang/BitsSpec*` and no `KernelWF/RazeRowN` (rel-130, rel-131). Every "no user" claim was therefore
re-checked against the source where it matters, and the one false positive found (`bitRowsOver_spec`, used by
`BitsSpec`) is excluded. Re-run `./scripts/lean-refactor index` before acting on a deletion list.

## Sizes

| part                                              | lines  | share |
|---------------------------------------------------|--------|-------|
| `KernelWF/*`, 51 files (kernel specs)             | 18,049 | 40 %  |
| `Rep*.lean`, 23 files (plain `rep_op`)            | 11,368 | 25 %  |
| `Lang/*` (1,942 of the lines are `BitsSpec*`)     | 7,245  | 16 %  |
| `CRel*.lean`, 8 files (`rep_opC`, `CRel`)         | 2,866  | 6 %   |
| `Alg.lean`                                        | 1,466  | 3 %   |
| `Code.lean`                                       | 1,405  | 3 %   |
| `Core`, `ValEq`, `AC3`, `AlgTest`, `Programs/*`   | 2,767  | 6 %   |
| total, 128 files                                  | 45,166 |       |

Proof text (KernelWF + Rep + CRel + BitsSpec) is 34,225 lines, 76 % of the tree. The run path (Core, Code, Alg, the
AC3 defs, Lang without BitsSpec/Calc/tests) is about 6,500.

## Ranked proposals

| #  | proposal                                      | saves / removes                 | cost                 | owner |
|----|-----------------------------------------------|---------------------------------|----------------------|-------|
| 1  | Discharge `hat` with the existing `hat_all`   | unproved premise of 49 theorems | 1 import             | this  |
| 2  | Take the proofs off the run path's imports    | `Eval`: 90 imports, 12 needed   | move 55 lines        | other |
| 3  | Thread the ok-bit through `ev`                | the bit is computed by no run   | 70 call sites        | other |
| 4  | Delete theorems with no user                  | about 1,560 lines               | re-index, delete     | mixed |
| 5  | Compare `Bits.run?` with `TP.table` in tests  | C-against-C boundary check      | about 10 lines       | other |
| 6  | `Ck` writer for the bit; drop `CRel.<op>`     | 787 lines, 124 hand `&&`        | every twin and proof | mixed |
| 7  | One theorem per op (23 plain into `rep_opC`)  | about 400 lines                 | per-op proof edits   | this  |
| 8  | 2-part raze read-back from `raze_rowN`        | up to 500 of 814 lines          | needs 7 first        | this  |
| 9  | `==` on one coding instead of two             | half of each equality's coding  | about 10 lines       | this  |
| 10 | Keep codes across ops (measure first)         | 32 recoding sites               | needs approval       | other |

Owner: `this` is the session that owns `Alg`/`Rep*`/`CRel*`/`KernelWF`; `other` is the session that owns
`Code.lean`, `Lang/*`, `AC3.lean`, `Programs/*`. The top five are 1–5. Details follow in the same order.

## 1. `hat` is already proved; 49 theorems still assume it

- `hat` is the hypothesis "`razeTo` of two atom parts lists the first part then the second, under `RazeFits`". It is
  spelled out as a five-line binder in `rep_unionC` (`CRel.lean`) and as a `local notation "hatOK"` copied into
  four files: `CRelEst.lean:20`, `CRelLoop.lean:20`, `AC3.lean:85`, `Lang/BitsSpec.lean:18`.
- 49 indexed theorems take it: `CRelFold` 19, `CRelLoop` 11, `CRelEst` 8, `AC3` 3, `CRel` 2, the rest in
  `KernelWF/Raze*`. `rep_tableC` and so `bits_table` take it too. `rel-done-tasks.md` rows 107–131 keep listing it
  as "kept: `hat` … a correctness gap, not capacity".
- `KernelWF/RazeFoR.lean:215` has `theorem hat_all` with exactly that statement and no extra premise, and
  `raze_row_full` (line 240) is `raze_row` with it applied. Their only users are `rep_union_full`,
  `rep_junc_full`, `cat_row`, `rep_cons`.
- Cause: `CRel.lean` imports `KernelWF.RazeRowAll`, which is upstream of `RazeFoR`
  (`RazeRowAll → RazeEnc → … → RazeParts → RazeFoR`), so `hat_all` was not in scope when the twins were written.
- Change: `CRel.lean` imports `KernelWF.RazeFoR`; `rep_unionC` calls `raze_row_full`; the `hat` binder and the four
  notation copies go, and every caller drops one argument. No cycle: `RazeFoR` does not reach `CRel*`.
- Removes: the last hypothesis that is not a capacity bit or a step spec from every `rep_*C` and from `bits_table`.
  About 60 lines of binders and notation. Cost: mechanical, one build of the CRel files, `BitsSpec*`, `AC3`.

## 2. The evaluator imports the whole proof tree

Transitive `LeetQ` imports, computed from the 289 `import LeetQ.*` lines:

| module               | imports | of them `KernelWF` | of them `Rep*`/`CRel*` |
|----------------------|---------|--------------------|------------------------|
| `LeetQ.Rel.Alg`      | 6       | 3                  | 0                      |
| `LeetQ.Rel.Lang.Elab`| 9       | 3                  | 0                      |
| `LeetQ.Rel.Lang.Bits`| 66      | 45                 | 13                     |
| `LeetQ.Rel.AC3`      | 82      | 49                 | 28                     |
| `LeetQ.Rel.Lang.Eval`| 90      | 49                 | 28                     |
| `LeetQ.Rel.Lang.Test`| 93      | 49                 | 28                     |

Two edges carry all of it:

- `Lang/Bits.lean:2` imports `CRelRel` for four calls in `TP.tableC` (`r.comp`, `.inter`, `.union`, `.leftDiv`,
  lines 42–47). Each is `compC`/`interC`/`unionC`/`leftDivC` from `Alg` plus an `&&`.
- `Lang/Eval.lean:2` imports `AC3` for `acFix`, `Revise`. In `AC3.lean` the definitions are lines 15–68 (namespace
  `Alg`, 55 lines, using only `Alg`'s twins); lines 83–500 are theorems that need `Rep*` and `CRel*`.

Change: move `AC3.lean` 15–68 to a definitions module that imports `Alg` only; write `TP.tableC` on `Alg`'s twins
(`rep_tableC` in `BitsSpec` then rewrites with `rep_compC` instead of `CRel.rep_comp`). `Lang.Eval` then imports about
12 `LeetQ` modules. An edit to any `KernelWF`/`Rep*`/`CRel*` proof stops rebuilding `Eval`, the eight `Lang/Test*`
files and `Programs/*`, whose `#guard`s run the programs.

Same kind, one line: `Code.lean:20` imports `QLean.Eval.Dyad` (5,020 lines, itself importing `Kernel.Index`,
`Prim.Builtin`, `Eval.Num`, `Eval.Lit`). The index has no dependency of `Code`, `Core` or `Alg` on any `QLean.Eval.*`
constant; in all of `LeetQ` the only ones are `QLean.Eval.nullAtom` (`KernelWF/PickSpec`) and `QLean.Eval.identical`
(`AlgTest`). Import the defining module of `nullAtom` where it is used instead, so that an edit to q's dyads does
not rebuild all 128 modules. Check by building `LeetQ.Rel.Code` alone.

Cost: small. Ownership: `AC3.lean`, `Lang/*`, `Code.lean` belong to the other session.

## 3. No run computes the ok-bit

- `rel-architecture.typ` says "a run either reports `ok = false`, or its answer is the relation the allegory
  defines". `Lang/Eval.lean` does not do that: `ev` (lines 95–209) calls the plain op at every constructor
  (`r ≫ s`, `pair`, `Alg.cat D`, `foldOn`, `loopOn`, `(fixOn …).1`, `(acFix …).1`), each of which is `(opC ..).1`.
  `EvM` is `StateM Memo`, `Out` (line 425) has no ok field, `Bits.run` (`Bits.lean`) falls back to `p.table`, which
  is `p.tableC.rel` with the bit dropped.
- What is checked at run time is only what sits behind qlean's `need`, which calls `stop` (`QLean/Kernel/Need.lean`).
  The other conjuncts of a bit — `Vals.fitsN`, the `codesC` bit, the decided `2^63` bounds — are evaluated by no
  run. Where one is false the op still answers a relation, no `rep_*C` theorem applies to it, and nothing reports it.
- So the 2,866 lines of `CRel*` and the capacity half of `Rep*` are theorems about values the language does not
  produce. The twins were built for exactly this: `estOnC`, `thinOnC`, `foldOnC`, `loopOnC`, `mergeOnC`, `thinLOnC`,
  `fixOnC` take a bit-returning callback, which is what `fun P => Id.run ((ev … Q P).run' {})` becomes.
- Change: `EvM := StateM (Memo × Bool)`, one helper `ck : Rel A B × Bool → EvM (Rel A B)` that `&&`s the bit into
  the state, `pure (op x)` → `ck (opC x)` at about 70 sites, callbacks return the pair, `Out` gains `ok`, `run`
  reports it. Independent of proposal 6.
- Follow-on, larger: with the bit in place, `TP.den` (7 constructors, `BitsSpec.lean:26`) extended to `Tm` gives the
  statement the architecture note claims, `ok → rep (ev t) = den t`. Until it exists, which `rep_*` theorems matter
  is decided by nothing; `Lang/Eval.lean` has 82 definitions and no theorem.

## 4. Theorems with no user

From the index (theorems no other `LeetQ` declaration depends on; headline theorems of ops are leaves by nature
and are not listed).

| group                                  | lines |
|----------------------------------------|-------|
| plain `rep_op` superseded by `rep_opC` | 598   |
| `*_fits` family of rel-104             | 167   |
| `KernelWF`                             | 507   |
| `Code.lean`, `Core.lean`               | 292   |

The declarations, each with its line count:

- Superseded `rep_op`: `rep_map` 78, `rep_length` 77, `rep_P` 77, `rep_arrUnion` 56, `rep_E_list` 52,
  `Arr.rep_sum` 48, `rep_setify` 41, `rep_fold` 35, `rep_merge` 34, `foldRows_rep` 23, `rep_ordered` 21,
  `rep_tic` 16, `rounds_closed` 16, `rep_loop` 14, `rep_suffix` 10.
- `*_fits`: `comp_fits` 55, `union_fits` 25, `leftDiv_join_fits` 21, `antiJoin_fits` 19, `ran_fits` 18,
  `inter_fits` 13, `outl_fits` 9, `pickFits_mod_of_reads` 7.
- `KernelWF`: `razeColumn_wf` 146, `razeFits_of_reads` 96, `razeColumn_count` 83, `razeColumn_isSome` 51,
  `codes_prod_boolean_long_one` 42, `groupIds_code_faithful` 39, `gradeColumn_isSome` 31, `pickShared_row` 19.
- `Code.lean`, `Core.lean`: `runStarts_group` 53, `offsets_faithful` 50, `toList_answer_int` 26,
  `Arr.toList_float` 24, `Arr.dense_float` 23, `longWords_answer` 18, `floatWords_answer` 16,
  `groupIds_long_faithful` 15, and nine shorter ones.

- About 1,560 lines directly; helpers used only by these fall out in a second pass, as in rel-127 (six theorems
  deleted, net −962).
- The `*_fits` theorems were written "for `AC3.acFix_eq_fixOn`" (row 104); that theorem does not use them, and the
  bit made them unnecessary (row 106).
- `razeFits_of_reads` was the rel-101 route from `Vals.reads` to `RazeFits`; nothing took it.
- Cost: low. `Code.lean` is the other session's file. Use `scripts/lean-refactor`, not hand edits.

## 5. Testing the C-against-Lean boundary cheaply

Facts:

- qlean has about 255 `@[extern]` definitions with Lean bodies in `QLean/Kernel/*.lean`. The Rel run path (`Core`,
  `Code`, `Alg`, `Lang.Bits`) calls about 55 of them (index: `dep.dst like 'QLean.Kernel.%'` from those modules'
  definitions, without the `Ew.*` op codes and `Scan.Kind` constructors). That list, not all 255, is Rel's trust
  base, and the query regenerates it.
- The `opaque` externs are `Kernel/Index.lean` (hash index, 13), `Value.lean` `IndexCell.*` (3) and
  `Coc.unpackAgrees`. None is on Rel's path, so no Rel proof rests on a body that does not exist.
- qlean's own check is a pair per sample, `example … := by decide` against the Lean body and `#guard` against the C
  (about 1,900 lines of them in `Kernel/*Test.lean`), on hand-written inputs.

Cheapest additional check, in freyd: the language already evaluates a closed `≫`/`∩`/`∪`/`−`/`\` term two ways
through disjoint kernels — `Bits.run?` (`bitRowsOver`, `Ew.bit`, `whereBits`, `scatter…`) and `TP.table` (`join`,
`member`, `groupIds`, `gather…`). `bits_table` proves the Lean bodies agree; no test compares the two C results
(`run?`, `.table` do not occur in `Lang/Test*.lean` or `AlgTest.lean`). A test-only `Bits.run` that evaluates both
and fails on a difference, switched on for the `Lang/Test*` corpus, is about 10 lines and turns every existing
program test into a differential test of about 18 + 20 kernels.

Next cheapest, in qlean, not tried here: a command that copies an extern definition's body from the environment to
a second, compiled constant (`getConstInfoDefn`, `addAndCompile` under `<name>.model`), so a test can run model and
C on random inputs at native speed with no edit to the kernel or its proofs. It works for bodies written as folds
(for example `binBytes`); a structurally recursive body holds `brecOn` and would need the definition split by hand.

## 6. One writer for the bit, and no `CRel.<op>` layer

- Every twin threads the bit by hand: `let D := ranC P; let t := …; (r.1, D.2 && t.2 && T.2 && Q.2 && M.2 && r.2)`
  (`snocC`, `Alg.lean:1071`; `uncatC`; `deltaStepC` in `AC3.lean` with eight conjuncts; `mergeRound` with 33).
  `Alg.lean` has 124 lines with `&&`, `AC3.lean` 11. The proofs mirror it with left-nested destructuring
  (`obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hb`, `CRel.lean`).
- `CRel k v` is `Rel k v × Bool` under another name. Each op then has five declarations: `op`, `opC`, `rep_opC`,
  `CRel.op`, `CRel.rep_op`. The `namespace CRel` sections are 787 lines (CRelFold 217, CRelEst 109, CRelRel 108,
  CRelList 99, CRelLoop 94, CRelArith 70, CRelPower 58, CRel 32); in the index all 62 `CRel.<op>` and 74
  `CRel.rep_<op>` have no user outside their own file, and in the source the only users are the four calls in
  `TP.tableC` (proposal 2 removes them).
- Change: `abbrev Ck α := α × Bool` with a `Monad` instance (`bind x f = let y := f x.1; (y.1, x.2 && y.2)`), twins
  written in `do`, one `okbit` lemma `(x >>= f).2 = true ↔ x.2 = true ∧ (f x.1).2 = true`. `CRel.op R S` is then
  `do compC (← R) (← S)` and needs no definition; `fun r => (q r, true)` (four sites) is `pure ∘ q`.
- Saves 787 lines and the hand `&&`; makes proposal 3's helper the monad's own `bind`.
- Cost and risk: every twin body and each proof that unfolds one changes. Row 112 records `isDefEq` timeouts when a
  twin's `.1` sits in a dependent argument, so pilot on the composites whose proofs go through `_ok` lemmas
  (`snocC`, `uncatC`, the `AC3` steps) before the primitives. Row 125 judged `opOK` bundling not worth it; this
  differs in removing a layer rather than adding one.

## 7. One theorem per op

- 23 theorems in `Rep*` have one user each, the `rep_*C` twin: `thin_body_set` (247 lines), `rep_unsnoc` 172,
  `rep_fixOn` 104, `rep_symDiv` 98, `rep_atPos` 93, `rep_uncat` 92, `perm_step_set` 65, `rep_thin` 60, `rep_prod` 50,
  `subseq_chain` 45, `rep_bagify` 38, `perm_chain` 35, `rep_leq` 34, `rep_sum` 32, `rep_tau` 25, `rep_est` 24,
  `rep_alpha` 21, `rep_sortSet` 20, `subseq_keep` 18, `rep_inl` 15, `rep_inr` 13, `rep_injective` 12,
  `rep_surjective` 9. Total 1,322 lines, of which about 230 are premise lists the twin re-derives from the bit
  (`rep_uncat`'s statement is 4,074 characters, `rep_symDiv`'s 3,515).
- Change: state each on the bit and delete the capacity-premise form, as rel-127 did for `perm`/`subseq`/`thinL`.
  Saves the 230 lines of premises plus the 23 wrappers, about 400 lines, and leaves one statement per op.
- Plain theorems with many users stay (`rep_comp` 20, `rep_pair` 15, `rep_top` 8, `rep_mem` 7).
- Cost: per-op proof edits; do it after proposal 4, which removes the 15 that need no edit at all.

## 8. Two-part raze read-back as a case of the N-part one

- `KernelWF/RazeRow.lean` (221), `RazeRowRec.lean` (433), `RazeRowAll.lean` (160) prove the read-back of `raze` of
  two parts under the proposition `Vals.RazeFits`; `RazeRowN.lean` (302) proves it for any number of parts under
  `razeC`'s bit, and its header says the cases "are `RazeRow`'s and `RazeRowRec`'s with the second part's offset
  generalised". Row 131 lists the derivation as open.
- The two cannot be merged as they stand: `Obj.razeC_fits` goes bit → `RazeFits`, and the plain theorems
  (`rep_union`, through `raze2_lt` with 41 users) hold only `RazeFits`. Once proposal 7 has moved the callers to the
  bit, they can call `raze_rowN` and the two-part family is deletable: up to about 500 of the 814 lines, plus
  `RazeFits` itself where no statement still names it.

## 9. `==` codes both relations twice

- `Alg.lean:186`: `instance : BEq (Rel A B) := ⟨fun R S => R ⊑ S && S ⊑ R⟩`, and `leC` (line 33) codes the joint
  pair side of `R` and `S` with `codesC` on each call, so one `==` runs that coding twice on the same two parts.
- `==` is on the run path: the memo hit in `ev`'s `.share` case, leaf interning (`Eval.lean:268`), the conformance
  check in `run` (line 520).
- Change: an `eqC` that codes once and takes `member` in both directions on `c.1[0]`, `c.1[1]`; `interC`, `diffC`,
  `leC` already share that `codesC` expression and can share the helper. About 10 lines; `rep_eq` has no user.

## 10. Codes are recomputed at every op

- 32 call sites of `codesC` in `Alg.lean`: `R ∩ S`, `R ⊑ S`, `R − S`, `dom`, `ran`, `≫`, the divisions each code
  their inputs from the values, and the result is a table of values again, coded again by the next op.
- `Lang.Bits` (235 lines, with 1,942 lines of `BitsSpec*`) exists to avoid that for small objects: `codeAll` codes
  every column of a plan once per object, and the inner nodes never return to values.
- A relation that keeps its codes beside its values (or objects whose universe is coded once per program, which
  `Tm.uni`/`idU U` already name) would give the table path the same property and could make `Bits` a fast path of
  one mechanism instead of a second evaluator with its own soundness proof.
- This is a change of representation in `Core.lean`/`Code.lean` (the other session's, and one that needs the
  author's approval), so the proposal is only the measurement that decides it: `perf record -g` on `SudokuPC9` and
  on one table-path program (`Knapsack`), and the share of samples under `Obj.codesC`. If it is small, drop this.

## Checked and left alone

- `Obj.sum` (tag, index, two sides, with `clampFin`/`dflt` in `Vals.row`) costs dedicated lemmas in `CodesRec`,
  `PickRow`, `RazeRowRec`, and only `Programs/Edit.lean` and the prelude's `⊕` use it. It is what `[R,S]` needs
  and the goals name sums, so no change is proposed.
- `Obj.arr` as `lo`, `hi` into one flat payload is what `uncons`, `inits`, `tails`, `cat` rely on (slices without
  copying). No simpler encoding was found that keeps that.
- `KernelWF` at 18,049 lines is the price of proving against compressed columns (`foR`, `alp`, `syms`) rather than
  dense ones; apart from the 507 unused lines and proposal 8 no shortcut was found that keeps the statements.
- The remaining `op`/`opC` pairs with two written bodies (`top`/`topC`, `num`/`numC`, `inl`/`inlC`, `inr`/`inrC`,
  `unsnoc`/`unsnocC`, `atPos`/`atPosC`, `tail`/`tailC`, `fixOn`/`fixOnC`) are each a body plus one decided bound;
  folding them is the tail of rows 112–126 and is worth doing only alongside proposal 6.
- `ev` and `evB` repeat `Bits.orLeaf (evB …) (ev …)` at 13 sites in `Eval.lean`; a two-line helper removes the
  repetition but nothing else.
