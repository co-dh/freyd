# Rel: finished tasks

Tasks removed from the session task list when they finished, oldest first. A task is appended here in the same
turn it is deleted from the list.

| #  | task                                                                                                 |
|----|------------------------------------------------------------------------------------------------------|
| 4  | Part A := (n : Nat) × Vals A n; delete Cols, ofCols, Vals.ofParts                                    |
| 5  | Open decision A/B: delete program-unused sum and special folds                                       |
| 6  | Obj.list → Obj.arr; est least, thin, uncons, fold, map on arrays; delete the four Except ops         |
| 7  | lean-refactor runs on any Lake package (leetq)                                                       |
| 9  | Obj.sum: tag + idx + two payloads; inl, inr, [R,S], R+S; delete SumRel                               |
| 10 | Rel language on top of Alg, then Blocks written in it                                                |
| 11 | Front end lifts note formulas to a state family (B)                                                  |
| 12 | Alg: payload compaction, foldOn, succ partial at the top                                             |
| 13 | Rel language front end: parser, elaborator with lifting, evaluator, blocks.rel                       |
| 14 | Chess, Circuit, Wumpus as .rel programs (B)                                                          |
| 15 | Rel language: no shadowing, shared sub-terms, lifted fold, where, object variables, nested literals  |
| 16 | A: Chess closure as a lifted fold (step keyed on demand)                                             |
| 17 | B: remaining B&dM operators in Alg                                                                   |
| 18 | C: sum empty-side gap, Ops.rank List fallback, audit of architecture steps 2/4/5                     |
| 19 | Architecture step 5: Algebra.lean split into Code, Alg, AlgTest (step 4 continues as tasks 43–46)    |
| 20 | bagify as an arr sorted by code (user chose C; trees declined)                                       |
| 21 | Alg arithmetic: one op by kernel opcode (plus, times, minus, div, mod)                               |
| 22 | New Alg ops as Rel-language builtins                                                                 |
| 23 | Delete declarations orphaned by step 2 (Core, Gather, Raze, Reduce)                                  |
| 24 | B&dM ch.6 spec as .rel (sorting)                                                                     |
| 25 | B&dM ch.7–10 specs as .rel (mss, knapsack, string edit, detab-entab)                                 |
| 26 | Rel lang: R°, R/∋, × on demand (merged; loop split off)                                              |
| 27 | Rel lang: est/thinL/merge/filter parameter on demand; est per key                                    |
| 29 | Fold seed depending on outer fold's pair (string edit tabulation)                                    |
| 30 | Rel lang: loop(F) on demand; detab/triple back to loop                                               |
| 31 | Rel lang: array constant in a literal's row                                                          |
| 32 | Prelude .rel: perm, ordered, sort defined in the language (fold form); remove the builtins           |
| 33 | Prelude: move the abbreviation builtins (frac, E, est, ∈)                                            |
| 34 | Prelude: move the list builtins that the book writes as folds                                        |
| 35 | Rel lang: every top-level definition carries its type; rel --types                                   |
| 36 | lake rebuilds Parse when prelude.rel changes                                                         |
| 38 | Rel literate files: .rel.md, code = indented Markdown blocks                                         |
| 39 | Empty array literal takes its object from the other side of check/=                                  |
| 40 | Programs: prints become checks; mss ⊞ → oplus, circuit ⊻ → xor; edit tabulation in edit.rel.md       |
| 41 | Primitive at(i) : [α] ⟶ α (0-based Alg op + builtin); full adder on an array [B]                     |
| 28 | Evaluator waste: keyed fold per-row seeds, detab, lifted `RS` as a join (chess 1743 → 171 MB)        |
| 37 | A `nil` whose source no context fixes has source `1`; `ran(nil)` in a fold seed elaborates           |
| 42 | `where` names known while the body is split into names; a lifted definition applied to closed terms  |
| 43 | qlean plan written: doc/qlean-kernel-length-plan.md (USize counts, run-time assert)                  |
| 48 | lean-refactor `coerce (A B f)…`: a named conversion where a term of type A meets expected type B     |
| 49 | lean-refactor `uncoerce` (drop a redundant conversion) and `rename --terms-only`/`--patterns-only`   |
| 50 | lean-refactor `retype A B`: retype a binder at its source where an A variable meets expected B       |
| 52 | lean-refactor `retype` on a 4983-line file: 27:26 → 2:43 (site search was quadratic; gate reuses elaborations) |
| 47 | qlean: `Kernel.maxBytes = 2^48`, `needBytes`; til, slice, expand, spread, cross, mmu, guid draw checked       |
| 55 | qlean: C-ABI count lists are `ByteArray` of 8-byte LE counts, single counts `USize`; no Nat count in an extern signature |
| 56 | qlean: `ungroup`/`expandColumn` counts are `Array USize`; `countBytes_size` replaces run-time size checks; tests use `asCount` |
| 57 | rel ↔ Lean mapping table written: doc/rel-lean-mapping.md (27 same / 33 differs / 15 none)                    |
| 44 | qlean: every count is `USize`, no `Nat` count in executable code; `usize-count` merged into qlean master (553 jobs green) |
| 45 | qlean: growing ops assert through `need`/`needSize`/`needBytes` that the result fits; no reference branch |
| 46 | leetq: `Arr`'s index is `USize` (Core → Code → Alg → Lang, steps L1–L5); reference branches deleted; 591 jobs green, 36 checks pass |
| 59 | `rel_program <name> where`: the Rel language as a closed Lean syntax category expanding to the existing AST; all 9 programs agree with the text parser, zero text changes |
| 60 | `rel(…)`: a Rel term read as an AOP allegory term (pure fragment), so an equational proof is a plain Lean `calc`; three B&dM ch.4 derivations as tests |
| 61 | `rel(…)` fragment: dom, ran, products, coproducts, Boolean complement, the book's one-argument fold `⦇R⦈`, `α`, `F(R)`; witnesses from the context, ambiguity is an error; B&dM ch.5–6 derivations as calc |
| 62 | AOP: `topMor_eq_topHom` (A6_2, no axioms); `rel(⊤)` under both instances is `topHom` through a table of registered identifications |
| 63 | `rel(…)` power group: `∋`, `∈`, `Λ(R)`, `E(R)`, `P(R)`, `est(R)`, `thin(Q)`, `union`, `τ` as AOP's power-object operators; (7.5) as a calc; `setify` stays outside |
| 64 | the nine Rel programs are `rel_program` modules under `leetq/LeetQ/Rel/Programs/`; their `.rel.md` files, the pasted copies and `#rel_agree` deleted; tests extend a program on the AST (`Test.extend`) |
| 65 | hand-written `LeetQ/Rel/{Blocks,BlocksRel,Chess,Circuit,Wumpus}.lean` deleted; the four tests compare to literals (15 oracle-only table comparisons dropped: Blocks `qM`, `qF`; Chess `D d`, `K`, `N`, `X₀`, `X₁`) |
| 53 | qlean: last Nat counts — `Enc.dense/raw/atoms/blobOf` take USize, sizes enter through `needSize`; audit in doc/qlean-usize-audit.md |
