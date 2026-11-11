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
