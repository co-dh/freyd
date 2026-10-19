# Handoff: ch9 printing of Edit.R and the bifunctor F(U,V)

Base 813b17a. WIP commit on this branch. NOT green: diag-regen has 3 red stubs (below).

## Done
- AOP/A9_2_Edit.lean `unexpandEditR` (~:2248): prints `R` instead of `≤` (superseded, see Left 1).
- AOP/A9_2_Edit.lean :975-1041 (edit_thin_step1/3/4, edit_thin_condition): every
  `(F Unit (Op A)).map (X)` replaced by `Fbimap Unit (𝟙 (dE (Op A))) (X)` (definitionally equal,
  `Fmap L E R := Fbimap L (𝟙 (dE E)) R`, A6_ConsList.lean:71), so 9.2.1k prints `F(𝟙,edit°)`.
  `lake build AOP.A9_2_Edit` exit 0.
- diag/aop/09-dynamic.typ :353 and :371 hand-written cells say `R` (to become `≼`, Left 1).
- Finding: the BiRelator.map printer (diag/tool/Label.lean:1977-1987) ALREADY always prints both
  arguments (`F(⊤,≤)` is in main's generated/formula for α_pres_R). 9.2.1j is `edit_mono`
  (A9_2_Edit.lean:509), stated with the UNARY relator `(F Unit (Op A)).map (R A)`, so `F(≤)` there
  is the one-argument relator, not a dropped ⊤. No exporter rule change was needed for item 2.

## Failing (diag-regen exit 1)
Red stubs for `Freyd.Alg.RelSet.Edit.edit_thin_step1.lhs`, `edit_thin_step3.rhs`, `edit_thin_step4.rhs`:
  "the bead `F(𝟙,edit°)` is a family and the environment proves neither its naturality nor a
  refutation"; search line: "state `LaxNatural (sum PUnit («𝟙» op × («𝟙» op) list)) (sum PUnit
  («𝟙» op × «𝟙» list × «𝟙» list)) (fun a => F (𝟙Op) edit°)`".
  The unary spelling got its naturality by lifting `edit_laxNatural` (A9_2_Edit.lean:1393) through
  the relator; the Fbimap spelling needs its own `LaxNatural` theorem at exactly that spelling
  (opus: Lean proving), or revert the :975-1041 substitution.
Stale markers after the statement change (09-dynamic.typ :505, :623, :630, :640, :646):
  edit_thin_condition@f8eeb0f3, edit_thin_step1@a9117843, step3@3276aa63, step4@46e2e6a4 — re-key
  from the index after `./scripts/lean-refactor index`.

## Left
1. User's new decision: Edit.R prints `≼` via a Lean notation, no unexpander. Make `A` implicit in
   `Freyd.Alg.RelSet.Edit.R` (A9_2_Edit.lean:223; ~59 uses of `R A` in the file, use
   scripts/lean-refactor) and add `notation "≼" => R`; delete `unexpandEditR`. Then typ :353/:371
   say `≼`. Same question for unexpandEditQ/α/V (they exist only to drop the type argument `A`).
2. The three numeric `"≤"` unexpanders in diag/StrDiagNames.lean (leRel on Nat :497, Party.leq on
   Int :492-ish, ListRel.leq on Int :528): the book writes `leq` for these numeric orders, so they
   keep `≤`; could become `notation "≤" => leRel`-style notations if the user wants no unexpanders
   (notation `≤` clashes with core's `LE.le` notation token, so it must be checked).
3. Gates: full ./scripts/diag-regen zero red stub; make c NOTE=aop CH=0..10; pdftotext check.
