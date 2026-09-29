/-
  WHICH BEAD CARRIES THE PASS TRIANGLE, checked at elaboration time on every `lake build diag`.

  Of the two beads a pass swaps (`passOf?`), the triangle is the more complicated one's
  (`heavierMark`), drawn in the side it leaves: 7.2b and dp-cost put it on the crossing `R` where the
  algebra it crosses was the bead the display is about, and 7.2.1b (`est(R)`) shipped unmarked.
  A theorem the step's proof does not cite marks nothing (`settlePass`'s `cites`, 10.4c's `tex_mono`).
-/
import diag.tool.StringDiagram
import AOP.A5_5_AlgCat
import AOP.A7_2
import AOP.A9_1
import AOP.A10_4_Tex

namespace Freyd.StrDiag.PassMarkTest

open Lean Meta Freyd.StrDiag

/-- Every mark of `decl`'s own statement, read under its binders: the bead a pass (`passOf?`) swaps
    that `heavierMark` puts the triangle on, its partner in the left side, and whether the partner
    stands below it (the up triangle).  Each
    bead is asked for as it is drawn, with no lane around it. -/
def marks (decl : Name) : MetaM (List (String × String × Bool)) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun xs body => do
    -- A predicate is read applied to its binders, a theorem by what it concludes.
    let ty := if body.isProp then mkAppN (mkConst decl (ci.levelParams.map mkLevelParam)) xs else body
    let some (l, r) ← relSides? ty | throwError "{decl} states no ⊑ or ="
    let core (e : Expr) := if e.getAppFn.isConstOf ``Freyd.Functor.map then e.appArg! else e
    let mut out := []
    for φ in (compFactors l ++ compFactors r).map core do
      if let some (P, below) ← withNewMCtxDepth (passOf? ty φ) then
        let (m, q, b) ← heavierMark φ P below
        out := out ++ [((← ppExpr m).pretty, (← ppExpr q).pretty, b)]
    return out.eraseDups

/-- Does the proof of `step`, at its own binders, cite `thm`?  A mark cited to a theorem it does
    not is dropped (`settlePass`). -/
def cites (step thm : Name) : MetaM Bool := do
  let ci ← getConstInfo step
  forallTelescope ci.type fun xs _ => return (← stepProof step xs).getUsedConstants.contains thm

-- 2.6a: `h` crosses `f`; `f : F(A)⟶A` outweighs `h : A⟶B`, so `f` carries it, `h` below: up.
/-- info: [("f", "h", true)] -/
#guard_msgs in #eval marks ``Freyd.Alg.IsFHom
-- 7.2b: `R` crosses `φ`; `φ : F(A)⟶A` outweighs `R : A⟶A`, `R` above it: the down triangle on `φ`.
/-- info: [("φ", "R", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.MonoAlg
-- dp-cost: `MonoAlg h R` again, the algebra `h` the heavier: the down triangle on `h`.
/-- info: [("h", "R", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.monoAlg_of_cost
-- 7.2.1b: `est(R)` crosses `f` below it in `F(est(R))f`, and outweighs it: the up triangle on `est(R)`.
/-- info: [("est(R)", "f", true)] -/
#guard_msgs in #eval marks ``Freyd.Alg.Distributes
-- 10.4c: no step of the greedy chain cites `tex_mono`, so its square marks none of them.
/-- info: [false, false, false, false, false, false, false] -/
#guard_msgs in #eval [1, 2, 3, 4, 5, 6, 7].mapM fun k =>
  cites (.str `Freyd.Alg.RelSet.Tex s!"tex_greedy_step{k}") ``Freyd.Alg.RelSet.Tex.tex_mono

end Freyd.StrDiag.PassMarkTest
