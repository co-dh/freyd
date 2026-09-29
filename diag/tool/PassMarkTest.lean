/-
  WHICH BEAD CARRIES THE PASS TRIANGLE, checked at elaboration time on every `lake build diag`.

  The triangle is the crossing bead's, drawn in the side it leaves (`passOf?`): three displays of the
  companion shipped it on the wrong bead or not at all — 2.6a (`f h = F(h) g`, an equation, was not
  read), 7.2b (`F(R)φ ⊑ φR` marked `φ`, and `R` in the right panel) and 7.2.1b (`est(R)` unmarked).
  A theorem the step's proof does not cite marks nothing (`settlePass`'s `cites`, 10.4c's `tex_mono`).
-/
import diag.tool.StringDiagram
import AOP.A5_5_AlgCat
import AOP.A7_2
import AOP.A10_4_Tex

namespace Freyd.StrDiag.PassMarkTest

open Lean Meta Freyd.StrDiag

/-- Every bead of `decl`'s own statement, read under its binders, that `passOf?` marks: the bead,
    its partner in the left side, and whether the partner stands below it (the up triangle).  Each
    bead is asked for as it is drawn, with no lane around it. -/
def marks (decl : Name) : MetaM (List (String × String × Bool)) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun xs _ => do
    let ty := mkAppN (mkConst decl (ci.levelParams.map mkLevelParam)) xs
    let some (l, r) ← relSides? ty | throwError "{decl} states no ⊑ or ="
    let core (e : Expr) := if e.getAppFn.isConstOf ``Freyd.Functor.map then e.appArg! else e
    let mut out := []
    for φ in (compFactors l ++ compFactors r).map core do
      if let some (P, below) ← withNewMCtxDepth (passOf? ty φ) then
        out := out ++ [((← ppExpr φ).pretty, (← ppExpr P).pretty, below)]
    return out.eraseDups

/-- Does the proof of `step`, at its own binders, cite `thm`?  A mark cited to a theorem it does
    not is dropped (`settlePass`). -/
def cites (step thm : Name) : MetaM Bool := do
  let ci ← getConstInfo step
  forallTelescope ci.type fun xs _ => return (← stepProof step xs).getUsedConstants.contains thm

-- 2.6a: `h` crosses `f`, which stands above it in `f h`: the down triangle, on `h` alone.
/-- info: [("h", "f", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.IsFHom
-- 7.2b: `R` crosses `φ` below it in `F(R)φ`: the up triangle on `R`, and none on `φ`.
/-- info: [("R", "φ", true)] -/
#guard_msgs in #eval marks ``Freyd.Alg.MonoAlg
-- 7.2.1b: `est(R)` crosses `f` below it in `F(est(R))f`: the up triangle on `est(R)`.
/-- info: [("est(R)", "f", true)] -/
#guard_msgs in #eval marks ``Freyd.Alg.Distributes
-- 10.4c: no step of the greedy chain cites `tex_mono`, so its square marks none of them.
/-- info: [false, false, false, false, false, false, false] -/
#guard_msgs in #eval [1, 2, 3, 4, 5, 6, 7].mapM fun k =>
  cites (.str `Freyd.Alg.RelSet.Tex s!"tex_greedy_step{k}") ``Freyd.Alg.RelSet.Tex.tex_mono

end Freyd.StrDiag.PassMarkTest
