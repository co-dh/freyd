/-
  WHICH BEAD CARRIES THE PASS TRIANGLE, checked at elaboration time on every `lake build diag`.

  The triangle is on the expression the two sides of a square have in common (`passOf?`) — a bead
  standing as it is on both, or bare on one and under the functor on the other; both, the one
  standing as it is — drawn in the side the step leaves: 7.2b put it on `R` although `φ` stands
  on both sides, 7.2.1b (`est(R)`) shipped unmarked, and `cata_comm`'s `⦇f⦈` lost its mark.
  A theorem the step's proof does not cite marks nothing (`settlePass`'s `cites`, 10.4c's `tex_mono`),
  and a peer's hypothesis marks only the panel that peer's step leaves (`peerHyps`).
-/
import diag.tool.StringDiagram
import AOP.A5_5
import AOP.A5_5_AlgCat
import AOP.A6_2
import AOP.A7_2
import AOP.A9_1
import AOP.A10_4_Tex

namespace Freyd.StrDiag.PassMarkTest

open Lean Meta Freyd.StrDiag

/-- Every mark of `decl`'s own statement, read under its binders: the bead a pass (`passOf?`) puts
    the triangle on, its partner in the left side, and whether the partner stands below it (the up
    triangle).  Each
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
        out := out ++ [((← ppExpr φ).pretty, (← ppExpr P).pretty, below)]
    return out.eraseDups

/-- Does the proof of `step`, at its own binders, cite `thm`?  A mark cited to a theorem it does
    not is dropped (`settlePass`). -/
def cites (step thm : Name) : MetaM Bool := do
  let ci ← getConstInfo step
  forallTelescope ci.type fun xs _ => return (← stepProof step xs).getUsedConstants.contains thm

/-- `marks` as `passThm` asks: the statement opened with METAVARIABLES, as a candidate theorem is,
    and asked for each bead of its own sides read under its binders. -/
def thmMarks (decl : Name) : MetaM (List (String × String × Bool)) := do
  let ci ← getConstInfo decl
  forallTelescope ci.type fun _ body => do
    let some (l, r) ← relSides? body | throwError "{decl} states no ⊑ or ="
    let core (e : Expr) := if e.getAppFn.isConstOf ``Freyd.Functor.map then e.appArg! else e
    let mut out := []
    for φ in (compFactors l ++ compFactors r).map core do
      let s ← saveState
      if let some (P, below) ← passOf? (← forallMetaTelescope ci.type).2.2 φ then
        out := out ++ [((← ppExpr φ).pretty, (← ppExpr (← instantiateMVars P)).pretty, below)]
      s.restore
    return out.eraseDups

/-- How many hypotheses `peer`'s step brings to the panel of each side of `decl` (`peerHyps`). -/
def peerUse (decl peer : Name) : MetaM (List Nat) := do
  forallTelescope (← getConstInfo decl).type fun _ body => do
    let some (l, r) ← relSides? body | throwError "{decl} states no ⊑ or ="
    return [(← peerHyps peer l).size, (← peerHyps peer r).size]

-- 2.6 `cata_comm`, `α⦇f⦈ = F(⦇f⦈)f`: `⦇f⦈` is the one expression on both sides, `α` above it: down.
-- Opened as the search opens it: `?f` unified with `α` made `α` the common bead and dropped the mark.
/-- info: [("⦇f⦈", "α", false)] -/
#guard_msgs in #eval thmMarks ``Freyd.Alg.InitialAlgebra.cata_comm
-- 6.2 `relCata_le_comp`: step 2 uses `h : F(S)T ⊑ RS` and leaves step 1's RIGHT side; step 1's left
-- side draws the same beads and is left by step 1 alone, which uses no hypothesis: no mark there.
/-- info: [0, 1] -/
#guard_msgs in #eval peerUse ``Freyd.Alg.relCata_le_comp_step1 ``Freyd.Alg.relCata_le_comp_step2
-- 2.6a: `h` is bare on the left and under `F` on the right, `f` becomes `g`: `h`, `f` above: down.
/-- info: [("h", "f", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.IsFHom
-- 7.2b: `R` crosses `φ`, which stands unchanged on both sides, `R` above it: the down triangle on `φ`.
/-- info: [("φ", "R", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.MonoAlg
-- dp-cost (9.2): `h cost = F(cost)k`, `cost` the only expression on both sides and `h` above it:
-- the down triangle on `cost`.
/-- info: [("cost", "h", false)] -/
#guard_msgs in #eval marks ``Freyd.Alg.monoAlg_of_cost_step1
-- 7.2.1b: `est(R)` crosses `f` below it in `F(est(R))f`, and `f` does not stand as it is on the right:
-- the up triangle on `est(R)`.
/-- info: [("est(R)", "f", true)] -/
#guard_msgs in #eval marks ``Freyd.Alg.Distributes
-- 10.4c: no step of the greedy chain cites `tex_mono`, so its square marks none of them.
/-- info: [false, false, false, false, false, false, false] -/
#guard_msgs in #eval [1, 2, 3, 4, 5, 6, 7].mapM fun k =>
  cites (.str `Freyd.Alg.RelSet.Tex s!"tex_greedy_step{k}") ``Freyd.Alg.RelSet.Tex.tex_mono

end Freyd.StrDiag.PassMarkTest
