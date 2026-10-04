/-
  WHICH BEAD CARRIES THE MARK, IN WHICH SHAPE, ON WHICH PANEL — checked at elaboration time on every
  `lake build diag`, by the exporter's own `settlePass` over the steps the exporter's own `peerStep`
  finds.

  A MARK BELONGS TO THE STEP THAT LEAVES THE PANEL (`Step`): for a panel with the sign `σ` drawn to
  its right, the mark is the rule applied to that panel to obtain the next one.  It stands on the
  expression the rule's two sides have in common (`passOf?`), and ITS SHAPE IS THE SIGN: a hollow
  circle for `=`, a triangle for `⊑` — down where the partner stands above the bead, up where below.
  The panel a step arrives at gets no mark from it, and the last panel of a chain has none.
  A theorem the step's proof does not cite marks nothing (`Step.cited`, 10.4c's `tex_mono`).
-/
import diag.tool.StringDiagram
import AOP.A5_5
import AOP.A5_5_AlgCat
import AOP.A6_2
import AOP.A6_3
import AOP.A7_2
import AOP.A9_1
import AOP.A10_4_Tex

namespace Freyd.StrDiag.PassMarkTest

open Lean Meta Freyd.StrDiag

/-- A side as the beads the panel draws it with, one per factor in order (`compFactors`), each with
    its term bare of the functor it runs under and the binders that let a neighbour past it
    (`passHyp`) — the fields `settlePass` reads, and no others. -/
def beads (side : Expr) : MetaM Diagram := do
  let core (e : Expr) := if e.getAppFn.isConstOf ``Freyd.Functor.map then e.appArg! else e
  let rows ← (compFactors side).mapM fun f => do
    let c := core f
    return ({ shape := .text (← label c), arms := #[], legs := #[], obj := "",
              src := default, tgt := default, core := some c, passCands := ← passHyp c } : Row)
  return { lanes := #[], rows, top := #[], bot := #[], otop := side, obot := side }

/-- The marks on one panel — `decl`'s left side or its right — in a call naming `peers` beside it:
    every marked bead with its shape.  Read as `drawWith` reads it: under the declaration's binders
    (a predicate's own claim among them), the panel's own step only for its LEFT side. -/
def panel (decl : Name) (left : Bool) (peers : List Name := []) : MetaM (List (String × String)) := do
  let ci ← getConstInfo decl
  let lv := ci.levelParams.map mkLevelParam
  forallTelescope ci.type fun xs body => do
    let claim := mkAppN (mkConst decl lv) xs
    let run (proof ty : Expr) : MetaM (List (String × String)) := do
      let some rel ← stmtRel? ty | throwError "{decl} states no ⊑ or ="
      let args := rel.getAppArgs
      let side := if left then args[args.size - 2]! else args[args.size - 1]!
      let own ← Step.new decl (rel.isAppOfArity ``Eq 3) proof #[] (some ty)
      let steps := (if left then #[own] else #[])
        ++ (← (peers.toArray.filter (· != decl)).filterMapM (peerStep · side))
      let d ← settlePass (← beads side) steps (some side)
      return d.rows.toList.filterMap fun r =>
        r.tri.map fun up => (r.label, if r.eq then "circle" else if up then "up" else "down")
    if body.isProp then withLocalDeclD decl claim fun h => run h claim
    else run (← stepProof decl xs) body

/-- A statement's two panels, left then right. -/
def pair (n : Name) : MetaM (List (List (String × String))) :=
  return [← panel n true, ← panel n false]

/-- Does the proof of `step`, at its own binders, cite `thm`? -/
def cites (step thm : Name) : MetaM Bool := do
  let ci ← getConstInfo step
  forallTelescope ci.type fun xs _ => return (← Step.new step false (← stepProof step xs)).cited.contains thm

-- 7.2b `F(R)φ ⊑ φR`: `φ` stands on both sides, `R` above it on the left: the down triangle on `φ`,
-- in the left panel; the right panel is where the step arrives.
/-- info: [[("φ", "down")], []] -/
#guard_msgs in #eval pair ``Freyd.Alg.MonoAlg
-- 7.2.1b: `est(R)` crosses `f` below it in `F(est(R))f`: the up triangle on `est(R)`, left panel.
/-- info: [[("est(R)", "up")], []] -/
#guard_msgs in #eval pair ``Freyd.Alg.Distributes
-- 2.6a `f h = F(h) g`: an equation, so the hollow circle, on `h`, in the left panel.
/-- info: [[("h", "circle")], []] -/
#guard_msgs in #eval pair ``Freyd.Alg.IsFHom
-- 2.6 `cata_comm`, `α⦇f⦈ = F(⦇f⦈)f`: the hollow circle on `⦇f⦈`, in the left panel.
/-- info: [[("⦇f⦈", "circle")], []] -/
#guard_msgs in #eval pair ``Freyd.Alg.InitialAlgebra.cata_comm
-- 9.2 dp-cost: panel (a) is left by the `=` step `h cost = F(cost)k`, panel (b) by a `⊑` step — the
-- hollow circle on `cost` in (a), the down triangle on `cost` in (b), each BEFORE its sign.
/-- info: [[("cost", "circle")], [("cost", "down")]] -/
#guard_msgs in #eval do
  let steps := [1, 2, 3, 4].map fun k => Name.str `Freyd.Alg.monoAlg_of_cost_shunted s!"step_{k}"
  return [← panel steps[0]! true steps, ← panel steps[1]! true steps]
-- 10.4c: no step of the greedy chain cites `tex_mono`, so its square marks none of them.
/-- info: [false, false, false, false, false, false, false, false] -/
#guard_msgs in #eval [1, 2, 3, 4, 5, 6, 7, 8].mapM fun k =>
  cites (.str `Freyd.Alg.RelSet.Tex.tex_greedy s!"step_{k}") ``Freyd.Alg.RelSet.Tex.tex_mono

end Freyd.StrDiag.PassMarkTest
