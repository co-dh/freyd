/-
  The leaves of a trans spine, alone in a module because they run in both phases: `calc_steps`
  (`AOP.CalcSteps`) reads them at build time through a `meta import`, and the exporter's formula
  route (`diag.tool.FormulaRender`) reads them at run time.
-/
module

public import Lean.Meta

open Lean Meta

namespace Freyd.Alg.CalcSteps

/-- The heads of a trans spine: `calc` elaborates to nested `Trans.trans` (`Eq.trans` for a chain
    of `=`), and a proof written `le_trans h₁ h₂` is a spine too.  Each composes its last two
    arguments.  The last two are named, not imported: they live in libraries this one precedes. -/
public def spineHeads : List Name :=
  [``Trans.trans, ``Eq.trans, `Freyd.Alg.le_trans, `Freyd.Diag.OrderedCat.«≤_trans»]

/-- The leaves of a trans spine, left to right, each with the type THE SPINE states for it — the
    binder type of its head at that argument — never the leaf's inferred type: a `rfl` step infers
    `X = X` where the `calc` line it closes reads `X = Y`.  `t` is the type `e` proves. -/
public partial def leaves (e t : Expr) : MetaM (Array (Expr × Expr)) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  let some c := e.getAppFn.constName? | return #[(e, t)]
  unless spineHeads.contains c && args.size ≥ 2 do return #[(e, t)]
  let (f, g) := (args[args.size - 2]!, args[args.size - 1]!)
  match ← whnf (← inferType (mkAppN e.getAppFn (args.extract 0 (args.size - 2)))) with
  | .forallE _ tf b _ =>
    match ← whnf (b.instantiate1 f) with
    | .forallE _ tg _ _ => return (← leaves f tf.headBeta) ++ (← leaves g tg.headBeta)
    | _ => return #[(e, t)]
  | _ => return #[(e, t)]

end Freyd.Alg.CalcSteps
