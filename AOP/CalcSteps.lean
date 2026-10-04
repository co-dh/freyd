/-
  `calc_steps <decl>` — one theorem per STEP of the `calc` that proves `<decl>`, read off the proof
  term: `<decl>.step_1`, …, `<decl>.step_k`, each `∀ <decl's binders>, aᵢ₋₁ rel aᵢ`, proved by that
  step's own justification.

  A proof table draws every intermediate term of the chain, the relation of every step and the law
  that justifies it.  Typed beside the proof, each is a hand copy a gate has to check; generated from
  the one proof, there is nothing to check.  The step theorems are what lets every route of the
  exporter (panel, formula, relation) address a step as it addresses any statement: by name and side.
-/
module

public import Lean

open Lean Elab Command Meta

namespace Freyd.Alg.CalcSteps

/-- The leaves of a `calc` spine, left to right, each with the relation the `calc` states for it:
    `calc` elaborates to nested `Trans.trans` (and `Eq.trans` for a chain of `=`), whose last two
    arguments are the two halves it composes.  The statement is read off `Trans.trans`'s own `r a b`
    and `s b c`, not off the leaf's type, which for a step proved by `hf : Simple f` is `Simple f`. -/
public meta partial def leaves (e : Expr) (ty : Option Expr := none) : Array (Expr × Option Expr) :=
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``Trans.trans, #[_, _, _, r, s, _, _, a, b, c, h₁, h₂]) =>
    leaves h₁ (some (mkApp2 r a b).headBeta) ++ leaves h₂ (some (mkApp2 s b c).headBeta)
  | (``Trans.trans, args) | (``Eq.trans, args) =>
    if args.size < 2 then #[(e, ty)] else leaves args[args.size - 2]! ++ leaves args[args.size - 1]!
  | _ => #[(e, ty)]

/-- `calc_steps <decl>`: adds `<decl>.step_i` for every step of the `calc` proving `<decl>`. -/
syntax (name := calcSteps) "calc_steps " ident : command

@[command_elab calcSteps] public meta def elabCalcSteps : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ci ← getConstInfo n
  let some v := ci.value? | throwError "calc_steps: {n} has no proof term to read the steps off"
  let steps ← liftTermElabM <| lambdaTelescope v fun xs b => do
    let ls := leaves b
    if ls.size < 2 then
      throwError "calc_steps: the proof of {n} is no `calc` of two or more steps — its body is \
        {← ppExpr b}"
    -- A binder the step does not use is no binder of the step: kept, it would have to be supplied
    -- by every caller of a step that never needs it.  Used means in the step, or in a used binder's
    -- type, so the binders are read last to first.
    ls.mapM fun (l, ty) => do
      let (t, l) := (← instantiateMVars (← ty.getDM (inferType l)), ← instantiateMVars l)
      let mut ys : Array Expr := #[]
      for x in xs.reverse do
        let used (e : Expr) := e.containsFVar x.fvarId!
        if used t || used l || (← ys.anyM fun y => return used (← inferType y)) then ys := ys.push x
      return (← mkForallFVars ys.reverse t, ← mkLambdaFVars ys.reverse l)
  for ((t, p), i) in steps.toList.zipIdx do
    liftCoreM <| withExporting <| addDecl <| .thmDecl
      { name := n ++ Name.mkSimple s!"step_{i + 1}", levelParams := ci.levelParams, type := t, value := p }

end Freyd.Alg.CalcSteps
