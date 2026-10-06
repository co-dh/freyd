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

/-- The heads of a trans spine: `calc` elaborates to nested `Trans.trans` (`Eq.trans` for a chain
    of `=`), and a proof written `le_trans h₁ h₂` is a spine too.  Each composes its last two
    arguments.  The last two are named, not imported: they live in libraries this one precedes. -/
public meta def spineHeads : List Name :=
  [``Trans.trans, ``Eq.trans, `Freyd.Alg.le_trans, `Freyd.Diag.OrderedCat.«≤_trans»]

/-- The leaves of a trans spine, left to right, each with the type THE SPINE states for it — the
    binder type of its head at that argument — never the leaf's inferred type: a `rfl` step infers
    `X = X` where the `calc` line it closes reads `X = Y`.  `t` is the type `e` proves. -/
public meta partial def leaves (e t : Expr) : MetaM (Array (Expr × Expr)) := do
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

/-- `calc_steps <decl>`: adds `<decl>.step_i` for every step of the `calc` proving `<decl>`. -/
syntax (name := calcSteps) "calc_steps " ident : command

@[command_elab calcSteps] public meta def elabCalcSteps : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ci ← getConstInfo n
  let some v := ci.value? | throwError "calc_steps: {n} has no proof term to read the steps off"
  let steps ← liftTermElabM <| lambdaTelescope v fun xs b => do
    -- A proof by one law is a chain of one step: `calc a ↔ b := h` elaborates to `h` itself.
    let ls ← leaves b (← inferType b)
    -- A binder the step does not use is no binder of the step: kept, it would have to be supplied
    -- by every caller of a step that never needs it.  Used means in the step, or in a used binder's
    -- type, so the binders are read last to first.
    ls.mapM fun (l, t) => do
      let (t, l) := (← instantiateMVars t, ← instantiateMVars l)
      let mut ys : Array Expr := #[]
      for x in xs.reverse do
        let used (e : Expr) := e.containsFVar x.fvarId!
        if used t || used l || (← ys.anyM fun y => return used (← inferType y)) then ys := ys.push x
      return (← mkForallFVars ys.reverse t, ← mkLambdaFVars ys.reverse l)
  for ((t, p), i) in steps.toList.zipIdx do
    liftCoreM <| withExporting <| addDecl <| .thmDecl
      { name := n ++ Name.mkSimple s!"step_{i + 1}", levelParams := ci.levelParams, type := t, value := p }

end Freyd.Alg.CalcSteps

namespace Freyd.Alg

/-- An implication as a `calc` relation: a `calc` step is an application `r a b`, and `a → b` is
    none, so a chain of statements writes `Imp a b`. -/
public abbrev Imp (a b : Prop) : Prop := a → b

public instance : Trans Imp Imp Imp := ⟨fun h₁ h₂ x => h₂ (h₁ x)⟩
public instance : Trans Iff Imp Imp := ⟨fun h₁ h₂ x => h₂ (h₁.mp x)⟩
public instance : Trans Imp Iff Imp := ⟨fun h₁ h₂ x => h₂.mp (h₁ x)⟩

end Freyd.Alg
