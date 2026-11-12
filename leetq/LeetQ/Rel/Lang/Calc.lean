import LeetQ.Rel.Lang.Embed
import Freyd.S2_30
import AOP.A4_4
import AOP.A4_5
import AOP.A5_2
import AOP.A5_3

/-! `rel(t)`: the Rel term `t` read as a term of the AOP allegory, so that an ordinary Lean statement, and the steps
    of a plain `calc`, can be written in Rel. `t` is the `rel` category of `Embed`, read to `Lang.Expr` by
    `Embed.expr` in a scope whose names are the local variables; the AST is then written as Lean notation and
    elaborated with the ambient instance, so objects and types are Lean's, not the Rel elaborator's. The category
    embeds no `term`: a Lean term reaches a proof only as the justification of a `calc` step.

    The fragment, each with the same meaning in Rel and in AOP (`doc/rel-lean-mapping.md`): a local variable, `R S`,
    `R°`, `R ∩ S`, `R ∪ S`, `R / S`, `R \ S`, `𝟙`, `𝟘`, `⊤`, `dom(R)`, `ran(R)`; `⟨R,S⟩`, `R × S`, `π₁`, `π₂` over
    a `RelProd` instance; `[R,S]`, `inl`, `inr` over a `Coproduct` hypothesis; `∼R`, `R − S` in a
    `BooleanAllegory`. `⊑` and `=` are Lean's, between `rel(…)` terms. Every other construct is an error naming it.

    A product, a coproduct or the Boolean instance is never written in the term: each is a metavariable that
    unification gives its objects, then `fill` takes from the statement's context. -/

namespace LeetQ.Rel.Lang.Calc

open Lean Elab Term Meta
open LeetQ.Rel.Lang
open Freyd Freyd.Alg

/-- A syntax node spanning the source position `p`, for an error at the construct it names. -/
def refAt (p : Lang.Pos) : TermElabM Syntax := do
  let i := (← getFileMap).ofPosition ⟨p.line, p.col - 1⟩; pure (.atom (.synthetic i i) "")

def outside {α : Type} (p : Lang.Pos) (what : String) (why : MessageData) : TermElabM α := do
  throwErrorAt (← refAt p) "{what} {why}"

/-- The context a construct needs and the term does not write: a metavariable of a witness type (`RelProd a b`,
    `Coproduct s a b`, `BooleanAllegory 𝒜`), the construct's place and spelling, and why it needs the witness. -/
abbrev Holes := IO.Ref (Array (Lean.Expr × Lang.Pos × String × String))

/-- A natural metavariable of type `ty`, so that unification may fix its objects before `fill` finds it. -/
def hole (hs : Holes) (p : Lang.Pos) (what why : String) (ty : Term) : TermElabM Term := do
  let w ← mkFreshExprMVar (← elabType ty); hs.modify (·.push (w, p, what, why)); exprToSyntax w

/-- `w` filled from the context: a class by instance search (local instances are the statement's hypotheses), a
    structure by the one hypothesis of its type. Objects still unknown wait for the expected type. -/
def fill (w : Lean.Expr) (p : Lang.Pos) (what why : String) : TermElabM Unit := do
  if (← w.mvarId!.isAssigned) then return
  let ty ← instantiateMVars (← inferType w)
  if ty.hasExprMVar then tryPostpone
  -- printed alone, so that the type never breaks across the message's line
  let tys := toString (← ppExpr ty)
  let set (c : Lean.Expr) := do unless ← isDefEq w c do outside p what m!"cannot use `{c}` as `{tys}`"
  if (← isClass? ty).isSome then
    if ty.hasExprMVar then outside p what m!"needs `{tys}` with objects the statement fixes: {why}"
    match ← synthInstance? ty with
    | some c => set c
    | none => outside p what m!"needs an instance or hypothesis `{tys}`: {why}"
  else
    let cs ← (← getLCtx).foldlM (init := #[]) fun cs d => do
      if d.isImplementationDetail || (← whnfR d.type).getAppFn.constName? != ty.getAppFn.constName? then return cs
      return if ← withoutModifyingState (isDefEq d.type ty) then cs.push d.toExpr else cs
    match cs with
    | #[c] => set c
    | #[] => outside p what m!"needs a hypothesis `{tys}`: {why}"
    | _ => outside p what m!"has several hypotheses `{tys}`, {", ".intercalate (← cs.toList.mapM fun c =>
        return toString (← ppExpr c))}: {why}"

def prod (hs : Holes) (p : Lang.Pos) (what : String) : TermElabM Term := do
  hole hs p what "rel(…) never writes the product" (← `(Freyd.Alg.RelProd _ _))

def coprod (hs : Holes) (p : Lang.Pos) (what : String) : TermElabM Term := do
  hole hs p what "rel(…) never writes it, and a structure is found by no instance search"
    (← `(Freyd.Alg.Coproduct _ _ _))

/-- The operand `a` of a complement elaborated, its allegory `𝒜` (the type of its target) and the instance
    `BooleanAllegory 𝒜`, found before the complement is: AOP's `∼R` is the Heyting `R ⇨ 𝟘`, which is the complement
    Rel means only in a Boolean allegory. -/
def boolean (p : Lang.Pos) (what : String) (a : Term) : TermElabM (Term × Term × Term) := do
  let e ← elabTerm a none
  let t ← instantiateMVars (← inferType e)
  if !t.isApp then outside p what m!"has an operand of type `{t}`, not an arrow"
  let c ← instantiateMVars (← inferType t.appArg!)
  if c.hasExprMVar then tryPostpone; outside p what m!"has an operand `{t}` in no fixed allegory"
  let ty ← elabType (← `(Freyd.Alg.BooleanAllegory $(← exprToSyntax c)))
  let tys := toString (← ppExpr ty)
  let some i ← synthInstance? ty | outside p what (m!"needs an instance `{tys}`: AOP's `∼R` is the Heyting " ++
    m!"`R ⇨ 𝟘`, the complement only in a Boolean allegory")
  pure (← exprToSyntax c, ← exprToSyntax i, ← exprToSyntax e)

/-- `e` written as AOP notation; `vars` the local variables a name may be, `hs` the products and coproducts. -/
partial def toTerm (vars : List String) (hs : Holes) : Lang.Expr → TermElabM Term
  | .name p n => if vars.contains n then pure (mkIdent (.mkSimple n)) else
      outside p s!"`{n}`" "is not a local variable: a name in rel(…) is a variable or hypothesis of the statement"
  | .comp a b => do `($(← toTerm vars hs a) ≫ $(← toTerm vars hs b))
  | .conv _ a => do `($(← toTerm vars hs a)°)
  | .compl p a => do let (c, _, a) ← boolean p "`∼R`" (← toTerm vars hs a); `(Freyd.Alg.neg (𝒜 := $c) $a)
  | .bin p o a b => do
    let (a, b) := (← toTerm vars hs a, ← toTerm vars hs b)
    match o with
    | .meet => `($a ∩ $b)
    | .join => `($a ∪ $b)
    | .rdiv => `($a / $b)
    | .ldiv => `($a \ $b)
    | .diff => do let (c, i, a) ← boolean p "`R − S`" a; `(@Freyd.Alg.sub $c $i _ _ $a $b)
    | .prod => `(Freyd.Alg.prodMap $(← prod hs p "`R × S`") $(← prod hs p "`R × S`") $a $b)
  | .pair p a b => do
    `(Freyd.Alg.RelProd.pair $(← prod hs p "`⟨R,S⟩`") $(← toTerm vars hs a) $(← toTerm vars hs b))
  | .junc p a b => do `(Freyd.Alg.junc $(← coprod hs p "`[R,S]`") $(← toTerm vars hs a) $(← toTerm vars hs b))
  | .op _ .id [] [] => `(𝟙 _)
  | .op _ .zero [] [] => `(𝟘)
  | .op _ .top [] [] => `(topHom _ _)
  | .op _ .dom [] [a] => do `(Freyd.Alg.dom $(← toTerm vars hs a))
  | .op _ .ran [] [a] => do `(Freyd.Alg.ran $(← toTerm vars hs a))
  | .op p .outl [] [] => do `(Freyd.Alg.RelProd.π₁ (self := $(← prod hs p "`π₁`")))
  | .op p .outr [] [] => do `(Freyd.Alg.RelProd.π₂ (self := $(← prod hs p "`π₂`")))
  | .op p .inl [] [] => do `(Freyd.Alg.Coproduct.u₁ $(← coprod hs p "`inl`"))
  | .op p .inr [] [] => do `(Freyd.Alg.Coproduct.u₂ $(← coprod hs p "`inr`"))
  | .op p o (_ :: _) _ => outside p s!"`{o.sym}(…)`" "names Rel objects: rel(…) takes its objects from the Lean types"
  | .op p (.index i) _ _ => outside p s!"`at({i})`" "has no AOP counterpart"
  | .op p o@.mem _ _ | .op p o@.lam _ _ | .op p o@.E _ _ | .op p o@.P _ _ | .op p o@.est _ _ | .op p o@.thin _ _
  | .op p o@.union _ _ | .op p o@.tau _ _ | .op p o@.setify _ _ => outside p s!"`{o.sym}`"
      "differs in AOP: Rel reads a set `𝒫A` as an array `[α]`, AOP as the power object `P A`"
  | .op p .map _ _ => outside p "`F(R)`" "differs in AOP: Rel's `F` is the list functor only, AOP's any relator"
  | .op p o _ _ => outside p s!"`{o.sym}`" "is outside the allegory fragment of rel(…)"
  | .lit p _ => outside p "a literal `{…}`" "has no AOP counterpart"
  | .fold p .. => outside p "`⦇e,S⦈`" ("differs in AOP: Rel folds lists from a start set `e : V ⟶ V`, AOP's " ++
      "`⦇R⦈` folds one algebra of an `InitialAlgebra F`, and AOP has the list functor only in `RelSet`")
  | .app p n _ | .inf p n .. => outside p s!"`{n}`" "is a Rel definition, and rel(…) has none"

-- `withoutPosition`: juxtaposition may cross a line here, the term ends at its `)`
syntax (name := relTerm) "rel(" withoutPosition(rel) ")" : term

@[term_elab relTerm] def elabRel : TermElab := fun stx ty? => do
  let vars := (← getLCtx).foldl (init := []) fun ns d =>
    if d.isImplementationDetail || d.userName.hasMacroScopes then ns else d.userName.toString false :: ns
  match ((Embed.expr stx[1]).run (← getFileMap)).run' { cs := #[], known := vars.map (·, 0) } with
  | .error e => throwErrorAt (← refAt e.pos) "{e.msg}"
  | .ok e => withRef stx do
    let hs ← IO.mkRef #[]
    let r ← elabTermEnsuringType (← toTerm vars hs e) ty?
    synthesizeSyntheticMVars (postpone := .yes)
    for (w, p, what, why) in ← hs.get do fill w p what why
    pure r

end LeetQ.Rel.Lang.Calc
