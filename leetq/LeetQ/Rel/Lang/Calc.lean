import LeetQ.Rel.Lang.Embed
import Freyd.S2_30
import AOP.A4_4

/-! `rel(t)`: the Rel term `t` read as a term of the AOP allegory, so that an ordinary Lean statement, and the steps
    of a plain `calc`, can be written in Rel. `t` is the `rel` category of `Embed`, read to `Lang.Expr` by
    `Embed.expr` in a scope whose names are the local variables; the AST is then written as Lean notation and
    elaborated with the ambient instance, so objects and types are Lean's, not the Rel elaborator's. The category
    embeds no `term`: a Lean term reaches a proof only as the justification of a `calc` step.

    The fragment, each with the same meaning in Rel and in AOP (`doc/rel-lean-mapping.md`): a local variable, `R S`,
    `R°`, `R ∩ S`, `R ∪ S`, `R / S`, `R \ S`, `𝟙`, `𝟘`, `⊤`; `⊑` and `=` are Lean's, between `rel(…)` terms. Every
    other construct is an error naming it. -/

namespace LeetQ.Rel.Lang.Calc

open Lean Elab Term
open LeetQ.Rel.Lang
open Freyd Freyd.Alg

/-- A syntax node spanning the source position `p`, for an error at the construct it names. -/
def refAt (p : Lang.Pos) : TermElabM Syntax := do
  let i := (← getFileMap).ofPosition ⟨p.line, p.col - 1⟩; pure (.atom (.synthetic i i) "")

def outside {α : Type} (p : Lang.Pos) (what why : String) : TermElabM α := do
  throwErrorAt (← refAt p) "{what} {why}"

/-- `e` written as AOP notation; `vars` the local variables a name may be. -/
partial def toTerm (vars : List String) : Lang.Expr → TermElabM Term
  | .name p n => if vars.contains n then pure (mkIdent (.mkSimple n)) else
      outside p s!"`{n}`" "is not a local variable: a name in rel(…) is a variable or hypothesis of the statement"
  | .comp a b => do `($(← toTerm vars a) ≫ $(← toTerm vars b))
  | .conv _ a => do `($(← toTerm vars a)°)
  | .bin p o a b => do
    let (a, b) := (← toTerm vars a, ← toTerm vars b)
    match o with
    | .meet => `($a ∩ $b)
    | .join => `($a ∪ $b)
    | .rdiv => `($a / $b)
    | .ldiv => `($a \ $b)
    | .diff => outside p "`R − S`" "differs in AOP: there `R − S` is `R ∩ ∼S`, `∼` the Heyting `R ⇨ 𝟘`"
    | .prod => outside p "`R × S`" "differs in AOP: `prodMap` takes an explicit `RelProd` witness"
  | .op _ .id [] [] => `(𝟙 _)
  | .op _ .zero [] [] => `(𝟘)
  | .op _ .top [] [] => `(topHom _ _)
  | .op p (.index i) _ _ => outside p s!"`at({i})`" "has no AOP counterpart"
  | .op p o _ _ => outside p s!"`{o.sym}`" "is outside the allegory fragment of rel(…)"
  | .lit p _ => outside p "a literal `{…}`" "has no AOP counterpart"
  | .compl p _ => outside p "`∼R`" "differs in AOP: there `∼R` is the Heyting `R ⇨ 𝟘`, a complement only when Boolean"
  | .pair p .. => outside p "`⟨R,S⟩`" "differs in AOP: `RelProd.pair` takes an explicit product witness"
  | .junc p .. => outside p "`[R,S]`" "differs in AOP: `junc` takes an explicit `Coproduct` witness"
  | .fold p .. => outside p "`⦇e,S⦈`" "differs in AOP: `⦇R⦈` folds an `InitialAlgebra`, not a list from a seed"
  | .app p n _ | .inf p n .. => outside p s!"`{n}`" "is a Rel definition, and rel(…) has none"

-- `withoutPosition`: juxtaposition may cross a line here, the term ends at its `)`
syntax (name := relTerm) "rel(" withoutPosition(rel) ")" : term

@[term_elab relTerm] def elabRel : TermElab := fun stx ty? => do
  let vars := (← getLCtx).foldl (init := []) fun ns d =>
    if d.isImplementationDetail || d.userName.hasMacroScopes then ns else d.userName.toString false :: ns
  match ((Embed.expr stx[1]).run (← getFileMap)).run' { cs := #[], known := vars.map (·, 0) } with
  | .error e => throwErrorAt (← refAt e.pos) "{e.msg}"
  | .ok e => withRef stx do elabTerm (← toTerm vars e) ty?

end LeetQ.Rel.Lang.Calc
