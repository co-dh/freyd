/-
  `ExprReader` — the Expr side of the theorem visualizer: a declaration's ELABORATED TYPE read as
  the 2-categorical data a picture is drawn from.  Nothing here reads a formula string, a signature
  table or the note; the types come from the environment, which is the only place they are true.

  THE SOURCE 2-CATEGORY.  A 0-cell is an allegory `𝒜`, a 1-cell a `Relator 𝒜 ℬ`, a 2-cell a family
  `φ : ∀ a, G.obj a ⟶ F.obj a` together with a proof that it is natural.  An OBJECT `a : 𝒜` is the
  1-cell `𝟏 → 𝒜` and an ARROW `R : a ⟶ b` a 2-cell between two such, which is why a factor that is a
  fixed arrow — not a family in the region's object — can only ride the object wire.

  THE DOT IS A THEOREM, NOT A FIELD.  `dot` builds `StrictNatural F G φ`, `LaxNatural F G φ` and
  `¬ LaxNatural G F φ` and looks for a declaration in the environment proving one; nothing is
  inferred from the family's shape or its name.  No declaration, no dot.
-/
import Lean
import AOP.A5_7

open Lean

namespace Freyd.StrDiag

/-- Lean's pretty printer on one line, the repo's own namespaces off: inside a picture of the
    repo's algebra `Freyd.Alg.relCata R` is noise and `⦇R⦈` is the thing itself. -/
def plain (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  let s := s.replace "Freyd.Alg.RelSet." "" |>.replace "Freyd.Alg." "" |>.replace "Freyd." ""
    |>.replace "Alg." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- The source and target of a hom type `a ⟶ b`. -/
def homObjs? (t : Expr) : Option (Expr × Expr) :=
  match t.getAppFnArgs with
  | (``Cat.Hom, #[_, _, a, b]) => some (a, b)
  | _ => none

/-- The last two arguments of an application. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- The WIRES a functor expression is: `Relator.comp F G` is not one wire but two NESTED, `G`
    outside `F`, and the identity relator is no wire at all.  Outermost first, as a wire stack is
    read left to right in the picture. -/
partial def wiresOf (f : Expr) : Array Expr :=
  match f.getAppFnArgs with
  | (``Freyd.Alg.Relator.toFunctor, args) => match args.back? with
    | some r => wiresOf r
    | none => #[f]
  | (``Freyd.Alg.Relator.comp, args) => match lastTwo args with
    | some (a, b) => wiresOf b ++ wiresOf a
    | none => #[f]
  | (``Freyd.Alg.Relator.idRelator, _) => #[]
  | (``Freyd.idFunctor, _) => #[]
  | _ => #[f]

/-- An object peeled into its wire stack (outermost first) and the object underneath. -/
partial def peelObj (e : Expr) : Array Expr × Expr :=
  match e.getAppFnArgs with
  | (``Freyd.Functor.obj, args) => match lastTwo args with
    | some (f, x) => let (ws, o) := peelObj x; (wiresOf f ++ ws, o)
    | none => (#[], e)
  | _ => (#[], e)

/-- A factor with the relators it runs UNDER stripped off: `F.map (G.map R)` is `R` with the wires
    `F`, `G` running past it.  Outermost first. -/
partial def peelMap (e : Expr) : Array Expr × Expr :=
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      let (ws, r) := peelMap args[args.size - 1]!
      (wiresOf args[4]! ++ ws, r)
    else (#[], e)
  | _ => (#[], e)

/-- A composite flattened into its factors, in diagram order. -/
partial def factors (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``Cat.comp, args) => match lastTwo args with
    | some (f, g) => factors f ++ factors g
    | none => #[e]
  | _ => #[e]

/-! ### The dot

  A bead between the wire stack `G` (what it eats) and `F` (what it makes) is a 2-cell only if a
  DECLARATION says so.  The search is over the environment: a constant whose type, under its `∀`
  binders, is one of the three propositions the bead could satisfy, unified against the wanted one.
  Filtering first on the constants the family mentions keeps it to a handful of candidates. -/

/-- Every constant a term is built from — the cheap filter that says which declarations could
    possibly be about this bead. -/
partial def consts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .app f a => consts a (consts f acc)
  | .lam _ t b _ | .forallE _ t b _ => consts b (consts t acc)
  | .const n _ => acc.insert n
  | .mdata _ b | .proj _ _ b => consts b acc
  | .letE _ t v b _ => consts b (consts v (consts t acc))
  | _ => acc

/-- The head of a statement's CONCLUSION, under whatever `∀` binders it carries. -/
partial def concHead : Expr → Name
  | .forallE _ _ b _ => concHead b
  | .mdata _ b => concHead b
  | t => (t.getAppFn.constName?).getD Name.anonymous

/-- Is `want` proved by some declaration of the environment?  Candidates are the constants whose
    conclusion is headed by `head` and whose statement mentions everything the family does; each
    one's type is opened with metavariables and unified with `want`. -/
def findProof (want : Expr) (head : Name) (must : NameSet) : MetaM (Option Name) := do
  let env ← getEnv
  let mut hit : Option Name := none
  for (n, ci) in env.constants do
    if hit.isSome then break
    if n.isInternal || ci.isUnsafe || concHead ci.type != head then continue
    let has := consts ci.type
    if must.any (fun m => !has.contains m) then continue
    let (_, _, body) ← Meta.forallMetaTelescope ci.type
    if ← Meta.isDefEq body want then hit := some n
  return hit

end Freyd.StrDiag
