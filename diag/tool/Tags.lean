/-
  `Tags` — what `diag/StrDiagNames.lean` needs of the exporter: the attributes the note's vocabulary
  is tagged with and the object-action reduction its delaborator asks.  A library module imports
  this and not the reader, so the exporter's code is no module of the statements it draws, and an
  edit of it leaves the verdict cache's `depText` of every statement unchanged.
-/
import Lean
import AOP.A5_7

open Lean

/-- WHICH DEFINITIONS A PICTURE OPENS.  The mirror of a name kept: where the NOTE writes a `def`'s
    BODY and Lean prints its name, the picture is of the body, so the exporter opens it before
    drawing.  Registered HERE, in the module the reader imports — an attribute is only usable in a
    module that imports the one declaring it, so the tags go in `diag/StrDiagNames.lean`. -/
register_label_attr diag_unfold

/-- WHICH DEFINITIONS ONLY A PICTURE OPENS.  `diag_unfold`'s weaker form: a picture needs the body's
    wires, but a FORMULA keeps the name — the note writes `Pres(S,Q)`, never the inequation it
    abbreviates.  Registered here and tagged in `diag/StrDiagNames.lean`, like `diag_unfold`. -/
register_label_attr diag_drawn_open

/-- WHICH CONSTANTS THE NOTE WRITES BY THEIR OWN NAME.  `checkSpelled` refuses a label that carries
    a constant no printing rule rewrote, because a page would then make its claim in Lean's
    vocabulary; but a name the note writes UNCHANGED — `dom`, `Entire`, `Map`, a case study's own
    `secureP` — has nothing to rewrite, and an identity unexpander per constant is that fact written
    fifteen times.  The tag is the declaration that this name IS the note's, one word per name, and
    an untagged constant is refused exactly as before.  Registered here, tagged in
    `diag/StrDiagNames.lean`, for the same reason as `diag_unfold`. -/
register_label_attr diag_noted

/-- WHICH FAMILIES WRITE THEIR INDEX BENEATH THEIR LETTER.  A family the theory DECLARES wears a
    notation of its own, and that notation spells the letter alone — `α` for the algebra of a
    parametrised initial algebra — so the object it is taken at is missing from the label and the
    note sets it as a subscript (`α`#sub[`A`], `α`#sub[`B`], the two ends of one naturality square).
    NOT derivable from the type: `∋ A`, `π₁ A B P` and `φ A` are components of families too and the
    note writes every one of them without an index, so what is tagged is the family whose picture
    needs telling apart, and the tag is one line beside the declaration.  Registered here, tagged in
    `diag/StrDiagNames.lean`, for the same reason as `diag_unfold`. -/
register_label_attr diag_indexed

/-- WHICH EQUATIONS A SIDE IS REWRITTEN ALONG before it is drawn.  The mirror of a name opened: where
    the NOTE draws a factor as two beads and Lean's statement names it as one, the side is rewritten
    by the declaration that says so, so the picture is of the note's form.  Registered here, tagged
    in `diag/StrDiagNames.lean`, for the same reason as `diag_unfold`. -/
register_label_attr diag_rewrite

/-- WHICH EQUATION DEFINES AN INDUCED ARROW.  The mirror of `diag_induced`: that attribute says a
    constant's application is what a universal property GIVES, this one says which theorem is the
    equation it gives it BY — `relCata_cancel`, `α⦇R⦈=F(⦇R⦈)R`.  A commutative diagram draws that
    square where the picture has to say what produced the arrow
    (`diag/tool/CommutativeDiagram.lean`, `definingFace`), finding it by UNIFYING the law's own
    induced arrow with the one in hand, so one tag answers every instance.  Registered here rather
    than beside `diag_induced` because the tags live in `diag/StrDiagNames.lean`, which imports this
    module and not the drawer. -/
register_label_attr diag_defines

/-- WHICH ARROWS ONLY RE-BRACKET A PRODUCT.  `×` is FLAT in the picture — a lane `A×−` per factor,
    so `(A×B)×Y` and `A×(B×Y)` are the one stack — and an arrow between two ends that peel to that
    one stack therefore has nothing to draw: it is the identity as far as the geometry is concerned
    (the note, `diag/ch/13-optimisation.typ`: "`assocl` draws nothing").  WHICH constants those are
    is a convention and not a shape, so it is TAGGED, like `diag_unfold` and `diag_rewrite`, and
    tagged in `diag/StrDiagNames.lean`; a converse of one is one, which `coherenceId?` reads off the
    term.  Any OTHER arrow between two equal stacks is a bead like any other. -/
register_label_attr diag_coherence

/-- WHICH CONVERSES HAVE A NAME OF THEIR OWN (CLAUDE.md: `≥`, never `≤°`).  The tag goes on the
    THEOREM `Q = P°` that makes the pair, so a pair nobody proved cannot be declared; the converse of
    `P` is then drawn as `Q` and the converse of `Q` as `P`, each spelled by its own printing rule.
    Registered here, tagged in `diag/StrDiagNames.lean`, for the same reason as `diag_unfold`. -/
register_label_attr diag_opposite

/-- WHICH BINARY OPERATION ON ONE HOM IS A JOIN, and the symbol that stands between the panels it
    draws.  An assertion about a JOIN is ONE PANEL PER OPERAND — the note's `∪` row of
    `<lax-closure>` is two squares with `∪` between them — where a MEET is one bead and one panel,
    which is what `laxNatural_inter_false` makes it.  The two have the SAME type, so nothing but the
    operator itself separates them: it is TAGGED and never matched, and the tag CARRIES ITS SYMBOL
    (`@[diag_join "∪"]`), so no drawer spells an operator and a new join costs one line beside its
    declaration.  Registered here, tagged in the module that reads it, like `diag_defines`. -/
syntax (name := diagJoin) "diag_join " str : attr

/-- The tagged operators, each with its symbol.  An EXTENSION and not a `ParametricAttribute`
    because the operator is in an imported module — the allegory's `∪` is not the picture's to
    edit — and a parametric attribute refuses those. -/
initialize diagJoinExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun es => es.foldl (fun m a => a.foldl (fun m (n, s) => m.insert n s) m) {} }

initialize registerBuiltinAttribute {
  name := `diagJoin
  descr := "a binary operation on one hom drawn as one panel per operand, with this symbol between"
  add := fun decl stx _ => do
    let sym ← match stx with
      | `(attr| diag_join $s:str) => pure s.getString
      | _ => throwError "diag_join takes the symbol the panels are separated by, as in \
          `@[diag_join \"∪\"]`"
    modifyEnv (diagJoinExt.addEntry · (decl, sym)) }

namespace Freyd.StrDiag

/-- THE RELATOR ALGEBRA'S COMBINATORS: the `def`s that BUILD a relator out of parts, where a NAMED
    relator (`E`, `list⁺`, `F`, `bag`) is a declaration of its own and a lane variable is no
    constant at all.  ONE LIST, because the label, the wire stack and the printer all ask the same
    question of it (`relatorObj?`) and two copies of it drift. -/
def relatorCombinators : Array Name :=
  #[``Freyd.Alg.Relator.const, ``Freyd.Alg.Relator.idRelator, ``Freyd.Alg.Relator.comp,
    ``Freyd.Alg.Relator.sum, ``Freyd.Alg.Relator.prod, ``Freyd.Alg.Relator.pair,
    ``Freyd.Alg.timesRel]

/-- LEAN'S PLUMBING INSIDE A COMBINATOR'S BODY, and nothing else: the identity relator's action is
    written `id` and the composite's `∘`, neither of which is an object.  They are unfolded as the
    combinator itself is, and the first head that is NOT one of them IS the object — a product
    apex, a coproduct, a named relator's own action — where the reduction stops. -/
def relatorPlumbing : Array Name := #[``id, ``Function.comp]

/-- THE OBJECT AN ACTION REDUCES TO, at REDUCIBLE transparency and one unfolding of the plumbing at
    a time: at the default transparency `whnf` unfolds the allegory's own product past `RelProd.p`
    into an instance's implementation, which is not an object the note writes. -/
partial def reduceObjAction (e : Expr) : MetaM Expr := do
  let v ← Meta.withTransparency .reducible (Meta.whnf e)
  let .const c _ := v.getAppFn | return v
  unless relatorPlumbing.contains c do return v
  let some v' ← Meta.unfoldDefinition? v | return v
  reduceObjAction v'

/-- THE OBJECT A COMBINATOR RELATOR'S ACTION REDUCES TO — `(const V).obj X` is `V`, `𝟙.obj X` is
    `X`, `(V×𝟙).obj X` is `V×X` — and `none` for every other relator, whose `F(X)`/`FX` stands.
    The note writes the OBJECT the action is, never the combinator applied to it: `(V×𝟙)(X)` and
    the `EV(list⁺(V))` it seams into write an action nothing performs.

    BY LEAN'S OWN UNFOLDING, never by building the product or the sum here — the combinator's `def`
    is unfolded and the projection and beta steps are `reduceObjAction`'s, so what comes back is the
    very `Expr` Lean holds for the object and it prints by whatever rule already prints one.

    THE WHOLE ACTION, not the relator alone: a binary relator's action stands at two arguments and
    an action reached through another field is still that field's, so what is reduced is the
    application in hand.  BY THE HEAD CONSTANT, never by the name the relator prints, and asked in
    every place a picture spells an object action — the label, the circuit's own wire stack, and
    the delaborator (`diag/StrDiagNames.lean`) for what the printer writes — so a wire and the
    label above it cannot disagree. -/
def relatorObj? (f e : Expr) : MetaM (Option Expr) := do
  let f ← instantiateMVars f
  let r := if f.isAppOf ``Freyd.Alg.Relator.toFunctor then f.appArg! else f
  let .const c _ := r.getAppFn | return none
  unless relatorCombinators.contains c do return none
  let some r' ← Meta.unfoldDefinition? r | return none
  let e ← instantiateMVars e
  let v ← reduceObjAction (e.replace fun s => if s == r then some r' else none)
  return if v == e then none else some v

end Freyd.StrDiag
