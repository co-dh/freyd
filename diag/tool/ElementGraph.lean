/-
  ElementGraph — the ELEMENT-GRAPH functor: a concrete relation between finite sets, drawn element
  by element.

  `./scripts/diag-export --graph Freyd.S2_30.Example.A+Freyd.S2_30.Example.H` writes
  `diag/generated/graph/<selector>.typ`, a data file `diag/gpanel.typ` draws.

  THE ELEMENTS ARE THE CONSTRUCTORS.  A relation here is a declaration `R : α → β → Prop` whose `α`
  and `β` are inductive types with argument-free constructors, so the elements are read off the
  environment, in declaration order, and nothing lists them twice.

  THE EDGES ARE DECIDED.  For every pair `(a, b)` the functor synthesises `Decidable (R a b)` and
  reduces `decide (R a b)` to `true` or `false`; a pair that reduces to neither ends the run naming
  it, so a relation Lean cannot evaluate draws a red stub, never an empty graph.

  The layout — which column a type stands in, where an element sits, how a relation is inked — is
  the note's call's, because it says nothing about which pairs hold.
-/
import Lean

open Lean Meta

namespace Freyd.ElementGraph

/-- Typst string literal: only `\` and `"` can end it early. -/
def typstString (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- The last component of a name as the note spells it: `A.«1»` is `1`, not `«1»`. -/
def short (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The elements of a finite type: an inductive type whose constructors take no argument. -/
def elements (ty : Expr) : MetaM (Name × List Expr) := do
  let ty ← whnf ty
  let .const I us := ty | throwError "the element type {ty} is not a bare inductive type"
  let some (.inductInfo iv) := (← getEnv).find? I
    | throwError "the element type {I} is not an inductive type"
  let cs ← iv.ctors.mapM fun c => do
    let ci ← getConstInfo c
    if ci.type.isForall then
      throwError "constructor {c} takes arguments, so {I} is not a finite set of named elements"
    return mkConst c us
  return (I, cs)

/-- Whether `R a b` holds, by reducing `decide (R a b)`. -/
def holds (rel a b : Expr) : MetaM Bool := do
  let p := mkApp2 rel a b
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let r ← withTransparency .all <| whnf (mkApp2 (mkConst ``Decidable.decide) p inst)
  if r.isConstOf ``Bool.true then return true
  if r.isConstOf ``Bool.false then return false
  throwError "deciding {p} reduced to {r}, which is neither `true` nor `false`"

/-- One relation as a typst dictionary: its key, its two element types, their elements, its pairs. -/
def relation (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  let rel := mkConst n (ci.levelParams.map mkLevelParam)
  forallTelescopeReducing ci.type fun xs body => do
    unless xs.size == 2 && body.isProp do
      throwError "{n} is not a relation `α → β → Prop` between two finite types: {ci.type}"
    let (src, as) ← elements (← inferType xs[0]!)
    let (tgt, bs) ← elements (← inferType xs[1]!)
    let mut pairs : Array String := #[]
    for a in as do
      for b in bs do
        if ← holds rel a b then
          pairs := pairs.push s!"({typstString (short a.constName!)}, {typstString (short b.constName!)})"
    let names (es : List Expr) := ", ".intercalate (es.map fun e => typstString (short e.constName!))
    return s!"  (key: {typstString (short n)}, src: {typstString (short src)}, \
      tgt: {typstString (short tgt)},\n    srcs: ({names as},), tgts: ({names bs},),\n    \
      pairs: ({", ".intercalate pairs.toList},)),"

/-- The file for one selector: every `+`-joined relation of it, drawn on one canvas. -/
def file (sel : String) : MetaM String := do
  let rels ← (sel.splitOn "+").mapM fun p => relation p.toName
  return "#let graph = (\n" ++ "\n".intercalate rels ++ "\n)\n"

end Freyd.ElementGraph
