/-
  `ValueTree` — a DATA VALUE that is a tree, drawn as a tree: `diag-export --value`, the note's
  `#leanv("<decl>")`.

  The note's example trees are values, not statements: a hand-laid canvas of one says what its author
  typed, and the `def` the proofs run on can say something else.  So the picture is READ OFF THE
  DECLARATION: its value is reduced constructor by constructor, and a node is one constructor
  application of the declaration's own type.

  WHAT A NODE IS, from the type alone.  A field of the declaration's type is a CHILD; a field whose
  type merely contains it (`ConsList Unit (Rose A)`) is a container, walked for the children inside
  it in order; every other field is a LABEL, a structure's fields each a label of their own (the
  employee `('a', 3)` is `a` and `3`).  Nothing here knows `Rose`: any inductive tree type draws.

  THE LAYOUT IS THE VALUE'S: leaves take consecutive columns left to right, and a parent stands
  midway between its first and last child, one level above them.  `diag/vtree.typ` only scales.
-/
import diag.tool.StringDiagram
import diag.tool.CommutativeDiagram

open Lean Meta

namespace Freyd.ValueTree

open Freyd.StrDiag

/-- One node of the drawn value: its labels, and its children in order. -/
structure Node where
  labels : Array String
  kids : Array Node

/-- The constructor `e` reduces to, and its fields (the arguments after the parameters). -/
def ctorFields (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  let some (.ctorInfo c) := e.getAppFn.constName?.bind (← getEnv).find? |
    throwError "{← ppExpr e} does not reduce to a constructor, so it is not a value to draw"
  unless e.getAppNumArgs == c.numParams + c.numFields do
    throwError "{← ppExpr e} is a partially applied constructor {c.name}"
  return e.getAppArgs.extract c.numParams e.getAppNumArgs

/-- A label field in the note's spelling.  A character literal is its character: `plain` would
    print Lean's quotes, `'a'`, where the note names the employee `a`. -/
partial def labels (x : Expr) : MetaM (Array String) := do
  if x.isAppOfArity ``Char.ofNat 1 then
    if let .lit (.natVal n) := x.appArg! then return #[(Char.ofNat n).toString]
  -- A STRUCTURE's fields are labels each: a node carrying a pair shows both components.
  if let some (.ctorInfo c) := x.getAppFn.constName?.bind (← getEnv).find? then
    if isStructure (← getEnv) c.induct && x.getAppNumArgs == c.numParams + c.numFields then
      return ← (x.getAppArgs.extract c.numParams x.getAppNumArgs).foldlM
        (fun a f => return a ++ (← labels f)) #[]
  return #[← plain x]

/-- The fields of `e`'s constructor sorted by their type against the tree type `T` (head `h`):
    the children, found through any container, and the labels.  A container's own non-tree fields
    (a list's `()`) are its, not the node's, so only the node keeps its labels. -/
partial def split (h : Name) (T e : Expr) : MetaM (Array String × Array Node) := do
  (← ctorFields e).foldlM (init := (#[], #[])) fun (ls, ks) x => do
    let t ← inferType x
    if ← isDefEq t T then
      let (l, k) ← split h T x
      return (ls, ks.push { labels := l, kids := k })
    else if (t.find? (·.isConstOf h)).isSome then return (ls, ks ++ (← split h T x).2)
    else return (ls ++ (← labels x), ks)

/-- The declaration's value as a tree, printed under its own file's scopes. -/
def read (declName : Name) : MetaM Node := withDeclScope declName do
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  let some h := ci.type.getAppFn.constName? |
    throwError "{declName} : {← ppExpr ci.type} is not a value of an inductive type"
  unless (← getEnv).find? h matches some (.inductInfo _) do
    throwError "{declName} : {← ppExpr ci.type} is not a value of an inductive type"
  let (l, k) ← split h ci.type (mkConst declName (ci.levelParams.map mkLevelParam))
  return { labels := l, kids := k }

/-- One placed node: its column, its level, its labels. -/
structure Placed where
  x : Float
  depth : Nat
  labels : Array String
  deriving Inhabited

/-- Pre-order placement: the next free leaf column, the nodes placed so far, the edges as index
    pairs parent→child.  Returns the node's index. -/
partial def place (n : Node) (depth : Nat) :
    StateM (Nat × Array Placed × Array (Nat × Nat)) Nat := do
  let i := (← get).2.1.size
  modify fun (c, ps, es) => (c, ps.push { x := 0, depth, labels := n.labels }, es)
  if n.kids.isEmpty then
    modify fun (c, ps, es) => (c + 1, ps.modify i ({ · with x := c.toFloat }), es)
  else
    let ks ← n.kids.mapM (place · (depth + 1))
    modify fun (c, ps, es) =>
      (c, ps.modify i ({ · with x := (ps[ks[0]!]!.x + ps[ks.back!]!.x) / 2 }), es ++ ks.map (i, ·))
  return i

/-- The file a note's `#leanv` imports: `pic`, the placed nodes and edges handed to `vtree`. -/
def file (declName : Name) : MetaM String := do
  let (_, ps, es) := ((place (← read declName) 0).run (0, #[], #[])).2
  -- A typst array: `()` when empty, and a trailing comma so one element is not a parenthesis.
  let arr (xs : List String) := if xs.isEmpty then "()" else "(" ++ ", ".intercalate xs ++ ",)"
  let nodes := ps.toList.map fun p => s!"(x: {p.x}, depth: {p.depth}, labels: \
    {arr (p.labels.toList.map Freyd.CommutativeDiagram.typstString)})"
  return s!"#import \"../../vtree.typ\": vtree\n\n#let pic = vtree(\n  {arr nodes},\n  \
    {arr (es.toList.map fun (a, b) => s!"({a}, {b})")})\n"

end Freyd.ValueTree
