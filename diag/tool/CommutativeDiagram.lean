/-
  CommutativeDiagram — the COMMUTATIVE-DIAGRAM functor: a declaration's STATEMENT drawn as a graph.

  `./scripts/diag-export --commutative AOP.A5_5_TypeFunctor.alpha_natural` writes
  `diag/generated/commutative/<name>.typ`, a page that imports `../../cdpanel.typ` and draws the
  face the statement asserts.

  THE FUNCTOR.  The source is the 1-category the statement lives in, the target a graph:

    an object `a`                a node labelled `a`
    an arrow `R : a ⟶ b`         an edge `a → b` labelled `R`
    `R ≫ S`                      the two edges end to end — the functor law, and the only
                                 structural case: any other arrow expression is ONE edge
    `𝟙 a`                        the empty path
    `L = R`, `L ⊑ R`             one face, the two paths sharing their ends, the symbol between

  Nothing here reads a table, a formula string or the note.  The nodes come from `inferType`ing each
  factor and reading `Cat.Hom`'s two object arguments, so the picture is the type, not a transcript
  of it; the labels are `Meta.ppExpr` under the repo's own notations, through `DiagExport.labelAt`.

  A NAMED PREDICATE IS OPENED, NOT SPECIAL-CASED.  `StrictNatural F G φ` and `LaxNatural F G φ` are
  `∀`-quantified equations behind a constant, so the loop that draws them is the general one: open
  the binders, and if the body is not yet an equation take ONE delta step on its head and open the
  binders that step exposed.  The naturality square with corners `G a, G b, F a, F b` then falls out
  of the equation the definition unfolds to, and every other predicate defined the same way draws
  without another line here.

  THE GRID IS COMPUTED FROM THE PATH LENGTHS.  The two paths share their start (top left) and their
  end (bottom right).  The left-hand path runs clockwise — along the top, then down the right — and
  the right-hand path counter-clockwise, down the left then along the bottom; each leg carries half
  the path's edges, the horizontal leg taking the odd one so a three-edge path turns once.  A path of
  ONE edge cannot turn a corner and is the chord.  Two edges on one side and two on the other is a
  square, two against one a triangle, one against four a pentagon — none of that is typed per
  declaration.  Column and row SPACING is not settled here: only `cdpanel` can measure a label, so
  this file emits grid coordinates and the panel turns them into centimetres.
-/
-- `AOP.A4_5` pulls the `Freyd` core and the allegory layer, so `Cat.comp`, `Cat.Hom` and `Alg.le`
-- are names this file can quote.  It does NOT import `DiagExport`: that module imports THIS one, to
-- route `--commutative`, and the four helpers below are its own, copied rather than made circular.
import Lean
import AOP.A4_5

open Lean

namespace Freyd.CommutativeDiagram

/-! ### `DiagExport`'s helpers, copied because the import runs the other way -/

/-- The two arrow arguments of a binary operator applied with instance and object arguments. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- Typst string literal: only `\` and `"` can end it early. -/
def typstString (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- Two decimal places.  `toString` on a `Float` prints six, and grid coordinates read as noise at
    that width. -/
def fmt (x : Float) : String :=
  let n := (x * 100.0).round
  let m := n.abs.toUInt64.toNat
  let frac := m % 100
  let s := s!"{m / 100}.{if frac < 10 then "0" else ""}{frac}"
  if n < 0.0 then "-" ++ s else s

/-- Lean's pretty printer, on one line.  The repo's namespaces carry no information inside a picture
    of the repo's own algebra, so they come off.  This is the ONE source of every label here: where
    the note spells a constant differently, the fix is an `app_unexpander` beside that constant, not
    a table in this file. -/
def plain (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  let s := s.replace "Freyd." "" |>.replace "Diag.CartBicat." "" |>.replace "Diag."  ""
    |>.replace "Alg.Allegory." "" |>.replace "Alg." "" |>.replace "RelSet." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- Every `.lean` file under `dir`, as module names below `pre` — the exe imports one environment
    holding all of them and draws every name on the command line from it. -/
partial def libModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "tool" && e.fileName != "generated" then
        out := out ++ (← libModules e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

/-! ### The graph -/

/-- A node: its identity, its place on the grid, and the object it stands for. -/
structure Node where
  id : String
  gx : Float
  gy : Float
  label : String

/-- An edge: the two nodes it joins, the arrow it stands for, and which side of the face it is on —
    the side is the direction its label is set in, away from the face. -/
structure Edge where
  src : String
  tgt : String
  label : String
  side : String
  /-- Perpendicular bow, in grid units.  Zero for every edge of a face with three or more nodes;
      two parallel arrows between one pair of nodes would otherwise be drawn on top of each other. -/
  bow : Float := 0.0

/-- A face: the relation the two paths round it are asserted to stand in, and where to set it. -/
structure Face where
  sym : String
  gx : Float
  gy : Float

/-! ### From the statement to the graph -/

/-- The arrows of one side, in diagram order.  `≫` flattens and `𝟙` contributes nothing; every
    other expression is one arrow, whatever it is made of. -/
partial def factors (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => factors f ++ factors g
    | none => #[e]
  | (``Cat.id, _) => #[]
  | _ => #[e]

/-- One side's edges.  An identity INSIDE a composite is the empty path and disappears; a side that
    is NOTHING BUT an identity keeps it, because a face needs two nodes and a loop is not drawable
    on a grid. -/
def sideArrows (e : Expr) : Array Expr :=
  let fs := factors e
  if fs.isEmpty then #[e] else fs

/-- The two objects an arrow runs between, read off its type.  `whnf` only as a fallback: a hom that
    is already `@Cat.Hom _ _ a b` must not be unfolded into the instance's own carrier. -/
def homEnds (e : Expr) : MetaM (Expr × Expr) := do
  let t ← instantiateMVars (← Meta.inferType e)
  let ends (t : Expr) : Option (Expr × Expr) :=
    match t.getAppFnArgs with
    | (``Cat.Hom, args) => lastTwo args
    | _ => none
  match ends t with
  | some r => return r
  | none =>
    match ends (← Meta.whnf t) with
    | some r => return r
    | none => throwError "not an arrow: {← Meta.ppExpr e} : {← Meta.ppExpr t}"

/-- An arrow's label — the same printer as an object's, because an edge and a node say the same kind
    of thing about the term they came from. -/
def arrowLabel (e : Expr) : MetaM String := plain e

/-! ### The grid

A path of `n` edges from the top-left corner to the bottom-right one runs along two legs, and the
HORIZONTAL leg takes the odd edge: `2` is `1,1`, `3` is `2,1`, `4` is `2,2`.  `n = 1` has no corner
to turn, so it is the chord — the pair `(1, 0)`, whose zero second leg every reader of these numbers
below takes to mean "straight to the far corner". -/
def legs (k : Nat) (mirror : Bool) : Nat × Nat :=
  if k ≤ 1 then (k, 0)
  else
    -- Clockwise leaves along the top and arrives down the right; counter-clockwise leaves DOWN the
    -- left and arrives along the bottom, so its two legs are the other's in the other order.
    if mirror then (k / 2, (k + 1) / 2) else ((k + 1) / 2, k / 2)

/-- Where the `i`-th vertex of a path sits, given its leg split and the grid's extent. -/
def vertexAt (first second : Nat) (nx ny : Float) (mirror : Bool) (i : Nat) : Float × Float :=
  if second == 0 then (if i == 0 then (0.0, 0.0) else (nx, -ny))
  else if mirror then
    if i ≤ first then (0.0, -(i.toFloat / first.toFloat) * ny)
    else (((i - first).toFloat / second.toFloat) * nx, -ny)
  else
    if i ≤ first then ((i.toFloat / first.toFloat) * nx, 0.0)
    else (nx, -((i - first).toFloat / second.toFloat) * ny)

/-- Which side of the face an edge is on, hence which way its label is set. -/
def sideAt (first second : Nat) (mirror : Bool) (i : Nat) : String :=
  if second == 0 then (if mirror then "bottom" else "top")
  else if mirror then (if i < first then "left" else "bottom")
  else (if i < first then "top" else "right")

/-- The graph of one face: the two paths, the nodes they share and the symbol between them. -/
def faceOf (sym : String) (lhs rhs : Array Expr) : MetaM (Array Node × Array Edge × Array Face) := do
  let (n, m) := (lhs.size, rhs.size)
  let (top, right) := legs n false
  let (left, bot) := legs m true
  -- The grid is as wide as the wider of its two horizontal legs and as tall as the taller of its
  -- two vertical ones; a leg a chord does not use counts for nothing.  Both sides chords is the
  -- digon: one column, no rows, and the two edges told apart by their bow.
  let nx := (max (if right == 0 then 0 else top) (if left == 0 then 0 else bot)).max 1
  let ny := max right left
  let (fx, fy) := (nx.toFloat, ny.toFloat)
  let bowed := ny == 0
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  -- A node's object is the SOURCE of the arrow leaving it, or the TARGET of the last arrow for the
  -- end node — read off the arrow's own type, never guessed from the statement's shape.
  let objAt (side : Array Expr) (i : Nat) : MetaM Expr := do
    if h : i < side.size then return (← homEnds side[i]).1
    else return (← homEnds side[side.size - 1]!).2
  let nodeId (pre : String) (i k : Nat) : String :=
    if i == 0 then "s" else if i == k then "t" else s!"{pre}{i}"
  for i in [0:n+1] do
    let (gx, gy) := vertexAt top right fx fy false i
    let id := nodeId "u" i n
    unless nodes.any (·.id == id) do
      nodes := nodes.push { id, gx, gy, label := (← plain (← objAt lhs i)) }
  for j in [0:m+1] do
    let (gx, gy) := vertexAt left bot fx fy true j
    let id := nodeId "v" j m
    unless nodes.any (·.id == id) do
      nodes := nodes.push { id, gx, gy, label := (← plain (← objAt rhs j)) }
  for i in [0:n] do
    edges := edges.push
      { src := nodeId "u" i n, tgt := nodeId "u" (i+1) n, label := (← arrowLabel lhs[i]!),
        side := sideAt top right false i, bow := if bowed then 0.9 else 0.0 }
  for j in [0:m] do
    edges := edges.push
      { src := nodeId "v" j m, tgt := nodeId "v" (j+1) m, label := (← arrowLabel rhs[j]!),
        side := sideAt left bot true j, bow := if bowed then -0.9 else 0.0 }
  -- The symbol goes at the average of the face's corners, which for a convex polygon is inside it.
  let cx := nodes.foldl (fun a v => a + v.gx) 0.0 / nodes.size.toFloat
  let cy := nodes.foldl (fun a v => a + v.gy) 0.0 / nodes.size.toFloat
  return (nodes, edges, #[{ sym, gx := cx, gy := cy }])

/-! ### Emitting the page -/

def typstNodes (ns : Array Node) : String :=
  "(\n" ++ String.join (ns.toList.map fun v =>
    s!"  (id: {typstString v.id}, at: ({fmt v.gx}, {fmt v.gy}), label: raw({typstString v.label})),\n")
    ++ ")\n"

def typstEdges (es : Array Edge) : String :=
  "(\n" ++ String.join (es.toList.map fun e =>
    s!"  (from: {typstString e.src}, to: {typstString e.tgt}, \
       label: raw({typstString e.label}), side: {typstString e.side}, bow: {fmt e.bow}),\n")
    ++ ")\n"

def typstFaces (fs : Array Face) : String :=
  "(\n" ++ String.join (fs.toList.map fun f =>
    s!"  (sym: {typstString f.sym}, at: ({fmt f.gx}, {fmt f.gy})),\n") ++ ")\n"

/-- The generated file is BOTH a standalone page and an importable module, as the string-diagram
    exporter's is: `pic` is bound at the top for a note that wants the picture in a table cell.
    The page below draws the panel UNSCALED — `pic` carries the note's `s: 74%`, and `scripts/svg-check`
    measures this page against `diag/natsq.typ`, which is drawn at full size. -/
def cdPage (declName : Name) (doc : Option String) (ns : Array Node) (es : Array Edge)
    (fs : Array Face) : String :=
  let docLet := match doc with
    | some d => "#let doc = " ++ typstString d ++ "\n"
    | none => "#let doc = none\n"
  "// GENERATED by `diag-export --commutative` — do not edit; regenerate with\n\
   //   ./scripts/diag-export --commutative " ++ declName.toString ++ "\n\
   #import \"../../cdpanel.typ\": *\n\n"
    ++ docLet
    ++ "#let nodes = " ++ typstNodes ns
    ++ "#let edges = " ++ typstEdges es
    ++ "#let faces = " ++ typstFaces fs
    ++ "#let cert = (lean: " ++ typstString declName.toString ++ ")\n"
    ++ "#let pic = cdpanel(nodes, edges, faces, cert: cert)\n\n"
    ++ "#set page(width: auto, height: auto, margin: 12pt)\n\
        #set text(size: 10pt)\n\n\
        #text(11pt)[*`" ++ declName.toString ++ "`*]\n\n\
        #if doc != none { text(9pt, luma(90), raw(doc)) }\n\n\
        #cdpanel(nodes, edges, faces, s: 100%, cert: cert)\n"

/-- The relation between two sides of a statement, and the sides. -/
def split (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.le, args) => (lastTwo args).map fun (l, r) => ("⊑", l, r)
  | (``LE.le, args) => (lastTwo args).map fun (l, r) => ("≤", l, r)
  | (``Eq, args) => (lastTwo args).map fun (l, r) => ("=", l, r)
  | _ => none

/-- Open the binders, and if what they expose is not yet an equation take ONE delta step on its head
    and open the binders THAT exposes.  `StrictNatural F G φ` needs exactly one such step; a
    statement that needs none is the common case and pays nothing.  Everything happens inside the
    telescope, so the locals the binders introduce are in scope where the face is built. -/
partial def build (declName : Name) (doc : Option String) (ty : Expr) (fuel : Nat) :
    MetaM String := do
  Meta.forallTelescopeReducing ty fun _ body => do
    match split body with
    | some (sym, l, r) =>
      let (ns, es, fs) ← faceOf sym (sideArrows l) (sideArrows r)
      return cdPage declName doc ns es fs
    | none =>
      if fuel == 0 then
        throwError "{declName}: not an equation or inequation of composites, and no definition to \
          open — {← Meta.ppExpr body}"
      let .const n us := body.getAppFn
        | throwError "{declName}: not an equation or inequation of composites — \
            {← Meta.ppExpr body}"
      let some ci := (← getEnv).find? n
        | throwError "{declName}: no such constant in the statement's head: {n}"
      let some v := ci.value?
        | throwError "{declName}: `{n}` heads the statement and has no definition to open"
      build declName doc ((mkAppN (v.instantiateLevelParams ci.levelParams us) body.getAppArgs).headBeta)
        (fuel - 1)

/-- Draw the statement of `declName` as a commutative diagram. -/
def draw (declName : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? declName | throwError "no such declaration: {declName}"
  let doc := (← findDocString? env declName).map fun d =>
    (d.splitOn "\n").headD "" |>.replace "`" "" |>.replace "*" ""
  build declName doc ci.type 3

/-- `--commutative`'s own entry point.  ONE environment per process, as in `DiagExport.main`: the
    import happens once and every name on the command line is drawn from it. -/
def main (args : List String) : IO UInt32 := do
  let args := args.filter (fun a => a != "--commutative")
  if args.isEmpty then
    IO.eprintln "usage: diag-export --commutative <declaration-name> [<declaration-name> ...]"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := #[`Freyd] ++ (← libModules "diag" `diag) ++ (← libModules "AOP" `AOP)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  IO.FS.createDirAll "diag/generated/commutative"
  -- Field notation stays ON, unlike the string-diagram route: a node here is an OBJECT, and
  -- `(F.appl a).obj X` is the object, where `Functor.obj (Relator.toFunctor (BiRelator.appl F a)) X`
  -- is a transcript of how it is built.  GENERALIZED field notation is off for the reason that
  -- route gives: a class projection printed through its anonymous instance comes out `instCat.id X`,
  -- which is not an arrow's name and hides the `𝟙 X` and `R°` notations behind it.
  -- `⟶`, `≫`, `°` and `⊑` are all `Freyd`/`Freyd.Alg` notations, so the printer only reaches them
  -- with those namespaces opened.
  let opts : Options := Options.empty.setBool `pp.fieldNotation.generalized false
  let ctx : Core.Context :=
    { fileName := "<diag-export>", fileMap := default, options := opts,
      openDecls := [.simple `Freyd [], .simple `Freyd.Alg [], .simple `Freyd.Alg.RelSet [],
        .simple `Freyd.Diag.SymMonCat [], .simple `Freyd.Diag.Word []] }
  let mut status : UInt32 := 0
  for arg in args do
    let run : CoreM String := Meta.MetaM.run' (draw arg.toName)
    -- The thrown message is the DIAGNOSIS — which statement was reached and why it is not a face —
    -- so a declaration this functor declines to draw says so in its own terms rather than as a
    -- blanket "cannot draw", which is the error that sends a reader back to the source.
    try
      let text ← Prod.fst <$> run.toIO ctx { env }
      let path := System.FilePath.mk s!"diag/generated/commutative/{arg}.typ"
      IO.FS.writeFile path text
      IO.println path.toString
    catch e =>
      IO.eprintln s!"diag-export --commutative: {e}"
      status := 1
  return status

end Freyd.CommutativeDiagram
