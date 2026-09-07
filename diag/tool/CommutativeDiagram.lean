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

  `interp` gives that value — a `Path`, a graph open at two ends — and `Face.of` puts two of them
  with the same ends into one face; the grid is a SEPARATE pass, `layout`, over the face's boundary.

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
-- route `--commutative`, so the typst helpers below are its own rather than made circular.
import Lean
-- `StrDiag`: one copy of what a statement states, of an arrow's two ends, and of an application's
-- last two arguments.
import diag.tool.ExprReader
import AOP.A4_5

open Lean

namespace Freyd.CommutativeDiagram

/-! ### `DiagExport`'s helpers, copied because the import runs the other way -/

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
  /-- How far the edge bows out of its chord, in grid units — a MAGNITUDE: which way it bows is
      `side`, as for the label.  Zero for every edge of a face with three or more nodes; two
      parallel arrows between one pair of nodes would otherwise be drawn on top of each other. -/
  bow : Float := 0.0

/-- Where a face's symbol is set, once the grid is known. -/
structure FaceMark where
  sym : String
  gx : Float
  gy : Float

/-! ### The value of an arrow expression: a path -/

/-- A graph open at two ends.  `nodes` are the vertices in path order, `edges` the arrows between
    them, `src`/`tgt` the ids of the two ends.  Only the three constructors below build one. -/
structure Path where
  nodes : Array (String × Expr)
  edges : Array (String × String × Expr)
  src : String
  tgt : String

/-- The `i`-th vertex's id while a path is being built.  A path is a LINE, so a vertex's position is
    already a unique name and no counter has to be carried between the constructors. -/
def Path.nid (i : Nat) : String := s!"n{i}"

/-- Every vertex renamed by its POSITION, the edges and the two ends following.  One renaming, used
    both to keep `comp`'s two operands apart and to give a face's ends their shared names. -/
def Path.rename (p : Path) (nm : Nat → String) : Path :=
  let ren (id : String) : String :=
    match p.nodes.findIdx? (·.1 == id) with | some i => nm i | none => id
  { nodes := (List.range p.nodes.size).toArray.map fun i => (nm i, (p.nodes[i]!).2),
    edges := p.edges.map fun (s, t, f) => (ren s, ren t, f),
    src := ren p.src, tgt := ren p.tgt }

/-- The object at a vertex — how a path says what its ends ARE, `src` and `tgt` being ids. -/
def Path.objAt (p : Path) (id : String) : MetaM Expr :=
  match p.nodes.find? (·.1 == id) with
  | some (_, o) => return o
  | none => throwError "no vertex {id} in a path of {p.nodes.size}"

/-- The empty path at `o`: one vertex, no edge.  It is the unit of `comp` by construction, which is
    everything an identity INSIDE a composite ever meant. -/
def Path.id (o : Expr) : Path :=
  { nodes := #[(nid 0, o)], edges := #[], src := nid 0, tgt := nid 0 }

/-- One edge, its two vertices read off the arrow's OWN TYPE — never guessed from the shape of the
    statement it came from. -/
def Path.arrow (f : Expr) : MetaM Path := do
  let (a, b) ← StrDiag.homEnds f
  return { nodes := #[(nid 0, a), (nid 1, b)], edges := #[(nid 0, nid 1, f)],
           src := nid 0, tgt := nid 1 }

/-- `q` after `p`, with `p.tgt` and `q.src` IDENTIFIED.  GATE: those two objects must agree, or the
    composite does not exist and the picture would glue arrows that never meet. -/
def Path.comp (p q : Path) : MetaM Path := do
  let a ← p.objAt p.tgt
  let b ← q.objAt q.src
  unless ← Meta.isDefEq a b do
    throwError "these do not compose: the first path ends at {← plain a}, the second starts at \
      {← plain b}"
  let p := p.rename nid
  let q := q.rename fun j => nid (j + p.nodes.size - 1)
  return { nodes := p.nodes ++ q.nodes.extract 1 q.nodes.size, edges := p.edges ++ q.edges,
           src := p.src, tgt := q.tgt }

/-- A term read as a path.  Composition is the ONLY structural case — that is the functor law; `𝟙`
    is the empty path, and any other expression is one edge, whatever it is made of. -/
partial def interp (e : Expr) : MetaM Path := do
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    match StrDiag.lastTwo args with
    | some (f, g) => Path.comp (← interp f) (← interp g)
    | none => Path.arrow e
  | (``Cat.id, _) => return Path.id (← StrDiag.homEnds e).1
  | _ => Path.arrow e

/-- A face: two paths with the SAME two ends, and the relation asserted between them. -/
structure Face where
  sym : String
  lhs : Path
  rhs : Path

/-- The face of an equation.  GATE: the two sides must start at one object and end at one object.
    A side with NO edge becomes the single edge `𝟙` — a face needs two vertices and a loop is not
    drawable on a grid, a decision about the PICTURE and not a fact about the term, which is why it
    lives here and not in `interp`. -/
def Face.of (sym : String) (p q : Path) : MetaM Face := do
  let (pa, pb) := (← p.objAt p.src, ← p.objAt p.tgt)
  let (qa, qb) := (← q.objAt q.src, ← q.objAt q.tgt)
  unless ← Meta.isDefEq pa qa do
    throwError "the two sides start at different objects: {← plain pa} and {← plain qa}"
  unless ← Meta.isDefEq pb qb do
    throwError "the two sides end at different objects: {← plain pb} and {← plain qb}"
  let drawable (r : Path) (o : Expr) : MetaM Path := do
    if r.edges.isEmpty then Path.arrow (← Meta.mkAppM ``Cat.id #[o]) else return r
  -- The two SHARED vertices are the ends, so they take the shared names and each side's interior
  -- its own; that identification is what makes the two paths one graph.
  let name (pre : String) (k i : Nat) : String :=
    if i == 0 then "s" else if i == k then "t" else s!"{pre}{i}"
  let lhs ← drawable p pa
  let rhs ← drawable q qa
  return { sym, lhs := lhs.rename (name "u" lhs.edges.size),
           rhs := rhs.rename (name "v" rhs.edges.size) }

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

/-- The face laid on the grid: coordinates for its two boundary paths, and the symbol between them.
    Only `cdpanel` can measure a label, so what leaves here is grid units, not centimetres. -/
def layout (fc : Face) : MetaM (Array Node × Array Edge × Array FaceMark) := do
  let (n, m) := (fc.lhs.edges.size, fc.rhs.edges.size)
  let (top, right) := legs n false
  let (left, bot) := legs m true
  -- The grid is as wide as the wider of its two horizontal legs and as tall as the taller of its
  -- two vertical ones; a leg a chord does not use counts for nothing.  Both sides chords is the
  -- digon: one column, no rows, and the two edges told apart by their bow.
  -- A leg belongs to a path only when that path turns a corner: `legs` gives a chord `(1, 0)`, whose
  -- `1` is the whole path and not a leg, so a side with a zero SECOND leg contributes neither.
  let nx := (max (if right == 0 then 0 else top) (if bot == 0 then 0 else bot)).max 1
  let ny := max (if right == 0 then 0 else right) (if bot == 0 then 0 else left)
  let (fx, fy) := (nx.toFloat, ny.toFloat)
  let bowed := ny == 0
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  -- The two paths share their end vertices, so the second contributes only its interior.
  for i in [0:n+1] do
    let (id, o) := fc.lhs.nodes[i]!
    let (gx, gy) := vertexAt top right fx fy false i
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← plain o) }
  for j in [0:m+1] do
    let (id, o) := fc.rhs.nodes[j]!
    let (gx, gy) := vertexAt left bot fx fy true j
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← plain o) }
  for i in [0:n] do
    let (src, tgt, f) := fc.lhs.edges[i]!
    edges := edges.push { src, tgt, label := (← plain f), side := sideAt top right false i,
                          bow := if bowed then 0.9 else 0.0 }
  for j in [0:m] do
    let (src, tgt, f) := fc.rhs.edges[j]!
    edges := edges.push { src, tgt, label := (← plain f), side := sideAt left bot true j,
                          bow := if bowed then 0.9 else 0.0 }
  -- A face commutes unless marked: an equation carries no symbol, a lax face keeps its `⊑`/`≤`.
  -- The symbol goes at the average of the face's corners, which for a convex polygon is inside it.
  let cx := nodes.foldl (fun a v => a + v.gx) 0.0 / nodes.size.toFloat
  let cy := nodes.foldl (fun a v => a + v.gy) 0.0 / nodes.size.toFloat
  return (nodes, edges, if fc.sym == "=" then #[] else #[{ sym := fc.sym, gx := cx, gy := cy }])

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

def typstFaces (fs : Array FaceMark) : String :=
  "(\n" ++ String.join (fs.toList.map fun f =>
    s!"  (sym: {typstString f.sym}, at: ({fmt f.gx}, {fmt f.gy})),\n") ++ ")\n"

/-- The generated file is BOTH a standalone page and an importable module, as the string-diagram
    exporter's is: `pic` is bound at the top for a note that wants the picture in a table cell.
    The page below draws the panel UNSCALED — `pic` carries the note's `s: 74%`, and `scripts/svg-check`
    measures this page against `diag/natsq.typ`, which is drawn at full size. -/
def cdPage (declName : Name) (ns : Array Node) (es : Array Edge) (fs : Array FaceMark) : String :=
  "// GENERATED by `diag-export --commutative` — do not edit; regenerate with\n\
   //   ./scripts/diag-export --commutative " ++ declName.toString ++ "\n\
   #import \"../../cdpanel.typ\": *\n\n"
    ++ "#let nodes = " ++ typstNodes ns
    ++ "#let edges = " ++ typstEdges es
    ++ "#let faces = " ++ typstFaces fs
    ++ "#let cert = (lean: " ++ typstString declName.toString ++ ")\n"
    ++ "#let pic = cdpanel(nodes, edges, faces, cert: cert)\n\n"
    ++ "#set page(width: auto, height: auto, margin: 12pt)\n\
        #set text(size: 10pt)\n\n\
        #text(11pt)[*`" ++ declName.toString ++ "`*]\n\n\
        #cdpanel(nodes, edges, faces, s: 100%, cert: cert)\n"

/-- Open the binders, and if what they expose is not yet an equation take ONE delta step on its head
    and open the binders THAT exposes.  `StrictNatural F G φ` needs exactly one such step; a
    statement that needs none is the common case and pays nothing.  Everything happens inside the
    telescope, so the locals the binders introduce are in scope where the face is built. -/
partial def build (declName : Name) (ty : Expr) (fuel : Nat) : MetaM String := do
  Meta.forallTelescopeReducing ty fun _ body => do
    match StrDiag.split body with
    | some (sym, l, r) =>
      let (ns, es, fs) ← layout (← Face.of sym (← interp l) (← interp r))
      return cdPage declName ns es fs
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
      build declName ((mkAppN (v.instantiateLevelParams ci.levelParams us) body.getAppArgs).headBeta)
        (fuel - 1)

/-- Draw the statement of `declName` as a commutative diagram. -/
def draw (declName : Name) : MetaM String := do
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  build declName ci.type 3

/-- The namespaces whose `scoped` notations a label is written in — opened for name shortening AND
    activated for printing (`main`).  `Freyd` carries `𝟙`, `≫`, `⟶`; `Freyd.Alg` the allegory's `°`,
    `⊑` and the fold's `⦇ ⦈`; the rest the note's own spellings. -/
def openNs : List Name :=
  [`Freyd, `Freyd.Alg, `Freyd.Alg.RelSet, `Freyd.Alg.RelSet.CL, `Freyd.Alg.RelSet.ListRel,
    `Freyd.Alg.RelSet.Van, `Freyd.Diag.SymMonCat, `Freyd.Diag.Word]

/-- `--commutative`'s own entry point.  ONE environment per process, as in `DiagExport.main`: the
    import happens once and every name on the command line is drawn from it. -/
def main (args : List String) : IO UInt32 := do
  let args := args.filter (fun a => a != "--commutative")
  if args.isEmpty then
    IO.eprintln "usage: diag-export --commutative <declaration-name> [<declaration-name> ...]"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := #[`Freyd] ++ (← libModules "diag" `diag) ++ (← libModules "AOP" `AOP)
  -- `loadExts` is what makes a label read as the repo's own notation: without it the delaborator's
  -- unexpander table is empty, so not one `notation` in the repo — nor `Eq`'s own `=` — is applied
  -- and every label is a raw application (`relCata R`, `instCat.id X`).
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
    (loadExts := true)
  IO.FS.createDirAll "diag/generated/commutative"
  -- Field notation is OFF.  It prints a functor's action by the FIELD's name, `F.obj X`, where the
  -- book applies the functor's own letter, `F X`; and it is tried BEFORE an unexpander, so
  -- `S1_18`'s `Functor.obj`/`Functor.map` unexpanders only fire once it is off.  What field
  -- notation was hiding — the coercion `Relator.toFunctor` — is peeled by its own unexpander
  -- (`A5_1`), so the head is still the relator's letter.
  -- `⟶`, `≫`, `°` and `⊑` are all `Freyd`/`Freyd.Alg` notations, so the printer only reaches them
  -- with those namespaces opened.
  let opts : Options := (Options.empty.setBool `pp.fieldNotation false).setBool
    -- A structure instance is not an application, so no unexpander can reach a bundled
    -- object; printed as a constructor it becomes one, and the note's own name comes back.
    `pp.structureInstances false
  let ctx : Core.Context :=
    { fileName := "<diag-export>", fileMap := default, options := opts,
      openDecls := openNs.map (.simple · []) }
  -- `openDecls` alone only SHORTENS names.  Every notation the repo writes is `scoped`, and a
  -- scoped unexpander lives in a scoped extension that `open` activates during elaboration — which
  -- an exe never runs.  Without this the labels read `Cat.id X`, `Cat.comp R S`, and the note's own
  -- spellings below never fire either.
  let env := (← (do for ns in openNs do activateScoped ns : CoreM Unit).toIO ctx { env }).2.env
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
