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

/-- A single NAME — one run of letters and digits.  That is what decides a bracket: brackets exist
    to stop a compound reading as a composite, and a name cannot be one. -/
def isName (s : String) : Bool :=
  s.length == 1 || (!s.isEmpty && s.all fun c => c.isAlphanum || c == '_' || c == '\'')

/-- A picture label.  Every SPELLING comes from an unexpander beside the constant, through `plain`;
    what no unexpander can say is the note's SPACING, because Lean's formatter always sets an
    application's argument off with a space where the note sets it against the head.  So the
    applications a picture writes TIGHT are here, and only those: a relator's action on an OBJECT is
    bare when the object is a single name (`FT`, `EA`) and bracketed otherwise (`F(A×B)`), its
    action on an ARROW always bracketed (`F(⦇f⦈)`, `E(R)`), and the product and the fork close up
    (`A×B`, `⟨⦇h⦈,⦇k⦈⟩`).  A node already says which object an operator is taken at, so `∋ b` and
    `π₁` drop theirs. -/
partial def label (e : Expr) : MetaM String := do
  let obj (x : Expr) : MetaM String := do
    let s ← label x; return if isName s then s else "(" ++ s ++ ")"
  match e.getAppFnArgs with
  | (``Freyd.Alg.PowerAllegory.eps, _) => return "∋"
  | (``Freyd.HasBinaryProducts.fst, _) => return "π₁"
  | (``Freyd.HasBinaryProducts.snd, _) => return "π₂"
  | (``Freyd.Alg.singletonMap, _) => return "𝟙%∋"
  | (``Freyd.Alg.PowerAllegory.powerObj, args) =>
    match args.back? with | some a => return "E" ++ (← obj a) | none => plain e
  | (``Freyd.Alg.existsImage, args) =>
    match args.back? with | some r => return "E(" ++ (← label r) ++ ")" | none => plain e
  | (``Freyd.HasBinaryProducts.prod, args) =>
    match StrDiag.lastTwo args with
    | some (a, b) => return (← label a) ++ "×" ++ (← label b)
    | none => plain e
  | (``Freyd.HasBinaryProducts.pair, args) =>
    match StrDiag.lastTwo args with
    | some (f, g) => return "⟨" ++ (← label f) ++ "," ++ (← label g) ++ "⟩"
    | none => plain e
  | (``Freyd.Functor.obj, args) =>
    match StrDiag.lastTwo args with
    | some (f, x) => return (← label f) ++ (← obj x)
    | none => plain e
  | (``Freyd.Functor.map, _) =>
    match StrDiag.functorMap? e with
    | some (f, r) => return (← label f) ++ "(" ++ (← label r) ++ ")"
    | none => plain e
  | _ => plain e

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
  /-- Drawn dashed.  THE NOTE DASHES THE ARROW THE STATEMENT PRODUCES, and nothing else — see
      `Face.dashes`. -/
  dash : Bool := false

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

/-- A path renamed to be ONE SIDE of a face: its two ENDS take the shared names `s`/`t` and its
    interior its own `pre`-prefixed ones.  Identifying the ends is what makes two paths one graph. -/
def Path.endName (p : Path) (pre : String) : Path :=
  p.rename fun i => if i == 0 then "s" else if i + 1 == p.nodes.size then "t" else s!"{pre}{i}"

/-- The path walked backwards.  Each edge keeps its OWN direction — reversing a walk turns the
    arrows round only in the reader's eye, never in the graph. -/
def Path.mirror (p : Path) : Path :=
  { nodes := p.nodes.reverse, edges := p.edges.reverse, src := p.tgt, tgt := p.src }

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

/-- A face: two paths with the SAME two ends, and the relation asserted between them.

    `chord` is what PASTING leaves: two faces sharing exactly one edge are one polygon — the two
    faces' other sides, as one closed walk — with that edge drawn straight across it.  `sym` is then
    the relation the `lhs` side of the chord asserts and the chord's second component the `rhs`
    side's; with no chord `sym` is the whole face's. -/
structure Face where
  sym : String
  lhs : Path
  rhs : Path
  chord : Option (Expr × String) := none
  /-- Arrows the statement's OTHER side, across an `↔`, says this one produces — see `inducedIn`.
      Empty for a statement that is a single claim, where the head constant says it instead. -/
  induced : Array Expr := #[]

/-- The face of an equation.  GATE: the two sides must start at one object and end at one object.
    A side with NO edge becomes the single edge `𝟙` — a face needs two vertices and a loop is not
    drawable on a grid, a decision about the PICTURE and not a fact about the term, which is why it
    lives here and not in `interp`. -/
def Face.of (sym : String) (p q : Path) (induced : Array Expr := #[]) : MetaM Face := do
  let (pa, pb) := (← p.objAt p.src, ← p.objAt p.tgt)
  let (qa, qb) := (← q.objAt q.src, ← q.objAt q.tgt)
  unless ← Meta.isDefEq pa qa do
    throwError "the two sides start at different objects: {← plain pa} and {← plain qa}"
  unless ← Meta.isDefEq pb qb do
    throwError "the two sides end at different objects: {← plain pb} and {← plain qb}"
  let drawable (r : Path) (o : Expr) : MetaM Path := do
    if r.edges.isEmpty then Path.arrow (← Meta.mkAppM ``Cat.id #[o]) else return r
  let lhs ← drawable p pa
  let rhs ← drawable q qa
  return { sym, lhs := lhs.endName "u", rhs := rhs.endName "v", induced }

/-- The face's boundary as ONE CLOSED WALK: `edges[i]` joins `nodes[i]` to `nodes[i+1]`, the last
    back to the first, each edge keeping its own direction.  The walk ignores those directions,
    which is what lets a face be traversed against an arrow — as one of two pasted faces must be. -/
def Face.cycle (fc : Face) : Array (String × Expr) × Array (String × String × Expr) :=
  (fc.lhs.nodes.pop ++ (fc.rhs.nodes.extract 1 fc.rhs.nodes.size).reverse,
   fc.lhs.edges ++ fc.rhs.edges.reverse)

/-- One face's boundary OPENED at its `i`-th edge: the rest of the walk, laid out so that it runs
    from that edge's SOURCE to its target — the direction the chord itself points, which is how the
    two sides of a paste agree on which corner is which. -/
def Face.opened (ns : Array (String × Expr)) (es : Array (String × String × Expr)) (i : Nat)
    : Path :=
  let k := ns.size
  let ns' := ns.extract (i + 1) k ++ ns.extract 0 (i + 1)
  let es' := (es.extract (i + 1) k ++ es.extract 0 (i + 1)).pop
  let w : Path := { nodes := ns', edges := es', src := ns'[0]!.1, tgt := ns'[k - 1]!.1 }
  -- The opened edge joins `ns'[k-1]` back to `ns'[0]`, so the walk leaves the edge's source already
  -- exactly when that source is `ns'[0]`.
  if es[i]!.1 == w.src then w else w.mirror

/-- Two faces pasted along the ONE edge they share: the union is one polygon — their other sides, as
    a closed walk — with that edge as a chord.  `none` when they share no edge or more than one,
    which is the pair the caller sets SIDE BY SIDE instead; that is the whole rule, and it is what
    makes the note's own two choices fall out of the terms rather than out of a table. -/
def Face.paste (f g : Face) : MetaM (Option Face) := do
  let (fn, fe) := f.cycle
  let (gn, ge) := g.cycle
  let mut hits : Array (Nat × Nat) := #[]
  for i in [0 : fe.size] do
    for j in [0 : ge.size] do
      if ← Meta.isDefEq fe[i]!.2.2 ge[j]!.2.2 then hits := hits.push (i, j)
  unless hits.size == 1 do return none
  let (i, j) := hits[0]!
  let p := Face.opened fn fe i
  let q := Face.opened gn ge j
  return some { sym := f.sym, lhs := p.endName "u", rhs := q.endName "v",
                chord := some (fe[i]!.2.2, g.sym) }

/-! ### Which arrow the statement PRODUCES -/

/-- The INDUCED-ARROW CONSTRUCTORS, read by their ATTRIBUTE and never by a name list here: a
    constant carries `@[diag_induced]` when applying it is what a universal property gives — the
    fold `⦇R⦈`, the pairing `⟨f,g⟩`, the transpose `Λ R`.  A new one is tagged beside its
    declaration and every picture dashes it without another line in this file. -/
def inducedHeads : MetaM (Array Name) := do return ← Lean.labelled `diag_induced

/-- Whether an arrow is one an induced constructor BUILT — its head, not something under it:
    `⦇f⦈` is induced and `F(⦇f⦈)` is `F`'s action on it. -/
def isInduced (heads : Array Name) (f : Expr) : Bool :=
  match f.getAppFn with | .const n _ => heads.contains n | _ => false

/-- The arrows a claim says are produced.  One side of an equation is produced when the OTHER is
    headed by an induced constructor, and so is every arrow ARGUMENT of an induced constructor at
    its head: `⟨f,g⟩=⦇⟨h,k⟩⦈` produces `⟨f,g⟩`, hence `f` and `g`. -/
partial def inducedIn (e : Expr) : MetaM (Array Expr) := do
  let heads ← inducedHeads
  let rec parts (x : Expr) : MetaM (Array Expr) := do
    unless isInduced heads x do return #[x]
    let mut out := #[x]
    for a in x.getAppArgs do
      if (← Meta.inferType a).isAppOf ``Cat.Hom then out := out ++ (← parts a)
    return out
  match e.getAppFnArgs with
  | (``And, #[l, r]) => return (← inducedIn l) ++ (← inducedIn r)
  | _ =>
    let some (_, l, r) := StrDiag.split e | return #[]
    if isInduced heads r then parts l else if isInduced heads l then parts r else return #[]

/-- WHICH ARROWS THIS STATEMENT PRODUCES, hence which are drawn dashed.  A pasted pair produces its
    CHORD — the arrow the two faces share is the one they jointly determine — and nothing else, so
    `⦇h⦈` and `⦇k⦈` under the fan's `⟨⦇h⦈,⦇k⦈⟩` stay solid: some other law produced them.  A single
    face has no chord, and then an arrow is produced when an induced constructor heads it
    (`α⦇f⦈=F(⦇f⦈)f` produces `⦇f⦈`) or when the other side of the statement's `↔` says so. -/
def Face.dashes (fc : Face) (f : Expr) : MetaM Bool := do
  if fc.chord.isSome then return false
  if isInduced (← inducedHeads) f then return true
  fc.induced.anyM fun g => Meta.isDefEq g f

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

/-- A FAN, the one pasted shape that is not a square: every arrow of the polygon LEAVES an end of
    the chord, so the two ends are two apexes over one row of shared targets, and the chord runs
    between them.  Laid out that way — the chord's source above, its target below it, the two
    interior vertices left and right of the target — where a square would put the chord on a
    diagonal and one apex's two arrows in opposite directions.  `⟨⦇h⦈,⦇k⦈⟩π₁=⦇h⦈ ∧ ⟨⦇h⦈,⦇k⦈⟩π₂=⦇k⦈`
    is a fan; `Λ(R)∋=R ∧ Λ(R)=(𝟙%∋)E(R)` is not, its `E(R)` arriving AT the chord's target. -/
def Face.isFan (fc : Face) : Bool :=
  fc.chord.isSome && fc.lhs.edges.size == 2 && fc.rhs.edges.size == 2 &&
    (fc.lhs.edges ++ fc.rhs.edges).all fun (s, _, _) => s == "s" || s == "t"

/-- The face laid on the grid: coordinates for its two boundary paths, and the symbol between them.
    Only `cdpanel` can measure a label, so what leaves here is grid units, not centimetres. -/
def layout (fc : Face) : MetaM (Array Node × Array Edge × Array FaceMark) := do
  if fc.isFan then
    -- Three columns, two rows: the apex over the middle of the row its chord ends in.
    let place (p : Path) (side₀ : String) (gx : Float) : MetaM (Array Node × Array Edge) := do
      let mut ns : Array Node := #[]
      let mut es : Array Edge := #[]
      for i in [0:3] do
        let (id, o) := p.nodes[i]!
        let p := if i == 0 then (1.0, 0.0) else if i == 1 then (gx, -1.0) else (1.0, -1.0)
        ns := ns.push { id, gx := p.1, gy := p.2, label := (← label o) }
      for i in [0:2] do
        let (src, tgt, f) := p.edges[i]!
        es := es.push { src, tgt, label := (← label f), side := if i == 0 then side₀ else "bottom",
                        dash := ← fc.dashes f }
      return (ns, es)
    let (ln, le) ← place fc.lhs "left" 0.0
    let (rn, re) ← place fc.rhs "right" 2.0
    let nodes := ln ++ rn.filter fun v => !ln.any (·.id == v.id)
    let some (c, sym) := fc.chord | throwError "a fan is a pasted pair and has a chord"
    -- The chord drops from the apex to the target below it, its label set to the LEFT, on the side
    -- of the face the `lhs` bounds.
    let edges := le ++ re ++ #[{ src := "s", tgt := "t", label := (← label c), side := "left",
                                 dash := true : Edge }]
    let mark (s : String) (ids : Array String) : Array FaceMark :=
      let ps := ids.filterMap fun id => (nodes.find? (·.id == id)).map fun v => (v.gx, v.gy)
      let k := ps.size.toFloat
      if s == "=" || ps.isEmpty then #[] else
        #[{ sym := s, gx := ps.foldl (fun a p => a + p.1) 0.0 / k,
            gy := ps.foldl (fun a p => a + p.2) 0.0 / k }]
    return (nodes, edges,
      mark fc.sym (fc.lhs.nodes.map (·.1)) ++ mark sym (fc.rhs.nodes.map (·.1)))
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
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← label o) }
  for j in [0:m+1] do
    let (id, o) := fc.rhs.nodes[j]!
    let (gx, gy) := vertexAt left bot fx fy true j
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← label o) }
  for i in [0:n] do
    let (src, tgt, f) := fc.lhs.edges[i]!
    edges := edges.push { src, tgt, label := (← label f), side := sideAt top right false i,
                          bow := if bowed then 0.9 else 0.0, dash := ← fc.dashes f }
  for j in [0:m] do
    let (src, tgt, f) := fc.rhs.edges[j]!
    edges := edges.push { src, tgt, label := (← label f), side := sideAt left bot true j,
                          bow := if bowed then 0.9 else 0.0, dash := ← fc.dashes f }
  -- A face commutes unless marked: an equation carries no symbol, a lax face keeps its `⊑`/`≤`.
  -- The symbol goes at the average of ITS OWN corners, which for a convex polygon is inside it —
  -- and a chord splits the polygon in two, so each side's symbol takes that side's corners alone.
  let vs := nodes
  let mark (sym : String) (ids : Array String) : Array FaceMark :=
    let ps := ids.filterMap fun id => (vs.find? (·.id == id)).map fun v => (v.gx, v.gy)
    let k := ps.size.toFloat
    if sym == "=" || ps.isEmpty then #[] else
      #[{ sym, gx := ps.foldl (fun a p => a + p.1) 0.0 / k,
          gy := ps.foldl (fun a p => a + p.2) 0.0 / k }]
  match fc.chord with
  | none => return (nodes, edges, mark fc.sym (nodes.map (·.id)))
  | some (c, sym) =>
    -- The chord runs straight between the two shared ends, dashed: it is the arrow the two faces
    -- induce, and its label is set above it, the one label the outer polygon may hold.
    let withChord := edges.push
      { src := "s", tgt := "t", label := (← label c), side := "top", dash := true }
    return (nodes, withChord,
      mark fc.sym (fc.lhs.nodes.map (·.1)) ++ mark sym (fc.rhs.nodes.map (·.1)))

/-! ### Emitting the page -/

/-- An array literal, one row a line.  `close` is what follows the closing `)`: a top-level `#let`
    ends there, a field of a panel dict needs the comma that separates it from the next field. -/
def typstArr (rows : List String) (close : String) : String :=
  "(\n" ++ String.join (rows.map fun r => s!"  {r},\n") ++ ")" ++ close

def typstNodes (ns : Array Node) (close := "\n") : String :=
  typstArr (ns.toList.map fun v =>
    s!"(id: {typstString v.id}, at: ({fmt v.gx}, {fmt v.gy}), label: raw({typstString v.label}))")
    close

-- `dash` is written only where it is set: the chord is the one dashed edge, and a `dash: false` on
-- every other line is a field no reader of the file has to know about.
def typstEdges (es : Array Edge) (close := "\n") : String :=
  typstArr (es.toList.map fun e =>
    s!"(from: {typstString e.src}, to: {typstString e.tgt}, \
       label: raw({typstString e.label}), side: {typstString e.side}, bow: {fmt e.bow}\
       {if e.dash then ", dash: true" else ""})")
    close

def typstFaces (fs : Array FaceMark) (close := "\n") : String :=
  typstArr (fs.toList.map fun f => s!"(sym: {typstString f.sym}, at: ({fmt f.gx}, {fmt f.gy}))") close

/-- One panel's three tables. -/
abbrev Panel := Array Node × Array Edge × Array FaceMark

def typstPanels (ps : Array Panel) : String :=
  typstArr (ps.toList.map fun (ns, es, fs) =>
    "(nodes: " ++ typstNodes ns ",\n   edges: " ++ typstEdges es ",\n   faces: "
      ++ typstFaces fs ")") "\n"

/-- The generated file is BOTH a standalone page and an importable module, as the string-diagram
    exporter's is: `pic` is bound at the top for a note that wants the picture in a table cell.
    The page below draws the panel UNSCALED — `pic` carries the note's `s: 74%`, and `scripts/svg-check`
    measures this page against `diag/natsq.typ`, which is drawn at full size.

    ONE panel is written as one panel, not as a row of one: a page holding a single face and a page
    holding a row are different pages, and `cdrow` is the row's helper. -/
def cdPage (sel : String) (ps : Array Panel) : String :=
  let head := "// GENERATED by `diag-export --commutative` — do not edit; regenerate with\n\
    //   ./scripts/diag-export --commutative " ++ sel ++ "\n\
    #import \"../../cdpanel.typ\": *\n\n"
  let cert := "#let cert = (lean: " ++ typstString sel ++ ")\n"
  let tail := "\n#set page(width: auto, height: auto, margin: 12pt)\n\
    #set text(size: 10pt)\n\n\
    #text(11pt)[*`" ++ sel ++ "`*]\n\n"
  match ps with
  | #[(ns, es, fs)] =>
    head ++ "#let nodes = " ++ typstNodes ns ++ "#let edges = " ++ typstEdges es
      ++ "#let faces = " ++ typstFaces fs ++ cert
      ++ "#let pic = cdpanel(nodes, edges, faces, cert: cert)\n"
      ++ tail ++ "#cdpanel(nodes, edges, faces, s: 100%, cert: cert)\n"
  | _ =>
    head ++ "#let panels = " ++ typstPanels ps ++ cert
      ++ "#let pic = cdrow(panels, cert: cert)\n"
      ++ tail ++ "#cdrow(panels, s: 100%, cert: cert)\n"

/-- The FACES a statement asserts.  An equation or inequation is one; a CONJUNCTION is one per
    conjunct, each drawn on its own grid unless the two paste; an `↔` is the side `side` names,
    because the two sides of an equivalence are two claims and not two paths.  What is not yet any
    of those gets ONE delta step on its head and its binders opened — `StrictNatural F G φ` needs
    exactly one such step, and a statement that needs none pays nothing. -/
partial def faces (what : Name) (body : Expr) (side : Option String) (fuel : Nat)
    (induced : Array Expr := #[]) : MetaM (Array Face) := do
  match body.getAppFnArgs with
  | (``And, #[l, r]) =>
    return (← faces what l side fuel induced) ++ (← faces what r side fuel induced)
  | (``Iff, #[l, r]) =>
    let some s := side
      | throwError "{what}: an `↔` is two claims, not two paths — name a side, `{what}.lhs` or \
          `{what}.rhs`"
    -- The side NOT drawn is still read: it is where an equivalence says which of the drawn
    -- arrows the statement produces, and that is what the picture dashes.
    let (this, other) := if s == "lhs" then (l, r) else (r, l)
    faces what this none fuel (induced ++ (← inducedIn other))
  | _ =>
    match StrDiag.split body with
    | some (sym, l, r) => return #[← Face.of sym (← interp l) (← interp r) induced]
    | none =>
      if fuel == 0 then
        throwError "{what}: not an equation or inequation of composites, and no definition to \
          open — {← Meta.ppExpr body}"
      let .const n us := body.getAppFn
        | throwError "{what}: not an equation or inequation of composites — {← Meta.ppExpr body}"
      let some ci := (← getEnv).find? n
        | throwError "{what}: no such constant in the statement's head: {n}"
      let some v := ci.value?
        | throwError "{what}: `{n}` heads the statement and has no definition to open"
      let body := (mkAppN (v.instantiateLevelParams ci.levelParams us) body.getAppArgs).headBeta
      Meta.forallTelescopeReducing body fun _ b => faces what b side (fuel - 1) induced

/-- One part of the command line: a declaration, and the side of its `↔` if it names one. -/
def part (s : String) : Name × Option String :=
  if s.endsWith ".lhs" then ((s.dropEnd 4).toString.toName, some "lhs")
  else if s.endsWith ".rhs" then ((s.dropEnd 4).toString.toName, some "rhs")
  else (s.toName, none)

/-- Draw one or more statements as ONE page.  The FIRST names the telescope and every other is
    instantiated at its binders: two faces of one picture are about one set of objects and arrows,
    and separately opened binders would be two variables that only look alike, so nothing would ever
    be found shared.  Two faces sharing exactly one edge are pasted along it; anything else is one
    panel per face, set side by side. -/
def draw (sel : String) : MetaM String := do
  let parts := (sel.splitOn "+").toArray.map part
  let (n₀, s₀) := parts[0]!
  let some ci := (← getEnv).find? n₀ | throwError "no such declaration: {n₀}"
  Meta.forallTelescopeReducing ci.type fun xs body => do
    let mut fs ← faces n₀ body s₀ 3
    for (n, s) in parts.extract 1 parts.size do
      let some c := (← getEnv).find? n | throwError "no such declaration: {n}"
      -- Matched by TYPE, not by position or by name: the two declarations may bind the same objects
      -- in either order — an instance before or after the objects it is about — and a binder's name
      -- is not what says two statements are about one arrow.
      -- Its UNIVERSES are metavariables too: two modules name the same level differently (`u` and
      -- `u_1`), and a level left as a parameter makes `Type u` and `Type u_1` two different types.
      let us ← c.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      let (ms, _, b) ← Meta.forallMetaTelescope (c.type.instantiateLevelParams c.levelParams us)
      let mut free := xs
      for m in ms do
        let ty ← Meta.inferType m
        let mut hit := false
        for i in [0 : free.size] do
          unless hit do
            if ← commitWhen (do
                if ← Meta.isDefEq ty (← Meta.inferType free[i]!) then Meta.isDefEq m free[i]!
                else return false) then
              free := free.extract 0 i ++ free.extract (i + 1) free.size
              hit := true
        unless hit do
          throwError "{n} binds `{← Meta.ppExpr ty}`, which {n₀} does not — it binds \
            {← free.mapM fun x => do return m!"`{← Meta.ppExpr (← Meta.inferType x)}`"} — so the \
            two are not statements about one set of objects and arrows and cannot be one picture"
      fs := fs ++ (← faces n (← instantiateMVars b) s 3)
    if let #[f, g] := fs then
      if let some fc ← Face.paste f g then
        return cdPage sel #[← layout fc]
    return cdPage sel (← fs.mapM layout)

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
    IO.eprintln "usage: diag-export --commutative <selector> [<selector> ...]\n\
      a selector is `<decl>`, `<decl>.lhs`/`.rhs` for one side of an `↔`, and `<a>+<b>` for two\n\
      statements drawn as one page — pasted along the edge they share, or set side by side"
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
    let run : CoreM String := Meta.MetaM.run' (draw arg)
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
