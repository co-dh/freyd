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
-- The note's spelling of a term, shared with the string and circuit pictures.
import diag.tool.Label
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

-- Every label of every picture is `diag/tool/Label.lean`'s: one spelling of composition, of the
-- converse and of the note's brackets, shared with the string and circuit functors.
open StrDiag (plain label labelParts)

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
  /-- The note's hue its object is drawn in, named by the ROLE it plays — see `nodeHues`. -/
  hue : String := "BLACK"

/-- An edge: the two nodes it joins, the arrow it stands for, and which side of the face it is on —
    the side is the direction its label is set in, away from the face. -/
structure Edge where
  src : String
  tgt : String
  /-- The arrow's label in the PARTS the panel sets it in (`StrDiag.labelParts`): one part for an
      ordinary arrow, numerator and denominator for the note's fraction bar. -/
  label : Array String
  side : String
  /-- How far the edge bows out of its chord, in grid units — a MAGNITUDE: which way it bows is
      `side`, as for the label.  Zero for every edge of a face with three or more nodes; two
      parallel arrows between one pair of nodes would otherwise be drawn on top of each other. -/
  bow : Float := 0.0
  /-- Drawn dashed.  THE NOTE DASHES THE ARROW THE STATEMENT PRODUCES, and nothing else — see
      `Face.dashes`. -/
  dash : Bool := false
  /-- The note's hue it is drawn in, named by the ROLE its arrow plays in the statement — see
      `Face.hue`.  No default: every edge is drawn in some colour, so every place that makes one
      says which. -/
  hue : String

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
    statement it came from — and each vertex spelled as the object it IS (`StrDiag.objSpelling`), so
    a square at a named initial algebra has the list at its corners where an abstract one has `T`. -/
def Path.arrow (f : Expr) : MetaM Path := do
  let (a, b) ← StrDiag.homEnds f
  let a ← StrDiag.objSpelling a
  let b ← StrDiag.objSpelling b
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
  | (``Cat.id, _) => return Path.id (← StrDiag.objSpelling (← StrDiag.homEnds e).1)
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

/-- Whether the AMBIENT STRUCTURE supplies this arrow, as against the statement handing it over: its
    head is a structure's PROJECTION — `(initial _ _).α`, `P.outl`, `∋`, `𝟙` — or its own declaration
    takes an INSTANCE of the class that gives it, as the singleton `𝟙%∋` takes a `PowerAllegory`.
    Read off the constant's declaration in the environment, never a list of names here: an arrow
    defined outright at the objects it stands between — `[nil,⊸ nil ∪ cons]` — takes neither, and is
    data the picture is handed exactly as a free variable would be. -/
def structureArrow (f : Expr) : MetaM Bool := do
  let some n := f.getAppFn.constName? | return false
  let env ← getEnv
  if env.isProjectionFn n then return true
  let some ci := env.find? n | return false
  return hasInst ci.type
where
  hasInst : Expr → Bool
    | .forallE _ _ b bi => bi.isInstImplicit || hasInst b
    | .mdata _ b => hasInst b
    | _ => false

/-- A declaration's conclusion read as an EQUATION, if it is one: the two sides, under whatever `∀`
    binders it carries.  Pure, and that is the point — the scan below runs over every declaration in
    the environment, so its filter may elaborate nothing. -/
partial def eqSides : Expr → Option (Expr × Expr)
  | .forallE _ _ b _ | .mdata _ b => eqSides b
  | t => match t.getAppFnArgs with
    | (``Eq, #[_, l, r]) => some (l, r)
    | _ => none

/-- Whether a constant NAMES ONE ARROW: its declaration stands at a `Cat.Hom` and takes no arrow of
    its own, so it is an arrow with a name rather than an operator ON arrows (`≫`, `∩`, `°`, a
    relator's action).  An equation about such a constant says what that arrow IS. -/
def arrowName (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some ci => go ci.type | none => false
where
  go : Expr → Bool
    | .forallE _ t b _ => !t.isAppOf ``Cat.Hom && go b
    | .mdata _ b => go b
    | t => t.isAppOf ``Cat.Hom

/-- THE ARROWS THE ENVIRONMENT DEFINES BY A UNIVERSAL CONSTRUCTION: a named arrow `c` some theorem
    states `c … = <induced former> …` of.  This is how a CLOSED statement says which of its constants
    a universal property produced — the same question the other side of an `↔` answers for an open
    one, and the same search the string exporter runs for a bead's naturality proof.  `prefix_cata`
    says `prefix=⦇[nil,⊸ nil ∪ cons]⦈`, so every picture of `prefix` draws what the fold produced and
    no name of it is written in this file.  Scanned ONCE per process: the pass is over every
    declaration. -/
initialize inducedDefsRef : IO.Ref (Option NameSet) ← IO.mkRef none

def inducedDefs : MetaM NameSet := do
  if let some s ← inducedDefsRef.get then return s
  let heads ← inducedHeads
  let env ← getEnv
  let mut out : NameSet := {}
  for (_, ci) in env.constants do
    unless ci matches .thmInfo _ do continue
    let some (l, r) := eqSides ci.type | continue
    let some a := l.getAppFn.constName? | continue
    let some b := r.getAppFn.constName? | continue
    if heads.contains b && arrowName env a then out := out.insert a
    if heads.contains a && arrowName env b then out := out.insert b
  inducedDefsRef.set (some out)
  return out

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

/-- WHETHER THE STATEMENT PRODUCES THIS ARROW: an induced constructor heads it (`α⦇f⦈=F(⦇f⦈)f`
    produces `⦇f⦈`), or the other side of the statement's `↔` says so (`αX=F(X)f ⟺ X=⦇f⦈` produces
    `X`, which is a variable and carries no head to read it off).  Being produced is what makes an
    arrow induced; being DRAWN dashed is that and having no chord, since a paste dashes the chord
    alone. -/
def Face.produces (fc : Face) (f : Expr) : MetaM Bool := do
  -- The `↔`'s other side is read FIRST: it says outright which arrow the claim determines, whatever
  -- symbol this side wears.
  if ← fc.induced.anyM fun g => Meta.isDefEq g f then return true
  -- AN INEQUATION DETERMINES NOTHING.  A universal property produces its arrow by an EQUATION —
  -- `α⦇f⦈=F(⦇f⦈)f` says `⦇f⦈` is the one arrow making the square commute — where `⊑` only compares
  -- two composites the statement is handed, so a lax square's `prefix` and `Λ(F(∋)f)` are arrows it
  -- is ABOUT, not arrows it builds, and the note draws both solid.
  unless fc.sym == "=" do return false
  if isInduced (← inducedHeads) f then return true
  -- A CLOSED arrow carries its role in the environment instead.  The structure is asked FIRST: an
  -- equation between a fold and an arrow the ambient structure supplies — `⦇α⦈=𝟙` — is a law about
  -- that arrow, not a definition of it.
  if ← structureArrow f then return false
  let some n := f.getAppFn.constName? | return false
  return (← inducedDefs).contains n

/-- WHICH ARROWS THIS STATEMENT PRODUCES, hence which are drawn dashed.  A pasted pair produces its
    CHORD — the arrow the two faces share is the one they jointly determine — and nothing else, so
    `⦇h⦈` and `⦇k⦈` under the fan's `⟨⦇h⦈,⦇k⦈⟩` stay solid: some other law produced them.  A single
    face has no chord, and then an arrow is produced when an induced constructor heads it
    (`α⦇f⦈=F(⦇f⦈)f` produces `⦇f⦈`) or when the other side of the statement's `↔` says so. -/
def Face.dashes (fc : Face) (f : Expr) : MetaM Bool := do
  if fc.chord.isSome then return false
  fc.produces f

/-! ### Which role an arrow plays, hence its colour -/

/-- The statement's free ARROW VARIABLES an expression mentions — the `f`, `R`, `h`, `k` a picture
    is HANDED.  Read off the TERM and never off a list of letters: a free variable whose type is a
    `Cat.Hom` is an arrow the statement binds, so a fold `⦇h⦈` of one mentions one and the structure
    map of a bundled algebra, whose free variable is the algebra, does not. -/
partial def arrowVars (e : Expr) : MetaM (Array Expr) := do
  match e with
  | .fvar _ => return if (← Meta.inferType e).isAppOf ``Cat.Hom then #[e] else #[]
  -- A FAMILY the statement binds is handed over one COMPONENT at a time: `φ : ∀ A, GA ⟶ FA` is no
  -- arrow itself — its type is a `∀`, so the clause above cannot see it — and `φ A` is, at the two
  -- objects that component runs between, which are the ones the picture draws.
  | .app f a =>
    if ← StrDiag.isComponent e then return #[e]
    return (← arrowVars f) ++ (← arrowVars a)
  | .lam _ t b _ | .forallE _ t b _ => return (← arrowVars t) ++ (← arrowVars b)
  | .letE _ t v b _ => return (← arrowVars t) ++ (← arrowVars v) ++ (← arrowVars b)
  | .mdata _ b => arrowVars b
  | .proj _ _ b => arrowVars b
  | _ => return #[]

/-- The arrow a FUNCTOR has moved, when this arrow is one: an application carrying an arrow argument
    and standing at objects that argument does not — `F(⦇f⦈) : FT ⟶ FA` over `⦇f⦈ : T ⟶ A`, `E(R)`
    over `R`, whichever way the action is written (`Functor.map`, or a relator's own constant, as
    the existential image is).  Read off the two TYPES, never off the head's name: an operator that
    RESHAPES an arrow — `R°`, `R∩S` — stands at the arrow's own two objects and is not an image, so
    it is still the arrow the statement handed over. -/
def imageOf (f : Expr) : MetaM (Option Expr) := do
  let (a, b) ← StrDiag.homEnds f
  for g in f.getAppArgs do
    if (← Meta.inferType g).isAppOf ``Cat.Hom then
      let (c, d) ← StrDiag.homEnds g
      unless ← [(a, c), (a, d), (b, c), (b, d)].anyM fun (x, y) => Meta.isDefEq x y do
        return some g
  return none

/-- THE ARROWS THE PICTURE IS HANDED, as the sub-expressions that carry them: the statement's free
    arrow VARIABLES, and — where it binds none — the arrow ITSELF, when it is a closed one no functor
    moved, no universal construction produced and no ambient structure supplies.  A closed statement
    hands its data over exactly as an open one does: `α prefix=F(prefix)[nil,⊸ nil ∪ cons]` hands over
    the algebra the way `α⦇f⦈=F(⦇f⦈)f` hands over `f`, and the objects it stands between are the ones
    the picture was handed. -/
def Face.handed (fc : Face) (f : Expr) : MetaM (Array Expr) := do
  let vs ← arrowVars f
  unless vs.isEmpty do return vs
  if (← imageOf f).isSome || (← fc.produces f) || (← structureArrow f) then return #[]
  return #[f]

/-- Whether an arrow is one the statement HANDED over. -/
def Face.given (fc : Face) (f : Expr) : MetaM Bool := return !(← fc.handed f).isEmpty

/-- The CLAIMS the face asserts, each as the arrows it is made of: a single face asserts one, its
    whole boundary, and a paste asserts two — the two statements it was pasted out of, each being one
    side closed by the chord the two share. -/
def Face.claims (fc : Face) : Array (Array Expr) :=
  let es (p : Path) := p.edges.map (·.2.2)
  match fc.chord with
  | none => #[es fc.lhs ++ es fc.rhs]
  | some (c, _) => #[(es fc.lhs).push c, (es fc.rhs).push c]

/-- Whether ONE CLAIM of the face names both this arrow and its image under a relator — `F(R)` drawn
    beside `R`.  A claim carrying an arrow BOTH ways is ABOUT that transport, so the arrow is the
    structure the property is about and not one more arrow the statement hands over, which is why it
    takes `GIVEN2` though it mentions a free variable.  Asked of one claim and not of the whole
    polygon: a paste is two statements, and `Λ(R)∋=R ∧ Λ(R)=(𝟙%∋)E(R)` names `R` in the first and
    `E(R)` in the second, so neither claim is about carrying `R` anywhere. -/
def Face.transports (fc : Face) (f : Expr) : MetaM Bool :=
  fc.claims.anyM fun cl => do
    unless ← cl.anyM (Meta.isDefEq · f) do return false
    cl.anyM fun g => do
      match ← imageOf g with
      | some h => Meta.isDefEq h f
      | none => return false

/-- WHICH ROLE an arrow plays, hence which of the note's hues it is drawn in (`diag/draw.typ`:
    `GIVEN1` green, `GIVEN2` purple, `INDUCED` blue).

    `INDUCED` is what a universal property PRODUCES: every arrow the dash rule marks, and a
    functor's image of a PRODUCED one — `F(⦇f⦈)` and `F(X)` under `αX=F(X)f ⟺ X=⦇f⦈` are induced
    without being dashed, since the induced arrow is what determines them, and which arrow that is
    is `Face.produces`, never a head test that a variable like `X` fails.  `GIVEN1` is an arrow the
    picture is HANDED (`Face.handed`) — one mentioning a free arrow variable, or, in a statement made
    entirely of constants, one the environment neither defines by a universal construction nor
    supplies out of the ambient structure.  `GIVEN2` is the structure the property is ABOUT — the
    initial algebra's `α`, `∋`, `π₁`, `𝟙`, the singleton `𝟙%∋`, each of which the structure supplies —
    and a relator's image of a given arrow, `E(R)`, which the relator determines rather than the
    statement handing it over. -/
def Face.hue (fc : Face) (f : Expr) : MetaM String := do
  if ← fc.dashes f then return "INDUCED"
  match ← imageOf f with
  | some g => return if ← fc.produces g then "INDUCED" else "GIVEN2"
  | none => return if (← fc.given f) && !(← fc.transports f) then "GIVEN1" else "GIVEN2"

/-- WHICH COMPONENT OF THE ARROW IT INDUCES each side of a pasted face carries — `none` unless the
    statement is ABOUT those components.  The chord is what the two faces jointly determine; when an
    induced constructor built it out of arrow arguments — `⟨f,g⟩` out of `f` and `g` — and each side
    of the paste carries exactly one of them, the two sides ARE the two components, and which is
    which is the whole content of the picture.  `some (i, j)`: the `lhs` carries the `i`-th
    argument, the `rhs` the `j`-th.  Every other chord names no components and each arrow keeps its
    ROLE hue: `Λ(R)∋=R ∧ Λ(R)=(𝟙%∋)E(R)` builds its chord out of the one arrow `R`, which is one
    side's leg and not a component the other side has a counterpart for. -/
structure Component where
  /-- Which argument of the chord this side carries — it is drawn in `GIVEN(idx+1)`. -/
  idx : Nat
  /-- The two vertices that argument's own arrow joins, by id: the objects THIS component is
      between, which is what tells a node of one component from one every component shares. -/
  ends : Array String
  deriving Inhabited

def Face.components (fc : Face) : MetaM (Option (Component × Component)) := do
  let some (c, _) := fc.chord | return none
  unless isInduced (← inducedHeads) c do return none
  let mut args : Array Expr := #[]
  for a in c.getAppArgs do
    if (← Meta.inferType a).isAppOf ``Cat.Hom then args := args.push a
  -- One component per SIDE of the paste, and a side carries exactly one of them: fewer and the
  -- sides would have to share a component, more and a side would carry two.
  unless args.size == 2 do return none
  let carries (p : Path) : MetaM (Array Component) := do
    let mut out : Array Component := #[]
    for i in [0 : args.size] do
      for (s, t, f) in p.edges do
        if ← Meta.isDefEq f args[i]! then out := out.push { idx := i, ends := #[s, t] }
    return out
  let (l, r) := (← carries fc.lhs, ← carries fc.rhs)
  unless l.size == 1 && r.size == 1 && l[0]!.idx != r[0]!.idx do return none
  return some (l[0]!, r[0]!)

/-- The hue an edge of one side of the face takes.  Where the statement is about the components
    (`Face.components`) it is the SIDE's, so a reader follows one component down each side; where it
    is not, it is the arrow's own role (`Face.hue`). -/
def Face.hueOn (fc : Face) (comp : Option Nat) (f : Expr) : MetaM String := do
  match comp with
  | some i => return s!"GIVEN{i + 1}"
  | none => fc.hue f

/-- The nodes of a face drawn BY COMPONENT, read off the objects each COMPONENT'S OWN ARROW is
    between: a node one component alone is an end of belongs to it and wears its hue; a node EVERY
    component is an end of is shared by all of them and belongs to none, so it stays black; and a
    node NO component is an end of is one the universal property built out of the components'
    objects — `A×B` over `A` and `B` — and wears the induced hue.  That is one rule for both shapes
    the note draws: `⟨f,g⟩π₁=f ∧ ⟨f,g⟩π₂=g`, whose components share their source, has one black
    node and one induced one, while `(R×S)π₁⊑π₁R ∧ (R×S)π₂⊑π₂S`, whose components share neither
    end, has two induced ones and no black. -/
def componentNodeHues (l r : Component) (ns : Array Node) : Array Node :=
  ns.map fun v =>
    match l.ends.contains v.id, r.ends.contains v.id with
    | true, true => { v with hue := "BLACK" }
    | true, false => { v with hue := s!"GIVEN{l.idx + 1}" }
    | false, true => { v with hue := s!"GIVEN{r.idx + 1}" }
    | false, false => { v with hue := "INDUCED" }

/-- The nodes the statement HANDS the picture: those standing at an END of one of the arrows it
    hands over (`Face.handed`).  A handed arrow gives its two objects whether or not the picture
    draws the arrow itself — `tri(f)⦇g⦈=⦇F(𝟙,f)g⦈` draws neither `f` nor `g` and is still handed
    their carrier `A` — so the question is asked of the OBJECTS, never of the edges that happen to be
    drawn, which is what an "end of a GIVEN1 edge" test could only answer for the ones that are. -/
def Face.givenNodes (fc : Face) : MetaM (Array String) := do
  let arrows := (fc.lhs.edges ++ fc.rhs.edges).map (·.2.2) ++ (fc.chord.map (·.1)).toArray
  let mut objs : Array Expr := #[]
  for f in arrows do
    for x in ← fc.handed f do
      let (a, b) ← StrDiag.homEnds x
      objs := (objs.push a).push b
  let mut ids : Array String := #[]
  for (id, o) in fc.lhs.nodes ++ fc.rhs.nodes do
    unless ids.contains id do
      if ← objs.anyM (Meta.isDefEq o) then ids := ids.push id
  return ids

/-- A node's hue: `GIVEN1` when the statement hands the picture that object (`Face.givenNodes`) and
    no GIVEN2 edge touches it — an object the picture is handed, as against one where the structure
    the property is about already lives (`T` and `FT` are ends of `α`, so they stay black). -/
def nodeHues (given : Array String) (ns : Array Node) (es : Array Edge) : Array Node :=
  ns.map fun v =>
    let touches (h : String) := es.any fun e => (e.src == v.id || e.tgt == v.id) && e.hue == h
    if given.contains v.id && !touches "GIVEN2" then { v with hue := "GIVEN1" } else v

/-- Where a face's symbol is set, once its corners are placed: the average of ITS OWN corners, which
    for a convex polygon is inside it — and a chord splits the polygon in two, so each side's symbol
    takes that side's corners alone.  A face commutes unless marked, so an equation carries none. -/
def faceMark (ns : Array Node) (sym : String) (ids : Array String) : Array FaceMark :=
  let ps := ids.filterMap fun id => (ns.find? (·.id == id)).map fun v => (v.gx, v.gy)
  let k := ps.size.toFloat
  if sym == "=" || ps.isEmpty then #[] else
    #[{ sym, gx := ps.foldl (fun a p => a + p.1) 0.0 / k,
        gy := ps.foldl (fun a p => a + p.2) 0.0 / k }]

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

/-- Whether that side is one of the two VERTICAL ones. -/
def isVertical (first second : Nat) (mirror : Bool) (i : Nat) : Bool :=
  let s := sideAt first second mirror i
  s == "left" || s == "right"

/-- WHICH WAY ROUND THE FACE HANGS.  `legs` sends a path clockwise — along the top, then down the
    right — and its partner counter-clockwise, and swapping the two flags is the only other way the
    same polygon can be laid on the same grid: it transposes the picture, horizontals for verticals.
    The note hangs an arrow a relator has MOVED — `F(R)` over `R`, `list(R)` over `R` — on a VERTICAL
    side, so the square reads as the transport sliding across, and that is the choice made here:
    whichever of the two orientations stands more of the moved edges upright, the clockwise one when
    they tie.  A face that moves nothing scores zero either way and keeps the default.

    A PASTE IS NOT FREE TO TURN: its chord runs from the shared source to the shared target with the
    `lhs` face above it and the `rhs` below, and the chord's own label is set inside the `lhs` face,
    so swapping the two sides would put each face on the other side of the arrow they induce. -/
def Face.transposed (fc : Face) : MetaM Bool := do
  if fc.chord.isSome then return false
  let moved (es : Array (String × String × Expr)) : MetaM (Array Bool) :=
    es.mapM fun (_, _, f) => return (← imageOf f).isSome
  let (ml, mr) := (← moved fc.lhs.edges, ← moved fc.rhs.edges)
  let upright (ms : Array Bool) (mirror : Bool) : Nat := Id.run do
    let (first, second) := legs ms.size mirror
    let mut k := 0
    for i in [0 : ms.size] do
      if ms[i]! && isVertical first second mirror i then k := k + 1
    return k
  return upright ml true + upright mr false > upright ml false + upright mr true

/-- A FAN, the one pasted shape that is not a square: every arrow of the polygon LEAVES an end of
    the chord, so the two ends are two apexes over one row of shared targets, and the chord runs
    between them.  Laid out that way — the chord's source above, its target below it, the two
    interior vertices left and right of the target — where a square would put the chord on a
    diagonal and one apex's two arrows in opposite directions.  `⟨⦇h⦈,⦇k⦈⟩π₁=⦇h⦈ ∧ ⟨⦇h⦈,⦇k⦈⟩π₂=⦇k⦈`
    is a fan; `Λ(R)∋=R ∧ Λ(R)=(𝟙%∋)E(R)` is not, its `E(R)` arriving AT the chord's target. -/
def Face.isFan (fc : Face) : Bool :=
  fc.chord.isSome && fc.lhs.edges.size == 2 && fc.rhs.edges.size == 2 &&
    (fc.lhs.edges ++ fc.rhs.edges).all fun (s, _, _) => s == "s" || s == "t"

/-- A PASTED PAIR OF SQUARES: each face, opened at the chord, runs the chord's source, two interior
    vertices and the chord's target — four vertices, three edges.  Two squares cannot be folded
    into one square's boundary the way two two-edge sides can, so the chord is drawn HORIZONTALLY
    between the two ends it joins, with one square above it and one below: the two components are
    symmetric about the arrow they induce, and the picture says so.  `(R×S)π₁⊑π₁R ∧ (R×S)π₂⊑π₂S`
    is this shape; `Λ(R)∋=R ∧ Λ(R)=(𝟙%∋)E(R)`, two two-edge sides, is the diagonal-chord square. -/
def Face.isPastedSquares (fc : Face) : Bool :=
  fc.chord.isSome && fc.lhs.edges.size == 3 && fc.rhs.edges.size == 3

/-- A TRIANGLE: one side turns a corner, the other is a chord that cannot.  Three nodes, so the grid
    has a free column, and the note spends it on SYMMETRY — the two sides leave the shared source at
    opposite ends of the top row and meet at the column between them, which makes the two arrows
    into the shared target mirror images.  The right triangle the general grid gives instead lays
    the chord along the diagonal of a square whose fourth corner is nobody's, and the two arrows
    into the target then look unrelated (the note's `<horner>`, `tri(f)⦇g⦈=⦇F(𝟙,f)g⦈`). -/
def Face.isTriangle (fc : Face) : Bool :=
  fc.chord.isNone && fc.lhs.edges.size + fc.rhs.edges.size == 3 &&
    (fc.lhs.edges.size == 1 || fc.rhs.edges.size == 1)

/-- The face laid on the grid: coordinates for its two boundary paths, and the symbol between them.
    Only `cdpanel` can measure a label, so what leaves here is grid units, not centimetres. -/
def layout (fc : Face) : MetaM (Array Node × Array Edge × Array FaceMark) := do
  let comps ← fc.components
  let given ← fc.givenNodes
  if fc.isTriangle then
    -- The turning side leaves the shared source along the top row to the far column and drops to
    -- the middle one; the chord drops to that same vertex from the other end of the row.  Which of
    -- the two sides turns decides which end of the row the shared source is at.
    let turns := fc.lhs.edges.size == 2
    let long := if turns then fc.lhs else fc.rhs
    let cells : Array (Float × Float) := #[(if turns then 0.0 else 2.0, 0.0),
                                           (if turns then 2.0 else 0.0, 0.0), (1.0, -1.0)]
    let mut nodes : Array Node := #[]
    for i in [0:3] do
      let (id, o) := long.nodes[i]!
      nodes := nodes.push { id, gx := cells[i]!.1, gy := cells[i]!.2, label := (← label o) }
    let mut edges : Array Edge := #[]
    for i in [0:2] do
      let (src, tgt, f) := long.edges[i]!
      edges := edges.push { src, tgt, label := (← labelParts f),
                            side := if i == 0 then "top" else if turns then "right" else "left",
                            dash := ← fc.dashes f, hue := ← fc.hue f }
    let (csrc, ctgt, cf) := (if turns then fc.rhs else fc.lhs).edges[0]!
    edges := edges.push { src := csrc, tgt := ctgt, label := (← labelParts cf),
                          side := if turns then "left" else "right",
                          dash := ← fc.dashes cf, hue := ← fc.hue cf }
    return (nodeHues given nodes edges, edges, faceMark nodes fc.sym (nodes.map (·.id)))
  if fc.isFan then
    -- Three columns, two rows: the apex over the middle of the row its chord ends in.
    let place (p : Path) (side₀ : String) (gx : Float) (comp : Option Nat)
        : MetaM (Array Node × Array Edge) := do
      let mut ns : Array Node := #[]
      let mut es : Array Edge := #[]
      for i in [0:3] do
        let (id, o) := p.nodes[i]!
        let p := if i == 0 then (1.0, 0.0) else if i == 1 then (gx, -1.0) else (1.0, -1.0)
        ns := ns.push { id, gx := p.1, gy := p.2, label := (← label o) }
      for i in [0:2] do
        let (src, tgt, f) := p.edges[i]!
        es := es.push { src, tgt, label := (← labelParts f), side := if i == 0 then side₀ else "bottom",
                        dash := ← fc.dashes f, hue := ← fc.hueOn comp f }
      return (ns, es)
    let (ln, le) ← place fc.lhs "left" 0.0 (comps.map (·.1.idx))
    let (rn, re) ← place fc.rhs "right" 2.0 (comps.map (·.2.idx))
    let nodes := ln ++ rn.filter fun v => !ln.any (·.id == v.id)
    let some (c, sym) := fc.chord | throwError "a fan is a pasted pair and has a chord"
    -- The chord drops from the apex to the target below it, its label set to the LEFT, on the side
    -- of the face the `lhs` bounds.
    let edges := le ++ re ++ #[{ src := "s", tgt := "t", label := (← labelParts c), side := "left",
                                 dash := true, hue := "INDUCED" : Edge }]
    let hued := match comps with
      | some (l, r) => componentNodeHues l r nodes
      | none => nodeHues given nodes edges
    return (hued, edges, faceMark nodes fc.sym (fc.lhs.nodes.map (·.1)) ++
      faceMark nodes sym (fc.rhs.nodes.map (·.1)))
  if fc.isPastedSquares then
    -- Two columns, three rows: the chord along the middle row, the `lhs` square's interior on the
    -- row above and the `rhs` square's on the row below.  Each side runs left, along, right.
    let place (p : Path) (gy : Float) (mid : String) (comp : Option Nat)
        : MetaM (Array Node × Array Edge) := do
      let cell : Array (Float × Float) := #[(0.0, -1.0), (0.0, gy), (1.0, gy), (1.0, -1.0)]
      let sides : Array String := #["left", mid, "right"]
      let mut ns : Array Node := #[]
      let mut es : Array Edge := #[]
      for i in [0:4] do
        let (id, o) := p.nodes[i]!
        ns := ns.push { id, gx := cell[i]!.1, gy := cell[i]!.2, label := (← label o) }
      for i in [0:3] do
        let (src, tgt, f) := p.edges[i]!
        es := es.push { src, tgt, label := (← labelParts f), side := sides[i]!,
                        dash := ← fc.dashes f, hue := ← fc.hueOn comp f }
      return (ns, es)
    let (ln, le) ← place fc.lhs 0.0 "top" (comps.map (·.1.idx))
    let (rn, re) ← place fc.rhs (-2.0) "bottom" (comps.map (·.2.idx))
    let nodes := ln ++ rn.filter fun v => !ln.any (·.id == v.id)
    let some (c, sym) := fc.chord | throwError "a pasted pair of squares is a paste and has a chord"
    -- The chord's own label is set ABOVE it, inside the face the `lhs` square bounds, which is where
    -- the note puts it: a chord lies between two faces and its label has to be inside one of them.
    let edges := le ++ re ++ #[{ src := "s", tgt := "t", label := (← labelParts c), side := "top",
                                 dash := true, hue := "INDUCED" : Edge }]
    let hued := match comps with
      | some (l, r) => componentNodeHues l r nodes
      | none => nodeHues given nodes edges
    return (hued, edges, faceMark nodes fc.sym (fc.lhs.nodes.map (·.1)) ++
      faceMark nodes sym (fc.rhs.nodes.map (·.1)))
  let (n, m) := (fc.lhs.edges.size, fc.rhs.edges.size)
  -- Which of the two sides runs clockwise is `Face.transposed`, so `lhs` carries the mirror flag and
  -- `rhs` the other one; every reader of the legs below takes them from the side's own flag.
  let flip ← fc.transposed
  let (lfst, lsnd) := legs n flip
  let (rfst, rsnd) := legs m (!flip)
  -- Each side's legs named by AXIS instead of by position: `legs` gives the leg a path leaves along
  -- first, and which axis that is is the side's own orientation.
  let (lhor, lver) := if flip then (lsnd, lfst) else (lfst, lsnd)
  let (rhor, rver) := if flip then (rfst, rsnd) else (rsnd, rfst)
  -- The grid is as wide as the wider of its two horizontal legs and as tall as the taller of its
  -- two vertical ones; a leg a chord does not use counts for nothing.  Both sides chords is the
  -- digon: one column, no rows, and the two edges told apart by their bow.
  -- A leg belongs to a path only when that path turns a corner: `legs` gives a chord `(1, 0)`, whose
  -- `1` is the whole path and not a leg, so a side with a zero SECOND leg contributes neither.
  let nx := (max (if lsnd == 0 then 0 else lhor) (if rsnd == 0 then 0 else rhor)).max 1
  let ny := max (if lsnd == 0 then 0 else lver) (if rsnd == 0 then 0 else rver)
  let (fx, fy) := (nx.toFloat, ny.toFloat)
  let bowed := ny == 0
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  -- The two paths share their end vertices, so the second contributes only its interior.
  for i in [0:n+1] do
    let (id, o) := fc.lhs.nodes[i]!
    let (gx, gy) := vertexAt lfst lsnd fx fy flip i
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← label o) }
  for j in [0:m+1] do
    let (id, o) := fc.rhs.nodes[j]!
    let (gx, gy) := vertexAt rfst rsnd fx fy (!flip) j
    unless nodes.any (·.id == id) do nodes := nodes.push { id, gx, gy, label := (← label o) }
  for i in [0:n] do
    let (src, tgt, f) := fc.lhs.edges[i]!
    edges := edges.push { src, tgt, label := (← labelParts f), side := sideAt lfst lsnd flip i,
                          bow := if bowed then 0.9 else 0.0, dash := ← fc.dashes f,
                          hue := ← fc.hueOn (comps.map (·.1.idx)) f }
  for j in [0:m] do
    let (src, tgt, f) := fc.rhs.edges[j]!
    edges := edges.push { src, tgt, label := (← labelParts f), side := sideAt rfst rsnd (!flip) j,
                          bow := if bowed then 0.9 else 0.0, dash := ← fc.dashes f,
                          hue := ← fc.hueOn (comps.map (·.2.idx)) f }
  match fc.chord with
  | none => return (nodeHues given nodes edges, edges, faceMark nodes fc.sym (nodes.map (·.id)))
  | some (c, sym) =>
    -- The chord runs straight between the two shared ends, dashed: it is the arrow the two faces
    -- induce, and its label is set above it, the one label the outer polygon may hold.
    let withChord := edges.push
      { src := "s", tgt := "t", label := (← labelParts c), side := "top", dash := true,
        hue := "INDUCED" }
    let hued := match comps with
      | some (l, r) => componentNodeHues l r nodes
      | none => nodeHues given nodes withChord
    return (hued, withChord, faceMark nodes fc.sym (fc.lhs.nodes.map (·.1)) ++
      faceMark nodes sym (fc.rhs.nodes.map (·.1)))

/-! ### Emitting the page -/

/-- An array literal, one row a line.  `close` is what follows the closing `)`: a top-level `#let`
    ends there, a field of a panel dict needs the comma that separates it from the next field. -/
def typstArr (rows : List String) (close : String) : String :=
  "(\n" ++ String.join (rows.map fun r => s!"  {r},\n") ++ ")" ++ close

def typstNodes (ns : Array Node) (close := "\n") : String :=
  typstArr (ns.toList.map fun v =>
    s!"(id: {typstString v.id}, at: ({fmt v.gx}, {fmt v.gy}), label: raw({typstString v.label}), \
       hue: {typstString v.hue})")
    close

-- `dash` is written only where it is set: the chord is the one dashed edge, and a `dash: false` on
-- every other line is a field no reader of the file has to know about.
def typstEdges (es : Array Edge) (close := "\n") : String :=
  typstArr (es.toList.map fun e =>
    s!"(from: {typstString e.src}, to: {typstString e.tgt}, \
       label: ({String.join (e.label.toList.map fun p => s!"raw({typstString p}), ")}), \
       side: {typstString e.side}, bow: {fmt e.bow}, \
       hue: {typstString e.hue}{if e.dash then ", dash: true" else ""})")
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
    exactly one such step, and a statement that needs none pays nothing.

    THE FACES ARE HANDED TO A CONTINUATION, not returned.  Opening a predicate's inner `∀` binders
    puts the arrows and objects the face is made of in a LOCAL CONTEXT, and a `Face` returned out of
    that context names free variables nobody can look up any more — an `unknown free variable` at the
    first `inferType`, which is every line of `layout`.  `k` runs at the bottom of every telescope
    this opens, so whatever reads the face reads it while its binders are still live. -/
partial def faces {α : Type} [Inhabited α] (what : Name) (body : Expr) (side : Option String)
    (fuel : Nat) (induced : Array Expr) (k : Array Face → MetaM α) : MetaM α := do
  match body.getAppFnArgs with
  | (``And, #[l, r]) =>
    faces what l side fuel induced fun fl =>
      faces what r side fuel induced fun fr => k (fl ++ fr)
  | (``Iff, #[l, r]) =>
    let some s := side
      | throwError "{what}: an `↔` is two claims, not two paths — name a side, `{what}.lhs` or \
          `{what}.rhs`"
    -- The side NOT drawn is still read: it is where an equivalence says which of the drawn
    -- arrows the statement produces, and that is what the picture dashes.
    let (this, other) := if s == "lhs" then (l, r) else (r, l)
    faces what this none fuel (induced ++ (← inducedIn other)) k
  | _ =>
    match StrDiag.split body with
    | some (sym, l, r) => k #[← Face.of sym (← interp l) (← interp r) induced]
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
      Meta.forallTelescopeReducing body fun _ b => faces what b side (fuel - 1) induced k

/-- One part of the command line: a declaration, and the side of its `↔` if it names one. -/
def part (s : String) : Name × Option String :=
  if s.endsWith ".lhs" then ((s.dropEnd 4).toString.toName, some "lhs")
  else if s.endsWith ".rhs" then ((s.dropEnd 4).toString.toName, some "rhs")
  else (s.toName, none)

/-- The page, once the FIRST part's faces are in hand: each remaining part adds its own, read inside
    its own telescope, and the layout runs at the bottom of them all.  It is a fold over the parts
    written as a recursion because every step opens a scope the next step must still be inside. -/
partial def drawParts (sel : String) (parts : Array (Name × Option String)) (xs : Array Expr)
    (i : Nat) (fs : Array Face) : MetaM String := do
  if i ≥ parts.size then
    if let #[f, g] := fs then
      if let some fc ← Face.paste f g then
        return cdPage sel #[← layout fc]
    return cdPage sel (← fs.mapM layout)
  else
      let (n, s) := parts[i]!
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
        for j in [0 : free.size] do
          unless hit do
            if ← commitWhen (do
                if ← Meta.isDefEq ty (← Meta.inferType free[j]!) then Meta.isDefEq m free[j]!
                else return false) then
              free := free.extract 0 j ++ free.extract (j + 1) free.size
              hit := true
        unless hit do
          throwError "{n} binds `{← Meta.ppExpr ty}`, which {parts[0]!.1} does not — it binds \
            {← free.mapM fun x => do return m!"`{← Meta.ppExpr (← Meta.inferType x)}`"} — so the \
            two are not statements about one set of objects and arrows and cannot be one picture"
      faces n (← instantiateMVars b) s 3 #[] fun fs' => drawParts sel parts xs (i + 1) (fs ++ fs')

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
    -- A DECLARATION WHOSE TYPE ENDS IN A SORT IS A PREDICATE, not a proof, so its claim is in its
    -- VALUE: what it states is itself APPLIED to its own binders, which `faces` opens with the same
    -- delta step it takes on a predicate a theorem names (`MonotonicAlg φ R`, `LaxNatural F G φ`).
    let body := if body.isSort then mkAppN (.const n₀ (ci.levelParams.map .param)) xs else body
    faces n₀ body s₀ 3 #[] fun fs => drawParts sel parts xs 1 fs

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
      openDecls := (openNs ++ StrDiag.repoNamespaces env).map (.simple · []) }
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
