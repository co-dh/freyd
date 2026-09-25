/-
  `StringDiagram` — the STRING-DIAGRAM functor: source, the 2-category of allegories, relators and
  natural families as `ExprReader` reads it off a declaration's elaborated type; target, one
  `dpanel(...)` call of `diag/dpanel.typ`, which draws it unchanged.

  A WIRE IS A RELATOR, A BEAD A 2-CELL, A REGION AN ALLEGORY (Hinze–Marsden).  So the picture is
  decided by TYPES, not by a formula: a factor's source and target say which wires it eats and which
  it makes, and the environment says whether it has a dot.

  THE GEOMETRY IS `scripts/diagram`'s, ported.  Columns are `DX` apart, rows `DY`, a bead's legs a
  block centred on the arms it replaces, and a lane's own name reserves room west of it — the same
  arithmetic, so a panel drawn from Lean and a panel drawn from a formula land on the same page in
  the same place.  The numbers are IntroString's own (pp. 46/75/79), measured there and not chosen.
-/
import diag.tool.ExprReader
-- The note's spelling of a term, shared with the circuit and commutative pictures.
import diag.tool.Label
-- The `lean:<Module>.<decl>@<key>` marker, computed exactly once in the exe: `cite-check` verifies
-- the notes' citations with it and the panels' `nat:` trace is written with the same function.
import diag.tool.Cite

open Lean

namespace Freyd.StrDiag

/-! ### The book's geometry -/

/-- The margin the leftmost lane's NAME is written into. -/
def X0 : Float := 1.875
/-- One column: IntroString p. 46's 0.5cm in cetz's own `length: 0.8cm` unit. -/
def DX : Float := 0.625
/-- One row — the height that holds one label clear of the label a row below it. -/
def DY : Float := 1.1
/-- The clear margin east of the object wire. -/
def PAD : Float := 1.85
/-- A label box: `dpanel`'s own character width and the gap it is anchored back from its lane. -/
def LCW : Float := 0.2039 / 0.8
def LDX : Float := 0.12
/-- The half-steps a block of legs is slid by until it fits between the arms' own neighbours. -/
def SLIDE : Array Float := Id.run do
  let mut out := #[0.0]
  for i in [0:12] do
    out := out.push (0.5 * DX * ((i / 2 + 1).toFloat) * (if i % 2 == 1 then -1.0 else 1.0))
  return out

/-- Python's `round(x, n)`: half to EVEN, so a column landing exactly on a half unit rounds the
    same way in both generators and the two pictures stay one picture. -/
def roundTo (n : Nat) (x : Float) : Float :=
  let m := (10.0 : Float) ^ n.toFloat
  let y := x * m
  let f := y.floor
  let d := y - f
  let r := if d > 0.5 then f + 1.0 else if d < 0.5 then f
           else if (f / 2.0).floor * 2.0 == f then f else f + 1.0
  r / m

/-- `%g`: six significant digits, no trailing zeros — the spelling `scripts/diagram` emits. -/
def num (x : Float) : String :=
  let x := roundTo 4 x
  let neg := x < 0.0
  let a := if neg then -x else x
  let scaled := (a * 10000.0 + 0.5).floor
  let ip := (scaled / 10000.0).floor
  let fp := scaled - ip * 10000.0
  let digits := (toString (fp.toUInt64.toNat + 10000)).drop 1
  let digits := digits.dropEndWhile (· == '0')
  let s := toString ip.toUInt64.toNat ++ (if digits.isEmpty then "" else "." ++ digits)
  if neg then "-" ++ s else s

/-! ### The panel model -/

/-- Still live: a lane no bead below has eaten, so it reaches whatever bottom edge it ends up under.
    A picture is built before its depth is known, so the bottom edge cannot be a row index yet. -/
private def LIVE : Int := -2

/-- One wire, from the bead that makes it to the bead that eats it.  `born = -1` is the top edge,
    `dies = rows.size` the bottom one.  `wire` is what the lane IS, so two edges are compared as
    relators (`Wire.beq`) rather than as the strings they happen to print as. -/
structure Lane where
  label : String
  born  : Int
  dies  : Int
  wire  : Wire
  x     : Float := 0.0
  pad   : Float := 0.0
  deriving Inhabited

/-- One horizontal cut: the lanes it crosses, outermost first, and the object underneath. -/
structure Cut where
  ws : Array Wire
  o  : Expr
  deriving Inhabited

/-- A CUT: the lanes, outermost first, then the object, `|`-separated — `F|a`.  Not `F(a)`: a lane
    may be `×` or `⟨𝟙,T⟩`, which no application spelling reads back, and `scripts/scanline` folds
    this list with the very `fold_cut` it reads the drawn cut with. -/
def cutText (c : Cut) : MetaM String := do
  let ls ← c.ws.mapM Wire.label
  return String.intercalate "|" (ls.push (← label c.o)).toList

/-- WHAT THE ENVIRONMENT PROVED ABOUT A BEAD, as a type and not a string.  The emitter matches on
    these five, so a verdict added here is a compile error until the mark it draws is decided —
    where a default branch silently drew the new one as an old one (`oplax` as `lax`).

    `maps` is the square proved for every MAP `f` and nothing proved at a relation.  It is a
    WEAKER claim than `strict`, which a filled dot would state of every arrow of the region, so it
    gets ink of its own; where the region is a CATEGORY every arrow is a map and the two coincide,
    and there the verdict is `strict`. -/
inductive Mark where
  | strict | lax | oplax | maps | spider
  deriving Inhabited, DecidableEq

/-- The word the drawing side reads the mark by.  One spelling, here: the panel's `nat:` row cites
    the same word the bead's 6th element carries. -/
def Mark.key : Mark → String
  | .strict => "strict" | .lax => "lax" | .oplax => "oplax" | .maps => "maps"
  | .spider => "spider"

/-- One bead: what it eats, what it makes, what the object wire carries below it, and whether a
    declaration says it is natural. -/
structure Row where
  /-- The bead's label, shape and all: a division stays a fraction inside any composite. -/
  shape : Lbl
  /-- THE BEAD'S OWN TERM (`beadKey`), which is what says two beads are ONE 2-CELL — the label is
      a rendering and a rendering is the printing rules' business, not the picture's identity. -/
  key   : String
  arms  : Array Nat
  legs  : Array Nat
  obj   : String
  /-- The cut the bead is drawn between: the lanes it TOUCHES, over the object wire.  Never a cut
      assembled from a sibling bundle — `scripts/scanline` narrows the drawn cut to the touched
      lanes too, so the two are the same list read from the two sides. -/
  src   : Cut
  tgt   : Cut
  nat   : Option Mark := none
  /-- The declarations the verdict was assembled from — the panel's own citation for its dots, and
      for a bead the environment REFUTES, which draws no dot and is a claim all the same.  More
      than one where the claim is a proved EQUIVALENCE away from what was found (Theorem 5.2), so
      the reader auditing the dot sees every step it rests on and not only the last. -/
  natLean : Array Name := #[]
  /-- THE BINDER THE VERDICT WAS READ OFF, where no declaration proves it: the drawn statement
      ASSUMES the square, so the panel's citation is the panel's own declaration and this name. -/
  natHyp : Option Name := none
  /-- IS THE BEAD A FAMILY IN AN OBJECT AT ALL?  One that is not is an arrow at this one object and
      has no naturality to be asked about; one that IS, carrying neither mark nor citation, is a
      family whose ends no lane of the region spells — and the trace says which, rather than
      leaving the bead out of it. -/
  family : Bool := false
  /-- A MAP (`isMapOf`): the bead a display lines up on next after a natural one — `Row.pin`. -/
  map   : Bool := false
  /-- The lanes the bead STANDS OVER: the object it is a family at, `F A` for `𝟙%∋` taken there.
      They run past it inside, and a bead with no arms opens its leg WEST of them. -/
  over  : Array Nat := #[]
  /-- A UNIT: a family `𝟙 ⟹ W` — no arms, one leg, the same object under both.  Drawn as the
      note's unit lane, born half a row below the row it stands on with its own mark, not a bead. -/
  unit  : Bool := false
  deriving Inhabited

/-- The flat spelling, for widths, messages and traces — never for what the panel sets. -/
def Row.label (r : Row) : String := r.shape.flat

/-- A PICTURE, with an open top and bottom edge — the value `⟦f⟧` is, so that `⟦f≫g⟧ = ⟦f⟧⋆⟦g⟧` and
    `⟦φ×ψ⟧ = ×▹(⟦φ⟧∥⟦ψ⟧)` are composites of pictures and not a second walk over the term. -/
structure Diagram where
  lanes : Array Lane
  rows  : Array Row
  /-- The lane indices AT each edge, west→east.  INVARIANT, and what the port lists and `columns`
      read as their west→east order: `top` is the lane array's own prefix `0,…,top.size-1`, every
      lane a row makes coming after every lane born at the top. -/
  top   : Array Nat
  bot   : Array Nat
  /-- The object each edge stands over — the object wire's label there. -/
  otop  : Expr
  obot  : Expr
  deriving Inhabited

/-! ### `columns` — how far apart the lanes sit -/

def minA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b < a then b else a) dflt
def maxA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b > a then b else a) dflt

/-- A column per lane.  The top-born lanes take the grid; a bead's legs are a contiguous `DX` block
    CENTRED on the arms it replaces, slid by half steps until it fits between the arms' own
    neighbours, so a lane west of the arms stays west of the legs. -/
def columns (p : Diagram) : Array Lane := Id.run do
  let n := p.rows.size
  let mut xs : Array (Option Float) := p.lanes.map (fun _ => none)
  let mut k := 0
  for i in [0 : p.lanes.size] do
    if p.lanes[i]!.born < 0 then
      xs := xs.set! i (some (k.toFloat * DX)); k := k + 1
  for i in [0 : n] do
    let r := p.rows[i]!
    if r.legs.isEmpty then continue
    let live := (List.range p.lanes.size).filter fun j =>
      (xs[j]!).isSome && p.lanes[j]!.born < (i : Int) && (i : Int) < p.lanes[j]!.dies
    let arms := r.arms.filterMap (fun a => xs[a]!)
    -- A bead with no arms of its own opens its wire east of every lane already live: born west, it
    -- would cross each of them on the way out.  Unless it STANDS OVER lanes — then it is outside
    -- them, and its leg opens one column west of the outermost, where `𝟙%∋` at `F A` puts `E`.
    let over := r.over.filterMap (fun j => xs[j]!)
    let c := if arms.isEmpty then
        if over.isEmpty then (maxA (Array.mk (live.map (fun j => (xs[j]!).get!))) (-DX)) + DX
        else minA over 1e9 - DX
      else (minA arms 1e9 + maxA arms (-1e9)) / 2.0
    -- A bead that gives back as many wires as it takes moves nothing sideways, so its legs KEEP the
    -- arms' columns and a swap is two straight lines crossing, not a staircase of knees.
    if !arms.isEmpty && r.legs.size == r.arms.size && arms.size == r.arms.size then
      let sorted := arms.qsort (· < ·)
      for j in [0 : r.legs.size] do xs := xs.set! r.legs[j]! (some sorted[j]!)
      continue
    let oth := live.filter fun j => !r.arms.contains j
    let othx := Array.mk (oth.map (fun j => (xs[j]!).get!))
    -- THE BAND THE LEGS TAKE MUST HOLD NO OTHER LIVE LANE — asked of each candidate, not of `c`:
    -- a lane exactly AT `c` is neither west of it nor east of it, so a test that brackets `c` reads
    -- the column as free and lays the new wire straight down the old one.
    let mut got : Array Float := #[]
    for d in SLIDE do
      got := Array.mk ((List.range r.legs.size).map fun j =>
        c + d + (j.toFloat - (r.legs.size.toFloat - 1.0) / 2.0) * DX)
      if othx.all fun x => x < got[0]! - 1e-6 || got[got.size - 1]! + 1e-6 < x then break
    for j in [0 : r.legs.size] do xs := xs.set! r.legs[j]! (some got[j]!)
  -- A lane OPENED at the bead that eats it has no row of legs to space it: it takes the free column
  -- beside the neighbour creation order already puts it next to.
  for i in [0 : p.lanes.size] do
    if (xs[i]!).isNone then
      let nxt := (List.range' (i + 1) (p.lanes.size - i - 1)).findSome? (fun j => xs[j]!)
      let prv := ((List.range i).reverse).findSome? (fun j => xs[j]!)
      xs := xs.set! i (some (match nxt, prv with
        | some v, _ => v - DX | none, some v => v + DX | none, none => 0.0))
  let mut ls : Array Lane := p.lanes.mapIdx fun i l => { l with x := (xs[i]!).get! }
  -- A lane's own NAME is written west of it, and a strand through that box is a collision.  One
  -- column holds two characters; a wider name moves every lane west of it west by the deficit,
  -- leaving the relative order — and the dots computed from it — untouched.
  for _ in [0 : ls.size] do
    let mut moved := false
    for i in [0 : ls.size] do
      if moved then continue
      let l := ls[i]!
      if l.label.isEmpty then continue
      let w := LDX + LCW * l.label.length.toFloat + 0.002 + l.pad
      let west := ls.filter fun o =>
        o.x < l.x - 1e-6 && o.born < l.dies && l.born < o.dies
      if west.isEmpty then continue
      let mx := maxA (west.map (·.x)) (-1e9)
      if l.x - mx >= w - 1e-6 then continue
      let d := w - (l.x - mx)
      ls := ls.map fun o => if o.x < l.x - 1e-6 then { o with x := o.x - d } else o
      moved := true
    if !moved then break
  -- The leftmost lane's own name is written into the margin, so the margin holds the wider of a
  -- column and that name.
  if ls.isEmpty then return ls
  let lo := ls.foldl (fun a b => if b.x < a.x then b else a) ls[0]!
  let gap := if lo.label.length > 1 then
      max DX (LDX + LCW * lo.label.length.toFloat + 0.002 + lo.pad) else DX
  let off := X0 + gap - minA (ls.map (·.x)) 0.0
  return ls.map fun l => { l with x := roundTo 3 (l.x + off) }

/-! ### `place` — one panel of the many the book calls equal -/

/-- One panel's OWN frame, in rows: as deep as its beads, plus the row of headroom the first bead
    sits below.  A statement's frame is the deepest of its parts' — see `emitStatement`. -/
def framex (p : Diagram) : Nat := max p.rows.size 1 + 1

/-- THE BOX A PANEL IS DRAWN IN: the depth the caller asks for, but never shallower than the
    picture.  HEADROOM ONLY is `emitStatement`'s rule for a statement's parts, and it is the panel's
    for the same reason — a box shallower than `framex` puts the last bead ON the floor, where its
    legs have no row to run in, and the sweep then reads the object wire as one of the wires that
    bead joins.  A note asking for a box the picture does not fit in gets the picture, and the
    difference is reported by the gate, not drawn. -/
def frameRows (p : Diagram) (frame : Option Nat) : Nat := max (frame.getD 0) (framex p)

/-- The frame's height in cetz units.  The panel and the gate in `emitStatement` both read THIS,
    so the gate measures the box that is drawn and not a second copy of the rule. -/
def frameHeight (p : Diagram) (frame : Option Nat) : Float := (frameRows p frame).toFloat * DY

/-- WHICH LANES THE DRAWING ALREADY HOLDS.  A lane reaching an edge is held by the panel's own
    ports, and one touching a bead that RIDES the object wire (`nat := none`, whose dot is drawn at
    `xat(y)`) is held by that wire; a bead passes its hold to every lane it eats and every lane it
    makes.  This is what `scanline`'s `pieces` asks of the ink, asked here of the lane table
    instead — the two placements of an armless bead are the SAME diagram (isotopy, IntroString
    (1.16)), so the one the exporter writes is decided by which of them is ONE DRAWING. -/
def heldLanes (p : Diagram) : Array Bool :=
  let n := p.rows.size
  let step : Array Bool → Array Bool := fun h => p.rows.foldl (fun h r =>
    let ws := r.arms ++ r.legs
    if !ws.isEmpty && (r.nat.isNone || ws.any fun j => h[j]!) then ws.foldl (·.set! · true) h
    else h) h
  (List.range (p.lanes.size + 1)).foldl (fun h _ => step h)
    -- `LIVE` is the sentinel a lane still alive at the bottom carries, and it is NEGATIVE: a lane
    -- reaches the bottom edge either by outliving every row or by never having been given a death.
    (p.lanes.map fun l => l.born < 0 || l.dies < 0 || l.dies >= (n : Int))

/-- The clear space between two port labels on one edge: one character, a word space. -/
def EGAP : Float := LCW

/-- AN EDGE'S PORT LABELS ARE ONE ROW OF TEXT.  Each is centred on its wire, so two wires closer
    than half their two labels' widths set the labels into each other — `G` under the `(` of
    `(e,w)`.  `edge` is the lanes reaching that edge west→east, the object wire (`xo`, labelled
    `ol`) east of them all; every wire east of a tight pair moves east by the deficit, so the order,
    and the lane names written west of each lane, are untouched. -/
def spreadEdge (ls : Array Lane) (xo : Float) (edge : Array Nat) (ol : String) :
    Array Lane × Float := Id.run do
  let mut (ls, xo) := (ls, xo)
  for i in [0 : edge.size] do
    let a := ls[edge[i]!]!
    let (bx, bl) := match edge[i + 1]? with
      | some j => (ls[j]!.x, ls[j]!.label)
      | none => (xo, ol)
    if a.label.isEmpty || bl.isEmpty then continue
    let d := LCW * (a.label.length + bl.length).toFloat / 2.0 + EGAP - (bx - a.x)
    if d > 1e-6 then
      ls := ls.map fun o => if o.x > a.x + 1e-6 then { o with x := roundTo 3 (o.x + d) } else o
      xo := roundTo 2 (xo + d)
  return (ls, xo)

/-- The `dpanel(...)` call this panel is.  `frame` and `top` are ROW COUNTS, the two halves of
    lining a short panel up with a tall one: the frame gives them one box, the top one bead
    height.  Left off, the frame is one row deeper than the panel and the first bead sits at the
    top of it. -/
def panelCode (p : Diagram) (frame topRow : Option Nat) : MetaM String := do
  let n := p.rows.size
  let ls := columns p
  let hh := frameHeight p frame
  let t0n := topRow.getD n
  let t0 := t0n.toFloat
  let ys : Array Float := Array.mk ((List.range n).map fun i => (t0 - i.toFloat) * DY)
  -- WITH NO LANE THERE IS NOTHING TO STAND EAST OF, so the object wire IS the first column.  The
  -- default `X0` is where a lane would have been, and adding `DX` to it puts the wire one column
  -- east of a column nobody drew (`11.4.1a`, `11.4.2a`).
  let xo := roundTo 2 (if ls.isEmpty then X0 else maxA (ls.map (·.x)) X0 + DX)
  let edge (f : Lane → Bool) : Array Nat :=
    ((List.range ls.size).filter fun i => f ls[i]!).toArray.qsort fun i j => ls[i]!.x < ls[j]!.x
  let (ls, xo) := spreadEdge ls xo (edge (·.born < 0)) (← label p.otop)
  let (ls, xo) := spreadEdge ls xo (edge (·.dies >= (n : Int))) (← label p.obot)
  -- A label is set from its TREE (`Lbl.typst`), so a division is the fraction the note draws
  -- wherever it stands — the unit `𝟙%∋`, and one nested in a composite (`[R%∋,S%∋]`) alike.
  let cell (l : Lbl) : String := l.bare.typst
  let key (m : Mark) : String := ", \"" ++ m.key ++ "\""
  let held := heldLanes p
  let mut beads : Array String := #[]
  let mut objs : Array String := #[]
  for i in [0 : n] do
    let r := p.rows[i]!
    -- THE BAR SPANS THE ARMS, THE DOT SITS ON WHAT THE BEAD TOUCHES.  A bead with NO arms stands on
    -- the object wire and its legs bend OUT of it, so it writes no reach — a bar taken from the legs
    -- would be drawn on the very wires it creates.  Its DOT sits among those legs — the book's
    -- floating unit, whose object wire runs past unbroken — ONLY where the drawing holds them
    -- already (`held`); a leg born at a floating dot and dying inside the panel is a piece of ink
    -- joined to nothing, and the same bead riding the object wire is the same diagram drawn whole.
    let xsr := r.arms.map fun j => ls[j]!.x
    let xsl := r.legs.map fun j => ls[j]!.x
    let xsd := if xsr.isEmpty then (if r.legs.any fun j => held[j]! then xsl else #[]) else xsr
    let reach : Option Float := if xsr.isEmpty then none else some (minA xsr 1e9)
    let dot : Option Float :=
      if xsd.isEmpty || r.nat.isNone then none
      else some (roundTo 4 ((minA xsd 1e9 + maxA xsd (-1e9)) / 2.0))
    -- The 6th element is the MARK, written by name for every verdict but the two that ARE the
    -- default drawing: a strict bead is the filled dot and a refuted one (`nat := none`) no dot at
    -- all.  One arm per constructor and no default, so `oplax` cannot be drawn as `lax` again.
    let mark := match r.nat with
      | none | some .strict => ""
      | some .lax => key .lax | some .oplax => key .oplax | some .maps => key .maps
      | some .spider => key .spider
    -- A UNIT is no bead: it is its leg's own birth, half a row below its row, written on the lane.
    if r.unit then
      objs := objs.push ("(" ++ num (ys[i]! - DY / 2.0) ++ ", " ++ cell r.obj ++ ")")
    else
      -- A DOT ON THE OBJECT WIRE STILL CARRIES ITS MARK: the fourth and fifth fields are the bar
      -- and the dot's own column, both absent here, and the sixth is the verdict — which a bead
      -- riding the object wire has exactly as much as one standing in its own column.
      beads := beads.push <| match reach, dot with
        | none, none =>
          if mark.isEmpty then "(" ++ num ys[i]! ++ ", " ++ cell r.shape ++ ")"
          else "(" ++ num ys[i]! ++ ", " ++ cell r.shape ++ ", black, none, none" ++ mark ++ ")"
        | none, some d =>
          "(" ++ num ys[i]! ++ ", " ++ cell r.shape ++ ", black, none, " ++ num d ++ mark ++ ")"
        | some rc, none => "(" ++ num ys[i]! ++ ", " ++ cell r.shape ++ ", black, " ++ num rc ++ ")"
        | some rc, some d =>
          "(" ++ num ys[i]! ++ ", " ++ cell r.shape ++ ", black, " ++ num rc ++ ", " ++ num d
            ++ mark ++ ")"
      objs := objs.push ("(" ++ num ys[i]! ++ ", " ++ cell r.obj ++ ")")
  let lanecode : Lane → String := fun l =>
    -- A lane born at a UNIT carries the unit as its own birth: half a row below the unit's row, the
    -- unit's label as the 5th element and its verdict as the 6th — `dlane` draws the mark there.
    let un : Option Row := if l.born < 0 then none else
      let r := p.rows[l.born.toNat]!
      if r.unit then some r else none
    let birth := if l.born < 0 then "\"top\""
      else if un.isSome then num (ys[l.born.toNat]! - DY / 2.0) else num ys[l.born.toNat]!
    let death := if l.dies >= (n : Int) then "\"bot\"" else num ys[l.dies.toNat]!
    let nm := if l.born < 0 || l.dies >= (n : Int) then "none" else cell l.label
    let tail := match un with
      | none => "none"
      | some r => cell r.shape ++ match r.nat with
        | some .strict => ""
        | some m => key m
        -- A refuted unit draws no mark, as a refuted bead draws no dot; the `nat:` row says which.
        | none => key .spider
    "(" ++ num l.x ++ ", " ++ birth ++ ", " ++ death ++ ", " ++ nm ++ ", " ++ tail ++ ")"
  -- THE LANE LIST IS `scripts/diagram`'s `made`: a bead's legs are written where the arms they
  -- replace stood, not at the end.  `dnamed` reads that order to decide which segment of a chain of
  -- same-named lanes carries the mid-run name, so the lane array's own BIRTH order puts the name on
  -- a different segment and the two panels draw different ink for the same picture.
  let made : Array Nat ← do
    let mut m := p.top
    for r in p.rows do
      if r.legs.isEmpty then continue
      let k := match r.arms[0]? <|> r.over[0]? with
        | some a => (m.findIdx? (· == a)).getD m.size
        | none => m.size
      m := m.extract 0 k ++ r.legs ++ m.extract k m.size
    unless m.size == ls.size do
      throwError "the lane order is built from the top cut and each bead's legs, and that reached \
        {m.size} of {ls.size} lanes: a lane no bead makes and the top cut has not got"
    pure m
  let tup (xs : Array String) : String :=
    "(" ++ String.intercalate ", " xs.toList ++ (if xs.size == 1 then "," else "") ++ ")"
  let top := (ls.filter (·.born < 0)).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell (← label p.otop) ++ ")")
  let bot := (ls.filter (·.dies >= (n : Int))).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell (← label p.obot) ++ ")")
  return "dpanel(" ++ num hh ++ ", " ++ num (roundTo 2 (xo + PAD)) ++ ", " ++ num xo ++ ",\n  "
    ++ tup (made.map fun i => lanecode ls[i]!) ++ ",\n  " ++ tup beads ++ ",\n  " ++ tup top
    ++ ",\n  " ++ tup bot
    -- NO CERTIFICATE: the panel is the declaration's own drawing, so a copy of the statement,
    -- the bead types and the verdicts beside it is a second source of truth for a gate to read.
    ++ ",\n  obj: " ++ tup objs ++ ")"

/-- The `lean:<Module>.<decl>@<key>` marker of each declaration a verdict leaned on, in ONE index
    query: the key is `decl_info.stmt_key`'s low half, `Freyd.Cite.keyHex`, the very number
    `scripts/cite-check` recomputes — so a statement that moves invalidates a panel's trace the
    same way it invalidates a note's citation.
    A NAME THE INDEX DOES NOT HOLD IS AN ERROR, never a blank citation: every name here came from
    the index's own candidate list, so a miss says the index is behind the environment the dot was
    read in, and a trace citing nothing would hide exactly that. -/
def natKeys (ns : Array Name) : MetaM (Std.HashMap Name String) := do
  let want := ns.toList.eraseDups
  if want.isEmpty then return {}
  let lits := want.map fun n => Freyd.Cite.sqlLit (toString n)
  let rows ← indexRows ("select i.user_name, i.module, i.stmt_key from decl_info i where \
    i.internal = 0 and i.user_name in (" ++ String.intercalate ", " lits ++ ")")
  let mut m : Std.HashMap Name String := {}
  for row in rows do
    let u ← cell row "user_name"
    let md ← cell row "module"
    let k := (← Freyd.Cite.numCell row "stmt_key").getD 0
    m := m.insert u.toName
      ("lean:" ++ md ++ "." ++ Freyd.Cite.lastComp u ++ "@" ++ Freyd.Cite.keyHex k)
  for n in want do
    unless m.contains n do
      throwError "the naturality search leaned on `{n}`, which `.lake/build/refactor-index.db` has \
        no row for: the index is behind the environment this panel was drawn in — run \
        `./scripts/lean-refactor index`"
  return m

/-- THE TRACE: one `nat:` comment per bead or unit the environment answered about, naming the mark
    drawn and every declaration the proof term leaned on.  A dot nobody can audit is a claim
    without a citation, and the panel IS the declaration's own drawing, so the citation belongs in
    the file the exporter writes — a comment, so the `dpanel` call and the note are unchanged by it
    (the note carries `#lean("<selector>")` and nothing else).

    ONE LINE PER BEAD DRAWN, and the word is the verdict: a mark, `none` for a refuted family, or
    `arrow` for a bead that is no family — an arrow of the base category at this one object, which
    is not the spider's "looked and found nothing" either. -/
def natLines (decl : Name) (ps : Array Diagram) : MetaM String := do
  -- THE OBLIGATION IS THE BEAD THE PANEL DRAWS, NOT THE VERDICT RECORD.  Looping over the beads the
  -- environment happened to answer about cannot find the one it was never asked about, which is how
  -- `zip`, `cp` and `cons` came out with no row at all; deleting a record shortens no obligation
  -- here, because the obligations ARE the rows the picture is drawn from.
  let rows := ps.flatMap (·.rows)
  -- The panel's OWN declaration is cited too where a bead's verdict is one of its hypotheses.
  let keys ← natKeys (rows.flatMap (·.natLean)
    ++ (if rows.any (·.natHyp.isSome) then #[decl] else #[]))
  let mut out := ""
  for r in rows do
    -- A bead that is NO FAMILY is an arrow of the base category at this one object (`est(R)`, a
    -- fold): there is no naturality to state, and the row says that rather than leaving the bead
    -- out.  A refuted family cites the refutation and draws no dot; a family whose ends no lane
    -- spells is `unread` — nothing claimed, and the reader, not the environment, is why.
    let word : String := match r.nat with
      | none => if !r.natLean.isEmpty then "none" else if r.family then "unread" else "arrow"
      | some m => m.key
    -- EVERY MARK BUT THE SPIDER CITES: a mark is ink for a proof term the search assembled, so a
    -- verdict added without a citation stops the panel instead of drawing an uncheckable dot.  The
    -- spider cites nothing because it says the tool looked and found nothing, and `arrow` because
    -- there was nothing to look at.
    if r.nat.isSome && r.nat != some .spider && r.natLean.isEmpty && r.natHyp.isNone then
      throwError "the bead `{r.label}` draws the mark `{word}` and cites no declaration: a mark is \
        the ink of a proof term the search assembled, so every one but the spider names the \
        declaration it rests on (`Verdict.lean`)"
    -- `unread` is thrown HERE and not in the bead constructor: a throw there is caught by the term
    -- walk, which reads the factor another way and draws the panel coarser with exit 0.
    if word == "unread" then
      throwError "the bead `{r.label}` is a family whose ends no lane spells, so nothing was searched \
        and it would draw as a spider that never looked: extend `relatorOfObj` (`ExprReader.lean`) \
        to read the end it refused"
    -- The spider is fatal too: a family the environment neither proves nor refutes is a claim nobody
    -- checked, and a picture that exits 0 with one is how `cons` and `moves` went unproved for weeks.
    if word == "spider" then
      throwError "the bead `{r.label}` is a family and the environment proves neither its naturality \
        nor a refutation: state `StrictNatural`/`LaxNatural`/`OplaxNatural` or `¬ LaxNatural` at the \
        spelling the line `the naturality search for … found nothing: state …` printed — its \
        `dropped …: lacks …` and `tried …: no unification` lines name the declarations that were \
        about this family and were not taken — then regenerate"
    let cites := String.join (r.natLean.toList.map fun n => " " ++ keys[n]!)
      ++ (match r.natHyp with
          | some hn => " " ++ keys[decl]! ++ " hyp:" ++ toString hn
          | none => "")
    out := out ++ "// nat: " ++ r.label ++ " " ++ word ++ cites ++ "\n"
  return out

/-- The file `--string` writes: the panel library, the picture, and the `nat:` trace of every dot
    the picture draws.  The header naming how to regenerate it is `DiagExport`'s, written from the
    argv it was run with. -/
def fileHead (up : String) : String := s!"#import \"{up}dpanel.typ\": *\n\n"

/-- `fileHead`'s argument: the panel library's path up from the file, deeper for a panel of a chain
    (`DiagExport.outPath`). -/
def fileOf (body : String) (nat : String := "") : String :=
  fileHead "../" ++ body ++ nat

/-- HOW FAR A BEAD IS TIED TO THE LANES, and so how much of the picture lining up ON it lines up.
    A bead the environment calls natural stands among the FUNCTOR wires and its dot is a claim about
    them, so two parts pinned there have their lanes at one height; next a MAP, the note's own
    order — the lax bead first, then the function; a bead that eats lanes is tied to where they
    die; a bead with none of these rides the object wire, where the note's own `place` lets it sit
    at any height (IntroString (1.16): two such placements are the SAME diagram). -/
def Row.pin (r : Row) : Nat :=
  if r.nat.isSome then 3 else if r.map then 2 else if r.arms.isEmpty then 0 else 1

/-- How many rows LOWER than the reference part's a part's first bead sits, so that a bead the two
    SHARE stands at the one height — the alignment `diagram --pairs` holds a display to.  The
    landmark is the reference's most lane-bound shared bead (`Row.pin`), its highest where several
    are equally bound.  Taking the highest shared bead outright pinned `F(R)φ ⊑ φR` at `R`, which
    rides the object wire in both parts, and left `φ` — where the `F` lane dies — at two heights;
    the note pins `φ`, and `secure prefix = prefix secure` likewise pins the natural `prefix` over
    the plain arrow `secure`.  Beads are compared by their KEY (`beadKey`), as that gate compares
    them: a bead is the same bead when it is the same 2-cell, which is a question about the term and
    not about how the printing rules render it. -/
def shiftTo (ref p : Diagram) : Int := Id.run do
  -- `pin + 1`, so `0` is "no shared bead yet" and a strictly better pin is needed to move the
  -- landmark down: equal pins keep the reference's highest, which is where the old rule stood.
  let mut best : Nat := 0
  let mut sh : Int := 0
  for i in [0 : ref.rows.size] do
    for j in [0 : p.rows.size] do
      if ref.rows[i]!.key == p.rows[j]!.key && ref.rows[i]!.pin + 1 > best then
        best := ref.rows[i]!.pin + 1
        sh := (j : Int) - (i : Int)
  return sh


/-- WHERE A STATEMENT'S PARTS STAND, decided ONCE over every part of it the run draws — the two
    sides a relation symbol joins, asked for whole or one file at a time, or the branches of them
    the note pairs.  The reference is the deepest
    part; THE FLOOR, NOT THE CEILING: its last bead lands on row 1 and every other part keeps its
    `shiftTo` slide from there, so extra frame is headroom ABOVE the picture and moves no bead
    (hanging the reference one row under the top of the box instead made every bead of the display
    move whenever the box got deeper).  A side that took its own row put the `R` of `f°F(R)f ⊑ R`
    a row above the `R` across the symbol from it: the two files lined up on nothing. -/
structure Placement where
  parts  : Array (Diagram × Int)   -- each part with its slide below the reference's first bead
  frame  : Nat
  topRef : Nat

/-- The parts stand IN A ROW, so each slides to its NEIGHBOUR, outward from the reference: a pair
    is the old slide to the reference, and a chain `a ⊑ b = c` lines up every step on the bead its
    two sides share, where sliding all to the reference aligned only the beads the reference has.
    The reference's first bead sits as high as the part reaching deepest below it demands, and the
    frame adds the most-slid part's rows and one of headroom: the max of the parts' OWN frames
    would clamp a slide and put a shared bead at two heights. -/
def placement (ps : Array Diagram) : Placement := Id.run do
  let r := (List.range ps.size).foldl (fun a i => if ps[i]!.rows.size > ps[a]!.rows.size then i else a) 0
  let mut s : Array Int := Array.replicate ps.size 0
  for i in [r + 1 : ps.size] do s := s.set! i (s[i - 1]! + shiftTo ps[i - 1]! ps[i]!)
  for k in [0 : r] do
    let i := r - 1 - k
    s := s.set! i (s[i + 1]! + shiftTo ps[i + 1]! ps[i]!)
  let topRef := ((List.range ps.size).foldl (fun a i => max a ((ps[i]!.rows.size : Int) - s[i]!)) 1).toNat
  return { parts := ps.zip s, topRef, frame := max (topRef + (s.foldl max 0).toNat + 1) 2 }

/-- The row a part's first bead sits on; a part is found by its beads, and two parts with the same
    beads are drawn alike. -/
def Placement.top (pl : Placement) (p : Diagram) : Nat :=
  let sh := (pl.parts.find? fun (q, _) => q.rows.map (·.key) == p.rows.map (·.key)).map (·.2)
  max ((pl.topRef : Int) + sh.get!) 1 |>.toNat

/-- One panel on its own — one side of a statement, or one branch of a side.  `panels` is the file's
    panels in order, so a caller holding the note to ONE of them names it by index instead of
    re-splitting the picture.

    IT IS DRAWN IN THE BOX ITS PEERS SHARE AND ON THE ROW THAT BOX GIVES IT, NOT ITS OWN: the two
    sides of one equation are two files, and a side that took its own depth came out shorter than the
    side across the `=` from it, one that took its own row put the bead they share at two heights.
    Asked for alone it has no peers and the box and the row are its own. -/
def emit (decl : Name) (p : Diagram) (pl : Placement) : MetaM String := do
  -- THE OBLIGATION, not the record: the part drawn must be one the placement was taken over.  A
  -- part the peer list did not reach can start above the box or reach below its floor, and
  -- `frameRows` would then draw it taller than the parts beside it rather than clip it.
  let t := pl.top p
  unless t < pl.frame && p.rows.size ≤ t do
    throwError "a part {p.rows.size} beads deep sits on row {t} of a frame of {pl.frame} rows: the \
      placement is the DECLARATION's, so every part of it must be among the ones it was taken over"
  return fileOf ("#let panels = (" ++ (← panelCode p (some pl.frame) (some t))
    ++ ",)\n#let pic = panels.at(0)\n") (← natLines decl #[p])

/-- One file for a WHOLE STATEMENT: its parts side by side, the relation symbol between them, in one
    frame.  Two panels a relation symbol joins are one display, so the frame is the statement's and
    never the part's — the placement's deepest part sets it and every shorter one is lined up
    inside it. -/
def emitStatement (decl : Name) (declName : String) (parts : Array (String × Diagram))
    (pl : Placement) : MetaM String := do
  let mut cells : Array String := #[]
  let mut panels : Array String := #[]
  let mut hs : Array Float := #[]
  for (sym, p) in parts do
    if !sym.isEmpty then cells := cells.push ("text(15pt)[" ++ sym ++ "]")
    cells := cells.push ("panels.at(" ++ toString panels.size ++ ")")
    panels := panels.push (← panelCode p (some pl.frame) (some (pl.top p)))
    hs := hs.push (frameHeight p (some pl.frame))
  -- THE GATE.  A part drawn to its own depth would put the relation symbol between two boxes of
  -- different heights, which reads as two displays rather than one statement.
  for i in [1 : hs.size] do
    if hs[i]! != hs[0]! then
      throwError "{declName}: part 1 is drawn {num hs[0]!} tall and part {i + 1} is {num hs[i]!} \
        — a relation symbol joins them into ONE display, so every part takes the statement's frame \
        (the deepest part's row count, plus one)"
  return fileOf ("#let panels = (\n  "
    ++ String.intercalate ",\n  " panels.toList ++ ",)\n"
    ++ "#let pic = align(center, grid(columns: " ++ toString cells.size
    ++ ", align: horizon, column-gutter: 6pt,\n  "
    ++ String.intercalate ",\n  " cells.toList ++ "))\n") (← natLines decl (parts.map (·.2)))

/-! ### The functor: an arrow of the allegory as a panel

  A factor is read by its TYPE.  Strip the relators it runs under (`F.map R` is `R` with `F`'s wire
  running past), then its own source and target say which wires it eats and which it makes: the
  stack they share below the change is untouched, everything above it dies and is reborn. -/

/-- The two RELATORS of a family `φ`, read off `φ`'s OWN type: open its binder and read each end of
    the arrow underneath as a relator in that variable (`relatorOfObj`).  Built this way the
    proposition `StrictNatural F G φ` type-checks by construction — `φ a : G.obj a ⟶ F.obj a` holds
    because `G` and `F` ARE those two ends — where a stack of lane labels is a second spelling of
    the same thing that can disagree with it. -/
def relatorsOf (alg : LaneAlg) (cat : Array Name) (regionTy φ : Expr) : MetaM (Expr × Expr) :=
  Meta.lambdaBoundedTelescope φ 1 fun xs body => do
    let some v := xs[0]?
      | throwError "not a family: `{← Meta.ppExpr φ}` takes no object of {← Meta.ppExpr regionTy}"
    let (x, y) ← homEnds body
    let G ← instantiateMVars (← relatorOfObj alg cat regionTy v x)
    let F ← instantiateMVars (← relatorOfObj alg cat regionTy v y)
    -- A relator that still mentions the object, or holds a metavariable, is not a relator of the
    -- region: it would escape this telescope as a loose variable, and the reading FAILED.
    if G.containsFVar v.fvarId! || F.containsFVar v.fvarId! || G.hasExprMVar || F.hasExprMVar then
      throwError "the ends of `{← Meta.ppExpr body}` do not read as relators of \
        {← Meta.ppExpr regionTy}: one of them still varies with {← Meta.ppExpr v}"
    return (G, F)

/-- Whether this factor is a FAMILY in the region's object, and so a candidate 2-cell at all: it
    varies with that object, and both its ends are objects a RELATOR spells.  `α : F(T)⟶T` at an
    initial algebra's carrier does not vary — `T` is one object, not a parameter — and `⦇R⦈ : T⟶A`
    does not even stand over one, so both are 2-cells between CONSTANT 1-cells `𝟏 → 𝒜`, which is the
    object wire.  `αᴀ : F(⟨𝟙,T⟩(A))⟶T(A)` does, which is why the two come out different by
    construction.

    The two ends need not be the SAME object: `nil : 𝟏⟶[[x]]` is a family whose source is constant,
    and `Relator.const` spells that.  What rules a bead out is an end no relator spells at all —
    `α : F(A,TA) ⟶ TA` with `A` pinned in the base functor, `F Unit A` — because there is then no
    naturality to state, which is exactly what `relatorsOf` fails on.

    ABSTRACTABLE over the object, not merely MENTIONING it: `S° : b⟶F(b)` names `b` only through
    the type of the local `S : F(b)⟶b`, so `fun b => S°` is ill-typed and `S` is one arrow. -/
def familyVar (core : Expr) (objVars : Array Expr) : MetaM (Option Expr) :=
  objVars.findM? fun v => do
    unless core.containsFVar v.fvarId! do return false
    -- A TEST ON THE LANE LABELS here would refuse the whole product family `[v]×[[v]]⟶[[v]]` on
    -- account of a label, and is a second reading of the same thing, which is what let the two
    -- disagree.  TYPE-CORRECTNESS IS THE WHOLE TEST, and the READER is asked nowhere in it: folding
    -- a reading that failed into "no family at all" drew the bead as `arrow` with exit 0, which is
    -- the obligation deleted rather than answered (`[nil,cons]`, `snoc` at an inductive alphabet).
    try Meta.isTypeCorrect (← Meta.mkLambdaFVars #[v] core) catch _ => pure false

/-- THE FAMILY A BEAD IS, WHERE THE STATEMENT BINDS NO OBJECT TO ABSTRACT.  A bead stands at the
    object its own WIRE carries, and that object is a family's index whether or not the statement
    happens to quantify over it: `𝟙%∋` at an initial algebra's carrier `T` is the very singleton
    `singleton_laxNatural` is about, and reading the index off the binders alone left it a bead
    nothing was claimed about — the same reading `beadLabel` already takes off the bead's own ends.
    So the object is `kabstract`ed out of the term, and TYPE-CORRECTNESS is the filter, exactly as
    it is for a binder: abstracting the object out of `est(R)` strands `R : x⟶x` at the old one and
    the lambda does not type-check, so an arrow AT one object stays an arrow at one object. -/
def familyAtIndex? (regionTy core t : Expr) : MetaM (Option Expr) := do
  let ty ← Meta.inferType t
  -- An index is an OBJECT of the region or the TYPE one is read from, and the two differ only in
  -- what goes back in its place: `a` itself, or `a`'s one field — the same family read through the
  -- structure's constructor, which is what `familyOf` does for a binder.
  let mk? : Option (Expr → MetaM Expr) ←
    if ← (try Meta.isDefEq ty regionTy catch _ => pure false) then pure (some pure) else do
      let some ity ← regionIndexType? regionTy | pure none
      let some f ← regionField? regionTy | pure none
      if ← (try Meta.isDefEq ty ity catch _ => pure false) then pure (some (Meta.mkProjection · f))
      else pure none
  let some mk := mk? | return none
  let body ← Meta.kabstract core t
  unless body.hasLooseBVars do return none
  Meta.withLocalDeclD `a regionTy fun a => do
    let φ ← instantiateMVars (← Meta.mkLambdaFVars #[a] (body.instantiate1 (← mk a)))
    if ← (try Meta.isTypeCorrect φ catch _ => pure false) then return some φ else return none

/-- THE INDICES A BEAD ITSELF NAMES: the object and `Type` arguments of the constants its term is
    applied from, outermost first.  A bead's index is the argument its OWN declaration takes —
    `@moves n X` is a family in `X` however deep the object standing at `X` is, and reading the
    index off a binder INSIDE that object cut the lanes of `X` at the bead's row and reborn them
    under it.  Read off the spine and the constant's own argument types, never off a name. -/
partial def indexArgs (regionTy e : Expr) (out : Array Expr) : MetaM (Array Expr) := do
  let mut out := out
  let args := e.getAppArgs
  -- A BINDER IS A DECLARATION TOO.  §7.4's `moves`, `trans`, `zip` are families of the SETTING, so
  -- their head is an fvar of the drawn statement and not a constant; reading an index off the spine
  -- only where the head is a constant left every such bead to be indexed by the object its wire
  -- happened to carry — `fun a => moves (E a)`, a family nothing states anything about.
  if e.getAppFn.isConst || e.getAppFn.isFVar then
    -- LAST ARGUMENT FIRST: a declaration's earlier object arguments are the parameters its later
    -- ones are taken over — `@snocR L E` is a family in the alphabet `E`, `L` being fixed before it
    -- — so the innermost argument is the index the picture varies.
    for a in args.reverse do
      unless out.contains a || a.hasLooseBVars do
        let ty ← instantiateMVars (← Meta.inferType a)
        let isTy := match ty with | .sort (.succ _) => true | _ => false
        if isTy || (← (try Meta.isDefEq ty regionTy catch _ => pure false)) then out := out.push a
  -- ONLY THROUGH THE BEAD'S OWN ARROWS.  A compound bead is the arrows it is built from — `graph con`
  -- is `con`, `[nil,cons]` is its two arms — so their arguments are its indices too; a RELATOR or an
  -- algebra handed to it is the region's furniture, and digging an index out of one made `α` at an
  -- abstract carrier a family in a type its own ends never show.
  for a in args do
    if (← instantiateMVars (← Meta.inferType a)).isAppOf ``Cat.Hom then
      out ← indexArgs regionTy a out
  return out

/-- THE TYPES AN OBJECT IS BUILT FROM, nearest first: every `Type` reachable from it through the
    arguments of what it is applied from and one delta step at a time.  A bead's index need not be
    named by its term at all — `est(R Char)` runs over an `Op(Char)` wire, and it is a family in
    `Op Char`, at which `F Unit −` is a lane and `dPair Char` a constant one, where at the `Char`
    its term names the base functor varies and no end reads.  `fuel` bounds the walk, which is over
    whole types and would otherwise follow a carrier down to its constructors. -/
partial def indexTypes : Nat → List Expr → Array Expr → MetaM (Array Expr)
  | 0, _, out => return out
  | _, [], out => return out
  | fuel + 1, e :: es, out => do
    let ty ← instantiateMVars (← Meta.inferType e)
    let isTy := match ty with | .sort (.succ _) => true | _ => false
    let out := if isTy && !out.contains e then out.push e else out
    let next := e.getAppArgs.toList.filter (!·.hasLooseBVars)
    indexTypes fuel (es ++ next ++ (← Meta.unfoldDefinition? e).toList) out

/-- THE TWO ENDS OF A FAMILY, READ AS LANES, and in WHICH algebra — the REGION'S, not the bead's.
    §1.241's function category is a `Cat` and no allegory, so its lanes are functors and its
    naturality is the plain square; and one region carries BOTH kinds, since `E`, the existential
    image, is a FUNCTOR in an allegory and no relator (its `powerRelator` needs tabularity), so a
    family under it is read a second time in the functor algebra rather than being called a bead
    nothing can be said about.  Same reader both times.

    `none` is a reading that FAILED — an end no lane spells — so there is a naturality to state and
    no way to state it: that is `unread`, and neither a verdict nor the spider's "looked and found
    nothing".  It is also what says a statement BINDER is not the index this picture shows. -/
def readEnds (regionTy : Expr) (cat : Array Name) (φ : Expr) :
    MetaM (Option (LaneAlg × Expr × Expr)) := do
  let alg0 ← laneAlgOf regionTy
  let read : LaneAlg → MetaM (Option (LaneAlg × Expr × Expr)) := fun a =>
    (some <$> (do let (G, F) ← relatorsOf a cat regionTy φ; return (a, G, F))) <|> pure none
  match ← read alg0 with
  | some r => return some r
  | none => if alg0 == .relator then read .functor else return none

/-- How deep a chain of CLOSURE theorems a compound bead's verdict may be read through:
    `strictNatural_prod` over `strictNatural_recip` over the square `cons_natural` states — the
    three `𝟙 X × cons°` needs, and the deepest bead the note draws.  Bounded because the search is
    over the whole environment at every step, so each step multiplies the scan. -/
def FUEL : Nat := 3

/-- What ONE BEAD's verdict may cost.  The read itself runs with heartbeats off (`drawString`),
    because a budget shared with the drawing dies naming whatever ran last; the SEARCH is where the
    cost is unbounded — a goal nothing proves is scanned for over the whole environment, once per
    step of `discharge` — so it is bounded here, from its own start, and spending the bound is the
    spider `verdict` already draws where nothing is proved. -/
def SEARCH_HEARTBEATS : Nat := 200000000

/-- What the environment says about a bead: the mark it draws — `"strict"`, `"lax"`, `"spider"`
    where nothing is proved either way, or none where the family is REFUTED and the bead rides the
    object wire — and the declaration that says so, which a spider has none of. -/
structure Verdict where
  mark : Option Mark
  /-- Every declaration the proof term leaned on, in the order it was assembled: the square the
      search found, then the equivalence that carried it to the mark drawn.  Empty is "nothing was
      looked at", which is not the same as "nothing was found" (the spider). -/
  lean : Array Name
  /-- The binder of the drawn statement the verdict was read off instead — see `hypVerdict`. -/
  hyp : Option Name := none
  deriving Inhabited

/-- WAS THE BEAD SPOKEN ABOUT AT ALL — by a declaration or by the drawn statement's own binder?
    An index whose verdict cites neither is one nothing was found at, and the reader goes on to the
    next; the two kinds of citation answer the question equally. -/
def Verdict.cited (v : Verdict) : Bool := !v.lean.isEmpty || v.hyp.isSome

/-- The three naturality predicates, as the mark each one draws.  A hypothesis is admitted by its
    HEAD CONSTANT and then by `isDefEq` on the arguments, never by the binder's name. -/
def markOfNatPredicate : Name → Option Mark
  | ``Freyd.Alg.StrictNatural => some .strict
  | ``Freyd.Alg.LaxNatural => some .lax
  | ``Freyd.Alg.OpLaxNatural => some .oplax
  | _ => none

/-- THE DRAWN STATEMENT'S OWN BINDERS ARE EVIDENCE.  A family the SETTING assumes natural — §7.4's
    `moves`, `trans`, `zip`, `setify`, abstract arrows of which the book states lax naturality and
    Lean can prove none — is spoken about by no declaration, so the environment search comes back a
    spider while the panel is drawn from a statement that ASSUMES the very square.  The hypothesis
    is found at the bead's own relators (`isDefEq`), and the citation is then the panel declaration
    plus the binder, so `cite-check` re-verifies the statement the assumption lives in.
    The binder may state the class or the family's SQUARE at an arrow of the statement
    (`laxNatural_comp_slide`'s `hψ`), graded by the square's relation. -/
def hypVerdict (alg : LaneAlg) (regionTy F G φ : Expr) : MetaM (Option (Mark × Name)) := do
  -- A category has only the equation to grade a square by (`laneSquare`).
  let grades := match alg with
    | .relator => #[(Grade.strict, Mark.strict), (.lax, .lax), (.oplax, .oplax)]
    | .functor => #[(Grade.strict, Mark.strict)]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let .const h _ := ty.getAppFn then
      if let some m := markOfNatPredicate h then
        let some want ← observing? (Meta.mkAppM h #[F, G, φ]) | continue
        if ← Meta.isDefEq ty want then return some (m, ← d.fvarId.getUserName)
        continue
    -- THE SQUARE AT ONE ARROW IS EVIDENCE FOR THE PICTURE OF THAT ARROW: a statement assuming
    -- `G(R) φ_B ⊑ φ_A F(R)` for the `R` it draws assumes all the bead's naturality the picture
    -- uses, so the binder is matched against the family's square with its arrow left open.
    unless ← Meta.isProp ty do continue
    for (g, m) in grades do
      let sq ← laneSquare alg regionTy F G φ g
      let hit ← Meta.withNewMCtxDepth do
        let (_, _, body) ← Meta.forallMetaTelescope sq
        Meta.isDefEq ty body
      if hit then return some (m, ← d.fvarId.getUserName)
  return none

/-- The bead's verdict, from the ENVIRONMENT.  `StrictNatural F G φ` is a solid dot, `LaxNatural`
    a hollow one, a refuted `LaxNatural` the object wire — each of them a proof term the search
    ASSEMBLED and `Meta.check`ed, never a name whose statement merely unified.  Where none of the
    three is proved the bead is a SPIDER: no dot, no claim, and a `nat:` row saying the tool
    looked and found nothing (CLAUDE.md: "a transformation with no naturality proof draws as a
    spider"). -/
def verdict (regionTy : Expr) (cat : Array Name) (φ : Expr) : MetaM Verdict := do
  -- THE STATEMENT IS READ OFF THE FAMILY, NOT OFF THE LANES.  `φ = fun v => core`, so its two
  -- relators are its own end objects as functions of `v` (`relatorOfObj`) and the proposition
  -- type-checks by construction; a stack of lane labels is a second spelling of the same thing that
  -- can disagree with it, and did.
  -- AN END NO LANE SPELLS IS A READING THAT FAILED, AND A FAILED READING IS NO VERDICT: the bead IS
  -- a family, so there is a naturality to state and nothing was claimed about it.  The `nat:` row
  -- says `unread` — `zip`, `cp` and `cons` over the peeled product lane had no row at all, while
  -- their squares sat proved in the environment.  NOT an error: a factor the reader throws on is
  -- read ANOTHER way by the term walk, so a throw here redraws the panel coarser instead of
  -- stopping it (it cost `prefix ⊑ prefix`'s `cons` its dot and its peeled `list` wire).
  -- `alg0` is the REGION's algebra and `alg` the one its ends were read in: an allegory's functor
  -- lane (`E`) is read in the functor algebra while the region still has maps to restrict to.
  let alg0 ← laneAlgOf regionTy
  let some (alg, G, F) ← readEnds regionTy cat φ | return { mark := none, lean := #[] }
  -- THE FILTER IS THE FAMILY'S CONSTANTS, NOT THE TERM'S AT ITS OBJECT.  A bead taken at an initial
  -- algebra's carrier carries `InitialAlgebra.t` into `core`, and no naturality theorem mentions a
  -- projection of the region's own structure, so filtering on it dropped every candidate there is.
  -- `id` is what separates this `do` from the enclosing one, so a hit `return`s from the search
  -- and not from `verdict`.
  let br ← bridges
  let must ← mustOfFamily br φ
  -- The spider's message is what the next proving agent reads, so the scan records what it passed
  -- over as it goes: re-running the search to explain it would pay for it twice.  The state is this
  -- search's own — the exporter runs a task per panel in one process.
  let s ← Search.new (← familyHead br φ)
  -- A CATEGORY HAS ONE NATURALITY STATEMENT, THE SQUARE, and no `⊑` to grade it by: there is no
  -- lax, no oplax and no refutation to look for, so a family between functor lanes is the solid
  -- dot its square proves or the spider below — never the object-wire bead a failed RELATOR
  -- reading used to demote it to.
  let search : MetaM (Option Verdict) := match alg with
    | .functor => id do
      if let some (n, _) ← findTelescoped br s (← laneSquare alg regionTy F G φ) must s.head FUEL then
        return some { mark := some .strict, lean := #[n] }
      -- THE SQUARE OVER THE MAPS, where the region HAS maps to restrict to.  `𝟙%∋ : 𝟙 ⟹ E` is
      -- natural there and at no relation (`singletonMap_natural`, whose `Map f` this square binds
      -- and `discharge` reads back), and so is every other family of maps between functor lanes of
      -- an allegory; asking only the unrestricted square left all of them with no claim at all.
      -- AND IT IS NOT THE FILLED DOT.  In an ALLEGORY the maps are a sub-category of the arrows,
      -- so a square proved only over them says nothing at any relation, where the filled dot says
      -- it of every arrow — `∋` drew solid here while the same `∋` elsewhere drew hollow off
      -- `eps_laxNatural`.  `maps` is that weaker claim with ink of its own; a region that is a
      -- CATEGORY (`alg0 == .functor`) never reaches this line, and there the two coincide.
      if alg0 == .relator then
        if let some (n, _) ← findTelescoped br s (← laneSquare alg regionTy F G φ .strict true)
            must s.head FUEL then
          return some { mark := some .maps, lean := #[n] }
      return none
    | .relator => id do
      let strict ← Meta.mkAppM ``Freyd.Alg.StrictNatural #[F, G, φ]
      let lax ← Meta.mkAppM ``Freyd.Alg.LaxNatural #[F, G, φ]
      let oplax ← Meta.mkAppM ``Freyd.Alg.OpLaxNatural #[F, G, φ]
      -- The refutation is of the very statement just searched for, `¬ LaxNatural F G φ`, and not
      -- of one with the two relators swapped: `φ a : G.obj a ⟶ F.obj a`, so a swapped statement is
      -- not even well typed unless the bead happens to end where it starts.
      let nolax ← Meta.mkAppM ``Not #[lax]
      if let some (n, _) ← findProof br s strict ``Freyd.Alg.StrictNatural {} FUEL then
        return some { mark := some .strict, lean := #[n] }
      -- THE SQUARE IS BUILT, NOT REACHED BY UNFOLDING THE CLASS, for the reason `laneSquare` gives:
      -- `LaxNatural F G φ` spells the lane stack's action as the COMPOSITE relator's `map`, and
      -- every hand-written square in the repo spells it wire by wire (`tupleP 3 (tupleP n S)`), so
      -- the unfolded class matched none of them and every `RelSet.graph` bead of the cylinder came
      -- back a spider.  Same builder as the functor algebra's, one grade apart.
      if let some (n, _) ← findTelescoped br s (← laneSquare alg regionTy F G φ) must s.head FUEL then
        return some { mark := some .strict, lean := #[n] }
      if let some (n, _) ← findProof br s lax ``Freyd.Alg.LaxNatural {} FUEL then
        return some { mark := some .lax, lean := #[n] }
      if let some (n, _) ← findTelescoped br s (← laneSquare alg regionTy F G φ .lax) must s.head FUEL then
        return some { mark := some .lax, lean := #[n] }
      -- The CONVERSE of a lax family is not lax, it is lax the other way (`laxNatural_recip`), so
      -- `OplaxNatural` is asked before the refutation: `prefix°` is not a spider, it is a hollow dot
      -- whose square points the other way, and the `nat:` row is where the direction is written.
      -- The CLASS only, not the square: nothing in the repo states a raw oplax inequation, so
      -- unfolding it would scan every `⊑` in the environment for a shape only `laxNatural_recip`
      -- ever produces — and that closure's own hypothesis IS searched as a square, through
      -- `discharge`.  A whole extra sweep per bead is what the H panels' budget cannot pay.
      if let some (n, _) ← findProof br s oplax ``Freyd.Alg.OpLaxNatural {} FUEL then
        return some { mark := some .oplax, lean := #[n] }
      if let some (n, _) ← findProof br s nolax ``Not must FUEL then
        return some { mark := none, lean := #[n] }
      -- THEOREM 5.2 IS A BRIDGE, AND IT IS CROSSED WITH A TERM.  A family whose only square in the
      -- repo is the one over the MAPS was a spider here, and it is not: on a TABULAR allegory that
      -- square IS lax naturality (`laxNatural_iff_strict_on_maps`), so the honest mark is the
      -- hollow dot.  `.mpr` applied to the square's own proof is BUILT and `Meta.check`ed, so the
      -- equivalence's `TabularAllegory 𝒜` has to synthesise for this region and its two ends have
      -- to be the very relators the bead runs between; where either fails there is no term and the
      -- bead keeps `maps` — what was proved over the maps, and nothing claimed at a relation.
      -- BOTH NAMES ARE RECORDED: the dot rests on the square AND on the theorem that carried it.
      if let some (n, pf) ← findTelescoped br s (← laneSquare alg regionTy F G φ .strict true)
          must s.head FUEL then
        let carried ← observing? do
          let e ← Meta.mkAppM ``Freyd.Alg.laxNatural_iff_strict_on_maps #[F, G, φ]
          let t ← Meta.mkAppM ``Iff.mpr #[e, pf]
          Meta.check t
          pure t
        if carried.isSome then
          return some { mark := some .lax,
                        lean := #[n, ``Freyd.Alg.laxNatural_iff_strict_on_maps] }
        return some { mark := some .maps, lean := #[n] }
      return none
  -- A SEARCH THAT CANNOT FINISH IS A BEAD NOTHING PROVES, SAID OUT LOUD.  The bound is measured
  -- from the search's own start and the handler runs outside it, so the message is not itself cut
  -- short; the answer is the spider below, and the line names the family so a bead that lost its
  -- dot to a budget is not silent about it.
  let bounded : MetaM (Option Verdict) := Core.withCurrHeartbeats <| withTheReader Core.Context
    (fun c => { c with maxHeartbeats := SEARCH_HEARTBEATS }) search
  let found : Option Verdict ← tryCatchRuntimeEx bounded fun e => do
    IO.eprintln s!"diag-export: the naturality search for {← Meta.ppExpr φ} stopped on \
      `{← e.toMessageData.toString}`: the bead draws as a spider"
    return none
  if let some v := found then return v
  -- WHAT THE DRAWN STATEMENT ASSUMES IS STILL A CLAIM THE PANEL MAY DRAW, and it is asked only
  -- after the environment: a family something PROVES natural cites the proof, never the binder.
  if let some (m, n) ← hypVerdict alg regionTy F G φ then return { mark := some m, lean := #[], hyp := some n }
  -- NO VERDICT, NO DOT, NO CLAIM.  The three statements are what was looked for and none of them
  -- is proved, so the bead draws as the book's spider (IntroString §2.2.4) — a node with no mark —
  -- rather than the panel failing or, worse, a dot standing for a naturality nobody has.
  -- THE SPELLING IS PRINTED, not left for the reader to reconstruct: the statement to write is the
  -- one that was looked for, at the relators this bead actually runs between.
  -- AND WHAT IT PASSED OVER, so a theorem that IS about this family but was filtered out or failed
  -- to unify is named here rather than left for the next agent to rediscover.
  let passed ← s.passed.get
  IO.eprintln (s!"diag-export: the naturality search for {← Meta.ppExpr φ} found nothing: state \
    `LaxNatural ({← Meta.ppExpr F}) ({← Meta.ppExpr G}) ({← Meta.ppExpr φ})`, one of its two \
    siblings, or its refutation" ++ String.join (passed.toList.map ("\n  " ++ ·)))
  return { mark := some .spider, lean := #[] }

/-! ### The four constructors — nothing else builds a `Diagram` -/

/-- The bare wires `ws` over the object `o`: born at the top edge, dying at the bottom, no bead.
    `⟦𝟙⟧`, and the lanes a factor merely runs past. -/
def Diagram.id (ws : Array Wire) (o : Expr) : MetaM Diagram := do
  let lanes ← ws.mapM fun w => return { label := ← w.label, born := -1, dies := LIVE, wire := w }
  let ix := Array.mk (List.range lanes.size)
  return { lanes, rows := #[], top := ix, bot := ix, otop := o, obot := o }

/-- A BEAD'S LABEL IS THE FAMILY'S NAME, and the object it is taken at is the WIRE UNDER IT.  So
    every application to the region's own object variable comes off the label — `α A` is the bead
    `α` over the `A` wire — because writing the index into the label as well spells one object twice
    and lets the two drift (`skills/string-diagram`: "a bead's index is the object wire under it").
    A bead that is no family in the object has no index to drop.

    THE OBJECT IS WHATEVER THE WIRE UNDER THE BEAD CARRIES, not only a binder of the statement.
    `moves I.t` in an abstract module is taken at the initial type, which is no binder of the
    region, and the label came out `movesT` — the object wire's own `T` spelled a second time. So
    the objects stripped are the bead's own two ends as well as the family variable, compared up to
    `isDefEq` because the end comes back rebuilt from its projection. -/
def beadCore (core : Expr) (vs : Array Expr) : MetaM Expr :=
  Meta.transform core (post := fun x => match x with
    | .app f a =>
      if f.getAppFn.isFVar then
        return if ← vs.anyM (Meta.isDefEq a) then .done f else .continue
      else return .continue
    | _ => return .continue)

/-- A BEAD'S IDENTITY IS ITS TERM, NOT ITS RENDERING — the key two parts of one display are told
    the same 2-cell by (`shiftTo`, and the one-height obligation `drawString` holds a call to).
    Comparing the LABEL instead tied identity to the printing rules: a constant whose index the
    rules drop reads as one bead at both ends of its own naturality square, and the two beads that
    swap across it can then be at one height in neither panel.

    THE TERM, SPELLED WITH ITS INDEX — never the `Expr` itself.  One `#lean(…)` call draws panels
    of TWO DECLARATIONS side by side (`thinRel_comp_eps_le` beside its reciprocal), and the same
    object is a different free variable in each, so a structural key makes every bead of such a
    pair a bead of its own and the two panels line up on nothing.  What is stable across the pair
    is the note's own spelling of the family AT its index, which is what this is. -/
def beadKey (core : Expr) (vs : Array Expr) : MetaM String := do
  label (← beadCore core vs)

/-- A CONSTANT'S INDEX COMES OFF AT THE BEAD'S OWN HEAD, and ONLY WHERE THE BARE CONSTANT HAS A
    PRINTING RULE BESIDE ITSELF.  An unexpander matches the term as APPLIED, so cutting the object
    argument out from under it stops it firing and the label comes out worse than the one the strip
    was meant to fix — `prefixR A` became `@ListRel.prefixR`, `𝟙 (dSched X)` became `𝟙dSched`.  The
    guard is that failure itself and not a list of names: the stripped term is offered to the
    printer, and a term that comes back wearing its own CONSTANT'S NAME (`printsItsName`) is a rule
    that did not fire, so the index stays.  A constant that wants its index dropped drops it in its
    own rule, beside itself — `notation:max "⦇·⦈" => fold`. -/
private def bareIndex (e : Expr) (vs : Array Expr) : MetaM Expr := do
  let .app f a := e | return e
  unless f.getAppFn.isConst do return e
  unless ← vs.anyM (Meta.isDefEq a) do return e
  if ← printsItsName f then return e
  return f

def beadLabel (core : Expr) (vs : Array Expr) : MetaM Lbl := do
  labelT (← bareIndex (← beadCore core vs) vs)

/-- ONE bead: `arms` born at the top edge and eaten by it, `legs` made by it and live to the bottom.
    The VERDICT is searched HERE, off the bead's own family — the lanes it runs under and the lanes
    drawn past it are alike none of its naturality statement's business. -/
def Diagram.bead (regionTy : Expr) (cat : Array Name) (objVars : Array Expr)
    (arms legs : Array Wire) (ox oy core : Expr) (over : Array Wire := #[]) :
    MetaM Diagram := do
  let mut lanes : Array Lane := #[]
  for w in arms do lanes := lanes.push { label := ← w.label, born := -1, dies := 0, wire := w }
  -- The lanes the bead stands over are born at the top and live past it, inside its legs.
  for w in over do lanes := lanes.push { label := ← w.label, born := -1, dies := LIVE, wire := w }
  for w in legs do lanes := lanes.push { label := ← w.label, born := 0, dies := LIVE, wire := w }
  -- The two ends need NOT be the same object.  `nil : 𝟏⟶[[x]]` starts at a constant and ends at a
  -- family, and `Relator.const` is a relator like any other, so demanding `ox` and `oy` agree threw
  -- away a naturality the environment proves.
  -- THE INDEX IS THE ARGUMENT THE BEAD'S OWN DECLARATION TAKES — `@moves n X` is a family in `X`,
  -- and reading it off a binder inside `X` cut that object's lanes at the bead's row — then a
  -- binder of the statement, then the object its wire carries.  The READER only CHOOSES among the
  -- indices that abstract type-correctly and rules none of them out: a family whose ends no lane
  -- spells is `unread` (`natLines`), never the `arrow` that says there was nothing to look at.
  -- AN INDEX IS AN OBJECT OF THE REGION THE OBJECT WIRE RUNS IN, which is not always the region
  -- the ARROW lives in: `Δᴛ`, `U : Algebra F ⟶ 𝒜` stand over an ALGEBRA while the arrow they carry
  -- is one of `𝒜`, so asking for an index of `𝒜` found none and the fold drew as a plain arrow.
  -- The two regions coincide for endofunctor lanes, which is every lane before one crossed
  -- categories.  READ OFF THE WIRE, never off the statement: the wire is what the bead stands on.
  let idxTy ← Meta.inferType oy
  -- ASKED OF BOTH, THE ARROW'S REGION FIRST: an index of the region the arrow lives in is what
  -- every endofunctor lane's family is indexed by, and it keeps its answer; the wire's own region
  -- answers where the two differ, which is where the lanes CROSS categories.  Neither is a
  -- fallback for a failure — they are two places an index can live, and the ENVIRONMENT picks
  -- between the readings below by which one has a square.
  let famAt : Expr → MetaM (Option Expr) := fun t => do
    match ← familyAtIndex? regionTy core t with
    | some φ => return some φ
    | none => familyAtIndex? idxTy core t
  let mut cands : Array (Expr × Expr) := #[]
  for t in (← indexArgs idxTy core (← indexArgs regionTy core #[])) do
    if let some φ ← famAt t then cands := cands.push (t, φ)
  -- THE TYPE THE WIRE IS BUILT FROM is an index no term need name: `est(R Char)` over an `Op(Char)`
  -- wire is a family in `Op Char` and in nothing its own spine holds.
  let mut typs : Array (Expr × Expr) := #[]
  for t in ← indexTypes 64 [oy, ox] #[] do
    if let some φ ← famAt t then typs := typs.push (t, φ)
  -- The object the bead's own WIRE carries comes LAST, as the `familyAt?` it replaces did: it is the
  -- index of a bead whose term names none — `𝟙%∋` at an initial algebra's carrier — and reading it
  -- ahead of a binder the ends are lanes in took `nil`'s square off the board.
  let mut wire : Array (Expr × Expr) := #[]
  for t in #[oy, ox] do
    if let some φ ← famAt t then wire := wire.push (t, φ)
  -- A STATEMENT BINDER IS NOT THE BEAD'S OWN INDEX, so it is kept only where the ends ARE lanes in
  -- it: `α : F(T)⟶T` at an abstract carrier names the module's `A` through its algebra and nothing
  -- else, and abstracting one out of the other is type-correct without the picture showing any of
  -- it.  For an index the bead's term itself takes, the term is the whole evidence.
  let mut bound : Array (Expr × Expr) := #[]
  for v in objVars do
    if let some φ ← famAt v then
      if (← readEnds regionTy cat φ).isSome then bound := bound.push (v, φ)
  let all := cands ++ typs ++ bound ++ wire
  -- WHICH of them the dot is at is the ENVIRONMENT'S answer and not the reader's: `nil` is a family
  -- in its own alphabet AND in the object its wire carries, both of them read, and only one has a
  -- square — taking the first that merely READS drew a spider beside the theorem that proves it.
  -- The first readable index stands where none of them is spoken about, so the row is the spider.
  -- THE BEAD IS NAMED IN ITS OWN FAILURE: a verdict that cannot be reached is this bead's error,
  -- and a message holding only the family's term leaves the reader matching it back to a label.
  -- AN INDEX NOTHING NAMES NEEDS THE ENVIRONMENT TO CONFIRM IT.  The `Type` a wire is built from is
  -- the weakest evidence there is — every object is built from some type — so it is admitted only
  -- where a square is stated at it: a family nothing is proved about at an index no term names is
  -- the object-wire arrow `α` already is, and drawing it as a spider claims a search nobody asked.
  let mut pick : Option (Expr × Expr × Verdict) := none
  for i in [0 : all.size + typs.size] do
    if (pick.map fun p => p.2.2.cited).getD false then break
    let named := i < all.size
    let c := if named then all[i]! else typs[i - all.size]!
    unless (← readEnds regionTy cat c.2).isSome do continue
    let vd ← try verdict regionTy cat c.2 catch e =>
      throwError "the bead `{(← beadLabel core #[ox, oy, c.1]).flat}`: {← e.toMessageData.toString}"
    if named && pick.isNone then pick := some (c.1, c.2, vd)
    if vd.cited then pick := some (c.1, c.2, vd)
  let v? := pick.map (·.1)
  let φ := (pick.map (·.2.1)) <|> (all[0]?.map (·.2))
  let vd := pick.map (·.2.2)
  let ar := Array.mk (List.range arms.size)
  let ov := Array.mk (List.range' arms.size over.size)
  let lg := Array.mk (List.range' (arms.size + over.size) legs.size)
  -- A unit is a FAMILY `𝟙 ⟹ W` THE ENVIRONMENT PROVES: a fixed arrow `A ⟶ F A` (`S°`) is a bead
  -- with a leg, not a lane, and so is one whose family the environment neither proves nor can even
  -- state — heading a lane with it claims the transformation IS the unit, which is the dot the
  -- spider exists to withhold.  `∈ ≜ ∋°` is that bead: the same shape as the singleton `𝟙%∋`, and
  -- only the verdict tells them apart.
  -- `maps` IS a proved family — the square over every map of the region — so it heads a lane like
  -- the other three; what it withholds is the claim at a relation, which is the ink, not the shape.
  let proved := match vd.bind (·.mark) with
    | some .strict | some .lax | some .oplax | some .maps => true
    | some .spider | none => false
  let unit := arms.isEmpty && legs.size == 1 && proved && (← Meta.isDefEq ox oy)
  let row : Row :=
    { shape := (← beadLabel core (#[ox, oy] ++ v?.toArray)),
      key := (← beadKey core (#[ox, oy] ++ v?.toArray)), arms := ar, legs := lg, over := ov,
      unit, obj := (← label oy),
      src := { ws := arms, o := ox }, tgt := { ws := legs, o := oy },
      nat := vd.bind (·.mark), natLean := (vd.map (·.lean)).getD #[], natHyp := vd.bind (·.hyp),
      family := φ.isSome, map := ← isMapOf core }
  return { lanes, rows := #[row], top := ar ++ ov, bot := lg ++ ov, otop := ox, obot := oy }

/-- One lane index shifted from a part's frame into the whole's: a row index moves by the rows drawn
    above it, and the two edge sentinels — `-1` the top, `LIVE` the bottom — do not move. -/
private def shiftRow (n : Nat) (i : Int) : Int := if i < 0 then i else i + n

/-- `d` ABOVE `e`.  The two edges must be the SAME cut, and each lane of `e.top` then IS the lane of
    `d.bot` it continues — one wire, not two stacked — which is what makes `⟦f≫g⟧` a composite. -/
def Diagram.vcomp (d e : Diagram) : MetaM Diagram := do
  let edge (p : Diagram) (ix : Array Nat) (o : Expr) : MetaM String :=
    cutText { ws := ix.map fun i => p.lanes[i]!.wire, o }
  let mut ok := d.bot.size == e.top.size && (← Meta.isDefEq d.obot e.otop)
  if ok then
    for j in [0 : e.top.size] do
      unless ← Wire.beq d.lanes[d.bot[j]!]!.wire e.lanes[e.top[j]!]!.wire do ok := false
  unless ok do
    throwError "a composite is ONE picture, so the cut it is cut at has to be the same read from \
      either side, and here the upper part ends at `{← edge d d.bot d.obot}` while the lower one \
      starts at `{← edge e e.top e.otop}`\n  — the objects the two sides read are \
      {← Meta.ppExpr d.obot} and {← Meta.ppExpr e.otop}"
  let nr := d.rows.size
  let mt := e.top.size
  let emap : Nat → Nat := fun j => if j < mt then d.bot[j]! else d.lanes.size + j - mt
  let mut lanes := d.lanes
  for j in [0 : mt] do
    lanes := lanes.modify d.bot[j]! fun l => { l with dies := shiftRow nr e.lanes[j]!.dies }
  for j in [mt : e.lanes.size] do
    let l := e.lanes[j]!
    lanes := lanes.push { l with born := shiftRow nr l.born, dies := shiftRow nr l.dies }
  let rows := d.rows ++ e.rows.map fun r =>
    { r with arms := r.arms.map emap, legs := r.legs.map emap, over := r.over.map emap }
  return { lanes, rows, top := d.top, bot := e.bot.map emap, otop := d.otop, obot := e.obot }

/-- `d` WEST of `e`.  The object wire is the EASTMOST one, so `e` owns it and `d` only runs past it;
    a row of `d` therefore keeps its OWN ends and only picks up the object wire's new label. -/
def Diagram.beside (d e : Diagram) : MetaM Diagram := do
  let nt := d.top.size; let mt := e.top.size; let dn := d.lanes.size - nt; let nr := d.rows.size
  let dmap : Nat → Nat := fun i => if i < nt then i else i + mt
  let emap : Nat → Nat := fun j => if j < mt then nt + j else nt + dn + j
  let esh : Lane → Lane := fun l =>
    { l with born := shiftRow nr l.born, dies := shiftRow nr l.dies }
  let lanes := d.lanes.extract 0 nt ++ (e.lanes.extract 0 mt).map esh
    ++ d.lanes.extract nt d.lanes.size ++ (e.lanes.extract mt e.lanes.size).map esh
  let obj ← label e.otop
  let drows := d.rows.map fun r =>
    { r with arms := r.arms.map dmap, legs := r.legs.map dmap, over := r.over.map dmap, obj }
  let rows := drows ++ e.rows.map fun r =>
    { r with arms := r.arms.map emap, legs := r.legs.map emap, over := r.over.map emap }
  return { lanes, rows, top := Array.mk (List.range (nt + mt)),
           bot := d.bot.map dmap ++ e.bot.map emap, otop := e.otop, obot := e.obot }

/-- THE REGION'S NAMED OBJECTS CLOSED for `k` — a `def Ix : RelSet := ⟨Fin 65536⟩` is the OBJECT
    `Ix`, and inside `k` nothing can unfold it to its carrier.  The objects of a concrete region
    are the constants AT that type; a relator (`RelSet ⟶ RelSet`) is a `∀` with no constant head,
    so the machinery that spells the lanes stays open.  A constant the note draws OPENED keeps its
    `diag_unfold` meaning: `openNoted` opens it ABOVE the peel, where the note's own body is drawn. -/
def withObjectsClosed {α : Type} (regionTy : Expr) (k : MetaM α) : MetaM α := do
  let some h := regionTy.getAppFn.constName? | k
  let env ← getEnv
  let opened ← Lean.labelled `diag_unfold
  for (n, ci) in env.constants do
    if n.isInternal || ci.isUnsafe || opened.contains n then continue
    if ci.type.getAppFn.constName? == some h then Lean.setIrreducibleAttribute n
  try k finally setEnv env

/-- A CUT'S OBJECT IS READ BY THE HEAD CONSTANT IT IS WRITTEN WITH, and only an object no lane
    spells that way is unfolded.

    The peel matches by `isDefEq`, which unfolds, so an object has more than one reading and which
    one comes back is an accident of where the catalogue's sweep reached first: `E(Ix)` is
    `⟨Fin 65536 → Prop⟩` once `Ix` is open, which the index lane `[65536]` over `Prop` answers as
    readily as `E` over `Ix`.  The two sides of one cut hold different spellings of its object —
    `powerObj Ix` above, `E.obj Ix` below — so each picked its own answer and the composite came
    apart at a cut both sides agreed the TYPE of.  Reading with the objects closed leaves exactly
    the lanes the object is written with, which is the same list from either side.

    The closure is on the READ alone, not on the comparisons: two sides holding two spellings of one
    object — `dCodes` above and `⟨List Code⟩` below — are still the same object, and `Wire.beq` and
    `vcomp`'s test say so with the objects open.  A fallback that OPENED a name the closed read found
    no lane in was tried and is wrong: `Decimal` has `list` in its carrier, so the factor that holds
    the bare name tore it open while the factor holding `E(Decimal)` — whose closed read stops at `E`
    — did not, and the same cut came apart one factor lower down. -/
def peelRead (objVars : Array Expr) (cat : Array Name) (regionTy X : Expr) :
    MetaM (Array (Wire × Expr) × Expr) :=
  withObjectsClosed regionTy (peelCuts objVars cat regionTy X)

/-- `peelRead` where the composite has already read the cut: the handed-down reading stands for the
    object it was read from, exactly as in `peelCutsAt`, and the closure governs only a cut this
    factor has to read for itself. -/
def peelReadAt (expect : Option Peeled) (objVars : Array Expr) (cat : Array Name)
    (regionTy X : Expr) : MetaM (Array (Wire × Expr) × Expr) := do
  if let some p := expect then
    let s ← Meta.saveState
    if ← Meta.isDefEq X p.obj then return (p.cuts, p.under)
    s.restore
  peelRead objVars cat regionTy X

/-- THE CUT BELOW `d` AS `d` DREW IT, which is what "read once, by the factor above" means.  An
    object `a×b` has two readings — the pair lane `peelCuts` prefers where both factors are lanes
    over one object, and `a×−` over `b` — and a product map split across its lanes (`wrap×𝟙`)
    draws the second; the factor below is then handed that one, not the free peel. -/
def cutAsDrawn (objVars : Array Expr) (cat : Array Name) (regionTy : Expr) (d : Diagram)
    (y : Expr) : MetaM (Array (Wire × Expr) × Expr) := do
  let drawn := d.bot.map fun i => d.lanes[i]!.wire
  let same (cs : Array (Wire × Expr)) : MetaM Bool := do
    unless cs.size == drawn.size do return false
    for (w, _) in cs, v in drawn do unless ← Wire.beq w v do return false
    return true
  let free ← peelRead objVars cat regionTy y
  if ← same free.1 then return free
  if let some (a, b) ← splitTimes? regionTy y then
    let (cb, ob) ← peelRead objVars cat regionTy b
    let flat := #[(Wire.timesL a, b)] ++ cb
    if ← same flat then return (flat, ob)
  return free

mutual

/-- `⟦e⟧`: the picture an arrow of the allegory IS.  A factor is taken apart until what is left acts
    on ONE contiguous block of lanes, and the parts that are identities are what runs past:

    * `⟦f≫g⟧` is `⟦f⟧` above `⟦g⟧`;
    * `⟦F(R)⟧` is `F`'s wires beside `⟦R⟧` — running past OUTSIDE it;
    * `⟦𝟙×ψ⟧` is the same thing for the lane `A×−`, `A×−` being a relator like any other and
      `𝟙×ψ` its action on `ψ`; `⟦φ×𝟙⟧` is ONE bead on that lane, turning `A×−` into `A'×−`; and
      `⟦φ×ψ⟧` is the interchange `⟦(φ×𝟙)(𝟙×ψ)⟧`, so the gate that the two halves meet at one cut
      is `vcomp`'s and needs no second copy here.

    Comparing the two ends' wire STACKS cannot do this: `cons : [A]×[[A]] ⟶ [[A]]` and
    `secure×𝟙` both leave `list list` below them, and the first eats those wires while the second
    does not.  What separates them is the factor's own form, which is what is read here. -/
partial def interp (regionTy : Expr) (cat : Array Name) (objVars : Array Expr)
    (vpass : Array Wire) (expect : Option Peeled) (e : Expr) : MetaM Diagram := do
  -- THE LANES A RELATOR'S ACTION RUNS PAST, and the arrow it acts on drawn under them.  One helper,
  -- so the three spellings that reach it cannot drift apart.
  let lane (ws : Array Wire) (r : Expr) : MetaM Diagram := do
    let d ← interp regionTy cat objVars (vpass ++ ws)
      (Peeled.inner expect ws.size (← homEnds r).1) r
    (← Diagram.id ws d.otop).beside d
  -- A constant the note draws OPENED is opened first, so the picture is of the body the note
  -- writes and not of one bead carrying the name Lean prints.
  let e' ← openNoted e
  if e' != e then return ← interp regionTy cat objVars vpass expect e'
  -- EVERY ARROW THIS DRAWS IS A SPINE, at whatever lane depth, so the `diag_rewrite` step is taken
  -- HERE and not on the side alone: a `Λ` under `E(−)` splits into the unit and its nested `E` lane
  -- exactly as one at the top does.  AFTER the opening, because `openNoted` opens `𝟙%∋` back to the
  -- `Λ 𝟙` the rewrite has just built, and the two chase each other for ever the other way round.
  let e ← rewriteSpine e
  let fs := factors e
  if fs.size > 1 then return ← vstack regionTy cat objVars vpass expect fs
  -- A BUILT BUNDLE'S ACTION OPENS AS ITS OBJECTS DO: `(F×F')(R)` is `F(R)×F'(R)`, the product map
  -- whose ends are the `FA×F'A` a product map beside it reads, so the cut they share is spelled once.
  -- ONLY where the opened action IS such a map: `F(X,−)`'s action opens to a `BiRelator.map` no
  -- clause reads, and there the `F.map` route below draws it under its own lane.
  if let some r ← openBuiltField? e then
    if r != e && ((← asProdMap? regionTy r fun p => pure p.isSome) || (← asSumMap? r).isSome) then
      return ← interp regionTy cat objVars vpass expect r
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      return ← lane ((wiresOf args[4]!).map Wire.rel) args[args.size - 1]!
  -- AN IDENTITY IS NO BEAD: `𝟙` is the bare wire, so its picture is the lanes it runs on with
  -- nothing drawn on them.  On the HEAD, so every identity of every object goes the same way.
  | (``Cat.id, _) =>
    let (x, _) ← homEnds e
    let (cx, ox) ← peelReadAt expect objVars cat regionTy x
    return ← Diagram.id (cx.map (·.1)) ox
  | _ => pure ()
  -- A PRODUCT MAP WHOSE SOURCE IS ONE PAIR LANE (`G×G'` over `B`, `peelCuts`) is no pair of lanes
  -- to split it across: it is ONE bead on that lane, `φ×ψ : G×G' ⇒ F×F'`, read by the tail below.
  let pairLane ← do
    let (cx, _) ← peelReadAt expect objVars cat regionTy (← homEnds e).1
    pure (match cx[0]? with | some (.rel f, _) => f.isAppOf ``Freyd.Alg.Relator.prod | _ => false)
  -- `none` from the product-map reading is "not drawn here": the tail below reads the factor.
  let prod (φψ : Option (Expr × Expr)) : MetaM (Option Diagram) := do
    let some (φ, ψ) := φψ | return none
    let (a, a') ← homEnds φ
    let (b, _) ← homEnds ψ
    -- `𝟙×ψ` IS `(A×−).map ψ`: the left factor is one lane and `ψ` runs under it, so this is the
    -- `F.map` route and the verdict of `ψ` closes through the same chain as any `F(R)`.
    if ← isIdArrow φ then return some (← lane #[Wire.timesL a] ψ)
    let one ← Meta.mkAppM ``Cat.id #[b]
    -- Interchange, `φ×ψ = (φ×𝟙)(𝟙×ψ)`, and functoriality, `(φ₁φ₂)×𝟙 = (φ₁×𝟙)(φ₂×𝟙)`: both split
    -- the map into product maps this same case then draws, one bead each.
    let fφ := factors φ
    if !(← isIdArrow ψ) || fφ.size > 1 then
      let mut ps : Array (Expr × Expr) := fφ.map (·, one)
      unless ← isIdArrow ψ do ps := ps.push (← Meta.mkAppM ``Cat.id #[a'], ψ)
      if ps.size > 1 then
        return some (← withProdMapsAt e ps.toList #[] #[] fun parts =>
          vstack regionTy cat objVars vpass expect parts)
    -- `φ×𝟙` is ONE bead on the left factor's lane, `A×− ⇒ A'×−`, ONLY where it is a family in the
    -- statement's own object: the lanes east of it are then what that object is, and only run past.
    -- Where `φ` cannot vary with it — `secure amount N`, whose `amount` pins the object — the whole
    -- `φ×𝟙` is ONE arrow, it rides the object wire like `α` and `⦇R⦈`, and its arrow is every lane
    -- its bar spans, which is what the tail below types it as.
    -- THE QUESTION HERE IS THE SHAPE, not the dot: whether the bar is one bead on the left lane at
    -- all.  Its ends are read by the `Diagram.bead` below, which is where a dot is claimed.
    if (← familyVar e objVars).isSome then
      let (cx, ox) ← peelReadAt expect objVars cat regionTy (← homEnds e).1
      let (_, oy) ← peelRead objVars cat regionTy (← homEnds e).2
      return some (← Diagram.bead regionTy cat objVars #[Wire.timesL a] #[Wire.timesL a'] ox oy e
        (over := (cx.extract 1 cx.size).map (·.1)))
    return none
  unless pairLane do
    if let some d ← asProdMap? regionTy e prod then return d
  -- A RELATOR'S ACTION IS THE `F.map` ROUTE WHATEVER IT IS SPELLED: `list (Λ(R) est(Q))` is that
  -- composite drawn under the `list` wire, two beads, not one bead nobody can read the run inside
  -- of.  Last, so a factor the reader already has a form for keeps it.
  if let some (R, r) ← peelMap? cat objVars regionTy e then
    return ← lane ((wiresOf R).map Wire.rel) r
  let (x, y) ← homEnds e
  let (cx, ox) ← peelReadAt expect objVars cat regionTy x
  let (cy, oy) ← peelRead objVars cat regionTy y
  let ax := cx.map (·.1)
  let ay := cy.map (·.1)
  -- THE LANES UNDER A BEAD RUN PAST IT INSIDE, AND THE OBJECT THEY SPELL IS THE ARGUMENT THE BEAD'S
  -- OWN DECLARATION TAKES.  `@moves n X` is a family in `X` however deep the object standing at `X`
  -- is, so every lane `X` peels into runs past it.  The stack the two ends merely SHARE reaches
  -- further — `moves`' own `[n]` trails both ends — and the abstraction there fails outright, which
  -- is how `[p][m]` came to be eaten at the `moves` row and reborn under it.  The shared stack stays
  -- as the LAST candidate: `𝟙%∋` at `F A` names no argument of its own and is a family all the same.
  if ← Meta.isDefEq ox oy then
    -- ONE candidate split: `k` trailing lanes run past the bead, the rest are its arms and legs.
    let split : Nat → MetaM (Option Diagram) := fun k => do
      -- A BEAD THAT TOUCHES NO LANE MAY NOT STAND OVER ONE.  Where the stack is the WHOLE of both
      -- cuts, the abstraction is a family `Id ⇒ Id` at the composite object, and every lane would
      -- run past a bead with no arms and no legs — the picture of `K(φ_A)`, the functor applied
      -- OUTSIDE, which is a different arrow from `φ` AT `K(A)`.  Such a bead SPANS its object
      -- instead: the fall-through gives it every lane of the ends as an arm and again as a leg, so
      -- they die at the bar and are reborn below, by the mechanics a bead with arms already has.
      if 0 < k && k == ax.size && k == ay.size then return none
      if k > ax.size || k > ay.size then return none
      -- The lanes running past are ONE stack, drawn once, so both ends have to spell them alike.
      for j in [0 : k] do
        unless ← Wire.beq ax[ax.size - 1 - j]! ay[ay.size - 1 - j]! do return none
      let x' := if k == ax.size then x else cx[ax.size - k - 1]!.2
      let y' := if k == ay.size then y else cy[ay.size - k - 1]!.2
      unless ← Meta.isDefEq (← Meta.inferType x') regionTy do return none
      unless ← Meta.isDefEq x' y' do return none
      let e' ← Meta.kabstract e x'
      unless e'.hasLooseBVars && !objVars.any (fun v => e'.containsFVar v.fvarId!) do return none
      -- A family only where the abstraction TYPE-CHECKS: `S°` at `A` abstracts its `A` too, but
      -- `S : F A ⟶ A` pins it, and the result is no arrow of any object.
      Meta.withLocalDeclD `a regionTy fun a => do
        let ea := e'.instantiate1 a
        unless ← Meta.isTypeCorrect ea do return none
        some <$> Diagram.bead regionTy cat #[a] (ax.extract 0 (ax.size - k))
          (ay.extract 0 (ay.size - k)) ox oy ea (over := ax.extract (ax.size - k) ax.size)
    -- How deep an end already holds `t`: the trailing lanes are the ones `t` itself peels into.
    let depth : Expr → MetaM (Option Nat) := fun t => do
      for i in [0 : cx.size] do
        if ← Meta.isDefEq cx[i]!.2 t then return some (cx.size - i - 1)
      return none
    -- LARGEST FIRST — `X = [p][m]A` before `A` — because the index a declaration takes stands for
    -- every lane the object at it peels into, and a shallower one cuts the rest at the bead's row.
    let mut ks : Array Nat := #[]
    for t in ← indexArgs regionTy e #[] do
      if let some k ← depth t then if 0 < k then ks := ks.push k
    let mut kmax := 0
    while kmax < ax.size && kmax < ay.size do
      unless ← Wire.beq ax[ax.size - 1 - kmax]! ay[ay.size - 1 - kmax]! do break
      kmax := kmax + 1
    for k in (ks.qsort (· > ·)).push kmax do
      if let some d ← split k then return d
  Diagram.bead regionTy cat objVars ax ay ox oy e

/-- THE FACTORS STACKED, each read at the cut the factor above it ENDED at.  A cut belongs to the
    COMPOSITE and not to either factor: the two factors hold different spellings of the one object
    between them, and an object has more than one peel, so a cut each side reads for itself comes
    out `F|[Char]` above and `F|Char` below with nothing wrong on either side.  It is therefore read
    once — by the factor above, at its own target, which is how that factor drew its bottom edge —
    and handed to the factor below as its source. -/
partial def vstack (regionTy : Expr) (cat : Array Name) (objVars : Array Expr)
    (vpass : Array Wire) (expect : Option Peeled) (fs : Array Expr) : MetaM Diagram := do
  let mut d ← interp regionTy cat objVars vpass expect fs[0]!
  for i in [1 : fs.size] do
    let y := (← homEnds fs[i-1]!).2
    let (cy, oy) ← cutAsDrawn objVars cat regionTy d y
    -- A cut mismatch is between TWO FACTORS, and the cut text alone does not say which pair, so
    -- the factors either side of it are added here rather than left for the reader to count out.
    d ← try d.vcomp (← interp regionTy cat objVars vpass
          (some { obj := y, cuts := cy, under := oy }) fs[i]!)
      catch err => throwError "{err.toMessageData}\n  — the cut between `{← plain fs[i-1]!}` and \
        `{← plain fs[i]!}`"
  return d

end

/-! ### One component of a side

  A SELECTOR STEP NAMES A COMPONENT BY THE TYPE OF THE TERM IT DESCENDS INTO, never by where on the
  side the branching happens to sit.  `branchOf` answers the one position whose arm is NOT an
  in-place substitution — the coproduct left open at the run's source, where the injection has to
  slide through every factor before the junction into that summand's own action — and the walk below
  asks the same question of the whole SPINE: the constructors the picture's own reader walks, which
  are composition's factors, a relator's action on an arrow however it is spelled, and a converse's
  argument.  A fraction needs no case of its own: `rewriteSpine` has already opened `Λ(R)` into the
  unit bead and `E(R)`, a relator's action like any other, and that is the same opening the panel is
  drawn from.  THE WALK STOPS AT THE FIRST BRANCHING NODE on each path, so a junction's arms and a
  union's operands belong to the NEXT step of the chain and not to this one.

  A JUNCTION'S ARM IS FORCED ACROSS THE WHOLE RUN; A UNION'S OPERAND IS A LOCAL CHOICE.  The
  coproduct object is carried ALONG the run — `[f,g]° ≫ … ≫ [h,k]` hands it from one end to the
  other — so a picture at one summand is at that summand wherever a junction stands over it, and the
  step takes arm `i` at every junction the spine reaches: the rule is the OBJECT they stand over,
  not how many of them there are, and taking a different arm at two of them does not type-check,
  which is why the result is CHECKED rather than counted.  Two unions on one spine name four
  combinations and `.inl`/`.inr` names none of them, so that is reported with both nodes rather than
  settled by picking the last. -/

/-- AN APPLICATION with one argument REPLACED, its IMPLICIT arguments solved afresh.  An arm does
    not start where the junction it replaces did, so the objects the implicit arguments pin are
    exactly what has to move with it: keeping them is what had `E(g)` checked at `E`'s old source and
    refused.  Only the EXPLICIT arguments are passed on, so the objects are re-solved from them. -/
def reapp (e : Expr) (k : Nat) (a : Expr) : MetaM Expr := do
  let .const n _ := e.getAppFn
    | throwError "`{← plain e}` is no constant applied to arguments, so the component has nothing \
        to go into"
  let some ci := (← getEnv).find? n
    | throwError "`{n}` heads `{← plain e}` and is in no environment, so the component cannot be \
        put back into it"
  let args := e.getAppArgs
  let mut expl : Array Expr := #[]
  let mut ty := ci.type
  for j in [0 : args.size] do
    let .forallE _ _ b bi := ty
      | throwError "`{n}` takes fewer arguments than `{← plain e}` gives it, so its implicit \
          arguments cannot be solved again"
    unless bi.isExplicit || j != k do
      throwError "the component sits at an implicit argument of `{← plain e}`, which the \
        application does not take back"
    if bi.isExplicit then expl := expl.push (if j == k then a else args[j]!)
    ty := b
  try Meta.mkAppM n expl
  catch err => throwError "{err.toMessageData}\n  — `{← plain e}` does not take the component back"

/-- A JUNCTION over a coproduct and its arms, whether it is written as one or as an arrow built from
    a MAP THAT BRANCHES ON ITS INPUT: `graph [f,g]` is the junction `[graph f, graph g]`, the branch
    living in the map, so the arm is the same wrapper at the arm map.  `sumArms` reads the arms off
    the elaborated `match` and the coproduct off the discriminant's type, so no `def`'s name appears
    here and the arm is found wherever the junction is spelled that way. -/
def juncArm? (e : Expr) (i : Nat) : MetaM (Option Expr) := do
  if let some (_, X, Y) ← juncOf? e then return some (if i == 0 then X else Y)
  unless e.getAppFn.isConst do return none
  let args := e.getAppArgs
  for k in [0 : args.size] do
    -- A MAP, by its TYPE: an argument that is not a function branches on nothing.
    if (← Meta.inferType args[k]!).isForall then
      if let some fw ← branchForm? args[k]! then
        if let some arms ← sumArms fw then
          -- ONLY the arm asked for is built: the other one is a different summand's arrow and a
          -- failure to build it says nothing about this one.
          let some a := arms[i]?
            | throwError "`{← plain e}` branches into {arms.size} arms, so it has no {i + 1}-th one"
          return some (← reapp e k a)
  return none

/-- The branching nodes the SPINE of `e` reaches — each with whether it is a junction, so a union
    among them can be reported — and `e` with component `i` of every one of them in its place. -/
partial def branchWalk (regionTy : Expr) (cat : Array Name) (objVars : Array Expr) (i : Nat)
    (e : Expr) : MetaM (Array (Bool × Expr) × Option (Expr × Expr) × Expr) := do
  if let some (l, r) ← binOperands? e then
    return (#[(false, e)], none, if i == 0 then l else r)
  if let some arm ← juncArm? e i then
    return (#[(true, e)], some ((← homEnds e).1, (← homEnds arm).1), arm)
  let fs := factors e
  if fs.size > 1 then
    let mut found : Array (Bool × Expr) := #[]
    let mut obj? : Option (Expr × Expr) := none
    let mut parts : Array Expr := #[]
    for f in fs do
      let (g, o, f') ← branchWalk regionTy cat objVars i f
      found := found ++ g
      if obj?.isNone then obj? := o
      parts := parts.push f'
    if found.isEmpty then return (#[], none, e)
    -- THE PICTURE IS AT ONE SUMMAND, SO THE WHOLE RUN IS: the coproduct object the arm restricts is
    -- substituted in every factor, because a factor above the junction runs FROM that object and
    -- names it wherever it likes — `𝟙%∋` is `Λ(𝟙 a)`, the object nested two deep — and only the
    -- object itself says which occurrences are the cut's.  A union's operand restricts no object,
    -- and then there is nothing to substitute.
    if let some (old, new) := obj? then
      unless ← Meta.isDefEq old new do
        for k in [0 : parts.size] do
          parts := parts.set! k ((← Meta.kabstract parts[k]! old).instantiate1 new)
    return (found, obj?, ← compose parts)
  -- A RELATOR'S ACTION AND A CONVERSE ARE FUNCTORIAL IN THE OBJECT THE BRANCHING IS OVER, so the
  -- component goes inside and the wrapper stands: `E([f,g])` is `E(g)` at the second arm and
  -- `[f,g]°` is `g°`.  The action is recognised the way `interp` recognises it — by the head, then
  -- by the catalogue — so a relator written as `powerRel` is entered like one written `E.map`.
  let inner? : Option Expr ←
    if e.isAppOf ``Freyd.Alg.Allegory.recip then pure e.getAppArgs.back?
    else match functorMap? e with
      | some (_, r) => pure (some r)
      | none => pure ((← peelMap? cat objVars regionTy e).map (·.2))
  let some r := inner? | return (#[], none, e)
  let (found, obj?, r') ← branchWalk regionTy cat objVars i r
  if found.isEmpty then return (#[], none, e)
  let args := e.getAppArgs
  let mut slot : Option Nat := none
  for k in [0 : args.size] do
    if slot.isNone && args[k]! == r then slot := some k
  let some k := slot
    | throwError "the branching is inside `{← plain r}`, which is no argument of `{← plain e}` as \
        it stands, so the component has nothing to go back into"
  return (found, obj?, ← reapp e k r')

/-- `.inl`/`.inr`: ONE COMPONENT of a side, `i` naming which.  `branchOf`'s position is tried first,
    being the only one whose answer is not an in-place substitution; its refusal is a SHAPE test and
    not a failure, so it is carried into whatever the spine walk then has to say rather than
    dropped. -/
def branchSel (regionTy : Expr) (cat : Array Name) (objVars : Array Expr) (e : Expr) (i : Nat) :
    MetaM Expr := do
  let slid : Except Exception Expr ←
    try pure (Except.ok (← branchOf regionTy e i)) catch err => pure (Except.error err)
  match slid with
  | .ok x => return x
  | .error err =>
    let (found, _, e') ← branchWalk regionTy cat objVars i (← rewriteSpine e)
    if found.isEmpty then
      throwError "{err.toMessageData}, and its spine reaches no junction and no binary operation \
        either, so `.inl`/`.inr` names nothing in it"
    if found.size > 1 && found.any (fun p => !p.1) then
      let mut names : Array String := #[]
      for (_, n) in found do names := names.push (← plain n)
      throwError "`.inl`/`.inr` names ONE component, and the spine of `{← plain e}` reaches \
        {found.size}: {String.intercalate ", " names.toList}.  A junction's arm is the same arm at \
        every junction the run carries its coproduct through, but a union's operand is a choice \
        local to that union, so this step names none of them"
    try Meta.check e'
    catch terr =>
      throwError "{terr.toMessageData}\n  — component {i + 1} of `{← plain e}` is \
        `{← plain e'}`, so what holds the branching is not functorial in the object it is over; \
        {err.toMessageData}"
    let out ← instantiateMVars e'
    -- An object nothing determines is a wire with nothing under it, so it is reported here rather
    -- than drawn as a metavariable.
    if out.hasExprMVar then
      throwError "component {i + 1} of `{← plain e}` came out as `{← plain out}`, whose objects \
        nothing in the statement determines"
    return out

/-- One side of a statement, as a panel: its picture, with the bottom edge's lanes told how deep the
    picture turned out to be.  The rewrite that draws `Λ S` as the note draws it — the unit bead and
    `S` on the `E` lane — is `interp`'s, taken at every spine it draws and so at every lane depth;
    a side is one such spine and gets no copy of it here. -/
def panelOf (regionTy : Expr) (cat : Array Name) (side : Expr) (objVars : Array Expr) :
    MetaM Diagram := do
  let d ← interp regionTy cat objVars #[] none (← instantiateMVars side)
  let n : Int := d.rows.size
  return { d with lanes := d.lanes.map fun l => if l.dies == LIVE then { l with dies := n } else l }

/-- The selectors applied in order, with the REST OF THE READ run under whatever locals they open.
    `.body` instantiates the least fixed point's binder with a local of that binder's own name, and
    the picture draws that local as a wire and prints it by that name — so the panel has to be built
    while the local is still in scope, which is why this takes a continuation instead of handing an
    expression back. -/
partial def withSel {α : Type} [Inhabited α] (regionTy : Expr) (cat : Array Name)
    (objVars : Array Expr) (sel : List Sel) (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  match sel with
  | [] => k e
  | .inl :: rest => withSel regionTy cat objVars rest (← branchSel regionTy cat objVars e 0) k
  | .inr :: rest => withSel regionTy cat objVars rest (← branchSel regionTy cat objVars e 1) k
  | .body :: rest =>
    let some φ := muArg? e
      | throwError "`.body` names the body of a least fixed point, and `{← plain e}` is not one"
    Meta.lambdaBoundedTelescope φ 1 fun xs b => do
      unless xs.size == 1 do
        throwError "`{← plain φ}` binds no arrow, so `.body` opens no wire to draw the body on"
      withSel regionTy cat objVars rest b k

/-- Every part of the statement drawn, each under its own selectors' locals, and the file emitted
    inside all of them: a bead's ends are printed from the `Expr`, so a local opened for one part is
    still needed when the last part's panel is written out. -/
partial def withParts {α : Type} [Inhabited α] (regionTy : Expr) (cat : Array Name)
    (objVars : Array Expr) (sel : List Sel) (drawn : List (String × Expr))
    (acc : Array (String × Diagram)) (k : Array (String × Diagram) → MetaM α) : MetaM α :=
  match drawn with
  | [] => k acc
  | (sym, e) :: rest =>
    withSel regionTy cat objVars sel e fun e' => do
      withParts regionTy cat objVars sel rest (acc.push (sym, ← panelOf regionTy cat e' objVars)) k

/-- A declaration is read in ITS OWN namespaces.  `Freyd.Alg` keeps its allegory instances and its
    `≫`/`°`/`⦇⦈` notations scoped, so outside them the region has no product to split an object on
    and every label prints as `Cat.comp` — the picture then comes out with no lanes at all and no
    error to say why.  Every prefix of the name is opened, which is exactly the scope the
    declaration itself was elaborated in. -/
def withDeclScope (declName : Name) (k : MetaM α) : MetaM α := do
  let mut ns : List OpenDecl := []
  let mut pre := declName
  while !pre.isAnonymous do
    pre := pre.getPrefix
    unless pre.isAnonymous do ns := .simple pre [] :: ns
  withTheReader Core.Context (fun c => { c with openDecls := c.openDecls ++ ns }) k

/-- DOES OPENING THIS `def` LOSE A LANE?  A `def` is drawn by its body so the picture shows what it
    IS, and a body that is a composite shows more wires and more beads than the name does.  But a
    body whose own type spells FEWER wires than the declaration's type has thrown the picture away
    rather than opened it: `fold A : Δᴛ(A) ⟶ carrier(A)` unfolds to `⦇alg(A)⦈ : t ⟶ carrier(A)`,
    where `Δᴛ` — the lane the whole 2-cell stands on — is gone, and with it the object wire's
    region.  Counted with the very peel the panel's cuts are read by, so what is compared is the
    wire stack the picture WOULD draw and not the shape the term happens to have. -/
def opensFewerLanes (cat : Array Name) (declTy opened : Expr) : MetaM Bool := do
  let some (x, y) := homObjs? declTy | return false
  let some (x', y') ← homEnds? opened | return false
  let lanes (t : Expr) : MetaM Nat := do
    let (cs, _) ← peelRead #[] cat (← Meta.inferType t) t
    return cs.size
  return (← lanes x) > (← lanes x') || (← lanes y) > (← lanes y')

/-- `--string <Name>[#<binder>][.lhs|.rhs][.inl|.inr…]`.  A `def` is drawn by its BODY unfolded one
    level; a HYPOTHESIS IS A STATEMENT TOO, so `#h` draws that binder's type instead of the
    conclusion, and a `def`'s body is then not unfolded because the binder belongs to the type.

    A statement is drawn WHOLE — both sides in one frame — or one side at a time.  `peers` is THE
    CALL: the selectors one `#lean(…)` names, this one among them, which are the panels that stand
    beside each other on the page.  They slide to the bead they share and come out in one box, at one
    height; a selector that arrived in a call of its own shares with nothing and is as deep as its own
    beads, whatever the declaration says.  The path names the statement, so `.lhs` on an `↔` draws the
    whole left statement and only a trailing name on a relation picks a side. -/
-- A PEER MAY BE ANOTHER DECLARATION: a chain `a ⊑ b = c` spreads its steps over several theorems,
-- and its panels stand in one row, so `draw := false` reads a peer's parts in its OWN telescope.
partial def drawWith (declName : Name) (path : List String) (binder : Option String) (sel : List Sel)
    (peers : List (String × Option String × List String × List Sel)) (draw : Bool) :
    MetaM (String × Array Diagram) :=
    -- THE BUDGET COVERS THE WHOLE READ, not the search inside it.  A budget lifted only around the
    -- searches lapses the moment they return, and what the panel does NEXT — printing each bead's
    -- ends — then runs on an allowance the searches have already spent, so the read dies naming an
    -- `isDefEq` that is not the expensive one.  `CANDIDATE_HEARTBEATS` bounds each match tried and
    -- `scripts/cap` bounds the process; nothing between them needs an allowance of its own.
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    withDeclScope declName do
  let env ← getEnv
  let some ci := env.find? declName | throwError "no such declaration: {declName}"
  -- ONE SWEEP.  The catalogue is the ENVIRONMENT's lanes and not the statement's, so it is read
  -- once and threaded: the def-opening test below peels cuts with it, and so does every panel.
  let cat ← catalogue
  -- `stmtTelescope`, not `forallTelescopeReducing`: in a CONCRETE region a hom reduces to a
  -- function type, so the reducing walk goes straight through the arrow an arrow-valued `def` IS
  -- and hands back the codomain with the arrow's own elements as extra binders — the def's body
  -- then came back applied to them and was refused as "not an arrow".  The circuit exporter
  -- already stops at the hom; this one must too.
  -- A DECLARATION'S BINDERS AND ITS STATEMENT'S OWN ARE ONE TELESCOPE.  A `def` whose body is a
  -- `∀` — a lax-naturality predicate — keeps the objects the statement quantifies over INSIDE the
  -- body, where the first walk cannot reach them, and the arrow still carried them and was refused
  -- as no arrow.  Re-quantifying over what has been entered and walking once more lands on the
  -- statement whichever side of the definition its binders sit.
  let stmt ← stmtTelescope ci.type fun xs body0 => do
    let body ← match binder with
      | some h =>
        match ← xs.findM? fun x => return (← x.fvarId!.getUserName).toString == h with
        | some x => Meta.inferType x
        | none =>
          let names ← xs.mapM fun x => return (← x.fvarId!.getUserName).toString
          throwError "{declName} has no binder `{h}`; its binders are \
            {String.intercalate ", " names.toList}"
      | none =>
        let isDef := match ci with | .defnInfo _ => true | _ => false
        match (if isDef then ci.value? else none) with
        | none => pure body0
        | some v =>
          let opened := (mkAppN v xs).headBeta
          -- ... UNLESS OPENING LOSES A LANE, in which case the declaration APPLIED TO ITS OWN
          -- BINDERS is the arrow drawn, and its type is what the picture reads its cuts off.
          if ← opensFewerLanes cat body0 opened then
            pure (mkAppN (mkConst declName (ci.levelParams.map mkLevelParam)) xs)
          else pure opened
    -- A PREDICATE STATES ITS OWN SQUARE.  Drawing `LaxNatural F G φ` opens its definition, so the
    -- square on the page IS the claim about `φ` — and `φ` is bound by the predicate itself, so no
    -- declaration in the environment can speak about it and the search comes back a spider.
    -- Re-quantifying the body under the predicate APPLIED TO ITS OWN BINDERS puts that claim where
    -- `hypVerdict` already looks, and it is the same evidence a theorem's `(h : LaxNatural F G φ)`
    -- binder is.  `isSort`: only a declaration whose type ENDS in a sort is a predicate, so a
    -- partially applied telescope that stopped at a hom states nothing about itself.
    if (markOfNatPredicate declName).isSome && body0.isSort then
      let self := mkAppN (mkConst declName (ci.levelParams.map mkLevelParam)) xs
      Meta.withLocalDeclD declName self fun h => Meta.mkForallFVars (xs.push h) body
    else Meta.mkForallFVars xs body
  stmtTelescope stmt fun xs body => do
    -- A PATH NAMES A STATEMENT; a TRAILING SIDE NAME picks one part of it.  `relCata_UP` is an `↔`
    -- between two inequations, so `.lhs` names the left inequation and draws it whole — both parts
    -- in one frame — and `.lhs.lhs` goes on to that inequation's left part alone.  A step descends
    -- while what it lands on is still a statement built from statements (`conn?`); the first step
    -- that is not names a part, and nothing can follow it.
    -- The statement's own PARTS and the ones ONE REQUEST draws: the two sides a relation symbol
    -- joins, or the arrow itself, and then the side the request's trailing name picks out of them.
    -- The steps that named the STATEMENT come back first, and the parts they leave are the ones
    -- this file draws — the parts that line up, in its one canvas, on a bead they share.
    let reqParts (path : List String) :
        MetaM (List String × Array (String × Expr) × Array (String × Expr)) := do
      let mut body := body
      let mut side : Option String := none
      let mut stmt : List String := []
      for s in path do
        match side, conn? body with
        | none, some (l, r) => body := if s == "lhs" then l else r; stmt := stmt ++ [s]
        | none, none => side := some s
        | some p, _ =>
          throwError "`.{s}` follows `.{p}`, which already names a part of \
            {← Meta.ppExpr body}: a part has no sides of its own"
      let parts : Array (String × Expr) := match split body with
        | some (sym, l, r) => #[("", l), (sym, r)]
        | none => #[("", body)]
      match side with
      | none => return (stmt, parts, parts)
      | some s =>
        if parts.size < 2 then throwError "{declName} has no two sides to draw one of"
        else return (stmt, parts, #[("", if s == "lhs" then parts[0]!.2 else parts[1]!.2)])
    let (_, parts, drawn) ← reqParts path
    let arrow := parts[0]!.2
    -- The OBJECT VARIABLES of the statement: a factor mentioning one is a family, and only a
    -- family can carry a dot.  A binder counts when it is an object of the region — or, where the
    -- region is a ONE-FIELD STRUCTURE over an index type, when it is that INDEX: `X : Type`
    -- names the object `⟨X⟩ : RelSet`, `dE X` IS that object, and `⟨a.carrier⟩` is `a`, so the
    -- two readings are one family and `StrictNatural F G φ` is a statement about it after all.
    let (src, _) ← homEnds arrow
    let regionTy ← Meta.inferType src
    let idxTy ← regionIndexType? regionTy
    let mut objVars : Array Expr := #[]
    for x in xs do
      let t ← Meta.inferType x
      if ← Meta.isDefEq t regionTy then objVars := objVars.push x
      else if let some it := idxTy then
        if ← Meta.isDefEq t it then objVars := objVars.push x
    unless draw do
      return ("", ← drawn.mapM fun (_, e) =>
        withSel regionTy cat objVars sel e fun e' => panelOf regionTy cat e' objVars)
    -- `.inl`/`.inr` is ONE BRANCH of the side, and the selectors CHAIN: each names an operand of
    -- the binary operation what the one before it left is, outermost first.  What that operation
    -- is — a union, a meet, a junction over a coproduct — is read off the run's type by
    -- `branchOf`, and the object variables are the statement's own either way.
    -- THE BOX IS THE ONE THE CALL NEEDS — a row per bead, and the row above the first of them that
    -- its arms and any lane born over it run in.  The selectors of ONE `#lean(…)` call are the
    -- panels that stand beside each other, so they slide to the bead they share and take one box, as
    -- deep as the deeper of them; a call naming one selector shares with nothing.  Grouping by the
    -- DECLARATION instead handed a side the depth of a side it is drawn nowhere near — half a panel
    -- of blank rows wherever the shared bead is one side's first and the other's last, which is what
    -- "unnecessary vertical space" named in (14.3f).
    let mut qs : Array Diagram := #[]
    for (b, h, p, s) in peers do
      if b.toName == declName && h == binder then
        let (_, _, d) ← reqParts p
        for (_, e) in d do
          qs := qs.push (← withSel regionTy cat objVars s e fun e' => panelOf regionTy cat e' objVars)
      else qs := qs ++ (← drawWith b.toName p h s [] false).2
    let pl := placement qs
    -- THE OBLIGATION IS THE CALL'S, and it is taken over the parts the CALL names — not over the
    -- one file this run writes, which is a record and would drop out of the count by being deleted.
    -- A pair owes two things and this is where both are answered: ONE HEIGHT, so the parts stand in
    -- the one box, and ONE ROW for every bead two of them carry, so the reader sees which bead moved
    -- instead of re-aligning them by eye.
    for i in [0 : qs.size] do
      let a := qs[i]!
      if framex a > pl.frame then
        throwError "{declName}: one part of this call needs {framex a} rows where the call's box is \
          {pl.frame}: every panel of one `#lean(…)` call is drawn at ONE height, the deepest part's"
      -- NEIGHBOURS ONLY: a chain's step is the two panels either side of its symbol, and a bead
      -- may move over several steps, so panels two steps apart owe each other nothing.
      for j in [i + 1 : min (i + 2) qs.size] do
        let b := qs[j]!
        -- The beads the two parts share, as (row in `a`, row in `b`, level in both).
        let mut shared : Array (Nat × Nat × Bool) := #[]
        for ra in [0 : a.rows.size] do
          for rb in [0 : b.rows.size] do
            if a.rows[ra]!.key == b.rows[rb]!.key then
              shared := shared.push (ra, rb, (pl.top a : Int) - ra == (pl.top b : Int) - rb)
        -- A BEAD THAT MOVED PAST A LEVEL ONE IS THE STATEMENT, not a misplacement: a slide
        -- `H(R)ψφ ⊑ ψφF(R)` carries `R` from above `ψ` to below it, and no box holds both level.
        -- So a shared bead may stand at two heights only where its order against a level bead
        -- differs between the parts; kept in order, two heights are the misplacement this refuses.
        -- A LABEL THAT OCCURS TWICE is two beads (`Λ(T°)` and `Λ(H)` both open with `𝟙%∋`), so a
        -- pairing is only a misplacement when neither bead has a level partner of its label.
        -- A BEAD ONLY ONE SIDE HAS, between a shared bead and a level one, needs an empty row on the
        -- other side that the layout does not give (`P(X)est(R) ⊑ ∋X` puts `∋` above `X`), so that
        -- distance cannot match; a gap of shared beads only can, and is still refused.
        let only (d e : Diagram) (i j : Nat) : Bool := (List.range' (min i j) (max i j - min i j)).any
          fun k => !(e.rows.any fun r => r.key == d.rows[k]!.key)
        for (ra, rb, level) in shared do
          unless level || shared.any (fun (sa, sb, l) => l && (sa == ra || sb == rb))
              || shared.any (fun (sa, sb, l) => l && (only a b ra sa || only b a rb sb))
              || shared.any fun (sa, sb, l) => l && (decide (ra < sa) != decide (rb < sb)) do
            let ya := (pl.top a : Int) - ra
            let yb := (pl.top b : Int) - rb
            throwError "{declName}: `{a.rows[ra]!.label}` stands on row {ya} of one panel of \
                  this call and row {yb} of another: the panels one `#lean(…)` call names are drawn \
                  side by side, so a bead they SHARE is drawn at one height in both"
    withParts regionTy cat objVars sel drawn.toList #[] fun parts => do
      let nm := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
        ++ path.foldl (fun a s => a ++ "." ++ s) ""
        ++ sel.foldl (fun s x => s ++ x.suffix) ""
      return (← if parts.size == 1 then emit declName parts[0]!.2 pl
        else emitStatement declName nm parts pl, #[])

def drawString (declName : Name) (path : List String) (binder : Option String) (sel : List Sel)
    (peers : List (String × Option String × List String × List Sel)) : MetaM String :=
  return (← drawWith declName path binder sel peers true).1

end Freyd.StrDiag
