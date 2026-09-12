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
  return String.intercalate "|" (ls.push (← plain c.o)).toList

/-- WHAT THE ENVIRONMENT PROVED ABOUT A BEAD, as a type and not a string.  The emitter matches on
    these four, so a verdict added here is a compile error until the mark it draws is decided —
    where a default branch silently drew the new one as an old one (`oplax` as `lax`). -/
inductive Mark where
  | strict | lax | oplax | spider
  deriving Inhabited, DecidableEq

/-- The word the drawing side reads the mark by.  One spelling, here: the panel's `nat:` row cites
    the same word the bead's 6th element carries. -/
def Mark.key : Mark → String
  | .strict => "strict" | .lax => "lax" | .oplax => "oplax" | .spider => "spider"

/-- One bead: what it eats, what it makes, what the object wire carries below it, and whether a
    declaration says it is natural. -/
structure Row where
  label : String
  arms  : Array Nat
  legs  : Array Nat
  obj   : String
  /-- The cut the bead is drawn between: the lanes it TOUCHES, over the object wire.  Never a cut
      assembled from a sibling bundle — `scripts/scanline` narrows the drawn cut to the touched
      lanes too, so the two are the same list read from the two sides. -/
  src   : Cut
  tgt   : Cut
  nat   : Option Mark := none
  /-- The declaration the verdict was read off — the panel's own citation for its dots, and for a
      bead the environment REFUTES, which draws no dot and is a claim all the same. -/
  natLean : Option Name := none
  /-- The lanes the bead STANDS OVER: the object it is a family at, `F A` for `𝟙%∋` taken there.
      They run past it inside, and a bead with no arms opens its leg WEST of them. -/
  over  : Array Nat := #[]
  /-- A UNIT: a family `𝟙 ⟹ W` — no arms, one leg, the same object under both.  Drawn as the
      note's unit lane, born half a row below the row it stands on with its own mark, not a bead. -/
  unit  : Bool := false
  deriving Inhabited

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
    let lo := maxA (othx.filter (· < minA arms c)) (-1e9)
    let hi := minA (othx.filter (· > maxA arms c)) 1e9
    let mut got : Array Float := #[]
    for d in SLIDE do
      got := Array.mk ((List.range r.legs.size).map fun j =>
        c + d + (j.toFloat - (r.legs.size.toFloat - 1.0) / 2.0) * DX)
      if lo + 1e-6 < got[0]! && got[got.size - 1]! < hi - 1e-6 then break
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

/-- The frame's height in cetz units.  The panel and the gate in `emitStatement` both read THIS,
    so the gate measures the box that is drawn and not a second copy of the rule. -/
def frameHeight (p : Diagram) (frame : Option Nat) : Float := (frame.getD (framex p)).toFloat * DY

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

/-- The `dpanel(...)` call this panel is.  `frame` and `top` are ROW COUNTS, the two halves of
    lining a short panel up with a tall one: the frame gives them one box, the top one bead
    height.  Left off, the frame is one row deeper than the panel and the first bead sits at the
    top of it. -/
def panelCode (p : Diagram) (declName : String) (frame topRow scale : Option Nat) :
    MetaM String := do
  let n := p.rows.size
  let ls := columns p
  let nr := frame.getD (framex p)
  let hh := frameHeight p frame
  let t0n := topRow.getD n
  let t0 := t0n.toFloat
  let ys : Array Float := Array.mk ((List.range n).map fun i => (t0 - i.toFloat) * DY)
  -- WITH NO LANE THERE IS NOTHING TO STAND EAST OF, so the object wire IS the first column.  The
  -- default `X0` is where a lane would have been, and adding `DX` to it puts the wire one column
  -- east of a column nobody drew (`11.4.1a`, `11.4.2a`).
  let xo := roundTo 2 (if ls.isEmpty then X0 else maxA (ls.map (·.x)) X0 + DX)
  -- A DIVISION `x%∋` is one token of the note's, `frac(x, ∋)` (`note-style.typ`'s `plain` reads it
  -- back as this very spelling), so a label that IS one is written as the note draws it — the unit
  -- `𝟙%∋` above all — where a division inside a composite label stays in the composite's text.
  let cell (s : String) : String :=
    let top := (s.dropEnd 2).toString
    if s.endsWith "%∋" && !top.contains '%' then "frc([`" ++ top ++ "`])" else "[`" ++ s ++ "`]"
  let str (s : String) : String := "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  let key (m : Mark) : String := ", \"" ++ m.key ++ "\""
  let held := heldLanes p
  let mut beads : Array String := #[]
  let mut objs : Array String := #[]
  let mut nats : Array String := #[]
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
      | some .lax => key .lax | some .oplax => key .oplax | some .spider => key .spider
    -- A UNIT is no bead: it is its leg's own birth, half a row below its row, written on the lane.
    if r.unit then
      objs := objs.push ("(" ++ num (ys[i]! - DY / 2.0) ++ ", " ++ cell r.obj ++ ")")
    else
      -- A DOT ON THE OBJECT WIRE STILL CARRIES ITS MARK: the fourth and fifth fields are the bar
      -- and the dot's own column, both absent here, and the sixth is the verdict — which a bead
      -- riding the object wire has exactly as much as one standing in its own column.
      beads := beads.push <| match reach, dot with
        | none, none =>
          if mark.isEmpty then "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ")"
          else "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, none, none" ++ mark ++ ")"
        | none, some d =>
          "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, none, " ++ num d ++ mark ++ ")"
        | some rc, none => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ")"
        | some rc, some d =>
          "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ", " ++ num d
            ++ mark ++ ")"
      objs := objs.push ("(" ++ num ys[i]! ++ ", " ++ cell r.obj ++ ")")
    -- Every FAMILY the tool looked at gets a row, the spider included: a reader must be able to
    -- see that the search ran and came back empty, which an absent row cannot say.
    if r.nat.isSome || r.natLean.isSome then
      nats := nats.push
        ("(" ++ str r.label ++ ", " ++ str ((r.nat.map Mark.key).getD "not-lax") ++ ", "
          ++ str ((r.natLean.map Name.toString).getD "") ++ ")")
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
      | some r => cell r.label ++ match r.nat with
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
    |>.push ("(" ++ num xo ++ ", " ++ cell (← plain p.otop) ++ ")")
  let bot := (ls.filter (·.dies >= (n : Int))).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell (← plain p.obot) ++ ")")
  return "dpanel(" ++ num hh ++ ", " ++ num (roundTo 2 (xo + PAD)) ++ ", " ++ num xo ++ ",\n  "
    ++ tup (made.map fun i => lanecode ls[i]!) ++ ",\n  " ++ tup beads ++ ",\n  " ++ tup top
    ++ ",\n  " ++ tup bot
    ++ ",\n  obj: " ++ tup objs
    -- A dot is a theorem, so the panel CITES the declaration each of its verdicts came from —
    -- including a refuted one, which draws no dot and is a claim all the same.  The frame and the
    -- top go in with them: they are the statement's, not this panel's, and `diagram --pairs` reads
    -- them back to hold the two sides of one display to one box.
    ++ ",\n  cert: (lean: \"" ++ declName ++ "\""
    ++ (if nats.isEmpty then "" else ", nat: " ++ tup nats)
    ++ ", frame: " ++ toString nr ++ ", top: " ++ toString t0n ++ ")"
    ++ (match scale with | some v => ", s: " ++ toString v ++ "%" | none => "") ++ ")"

/-- The file `--string` writes: how to regenerate it, the panel library, and the picture. -/
def fileOf (declName body : String) : String :=
  "// GENERATED by `diag-export --string` — do not edit; regenerate with\n\
   //   ./scripts/diag-export --string " ++ declName ++ "\n\
   #import \"../../dpanel.typ\": *\n\
   #import \"../../circuit.typ\": frc\n\n" ++ body

/-- One panel on its own — one side of a statement, or one branch of a side.  `panels` is the file's
    panels in order, so a caller holding the note to ONE of them — `scripts/string-check`, where the
    note draws the parts itself and the frame belongs to the statement — names it by index instead
    of re-splitting the picture. -/
def emit (p : Diagram) (declName : String) (frame topRow scale : Option Nat) : MetaM String :=
  return fileOf declName ("#let panels = (" ++ (← panelCode p declName frame topRow scale)
    ++ ",)\n#let pic = panels.at(0)\n")

/-- `--string --sigs`: what LEAN says each bead of `sel`'s panels is an arrow between, one JSON
    object per bead — `selector`, `panel` (numbered as the file emits them), `label`, `src`, `tgt`
    — so a reader takes FIELDS and never cuts a type at a separator the type may itself spell.
    Grouped by panel, so a panel with no bead is still one entry and a reader can tell it from a
    panel nobody answered for.  Nothing is written into the picture: `scripts/scanline` asks this at
    check time, so the types it holds the ink to are the environment's and cannot go stale. -/
def sigRecords (sel : String) (ps : Array Diagram) : MetaM (Array (Array Json)) :=
  ps.zipIdx.mapM fun (p, i) => p.rows.mapM fun r => do
    return Json.mkObj [("selector", sel), ("panel", toJson (i + 1)), ("label", r.label),
      ("src", ← cutText r.src), ("tgt", ← cutText r.tgt)]

/-- What one `--string` selector draws: the picture file's text and, when its bead types were
    asked for, `sigRecords` of its panels — both from ONE read of the statement, so a caller that
    needs the two does not pay the read twice. -/
structure Drawn where
  text : String
  sigs : Array (Array Json)
  deriving Inhabited

/-- How many rows LOWER than the reference part's a part's first bead sits, so that a bead the two
    SHARE stands at the one height — the alignment `diagram --pairs` holds a display to.  The
    landmark is the reference's HIGHEST shared bead: a lower one would be read first by a part that
    leads with it (`F(f)α` leads with `f`, which is `αT(f)`'s last) and would hang the part off the
    bottom of the box.  Labels are compared whole, as that gate compares them: a bead is the same
    bead when it is the same 2-cell. -/
def shiftTo (ref p : Diagram) : Int := Id.run do
  for i in [0 : ref.rows.size] do
    for j in [0 : p.rows.size] do
      if ref.rows[i]!.label == p.rows[j]!.label then return (j : Int) - (i : Int)
  return 0

/-- How far the most-shifted part slides below the reference's first bead. -/
def maxShift (ref : Diagram) (ps : Array Diagram) : Nat :=
  (ps.foldl (fun a p => max a (shiftTo ref p)) 0).toNat

/-- Where the REFERENCE part's first bead sits, in rows.  Every part starts `shiftTo` rows below it
    and its own last bead must still land on row 1, so the reference sits as high as the part that
    reaches deepest below it demands. -/
def topRefOf (ref : Diagram) (ps : Array Diagram) : Nat :=
  (ps.foldl (fun a p => max a ((p.rows.size : Int) - shiftTo ref p)) 1).toNat

/-- A DISPLAY's frame, in rows: the reference's first bead, the rows the most-shifted part adds
    above it, and the row of headroom the first bead sits below.  That is the deepest part's row
    count only when nothing slides; taking the max of the parts' OWN frames instead has to clamp a
    slide to fit, which puts a shared bead at two different heights — and aligning it is the whole
    reason the parts are drawn in one box. -/
def frameOf (ref : Diagram) (ps : Array Diagram) : Nat :=
  max (topRefOf ref ps + maxShift ref ps + 1) 2

/-- Where a part's first bead sits, in rows: the reference's, plus its own slide. -/
def topOf (topRef : Nat) (ref p : Diagram) : Nat := max ((topRef : Int) + shiftTo ref p) 1 |>.toNat

/-- One file for a WHOLE STATEMENT: its parts side by side, the relation symbol between them, in one
    frame.  Two panels a relation symbol joins are one display, so the frame is the statement's and
    never the part's — the deepest part sets it and every shorter one is lined up inside it. -/
def emitStatement (declName : String) (parts : Array (String × Diagram))
    (frame topRow scale : Option Nat) : MetaM String := do
  let ps := parts.map (·.2)
  let ref := ps.foldl (fun a p => if p.rows.size > a.rows.size then p else a) ps[0]!
  let fr := frame.getD (frameOf ref ps)
  -- A frame given from outside is extra HEADROOM, so the reference drops with it and the slides
  -- below it are unchanged: the alignment is what the frame exists to hold.
  let tr := fr - maxShift ref ps - 1
  let mut cells : Array String := #[]
  let mut panels : Array String := #[]
  let mut hs : Array Float := #[]
  for (sym, p) in parts do
    if !sym.isEmpty then cells := cells.push ("text(15pt)[" ++ sym ++ "]")
    cells := cells.push ("panels.at(" ++ toString panels.size ++ ")")
    panels := panels.push
      (← panelCode p declName (some fr) (some (topRow.getD (topOf tr ref p))) scale)
    hs := hs.push (frameHeight p (some fr))
  -- THE GATE.  A part drawn to its own depth would put the relation symbol between two boxes of
  -- different heights, which reads as two displays rather than one statement.
  for i in [1 : hs.size] do
    if hs[i]! != hs[0]! then
      throwError "{declName}: part 1 is drawn {num hs[0]!} tall and part {i + 1} is {num hs[i]!} \
        — a relation symbol joins them into ONE display, so every part takes the statement's frame \
        (the deepest part's row count, plus one)"
  return fileOf declName ("#let panels = (\n  "
    ++ String.intercalate ",\n  " panels.toList ++ ",)\n"
    ++ "#let pic = align(center, grid(columns: " ++ toString cells.size
    ++ ", align: horizon, column-gutter: 6pt,\n  "
    ++ String.intercalate ",\n  " cells.toList ++ "))\n")

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
    -- WHETHER THE ENDS ARE OBJECTS A RELATOR SPELLS IS `verdict`'S QUESTION, asked of the statement
    -- itself and answered with a spider where they are not.  A test on the LANES here refuses the
    -- whole product family `[v]×[[v]]⟶[[v]]` on account of a label, and it is a second reading of
    -- the same thing, which is what let the two disagree.
    try Meta.isTypeCorrect (← Meta.mkLambdaFVars #[v] core) catch _ => pure false

/-- THE FAMILY A BEAD IS, WHERE THE STATEMENT BINDS NO OBJECT TO ABSTRACT.  A bead stands at the
    object its own WIRE carries, and that object is a family's index whether or not the statement
    happens to quantify over it: `𝟙%∋` at an initial algebra's carrier `T` is the very singleton
    `singleton_laxNatural` is about, and reading the index off the binders alone left it a bead
    nothing was claimed about — the same reading `beadLabel` already takes off the bead's own ends.
    So the object is `kabstract`ed out of the term, and TYPE-CORRECTNESS is the filter, exactly as
    it is for a binder: abstracting the object out of `est(R)` strands `R : x⟶x` at the old one and
    the lambda does not type-check, so an arrow AT one object stays an arrow at one object. -/
def familyAt? (regionTy core : Expr) (os : Array Expr) : MetaM (Option Expr) := do
  for o in os do
    unless ← (try Meta.isDefEq (← Meta.inferType o) regionTy catch _ => pure false) do continue
    let body ← Meta.kabstract core o
    unless body.hasLooseBVars do continue
    let φ? ← Meta.withLocalDeclD `a regionTy fun a => do
      let φ ← instantiateMVars (← Meta.mkLambdaFVars #[a] (body.instantiate1 a))
      if ← (try Meta.isTypeCorrect φ catch _ => pure false) then return some φ else return none
    if φ?.isSome then return φ?
  return none

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
  lean : Option Name
  deriving Inhabited

/-- The bead's verdict, from the ENVIRONMENT.  `StrictNatural F G φ` is a solid dot, `LaxNatural`
    a hollow one, a refuted `LaxNatural` the object wire — each of them a proof term the search
    ASSEMBLED and `Meta.check`ed, never a name whose statement merely unified.  Where none of the
    three is proved the bead is a SPIDER: no dot, no claim, and a `nat:` row saying the tool
    looked and found nothing (CLAUDE.md: "a transformation with no naturality proof draws as a
    spider"). -/
def verdict (regionTy : Expr) (cat : Array Name) (core φ : Expr) : MetaM Verdict := do
  -- THE STATEMENT IS READ OFF THE FAMILY, NOT OFF THE LANES.  `φ = fun v => core`, so its two
  -- relators are its own end objects as functions of `v` (`relatorOfObj`) and the proposition
  -- type-checks by construction; a stack of lane labels is a second spelling of the same thing that
  -- can disagree with it, and did.
  -- AN END NO RELATOR SPELLS IS NO FAMILY AT ALL, so it is not a spider either.  A spider says the
  -- tool looked at a naturality statement and found no proof; where one end is `F Unit A`, or the
  -- lane over it is a FUNCTOR and not a relator of the region (`E` under `UnguardedPowerLCDA`,
  -- whose `powerRelator` needs tabularity), there is no statement to look at, and what the bead IS
  -- is an arrow of the base category at this one object — the plain dot on the object wire every
  -- other such bead gets (`Q°`, `est(R)`), and no `nat:` row, because nothing was claimed either
  -- way.  Naming it an error would fail the whole panel over one bead.
  -- WHICH ALGEBRA THE STATEMENT IS IN IS THE REGION'S, not the bead's: §1.241's function category
  -- is a `Cat` and no allegory, so its lanes are functors and its naturality is the plain square.
  -- THE LANES DECIDE WHICH NATURALITY THERE IS TO STATE, and a region can carry both kinds.  An
  -- allegory's lanes are RELATORS and a family between them is graded by `⊑`; but `E`, the
  -- existential image, is a FUNCTOR there and no relator (its `powerRelator` needs tabularity), so
  -- a family under it states the plain SQUARE — read the ends a second time in the functor algebra
  -- rather than calling a bead nothing can be said about.  Same reader both times.
  let alg0 ← laneAlgOf regionTy
  let read : LaneAlg → MetaM (Option (LaneAlg × Expr × Expr)) := fun a =>
    (some <$> (do let (G, F) ← relatorsOf a cat regionTy φ; return (a, G, F))) <|> pure none
  let some (alg, G, F) ← (do match ← read alg0 with
      | some r => pure (some r)
      | none => if alg0 == .relator then read .functor else pure none)
    | return { mark := none, lean := none }
  -- THE FILTER IS THE FAMILY'S CONSTANTS, NOT THE TERM'S AT ITS OBJECT.  A bead taken at an initial
  -- algebra's carrier carries `InitialAlgebra.t` into `core`, and no naturality theorem mentions a
  -- projection of the region's own structure, so filtering on it dropped every candidate there is.
  -- `id` is what separates this `do` from the enclosing one, so a hit `return`s from the search
  -- and not from `verdict`.
  let br ← bridges
  let must ← mustOfFamily br φ
  -- A CATEGORY HAS ONE NATURALITY STATEMENT, THE SQUARE, and no `⊑` to grade it by: there is no
  -- lax, no oplax and no refutation to look for, so a family between functor lanes is the solid
  -- dot its square proves or the spider below — never the object-wire bead a failed RELATOR
  -- reading used to demote it to.
  let search : MetaM (Option Verdict) := match alg with
    | .functor => id do
      if let some (n, _) ← findTelescoped br (← laneSquare alg regionTy F G φ) must FUEL then
        return some { mark := some .strict, lean := n }
      -- THE SQUARE OVER THE MAPS, where the region HAS maps to restrict to.  `𝟙%∋ : 𝟙 ⟹ E` is
      -- natural there and at no relation (`singletonMap_natural`, whose `Map f` this square binds
      -- and `discharge` reads back), and so is every other family of maps between functor lanes of
      -- an allegory; asking only the unrestricted square left all of them with no claim at all.
      if alg0 == .relator then
        if let some (n, _) ← findTelescoped br (← laneSquare alg regionTy F G φ .strict true)
            must FUEL then
          return some { mark := some .strict, lean := n }
      return none
    | .relator => id do
      let strict ← Meta.mkAppM ``Freyd.Alg.StrictNatural #[F, G, φ]
      let lax ← Meta.mkAppM ``Freyd.Alg.LaxNatural #[F, G, φ]
      let oplax ← Meta.mkAppM ``Freyd.Alg.OpLaxNatural #[F, G, φ]
      -- The refutation is of the very statement just searched for, `¬ LaxNatural F G φ`, and not
      -- of one with the two relators swapped: `φ a : G.obj a ⟶ F.obj a`, so a swapped statement is
      -- not even well typed unless the bead happens to end where it starts.
      let nolax ← Meta.mkAppM ``Not #[lax]
      if let some (n, _) ← findProof br strict ``Freyd.Alg.StrictNatural {} FUEL then
        return some { mark := some .strict, lean := n }
      -- THE SQUARE IS BUILT, NOT REACHED BY UNFOLDING THE CLASS, for the reason `laneSquare` gives:
      -- `LaxNatural F G φ` spells the lane stack's action as the COMPOSITE relator's `map`, and
      -- every hand-written square in the repo spells it wire by wire (`tupleP 3 (tupleP n S)`), so
      -- the unfolded class matched none of them and every `RelSet.graph` bead of the cylinder came
      -- back a spider.  Same builder as the functor algebra's, one grade apart.
      if let some (n, _) ← findTelescoped br (← laneSquare alg regionTy F G φ) must FUEL then
        return some { mark := some .strict, lean := n }
      if let some (n, _) ← findProof br lax ``Freyd.Alg.LaxNatural {} FUEL then
        return some { mark := some .lax, lean := n }
      if let some (n, _) ← findTelescoped br (← laneSquare alg regionTy F G φ .lax) must FUEL then
        return some { mark := some .lax, lean := n }
      -- The CONVERSE of a lax family is not lax, it is lax the other way (`laxNatural_recip`), so
      -- `OplaxNatural` is asked before the refutation: `prefix°` is not a spider, it is a hollow dot
      -- whose square points the other way, and the `nat:` row is where the direction is written.
      -- The CLASS only, not the square: nothing in the repo states a raw oplax inequation, so
      -- unfolding it would scan every `⊑` in the environment for a shape only `laxNatural_recip`
      -- ever produces — and that closure's own hypothesis IS searched as a square, through
      -- `discharge`.  A whole extra sweep per bead is what the H panels' budget cannot pay.
      if let some (n, _) ← findProof br oplax ``Freyd.Alg.OpLaxNatural {} FUEL then
        return some { mark := some .oplax, lean := n }
      if let some (n, _) ← findProof br nolax ``Not must FUEL then
        return some { mark := none, lean := n }
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
  -- NO VERDICT, NO DOT, NO CLAIM.  The three statements are what was looked for and none of them
  -- is proved, so the bead draws as the book's spider (IntroString §2.2.4) — a node with no mark —
  -- rather than the panel failing or, worse, a dot standing for a naturality nobody has.
  return found.getD { mark := some .spider, lean := none }

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

    ONLY WHERE THE HEAD IS A BINDER.  A CONSTANT's spelling is its own unexpander's business, and
    that unexpander matches the term as APPLIED — cutting the object argument out from under it
    stops it firing, and the label comes out worse than the one it was meant to fix (`prefixR A`
    became `@ListRel.prefixR`, `𝟙 (dSched X)` became `𝟙dSched`).  A constant that wants its index
    dropped drops it in its own rule, beside itself.

    THE OBJECT IS WHATEVER THE WIRE UNDER THE BEAD CARRIES, not only a binder of the statement.
    `moves I.t` in an abstract module is taken at the initial type, which is no binder of the
    region, and the label came out `movesT` — the object wire's own `T` spelled a second time. So
    the objects stripped are the bead's own two ends as well as the family variable, compared up to
    `isDefEq` because the end comes back rebuilt from its projection. -/
def beadLabel (core : Expr) (vs : Array Expr) : MetaM String := do
  label (← Meta.transform core (post := fun x => match x with
    | .app f a =>
      if f.getAppFn.isFVar then
        return if ← vs.anyM (Meta.isDefEq a) then .done f else .continue
      else return .continue
    | _ => return .continue))

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
  let v? ← familyVar core objVars
  let φ ← match v? with
    | some v => some <$> familyOf regionTy v core
    | none => familyAt? regionTy core #[oy, ox]
  let vd ← match φ with
    | none => pure none
    | some φ => some <$> verdict regionTy cat core φ
  let ar := Array.mk (List.range arms.size)
  let ov := Array.mk (List.range' arms.size over.size)
  let lg := Array.mk (List.range' (arms.size + over.size) legs.size)
  -- A unit is a FAMILY `𝟙 ⟹ W` THE ENVIRONMENT PROVES: a fixed arrow `A ⟶ F A` (`S°`) is a bead
  -- with a leg, not a lane, and so is one whose family the environment neither proves nor can even
  -- state — heading a lane with it claims the transformation IS the unit, which is the dot the
  -- spider exists to withhold.  `∈ ≜ ∋°` is that bead: the same shape as the singleton `𝟙%∋`, and
  -- only the verdict tells them apart.
  let proved := match vd.bind (·.mark) with
    | some .strict | some .lax | some .oplax => true
    | some .spider | none => false
  let unit := arms.isEmpty && legs.size == 1 && proved && (← Meta.isDefEq ox oy)
  let row : Row :=
    { label := (← beadLabel core (#[ox, oy] ++ v?.toArray)), arms := ar, legs := lg, over := ov,
      unit, obj := (← plain oy),
      src := { ws := arms, o := ox }, tgt := { ws := legs, o := oy },
      nat := vd.bind (·.mark), natLean := vd.bind (·.lean) }
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
      starts at `{← edge e e.top e.otop}`"
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
  let obj ← plain e.otop
  let drows := d.rows.map fun r =>
    { r with arms := r.arms.map dmap, legs := r.legs.map dmap, over := r.over.map dmap, obj }
  let rows := drows ++ e.rows.map fun r =>
    { r with arms := r.arms.map emap, legs := r.legs.map emap, over := r.over.map emap }
  return { lanes, rows, top := Array.mk (List.range (nt + mt)),
           bot := d.bot.map dmap ++ e.bot.map emap, otop := e.otop, obot := e.obot }

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
    (vpass : Array Wire) (e : Expr) : MetaM Diagram := do
  -- A constant the note draws OPENED is opened first, so the picture is of the body the note
  -- writes and not of one bead carrying the name Lean prints.
  let e' ← openNoted e
  if e' != e then return ← interp regionTy cat objVars vpass e'
  let fs := factors e
  if fs.size > 1 then
    let mut d ← interp regionTy cat objVars vpass fs[0]!
    for i in [1 : fs.size] do
      d ← d.vcomp (← interp regionTy cat objVars vpass fs[i]!)
    return d
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      let ws := (wiresOf args[4]!).map Wire.rel
      let d ← interp regionTy cat objVars (vpass ++ ws) args[args.size - 1]!
      return ← (← Diagram.id ws d.otop).beside d
  -- AN IDENTITY IS NO BEAD: `𝟙` is the bare wire, so its picture is the lanes it runs on with
  -- nothing drawn on them.  On the HEAD, so every identity of every object goes the same way.
  | (``Cat.id, _) =>
    let (x, _) ← homEnds e
    let (cx, ox) ← peelCuts objVars cat regionTy x
    return ← Diagram.id (cx.map (·.1)) ox
  | _ => pure ()
  if let some (φ, ψ) ← asProdMap? regionTy e then
    -- The head constant is how a factor of `φ` is paired back with `𝟙` — the notation the
    -- declaration is written in, and no string surgery.
    let .const n _ := e.getAppFn
      | throwError "the product map `{← plain e}` is headed by no constant, so its left factor \
          cannot be paired back with `𝟙`"
    let (a, a') ← homEnds φ
    let (b, _) ← homEnds ψ
    -- `𝟙×ψ` IS `(A×−).map ψ`: the left factor is one lane and `ψ` runs under it, so this is the
    -- `F.map` route and the verdict of `ψ` closes through the same chain as any `F(R)`.
    if ← isIdArrow φ then
      let l := Wire.timesL a
      let d ← interp regionTy cat objVars (vpass.push l) ψ
      return ← (← Diagram.id #[l] d.otop).beside d
    let one ← Meta.mkAppM ``Cat.id #[b]
    -- Interchange, `φ×ψ = (φ×𝟙)(𝟙×ψ)`, and functoriality, `(φ₁φ₂)×𝟙 = (φ₁×𝟙)(φ₂×𝟙)`: both split
    -- the map into product maps this same case then draws, one bead each.
    let fφ := factors φ
    if !(← isIdArrow ψ) || fφ.size > 1 then
      let mut parts : Array Expr := #[]
      for f in fφ do parts := parts.push (← Meta.mkAppM n #[f, one])
      unless ← isIdArrow ψ do parts := parts.push (← Meta.mkAppM n #[← Meta.mkAppM ``Cat.id #[a'], ψ])
      if parts.size > 1 then
        let mut d ← interp regionTy cat objVars vpass parts[0]!
        for i in [1 : parts.size] do d ← d.vcomp (← interp regionTy cat objVars vpass parts[i]!)
        return d
    -- `φ×𝟙` is ONE bead on the left factor's lane, `A×− ⇒ A'×−`, ONLY where it is a family in the
    -- statement's own object: the lanes east of it are then what that object is, and only run past.
    -- Where `φ` cannot vary with it — `secure amount N`, whose `amount` pins the object — the whole
    -- `φ×𝟙` is ONE arrow, it rides the object wire like `α` and `⦇R⦈`, and its arrow is every lane
    -- its bar spans, which is what the tail below types it as.
    if (← familyVar e objVars).isSome then
      let (cx, ox) ← peelCuts objVars cat regionTy (← homEnds e).1
      let (_, oy) ← peelCuts objVars cat regionTy (← homEnds e).2
      return ← Diagram.bead regionTy cat objVars #[Wire.timesL a] #[Wire.timesL a'] ox oy e
        (over := (cx.extract 1 cx.size).map (·.1))
  -- A RELATOR'S ACTION IS THE `F.map` ROUTE WHATEVER IT IS SPELLED: `list (Λ(R) est(Q))` is that
  -- composite drawn under the `list` wire, two beads, not one bead nobody can read the run inside
  -- of.  Last, so a factor the reader already has a form for keeps it.
  if let some (R, r) ← peelMap? cat objVars regionTy e then
    let ws := (wiresOf R).map Wire.rel
    let d ← interp regionTy cat objVars (vpass ++ ws) r
    return ← (← Diagram.id ws d.otop).beside d
  let (x, y) ← homEnds e
  let (cx, ox) ← peelCuts objVars cat regionTy x
  let (cy, oy) ← peelCuts objVars cat regionTy y
  let ax := cx.map (·.1)
  let ay := cy.map (·.1)
  -- THE LANES UNDER A BEAD RUN PAST IT INSIDE.  A family `φ : G a ⟶ H a` taken at `a := F' A` acts
  -- on `G` alone, and `F'` is the object it is taken at: the inner stack the two ends share is what
  -- the bead stands over, when the bead depends on the statement's objects through that object
  -- ONLY — `𝟙%∋` at `F A` opens the `E` lane beside `F` and eats nothing, where `cons` at `A`, a
  -- family in `A` itself, eats every lane of `[A]×[[A]]`.
  -- With NO lane shared the object itself is what the bead may be a family in: `𝟙%∋` at the
  -- type functor's carrier `T`, an object no wire spells, is the same unit as at `F A`.
  if ← Meta.isDefEq ox oy then
    let mut k := 0
    while k < ax.size && k < ay.size do
      unless ← Wire.beq ax[ax.size - 1 - k]! ay[ay.size - 1 - k]! do break
      k := k + 1
    let x' := if k == ax.size then x else cx[ax.size - k - 1]!.2
    let y' := if k == ay.size then y else cy[ay.size - k - 1]!.2
    if (← Meta.isDefEq (← Meta.inferType x') regionTy) && (← Meta.isDefEq x' y') then
      let e' ← Meta.kabstract e x'
      if e'.hasLooseBVars && !objVars.any (fun v => e'.containsFVar v.fvarId!) then
        -- A family only where the abstraction TYPE-CHECKS: `S°` at `A` abstracts its `A` too,
        -- but `S : F A ⟶ A` pins it, and the result is no arrow of any object.
        let d? ← Meta.withLocalDeclD `a regionTy fun a => do
          let ea := e'.instantiate1 a
          unless ← Meta.isTypeCorrect ea do return none
          some <$> Diagram.bead regionTy cat #[a] (ax.extract 0 (ax.size - k))
            (ay.extract 0 (ay.size - k)) ox oy ea (over := ax.extract (ax.size - k) ax.size)
        if let some d := d? then return d
  Diagram.bead regionTy cat objVars ax ay ox oy e

/-- ONE STEP OF THE SELECTOR CHAIN that goes inside a side: an operand of a binary operation, an arm
    of a junction, or the BODY of a least fixed point.  `.body` opens a BINDER, so the chain cannot
    be a list of operand indices: the bound arrow is a wire of the picture, and a number says
    nothing about where in the chain that wire is opened. -/
inductive Sel where | inl | inr | body
  deriving Inhabited, DecidableEq

/-- The suffix the selector is written with — what `diag-export` parses and names the file by. -/
def Sel.suffix : Sel → String
  | .inl => ".inl" | .inr => ".inr" | .body => ".body"

/-- The function a least fixed point is taken of, `mu φ`, by the HEAD CONSTANT. -/
def muArg? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.mu, args) => args.back?
  | _ => none

/-- One side of a statement, as a panel: its picture, with the bottom edge's lanes told how deep the
    picture turned out to be.  A SIDE IS REWRITTEN ONCE, HERE, along its spine and before the read:
    `Λ S` is drawn as the note draws it — the unit bead and `S` on the `E` lane — and a side is what
    a rewrite is a statement about, so it is applied at the top and never inside `interp`. -/
def panelOf (regionTy : Expr) (cat : Array Name) (side : Expr) (objVars : Array Expr) :
    MetaM Diagram := do
  let d ← interp regionTy cat objVars #[] (← instantiateMVars (← rewriteSpine side))
  let n : Int := d.rows.size
  return { d with lanes := d.lanes.map fun l => if l.dies == LIVE then { l with dies := n } else l }

/-- The selectors applied in order, with the REST OF THE READ run under whatever locals they open.
    `.body` instantiates the least fixed point's binder with a local of that binder's own name, and
    the picture draws that local as a wire and prints it by that name — so the panel has to be built
    while the local is still in scope, which is why this takes a continuation instead of handing an
    expression back. -/
partial def withSel {α : Type} [Inhabited α] (regionTy : Expr) (sel : List Sel) (e : Expr)
    (k : Expr → MetaM α) : MetaM α := do
  match sel with
  | [] => k e
  | .inl :: rest => withSel regionTy rest (← branchOf regionTy e 0) k
  | .inr :: rest => withSel regionTy rest (← branchOf regionTy e 1) k
  | .body :: rest =>
    let some φ := muArg? e
      | throwError "`.body` names the body of a least fixed point, and `{← plain e}` is not one"
    Meta.lambdaBoundedTelescope φ 1 fun xs b => do
      unless xs.size == 1 do
        throwError "`{← plain φ}` binds no arrow, so `.body` opens no wire to draw the body on"
      withSel regionTy rest b k

/-- Every part of the statement drawn, each under its own selectors' locals, and the file emitted
    inside all of them: a bead's ends are printed from the `Expr`, so a local opened for one part is
    still needed when the last part's panel is written out. -/
partial def withParts {α : Type} [Inhabited α] (regionTy : Expr) (cat : Array Name)
    (objVars : Array Expr) (sel : List Sel) (drawn : List (String × Expr))
    (acc : Array (String × Diagram)) (k : Array (String × Diagram) → MetaM α) : MetaM α :=
  match drawn with
  | [] => k acc
  | (sym, e) :: rest =>
    withSel regionTy sel e fun e' => do
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

/-- `--string <Name>[#<binder>][.lhs|.rhs][.inl|.inr…]`.  A `def` is drawn by its BODY unfolded one
    level; a HYPOTHESIS IS A STATEMENT TOO, so `#h` draws that binder's type instead of the
    conclusion, and a `def`'s body is then not unfolded because the binder belongs to the type.

    A statement is drawn WHOLE — both sides in one frame — or one side at a time; either way every
    side is read, because the frame is a property of the statement and a side alone cannot know how
    deep the other one is.  The path names the statement, so `.lhs` on an `↔` draws the whole left
    statement and only a trailing name on a relation picks a side. -/
def drawString (declName : Name) (path : List String) (binder : Option String) (sel : List Sel)
    (frame topRow scale : Option Nat) (sigsOf : Option String := none) : MetaM Drawn :=
    -- THE BUDGET COVERS THE WHOLE READ, not the search inside it.  A budget lifted only around the
    -- searches lapses the moment they return, and what the panel does NEXT — printing each bead's
    -- ends — then runs on an allowance the searches have already spent, so the read dies naming an
    -- `isDefEq` that is not the expensive one.  `CANDIDATE_HEARTBEATS` bounds each match tried and
    -- `scripts/cap` bounds the process; nothing between them needs an allowance of its own.
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    withDeclScope declName do
  let env ← getEnv
  let some ci := env.find? declName | throwError "no such declaration: {declName}"
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
  let stmt ← stmtTelescope ci.type fun xs body => do
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
        pure <| if isDef then
            match ci.value? with
            | some v => (mkAppN v xs).headBeta
            | none => body
          else body
    Meta.mkForallFVars xs body
  stmtTelescope stmt fun xs body => do
    -- A PATH NAMES A STATEMENT; a TRAILING SIDE NAME picks one part of it.  `relCata_UP` is an `↔`
    -- between two inequations, so `.lhs` names the left inequation and draws it whole — both parts
    -- in one frame — and `.lhs.lhs` goes on to that inequation's left part alone.  A step descends
    -- while what it lands on is still a statement built from statements (`conn?`); the first step
    -- that is not names a part, and nothing can follow it.
    let mut body := body
    let mut side : Option String := none
    for s in path do
      match side, conn? body with
      | none, some (l, r) => body := if s == "lhs" then l else r
      | none, none => side := some s
      | some p, _ =>
        throwError "`.{s}` follows `.{p}`, which already names a part of \
          {← Meta.ppExpr body}: a part has no sides of its own"
    -- The statement's PARTS: the two sides a relation symbol joins, or the arrow itself.
    let parts : Array (String × Expr) := match split body with
      | some (sym, l, r) => #[("", l), (sym, r)]
      | none => #[("", body)]
    let arrow := parts[0]!.2
    -- The OBJECT VARIABLES of the statement: a factor mentioning one is a family, and only a
    -- family can carry a dot.  A binder counts when it is an object of the region — or, where the
    -- region is a ONE-FIELD STRUCTURE over an index type, when it is that INDEX: `X : Type`
    -- names the object `⟨X⟩ : RelSet`, `dE X` IS that object, and `⟨a.carrier⟩` is `a`, so the
    -- two readings are one family and `StrictNatural F G φ` is a statement about it after all.
    let (src, _) ← homEnds arrow
    let regionTy ← Meta.inferType src
    let cat ← catalogue
    let idxTy ← regionIndexType? regionTy
    let mut objVars : Array Expr := #[]
    for x in xs do
      let t ← Meta.inferType x
      if ← Meta.isDefEq t regionTy then objVars := objVars.push x
      else if let some it := idxTy then
        if ← Meta.isDefEq t it then objVars := objVars.push x
    -- `.inl`/`.inr` is ONE BRANCH of the side, and the selectors CHAIN: each names an operand of
    -- the binary operation what the one before it left is, outermost first.  What that operation
    -- is — a union, a meet, a junction over a coproduct — is read off the run's type by
    -- `branchOf`, and the object variables are the statement's own either way.
    let drawn : Array (String × Expr) ← match side with
      | none => pure parts
      | some s =>
        if parts.size < 2 then throwError "{declName} has no two sides to draw one of"
        else pure #[("", if s == "lhs" then parts[0]!.2 else parts[1]!.2)]
    withParts regionTy cat objVars sel drawn.toList #[] fun ps => do
      let sigs ← match sigsOf with | some s => sigRecords s (ps.map (·.2)) | none => pure #[]
      let nm := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
        ++ path.foldl (fun a s => a ++ "." ++ s) ""
        ++ sel.foldl (fun s x => s ++ x.suffix) ""
      -- A PART EMITTED ALONE STANDS BESIDE NOTHING, so it takes its OWN depth.  The shared frame
      -- exists to hold the parts a relation symbol joins in ONE grid to one box and one bead
      -- height; a calc-table row holding only `.rhs` has no such neighbour, and giving it the whole
      -- statement's frame drew it taller than the picture beside it.
      let text ← if ps.size == 1 then emit ps[0]!.2 nm frame topRow scale
        else emitStatement nm ps frame topRow scale
      return Drawn.mk text sigs

end Freyd.StrDiag
