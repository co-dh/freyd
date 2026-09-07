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

/-- One wire, from the bead that makes it to the bead that eats it.  `born = -1` is the top edge,
    `dies = rows.size` the bottom one. -/
structure Lane where
  label : String
  born  : Int
  dies  : Int
  x     : Float := 0.0
  pad   : Float := 0.0
  deriving Inhabited

/-- One bead: what it eats, what it makes, what the object wire carries below it, and whether a
    declaration says it is natural. -/
structure Row where
  label : String
  arms  : Array Nat
  legs  : Array Nat
  obj   : String
  /-- What the bead is an arrow BETWEEN, its `core`'s hom ends in the note's notation.  The panel
      states it so `scripts/scanline` checks the drawn type against Lean's and not against `x⟶x`. -/
  sig   : String := ""
  nat   : Option String := none
  /-- The declaration the verdict was read off — the panel's own citation for its dots, and for a
      bead the environment REFUTES, which draws no dot and is a claim all the same. -/
  natLean : Option Name := none
  deriving Inhabited

structure Panel where
  lanes : Array Lane
  rows  : Array Row
  otop  : String
  obot  : String
  deriving Inhabited

/-! ### `columns` — how far apart the lanes sit -/

def minA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b < a then b else a) dflt
def maxA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b > a then b else a) dflt

/-- A column per lane.  The top-born lanes take the grid; a bead's legs are a contiguous `DX` block
    CENTRED on the arms it replaces, slid by half steps until it fits between the arms' own
    neighbours, so a lane west of the arms stays west of the legs. -/
def columns (p : Panel) : Array Lane := Id.run do
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
    -- would cross each of them on the way out.
    let c := if arms.isEmpty then
        (maxA (Array.mk (live.map (fun j => (xs[j]!).get!))) (-DX)) + DX
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
def framex (p : Panel) : Nat := max p.rows.size 1 + 1

/-- The frame's height in cetz units.  The panel and the gate in `emitStatement` both read THIS,
    so the gate measures the box that is drawn and not a second copy of the rule. -/
def frameHeight (p : Panel) (frame : Option Nat) : Float := (frame.getD (framex p)).toFloat * DY

/-- The `dpanel(...)` call this panel is.  `frame` and `top` are ROW COUNTS, the two halves of
    lining a short panel up with a tall one: the frame gives them one box, the top one bead
    height.  Left off, the frame is one row deeper than the panel and the first bead sits at the
    top of it. -/
def panelCode (p : Panel) (declName : String) (frame topRow scale : Option Nat) : String := Id.run do
  let n := p.rows.size
  let ls := columns p
  let nr := frame.getD (framex p)
  let hh := frameHeight p frame
  let t0n := topRow.getD n
  let t0 := t0n.toFloat
  let ys : Array Float := Array.mk ((List.range n).map fun i => (t0 - i.toFloat) * DY)
  let xo := roundTo 2 (maxA (ls.map (·.x)) X0 + DX)
  let cell (s : String) : String := "[`" ++ s ++ "`]"
  let str (s : String) : String := "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  let mut beads : Array String := #[]
  let mut objs : Array String := #[]
  let mut nats : Array String := #[]
  for i in [0 : n] do
    let r := p.rows[i]!
    -- A bead with NO arms stands on the object wire and its legs bend OUT of it, so it writes no
    -- x fields: a reach taken from the legs draws it on the very wire it creates.
    let xsr := r.arms.map fun j => ls[j]!.x
    let reach : Option Float := if xsr.isEmpty then none else some (minA xsr 1e9)
    let dot : Option Float :=
      if xsr.isEmpty || r.nat.isNone then none
      else some (roundTo 4 ((minA xsr 1e9 + maxA xsr (-1e9)) / 2.0))
    -- The 6th element is the MARK: `"lax"` a hollow dot, `"spider"` no dot at all.
    let mark := match r.nat with
      | some "lax" => ", \"lax\"" | some "spider" => ", \"spider\"" | _ => ""
    beads := beads.push <| match reach, dot with
      | none, _ => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ")"
      | some rc, none => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ")"
      | some rc, some d =>
        "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ", " ++ num d
          ++ mark ++ ")"
    objs := objs.push ("(" ++ num ys[i]! ++ ", " ++ cell r.obj ++ ")")
    -- Every FAMILY the tool looked at gets a row, the spider included: a reader must be able to
    -- see that the search ran and came back empty, which an absent row cannot say.
    if r.nat.isSome || r.natLean.isSome then
      nats := nats.push
        ("(" ++ str r.label ++ ", " ++ str (r.nat.getD "not-lax") ++ ", "
          ++ str ((r.natLean.map Name.toString).getD "") ++ ")")
  let lanecode : Lane → String := fun l =>
    let birth := if l.born < 0 then "\"top\"" else num ys[l.born.toNat]!
    let death := if l.dies >= (n : Int) then "\"bot\"" else num ys[l.dies.toNat]!
    let nm := if l.born < 0 || l.dies >= (n : Int) then "none" else cell l.label
    "(" ++ num l.x ++ ", " ++ birth ++ ", " ++ death ++ ", " ++ nm ++ ", none)"
  let tup (xs : Array String) : String :=
    "(" ++ String.intercalate ", " xs.toList ++ (if xs.size == 1 then "," else "") ++ ")"
  let top := (ls.filter (·.born < 0)).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell p.otop ++ ")")
  let bot := (ls.filter (·.dies >= (n : Int))).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell p.obot ++ ")")
  "dpanel(" ++ num hh ++ ", " ++ num (roundTo 2 (xo + PAD)) ++ ", " ++ num xo ++ ",\n  "
    ++ tup (ls.map lanecode) ++ ",\n  " ++ tup beads ++ ",\n  " ++ tup top ++ ",\n  " ++ tup bot
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
   #import \"../../dpanel.typ\": *\n\n" ++ body

/-- One panel on its own — one side of a statement, or one branch of a side. -/
def emit (p : Panel) (declName : String) (frame topRow scale : Option Nat) : String :=
  fileOf declName ("#let pic = " ++ panelCode p declName frame topRow scale ++ "\n")

/-- `--string --sigs`: what LEAN says each bead is an arrow between, one line
    `<panel>\t<label>\t<src>⟶<tgt>` per bead, the panels numbered as the file emits them.  Nothing
    is written into the picture: `scripts/scanline` asks this at check time, so the types it holds
    the ink to are the environment's and cannot go stale in a file. -/
def sigLines (ps : Array Panel) : String := Id.run do
  let mut out := ""
  for i in [0 : ps.size] do
    for r in ps[i]!.rows do
      out := out ++ toString (i + 1) ++ "\t" ++ r.label ++ "\t" ++ r.sig ++ "\n"
  return out

/-- Where a part's first bead sits, in rows.  The deepest part's sits one row below the ceiling; a
    shorter part slides until a bead it SHARES with that part stands at the same height, which is
    the alignment `diagram --pairs` holds a display to.  Labels are compared whole, as that gate
    compares them: a bead is the same bead when it is the same 2-cell. -/
def topOf (frame : Nat) (ref p : Panel) : Nat :=
  let t : Int := (frame : Int) - 1
  let shift : Int := Id.run do
    for j in [0 : p.rows.size] do
      for i in [0 : ref.rows.size] do
        if ref.rows[i]!.label == p.rows[j]!.label then return (j : Int) - (i : Int)
    return 0
  (max (min (t + shift) t) (p.rows.size : Int)).toNat

/-- One file for a WHOLE STATEMENT: its parts side by side, the relation symbol between them, in one
    frame.  Two panels a relation symbol joins are one display, so the frame is the statement's and
    never the part's — the deepest part sets it and every shorter one is lined up inside it. -/
def emitStatement (declName : String) (parts : Array (String × Panel))
    (frame topRow scale : Option Nat) : MetaM String := do
  let ps := parts.map (·.2)
  let fr := frame.getD (ps.foldl (fun a p => max a (framex p)) 2)
  let ref := ps.foldl (fun a p => if p.rows.size > a.rows.size then p else a) ps[0]!
  let mut cells : Array String := #[]
  let mut hs : Array Float := #[]
  for (sym, p) in parts do
    if !sym.isEmpty then cells := cells.push ("text(15pt)[" ++ sym ++ "]")
    cells := cells.push (panelCode p declName (some fr) (some (topRow.getD (topOf fr ref p))) scale)
    hs := hs.push (frameHeight p (some fr))
  -- THE GATE.  A part drawn to its own depth would put the relation symbol between two boxes of
  -- different heights, which reads as two displays rather than one statement.
  for i in [1 : hs.size] do
    if hs[i]! != hs[0]! then
      throwError "{declName}: part 1 is drawn {num hs[0]!} tall and part {i + 1} is {num hs[i]!} \
        — a relation symbol joins them into ONE display, so every part takes the statement's frame \
        (the deepest part's row count, plus one)"
  return fileOf declName ("#let pic = align(center, grid(columns: " ++ toString cells.size
    ++ ", align: horizon, column-gutter: 6pt,\n  "
    ++ String.intercalate ",\n  " cells.toList ++ "))\n")

/-! ### The functor: an arrow of the allegory as a panel

  A factor is read by its TYPE.  Strip the relators it runs under (`F.map R` is `R` with `F`'s wire
  running past), then its own source and target say which wires it eats and which it makes: the
  stack they share below the change is untouched, everything above it dies and is reborn. -/

/-- Still live: a lane the walk has not yet seen eaten. -/
private def LIVE : Int := -2

/-- Whether this factor is a FAMILY in the region's object, and so a candidate 2-cell at all: its
    two ends stand over the SAME object and it varies with that object.  `α : F(T)⟶T` at an initial
    algebra's carrier does not vary — `T` is one object, not a parameter — and `⦇R⦈ : T⟶A` does not
    even stand over one, so both are 2-cells between CONSTANT 1-cells `𝟏 → 𝒜`, which is the object
    wire.  `αᴀ : F(⟨𝟙,T⟩(A))⟶T(A)` does, which is why the two come out different by construction.

    A WIRE that mentions the object rules the bead out too: a lane is a relator of the WHOLE
    region, so `α : F(A,TA) ⟶ TA` read with its source peeled to `F(A,−)` runs on a lane that is
    a different functor at each `A` and states no naturality at all.  The packing `⟨𝟙,T⟩` then `F`
    is what gives that same bead lanes it can be a family over; where no packed relator exists —
    `F Unit A`, the base functor with the element type baked in — the bead is an arrow at one
    object and carries no dot.

    ABSTRACTABLE over the object, not merely MENTIONING it: `S° : b⟶F(b)` names `b` only through
    the type of the local `S : F(b)⟶b`, so `fun b => S°` is ill-typed and `S` is one arrow. -/
def familyVar (core oX : Expr) (objVars : Array Expr) (wires : Array Wire) : MetaM (Option Expr) :=
  objVars.findM? fun v => do
    unless core.containsFVar v.fvarId! && oX.containsFVar v.fvarId!
        && !wires.any (Wire.mentions v.fvarId!) do
      return false
    try Meta.isTypeCorrect (← Meta.mkLambdaFVars #[v] core) catch _ => pure false

/-- How deep a chain of CLOSURE theorems a compound bead's verdict may be read through:
    `strictNatural_prod` over `strictNatural_recip` over the square `cons_natural` states — the
    three `𝟙 Tx × cons°` needs, and the deepest bead the note draws.  Bounded because the search is
    over the whole environment at every step, so each step multiplies the scan. -/
def FUEL : Nat := 3

/-- What the environment says about a bead: the mark it draws — `"strict"`, `"lax"`, `"spider"`
    where nothing is proved either way, or none where the family is REFUTED and the bead rides the
    object wire — and the declaration that says so, which a spider has none of. -/
structure Verdict where
  mark : Option String
  lean : Option Name
  deriving Inhabited

/-- The bead's verdict, from the ENVIRONMENT.  `StrictNatural F G φ` is a solid dot, `LaxNatural`
    a hollow one, a refuted `LaxNatural` the object wire — each of them a proof term the search
    ASSEMBLED and `Meta.check`ed, never a name whose statement merely unified.  Where none of the
    three is proved the bead is a SPIDER: no dot, no claim, and a `nat:` row saying the tool
    looked and found nothing (CLAUDE.md: "a transformation with no naturality proof draws as a
    spider"). -/
def verdict (regionTy : Expr) (armsW legsW : Array Wire) (core v : Expr) (label : String) :
    MetaM Verdict := do
  let φ ← familyOf regionTy v core
  -- The three statements have to be BUILDABLE before they can be searched for: a wire that is not
  -- a `Relator` — a bifunctor applied to two arrows, say — has no `StrictNatural` to state, and
  -- saying so names the bead instead of leaving an elaboration error to stand for it.
  let some G ← (some <$> stackRelator regionTy armsW) <|> pure none
    | throwError "the bead `{label}` runs under wires that are not relators, so there is no \
      naturality statement to look for: {← (armsW.foldl (· ++ ·.lanes) #[]).mapM Wire.label}"
  let some F ← (some <$> stackRelator regionTy legsW) <|> pure none
    | throwError "the bead `{label}` makes wires that are not relators, so there is no \
      naturality statement to look for: {← (legsW.foldl (· ++ ·.lanes) #[]).mapM Wire.label}"
  let must := consts core
  let strict ← Meta.mkAppM ``Freyd.Alg.StrictNatural #[F, G, φ]
  let lax ← Meta.mkAppM ``Freyd.Alg.LaxNatural #[F, G, φ]
  -- The refutation is of the very statement just searched for, `¬ LaxNatural F G φ`, and not of
  -- one with the two relators swapped: `φ a : G.obj a ⟶ F.obj a`, so a swapped statement is not
  -- even well typed unless the bead happens to end where it starts.
  let nolax ← Meta.mkAppM ``Not #[lax]
  -- `id` is what separates this `do` from the enclosing one, so a hit `return`s from the search
  -- and not from `verdict`.
  let br ← bridges
  let found : Option Verdict ← id do
      if let some (n, _) ← findProof br strict ``Freyd.Alg.StrictNatural {} FUEL then
        return some { mark := some "strict", lean := n }
      if let some (n, _) ← findSquare br strict must FUEL then
        return some { mark := some "strict", lean := n }
      if let some (n, _) ← findProof br lax ``Freyd.Alg.LaxNatural {} FUEL then
        return some { mark := some "lax", lean := n }
      if let some (n, _) ← findSquare br lax must FUEL then
        return some { mark := some "lax", lean := n }
      if let some (n, _) ← findProof br nolax ``Not must FUEL then
        return some { mark := none, lean := n }
      return none
  -- NO VERDICT, NO DOT, NO CLAIM.  The three statements are what was looked for and none of them
  -- is proved, so the bead draws as the book's spider (IntroString §2.2.4) — a node with no mark —
  -- rather than the panel failing or, worse, a dot standing for a naturality nobody has.
  return found.getD { mark := some "spider", lean := none }

/-- What one factor does to the stack: how many lanes run past it on the OUTSIDE, the lanes it
    eats, the lanes it makes, and the arrow itself. -/
structure RowSpec where
  pass  : Array Wire
  /-- The wires the VERDICT composes outside the bead.  A relator the bead runs under is part of
      its naturality statement; the `×` and the sibling bundle of a product are only drawn past it. -/
  vpass : Array Wire := #[]
  arms  : Array Wire
  legs  : Array Wire
  core  : Expr
  /-- What the bead is LABELLED and TYPED as.  `core` itself, except where a sibling bundle runs
      east of it: the bar then spans that bundle too, and what the bar is, is `core×𝟙`. -/
  shown : Expr
  /-- The sibling lanes the bar runs over, east of the arms and west of the object wire. -/
  east  : Array Wire := #[]
  deriving Inhabited

/-- The rows of `φ` re-read as rows of `φ×𝟙`, `e` being the product map they were cut from and
    `east` the sibling bundle the bar runs over.  The `𝟙` is built with `e`'s OWN head constant, so
    the label is spelled by the notation the declaration is written in and by no string surgery;
    `core` is untouched, since the naturality the dot claims is still `φ`'s own. -/
def underProd (e ψ : Expr) (east : Array Wire) (rs : Array RowSpec) : MetaM (Array RowSpec) := do
  if (east.foldl (· ++ ·.lanes) #[]).isEmpty then return rs
  let .const n _ := e.getAppFn
    | throwError "the product map `{← plain e}` is headed by no constant, so the bar over it \
        cannot be spelled `×𝟙`"
  let i ← Meta.mkAppM ``Cat.id #[(← homEnds ψ).1]
  rs.mapM fun r => do
    let shown ← try Meta.mkAppM n #[r.shown, i] catch ex =>
      throwError "`{n}` does not take `{← plain r.shown}` and `{← plain i}` as its two arrows, so \
        the bar over `{← plain e}` cannot be labelled: {ex.toMessageData}"
    return { r with shown, east := r.east ++ east }

/-- The rows a factor is.  A factor is taken apart until what is left acts on ONE contiguous block
    of lanes, and the parts that are identities are what runs past:

    * `F.map R` is `R` with `F`'s wires running past OUTSIDE it — the rule that was already here;
    * a product map `φ×𝟙` is `φ` on the LEFT BUNDLE's lanes with `×` and the right bundle running
      past, and `𝟙×ψ` is `ψ` on the right bundle with `×` and the left bundle running past;
    * a composite inside either of those is still a composite, so `(cons secure)×𝟙` is two beads.

    Comparing the two ends' wire STACKS cannot do this: `cons : [A]×[[A]] ⟶ [[A]]` and
    `secure×𝟙` both leave `list list` below them, and the first eats those wires while the second
    does not.  What separates them is the factor's own form, which is what is read here.  A factor
    whose two ends are DIFFERENT objects with the SAME stack is a re-bracketing of a product —
    `assocl` — and a picture has no bracketing to redraw, so it is no row at all.

    `dpanel` draws a bead as a BAR from its westmost arm to the object wire, so a sibling bundle
    east of `φ` lies under that bar: what the bar is, is `φ×𝟙` on the pair, and `underProd` names
    and types it as one.  `𝟙×ψ` needs none of that — `φ`'s bundle passes WEST of the bar. -/
partial def rowsOf (objVars : Array Expr) (regionTy : Expr) (cat : Array Name)
    (pass vpass : Array Wire) (inLeft : Bool) (e : Expr) : MetaM (Array RowSpec) := do
  let fs := factors e
  if fs.size > 1 then
    let mut out : Array RowSpec := #[]
    for f in fs do out := out ++ (← rowsOf objVars regionTy cat pass vpass inLeft f)
    return out
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      let ws := (wiresOf args[4]!).map Wire.rel
      return ← rowsOf objVars regionTy cat (pass ++ ws) (vpass ++ ws) inLeft args[args.size - 1]!
  | _ => pure ()
  if let some (φ, ψ) ← asProdMap? regionTy e then
    let (ex, ey) ← homEnds e
    let (ax, _) ← peelObj objVars cat regionTy ex
    let (ay, _) ← peelObj objVars cat regionTy ey
    -- `×` is a functor out of a PRODUCT category, so an object of `𝒜×𝒜` is two BUNDLES of lanes
    -- side by side and `φ×ψ` acts on one of them with `×` and the sibling bundle running past.
    -- `vpass` is not extended: neither of those is part of the bead's own naturality statement,
    -- and `𝟙×cons°` asked for a closure chain one step deeper than `cons°` itself.
    if let some (Wire.pairW la ra) := ax[1]? then
      if ← isIdArrow φ then
        return ← rowsOf objVars regionTy cat (pass.push ax[0]! ++ la) vpass false ψ
      let rl ← underProd e ψ ra (← rowsOf objVars regionTy cat (pass.push ax[0]!) vpass false φ)
      if ← isIdArrow ψ then return rl
      -- Interchange: `φ×ψ` is `(φ×𝟙)(𝟙×ψ)`, so by the time `ψ` runs the left bundle is `φ`'s TARGET.
      let some (Wire.pairW la' _) := ay[1]?
        | throwError "the product map `{← plain e}` ends at `{← plain ey}`, which peels to \
            {ay.size} wires whose second is no pairing, so `{← plain ψ}` has no bundle to run east of"
      return rl ++ (← rowsOf objVars regionTy cat (pass.push ax[0]! ++ la') vpass false ψ)
    -- A CONSTANT left factor is a lane of its own, and `φ` then acts on the lanes below it.
    if ← isIdArrow ψ then
      return ← underProd e ψ (← peelObj objVars cat regionTy (← homEnds ψ).1).1
        (← rowsOf objVars regionTy cat pass vpass true φ)
    if ← isIdArrow φ then
      let (x, _) ← homEnds φ
      let ls ← peelLefts regionTy x
      return ← rowsOf objVars regionTy cat (pass ++ ls) (vpass ++ ls) inLeft ψ
  let (x, y) ← homEnds e
  let (ax, ox) ← peelObj objVars cat regionTy x
  let (ay, oy) ← peelObj objVars cat regionTy y
  let arms ← if inLeft then peelLefts regionTy x else pure ax
  let legs ← if inLeft then peelLefts regionTy y else pure ay
  -- A re-bracketing is the ONE factor a picture does not show: the same LANES over the same object
  -- at both ends, `(A×B)×C` and `A×(B×C)` differing only in a tree a picture has no room for.  The
  -- object has to be compared too — `⦇R⦈ : t F ⟶ c` has no lanes at either end and is not invisible.
  let al := arms.foldl (· ++ ·.lanes) #[]
  let ll := legs.foldl (· ++ ·.lanes) #[]
  if (← Meta.isDefEq ox oy) && al.size == ll.size && !(← Meta.isDefEq x y) then
    let mut same := true
    for i in [0 : al.size] do
      unless ← Wire.beq al[i]! ll[i]! do same := false
    if same then return #[]
  return #[{ pass, vpass, arms, legs, core := e, shown := e }]

/-- A CUT: the lanes, outermost first, then the object, `|`-separated — `F|a`.  Not `F(a)`: a lane
    may be `×` or `⟨𝟙,T⟩`, which no application spelling reads back, and `scripts/scanline` folds
    this list with the very `fold_cut` it reads the drawn cut with. -/
def cutText (ws : Array Wire) (o : Expr) : MetaM String := do
  let ls ← (ws.foldl (· ++ ·.lanes) #[]).mapM Wire.label
  return String.intercalate "|" (ls.push (← plain o)).toList

/-- One side of a statement, as a panel. -/
def panelOf (regionTy : Expr) (cat : Array Name) (side : Expr) (objVars : Array Expr) :
    MetaM Panel :=
  -- A HEARTBEAT BUDGET BOUNDS A UNIFICATION, NOT A WALK.  One bead's search reads every declaration
  -- in the environment and spends far more than any default allowance, and a budget only ever
  -- measures from where it was set — so a panel under one dies on whatever step follows a search,
  -- naming an `isDefEq` that is not the expensive one.  What bounds the work is
  -- `CANDIDATE_HEARTBEATS` on each match the search tries, and `scripts/cap` on the process.
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let (src, tgt) ← homEnds side
  let (ws0, o0) ← peelObj objVars cat regionTy src
  let mut lanes : Array Lane := #[]
  let mut stack : Array Nat := #[]
  -- The stack is FLAT: a pairing is its bundles' lanes, so a product's left factor's wires sit west
  -- of its right factor's and a bead lands on one block of them.
  for w in ws0.foldl (· ++ ·.lanes) #[] do
    lanes := lanes.push { label := ← w.label, born := -1, dies := LIVE }
    stack := stack.push (lanes.size - 1)
  let mut rows : Array Row := #[]
  for f in factors side do
    let (_, fy) ← homEnds f
    let obj ← plain (← peelObj objVars cat regionTy fy).2
    let specs ← rowsOf objVars regionTy cat #[] #[] false f
    for r in specs do
      let p := r.pass.foldl (· + ·.width) 0
      let na := r.arms.foldl (· + ·.width) 0
      if p + na > stack.size then
        throwError "the factor `{← plain r.core}` eats {na} lanes under {p}, and \
          only {stack.size} are live"
      let i : Int := rows.size
      let arms := stack.extract p (p + na)
      for a in arms do lanes := lanes.set! a { lanes[a]! with dies := i }
      let mut legs : Array Nat := #[]
      for w in r.legs.foldl (· ++ ·.lanes) #[] do
        lanes := lanes.push { label := ← w.label, born := i, dies := LIVE }
        legs := legs.push (lanes.size - 1)
      stack := stack.extract 0 p ++ legs ++ stack.extract (p + na) stack.size
      let (cx, cy) ← homEnds r.core
      let (wx, ox) ← peelObj objVars cat regionTy cx
      let (wy, oy) ← peelObj objVars cat regionTy cy
      let wires := (r.pass ++ r.arms ++ r.legs).foldl (· ++ ·.lanes) #[]
      let fam ← if ← Meta.isDefEq ox oy then familyVar r.core ox objVars wires else pure none
      let vd ← match fam with
        | none => pure none
        | some v =>
          some <$> verdict regionTy (r.vpass ++ r.arms) (r.vpass ++ r.legs) r.core v
            (← plain r.core)
      -- A bead with a verdict sits on its OWN lane and its bar stops at its dot; one WITHOUT sits
      -- on the object wire, so its bar spans the sibling bundle east of it and is `core×𝟙`.
      let east := if !arms.isEmpty && (vd.bind (·.mark)).isNone then r.east else #[]
      rows := rows.push
        { label := ← plain (if east.isEmpty then r.core else r.shown), arms, legs, obj,
          -- The cut the BAR is drawn between, sibling lanes and all: `core`'s own ends would say
          -- the bead eats fewer wires than the bar covers, which is the drift this reports.
          sig := (← cutText (wx ++ east) ox) ++ "⟶" ++ (← cutText (wy ++ east) oy),
          nat := vd.bind (·.mark), natLean := vd.bind (·.lean) }
  let n : Int := rows.size
  lanes := lanes.map fun l => if l.dies == LIVE then { l with dies := n } else l
  -- The two edges' own objects: the source's tail at the top, the target's at the bottom.
  return { lanes, rows, otop := ← plain o0,
           obot := ← plain (← peelObj objVars cat regionTy tgt).2 }

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
    deep the other one is. -/
def drawString (declName : Name) (side binder : Option String) (branch : List Nat)
    (frame topRow scale : Option Nat) (sigsOnly : Bool := false) : MetaM String :=
    withDeclScope declName do
  let env ← getEnv
  let some ci := env.find? declName | throwError "no such declaration: {declName}"
  Meta.forallTelescopeReducing ci.type fun xs body => do
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
    -- The statement's PARTS: the two sides a relation symbol joins, or the arrow itself.
    let parts : Array (String × Expr) := match split body with
      | some (sym, l, r) => #[("", l), (sym, r)]
      | none => #[("", body)]
    let arrow := parts[0]!.2
    -- The OBJECT VARIABLES of the statement: a factor mentioning one is a family, and only a
    -- family can carry a dot.  A binder counts when it is an object of the region — or, where the
    -- region is a ONE-FIELD STRUCTURE over an index type, when it is that INDEX: `Tx : Type`
    -- names the object `⟨Tx⟩ : RelSet`, `dE Tx` IS that object, and `⟨a.carrier⟩` is `a`, so the
    -- two readings are one family and `StrictNatural F G φ` is a statement about it after all.
    let (src, _) ← homEnds arrow
    let regionTy ← Meta.inferType src
    let cat ← relatorCatalogue
    let idxTy ← regionIndexType? regionTy
    let mut objVars : Array Expr := #[]
    for x in xs do
      let t ← Meta.inferType x
      if ← Meta.isDefEq t regionTy then objVars := objVars.push x
      else if let some it := idxTy then
        if ← Meta.isDefEq t it then objVars := objVars.push x
    -- EVERY part is drawn, even when one is asked for: the frame is the max row count over the
    -- statement's sides, so the file for one side has to read the other to be sized.
    let mut sides : Array Panel := #[]
    for (_, e) in parts do sides := sides.push (← panelOf regionTy cat e objVars)
    let ref := sides.foldl (fun a p => if p.rows.size > a.rows.size then p else a) sides[0]!
    -- `.inl`/`.inr` is ONE BRANCH of the side, and the selectors CHAIN: each names an operand of
    -- the binary operation what the one before it left is, outermost first.  What that operation
    -- is — a union, a meet, a junction over a coproduct — is read off the run's type by
    -- `branchOf`, and the object variables are the statement's own either way.
    let drawn : Array (String × Expr) ← match side with
      | none => pure parts
      | some s =>
        if parts.size < 2 then throwError "{declName} has no two sides to draw one of"
        else pure #[("", if s == "lhs" then parts[0]!.2 else parts[1]!.2)]
    let mut ps : Array (String × Panel) := #[]
    for (sym, e) in drawn do
      let mut e := e
      for i in branch do e ← branchOf regionTy e i
      ps := ps.push (sym, ← panelOf regionTy cat e objVars)
    if sigsOnly then return sigLines (ps.map (·.2))
    let nm := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
      ++ (match side with | some s => "." ++ s | none => "")
      ++ branch.foldl (fun s i => s ++ (if i == 0 then ".inl" else ".inr")) ""
    -- A branch panel can be deeper than the side it was cut from — `R ∪ S` is one row and `R` may
    -- be three — so the frame is the deepest of the statement's sides AND of what is drawn.
    let fr := frame.getD (ps.foldl (fun a (_, p) => max a (framex p))
      (sides.foldl (fun a p => max a (framex p)) 2))
    if ps.size == 1 then
      return emit ps[0]!.2 nm (some fr) (some (topRow.getD (topOf fr ref ps[0]!.2))) scale
    return ← emitStatement nm ps (some fr) topRow scale

end Freyd.StrDiag
