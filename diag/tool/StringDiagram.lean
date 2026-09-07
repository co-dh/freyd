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
  nat   : Option String := none
  /-- The declaration the verdict was read off — the panel's own citation for its dots, and for a
      bead the environment REFUTES, which draws no dot and is a claim all the same. -/
  natLean : Option Name := none
  deriving Inhabited

/-- What LEAN says the bead is an arrow between, in the note's notation. -/
def Row.sig (r : Row) : MetaM String := return (← cutText r.src) ++ "⟶" ++ (← cutText r.tgt)

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
def framex (p : Diagram) : Nat := max p.rows.size 1 + 1

/-- The frame's height in cetz units.  The panel and the gate in `emitStatement` both read THIS,
    so the gate measures the box that is drawn and not a second copy of the rule. -/
def frameHeight (p : Diagram) (frame : Option Nat) : Float := (frame.getD (framex p)).toFloat * DY

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
  let xo := roundTo 2 (maxA (ls.map (·.x)) X0 + DX)
  let cell (s : String) : String := "[`" ++ s ++ "`]"
  let str (s : String) : String := "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  let mut beads : Array String := #[]
  let mut objs : Array String := #[]
  let mut nats : Array String := #[]
  for i in [0 : n] do
    let r := p.rows[i]!
    -- THE BAR SPANS THE ARMS, THE DOT SITS ON WHAT THE BEAD TOUCHES.  A bead with NO arms stands on
    -- the object wire and its legs bend OUT of it, so it writes no reach — a bar taken from the legs
    -- would be drawn on the very wires it creates.  Its DOT is still theirs: the mark is the bead's
    -- own, and the only wires it has to sit among are the legs.
    let xsr := r.arms.map fun j => ls[j]!.x
    let xsl := r.legs.map fun j => ls[j]!.x
    let xsd := if xsr.isEmpty then xsl else xsr
    let reach : Option Float := if xsr.isEmpty then none else some (minA xsr 1e9)
    let dot : Option Float :=
      if xsd.isEmpty || r.nat.isNone then none
      else some (roundTo 4 ((minA xsd 1e9 + maxA xsd (-1e9)) / 2.0))
    -- The 6th element is the MARK: `"lax"` and `"oplax"` a hollow dot — the square commutes one way
    -- only, and which way is the cert's business — `"spider"` no dot at all.
    let mark := match r.nat with
      | some "lax" => ", \"lax\"" | some "oplax" => ", \"oplax\""
      | some "spider" => ", \"spider\"" | _ => ""
    beads := beads.push <| match reach, dot with
      | none, none => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ")"
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
    |>.push ("(" ++ num xo ++ ", " ++ cell (← plain p.otop) ++ ")")
  let bot := (ls.filter (·.dies >= (n : Int))).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell (← plain p.obot) ++ ")")
  return "dpanel(" ++ num hh ++ ", " ++ num (roundTo 2 (xo + PAD)) ++ ", " ++ num xo ++ ",\n  "
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
def emit (p : Diagram) (declName : String) (frame topRow scale : Option Nat) : MetaM String :=
  return fileOf declName ("#let pic = " ++ (← panelCode p declName frame topRow scale) ++ "\n")

/-- `--string --sigs`: what LEAN says each bead is an arrow between, one line
    `<panel>\t<label>\t<src>⟶<tgt>` per bead, the panels numbered as the file emits them.  Nothing
    is written into the picture: `scripts/scanline` asks this at check time, so the types it holds
    the ink to are the environment's and cannot go stale in a file. -/
def sigLines (ps : Array Diagram) : MetaM String := do
  let mut out := ""
  for i in [0 : ps.size] do
    for r in ps[i]!.rows do
      out := out ++ toString (i + 1) ++ "\t" ++ r.label ++ "\t" ++ (← r.sig) ++ "\n"
  return out

/-- Where a part's first bead sits, in rows.  The deepest part's sits one row below the ceiling; a
    shorter part slides until a bead it SHARES with that part stands at the same height, which is
    the alignment `diagram --pairs` holds a display to.  Labels are compared whole, as that gate
    compares them: a bead is the same bead when it is the same 2-cell. -/
def topOf (frame : Nat) (ref p : Diagram) : Nat :=
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
def emitStatement (declName : String) (parts : Array (String × Diagram))
    (frame topRow scale : Option Nat) : MetaM String := do
  let ps := parts.map (·.2)
  let fr := frame.getD (ps.foldl (fun a p => max a (framex p)) 2)
  let ref := ps.foldl (fun a p => if p.rows.size > a.rows.size then p else a) ps[0]!
  let mut cells : Array String := #[]
  let mut hs : Array Float := #[]
  for (sym, p) in parts do
    if !sym.isEmpty then cells := cells.push ("text(15pt)[" ++ sym ++ "]")
    cells := cells.push
      (← panelCode p declName (some fr) (some (topRow.getD (topOf fr ref p))) scale)
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

/-- The two RELATORS of a family `φ`, read off `φ`'s OWN type: open its binder and read each end of
    the arrow underneath as a relator in that variable (`relatorOfObj`).  Built this way the
    proposition `StrictNatural F G φ` type-checks by construction — `φ a : G.obj a ⟶ F.obj a` holds
    because `G` and `F` ARE those two ends — where a stack of lane labels is a second spelling of
    the same thing that can disagree with it. -/
def relatorsOf (cat : Array Name) (regionTy φ : Expr) : MetaM (Expr × Expr) :=
  Meta.lambdaBoundedTelescope φ 1 fun xs body => do
    let some v := xs[0]?
      | throwError "not a family: `{← Meta.ppExpr φ}` takes no object of {← Meta.ppExpr regionTy}"
    let (x, y) ← homEnds body
    let G ← instantiateMVars (← relatorOfObj cat regionTy v x)
    let F ← instantiateMVars (← relatorOfObj cat regionTy v y)
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
def verdict (regionTy : Expr) (cat : Array Name) (core φ : Expr) : MetaM Verdict := do
  -- THE STATEMENT IS READ OFF THE FAMILY, NOT OFF THE LANES.  `φ = fun v => core`, so its two
  -- relators are its own end objects as functions of `v` (`relatorOfObj`) and the proposition
  -- type-checks by construction; a stack of lane labels is a second spelling of the same thing that
  -- can disagree with it, and did.
  -- An end no relator spells — `F Unit A`, the base functor with the element type baked in — leaves
  -- no proposition to search for, and that is a SPIDER: the tool looked, there was nothing to look
  -- at, and the bead makes no claim.  Naming it an error would fail the whole panel over one bead.
  let some (G, F) ← (some <$> relatorsOf cat regionTy φ) <|> pure none
    | return { mark := some "spider", lean := none }
  let must := consts core
  let strict ← Meta.mkAppM ``Freyd.Alg.StrictNatural #[F, G, φ]
  let lax ← Meta.mkAppM ``Freyd.Alg.LaxNatural #[F, G, φ]
  let oplax ← Meta.mkAppM ``Freyd.Alg.OpLaxNatural #[F, G, φ]
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
      -- The CONVERSE of a lax family is not lax, it is lax the other way (`laxNatural_recip`), so
      -- `OplaxNatural` is asked before the refutation: `prefix°` is not a spider, it is a hollow dot
      -- whose square points the other way, and the `nat:` row is where the direction is written.
      -- The CLASS only, not the square: nothing in the repo states a raw oplax inequation, so
      -- unfolding it would scan every `⊑` in the environment for a shape only `laxNatural_recip`
      -- ever produces — and that closure's own hypothesis IS searched as a square, through
      -- `discharge`.  A whole extra sweep per bead is what the H panels' budget cannot pay.
      if let some (n, _) ← findProof br oplax ``Freyd.Alg.OpLaxNatural {} FUEL then
        return some { mark := some "oplax", lean := n }
      if let some (n, _) ← findProof br nolax ``Not must FUEL then
        return some { mark := none, lean := n }
      return none
  -- NO VERDICT, NO DOT, NO CLAIM.  The three statements are what was looked for and none of them
  -- is proved, so the bead draws as the book's spider (IntroString §2.2.4) — a node with no mark —
  -- rather than the panel failing or, worse, a dot standing for a naturality nobody has.
  return found.getD { mark := some "spider", lean := none }

/-! ### The four constructors — nothing else builds a `Diagram` -/

/-- The bare wires `ws` over the object `o`: born at the top edge, dying at the bottom, no bead.
    `⟦𝟙⟧`, and the lanes a factor merely runs past. -/
def Diagram.id (ws : Array Wire) (o : Expr) : MetaM Diagram := do
  let lanes ← ws.mapM fun w => return { label := ← w.label, born := -1, dies := LIVE, wire := w }
  let ix := Array.mk (List.range lanes.size)
  return { lanes, rows := #[], top := ix, bot := ix, otop := o, obot := o }

/-- ONE bead: `arms` born at the top edge and eaten by it, `legs` made by it and live to the bottom.
    The VERDICT is searched HERE, off the bead's own family — the lanes it runs under and the lanes
    drawn past it are alike none of its naturality statement's business.

    `fam` is the family the bead is a component of, where the caller already knows it: `φ×𝟙` varies
    with the object UNDER its lane, not with an object variable of the statement, so no fvar of the
    statement abstracts it.  Left off, the family is read off the statement's own object binders. -/
def Diagram.bead (regionTy : Expr) (cat : Array Name) (objVars : Array Expr)
    (arms legs : Array Wire) (ox oy core : Expr) (fam : Option Expr := none) :
    MetaM Diagram := do
  let mut lanes : Array Lane := #[]
  for w in arms do lanes := lanes.push { label := ← w.label, born := -1, dies := 0, wire := w }
  for w in legs do lanes := lanes.push { label := ← w.label, born := 0, dies := LIVE, wire := w }
  -- The two ends need NOT be the same object.  `nil : 𝟏⟶[[x]]` starts at a constant and ends at a
  -- family, and `Relator.const` is a relator like any other, so demanding `ox` and `oy` agree threw
  -- away a naturality the environment proves.
  let φ ← match fam with
    | some φ => pure (some φ)
    | none =>
      match ← familyVar core objVars with
      | some v => some <$> familyOf regionTy v core
      | none => pure none
  let vd ← match φ with
    | none => pure none
    | some φ => some <$> verdict regionTy cat core φ
  let top := Array.mk (List.range arms.size)
  let bot := Array.mk (List.range' arms.size legs.size)
  let row : Row :=
    { label := (← plain core), arms := top, legs := bot, obj := (← plain oy),
      src := { ws := arms, o := ox }, tgt := { ws := legs, o := oy },
      nat := vd.bind (·.mark), natLean := vd.bind (·.lean) }
  return { lanes, rows := #[row], top, bot, otop := ox, obot := oy }

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
  let rows := d.rows ++ e.rows.map fun r => { r with arms := r.arms.map emap, legs := r.legs.map emap }
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
  let drows := d.rows.map fun r => { r with arms := r.arms.map dmap, legs := r.legs.map dmap, obj }
  let rows := drows ++ e.rows.map fun r => { r with arms := r.arms.map emap, legs := r.legs.map emap }
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
    -- `φ×𝟙` is ONE bead on the left factor's lane, `A×− ⇒ A'×−`.  Its family runs over the object
    -- UNDER that lane, which no binder of the statement names, so it is built here and handed to
    -- `Diagram.bead`; the lanes east of it are what that object is, and only run past.
    let (ax, ox) ← peelObj objVars cat regionTy (← homEnds e).1
    let (_, oy) ← peelObj objVars cat regionTy (← homEnds e).2
    let fam ← Meta.withLocalDeclD `Y regionTy fun Y => do
      Meta.mkLambdaFVars #[Y] (← Meta.mkAppM n #[φ, ← Meta.mkAppM ``Cat.id #[Y]])
    let d ← Diagram.bead regionTy cat objVars #[Wire.timesL a] #[Wire.timesL a'] ox oy e
      (some fam)
    return ← d.beside (← Diagram.id (ax.extract 1 ax.size) ox)
  let (x, y) ← homEnds e
  let (ax, ox) ← peelObj objVars cat regionTy x
  let (ay, oy) ← peelObj objVars cat regionTy y
  Diagram.bead regionTy cat objVars ax ay ox oy e

/-- One side of a statement, as a panel: its picture, with the bottom edge's lanes told how deep the
    picture turned out to be. -/
def panelOf (regionTy : Expr) (cat : Array Name) (side : Expr) (objVars : Array Expr) :
    MetaM Diagram := do
  let d ← interp regionTy cat objVars #[] side
  let n : Int := d.rows.size
  return { d with lanes := d.lanes.map fun l => if l.dies == LIVE then { l with dies := n } else l }

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
    -- THE BUDGET COVERS THE WHOLE READ, not the search inside it.  A budget lifted only around the
    -- searches lapses the moment they return, and what the panel does NEXT — printing each bead's
    -- ends — then runs on an allowance the searches have already spent, so the read dies naming an
    -- `isDefEq` that is not the expensive one.  `CANDIDATE_HEARTBEATS` bounds each match tried and
    -- `scripts/cap` bounds the process; nothing between them needs an allowance of its own.
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
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
    let mut sides : Array Diagram := #[]
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
    let mut ps : Array (String × Diagram) := #[]
    for (sym, e) in drawn do
      let mut e := e
      for i in branch do e ← branchOf regionTy e i
      ps := ps.push (sym, ← panelOf regionTy cat e objVars)
    if sigsOnly then return ← sigLines (ps.map (·.2))
    let nm := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
      ++ (match side with | some s => "." ++ s | none => "")
      ++ branch.foldl (fun s i => s ++ (if i == 0 then ".inl" else ".inr")) ""
    -- A branch panel can be deeper than the side it was cut from — `R ∪ S` is one row and `R` may
    -- be three — so the frame is the deepest of the statement's sides AND of what is drawn.
    let fr := frame.getD (ps.foldl (fun a (_, p) => max a (framex p))
      (sides.foldl (fun a p => max a (framex p)) 2))
    if ps.size == 1 then
      return ← emit ps[0]!.2 nm (some fr) (some (topRow.getD (topOf fr ref ps[0]!.2))) scale
    return ← emitStatement nm ps (some fr) topRow scale

end Freyd.StrDiag
