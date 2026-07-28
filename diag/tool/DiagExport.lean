/-
  `diag-export` — draw the STATEMENT of a Lean declaration as a string diagram.

  `./scripts/diag-export Freyd.Diag.dom_cd` writes `diag/generated/Freyd.Diag.dom_cd.typ`, a page
  that imports `../strdiag.typ` and draws the theorem's two sides joined by its relation symbol.
  The proof is not looked at; only `ConstantInfo.type`.

  WHY THIS IS A TERM WALK AND NOT A GRAPH LAYOUT.  A statement of this calculus is a composite of
  arrows, and a composite is a TREE, so its picture is built left to right by structural recursion —
  there is nothing to route.  Everything the walk does not recognise degrades to an opaque labelled
  box carrying the pretty-printed subterm, so an unknown operator costs one box, never a failure.

  WHAT IS RECOGNISED.  `Cat.comp` flattens into a run of cells; `Cat.id` is a bare wire;
  `Allegory.inter`/`Diag.meet` draw the `Δ;(R ⊗ S);∇` block NESTED, so `(R ∩ S) ∩ T` shows its inner
  meet rather than a box labelled `R ∩ S`; `Diag.union` (phase 8) draws the tape, the same shape on
  the second monoidal product; `Allegory.recip`/`Diag.conv` draw the mirrored box.  `Diag.residual`
  and `LinearBicat.perp` (phase 9) draw a DASHED box: they are not composites of the generators, and
  the dashed frame is what `strdiag.typ` reserves for that.  At the top, `Alg.le` (`⊑`), `LE.le`
  (`≤`) and `Eq` split the statement into two pictures with the symbol between them.

  A converse's operand is still a single box: `strdiag.typ`'s mirrored `gbox` takes a LABEL, so a
  composite under a `°` appears as one box reading `R ; S`.

  ONE ENVIRONMENT PER PROCESS — the `lean-refactor` OOM lesson (`Freyd/tool/LeanRefactor.lean`):
  `importModules` retains its environment for the life of the process, so this exe imports once and
  handles every declaration named on the command line from that one environment.
-/
import Lean
import diag.FO
import diag.Tape
import diag.S2_124

open Lean

namespace Freyd.DiagExport

/-! ### Picture model

The measurements are `diag/strdiag.typ`'s own, and must move with it: `BW`/`LEAD` are its constants,
`meetW`/`convW` are its `meet-w`/`conv-w` at their default arguments. -/

def BW : Float := 0.92
def BH : Float := 0.60
def LEAD : Float := 0.34
def GAP : Float := 0.34
def wireW : Float := 0.60
/-- How far `Δ` opens and `∇` closes on either side of a meet. -/
def FORK : Float := 0.42
/-- The clear vertical gap between the two strands of a meet, edge to edge. -/
def STRANDGAP : Float := 0.64
/-- How far the tape's rounded wrapper stands off the circuit inside it. -/
def TAPEPAD : Float := 0.22
/-- How far a cap's or a cup's strands bend over. -/
def CAPBEND : Float := 0.60
/-- `strdiag.typ`'s `SPLIT`: the stub between the two dots of a cap (`∇` then `!`) or a cup (`?`
    then `Δ`).  They are drawn split, as the paper draws the converse. -/
def SPLITW : Float := 0.34
/-- A cap or cup occupies its bend plus that stub. -/
def CAPW : Float := CAPBEND + SPLITW
/-- The column a chain's relation symbol sits in, to the left of every term. -/
def SYMCOL : Float := 0.95
/-- The strand offset a fork, a cap and a cup open by.  A `⊗` may sit wider — `meetSep` grows with
    what is nested in its runs — and `joinWire` bends between the two, so the two need not agree. -/
def STACKSEP : Float := 0.62

/-- One left-to-right slot of a picture. -/
inductive Cell where
  | wire
  | box (label : String)
  /-- A generator `strdiag.typ` draws directly.  `lead` is the distance from this cell's LEFT EDGE
      to the anchor the drawing function wants: `delta`, `nabla` and `bang` hang their incoming stub
      to the LEFT of that anchor, so passing the left edge straight through leaves the wire hanging
      in mid-air — which is what disconnected `∇ ; Δ` pictures were. -/
  | gen (fn : String) (width lead : Float)
  /-- A meet, drawn as the nested picture `Δ ; (upper ⊗ lower) ; ∇`, not as a box with a label.
      Nesting is why the operands are cell RUNS: `(R ∩ S) ∩ T` has to show its inner meet. -/
  | meet (upper lower : Array Cell)
  /-- A union (phase 8, `diag/Tape.lean`), drawn as a TAPE: the same fork-runs-join shape as a meet,
      but on the second monoidal product, so it is the tape's `▷`/`◁` and not `Δ`/`∇`
      (`TapeDiagrams.pdf` Fig. 1).  A particle takes exactly one branch, which is the union. -/
  | union (upper lower : Array Cell)
  /-- A box the calculus cannot build out of its generators — the residual `R / S` of phase 9
      (`diag/FO.lean`), which needs the second composition and the linear adjoint.  `strdiag.typ`
      reserves the dashed frame for exactly this. -/
  | dbox (label : String)
  /-- A monoidal product `f ⊗ g`, drawn as the two runs STACKED — no fork, no join, since `⊗` puts
      two arrows side by side rather than copying one.  This is what makes a proof about bent wires
      readable: `𝟙 ⊗ S°` is a wire above a mirrored box, not an opaque label. -/
  | stack (upper lower : Array Cell)
  /-- The cap `∇ ; !` and the cup `? ; Δ`, in `strdiag.typ`'s `capAt`/`cupAt` one-anchor form.  A cap
      takes a pair on the left and gives nothing on the right; a cup is its mirror. -/
  | capC
  | cupC
  /-- A converse: the same box MIRRORED, which is how
      functorialSemanticsForRelationalTheories.pdf writes `†`. -/
  | dagger (label : String)

instance : Inhabited Cell := ⟨.wire⟩

/-- What a cell offers on one of its sides: a single strand, the two strands of a fork, or nothing
    at all.  Only `one` against `one` gets a joining wire — a wire drawn at the centre line between
    `Δ` and `∇` runs straight through the middle of the bubble they form, and a stub in front of `∇`
    hangs off a port that has two strands, not one. -/
inductive Port where
  /-- one strand on the centre line -/
  | one
  /-- the two prongs of a fork: `Δ`'s output, `∇`'s input.  Two of these facing each other ABUT into
      a single bubble; against a `⊗` they take a gap and two wires like any other pair of levels. -/
  | pair
  /-- the two levels of a `⊗`, or of a cap or cup. -/
  | strands
  | nothing
  deriving BEq

/-- Carries two strands, whichever kind. -/
def Port.isTwo : Port → Bool
  | .pair | .strands => true
  | _ => false

def Cell.leftPort : Cell → Port
  | .gen "nabla" _ _ | .gen "swap" _ _ => .pair
  | .gen "unitR" _ _ | .cupC => .nothing
  | .stack _ _ | .capC => .strands
  | _ => .one

def Cell.rightPort : Cell → Port
  | .gen "delta" _ _ | .gen "swap" _ _ => .pair
  | .gen "bang" _ _ | .capC => .nothing
  | .stack _ _ | .cupC => .strands
  | _ => .one

/-- A box has to hold its label.  `strdiag.typ`'s default `BW` fits about six characters at 10pt;
    anything longer widens the box rather than spilling out of it. -/
def boxWidth (l : String) : Float := max BW (0.225 * l.length.toFloat + 0.30)

mutual

partial def Cell.width : Cell → Float
  | .wire => wireW
  | .box l | .dbox l => boxWidth l
  | .gen _ w _ => w
  | .meet u l => 2.0 * FORK + max (runWidth u) (runWidth l)
  | .union u l => 2.0 * FORK + 2.0 * TAPEPAD + max (runWidth u) (runWidth l)
  | .stack u l => max (runWidth u) (runWidth l)
  | .capC | .cupC => CAPW
  | .dagger l => boxWidth l

/-- The horizontal room between two adjacent cells: none when two forks face each other, since they
    abut into one bubble. -/
partial def joinGap (c next : Cell) : Float :=
  if c.rightPort == .pair && next.leftPort == .pair then 0.0 else GAP

/-- A run of cells wired in series, without the outer stubs a whole picture gets. -/
partial def runWidth (cells : Array Cell) : Float := Id.run do
  let mut w := 0.0
  for i in [0 : cells.size] do
    w := w + cells[i]!.width
    if h : i + 1 < cells.size then w := w + joinGap cells[i]! cells[i + 1]
  return w

/-- Half the vertical extent, so a meet can separate its strands by enough to clear whatever is
    nested inside them. -/
partial def Cell.span : Cell → Float
  | .meet u l => meetSep u l + max (runSpan u) (runSpan l)
  | .union u l => meetSep u l + max (runSpan u) (runSpan l) + TAPEPAD
  | .stack u l => meetSep u l + max (runSpan u) (runSpan l)
  | .capC | .cupC => STACKSEP + BH / 2.0
  | .gen "delta" _ _ | .gen "nabla" _ _ => STACKSEP
  | _ => BH / 2.0

/-- The height at which a two-strand port's strands sit, above and below the centre line.  A `⊗`
    separates its runs by `meetSep`, which grows with what is nested inside them; a fork, a cap and a
    cup always open by `STACKSEP`.  `renderRun` reads both sides and joins them. -/
partial def Cell.strandSep : Cell → Float
  | .stack u l => meetSep u l
  | _ => STACKSEP

/-- Where a cell's strands MEET its left edge, top to bottom.  A port is not one strand or two: a
    `⊗` of a fork and a wire offers three, and whatever follows has to be wired to all three.
    Composing two pictures means connecting these lists, so they are computed structurally rather
    than assumed. -/
partial def Cell.leftOffsets (sep : Float) : Cell → Array Float
  | .gen "nabla" _ _ | .gen "swap" _ _ | .capC => #[sep, -sep]
  | .gen "unitR" _ _ | .cupC => #[]
  | .stack u l =>
    (runLeftOffsets u).map (· + sep) ++ (runLeftOffsets l).map (· - sep)
  | _ => #[0.0]

/-- Where a cell's strands meet its right edge, top to bottom. -/
partial def Cell.rightOffsets (sep : Float) : Cell → Array Float
  | .gen "delta" _ _ | .gen "swap" _ _ | .cupC => #[sep, -sep]
  | .gen "bang" _ _ | .capC => #[]
  | .stack u l =>
    (runRightOffsets u).map (· + sep) ++ (runRightOffsets l).map (· - sep)
  | _ => #[0.0]

/-- What a cell needs its two strands separated by: a `⊗` by `meetSep`, so its runs clear each
    other; a fork, a swap, a cap and a cup by nothing in particular. -/
partial def Cell.natSep : Cell → Float
  | .stack u l => meetSep u l
  | _ => STACKSEP

/-- THE SEPARATION EVERY TWO-STRAND CELL OF A RUN IS DRAWN AT.  Composition has to line up: a fork
    feeding a `⊗` opens exactly as wide as the `⊗` stacks, so the strands meet as straight wires
    instead of being bent into place afterwards.  One number per run, the widest any cell needs. -/
partial def runSep (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => max acc c.natSep) STACKSEP

partial def runLeftOffsets (cells : Array Cell) : Array Float :=
  match cells[0]? with | some c => c.leftOffsets (runSep cells) | none => #[0.0]

partial def runRightOffsets (cells : Array Cell) : Array Float :=
  match cells.back? with | some c => c.rightOffsets (runSep cells) | none => #[0.0]

partial def runSpan (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => max acc c.span) (BH / 2.0)

/-- The offset of each strand of a meet from its centre line: enough that the two runs clear each
    other by `STRANDGAP`.  At the leaves this is `strdiag.typ`'s own `0.62`. -/
partial def meetSep (u l : Array Cell) : Float :=
  (runSpan u + runSpan l + STRANDGAP) / 2.0

end

/-- Typst string literal: only `\` and `"` can end it early. -/
def typstString (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- Labels are set at 9pt monospace, which is what `boxWidth`'s per-character figure measures.  Keep
    the two in step: raising one without the other either overflows the box or pads it. -/
def labelContent (l : String) : String := s!"text(9pt, raw({typstString l}))"

/-- Two decimal places.  `toString` on a `Float` prints six, and cetz coordinates read as noise at
    that width. -/
def fmt (x : Float) : String :=
  let n := (x * 100.0).round
  let m := n.abs.toUInt64.toNat
  let frac := m % 100
  let s := s!"{m / 100}.{if frac < 10 then "0" else ""}{frac}"
  if n < 0.0 then "-" ++ s else s

/-- A horizontal wire, or nothing when the two ends coincide — a zero-length `wire` draws a blob at
    the joint. -/
def hwire (x₀ x₁ y : Float) : Array String :=
  if x₁ - x₀ > 0.005 then #[s!"  wire(({fmt x₀}, {fmt y}), ({fmt x₁}, {fmt y}))"] else #[]

/-- Join two ports that are at DIFFERENT heights: a wire when they agree, a bend when they do not.
    Composition has to connect — the output strands of one cell are the input strands of the next,
    wherever each happens to sit — and the offsets do not always agree: a `⊗` separates its two runs
    by enough to clear whatever is nested in them, while a fork always opens by `STACKSEP`.  Drawing
    both at a fixed offset is what left `Δ ; (Δ ⊗ 𝟙)` as four strands meeting nothing. -/
def joinWire (x₀ x₁ y₀ y₁ : Float) : Array String :=
  if (y₁ - y₀).abs < 0.005 then hwire x₀ x₁ y₀
  else #[s!"  bend(({fmt x₀}, {fmt y₀}), ({fmt x₁}, {fmt y₁}), k: 0.5)"]

mutual

partial def Cell.render (c : Cell) (x y sep : Float) : Array String :=
  match c with
  | .wire => hwire x (x + wireW) y
  | .box l => #[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH})"]
  | .gen fn w lead =>
    -- Every two-strand generator opens at the separation its RUN settled on, so the strands it
    -- offers are the strands its neighbours expect.  `strdiag.typ`'s defaults are narrower; this
    -- overrides them.  The swap also spans its cell, or the wires into it stop short of the
    -- crossing.
    let sp :=
      if fn == "delta" || fn == "nabla" then s!", sp: {fmt sep}"
      else if fn == "swap" then s!", sp: {fmt sep}, w: {fmt w}"
      else ""
    #[s!"  {fn}(({fmt (x + lead)}, {fmt y}){sp})"]
  -- Tinted as well as mirrored: see `TINT` in `strdiag.typ`.  A chain whose whole content is a box
  -- crossing a bend and coming back upright has to show that at a glance, not on inspection of
  -- which corner is chamfered.
  | .dagger l =>
    #[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH},        flip: true, fill: TINT)"]
  | .dbox l =>
    #[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH}, dashed: true)"]
  -- A cap's second dot sits to the RIGHT of its bend, a cup's to the LEFT, so the cup is anchored
  -- one stub in from this cell's left edge.
  | .capC => #[s!"  capAt(({fmt x}, {fmt y}), sp: {fmt sep}, w: {fmt CAPBEND})"]
  | .cupC => #[s!"  cupAt(({fmt (x + SPLITW)}, {fmt y}), sp: {fmt sep}, w: {fmt CAPBEND})"]
  | .stack u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let mut out := #[]
    for (run, dy) in [(u, sep), (l, -sep)] do
      let rx := x + (iw - runWidth run) / 2.0
      out := out ++ hwire x rx (y + dy) ++ renderRun run rx (y + dy)
        ++ hwire (rx + runWidth run) (x + iw) (y + dy)
    return out
  | .union u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let sep := meetSep u l
    let inner := max (runSpan u) (runSpan l)
    let x₁ := x + TAPEPAD + FORK             -- where the tape's two branches begin
    let x₂ := x₁ + iw
    let w := 2.0 * FORK + 2.0 * TAPEPAD + iw
    -- The wrapper is drawn FIRST so the circuit sits on top of it, not under it.
    let mut out := #[s!"  tape(({fmt x}, {fmt (y - sep - inner - TAPEPAD)}), \
      ({fmt (x + w)}, {fmt (y + sep + inner + TAPEPAD)}))",
      s!"  tape-fork(({fmt (x + TAPEPAD)}, {fmt y}), sp: {fmt sep}, len: {fmt FORK})"]
    for (run, dy) in [(u, sep), (l, -sep)] do
      let rx := x₁ + (iw - runWidth run) / 2.0
      out := out ++ hwire x₁ rx (y + dy) ++ renderRun run rx (y + dy)
        ++ hwire (rx + runWidth run) x₂ (y + dy)
    return out.push
      s!"  tape-join(({fmt (x + w - TAPEPAD)}, {fmt y}), sp: {fmt sep}, len: {fmt FORK})"
  | .meet u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let sep := meetSep u l
    let x₁ := x + FORK                       -- where `Δ`'s two strands arrive
    let x₂ := x₁ + iw                        -- where `∇`'s two strands leave
    let mut out :=
      #[s!"  delta(({fmt x}, {fmt y}), li: 0, lo: {fmt FORK}, sp: {fmt sep})"]
    -- Each operand run is centred in the shared inner width, and wired out to both ends.
    for (run, dy) in [(u, sep), (l, -sep)] do
      let rx := x₁ + (iw - runWidth run) / 2.0
      out := out ++ hwire x₁ rx (y + dy) ++ renderRun run rx (y + dy)
        ++ hwire (rx + runWidth run) x₂ (y + dy)
    return out.push
      s!"  nabla(({fmt (x₂ + FORK)}, {fmt y}), li: {fmt FORK}, lo: 0, sp: {fmt sep})"

/-- Lay a run of cells out at height `y` from `x0`, joining consecutive ones with a wire.  Two forks
    facing each other ABUT — `Δ ; ∇` is one bubble, not two shapes with a gap — so `runWidth` has to
    agree with this, which is what `joinGap` is for. -/
partial def renderRun (cells : Array Cell) (x0 y : Float) : Array String := Id.run do
  let sep := runSep cells
  let mut out := #[]
  let mut x := x0
  for i in [0 : cells.size] do
    let c := cells[i]!
    out := out ++ c.render x y sep
    x := x + c.width
    if h : i + 1 < cells.size then
      let next := cells[i + 1]
      -- Nothing to join when the two abut: a fork straight into a fork is ONE bubble, and a wire
      -- drawn across it would run through the middle of the shape.
      if joinGap c next < 0.005 then
        pure ()
      else if c.rightPort == .one && next.leftPort == .one then
        out := out ++ hwire x (x + GAP) y
      else if c.rightPort.isTwo && next.leftPort.isTwo then
        -- One join per strand, from where THIS cell's strands end to where the next one's begin.
        -- The two lists agree in length whenever the statement typechecks; if a cell this walk does
        -- not model made them disagree, wire what can be wired rather than drop the join entirely.
        let a := c.rightOffsets sep
        let b := next.leftOffsets sep
        for j in [0 : min a.size b.size] do
          out := out ++ joinWire x (x + GAP) (y + a[j]!) (y + b[j]!)
      x := x + joinGap c next
  return out

end

/-- A whole side of a statement: the run with a stub at each end — but only where the end really is
    a single strand — and the x it ends at. -/
def renderCells (cells : Array Cell) (x0 : Float) : String × Float :=
  let lp := (cells[0]?.map Cell.leftPort).getD .one
  let rp := (cells.back?.map Cell.rightPort).getD .one
  let lead := if lp == .nothing || lp == .pair then 0.0 else LEAD
  let tail := if rp == .nothing || rp == .pair then 0.0 else LEAD
  let w := runWidth cells
  let stub (x₀ x₁ : Float) (offs : Array Float) : Array String :=
    offs.foldl (fun acc o => acc ++ hwire x₀ x₁ o) #[]
  let out := stub x0 (x0 + lead) (runLeftOffsets cells) ++ renderRun cells (x0 + lead) 0.0
    ++ stub (x0 + lead + w) (x0 + lead + w + tail) (runRightOffsets cells)
  (String.intercalate "\n" out.toList, x0 + lead + w + tail)

/-! ### The term walk -/

/-- The two arrow arguments of a binary operator applied with instance and object arguments. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- Last resort: Lean's pretty printer, on one line.  The repo's namespaces carry no information
    inside a picture of the repo's own algebra, so they come off. -/
def plain (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  -- Both the fully qualified form and the form the printer shortens to under `open Freyd`.
  let s := s.replace "Freyd." "" |>.replace "Diag.CartBicat." "" |>.replace "Diag." ""
    |>.replace "Alg.Allegory." "" |>.replace "Alg." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- A term, spelled the way the BOOK spells it — `;` for composition, `°` for the converse —
    rather than left to the pretty printer, because it is read beside a picture, where
    `CartBicat.conv S` is noise and `S°` is the thing itself.  `°`, not the paper's `†`: these terms
    are read against Freyd throughout, and one symbol per idea beats matching two.

    PARENTHESISED BY PRECEDENCE, `;` loosest and `°` tightest, so the bracketing is visible.  That
    matters: several steps of a `calc` do nothing but re-bracket, and the term column is the only
    place a reader can see them happen — the picture, quite correctly, does not change. -/
partial def labelAt (prec : Nat) (e : Expr) : MetaM String := do
  let wrap (p : Nat) (s : String) : String := if prec > p then "(" ++ s ++ ")" else s
  let bin (p : Nat) (op : String) (args : Array Expr) : MetaM String :=
    match lastTwo args with
    | some (f, g) => return wrap p ((← labelAt (p + 1) f) ++ op ++ (← labelAt (p + 1) g))
    | none => plain e
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  | (``Freyd.Diag.CartBicat.Δ, _) => return "Δ"
  | (``Freyd.Diag.CartBicat.«∇», _) => return "∇"
  | (``Freyd.Diag.CartBicat.«!», _) => return "!"
  | (``Freyd.Diag.CartBicat.«?», _) => return "?"
  | (``Freyd.Diag.CartBicat.cap, _) => return "cap"
  | (``Freyd.Diag.CartBicat.cup, _) => return "cup"
  | (``Freyd.Diag.top, _) => return "⊤"
  | (``Freyd.Diag.Biprod.bot, _) => return "⊥"
  -- No `α`, `λ` or `ρ` cases: this branch's monoidal structure is STRICT, so the coherence arrows
  -- do not exist and no statement can mention one.
  | (``Freyd.Diag.SymMonCat.swap, _) => return "σ"
  | (``Cat.comp, args) => bin 0 " ; " args
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 1 " ∩ " args
  | (``Freyd.Diag.Biprod.union, args) => bin 1 " ∪ " args
  | (``Freyd.Diag.ClosedLinearBicat.residual, args) => bin 1 " / " args
  | (``Freyd.Alg.Allegory.recip, args) | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    | some r => return (← labelAt 3 r) ++ "°"
    | none => plain e
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) =>
    match args.back? with
    | some r => return (← labelAt 3 r) ++ "⊥"
    | none => plain e
  | _ => plain e

/-- A label at the top of its own picture or box: no outer parentheses. -/
def label (e : Expr) : MetaM String := labelAt 0 e

mutual

/-- One cell for `e`, used where a sub-picture is not available (inside a meet or a converse). -/
partial def toCell (e : Expr) : MetaM Cell := do
  match e.getAppFnArgs with
  | (``Cat.id, _) => return .wire
  -- width and lead are the generators' own stubs in `strdiag.typ`: `li + lo` wide, `li` of it to
  -- the left of the anchor (`unitR` and `swap` anchor on their left edge, so their lead is 0).
  | (``Freyd.Diag.CartBicat.Δ, _) => return .gen "delta" 1.4 0.7
  | (``Freyd.Diag.CartBicat.«∇», _) => return .gen "nabla" 1.4 0.7
  | (``Freyd.Diag.CartBicat.«!», _) => return .gen "bang" 0.7 0.7
  | (``Freyd.Diag.CartBicat.«?», _) => return .gen "unitR" 0.7 0.0
  | (``Freyd.Diag.SymMonCat.swap, _) => return .gen "swap" 0.55 0.0
  | (``Freyd.Diag.CartBicat.cap, _) => return .capC
  | (``Freyd.Diag.CartBicat.cup, _) => return .cupC
  | (``Freyd.Diag.SymMonCat.tensHom, args) =>
    match lastTwo args with
    | some (u, l) => return .stack (← toCells u) (← toCells l)
    | none => return .box (← label e)
  | (``Freyd.Alg.Allegory.inter, args)
  | (``Freyd.Diag.meet, args) =>
    match lastTwo args with
    | some (u, l) => return .meet (← toCells u) (← toCells l)
    | none => return .box (← label e)
  | (``Freyd.Diag.Biprod.union, args) =>
    match lastTwo args with
    | some (u, l) => return .union (← toCells u) (← toCells l)
    | none => return .box (← label e)
  -- The residual is NOT a composite of the generators; `strdiag.typ`'s dashed frame says so.
  | (``Freyd.Diag.ClosedLinearBicat.residual, _) => return .dbox (← label e)
  | (``Freyd.Diag.ClosedLinearBicat.perp, _) => return .dbox (← label e)
  | (``Freyd.Alg.Allegory.recip, args)
  | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    | some r => return .dagger (← label r)
    | none => return .box (← label e)
  | _ => return .box (← label e)

/-- The run of cells for `e`, flattening composition. -/
partial def toCells (e : Expr) : MetaM (Array Cell) := do
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => return (← toCells f) ++ (← toCells g)
    | none => return #[← toCell e]
  | _ => return #[← toCell e]

end

/-- The relation between the two sides of a statement, and the sides. -/
def split (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.le, args) => (lastTwo args).map fun (l, r) => ("⊑", l, r)
  | (``LE.le, args) => (lastTwo args).map fun (l, r) => ("≤", l, r)
  | (``Eq, args) => (lastTwo args).map fun (l, r) => ("=", l, r)
  | _ => none

/-- `split`, retrying once through the definition of a named predicate.  `Total (R ∩ S)` is a `Prop`
    with no sides until `Total` is unfolded; then it is `𝟙 ≤ (R ∩ S);(R ∩ S)°` and draws.

    ONE delta step, never `whnf`: `whnf` keeps going past `LE.le` into the `OrderedCat` projection it
    is a field of, and the whole inequation collapses into one opaque box. -/
def splitM (e : Expr) : MetaM (Option (String × Expr × Expr)) := do
  if let some r := split e then return some r
  let .const n us := e.getAppFn | return none
  let some ci := (← getEnv).find? n | return none
  let some v := ci.value? | return none
  return split ((mkAppN (v.instantiateLevelParams ci.levelParams us) e.getAppArgs).headBeta)

/-! ### Proofs

A `calc` proof elaborates to nested `Trans.trans`/`Eq.trans`, so its intermediate terms are all
recoverable from the proof TERM: flatten the trans spine and infer the type of each leaf.  That is
the whole mechanism — no tactic state is replayed, and the picture chain is therefore exactly the
chain the kernel accepted.

The spine is not always at the top: `conv_comp` is `(conv_unique ?_).symm` with the `calc` inside the
hole, so `bestChain` searches for the LONGEST spine anywhere in the term. -/

/-- One step: the relation symbol and the two sides. -/
abbrev Step := String × Expr × Expr

mutual

/-- Flatten a trans spine, or fail.  `calc` elaborates to `Trans.trans`, but a proof written as
    `le_trans h₁ h₂` — which is most of `diag` — is a spine too, and the picture chain is the same
    either way. -/
partial def transChain (e : Expr) : MetaM (Option (Array Step)) := do
  match e.getAppFnArgs with
  | (``Trans.trans, args) | (``Eq.trans, args)
  | (``Freyd.Diag.OrderedCat.«≤_trans», args) | (``Freyd.Alg.le_trans, args) =>
    match lastTwo args with
    | some (f, g) => return some ((← chainOrLeaf f) ++ (← chainOrLeaf g))
    | none => return none
  | _ => return none

/-- The chain a proof contributes: its trans spine if it has one, else the single step it proves.
    `splitM`, not `split`: a hypothesis of a named predicate — `h : Total (R ∩ S)` — is a link like
    any other once the predicate is unfolded, and dropping it silently shortens the chain. -/
partial def chainOrLeaf (e : Expr) : MetaM (Array Step) := do
  match ← transChain e with
  | some c => return c
  | none =>
    let t ← (do pure (some (← Meta.inferType e))) <|> pure none
    match ← t.mapM splitM with
    | some (some st) => return #[st]
    | _ => return #[]

end

/-- The longest trans spine anywhere in `e`.  Depth-first over applications, lambdas and lets; a
    spine found at a node wins over anything nested inside its leaves, since that is the outermost
    calc and the one the author wrote. -/
partial def bestChain (e : Expr) : MetaM (Array Step) := do
  if let some c ← transChain e then return c
  -- A tactic-block `have h : T := …` is `letFun`, an APPLICATION whose last argument is a lambda;
  -- left to the `.app` case below, the auxiliary `have`'s chain would compete with the final one and
  -- the longer would win.  Descend into the BODY: the `have`s are scaffolding, the last tactic is
  -- the argument.  (`have` in a tactic block usually elaborates to `.letE` instead — same treatment
  -- just below.)
  if let (``letFun, #[t, _, _, f]) := e.getAppFnArgs then
    return ← Meta.withLocalDeclD (match f with | .lam n .. => n | _ => `h) t fun x =>
      bestChain (mkApp f x).headBeta
  match e with
  -- A lambda is NOT descended into.  Opening it would give the leaves free variables belonging to a
  -- scope that is gone by the time they are drawn, and every label would print as `_fvar.8`.  The
  -- caller opens the binders it means to, and renders inside that scope.
  | .lam .. => return #[]
  -- Opened as a local HYPOTHESIS, never substituted.  Substituting puts the `have`'s proof in the
  -- leaf position, and a leaf that is itself a `calc` gets flattened by `chainOrLeaf` — so a
  -- three-line argument standing on a thirteen-line reshaping lemma comes out as thirteen lines of
  -- that lemma.  As a hypothesis the leaf is an fvar whose TYPE is the one step it contributes.
  -- Safe to return from under the binder: those types are the closed statements, never the fvar.
  | .letE n t v b _ =>
    -- `isProof`, not `isProp` on the type: `Expr.isProp` asks whether the expression IS the literal
    -- `Prop`, which an equation between morphisms is not.  A `let` binding DATA is substituted as
    -- before — its value can occur in the statements, and an unsubstituted fvar would print as one.
    if ← Meta.isProof v then
      Meta.withLocalDeclD n t fun x => bestChain (b.instantiate1 x)
    else bestChain (b.instantiate1 v)
  | .mdata _ b | .proj _ _ b => bestChain b
  | .app f a => do
    let cf ← bestChain f
    let ca ← bestChain a
    return if ca.size > cf.size then ca else cf
  | _ => return #[]

/-! ### Emitting a page -/

/-- The generated file is BOTH a standalone page and an importable module: `pic` and `doc` are
    bound at the top, and a note that wants this picture in a table cell writes
    `#import "generated/<name>.typ": pic`.  Typst runs an imported module for its bindings and
    discards its content, so the page below costs the importer nothing — which is what keeps a note
    from ever redrawing by hand what the exporter already derives from the Lean statement. -/
def page (declName : Name) (doc : Option String) (body : String) (isChain := false)
    (extra : String := "") : String :=
  -- The docstring goes through `raw`: it is arbitrary prose, and `#`, `[`, `$`, `*` in it would
  -- otherwise be read as Typst markup.
  let docLet := match doc with
    | some d => "#let doc = " ++ typstString d ++ "\n"
    | none => "#let doc = none\n"
  "// GENERATED by `diag-export` — do not edit; regenerate with\n\
   //   ./scripts/diag-export " ++ (if isChain then "--proof " else "") ++ declName.toString ++ "\n\
   #import \"../strdiag.typ\": cetz, d, wire, gbox, delta, nabla, bang, unitR, bend, cap, cup, conv, meet, swap, tape, tape-fork, tape-join, capAt, cupAt, TINT\n\n"
    ++ docLet ++ (if isChain then "#let branches = " else "#let pic = ") ++ body
    ++ (if isChain then
          "#let pic = stack(dir: ttb, spacing: 14pt, ..branches.map(b => stack(dir: ttb, \
           spacing: 10pt, ..(if b.name == \"\" { () } else { (text(11pt)[*#b.name*],) }) \
           + b.steps)))\n" else "")
    ++ extra
    ++ "\n\
   #set page(width: auto, height: auto, margin: 12pt)\n\
   #set text(size: 10pt)\n\n\
   #text(11pt)[*`" ++ declName.toString ++ "`*]\n\n\
   #if doc != none { text(9pt, luma(90), raw(doc)) }\n\n\
   #pic\n"

/-- One canvas holding several drawings in a row, each preceded by the symbol that introduces it —
    the first by nothing.  A statement is two of these; a `↔` between two statements is four, and
    that is the only reason this is n-ary rather than a pair. -/
def canvasOfParts (parts : Array (String × Expr)) : MetaM String := do
  let mut out := ""
  let mut x := 0.0
  for (sym, e) in parts do
    if !sym.isEmpty then
      -- Set large: at body size a relation symbol reads as a stray mark between two pictures
      -- rather than as the assertion the whole statement is about.
      out := out ++ s!"  d.content(({fmt (x + 0.45)}, 0), text(17pt)[{sym}])\n"
      x := x + 0.90
    let (d, xend) := renderCells (← toCells e) x
    out := out ++ d ++ "\n"
    x := xend
  return "cetz.canvas({\n" ++ out ++ "})\n"

/-- One canvas for a statement given as its relation and two sides. -/
def canvasOf (sym : String) (lhs rhs : Expr) : MetaM String :=
  canvasOfParts #[("", lhs), (sym, rhs)]

/-- One canvas for a single TERM of a chain, with the relation symbol that reaches it set to its
    left.  The first term of a chain has no symbol; the room for one is still reserved, so a column
    of these lines up. -/
def canvasOfTerm (sym : Option String) (e : Expr) : MetaM String := do
  let (d, _) := renderCells (← toCells e) SYMCOL
  let head := match sym with
    | some s => s!"  d.content((0.30, 0), text(17pt)[{s}])\n"
    | none => ""
  return "cetz.canvas({\n" ++ head ++ d ++ "\n})\n"

/-- One branch of a proof, rendered: its `steps` canvases and its `terms` strings, as a Typst
    dictionary.  Rendering happens HERE, inside whatever scope opened the branch's binders, which is
    what keeps `R` and `f` from printing as `_fvar.8`. -/
def renderBranch (name : String) (chain : Array Step) : MetaM String := do
  let (_, first, _) := chain[0]!
  let mut rows := #["      " ++ (← canvasOfTerm none first).trimAsciiEnd.toString ++ ","]
  -- The term column comes off the SAME walk as the picture, so the two cannot drift apart.
  let mut terms := #["      " ++ typstString (← label first) ++ ","]
  for (sym, _, r) in chain do
    rows := rows.push ("      " ++ (← canvasOfTerm (some sym) r).trimAsciiEnd.toString ++ ",")
    terms := terms.push ("      " ++ typstString (sym ++ " " ++ (← label r)) ++ ",")
  return "  (name: " ++ typstString name ++ ",\n   steps: (\n"
    ++ String.intercalate "\n" rows.toList ++ "\n   ),\n   terms: (\n"
    ++ String.intercalate "\n" terms.toList ++ "\n   )),"

/-- Draw a PROOF: its chain of steps, ONE CANVAS PER TERM.

    Not one per step.  A chain is `a₀ R a₁ R a₂ …`, so the right-hand side of every step is the
    left-hand side of the next — drawing steps means drawing every term twice and leaves the reader
    matching pictures across rows to see they are the same picture.  A column of terms, each with
    the symbol that reaches it, is how the `calc` reads in the source and how the argument reads on
    the page.

    An `↔` proved by `Iff.intro` is TWO chains and comes out as two named branches; drawing only the
    longer of them would silently drop half the proof. -/
def drawProof (declName : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "no such declaration: {declName}"
  let some val := ci.value?
    | throwError "{declName} has no value to walk — it is an axiom or a class field"
  let doc := (← findDocString? env declName).map fun d =>
    (d.splitOn "\n").headD "" |>.replace "`" "" |>.replace "*" ""
  let blocks ← Meta.lambdaTelescope val fun _ body => do
    let one (name : String) (br : Expr) : MetaM (Array String) :=
      Meta.lambdaTelescope br fun _ bb => do
        let c ← bestChain bb
        if c.isEmpty then return #[] else return #[← renderBranch name c]
    match body.getAppFnArgs with
    | (``Iff.intro, args) =>
      match lastTwo args with
      | some (mp, mpr) => return (← one "⟹" mp) ++ (← one "⟸" mpr)
      | none => one "" body
    | _ => one "" body
  if blocks.isEmpty then
    throwError "{declName}: no chain of `Trans.trans`/`le_trans` steps in the proof term"
  return page declName doc ("(\n" ++ String.intercalate "\n" blocks.toList ++ "\n)\n")
    (isChain := true)

/-- Draw the statement of `declName`: the two sides side by side, the relation symbol between.  A
    `def` whose telescope ends in `Prop` — `SingleValued`, `Total`, … — has no statement in its TYPE,
    so its VALUE is drawn instead; that is the inequation the definition unfolds to. -/
def draw (declName : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "no such declaration: {declName}"
  Meta.forallTelescopeReducing ci.type fun xs tybody => do
    let doc := (← findDocString? env declName).map fun d =>
      (d.splitOn "\n").headD "" |>.replace "`" "" |>.replace "*" ""
    -- BETA only, never `whnf`: `whnf` keeps going past `LE.le` into the `OrderedCat` projection it
    -- is a field of, and the whole inequation then prints as one opaque box.  Unfolding the
    -- definition is all that is wanted; its body is already `_ ≤ _`.
    let body := if tybody.isProp && (split tybody).isNone then
        match ci.value? with
        | some v => (mkAppN v xs).headBeta
        | none => tybody
      else tybody
    match ← splitM body with
    | some (sym, lhs, rhs) =>
      return page declName doc (← canvasOf sym lhs rhs)
    | none =>
      -- An `↔` between two containments — the shunting rules — is four drawings in a row.
      match body.getAppFnArgs with
      | (``Iff, #[l, r]) =>
        match ← splitM l, ← splitM r with
        | some (s₁, a, b), some (s₂, c, d) =>
          -- The two SIDES are bound as well as the whole `⟺`.  A proof of an `↔` runs one side to
          -- the other, so a note presenting that proof wants each side on its own — as the
          -- hypothesis of one branch and the goal of the other.
          let sides := "#let lhs = " ++ (← canvasOf s₁ a b) ++ "#let rhs = " ++ (← canvasOf s₂ c d)
          return page declName doc (← canvasOfParts #[("", a), (s₁, b), ("⟺", c), (s₂, d)])
            (extra := sides)
        | _, _ => throwError "{declName}: an `↔` whose sides are not containments"
      | _ =>
        let (d, _) := renderCells (← toCells body) 0.0
        return page declName doc ("cetz.canvas({\n" ++ d ++ "\n})\n")

/-! ### Driver -/

/-- Every `diag.*` module except this tool, so the exporter can name any declaration of the tower
    without the caller listing imports. -/
partial def diagModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "tool" && e.fileName != "generated" then
        out := out ++ (← diagModules e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

def usage : String :=
  "usage: diag-export [--proof] <declaration-name> [<declaration-name> ...]\n\
   writes diag/generated/<name>.typ per declaration and prints each path\n\
   --proof draws the calc chain of each PROOF instead of the statement, to <name>.proof.typ"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then IO.eprintln usage; return 2
  let proofMode := args.contains "--proof"
  let args := args.filter (· != "--proof")
  if args.isEmpty then IO.eprintln usage; return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := #[`Freyd] ++ (← diagModules "diag" `diag)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  IO.FS.createDirAll "diag/generated"
  -- `≫` and `⟶` are `scoped` in `Freyd`, so the delaborator only reaches them with that namespace
  -- opened; without this a fallthrough label prints `inst✝.comp R S`.
  -- Generalized field notation prints a class projection through its instance argument, so `Δ_a`
  -- comes out as `inst✝.delta a`.  The instance is anonymous inside a `forallTelescope`, so that is
  -- worse than useless in a picture; off, it prints `CartBicat.delta a` and the strip in `plain`
  -- takes the namespace.
  let opts : Options :=
    (Options.empty.setBool `pp.fieldNotation false).setBool `pp.fieldNotation.generalized false
  let ctx : Core.Context :=
    { fileName := "<diag-export>", fileMap := default,
      options := opts,
      -- `≫` and `⟶` live in `Freyd`, `⊗ₕ` in `Freyd.Diag.SymMonCat`, `⊗`/`𝕀` in `Freyd.Diag.Word`.
      openDecls := [.simple `Freyd [], .simple `Freyd.Diag.SymMonCat [],
        .simple `Freyd.Diag.Word []] }
  let mut status : UInt32 := 0
  for arg in args do
    let run : CoreM String :=
      Meta.MetaM.run' (if proofMode then drawProof arg.toName else draw arg.toName)
    match ← (do pure (some (← Prod.fst <$> run.toIO ctx { env }))) <|> pure none with
    | none =>
      IO.eprintln s!"diag-export: cannot draw `{arg}` — no such declaration in `Freyd` or `diag.*`, \
        or (with --proof) no calc chain in its proof term"
      status := 1
    | some text =>
      let path := System.FilePath.mk s!"diag/generated/{arg}{if proofMode then ".proof" else ""}.typ"
      IO.FS.writeFile path text
      IO.println path.toString
  return status

end Freyd.DiagExport

def main (args : List String) : IO UInt32 := Freyd.DiagExport.main args
