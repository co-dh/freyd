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
  the second monoidal product; `Allegory.recip`/`Diag.conv` draw the mirrored box.  At the top,
  `Alg.le` (`⊑`), `LE.le` (`≤`) and `Eq` split the statement into two pictures with the symbol
  between them.

  NEGATION IS A CUT, NOT A BOX.  `DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 2: given `c`, "take
  its mirror image and then its photographic negative" — that is `c⊥`; and p. 10, on translating
  Peirce's existential graphs, "each cut [is] a color switch".  So `Alg.neg`, `LinearBicat.bcomp`
  and `ClosedLinearBicat.perp` draw REGIONS on the other colour, and `Diag.residual`, which is
  `R ⨟• S⊥` by definition, is unfolded and drawn as one: `R` on black with `S` mirrored in a white
  island.  Nesting alternates the ground — Peirce's double cut — so `∼∼R = R` is two grounds
  cancelling.  A box labelled `R / S` would have said only what the term beside it already says,
  which is what an earlier version of this file drew.

  THE ALLEGORY LAYER IS RECOGNISED TOO.  `DistributiveAllegory.union` is the tape and `Alg.neg` the
  cut, so B&dM §4.4–4.5 draws.  The tape is the picture of `∪`, not a claim that a distributive
  allegory carries the biproduct `diag/Tape.lean` builds it from; `distributiveAllegoryOfFbCb` is
  what makes the two `∪`s the same operation.

  DIVISION DRAWS AS LONG DIVISION.  `DivisionAllegory.div` has no definition to unfold — it is a
  class field — but that is a reason to draw its universal property, not a reason to print the term
  twice, which a dashed box reading `R / S` beside a term column reading `R / S` does.  `divbox`
  keeps the chamfered outline, so it wires up and says which way it runs, and puts the numerator's
  ground, the divisor laid inside it and a hairline of slack where the label was.  `leftDiv` is the
  mirror.  This is the one account of `/` in the tower that needs NO complement, which matters:
  a division allegory need not be Boolean, so the cut picture of `residual` is not available at that
  generality and this one is.  Still DASHED, having neither a definition nor a quotient metaphor:
  `symmDiv`, `impl` and `thenRel`.

  A converse's operand is still a single box: `strdiag.typ`'s mirrored `gbox` takes a LABEL, so a
  composite under a `°` appears as one box reading `R S`.

  ONE ENVIRONMENT PER PROCESS — the `lean-refactor` OOM lesson (`Freyd/tool/LeanRefactor.lean`):
  `importModules` retains its environment for the life of the process, so this exe imports once and
  handles every declaration named on the command line from that one environment.
-/
import Lean
import diag.FO
import diag.Tape
import diag.S2_124
-- The allegory layer's division and negation (B&dM §4.4–4.5), so `Alg.neg`, `Alg.impl` and
-- `Alg.thenRel` are names this file can quote.  `AOP.A4_5` pulls `AOP.A4_4` and the `Freyd` core.
import AOP.A4_5

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
/-- How far a cut's ground extends past the circuit inside it.  Wider than `TAPEPAD`: the tape has an
    edge stroke to read against, a cut has only the colour change. -/
def CUTPAD : Float := 0.30
/-- How far a cap's or a cup's strands bend over. -/
def CAPBEND : Float := 0.60
/-- `strdiag.typ`'s `SPLIT`: the stub between the two dots of a cap (`▷` then `⊸`) or a cup (`⟜`
    then `◁`).  They are drawn split, as the paper draws the converse. -/
def SPLITW : Float := 0.34
/-- How much wider each further arc of a cap at a PRODUCT object bends.  The arcs of such a cap
    interleave rather than nest — `cap_{m⊗n}` joins the first `m` to the third and the second `n` to
    the fourth — so drawing them at one bend width would lay their vertical segments on top of each
    other and read as a single bracket.  One crossing per extra arc is the honest picture, and it is
    the picture `cap_tens` states: two caps behind a crossing. -/
def ARCSTEP : Float := 0.30
/-- A cap or cup occupies its widest bend plus that stub. -/
def capW (n : Nat) : Float := CAPBEND + (n.toFloat - 1.0) * ARCSTEP + SPLITW
/-- The column a chain's relation symbol sits in, to the left of every term. -/
def SYMCOL : Float := 0.95
/-- The strand offset a fork, a cap and a cup open by, and the pitch new lanes are opened at.  A `⊗`
    may sit wider: `meetSep` grows with what is nested in its runs. -/
def STACKSEP : Float := 0.62
/-- `strdiag.typ`'s `conv` geometry: how far the snake climbs from its incoming strand to its
    outgoing one, and the fixed width its two bends and stubs cost around the box.

    NOT `conv-w`, which is one `SPLIT` wider than what `conv` actually draws — its outgoing wire
    stops at `0.28 + SPLIT + 2·arc + w + lead`.  The note only ever set a snake on its own, where
    trailing air costs nothing; in a run it is a gap between the snake and whatever follows, and the
    joining wire starts after it.  That gap is what made the first snake pictures look unwired. -/
def RISE : Float := 1.6
def CONVPAD : Float := 0.28 + 0.34 + 2.0 * 0.78 + 0.40

/-- One left-to-right slot of a picture. -/
inductive Cell where
  | wire
  | box (label : String)
  /-- A generator `strdiag.typ` draws directly.  `lead` is the distance from this cell's LEFT EDGE
      to the anchor the drawing function wants: `delta`, `nabla` and `bang` hang their incoming stub
      to the LEFT of that anchor, so passing the left edge straight through leaves the wire hanging
      in mid-air — which is what disconnected `▷ ◁` pictures were. -/
  | gen (fn : String) (width lead : Float)
  /-- A meet, drawn as the nested picture `◁ (upper ⊗ lower) ▷`, not as a box with a label.
      Nesting is why the operands are cell RUNS: `(R ∩ S) ∩ T` has to show its inner meet. -/
  | meet (upper lower : Array Cell)
  /-- A union (phase 8, `diag/Tape.lean`), drawn as a TAPE: the same fork-runs-join shape as a meet,
      but on the second monoidal product, so it is the tape's `Δ⊕`/`∇⊕` and not the Frobenius `◁`/`▷`
      (`TapeDiagrams.pdf` Fig. 1).  A particle takes exactly one branch, which is the union. -/
  | union (upper lower : Array Cell)
  /-- A box the calculus cannot build out of its generators — the residual `R / S` of phase 9
      (`diag/FO.lean`), which needs the second composition and the linear adjoint.  `strdiag.typ`
      reserves the dashed frame for exactly this. -/
  | dbox (label : String)
  /-- `R / S`, drawn as long division: a chamfered box like any other, whose interior is the
      numerator's ground with the divisor laid inside it and a hairline of slack past it.  What
      replaced a dashed box reading `R / S`, which said only what the term column already said.
      `flip` mirrors chamfer and tile together, for left division. -/
  | divbox (num den : String) (flip : Bool)
  /-- A CUT: the run drawn on the other colour.  This is how
      `DiagrammaticAlgebraOfFirstOrderLogic.pdf` writes complement — p. 2, "take its mirror image and
      then its photographic negative", and p. 10, "each cut [is] a color switch" — so `∼R`, the black
      composition `⨟•` and hence the residual are REGIONS, not boxes with the operator printed in
      them.  A box labelled `R / S` says only what the term already says.
      Cuts nest, and nesting alternates the ground: that is Peirce's double cut, and it is why
      `R / S = ∼(∼R S°)` comes out as a white island inside a black region. -/
  | cut (inner : Array Cell)
  /-- A monoidal product `f ⊗ g`, drawn as the two runs STACKED — no fork, no join, since `⊗` puts
      two arrows side by side rather than copying one.  This is what makes a proof about bent wires
      readable: `𝟙 ⊗ S°` is a wire above a mirrored box, not an opaque label. -/
  | stack (upper lower : Array Cell)
  /-- The cap `▷ ⊸` and the cup `⟜ ◁`, in `strdiag.typ`'s `capAt`/`cupAt` one-anchor form.  A cap
      takes a pair on the left and gives nothing on the right; a cup is its mirror.

      `n` is the WIDTH OF THE OBJECT, so `cap` at a two-letter word is two arcs and not one: it
      takes four strands and joins the first to the third, the second to the fourth.  Drawing it as
      a single arc was silently wrong — the picture ended two strands short of the term. -/
  | capC (n : Nat)
  | cupC (n : Nat)
  /-- A converse: the same box MIRRORED, which is how
      functorialSemanticsForRelationalTheories.pdf writes `†`.  `dashed` when the operand would have
      been a `dbox`: `(R /ₛ S)°` is a converse OF a construct the generators cannot build, and
      dropping the frame on the way through the mirror would draw the two sides of
      `(R /ₛ S)° = S /ₛ R` as two different kinds of thing. -/
  | dagger (label : String) (dashed : Bool)
  /-- A MAP, drawn as a plain rectangle.  The chamfer says which way a relation runs; a map runs one
      way by construction, so there is nothing for the corner to disambiguate, and dropping it makes
      the maps findable at a glance — which is what shunting, and most of the division laws, turn
      on.  Recognised from the LOCAL CONTEXT: a statement that quantifies over `f` with a hypothesis
      `Map f` is the only place the walk can learn it, and inside the telescope that hypothesis is
      simply there to be read. -/
  | mbox (label : String)

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
  -- `Inhabited` because `leftPort`/`rightPort` are `partial`: a cut reports its CONTENTS' ports, and
  -- the recursion through nested cuts is what Lean cannot see terminating.
  deriving BEq, Inhabited

/-- Whether this cell's ports sit off the centre line, which is true of exactly the snake. -/
def Cell.isDagger : Cell → Bool
  | .dagger _ _ => true
  | _ => false

partial def Cell.leftPort : Cell → Port
  | .gen "nabla" _ _ | .gen "swap" _ _ => .pair
  | .gen "unitR" _ _ | .cupC _ => .nothing
  | .stack _ _ | .capC _ => .strands
  -- A cut is transparent to wiring: what meets its left edge is whatever its contents meet.
  | .cut inner => match inner[0]? with | some c => c.leftPort | none => .one
  | _ => .one

partial def Cell.rightPort : Cell → Port
  | .gen "delta" _ _ | .gen "swap" _ _ => .pair
  | .gen "bang" _ _ | .capC _ => .nothing
  | .stack _ _ | .cupC _ => .strands
  | .cut inner => match inner.back? with | some c => c.rightPort | none => .one
  | _ => .one

/-- A box has to hold its label.  `strdiag.typ`'s default `BW` fits about six characters at 10pt;
    anything longer widens the box rather than spilling out of it. -/
def boxWidth (l : String) : Float := max BW (0.225 * l.length.toFloat + 0.30)

/-- The divisor tile inside a `divbox`, and the box that has to hold it beside the numerator.
    Same per-character figure as `boxWidth`, one size down, since the tile's label is set at 8pt. -/
def denWidth (l : String) : Float := max 0.62 (0.185 * l.length.toFloat + 0.22)
def divboxWidth (num den : String) : Float := boxWidth num + denWidth den + 0.34

mutual

partial def Cell.width : Cell → Float
  | .wire => wireW
  | .box l | .dbox l | .mbox l => boxWidth l
  | .gen _ w _ => w
  | .meet u l => 2.0 * FORK + max (runWidth u) (runWidth l)
  | .union u l => 2.0 * FORK + 2.0 * TAPEPAD + max (runWidth u) (runWidth l)
  | .stack u l => max (runWidth u) (runWidth l)
  | .capC n | .cupC n => capW n
  | .dagger l _ => CONVPAD + boxWidth l
  | .divbox n dn _ => divboxWidth n dn
  | .cut inner => 2.0 * CUTPAD + runWidth inner

/-- The horizontal room between two adjacent cells: none when two forks face each other, since they
    abut into one bubble. -/
partial def joinGap (c next : Cell) : Float :=
  if c.rightPort == .pair && next.leftPort == .pair then 0.0
  -- A snake leaves `RISE` above where the next cell wants its strand, and a bend that has to fall
  -- that far inside `GAP` comes out as a near-vertical hook.  Give it room proportional to the drop.
  else if c.isDagger || next.isDagger then GAP + RISE / 2.0
  else GAP

/-- A run of cells wired in series, without the outer stubs a whole picture gets. -/
partial def runWidth (cells : Array Cell) : Float := Id.run do
  let mut w := 0.0
  for i in [0 : cells.size] do
    w := w + cells[i]!.width
    if h : i + 1 < cells.size then w := w + joinGap cells[i]! cells[i + 1]
  return w

/-- How far a cell reaches ABOVE the lane it is entered at, and how far BELOW.  Not one number: the
    snake is entered at its lane and left `RISE` higher, so it reaches up and not down, and a `⊗`
    that reserved the same room on either side of it would hold its other operand a whole rise clear
    of nothing.  What has to be kept apart is the DOWNWARD reach of the upper operand and the UPWARD
    reach of the lower one, which is what `meetSep` adds up. -/
partial def Cell.spanUp : Cell → Float
  | .meet u l | .stack u l => meetSep u l + runSpanUp u
  | .union u l => meetSep u l + runSpanUp u + TAPEPAD
  | .capC n | .cupC n => (2.0 * n.toFloat - 1.0) * STACKSEP + BH / 2.0
  | .gen "delta" _ _ | .gen "nabla" _ _ => STACKSEP
  | .cut inner => runSpanUp inner + CUTPAD
  | .dagger _ _ => RISE + BH / 2.0
  | _ => BH / 2.0

partial def Cell.spanDown : Cell → Float
  | .meet u l | .stack u l => meetSep u l + runSpanDown l
  | .union u l => meetSep u l + runSpanDown l + TAPEPAD
  | .capC n | .cupC n => (2.0 * n.toFloat - 1.0) * STACKSEP + BH / 2.0
  | .gen "delta" _ _ | .gen "nabla" _ _ => STACKSEP
  | .cut inner => runSpanDown inner + CUTPAD
  | _ => BH / 2.0

/-- How many strands a cell takes from upstream, and how many it hands downstream.  The COUNT is
    all that is structural: WHERE those strands sit is threaded along the run, cell by cell, and is
    not a property of any one cell.  A `⊗` of a fork and a wire takes one strand and gives three. -/
partial def Cell.leftCount : Cell → Nat
  | .gen "nabla" _ _ | .gen "swap" _ _ => 2
  | .capC n => 2 * n
  | .gen "unitR" _ _ | .cupC _ => 0
  | .stack u l => runLeftCount u + runLeftCount l
  | .cut inner => runLeftCount inner
  | _ => 1

partial def Cell.rightCount : Cell → Nat
  | .gen "delta" _ _ | .gen "swap" _ _ => 2
  | .cupC n => 2 * n
  | .gen "bang" _ _ | .capC _ => 0
  | .stack u l => runRightCount u + runRightCount l
  | .cut inner => runRightCount inner
  | _ => 1

partial def runLeftCount (cells : Array Cell) : Nat :=
  match cells[0]? with | some c => c.leftCount | none => 1
partial def runRightCount (cells : Array Cell) : Nat :=
  match cells.back? with | some c => c.rightCount | none => 1

partial def runSpanUp (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => max acc c.spanUp) (BH / 2.0)
partial def runSpanDown (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => max acc c.spanDown) (BH / 2.0)

/-- What a cell needs its two strands separated by: a `⊗` by `meetSep`, so its runs clear each
    other; a fork, a swap, a cap and a cup by nothing in particular. -/
partial def Cell.natSep : Cell → Float
  | .stack u l => meetSep u l
  | _ => STACKSEP

/-- HALF THE PITCH A RUN OPENS NEW LANES AT.  Only the cells that CREATE strands consult it — a
    fork, a cup, and a `⊗` reserving room for an operand upstream handed nothing to.  One number per
    run, the widest any cell needs, so lanes opened at one point of the run clear whatever is nested
    further along it. -/
partial def runSep (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => max acc c.natSep) STACKSEP

/-- The offset of each strand of a meet from its centre line: enough that the two runs clear each
    other by `STRANDGAP`.  At the leaves this is `strdiag.typ`'s own `0.62`. -/
partial def meetSep (u l : Array Cell) : Float :=
  (runSpanDown u + runSpanUp l + STRANDGAP) / 2.0

/-- How far a cell reaches above the FIRST lane it is handed, and below the LAST.

    Not `spanUp`/`spanDown`, which are both measured from the entry lane: for a cell that takes
    SEVERAL lanes they therefore contain the spread between those lanes, and feeding that back into
    the gap between them counts it twice.  `((𝟙 ⊗ R°) cap) ⊗ ((𝟙 ⊗ S°) cap)` is where it showed:
    each operand needs `2.84` between its own two lanes, and the two operands then need `4.08`
    between them — measured from the wrong ends, `1.72 + 1.72 + 0.64`, when nothing at all is drawn
    outside the four lanes and `1.24` is enough.  Every lane in the picture was pitched at the
    worst of those, so a crossing came out looking like a bracket. -/
partial def Cell.edgeUp : Cell → Float
  | .stack u l => if runLeftCount u == 0 then runEdgeUp l else runEdgeUp u
  | .meet u l => meetSep u l + runSpanUp u
  | .union u l => meetSep u l + runSpanUp u + TAPEPAD
  | .cupC n => (2.0 * n.toFloat - 1.0) * STACKSEP + BH / 2.0
  | .gen "delta" _ _ => STACKSEP
  | .cut inner => runEdgeUp inner + CUTPAD
  | .dagger _ _ => RISE + BH / 2.0
  | _ => BH / 2.0

partial def Cell.edgeDown : Cell → Float
  | .stack u l => if runLeftCount l == 0 then runEdgeDown u else runEdgeDown l
  | .meet u l => meetSep u l + runSpanDown l
  | .union u l => meetSep u l + runSpanDown l + TAPEPAD
  | .cupC n => (2.0 * n.toFloat - 1.0) * STACKSEP + BH / 2.0
  | .gen "delta" _ _ => STACKSEP
  | .cut inner => runEdgeDown inner + CUTPAD
  | _ => BH / 2.0

/-- How far a cell LIFTS the first lane it is handed, and the last.  Only the converse lifts
    anything: it is entered at its lane and left `RISE` higher, and everything after it runs at the
    new height. -/
partial def Cell.riseFirst : Cell → Float
  | .dagger _ _ => RISE
  | .stack u _ => runRiseFirst u
  | .cut inner => runRiseFirst inner
  | _ => 0.0

partial def Cell.riseLast : Cell → Float
  | .dagger _ _ => RISE
  | .stack _ l => runRiseLast l
  | .cut inner => runRiseLast inner
  | _ => 0.0

partial def runRiseFirst (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => acc + c.riseFirst) 0.0
partial def runRiseLast (cells : Array Cell) : Float :=
  cells.foldl (fun acc c => acc + c.riseLast) 0.0

/-- A run's reach, ACCUMULATING the lifts on the way: the second converse of `S° R°` starts a whole
    `RISE` above where the first one did, so the two of them in series reach twice as far as either.
    Taken as a plain maximum, the lane above them was opened for one rise, the second output
    overshot it, and the cap that closes the two came out inside out — `sp` negative, a 0.36-high
    hook over strands 3.2 apart. -/
partial def runEdgeUp (cells : Array Cell) : Float := Id.run do
  let mut drift := 0.0
  let mut reach := BH / 2.0
  for c in cells do
    reach := max reach (drift + c.edgeUp)
    drift := drift + c.riseFirst
  return reach

partial def runEdgeDown (cells : Array Cell) : Float := Id.run do
  let mut drift := 0.0
  let mut reach := BH / 2.0
  for c in cells do
    reach := max reach (c.edgeDown - drift)
    drift := drift + c.riseLast
  return reach

/-- THE GAP EACH ADJACENT PAIR of a cell's incoming lanes needs — one number per pair, not one
    number for the picture.  A `⊗` is the only cell that divides the lanes it is handed between two
    runs, so it is the only one with anything to say; everything else wants the plain pitch. -/
partial def Cell.laneGaps : Cell → Array Float
  | .stack u l =>
    if runLeftCount u == 0 then runLaneGaps l
    else if runLeftCount l == 0 then runLaneGaps u
    else (runLaneGaps u |>.push (runEdgeDown u + runEdgeUp l + STRANDGAP)) ++ runLaneGaps l
  | .cut inner => runLaneGaps inner
  | c => Array.replicate (c.leftCount - 1) (2.0 * STACKSEP)

/-- The run's lane gaps: what its cells need, pair by pair.  Only the first cell is handed the run's
    own lanes, but the later ones inherit their positions, so each has a say — pairwise, and from
    the top, which is how a `⊗` divides them.  Where a cell takes fewer lanes than the run does
    there is nothing to line its gaps up with, and those pairs keep the plain pitch. -/
partial def runLaneGaps (cells : Array Cell) : Array Float := Id.run do
  let mut g := Array.replicate (runLeftCount cells - 1) (2.0 * STACKSEP)
  for c in cells do
    let gc := c.laneGaps
    for i in [0 : min g.size gc.size] do g := g.set! i (max g[i]! gc[i]!)
  return g

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

/-- `, invert: true` when the ground under this primitive is black, and nothing when it is white.
    Every drawing function in `strdiag.typ` takes the same flag on the same axis, so one suffix
    serves them all. -/
def inv (b : Bool) : String := if b then ", invert: true" else ""

/-- A horizontal wire, or nothing when the two ends coincide — a zero-length `wire` draws a blob at
    the joint. -/
def hwire (x₀ x₁ y : Float) (iv : Bool := false) : Array String :=
  if x₁ - x₀ > 0.005 then #[s!"  wire(({fmt x₀}, {fmt y}), ({fmt x₁}, {fmt y}){inv iv})"] else #[]

/-- What laying a run out produced: the drawing, the lane positions it hands DOWNSTREAM, and the
    lowest and highest strand it touched — which is what an enclosing `⊗` needs in order to put its
    other operand clear of it. -/
structure Lay where
  out : Array String
  ys : Array Float
  lo : Float
  hi : Float
  deriving Inhabited

mutual

/-- One operand run of a meet, a stack or a tape: centred in the shared inner width `iw`, entered at
    the heights `ys` it is handed and left at the heights it hands on, with a flat stub to each edge
    of the shared width.  The stubs are flat because the run neither moved the strands nor may: a
    strand is where upstream put it. -/
partial def layStrand (run : Array Cell) (x₁ iw : Float) (ys : Array Float) (anchor : Float)
    (iv : Bool) : Lay := Id.run do
  let w := runWidth run
  let l₀ := x₁ + (iw - w) / 2.0            -- where this run's cells begin
  let b := renderRun run l₀ ys anchor iv
  let mut out := #[]
  for y in ys do out := out ++ hwire x₁ l₀ y iv
  out := out ++ b.out
  for y in b.ys do out := out ++ hwire (l₀ + w) (x₁ + iw) y iv
  return { b with out }

/-- Lay one cell out at `x`, entered at the lane heights `ys`.

    `anchor` is where to put a strand there is no upstream lane for — a cup creates two strands out
    of nothing, so only its surroundings can say where they go — and `sep` is the half-pitch the run
    opens new lanes at.  Everything else follows from `ys`: a fork opens either side of the strand it
    is handed, a merge closes on the midpoint of the two it is handed, a cap bends over exactly the
    two that arrive. -/
partial def Cell.lay (c : Cell) (x : Float) (ys : Array Float) (anchor sep : Float)
    (iv : Bool) : Lay :=
  let y := (ys[0]?).getD anchor
  let y₂ := (ys[1]?).getD (y - 2.0 * sep)
  let mid := (y + y₂) / 2.0
  let half := (y - y₂) / 2.0
  match c with
  | .wire => ⟨hwire x (x + wireW) y iv, #[y], y, y⟩
  | .box l =>
    ⟨#[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH}{inv iv})"],
     #[y], y, y⟩
  | .mbox l =>
    ⟨#[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH}, \
        chamfer: false{inv iv})"], #[y], y, y⟩
  | .gen fn w lead =>
    -- A generator is drawn at the lanes it is actually wired to, and REPORTS those lanes, so what
    -- it offers is what its neighbour expects and the two meet as a straight wire.  Never a
    -- `strdiag.typ` default: those are not all `STACKSEP` — `swap`'s is 0.33 — and a generator drawn
    -- at one separation while reporting another abuts a fork whose prongs are somewhere else, which
    -- is what left the swap in `◁ σ = ◁` hanging beside the copy that feeds it.  The swap also
    -- spans its cell, or the wires into it stop short of the crossing.
    let ay := if fn == "nabla" || fn == "swap" then mid else y
    let sp :=
      if fn == "delta" then s!", sp: {fmt sep}"
      else if fn == "nabla" then s!", sp: {fmt half}"
      else if fn == "swap" then s!", sp: {fmt half}, w: {fmt w}"
      else ""
    let draw := #[s!"  {fn}(({fmt (x + lead)}, {fmt ay}){sp}{inv iv})"]
    match fn with
    | "delta" => ⟨draw, #[y + sep, y - sep], y - sep, y + sep⟩
    | "nabla" => ⟨draw, #[mid], y₂, y⟩
    | "swap" => ⟨draw, #[y, y₂], y₂, y⟩
    | "bang" => ⟨draw, #[], y, y⟩
    | _ => ⟨draw, #[y], y, y⟩
  -- Tinted as well as mirrored: see `TINT` in `strdiag.typ`.  A chain whose whole content is a box
  -- crossing a bend and coming back upright has to show that at a glance, not on inspection of
  -- which corner is chamfered.  On black ground the tint is dropped: `invert` supplies the paper.
  -- THE SNAKE, and it is the only drawing of a converse in this file.  It is the one cell that
  -- hands its strand on at a different height from the one it took: `conv` enters low and leaves
  -- `RISE` higher, and everything after it simply runs at the new height.
  | .dagger l dashed =>
    let dsh := if dashed then ", dashed: true" else ""
    ⟨#[s!"  conv(({fmt x}, {fmt y}), {labelContent l}, \
        w: {fmt (boxWidth l)}, h: {fmt BH}{dsh}{inv iv})"], #[y + RISE], y, y + RISE⟩
  | .dbox l =>
    ⟨#[s!"  gbox(({fmt x}, {fmt y}), {labelContent l}, w: {fmt (boxWidth l)}, \
        h: {fmt BH}, dashed: true{inv iv})"], #[y], y, y⟩
  | .divbox n dn flip =>
    let fl := if flip then ", flip: true" else ""
    ⟨#[s!"  divbox(({fmt x}, {fmt y}), {labelContent n}, {labelContent dn}, \
        w: {fmt (divboxWidth n dn)}, h: {fmt BH}, denw: {fmt (denWidth dn)}{fl}{inv iv})"],
     #[y], y, y⟩
  -- A cap's second dot sits to the RIGHT of its bend, a cup's to the LEFT, so the cup is anchored
  -- one stub in from this cell's left edge.  The cap bends over the lanes that arrive; the cup,
  -- with nothing arriving, opens either side of the anchor its surroundings reserved for it.
  --
  -- ARC `i` OF `k` JOINS LANE `i` TO LANE `i + k`, which is what `cap_{m⊗n}` does — the first `m`
  -- to the third strand, the second `n` to the fourth — and each further arc bends `ARCSTEP` wider
  -- so the crossing that pairing implies is drawn as a crossing instead of as overlapping ink.
  | .capC k => Id.run do
    let mut out := #[]
    for i in [0 : k] do
      let ya := (ys[i]?).getD y
      let yb := (ys[i + k]?).getD y₂
      out := out.push s!"  capAt(({fmt x}, {fmt ((ya + yb) / 2.0)}), sp: {fmt ((ya - yb) / 2.0)}, \
        w: {fmt (CAPBEND + i.toFloat * ARCSTEP)}{inv iv})"
    return ⟨out, #[], ys.foldl min y, ys.foldl max y⟩
  | .cupC k => Id.run do
    let mut out := #[]
    let mut lanes := #[]
    for i in [0 : k] do
      out := out.push s!"  cupAt(({fmt (x + SPLITW)}, {fmt (y + (k.toFloat - 1.0 - 2.0 * i.toFloat) * sep)}), \
        sp: {fmt (k.toFloat * sep)}, w: {fmt (CAPBEND + i.toFloat * ARCSTEP)}{inv iv})"
    for j in [0 : 2 * k] do lanes := lanes.push (y + (2.0 * k.toFloat - 1.0 - 2.0 * j.toFloat) * sep)
    let edge := (2.0 * k.toFloat - 1.0) * sep
    return ⟨out, lanes, y - edge, y + edge⟩
  | .stack u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let nu := min (runLeftCount u) ys.size
    let msep := meetSep u l
    let yu := ys.extract 0 nu
    let yl := ys.extract nu ys.size
    -- The operand upstream hands strands to is placed BY them; the other has nothing to be placed
    -- by, so it is put clear of the first — below it when it is the lower half of the `⊗`, above it
    -- when it is the upper half.  That is the whole of the vertical layout: no operand is centred
    -- on anything, so composing two `⊗`s that split their strands differently still meets flat.
    let (bu, bl) :=
      if yu.isEmpty && !yl.isEmpty then
        let bl := layStrand l x iw yl anchor iv
        (layStrand u x iw yu (bl.hi + 2.0 * msep) iv, bl)
      else
        let bu := layStrand u x iw yu anchor iv
        (bu, layStrand l x iw yl (bu.lo - 2.0 * msep) iv)
    return ⟨bu.out ++ bl.out, bu.ys ++ bl.ys, min bu.lo bl.lo, max bu.hi bl.hi⟩
  | .union u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let s := meetSep u l
    let top := y + s + runSpanUp u + TAPEPAD
    let bot := y - s - runSpanDown l - TAPEPAD
    let x₁ := x + TAPEPAD + FORK             -- where the tape's two branches begin
    let w := 2.0 * FORK + 2.0 * TAPEPAD + iw
    -- The tape carries its own colour, so its interior is white ground whatever is outside it.
    let bu := layStrand u x₁ iw #[y + s] (y + s) false
    let bl := layStrand l x₁ iw #[y - s] (y - s) false
    let a := (bu.ys[0]?).getD (y + s)
    let b := (bl.ys[0]?).getD (y - s)
    -- The wrapper is drawn FIRST so the circuit sits on top of it, not under it.
    let out := #[s!"  tape(({fmt x}, {fmt bot}), ({fmt (x + w)}, {fmt top}))",
      s!"  tape-fork(({fmt (x + TAPEPAD)}, {fmt y}), sp: {fmt s}, len: {fmt FORK})"]
      ++ bu.out ++ bl.out
      ++ #[s!"  tape-join(({fmt (x + w - TAPEPAD)}, {fmt ((a + b) / 2.0)}), \
        sp: {fmt ((a - b) / 2.0)}, len: {fmt FORK})"]
    return ⟨out, #[(a + b) / 2.0], bot, top⟩
  | .meet u l => Id.run do
    let iw := max (runWidth u) (runWidth l)
    let s := meetSep u l
    let x₁ := x + FORK                       -- where `Δ`'s two strands arrive
    let x₂ := x₁ + iw                        -- where `∇`'s two strands leave
    let bu := layStrand u x₁ iw #[y + s] (y + s) iv
    let bl := layStrand l x₁ iw #[y - s] (y - s) iv
    let a := (bu.ys[0]?).getD (y + s)
    let b := (bl.ys[0]?).getD (y - s)
    let out := #[s!"  delta(({fmt x}, {fmt y}), li: 0, lo: {fmt FORK}, sp: {fmt s}{inv iv})"]
      ++ bu.out ++ bl.out
      ++ #[s!"  nabla(({fmt (x₂ + FORK)}, {fmt ((a + b) / 2.0)}), li: {fmt FORK}, lo: 0, \
        sp: {fmt ((a - b) / 2.0)}{inv iv})"]
    return ⟨out, #[(a + b) / 2.0], min bl.lo (y - s), max bu.hi (y + s)⟩
  -- The cut.  Ground first, contents on top of it with the colour flipped, and a stub at each edge
  -- so the wire crosses the boundary instead of stopping at it — a cut is a region a strand passes
  -- through, not a box it ends on.
  | .cut inner => Id.run do
    let w := runWidth inner
    let top := y + runSpanUp inner + CUTPAD
    let bot := y - runSpanDown inner - CUTPAD
    let x₁ := x + CUTPAD
    let b := renderRun inner x₁ ys y (!iv)
    let mut out := #[s!"  cut(({fmt x}, {fmt bot}), ({fmt (x + w + 2.0 * CUTPAD)}, {fmt top})\
{inv iv})"] ++ b.out
    -- The stubs are drawn in the OUTER colour on the outer side of each edge; the inner run already
    -- carries its own.  Both are only a `CUTPAD` long, so drawing them in one colour is enough.
    for o in ys do out := out ++ hwire x x₁ o (!iv)
    for o in b.ys do out := out ++ hwire (x₁ + w) (x + w + 2.0 * CUTPAD) o (!iv)
    return ⟨out, b.ys, min b.lo bot, max b.hi top⟩

/-- Lay a run of cells out from `x0`, entered at the lane heights `ys`, THREADING those heights: each
    cell is handed what the one before it gave, so every joining wire is flat and no strand is ever
    bent back to a centre line it was never on.  Drawing each cell at a height computed from its own
    shape instead is what put three diagonal bends through the middle of the snake, where the same
    three strands leave one `⊗` and enter the next. -/
partial def renderRun (cells : Array Cell) (x0 : Float) (ys : Array Float) (anchor : Float)
    (iv : Bool) : Lay := Id.run do
  let sep := runSep cells
  let mut cur := ys
  let mut out := #[]
  -- `anchor` is where a strand goes when there is none to inherit; it is NOT part of the extent
  -- unless something is actually drawn there, or an operand a `⊗` reserved room below would drag
  -- the picture's centre down by room nothing occupies.
  let mut lo := (ys[0]?).getD anchor
  let mut hi := lo
  for y in ys do
    lo := min lo y
    hi := max hi y
  let mut x := x0
  for i in [0 : cells.size] do
    let c := cells[i]!
    let b := c.lay x cur anchor sep iv
    out := out ++ b.out
    lo := min lo b.lo
    hi := max hi b.hi
    cur := b.ys
    x := x + c.width
    if h : i + 1 < cells.size then
      -- Nothing to join when the two abut: a fork straight into a fork is ONE bubble, and a wire
      -- drawn across it would run through the middle of the shape.  Otherwise the wire spans the
      -- WHOLE gap, which is not always `GAP` — a snake gets extra room to climb through, and drawing
      -- at `GAP` while advancing by more left the strand short of the next cell.
      let g := joinGap c cells[i + 1]
      if g > 0.005 then
        for y in cur do out := out ++ hwire x (x + g) y iv
      x := x + g
  return ⟨out, cur, lo, hi⟩

end

/-- A whole side of a statement: the run with a stub at each end — but only where the end really is
    a single strand — and the x it ends at.

    Laid out TWICE.  The first pass only measures how far the picture reaches above and below its
    entry, so the second can enter where the whole drawing comes out centred on `y = 0`: a chain
    sets its relation symbol at 0 and the note aligns its pictures on the horizon, so a picture that
    drifts off zero reads as a picture that is falling over. -/
def renderCells (cells : Array Cell) (x0 : Float) : String × Float :=
  let lp := (cells[0]?.map Cell.leftPort).getD .one
  let rp := (cells.back?.map Cell.rightPort).getD .one
  let lead := if lp == .nothing || lp == .pair then 0.0 else LEAD
  let tail := if rp == .nothing || rp == .pair then 0.0 else LEAD
  let w := runWidth cells
  -- The strands the picture is entered at: one lane per gap its cells actually need, centred
  -- on `a`.  ONE PITCH FOR ALL OF THEM was the old rule, and with a converse anywhere in the run
  -- that pitch was the converse's — every lane in the picture spread to clear a rise that only one
  -- of them had.
  let gaps := runLaneGaps cells
  let total := gaps.foldl (· + ·) 0.0
  let entry (a : Float) : Array Float := Id.run do
    let mut ys := #[a + total / 2.0]
    for g in gaps do ys := ys.push (ys.back! - g)
    return ys
  let probe := renderRun cells (x0 + lead) (entry 0.0) 0.0 false
  let a := -(probe.lo + probe.hi) / 2.0
  let b := renderRun cells (x0 + lead) (entry a) a false
  let stub (x₀ x₁ : Float) (offs : Array Float) : Array String :=
    offs.foldl (fun acc o => acc ++ hwire x₀ x₁ o) #[]
  let out := stub x0 (x0 + lead) (entry a) ++ b.out
    ++ stub (x0 + lead + w) (x0 + lead + w + tail) b.ys
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
    |>.replace "Alg.Allegory." "" |>.replace "Alg." "" |>.replace "RelSet." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- A term, spelled the way the BOOK spells it — juxtaposition for composition, `°` for the converse
    — rather than left to the pretty printer, because it is read beside a picture, where
    `CartBicat.conv S` is noise and `S°` is the thing itself.  `°`, not the paper's `†`: these terms
    are read against Freyd throughout, and one symbol per idea beats matching two.

    PARENTHESISED BY PRECEDENCE, composition loosest and `°` tightest, so the bracketing is visible.  That
    matters: several steps of a `calc` do nothing but re-bracket, and the term column is the only
    place a reader can see them happen — the picture, quite correctly, does not change. -/
partial def labelAt (prec : Nat) (e : Expr) : MetaM String := do
  let wrap (p : Nat) (s : String) : String := if prec > p then "(" ++ s ++ ")" else s
  -- `cp` is the precedence the OPERANDS are set at, which is not always one above the operator's:
  -- composition is written by juxtaposition, so it has no symbol to separate its operands and every
  -- operand that is itself an operator has to carry brackets or `R (S ∩ T)` comes out reading as
  -- `(R S) ∩ T`.
  let bin (p : Nat) (op : String) (args : Array Expr) (cp : Nat := p + 1) : MetaM String :=
    match lastTwo args with
    | some (f, g) => return wrap p ((← labelAt cp f) ++ op ++ (← labelAt cp g))
    | none => plain e
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  | (``Freyd.Diag.CartBicat.Δ, _) => return "◁"
  | (``Freyd.Diag.CartBicat.«∇», _) => return "▷"
  | (``Freyd.Diag.CartBicat.«!», _) => return "⊸"
  | (``Freyd.Diag.CartBicat.«?», _) => return "⟜"
  | (``Freyd.Diag.CartBicat.cap, _) => return "cap"
  | (``Freyd.Diag.CartBicat.cup, _) => return "cup"
  | (``Freyd.Diag.top, _) | (``Freyd.Alg.topHom, _) => return "⊤"
  | (``Freyd.Diag.Biprod.bot, _) => return "⊥"
  -- The allegory's zero keeps the book's own `𝟘`; the tape layer's is `⊥` and they are different
  -- arrows of different towers, so they are not spelled alike.
  | (``Freyd.Alg.DistributiveAllegory.zero, _) => return "𝟘"
  -- No `α`, `λ` or `ρ` cases: this branch's monoidal structure is STRICT, so the coherence arrows
  -- do not exist and no statement can mention one.
  | (``Freyd.Diag.SymMonCat.swap, _) => return "σ"
  | (``Cat.comp, args) => bin 0 " " args 2
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 1 " ∩ " args
  | (``Freyd.Diag.Biprod.union, args) | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    bin 1 " ∪ " args
  | (``Freyd.Diag.ClosedLinearBicat.residual, args)
  | (``Freyd.Alg.DivisionAllegory.div, args) => bin 1 " / " args
  | (``Freyd.Alg.leftDiv, args) => bin 1 " \\ " args
  | (``Freyd.Alg.symmDiv, args) => bin 1 " /ₛ " args
  | (``Freyd.Alg.impl, args) => bin 1 " ⇨ " args
  | (``Freyd.Alg.thenRel, args) => bin 1 " ⨾ " args
  | (``Freyd.Alg.Allegory.recip, args) | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    | some r => return (← labelAt 3 r) ++ "°"
    | none => plain e
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) =>
    match args.back? with
    | some r => return (← labelAt 3 r) ++ "⊥"
    | none => plain e
  -- `∼` binds tighter than everything but `°`, so its operand is set at `°`'s precedence.
  | (``Freyd.Alg.neg, args) =>
    match args.back? with
    | some r => return "∼" ++ (← labelAt 3 r)
    | none => plain e
  | _ => plain e

/-- A label at the top of its own picture or box: no outer parentheses. -/
def label (e : Expr) : MetaM String := labelAt 0 e

/-- Whether the local context carries a `Map` hypothesis for this arrow.  No threading needed: the
    walk runs inside the statement's own `forallTelescope`, so `Map f` is a local hypothesis right
    there to be read, exactly as the reader of the Lean statement reads it. -/
def isMap (e : Expr) : MetaM Bool := do
  unless e.isFVar do return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match d.type.getAppFnArgs with
    | (``Freyd.Alg.Map, args) | (``Freyd.Diag.Map, args) =>
      if args.back? == some e then return true
    | _ => pure ()
  return false

/-- How many strands an object is: one per letter of its word.  The identity at `n ⊗ n` is TWO
    wires, and drawing it as one does not even line up with the `▷ ◁` it is compared against. -/
partial def wordWidth (e : Expr) : Nat :=
  match e.getAppFnArgs with
  | (``Freyd.Diag.Word.tens, args) =>
    match lastTwo args with
    | some (a, b) => wordWidth a + wordWidth b
    | none => 1
  | (``Freyd.Diag.Word.unit, _) => 0
  | _ => 1

/-- That many wires, stacked. -/
def wires : Nat → Cell
  | 0 | 1 => .wire
  | n + 2 => .stack #[.wire] #[wires (n + 1)]

mutual

/-- One cell for `e`, used where a sub-picture is not available (inside a meet or a converse). -/
partial def toCell (e : Expr) : MetaM Cell := do
  match e.getAppFnArgs with
  | (``Cat.id, args) => return wires (args.back?.map wordWidth |>.getD 1)
  -- width and lead are the generators' own stubs in `strdiag.typ`: `li + lo` wide, `li` of it to
  -- the left of the anchor (`unitR` and `swap` anchor on their left edge, so their lead is 0).
  | (``Freyd.Diag.CartBicat.Δ, _) => return .gen "delta" 1.4 0.7
  | (``Freyd.Diag.CartBicat.«∇», _) => return .gen "nabla" 1.4 0.7
  | (``Freyd.Diag.CartBicat.«!», _) => return .gen "bang" 0.7 0.7
  | (``Freyd.Diag.CartBicat.«?», _) => return .gen "unitR" 0.7 0.0
  | (``Freyd.Diag.SymMonCat.swap, _) => return .gen "swap" 0.55 0.0
  -- One arc per LETTER of the object, as `cap_tens` says: the cap at `m ⊗ n` is `cap_m` and `cap_n`
  -- behind a crossing, so it takes four strands and not two.
  | (``Freyd.Diag.CartBicat.cap, args) => return .capC (max 1 (args.back?.map wordWidth |>.getD 1))
  | (``Freyd.Diag.CartBicat.cup, args) => return .cupC (max 1 (args.back?.map wordWidth |>.getD 1))
  | (``Freyd.Diag.SymMonCat.tensHom, args) =>
    match lastTwo args with
    | some (u, l) => return .stack (← toCells u) (← toCells l)
    | none => return .box (← label e)
  | (``Freyd.Alg.Allegory.inter, args)
  | (``Freyd.Diag.meet, args) =>
    match lastTwo args with
    | some (u, l) => return .meet (← toCells u) (← toCells l)
    | none => return .box (← label e)
  | (``Freyd.Diag.Biprod.union, args)
  | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    match lastTwo args with
    | some (u, l) => return .union (← toCells u) (← toCells l)
    | none => return .box (← label e)
  -- THE CUT, and the three things drawn with it.
  --
  -- `∼R` is the photographic negative of `R`'s own picture — `R` drawn on the other colour, not a
  -- box with `∼R` printed inside it.  So `∼(R ∪ S)` shows the tape it is the negative OF, and
  -- `∼∼R = R` is two grounds cancelling.
  | (``Freyd.Alg.neg, args) =>
    match args.back? with
    | some r => return .cut (← toCells r)
    | none => return .box (← label e)
  -- The black composition is the same switch: `DiagrammaticAlgebraOfFirstOrderLogic.pdf` Fig. 4
  -- draws `d ⨟• e` as `d` and `e` on black ground, which is what (δl) and (δr) are pictures of.
  | (``Freyd.Diag.LinearBicat.bcomp, args) =>
    match lastTwo args with
    | some (f, g) => return .cut ((← toCells f) ++ (← toCells g))
    | none => return .box (← label e)
  -- `R⊥` is the mirror image AND the negative (paper, p. 2), so it is a cut around a `°`.  The
  -- residual is `R ⨟• S⊥` BY DEFINITION (`diag/FO.lean:162`), and unfolding it here is what turns
  -- `R / S` from a box repeating its own label into the picture the paper draws: `R` on black, with
  -- `S` mirrored inside a white island — Peirce's double cut.
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) =>
    match args.back? with
    | some r => return .cut #[.dagger (← label r) false]
    | none => return .box (← label e)
  -- The residual draws as LONG DIVISION, not as its own definition unfolded.  `R ⨟• S⊥` is a cut
  -- with a cut inside it, which is a faithful picture of the phase-9 term and needs a complement to
  -- mean anything; `R / S` needs none, and it is the same operation — `«≤_residual_iff»` and
  -- `le_div_iff` are one Galois statement.  One picture for one operation.
  | (``Freyd.Diag.ClosedLinearBicat.residual, args) =>
    match lastTwo args with
    | some (r, sd) => return .divbox (← labelAt 2 r) (← labelAt 2 sd) false
    | none => return .box (← label e)
  -- Division draws as LONG DIVISION.  `div` has no definition to unfold — it is a field of
  -- `DivisionAllegory` — but that is a reason to draw the universal property, not a reason to print
  -- the term twice: a dashed box reading `R / S` beside a term column reading `R / S` is a frame
  -- around a string.  The box keeps its chamfer and wires up as before; only its interior changes.
  -- `leftDiv` is the mirror, chamfer and divisor tile together, since `S \ R` lays `S` down first.
  | (``Freyd.Alg.DivisionAllegory.div, args) =>
    match lastTwo args with
    | some (r, sd) => return .divbox (← labelAt 2 r) (← labelAt 2 sd) false
    | none => return .box (← label e)
  | (``Freyd.Alg.leftDiv, args) =>
    match lastTwo args with
    | some (sd, r) => return .divbox (← labelAt 2 r) (← labelAt 2 sd) true
    | none => return .box (← label e)
  -- Still dashed: no definition to unfold at any layer, and no quotient metaphor either.  `impl`
  -- and `symmDiv` are `Sup`s and `thenRel` is built from `impl`; a meet of two converses is not a
  -- quotient with a remainder.
  | (``Freyd.Alg.symmDiv, _) | (``Freyd.Alg.impl, _) | (``Freyd.Alg.thenRel, _) =>
    return .dbox (← label e)
  | (``Freyd.Alg.Allegory.recip, args)
  | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    -- Whether the mirrored box keeps a dashed frame is read off the operand's OWN cell, so the one
    -- list of dashed constructs above stays the only place that classification is made.
    | some r => return .dagger (← label r) (match ← toCell r with | .dbox _ => true | _ => false)
    | none => return .box (← label e)
  | _ => if ← isMap e then return .mbox (← label e) else return .box (← label e)

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
   #import \"../strdiag.typ\": cetz, d, wire, gbox, delta, nabla, bang, unitR, bend, cap, cup, conv, meet, swap, tape, tape-fork, tape-join, cut, divbox, capAt, cupAt, TINT\n\n"
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

/-- Every module of a library root except this tool, so the exporter can name any declaration of
    the tower without the caller listing imports.  Walked for `diag` and for `AOP`: the cheatsheet
    the notes are drawn against is an AOP cheatsheet, and its division and negation laws are
    theorems of `AOP.A4_4`/`AOP.A4_5`, not of the diagrammatic tower. -/
partial def libModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "tool" && e.fileName != "generated" then
        out := out ++ (← libModules e.path (pre.str e.fileName))
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
  let mods := #[`Freyd] ++ (← libModules "diag" `diag) ++ (← libModules "AOP" `AOP)
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
