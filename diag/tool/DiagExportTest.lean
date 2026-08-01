/-
  Invariants of `diag-export`'s picture model, checked at elaboration time.

  WHY THIS FILE EXISTS.  Every wrong picture this exporter has shipped was one bug: a cell's
  DECLARED geometry disagreeing with what its render actually draws.  The declared side is
  `leftCount`/`rightCount` and `width`; the drawn side is the string `Cell.lay` emits.  Nothing
  forces them to agree, and five times running they did not:

  * `swap` reported its strands at `STACKSEP` and was drawn at `strdiag.typ`'s default `0.33`, so the
    fork feeding `◁ σ = ◁` abutted a crossing that was somewhere else;
  * a run ending in a snake reported the snake's skew outwards while its stub was also bending it
    away inside, so the outer stub and the strand's own wire were drawn at two different heights;
  * the room reserved for that bend fired on every non-zero offset, which includes a fork's two
    prongs, and tied them to the centre line;
  * `conv-w` was one `SPLIT` wider than `conv` draws, so a snake ended before its cell did;
  * a `⊗` centred its two operands on ITS middle rather than passing the strands through, so
    `𝟙 ⊗ cup` and `cap ⊗ 𝟙` put the same three strands at different heights and the snake came out
    with three diagonal bends through the middle of it.

  These `#guard`s are cheap and run on every `lake build diag`.  They do not check that a picture is
  BEAUTIFUL — they check that the model is self-consistent, which is the part a reader cannot see and
  the part that has been wrong.
-/
import diag.tool.DiagExport

namespace Freyd.DiagExport.Test

open Freyd.DiagExport

/-- A separation deliberately unlike any `strdiag.typ` default, so a shape that ignores the
    argument and falls back to its own cannot pass. -/
def oddSep : Float := 0.77

/-- The lanes a cell of this many strands is entered at: centred on zero, `2 · oddSep` apart. -/
def lanes (k : Nat) : Array Float :=
  (Array.range k).map fun i => ((k - 1).toFloat / 2.0 - i.toFloat) * 2.0 * oddSep

def lay (c : Cell) : Lay := c.lay 0.0 (lanes c.leftCount) 0.0 oddSep false
def drawn (c : Cell) : String := String.join (lay c).out.toList

def delta : Cell := .gen "delta" 1.4 0.7
def nabla : Cell := .gen "nabla" 1.4 0.7
def swapC : Cell := .gen "swap" 0.55 0.0
def snake : Cell := .dagger "R" false
def plainBox : Cell := .box "R"

/-! ### A generator drawn at one separation and reported at another -/

/-- Every cell that carries two strands must be DRAWN at the separation of the lanes it is wired to
    — the ones it was handed, or the ones it opens at `sep` — never at a `strdiag.typ` default,
    since those are not all alike (`swap`'s is 0.33). -/
def statesItsStrands (c : Cell) : Bool :=
  if c.leftCount ≥ 2 || c.rightCount ≥ 2 then
    ((drawn c).splitOn ("sp: " ++ fmt oddSep)).length > 1
  else true

#guard statesItsStrands delta
#guard statesItsStrands nabla
#guard statesItsStrands swapC
#guard statesItsStrands (.capC)
#guard statesItsStrands (.cupC)

/-! ### Declared counts are the counts the render threads -/

/-- What a cell says it hands downstream is what laying it out actually hands downstream.  A `⊗` of
    a wire and a cup takes one strand and gives three, and every cell after it is placed by those
    three. -/
def countsItsStrands (c : Cell) : Bool := (lay c).ys.size == c.rightCount

#guard countsItsStrands delta
#guard countsItsStrands nabla
#guard countsItsStrands swapC
#guard countsItsStrands (.capC)
#guard countsItsStrands (.cupC)
#guard countsItsStrands snake
#guard countsItsStrands (.stack #[.wire] #[.cupC])
#guard countsItsStrands (.stack #[.capC] #[.wire])
#guard countsItsStrands (.meet #[plainBox] #[.box "S"])

/-! ### A cell is drawn WHERE IT IS WIRED, not where it would centre itself

The whole of thread mode.  Handed lanes that are not symmetric about anything, every cell has to
draw itself across exactly those lanes — a cap between them, a wire along one — rather than at an
offset computed from its own shape.  Drawing at the shape is what put the same three strands at two
different heights on either side of the snake's middle. -/

/-- Deliberately off centre and unevenly spaced about zero: a cell that centres itself, or that
    opens at its own `sep`, cannot land on both of these. -/
def odd : Array Float := #[1.30, -0.10]

def laidAt (c : Cell) (ys : Array Float) : String :=
  String.join (c.lay 0.0 ys 0.0 oddSep false).out.toList

def mentions (s pat : String) : Bool := (s.splitOn pat).length > 1

-- A cap bends over the two lanes it is handed: midpoint `0.60`, half-separation `0.70`.
#guard mentions (laidAt .capC odd) "capAt((0.00, 0.60), sp: 0.70"
#guard mentions (laidAt nabla odd) "nabla((0.70, 0.60), sp: 0.70)"
#guard mentions (laidAt swapC odd) "swap((0.00, 0.60), sp: 0.70"
-- A `⊗` passes its lanes straight through to its operands; it does not recentre them.
#guard mentions (laidAt (.stack #[plainBox] #[.box "S"]) odd) ", 1.30)"
#guard mentions (laidAt (.stack #[plainBox] #[.box "S"]) odd) ", -0.10)"
-- And the one that was wrong: the wire above a cup stays where it came in, and the cup's two
-- strands are opened BELOW it rather than the pair being centred on the cell.
#guard (Cell.lay (.stack #[.wire] #[.cupC]) 0.0 #[0.0] 0.0 oddSep false).ys[0]! == 0.0
#guard mentions (laidAt (.stack #[.wire] #[.cupC]) #[0.0]) "wire((0.00, 0.00)"

/-! ### Composition is flat

A strand is where upstream put it.  Nothing in this exporter may move one sideways, so nothing it
emits is ever a `bend` — the drawing functions bend inside themselves, but no wire between two cells
does.  This is the invariant the snake broke. -/

def flat (s : String) : Bool := (s.splitOn "bend(").length == 1

#guard flat (drawn (.stack #[.wire] #[.cupC]))
#guard flat (drawn (.meet #[snake] #[plainBox]))
#guard flat (drawn (.union #[plainBox] #[.box "S"]))
#guard flat (drawn (.cut #[plainBox]))

/-- The snake itself: `(𝟙 ⊗ cup) (cap ⊗ 𝟙)`, one strand in and one out, drawn without a single
    bend between cells — the cup and the cap open at the same separation because they are wired to
    the same three lanes. -/
def snakeRun : Array Cell := #[.stack #[.wire] #[.cupC], .stack #[.capC] #[.wire]]

#guard flat (String.join (renderRun snakeRun 0.0 #[0.0] 0.0 false).out.toList)
#guard (renderRun snakeRun 0.0 #[0.0] 0.0 false).ys.size == 1

/-! ### The identity is as wide as its object

`𝟙` at an `n`-letter word is `n` wires.  Drawn as one it does not line up with the `▷ ◁` it is
compared against. -/

#guard (wires 2).rightCount == 2
#guard (wires 3).rightCount == 3
#guard (wires 1).rightCount == 1

/-! ### Width is what the render occupies

A cell that claims to be wider than it draws leaves a gap the joining wire never crosses, which is
what made the first snakes look unwired. -/

-- `conv`'s outgoing wire stops at `0.28 + SPLIT + 2·arc + w + lead`; `strdiag.typ`'s `conv-w` adds
-- one more `SPLIT` of trailing air, and the snake's width must follow the DRAWING.
#guard (Cell.width snake - boxWidth "R") == CONVPAD
#guard CONVPAD < 0.28 + 0.34 + 2.0 * 0.78 + 0.34 + 0.40

-- A composite's width is the same arithmetic its render lays out with: the shared inner width the
-- operands are centred in, or they are centred against the wrong total.
#guard Cell.width (.meet #[snake] #[.box "S"]) ==
  2.0 * FORK + max (runWidth #[snake]) (runWidth #[.box "S"])

end Freyd.DiagExport.Test
