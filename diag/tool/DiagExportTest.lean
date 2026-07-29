/-
  Invariants of `diag-export`'s picture model, checked at elaboration time.

  WHY THIS FILE EXISTS.  Every wrong picture this exporter has shipped was one bug: a cell's
  DECLARED geometry disagreeing with what its render actually draws.  The declared side is
  `leftPort`/`rightPort`, `leftOffsets`/`rightOffsets` and `width`; the drawn side is the string
  `Cell.render` emits.  Nothing forced them to agree, and four times running they did not:

  * `swap` reported its strands at `STACKSEP` and was drawn at `strdiag.typ`'s default `0.33`, so the
    fork feeding `Δ ; σ = Δ` abutted a crossing that was somewhere else;
  * a run ending in a snake reported the snake's skew outwards while `renderStrand` was also bending
    it away inside, so the outer stub and the strand's own wire were drawn at two different heights;
  * `runPad` fired on every non-zero offset, which includes a fork's two prongs, and tied them to the
    centre line;
  * `conv-w` was one `SPLIT` wider than `conv` draws, so a snake ended before its cell did.

  These `#guard`s are cheap and run on every `lake build diag`.  They do not check that a picture is
  BEAUTIFUL — they check that the model is self-consistent, which is the part a reader cannot see and
  the part that has been wrong.
-/
import diag.tool.DiagExport

namespace Freyd.DiagExport.Test

open Freyd.DiagExport

/-! ### A generator drawn at one separation and reported at another -/

/-- Every generator that presents two strands must SAY where they are, at the separation its RUN
    settled on — never at a `strdiag.typ` default, since those are not all alike (`swap`'s is 0.33).
    Checked at a separation deliberately unlike any default, so a shape that ignores the argument and
    falls back cannot pass. -/
def oddSep : Float := 0.77

def statesItsStrands (c : Cell) : Bool :=
  let s := String.join (c.render 0.0 0.0 oddSep false).toList
  if c.leftPort.isTwo || c.rightPort.isTwo then
    (s.splitOn ("sp: " ++ fmt oddSep)).length > 1
  else true

def delta : Cell := .gen "delta" 1.4 0.7
def nabla : Cell := .gen "nabla" 1.4 0.7
def swapC : Cell := .gen "swap" 0.55 0.0

#guard statesItsStrands delta
#guard statesItsStrands nabla
#guard statesItsStrands swapC
#guard statesItsStrands (.capC)
#guard statesItsStrands (.cupC)

/-! ### Ports must agree across an abutment

Two `pair` ports facing each other are drawn touching, with no wire between them to absorb a
mismatch, so they have to be at the same heights. -/

def abuts (c next : Cell) : Bool :=
  !(c.rightPort == .pair && next.leftPort == .pair)
    || c.rightOffsets oddSep == next.leftOffsets oddSep

#guard abuts delta nabla
#guard abuts delta swapC
#guard abuts swapC nabla
#guard abuts delta (.capC)

/-! ### A run reports what `renderStrand` delivers, not what its cells want

`renderStrand` bends a single skewed strand back to the centre line, so an enclosing `⊗`, meet or
tape must see it there.  A snake at either end is the only skew there is; anything else passes
through. -/

def snake : Cell := .dagger "R" false
def plainBox : Cell := .box "R"

#guard runPortL #[snake] == #[0.0]
#guard runPortR #[snake] == #[0.0]
#guard runPortL #[plainBox] == runLeftOffsets #[plainBox]
#guard runPortR #[delta] == runRightOffsets #[delta]
-- A fork is not skew, so it reserves no room.
#guard runPadR #[delta] == 0.0
#guard runPadL #[delta] == 0.0
-- A snake is, so it does.
#guard runPadL #[snake] > 0.0
#guard runPadR #[snake] > 0.0

/-! ### Width is what the render occupies

A cell that claims to be wider than it draws leaves a gap the joining wire never crosses, which is
what made the first snakes look unwired. -/

-- `conv`'s outgoing wire stops at `0.28 + SPLIT + 2·arc + w + lead`; `strdiag.typ`'s `conv-w` adds
-- one more `SPLIT` of trailing air, and the snake's width must follow the DRAWING.
#guard (Cell.width snake - boxWidth "R") == CONVPAD
#guard CONVPAD < 0.28 + 0.34 + 2.0 * 0.78 + 0.34 + 0.40

-- A composite's width is the same arithmetic its render lays out with: the shared inner width is
-- `runOuterWidth`, padding included, or the strands are centred against the wrong total.
def meetOfSnakes : Cell := .meet #[snake] #[.box "S"]
#guard Cell.width meetOfSnakes ==
  2.0 * FORK + max (runOuterWidth #[snake]) (runOuterWidth #[.box "S"])
#guard runOuterWidth #[snake] == runPadL #[snake] + runWidth #[snake] + runPadR #[snake]

end Freyd.DiagExport.Test
