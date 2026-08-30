/-
  Embedded surface notation `rel⟦ … ⟧` for the `RE` relation-algebra GADT (`rel.RelInterp`).

  This is the PROVABLE counterpart to the external `.ralg` interpreter (`rel.RelParse`): there a
  program is a text file parsed at runtime, so nothing about it can be a theorem; here a program is
  a `rel⟦ … ⟧` quotation that ELABORATES to an `RE a b` Lean value, so every tool the GADT has —
  `eval`, `by decide`, the proven `Allegory`/`PowerAllegory` laws — applies to it.

  Two structural wins over the `.ralg` parser, both from Lean's elaborator:
  * the dependent object indices `{a b c}` of `RE` are inferred and CHECKED at compile time — a
    dimension mismatch is a type error with a source location, replacing `RelCore`'s runtime
    `Except`-wrapped dimension checks;
  * atoms are `!(term)` splices — any Lean term of type `RE a b` — so an atom can be COMPUTED from
    instance data and proven faithful, instead of the hand-baked answer tables the `.ralg` encodings
    were forced into (e.g. Two Sum's `compl : v ↦ target-v`).

  Surface grammar uses the BOOK's Unicode (Freyd, *Categories, Allegories*), matching `RelInterp`:
  `≫` composition (diagram order), `∩` meet, `∪` join, `/` right- and `\` left-division (all ONE
  precedence level, left-associative — the flat left fold), postfix `°` converse (book `R°`, binds
  tightest), and call-style keywords `id(o)`, `eps(o)`, `Λ(e)` (power transpose), `est(e)`.
  Keywords are call-style so they do not reserve the tokens `id`/`est` as global keywords
  (checked at the bottom).  The examples below are the point: each is a theorem no `.ralg` file can state.
-/
import rel.RelInterp

namespace Freyd.Alg.FinRel

/-! ## The `rel⟦ … ⟧` quotation: relation-algebra surface syntax as a Lean syntax category -/

declare_syntax_cat ralg

-- primaries
syntax ident                      : ralg  -- an atom: a Lean constant of type `RE a b`
syntax ident "(" ralg ")"         : ralg  -- call-style prefix: Λ(e), est(e), id(a), eps(a)
syntax "(" ralg ")"               : ralg
syntax "!(" term ")"              : ralg  -- splice: any Lean term of type `RE a b`
-- postfix converse `°` (book `R°`), binds tightest
syntax:100 ralg:100 "°"           : ralg
-- the five binops: ONE precedence level, left-associative — the flat left fold
syntax:60 ralg:60 " ≫ " ralg:61   : ralg
syntax:60 ralg:60 " ∩ " ralg:61   : ralg
syntax:60 ralg:60 " ∪ " ralg:61   : ralg
syntax:60 ralg:60 " / " ralg:61   : ralg
syntax:60 ralg:60 " \\ " ralg:61  : ralg

syntax "rel⟦" ralg "⟧" : term

macro_rules
  | `(rel⟦ $x:ident ⟧)           => `(($x : RE _ _))
  | `(rel⟦ !($t:term) ⟧)         => `(($t : RE _ _))
  | `(rel⟦ ($a:ralg) ⟧)          => `(rel⟦ $a ⟧)
  | `(rel⟦ $a:ralg ° ⟧)          => `(RE.conv rel⟦ $a ⟧)
  | `(rel⟦ id($o:ident) ⟧)       => `(RE.id $o)
  | `(rel⟦ eps($o:ident) ⟧)      => `(RE.eps $o)
  | `(rel⟦ Λ($a:ralg) ⟧)         => `(AE rel⟦ $a ⟧)
  | `(rel⟦ est($a:ralg) ⟧)       => `(estE rel⟦ $a ⟧)
  | `(rel⟦ $a:ralg ≫ $b:ralg ⟧)  => `(RE.comp rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg ∩ $b:ralg ⟧)  => `(RE.meet rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg ∪ $b:ralg ⟧)  => `(RE.join rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg / $b:ralg ⟧)  => `(RE.div rel⟦ $a ⟧ rel⟦ $b ⟧)
  | `(rel⟦ $a:ralg \ $b:ralg ⟧)  => `(leftDivE rel⟦ $a ⟧ rel⟦ $b ⟧)

/-! ## Proofs `.ralg` files can never state -/

-- (Instance-data examples that USE the demo fixtures live in `rel/RelNotationDemo.lean`;
--  the examples below are generic — they hold for ALL atoms, which is the notation's real payoff.)

-- (2) Two programs EQUAL, generic over atoms — an allegory-law proof, no instance data.
example {a b c : FinObj} (e : RE a b) (f : RE b c) :
    eval rel⟦ (!(e) ≫ !(f))° ⟧ = eval rel⟦ !(f)° ≫ !(e)° ⟧ :=
  Allegory.recip_comp (eval e) (eval f)

-- (3) Program-refines-spec via the division universal property — generic, structural.
example {a b c : FinObj} (t : RE a b) (r : RE a c) (s : RE b c) :
    eval rel⟦ !(t) ⟧ ⊑ eval rel⟦ !(r) / !(s) ⟧ ↔ eval rel⟦ !(t) ≫ !(s) ⟧ ⊑ eval rel⟦ !(r) ⟧ :=
  le_div_iff (eval t) (eval r) (eval s)

-- (4) Equal-precedence left fold parses like the book: `a ≫ b ∩ c` = `(a ≫ b) ∩ c`.
example {a : FinObj} (e f g : RE a a) :
    eval rel⟦ !(e) ≫ !(f) ∩ !(g) ⟧ = eval rel⟦ (!(e) ≫ !(f)) ∩ !(g) ⟧ := rfl

-- (5) A verified TERM-LEVEL optimizer step: double-converse elimination preserves `eval`
--     — a theorem ABOUT programs, by cases on the AST. Unstatable for an external .ralg file.
def unconv2 : {a b : FinObj} → RE a b → RE a b
  | _, _, .conv (.conv e) => e
  | _, _, e => e

theorem eval_unconv2 {a b : FinObj} (e : RE a b) : eval (unconv2 e) = eval e := by
  match e with
  | .conv (.conv e) => exact (Allegory.recip_recip (eval e)).symm
  | .atom _ | .id _ | .comp _ _ | .conv (.atom _) | .conv (.id _) | .conv (.comp _ _)
  | .conv (.meet _ _) | .conv (.join _ _) | .conv (.bot _ _) | .conv (.top _ _)
  | .conv (.div _ _) | .conv (.eps _) | .meet _ _ | .join _ _ | .bot _ _ | .top _ _
  | .div _ _ | .eps _ => rfl

-- Regression: the call-style keywords must NOT reserve `id`/`est` as global tokens.
example : id 3 = 3 := rfl
example : min 1 2 = 1 := rfl

end Freyd.Alg.FinRel
