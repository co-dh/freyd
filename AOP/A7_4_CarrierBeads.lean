/-
  The note's beads that are arrows at ONE object, refuted as natural families.

  A bead drawn OFF the object wire claims to be a natural transformation — the square
  `F(f) ≫ φ ⊑ φ ≫ G(f)` for EVERY `f`.  Two families in the note claim nothing of the kind, and
  one counterexample each says so, so the bead rides the object wire:

  * `est(R)` is an arrow at the one object its `R` lives on.  Naturality would need
    `E(f) est(R) ⊑ est(R) f` for every `f`, and `f` need not be monotone: `est_not_lax_natural`
    takes `≤` on `Bool` and `not`, where the least element of a set and the least element of its
    `not`-image are the two different elements of `Bool`.
  * An ALGEBRA `α : F(x)⟶x` is an arrow at the carrier the panel names, not a family over it.
    `listAlg_not_lax_natural` fails on the `zero` branch alone (`0` is not `0+1`), which is why
    one witness settles `[,]`, its `zero`, and the fold `⦇[zero,plus]⦈ = sum` at once
    (`sum_not_lax_natural`).  `plus` needs a map of its own — it does commute with `(+1)` —
    and `plus_not_lax_natural` breaks it with doubling.

  Composition is diagram order (`≫`); every witness is a concrete `RelSet` over `Bool` or `Int`.
-/
module

public import AOP.A7_4_Horner
public import AOP.A5_7_PowerBeads
public import AOP.A6_Poly_List
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Carrier

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel
open Freyd.Alg.RelSet.Poly

/-! ## `est(R)` at a fixed `R` -/

/-- `≤` on `Bool`. -/
@[expose] public def leB : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun p q => p = false ∨ q = true

/-- `not` on `Bool` — the ANTITONE map that breaks the `est` square. -/
@[expose] public def notB : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := graph not

/-- **`est(R)` at a fixed `R` is not even lax natural**: `E(f) est(R) ⊑ est(R) f` fails.  At the
    full set `{false,true}` the left side reaches `false` — `E(not)` maps the full set to itself
    and `false` is the `≤`-least member — while the right side takes the least member first and
    then negates it, reaching `true` alone. -/
public theorem est_not_lax_natural :
    ∃ (a : RelSet.{0}) (R f : a ⟶ a), ¬ (powerRel f ≫ est R ⊑ est R ≫ f) := by
  refine ⟨⟨Bool⟩, leB, notB, fun h => ?_⟩
  have hfull : powerRel notB (fun _ => True) (fun _ => True) :=
    (powerRel_apply notB _ _).mpr
      ⟨fun x _ => ⟨not x, rfl, trivial⟩, fun y _ => ⟨not y, trivial, (Bool.not_not y).symm⟩⟩
  have hest : est leB (fun _ => True) false :=
    (est_apply leB _ false).mpr ⟨trivial, fun _ _ => Or.inl rfl⟩
  obtain ⟨w, hw, hfw⟩ :=
    RelSet.le_iff.mp h (fun _ => True) false ⟨fun _ => True, hfull, hest⟩
  have hwf : w = false := by
    rcases ((est_apply leB _ w).mp hw).2 false trivial with h1 | h1
    · exact h1
    · exact absurd h1 (by decide)
  subst hwf
  exact Bool.noConfusion (show (false : Bool) = true from hfw)

/-! ## An algebra at ONE carrier -/

/-- `(+1) : Int ⟶ Int`. -/
@[expose] public def succI : dE Int ⟶ dE Int := graph (fun n => n + 1)

/-- **`[,] : F(x)⟶x` is not even lax natural**: `F(f) [zero,plus] ⊑ [zero,plus] f` fails at the
    carrier `Int`, the algebra `[0,+]` and `f = (+1)`, on the `zero` branch alone — `F(f)` leaves
    the empty summand alone and the algebra answers `0`, where `f` demands `0+1`. -/
public theorem listAlg_not_lax_natural :
    ¬ (fmapR ListF.LF succI ≫ ListF.listAlg (0 : Int) (fun a c => a + c)
        ⊑ ListF.listAlg (0 : Int) (fun a c => a + c) ≫ succI) := by
  intro h
  obtain ⟨c, hc, hf⟩ :=
    RelSet.le_iff.mp h (Sum.inl PUnit.unit) 0 ⟨Sum.inl PUnit.unit, trivial, rfl⟩
  have hc' : c = 0 := hc
  subst hc'
  exact absurd (show (0 : Int) = 1 from hf) (by decide)


/-- **`sum : [x]⟶x`, the fold `⦇[zero,plus]⦈`, is not even lax natural**: `list(f) sum ⊑ sum f`
    fails at `f = (+1)` and the empty list — `sum []` is `0`, and `0+1` is not `0`.  A fold lands
    on the carrier its algebra names, so this is `listAlg_not_lax_natural` read through the fold. -/
public theorem sum_not_lax_natural : ¬ (list succI ≫ sumR ⊑ sumR ≫ succI) := by
  intro h
  obtain ⟨c, hc, hf⟩ :=
    RelSet.le_iff.mp h (ConsList.wrap ()) 0 ⟨ConsList.wrap (), trivial, rfl⟩
  have hc' : c = 0 := hc
  subst hc'
  exact absurd (show (0 : Int) = 1 from hf) (by decide)


/-- The note's `plus : A×x⟶x`, at `A = x = Int`. -/
@[expose] public def plusR : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := graph (fun p => p.1 + p.2)

/-- Doubling: `plus` commutes with `(+1)`, so the `est`/`sum` witness does not reach it. -/
@[expose] public def dblI : dE Int ⟶ dE Int := graph (fun n => n + n)

/-- **`plus : A×x⟶x` is not even lax natural**: `(𝟙×f) plus ⊑ plus f` fails at `f` the doubling
    map and the pair `(1,0)` — adding after doubling the second component gives `1`, doubling
    after adding gives `2`. -/
public theorem plus_not_lax_natural :
    ¬ (rprodMap (𝟙 (⟨Int⟩ : RelSet.{0})) dblI ≫ plusR ⊑ plusR ≫ dblI) := by
  intro h
  obtain ⟨w, hw, hf⟩ :=
    RelSet.le_iff.mp h (1, 0) 1
      ⟨(1, 0), ⟨rfl, (rfl : (0 : Int) = 0 + 0)⟩, (rfl : (1 : Int) = 1 + 0)⟩
  have hw' : w = 1 := hw
  subst hw'
  exact absurd (show (1 : Int) = 2 from hf) (by decide)

end Freyd.Alg.RelSet.Carrier
