/-
  Port of the nontrivial content of AoPA `Relations/WellFound.agda` into `Rel(Set)`.

  Lean core already provides `Acc`/`WellFounded` with the SAME convention as AoPA
  (`Acc r x` = every `y` with `r y x` is accessible), so only the two lemmas AoPA proves on
  top of the eliminator are ported:

  * `acc_fRfº` — accessibility transported along a function:
      `Acc (f ○ R ○ f°) (f x) → Acc R x`  (AoPA `acc-fRfº`).
      Translation `fun f ○ R ○ (fun f)˘ ↦ (graph f)° ≫ (R ≫ graph f)`.
  * `acc_tc`   — the transitive closure `R⁺` of `R` preserves accessibility:
      `Acc R x → Acc (R⁺) x`  (AoPA `acc-tc`), with `R⁺` the inductive `TransClo` below.

  Mathlib-free; axioms ⊆ {} (no propext/Quot.sound needed — pure `Acc` recursion).
-/
module

public import AOP.A6_1_RelSet

universe u

namespace Freyd.Alg
namespace RelSet

variable {a b : RelSet.{u}}

/-! ### Accessibility transported along a function (AoPA `acc-fRfº`) -/

/-- AoPA `acc-fRfº`: if `f x` is accessible under `f ○ R ○ f°` then `x` is accessible under `R`.
    The transported relation `fun f ○ R ○ (fun f)˘` is `(graph f)° ≫ (R ≫ graph f)`. -/
theorem acc_fRf_recip (f : a.carrier → b.carrier) (R : a ⟶ a) (x : a.carrier)
    (hx : Acc ((graph f)° ≫ (R ≫ graph f)) (f x)) : Acc R x := by
  -- Generalise `f x` to an abstract accessible point `z` with a witness `z = f w`.
  have gen : ∀ z, Acc ((graph f)° ≫ (R ≫ graph f)) z → ∀ w, z = f w → Acc R w := by
    intro z hz
    induction hz with
    | intro z _ ih =>
      intro w hzw
      refine Acc.intro w (fun y hRyw => ?_)
      -- `f y` is a predecessor of `z = f w` under the transported relation, via `R y w`.
      refine ih (f y) ?_ y rfl
      rw [hzw]
      exact ⟨y, rfl, w, hRyw, rfl⟩
  exact gen (f x) hx x rfl

/-! ### Transitive closure and its accessibility (AoPA `_⁺` / `acc-tc`) -/

/-- The transitive closure `R⁺` (AoPA `_⁺`): a nonempty `R`-chain, extended on the right. -/
inductive TransClo (R : a ⟶ a) : a.carrier → a.carrier → Prop where
  | base {x y} : R x y → TransClo R x y
  | step {x z} (y : a.carrier) : TransClo R x y → R y z → TransClo R x z

/-- The recursive core of `acc_tc` (AoPA's local `access`): from `Acc R x` build accessibility
    under `R⁺` of every `R⁺`-predecessor of `x`.  Structural recursion on the `Acc R _` proof. -/
private def accessTC (R : a ⟶ a) :
    ∀ x, Acc R x → ∀ y, TransClo R y x → Acc (TransClo R) y
  | _, Acc.intro _ h, y, TransClo.base yRx => Acc.intro y (accessTC R y (h y yRx))
  | _, Acc.intro _ h, y, TransClo.step z hyz zRx => accessTC R z (h z zRx) y hyz

/-- AoPA `acc-tc`: accessibility under `R` implies accessibility under its transitive closure. -/
theorem acc_tc (R : a ⟶ a) (x : a.carrier) (ac : Acc R x) : Acc (TransClo R) x :=
  Acc.intro x (accessTC R x ac)

end RelSet
end Freyd.Alg
