/-
  Freyd & Scedrov, *Categories and Allegories* §1.53  The SLICE LEMMA.

  §1.531  Σ : A/B → A preserves and reflects monos and covers.
          Monic preservation/reflection (and Σ as a `Functor`) are in `S1_44`,
          packaged as `slice_preservesMono` / `slice_reflectsMono` via
          `PreservesMono` / `ReflectsMono`.  Cover reflection is here (needs §1.51).
  §1.532  The pullback square for B×A₁ → B×A₂ over A₁→A₂.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_26
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_44
import Freyd.S1_45
import Freyd.S1_51


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

-- BOOK §1.521: For small A, the functor category S^A is regular and the evaluation
--   functors form a collectively faithful family of representations of regular categories.
--   (Blocked: requires functor category machinery not yet available in this repo.)

-- BOOK §1.53 / §1.532: Δ : A → A/B is a representation of pre-regular categories.
--   Pre-regularity of A/B: `overPreRegular` in SliceRegular.lean.
--   Δ as a functor: `sliceEmbedFunctor` in RelativeCapitalization.lean.
--   (B×-) preserves covers: the §1.532 pullback `prod_pullback` here + `overPullbacksTransferCovers`
--   in SliceRegular.lean; together these give §1.532's claim that Δ preserves covers.

-- BOOK §1.53 / §1.533–1.534: Δ is faithful iff B is well-supported.
--   (⟹) B well-supported ⟹ Δ faithful: `sliceEmbedFaithful` in RelativeCapitalization.lean
--       (relies on `slice_embedding_separates` in S1_54.lean — `fst : C×B → C` is a cover
--        when B is well-supported, hence epic, so prodRight B is an embedding).
--   (⟸) B not well-supported ⟹ Δ not faithful: `prodRight_not_reflects_iso` in S1_54.lean
--       (U.arr : U ↣ 1 proper, b : B → U factors term B; pair(fst≫U.arr,snd) is iso by
--        two-sided inverse pair(snd≫b,snd) via monicity of U.arr, but U.arr not iso).

/-! ## §1.531  Σ reflects covers

  Σ-as-a-`Functor` and its mono preservation/reflection live in `S1_44`
  (`sliceForgetFunctor`, `sigma_preserves_mono`, `sigma_reflects_mono`, and the
  `slice_preservesMono` / `slice_reflectsMono` packaging via `PreservesMono` /
  `ReflectsMono`).  Cover reflection is here since it additionally needs `Cover`. -/

/-- **§1.531**: Σ reflects covers.  If u.f is a cover in A and factors
    through a monic m in A/B, then m.f is iso in A. -/
theorem sigma_reflects_cover {B : 𝒞} {X Y Z : Over B} (u : OverHom X Y) (m : OverHom Z Y)
    (g : OverHom X Z) (hu : Cover u.f) (hmMono : OverMono m) (hgm : g ⊚ m = u) : IsIso m.f := by
  have hgmA : g.f ≫ m.f = u.f := congrArg OverHom.f hgm
  have hmA : Monic m.f := sigma_preserves_mono m hmMono
  exact hu m.f g.f hmA hgmA

/-! ## §1.532  The pullback square for Δ -/

/-- Helper: `pair a b ≫ pair fst (snd ≫ x) = pair a (b ≫ x)`. -/
theorem pair_prod_map {X B A₁ A₂ : 𝒞} (a : X ⟶ B) (b : X ⟶ A₁) (x : A₁ ⟶ A₂) :
    pair a b ≫ pair fst (snd ≫ x) = pair a (b ≫ x) := by
  apply pair_uniq _ _ (pair a b ≫ pair fst (snd ≫ x))
  · rw [Cat.assoc, fst_pair, fst_pair]
  · calc
      (pair a b ≫ pair fst (snd ≫ x)) ≫ snd = pair a b ≫ (pair fst (snd ≫ x) ≫ snd) := by rw [Cat.assoc]
      _ = pair a b ≫ (snd ≫ x) := by rw [snd_pair]
      _ = (pair a b ≫ snd) ≫ x := by rw [← Cat.assoc]
      _ = b ≫ x := by rw [snd_pair]

/-- **§1.532 pullback square**.  In any category with binary products,
         B×A₁ —pair fst (snd≫x)—→ B×A₂
          |                       |
         snd                     snd
          v                       v
         A₁  ————x——————→       A₂
    is a pullback. -/
def prod_pullback (B A₁ A₂ : 𝒞) (x : A₁ ⟶ A₂) : HasPullback (snd (A:=B) (B:=A₂)) x := by
  let P : 𝒞 := prod B A₁
  let p₁ : P ⟶ prod B A₂ := pair fst (snd ≫ x)
  let p₂ : P ⟶ A₁ := snd
  have h_sq : p₁ ≫ snd = p₂ ≫ x := by simp [p₁, p₂, snd_pair]
  refine {
    cone := { pt := P, π₁ := p₁, π₂ := p₂, w := h_sq }
    lift := λ c => pair (c.π₁ ≫ fst) c.π₂
    lift_fst := λ c => ?_
    lift_snd := λ c => ?_
    lift_uniq := λ c u hu₁ hu₂ => ?_
  }
  · dsimp [p₁]; rw [pair_prod_map (c.π₁ ≫ fst) c.π₂ x, ← c.w]
    exact (pair_uniq (c.π₁ ≫ fst) (c.π₁ ≫ snd) c.π₁ rfl rfl).symm
  · dsimp [p₂]; simp [snd_pair]
  · apply pair_uniq _ _ u
    · dsimp [p₁] at hu₁; rw [← hu₁, Cat.assoc, fst_pair]
    · dsimp [p₂] at hu₂; rw [← hu₂]

end Freyd
