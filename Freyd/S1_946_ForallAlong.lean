/-
  Freyd & Scedrov, *Categories and Allegories* — the right adjoint to inverse image
  (`∀_f : Sub(A) → Sub(B)`, the internal universal quantifier along `f : A → B`) in a topos,
  and the resulting FRAME LAW that inverse image preserves binary unions:

      f#(S ∪ T)  ≤  f#S ∪ f#T.

  Mathematically `∀_f S = { b : B | ∀ a : A. (f a = b) ⇒ (a ∈ S) }`.  As a characteristic
  map `B → Ω` this is the fibered-∀ over `A` of the body `(a,b) ↦ (f a = b) ⇒ (a ∈ S)`,
  built from `forallC A` (internal ∀), the diagonal classifier `χ_Δ` (internal equality),
  and `impΩ` (internal implication) — all already in `InternalForallTopos`.

  The adjunction `f# ⊣ ∀_f` is proven on subobjects: `f# T ≤ S  ↔  T ≤ ∀_f S`.  A left
  adjoint (here `f#`) preserves joins, which yields the frame law `≤` direction directly.
-/

import Freyd.S1_94_InternalForallTopos
import Freyd.S1_946_RightAdjointImage
import Freyd.S1_45
import Freyd.S1_60
import Freyd.S1_95_ToposColimits

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## The book-facing `∀_f` notation for the right-adjoint image. -/

/-- **`∀_f S` — the internal universal image of `S` along `f`.** -/
noncomputable def forallAlong {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) : Subobject 𝒞 B :=
  radjImage f S

/-! ## The adjunction `f# ⊣ ∀_f`.

  This is the already proved right-adjoint-image adjunction, transported between two
  chosen pullbacks by `invImg_compare`. -/

theorem forallAlong_adjunction {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (T : Subobject 𝒞 B)
    (hp : HasPullback f T.arr) :
    (invImg f T hp).le S ↔ T.le (forallAlong f S) :=
  ⟨fun h => (radjImage_adjunction f T S).1
      (Subobject.le_trans (invImg_compare f T (HasPullbacks.has f T.arr) hp) h),
    fun h => Subobject.le_trans (invImg_compare f T hp (HasPullbacks.has f T.arr))
      ((radjImage_adjunction f T S).2 h)⟩

/-! ## Consequence: inverse image preserves binary unions (the FRAME LAW). -/

/-- **Frame law** (forward direction): `f#(S ∪ T) ≤ f#S ∪ f#T`.  `f#` is a left adjoint
    (to `∀_f`), so it preserves the join `∪`. -/
theorem invImage_preserves_union {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B)
    (hpU : HasPullback f (HasSubobjectUnions.union S T).arr)
    (hpS : HasPullback f S.arr) (hpT : HasPullback f T.arr) :
    (invImg f (HasSubobjectUnions.union S T) hpU).le
      (HasSubobjectUnions.union (invImg f S hpS) (invImg f T hpT)) := by
  -- `f#` is left adjoint to `∀_f`, so it preserves the join `∪`.  Write `U := f#S ∪ f#T`.
  -- f#(S∪T) ≤ U  ↔  (S∪T) ≤ ∀_f U.
  rw [forallAlong_adjunction f (HasSubobjectUnions.union (invImg f S hpS) (invImg f T hpT))
    (HasSubobjectUnions.union S T) hpU]
  -- by union_min, suffices S ≤ ∀_f U and T ≤ ∀_f U.
  refine HasSubobjectUnions.union_min S T _ ?_ ?_
  · -- S ≤ ∀_f U  ↔  f#S ≤ U = f#S ∪ f#T,  which is union_left.
    rw [← forallAlong_adjunction f _ S hpS]
    exact HasSubobjectUnions.union_left _ _
  · -- T ≤ ∀_f U  ↔  f#T ≤ U,  which is union_right.
    rw [← forallAlong_adjunction f _ T hpT]
    exact HasSubobjectUnions.union_right _ _

end Freyd
