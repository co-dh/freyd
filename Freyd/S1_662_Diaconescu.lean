/-
# §1.662 Diaconescu (2)→(3): `Choice (1+1) ⟹ Boolean`

  The keystone of Diaconescu's theorem for pre-toposes: in a `PreToposDisjoint` with
  `HasReflTransClosure`, base `Choice (1+1)` makes the pre-topos a `BooleanPreLogos`.

  Freyd's route runs inside the slice `Over (A×A)` (a `PreToposDisjoint` + `HasReflTransClosure`,
  via the slice instances in `Freyd.SlicePreTopos`).  The diagonal `Δ_A : A ↣ A×A` is a subterminal
  `U ⊆ 1_𝒮` there; complementing `U` transports down to `DecidableObject A`, and
  `preTopos_boolean_iff_all_decidable.mpr` finishes.

  All the supporting pieces live in `SlicePreTopos`: the slice pre-topos bundling instance
  `overPreToposDisjoint`, `one_one_decidable`, `slice_choice_codiag`, `cover_splits_of_dom_choice`,
  `mono_of_retraction`, `forgetSlice_isComplemented`.  Only the two final theorems land here, in a file
  that IMPORTS `SlicePreTopos` (rather than living inside it) for clean separation.
-/
import Freyd.S1_65_SlicePreTopos

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

open HasBinaryCoproducts

/-- **§1.662 keystone**: from base `Choice (1+1)`, every object `A` of `𝒞` is decidable.
    Run inside `Over (A×A)`: `U = Δ_A ⊆ 1_𝒮` (`liftSlice 1_𝒮 (diagSub A)`); its amalgam `D` with
    itself is a quotient `case u v : 1_𝒮+1_𝒮 ↠ D`, split by slice choice (`slice_choice_codiag`
    ⟹ `1_𝒮+1_𝒮` choice ⟹ projective).  `1_𝒮+1_𝒮` is decidable (`one_one_decidable` at the
    slice), so the split mono carries decidability to `D` (`decidableSub_of_mono`); then
    `subobject_complemented_of_amalg_decidable` complements `U`, and `forgetSlice` transports
    `IsComplemented U` to `IsComplemented (diagSub A) = DecidableObject A`. -/
theorem all_decidable_of_one_one_choice [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    (hch : Choice (coprod (one : 𝒞) one)) (A : 𝒞) : DecidableObject A := by
  classical
  -- work in the slice `Over (A×A)`.
  let B := prod A A
  -- the subterminal `U = Δ_A ⊆ 1_𝒮` in `Over B`, with `forgetSlice U = diagSub A`.
  let U : Subobject (Over B) (one : Over B) := Subobject.liftSlice (one : Over B) (diagSub A)
  -- amalgamate `U.arr` with itself: amalgam `D`, monic legs `u, v`, square a pullback, `case u v`
  -- a cover.
  obtain ⟨D, u, v, hsq, hpb, _hpush, hcov⟩ :=
    amalgamation_is_pullback U.arr U.monic U.arr U.monic
  -- `1_𝒮+1_𝒮` is choice (slice codiagonal) and decidable (`one_one_decidable` at the slice).
  have hchS : Choice (coprod (one : Over B) one) := slice_choice_codiag A hch
  have hdecS : DecidableObjectSub (coprod (one : Over B) one) :=
    (isComplemented_iff_sub _).mp one_one_decidable
  -- split the cover `case u v : 1_𝒮+1_𝒮 ↠ D` (its domain `1_𝒮+1_𝒮` is choice).
  obtain ⟨s, hs⟩ := cover_splits_of_dom_choice (case u v) hcov hchS
  -- `s : D ↣ 1_𝒮+1_𝒮` is a split mono, so `D` is decidable.
  have hDmono : Monic s := mono_of_retraction s (case u v) hs
  have hDdec : DecidableObjectSub D := decidableSub_of_mono s hDmono hdecS
  -- complement `U` in `Over B`, then forget to `IsComplemented (diagSub A) = DecidableObject A`.
  have hUcomp : IsComplemented U :=
    subobject_complemented_of_amalg_decidable U hsq hpb hDdec
  have hbase : IsComplemented (Subobject.forgetSlice (one : Over B) U) :=
    forgetSlice_isComplemented U hUcomp
  -- `forgetSlice U = diagSub A` on the nose, and `diagSub A` is the `DecidableObject` witness for A.
  have hforget : Subobject.forgetSlice (one : Over B) U = diagSub A := rfl
  rw [hforget] at hbase
  exact hbase

/-- **§1.662 (2)→(3)** `one_one_choice_to_boolean`: in a `PreToposDisjoint` with
    `HasReflTransClosure`, `Choice (1+1)` makes the pre-topos boolean.  By
    `all_decidable_of_one_one_choice` every object is decidable, and
    `preTopos_boolean_iff_all_decidable.mpr` finishes. -/
theorem one_one_choice_to_boolean [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]
    (h : Choice (coprod (one : 𝒞) one)) :
    Nonempty (BooleanPreLogos 𝒞) :=
  (preTopos_boolean_iff_all_decidable).mpr (all_decidable_of_one_one_choice h)

end Freyd
