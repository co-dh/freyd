/-
  §1.635 — the STALK FAMILY collective conservativity (toward §2.218).

  Freyd represents a capital positive pre-logos in a POWER of `Set` via the family of stalks
  `{T_F̂}` over ultra-filters `F̂` of complemented subterminators.  The family is COLLECTIVELY
  faithful (Freyd §1.635:239-253): given a proper subobject, SOME ultra-filter's stalk keeps it
  proper.  No single stalk reflects isos — that needs full well-pointedness, which the
  capitalization does NOT give; the family does not.

  This file builds the collective-conservativity ingredients.  First brick: the stalk evaluated
  on a SUBTERMINATOR `V` is inhabited iff `V` is in the filter (`TF_subterminator_nonempty`) —
  the bridge between the geometric "stalk" and the combinatorial "ultra-filter membership" that
  Freyd's separation argument turns on. -/
import Freyd.S1_75

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [PreLogos 𝒞]

/-- **Stalk of a subterminator = filter membership.**  For a FILTER `ℱ` (upward-closed) and a
    subterminator `V : Subobject 𝒞 one`, the stalk `T_ℱ(V.dom)` is inhabited iff `V ∈ ℱ`.

    `←`: `V ∈ ℱ` names the identity `V.dom → V.dom`.  `→`: a name `a : U.dom → V.dom` with `U ∈ ℱ`
    forces `U ≤ V` (both `U.dom, V.dom` map uniquely to the terminator `one`, so `a ≫ V.arr =
    U.arr`), and upward-closure lifts `U ∈ ℱ` to `V ∈ ℱ`. -/
theorem TF_subterminator_nonempty (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsFilter ℱ)
    (V : Subobject 𝒞 one) : Nonempty (TF ℱ V.dom) ↔ ℱ V := by
  constructor
  · rintro ⟨t⟩
    obtain ⟨⟨U, hU, a⟩, -⟩ := Quot.exists_rep t
    exact hℱ.2 U V hU ⟨a, term_uniq _ _⟩
  · intro hV
    exact ⟨TF.mk ℱ ⟨V, hV, Cat.id V.dom⟩⟩

variable [HasBinaryCoproducts 𝒞]

/-- **§1.635 detection at the stalk level.**  A PROPER complemented subterminator `V` (≠ `1`) is
    killed by SOME ultra-filter stalk: there is an ultra-filter `ℱ` with `T_ℱ(V.dom)` EMPTY.

    This is `exists_ultrafilter_excluding` (§1.635:253) read through the stalk: the excluding
    ultra-filter omits `V`, and a name `U.dom → V.dom` from a member `U ∈ ℱ` would force `V ∈ ℱ`
    (`ultrafilter_isFilter` up-closure to the complemented `V`), a contradiction. -/
theorem exists_stalk_empty_of_proper (V : Subobject 𝒞 one) (hVcomp : IsComplementedSub V)
    (hVproper : ¬ (Subobject.entire one).le V) :
    ∃ ℱ, IsUltraFilter ℱ ∧ ¬ Nonempty (TF ℱ V.dom) := by
  obtain ⟨ℱ, hUF, hnotV⟩ := exists_ultrafilter_excluding V hVcomp hVproper
  refine ⟨ℱ, hUF, fun ⟨t⟩ => ?_⟩
  obtain ⟨⟨U, hU, a⟩, -⟩ := Quot.exists_rep t
  exact hnotV (ultrafilter_isFilter ℱ hUF U V hU hVcomp ⟨a, term_uniq _ _⟩)

/-- Meet distributes over join (one inclusion), in the subobject lattice of `1`:
    `(S∪W₁) ∩ (S∪W₂) ≤ S ∪ (W₁∩W₂)`.  Derived from `inter_union_le` (distributivity) by
    splitting both meets and bounding each piece by `S` or `W₁∩W₂`. -/
private theorem meetJoin_le (S W₁ W₂ : Subobject 𝒞 one) :
    Subobject.le (Subobject.inter (HasSubobjectUnions.union S W₁) (HasSubobjectUnions.union S W₂))
      (HasSubobjectUnions.union S (Subobject.inter W₁ W₂)) := by
  refine Subobject.le_trans (inter_union_le (HasSubobjectUnions.union S W₁) S W₂) ?_
  refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
  · exact Subobject.le_trans (Subobject.inter_le_right _ _) (HasSubobjectUnions.union_left _ _)
  · refine Subobject.le_trans (inter_comm_le _ _) ?_
    refine Subobject.le_trans (inter_union_le W₂ S W₁) ?_
    refine HasSubobjectUnions.union_min _ _ _ ?_ ?_
    · exact Subobject.le_trans (Subobject.inter_le_right _ _) (HasSubobjectUnions.union_left _ _)
    · exact Subobject.le_trans (inter_comm_le _ _) (HasSubobjectUnions.union_right _ _)

/-- **§1.635:253 — the RELATIVE ultra-filter construction.**  Given a complemented subterminator
    `U` and a sub `Usub ≤ U` that does NOT exhaust `U` (`¬ U ≤ Usub`), there is an ultra-filter `ℱ`
    that CONTAINS `U` yet omits every complemented `V ≤ Usub`.

    Freyd's `F = {W ∈ ℬ | U ≤ Usub ∪ W}` (a proper pre-filter — proper exactly because
    `¬ U ≤ Usub`, ↓-directed by `meetJoin_le`); extend to an ultra-filter `ℱ`.  Then `U ∈ ℱ`, and a
    complemented `V ≤ Usub` is excluded because its complement `Vᶜ ∈ F ⊆ ℱ` (as `Usub ∪ Vᶜ ⊇ V∪Vᶜ =
    1 ⊇ U`), so `V ∈ ℱ` would put `V ∩ Vᶜ ≤ 0` in `ℱ`, against properness.

    This is strictly more than `exists_ultrafilter_excluding` (`Usub = ` a complemented `V ⊊ 1`); it
    is what detects a proper subobject probed by a complemented subterminator. -/
theorem exists_ultrafilter_excluding_within (U : Subobject 𝒞 one) (hUcomp : IsComplementedSub U)
    (Usub : Subobject 𝒞 one) (_hsub : Usub.le U) (hproper : ¬ U.le Usub) :
    ∃ ℱ, IsUltraFilter ℱ ∧ ℱ U ∧
      ∀ V : Subobject 𝒞 one, IsComplementedSub V → V.le Usub → ¬ ℱ V := by
  let 𝒫 : (Subobject 𝒞 one) → Prop :=
    fun W => IsComplementedSub W ∧ U.le (HasSubobjectUnions.union Usub W)
  have h𝒫pre : IsPreFilter 𝒫 := by
    refine ⟨⟨U, hUcomp, HasSubobjectUnions.union_right Usub U⟩, ?_⟩
    rintro W₁ W₂ ⟨hW₁c, hW₁⟩ ⟨hW₂c, hW₂⟩
    refine ⟨Subobject.inter W₁ W₂, ⟨inter_complemented hW₁c hW₂c, ?_⟩,
      Subobject.inter_le_left _ _, Subobject.inter_le_right _ _⟩
    exact Subobject.le_trans (Subobject.le_inter hW₁ hW₂) (meetJoin_le Usub W₁ W₂)
  have h𝒫proper : IsProperFilter 𝒫 := by
    refine ⟨h𝒫pre, ?_⟩
    rintro ⟨W, ⟨_, hW⟩, hW0⟩
    refine hproper (Subobject.le_trans hW ?_)
    exact HasSubobjectUnions.union_min _ _ _ (Subobject.le_refl Usub)
      (Subobject.le_trans hW0 (PreLogos.bottom_min Usub))
  have h𝒫comp : ∀ W, 𝒫 W → IsComplementedSub W := fun W hW => hW.1
  obtain ⟨ℱ, hUF, hext⟩ := exists_ultrafilter_extending 𝒫 h𝒫proper h𝒫comp
  refine ⟨ℱ, hUF, hext U ⟨hUcomp, HasSubobjectUnions.union_right Usub U⟩, ?_⟩
  intro V hVcomp hVsub hVF
  obtain ⟨Vc, hVdisj, hVcov⟩ := hVcomp
  have hVcComp : IsComplementedSub Vc :=
    ⟨V, Subobject.le_trans (inter_comm_le Vc V) hVdisj, Subobject.le_trans hVcov (union_comm_le V Vc)⟩
  have hVcInP : 𝒫 Vc := by
    refine ⟨hVcComp, Subobject.le_trans (le_entire U) (Subobject.le_trans hVcov ?_)⟩
    exact HasSubobjectUnions.union_min _ _ _
      (Subobject.le_trans hVsub (HasSubobjectUnions.union_left Usub Vc))
      (HasSubobjectUnions.union_right Usub Vc)
  have hVcF : ℱ Vc := hext Vc hVcInP
  obtain ⟨W, hWF, hWV, hWVc⟩ := hUF.1.1.2 V Vc hVF hVcF
  exact hUF.1.2 ⟨W, hWF, Subobject.le_trans (Subobject.le_inter hWV hWVc) hVdisj⟩

end Freyd
