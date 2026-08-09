/-
  Freyd & Scedrov, *Categories and Allegories* §1.513–§1.514.

  §1.513  COVERING FAMILY.  A collection of morphisms `{Aᵢ → B}` with a common
  target COVERS if no proper subobject of `B` allows all of them.  This is the
  family generalization of the single-morphism `Cover` of §1.512 (`S1_51.lean`):
  `Cover f` is exactly `CoveringFamily` of the one-element family.

  §1.514  EPIC FAMILY.  A collection `{Aᵢ → B}` is EPIC if the maps collectively
  cancel (a monic family in the opposite category).  In a category with
  equalizers, COVER implies EPIC — the family version of §1.512's `cover_epi`,
  argued directly through the equalizer subobject.
-/

module

public import Freyd.S1_43
public import Freyd.S1_51

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.513  Covering family

  Reuses the §1.51 `Subobject` / `Allows` / `Subobject.IsEntire` machinery.
  A family `f : ∀ i, A i ⟶ B` COVERS `B` when every subobject that allows all
  of the `f i` is entire — i.e. no *proper* subobject allows all of them. -/

@[expose] public def CoveringFamily {ι : Type} {A : ι → 𝒞} {B : 𝒞} (f : ∀ i, A i ⟶ B) : Prop :=
  ∀ S : Subobject 𝒞 B, (∀ i, Allows S (f i)) → S.IsEntire

/-- The single-morphism `Cover` (§1.512) is exactly `CoveringFamily` of the
    one-element (`Unit`-indexed) family.  Both say: any subobject through which
    the morphism(s) factor is entire. -/
public theorem cover_iff_coveringFamily_singleton {X B : 𝒞} (f : X ⟶ B) :
    Cover f ↔ CoveringFamily (A := fun _ : Unit => X) (fun _ : Unit => f) := by
  constructor
  · -- Cover f → CoveringFamily {f}
    intro hcov S hallow
    obtain ⟨g, hg⟩ := hallow ()
    exact hcov S.arr g S.monic hg
  · -- CoveringFamily {f} → Cover f
    intro hfam C m g hm hgm
    exact hfam (Subobject.mk C m hm) (fun _ => ⟨g, hgm⟩)

/-! ## §1.514  Epic family, and cover ⟹ epic

  A family `f : ∀ i, A i ⟶ B` is EPIC (jointly right-cancellable) if any two
  maps out of `B` agreeing after every `f i` are equal. -/

@[expose] public def EpicFamily {ι : Type} {A : ι → 𝒞} {B : 𝒞} (f : ∀ i, A i ⟶ B) : Prop :=
  ∀ {Y : 𝒞} (g h : B ⟶ Y), (∀ i, f i ≫ g = f i ≫ h) → g = h

/-- The equalizer inclusion `eqMap g h : E ⟶ B` is monic: two maps into `E`
    agreeing after it are both the equalizer lift of the same cone, hence equal.
    Stated from the bare equalizer API, so it needs no Cartesian context and this file's imports
    stay minimal; it is the repo's single statement of the fact. -/
public theorem eqMap_monic [HasEqualizers 𝒞] {A B : 𝒞} (g h : A ⟶ B) : Monic (eqMap g h) := by
  intro W p q hpq
  have hp_eq : (p ≫ eqMap g h) ≫ g = (p ≫ eqMap g h) ≫ h := by
    rw [Cat.assoc, Cat.assoc, eqMap_eq]
  have hp : p = eqLift g h (p ≫ eqMap g h) hp_eq := eqLift_uniq g h _ hp_eq p rfl
  have hq : q = eqLift g h (p ≫ eqMap g h) hp_eq := eqLift_uniq g h _ hp_eq q hpq.symm
  rw [hp, hq]

/-- **§1.514.**  In a category with equalizers, a COVERING family is EPIC.
    If `g, h : B ⟶ Y` agree after every `f i`, they factor through the
    equalizer subobject `e : E ↣ B`; each `f i` factors through `e` (via the
    equalizer lift), so the covering condition forces `e` iso, and `e ≫ g = e ≫ h`
    then cancels to `g = h`. -/
public theorem covering_family_epic [HasEqualizers 𝒞] {ι : Type} {A : ι → 𝒞} {B : 𝒞}
    {f : ∀ i, A i ⟶ B} (hf : CoveringFamily f) : EpicFamily f := by
  intro Y g h hgh
  -- The equalizer of g, h as a subobject of B.
  let S : Subobject 𝒞 B := ⟨eqObj g h, eqMap g h, eqMap_monic g h⟩
  -- Every `f i` factors through the equalizer (it equalizes g, h by `hgh`).
  have hallows : ∀ i, Allows S (f i) :=
    fun i => ⟨eqLift g h (f i) (hgh i), eqLift_fac g h (f i) (hgh i)⟩
  -- Covering ⟹ the equalizer inclusion is iso.
  obtain ⟨einv, _, hinv⟩ := hf S hallows
  -- `e ≫ g = e ≫ h`; cancel the (now invertible) `e = eqMap g h` on the left.
  calc g = (einv ≫ eqMap g h) ≫ g := by rw [hinv, Cat.id_comp]
    _ = einv ≫ (eqMap g h ≫ g) := Cat.assoc _ _ _
    _ = einv ≫ (eqMap g h ≫ h) := by rw [eqMap_eq]
    _ = (einv ≫ eqMap g h) ≫ h := (Cat.assoc _ _ _).symm
    _ = h := by rw [hinv, Cat.id_comp]

end Freyd
