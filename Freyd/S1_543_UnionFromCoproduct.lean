/-
  Generic union-closure brick: `HasBinaryCoproducts` + `HasImages` ⟹ `HasSubobjectUnions`.

  In any (positive) category with binary coproducts and images, the union of two subobjects
  `S, T ⊆ A` is `image (case S.arr T.arr : S.dom + T.dom → A)` — the image of the copairing of
  their inclusions.  This is `union_via_coproduct_image` (S1_61) read as a CONSTRUCTOR.

  Kept as a `def` (not an `instance`) to avoid `HasImages`/`HasSubobjectUnions` instance diamonds;
  applied explicitly where a category has coproducts+images but no bespoke unions — in particular the
  §1.543 capitalization colimit (`colimitHasBinaryCoproducts` + `colimitHasImages`), the
  union-closure step of §1.63 (capital POSITIVE pre-logos). -/
module

public import Freyd.S1_61

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [HasImages 𝒞] [HasBinaryCoproducts 𝒞]

/-- **Unions from coproducts + images.**  `S ∪ T := image (case S.arr T.arr)`.  `union_left`/
    `union_right` factor `S.arr`/`T.arr` through the image via `inl`/`inr`; `union_min` copairs the
    two `≤ U` witnesses and applies `image_min`. -/
@[expose] public def hasSubobjectUnions_of_coproducts_images : HasSubobjectUnions 𝒞 where
  union {_} S T := image (HasBinaryCoproducts.case S.arr T.arr)
  union_left {_} S T :=
    ⟨HasBinaryCoproducts.inl ≫ image.lift (HasBinaryCoproducts.case S.arr T.arr), by
      rw [Cat.assoc, image.lift_fac]; exact HasBinaryCoproducts.case_inl S.arr T.arr⟩
  union_right {_} S T :=
    ⟨HasBinaryCoproducts.inr ≫ image.lift (HasBinaryCoproducts.case S.arr T.arr), by
      rw [Cat.assoc, image.lift_fac]; exact HasBinaryCoproducts.case_inr S.arr T.arr⟩
  union_min {_} S T U hSU hTU := by
    obtain ⟨s, hs⟩ := hSU
    obtain ⟨t, ht⟩ := hTU
    refine image_min (HasBinaryCoproducts.case S.arr T.arr) U
      ⟨HasBinaryCoproducts.case s t, ?_⟩
    refine HasBinaryCoproducts.case_uniq S.arr T.arr (HasBinaryCoproducts.case s t ≫ U.arr) ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hs
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact ht

end Freyd
