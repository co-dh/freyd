/-
  Freyd & Scedrov, *Categories and Allegories* §1.568  Quotient-objects.

  There is a PREORDER of covers with a given object `A` as source, where
  `f ≤ g` iff `f` factors through `g`.  Its associated poset [1.246] consists
  of the QUOTIENT-OBJECTS of `A`, called `Quot(A)`.  This is NOT dual to
  `Sub(A)` [1.412].  [1.566] yields a FAITHFUL ORDER-REVERSING functor from
  `Quot(A)` to the poset of equivalence relations on `A`, sending a cover to
  its kernel-pair (level) equivalence relation.

  We mirror the `Subobject` presentation of §1.51 exactly: we do not quotient,
  we keep the preorder plus the "mutual `≤` ⟹ iso" lemma (`le_antisymm_iso`),
  which realises the associated poset in the sense of [1.246].  The order side
  is FLIPPED relative to `Subobject`: covers point OUT of `A`, so the witness
  post-composes on the codomain (`g.arr ≫ h = f.arr`) instead of pre-composing
  on the domain.
-/


module

public import Freyd.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.568  The preorder of covers with source `A` -/

/-- A candidate QUOTIENT-OBJECT of `A`: a cover with source `A`
    (codomain `cod`, cover `arr : A ⟶ cod`).  The dual side to `Subobject`. -/
public structure QuotObj (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) where
  cod   : 𝒞
  arr   : A ⟶ cod
  cover : Cover arr

/-- §1.568 order on covers: `f ≤ g` iff `f` FACTORS THROUGH `g`, i.e. there is
    `h : g.cod ⟶ f.cod` with `g.arr ≫ h = f.arr` (diagram order).  Note the
    factoring is on the codomain side — the mirror image of `Subobject.le`. -/
@[expose] public def QuotObj.le {A : 𝒞} (f g : QuotObj 𝒞 A) : Prop :=
  ∃ h : g.cod ⟶ f.cod, g.arr ≫ h = f.arr

@[refl] theorem QuotObj.le_refl {A : 𝒞} (f : QuotObj 𝒞 A) : f.le f :=
  ⟨Cat.id f.cod, Cat.comp_id f.arr⟩

public theorem QuotObj.le_trans {A : 𝒞} {X Y Z : QuotObj 𝒞 A}
    (h₁ : X.le Y) (h₂ : Y.le Z) : X.le Z :=
  let ⟨f, hf⟩ := h₁; let ⟨g, hg⟩ := h₂
  -- X factors through Y (`Y.arr ≫ f = X.arr`), Y through Z (`Z.arr ≫ g = Y.arr`),
  -- so X factors through Z via `g ≫ f`.
  ⟨g ≫ f, by rw [← Cat.assoc, hg, hf]⟩

@[expose] public instance {A : 𝒞} : Trans (@QuotObj.le 𝒞 _ A) (@QuotObj.le 𝒞 _ A) (@QuotObj.le 𝒞 _ A) :=
  ⟨QuotObj.le_trans⟩

/-- §1.246/§1.568  ANTISYMMETRY up to iso: two mutually-`≤` covers with source `A`
    have isomorphic codomains OVER `A`.  Both round-trips are identities because
    covers are epic (`cover_epi`).  This realises the associated poset `Quot(A)`. -/
theorem QuotObj.le_antisymm_iso [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {A : 𝒞} {f g : QuotObj 𝒞 A}
    (hfg : f.le g) (hgf : g.le f) :
    ∃ e : g.cod ⟶ f.cod, IsIso e ∧ g.arr ≫ e = f.arr := by
  obtain ⟨h, hh⟩ := hfg   -- h : g.cod ⟶ f.cod, g.arr ≫ h = f.arr
  obtain ⟨k, hk⟩ := hgf   -- k : f.cod ⟶ g.cod, f.arr ≫ k = g.arr
  -- `h ≫ k = id` on `g.cod`: cancel the cover `g.arr` (epic).
  have hhk : h ≫ k = Cat.id g.cod :=
    cover_epi g.cover (by rw [← Cat.assoc, hh, hk, Cat.comp_id])
  -- `k ≫ h = id` on `f.cod`: cancel the cover `f.arr` (epic).
  have hkh : k ≫ h = Cat.id f.cod :=
    cover_epi f.cover (by rw [← Cat.assoc, hk, hh, Cat.comp_id])
  exact ⟨h, ⟨k, hhk, hkh⟩, hh⟩

/-! ## §1.568  The faithful order-reversing functor `Quot(A) → EquivRel(A)`

  [1.566]: a cover `f : A ↠ B` is the coequalizer of its kernel pair, so the
  map sending a quotient-object to its LEVEL (kernel-pair) equivalence relation
  on `A` is a faithful order-REVERSING functor into the poset of equivalence
  relations.  We reuse the §1.567 machinery: `kernelPairRel`,
  `level_is_equivalence_relation`, `cover_is_coequalizer_of_level`. -/

section Ker
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The image of a quotient-object under the §1.568 functor: the LEVEL
    (kernel-pair) relation of its cover, a relation on `A`. -/
def QuotObj.ker {A : 𝒞} (f : QuotObj 𝒞 A) : BinRel 𝒞 A A := kernelPairRel f.arr

/-- §1.567: the value `f.ker` really is an equivalence relation on `A`. -/
theorem QuotObj.ker_isEquivalence [HasImages 𝒞] {A : 𝒞} (f : QuotObj 𝒞 A) :
    EquivalenceRelation f.ker :=
  level_is_equivalence_relation f.arr

/-- §1.568 (ORDER-REVERSING).  If `f ≤ g` (f factors through g) then the level of
    `g` is CONTAINED in the level of `f`: `g.ker ⊂ f.ker`.  Reason: `g.arr ≫ h =
    f.arr`, so the kernel pair of `g` also equalizes `f.arr` and hence lifts into
    the kernel pair of `f`.  The functor `Quot(A) → EquivRel(A)` is antitone. -/
theorem QuotObj.ker_antitone {A : 𝒞} {f g : QuotObj 𝒞 A}
    (hfg : f.le g) : RelLe g.ker f.ker := by
  obtain ⟨h, hh⟩ := hfg   -- g.arr ≫ h = f.arr
  -- The two legs of `g`'s kernel pair agree after `f.arr`.
  have heq : kp₁ (f := g.arr) ≫ f.arr = kp₂ (f := g.arr) ≫ f.arr := by
    rw [← hh, ← Cat.assoc, kp_sq, Cat.assoc]
  -- Lift them into the kernel pair of `f`.
  let k := (HasPullbacks.has f.arr f.arr).lift ⟨_, kp₁ (f := g.arr), kp₂ (f := g.arr), heq⟩
  exact ⟨k, kp_lift_p₁ _ _ heq, kp_lift_p₂ _ _ heq⟩

end Ker

/-- §1.568 (FAITHFUL / order-reflecting).  Conversely, in a REGULAR category, if
    `g.ker ⊂ f.ker` then `f ≤ g`.  Reason: a `RelHom g.ker → f.ker` says `f.arr`
    equalizes the kernel pair of `g`; since `g` is a cover it is the coequalizer of
    its kernel pair [1.566], so `f.arr` factors through `g.arr`. -/
theorem QuotObj.le_of_ker_le [RegularCategory 𝒞] {A : 𝒞} {f g : QuotObj 𝒞 A}
    (hle : RelLe g.ker f.ker) : f.le g := by
  obtain ⟨k, hk₁, hk₂⟩ := hle   -- k : ker g → ker f, k ≫ kp₁ f = kp₁ g, k ≫ kp₂ f = kp₂ g
  simp only [QuotObj.ker, kernelPairRel] at hk₁ hk₂
  -- `f.arr` equalizes the kernel pair of `g`.
  have hg_eq : kp₁ (f := g.arr) ≫ f.arr = kp₂ (f := g.arr) ≫ f.arr := by
    rw [← hk₁, ← hk₂, Cat.assoc, Cat.assoc, kp_sq]
  -- `g` is the coequalizer of its kernel pair, so `f.arr` factors through `g.arr`.
  obtain ⟨h, hh, _⟩ := cover_is_coequalizer_of_level g.arr g.cover f.arr hg_eq
  exact ⟨h, hh⟩

/-- §1.568 (HEADLINE): the functor `Quot(A) → EquivRel(A)`, `f ↦ f.ker`, is a
    FAITHFUL ORDER-REVERSING functor.  In a regular category the order relation
    is mirrored exactly: `f ≤ g` in `Quot(A)` iff `g.ker ⊂ f.ker` in `EquivRel(A)`.
    Forward is `ker_antitone` (order-reversing), backward is `le_of_ker_le`
    (faithfulness / order-reflection); together an order-embedding into the
    opposite of `EquivRel(A)`. -/
theorem QuotObj.le_iff_ker_le [RegularCategory 𝒞] {A : 𝒞} {f g : QuotObj 𝒞 A} :
    f.le g ↔ RelLe g.ker f.ker :=
  ⟨QuotObj.ker_antitone, QuotObj.le_of_ker_le⟩

/-- §1.568 (faithful, iso form): equal levels ⟹ isomorphic quotient-objects.
    If `f.ker` and `g.ker` are mutually contained (equal as equivalence relations)
    then the two covers have isomorphic codomains over `A`.  So distinct
    quotient-objects of `Quot(A)` have distinct levels — the functor is faithful. -/
theorem QuotObj.iso_of_ker_eq [RegularCategory 𝒞] {A : 𝒞} {f g : QuotObj 𝒞 A}
    (h₁ : RelLe f.ker g.ker) (h₂ : RelLe g.ker f.ker) :
    ∃ e : g.cod ⟶ f.cod, IsIso e ∧ g.arr ≫ e = f.arr :=
  QuotObj.le_antisymm_iso (QuotObj.le_of_ker_le h₂) (QuotObj.le_of_ker_le h₁)

end Freyd
