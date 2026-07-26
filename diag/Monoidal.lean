/-
  `diag.Monoidal` — the poset-enriched symmetric monoidal category underlying every layer.

  arXiv:1711.08699 Def. 4.1 opens "A cartesian bicategory of relations is a poset enriched category
  that is symmetric monoidal and additionally …".  This file supplies exactly that opening clause;
  `diag.CB` adds the "additionally".

  NON-STRICT, deliberately.  The papers state their syntax over props (Def. 2.2: objects are `ℕ`
  and `m ⊕ n = m + n`), where the monoidal product is strict.  We cannot follow that here: the
  semantics we must reach is `RelSet` (`AOP/A6_1_RelSet.lean`), whose tensor is the carrier product,
  and `(a × b) × c` is not `a × (b × c)` as a Lean type.  So the coherence isos are real arrows.

  SYMBOL CHOICE.  1711.08699 writes its single monoidal product `⊕`.  We write `⊗` and keep `⊕`
  free for the biproduct that `diag.Tape` adds (2210.09950 Def. 7.1), so the two products never
  collide once both layers exist.
-/
import diag.Basic

universe v u

namespace Freyd.Diag

open Freyd

/-- A poset-enriched symmetric monoidal category: `OrderedCat` plus a tensor whose action on
    arrows is functorial and monotone, with associator, unitors and symmetry as honest isos. -/
class SymMonCat (𝒞 : Type u) extends OrderedCat.{v} 𝒞 where
  /-- The monoidal product on objects. -/
  tens : 𝒞 → 𝒞 → 𝒞
  /-- The monoidal unit `I`. -/
  tunit : 𝒞
  /-- The action of the product on arrows. -/
  tensHom {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') : tens a b ⟶ tens a' b'

  /-- The product is a functor: it preserves identities. -/
  tensHom_id (a b : 𝒞) : tensHom (𝟙 a) (𝟙 b) = 𝟙 (tens a b)
  /-- The product is a functor: interchange with composition. -/
  tensHom_comp {a a' a'' b b' b'' : 𝒞} (R : a ⟶ a') (R' : a' ⟶ a'') (S : b ⟶ b') (S' : b' ⟶ b'') :
    tensHom (R ≫ R') (S ≫ S') = tensHom R S ≫ tensHom R' S'
  /-- Poset enrichment of `⊗`, the counterpart of `comp_mono`. -/
  tensHom_mono {a a' b b' : 𝒞} {R R' : a ⟶ a'} {S S' : b ⟶ b'} :
    le R R' → le S S' → le (tensHom R S) (tensHom R' S')

  /-- Associator `(a ⊗ b) ⊗ c ⟶ a ⊗ (b ⊗ c)`. -/
  tensAssoc (a b c : 𝒞) : tens (tens a b) c ⟶ tens a (tens b c)
  /-- Its inverse. -/
  tensAssocInv (a b c : 𝒞) : tens a (tens b c) ⟶ tens (tens a b) c
  tensAssoc_inv (a b c : 𝒞) : tensAssoc a b c ≫ tensAssocInv a b c = 𝟙 (tens (tens a b) c)
  inv_tensAssoc (a b c : 𝒞) : tensAssocInv a b c ≫ tensAssoc a b c = 𝟙 (tens a (tens b c))
  tensAssoc_nat {a a' b b' c c' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    tensHom (tensHom R S) T ≫ tensAssoc a' b' c'
      = tensAssoc a b c ≫ tensHom R (tensHom S T)

  /-- Left unitor `I ⊗ a ⟶ a`. -/
  lunit (a : 𝒞) : tens tunit a ⟶ a
  lunitInv (a : 𝒞) : a ⟶ tens tunit a
  lunit_inv (a : 𝒞) : lunit a ≫ lunitInv a = 𝟙 (tens tunit a)
  inv_lunit (a : 𝒞) : lunitInv a ≫ lunit a = 𝟙 a
  lunit_nat {a b : 𝒞} (R : a ⟶ b) : tensHom (𝟙 tunit) R ≫ lunit b = lunit a ≫ R

  /-- Right unitor `a ⊗ I ⟶ a`. -/
  runit (a : 𝒞) : tens a tunit ⟶ a
  runitInv (a : 𝒞) : a ⟶ tens a tunit
  runit_inv (a : 𝒞) : runit a ≫ runitInv a = 𝟙 (tens a tunit)
  inv_runit (a : 𝒞) : runitInv a ≫ runit a = 𝟙 a
  runit_nat {a b : 𝒞} (R : a ⟶ b) : tensHom R (𝟙 tunit) ≫ runit b = runit a ≫ R

  /-- Symmetry `a ⊗ b ⟶ b ⊗ a`. -/
  swap (a b : 𝒞) : tens a b ⟶ tens b a
  swap_swap (a b : 𝒞) : swap a b ≫ swap b a = 𝟙 (tens a b)
  swap_nat {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    tensHom R S ≫ swap a' b' = swap a b ≫ tensHom S R

  /-- Pentagon. -/
  pentagon (a b c d : 𝒞) :
    tensHom (tensAssoc a b c) (𝟙 d) ≫ tensAssoc a (tens b c) d
        ≫ tensHom (𝟙 a) (tensAssoc b c d)
      = tensAssoc (tens a b) c d ≫ tensAssoc a b (tens c d)
  /-- Triangle. -/
  triangle (a b : 𝒞) :
    tensAssoc a tunit b ≫ tensHom (𝟙 a) (lunit b) = tensHom (runit a) (𝟙 b)
  /-- Hexagon. -/
  hexagon (a b c : 𝒞) :
    tensAssoc a b c ≫ swap a (tens b c) ≫ tensAssoc b c a
      = tensHom (swap a b) (𝟙 c) ≫ tensAssoc b a c ≫ tensHom (𝟙 b) (swap a c)

namespace SymMonCat

scoped infixr:70 " ⊗ " => SymMonCat.tens
scoped infixr:70 " ⊗ₕ " => SymMonCat.tensHom
scoped notation "𝕀" => SymMonCat.tunit

end SymMonCat

open scoped SymMonCat

variable {𝒞 : Type u} [SymMonCat.{v} 𝒞]

/-- `R ⊗ₕ 𝟙` then `𝟙 ⊗ₕ S` is `R ⊗ₕ S`: the two ways of building a product arrow agree.
    Used constantly to split a `⊗` of composites into stages. -/
theorem tensHom_split {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    (R ⊗ₕ 𝟙 b) ≫ (𝟙 a' ⊗ₕ S) = R ⊗ₕ S := by
  rw [← SymMonCat.tensHom_comp, Cat.comp_id, Cat.id_comp]

/-- The other splitting order. -/
theorem tensHom_split' {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    (𝟙 a ⊗ₕ S) ≫ (R ⊗ₕ 𝟙 b') = R ⊗ₕ S := by
  rw [← SymMonCat.tensHom_comp, Cat.comp_id, Cat.id_comp]

end Freyd.Diag
