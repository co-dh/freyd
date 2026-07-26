/-
  `diag.Monoidal` — the poset-enriched symmetric monoidal category underlying every layer.

  functorialSemanticsForRelationalTheories.pdf Def. 4.1 opens "A cartesian bicategory of
  relations is a poset enriched category
  that is symmetric monoidal and additionally …".  This file supplies exactly that opening clause;
  `diag.CB` adds the "additionally".

  NON-STRICT, deliberately.  The papers state their syntax over props (Def. 2.2: objects are `ℕ`
  and `m ⊕ n = m + n`), where the monoidal product is strict.  We cannot follow that here: the
  semantics we must reach is `RelSet` (`AOP/A6_1_RelSet.lean`), whose tensor is the carrier product,
  and `(a × b) × c` is not `a × (b × c)` as a Lean type.  So the coherence isos are real arrows.

  SYMBOL CHOICE.  functorialSemanticsForRelationalTheories.pdf writes its single monoidal
  product `⊕`.  We write `⊗` and keep `⊕`
  free for the biproduct that `diag.Tape` adds (TapeDiagrams.pdf Def. 7.1), so the two products never
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
  /-- Unitor–symmetry compatibility, `γ_{a,I} ; λ_a = ρ_a`.  Part of the standard axioms for a
      symmetric monoidal category (Mac Lane), not an extra assumption of our own; it is what lets
      a discard be moved from one side of a product to the other. -/
  swap_lunit (a : 𝒞) : swap a tunit ≫ lunit a = runit a

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

/-- The inverse form of `swap_lunit`: `λ⁻¹_a ; γ_{I,a} = ρ⁻¹_a`. -/
theorem lunitInv_swap (a : 𝒞) :
    SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a = SymMonCat.runitInv a := by
  have hround : (SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a) ≫ SymMonCat.runit a = 𝟙 a := by
    calc (SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a) ≫ SymMonCat.runit a
        = (SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a)
            ≫ SymMonCat.swap a (𝕀 : 𝒞) ≫ SymMonCat.lunit a := by rw [SymMonCat.swap_lunit]
      _ = SymMonCat.lunitInv a ≫ (SymMonCat.swap (𝕀 : 𝒞) a ≫ SymMonCat.swap a (𝕀 : 𝒞))
            ≫ SymMonCat.lunit a := by simp only [Cat.assoc]
      _ = SymMonCat.lunitInv a ≫ 𝟙 ((𝕀 : 𝒞) ⊗ a) ≫ SymMonCat.lunit a := by
            rw [SymMonCat.swap_swap]
      _ = 𝟙 a := by rw [Cat.id_comp, SymMonCat.inv_lunit]
  calc SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a
      = (SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a) ≫ 𝟙 (a ⊗ (𝕀 : 𝒞)) := (Cat.comp_id _).symm
    _ = (SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a)
          ≫ SymMonCat.runit a ≫ SymMonCat.runitInv a := by rw [SymMonCat.runit_inv]
    _ = ((SymMonCat.lunitInv a ≫ SymMonCat.swap (𝕀 : 𝒞) a) ≫ SymMonCat.runit a)
          ≫ SymMonCat.runitInv a := by simp only [Cat.assoc]
    _ = SymMonCat.runitInv a := by rw [hround, Cat.id_comp]

/-- Naturality of the associator read in the inverse direction — obtained by conjugating
    `tensAssoc_nat` with `tensAssoc_inv`/`inv_tensAssoc`.  Needed whenever a proof pushes a
    re-bracketing past a product of arrows rather than pulling it. -/
theorem tensAssocInv_nat {a a' b b' c c' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    SymMonCat.tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = (R ⊗ₕ (S ⊗ₕ T)) ≫ SymMonCat.tensAssocInv a' b' c' := by
  have hnat := SymMonCat.tensAssoc_nat (𝒞 := 𝒞) R S T
  calc SymMonCat.tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = SymMonCat.tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
          ≫ (SymMonCat.tensAssoc a' b' c' ≫ SymMonCat.tensAssocInv a' b' c') := by
        rw [SymMonCat.tensAssoc_inv, Cat.comp_id]
    _ = SymMonCat.tensAssocInv a b c ≫ (((R ⊗ₕ S) ⊗ₕ T) ≫ SymMonCat.tensAssoc a' b' c')
          ≫ SymMonCat.tensAssocInv a' b' c' := by simp only [Cat.assoc]
    _ = SymMonCat.tensAssocInv a b c ≫ (SymMonCat.tensAssoc a b c ≫ (R ⊗ₕ (S ⊗ₕ T)))
          ≫ SymMonCat.tensAssocInv a' b' c' := by rw [hnat]
    _ = (SymMonCat.tensAssocInv a b c ≫ SymMonCat.tensAssoc a b c)
          ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ SymMonCat.tensAssocInv a' b' c' := by simp only [Cat.assoc]
    _ = (R ⊗ₕ (S ⊗ₕ T)) ≫ SymMonCat.tensAssocInv a' b' c' := by
        rw [SymMonCat.inv_tensAssoc, Cat.id_comp]

/-- Naturality of the left unitor read in the inverse direction, `λ⁻¹_a ; (𝟙_I ⊗ R) = R ; λ⁻¹_b`.
    This is the step that pulls an arrow out to the front of a bent wire (`CartBicat.bend_unbend`). -/
theorem lunitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) = R ≫ SymMonCat.lunitInv b := by
  calc SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R)
      = SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R)
          ≫ SymMonCat.lunit b ≫ SymMonCat.lunitInv b := by
        rw [SymMonCat.lunit_inv, Cat.comp_id]
    _ = SymMonCat.lunitInv a ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ SymMonCat.lunit b)
          ≫ SymMonCat.lunitInv b := by simp only [Cat.assoc]
    _ = (SymMonCat.lunitInv a ≫ SymMonCat.lunit a) ≫ R ≫ SymMonCat.lunitInv b := by
        rw [SymMonCat.lunit_nat]; simp only [Cat.assoc]
    _ = R ≫ SymMonCat.lunitInv b := by rw [SymMonCat.inv_lunit, Cat.id_comp]

/-- Naturality of the right unitor read in the inverse direction, `ρ⁻¹_a ; (R ⊗ 𝟙_I) = R ; ρ⁻¹_b`. -/
theorem runitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    SymMonCat.runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = R ≫ SymMonCat.runitInv b := by
  calc SymMonCat.runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = SymMonCat.runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ SymMonCat.runit b ≫ SymMonCat.runitInv b := by
        rw [SymMonCat.runit_inv, Cat.comp_id]
    _ = SymMonCat.runitInv a ≫ ((R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b)
          ≫ SymMonCat.runitInv b := by simp only [Cat.assoc]
    _ = (SymMonCat.runitInv a ≫ SymMonCat.runit a) ≫ R ≫ SymMonCat.runitInv b := by
        rw [SymMonCat.runit_nat]; simp only [Cat.assoc]
    _ = R ≫ SymMonCat.runitInv b := by rw [SymMonCat.inv_runit, Cat.id_comp]

/-! ### Kelly's coherence lemmas

  Mac Lane's original axiom list for a monoidal category contained five diagrams; Kelly (1964)
  showed that only the pentagon and the triangle are independent, the other three being derivable.
  The three derivable ones are `lunit_tens`, `runit_tens` and `lunit_unit` below.  They are proved
  here rather than added as `SymMonCat` fields, because they are exactly what the wire-bending
  proofs of `diag/CB.lean` consume: they are what lets a *passenger* wire ride past the unit object
  created by a cap.  Nothing in this group mentions the Frobenius structure — it is pure monoidal
  bookkeeping. -/

/-- `𝟙_I ⊗ −` is faithful: `λ` conjugates it back to the identity.  Kelly's derivations all end by
    cancelling this functor. -/
theorem tensUnit_left_faithful {a b : 𝒞} {R S : a ⟶ b}
    (h : (𝟙 (𝕀 : 𝒞) ⊗ₕ R) = (𝟙 (𝕀 : 𝒞) ⊗ₕ S)) : R = S := by
  have key : ∀ T : a ⟶ b,
      SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ T) ≫ SymMonCat.lunit b = T := by
    intro T
    rw [SymMonCat.lunit_nat, ← Cat.assoc, SymMonCat.inv_lunit, Cat.id_comp]
  calc R = SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ SymMonCat.lunit b := (key R).symm
    _ = SymMonCat.lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ SymMonCat.lunit b := by rw [h]
    _ = S := key S

/-- `− ⊗ 𝟙_I` is faithful, the mirror of `tensUnit_left_faithful` via `ρ`. -/
theorem tensUnit_right_faithful {a b : 𝒞} {R S : a ⟶ b}
    (h : (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = (S ⊗ₕ 𝟙 (𝕀 : 𝒞))) : R = S := by
  have key : ∀ T : a ⟶ b,
      SymMonCat.runitInv a ≫ (T ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b = T := by
    intro T
    rw [SymMonCat.runit_nat, ← Cat.assoc, SymMonCat.inv_runit, Cat.id_comp]
  calc R = SymMonCat.runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b := (key R).symm
    _ = SymMonCat.runitInv a ≫ (S ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.runit b := by rw [h]
    _ = S := key S

/-- KELLY: `α_{I,a,b} ; λ_{a⊗b} = λ_a ⊗ 𝟙_b`.  Both sides, prefixed by the isomorphism
    `(α_{I,I,a} ⊗ 𝟙_b) ; α_{I,I⊗a,b}` and wrapped in `𝟙_I ⊗ −`, reduce to
    `α_{I⊗I,a,b} ; (ρ_I ⊗ 𝟙_{a⊗b})` — the first by the pentagon and the triangle at `(I, a⊗b)`,
    the second by associator naturality and the triangle at `(I, a)`. -/
theorem lunit_tens (a b : 𝒞) :
    SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b)
      = SymMonCat.lunit a ⊗ₕ 𝟙 b := by
  refine tensUnit_left_faithful ?_
  -- The common prefix, and its inverse.
  have hPP : (SymMonCat.tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
        ≫ (SymMonCat.tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
      ≫ ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b) = 𝟙 _ := by
    calc (SymMonCat.tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
          ≫ (SymMonCat.tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
        ≫ ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        = SymMonCat.tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ ((SymMonCat.tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a
                  ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a) ⊗ₕ (𝟙 b ≫ 𝟙 b))
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b := by
          rw [SymMonCat.tensHom_comp]; simp only [Cat.assoc]
      _ = 𝟙 _ := by
          rw [SymMonCat.inv_tensAssoc, Cat.id_comp, SymMonCat.tensHom_id, Cat.id_comp,
            SymMonCat.inv_tensAssoc]
  -- Claim A: the pentagon route.
  have hA : ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
      ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b)))
      = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by
    have hsplit : (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b)))
        = (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.tensAssoc (𝕀 : 𝒞) a b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (a ⊗ b)) := by
      rw [← SymMonCat.tensHom_comp, Cat.id_comp]
    rw [hsplit]
    calc ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.tensAssoc (𝕀 : 𝒞) a b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (a ⊗ b))
        = ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.tensAssoc (𝕀 : 𝒞) a b))
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (a ⊗ b)) := by simp only [Cat.assoc]
      _ = (SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (a ⊗ b))
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (a ⊗ b)) := by rw [SymMonCat.pentagon]
      _ = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (a ⊗ b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (a ⊗ b)) := by simp only [Cat.assoc]
      _ = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by rw [SymMonCat.triangle]
  -- Claim B: the naturality route.
  have hB : ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
      ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b))
      = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by
    calc ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b))
        = (SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b)) := by simp only [Cat.assoc]
      _ = (SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit a) ⊗ₕ 𝟙 b)
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) a b := by rw [← SymMonCat.tensAssoc_nat]
      _ = ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit a))
              ⊗ₕ (𝟙 b ≫ 𝟙 b))
            ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) a b := by
          rw [SymMonCat.tensHom_comp]; simp only [Cat.assoc]
      _ = ((SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) a b := by
          rw [SymMonCat.triangle, Cat.id_comp]
      _ = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ (𝟙 a ⊗ₕ 𝟙 b)) := by rw [SymMonCat.tensAssoc_nat]
      _ = SymMonCat.tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by rw [SymMonCat.tensHom_id]
  -- Cancel the common prefix.
  have hAB := hA.trans hB.symm
  calc (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b)))
      = 𝟙 _ ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b))) :=
        (Cat.id_comp _).symm
    _ = (SymMonCat.tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (SymMonCat.tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
          ≫ ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
              ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
          ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.tensAssoc (𝕀 : 𝒞) a b ≫ SymMonCat.lunit (a ⊗ b))) := by
        rw [← hPP]; simp only [Cat.assoc]
    _ = (SymMonCat.tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (SymMonCat.tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
          ≫ ((SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
              ≫ SymMonCat.tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
          ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b)) := by rw [hAB]
    _ = 𝟙 _ ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b)) := by
        rw [← hPP]; simp only [Cat.assoc]
    _ = (𝟙 (𝕀 : 𝒞) ⊗ₕ (SymMonCat.lunit a ⊗ₕ 𝟙 b)) := Cat.id_comp _

/-- KELLY, the mirror of `lunit_tens`: `α_{a,b,I} ; (𝟙_a ⊗ ρ_b) = ρ_{a⊗b}`.  Both sides, tensored
    with `𝟙_I` and followed by `α_{a,b,I}`, are the two halves of the pentagon at `(a, b, I, I)`
    post-composed with `𝟙_a ⊗ (𝟙_b ⊗ λ_I)`; the triangle at `(b, I)` closes one and the triangle
    at `(a⊗b, I)` the other. -/
theorem runit_tens (a b : 𝒞) :
    SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b) = SymMonCat.runit (a ⊗ b) := by
  refine tensUnit_right_faithful ?_
  -- Claim A: the pentagon's left-hand side, closed by the triangle at `(b, I)`.
  have hA : ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
        ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)
      = ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ SymMonCat.tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
          ≫ (𝟙 a ⊗ₕ SymMonCat.tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)))
        ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by
    calc ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)
        = ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ ((𝟙 a ⊗ₕ SymMonCat.runit b) ⊗ₕ 𝟙 (𝕀 : 𝒞)))
            ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞) := by
          rw [← SymMonCat.tensHom_comp, Cat.comp_id]
      _ = (SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ ((𝟙 a ⊗ₕ SymMonCat.runit b) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞) := by simp only [Cat.assoc]
      _ = (SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ SymMonCat.tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ (SymMonCat.runit b ⊗ₕ 𝟙 (𝕀 : 𝒞))) := by rw [SymMonCat.tensAssoc_nat]
      _ = (SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ SymMonCat.tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ (SymMonCat.tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)
                ≫ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞)))) := by rw [SymMonCat.triangle]
      _ = ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ SymMonCat.tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ SymMonCat.tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by
          have hs : (𝟙 a ⊗ₕ (SymMonCat.tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)
                ≫ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))))
              = (𝟙 a ⊗ₕ SymMonCat.tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞))
                  ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by
            rw [← SymMonCat.tensHom_comp, Cat.id_comp]
          rw [hs]; simp only [Cat.assoc]
  -- Claim B: the pentagon's right-hand side, closed by the triangle at `(a⊗b, I)`.
  have hB : (SymMonCat.runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)
      = (SymMonCat.tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞) ≫ SymMonCat.tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)))
        ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by
    calc (SymMonCat.runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)
        = (SymMonCat.tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (a ⊗ b) ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞)))
            ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞) := by rw [SymMonCat.triangle]
      _ = SymMonCat.tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ ((𝟙 a ⊗ₕ 𝟙 b) ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))
            ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞) := by
          rw [SymMonCat.tensHom_id]; simp only [Cat.assoc]
      _ = SymMonCat.tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ SymMonCat.tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by rw [SymMonCat.tensAssoc_nat]
      _ = (SymMonCat.tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ SymMonCat.tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) := by simp only [Cat.assoc]
  -- The two prefixes agree by the pentagon, so the two `⊗ 𝟙_I`s agree once `α` is cancelled.
  have hcancel : ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
        ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)
      = (SymMonCat.runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞) := by
    rw [hA, hB, SymMonCat.pentagon]
  calc ((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = (((SymMonCat.tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ SymMonCat.runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞)) ≫ SymMonCat.tensAssocInv a b (𝕀 : 𝒞) := by
        rw [Cat.assoc, SymMonCat.tensAssoc_inv, Cat.comp_id]
    _ = ((SymMonCat.runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.tensAssoc a b (𝕀 : 𝒞))
          ≫ SymMonCat.tensAssocInv a b (𝕀 : 𝒞) := by rw [hcancel]
    _ = (SymMonCat.runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) := by
        rw [Cat.assoc, SymMonCat.tensAssoc_inv, Cat.comp_id]

/-- KELLY: `λ_I = ρ_I`, Mac Lane's third redundant axiom.  Both `λ_I ⊗ 𝟙_I` and `ρ_I ⊗ 𝟙_I`,
    followed by `λ_I`, equal `α_{I,I,I} ; (𝟙_I ⊗ λ_I) ; λ_I` — the first by `lunit_tens` plus
    naturality of `λ`, the second by the triangle at `(I, I)`. -/
theorem lunit_unit : SymMonCat.lunit (𝕀 : 𝒞) = SymMonCat.runit (𝕀 : 𝒞) := by
  refine tensUnit_right_faithful ?_
  have hkey : (SymMonCat.lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞)
      = (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
    calc (SymMonCat.lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞)
        = (SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ SymMonCat.lunit ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞))) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
          rw [lunit_tens]
      _ = SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ SymMonCat.lunit ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
          simp only [Cat.assoc]
      _ = SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
          rw [SymMonCat.lunit_nat]
      _ = (SymMonCat.tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ SymMonCat.lunit (𝕀 : 𝒞))) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
          simp only [Cat.assoc]
      _ = (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞) := by
          rw [SymMonCat.triangle]
  calc (SymMonCat.lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = ((SymMonCat.lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞))
          ≫ SymMonCat.lunitInv (𝕀 : 𝒞) := by
        rw [Cat.assoc, SymMonCat.lunit_inv, Cat.comp_id]
    _ = ((SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ SymMonCat.lunit (𝕀 : 𝒞))
          ≫ SymMonCat.lunitInv (𝕀 : 𝒞) := by rw [hkey]
    _ = (SymMonCat.runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) := by
        rw [Cat.assoc, SymMonCat.lunit_inv, Cat.comp_id]

end Freyd.Diag
