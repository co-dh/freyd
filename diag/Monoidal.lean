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
    R ≤ R' → S ≤ S' → (tensHom R S) ≤ (tensHom R' S')

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

open SymMonCat

variable {𝒞 : Type u} [SymMonCat.{v} 𝒞]

/-- `R ⊗ₕ 𝟙` then `𝟙 ⊗ₕ S` is `R ⊗ₕ S`: the two ways of building a product arrow agree.
    Used constantly to split a `⊗` of composites into stages. -/
theorem tensHom_split {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    (R ⊗ₕ 𝟙 b) ≫ (𝟙 a' ⊗ₕ S) = R ⊗ₕ S := by
  rw [← tensHom_comp, Cat.comp_id, Cat.id_comp]

/-- The other splitting order. -/
theorem tensHom_split' {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    (𝟙 a ⊗ₕ S) ≫ (R ⊗ₕ 𝟙 b') = R ⊗ₕ S := by
  rw [← tensHom_comp, Cat.comp_id, Cat.id_comp]

/-- The inverse form of `swap_lunit`: `λ⁻¹_a ; γ_{I,a} = ρ⁻¹_a`. -/
theorem lunitInv_swap (a : 𝒞) :
    lunitInv a ≫ swap (𝕀 : 𝒞) a = runitInv a := by
  have hround : (lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ runit a = 𝟙 a := by
    calc (lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ runit a
        = (lunitInv a ≫ swap (𝕀 : 𝒞) a)
            ≫ swap a (𝕀 : 𝒞) ≫ lunit a := by rw [swap_lunit]
      _ = lunitInv a ≫ (swap (𝕀 : 𝒞) a ≫ swap a (𝕀 : 𝒞))
            ≫ lunit a := by simp only [Cat.assoc]
      _ = lunitInv a ≫ 𝟙 ((𝕀 : 𝒞) ⊗ a) ≫ lunit a := by
            rw [swap_swap]
      _ = 𝟙 a := by rw [Cat.id_comp, inv_lunit]
  calc lunitInv a ≫ swap (𝕀 : 𝒞) a
      = (lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ 𝟙 (a ⊗ (𝕀 : 𝒞)) := (Cat.comp_id _).symm
    _ = (lunitInv a ≫ swap (𝕀 : 𝒞) a)
          ≫ runit a ≫ runitInv a := by rw [runit_inv]
    _ = ((lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ runit a)
          ≫ runitInv a := by simp only [Cat.assoc]
    _ = runitInv a := by rw [hround, Cat.id_comp]

/-- Naturality of the associator read in the inverse direction — obtained by conjugating
    `tensAssoc_nat` with `tensAssoc_inv`/`inv_tensAssoc`.  Needed whenever a proof pushes a
    re-bracketing past a product of arrows rather than pulling it. -/
theorem tensAssocInv_nat {a a' b b' c c' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = (R ⊗ₕ (S ⊗ₕ T)) ≫ tensAssocInv a' b' c' := by
  have hnat := tensAssoc_nat (𝒞 := 𝒞) R S T
  calc tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
          ≫ (tensAssoc a' b' c' ≫ tensAssocInv a' b' c') := by
        rw [tensAssoc_inv, Cat.comp_id]
    _ = tensAssocInv a b c ≫ (((R ⊗ₕ S) ⊗ₕ T) ≫ tensAssoc a' b' c')
          ≫ tensAssocInv a' b' c' := by simp only [Cat.assoc]
    _ = tensAssocInv a b c ≫ (tensAssoc a b c ≫ (R ⊗ₕ (S ⊗ₕ T)))
          ≫ tensAssocInv a' b' c' := by rw [hnat]
    _ = (tensAssocInv a b c ≫ tensAssoc a b c)
          ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ tensAssocInv a' b' c' := by simp only [Cat.assoc]
    _ = (R ⊗ₕ (S ⊗ₕ T)) ≫ tensAssocInv a' b' c' := by
        rw [inv_tensAssoc, Cat.id_comp]

/-- Naturality of the left unitor read in the inverse direction, `λ⁻¹_a ; (𝟙_I ⊗ R) = R ; λ⁻¹_b`.
    This is the step that pulls an arrow out to the front of a bent wire (`CartBicat.bend_unbend`). -/
theorem lunitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) = R ≫ lunitInv b := by
  calc lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R)
      = lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R)
          ≫ lunit b ≫ lunitInv b := by
        rw [lunit_inv, Cat.comp_id]
    _ = lunitInv a ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ lunit b)
          ≫ lunitInv b := by simp only [Cat.assoc]
    _ = (lunitInv a ≫ lunit a) ≫ R ≫ lunitInv b := by
        rw [lunit_nat]; simp only [Cat.assoc]
    _ = R ≫ lunitInv b := by rw [inv_lunit, Cat.id_comp]

/-- Naturality of the right unitor read in the inverse direction, `ρ⁻¹_a ; (R ⊗ 𝟙_I) = R ; ρ⁻¹_b`. -/
theorem runitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = R ≫ runitInv b := by
  calc runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ runit b ≫ runitInv b := by
        rw [runit_inv, Cat.comp_id]
    _ = runitInv a ≫ ((R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b)
          ≫ runitInv b := by simp only [Cat.assoc]
    _ = (runitInv a ≫ runit a) ≫ R ≫ runitInv b := by
        rw [runit_nat]; simp only [Cat.assoc]
    _ = R ≫ runitInv b := by rw [inv_runit, Cat.id_comp]

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
      lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ T) ≫ lunit b = T := by
    intro T
    rw [lunit_nat, ← Cat.assoc, inv_lunit, Cat.id_comp]
  calc R = lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ lunit b := (key R).symm
    _ = lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ lunit b := by rw [h]
    _ = S := key S

/-- `− ⊗ 𝟙_I` is faithful, the mirror of `tensUnit_left_faithful` via `ρ`. -/
theorem tensUnit_right_faithful {a b : 𝒞} {R S : a ⟶ b}
    (h : (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = (S ⊗ₕ 𝟙 (𝕀 : 𝒞))) : R = S := by
  have key : ∀ T : a ⟶ b,
      runitInv a ≫ (T ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b = T := by
    intro T
    rw [runit_nat, ← Cat.assoc, inv_runit, Cat.id_comp]
  calc R = runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b := (key R).symm
    _ = runitInv a ≫ (S ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b := by rw [h]
    _ = S := key S

/-- KELLY: `α_{I,a,b} ; λ_{a⊗b} = λ_a ⊗ 𝟙_b`.  Both sides, prefixed by the isomorphism
    `(α_{I,I,a} ⊗ 𝟙_b) ; α_{I,I⊗a,b}` and wrapped in `𝟙_I ⊗ −`, reduce to
    `α_{I⊗I,a,b} ; (ρ_I ⊗ 𝟙_{a⊗b})` — the first by the pentagon and the triangle at `(I, a⊗b)`,
    the second by associator naturality and the triangle at `(I, a)`. -/
theorem lunit_tens (a b : 𝒞) :
    tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b)
      = lunit a ⊗ₕ 𝟙 b := by
  refine tensUnit_left_faithful ?_
  -- The common prefix, and its inverse.
  have hPP : (tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
        ≫ (tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
      ≫ ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b) = 𝟙 _ := by
    calc (tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
          ≫ (tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
        ≫ ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        = tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ ((tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a
                  ≫ tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a) ⊗ₕ (𝟙 b ≫ 𝟙 b))
            ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b := by
          rw [tensHom_comp]; simp only [Cat.assoc]
      _ = 𝟙 _ := by
          rw [inv_tensAssoc, Cat.id_comp, tensHom_id, Cat.id_comp,
            inv_tensAssoc]
  -- Claim A: the pentagon route.
  have hA : ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
      ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b)))
      = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by
    have hsplit : (𝟙 (𝕀 : 𝒞) ⊗ₕ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b)))
        = (𝟙 (𝕀 : 𝒞) ⊗ₕ tensAssoc (𝕀 : 𝒞) a b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (a ⊗ b)) := by
      rw [← tensHom_comp, Cat.id_comp]
    rw [hsplit]
    calc ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ tensAssoc (𝕀 : 𝒞) a b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (a ⊗ b))
        = ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ tensAssoc (𝕀 : 𝒞) a b))
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (a ⊗ b)) := by simp only [Cat.assoc]
      _ = (tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (a ⊗ b))
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (a ⊗ b)) := by rw [pentagon]
      _ = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (a ⊗ b)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (a ⊗ b)) := by simp only [Cat.assoc]
      _ = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by rw [triangle]
  -- Claim B: the naturality route.
  have hB : ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
        ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
      ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b))
      = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b ≫ (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by
    calc ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
          ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
        ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b))
        = (tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b)) := by simp only [Cat.assoc]
      _ = (tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
            ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ lunit a) ⊗ₕ 𝟙 b)
            ≫ tensAssoc (𝕀 : 𝒞) a b := by rw [← tensAssoc_nat]
      _ = ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit a))
              ⊗ₕ (𝟙 b ≫ 𝟙 b))
            ≫ tensAssoc (𝕀 : 𝒞) a b := by
          rw [tensHom_comp]; simp only [Cat.assoc]
      _ = ((runit (𝕀 : 𝒞) ⊗ₕ 𝟙 a) ⊗ₕ 𝟙 b) ≫ tensAssoc (𝕀 : 𝒞) a b := by
          rw [triangle, Cat.id_comp]
      _ = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (runit (𝕀 : 𝒞) ⊗ₕ (𝟙 a ⊗ₕ 𝟙 b)) := by rw [tensAssoc_nat]
      _ = tensAssoc ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) a b
            ≫ (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (a ⊗ b)) := by rw [tensHom_id]
  -- Cancel the common prefix.
  have hAB := hA.trans hB.symm
  calc (𝟙 (𝕀 : 𝒞) ⊗ₕ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b)))
      = 𝟙 _ ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b))) :=
        (Cat.id_comp _).symm
    _ = (tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
          ≫ ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
              ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
          ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (tensAssoc (𝕀 : 𝒞) a b ≫ lunit (a ⊗ b))) := by
        rw [← hPP]; simp only [Cat.assoc]
    _ = (tensAssocInv (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b
            ≫ (tensAssocInv (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b))
          ≫ ((tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) a ⊗ₕ 𝟙 b)
              ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b)
          ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b)) := by rw [hAB]
    _ = 𝟙 _ ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b)) := by
        rw [← hPP]; simp only [Cat.assoc]
    _ = (𝟙 (𝕀 : 𝒞) ⊗ₕ (lunit a ⊗ₕ 𝟙 b)) := Cat.id_comp _

/-- KELLY, the mirror of `lunit_tens`: `α_{a,b,I} ; (𝟙_a ⊗ ρ_b) = ρ_{a⊗b}`.  Both sides, tensored
    with `𝟙_I` and followed by `α_{a,b,I}`, are the two halves of the pentagon at `(a, b, I, I)`
    post-composed with `𝟙_a ⊗ (𝟙_b ⊗ λ_I)`; the triangle at `(b, I)` closes one and the triangle
    at `(a⊗b, I)` the other. -/
theorem runit_tens (a b : 𝒞) :
    tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b) = runit (a ⊗ b) := by
  refine tensUnit_right_faithful ?_
  -- Claim A: the pentagon's left-hand side, closed by the triangle at `(b, I)`.
  have hA : ((tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
        ≫ tensAssoc a b (𝕀 : 𝒞)
      = ((tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
          ≫ (𝟙 a ⊗ₕ tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)))
        ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by
    calc ((tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ tensAssoc a b (𝕀 : 𝒞)
        = ((tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ ((𝟙 a ⊗ₕ runit b) ⊗ₕ 𝟙 (𝕀 : 𝒞)))
            ≫ tensAssoc a b (𝕀 : 𝒞) := by
          rw [← tensHom_comp, Cat.comp_id]
      _ = (tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ ((𝟙 a ⊗ₕ runit b) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ tensAssoc a b (𝕀 : 𝒞) := by simp only [Cat.assoc]
      _ = (tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ (runit b ⊗ₕ 𝟙 (𝕀 : 𝒞))) := by rw [tensAssoc_nat]
      _ = (tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ (tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)
                ≫ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞)))) := by rw [triangle]
      _ = ((tensAssoc a b (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
            ≫ tensAssoc a (b ⊗ (𝕀 : 𝒞)) (𝕀 : 𝒞)
            ≫ (𝟙 a ⊗ₕ tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by
          have hs : (𝟙 a ⊗ₕ (tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞)
                ≫ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))))
              = (𝟙 a ⊗ₕ tensAssoc b (𝕀 : 𝒞) (𝕀 : 𝒞))
                  ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by
            rw [← tensHom_comp, Cat.id_comp]
          rw [hs]; simp only [Cat.assoc]
  -- Claim B: the pentagon's right-hand side, closed by the triangle at `(a⊗b, I)`.
  have hB : (runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ tensAssoc a b (𝕀 : 𝒞)
      = (tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞) ≫ tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)))
        ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by
    calc (runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ tensAssoc a b (𝕀 : 𝒞)
        = (tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (a ⊗ b) ⊗ₕ lunit (𝕀 : 𝒞)))
            ≫ tensAssoc a b (𝕀 : 𝒞) := by rw [triangle]
      _ = tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ ((𝟙 a ⊗ₕ 𝟙 b) ⊗ₕ lunit (𝕀 : 𝒞))
            ≫ tensAssoc a b (𝕀 : 𝒞) := by
          rw [tensHom_id]; simp only [Cat.assoc]
      _ = tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by rw [tensAssoc_nat]
      _ = (tensAssoc (a ⊗ b) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ tensAssoc a b ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)))
            ≫ (𝟙 a ⊗ₕ (𝟙 b ⊗ₕ lunit (𝕀 : 𝒞))) := by simp only [Cat.assoc]
  -- The two prefixes agree by the pentagon, so the two `⊗ 𝟙_I`s agree once `α` is cancelled.
  have hcancel : ((tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
        ≫ tensAssoc a b (𝕀 : 𝒞)
      = (runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ tensAssoc a b (𝕀 : 𝒞) := by
    rw [hA, hB, pentagon]
  calc ((tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = (((tensAssoc a b (𝕀 : 𝒞) ≫ (𝟙 a ⊗ₕ runit b)) ⊗ₕ 𝟙 (𝕀 : 𝒞))
          ≫ tensAssoc a b (𝕀 : 𝒞)) ≫ tensAssocInv a b (𝕀 : 𝒞) := by
        rw [Cat.assoc, tensAssoc_inv, Cat.comp_id]
    _ = ((runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ tensAssoc a b (𝕀 : 𝒞))
          ≫ tensAssocInv a b (𝕀 : 𝒞) := by rw [hcancel]
    _ = (runit (a ⊗ b) ⊗ₕ 𝟙 (𝕀 : 𝒞)) := by
        rw [Cat.assoc, tensAssoc_inv, Cat.comp_id]

/-- KELLY: `λ_I = ρ_I`, Mac Lane's third redundant axiom.  Both `λ_I ⊗ 𝟙_I` and `ρ_I ⊗ 𝟙_I`,
    followed by `λ_I`, equal `α_{I,I,I} ; (𝟙_I ⊗ λ_I) ; λ_I` — the first by `lunit_tens` plus
    naturality of `λ`, the second by the triangle at `(I, I)`. -/
theorem lunit_unit : lunit (𝕀 : 𝒞) = runit (𝕀 : 𝒞) := by
  refine tensUnit_right_faithful ?_
  have hkey : (lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞)
      = (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞) := by
    calc (lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞)
        = (tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ lunit ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞))) ≫ lunit (𝕀 : 𝒞) := by
          rw [lunit_tens]
      _ = tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ lunit ((𝕀 : 𝒞) ⊗ (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞) := by
          simp only [Cat.assoc]
      _ = tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞) := by
          rw [lunit_nat]
      _ = (tensAssoc (𝕀 : 𝒞) (𝕀 : 𝒞) (𝕀 : 𝒞)
            ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ lunit (𝕀 : 𝒞))) ≫ lunit (𝕀 : 𝒞) := by
          simp only [Cat.assoc]
      _ = (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞) := by
          rw [triangle]
  calc (lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = ((lunit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞))
          ≫ lunitInv (𝕀 : 𝒞) := by
        rw [Cat.assoc, lunit_inv, Cat.comp_id]
    _ = ((runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ lunit (𝕀 : 𝒞))
          ≫ lunitInv (𝕀 : 𝒞) := by rw [hkey]
    _ = (runit (𝕀 : 𝒞) ⊗ₕ 𝟙 (𝕀 : 𝒞)) := by
        rw [Cat.assoc, lunit_inv, Cat.comp_id]

end Freyd.Diag
