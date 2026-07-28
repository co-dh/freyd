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

/-! ### The bookkeeping, done by `simp` instead of by hand

  This layer is non-strict and has to be (see the file header), so `α`, `λ`, `ρ` are real arrows and
  a proof that a string diagram would draw as ONE picture is, in Lean, a chain of re-bracketings.
  Those steps carry no content — the coherence theorem is exactly the statement that they are
  forced — so they belong in a tactic, not in the source of every proof.

  The normal form `coherence` drives at: `≫` right-nested; identities dropped; neighbouring tensors
  merged into one, so `(R ⊗ₕ 𝟙) ≫ (𝟙 ⊗ₕ S)` becomes `R ⊗ₕ S` without being told; a coherence iso
  met by its inverse cancelled.

  It is NOT a decision procedure for coherence: it does not know the pentagon.  It cancels what is
  adjacent after normalisation, which is what the proofs in this tower need; a goal that genuinely
  needs the pentagon still cites `pentagon`. -/

/-- Two tensors in a row are one tensor, stated with the rest of the composite spelled out so that
    it matches inside a chain of any length: `(R ⊗ S) ; (R' ⊗ S') ; f = ((R ; R') ⊗ (S ; S')) ; f`.
    The tail is the whole point — in the normal form the two tensors are never adjacent at the top,
    the composite reads `(R ⊗ S) ; ((R' ⊗ S') ; f)`, which `tensHom_comp` cannot match. -/
theorem tensHom_merge {a a' a'' b b' b'' d : 𝒞} (R : a ⟶ a') (R' : a' ⟶ a'') (S : b ⟶ b')
    (S' : b' ⟶ b'') (f : a'' ⊗ b'' ⟶ d) :
    (R ⊗ₕ S) ≫ (R' ⊗ₕ S') ≫ f = ((R ≫ R') ⊗ₕ (S ≫ S')) ≫ f := by
  rw [← Cat.assoc, ← tensHom_comp]

/-- `α ; α⁻¹ ; f = f` — `tensAssoc_inv` with the tail, for the same reason as `tensHom_merge`. -/
theorem tensAssoc_cancel {a b c d : 𝒞} (f : (a ⊗ b) ⊗ c ⟶ d) :
    tensAssoc a b c ≫ tensAssocInv a b c ≫ f = f := by
  rw [← Cat.assoc, tensAssoc_inv, Cat.id_comp]

/-- `α⁻¹ ; α ; f = f`. -/
theorem tensAssocInv_cancel {a b c d : 𝒞} (f : a ⊗ (b ⊗ c) ⟶ d) :
    tensAssocInv a b c ≫ tensAssoc a b c ≫ f = f := by
  rw [← Cat.assoc, inv_tensAssoc, Cat.id_comp]

/-- `λ ; λ⁻¹ ; f = f`. -/
theorem lunit_cancel {a d : 𝒞} (f : (𝕀 : 𝒞) ⊗ a ⟶ d) : lunit a ≫ lunitInv a ≫ f = f := by
  rw [← Cat.assoc, lunit_inv, Cat.id_comp]

/-- `λ⁻¹ ; λ ; f = f`. -/
theorem lunitInv_cancel {a d : 𝒞} (f : a ⟶ d) : lunitInv a ≫ lunit a ≫ f = f := by
  rw [← Cat.assoc, inv_lunit, Cat.id_comp]

/-- `ρ ; ρ⁻¹ ; f = f`. -/
theorem runit_cancel {a d : 𝒞} (f : a ⊗ (𝕀 : 𝒞) ⟶ d) : runit a ≫ runitInv a ≫ f = f := by
  rw [← Cat.assoc, runit_inv, Cat.id_comp]

/-- `ρ⁻¹ ; ρ ; f = f`. -/
theorem runitInv_cancel {a d : 𝒞} (f : a ⟶ d) : runitInv a ≫ runit a ≫ f = f := by
  rw [← Cat.assoc, inv_runit, Cat.id_comp]

/-- `γ ; γ ; f = f`: the symmetry is its own inverse. -/
theorem swap_cancel {a b d : 𝒞} (f : a ⊗ b ⟶ d) : swap a b ≫ swap b a ≫ f = f := by
  rw [← Cat.assoc, swap_swap, Cat.id_comp]

/-! The four naturality laws, each with the rest of the composite spelled out.  Same reason as
    `tensHom_merge`: in the normal form the pair the law names is never adjacent at the top, so the
    law as stated cannot fire.  These are what let a proof push a coherence iso past an arrow
    without first re-bracketing by hand — hand them to `coherence [...]`. -/

/-- `α ; (R ⊗ (S ⊗ T)) ; f`, reached from `((R ⊗ S) ⊗ T) ; α ; f`. -/
theorem tensAssoc_nat_tail {a a' b b' c c' d : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c')
    (f : a' ⊗ (b' ⊗ c') ⟶ d) :
    ((R ⊗ₕ S) ⊗ₕ T) ≫ tensAssoc a' b' c' ≫ f = tensAssoc a b c ≫ (R ⊗ₕ (S ⊗ₕ T)) ≫ f := by
  rw [← Cat.assoc, tensAssoc_nat, Cat.assoc]

/-- `λ` past an arrow: `(𝟙_I ⊗ R) ; λ ; f = λ ; R ; f`. -/
theorem lunit_nat_tail {a b d : 𝒞} (R : a ⟶ b) (f : b ⟶ d) :
    (𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ lunit b ≫ f = lunit a ≫ R ≫ f := by
  rw [← Cat.assoc, lunit_nat, Cat.assoc]

/-- `ρ` past an arrow: `(R ⊗ 𝟙_I) ; ρ ; f = ρ ; R ; f`. -/
theorem runit_nat_tail {a b d : 𝒞} (R : a ⟶ b) (f : b ⟶ d) :
    (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b ≫ f = runit a ≫ R ≫ f := by
  rw [← Cat.assoc, runit_nat, Cat.assoc]

/-- `γ` past a tensor: `(R ⊗ S) ; γ ; f = γ ; (S ⊗ R) ; f`. -/
theorem swap_nat_tail {a a' b b' d : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (f : b' ⊗ a' ⟶ d) :
    (R ⊗ₕ S) ≫ swap a' b' ≫ f = swap a b ≫ (S ⊗ₕ R) ≫ f := by
  rw [← Cat.assoc, swap_nat, Cat.assoc]

/-- Normalise a composite: right-nest `≫`, drop identities, merge neighbouring tensors, cancel a
    coherence iso against its inverse.  `coherence [h, ...]` puts `h, ...` in the same `simp only`,
    for the step where one content-carrying rewrite has to happen amid the bookkeeping — the
    `*_nat_tail` laws above are the usual arguments. -/
syntax "coherence" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| coherence $[[$extra,*]]?) => do
    let extra := extra.getD ⟨#[]⟩
    `(tactic| simp only [Cat.assoc, Cat.id_comp, Cat.comp_id, tensHom_id, ← tensHom_comp,
        tensHom_merge, tensAssoc_inv, inv_tensAssoc, tensAssoc_cancel, tensAssocInv_cancel,
        lunit_inv, inv_lunit, lunit_cancel, lunitInv_cancel, runit_inv, inv_runit, runit_cancel,
        runitInv_cancel, swap_swap, swap_cancel, $extra,*])

/-- The inverse form of `swap_lunit`: `λ⁻¹_a ; γ_{I,a} = ρ⁻¹_a`. -/
theorem lunitInv_swap (a : 𝒞) :
    lunitInv a ≫ swap (𝕀 : 𝒞) a = runitInv a := by
  have hround : (lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ runit a = 𝟙 a := by
    rw [← swap_lunit]; coherence
  calc lunitInv a ≫ swap (𝕀 : 𝒞) a
      = ((lunitInv a ≫ swap (𝕀 : 𝒞) a) ≫ runit a) ≫ runitInv a := by coherence
    _ = runitInv a := by rw [hround, Cat.id_comp]

/-- `λ⁻¹ ; γ ; f = ρ⁻¹ ; f`, the tail form of `lunitInv_swap` — what lets `coherence` bend a wire
    from the left unit to the right one in the middle of a composite. -/
theorem lunitInv_swap_tail {a d : 𝒞} (f : a ⊗ (𝕀 : 𝒞) ⟶ d) :
    lunitInv a ≫ swap (𝕀 : 𝒞) a ≫ f = runitInv a ≫ f := by
  rw [← Cat.assoc, lunitInv_swap]

/-- Naturality of the associator read in the inverse direction — obtained by conjugating
    `tensAssoc_nat` with `tensAssoc_inv`/`inv_tensAssoc`.  Needed whenever a proof pushes a
    re-bracketing past a product of arrows rather than pulling it. -/
theorem tensAssocInv_nat {a a' b b' c c' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = (R ⊗ₕ (S ⊗ₕ T)) ≫ tensAssocInv a' b' c' := by
  calc tensAssocInv a b c ≫ ((R ⊗ₕ S) ⊗ₕ T)
      = tensAssocInv a b c ≫ (((R ⊗ₕ S) ⊗ₕ T) ≫ tensAssoc a' b' c')
          ≫ tensAssocInv a' b' c' := by coherence
    _ = tensAssocInv a b c ≫ (tensAssoc a b c ≫ (R ⊗ₕ (S ⊗ₕ T)))
          ≫ tensAssocInv a' b' c' := by rw [tensAssoc_nat]
    _ = (R ⊗ₕ (S ⊗ₕ T)) ≫ tensAssocInv a' b' c' := by coherence

/-- Naturality of the left unitor read in the inverse direction, `λ⁻¹_a ; (𝟙_I ⊗ R) = R ; λ⁻¹_b`.
    This is the step that pulls an arrow out to the front of a bent wire (`CartBicat.bend_unbend`). -/
theorem lunitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) = R ≫ lunitInv b := by
  calc lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R)
      = lunitInv a ≫ ((𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ lunit b) ≫ lunitInv b := by coherence
    _ = R ≫ lunitInv b := by coherence [lunit_nat]

/-- Naturality of the right unitor read in the inverse direction, `ρ⁻¹_a ; (R ⊗ 𝟙_I) = R ; ρ⁻¹_b`. -/
theorem runitInv_nat {a b : 𝒞} (R : a ⟶ b) :
    runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = R ≫ runitInv b := by
  calc runitInv a ≫ (R ⊗ₕ 𝟙 (𝕀 : 𝒞))
      = runitInv a ≫ ((R ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b) ≫ runitInv b := by coherence
    _ = R ≫ runitInv b := by coherence [runit_nat]

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
  have key : ∀ T : a ⟶ b, lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ T) ≫ lunit b = T := fun _ => by
    coherence [lunit_nat]
  calc R = lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ R) ≫ lunit b := (key R).symm
    _ = lunitInv a ≫ (𝟙 (𝕀 : 𝒞) ⊗ₕ S) ≫ lunit b := by rw [h]
    _ = S := key S

/-- `− ⊗ 𝟙_I` is faithful, the mirror of `tensUnit_left_faithful` via `ρ`. -/
theorem tensUnit_right_faithful {a b : 𝒞} {R S : a ⟶ b}
    (h : (R ⊗ₕ 𝟙 (𝕀 : 𝒞)) = (S ⊗ₕ 𝟙 (𝕀 : 𝒞))) : R = S := by
  have key : ∀ T : a ⟶ b, runitInv a ≫ (T ⊗ₕ 𝟙 (𝕀 : 𝒞)) ≫ runit b = T := fun _ => by
    coherence [runit_nat]
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
        ≫ tensAssoc (𝕀 : 𝒞) ((𝕀 : 𝒞) ⊗ a) b) = 𝟙 _ := by coherence
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
