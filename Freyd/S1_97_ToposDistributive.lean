/-
  Freyd & Scedrov, *Categories and Allegories* — Cartesian-closed DISTRIBUTIVITY layer.

  In a category with binary products in which `A × −` has a right adjoint (an
  EXPONENTIAL category, `HasExponentials`), the functor `A × −` is a LEFT ADJOINT,
  hence preserves colimits.  In particular it preserves binary coproducts and
  arbitrary copowers:

      A × (B + C)  ≅  (A × B) + (A × C)          `prod_distrib_coprod`
      A × (∐_I 1)  ≅  ∐_I A      (copower)        `prod_distrib_copow`

  The proof is the classic adjunction argument made fully constructive: a cocone
  out of `A × (B+C)` corresponds — under the curry/uncurry bijection
  `Hom(A×X, Y) ≅ Hom(X, Y^A)` — to a cocone out of `B+C`, whose universal map is
  obtained from the coproduct UMP and transported back by `uncurry`.

  Axiom profile: every lemma below is `#print axioms`-clean (depends on NO axioms).
  It is a generic `HasExponentials` + `HasBinaryCoproducts` result; the topos axioms
  (`Classical.choice` etc.) enter only downstream when those instances are supplied
  by a concrete topos (`topos_has_exponentials`).
-/

module

public import Freyd.S1_42
public import Freyd.S1_58
public import Freyd.S1_85

universe w v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

open HasBinaryCoproducts

/-! ## The curry/uncurry adjunction bijection `Hom(A×X, Y) ≅ Hom(X, Y^A)`

  `HasExponentials` already supplies `curry : (A×X ⟶ Y) → (X ⟶ Y^A)` together with
  `curry_eval_eq` (β-rule) and `curry_unique_eq` (η/uniqueness).  We package the
  inverse `uncurry` and the two round-trip identities, then derive the single fact
  the distributivity proofs need: precomposition naturality of `uncurry`. -/

section Adjunction

variable [HasExponentials 𝒞]

-- The inverse transpose `k : X ⟶ Y^A ↦ (A × k) ≫ eval` is `transp`, in `Freyd.S1_85` beside
-- `curry`; this file's `uncurry` was the same definition under a second name.  The `uncurry_*`
-- lemmas below are stated about `transp` and keep their names.

/-- `curry` then `transp` is the identity (β-rule, restated). -/
@[simp] public theorem uncurry_curry {A Y X : 𝒞} (f : prod A X ⟶ Y) :
    transp (curry f) = f := by
  unfold transp; exact curry_eval_eq f

/-- `transp` then `curry` is the identity (uniqueness). -/
@[simp] public theorem curry_uncurry {A Y X : 𝒞} (k : X ⟶ Y ^^ A) :
    curry (transp k) = k :=
  (curry_unique_eq (f := transp k) (g := k) rfl).symm

-- Naturality of `transp` in `X` on the left (`transp (u ≫ k) = (A × u) ≫ transp k`) is
-- `transp_precomp`, in `Freyd.S1_85`.


end Adjunction

/-! ## §1.957(binary)  `A × (B+C) ≅ (A×B) + (A×C)`

  We first show the object `A × (B+C)` with injections `A × inl`, `A × inr`
  satisfies the coproduct universal property, then transport the iso to the
  ambient `coprod (A×B) (A×C)`. -/

section BinaryDistrib

variable [HasExponentials 𝒞] [HasBinaryCoproducts 𝒞]

/-- The left injection of the distributed coproduct: `A × inl : A×B → A×(B+C)`. -/
@[expose] public def distInl (A B C : 𝒞) : prod A B ⟶ prod A (coprod B C) :=
  prodMap A B (coprod B C) inl

/-- The right injection: `A × inr : A×C → A×(B+C)`. -/
@[expose] public def distInr (A B C : 𝒞) : prod A C ⟶ prod A (coprod B C) :=
  prodMap A C (coprod B C) inr

/-- The copairing out of `A×(B+C)`: given `f : A×B ⟶ X` and `g : A×C ⟶ X`,
    transpose to `B ⟶ X^A`, `C ⟶ X^A`, copair, then transpose back. -/
@[expose] public def distCase {A B C X : 𝒞} (f : prod A B ⟶ X) (g : prod A C ⟶ X) :
    prod A (coprod B C) ⟶ X :=
  transp (case (curry f) (curry g))

public theorem distCase_inl {A B C X : 𝒞} (f : prod A B ⟶ X) (g : prod A C ⟶ X) :
    distInl A B C ≫ distCase f g = f := by
  unfold distInl distCase
  rw [← transp_precomp, case_inl, uncurry_curry]

public theorem distCase_inr {A B C X : 𝒞} (f : prod A B ⟶ X) (g : prod A C ⟶ X) :
    distInr A B C ≫ distCase f g = g := by
  unfold distInr distCase
  rw [← transp_precomp, case_inr, uncurry_curry]

public theorem distCase_uniq {A B C X : 𝒞} (f : prod A B ⟶ X) (g : prod A C ⟶ X)
    (h : prod A (coprod B C) ⟶ X)
    (h₁ : distInl A B C ≫ h = f) (h₂ : distInr A B C ≫ h = g) :
    h = distCase f g := by
  -- Transpose h to `curry h : (B+C) ⟶ X^A` and use coproduct uniqueness.
  unfold distCase
  -- Suffices `curry h = case (curry f) (curry g)` then apply `uncurry` and `uncurry_curry`.
  have key : curry h = case (curry f) (curry g) := by
    apply case_uniq
    · -- inl ≫ curry h = curry (distInl ≫ h) = curry f
      rw [curry_precomp]
      have : prodMap A B (coprod B C) inl ≫ h = f := h₁
      rw [this]
    · rw [curry_precomp]
      have : prodMap A C (coprod B C) inr ≫ h = g := h₂
      rw [this]
  calc h = transp (curry h) := (uncurry_curry h).symm
    _ = transp (case (curry f) (curry g)) := by rw [key]

/-- The canonical comparison map `(A×B) + (A×C) → A×(B+C)`, the copairing of the
    two distributed injections. -/
def distrib_fwd (A B C : 𝒞) : coprod (prod A B) (prod A C) ⟶ prod A (coprod B C) :=
  case (distInl A B C) (distInr A B C)

/-- The inverse `A×(B+C) → (A×B) + (A×C)`, the copairing (via the new UMP) of the
    coproduct's own injections `inl : A×B → (A×B)+(A×C)`, `inr : A×C → (A×B)+(A×C)`. -/
def distrib_inv (A B C : 𝒞) : prod A (coprod B C) ⟶ coprod (prod A B) (prod A C) :=
  distCase inl inr

theorem distrib_fwd_inv (A B C : 𝒞) :
    distrib_fwd A B C ≫ distrib_inv A B C = Cat.id _ := by
  -- On `coprod (A×B) (A×C)` check both injections via `case_uniq`.
  have h₁ : inl ≫ (distrib_fwd A B C ≫ distrib_inv A B C) = inl := by
    rw [← Cat.assoc]; unfold distrib_fwd; rw [case_inl]; unfold distrib_inv; rw [distCase_inl]
  have h₂ : inr ≫ (distrib_fwd A B C ≫ distrib_inv A B C) = inr := by
    rw [← Cat.assoc]; unfold distrib_fwd; rw [case_inr]; unfold distrib_inv; rw [distCase_inr]
  have e1 := case_uniq (X := coprod (prod A B) (prod A C)) inl inr
    (distrib_fwd A B C ≫ distrib_inv A B C) h₁ h₂
  have e2 := case_uniq (X := coprod (prod A B) (prod A C)) inl inr
    (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)
  exact e1.trans e2.symm

theorem distrib_inv_fwd (A B C : 𝒞) :
    distrib_inv A B C ≫ distrib_fwd A B C = Cat.id _ := by
  -- On `A×(B+C)` use the new UMP uniqueness (`distCase_uniq`).
  have h₁ : distInl A B C ≫ (distrib_inv A B C ≫ distrib_fwd A B C) = distInl A B C := by
    rw [← Cat.assoc]; unfold distrib_inv; rw [distCase_inl]
    unfold distrib_fwd; rw [case_inl]
  have h₂ : distInr A B C ≫ (distrib_inv A B C ≫ distrib_fwd A B C) = distInr A B C := by
    rw [← Cat.assoc]; unfold distrib_inv; rw [distCase_inr]
    unfold distrib_fwd; rw [case_inr]
  have e1 := distCase_uniq (distInl A B C) (distInr A B C)
    (distrib_inv A B C ≫ distrib_fwd A B C) h₁ h₂
  -- identity also satisfies the UMP
  have hid₁ : distInl A B C ≫ Cat.id (prod A (coprod B C)) = distInl A B C := Cat.comp_id _
  have hid₂ : distInr A B C ≫ Cat.id (prod A (coprod B C)) = distInr A B C := Cat.comp_id _
  have e2 := distCase_uniq (distInl A B C) (distInr A B C)
    (Cat.id (prod A (coprod B C))) hid₁ hid₂
  exact e1.trans e2.symm

/-- **Distributivity (binary)**: in an exponential category with binary coproducts,
    `(A×B) + (A×C) ≅ A×(B+C)`, witnessed by `distrib_fwd` (copairing of `A×inl`,
    `A×inr`).  This is the statement that `A × −` preserves the binary coproduct. -/
theorem prod_distrib_coprod (A B C : 𝒞) : IsIso (distrib_fwd A B C) :=
  ⟨distrib_inv A B C, distrib_fwd_inv A B C, distrib_inv_fwd A B C⟩

end BinaryDistrib

/-! ## §1.967  Infinitary distributivity  `A × ∐_I 1 ≅ ∐_I A`

  The same adjunction argument, now over an arbitrary copower.  A *genuine* copower
  of `1` (object `cI`, injections `u i : 1 ⟶ cI`, with cotupling AND its uniqueness)
  yields a genuine copower of `A` on the object `A × cI`.

  We bundle the copower data as structures (mirroring the fields of
  `HasArbitraryCopowers` but for a single index type) so the construction is reusable
  by §1.967.  The injection of the copower of `A` is `⟨id_A, term_A ≫ u i⟩ : A ⟶ A×cI`. -/

section InfDistrib

variable [HasExponentials 𝒞] [HasTerminal 𝒞]

/-- A genuine `I`-fold copower of the terminal object `1`: object `obj`, injections
    `inj i : 1 ⟶ obj`, cotupling for every target, and uniqueness of cotupling. -/
public structure CopowerOfOne (I : Type w) (𝒞 : Type u) [Cat.{v} 𝒞] [HasTerminal 𝒞] where
  obj : 𝒞
  inj : I → (one ⟶ obj)
  cotup : {X : 𝒞} → (I → one ⟶ X) → (obj ⟶ X)
  inj_cotup : ∀ {X : 𝒞} (f : I → one ⟶ X) (i : I), inj i ≫ cotup f = f i
  cotup_uniq : ∀ {X : 𝒞} (f : I → one ⟶ X) (h : obj ⟶ X),
    (∀ i, inj i ≫ h = f i) → h = cotup f

/-- A genuine `I`-fold copower of an object `A`. -/
public structure CopowerOf (I : Type w) (A : 𝒞) where
  obj : 𝒞
  inj : I → (A ⟶ obj)
  cotup : {X : 𝒞} → (I → A ⟶ X) → (obj ⟶ X)
  inj_cotup : ∀ {X : 𝒞} (f : I → A ⟶ X) (i : I), inj i ≫ cotup f = f i
  cotup_uniq : ∀ {X : 𝒞} (f : I → A ⟶ X) (h : obj ⟶ X),
    (∀ i, inj i ≫ h = f i) → h = cotup f

/-- The copower-of-`A` injection built from a copower-of-`1`:
    `⟨id_A, term_A ≫ u i⟩ : A ⟶ A × cI`. -/
@[expose] public def copInj {I : Type w} (P : CopowerOfOne I 𝒞) (A : 𝒞) (i : I) : A ⟶ prod A P.obj :=
  pair (Cat.id A) (term A ≫ P.inj i)

/-- `copInj` factors as `prodOneRightInv ≫ (A × inj i)` — the bridge to `transp_precomp`. -/
public theorem copInj_factor {I : Type w} (P : CopowerOfOne I 𝒞) (A : 𝒞) (i : I) :
    copInj P A i = prodOneRightInv A ≫ prodMap A one P.obj (P.inj i) := by
  unfold copInj
  refine (pair_uniq (Cat.id A) (term A ≫ P.inj i) _ ?_ ?_).symm
  · -- (prodOneRightInv ≫ prodMap) ≫ fst = id
    rw [Cat.assoc, prodMap_fst, show prodOneRightInv A ≫ fst = Cat.id A from fst_pair _ _]
  · -- (prodOneRightInv ≫ prodMap) ≫ snd = term ≫ inj i
    rw [Cat.assoc, prodMap_snd, ← Cat.assoc]
    unfold prodOneRightInv
    rw [snd_pair]

/-- **Infinitary distributivity**: `A × cI` is a genuine `I`-fold copower of `A`,
    where `cI` is a genuine `I`-fold copower of `1`.  This is `A × ∐_I 1 ≅ ∐_I A`,
    i.e. `A × −` preserves the copower. -/
@[expose] public noncomputable def prod_distrib_copow {I : Type w} (P : CopowerOfOne I 𝒞) (A : 𝒞) :
    CopowerOf I A where
  obj := prod A P.obj
  inj i := copInj P A i
  cotup {X} g :=
    -- transpose family g i : A ⟶ X to one ⟶ X^A, copower-of-1 cotuple, untranspose
    transp (P.cotup (fun i => curry (fst ≫ g i)))
  inj_cotup {X} g i := by
    -- copInj i ≫ uncurry(cotup f) = prodOneRightInv ≫ uncurry (inj i ≫ cotup f)
    rw [copInj_factor, Cat.assoc, ← transp_precomp, P.inj_cotup,
        uncurry_curry, ← Cat.assoc, show prodOneRightInv A ≫ fst = Cat.id A from fst_pair _ _,
        Cat.id_comp]
  cotup_uniq {X} g h hh := by
    -- transpose h to curry h : cI ⟶ X^A; show it equals the copower-of-1 cotuple,
    -- then untranspose by uniqueness of curry.
    have key : curry h = P.cotup (fun i => curry (fst ≫ g i)) := by
      apply P.cotup_uniq
      intro i
      -- inj i ≫ curry h = curry (fst ≫ g i)
      rw [curry_precomp]
      -- curry (prodMap A one cI (inj i) ≫ h) = curry (fst ≫ g i)
      congr 1
      -- prodMap A one cI (inj i) ≫ h = fst ≫ g i
      -- precompose by iso prodOneRightInv to compare with copInj i ≫ h = g i
      have e : prodOneRightInv A ≫ (prodMap A one P.obj (P.inj i) ≫ h) = g i := by
        rw [← Cat.assoc, ← copInj_factor]; exact hh i
      -- prodOneRightInv ≫ fst = id, and fst is iso with inverse prodOneRightInv (S1_42)
      have hfst : (fst : prod A one ⟶ A) ≫ prodOneRightInv A = Cat.id (prod A one) :=
        fst_prodOneRightInv
      calc prodMap A one P.obj (P.inj i) ≫ h
          = (fst ≫ prodOneRightInv A) ≫ (prodMap A one P.obj (P.inj i) ≫ h) := by
            rw [hfst, Cat.id_comp]
        _ = fst ≫ (prodOneRightInv A ≫ (prodMap A one P.obj (P.inj i) ≫ h)) := by
            rw [Cat.assoc]
        _ = fst ≫ g i := by rw [e]
    calc h = transp (curry h) := (uncurry_curry h).symm
      _ = transp (P.cotup (fun i => curry (fst ≫ g i))) := by rw [key]

end InfDistrib

end Freyd
