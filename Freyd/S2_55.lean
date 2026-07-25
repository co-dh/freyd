import Freyd.S2_05
import Freyd.S2_22

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.55

  AN AMENABLE QUOTIENT OF A LOCALLY (resp. GLOBALLY) COMPLETE ALLEGORY IS
  LOCALLY (resp. GLOBALLY) COMPLETE.

  Book's proof.  Writing `R⁺` for `largest R` (the biggest element of `R`'s
  congruence class):

      (∪ᵢRᵢ)⁺ ⊑ (∪ᵢRᵢ⁺)⁺  and  Rⱼ⁺ ⊑ (∪ᵢRᵢ)⁺  for each j   [by 2.531],

  so `∪ᵢRᵢ⁺ ⊑ (∪ᵢRᵢ)⁺`; thus `(∪ᵢRᵢ⁺)⁺ ⊑ (∪ᵢRᵢ)⁺⁺ = (∪ᵢRᵢ)⁺ ⊑ (∪ᵢRᵢ⁺)⁺`, giving
  `(∪ᵢRᵢ)⁺ = (∪ᵢRᵢ⁺)⁺`.  Hence if `Sᵢ ≡ Tᵢ` for each `i` then `(∪ᵢSᵢ) ≡ (∪ᵢTᵢ)`:
  arbitrary `Sup` respects the congruence, so it descends to the quotient.

  Here we carry that argument over to the predicate-based `Sup` of
  `LocallyCompleteDistributiveAllegory` (§2.22).  The quotient `Sup` of a
  predicate `P` on congruence classes is the class of the base `Sup` taken over
  the representatives whose class satisfies `P`:

      Sup P  :=  [ Sup (fun r => P [r]) ].

  Because the base predicate `fun r => P [r]` is *determined* by `P`, the
  definition is automatically single-valued; the content of §2.55 is that this
  `Sup` is genuinely a supremum for the quotient order and that composition /
  intersection still distribute over it.  Both reduce to the one fact
  `largest (largest X) = largest X` together with §2.531 (`amenable_le_largest`)
  and §2.532 (`amenable_inter_largest`).

  Instances pin the *base* `LocallyCompleteDistributiveAllegory 𝒜` explicitly
  with `@ … 𝒜 _` so the elaborator never tries to synthesise the quotient
  instance that is still under construction.
-/



namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

/-! ## §2.53  Largest-element calculus used by §2.55 -/

section LargestCalculus

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- If two morphisms have the same largest element they are congruent
    (`R⁺ = S⁺ → R ≡ S`).  The converse of `amenable_largest_class_invariant`. -/
theorem rel_of_largest_eq (amen : AmenableCongruence 𝒜) {a b : 𝒜} {X Y : a ⟶ b}
    (h : amen.largest X = amen.largest Y) : amen.cong.rel X Y := by
  have h1 : amen.cong.rel X (amen.largest X) := amen.largest_rel X
  have h2 : amen.cong.rel (amen.largest Y) Y := amen.cong.symm (amen.largest_rel Y)
  rw [h] at h1
  exact amen.cong.trans h1 h2



end LargestCalculus

/-! ## §2.55  The quotient supremum and its order properties -/

section QuotSup

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- §2.533 in `Sup` form: in the quotient, `[X] ⊑ [Y] ↔ X⁺ ⊑ Y⁺`.  Forward uses
    `amenable_largest_class_invariant` + §2.532; backward §2.532 + `rel_of_largest_eq`. -/
theorem quot_le_iff_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (X Y : a ⟶ b) :
    (@le (QuotAllegory 𝒜 amen.cong) a b (QuotAllegory.instAllegory amen.cong)
        (Quotient.mk (congSetoid amen.cong) X) (Quotient.mk (congSetoid amen.cong) Y))
      ↔ amen.largest X ⊑ amen.largest Y := by
  -- The quotient order `[X] ⊑ [Y]` is `[X ∩ Y] = [X]`, i.e. `X ∩ Y ≡ X`.
  have hbridge :
      (@le (QuotAllegory 𝒜 amen.cong) a b (QuotAllegory.instAllegory amen.cong)
          (Quotient.mk (congSetoid amen.cong) X) (Quotient.mk (congSetoid amen.cong) Y))
        ↔ amen.cong.rel (X ∩ Y) X := by
    constructor
    · intro hle
      have hle' : (Quotient.mk (congSetoid amen.cong) (X ∩ Y))
          = Quotient.mk (congSetoid amen.cong) X := hle
      exact Quotient.exact hle'
    · intro hr
      exact Quotient.sound hr
  rw [hbridge]
  constructor
  · intro hr
    have hci : amen.largest (X ∩ Y) = amen.largest X := amenable_largest_class_invariant amen hr
    have hil : amen.largest (X ∩ Y) = amen.largest X ∩ amen.largest Y :=
      amenable_inter_largest amen X Y
    show amen.largest X ∩ amen.largest Y = amen.largest X
    rw [← hil, hci]
  · intro hle
    have hil : amen.largest (X ∩ Y) = amen.largest X ∩ amen.largest Y :=
      amenable_inter_largest amen X Y
    have heq : amen.largest X ∩ amen.largest Y = amen.largest X := hle
    rw [heq] at hil
    exact rel_of_largest_eq amen hil

/-- The crux of §2.55.  Two base predicates `P₁ ⊆ P₂` whose `P₂`-elements are each
    congruent to a `P₁`-element have congruent suprema: `Sup P₁ ≡ Sup P₂`.

    This is exactly the book's `(∪ᵢRᵢ)⁺ = (∪ᵢRᵢ⁺)⁺` packaged for arbitrary
    `Sup`: `P₁` plays the role of `∪ᵢRᵢ`, `P₂` of the congruence-saturated family.
    Proof: `Sup P₁ ⊑ (Sup P₂)⁺` and `Sup P₂ ⊑ (Sup P₁)⁺` (base `Sup_le`,
    `self_le_largest`, class-invariance), then §2.531 + idempotence collapse `⁺`. -/
theorem quotSup_distrib_rel (amen : AmenableCongruence 𝒜) {a b : 𝒜}
    (P₁ P₂ : (a ⟶ b) → Prop)
    (hsat : ∀ x, P₂ x → ∃ y, P₁ y ∧ amen.cong.rel x y)
    (hsub : ∀ x, P₁ x → P₂ x) :
    amen.cong.rel (Sup P₁) (Sup P₂) := by
  -- (Sup P₁)⁺ ⊑ (Sup P₂)⁺
  have e1 : amen.largest (Sup P₁) ⊑ amen.largest (Sup P₂) := by
    have hb : Sup P₁ ⊑ amen.largest (Sup P₂) := by
      apply Sup_le
      intro x hx
      exact le_trans (le_Sup (hsub x hx)) (self_le_largest amen _)
    have h2 := amenable_le_largest amen hb
    rwa [largest_idem amen] at h2
  -- (Sup P₂)⁺ ⊑ (Sup P₁)⁺
  have e2 : amen.largest (Sup P₂) ⊑ amen.largest (Sup P₁) := by
    have hb : Sup P₂ ⊑ amen.largest (Sup P₁) := by
      apply Sup_le
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hsat x hx
      refine le_trans (self_le_largest amen x) ?_
      rw [amenable_largest_class_invariant amen hxy]
      exact amenable_le_largest amen (le_Sup hy)
    have h2 := amenable_le_largest amen hb
    rwa [largest_idem amen] at h2
  exact rel_of_largest_eq amen (le_antisymm e1 e2)

end QuotSup

/-! ## §2.55  Local completeness of the amenable quotient -/

/-- §2.55.  The amenable quotient of a locally complete distributive allegory is a
    locally complete distributive allegory.  `Sup P := [ Sup (fun r => P [r]) ]`;
    the supremum laws and the §2.22 distributive laws descend by the largest-element
    calculus above.  A `def` (not a global `instance`) because it needs the explicit
    `amen : AmenableCongruence 𝒜`. -/
def QuotAllegory.instLocallyComplete {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (amen : AmenableCongruence 𝒜) :
    LocallyCompleteDistributiveAllegory (QuotAllegory 𝒜 amen.cong) :=
  { QuotAllegory.instDistributiveAllegory amen.cong amen.union_congr with
    Sup := fun {a b} P =>
      Quotient.mk (congSetoid amen.cong)
        (@LocallyCompleteDistributiveAllegory.Sup 𝒜 _ a b
          (fun r => P (Quotient.mk (congSetoid amen.cong) r)))
    -- `[r] ⊑ Sup P`: since `r ⊑ Sup(P∘[·])` in the base, §2.531 gives `r⁺ ⊑ (Sup …)⁺`.
    le_Sup := by
      intro a b P R hR
      induction R using Quotient.inductionOn with
      | _ r =>
        refine (quot_le_iff_largest amen r _).mpr ?_
        exact amenable_le_largest amen
          (@LocallyCompleteDistributiveAllegory.le_Sup 𝒜 _ a b
            (fun r => P (Quotient.mk (congSetoid amen.cong) r)) r hR)
    -- `Sup P ⊑ [t]`: each `r` in the family has `r ⊑ r⁺ ⊑ t⁺`, so `Sup(P∘[·]) ⊑ t⁺`,
    -- whence `(Sup …)⁺ ⊑ t⁺⁺ = t⁺`.
    Sup_le := by
      intro a b P T h
      induction T using Quotient.inductionOn with
      | _ t =>
        refine (quot_le_iff_largest amen _ t).mpr ?_
        have hbound :
            (@LocallyCompleteDistributiveAllegory.Sup 𝒜 _ a b
              (fun r => P (Quotient.mk (congSetoid amen.cong) r))) ⊑ amen.largest t := by
          refine @LocallyCompleteDistributiveAllegory.Sup_le 𝒜 _ a b
            (fun r => P (Quotient.mk (congSetoid amen.cong) r)) (amen.largest t) ?_
          intro r hr
          have hrt : amen.largest r ⊑ amen.largest t :=
            (quot_le_iff_largest amen r t).mp (h (Quotient.mk (congSetoid amen.cong) r) hr)
          exact le_trans (self_le_largest amen r) hrt
        have hh := amenable_le_largest amen hbound
        rwa [largest_idem amen] at hh
    -- §2.22 right distributivity `[r] ≫ Sup P = Sup {[r] ≫ S}` (the well-definedness crux).
    comp_Sup_distrib := by
      intro a b c R P
      induction R using Quotient.inductionOn with
      | _ r =>
        refine Quotient.sound ?_
        rw [@LocallyCompleteDistributiveAllegory.comp_Sup_distrib 𝒜 _ a b c r
          (fun s => P (Quotient.mk (congSetoid amen.cong) s))]
        apply quotSup_distrib_rel amen
        · -- congruence-saturation: every RHS member is congruent to a literal `r ≫ s`
          intro x hx
          obtain ⟨S, hPS, hxS⟩ := hx
          induction S using Quotient.inductionOn with
          | _ s =>
            refine ⟨r ≫ s, ⟨s, hPS, rfl⟩, ?_⟩
            have hxS' : (Quotient.mk (congSetoid amen.cong) x)
                = Quotient.mk (congSetoid amen.cong) (r ≫ s) := hxS
            exact Quotient.exact hxS'
        · -- the literal family is contained in the RHS family
          intro x hx
          obtain ⟨s, hPs, hxs⟩ := hx
          refine ⟨Quotient.mk (congSetoid amen.cong) s, hPs, ?_⟩
          subst hxs
          rfl
    -- §2.22 intersection distributivity `[r] ∩ Sup P = Sup {[r] ∩ S}`.
    inter_Sup_distrib := by
      intro a b R P
      induction R using Quotient.inductionOn with
      | _ r =>
        refine Quotient.sound ?_
        rw [@LocallyCompleteDistributiveAllegory.inter_Sup_distrib 𝒜 _ a b r
          (fun s => P (Quotient.mk (congSetoid amen.cong) s))]
        apply quotSup_distrib_rel amen
        · intro x hx
          obtain ⟨S, hPS, hxS⟩ := hx
          induction S using Quotient.inductionOn with
          | _ s =>
            refine ⟨r ∩ s, ⟨s, hPS, rfl⟩, ?_⟩
            have hxS' : (Quotient.mk (congSetoid amen.cong) x)
                = Quotient.mk (congSetoid amen.cong) (r ∩ s) := hxS
            exact Quotient.exact hxS'
        · intro x hx
          obtain ⟨s, hPs, hxs⟩ := hx
          refine ⟨Quotient.mk (congSetoid amen.cong) s, hPs, ?_⟩
          subst hxs
          rfl }

/-! ## §2.55  Global completeness of the amenable quotient

  "Global completeness is readily preserved": disjoint unions of objects already
  live in `𝒜`; the injections and their disjointness/completeness laws descend
  classwise, the only `Sup` law (`complete`) being a further instance of
  `quotSup_distrib_rel`. -/

/-- §2.55.  The amenable quotient of a globally complete allegory is globally
    complete. -/
def QuotAllegory.instGloballyComplete {𝒜 : Type u} [GloballyCompleteAllegory 𝒜]
    (amen : AmenableCongruence 𝒜) :
    GloballyCompleteAllegory (QuotAllegory 𝒜 amen.cong) :=
  { QuotAllegory.instLocallyComplete amen with
    disjointUnion := fun {I} a => @GloballyCompleteAllegory.disjointUnion 𝒜 _ I a
    inject := fun {I} {a} i =>
      Quotient.mk (congSetoid amen.cong) (@GloballyCompleteAllegory.inject 𝒜 _ I a i)
    inject_self_comp_recip := by
      intro I a i
      exact congrArg (Quotient.mk (congSetoid amen.cong))
        (@GloballyCompleteAllegory.inject_self_comp_recip 𝒜 _ I a i)
    inject_comp_recip_ne := by
      intro I a i j hij
      exact congrArg (Quotient.mk (congSetoid amen.cong))
        (@GloballyCompleteAllegory.inject_comp_recip_ne 𝒜 _ I a i j hij)
    complete := by
      intro I a
      -- base: `Sup {(inj i)° ≫ inj i} = 1`.  Lift it and absorb the quotient `Sup`.
      have hbase := @GloballyCompleteAllegory.complete 𝒜 _ I a
      refine Eq.trans ?_ (congrArg (Quotient.mk (congSetoid amen.cong)) hbase)
      refine Quotient.sound ?_
      refine amen.cong.symm (quotSup_distrib_rel amen _ _ ?_ ?_)
      · -- each quotient member is congruent to a base member `(inj i)° ≫ inj i`
        intro x hx
        obtain ⟨i, hxi⟩ := hx
        refine ⟨(@GloballyCompleteAllegory.inject 𝒜 _ I a i)°
            ≫ (@GloballyCompleteAllegory.inject 𝒜 _ I a i), ⟨i, rfl⟩, ?_⟩
        have hxi' : (Quotient.mk (congSetoid amen.cong) x)
            = Quotient.mk (congSetoid amen.cong)
              ((@GloballyCompleteAllegory.inject 𝒜 _ I a i)°
                ≫ (@GloballyCompleteAllegory.inject 𝒜 _ I a i)) := hxi
        exact Quotient.exact hxi'
      · -- the base family is contained in the quotient family
        intro x hx
        obtain ⟨i, hxi⟩ := hx
        refine ⟨i, ?_⟩
        subst hxi
        rfl }

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.551 (algebraic core).

  > 2.551. Disjoint unions in a globally complete allegory coincide with
  > coproducts (AND WITH PRODUCTS) [2.223, 2.214] ...

  `Freyd/S2_223_CoproductConverse.lean` together with `IndexedDisjointUnion.isCoproduct`
  (S2_22_Completions) establishes the COPRODUCT coincidence (both directions).  This
  file adds the PRODUCT coincidence, the other half of the §2.551 citation: a disjoint
  union is an indexed PRODUCT with projections the reciprocals `Uᵢ°` of its injections.

  This is the indexed instance of Freyd's §2.215 reciprocal duality ("any allegory is
  isomorphic, via reciprocation, to its opposite; `⟨U₁,U₂⟩` is a coproduct iff
  `⟨U₁°,U₂°⟩` is a product"): the product universal property for `(Uᵢ°)` is the
  coproduct universal property for `(Uᵢ)` read through `(·)°`.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`.  Mathlib-free.
-/



namespace Freyd.Alg

open Cat

section LCDAProduct

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- The indexed PRODUCT universal property for projections `p : ∀ i, β ⟶ αᵢ`
    (§2.215/§2.551, the reciprocal dual of `IsIndexedCoproduct`): every family
    `{Rᵢ : c → αᵢ}` factors uniquely through the projections. -/
def IsIndexedProduct (p : (i : I) → β ⟶ α i) : Prop :=
  ∀ (c : 𝒜) (R : (i : I) → c ⟶ α i),
    ∃ M : c ⟶ β, (∀ i, M ≫ p i = R i) ∧
      (∀ M' : c ⟶ β, (∀ i, M' ≫ p i = R i) → M' = M)

/-- **§2.551 (product coincidence).**  A disjoint union is an indexed PRODUCT with
    projections `Uᵢ°`.  By §2.215 reciprocal duality, the product mediator of a family
    `{Rᵢ : c → αᵢ}` is `N°`, where `N : β → c` is the coproduct mediator of the
    reciprocated family `{Rᵢ° : αᵢ → c}` (`IndexedDisjointUnion.isCoproduct`):
      `N° ≫ Uᵢ° = (Uᵢ ≫ N)° = (Rᵢ°)° = Rᵢ`,
    and uniqueness reciprocates the coproduct's. -/
theorem IndexedDisjointUnion.isProduct (du : IndexedDisjointUnion α β) :
    IsIndexedProduct (fun i => (du.U i)°) := by
  intro c R
  -- Coproduct mediator `N : β → c` of the reciprocated family `Rᵢ° : αᵢ → c`.
  obtain ⟨N, hN, hNuniq⟩ := du.isCoproduct c (fun i => (R i)°)
  refine ⟨N°, ?_, ?_⟩
  · -- `N° ≫ Uᵢ° = (Uᵢ ≫ N)° = (Rᵢ°)° = Rᵢ`.
    intro i
    rw [← Allegory.recip_comp, hN i, Allegory.recip_recip]
  · -- Uniqueness: `M' ≫ Uᵢ° = Rᵢ ⟹ Uᵢ ≫ M'° = Rᵢ° ⟹ M'° = N ⟹ M' = N°`.
    intro M' hM'
    have hM'rec : ∀ i, du.U i ≫ M'° = (R i)° := by
      intro i
      have hi : M' ≫ (du.U i)° = R i := hM' i
      rw [← hi, Allegory.recip_comp, Allegory.recip_recip]
    have : M'° = N := hNuniq M'° hM'rec
    rw [← Allegory.recip_recip M', this]

end LCDAProduct

end Freyd.Alg
