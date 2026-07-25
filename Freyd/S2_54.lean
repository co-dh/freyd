import Freyd.S2_50

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.541
  TRANSITIVE CLOSURE IN AN AMENABLE QUOTIENT.

  "We now show that transitive closure in an allegory remains such in an
  amenable quotient."

  Book proof.  Use the characterization [1.787] of the transitive closure `R*`
  as the LEAST reflexive `S` such that `R≫S ⊑ S`.  Note `overline(R*)` (the
  congruence class of `R*`) is reflexive; and `R̄·overline(R*) ⊑ overline(R*)`
  because `R·R* ⊑ R*`.  Conversely if a class `S̄` is reflexive and
  `R̄·S̄ ⊑ S̄`, then taking `S⁺ = largest S` we have, by [2.533–2.535],
  `1 ⊑ 1⁺ ⊑ S⁺` and `R·S⁺ ⊑ R⁺·S⁺ ⊑ S⁺`, so `S⁺` is a reflexive absorber of
  `R`; hence `R* ⊑ S⁺` by [1.787].  By [2.531], `(R*)⁺ ⊑ S⁺⁺ = S⁺`, which by
  [2.533] gives `overline(R*) ⊑ S̄`.  Therefore `(R̄)* = overline(R*)`.

  We package [1.787]'s characterization as `IsTransClosure R Rstar` and prove
  `IsTransClosure (quotRep R) (quotRep Rstar)` in the quotient allegory.
-/



namespace Freyd.Alg

/-! ## [1.787]  Transitive closure as a least reflexive absorber

  In any allegory, the TRANSITIVE CLOSURE `R*` of an endo `R : a ⟶ a` is the
  least reflexive `S` with `R≫S ⊑ S` (Freyd [1.787]).  We carry this
  characterization as data so that the §2.541 transfer can be stated and used
  abstractly, with no reference to how `R*` is built. -/

/-- `Rstar` is the TRANSITIVE CLOSURE of `R` (book [1.787] characterization):
    it is reflexive, absorbs `R` on the left (`R≫Rstar ⊑ Rstar`), and is least
    among reflexive relations doing so. -/
structure IsTransClosure {𝒜 : Type u} [Allegory 𝒜] {a : 𝒜} (R Rstar : a ⟶ a) : Prop where
  /-- `1 ⊑ R*`. -/
  reflexive : Reflexive Rstar
  /-- `R·R* ⊑ R*`. -/
  absorbs : R ≫ Rstar ⊑ Rstar
  /-- `R*` is below every reflexive `S` with `R·S ⊑ S`. -/
  least : ∀ S : a ⟶ a, Reflexive S → R ≫ S ⊑ S → Rstar ⊑ S

/-! ## §2.5  The quotient order on classes

  `[R] ⊑ [S]` in `QuotAllegory 𝒜 C` is exactly `C.rel (R∩S) R`, i.e. the class
  of `R∩S` equals the class of `R`.  `quotRep` is monotone, and for an amenable
  congruence the quotient order is detected by largest representatives (this is
  the book's [2.533]). -/

section QuotOrder

variable {𝒜 : Type u} [Allegory 𝒜]

/-- `[R] ⊑ [S]` in the quotient allegory iff `R∩S ≡ R` in the congruence.
    (The quotient order `le` unfolds to `[R]∩[S] = [R]`, i.e. `[R∩S] = [R]`,
    which by `Quotient.eq` is `C.rel (R∩S) R`.) -/
theorem quotRep_le_iff_rel (C : Congruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    (quotRep C).map R ⊑ (quotRep C).map S ↔ C.rel (R ∩ S) R := by
  constructor
  · intro h
    have h' : (Quotient.mk (congSetoid C) (R ∩ S)) = Quotient.mk (congSetoid C) R := h
    exact Quotient.exact h'
  · intro h
    show (Quotient.mk (congSetoid C) (R ∩ S)) = Quotient.mk (congSetoid C) R
    exact Quotient.sound h

end QuotOrder

section AmenableQuot

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- §2.533 in the quotient order: `[R] ⊑ [S]` iff `R⁺ ⊑ S⁺`.  Combines
    `quotRep_le_iff_rel` with `quotient_order_iff_largest`. -/
theorem quotRep_le_iff_largest (amen : AmenableCongruence 𝒜) {a b : 𝒜} (R S : a ⟶ b) :
    (quotRep amen.cong).map R ⊑ (quotRep amen.cong).map S ↔ amen.largest R ⊑ amen.largest S := by
  rw [quotRep_le_iff_rel amen.cong R S, ← quotient_order_iff_largest amen R S]
  constructor
  · intro h
    exact ⟨R ∩ S, S, amen.cong.symm h, amen.cong.refl S, inter_lb_right R S⟩
  · rintro ⟨R', S', hR, hS, hle⟩
    have h1 : amen.cong.rel (R ∩ S) (R' ∩ S') := amen.cong.inter_congr hR hS
    rw [inter_eq_left hle] at h1
    exact amen.cong.trans h1 (amen.cong.symm hR)


/-! ## §2.541  Transitive closure survives an amenable quotient -/

/-- §2.541: TRANSITIVE CLOSURE IN AN ALLEGORY REMAINS SUCH IN AN AMENABLE
    QUOTIENT.  If `Rstar` is the transitive closure of `R` in `𝒜` (book
    [1.787]), then its class `overline(Rstar) = quotRep Rstar` is the
    transitive closure of `quotRep R` in `QuotAllegory 𝒜 amen.cong`, i.e.
    `(R̄)* = overline(R*)`. -/
theorem quotRep_isTransClosure (amen : AmenableCongruence 𝒜) {a : 𝒜} {R Rstar : a ⟶ a}
    (hRstar : IsTransClosure R Rstar) :
    IsTransClosure ((quotRep amen.cong).map R) ((quotRep amen.cong).map Rstar) where
  -- `overline(R*)` is reflexive because `R*` is and `quotRep` preserves `1`, order.
  reflexive := by
    show (quotRep amen.cong).map (Cat.id a) ⊑ (quotRep amen.cong).map Rstar
    exact quotRep_mono amen.cong (show Cat.id a ⊑ Rstar from hRstar.reflexive)
  -- `R̄·overline(R*) = overline(R·R*) ⊑ overline(R*)` from `R·R* ⊑ R*`.
  absorbs := by
    show (quotRep amen.cong).map (R ≫ Rstar) ⊑ (quotRep amen.cong).map Rstar
    exact quotRep_mono amen.cong hRstar.absorbs
  -- Leastness: a reflexive class `[S₀]` absorbing `R̄` has `S₀⁺` a reflexive
  -- absorber of `R` in `𝒜`; apply [1.787], then [2.531]+`S⁺⁺=S⁺` and [2.533].
  least := by
    intro Sbar
    refine Quotient.inductionOn Sbar (fun S₀ => ?_)
    intro hrefl habs
    -- Translate the two quotient hypotheses to largest-element inequalities (§2.533).
    have hrefl' : (quotRep amen.cong).map (Cat.id a) ⊑ (quotRep amen.cong).map S₀ := hrefl
    have habs' : (quotRep amen.cong).map (R ≫ S₀) ⊑ (quotRep amen.cong).map S₀ := habs
    have h1 : amen.largest (Cat.id a) ⊑ amen.largest S₀ :=
      (quotRep_le_iff_largest amen (Cat.id a) S₀).mp hrefl'
    have h2 : amen.largest (R ≫ S₀) ⊑ amen.largest S₀ :=
      (quotRep_le_iff_largest amen (R ≫ S₀) S₀).mp habs'
    -- (a) `S₀⁺` reflexive: `1 ⊑ 1⁺ ⊑ S₀⁺`.
    have h1plus : Cat.id a ⊑ amen.largest (Cat.id a) := amen.largest_max (amen.cong.refl (Cat.id a))
    have hSref : Reflexive (amen.largest S₀) := le_trans h1plus h1
    -- (b) `S₀⁺` absorbs `R`: `R·S₀⁺ ⊑ R⁺·S₀⁺ ⊑ (R·S₀)⁺ ⊑ S₀⁺`.
    have hRle : R ⊑ amen.largest R := amen.largest_max (amen.cong.refl R)
    have hb1 : R ≫ amen.largest S₀ ⊑ amen.largest R ≫ amen.largest S₀ := comp_mono_right hRle _
    have hb2 : amen.largest R ≫ amen.largest S₀ ⊑ amen.largest (R ≫ S₀) := largest_comp_le amen R S₀
    have hSabs : R ≫ amen.largest S₀ ⊑ amen.largest S₀ := le_trans (le_trans hb1 hb2) h2
    -- [1.787]: `R* ⊑ S₀⁺`.
    have hstar : Rstar ⊑ amen.largest S₀ := hRstar.least (amen.largest S₀) hSref hSabs
    -- [2.531] + `S⁺⁺ = S⁺`: `(R*)⁺ ⊑ S₀⁺`.
    have hfin : amen.largest Rstar ⊑ amen.largest S₀ := by
      have hstep := amenable_le_largest amen hstar
      rwa [largest_idem amen S₀] at hstep
    -- [2.533]: `overline(R*) ⊑ [S₀]`.
    exact (quotRep_le_iff_largest amen Rstar S₀).mpr hfin

end AmenableQuot

end Freyd.Alg
