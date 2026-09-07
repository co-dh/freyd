module

public import Freyd.S2_50

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.522 / §2.53.

  CLOSED QUOTIENTS ARE AMENABLE.

  §2.522  The CLOSED QUOTIENT with respect to `U : λ ⟶ λ` identifies `R, S : α ⟶ β`
  iff `R ∪ pα U pβ° = S ∪ pα U pβ°`.  It is the least congruence which identifies `U`
  with zero and respects binary unions.

  §2.53   Closed quotients are AMENABLE: the largest member of the class of `R` is
            `R⁺ = R ∪ pα U pβ°`.

  This file packages the closed-quotient congruence (already built in
  `Freyd/S2_5.lean` as `closedQuotientRel_is_congruence`) as an
  `AmenableCongruence`, with `largest R := R ∪ (p a ≫ U ≫ (p b)°)` — Freyd's `R⁺`.
-/



namespace Freyd.Alg

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The join of three elements regrouped: `(R ∪ K) ∪ (S ∪ K) = (R ∪ S) ∪ K`.
    Both sides are the least upper bound of `R`, `S`, `K`; proved by the
    union laws (associativity, commutativity, idempotence). -/
private theorem union_pull {A B : 𝒜} (R S K : A ⟶ B) :
    (R ∪ K) ∪ (S ∪ K) = (R ∪ S) ∪ K := by
  rw [DistributiveAllegory.union_assoc (R ∪ K) S K,
      ← DistributiveAllegory.union_assoc R K S,
      DistributiveAllegory.union_comm K S,
      DistributiveAllegory.union_assoc R S K,
      ← DistributiveAllegory.union_assoc (R ∪ S) K K,
      DistributiveAllegory.union_idem K]

/-! ## §2.53  The closed quotient is amenable

  We reuse the closed-quotient congruence `closedQuotientRel_is_congruence`
  (the *same* `U`/`p` data, with the same symmetry/ideal hypotheses) and
  exhibit, for each class, the largest member `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`.

  The three amenability obligations are pure union algebra:

  * `union_congr` — the relation is defined by a `∪`-equation, so it respects `∪`
    (regroup with `union_pull` and rewrite by the two hypotheses).
  * `largest_rel`  — `R ∪ K = (R ∪ K) ∪ K` by associativity + idempotence of `K`.
  * `largest_max`  — if `R ∪ K = S ∪ K` then `S ⊑ S ∪ K = R ∪ K = R⁺`. -/

/-- §2.53  CLOSED QUOTIENTS ARE AMENABLE.

    For a symmetric `U : T ⟶ T` on the unit, with the canonical projection family
    `p : ∀ a, a ⟶ T` and the two-sided ideal absorption laws `hL`, `hR'`
    (exactly the data of `closedQuotientRel_is_congruence`), the closed-quotient
    congruence is amenable, with largest-in-class operator the book's
    `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`. -/
def closedQuotient_amenable
    {T : 𝒜} (U : T ⟶ T) (p : ∀ (A : 𝒜), A ⟶ T) (hU : U° = U)
    (hL : ∀ {A B C : 𝒜} (R : A ⟶ B),
      R ≫ (p B ≫ U ≫ (p C)°) ⊑ p A ≫ U ≫ (p C)°)
    (hR' : ∀ {A B C : 𝒜} (S : B ⟶ C),
      (p A ≫ U ≫ (p B)°) ≫ S ⊑ p A ≫ U ≫ (p C)°) :
    AmenableCongruence 𝒜 where
  cong := closedQuotientRel_is_congruence U p hU hL hR'
  union_congr {A B R S R' S'} hR hS := by
    -- `cong.rel X Y` is `X ∪ K = Y ∪ K` with `K = p a ≫ U ≫ (p b)°`.
    have hRe : R ∪ (p A ≫ U ≫ (p B)°) = R' ∪ (p A ≫ U ≫ (p B)°) := hR
    have hSe : S ∪ (p A ≫ U ≫ (p B)°) = S' ∪ (p A ≫ U ≫ (p B)°) := hS
    show closedQuotientRel U (p A) (p B) (R ∪ S) (R' ∪ S')
    simp only [closedQuotientRel]
    -- (R∪S)∪K = (R∪K)∪(S∪K) = (R'∪K)∪(S'∪K) = (R'∪S')∪K.
    rw [← union_pull R S (p A ≫ U ≫ (p B)°), ← union_pull R' S' (p A ≫ U ≫ (p B)°),
        hRe, hSe]
  largest {A B} R := R ∪ (p A ≫ U ≫ (p B)°)
  largest_rel {A B} R := by
    -- Goal: `R ∪ K = (R ∪ K) ∪ K`, by associativity + idempotence.
    show R ∪ (p A ≫ U ≫ (p B)°)
       = (R ∪ (p A ≫ U ≫ (p B)°)) ∪ (p A ≫ U ≫ (p B)°)
    rw [← DistributiveAllegory.union_assoc R (p A ≫ U ≫ (p B)°) (p A ≫ U ≫ (p B)°),
        DistributiveAllegory.union_idem]
  largest_max {A B R S} h := by
    -- h : R ∪ K = S ∪ K.  Goal: S ⊑ R ∪ K.  Use S ⊑ S ∪ K = R ∪ K.
    have he : R ∪ (p A ≫ U ≫ (p B)°) = S ∪ (p A ≫ U ≫ (p B)°) := h
    have hs : S ⊑ S ∪ (p A ≫ U ≫ (p B)°) := le_union_left S _
    rw [← he] at hs
    exact hs

/-- §2.53 headline: the closed quotient (w.r.t. a symmetric `U` with the
    canonical projections `p` and ideal-absorption laws `hL`, `hR'`) is amenable.
    Its largest-in-class operator is Freyd's `R⁺ = R ∪ (p a ≫ U ≫ (p b)°)`. -/
theorem closedQuotient_amenable_largest_eq
    {T : 𝒜} (U : T ⟶ T) (p : ∀ (A : 𝒜), A ⟶ T) (hU : U° = U)
    (hL : ∀ {A B C : 𝒜} (R : A ⟶ B),
      R ≫ (p B ≫ U ≫ (p C)°) ⊑ p A ≫ U ≫ (p C)°)
    (hR' : ∀ {A B C : 𝒜} (S : B ⟶ C),
      (p A ≫ U ≫ (p B)°) ≫ S ⊑ p A ≫ U ≫ (p C)°)
    {A B : 𝒜} (R : A ⟶ B) :
    (closedQuotient_amenable U p hU hL hR').largest R = R ∪ (p A ≫ U ≫ (p B)°) :=
  rfl

end Freyd.Alg
