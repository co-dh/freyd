/-
  Bird & de Moor, *Algebra of Programming* §4.5  Boolean allegories.

  Builds on `AOP.A4_4` (implication `R ⇨ S`, `topHom`, division, `comp_inter_zero_iff`).

  Contents:
  §1  Negation `∼R := R ⇨ 0` and its LCDA-level laws (Ex 4.29/4.31/4.41).
  §2  `BooleanAllegory` and its consequences (Ex 4.41/4.42).
  §3  Division via negation (`neg_div`, `div_eq_neg_comp`).
  §4  Schröder's rule (Ex 4.43).
  §5  Subtraction (Ex 4.30).
-/

module

public import AOP.A4_4

universe v u

namespace Freyd.Alg

/-! ## §1  Negation (B&dM §4.4/4.5) -/

section LCDANeg

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- `R ⊑ 0 ↔ R = 0` — zero is the bottom of every hom-set. -/
public theorem le_zero_iff_eq_zero {a b : 𝒜} (R : a ⟶ b) : R ⊑ (𝟘 : a ⟶ b) ↔ R = 𝟘 :=
  ⟨fun h => le_antisymm h (zero_le _), fun h => h ▸ le_refl _⟩

/-- `A∪B = 0 ↔ A = 0 ∧ B = 0`. -/
theorem union_eq_zero_iff {a b : 𝒜} (A B : a ⟶ b) :
    (A ∪ B = (𝟘 : a ⟶ b)) ↔ (A = 𝟘 ∧ B = 𝟘) := by
  constructor
  · intro h
    exact ⟨(le_zero_iff_eq_zero A).mp (h ▸ le_union_left A B),
           (le_zero_iff_eq_zero B).mp (h ▸ le_union_right A B)⟩
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    exact DistributiveAllegory.union_idem 𝟘

/-- Negation `∼R := R ⇨ 0`. -/
@[expose] public def neg {a b : 𝒜} (R : a ⟶ b) : a ⟶ b := R ⇨ (𝟘 : a ⟶ b)

/-- Negation notation `∼R`. -/
prefix:max (name := negNotation) "∼" => neg

/-- The universal property of negation: `X ⊑ ∼R ↔ X∩R = 0`. -/
public theorem le_neg_iff {a b : 𝒜} (X R : a ⟶ b) : X ⊑ ∼R ↔ X ∩ R = 𝟘 := by
  rw [neg, le_impl_iff, le_zero_iff_eq_zero]

public theorem inter_neg_zero {a b : 𝒜} (R : a ⟶ b) : R ∩ (∼R) = 𝟘 := by
  rw [Allegory.inter_comm]
  exact (le_neg_iff (∼R) R).mp (le_refl _)

/-- De Morgan: `∼(R∪S) = ∼R ∩ ∼S`. -/
public theorem neg_union {a b : 𝒜} (R S : a ⟶ b) : ∼(R ∪ S) = (∼R) ∩ (∼S) := by
  apply le_antisymm
  · exact le_inter (impl_antitone_left (le_union_left R S)) (impl_antitone_left (le_union_right R S))
  · apply (le_neg_iff _ _).mpr
    rw [DistributiveAllegory.inter_union_distrib]
    have hR0 : ((∼R) ∩ (∼S)) ∩ R = 𝟘 := by
      apply (le_zero_iff_eq_zero _).mp
      have h1 : ((∼R) ∩ (∼S)) ∩ R ⊑ (∼R) ∩ R := inter_mono (inter_lb_left _ _) (le_refl R)
      rwa [Allegory.inter_comm (∼R) R, inter_neg_zero R] at h1
    have hS0 : ((∼R) ∩ (∼S)) ∩ S = 𝟘 := by
      apply (le_zero_iff_eq_zero _).mp
      have h1 : ((∼R) ∩ (∼S)) ∩ S ⊑ (∼S) ∩ S := inter_mono (inter_lb_right _ _) (le_refl S)
      rwa [Allegory.inter_comm (∼S) S, inter_neg_zero S] at h1
    rw [hR0, hS0]
    exact DistributiveAllegory.union_idem 𝟘

/-- **Ex 4.41**: `∼0 = ⊤`. -/
public theorem neg_zero {a b : 𝒜} : (∼(𝟘 : a ⟶ b)) = topHom a b := by
  apply le_antisymm (le_Sup trivial)
  apply (le_neg_iff _ _).mpr
  exact le_antisymm (inter_lb_right _ _) (zero_le _)

/-- **Ex 4.41**: `∼⊤ = 0`. -/
public theorem neg_topHom {a b : 𝒜} : (∼(topHom a b)) = (𝟘 : a ⟶ b) := by
  have h := (le_neg_iff (∼(topHom a b)) (topHom a b)).mp (le_refl _)
  rwa [inter_eq_left (show (∼(topHom a b) : a ⟶ b) ⊑ topHom a b from le_Sup trivial)] at h

public theorem le_neg_neg {a b : 𝒜} (R : a ⟶ b) : R ⊑ ∼∼R :=
  (le_neg_iff R (∼R)).mpr (inter_neg_zero R)

/-- **Ex 4.41**: `∼R = ∼∼∼R`. -/
theorem neg_neg_neg {a b : 𝒜} (R : a ⟶ b) : (∼R) = ∼∼∼R :=
  le_antisymm (le_neg_neg (∼R)) (impl_antitone_left (le_neg_neg R))

/-- **Ex 4.41**: `∼∼(R∪∼R) = ⊤`. -/
public theorem neg_neg_union_neg {a b : 𝒜} (R : a ⟶ b) : ∼∼(R ∪ ∼R) = topHom a b := by
  have h : ∼(R ∪ ∼R) = (𝟘 : a ⟶ b) := by
    rw [neg_union]; exact inter_neg_zero (∼R)
  rw [h, neg_zero]

/-- **Ex 4.42**: `∼∼` is the identity for all `R` iff `R∪∼R = ⊤` for all `R` (excluded
    middle iff double-negation elimination).  Stated as a plain theorem quantifying over the
    property (NOT `BooleanAllegory`, which bundles the forward direction as a field). -/
theorem boolean_iff {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜] :
    (∀ {a b : 𝒜} (R : a ⟶ b), ∼∼R = R) ↔ (∀ {a b : 𝒜} (R : a ⟶ b), R ∪ (∼R) = topHom a b) := by
  constructor
  · intro hnn a b R
    have h := neg_neg_union_neg R
    rwa [hnn (R ∪ ∼R)] at h
  · intro hem a b R
    apply le_antisymm _ (le_neg_neg R)
    have heq : ∼∼R = ((∼∼R) ∩ R) ∪ ((∼∼R) ∩ (∼R)) := by
      rw [← DistributiveAllegory.inter_union_distrib, hem R,
        inter_eq_left (show (∼∼R : a ⟶ b) ⊑ topHom a b from le_Sup trivial)]
    have h2 : (∼∼R) ∩ (∼R) = 𝟘 := by
      rw [Allegory.inter_comm]; exact inter_neg_zero (∼R)
    rw [heq, h2, union_zero]
    exact inter_lb_right (∼∼R) R

end LCDANeg

/-! ## §2  Boolean allegories (B&dM p.102) -/

/-- A **BOOLEAN ALLEGORY** (B&dM p.102): a locally complete distributive allegory in which
    negation is involutive.  `Rel` is Boolean. -/
public class BooleanAllegory (𝒜 : Type u) extends LocallyCompleteDistributiveAllegory 𝒜 where
  neg_neg : ∀ {a b : 𝒜} (R : a ⟶ b), Freyd.Alg.neg (Freyd.Alg.neg R) = R

section Boolean

variable {𝒜 : Type u} [BooleanAllegory 𝒜]

/-- De Morgan for `∩` (dual of `neg_union`, needs full negation). -/
theorem neg_inter {a b : 𝒜} (R S : a ⟶ b) : (∼(R ∩ S)) = (∼R) ∪ (∼S) := by
  have h : ∼((∼R) ∪ (∼S)) = R ∩ S := by
    rw [neg_union, BooleanAllegory.neg_neg, BooleanAllegory.neg_neg]
  have h2 := congrArg neg h
  rw [BooleanAllegory.neg_neg] at h2
  exact h2.symm

/-- **Ex 4.42**, forward instance: `R ∪ ∼R = ⊤` (excluded middle) in a Boolean allegory. -/
public theorem union_neg_eq_top {a b : 𝒜} (R : a ⟶ b) : R ∪ (∼R) = topHom a b := by
  rw [← BooleanAllegory.neg_neg (R ∪ ∼R)]
  exact neg_neg_union_neg R

/-- `R ⊑ S ↔ R∩∼S = 0`. -/
theorem le_iff_inter_neg_zero {a b : 𝒜} (R S : a ⟶ b) : R ⊑ S ↔ R ∩ (∼S) = 𝟘 := by
  constructor
  · intro h
    have h1 : R ∩ (∼S) ⊑ S ∩ (∼S) := inter_mono h (le_refl (∼S))
    rw [inter_neg_zero S] at h1
    exact (le_zero_iff_eq_zero _).mp h1
  · intro h
    have heq : R = (R ∩ S) ∪ (R ∩ (∼S)) := by
      rw [← DistributiveAllegory.inter_union_distrib, union_neg_eq_top S,
        inter_eq_left (show R ⊑ topHom a b from LocallyCompleteDistributiveAllegory.le_Sup trivial)]
    rw [heq, h, union_zero]
    exact inter_lb_right R S

/-! ### §4  Schröder's rule (Ex 4.43) -/

/-- **private**: `X = 0 ↔ X° = 0` (reciprocation is an order isomorphism fixing `0`). -/
private theorem zero_iff_recip_zero {a b : 𝒜} (X : a ⟶ b) : X = (𝟘 : a ⟶ b) ↔ X° = (𝟘 : b ⟶ a) := by
  constructor
  · intro h; rw [h]; exact recip_zero
  · intro h
    have h2 := congrArg Allegory.recip h
    rwa [Allegory.recip_recip, recip_zero] at h2

/-- **private**: the mirror of `comp_inter_zero_iff` rotating through `R°` instead of `S°`:
    `(R≫S)∩T = 0 ↔ S∩(R°≫T) = 0`. -/
private theorem comp_inter_zero_iff_left {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    ((R ≫ S) ∩ T = (𝟘 : a ⟶ c)) ↔ (S ∩ (R° ≫ T) = (𝟘 : b ⟶ c)) := by
  calc (R ≫ S) ∩ T = (𝟘 : a ⟶ c) ↔ ((R ≫ S) ∩ T)° = (𝟘 : c ⟶ a) := zero_iff_recip_zero _
    _ ↔ (S° ≫ R°) ∩ T° = (𝟘 : c ⟶ a) := by rw [Allegory.recip_inter, Allegory.recip_comp]
    _ ↔ S° ∩ (T° ≫ R°°) = (𝟘 : c ⟶ b) := comp_inter_zero_iff (S°) (R°) (T°)
    _ ↔ S° ∩ (T° ≫ R) = (𝟘 : c ⟶ b) := by rw [Allegory.recip_recip]
    _ ↔ (S° ∩ (T° ≫ R))° = (𝟘 : b ⟶ c) := zero_iff_recip_zero _
    _ ↔ S°° ∩ (T° ≫ R)° = (𝟘 : b ⟶ c) := by rw [Allegory.recip_inter]
    _ ↔ S ∩ (R° ≫ T) = (𝟘 : b ⟶ c) := by
          rw [Allegory.recip_recip, Allegory.recip_comp, Allegory.recip_recip]

/-- **Schröder's rule**, left form (Ex 4.43). -/
theorem schroeder_left {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S ⊑ T) ↔ (R° ≫ (∼T) ⊑ ∼S) := by
  calc R ≫ S ⊑ T ↔ (R ≫ S) ∩ (∼T) = 𝟘 := le_iff_inter_neg_zero (R ≫ S) T
    _ ↔ S ∩ (R° ≫ (∼T)) = 𝟘 := comp_inter_zero_iff_left R S (∼T)
    _ ↔ R° ≫ (∼T) ⊑ ∼S := by rw [Allegory.inter_comm]; exact (le_neg_iff _ _).symm

/-- **Schröder's rule**, right form (Ex 4.43). -/
theorem schroeder_right {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S ⊑ T) ↔ ((∼T) ≫ S° ⊑ ∼R) := by
  calc R ≫ S ⊑ T ↔ (R ≫ S) ∩ (∼T) = 𝟘 := le_iff_inter_neg_zero (R ≫ S) T
    _ ↔ R ∩ ((∼T) ≫ S°) = 𝟘 := comp_inter_zero_iff R S (∼T)
    _ ↔ (∼T) ≫ S° ⊑ ∼R := by rw [Allegory.inter_comm]; exact (le_neg_iff _ _).symm

/-! ### §5  Subtraction (Ex 4.30) -/

/-- Subtraction `R − S := R ∩ ∼S`. -/
@[expose] public def sub {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b := R ∩ (∼S)

/-- The universal property of subtraction: `R−S ⊑ X ↔ R ⊑ S∪X`. -/
theorem sub_le_iff {a b : 𝒜} (R S X : a ⟶ b) : sub R S ⊑ X ↔ R ⊑ S ∪ X := by
  show R ∩ (∼S) ⊑ X ↔ R ⊑ S ∪ X
  constructor
  · intro h
    have heq : R = (R ∩ S) ∪ (R ∩ (∼S)) := by
      rw [← DistributiveAllegory.inter_union_distrib, union_neg_eq_top S,
        inter_eq_left (show R ⊑ topHom a b from LocallyCompleteDistributiveAllegory.le_Sup trivial)]
    rw [heq]
    exact union_lub (le_trans (inter_lb_right R S) (le_union_left S X)) (le_trans h (le_union_right S X))
  · intro h
    have h1 : R ∩ (∼S) ⊑ (S ∪ X) ∩ (∼S) := inter_mono h (le_refl _)
    rw [Allegory.inter_comm (S ∪ X) (∼S), DistributiveAllegory.inter_union_distrib] at h1
    have h2 : (∼S) ∩ S = 𝟘 := by rw [Allegory.inter_comm]; exact inter_neg_zero S
    rw [h2, DistributiveAllegory.zero_union] at h1
    exact le_trans h1 (inter_lb_right (∼S) X)

public theorem sub_zero {a b : 𝒜} (R : a ⟶ b) : sub R 𝟘 = R := by
  show R ∩ (∼(𝟘 : a ⟶ b)) = R
  rw [neg_zero]
  exact inter_eq_left (LocallyCompleteDistributiveAllegory.le_Sup trivial)

public theorem union_sub_absorb {a b : 𝒜} (R S : a ⟶ b) : R ∪ (sub S R) = R ∪ S := by
  apply le_antisymm
  · apply union_lub (le_union_left R S)
    exact le_trans (inter_lb_left S (∼R)) (le_union_right R S)
  · apply union_lub (le_union_left R (sub S R))
    have heq : S = (S ∩ R) ∪ (S ∩ (∼R)) := by
      rw [← DistributiveAllegory.inter_union_distrib, union_neg_eq_top R,
        inter_eq_left (show S ⊑ topHom a b from LocallyCompleteDistributiveAllegory.le_Sup trivial)]
    have hu : (S ∩ R) ∪ (S ∩ (∼R)) ⊑ R ∪ (sub S R) :=
      union_lub (le_trans (inter_lb_right S R) (le_union_left R (sub S R)))
        (le_union_right R (sub S R))
    rwa [← heq] at hu

public theorem sub_union {a b : 𝒜} (R S T : a ⟶ b) : sub R (S ∪ T) = sub (sub R S) T := by
  show R ∩ (∼(S ∪ T)) = (R ∩ (∼S)) ∩ (∼T)
  rw [neg_union, Allegory.inter_assoc]

public theorem union_sub_distrib {a b : 𝒜} (R S T : a ⟶ b) : sub (R ∪ S) T = sub R T ∪ sub S T := by
  show (R ∪ S) ∩ (∼T) = (R ∩ (∼T)) ∪ (S ∩ (∼T))
  rw [Allegory.inter_comm (R ∪ S) (∼T), DistributiveAllegory.inter_union_distrib,
    Allegory.inter_comm (∼T) R, Allegory.inter_comm (∼T) S]

/-- `sub` is monotonic in its numerator. -/
public theorem sub_mono_left {a b : 𝒜} {R R' : a ⟶ b} (h : R ⊑ R') (S : a ⟶ b) :
    sub R S ⊑ sub R' S :=
  inter_mono h (le_refl (∼S))

end Boolean

/-! ## §3  Division via negation (B&dM 4.21/4.22)

  `LocallyCompleteDistributiveAllegory` and `DivisionAllegory` both `extends
  DistributiveAllegory` independently; taking them as two SEPARATE `variable` hypotheses makes
  `𝟘`/`∩`/`≫` ambiguous between the two paths (the same diamond `S2_147`'s
  `TabularUnitaryDistributiveAllegory` was built to avoid).  We merge them into one class,
  matching that pattern, so their shared `Allegory` ancestor collapses to a single field. -/

/-- A `LocallyCompleteDistributiveAllegory` that is ALSO given as a `DivisionAllegory`
    (diamond-safe merge). -/
public class DivisionLCDA (𝒜 : Type u) extends LocallyCompleteDistributiveAllegory 𝒜, DivisionAllegory 𝒜

/-- A `BooleanAllegory` that is ALSO given as a `DivisionAllegory` (diamond-safe merge). -/
public class DivisionBooleanAllegory (𝒜 : Type u) extends BooleanAllegory 𝒜, DivisionAllegory 𝒜

/-- The Boolean merge is in particular a `DivisionLCDA` (all fields come from the ONE
    `DivisionBooleanAllegory` instance, so the bridge is diamond-safe). -/
@[expose] public instance (priority := 100) DivisionBooleanAllegory.toDivisionLCDA {𝒜 : Type u}
    [inst : DivisionBooleanAllegory 𝒜] : DivisionLCDA 𝒜 := { inst with }

section DivNeg

variable {𝒜 : Type u} [DivisionLCDA 𝒜]

/-- **B&dM 4.22**: `∼R / Y = ∼(R≫Y°)` — valid in ANY locally complete distributive allegory. -/
public theorem neg_div {a b c : 𝒜} (R : a ⟶ c) (Y : b ⟶ c) : (∼R) / Y = ∼(R ≫ Y°) := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ (∼R) / Y ↔ X ≫ Y ⊑ ∼R := le_div_iff _ _ _
    _ ↔ (X ≫ Y) ∩ R = 𝟘 := le_neg_iff _ _
    _ ↔ X ∩ (R ≫ Y°) = 𝟘 := comp_inter_zero_iff X Y R
    _ ↔ X ⊑ ∼(R ≫ Y°) := (le_neg_iff _ _).symm

end DivNeg

section DivBoolean

variable {𝒜 : Type u} [DivisionBooleanAllegory 𝒜]

/-- **B&dM 4.21**: `R / Y = ∼(∼R≫Y°)` in a Boolean allegory (substitute `R := ∼R` in the
    `neg_div` derivation and use `BooleanAllegory.neg_neg`; proved directly rather than via
    `neg_div` since the two division-merge classes, `DivisionLCDA` and
    `DivisionBooleanAllegory`, are not related by `extends`). -/
public theorem div_eq_neg_comp {a b c : 𝒜} (R : a ⟶ c) (Y : b ⟶ c) : R / Y = ∼((∼R) ≫ Y°) := by
  apply antisymm_of_le_iff
  intro X
  calc X ⊑ R / Y ↔ X ≫ Y ⊑ R := le_div_iff _ _ _
    _ ↔ X ≫ Y ⊑ ∼∼R := by rw [BooleanAllegory.neg_neg]
    _ ↔ (X ≫ Y) ∩ (∼R) = 𝟘 := le_neg_iff _ _
    _ ↔ X ∩ ((∼R) ≫ Y°) = 𝟘 := comp_inter_zero_iff X Y (∼R)
    _ ↔ X ⊑ ∼((∼R) ≫ Y°) := (le_neg_iff _ _).symm

end DivBoolean

end Freyd.Alg
