/-
  Bird & de Moor §7.1-7.2 in the set model: `Λ`, `est` and `E` read pointwise, and `+`
  distributes over `≤`.

  `AOP.A7_2` states `Distributes` abstractly and proves Theorem 7.1 from it.  The INSTANCE the
  book reads the definition by — the minimum of a sum is the sum of the minima — is a concrete
  construction, so it needs a concrete allegory and lives here rather than dragging the §6.1 set
  model into the abstract §7.2 module.

  This is also the earliest module in which `est` (§7.1) and `Rel(Set)` (§6.1) meet, so the
  pointwise readings of `Λ`, `est` and `E` are proved here once; §7.4's Horner example and every
  later case study read them from here rather than each carrying its own.
-/
module

public import AOP.A6_1_OrdRelSet
public import AOP.A7_2

namespace Freyd.Alg.RelSet

/-! ## Concrete Rel(Set) helpers: `Λ` is the classifier, and `est` pointwise -/

/-- In Rel(Set) the transpose `Λ` is the concrete `classifier` (graph of `x ↦ {y | R x y}`):
    both are maps whose composition with `∋` is `R`, and that map is unique. -/
public theorem Λ_eq_classifier {B C : RelSet.{0}} (R : C ⟶ B) : Λ R = classifier R :=
  ((Λ_UP R (f := classifier R) (graph_map _)).mpr (classifier_comp_eps R)).symm

/-- Pointwise form of `est` in Rel(Set): `w` is a `est R`-choice of the set `P` iff
    `w ∈ P` and `w` `R`-dominates every member `z ∈ P` (`R w z`). -/
public theorem est_apply {A : RelSet.{0}} (R : A ⟶ A)
    (P : (PowerAllegory.powerObj A).carrier) (w : A.carrier) :
    (est R) P w ↔ P w ∧ ∀ z, P z → R w z := Iff.rfl

/-- Pointwise form of `Λ T ≫ est R` ((7.5) unbundled): `w` is an `est R`-choice over the
    `T`-image of `x` iff `T x w` and `w` `R`-dominates every `T`-image `z` of `x`. -/
public theorem Λ_comp_est_apply {B A : RelSet.{0}} (T : B ⟶ A) (R : A ⟶ A) (x : B.carrier)
    (w : A.carrier) : (Λ T ≫ est R) x w ↔ T x w ∧ ∀ z, T x z → R w z := by
  rw [Λ_eq_classifier]
  constructor
  · rintro ⟨P, hP, hest⟩
    have hPeq : P = fun v => T x v := hP
    subst hPeq
    exact (est_apply R _ w).mp hest
  · rintro ⟨hT, hall⟩
    exact ⟨fun v => T x v, rfl, (est_apply R _ w).mpr ⟨hT, hall⟩⟩

/-- Pointwise form of `E R` in Rel(Set): the `E R`-image of a set `P` is the set of all
    `R`-images of its members. -/
public theorem existsImage_apply {A B : RelSet.{0}} (R : A ⟶ B) (P : (pow A).carrier)
    (Q : (pow B).carrier) : existsImage R P Q ↔ Q = fun w => ∃ s, P s ∧ R s w := by
  show Λ (epsRel A ≫ R) P Q ↔ _
  rw [Λ_eq_classifier]
  exact Iff.rfl

/-- The pointwise readings of the three relations between subsets that `P(R)` and `E(R)` are
    built from: every member of `Q` is reached, every reached element is in `Q`, every member of
    `P` reaches into `Q`. -/
public theorem powrel_readings {A B : RelSet.{0}} (R : A ⟶ B) (P : (pow A).carrier)
    (Q : (pow B).carrier) :
    (((∋ A ≫ R) / ∋ B) P Q ↔ ∀ w, Q w → ∃ s, P s ∧ R s w) ∧
    ((∋ B / (∋ A ≫ R))° P Q ↔ ∀ w, (∃ s, P s ∧ R s w) → Q w) ∧
    (((∋ B ≫ R°) / ∋ A)° P Q ↔ ∀ s, P s → ∃ w, Q w ∧ R s w) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Pointwise form of `E T ≫ est R`: `w` is an `est R`-choice over the `T`-images of the members
    of `P` iff some member has `w` as a `T`-image and `w` `R`-dominates every such image. -/
public theorem existsImage_comp_est_apply {A B : RelSet.{0}} (T : A ⟶ B) (R : B ⟶ B)
    (P : (pow A).carrier) (w : B.carrier) :
    (existsImage T ≫ est R) P w
      ↔ (∃ s, P s ∧ T s w) ∧ ∀ z, (∃ s, P s ∧ T s z) → R w z := by
  constructor
  · rintro ⟨Q, hQ, hest⟩
    have hQeq : Q = fun v => ∃ s, P s ∧ T s v := (existsImage_apply T P Q).mp hQ
    subst hQeq
    exact (est_apply R _ w).mp hest
  · intro h
    exact ⟨_, (existsImage_apply T P _).mpr rfl, (est_apply R _ w).mpr h⟩

/-- **(7.9)**, `R` reflexive: `P(S) est(R) = (∋S)∩(∈\(SR°))`.  `⊑` is `powerRel_comp_est_le`; `⊒`
    needs the set `y` the right-hand side only describes, which the set model has: the `S`-images
    of `X` that `a` `R`-dominates, `a` among them because `R` is reflexive. -/
public theorem powerRel_comp_est {B A : RelSet.{0}} (S : B ⟶ A) (R : A ⟶ A) (hrefl : 𝟙 A ⊑ R) :
    powerRel S ≫ est R = (∋ B ≫ S) ∩ (((∋ B)°) \ (S ≫ R°)) := by
  refine le_antisymm (powerRel_comp_est_le S R) (le_iff.mpr ?_)
  rintro X a ⟨⟨b, hb, hSb⟩, hdiv⟩
  refine ⟨fun a' => (∃ b, X b ∧ S b a') ∧ R a a',
    ⟨fun b' hb' => ?_, fun a' ha' => ha'.1⟩, ⟨⟨b, hb, hSb⟩, le_iff.mp hrefl a a rfl⟩, fun _ hz => hz.2⟩
  obtain ⟨a', hS', hR'⟩ := hdiv b' hb'
  exact ⟨a', hS', ⟨b', hb', hS'⟩, hR'⟩

/-! ## Honest headline: a deterministic solver IS `Λspec ≫ est D`

  This is the bridge that lets an optimization case study state its headline as the actual
  morphism equation `solve = Λ spec ≫ est D` (§7.5's `max D · Λ spec`), instead of only in
  prose.  It consumes exactly the two halves the case study already proves — achievability
  (`hsound`) and domination (`hbest`) — plus antisymmetry of the preference order `D`, which
  pins the maximum uniquely so `solve` (a map) equals it. -/

/-- **Morphism-equation headline for a maximization solver.**  If `solveFn` always produces a
    `spec`-value (`hsound`) that `D`-dominates every `spec`-value (`hbest`), and the preference
    order `D` is antisymmetric, then `graph solveFn = Λ spec ≫ est D` — the program is exactly
    `max D · Λ spec` as a relation, not merely pointwise.  For a `≤`-maximum take `D w z := z ≤ w`;
    for a `≤`-minimum take `D w z := w ≤ z` (`est` of the reversed order). -/
public theorem eq_Λ_comp_est {d : RelSet.{0}} {V : Type} (D : (⟨V⟩ : RelSet.{0}) ⟶ ⟨V⟩)
    (hanti : ∀ x y : V, D x y → D y x → x = y)
    (solveFn : d.carrier → V) (spec : d ⟶ (⟨V⟩ : RelSet.{0}))
    (hsound : ∀ xs, spec xs (solveFn xs))
    (hbest : ∀ xs v, spec xs v → D (solveFn xs) v) :
    (graph solveFn : d ⟶ (⟨V⟩ : RelSet.{0})) = Λ spec ≫ est D := by
  apply hom_ext; intro xs w
  rw [comp_apply]
  constructor
  · intro hw
    have hwe : w = solveFn xs := hw
    subst hwe
    refine ⟨fun v => spec xs v, ?_, (est_apply D _ _).mpr ⟨hsound xs, hbest xs⟩⟩
    rw [Λ_eq_classifier]; rfl
  · rintro ⟨P, hAP, hmax⟩
    rw [Λ_eq_classifier] at hAP
    have hPeq : P = fun v => spec xs v := hAP
    subst hPeq
    obtain ⟨hmem, hdomw⟩ := (est_apply D _ _).mp hmax
    exact hanti w (solveFn xs) (hdomw (solveFn xs) (hsound xs)) (hbest xs w hmem)

/-! ## §7.2's instance: `+` distributes over `≤` -/

/-- Addition as an arrow `Nat×Nat ⟶ Nat` of `Rel(Set)`, the algebra of the relator `Δ`. -/
@[expose] public def plusRel : (Δ RelSet.{0}).obj (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  -- `Nat.add`/`Nat.le` and not `+`/`≤`: the `binop%` elaborator reads the OPERANDS' types, and a
  -- component of the relator's object is one only up to unfolding, where the instance search stops.
  fun p n => Nat.add p.1 p.2 = n

/-- The order `≤` on `Nat` as an endorelation, the `R` of `est R`. -/
@[expose] public def leRel : (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) := fun x y => Nat.le x y

/-- `{x+y ∣ x ∈ xs ∧ y ∈ ys}` — the set the square's top edge carries `(xs,ys)` to.  Named rather
    than written out at the corner it labels: the picture sets a corner's value in one line. -/
@[expose] public def sums (xs ys : (pow (⟨Nat⟩ : RelSet.{0})).carrier) :
    (pow (⟨Nat⟩ : RelSet.{0})).carrier := fun n => ∃ x y, xs x ∧ ys y ∧ Nat.add x y = n

/-- `min(xs)` — the least member of `xs`, the point `est(≤)` sends `xs` to; `xs` stays explicit
    because it is what the printed corner shows.  The witness is a binder, not `Classical.choose`:
    a set of naturals is `Nat → Prop`, nothing computes its least member, and the statement is about
    sets that have one. -/
@[expose] public def minOf (xs : (pow (⟨Nat⟩ : RelSet.{0})).carrier)
    (m : {a // est leRel xs a}) : Nat := m.val

/-- **`+` distributes over `≤`** — `Distributes` (§7.2) at `Rel(Set)`'s `+` and `est(≤)`: the
    smallest sum of a member of `xs` and a member of `ys` is the sum of the smallest of each.

    The four points are the square's corners read at `(xs,ys)`: they say what the picture writes
    under each object, and they are hypotheses because the terms are of this statement's own
    context — `(xs,ys)` names binders of it — where an attribute is elaborated outside it. -/
public theorem plus_distributes_le
    {xs ys : (pow (⟨Nat⟩ : RelSet.{0})).carrier}
    (mx : {a // est leRel xs a}) (my : {a // est leRel ys a})
    {fea : ((Δ RelSet.{0}).obj (pow (⟨Nat⟩ : RelSet.{0}))).carrier} (_hfea : fea = (xs, ys))
    {ea : (pow (⟨Nat⟩ : RelSet.{0})).carrier}
    (_hea : ea = sums xs ys)
    {fa : ((Δ RelSet.{0}).obj (⟨Nat⟩ : RelSet.{0})).carrier}
    (_hfa : fa = (minOf xs mx, minOf ys my))
    {c : Nat} (_hc : c = minOf xs mx + minOf ys my) :
    Distributes (F := Δ RelSet.{0}) plusRel leRel := by
  refine RelSet.le_iff.mpr ?_
  rintro p w ⟨q, hq, hw⟩
  obtain ⟨hq1, hq2⟩ := (delta_map_apply (est leRel) p q).mp hq
  obtain ⟨hm1, hd1⟩ := (est_apply leRel p.1 q.1).mp hq1
  obtain ⟨hm2, hd2⟩ := (est_apply leRel p.2 q.2).mp hq2
  refine (Λ_comp_est_apply _ leRel p w).mpr
    ⟨⟨q, (delta_map_apply (∋ (⟨Nat⟩ : RelSet.{0})) p q).mpr ⟨hm1, hm2⟩, hw⟩, ?_⟩
  rintro z ⟨r, hr, hz⟩
  obtain ⟨hr1, hr2⟩ := (delta_map_apply (∋ (⟨Nat⟩ : RelSet.{0})) p r).mp hr
  have hw' : Nat.add q.1 q.2 = w := hw
  have hz' : Nat.add r.1 r.2 = z := hz
  have h1 : Nat.le q.1 r.1 := hd1 r.1 hr1
  have h2 : Nat.le q.2 r.2 := hd2 r.2 hr2
  show Nat.le w z
  exact hw' ▸ hz' ▸ Nat.add_le_add h1 h2

end Freyd.Alg.RelSet
