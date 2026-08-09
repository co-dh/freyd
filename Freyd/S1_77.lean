/-
  Freyd & Scedrov, *Categories, Allegories* §1.77–§1.78

  §1.77   TRANSITIVE CLOSURE R^t; TRANSITIVE-REFLEXIVE CLOSURE R*.
          Relations between R^t and R* in a pre-logos.
          TRANSITIVE (PRE-)LOGOS.
  §1.772  ω-TRANSITIVE LOGOS / ω-TRANSITIVE PRE-LOGOS.
  §1.775  EQUIVALENCE CLOSURE R^E; E-STANDARD pre-logos.
  §1.78   Relational quotient R/S (largest T with TS ⊑ R).
  §1.781  Set description of R/S.
  §1.782  R/f = Rf° (quotient by a map).
  §1.783  (R/S₁)/S₂ = R/(S₁S₂).
  §1.786  (R/S)(S/T) ⊑ R/T.
  §1.787  In a logos, R̄ = R* (closure via quotient equals transitive-reflexive closure).
-/

module

public import Freyd.S1_56
public import Freyd.S1_60
public import Freyd.S1_70
public import Freyd.S1_85

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.77 Transitive and transitive-reflexive closures -/

/-- An endo-relation R on A is TRANSITIVE if R ⊚ R ⊑ R (§1.77). -/
@[expose] public def IsTransitive [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (R ⊚ R) R

/-- An endo-relation R on A is REFLEXIVE if 1_A ⊑ R (§1.77). -/
@[expose] public def IsReflexive {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (graph (Cat.id A)) R

/-- TRANSITIVE CLOSURE R^t (§1.77): minimum transitive relation containing R.
    Existence is not guaranteed in every regular category. -/
structure TransClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  trans   : IsTransitive clos
  minimal : ∀ (T : BinRel 𝒞 A A), RelLe R T → IsTransitive T → RelLe clos T

/-- TRANSITIVE-REFLEXIVE CLOSURE R* (§1.77): minimum reflexive-transitive relation ⊇ R. -/
public structure TransRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  refl    : IsReflexive clos
  trans   : IsTransitive clos
  minimal : ∀ (T : BinRel 𝒞 A A), RelLe R T → IsReflexive T → IsTransitive T → RelLe clos T

/-! ## §1.77 R^t ⊑ R* when both exist -/

/-- §1.77: R^t ⊑ R* (transitive closure contained in transitive-reflexive closure). -/
theorem transClos_le_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (ht : TransClos R) (hr : TransRefClos R) :
    RelLe ht.clos hr.clos :=
  ht.minimal hr.clos hr.le hr.trans

/-! ## §1.77 Transitive (pre-)logos -/

/-- A TRANSITIVE PRE-LOGOS (§1.77): every endo-relation has a transitive closure. -/
class TransitivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends PreLogos 𝒞 where
  transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A), TransClos R

set_option linter.unusedVariables false in
/-- A TRANSITIVE LOGOS (§1.77): transitive pre-logos with right adjoint f##.
    We inline the logos axiom (f## existence) to avoid importing S1_70. -/
class TransitiveLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitivePreLogos 𝒞 where
  rightAdj  : ∀ {A B : 𝒞} (f : A ⟶ B), Subobject 𝒞 A → Subobject 𝒞 B
  adjunction : ∀ {A B : 𝒞} (f : A ⟶ B) (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A),
    Subobject.le (InverseImage f B') A' ↔ Subobject.le B' (rightAdj f A')

/-! ## §1.772 ω-Transitive logos / ω-transitive pre-logos -/

/-- Relational power R^n (diagram order): R^0 = 1_A, R^(n+1) = R^n ⊚ R. -/
def relPow [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat) : BinRel 𝒞 A A :=
  Nat.rec (graph (Cat.id A)) (fun _ rec => rec ⊚ R) n

theorem relPow_zero [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : relPow R 0 = graph (Cat.id A) := rfl

theorem relPow_succ [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat) : relPow R (n + 1) = relPow R n ⊚ R := rfl

/-- An ω-TRANSITIVE LOGOS (§1.772): transitive logos in which R^t is
    the least upper bound of the positive finite powers {R^n | n ≥ 1}. -/
class OmegaTransitiveLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitiveLogos 𝒞 where
  pow_le_transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat), 1 ≤ n →
    RelLe (relPow R n) (transClos R).clos
  transClos_le_of_pow_le : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (T : BinRel 𝒞 A A),
    (∀ n : Nat, 1 ≤ n → RelLe (relPow R n) T) → RelLe (transClos R).clos T

/-- An ω-TRANSITIVE PRE-LOGOS (§1.772): a transitive pre-logos in which, for every
    endo-relation R, R† is the **STABLE** least upper bound of the positive finite powers
    {R^n | n ≥ 1}.

    Book §1.772: "R† = ⋃ₙ₌₁^∞ Rⁿ AND the countable union in question is preserved under
    inverse images."  This is strictly stronger than the (logos) lub property: the lub must
    survive pullback along every map into the carrier `A × A`.  Book §1.772 spells out the exact
    infinitary Horn sentence for pre-logoi (line 507–508): given `R ⊂ B×B`, `f : A → B×B` and a
    subobject `A' ⊂ A`,
        (f#(R) ⊑ A') ∧ (f#(R²) ⊑ A') ∧ ⋯ ∧ (f#(Rⁿ) ⊑ A') ∧ ⋯   implies   f#(R†) ⊑ A'.
    `transClos_stable` below is exactly this clause, with `B×B = prod A A`, the carrier of the
    endo-relation.  The `f = 𝟙` instance recovers the plain (logos) lub, so this is the σ-transitive
    LOGOS condition pulled back along *every* `f` — the distinguishing "stable" requirement that the
    logos field (`transClos_le_of_pow_le`) lacks. -/
class OmegaTransitivePreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends TransitivePreLogos 𝒞 where
  pow_le_transClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (n : Nat), 1 ≤ n →
    RelLe (relPow R n) (transClos R).clos
  /-- STABLE least upper bound (book §1.772, lines 507–508): for every map `f : X ⟶ A × A` into the
      carrier and every subobject `A' ⊑ X`, if every positive finite power's inverse image `f#(Rⁿ)`
      lies under `A'`, then so does the inverse image `f#(R†)` of the transitive closure. -/
  transClos_stable : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) {X : 𝒞} (f : X ⟶ prod A A)
      (A' : Subobject 𝒞 X),
    (∀ n : Nat, 1 ≤ n → (InverseImage f (relSub (relPow R n))).le A') →
    (InverseImage f (relSub (transClos R).clos)).le A'

/-! ## §1.776 Representation theorems for σ-transitive categories

  "Every countable positive σ-transitive pre-logos is faithfully representable in a power of S."
  "Every countable positive σ-transitive logos is faithfully representable in H(X), where X may
   be taken as either the rationals or the irrationals."
  "Every countable E-standard bicartesian pre-topos is faithfully representable in a power of S."
  (Freyd §1.776, proofs in §1.777.)

  OPEN.  These are the top-level corollaries of §1.777 + §1.75 Stone representation.
  They require, in order:
  (a) §1.777's dense G_δ lemma (see below — itself OPEN for Stone/topological reasons),
  (b) The Stone representation theorem §1.754 (OPEN, see S1_75.lean),
  (c) A `CountableCategory` predicate and the atom-splitting step (§1.751 periodic-power
      reduction to the atomless case, OPEN — see S1_75.lean §1.751 block),
  (d) For the logos / H(X) variant: the topological fact that the rationals Q and the
      irrationals ℝ∖Q are homeomorphic to the Stone space of a countable atomless boolean
      algebra — requires metric topology not in repo,
  (e) For the E-standard pre-topos variant: equivalence-closure R^E preserves the
      `OmegaTransitivePreLogos` structure (§1.775 `EquivClos` is defined above but no
      preservation theorem is proven). -/

-- BOOK §1.776: Every countable positive σ-transitive pre-logos is faithfully representable
-- in a power of S.
-- OPEN: needs §1.777 + Stone repr (§1.754, OPEN) + countable-atomless reduction (§1.751, OPEN).
-- BOOK §1.776: Every countable positive σ-transitive logos is faithfully representable in
-- H(X), where X may be taken as either the rationals or the irrationals.
-- OPEN: additionally needs metric topology (Q ≅ Stone space of countable atomless boolean alg).
-- BOOK §1.776: Every countable E-standard bicartesian pre-topos is faithfully representable
-- in a power of S.
-- OPEN: additionally needs EquivClos preserves OmegaTransitivePreLogos structure.

/-! ## §1.777 Dense G-delta slice of the Stone space

  "Given a countable atomless positive capital (pre-)logos A and a countable family of stable
   unions therein, there exists a dense G_δ, Z, in the Stone-space B̂ (B the boolean algebra
   of complemented subterminators) such that A → H(Z) is faithful and preserves each of the
   stable unions in the given countable family."
  (Freyd §1.777; this is the key lemma behind §1.776.)

  OPEN.  Missing:
  1. `StoneSpace B` as a concrete type with a topology (S1_38.lean has only an opaque
     placeholder `StoneSpace : Type u` with no `Cat` or topological structure).
  2. The notion of a `GDeltaSet` (countable intersection of open sets) in the Stone space.
  3. The sheaf functor `A → H(Z)` for `Z ⊆ B̂` and the proof it is faithful and preserves
     the given countable family of stable unions.
  4. A `CapitalPreLogos` instance (§1.54 capitalization); `Capitalization.lean` closes this
     for the abstract setting but H(Z) is not known to be capital in the repo.
  This is a combination of the Stone-space infra wall (shared with §1.75) and the
  constructive-density argument (Baire category theorem / ω-tower of open sets). -/

-- BOOK §1.777: Given a countable atomless positive capital (pre-)logos A and a countable
-- family of stable unions therein, there exists a dense G_δ Z in B̂ (B = boolean algebra of
-- complemented subterminators) such that A → H(Z) is faithful and preserves each stable union.
-- OPEN: needs StoneSpace B̂ with topology, G_δ notion, sheaf functor A → H(Z), capital infra.

/-! ## §1.775 Equivalence closure R^E and E-standard pre-logos -/

/-- R is SYMMETRIC if R° ⊑ R. -/
@[expose] public def IsSymmetric {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  RelLe (R°) R

/-- R is an EQUIVALENCE RELATION: reflexive, symmetric, transitive. -/
@[expose] public def IsEquivRel [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : Prop :=
  IsReflexive R ∧ IsSymmetric R ∧ IsTransitive R

/-- EQUIVALENCE CLOSURE R^E (§1.775): minimum equivalence relation containing R. -/
public structure EquivClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  le      : RelLe R clos
  isEquiv : IsEquivRel clos
  minimal : ∀ (E : BinRel 𝒞 A A), RelLe R E → IsEquivRel E → RelLe clos E


/-- The reciprocal of the diagonal is the diagonal: graph(id) ⊑ (graph(id))°.
    Both have colA = colB = id, so the identity RelHom witnesses the containment. -/
public theorem graph_id_le_reciprocal {A : 𝒞} :
    RelLe (graph (Cat.id A)) ((graph (Cat.id A))°) :=
  ⟨⟨Cat.id _, by simp [graph, reciprocal, Cat.id_comp], by simp [graph, reciprocal, Cat.id_comp]⟩⟩

/-- §1.775: In a transitive pre-logos, R^E is constructible as (R ∪ R°)*.
    Stated: given a relation Rsym with R ⊑ Rsym, R° ⊑ Rsym, 1 ⊑ Rsym,
    and Rsym is symmetric, any TransRefClos of Rsym gives an EquivClos of R.
    `hJoin` records that Rsym is the JOIN of R, R° and 1 (its universal property as the
    symmetrisation), which is what makes the equivalence-closure minimality go through. -/
@[expose] public def equivClos_from_symm_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (Rsym : BinRel 𝒞 A A)
    (hR   : RelLe R Rsym)
    (hSym : IsSymmetric Rsym)
    (hJoin : ∀ (U : BinRel 𝒞 A A),
      RelLe R U → RelLe (R°) U → RelLe (graph (Cat.id A)) U → RelLe Rsym U)
    (hr   : TransRefClos Rsym) :
    EquivClos R where
  clos    := hr.clos
  le      := rel_le_trans hR hr.le
  isEquiv := ⟨hr.refl, by
    -- Rsym* is symmetric: (Rsym*)° ⊑ Rsym*.
    -- The candidate (Rsym*)° is itself reflexive, transitive and contains Rsym, so by
    -- minimality Rsym* ⊑ (Rsym*)°; reciprocate (and use involution) to flip the direction.
    have hle : RelLe hr.clos (hr.clos°) := by
      apply hr.minimal
      · -- Rsym ⊑ (Rsym*)°:  Rsym° ⊑ Rsym ⊑ Rsym*, reciprocate and use involution.
        have h1 : RelLe (Rsym°) hr.clos := rel_le_trans hSym hr.le
        have h2 : RelLe (Rsym°°) (hr.clos°) := reciprocal_mono h1
        rwa [reciprocal_invol] at h2
      · -- (Rsym*)° reflexive:  graph(id) ⊑ (graph(id))° ⊑ (Rsym*)°.
        exact rel_le_trans graph_id_le_reciprocal (reciprocal_mono hr.refl)
      · -- (Rsym*)° transitive:  (Rsym*)°(Rsym*)° ⊑ (Rsym* Rsym*)° ⊑ (Rsym*)°.
        exact rel_le_trans (comp_reciprocal_le hr.clos hr.clos) (reciprocal_mono hr.trans)
    have h3 : RelLe (hr.clos°) (hr.clos°°) := reciprocal_mono hle
    rwa [reciprocal_invol] at h3,
   hr.trans⟩
  minimal := by
    intro E hRE hEquiv
    apply hr.minimal
    · -- Rsym ⊑ E: R ⊑ E (hRE), R° ⊑ E (R ⊑ E reciprocated, E symmetric), 1 ⊑ E (E reflexive).
      apply hJoin
      · exact hRE
      · -- R° ⊑ E:  R° ⊑ E° ⊑ E  (E symmetric).
        exact rel_le_trans (reciprocal_mono hRE) hEquiv.2.1
      · exact hEquiv.1
    · exact hEquiv.1
    · exact hEquiv.2.2

/-- An E-STANDARD PRE-LOGOS (§1.775): every endo-relation R has an equivalence closure R≡,
    and R≡ is always the **STABLE** union of the finite powers of the symmetrisation `R° ∪ 1 ∪ R`.

    Book §1.775 (line 529): "R≡ is always the stable union of finite powers of `R° ∪ 1 ∪ R`."
    As in §1.772 (E-standardness is implied by σ-transitivity and shares its stability clause), the
    "stable" union must be preserved under inverse images.  `equivClos_stable` below is the §1.772
    Horn sentence (lines 507–508) transported to the equivalence closure: with the symmetrisation
    `Rsym` (pinned down by `R ⊑ Rsym`, `1 ⊑ Rsym`, `Rsym° ⊑ Rsym`), for every `f : X ⟶ A × A` and
    subobject `A' ⊑ X`, if every finite power's inverse image `f#(Rsymⁿ)` lies under `A'`, then so
    does `f#(R≡)`.  The `f = 𝟙` instance is the plain (non-stable) lub, so this strictly strengthens
    a bare PreLogos field. -/
class EStandardPreLogos (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    extends PreLogos 𝒞 where
  equivClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A), EquivClos R
  /-- STABLE union of finite powers of the symmetrisation (book §1.775 + §1.772 lines 507–508):
      for the symmetrisation `Rsym = R° ∪ 1 ∪ R`, every map `f : X ⟶ A × A` and subobject `A' ⊑ X`,
      if each `f#(Rsymⁿ)` lies under `A'` then so does `f#(R≡)`. -/
  equivClos_stable : ∀ {A : 𝒞} (R : BinRel 𝒞 A A) (Rsym : BinRel 𝒞 A A)
      {X : 𝒞} (f : X ⟶ prod A A) (A' : Subobject 𝒞 X),
    RelLe R Rsym → RelLe (graph (Cat.id A)) Rsym → RelLe (Rsym°) Rsym →
    (∀ n : Nat, (InverseImage f (relSub (relPow Rsym n))).le A') →
    (InverseImage f (relSub (equivClos R).clos)).le A'

/-! ## §1.78 Relational quotient R/S -/

/-- RELATIONAL QUOTIENT R/S (§1.78): given R : A → C and S : B → C,
    R/S is the maximum T : A → B with T ⊚ S ⊑ R.
    Universal property: T ⊑ R/S ↔ T ⊚ S ⊑ R. -/
public structure RelQuot [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (S : BinRel 𝒞 B C) where
  quot    : BinRel 𝒞 A B
  le      : RelLe (quot ⊚ S) R
  maximal : ∀ (T : BinRel 𝒞 A B), RelLe (T ⊚ S) R → RelLe T quot


/-- §1.78 universal property: T ⊑ R/S ↔ T ⊚ S ⊑ R. -/
public theorem relQuot_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A B C : 𝒞} {R : BinRel 𝒞 A C} {S : BinRel 𝒞 B C}
    (q : RelQuot R S) (T : BinRel 𝒞 A B) :
    RelLe T q.quot ↔ RelLe (T ⊚ S) R := by
  constructor
  · intro hT; exact rel_le_trans (compose_le_left hT S) q.le
  · exact q.maximal T

/-! ## §1.781 Set description

  In 𝒮et: x(R/S)y iff ∀z, ySz → xRz.
  This is exactly the categorical universal property (relQuot_iff):
  T ⊑ R/S ↔ TS ⊑ R. -/

/-! ## §1.782 R/f = R ⊚ f° -/

/-- §1.782: R/(graph f) is represented by R ⊚ (graph f)°.
    Proof: Tf ⊑ R ↔ T ⊑ Rf°, using simplicity (f°f ⊑ 1) and entireness (1 ⊑ ff°) of graph f.
    Requires composition associativity (regular category). -/
@[expose] public def relQuotByMap [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (f : B ⟶ C) : RelQuot R (graph f) where
  quot    := R ⊚ (graph f)°
  le      := by
    -- Goal: (R ⊚ (graph f)°) ⊚ (graph f) ⊑ R
    -- = R ⊚ ((graph f)° ⊚ (graph f)) ⊑ R ⊚ graph(id) ⊑ R
    -- via: assoc, simplicity of (graph f), right unit
    have h_assoc : RelLe ((R ⊚ (graph f)°) ⊚ graph f) (R ⊚ ((graph f)° ⊚ graph f)) :=
      compose_assoc R ((graph f)°) (graph f)
    -- Simple (graph f) : (graph f)° ⊚ (graph f) ⊑ graph(id_C) where C is target of graph f
    have h_simp_le : RelLe ((graph f)° ⊚ graph f) (graph (Cat.id C)) := (graph_is_map f).2
    have h_step2 : RelLe (R ⊚ ((graph f)° ⊚ graph f)) (R ⊚ graph (Cat.id C)) :=
      compose_le (rel_le_refl R) h_simp_le
    have h_unit : RelLe (R ⊚ graph (Cat.id C)) R := comp_graph_id R
    exact rel_le_trans (rel_le_trans h_assoc h_step2) h_unit
  maximal := by
    intro T hTf
    -- Goal: T ⊑ R ⊚ (graph f)°
    -- T ⊑ T ⊚ graph(id_B) ⊑ T ⊚ ((graph f) ⊚ (graph f)°)  [entireness]
    --   ⊑ (T ⊚ (graph f)) ⊚ (graph f)°                       [assoc']
    --   ⊑ R ⊚ (graph f)°                                       [hTf + monotone]
    -- Entire (graph f) : graph(id_B) ⊑ (graph f) ⊚ (graph f)°  (B = source of graph f)
    have h_ent_le : RelLe (graph (Cat.id B)) (graph f ⊚ (graph f)°) := (graph_is_map f).1
    have h_step1 : RelLe T (T ⊚ graph (Cat.id B)) := comp_graph_id_right T
    have h_step2 : RelLe (T ⊚ graph (Cat.id B)) (T ⊚ (graph f ⊚ (graph f)°)) :=
      compose_le (rel_le_refl T) h_ent_le
    have h_step3 : RelLe (T ⊚ (graph f ⊚ (graph f)°)) ((T ⊚ graph f) ⊚ (graph f)°) :=
      compose_assoc' T (graph f) ((graph f)°)
    have h_step4 : RelLe ((T ⊚ graph f) ⊚ (graph f)°) (R ⊚ (graph f)°) :=
      compose_le_left hTf ((graph f)°)
    exact rel_le_trans h_step1 (rel_le_trans h_step2 (rel_le_trans h_step3 h_step4))

/-- §1.782: T ⊑ R/(graph f) ↔ T ⊚ (graph f) ⊑ R. -/
theorem relQuot_map_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A C) (f : B ⟶ C) (T : BinRel 𝒞 A B) :
    RelLe T (relQuotByMap R f).quot ↔ RelLe (T ⊚ graph f) R :=
  relQuot_iff (relQuotByMap R f) T

/-! ## §1.784 In a logos, R/S exists for every pair of relations with a common target

  Freyd §1.784: "In a logos, R/S exists for every pair of relations with a common target."
  Since every relation `S = l° ⊚ r` factors through a span, R/S reduces to a quotient by a
  *reciprocal of a map*, and that quotient is the **double-sharp** `f##` of the right-adjoint
  to inverse image: `R/f° = (1 × f)##(R)`.  We construct `R/(graph f)°` directly as the
  subobject `Q = (prodMap A B C f)##(relSub R)`, read back as a relation `A → C`.

  The construction needs only `HasRightAdjointImage` (the `f##` adjoint, §1.70), not the full
  `Logos`; together with `PreLogos` for the `relSub`/`relLe_iff_subLe` bridge between relations
  and subobjects of the product. -/

/-- The §1.784 bridge: for `T : A → C` and a map `f : B → C`, the subobject of `A × B`
    represented by the relation `T ⊚ (graph f)°` is exactly the inverse image of `relSub T`
    along `prodMap A B C f : A × B → A × C` (mutual containment).
    This is the geometric content of `T ⊚ f° = (1 × f)#(T)`. -/
public theorem relSub_compRecip_eq_invImage [PreLogos 𝒞] [HasRightAdjointImage 𝒞]
    {A B C : 𝒞} (f : B ⟶ C) (T : BinRel 𝒞 A C) :
    (relSub (T ⊚ (graph f)°)).le (InverseImage (prodMap A B C f) (relSub T)) ∧
    (InverseImage (prodMap A B C f) (relSub T)).le (relSub (T ⊚ (graph f)°)) := by
  let pb := HasPullbacks.has T.colB f
  let span : pb.cone.pt ⟶ prod A B := pair (pb.cone.π₁ ≫ T.colA) (pb.cone.π₂ ≫ Cat.id B)
  have harr : (relSub (T ⊚ (graph f)°)).arr = (image span).arr := by
    dsimp [relSub, compose, reciprocal, graph, span]
    have pairEta : ∀ {X A' B' : 𝒞} (h : X ⟶ prod A' B'), h = pair (h ≫ fst) (h ≫ snd) :=
      fun h => pair_uniq (self := inferInstance) _ _ h rfl rfl
    rw [← pairEta]
  let pb3 := HasPullbacks.has (prodMap A B C f) (relSub T).arr
  refine ⟨?_, ?_⟩
  · -- relSub(T ⊚ f°) ≤ InverseImage(prodMap)(relSub T)
    have hle1 : (relSub (T ⊚ (graph f)°)).le (image span) :=
      ⟨Cat.id _, by rw [Cat.id_comp]; exact harr.symm⟩
    have hspan : span ≫ prodMap A B C f = pb.cone.π₁ ≫ (relSub T).arr := by
      apply fst_snd_jointly_monic (span ≫ prodMap A B C f) (pb.cone.π₁ ≫ (relSub T).arr)
      · rw [Cat.assoc, prodMap_fst]
        dsimp [span, relSub]; rw [fst_pair, Cat.assoc, fst_pair]
      · rw [Cat.assoc, prodMap_snd]
        dsimp [span, relSub]
        rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.comp_id]
        exact (pb.cone.w).symm
    let cone3 : Cone (prodMap A B C f) (relSub T).arr := ⟨pb.cone.pt, span, pb.cone.π₁, hspan⟩
    have hallow : Allows (InverseImage (prodMap A B C f) (relSub T)) span :=
      ⟨pb3.lift cone3, pb3.lift_fst cone3⟩
    have hle2 : (image span).le (InverseImage (prodMap A B C f) (relSub T)) :=
      image_min span _ hallow
    obtain ⟨h1, hh1⟩ := hle1; obtain ⟨h2, hh2⟩ := hle2
    exact ⟨h1 ≫ h2, by rw [Cat.assoc, hh2, hh1]⟩
  · -- InverseImage(prodMap)(relSub T) ≤ relSub(T ⊚ f°)
    have hle_img : (image span).le (relSub (T ⊚ (graph f)°)) :=
      ⟨Cat.id _, by rw [Cat.id_comp]; exact harr⟩
    have hsnd : pb3.cone.π₁ ≫ snd ≫ f = pb3.cone.π₂ ≫ T.colB := by
      have h2 : (pb3.cone.π₁ ≫ prodMap A B C f) ≫ snd = (pb3.cone.π₂ ≫ (relSub T).arr) ≫ snd :=
        congrArg (· ≫ snd) pb3.cone.w
      simp only [Cat.assoc, prodMap_snd] at h2
      dsimp [relSub] at h2
      simp only [snd_pair] at h2
      exact h2
    have hfst : pb3.cone.π₁ ≫ fst = pb3.cone.π₂ ≫ T.colA := by
      have h1 : (pb3.cone.π₁ ≫ prodMap A B C f) ≫ fst = (pb3.cone.π₂ ≫ (relSub T).arr) ≫ fst :=
        congrArg (· ≫ fst) pb3.cone.w
      simp only [Cat.assoc, prodMap_fst] at h1
      dsimp [relSub] at h1
      simp only [fst_pair] at h1
      exact h1
    let cone_pb : Cone T.colB f :=
      ⟨pb3.cone.pt, pb3.cone.π₂, pb3.cone.π₁ ≫ snd, by rw [Cat.assoc]; exact hsnd.symm⟩
    let lift3 : pb3.cone.pt ⟶ pb.cone.pt := pb.lift cone_pb
    have hlift : lift3 ≫ span = pb3.cone.π₁ := by
      apply fst_snd_jointly_monic (lift3 ≫ span) pb3.cone.π₁
      · dsimp [span]
        rw [Cat.assoc, fst_pair, ← Cat.assoc]
        rw [show lift3 ≫ pb.cone.π₁ = pb3.cone.π₂ from pb.lift_fst cone_pb]
        exact hfst.symm
      · dsimp [span]
        rw [Cat.assoc, snd_pair, Cat.comp_id]
        exact pb.lift_snd cone_pb
    obtain ⟨img_factor, himg⟩ := image_allows span
    have hle_inv : (InverseImage (prodMap A B C f) (relSub T)).le (image span) := by
      refine ⟨lift3 ≫ img_factor, ?_⟩
      show (lift3 ≫ img_factor) ≫ (image span).arr = pb3.cone.π₁
      rw [Cat.assoc, himg, hlift]
    obtain ⟨h1, hh1⟩ := hle_inv; obtain ⟨h2, hh2⟩ := hle_img
    exact ⟨h1 ≫ h2, by rw [Cat.assoc, hh2, hh1]⟩


/-- The relation `A → C` underlying `R/(graph f)°` (§1.784): the right-adjoint image
    `Q = (prodMap A B C f)##(relSub R)`, read back through the projections of `A × C`. -/
@[expose] public noncomputable def quotRecipRel [PreLogos 𝒞] [HasRightAdjointImage 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A B) (f : B ⟶ C) : BinRel 𝒞 A C :=
  let Q := HasRightAdjointImage.rightAdj (prodMap A B C f) (relSub R)
  { src := Q.dom
    colA := Q.arr ≫ fst
    colB := Q.arr ≫ snd
    isMonicPair := by
      apply monicPair_of_monic_pair
      rw [← pair_uniq (self := inferInstance) _ _ Q.arr rfl rfl]
      exact Q.monic }

/-- `relSub (quotRecipRel R f)` is the subobject `Q = (prodMap A B C f)##(relSub R)`:
    its representing arrow is `pair (Q.arr ≫ fst) (Q.arr ≫ snd) = Q.arr` (the eta law). -/
public theorem relSub_quotRecipRel_arr [PreLogos 𝒞] [HasRightAdjointImage 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A B) (f : B ⟶ C) :
    (relSub (quotRecipRel R f)).arr
      = (HasRightAdjointImage.rightAdj (prodMap A B C f) (relSub R)).arr := by
  dsimp [relSub, quotRecipRel]
  have pairEta : ∀ {X A' B' : 𝒞} (h : X ⟶ prod A' B'), h = pair (h ≫ fst) (h ≫ snd) :=
    fun h => pair_uniq (self := inferInstance) _ _ h rfl rfl
  rw [← pairEta]

/-- §1.784: in a logos (here: a pre-logos with the right-adjoint image `f##`), the relational
    quotient `R/(graph f)°` exists, for any relation `R : A → B` and map `f : B → C`.
    It is `(prodMap A B C f)##(relSub R)`, read back as a relation `A → C`. -/
@[expose] public noncomputable def relQuotByMapRecip [PreLogos 𝒞] [HasRightAdjointImage 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A B) (f : B ⟶ C) :
    RelQuot R ((graph f)°) where
  quot := quotRecipRel R f
  le := by
    -- relSub(quot ⊚ f°) ≤ InverseImage(prodMap)(relSub quot) ≤ relSub R.
    apply (relLe_iff_subLe _ _).2
    have hbridge := (relSub_compRecip_eq_invImage f (quotRecipRel R f)).1
    -- relSub quot ≤ Q, so by adjunction InverseImage(prodMap)(relSub quot) ≤ relSub R.
    have hquot_le_Q : (relSub (quotRecipRel R f)).le
        (HasRightAdjointImage.rightAdj (prodMap A B C f) (relSub R)) :=
      ⟨Cat.id _, by rw [Cat.id_comp]; exact (relSub_quotRecipRel_arr R f).symm⟩
    have hinv_le : (InverseImage (prodMap A B C f) (relSub (quotRecipRel R f))).le (relSub R) :=
      (HasRightAdjointImage.adjunction (prodMap A B C f) _ (relSub R)).2 hquot_le_Q
    obtain ⟨a, ha⟩ := hbridge; obtain ⟨b, hb⟩ := hinv_le
    exact ⟨a ≫ b, by rw [Cat.assoc, hb, ha]⟩
  maximal := by
    intro T hT
    -- InverseImage(prodMap)(relSub T) ≤ relSub(T ⊚ f°) ≤ relSub R, so relSub T ≤ Q.
    apply (relLe_iff_subLe _ _).2
    have hbridge := (relSub_compRecip_eq_invImage f T).2
    have hTfle : (relSub (T ⊚ (graph f)°)).le (relSub R) := subLe_of_relLe hT
    have hinv_le_R : (InverseImage (prodMap A B C f) (relSub T)).le (relSub R) := by
      obtain ⟨a, ha⟩ := hbridge; obtain ⟨b, hb⟩ := hTfle
      exact ⟨a ≫ b, by rw [Cat.assoc, hb, ha]⟩
    have hT_le_Q : (relSub T).le (HasRightAdjointImage.rightAdj (prodMap A B C f) (relSub R)) :=
      (HasRightAdjointImage.adjunction (prodMap A B C f) (relSub T) (relSub R)).1 hinv_le_R
    -- Q ≤ relSub quot (reverse arr equality), so relSub T ≤ relSub quot.
    have hQ_le_quot : (HasRightAdjointImage.rightAdj (prodMap A B C f) (relSub R)).le
        (relSub (quotRecipRel R f)) :=
      ⟨Cat.id _, by rw [Cat.id_comp]; exact relSub_quotRecipRel_arr R f⟩
    obtain ⟨a, ha⟩ := hT_le_Q; obtain ⟨b, hb⟩ := hQ_le_quot
    exact ⟨a ≫ b, by rw [Cat.assoc, hb, ha]⟩

/-- §1.784: T ⊑ R/(graph f)° ↔ T ⊚ (graph f)° ⊑ R, for `R : A → B` and `f : B → C`. -/
theorem relQuotByMapRecip_iff [PreLogos 𝒞] [HasRightAdjointImage 𝒞]
    {A B C : 𝒞} (R : BinRel 𝒞 A B) (f : B ⟶ C) (T : BinRel 𝒞 A C) :
    RelLe T (relQuotByMapRecip R f).quot ↔ RelLe (T ⊚ (graph f)°) R :=
  relQuot_iff (relQuotByMapRecip R f) T

/-! ## §1.783 (R/S₁)/S₂ = R/(S₂ ⊚ S₁) -/

/-- §1.783: T ⊑ (R/S₁)/S₂ ↔ T ⊑ R/(S₂ ⊚ S₁).
    Book proof: T ⊑ (R/S₁)/S₂ ↔ TS₂ ⊑ R/S₁ ↔ TS₂S₁ ⊑ R ↔ T(S₂S₁) ⊑ R ↔ T ⊑ R/(S₂S₁). -/
theorem relQuot_assoc_iff [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C D : 𝒞}
    (R : BinRel 𝒞 A D) (S₁ : BinRel 𝒞 C D) (S₂ : BinRel 𝒞 B C)
    (q₁  : RelQuot R S₁)
    (q₂  : RelQuot q₁.quot S₂)
    (q₁₂ : RelQuot R (S₂ ⊚ S₁))
    (T : BinRel 𝒞 A B) :
    RelLe T q₂.quot ↔ RelLe T q₁₂.quot := by
  -- T ⊑ q₂.quot ↔ T ⊚ S₂ ⊑ q₁.quot ↔ (T ⊚ S₂) ⊚ S₁ ⊑ R
  -- T ⊑ q₁₂.quot ↔ T ⊚ (S₂ ⊚ S₁) ⊑ R
  -- These are equal by compose_assoc / compose_assoc'.
  constructor
  · intro h
    rw [relQuot_iff q₁₂]
    exact rel_le_trans (compose_assoc' T S₂ S₁) ((relQuot_iff q₁ _).mp ((relQuot_iff q₂ _).mp h))
  · intro h
    rw [relQuot_iff q₂, relQuot_iff q₁]
    exact rel_le_trans (compose_assoc T S₂ S₁) ((relQuot_iff q₁₂ _).mp h)

/-! ## §1.786 (R/S)(S/T) ⊑ R/T -/

/-- §1.786: (R/S) ⊚ (S/T) ⊑ R/T.
    Proof: ((R/S)(S/T)) ⊚ T ⊑ (R/S) ⊚ ((S/T) ⊚ T) ⊑ (R/S) ⊚ S ⊑ R. -/
theorem relQuot_comp_le [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A B C D : 𝒞}
    (R : BinRel 𝒞 A D) (S : BinRel 𝒞 B D) (T : BinRel 𝒞 C D)
    (qRS : RelQuot R S) (qST : RelQuot S T) (qRT : RelQuot R T) :
    RelLe (qRS.quot ⊚ qST.quot) qRT.quot := by
  apply qRT.maximal
  -- ((R/S) ⊚ (S/T)) ⊚ T ⊑ R.
  -- Step 1: ((R/S) ⊚ (S/T)) ⊚ T ⊑ (R/S) ⊚ ((S/T) ⊚ T)  [assoc]
  -- Step 2: (S/T) ⊚ T ⊑ S                                  [qST.le]
  -- Step 3: (R/S) ⊚ ((S/T) ⊚ T) ⊑ (R/S) ⊚ S              [monotone in right]
  -- Step 4: (R/S) ⊚ S ⊑ R                                   [qRS.le]
  have h1 : RelLe ((qRS.quot ⊚ qST.quot) ⊚ T) (qRS.quot ⊚ (qST.quot ⊚ T)) :=
    compose_assoc qRS.quot qST.quot T
  have h2 : RelLe (qRS.quot ⊚ (qST.quot ⊚ T)) (qRS.quot ⊚ S) :=
    compose_le (rel_le_refl qRS.quot) qST.le
  exact rel_le_trans h1 (rel_le_trans h2 qRS.le)

/-- §1.786: R/R is reflexive: graph(id) ⊑ R/R. -/
theorem relQuot_self_refl [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qRR : RelQuot R R) :
    IsReflexive qRR.quot := by
  apply qRR.maximal
  -- graph(id_A) ⊚ R ⊑ R: identity is a left unit for composition.
  exact graph_id_comp R

/-- §1.786: R/R is transitive: (R/R) ⊚ (R/R) ⊑ R/R. -/
theorem relQuot_self_trans [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qRR : RelQuot R R) :
    IsTransitive qRR.quot :=
  relQuot_comp_le R R R qRR qRR qRR

/-! ## §1.787 In a logos, R̄ = R* -/

/-- R̄ (§1.787): minimum reflexive S with R ⊚ S ⊑ S ("right-quotient closure"). -/
structure QuotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) where
  clos    : BinRel 𝒞 A A
  refl    : IsReflexive clos
  stable  : RelLe (R ⊚ clos) clos
  minimal : ∀ (S : BinRel 𝒞 A A), IsReflexive S → RelLe (R ⊚ S) S → RelLe clos S

/-- §1.787: R* satisfies R ⊚ R* ⊑ R*. -/
theorem transRefClos_stable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (hr : TransRefClos R) :
    RelLe (R ⊚ hr.clos) hr.clos :=
  -- R ⊚ R* ⊑ R* ⊚ R* ⊑ R* (using R ⊑ R* and R* transitivity)
  rel_le_trans (compose_le_left hr.le hr.clos) hr.trans

/-- §1.787: R̄ ⊑ R* (R* is reflexive and satisfies R ⊚ R* ⊑ R*). -/
theorem quotClos_le_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) :
    RelLe qBar.clos hr.clos :=
  qBar.minimal hr.clos hr.refl (transRefClos_stable R hr)

/-- §1.787: R ⊑ R̄ (R̄ contains R).
    R ⊑ R ⊚ graph(id) ⊑ R ⊚ R̄ ⊑ R̄ (using R̄ reflexive and qBar.stable). -/
theorem le_quotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (qBar : QuotClos R) :
    RelLe R qBar.clos :=
  rel_le_trans (comp_graph_id_right R)
    (rel_le_trans (compose_le (rel_le_refl R) qBar.refl) qBar.stable)

/-- §1.787: R* ⊑ R̄ — the reflexive-transitive closure is contained in the quotient closure.
    Book proof (§1.787, first half): with S = R̄ (reflexive, R·S ⊑ S), the self-quotient S/S
    is reflexive and transitive, and R ⊑ S/S (since R·S ⊑ S), so by minimality of R*,
    R* ⊑ S/S.  Hence R*·S ⊑ (S/S)·S ⊑ S, and R* = R*·1 ⊑ R*·S ⊑ S.
    Needs a RelQuot R̄ R̄ (self-quotient S/S; exists in a logos by §1.784) and assoc. -/
theorem transRefClos_le_quotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    RelLe hr.clos qBar.clos := by
  -- S := qBar.clos = R̄.  S/S := qSS.quot.
  -- R ⊑ S/S: by univ prop of S/S, need R ⊚ S ⊑ S — that is qBar.stable.
  have hR_le_SS : RelLe R qSS.quot := qSS.maximal R qBar.stable
  -- S/S is reflexive and transitive (§1.786).
  have hrefl_SS  : IsReflexive  qSS.quot := relQuot_self_refl  qBar.clos qSS
  have htrans_SS : IsTransitive qSS.quot := relQuot_self_trans qBar.clos qSS
  -- R* ⊑ S/S by minimality of R*.
  have hstar_le_SS : RelLe hr.clos qSS.quot :=
    hr.minimal qSS.quot hR_le_SS hrefl_SS htrans_SS
  -- R*·S ⊑ (S/S)·S ⊑ S.
  have hstarS_le_S : RelLe (hr.clos ⊚ qBar.clos) qBar.clos :=
    rel_le_trans (compose_le_left hstar_le_SS qBar.clos) qSS.le
  -- R* = R*·1 ⊑ R*·S ⊑ S  (S reflexive).
  exact rel_le_trans (comp_graph_id_right hr.clos)
    (rel_le_trans (compose_le (rel_le_refl hr.clos) qBar.refl) hstarS_le_S)

/-- §1.787: R̄ is transitive, proved *directly* from its own minimality (no prior R* needed).
    With S := R̄ and its self-quotient S/S (§1.784):
    · S/S is reflexive and transitive (§1.786);
    · R ⊑ S/S, because R⊚S ⊑ S (`qBar.stable`) is the universal property of S/S;
    · hence R⊚(S/S) ⊑ (S/S)⊚(S/S) ⊑ S/S, so S/S is reflexive with R⊚(S/S) ⊑ S/S;
    · by R̄'s minimality among such relations, S ⊑ S/S;
    · therefore S⊚S ⊑ (S/S)⊚S ⊑ S  (the last step is `qSS.le`). -/
theorem quotClos_self_transitive [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    IsTransitive qBar.clos := by
  -- S/S reflexive and transitive (§1.786).
  have hrefl_SS  : IsReflexive  qSS.quot := relQuot_self_refl  qBar.clos qSS
  have htrans_SS : IsTransitive qSS.quot := relQuot_self_trans qBar.clos qSS
  -- R ⊑ S/S, by the universal property of S/S and qBar.stable (R⊚S ⊑ S).
  have hR_le_SS : RelLe R qSS.quot := qSS.maximal R qBar.stable
  -- R⊚(S/S) ⊑ (S/S)⊚(S/S) ⊑ S/S.
  have hstable_SS : RelLe (R ⊚ qSS.quot) qSS.quot :=
    rel_le_trans (compose_le_left hR_le_SS qSS.quot) htrans_SS
  -- S ⊑ S/S by R̄'s minimality (S/S reflexive, R⊚(S/S) ⊑ S/S).
  have hS_le_SS : RelLe qBar.clos qSS.quot := qBar.minimal qSS.quot hrefl_SS hstable_SS
  -- S⊚S ⊑ (S/S)⊚S ⊑ S.
  exact rel_le_trans (compose_le_left hS_le_SS qBar.clos) qSS.le

/-- §1.787 main: R̄ = R* — the quotient closure and transitive-reflexive closure coincide.
    Needs the self-quotient R̄/R̄ (`qSS`), available in a logos by §1.784. -/
theorem quotClos_eq_transRefClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (hr : TransRefClos R) (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    RelLe qBar.clos hr.clos ∧ RelLe hr.clos qBar.clos :=
  ⟨quotClos_le_transRefClos R hr qBar, transRefClos_le_quotClos R hr qBar qSS⟩

/-! ## §1.787 / §1.947 Constructing R* from R̄ (the keystone bridge)

  KEYSTONE.  Downstream §1.84 (coequalizer in Rel), §1.947 (`topos_has_rtc`) and §1.64
  (`HasMinEquivContaining` via the equivalence closure) all need an *honest* `TransRefClos R`
  — the reflexive-transitive closure R* as a usable relation with its four properties (R ⊑ R*,
  reflexive, transitive, minimal).  Freyd never posits R* in a bare regular category; he
  *constructs* it.  §1.947's topos construction produces exactly the glb `⋂F` of all reflexive
  S with R⊚S ⊑ S — which is precisely `QuotClos R` (R̄).  This block closes the gap §1.787 leaves
  open: it manufactures a full `TransRefClos R` out of an R̄ together with the self-quotient R̄/R̄
  (a logos always has R̄/R̄ by §1.784).  No new axiom: every input is a structure Freyd's text
  supplies. -/

/-- §1.787 / §1.947 KEYSTONE: an R̄ (`QuotClos R`) together with its self-quotient R̄/R̄
    assembles into a genuine `TransRefClos R`.
    · `le`     : R ⊑ R̄                         (`le_quotClos`);
    · `refl`   : 1 ⊑ R̄                         (`qBar.refl`);
    · `trans`  : R̄⊚R̄ ⊑ R̄                       (`quotClos_self_transitive`);
    · `minimal`: any reflexive-transitive T ⊇ R has R⊚T ⊑ T⊚T ⊑ T (T transitive), so T is a
      reflexive S with R⊚S ⊑ S, and R̄'s minimality gives R̄ ⊑ T. -/
def transRefClos_of_quotClos [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (qBar : QuotClos R) (qSS : RelQuot qBar.clos qBar.clos) :
    TransRefClos R where
  clos    := qBar.clos
  le      := le_quotClos R qBar
  refl    := qBar.refl
  trans   := quotClos_self_transitive R qBar qSS
  minimal := by
    intro T hRT hReflT hTransT
    -- T reflexive, and R⊚T ⊑ T⊚T ⊑ T (R ⊑ T, T transitive); R̄'s minimality gives R̄ ⊑ T.
    have hStableT : RelLe (R ⊚ T) T := rel_le_trans (compose_le_left hRT T) hTransT
    exact qBar.minimal T hReflT hStableT

/-- §1.947 packaging: the topos construction yields `M = ⋂F`, the *greatest lower bound* of
    `{S | 1 ⊑ S ∧ R⊚S ⊑ S}`, together with the facts that M is itself reflexive and R⊚M ⊑ M.
    That is exactly a `QuotClos R`.  Feeding it (and a self-quotient M/M) to
    `transRefClos_of_quotClos` produces R*.  This is the reusable entry point for
    `topos_has_rtc` (§1.94/§1.95): build `M`, show it reflexive + preclosed + the glb, hand it
    here. -/
def transRefClos_of_glb_preclosed [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [PullbacksTransferCovers 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A)
    (M : BinRel 𝒞 A A)
    (hMrefl   : IsReflexive M)
    (hMstable : RelLe (R ⊚ M) M)
    (hMglb    : ∀ (S : BinRel 𝒞 A A), IsReflexive S → RelLe (R ⊚ S) S → RelLe M S)
    (qMM : RelQuot M M) :
    TransRefClos R :=
  transRefClos_of_quotClos R ⟨M, hMrefl, hMstable, hMglb⟩ qMM

/-! ## §1.77 / §1.947 HasReflTransClosure — the "has-R*" structure

  Freyd's transitive (pre-)logos posits the *transitive* closure R^t (`TransitivePreLogos`
  above).  In a pre-logos R^t and R* are interderivable (§1.77: R* = 1 ∪ R^t, R^t = R⊚R*), so
  a category that has all transitive closures has all reflexive-transitive closures.  This class
  records the latter directly, as the natural hypothesis for `topos_has_rtc` (§1.947) and the
  Rel-coequalizer descent (§1.84): every endo-relation has a reflexive-transitive closure. -/
public class HasReflTransClosure (𝒞 : Type u) [Cat.{v} 𝒞]
    [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] where
  transRefClos : ∀ {A : 𝒞} (R : BinRel 𝒞 A A), TransRefClos R

/-- `rtc R` — the reflexive-transitive closure relation, in a category that `HasReflTransClosure`. -/
@[expose] public def rtc [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasReflTransClosure 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : BinRel 𝒞 A A :=
  (HasReflTransClosure.transRefClos R).clos

/-- `R ⊑ rtc R`. -/
public theorem le_rtc [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasReflTransClosure 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : RelLe R (rtc R) :=
  (HasReflTransClosure.transRefClos R).le

/-- `rtc R` is transitive:  rtc R ⊚ rtc R ⊑ rtc R. -/
public theorem rtc_transitive [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasReflTransClosure 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) : IsTransitive (rtc R) :=
  (HasReflTransClosure.transRefClos R).trans

/-- Minimality:  rtc R is below every reflexive-transitive relation containing R. -/
public theorem rtc_minimal [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] [HasReflTransClosure 𝒞]
    {A : 𝒞} (R : BinRel 𝒞 A A) (T : BinRel 𝒞 A A)
    (hRT : RelLe R T) (hReflT : IsReflexive T) (hTransT : IsTransitive T) :
    RelLe (rtc R) T :=
  (HasReflTransClosure.transRefClos R).minimal T hRT hReflT hTransT

end Freyd
