/-
  Freyd & Scedrov, *Categories and Allegories* §2.155

  INDEPENDENCE OF THE MODULAR IDENTITY.

  Book (§2.155, verbatim): "Let B be the subcategory of Rel(S) defined by
  (A →R B) ∈ B iff either R = ∅ or both R and R° are entire.  B is not a
  suballegory of Rel(S): it is closed with respect to composition and
  reciprocation but not with respect to intersection.  Nonetheless, each
  hom-set of B is easily seen to be a semi-lattice.  All axioms for
  allegories hold except for the modular identity.

  B is tabular (a tabulation that works in Rel(S) works in B).  Hence the
  modular identity is not a consequence of tabularity.  Map(B) is not a
  regular category: it has equalizers and a terminator but it does not
  have products."

  We work at the plain binary-relation level: a Rel(S)-morphism A → B is a
  matrix `A → B → Prop`, composition is diagram-order relational composition
  (`xy` = first x then y), the identity is `Eq`, reciprocation is
  transposition.  The B-INTERSECTION — the semi-lattice meet of the hom-sets
  of B — is the pointwise intersection GUARDED by the proposition that it is
  bi-entire (`interB`); no decidability is needed because bi-entirety is
  upward closed, so any nonzero lower bound in B already forces the guard.
-/

import Freyd.S2_10

universe u

namespace Freyd.Alg

/-! ## §2.155 (i)  Relations of B: `∅` or bi-entire

  Relation-level layer: everything is proved for plain matrices
  `A → B → Prop` first; the hom-level statements below are thin wrappers. -/

/-- `R` and `R°` are both ENTIRE (§2.155): every `a` is related to some `b`
    and every `b` to some `a`.  (Named `BiEntire` to avoid clashing with the
    allegory-level `Entire` of §2.13.) -/
@[reducible] def BiEntire {A B : Type u} (R : A → B → Prop) : Prop :=
  (∀ a, ∃ b, R a b) ∧ (∀ b, ∃ a, R a b)

/-- Membership in B (§2.155): `R = ∅` or `R` is bi-entire. -/
@[reducible] def IsB {A B : Type u} (R : A → B → Prop) : Prop :=
  (∀ a b, ¬ R a b) ∨ BiEntire R

/-- Pointwise intersection — the intersection of Rel(S), which B is NOT
    closed under (§2.155). -/
@[reducible] def pInter {A B : Type u} (R S : A → B → Prop) : A → B → Prop :=
  fun a b => R a b ∧ S a b

/-- Diagram-order relational composition: `bComp R S a c` iff some `b` has
    `R a b` and `S b c` (first `R`, then `S`). -/
@[reducible] def bComp {A B C : Type u} (R : A → B → Prop) (S : B → C → Prop) :
    A → C → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

/-- Reciprocation (transposition): `R° b a` iff `R a b`. -/
@[reducible] def bRecip {A B : Type u} (R : A → B → Prop) : B → A → Prop :=
  fun b a => R a b

/-- The B-INTERSECTION: the pointwise intersection guarded by the (undecided)
    proposition that it is bi-entire.  If the guard holds this IS `R ∩ S`;
    otherwise it is `∅`.  This is the semi-lattice meet of the hom-sets of B
    (§2.155: "each hom-set of B is easily seen to be a semi-lattice"). -/
@[reducible] def interB {A B : Type u} (R S : A → B → Prop) : A → B → Prop :=
  fun a b => R a b ∧ S a b ∧ BiEntire (pInter R S)

/-- Bi-entirety is UPWARD CLOSED — the engine behind every guard argument. -/
theorem biEntire_mono {A B : Type u} {R S : A → B → Prop}
    (hsub : ∀ a b, R a b → S a b) (h : BiEntire R) : BiEntire S :=
  ⟨fun a => (h.1 a).elim fun b hb => ⟨b, hsub a b hb⟩,
   fun b => (h.2 b).elim fun a ha => ⟨a, hsub a b ha⟩⟩

/-- The identity relation is bi-entire. -/
theorem biEntire_eq {A : Type u} : BiEntire (Eq : A → A → Prop) :=
  ⟨fun a => ⟨a, rfl⟩, fun a => ⟨a, rfl⟩⟩

/-- Bi-entire relations compose to bi-entire relations. -/
theorem biEntire_comp {A B C : Type u} {R : A → B → Prop} {S : B → C → Prop}
    (hR : BiEntire R) (hS : BiEntire S) : BiEntire (bComp R S) :=
  ⟨fun a => (hR.1 a).elim fun b hb => (hS.1 b).elim fun c hc => ⟨c, b, hb, hc⟩,
   fun c => (hS.2 c).elim fun b hb => (hR.2 b).elim fun a ha => ⟨a, b, ha, hb⟩⟩

/-- A relation is bi-entire iff its reciprocal is (definitional swap). -/
theorem biEntire_recip {A B : Type u} {R : A → B → Prop} (h : BiEntire R) :
    BiEntire (bRecip R) :=
  ⟨h.2, h.1⟩

/-! ### Closure of B under the categorical structure (§2.155: "it is closed
  with respect to composition and reciprocation") -/

/-- B is closed under composition: bi-entire ∘ bi-entire is bi-entire, and
    anything composed with `∅` is `∅`. -/
theorem isB_comp {A B C : Type u} {R : A → B → Prop} {S : B → C → Prop}
    (hR : IsB R) (hS : IsB S) : IsB (bComp R S) := by
  rcases hR with hR | hR
  · exact Or.inl fun a c h => h.elim fun b hb => hR a b hb.1
  rcases hS with hS | hS
  · exact Or.inl fun a c h => h.elim fun b hb => hS b c hb.2
  · exact Or.inr (biEntire_comp hR hS)

/-- B is closed under reciprocation. -/
theorem isB_recip {A B : Type u} {R : A → B → Prop} (h : IsB R) : IsB (bRecip R) :=
  h.elim (fun he => Or.inl fun b a hba => he a b hba)
    (fun hb => Or.inr (biEntire_recip hb))

/-- The guarded intersection is in B: if the guard holds it IS the pointwise
    intersection (hence bi-entire); if not, it is `∅`. -/
theorem isB_interB {A B : Type u} (R S : A → B → Prop) : IsB (interB R S) :=
  (Classical.em (BiEntire (pInter R S))).elim
    (fun hg => Or.inr (biEntire_mono (fun _ _ h => ⟨h.1, h.2, hg⟩) hg))
    (fun hg => Or.inl fun _ _ h => hg h.2.2)

/-! ### `interB` is the greatest lower bound in B

  KEY LEMMA: since bi-entirety is upward closed, a NONZERO lower bound
  `T ∈ B` of `R` and `S` forces the pointwise intersection to be bi-entire —
  so the guard costs nothing on any nonzero lower bound. -/

/-- KEY LEMMA (upward closure): if `T ∈ B`, `T ⊆ R`, `T ⊆ S` and `T` is
    nonzero, then `R ∩ S` (pointwise) is bi-entire. -/
theorem guard_of_lowerBound {A B : Type u} {T R S : A → B → Prop} (hT : IsB T)
    (hTR : ∀ a b, T a b → R a b) (hTS : ∀ a b, T a b → S a b)
    {a : A} {b : B} (hab : T a b) : BiEntire (pInter R S) :=
  hT.elim (fun he => absurd hab (he a b))
    (fun hbe => biEntire_mono (fun x y h => ⟨hTR x y h, hTS x y h⟩) hbe)

/-- `interB R S` is a lower bound of `R`. -/
theorem interB_le_left {A B : Type u} (R S : A → B → Prop) :
    ∀ a b, interB R S a b → R a b := fun _ _ h => h.1

/-- `interB R S` is a lower bound of `S`. -/
theorem interB_le_right {A B : Type u} (R S : A → B → Prop) :
    ∀ a b, interB R S a b → S a b := fun _ _ h => h.2.1

/-- The B-order collapses to pointwise inclusion: for `X ∈ B`,
    `interB X Y = X` (i.e. `X ⊑ Y` in B) iff `X ⊆ Y` pointwise. -/
theorem interB_eq_left {A B : Type u} {X Y : A → B → Prop} (hX : IsB X)
    (hsub : ∀ a b, X a b → Y a b) (a : A) (b : B) : interB X Y a b ↔ X a b :=
  ⟨fun h => h.1, fun h => ⟨h, hsub a b h, guard_of_lowerBound hX (fun _ _ => id) hsub h⟩⟩

/-! ## §2.155 (ii)  The category B -/

/-- Objects of B: the objects of Rel(S), i.e. sets. -/
def BObj : Type (u + 1) := Type u

/-- View a set as an object of B. -/
abbrev BObj.of (A : Type u) : BObj.{u} := A

/-- Hom-sets of B (§2.155): relations that are `∅` or bi-entire. -/
def BHom (A B : Type u) : Type u := { R : A → B → Prop // IsB R }

/-- Hom extensionality: B-morphisms are equal iff pointwise equivalent. -/
theorem BHom.ext {A B : Type u} {R S : BHom A B} (h : ∀ a b, R.val a b ↔ S.val a b) :
    R = S :=
  Subtype.ext (funext fun a => funext fun b => propext (h a b))

/-- Pointwise reading of an equality of B-morphisms. -/
theorem BHom.congr {A B : Type u} {R S : BHom A B} (h : R = S) (a : A) (b : B) :
    R.val a b ↔ S.val a b := by rw [h]

/-- Identity of B: the identity relation. -/
@[reducible] def BHom.id (A : Type u) : BHom A A := ⟨Eq, Or.inr biEntire_eq⟩

/-- Composition of B (diagram order). -/
@[reducible] def BHom.comp {A B C : Type u} (R : BHom A B) (S : BHom B C) : BHom A C :=
  ⟨bComp R.val S.val, isB_comp R.property S.property⟩

/-- `1 ≫ R = R` at the relation level. -/
theorem bComp_eq_left {A B : Type u} (R : A → B → Prop) (a : A) (b : B) :
    bComp Eq R a b ↔ R a b :=
  ⟨fun h => by obtain ⟨x, rfl, hx⟩ := h; exact hx, fun h => ⟨a, rfl, h⟩⟩

/-- `R ≫ 1 = R` at the relation level. -/
theorem bComp_eq_right {A B : Type u} (R : A → B → Prop) (a : A) (b : B) :
    bComp R Eq a b ↔ R a b :=
  ⟨fun h => by obtain ⟨x, hx, rfl⟩ := h; exact hx, fun h => ⟨b, h, rfl⟩⟩

/-- Associativity of relational composition. -/
theorem bComp_assoc {A B C D : Type u} (R : A → B → Prop) (S : B → C → Prop)
    (T : C → D → Prop) (a : A) (d : D) :
    bComp (bComp R S) T a d ↔ bComp R (bComp S T) a d :=
  ⟨fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ => ⟨b, hab, c, hbc, hcd⟩,
   fun ⟨b, hab, c, hbc, hcd⟩ => ⟨c, ⟨b, hab, hbc⟩, hcd⟩⟩

/-- §2.155: B is a category ("the subcategory of Rel(S) defined by
    (A →R B) ∈ B iff either R = ∅ or both R and R° are entire"). -/
instance instCatB : Cat.{u, u + 1} BObj.{u} where
  Hom A B := BHom A B
  id A := BHom.id A
  comp R S := BHom.comp R S
  id_comp R := BHom.ext fun a b => bComp_eq_left R.val a b
  comp_id R := BHom.ext fun a b => bComp_eq_right R.val a b
  assoc R S T := BHom.ext fun a d => bComp_assoc R.val S.val T.val a d

/-- Reciprocation of B (typed at the `BObj` level so it composes with `≫`). -/
@[reducible] def BHom.recip {a b : BObj.{u}} (R : a ⟶ b) : b ⟶ a :=
  ⟨bRecip R.val, isB_recip R.property⟩

/-- The semi-lattice meet of the hom-sets of B. -/
@[reducible] def BHom.inter {a b : BObj.{u}} (R S : a ⟶ b) : a ⟶ b :=
  ⟨interB R.val S.val, isB_interB R.val S.val⟩

/-! ## §2.155 (iii)  B is NOT closed under the intersection of Rel(S)

  Witness: `wR : Two → Three` relates `e0↦e0, e1↦e1, e1↦e2`; `wS : Three → Two`
  relates `e0↦e0, e1↦e1, e2↦e0`.  Both `wR` and `wS°` are bi-entire, but the
  pointwise intersection `wR ∩ wS° = {(e0,e0),(e1,e1)}` misses `e2 : Three`,
  so it is entire but not CO-entire — and it is nonzero, so it is not in B. -/

/-- Two-element carrier for the §2.155 counterexamples. -/
inductive Two : Type where
  | e0 | e1

/-- Three-element carrier for the §2.155 counterexamples. -/
inductive Three : Type where
  | e0 | e1 | e2

/-- The relation `{(e0,e0), (e1,e1), (e1,e2)} : Two → Three`. -/
@[reducible] def wR : Two → Three → Prop := fun a b =>
  (a = .e0 ∧ b = .e0) ∨ (a = .e1 ∧ b = .e1) ∨ (a = .e1 ∧ b = .e2)

/-- The relation `{(e0,e0), (e1,e1), (e2,e0)} : Three → Two`. -/
@[reducible] def wS : Three → Two → Prop := fun b c =>
  (b = .e0 ∧ c = .e0) ∨ (b = .e1 ∧ c = .e1) ∨ (b = .e2 ∧ c = .e0)

theorem wR_biEntire : BiEntire wR :=
  ⟨fun a => match a with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
   fun b => match b with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | .e2 => ⟨.e1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩

theorem wS_biEntire : BiEntire wS :=
  ⟨fun b => match b with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | .e2 => ⟨.e0, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩,
   fun c => match c with
    | .e0 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩

/-- The pointwise intersection `wR ∩ wS°` is not bi-entire: nothing is related
    to `e2 : Three` (`wR · e2` forces `e1`, `wS e2 ·` forces `e0`). -/
theorem wRSo_not_biEntire : ¬ BiEntire (pInter wR (bRecip wS)) := fun h => by
  obtain ⟨a, hR, hS⟩ := h.2 Three.e2
  rcases hR with ⟨-, h0⟩ | ⟨-, h0⟩ | ⟨ha, -⟩
  · exact nomatch h0
  · exact nomatch h0
  · rcases hS with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ha'⟩
    · exact nomatch h0
    · exact nomatch h0
    · subst ha; exact nomatch ha'

/-- `wR ∩ wS°` is nonzero (it contains `(e0, e0)`) yet not bi-entire — so it
    is not in B. -/
theorem wRSo_not_isB : ¬ IsB (pInter wR (bRecip wS)) := fun h =>
  h.elim (fun he => he Two.e0 Three.e0 ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩)
    wRSo_not_biEntire

/-- §2.155: "B is not a suballegory of Rel(S): it is … not closed with respect
    to intersection."  Both `wR` and `wS°` are in B; their pointwise
    intersection is not. -/
theorem b_not_closed_inter :
    ∃ (A B : Type) (R S : A → B → Prop), IsB R ∧ IsB S ∧ ¬ IsB (pInter R S) :=
  ⟨Two, Three, wR, bRecip wS, Or.inr wR_biEntire,
   isB_recip (Or.inr wS_biEntire), wRSo_not_isB⟩

/-! ## §2.155 (iv)  Each hom-set of B is a semi-lattice

  `interB` is idempotent, commutative and associative on B-morphisms.
  Associativity rides on the upward-closure argument: both nestings are
  pointwise the triple intersection guarded by ITS bi-entirety (if an inner
  guard fails, the triple guard fails too, and both sides collapse to `∅`). -/

/-- Right-nested characterization: `R ∩ (S ∩ T)` is the guarded triple. -/
theorem interB_assoc_char {A B : Type u} (R S T : A → B → Prop) (a : A) (b : B) :
    interB R (interB S T) a b ↔
      (R a b ∧ S a b ∧ T a b) ∧ BiEntire (pInter R (pInter S T)) := by
  constructor
  · rintro ⟨hR, ⟨hS, hT, -⟩, gOut⟩
    exact ⟨⟨hR, hS, hT⟩, biEntire_mono (fun x y h => ⟨h.1, h.2.1, h.2.2.1⟩) gOut⟩
  · rintro ⟨⟨hR, hS, hT⟩, g3⟩
    have gST : BiEntire (pInter S T) := biEntire_mono (fun x y h => ⟨h.2.1, h.2.2⟩) g3
    exact ⟨hR, ⟨hS, hT, gST⟩, biEntire_mono (fun x y h => ⟨h.1, h.2.1, h.2.2, gST⟩) g3⟩

/-- Left-nested characterization: `(R ∩ S) ∩ T` is the same guarded triple. -/
theorem interB_assoc_char' {A B : Type u} (R S T : A → B → Prop) (a : A) (b : B) :
    interB (interB R S) T a b ↔
      (R a b ∧ S a b ∧ T a b) ∧ BiEntire (pInter R (pInter S T)) := by
  constructor
  · rintro ⟨⟨hR, hS, -⟩, hT, gOut⟩
    exact ⟨⟨hR, hS, hT⟩, biEntire_mono (fun x y h => ⟨h.1.1, h.1.2.1, h.2⟩) gOut⟩
  · rintro ⟨⟨hR, hS, hT⟩, g3⟩
    have gRS : BiEntire (pInter R S) := biEntire_mono (fun x y h => ⟨h.1, h.2.1⟩) g3
    exact ⟨⟨hR, hS, gRS⟩, hT, biEntire_mono (fun x y h => ⟨⟨h.1, h.2.1, gRS⟩, h.2.2⟩) g3⟩

/-- `R ∩ R = R` in B (`inter_idem` of §2.11): a nonzero point of `R` forces
    the guard because `R ∈ B` is then bi-entire. -/
theorem b_inter_idem {a b : BObj.{u}} (R : a ⟶ b) : BHom.inter R R = R :=
  BHom.ext fun _ _ =>
    ⟨fun h => h.1,
     fun h => ⟨h, h, guard_of_lowerBound R.property (fun _ _ => id) (fun _ _ => id) h⟩⟩

/-- `R ∩ S = S ∩ R` in B (`inter_comm` of §2.11). -/
theorem b_inter_comm {a b : BObj.{u}} (R S : a ⟶ b) :
    BHom.inter R S = BHom.inter S R :=
  BHom.ext fun _ _ =>
    ⟨fun h => ⟨h.2.1, h.1, biEntire_mono (fun _ _ hh => ⟨hh.2, hh.1⟩) h.2.2⟩,
     fun h => ⟨h.2.1, h.1, biEntire_mono (fun _ _ hh => ⟨hh.2, hh.1⟩) h.2.2⟩⟩

/-- `R ∩ (S ∩ T) = (R ∩ S) ∩ T` in B (`inter_assoc` of §2.11). -/
theorem b_inter_assoc {a b : BObj.{u}} (R S T : a ⟶ b) :
    BHom.inter R (BHom.inter S T) = BHom.inter (BHom.inter R S) T :=
  BHom.ext fun x y =>
    (interB_assoc_char R.val S.val T.val x y).trans
      (interB_assoc_char' R.val S.val T.val x y).symm

/-- Hom-level form of `interB_eq_left`: `X ∩ Y = X` (i.e. `X ⊑ Y` in the
    B-order) whenever `X ⊆ Y` pointwise. -/
theorem binter_eq_left {a b : BObj.{u}} {X Y : a ⟶ b}
    (hsub : ∀ p q, X.val p q → Y.val p q) : BHom.inter X Y = X :=
  BHom.ext fun p q => interB_eq_left X.property hsub p q

/-! ## §2.155 (v)  All allegory axioms hold in B except the modular identity

  The theorems below mirror, one for one, the fields of the `Allegory` class
  of §2.11 (`Freyd.S2_1`) with `interB` as the intersection — except
  `Allegory.modular`, which FAILS (next section).  No `Allegory` instance can
  therefore be declared for B. -/

/-- `(R°)° = R` in B (mirrors `Allegory.recip_recip`). -/
theorem b_recip_recip {a b : BObj.{u}} (R : a ⟶ b) :
    BHom.recip (BHom.recip R) = R :=
  BHom.ext fun _ _ => Iff.rfl

/-- `(R ≫ S)° = S° ≫ R°` in B (mirrors `Allegory.recip_comp`). -/
theorem b_recip_comp {a b c : BObj.{u}} (R : a ⟶ b) (S : b ⟶ c) :
    BHom.recip (R ≫ S) = BHom.recip S ≫ BHom.recip R :=
  BHom.ext fun _ _ =>
    ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h2, h1⟩ => ⟨y, h1, h2⟩⟩

/-- `(R ∩ S)° = R° ∩ S°` in B (mirrors `Allegory.recip_inter`): the guards
    transport because `pInter R° S°` IS `(pInter R S)°` definitionally. -/
theorem b_recip_inter {a b : BObj.{u}} (R S : a ⟶ b) :
    BHom.recip (BHom.inter R S) = BHom.inter (BHom.recip R) (BHom.recip S) :=
  BHom.ext fun _ _ =>
    ⟨fun h => ⟨h.1, h.2.1, biEntire_recip h.2.2⟩,
     fun h => ⟨h.1, h.2.1, biEntire_recip h.2.2⟩⟩

/-- SEMI-DISTRIBUTIVITY holds in B, relation level, in the exact equational
    shape of `Allegory.semidistrib` (§2.11):
    `R(S ∩ T) = RS ∩ R(S ∩ T) ∩ RT`.  Two-case analysis on the guard of
    `S ∩ T`; when it fails both sides collapse to `∅`, when it holds the
    composite `R ≫ (S ∩ T)` is itself bi-entire (or `R = ∅` kills both
    sides), so every outer guard is forced by upward closure. -/
theorem interB_semidistrib_pt {A B C : Type u} {r : A → B → Prop} {s t : B → C → Prop}
    (hr : IsB r) : ∀ (x : A) (z : C),
    bComp r (interB s t) x z ↔
      interB (interB (bComp r s) (bComp r (interB s t))) (bComp r t) x z := by
  by_cases hG : BiEntire (pInter s t)
  · -- guard of S ∩ T holds: interB s t is pointwise s ∩ t
    have hMval : ∀ y w, interB s t y w ↔ (s y w ∧ t y w) :=
      fun y w => ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hG⟩⟩
    rcases hr with hRe | hRbe
    · -- r = ∅: both sides are pointwise empty
      intro x z
      constructor
      · rintro ⟨y, hry, -⟩; exact absurd hry (hRe x y)
      · rintro ⟨⟨⟨y, hry, -⟩, -, -⟩, -, -⟩; exact absurd hry (hRe x y)
    · -- r bi-entire: L := r ≫ (s ∩ t) is bi-entire and forces all guards
      have hLBE : BiEntire (bComp r (interB s t)) := by
        refine biEntire_mono ?_ (biEntire_comp hRbe hG)
        rintro x z ⟨y, hry, hst⟩
        exact ⟨y, hry, (hMval y z).mpr hst⟩
      have hsubS : ∀ x z, bComp r (interB s t) x z → bComp r s x z := by
        rintro x z ⟨y, hry, hm⟩; exact ⟨y, hry, hm.1⟩
      have hsubT : ∀ x z, bComp r (interB s t) x z → bComp r t x z := by
        rintro x z ⟨y, hry, hm⟩; exact ⟨y, hry, hm.2.1⟩
      have g1 : BiEntire (pInter (bComp r s) (bComp r (interB s t))) :=
        biEntire_mono (fun x z h => ⟨hsubS x z h, h⟩) hLBE
      have hInner : ∀ x z,
          interB (bComp r s) (bComp r (interB s t)) x z ↔ bComp r (interB s t) x z :=
        fun x z => ⟨fun h => h.2.1, fun h => ⟨hsubS x z h, h, g1⟩⟩
      have g2 : BiEntire (pInter (interB (bComp r s) (bComp r (interB s t)))
          (bComp r t)) :=
        biEntire_mono (fun x z h => ⟨(hInner x z).mpr h, hsubT x z h⟩) hLBE
      intro x z
      exact ⟨fun h => ⟨(hInner x z).mpr h, hsubT x z h, g2⟩,
             fun h => (hInner x z).mp h.1⟩
  · -- guard of S ∩ T fails: interB s t = ∅ and both sides are pointwise empty
    intro x z
    constructor
    · rintro ⟨y, -, -, -, hg⟩; exact absurd hg hG
    · rintro ⟨⟨-, ⟨y, -, -, -, hg⟩, -⟩, -, -⟩; exact absurd hg hG

/-- §2.155/§2.11: SEMI-DISTRIBUTIVITY holds in B —
    `R ≫ (S ∩ T) = (R≫S ∩ R≫(S∩T)) ∩ R≫T`, mirroring `Allegory.semidistrib`
    exactly. -/
theorem b_semidistrib {a b c : BObj.{u}} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ BHom.inter S T =
      BHom.inter (BHom.inter (R ≫ S) (R ≫ BHom.inter S T)) (R ≫ T) :=
  BHom.ext fun x z => interB_semidistrib_pt R.property x z

/-! ## §2.155 (vi)  The MODULAR IDENTITY fails in B

  Witness (carriers `Two, Three, Two`): `R := wR`, `S := wS`, `T := 1`.
  `R ≫ S = {(e0,e0),(e1,e0),(e1,e1)} ⊇ 1` is bi-entire, so the left side
  `RS ∩ 1 = 1 ≠ ∅`.  But `1 ≫ S° = S°` and the pointwise `wR ∩ wS°` is the
  non-closure witness above — entire yet not co-entire — so its guard fails,
  `R ∩ (1 ≫ S°) = ∅` in B, and the right side collapses to `∅`. -/

/-- `wR` as a morphism of B. -/
def homR : BObj.of Two ⟶ BObj.of Three := ⟨wR, Or.inr wR_biEntire⟩

/-- `wS` as a morphism of B. -/
def homS : BObj.of Three ⟶ BObj.of Two := ⟨wS, Or.inr wS_biEntire⟩

/-- The guard of `(wR ≫ wS) ∩ 1` holds: the composite relates `e0↦e0` (via
    `e0`) and `e1↦e1` (via `e1`), so the pointwise intersection with the
    diagonal IS the diagonal — bi-entire. -/
theorem lhs_guard : BiEntire (pInter (bComp wR wS) (Eq : Two → Two → Prop)) :=
  ⟨fun a => match a with
    | .e0 => ⟨.e0, ⟨.e0, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
    | .e1 => ⟨.e1, ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, rfl⟩,
   fun b => match b with
    | .e0 => ⟨.e0, ⟨.e0, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
    | .e1 => ⟨.e1, ⟨.e1, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, rfl⟩⟩

/-- `pInter wR (1 ≫ wS°) ⊆ pInter wR wS°` (the composite with the identity
    changes nothing). -/
theorem eqComp_sub : ∀ a b, pInter wR (bComp Eq (bRecip wS)) a b →
    pInter wR (bRecip wS) a b :=
  fun _ _ h => ⟨h.1, by obtain ⟨x, rfl, hw⟩ := h.2; exact hw⟩

/-- The RIGHT side of the modular law is empty at `(e0, e0)`: any point of
    `(R ∩ 1≫S°) ≫ S` carries the guard of `pInter wR (1 ≫ wS°)`, which fails
    because `wR ∩ wS°` is not bi-entire. -/
theorem rhs_empty_at :
    ¬ interB (interB (bComp wR wS) Eq)
        (bComp (interB wR (bComp Eq (bRecip wS))) wS) Two.e0 Two.e0 := by
  rintro ⟨-, ⟨y, ⟨-, -, g⟩, -⟩, -⟩
  exact wRSo_not_biEntire (biEntire_mono eqComp_sub g)

/-- §2.155, concrete form: the modular law `RS ∩ T = (RS ∩ T) ∩ (R ∩ TS°)S`
    (the exact equational shape of `Allegory.modular`, §2.11) FAILS in B for
    `R := wR`, `S := wS`, `T := 1`. -/
theorem modular_fails_concrete :
    BHom.inter (homR ≫ homS) (Cat.id (BObj.of Two)) ≠
      BHom.inter (BHom.inter (homR ≫ homS) (Cat.id (BObj.of Two)))
        (BHom.inter homR (Cat.id (BObj.of Two) ≫ BHom.recip homS) ≫ homS) := by
  intro heq
  have hpt := congrFun (congrFun (congrArg Subtype.val heq) Two.e0) Two.e0
  have hL : (BHom.inter (homR ≫ homS) (Cat.id (BObj.of Two))).val Two.e0 Two.e0 :=
    ⟨⟨Three.e0, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩, rfl, lhs_guard⟩
  have hR' : (BHom.inter (BHom.inter (homR ≫ homS) (Cat.id (BObj.of Two)))
      (BHom.inter homR (Cat.id (BObj.of Two) ≫ BHom.recip homS) ≫ homS)).val
      Two.e0 Two.e0 := hpt ▸ hL
  exact rhs_empty_at hR'

/-- §2.155: "All axioms for allegories hold except for the modular identity"
    — and the modular identity indeed FAILS: B satisfies every other
    `Allegory` field (theorems above), but there are B-morphisms violating
    `Allegory.modular`.  Hence the modular identity is INDEPENDENT of the
    remaining allegory axioms. -/
theorem modular_fails :
    ∃ (a b c : BObj.{0}) (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c),
      BHom.inter (R ≫ S) T ≠
        BHom.inter (BHom.inter (R ≫ S) T) (BHom.inter R (T ≫ BHom.recip S) ≫ S) :=
  ⟨BObj.of Two, BObj.of Three, BObj.of Two, homR, homS, Cat.id (BObj.of Two),
   modular_fails_concrete⟩

/-! ## §2.155 (vii)  Maps of B

  ENTIRE, SIMPLE and MAP mirrored from §2.13 with `interB` as the
  intersection (`Entire R := dom R = 1` with `dom R = 1 ∩ RR°`;
  `Simple R := R°R ⊑ 1`, the B-order `X ⊑ Y := X ∩ Y = X` unfolded). -/

/-- ENTIRE in B (§2.13 shape): `1 ∩ f f° = 1`. -/
@[reducible] def BEntire {a b : BObj.{u}} (f : a ⟶ b) : Prop :=
  BHom.inter (Cat.id a) (f ≫ BHom.recip f) = Cat.id a

/-- SIMPLE in B (§2.13 shape): `f° f ⊑ 1` in the B-order, unfolded. -/
@[reducible] def BSimple {a b : BObj.{u}} (f : a ⟶ b) : Prop :=
  BHom.inter (BHom.recip f ≫ f) (Cat.id b) = BHom.recip f ≫ f

/-- MAP of B (§2.13): entire and simple. -/
@[reducible] def BMap {a b : BObj.{u}} (f : a ⟶ b) : Prop := BEntire f ∧ BSimple f

/-- `BEntire` is the usual totality: every point has an image.  (The B-order
    guard costs nothing: the diagonal is bi-entire.) -/
theorem bEntire_iff {a b : BObj.{u}} (f : a ⟶ b) :
    BEntire f ↔ ∀ x, ∃ y, f.val x y := by
  constructor
  · intro h x
    have hx : ∃ y, f.val x y ∧ f.val x y := ((BHom.congr h x x).mpr rfl).2.1
    exact hx.elim fun y hy => ⟨y, hy.1⟩
  · intro h
    exact binter_eq_left fun p q hpq => by
      have hpq' : p = q := hpq
      cases hpq'
      exact (h p).elim fun y hy => ⟨y, hy, hy⟩

/-- `BSimple` is the usual single-valuedness. -/
theorem bSimple_iff {a b : BObj.{u}} (f : a ⟶ b) :
    BSimple f ↔ ∀ x y y', f.val x y → f.val x y' → y = y' := by
  constructor
  · intro h x y y' hy hy'
    have hyy : (BHom.recip f ≫ f).val y y' := ⟨x, hy, hy'⟩
    exact ((BHom.congr h y y').mpr hyy).2.1
  · intro h
    exact binter_eq_left fun y y' hyy => by
      have hyy' : ∃ x, f.val x y ∧ f.val x y' := hyy
      exact hyy'.elim fun x hx => h x y y' hx.1 hx.2

/-- The identity is a map of B. -/
theorem bmap_id {a : BObj.{u}} : BMap (Cat.id a) :=
  ⟨(bEntire_iff _).mpr fun x => ⟨x, rfl⟩,
   (bSimple_iff _).mpr fun x y y' h h' => by
     have h1 : x = y := h
     have h2 : x = y' := h'
     exact h1 ▸ h2⟩

/-! ## §2.155 (viii)  B is TABULAR

  "B is tabular (a tabulation that works in Rel(S) works in B)."  The graph
  tabulation of `Φ` — apex `{p : A × B // Φ p.1 p.2}` with the two projection
  legs — lies in B: if `Φ = ∅` the apex is empty and both legs are the empty
  relation (in B); if `Φ` is bi-entire, `f` is co-entire because `Φ` is
  entire and `g` is co-entire because `Φ°` is. -/

/-- The tabulation apex: the graph of `Φ`. -/
def bTabApex {A B : Type u} (Φ : A → B → Prop) : Type u := { p : A × B // Φ p.1 p.2 }

/-- First leg of the tabulation (the projection to `A`, as a relation). -/
@[reducible] def tabF {A B : Type u} (Φ : A → B → Prop) : bTabApex Φ → A → Prop :=
  fun p a => p.val.1 = a

/-- Second leg of the tabulation (the projection to `B`, as a relation). -/
@[reducible] def tabG {A B : Type u} (Φ : A → B → Prop) : bTabApex Φ → B → Prop :=
  fun p b => p.val.2 = b

/-- The first leg is in B (empty when `Φ = ∅` — its domain is empty —
    bi-entire when `Φ` is). -/
theorem isB_tabF {A B : Type u} {Φ : A → B → Prop} (h : IsB Φ) : IsB (tabF Φ) :=
  h.elim (fun he => Or.inl fun p _ _ => he p.val.1 p.val.2 p.property)
    (fun hbe => Or.inr ⟨fun p => ⟨p.val.1, rfl⟩,
      fun x => (hbe.1 x).elim fun y hy => ⟨⟨(x, y), hy⟩, rfl⟩⟩)

/-- The second leg is in B. -/
theorem isB_tabG {A B : Type u} {Φ : A → B → Prop} (h : IsB Φ) : IsB (tabG Φ) :=
  h.elim (fun he => Or.inl fun p _ _ => he p.val.1 p.val.2 p.property)
    (fun hbe => Or.inr ⟨fun p => ⟨p.val.2, rfl⟩,
      fun y => (hbe.2 y).elim fun x hx => ⟨⟨(x, y), hx⟩, rfl⟩⟩)

/-- `f° ≫ g = Φ` at the relation level. -/
theorem tab_recip_comp_pt {A B : Type u} (Φ : A → B → Prop) (a : A) (b : B) :
    bComp (bRecip (tabF Φ)) (tabG Φ) a b ↔ Φ a b := by
  constructor
  · rintro ⟨p, hpa, hpb⟩
    rw [← hpa, ← hpb]
    exact p.property
  · intro h
    exact ⟨⟨(a, b), h⟩, rfl, rfl⟩

private theorem prodExt {α β : Type u} {x y : α × β} (h1 : x.1 = y.1)
    (h2 : x.2 = y.2) : x = y := by
  obtain ⟨xa, xb⟩ := x
  obtain ⟨ya, yb⟩ := y
  have h1' : xa = ya := h1
  have h2' : xb = yb := h2
  cases h1'; cases h2'; rfl

/-- The guard of `f≫f° ∩ g≫g°` holds: the pointwise intersection contains the
    diagonal of the apex. -/
theorem tab_guard {A B : Type u} (Φ : A → B → Prop) :
    BiEntire (pInter (bComp (tabF Φ) (bRecip (tabF Φ)))
      (bComp (tabG Φ) (bRecip (tabG Φ)))) :=
  ⟨fun p => ⟨p, ⟨p.val.1, rfl, rfl⟩, ⟨p.val.2, rfl, rfl⟩⟩,
   fun q => ⟨q, ⟨q.val.1, rfl, rfl⟩, ⟨q.val.2, rfl, rfl⟩⟩⟩

/-- `f≫f° ∩ g≫g° = 1` at the relation level: sharing both coordinates is
    equality on the graph. -/
theorem tab_inter_pt {A B : Type u} (Φ : A → B → Prop) (p q : bTabApex Φ) :
    interB (bComp (tabF Φ) (bRecip (tabF Φ))) (bComp (tabG Φ) (bRecip (tabG Φ))) p q
      ↔ p = q := by
  constructor
  · rintro ⟨⟨x, h1, h2⟩, ⟨y, h3, h4⟩, -⟩
    have h1' : p.val.1 = x := h1
    have h2' : q.val.1 = x := h2
    have h3' : p.val.2 = y := h3
    have h4' : q.val.2 = y := h4
    exact Subtype.ext (prodExt (h1'.trans h2'.symm) (h3'.trans h4'.symm))
  · rintro rfl
    exact ⟨⟨p.val.1, rfl, rfl⟩, ⟨p.val.2, rfl, rfl⟩, tab_guard Φ⟩

/-- The first tabulation leg as a morphism of B. -/
def tabFHom {a b : BObj.{u}} (Φ : a ⟶ b) : BObj.of (bTabApex Φ.val) ⟶ a :=
  ⟨tabF Φ.val, isB_tabF Φ.property⟩

/-- The second tabulation leg as a morphism of B. -/
def tabGHom {a b : BObj.{u}} (Φ : a ⟶ b) : BObj.of (bTabApex Φ.val) ⟶ b :=
  ⟨tabG Φ.val, isB_tabG Φ.property⟩

/-- The first leg is a map of B (it is a function; simplicity is automatic). -/
theorem tabF_bmap {a b : BObj.{u}} (Φ : a ⟶ b) : BMap (tabFHom Φ) :=
  ⟨(bEntire_iff _).mpr fun p => ⟨p.val.1, rfl⟩,
   (bSimple_iff _).mpr fun p x x' h h' => by
     have h1 : p.val.1 = x := h
     have h2 : p.val.1 = x' := h'
     exact h1 ▸ h2⟩

/-- The second leg is a map of B. -/
theorem tabG_bmap {a b : BObj.{u}} (Φ : a ⟶ b) : BMap (tabGHom Φ) :=
  ⟨(bEntire_iff _).mpr fun p => ⟨p.val.2, rfl⟩,
   (bSimple_iff _).mpr fun p y y' h h' => by
     have h1 : p.val.2 = y := h
     have h2 : p.val.2 = y' := h'
     exact h1 ▸ h2⟩

/-- §2.155: "B is tabular (a tabulation that works in Rel(S) works in B)."
    The graph tabulation of any B-morphism `Φ` lies in B and tabulates it, in
    the exact shape of `Tabulates` (§2.14): both legs are maps of B,
    `f° ≫ g = Φ`, and `f≫f° ∩ g≫g° = 1`.

    Combined with `modular_fails` above: THE MODULAR IDENTITY IS NOT A
    CONSEQUENCE OF TABULARITY. -/
theorem b_tabular {a b : BObj.{u}} (Φ : a ⟶ b) :
    BMap (tabFHom Φ) ∧ BMap (tabGHom Φ) ∧
      BHom.recip (tabFHom Φ) ≫ tabGHom Φ = Φ ∧
      BHom.inter (tabFHom Φ ≫ BHom.recip (tabFHom Φ))
        (tabGHom Φ ≫ BHom.recip (tabGHom Φ)) = Cat.id (BObj.of (bTabApex Φ.val)) :=
  ⟨tabF_bmap Φ, tabG_bmap Φ,
   BHom.ext fun x y => tab_recip_comp_pt Φ.val x y,
   BHom.ext fun p q => tab_inter_pt Φ.val p q⟩

/-! ## §2.155 (ix)  Map(B) is not a regular category

  "Map(B) is not a regular category: it has equalizers and a terminator but
  it does not have products."

  A map of B with nonempty source is a SURJECTIVE function (entire + simple
  + bi-entire), so Map(B) is the category of sets and surjections (plus the
  empty maps out of `∅`).  We prove the terminator and the failure of
  products.

  On EQUALIZERS (book claim, recorded here without proof): cones are scarce —
  an equalizing map `t` with nonempty source is surjective, so `t ≫ f = t ≫ g`
  forces `f = g`.  Hence the equalizer of `f ≠ g` is `∅` (with the empty map,
  which every empty-source cone factors through uniquely), and the equalizer
  of `f = f` is the identity.  Formalizing this requires the case split
  `f = g ∨ f ≠ g` and is routine but lengthy; it is not needed for the
  headline (independence of the modular identity), so we stop at the
  terminator + no-products, which give "not regular" already. -/

/-- The total relation into the one-point set: bi-entire when the carrier is
    nonempty, empty (vacuously, out of an empty carrier) otherwise — in B
    either way. -/
def toTermHom (a : BObj.{u}) : a ⟶ BObj.of PUnit.{u + 1} :=
  ⟨fun _ _ => True,
   (Classical.em (Nonempty a)).elim
     (fun hne => Or.inr ⟨fun _ => ⟨PUnit.unit, trivial⟩,
       fun _ => hne.elim fun x => ⟨x, trivial⟩⟩)
     (fun hne => Or.inl fun x _ _ => hne ⟨x⟩)⟩

/-- The total relation to `PUnit` is a map of B. -/
theorem toTerm_bmap (a : BObj.{u}) : BMap (toTermHom a) :=
  ⟨(bEntire_iff _).mpr fun _ => ⟨PUnit.unit, trivial⟩,
   (bSimple_iff _).mpr fun _ _ _ _ _ => rfl⟩

/-- Any map of B into `PUnit` is the total relation (entirety fills every
    point; `PUnit` has only one). -/
theorem toTerm_unique {a : BObj.{u}} (f : a ⟶ BObj.of PUnit.{u + 1})
    (hf : BMap f) : f = toTermHom a :=
  BHom.ext fun x _ =>
    ⟨fun _ => trivial,
     fun _ => ((bEntire_iff f).mp hf.1 x).elim fun _ hy => hy⟩

/-- §2.155: Map(B) has a TERMINATOR — `PUnit` with the total relation. -/
theorem map_b_terminator (a : BObj.{u}) :
    BMap (toTermHom a) ∧ ∀ f : a ⟶ BObj.of PUnit.{u + 1}, BMap f → f = toTermHom a :=
  ⟨toTerm_bmap a, fun f hf => toTerm_unique f hf⟩

/-- The swap relation on `Two` — a map of B. -/
@[reducible] def wSwap : Two → Two → Prop := fun x y =>
  (x = .e0 ∧ y = .e1) ∨ (x = .e1 ∧ y = .e0)

theorem wSwap_biEntire : BiEntire wSwap :=
  ⟨fun x => match x with
    | .e0 => ⟨.e1, Or.inl ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e0, Or.inr ⟨rfl, rfl⟩⟩,
   fun y => match y with
    | .e0 => ⟨.e1, Or.inr ⟨rfl, rfl⟩⟩
    | .e1 => ⟨.e0, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- `wSwap` as a morphism of B. -/
def swapHom : BObj.of Two ⟶ BObj.of Two := ⟨wSwap, Or.inr wSwap_biEntire⟩

theorem swap_bmap : BMap swapHom :=
  ⟨(bEntire_iff _).mpr wSwap_biEntire.1,
   (bSimple_iff _).mpr fun x y y' h h' => by
     rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
     · rcases h' with ⟨-, rfl⟩ | ⟨h0, -⟩
       · rfl
       · exact nomatch h0
     · rcases h' with ⟨h0, -⟩ | ⟨-, rfl⟩
       · exact nomatch h0
       · rfl⟩

/-- §2.155: Map(B) does NOT have products.  Even MERE PAIRINGS (no uniqueness
    required) fail for the cones `(1, 1)` and `(1, swap)` over `Two, Two`:
    the pairing `h₂` of `(1, swap)` yields a vertex point `w₀` with
    `p w₀ = e0` and `q w₀ = e1`; the pairing `h₁` of `(1, 1)` is a map of B,
    hence SURJECTIVE onto the vertex (bi-entirety is forced), so `w₀ = h₁ x`
    for some `x` — giving `x = e0` (via `p`) and `x = e1` (via `q`).
    Contradiction.  This is where B bites: in Set the pairing need not be
    surjective, but in B every nonzero map is. -/
theorem map_b_no_products :
    ¬ ∃ (w : BObj.{0}) (p : w ⟶ BObj.of Two) (q : w ⟶ BObj.of Two),
      BMap p ∧ BMap q ∧
        ∀ (t : BObj.{0}) (f : t ⟶ BObj.of Two) (g : t ⟶ BObj.of Two),
          BMap f → BMap g →
            ∃ h : t ⟶ w, BMap h ∧ h ≫ p = f ∧ h ≫ q = g := by
  rintro ⟨w, p, q, -, -, huniv⟩
  obtain ⟨h₁, hm₁, hp₁, hq₁⟩ :=
    huniv (BObj.of Two) (Cat.id _) (Cat.id _) bmap_id bmap_id
  obtain ⟨h₂, hm₂, hp₂, hq₂⟩ :=
    huniv (BObj.of Two) (Cat.id _) swapHom bmap_id swap_bmap
  -- from h₂: a vertex point w₀ with `p w₀ e0` and `q w₀ e1`
  have hex : ∃ v, h₂.val Two.e0 v ∧ p.val v Two.e0 :=
    (BHom.congr hp₂ Two.e0 Two.e0).mpr rfl
  obtain ⟨w₀, hw₀, hpw₀⟩ := hex
  have hex' : ∃ v, h₂.val Two.e0 v ∧ q.val v Two.e1 :=
    (BHom.congr hq₂ Two.e0 Two.e1).mpr (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨w₁, hw₁, hqw₁⟩ := hex'
  have hw01 : w₀ = w₁ := (bSimple_iff h₂).mp hm₂.2 Two.e0 w₀ w₁ hw₀ hw₁
  subst hw01
  -- h₁ is entire hence nonzero, hence bi-entire: it hits w₀ from some x
  obtain ⟨y0, hy0⟩ := (bEntire_iff h₁).mp hm₁.1 Two.e0
  have hbe : BiEntire h₁.val := h₁.property.elim
    (fun he => absurd hy0 (he Two.e0 y0)) id
  obtain ⟨x, hxw⟩ := hbe.2 w₀
  -- transfer along the two commutativities: x = e0 and x = e1
  have hx0 : x = Two.e0 := (BHom.congr hp₁ x Two.e0).mp ⟨w₀, hxw, hpw₀⟩
  have hx1 : x = Two.e1 := (BHom.congr hq₁ x Two.e1).mp ⟨w₀, hxw, hqw₁⟩
  subst hx0
  exact nomatch hx1

end Freyd.Alg
