/-
  Bird & de Moor, *Algebra of Programming* §5.6  Combinatorial functions (book pp. 125-132) —
  the list combinators, as concrete relations on `list A = ConsList Unit A` in the Set model.

  These are the relations the optimisation case studies (§6.6 sorting, §7.5 security van, §8.x
  thinning, …) take as their coalgebra / specification: `perm` (permutation), `prefix`/`suffix`,
  `subseq` (subsequence), `inlist` (membership).  Each combinator appears twice: as a concrete
  inductive/structural relation with the algebraic properties (reflexivity, symmetry, transitivity)
  the derivations use, and — in the point-free section at the end — as B&dM's own definition
  (`subseq = ⦇[nil, cons∪π₂]⦈`, `prefix = ⦇[nil, nil∪cons]⦈`, `suffix = cat° π₂`,
  `partition = concat°`, …), proved equal to the concrete relation, each catamorphism by one
  application of `relCata_UP`.  Arrows are mirrored to diagram order, so a combinator maps the
  WHOLE list (domain) to its parts: `prefixR x ys` reads "`ys` is a prefix of `x`", while the
  underlying predicate keeps B&dM's application order (`prefixP ys x` = "`ys` is a prefix of `x`").
  Built on the cons-list engine `AOP.A6_ConsList` (`list A = ConsList Unit A`).
-/
module

public import AOP.A6_ConsList

namespace Freyd.Alg.RelSet.ListRel

open Freyd Freyd.Alg.RelSet.CL

variable {A : Type}

/-- `list A = ConsList Unit A` (`nil = wrap ()`, `cons a x`). -/
@[expose] public abbrev dList (A : Type) : RelSet.{0} := dCL Unit A

/-! ## Membership `inlist : A ← list A` and `setify : E A ← list A` -/

/-- `a ∈ x`. -/
@[expose] public def inlistP : ConsList Unit A → A → Prop
  | ConsList.wrap _, _ => False
  | ConsList.cons b x, a => a = b ∨ inlistP x a

/-- The membership relation `inlist : list A ⟶ A`. -/
def inlist : dList A ⟶ dE A := inlistP

/-- **`setify[a₁,…,aₙ] = {a₁,…,aₙ}`** (B&dM §7.3 p.177), `setify : [A]⟶E(A)`: a list goes to the
    set of its elements, so the order and the repetitions are forgotten.  It is the classifier of
    `inlist` — `Λ(inlist)`, `graph` of `x ↦ {a | a ∈ x}`, hence a MAP by `graph_map`, since a list
    has exactly one element set.  `AOP.A7_4_CylinderBeads`'s `Tuple.setify` is the §7.4 arrow of the
    same name at the tuple relator, `Aⁿ⟶E(A)`, forgetting which row a component came from; the
    two are different arrows and neither is an instance of the other. -/
@[expose] public def setify : dList A ⟶ PowerAllegory.powerObj (dE A) := graph inlistP

/-! ## Permutation `perm : list A ← list A` -/

/-- The permutation relation, inductively (equivalent to B&dM's `⦇[nil, perm·cons]⦈`): `y` is a
    rearrangement of `x`. -/
public inductive Perm : ConsList Unit A → ConsList Unit A → Prop
  | nil : Perm (ConsList.wrap ()) (ConsList.wrap ())
  | cons (a : A) {x y : ConsList Unit A} : Perm x y → Perm (ConsList.cons a x) (ConsList.cons a y)
  | swap (a b : A) (x : ConsList Unit A) :
      Perm (ConsList.cons a (ConsList.cons b x)) (ConsList.cons b (ConsList.cons a x))
  | trans {x y z : ConsList Unit A} : Perm x y → Perm y z → Perm x z

public theorem Perm.refl : ∀ x : ConsList Unit A, Perm x x
  | ConsList.wrap () => Perm.nil
  | ConsList.cons a x => Perm.cons a (Perm.refl x)

public theorem Perm.symm : ∀ {x y : ConsList Unit A}, Perm x y → Perm y x
  | _, _, Perm.nil => Perm.nil
  | _, _, Perm.cons a h => Perm.cons a h.symm
  | _, _, Perm.swap a b x => Perm.swap b a x
  | _, _, Perm.trans h1 h2 => Perm.trans h2.symm h1.symm

/-- A permutation of `nil` is `nil` (inversion through the `trans` chains). -/
public theorem Perm.eq_nil : ∀ {x y : ConsList Unit A},
    Perm x y → x = ConsList.wrap () → y = ConsList.wrap ()
  | _, _, Perm.nil, _ => rfl
  | _, _, Perm.cons _ _, h => nomatch h
  | _, _, Perm.swap _ _ _, h => nomatch h
  | _, _, Perm.trans h1 h2, h => Perm.eq_nil h2 (Perm.eq_nil h1 h)

/-- The permutation relation `perm : list A ⟶ list A`. -/
@[expose] public def perm : dList A ⟶ dList A := Perm

/-- **`perm` is transitive**: `perm ≫ perm ⊑ perm`. -/
theorem perm_transitive : (perm : dList A ⟶ dList A) ≫ perm ⊑ perm :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact Perm.trans hxy hyz

/-! ## Prefix `prefix : list A ← list A` -/

/-- `x` is a prefix of `y`. -/
@[expose] public def prefixP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => a = b ∧ prefixP x y

/-- The prefix relation `prefix : list A ⟶ list A`, mirrored to diagram order:
    `prefixR x ys` iff `ys` is an initial segment of `x`. -/
@[expose] public def prefixR : dList A ⟶ dList A := fun x ys => prefixP ys x

public theorem prefixP.refl : ∀ x : ConsList Unit A, prefixP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ x => ⟨rfl, prefixP.refl x⟩

/-- `nil` is a prefix of every list. -/
public theorem prefixP.nil : ∀ x : ConsList Unit A, prefixP (ConsList.wrap ()) x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ _ => trivial

public theorem prefixP.trans : ∀ {x y z : ConsList Unit A}, prefixP x y → prefixP y z → prefixP x z
  | ConsList.wrap _, _, _, _, _ => trivial
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.cons _ _, ⟨hab, hxy⟩, ⟨hbc, hyz⟩ =>
      ⟨hab.trans hbc, prefixP.trans hxy hyz⟩

/-- **`prefix` is transitive**. -/
theorem prefix_transitive : (prefixR : dList A ⟶ dList A) ≫ prefixR ⊑ prefixR :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact prefixP.trans hyz hxy

/-! ## Subsequence `subseq : list A ← list A` -/

/-- `x` is a subsequence of `y` (drop some elements of `y`). -/
@[expose] public def subseqP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => (a = b ∧ subseqP x y) ∨ subseqP (ConsList.cons a x) y

/-- The subsequence relation `subseq : list A ⟶ list A`, mirrored to diagram order:
    `subseq x ys` iff `ys` is `x` with some elements dropped. -/
@[expose] public def subseq : dList A ⟶ dList A := fun x ys => subseqP ys x

theorem subseqP.refl : ∀ x : ConsList Unit A, subseqP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ x => Or.inl ⟨rfl, subseqP.refl x⟩

/-- `nil` is a subsequence of every list. -/
public theorem subseqP.nil : ∀ x : ConsList Unit A, subseqP (ConsList.wrap ()) x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ _ => trivial

/-- Extending the larger list on the front preserves subsequence: `subseq x y → subseq x (b::y)`. -/
public theorem subseqP.weaken {b : A} : ∀ {x y : ConsList Unit A}, subseqP x y → subseqP x (ConsList.cons b y)
  | ConsList.wrap _, _, _ => trivial
  | ConsList.cons _ _, _, h => Or.inr h

/-- Dropping the front element of the smaller list preserves subsequence. -/
theorem subseqP.of_cons {a : A} :
    ∀ {x y : ConsList Unit A}, subseqP (ConsList.cons a x) y → subseqP x y
  | x, ConsList.wrap _, h => h.elim
  | x, ConsList.cons b y, h => by
    cases h with
    | inl h => exact subseqP.weaken h.2
    | inr h => exact subseqP.weaken (subseqP.of_cons h)

/-- **`subseq` is reflexive**. -/
theorem subseq_reflexive : Cat.id (dList A) ⊑ subseq :=
  le_iff.mpr fun x y hxy => by obtain rfl := (hxy : x = y); exact subseqP.refl x

/-! ## Sortedness `ordered : list A ← list A` (B&dM p.152, `ordered = ⦇[nil, cons·ok]⦈`) -/

variable (R : A → A → Prop)

/-- `x` is sorted under `R`: each element is `R`-below every later element (matches B&dM's `ok`
    coreflexive, `ok(a,x)` iff `∀ b ∈ x, aRb`, threaded through the list). -/
@[expose] public def orderedP : ConsList Unit A → Prop
  | ConsList.wrap _ => True
  | ConsList.cons a x => (∀ b, inlistP x b → R a b) ∧ orderedP x

/-- The sortedness coreflexive `ordered : list A ⟶ list A`. -/
@[expose] public def ordered : dList A ⟶ dList A := fun x y => x = y ∧ orderedP R x

/-- **`ordered` is coreflexive** (`ordered ⊑ id`) — discharges the `hord` hypothesis of §6.6's
    `selection_sort_correct` for the concrete sortedness relation. -/
theorem ordered_coreflexive : (ordered R : dList A ⟶ dList A) ⊑ Cat.id (dList A) :=
  le_iff.mpr fun _ _ h => h.1

/-! ## Partition `partition : list (list⁺ A) ← list A` (B&dM p.128, `partition = concat°`) -/

/-- List append. -/
@[expose] public def cappend : ConsList Unit A → ConsList Unit A → ConsList Unit A
  | ConsList.wrap _, ys => ys
  | ConsList.cons a x, ys => ConsList.cons a (cappend x ys)

/-- Flatten a list of lists (`concat = ⦇[nil, cat]⦈`). -/
@[expose] public def cconcat : ConsList Unit (ConsList Unit A) → ConsList Unit A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons seg rest => cappend seg (cconcat rest)

/-- A segment is non-empty (not `nil`). -/
@[expose] public def isNonempty : ConsList Unit A → Prop
  | ConsList.wrap _ => False
  | ConsList.cons _ _ => True

/-- Every segment of a list-of-lists is non-empty. -/
@[expose] public def allNonempty : ConsList Unit (ConsList Unit A) → Prop
  | ConsList.wrap _ => True
  | ConsList.cons seg rest => isNonempty seg ∧ allNonempty rest

/-- **`partition : list A ⟶ list (list⁺ A)`** (B&dM p.128, `partition = concat°`): a decomposition
    of `x` into a list of non-empty contiguous segments — `ps` is a partition of `x` iff flattening
    `ps` gives `x` and every segment is non-empty. -/
@[expose] public def partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) :=
  fun x ps => cconcat ps = x ∧ allNonempty ps

/-- The one-segment non-emptiness coreflexive `neSeg ⊑ 𝟙`: pass a segment iff it is not `nil`. -/
@[expose] public def neSeg : dList A ⟶ dList A := fun s t => s = t ∧ isNonempty s

/-- The flatten relation `concat : list (list A) ⟶ list A` — the graph of `cconcat`. -/
@[expose] public def concatR : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A := graph cconcat

/-! ## Suffix `suffix : list A ← list A` and `cat` (append) as a relation -/

/-- `x` is a suffix (final segment) of `y`. -/
@[expose] public def suffixP : ConsList Unit A → ConsList Unit A → Prop
  | x, ConsList.wrap _ => x = ConsList.wrap ()
  | x, ConsList.cons b y => x = ConsList.cons b y ∨ suffixP x y

/-- The suffix relation `suffix : list A ⟶ list A`, mirrored to diagram order:
    `suffixR x ys` iff `ys` is a final segment of `x`. -/
@[expose] public def suffixR : dList A ⟶ dList A := fun x ys => suffixP ys x

/-- B&dM's `cat` (append) as a relation: the graph of `cappend`. -/
public def catR : (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  graph fun p => cappend p.1 p.2

/-- `cat` at the restricted type `list A ⟵ list⁺ A × list A` (B&dM p.128), the restriction carried
    by the coreflexive `neSeg` on the first argument. -/
public def catNE : (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  rprodMap neSeg (𝟙 (dList A)) ≫ catR

/-- B&dM's `concat = ⦇[nil, cat]⦈` at p.128, where that `cat` is `catNE`: only a flattening whose
    segments are all non-empty, so that `concat°` is `partition`. -/
public def concatNE : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A :=
  ⦇(junc (sumCop (dL Unit) ⟨ConsList Unit A × ConsList Unit A⟩) wrapR catNE
    : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈

/-- The length of a list. -/
@[expose] public def clen : ConsList Unit A → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons _ x => clen x + 1

/-- Every list is a suffix of itself. -/
public theorem suffixP.refl : ∀ x : ConsList Unit A, suffixP x x
  | ConsList.wrap () => rfl
  | ConsList.cons _ _ => Or.inl rfl

/-- A suffix is no longer than the list it is a suffix of. -/
public theorem suffixP_clen_le {w : ConsList Unit A} :
    ∀ {x : ConsList Unit A}, suffixP w x → clen w ≤ clen x
  | ConsList.wrap _, h => by rw [show w = ConsList.wrap () from h]; exact Nat.le_refl 0
  | ConsList.cons a y, h => by
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (suffixP_clen_le h)

/-- **`suffixP` is antisymmetric**: a set of suffixes has at most one longest member, which is
    what lets `est(suffix)` recover a list from the set of its suffixes. -/
public theorem suffixP_antisymm : ∀ {w x : ConsList Unit A}, suffixP w x → suffixP x w → w = x
  | _, ConsList.wrap (), h1, _ => h1
  | w, ConsList.cons a y, h1, h2 => by
    rcases h1 with rfl | h1
    · rfl
    · have hle : clen w ≤ clen y := suffixP_clen_le h1
      have hge : clen y + 1 ≤ clen w := suffixP_clen_le h2
      exact absurd (Nat.le_trans hge hle) (Nat.not_succ_le_self (clen y))

/-- `ys` is a prefix of `x` iff some `v` completes it on the right: `ys ++ v = x`. -/
public theorem prefixP_iff_append :
    ∀ (ys x : ConsList Unit A), prefixP ys x ↔ ∃ v, cappend ys v = x
  | ConsList.wrap _, x => ⟨fun _ => ⟨x, rfl⟩, fun _ => prefixP.nil x⟩
  | ConsList.cons _ z, ConsList.wrap _ => ⟨False.elim, fun ⟨_, hv⟩ => nomatch hv⟩
  | ConsList.cons b z, ConsList.cons a x => by
    show (b = a ∧ prefixP z x) ↔ ∃ v, ConsList.cons b (cappend z v) = ConsList.cons a x
    constructor
    · rintro ⟨rfl, h⟩
      obtain ⟨v, hv⟩ := (prefixP_iff_append z x).mp h
      exact ⟨v, by rw [hv]⟩
    · rintro ⟨v, hv⟩
      injection hv with hba hzx
      exact ⟨hba, (prefixP_iff_append z x).mpr ⟨v, hzx⟩⟩

/-- `ys` is a suffix of `x` iff some `u` completes it on the left: `u ++ ys = x`. -/
public theorem suffixP_iff_append :
    ∀ (ys x : ConsList Unit A), suffixP ys x ↔ ∃ u, cappend u ys = x
  | ys, ConsList.wrap w => by
    show ys = ConsList.wrap () ↔ ∃ u, cappend u ys = ConsList.wrap w
    constructor
    · rintro rfl
      exact ⟨ConsList.wrap (), rfl⟩
    · rintro ⟨u, hu⟩
      cases u with
      | wrap _ => exact hu
      | cons c u' => exact nomatch hu
  | ys, ConsList.cons a x => by
    show (ys = ConsList.cons a x ∨ suffixP ys x) ↔ ∃ u, cappend u ys = ConsList.cons a x
    constructor
    · rintro (rfl | h)
      · exact ⟨ConsList.wrap (), rfl⟩
      · obtain ⟨u, hu⟩ := (suffixP_iff_append ys x).mp h
        exact ⟨ConsList.cons a u, by show ConsList.cons a (cappend u ys) = _; rw [hu]⟩
    · rintro ⟨u, hu⟩
      cases u with
      | wrap _ => exact Or.inl hu
      | cons c u' =>
        injection hu with _ hrest
        exact Or.inr ((suffixP_iff_append ys x).mpr ⟨u', hrest⟩)

/-- The contiguous-segment relation, concretely: `segment x ys` iff `ys` occurs inside `x`
    (`u ++ ys ++ v = x`). -/
@[expose] public def segment : dList A ⟶ dList A := fun x ys => ∃ u v, cappend u (cappend ys v) = x

/-! ## Sum `sum : Int ← list Int` (B&dM's `sum = ⦇[zero, plus]⦈`) -/

/-- The total of a list of numbers (B&dM's `Real` is `Int` here — the repo is Mathlib-free, and
    only `+` and `≤` are ever used). -/
@[expose] public def csum : ConsList Unit Int → Int
  | ConsList.wrap _ => 0
  | ConsList.cons n x => n + csum x

/-- The sum as a morphism `sum : list Int ⟶ Int`. -/
@[expose] public def sumR : dList Int ⟶ (⟨Int⟩ : RelSet.{0}) := graph csum

/-! ## The two orders on `Int` the optimisation case studies compare costs by -/

/-- `≤` on `Int` as a relation — the order every `cost ≤ cost°` is built from. -/
@[expose] public def leq : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun m n => m ≤ n

/-- `≥` on `Int` as a relation, the order `est` maximises over.  Spelled out rather than as
    `leq°`, per the book-notation rule that a converse with a name of its own gets the name. -/
@[expose] public def geq : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun a b => b ≤ a

/-- `≤` is transitive. -/
public theorem leq_trans : leq ≫ leq ⊑ leq :=
  le_iff.mpr fun _ _ h => by obtain ⟨_, h1, h2⟩ := h; exact Int.le_trans h1 h2

/-- `≥` is transitive — the greedy theorem's preorder hypothesis. -/
public theorem geq_trans : geq ≫ geq ⊑ geq :=
  le_iff.mpr fun _ _ h => by obtain ⟨_, h1, h2⟩ := h; exact Int.le_trans h2 h1

/-! ## The point-free definitions (B&dM §5.6, the note's `comb-fns` table)

  B&dM define the combinators point-free; each theorem below proves such a definition equal to
  the concrete relation above.  Everything is mirrored to diagram order (B&dM's `R·S` is `S ≫ R`),
  and the algebra bracket `[g,h]` is `junc` over the concrete coproduct `F c = Unit + (E × c)`. -/

/-- `[g,h]` on the left summand: `[g,h] (inl x) = g x`. -/
public theorem junc_sum_inl {a b c : RelSet.{0}} (g : a ⟶ c) (h : b ⟶ c) (x : a.carrier) (r : c.carrier) :
    junc (sumCop a b) g h (Sum.inl x) r ↔ g x r := by
  show (∃ x', (Sum.inl x : a.carrier ⊕ b.carrier) = Sum.inl x' ∧ g x' r)
      ∨ (∃ y', (Sum.inl x : a.carrier ⊕ b.carrier) = Sum.inr y' ∧ h y' r) ↔ g x r
  constructor
  · rintro (⟨x', hx', hg⟩ | ⟨y', hy', -⟩)
    · obtain rfl := Sum.inl.inj hx'
      exact hg
    · exact nomatch hy'
  · exact fun hg => Or.inl ⟨x, rfl, hg⟩

/-- `[g,h]` on the right summand: `[g,h] (inr p) = h p`. -/
public theorem junc_sum_inr {a b c : RelSet.{0}} (g : a ⟶ c) (h : b ⟶ c) (p : b.carrier) (r : c.carrier) :
    junc (sumCop a b) g h (Sum.inr p) r ↔ h p r := by
  show (∃ x', (Sum.inr p : a.carrier ⊕ b.carrier) = Sum.inl x' ∧ g x' r)
      ∨ (∃ y', (Sum.inr p : a.carrier ⊕ b.carrier) = Sum.inr y' ∧ h y' r) ↔ h p r
  constructor
  · rintro (⟨x', hx', -⟩ | ⟨y', hy', hh⟩)
    · exact nomatch hx'
    · obtain rfl := Sum.inr.inj hy'
      exact hh
  · exact fun hh => Or.inr ⟨p, rfl, hh⟩

/-- The Eilenberg–Wright square `α ≫ X = F(X) ≫ φ` of `relCata_UP`, unpacked to one pointwise
    component per constructor. -/
theorem cata_square_iff {L E : Type} {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) (X : dCL L E ⟶ c) :
    (graph con ≫ X = (F L E).map X ≫ φ)
      ↔ ((∀ d r, X (ConsList.wrap d) r ↔ φ (Sum.inl d) r)
          ∧ (∀ a x r, X (ConsList.cons a x) r ↔ ∃ y, X x y ∧ φ (Sum.inr (a, y)) r)) := by
  constructor
  · intro hsq
    refine ⟨fun d r => ?_, fun a x r => ?_⟩
    · have key := congrFun (congrFun hsq (Sum.inl d)) r
      constructor
      · intro hx
        have hl : (graph con ≫ X) (Sum.inl d) r := ⟨ConsList.wrap d, rfl, hx⟩
        rw [key] at hl
        obtain ⟨v, hv, hφ⟩ := hl
        cases v with
        | inl d' => obtain rfl := (hv : d = d'); exact hφ
        | inr q => exact (hv : False).elim
      · intro hφ
        have hr : ((F L E).map X ≫ φ) (Sum.inl d) r := ⟨Sum.inl d, rfl, hφ⟩
        rw [← key] at hr
        obtain ⟨dec, hdec, hx⟩ := hr
        obtain rfl := (hdec : dec = ConsList.wrap d)
        exact hx
    · have key := congrFun (congrFun hsq (Sum.inr (a, x))) r
      constructor
      · intro hx
        have hl : (graph con ≫ X) (Sum.inr (a, x)) r := ⟨ConsList.cons a x, rfl, hx⟩
        rw [key] at hl
        obtain ⟨v, hv, hφ⟩ := hl
        cases v with
        | inl d' => exact (hv : False).elim
        | inr q =>
          obtain ⟨q1, q2⟩ := q
          obtain ⟨ha, hXq⟩ := hv
          obtain rfl := (ha : a = q1)
          exact ⟨q2, hXq, hφ⟩
      · intro hex
        obtain ⟨y, hXy, hφ⟩ := hex
        have hr : ((F L E).map X ≫ φ) (Sum.inr (a, x)) r := ⟨Sum.inr (a, y), ⟨rfl, hXy⟩, hφ⟩
        rw [← key] at hr
        obtain ⟨dec, hdec, hx⟩ := hr
        obtain rfl := (hdec : dec = ConsList.cons a x)
        exact hx
  · intro hcomp
    obtain ⟨hw, hc⟩ := hcomp
    apply hom_ext; intro u r
    cases u with
    | inl d =>
      constructor
      · intro hl
        obtain ⟨dec, hdec, hx⟩ := hl
        obtain rfl := (hdec : dec = ConsList.wrap d)
        exact ⟨Sum.inl d, rfl, (hw d r).mp hx⟩
      · intro hr
        obtain ⟨v, hv, hφ⟩ := hr
        cases v with
        | inl d' => obtain rfl := (hv : d = d'); exact ⟨ConsList.wrap d, rfl, (hw d r).mpr hφ⟩
        | inr q => exact (hv : False).elim
    | inr p =>
      obtain ⟨a, x⟩ := p
      constructor
      · intro hl
        obtain ⟨dec, hdec, hx⟩ := hl
        obtain rfl := (hdec : dec = ConsList.cons a x)
        obtain ⟨y, hXy, hφ⟩ := (hc a x r).mp hx
        exact ⟨Sum.inr (a, y), ⟨rfl, hXy⟩, hφ⟩
      · intro hr
        obtain ⟨v, hv, hφ⟩ := hr
        cases v with
        | inl d' => exact (hv : False).elim
        | inr q =>
          obtain ⟨q1, q2⟩ := q
          obtain ⟨ha, hXq⟩ := hv
          obtain rfl := (ha : a = q1)
          exact ⟨ConsList.cons a x, rfl, (hc a x r).mpr ⟨q2, hXq, hφ⟩⟩

/-- `cata_square_iff` for a `[g,h]` (`junc`) algebra, the coproduct already evaluated: the two
    components mention `g` and `h` directly. -/
public theorem cata_square_junc_iff {L E : Type} {c : RelSet.{0}} (g : dL L ⟶ c)
    (h : (⟨E × c.carrier⟩ : RelSet.{0}) ⟶ c) (X : dCL L E ⟶ c) :
    (graph con ≫ X = (F L E).map X ≫ junc (sumCop (dL L) ⟨E × c.carrier⟩) g h)
      ↔ ((∀ d r, X (ConsList.wrap d) r ↔ g d r)
          ∧ (∀ a x r, X (ConsList.cons a x) r ↔ ∃ y, X x y ∧ h (a, y) r)) := by
  rw [cata_square_iff]
  constructor
  · intro hsq
    obtain ⟨hw, hc⟩ := hsq
    refine ⟨fun d r => (hw d r).trans (junc_sum_inl g h d r), fun a x r => (hc a x r).trans ?_⟩
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h1, (junc_sum_inr g h (a, y) r).mp h2⟩,
           fun ⟨y, h1, h2⟩ => ⟨y, h1, (junc_sum_inr g h (a, y) r).mpr h2⟩⟩
  · intro hcm
    obtain ⟨hw, hc⟩ := hcm
    refine ⟨fun d r => (hw d r).trans (junc_sum_inl g h d r).symm, fun a x r => (hc a x r).trans ?_⟩
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h1, (junc_sum_inr g h (a, y) r).mpr h2⟩,
           fun ⟨y, h1, h2⟩ => ⟨y, h1, (junc_sum_inr g h (a, y) r).mp h2⟩⟩

/-! ### The list relator `list(R)` -/

variable {B : Type}

/-- Elementwise lifting, concretely: `listP R x y` iff `y` has the shape of `x` with each
    element related by `R`. -/
@[expose] public def listP (R : dE A ⟶ dE B) : ConsList Unit A → ConsList Unit B → Prop
  | ConsList.wrap _, ConsList.wrap _ => True
  | ConsList.wrap _, ConsList.cons _ _ => False
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => R a b ∧ listP R x y

/-- The list relator's action `list(R) : list A ⟶ list B` (B&dM's `listr R`). -/
@[expose] public def list (R : dE A ⟶ dE B) : dList A ⟶ dList B := listP R

/-- **`list(R) = ⦇[nil, (R⊗𝟙) cons]⦈`** (note `comb-fns`; B&dM p.126): one `R` per element,
    the shape untouched. -/
public theorem list_cata (R : dE A ⟶ dE B) :
    list R = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit B⟩) wrapR
        (rprodMap R (𝟙 (dList B)) ≫ consR) : (F Unit A).obj (dList B) ⟶ dList B)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · show listP R (ConsList.wrap ()) r ↔ r = ConsList.wrap d
    cases r with
    | wrap u => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | cons b z => exact ⟨False.elim, fun h => nomatch h⟩
  · show listP R (ConsList.cons a x) r
        ↔ ∃ y, listP R x y
            ∧ ∃ q : B × ConsList Unit B, (R a q.1 ∧ y = q.2) ∧ r = ConsList.cons q.1 q.2
    constructor
    · intro h
      cases r with
      | wrap u => exact h.elim
      | cons b z => exact ⟨z, h.2, (b, z), ⟨h.1, rfl⟩, rfl⟩
    · rintro ⟨y, hy, q, ⟨hab, rfl⟩, rfl⟩
      exact ⟨hab, hy⟩

/-! ### `list` is a relator: identities, composition, monotonicity, converse (B&dM p.126) -/

public theorem listP_id : ∀ x y : ConsList Unit A, listP (𝟙 (dE A)) x y ↔ x = y
  | ConsList.wrap (), ConsList.wrap () => ⟨fun _ => rfl, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨False.elim, fun h => nomatch h⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨False.elim, fun h => nomatch h⟩
  | ConsList.cons a x, ConsList.cons b y =>
      ⟨fun h => by rw [show a = b from h.1, (listP_id x y).mp h.2],
       fun h => by cases h; exact ⟨rfl, (listP_id x x).mpr rfl⟩⟩

/-- `list(𝟙) = 𝟙`. -/
public theorem list_id : list (𝟙 (dE A)) = 𝟙 (dList A) := hom_ext listP_id

public theorem listP_comp {B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    ∀ (x : ConsList Unit A) (z : ConsList Unit C),
      listP (R ≫ S) x z ↔ ∃ y, listP R x y ∧ listP S y z
  | ConsList.wrap _, ConsList.wrap _ =>
      ⟨fun _ => ⟨ConsList.wrap (), trivial, trivial⟩, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ =>
      ⟨False.elim, fun ⟨y, h1, h2⟩ => by cases y with
        | wrap _ => exact h2
        | cons _ _ => exact h1⟩
  | ConsList.cons _ _, ConsList.wrap _ =>
      ⟨False.elim, fun ⟨y, h1, h2⟩ => by cases y with
        | wrap _ => exact h1
        | cons _ _ => exact h2⟩
  | ConsList.cons a x, ConsList.cons c z => by
      constructor
      · rintro ⟨⟨b, hR, hS⟩, hxz⟩
        obtain ⟨y, hy1, hy2⟩ := (listP_comp R S x z).mp hxz
        exact ⟨ConsList.cons b y, ⟨hR, hy1⟩, hS, hy2⟩
      · rintro ⟨y, hy1, hy2⟩
        cases y with
        | wrap _ => exact hy1.elim
        | cons b ys =>
            exact ⟨⟨b, hy1.1, hy2.1⟩, (listP_comp R S x z).mpr ⟨ys, hy1.2, hy2.2⟩⟩

/-- `list(RS) = list(R) list(S)`. -/
public theorem list_comp {B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    list (R ≫ S) = list R ≫ list S := hom_ext (listP_comp R S)

public theorem listP_mono {B : Type} {R S : dE A ⟶ dE B} (h : ∀ a b, R a b → S a b) :
    ∀ x y, listP R x y → listP S x y
  | ConsList.wrap _, ConsList.wrap _, _ => trivial
  | ConsList.wrap _, ConsList.cons _ _, hxy => hxy.elim
  | ConsList.cons _ _, ConsList.wrap _, hxy => hxy.elim
  | ConsList.cons a x, ConsList.cons b y, hxy =>
      ⟨h a b hxy.1, listP_mono h x y hxy.2⟩

/-- `R ⊑ S ⟹ list(R) ⊑ list(S)` — `list` is monotonic. -/
public theorem list_mono {B : Type} {R S : dE A ⟶ dE B} (h : R ⊑ S) : list R ⊑ list S :=
  le_iff.mpr (listP_mono (le_iff.mp h))

/-- `list` BUNDLED as a relator, so §5.7's closure theorems — `laxNatural_prod`,
    `strictNatural_prod` — can be read at it.  `RelSet` is a one-field structure, so `dE a.carrier`
    IS `a` and the object part is just `list`'s own target. -/
@[expose] public def listRelator : Relator RelSet.{0} RelSet.{0} where
  obj a := dList a.carrier
  map R := list R
  map_id _ := list_id
  map_comp R S := list_comp R S
  map_mono h := list_mono h

public theorem listP_recip {B : Type} (R : dE A ⟶ dE B) :
    ∀ (y : ConsList Unit B) (x : ConsList Unit A), listP R° y x ↔ listP R x y
  | ConsList.wrap _, ConsList.wrap _ => Iff.rfl
  | ConsList.wrap _, ConsList.cons _ _ => Iff.rfl
  | ConsList.cons _ _, ConsList.wrap _ => Iff.rfl
  | ConsList.cons _ y, ConsList.cons _ x =>
      ⟨fun h => ⟨h.1, (listP_recip R y x).mp h.2⟩, fun h => ⟨h.1, (listP_recip R y x).mpr h.2⟩⟩

/-- `list(R°) = list(R)°` — `list` preserves converse. -/
public theorem list_recip {B : Type} (R : dE A ⟶ dE B) : list R° = (list R)° :=
  hom_ext (listP_recip R)

/-! ### The free theorems of `cons` and `concat`

  A polymorphic combinator's type names two relators, and the free theorem is the lax naturality
  square between them.  For `cons : A × list A ⟶ list A` the relators are `× ∘ ⟨1, list⟩` and
  `list`; for `concat : list (list A) ⟶ list A` they are `list ∘ list` and `list` — `concat` is
  the list monad's `μ`, the shape `bigUnion_natural` (A4_6) has for the power relator.  Both come
  out as EQUALITIES, not merely the `⊑` of `LaxNatural`: `cons` because it is the initial
  algebra's constructor, `concat` because `list(R)` preserves the length of every segment, so a
  related flattening can be re-split along the segment boundaries.  Contrast `π₂`
  (`outr_laxNatural`, A5_2), whose square is strict exactly at the entire relations. -/

/-- `list(R)` respects append: relating the two halves relates the appends. -/
public theorem listP_cappend {B : Type} (R : dE A ⟶ dE B) :
    ∀ (x : ConsList Unit A) (y : ConsList Unit B) {u : ConsList Unit A} {v : ConsList Unit B},
      listP R x y → listP R u v → listP R (cappend x u) (cappend y v)
  | ConsList.wrap _, ConsList.wrap _, _, _, _, huv => huv
  | ConsList.wrap _, ConsList.cons _ _, _, _, hxy, _ => hxy.elim
  | ConsList.cons _ _, ConsList.wrap _, _, _, hxy, _ => hxy.elim
  | ConsList.cons _ x, ConsList.cons _ y, _, _, hxy, huv =>
      ⟨hxy.1, listP_cappend R x y hxy.2 huv⟩

/-- The converse half: anything `list(R)`-related to an append SPLITS at the same boundary.
    This is what makes `concat`'s free theorem strict — `list(R)` cannot move an element across
    a segment boundary, because it relates `cons` to `cons` and `nil` to `nil` only. -/
public theorem listP_cappend_split {B : Type} (R : dE A ⟶ dE B) :
    ∀ (x u : ConsList Unit A) (w : ConsList Unit B), listP R (cappend x u) w →
      ∃ y v, listP R x y ∧ listP R u v ∧ w = cappend y v
  | ConsList.wrap _, _, w, h => ⟨ConsList.wrap (), w, trivial, h, rfl⟩
  | ConsList.cons _ _, _, ConsList.wrap _, h => h.elim
  | ConsList.cons _ x, u, ConsList.cons b w, h => by
      obtain ⟨y, v, hy, hv, rfl⟩ := listP_cappend_split R x u w h.2
      exact ⟨ConsList.cons b y, v, ⟨h.1, hy⟩, hv, rfl⟩

/-- `list(list R)`-related lists of lists have `list(R)`-related flattenings. -/
public theorem listP_cconcat {B : Type} (R : dE A ⟶ dE B) :
    ∀ (xs : ConsList Unit (ConsList Unit A)) (ys : ConsList Unit (ConsList Unit B)),
      listP (list R) xs ys → listP R (cconcat xs) (cconcat ys)
  | ConsList.wrap _, ConsList.wrap _, _ => trivial
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons x xs, ConsList.cons y ys, h =>
      listP_cappend R x y h.1 (listP_cconcat R xs ys h.2)

/-- And the converse: a `list(R)`-image of a flattening is itself a flattening, of a
    `list(list R)`-image of the original segments — `listP_cappend_split` at each `cons`. -/
public theorem listP_cconcat_split {B : Type} (R : dE A ⟶ dE B) :
    ∀ (xs : ConsList Unit (ConsList Unit A)) (w : ConsList Unit B), listP R (cconcat xs) w →
      ∃ ys, listP (list R) xs ys ∧ w = cconcat ys
  | ConsList.wrap _, ConsList.wrap _, _ => ⟨ConsList.wrap (), trivial, rfl⟩
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons x xs, w, h => by
      obtain ⟨y, v, hy, hv, rfl⟩ := listP_cappend_split R x (cconcat xs) w h
      obtain ⟨ys, hys, rfl⟩ := listP_cconcat_split R xs v hv
      exact ⟨ConsList.cons y ys, ⟨hy, hys⟩, rfl⟩

/-- **The free theorem of `cons`**, and it is STRICT: `(R × list R) cons = cons list(R)`.  Both
    sides relate `(a,x)` to `cons b y` exactly when `R a b` and `list(R) x y`. -/
public theorem cons_natural {B : Type} (R : dE A ⟶ dE B) :
    rprodMap R (list R) ≫ consR = consR ≫ list R := by
  apply hom_ext; intro p w
  obtain ⟨a, x⟩ := p
  constructor
  · rintro ⟨⟨b, y⟩, ⟨hab, hxy⟩, rfl⟩
    exact ⟨ConsList.cons a x, rfl, hab, hxy⟩
  · rintro ⟨_, rfl, hz⟩
    cases w with
    | wrap _ => exact hz.elim
    | cons b y => exact ⟨(b, y), ⟨hz.1, hz.2⟩, rfl⟩

/-- **The free theorem of `wrap`**, and it is STRICT: `wrap list(R) = R wrap`.  Both sides relate
    `a` to the one-element list `[b]` exactly when `R a b`, and to nothing else. -/
public theorem wrap_natural {B : Type} (R : dE A ⟶ dE B) :
    (singleR () : dE A ⟶ dList A) ≫ list R = R ≫ singleR () := by
  apply hom_ext; intro a w
  constructor
  · rintro ⟨_, rfl, hz⟩
    cases w with
    | wrap _ => exact hz.elim
    | cons b y =>
      cases y with
      | wrap _ => exact ⟨b, hz.1, rfl⟩
      | cons _ _ => exact hz.2.elim
  · rintro ⟨b, hab, rfl⟩
    exact ⟨ConsList.cons a (ConsList.wrap ()), rfl, hab, trivial⟩

/-- **The free theorem of the initial list algebra `α=[nil,cons]`**, in the ELEMENT type, and it is
    STRICT: `α list(R) = F(R,list R) α`.  The `nil` branch is the leaf identity, the `cons` branch is
    `cons_natural` read off the constructors — so the note's `α` bead is a natural transformation
    `F∘⟨𝟙,list⟩ ⇒ list` and leaves the object wire.  (The OTHER family, `α` over its CARRIER at a
    fixed element type, is refuted by `Carrier.listAlg_not_lax_natural`; these are different squares.) -/
public theorem alphaR_natural (R : dE A ⟶ dE B) :
    (alphaR : (F Unit A).obj (dList A) ⟶ dList A) ≫ list R
      = Fbimap Unit R (list R) ≫ (alphaR : (F Unit B).obj (dList B) ⟶ dList B) := by
  apply hom_ext; intro u w
  cases u with
  | inl d =>
    cases w with
    | wrap e => exact ⟨fun _ => ⟨Sum.inl e, rfl, rfl⟩, fun _ => ⟨ConsList.wrap d, rfl, trivial⟩⟩
    | cons b y =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨_, rfl, hz⟩ := h; exact hz.elim
      · obtain ⟨v, hv, hw⟩ := h
        cases v with
        | inl e => exact nomatch hw
        | inr q => exact hv.elim
  | inr p =>
    obtain ⟨a, x⟩ := p
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, rfl, hz⟩ := h
      cases w with
      | wrap e => exact hz.elim
      | cons b y => exact ⟨Sum.inr (b, y), ⟨hz.1, hz.2⟩, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := h
      cases v with
      | inl e => exact hv.elim
      | inr q => obtain ⟨b, y⟩ := q; exact ⟨ConsList.cons a x, rfl, hv.1, hv.2⟩

/-- **The free theorem of `concat`**, and it is STRICT: `list(list R) concat = concat list(R)`.
    `⊑` is `listP_cconcat`, `⊒` is `listP_cconcat_split`. -/
public theorem concat_natural {B : Type} (R : dE A ⟶ dE B) :
    list (list R) ≫ concatR = concatR ≫ list R := by
  apply hom_ext; intro xs w
  constructor
  · rintro ⟨ys, hxy, rfl⟩
    exact ⟨cconcat xs, rfl, listP_cconcat R xs ys hxy⟩
  · rintro ⟨_, rfl, hz⟩
    obtain ⟨ys, hys, rfl⟩ := listP_cconcat_split R xs w hz
    exact ⟨ys, hys, rfl⟩

/-! ### The function-level map: `list` of a graph is a graph -/

/-- Function-level list map. -/
@[expose] public def cmap {B : Type} (f : A → B) : ConsList Unit A → ConsList Unit B
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons a x => ConsList.cons (f a) (cmap f x)

public theorem listP_graph {B : Type} (f : A → B) :
    ∀ (x : ConsList Unit A) (y : ConsList Unit B), listP (graph f) x y ↔ y = cmap f x
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨False.elim, fun h => nomatch h⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨False.elim, fun h => nomatch h⟩
  | ConsList.cons a x, ConsList.cons b y =>
      ⟨fun h => by rw [show b = f a from h.1, (listP_graph f x y).mp h.2]; rfl,
       fun h => by cases h; exact ⟨rfl, (listP_graph f x (cmap f x)).mpr rfl⟩⟩

/-- `list(graph f) = graph(cmap f)` — the list relator restricts to the list functor on maps. -/
public theorem list_graph {B : Type} (f : A → B) :
    list (graph f) = (graph (cmap f) : dList A ⟶ dList B) := by
  apply hom_ext; intro x y
  show listP (graph f) x y ↔ y = cmap f x
  exact listP_graph f x y

/-! ### `total f = sum·list f`, the shape every case study's cost has -/

/-- B&dM's `sum·list f` — the total of a list under a weighting `f` (`value = total vol` and
    `weight = total wt` in §8.4).  `total f (cons a x) = f a + total f x` holds by `rfl`. -/
@[expose] public def total (f : A → Int) (x : ConsList Unit A) : Int := csum (cmap f x)

/-- `total f = list(f) sum`, point-free. -/
public theorem total_eq (f : A → Int) :
    (graph (total f) : dList A ⟶ (⟨Int⟩ : RelSet.{0})) = list (graph f) ≫ sumR := by
  apply hom_ext; intro x n
  constructor
  · intro h
    exact ⟨cmap f x, (listP_graph f x _).mpr rfl, (h : n = total f x)⟩
  · rintro ⟨ns, hns, hsum⟩
    show n = total f x
    rw [(show n = csum ns from hsum), (listP_graph f x ns).mp hns]
    rfl

/-! ### The catamorphism and `cat°` forms of the note's `comb-fns` rows -/

/-- **`subseq = ⦇[nil, cons ∪ π₂]⦈`** (note `comb-fns`; B&dM §5.6): fold the list; at each
    element either `cons` keeps the head or `π₂` drops it.  `π₂` is spelled as its Rel(Set)
    value `graph (·.2)` — definitionally `(relProd _ _).outr` — so that the fold's square
    reduces on a pair, which the abstract projection does not. -/
public theorem subseq_cata :
    (subseq : dList A ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR
          (consR ∪ graph fun p => p.2) : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · show subseqP r (ConsList.wrap d) ↔ r = ConsList.wrap d
    cases r with
    | wrap u => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | cons b z => exact ⟨False.elim, fun h => nomatch h⟩
  · show subseqP r (ConsList.cons a x)
        ↔ ∃ y, subseqP y x ∧ (r = ConsList.cons a y ∨ r = y)
    constructor
    · intro h
      cases r with
      | wrap u => exact ⟨ConsList.wrap (), subseqP.nil x, Or.inr rfl⟩
      | cons b z =>
        cases h with
        | inl h => exact ⟨z, h.2, Or.inl (by rw [h.1])⟩
        | inr h => exact ⟨ConsList.cons b z, h, Or.inr rfl⟩
    · rintro ⟨y, hy, rfl | rfl⟩
      · exact Or.inl ⟨rfl, hy⟩
      · exact subseqP.weaken hy

/-- The note's `subseq-EW-join` second row: **`(𝟙×∋)(cons ∪ π₂) = (𝟙×∋)cons ∪ (𝟙×∋)π₂`** —
    `comp_union_distrib` at `subseq`'s algebra, the instance the row states. -/
public theorem prod_ni_union_dist :
    rprodMap (𝟙 (dE A)) (∋ (dList A))
        ≫ (consR ∪ graph fun p : A × ConsList Unit A => p.2)
      = (rprodMap (𝟙 (dE A)) (∋ (dList A)) ≫ consR)
        ∪ (rprodMap (𝟙 (dE A)) (∋ (dList A)) ≫ graph fun p : A × ConsList Unit A => p.2) :=
  DistributiveAllegory.comp_union_distrib _ _ _

/-- The note's `subseq-EW-join` third row: **`(𝟙×∋)π₂ = π₂∋`** — `rprodMap_id_snd` at `∋`, the
    instance the row states: the membership crosses the projection unchanged. -/
public theorem prod_ni_proj_slide :
    rprodMap (𝟙 (dE A)) (∋ (dList A)) ≫ (graph fun p : A × ConsList Unit A => p.2)
      = (graph fun q : A × (PowerAllegory.powerObj (dList A)).carrier => q.2) ≫ ∋ (dList A) :=
  rprodMap_id_snd _

/-- The note's `subseq-EW-join`: **`Λ((𝟙×∋)(cons ∪ π₂)) = ⟨Λ(𝟙×∋) E(cons), π₂⟩ cup`** — the
    second arm of `subseq`'s algebra under the power transpose.  Composition distributes over the
    `∪`, `(𝟙×∋)π₂ = π₂∋` slides the membership past the projection (`rprodMap_id_snd`), `Λ` of a
    union is the fork into `cup` (`Λ_union`), and then absorption takes `Λ` inside the `cons`
    operand while fusion and `Λ(∋)=𝟙` leave the `π₂` operand bare. -/
public theorem subseq_alg_join :
    Λ (rprodMap (𝟙 (dE A)) (∋ (dList A))
        ≫ (consR ∪ graph fun p : A × ConsList Unit A => p.2))
      = rpair (Λ (rprodMap (𝟙 (dE A)) (∋ (dList A))) ≫ existsImage consR)
          (graph fun q : A × (PowerAllegory.powerObj (dList A)).carrier => q.2)
        ≫ cup (relProd (PowerAllegory.powerObj (dList A))
            (PowerAllegory.powerObj (dList A))) := by
  rw [DistributiveAllegory.comp_union_distrib, rprodMap_id_snd,
    Λ_union _ _ (relProd (PowerAllegory.powerObj (dList A))
      (PowerAllegory.powerObj (dList A))),
    pair_eq_rpair, Λ_absorption, Λ_fusion (graph_map _), Λ_eps_reflection, Cat.comp_id]

/-- **`prefix = ⦇[nil, nil ∪ cons]⦈`** (note `comb-fns`; B&dM §5.6): fold the list; the first
    branch (`⊸nil`, discard then `nil`) stops early, `cons` keeps going. -/
public theorem prefix_cata :
    (prefixR : dList A ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR
          ((graph fun _ => ConsList.wrap ()) ∪ consR) : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · show prefixP r (ConsList.wrap d) ↔ r = ConsList.wrap d
    cases r with
    | wrap u => exact ⟨fun _ => rfl, fun _ => trivial⟩
    | cons b z => exact ⟨False.elim, fun h => nomatch h⟩
  · show prefixP r (ConsList.cons a x)
        ↔ ∃ y, prefixP y x ∧ (r = ConsList.wrap () ∨ r = ConsList.cons a y)
    constructor
    · intro h
      cases r with
      | wrap u => exact ⟨ConsList.wrap (), prefixP.nil x, Or.inl rfl⟩
      | cons b z => exact ⟨z, h.2, Or.inr (by rw [h.1])⟩
    · rintro ⟨y, hy, rfl | rfl⟩
      · exact trivial
      · exact ⟨rfl, hy⟩

/-- **`prefix = cat° π₁`** (note `comb-fns`): split `x` as `ys ++ v` and keep the left part.
    `π₁ = graph (·.1)`, as in `subseq_cata`. -/
public theorem prefix_cat :
    (prefixR : dList A ⟶ dList A) = catR° ≫ graph (fun p => p.1) := by
  apply hom_ext; intro x ys
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (prefixP_iff_append ys x).mp h
    exact ⟨(ys, v), hv.symm, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (prefixP_iff_append _ _).mpr ⟨p.2, hp.symm⟩

/-- **`suffix = cat° π₂`** (note `comb-fns`; B&dM §5.6): split `x` as `u ++ ys` and keep the
    right part.  `π₂ = graph (·.2)`, as in `subseq_cata`. -/
public theorem suffix_cat :
    (suffixR : dList A ⟶ dList A) = catR° ≫ graph (fun p => p.2) := by
  apply hom_ext; intro x ys
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (suffixP_iff_append ys x).mp h
    exact ⟨(u, ys), hu.symm, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (suffixP_iff_append _ _).mpr ⟨p.1, hp.symm⟩

/-- **`segment = suffix prefix`** (note `comb-fns`; B&dM §7.5): a suffix, then a prefix of it. -/
public theorem segment_eq : (segment : dList A ⟶ dList A) = suffixR ≫ prefixR := by
  apply hom_ext; intro x ys
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨cappend ys v, (suffixP_iff_append _ _).mpr ⟨u, rfl⟩,
      (prefixP_iff_append _ _).mpr ⟨v, rfl⟩⟩
  · rintro ⟨zs, hsuf, hpre⟩
    obtain ⟨u, rfl⟩ := (suffixP_iff_append zs x).mp hsuf
    obtain ⟨v, rfl⟩ := (prefixP_iff_append ys zs).mp hpre
    exact ⟨u, v, rfl⟩

/-- **`perm = ⦇[nil, cons perm]⦈`** (B&dM §5.6, `⦇[nil, perm·cons]⦈` mirrored): fold; each
    step `cons`es the head onto a permuted tail and permutes the result. -/
public theorem perm_cata :
    (perm : dList A ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (consR ≫ perm)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · show Perm (ConsList.wrap ()) r ↔ r = ConsList.wrap d
    exact ⟨fun h => Perm.eq_nil h rfl, fun h => by obtain rfl := h; exact Perm.nil⟩
  · show Perm (ConsList.cons a x) r
        ↔ ∃ y, Perm x y ∧ ∃ w, w = ConsList.cons a y ∧ Perm w r
    constructor
    · intro h
      exact ⟨x, Perm.refl x, ConsList.cons a x, rfl, h⟩
    · rintro ⟨y, hxy, w, rfl, hwr⟩
      exact Perm.trans (Perm.cons a hxy) hwr

/-- **`partition = concat°`** (note `comb-fns`; B&dM p.128), the book's own spelling: the `concat`
    it converses is `concatNE`, built on `cat` at the restricted type. -/
public theorem partition_concat :
    (partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0})) = concatNE° := by
  have h : (fun ps x => cconcat ps = x ∧ allNonempty ps
        : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A)
      = concatNE := by
    refine (relCata_UP (initial Unit (ConsList Unit A)) _ _).mp
      ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun seg rest r => ?_⟩)
    · show (ConsList.wrap () = r ∧ True) ↔ r = ConsList.wrap d
      exact ⟨fun hh => hh.1.symm, fun hh => ⟨hh.symm, trivial⟩⟩
    · show (cappend seg (cconcat rest) = r ∧ isNonempty seg ∧ allNonempty rest)
          ↔ ∃ y, (cconcat rest = y ∧ allNonempty rest)
              ∧ ∃ q : ConsList Unit A × ConsList Unit A,
                  ((seg = q.1 ∧ isNonempty seg) ∧ y = q.2) ∧ r = cappend q.1 q.2
      constructor
      · rintro ⟨hcat, hne, hall⟩
        exact ⟨cconcat rest, ⟨rfl, hall⟩, (seg, cconcat rest), ⟨⟨rfl, hne⟩, rfl⟩, hcat.symm⟩
      · rintro ⟨y, ⟨hy, hall⟩, q, ⟨⟨rfl, hne⟩, rfl⟩, rfl⟩
        exact ⟨by rw [hy], hne, hall⟩
  rw [← h]
  exact rfl

/-- **`concat = ⦇[nil, cat]⦈`** (note `comb-fns`; B&dM §5.6): fold the list of segments,
    appending each onto the flattened rest. -/
public theorem concat_cata :
    (concatR : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨ConsList Unit A × ConsList Unit A⟩) wrapR catR
          : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit (ConsList Unit A)) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun seg rest r => ?_⟩)
  · exact Iff.rfl
  · show r = cappend seg (cconcat rest) ↔ ∃ y, y = cconcat rest ∧ r = cappend seg y
    exact ⟨fun h => ⟨cconcat rest, rfl, h⟩, fun ⟨y, hy, hr⟩ => by rw [hr, hy]⟩

/-- **`sum = ⦇[zero, plus]⦈`** (note `cata-examples`; B&dM §5.x): fold the list, adding each head
    onto the total of the tail, `nil` contributing `zero`. -/
public theorem sum_cata :
    (sumR : dList Int ⟶ (⟨Int⟩ : RelSet.{0}))
      = ⦇(junc (sumCop (dL Unit) ⟨Int × Int⟩) (graph fun _ => (0 : Int))
          (graph fun q => q.1 + q.2) : (F Unit Int).obj (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩)⦈ := by
  refine (relCata_UP (initial Unit Int) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => Iff.rfl, fun a x r => ?_⟩)
  show r = a + csum x ↔ ∃ y, y = csum x ∧ r = a + y
  exact ⟨fun h => ⟨csum x, rfl, h⟩, fun ⟨y, hy, hr⟩ => by rw [hr, hy]⟩

end Freyd.Alg.RelSet.ListRel

