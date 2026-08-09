/-
  Bird & de Moor, *Algebra of Programming* §5.6  Combinatorial functions (book pp. 125-132) —
  the list combinators, as concrete relations on `list A = ConsList Unit A` in the Set model.

  These are the relations the optimisation case studies (§6.6 sorting, §7.5 security van, §8.x
  thinning, …) take as their coalgebra / specification: `perm` (permutation), `prefix`/`suffix`,
  `subseq` (subsequence), `inlist` (membership).  B&dM define them point-free (catamorphisms:
  `perm = ⦇[nil, perm·cons]⦈`, `prefix = ⦇[nil, nil∪cons]⦈`, `partition = concat°`, …); here we
  give the equivalent concrete meaning as an inductive/structural relation and prove the algebraic
  properties (reflexivity, symmetry, transitivity) that the derivations use.  Built on the cons-list
  engine `AOP.A6_ConsList` (`list A = ConsList Unit A`).
-/
module

public import AOP.A6_ConsList

namespace Freyd.Alg.RelSet.ListRel

open Freyd Freyd.Alg.RelSet.CL

variable {A : Type}

/-- `list A = ConsList Unit A` (`nil = wrap ()`, `cons a x`). -/
@[expose] public abbrev dList (A : Type) : RelSet.{0} := dCL Unit A

/-! ## Membership `inlist : A ← list A` -/

/-- `a ∈ x`. -/
@[expose] public def inlistP : ConsList Unit A → A → Prop
  | ConsList.wrap _, _ => False
  | ConsList.cons b x, a => a = b ∨ inlistP x a

/-- The membership relation `inlist : list A ⟶ A`. -/
def inlist : dList A ⟶ dE A := inlistP

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

/-- The permutation relation `perm : list A ⟶ list A`. -/
@[expose] public def perm : dList A ⟶ dList A := Perm

/-- **`perm` is transitive**: `perm ≫ perm ⊑ perm`. -/
theorem perm_transitive : (perm : dList A ⟶ dList A) ≫ perm ⊑ perm :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact Perm.trans hxy hyz

/-! ## Prefix `prefix : list A ← list A` -/

/-- `x` is a prefix of `y`. -/
def prefixP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => a = b ∧ prefixP x y

/-- The prefix relation `prefix : list A ⟶ list A`. -/
def prefixR : dList A ⟶ dList A := prefixP

theorem prefixP.refl : ∀ x : ConsList Unit A, prefixP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ x => ⟨rfl, prefixP.refl x⟩

theorem prefixP.trans : ∀ {x y z : ConsList Unit A}, prefixP x y → prefixP y z → prefixP x z
  | ConsList.wrap _, _, _, _, _ => trivial
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.cons _ _, ⟨hab, hxy⟩, ⟨hbc, hyz⟩ =>
      ⟨hab.trans hbc, prefixP.trans hxy hyz⟩

/-- **`prefix` is transitive**. -/
theorem prefix_transitive : (prefixR : dList A ⟶ dList A) ≫ prefixR ⊑ prefixR :=
  le_iff.mpr fun x z h => by obtain ⟨y, hxy, hyz⟩ := h; exact prefixP.trans hxy hyz

/-! ## Subsequence `subseq : list A ← list A` -/

/-- `x` is a subsequence of `y` (drop some elements of `y`). -/
def subseqP : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, _ => True
  | ConsList.cons _ _, ConsList.wrap _ => False
  | ConsList.cons a x, ConsList.cons b y => (a = b ∧ subseqP x y) ∨ subseqP (ConsList.cons a x) y

/-- The subsequence relation `subseq : list A ⟶ list A`. -/
def subseq : dList A ⟶ dList A := subseqP

theorem subseqP.refl : ∀ x : ConsList Unit A, subseqP x x
  | ConsList.wrap _ => trivial
  | ConsList.cons _ x => Or.inl ⟨rfl, subseqP.refl x⟩

/-- Extending the larger list on the front preserves subsequence: `subseq x y → subseq x (b::y)`. -/
theorem subseqP.weaken {b : A} : ∀ {x y : ConsList Unit A}, subseqP x y → subseqP x (ConsList.cons b y)
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
  le_iff.mpr fun x _ hxy => hxy ▸ subseqP.refl x

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
def cconcat : ConsList Unit (ConsList Unit A) → ConsList Unit A
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons seg rest => cappend seg (cconcat rest)

/-- A segment is non-empty (not `nil`). -/
def isNonempty : ConsList Unit A → Prop
  | ConsList.wrap _ => False
  | ConsList.cons _ _ => True

/-- Every segment of a list-of-lists is non-empty. -/
def allNonempty : ConsList Unit (ConsList Unit A) → Prop
  | ConsList.wrap _ => True
  | ConsList.cons seg rest => isNonempty seg ∧ allNonempty rest

/-- **`partition : list A ⟶ list (list⁺ A)`** (B&dM p.128, `partition = concat°`): a decomposition
    of `x` into a list of non-empty contiguous segments — `ps` is a partition of `x` iff flattening
    `ps` gives `x` and every segment is non-empty. -/
def partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) :=
  fun x ps => cconcat ps = x ∧ allNonempty ps

end Freyd.Alg.RelSet.ListRel
