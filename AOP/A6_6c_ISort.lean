/-
  **Insertion sort, DERIVED from the relational sorting spec** — a port of AoPA
  `Examples/Sorting/iSort.agda` into the mathlib-free `Rel(Set)` model.

  The specification is program-independent and exactly the book's `sort = ordered? ∘ permute`
  (AoPA `sort = ordered? ○ permute`; here, in DIAGRAM order, `perm ≫ ordered R`): `y` is a sorted
  permutation of `x`.  `AOP.A6_6_Sort`/`A6_6b_SortConcrete` already derive SELECTION sort for this
  same spec (as the converse of a catamorphism); THIS file derives the DIFFERENT algorithm
  `foldr insert []` and reuses their `perm`/`ordered`/`perm_mem` verbatim.

  AoPA derives insertion sort by two fusions (`○` = right-to-left; we REVERSE to diagram order):

      ordered? ○ permute
    ⊒ ordered? ○ foldR combine nil          -- permute-is-fold  (perm as a fold of `combine`)
    ⊒ foldR (fun (uncurry insert)) nil      -- foldR-fusion-⊒ ordered? ins-step ins-base
    = fun (foldr insert [])                 -- foldR-to-foldr

  where `combine` is the RELATIONAL insert (insert `a` at ANY position) and `insert ⊑ combine`.
  The point-free fusion law (`foldR-fusion-⊒`) is, in this repo, `relCata_le_comp`, which routes
  through the Eilenberg–Wright bridge `cataR_eq_relCata` and hence pulls `Classical.choice`.  To
  keep the port constructive (axioms ⊆ {propext, Quot.sound}, as AoPA is), we instead:

    * EMERGE the program by the constructive fold-uniqueness law `CL.consFold_unique`
      (`isort_emerges : graph isortFn = cataR insertAlg`) — insertion sort IS a catamorphism; and
    * prove the refinement `graph isortFn ⊑ perm ≫ ordered R` by the two facts AoPA's fusion
      encodes: `insert` PERMUTES (AoPA `bagify-homo`, via the relational `combine` and `insert ⊑
      combine`) and `insert` ESTABLISHES SORTEDNESS (AoPA `insert-respects-order`/`-lbound`,
      `relax-lbound`).

  Parameters mirror AoPA's `DecTotalOrder`: an order `R` with a Boolean test `leb` sound for it
  (`hleb`), totality (`htotal`, AoPA `≰-elim`+`<-relax`) and transitivity (`htrans`, `≤-trans`).
-/
module

public import AOP.A6_GenFold
public import AOP.A6_6b_SortConcrete

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.ISort

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-! ## The insertion function and insertion sort -/

/-- `insert a x` slides `a` into `x` past every element it is not `leb`-below (AoPA `insert`,
    `iSort.agda`'s `Second-try.insert`). -/
def insert (leb : A → A → Bool) (a : A) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.cons a (ConsList.wrap ())
  | ConsList.cons b x => match leb a b with
    | true  => ConsList.cons a (ConsList.cons b x)
    | false => ConsList.cons b (insert leb a x)

/-- **Insertion sort** `isortFn = foldr insert []` (AoPA `isort = foldr insert []`), a cons-list
    fold: nil ↦ nil, `cons a x ↦ insert a (isortFn x)`. -/
def isortFn (leb : A → A → Bool) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.wrap ()
  | ConsList.cons a x => insert leb a (isortFn leb x)

/-- The insertion-sort algebra `[nil, insert]` over the carrier `list A` (`consScalarAlg` with
    base `nil` and step `insert`). -/
def insertAlg (leb : A → A → Bool) : Fobj Unit A (dList A) ⟶ dList A :=
  consScalarAlg (fun _ => ConsList.wrap ()) (insert leb)

/-- **The program EMERGES from the fold-uniqueness law** (AoPA `foldR-to-foldr insert []`):
    `graph isortFn = cataR insertAlg`.  The recursion is not hand-written — `isortFn` obeys the
    cons-list fold equations (both `rfl`), so `CL.consFold_unique` emits it as the catamorphism. -/
theorem isort_emerges (leb : A → A → Bool) :
    (graph (isortFn leb) : dList A ⟶ dList A) = cataR (insertAlg leb) :=
  CL.consFold_unique (fun _ => ConsList.wrap ()) (insert leb) (isortFn leb)
    (fun _ => rfl) (fun _ _ => rfl)

/-! ## `combine`, the RELATIONAL insert, and `insert ⊑ combine` (AoPA `Combine`)

  AoPA's `combine y (a, x)` holds when `y` is `x` with `a` inserted at some position.  We give it
  as a structural relation and prove `insert ⊑ combine` (AoPA `insert⊑combine`); `combine` is the
  step of `permute` as a fold, so this is the point-free witness that `insert` permutes. -/

/-- `combine x a y` : `y` is `x` with `a` spliced in at some position (AoPA `combine`, arguments
    curried and reordered to diagram convenience). -/
def combineP (a : A) : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, y   => y = ConsList.cons a (ConsList.wrap ())
  | ConsList.cons b x, y =>
      y = ConsList.cons a (ConsList.cons b x) ∨
      ∃ z, combineP a x z ∧ y = ConsList.cons b z

/-- Splicing `a` into `x` yields a permutation of `a :: x` (AoPA content of `bagify-homo`). -/
theorem combine_perm (leb : A → A → Bool) (a : A) :
    ∀ {x y : ConsList Unit A}, combineP a x y → Perm (ConsList.cons a x) y
  | ConsList.wrap u, y, h => by
      cases u; rw [(h : y = _)]; exact Perm.refl _
  | ConsList.cons b x, y, h => by
      cases h with
      | inl h => rw [h]; exact Perm.refl _
      | inr h =>
          obtain ⟨z, hz, hy⟩ := h
          rw [hy]
          -- a::b::x  --swap-->  b::a::x  --cons b (combine_perm)-->  b::z
          exact Perm.trans (Perm.swap a b x) (Perm.cons b (combine_perm leb a hz))

/-- **`insert ⊑ combine`** (AoPA `insert⊑combine`): the deterministic `insert` is one branch of
    the relational splice. -/
theorem insert_le_combine (leb : A → A → Bool) (a : A) :
    ∀ x : ConsList Unit A, combineP a x (insert leb a x)
  | ConsList.wrap _   => rfl
  | ConsList.cons b x => by
      show combineP a (ConsList.cons b x) (insert leb a (ConsList.cons b x))
      unfold insert
      cases h : leb a b with
      | true  => exact Or.inl rfl
      | false => exact Or.inr ⟨insert leb a x, insert_le_combine leb a x, rfl⟩

/-! ## Insertion permutes (AoPA `bagify-homo`) -/

/-- `insert a x` is a permutation of `a :: x`.  Directly from `insert ⊑ combine` and
    `combine_perm`. -/
theorem insert_perm (leb : A → A → Bool) (a : A) (x : ConsList Unit A) :
    Perm (ConsList.cons a x) (insert leb a x) :=
  combine_perm leb a (insert_le_combine leb a x)

/-! ## Insertion establishes sortedness (AoPA `insert-respects-order`, `-lbound`, `relax-lbound`)

  Reuses `ListRel.orderedP`/`inlistP` and `Sort.perm_mem` from the existing sort files. -/

/-- Membership through `insert`: an element of `insert a x` is `a` or was already in `x`.  AoPA
    handles this inside `insert-respects-lbound` by recursion; we get it free from `insert_perm`
    and the existing `Sort.perm_mem`. -/
theorem inlist_insert (leb : A → A → Bool) (a : A) (x : ConsList Unit A) {c : A}
    (h : inlistP (insert leb a x) c) : c = a ∨ inlistP x c :=
  Sort.perm_mem (Perm.symm (insert_perm leb a x)) h

/-- **`insert` respects and establishes sortedness** (AoPA `insert-respects-order`): if `x` is
    sorted then so is `insert a x`.  Needs the order to be transitive (`htrans`, AoPA `≤-trans`)
    and total with a sound test (`hleb`, `htotal`, AoPA `≰-elim`/`<-relax`). -/
theorem insert_ordered {R : A → A → Prop} {leb : A → A → Bool}
    (hleb : ∀ a b, leb a b = true → R a b)
    (htotal : ∀ a b, leb a b = false → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) (a : A) :
    ∀ x : ConsList Unit A, orderedP R x → orderedP R (insert leb a x)
  | ConsList.wrap _, _ =>
      -- insert a [] = [a] : sorted vacuously
      ⟨fun b hb => hb.elim, trivial⟩
  | ConsList.cons b x, hx => by
      show orderedP R (insert leb a (ConsList.cons b x))
      unfold insert
      cases h : leb a b with
      | true =>
          -- a::b::x : a below b (test) and below all of x (transitivity through b)
          refine ⟨fun c hc => ?_, hx⟩
          cases hc with
          | inl hcb => rw [hcb]; exact hleb a b h
          | inr hcx => exact htrans a b c (hleb a b h) (hx.1 c hcx)
      | false =>
          -- b :: insert a x : b below everything in insert a x, and insert a x sorted (IH)
          refine ⟨fun c hc => ?_, insert_ordered hleb htotal htrans a x hx.2⟩
          cases inlist_insert leb a x hc with
          | inl hca => rw [hca]; exact htotal a b h
          | inr hcx => exact hx.1 c hcx

/-! ## The two whole-list facts, then the refinement headline -/

/-- `isortFn x` is a permutation of `x` (AoPA `permute ⊒ perm`, the permutation half). -/
theorem isort_perm (leb : A → A → Bool) : ∀ x : ConsList Unit A, Perm x (isortFn leb x)
  | ConsList.wrap _   => Perm.nil
  | ConsList.cons a x =>
      -- a::x  --cons a (IH)-->  a::(isortFn x)  --insert_perm-->  insert a (isortFn x)
      Perm.trans (Perm.cons a (isort_perm leb x)) (insert_perm leb a (isortFn leb x))

/-- `isortFn x` is sorted (AoPA `ordered?` half of the derivation). -/
theorem isort_sorted {R : A → A → Prop} {leb : A → A → Bool}
    (hleb : ∀ a b, leb a b = true → R a b)
    (htotal : ∀ a b, leb a b = false → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ x : ConsList Unit A, orderedP R (isortFn leb x)
  | ConsList.wrap _   => trivial
  | ConsList.cons a x =>
      insert_ordered hleb htotal htrans a (isortFn leb x) (isort_sorted hleb htotal htrans x)

/-- **The sorting specification** (program-independent), the book's `sort = ordered? ∘ permute`
    in diagram order: `(perm ≫ ordered R) x y` iff `y` is a sorted permutation of `x`. -/
def sortSpec (R : A → A → Prop) : dList A ⟶ dList A := perm ≫ ordered R

/-- **HEADLINE — insertion sort refines the sorting spec**: `graph isortFn ⊑ perm ≫ ordered R`.
    Mirrors AoPA's `ordered? ○ permute ⊒ fun (foldr insert [])`.  The program itself is the
    catamorphism `isort_emerges`; here we prove it produces a SORTED PERMUTATION, i.e. it refines
    `sortSpec`.  Together with `isort_emerges` this is the full AoPA derivation. -/
theorem isort_refines_spec {R : A → A → Prop} {leb : A → A → Bool}
    (hleb : ∀ a b, leb a b = true → R a b)
    (htotal : ∀ a b, leb a b = false → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    (graph (isortFn leb) : dList A ⟶ dList A) ⊑ sortSpec R := by
  rw [le_iff]; intro x y hxy
  -- hxy : y = isortFn x.  Witness the permutation `z := isortFn x = y`.
  refine ⟨isortFn leb x, isort_perm leb x, ?_⟩
  exact ⟨hxy.symm, isort_sorted hleb htotal htrans x⟩

/-! ## Sanity checks on `ℕ` with `Nat.ble` -/

example : isortFn Nat.ble (ConsList.cons 3 (ConsList.cons 1 (ConsList.cons 2 (ConsList.wrap ()))))
    = ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 3 (ConsList.wrap ()))) := rfl

example : isortFn Nat.ble
      (ConsList.cons 2 (ConsList.cons 2 (ConsList.cons 1 (ConsList.wrap ()))))
    = ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 2 (ConsList.wrap ()))) := rfl

end Freyd.Alg.RelSet.ISort
