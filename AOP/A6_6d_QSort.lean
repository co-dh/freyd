/-
  **Quicksort, DERIVED from the relational sorting spec as a HYLOMORPHISM** — a port of AoPA
  `Examples/Sorting/qSort.agda` into the mathlib-free `Rel(Set)` model.

  Same program-independent spec as `A6_6c_ISort`: `sort = ordered? ∘ permute` (diagram order
  `perm ≫ ordered R`).  AoPA derives quicksort as `flatten ∘ unfoldt partition` — a HYLOMORPHISM:
  UNFOLD the list into a binary search tree (pivot + smaller/larger sublists), then FOLD (flatten)
  the tree back.  Its termination is a WELL-FOUNDEDNESS obligation (AoPA `partition-wf`), here a
  `Nat` measure (the list length) that strictly decreases into both sublists.

  AoPA's chain (`○` = right-to-left, we REVERSE to diagram order):

      ordered? ○ permute
    ⊒ fun flatten ○ ordtree? ○ (fun flatten)˘ ○ permute        -- ordflatten
    ⊒ fun flatten ○ (foldT (permute ○ join ○ okl¿) nil)˘        -- fuse1 (converse)
    ⊒ fun flatten ○ (foldT (partition˘ ○ inj₂) …)˘              -- part1 (partition)
    ⊒ fun (flatten ∘ unfoldt partition partition-wf)            -- foldT-to-unfoldt + fun○

  The point-free tree-fusion + converse-of-fold laws are not in this repo, and AoPA itself POSTULATES
  the multiset lemmas the bag-based `permute` needs (`bag-++`, `ε-List-bCons-⇒`, `remove-bg`,
  `m≰n⇒n≤m`).  We keep the port constructive (axioms ⊆ {propext, Quot.sound}):

    * the divide-and-conquer program EMERGES from a `Nat`-measured TREE-hylomorphism uniqueness law
      `TreeHylo.treeHyloFold_unique` (built here — the dual of `TB.treeFold_unique`, with TWO
      recursive calls; `A6_GenHylo` only has the linear one) as `qsort_emerges`; and
    * the refinement `graph qsortFn ⊑ perm ≫ ordered R` is proved by the two facts AoPA's chain
      encodes — partition preserves the multiset (AoPA `split-permute` / the postulated `bag-++`,
      here the constructive `Perm`-congruence `perm_cappend`) and flattening a BST is sorted
      (AoPA `join○ordered²` / `lbound²` / `ε-lbound`).

  Parameters as in `A6_6c_ISort`: an order `R` with a sound Boolean test `leb`, totality, transitivity.
-/
module

public import AOP.A6_GenFold
public import AOP.A6_6b_SortConcrete

set_option linter.unusedVariables false

/-! # A `Nat`-measured TREE hylomorphism uniqueness law (new infrastructure)

  Dual of `TB.treeFold_unique`: a recursive coalgebra `c : S → L + (S × A × S)` with a `Nat` measure
  strictly decreasing into BOTH children.  A function obeying the two-way recursion IS the
  hylomorphism.  (`A6_GenHylo.hyloFold_unique` is the single-recursive-call version, for merges.) -/

namespace Freyd.Alg.RelSet.TreeHylo

open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {L A S C : Type}

/-- One layer of the tree-hylomorphism recursion, abstracting the two recursive calls as `rec`. -/
def treeHyloStep (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C)
    (s : S) (rec : (s' : S) → μ s' < μ s → C → Prop) (res : C) : Prop :=
  match hcs : c s with
  | Sum.inl leaf => res = g leaf
  | Sum.inr (l, a, r) =>
      ∃ rl rr, rec l (hdec s l a r hcs).1 rl ∧ rec r (hdec s l a r hcs).2 rr ∧ res = st rl a rr

/-- The relational tree-hylomorphism of a `Nat`-measured recursive coalgebra. -/
def treeHyloFold (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) : S → C → Prop :=
  WellFounded.fix (measure μ).wf (treeHyloStep c μ hdec g st)

theorem treeHyloFold_unfold (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) (s : S) :
    treeHyloFold c μ hdec g st s
      = treeHyloStep c μ hdec g st s (fun s' _ => treeHyloFold c μ hdec g st s') :=
  WellFounded.fix_eq (measure μ).wf (treeHyloStep c μ hdec g st) s

theorem treeHyloFold_inl (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) {s : S} {leaf : L} {res : C} (hc : c s = Sum.inl leaf) :
    treeHyloFold c μ hdec g st s res ↔ res = g leaf := by
  rw [congrFun (treeHyloFold_unfold c μ hdec g st s) res]
  unfold treeHyloStep
  split
  · rename_i l' heq; rw [hc] at heq; injection heq with h1; subst h1; exact Iff.rfl
  · rename_i l a r heq; rw [hc] at heq; nomatch heq

theorem treeHyloFold_inr (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) {s : S} {l : S} {a : A} {r : S} {res : C}
    (hc : c s = Sum.inr (l, a, r)) :
    treeHyloFold c μ hdec g st s res
      ↔ ∃ rl rr, treeHyloFold c μ hdec g st l rl ∧ treeHyloFold c μ hdec g st r rr
              ∧ res = st rl a rr := by
  rw [congrFun (treeHyloFold_unfold c μ hdec g st s) res]
  unfold treeHyloStep
  split
  · rename_i leaf heq; rw [hc] at heq; nomatch heq
  · rename_i l0 a0 r0 heq
    rw [hc] at heq; injection heq with h1
    injection h1 with h2 h34; injection h34 with h3 h4
    subst h2; subst h3; subst h4; exact Iff.rfl

/-- The tree-hylomorphism as a `Rel(Set)` morphism. -/
def treeHyloR (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) : (⟨S⟩ : RelSet.{0}) ⟶ ⟨C⟩ :=
  treeHyloFold c μ hdec g st

/-- **Tree-hylomorphism uniqueness** (dual of `TB.treeFold_unique`).  A function `h : S → C`
    obeying `h s = match c s with | inl l => g l | inr (l,a,r) => st (h l) a (h r)` IS the
    tree-hylomorphism of the measured coalgebra `c` with algebra `[g, st]`.  Strong induction on `μ`. -/
theorem treeHyloFold_unique (c : S → Sum L (S × A × S)) (μ : S → Nat)
    (hdec : ∀ s l a r, c s = Sum.inr (l, a, r) → μ l < μ s ∧ μ r < μ s)
    (g : L → C) (st : C → A → C → C) (h : S → C)
    (hstep : ∀ s, h s = match c s with
      | Sum.inl l => g l
      | Sum.inr (l, a, r) => st (h l) a (h r)) :
    (graph h : (⟨S⟩ : RelSet.{0}) ⟶ ⟨C⟩) = treeHyloR c μ hdec g st := by
  have key : ∀ s res, (res = h s ↔ treeHyloFold c μ hdec g st s res) := by
    intro s
    refine (measure μ).wf.induction
      (C := fun s => ∀ res, (res = h s ↔ treeHyloFold c μ hdec g st s res)) s ?_
    clear s; intro s IH res
    cases hcs : c s with
    | inl leaf =>
        rw [treeHyloFold_inl c μ hdec g st hcs]
        have hhs : h s = g leaf := by rw [hstep s, hcs]
        rw [hhs]
    | inr lar =>
        obtain ⟨l, a, r⟩ := lar
        rw [treeHyloFold_inr c μ hdec g st hcs]
        have hhs : h s = st (h l) a (h r) := by rw [hstep s, hcs]
        have hIHl := IH l (hdec s l a r hcs).1
        have hIHr := IH r (hdec s l a r hcs).2
        rw [hhs]
        constructor
        · intro hr
          exact ⟨h l, h r, (hIHl (h l)).mp rfl, (hIHr (h r)).mp rfl, hr⟩
        · rintro ⟨rl, rr, hrl, hrr, hres⟩
          rw [(hIHl rl).mpr hrl, (hIHr rr).mpr hrr] at hres
          exact hres
  exact hom_ext fun s res => key s res

end Freyd.Alg.RelSet.TreeHylo

/-! # Quicksort as a tree-hylomorphism -/

namespace Freyd.Alg.RelSet.QSort

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-! ## List measure and filter on `ConsList Unit A` -/

/-- List length on `ConsList Unit A`. -/
def clen : ConsList Unit A → Nat
  | ConsList.wrap _   => 0
  | ConsList.cons _ x => clen x + 1

/-- Keep the elements satisfying `p` (`cappend` is reused from `ListRel`). -/
def cfilter (p : A → Bool) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.wrap ()
  | ConsList.cons a x => match p a with
    | true  => ConsList.cons a (cfilter p x)
    | false => cfilter p x

theorem clen_cfilter_le (p : A → Bool) : ∀ x : ConsList Unit A, clen (cfilter p x) ≤ clen x
  | ConsList.wrap _   => Nat.le_refl 0
  | ConsList.cons a x => by
      show clen (cfilter p (ConsList.cons a x)) ≤ clen x + 1
      unfold cfilter
      cases p a with
      | true  => exact Nat.succ_le_succ (clen_cfilter_le p x)
      | false => exact Nat.le_succ_of_le (clen_cfilter_le p x)

/-- Elements of `cfilter p x` satisfy `p` (used for the pivot ordering). -/
theorem mem_cfilter (p : A → Bool) : ∀ {x : ConsList Unit A} {y : A},
    inlistP (cfilter p x) y → p y = true
  | ConsList.wrap _, y, h => h.elim
  | ConsList.cons a x, y, h => by
      unfold cfilter at h
      cases hp : p a with
      | true  =>
          rw [hp] at h
          cases h with
          | inl hya => rw [hya]; exact hp
          | inr hx  => exact mem_cfilter p hx
      | false => rw [hp] at h; exact mem_cfilter p h

/-! ## `cappend` membership, permutation congruences, `ordered` of an append -/

/-- Membership through `cappend`. -/
theorem inlist_cappend : ∀ {L M : ConsList Unit A} {c : A},
    inlistP (cappend L M) c → inlistP L c ∨ inlistP M c
  | ConsList.wrap _, M, c, h => Or.inr h
  | ConsList.cons b L, M, c, h => by
      simp only [cappend, inlistP] at h
      cases h with
      | inl hcb => exact Or.inl (Or.inl hcb)
      | inr hc  => exact (inlist_cappend hc).elim (fun h => Or.inl (Or.inr h)) Or.inr

/-- `cappend` respects `Perm` on its LEFT argument (induction on the `Perm` derivation). -/
theorem perm_cappend_left {M : ConsList Unit A} :
    ∀ {L L' : ConsList Unit A}, Perm L L' → Perm (cappend L M) (cappend L' M)
  | _, _, Perm.nil => Perm.refl _
  | _, _, Perm.cons a h => Perm.cons a (perm_cappend_left h)
  | _, _, Perm.swap a b x => Perm.swap a b (cappend x M)
  | _, _, Perm.trans h1 h2 => Perm.trans (perm_cappend_left h1) (perm_cappend_left h2)

/-- `cappend` respects `Perm` on its RIGHT argument (induction on the left list). -/
theorem perm_cappend_right : ∀ (L : ConsList Unit A) {M M' : ConsList Unit A},
    Perm M M' → Perm (cappend L M) (cappend L M')
  | ConsList.wrap _, M, M', h => h
  | ConsList.cons a L, M, M', h => Perm.cons a (perm_cappend_right L h)

/-- `cappend` is a `Perm`-congruence (AoPA's postulated `bag-++` / `++⇒permute`, here constructive). -/
theorem perm_cappend {L L' M M' : ConsList Unit A} (hL : Perm L L') (hM : Perm M M') :
    Perm (cappend L M) (cappend L' M') :=
  Perm.trans (perm_cappend_left hL) (perm_cappend_right L' hM)

/-- Moving the head into the middle of an append is a permutation (AoPA `bCons-commute-++`). -/
theorem perm_cons_cappend (a : A) : ∀ L M : ConsList Unit A,
    Perm (ConsList.cons a (cappend L M)) (cappend L (ConsList.cons a M))
  | ConsList.wrap _, M => Perm.refl _
  | ConsList.cons b L, M => by
      show Perm (ConsList.cons a (ConsList.cons b (cappend L M)))
                (ConsList.cons b (cappend L (ConsList.cons a M)))
      exact Perm.trans (Perm.swap a b (cappend L M))
              (Perm.cons b (perm_cons_cappend a L M))

/-- Partition preserves the multiset: `x` is a permutation of `(keep p x) ++ (drop p x)` (AoPA
    `split-permute`). -/
theorem partition_perm (p : A → Bool) : ∀ x : ConsList Unit A,
    Perm x (cappend (cfilter p x) (cfilter (fun y => !p y) x))
  | ConsList.wrap _ => Perm.nil
  | ConsList.cons a x => by
      show Perm (ConsList.cons a x)
             (cappend (cfilter p (ConsList.cons a x)) (cfilter (fun y => !p y) (ConsList.cons a x)))
      have ih := partition_perm p x
      unfold cfilter
      cases hp : p a with
      | true =>
          simp only [Bool.not_true]
          -- left = a :: keep, right = drop ; cappend (a::keep) drop = a :: cappend keep drop
          exact Perm.cons a ih
      | false =>
          simp only [Bool.not_false]
          -- left = keep, right = a :: drop
          exact Perm.trans (Perm.cons a ih)
                  (perm_cons_cappend a (cfilter p x) (cfilter (fun y => !p y) x))

/-- Sortedness of an append: if `L`, `M` are sorted and every element of `L` is `R`-below every
    element of `M`, then `cappend L M` is sorted (AoPA `join○ordered²` / `lbound²`). -/
theorem ordered_cappend {R : A → A → Prop} :
    ∀ {L M : ConsList Unit A}, orderedP R L → orderedP R M →
      (∀ l m, inlistP L l → inlistP M m → R l m) → orderedP R (cappend L M)
  | ConsList.wrap _, M, _, hM, _ => hM
  | ConsList.cons b L, M, hL, hM, hcross => by
      show orderedP R (ConsList.cons b (cappend L M))
      refine ⟨fun c hc => ?_, ordered_cappend hL.2 hM (fun l m hl hm => hcross l m (Or.inr hl) hm)⟩
      cases inlist_cappend hc with
      | inl hcL => exact hL.1 c hcL
      | inr hcM => exact hcross b c (Or.inl rfl) hcM

/-! ## The quicksort coalgebra, program, and emergence -/

/-- The pivot predicate "≤ pivot". -/
def ple (leb : A → A → Bool) (a : A) : A → Bool := fun y => leb y a
/-- The pivot predicate "> pivot". -/
def pgt (leb : A → A → Bool) (a : A) : A → Bool := fun y => !leb y a

/-- **The partition coalgebra** (AoPA `partition`): a leaf on `[]`, else pivot + (≤pivot, >pivot). -/
def qpart (leb : A → A → Bool) : ConsList Unit A → Sum Unit (ConsList Unit A × A × ConsList Unit A)
  | ConsList.wrap _   => Sum.inl ()
  | ConsList.cons a x => Sum.inr (cfilter (ple leb a) x, a, cfilter (pgt leb a) x)

/-- Both children are strictly shorter (AoPA `split⊑<`, `partition-wf`). -/
theorem qpart_dec (leb : A → A → Bool) : ∀ s l a r,
    qpart leb s = Sum.inr (l, a, r) → clen l < clen s ∧ clen r < clen s
  | ConsList.wrap _, l, a, r, h => by nomatch h
  | ConsList.cons b x, l, a, r, h => by
      have h' : (cfilter (ple leb b) x, b, cfilter (pgt leb b) x) = (l, a, r) := Sum.inr.inj h
      injection h' with hl h2; injection h2 with ha hr
      subst hl; subst hr
      exact ⟨Nat.lt_succ_of_le (clen_cfilter_le (ple leb b) x),
             Nat.lt_succ_of_le (clen_cfilter_le (pgt leb b) x)⟩

/-- **Quicksort** `qsortFn = flatten ∘ unfoldt partition` (AoPA), by well-founded recursion on the
    list length: `[] ↦ []`, `x::xs ↦ qsort(≤x) ++ x :: qsort(>x)`. -/
def qsortFn (leb : A → A → Bool) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.wrap ()
  | ConsList.cons a x =>
      cappend (qsortFn leb (cfilter (ple leb a) x))
              (ConsList.cons a (qsortFn leb (cfilter (pgt leb a) x)))
  termination_by x => clen x
  decreasing_by
    · exact Nat.lt_succ_of_le (clen_cfilter_le (ple leb a) x)
    · exact Nat.lt_succ_of_le (clen_cfilter_le (pgt leb a) x)

/-- Equation lemma for the `wrap` case (WF defs do not reduce by `rfl`). -/
theorem qsortFn_wrap (leb : A → A → Bool) (u : Unit) :
    qsortFn leb (ConsList.wrap u) = ConsList.wrap () := by simp only [qsortFn]

/-- Equation lemma for the `cons` case. -/
theorem qsortFn_cons (leb : A → A → Bool) (a : A) (x : ConsList Unit A) :
    qsortFn leb (ConsList.cons a x)
      = cappend (qsortFn leb (cfilter (ple leb a) x))
          (ConsList.cons a (qsortFn leb (cfilter (pgt leb a) x))) := by simp only [qsortFn]

/-- The quicksort algebra `[nil, join]`: `join l a r = l ++ a :: r` (AoPA `join`). -/
def qjoin (l : ConsList Unit A) (a : A) (r : ConsList Unit A) : ConsList Unit A :=
  cappend l (ConsList.cons a r)

/-- **The program EMERGES from the tree-hylomorphism law** (AoPA `foldT-to-unfoldt` + `fun∘`):
    `graph qsortFn = treeHyloR qpart clen qpart_dec (fun _ => nil) qjoin`.  The divide-and-conquer
    recursion is not hand-certified — `qsortFn` obeys the two-way hylo recurrence, so
    `TreeHylo.treeHyloFold_unique` emits it as the hylomorphism. -/
theorem qsort_emerges (leb : A → A → Bool) :
    (graph (qsortFn leb) : dList A ⟶ dList A)
      = TreeHylo.treeHyloR (qpart leb) clen (qpart_dec leb) (fun _ => ConsList.wrap ()) qjoin := by
  refine TreeHylo.treeHyloFold_unique (qpart leb) clen (qpart_dec leb)
    (fun _ => ConsList.wrap ()) qjoin (qsortFn leb) ?_
  intro s
  cases s with
  | wrap u => simp only [qsortFn_wrap, qpart]
  | cons a x =>
      rw [qsortFn_cons]
      simp only [qpart, qjoin]

/-! ## Correctness: quicksort produces a sorted permutation -/

/-- `qsortFn x` is a permutation of `x` (AoPA `permute` half: `split-permute` + `bag-++`). -/
theorem qsort_perm (leb : A → A → Bool) : ∀ x : ConsList Unit A, Perm x (qsortFn leb x)
  | ConsList.wrap u => by cases u; rw [qsortFn_wrap]; exact Perm.nil
  | ConsList.cons a x => by
      rw [qsortFn_cons]
      -- IH on both (strictly shorter) sublists
      have ihl := qsort_perm leb (cfilter (ple leb a) x)
      have ihr := qsort_perm leb (cfilter (pgt leb a) x)
      -- x ~ keep ++ drop  (partition_perm with p = ple)
      have hpart := partition_perm (ple leb a) x
      -- assemble: a::x ~ a::(keep++drop) ~ a::(L++R) ~ (L ++ a::R)
      refine Perm.trans (Perm.cons a hpart) (Perm.trans (Perm.cons a (perm_cappend ihl ihr)) ?_)
      exact perm_cons_cappend a (qsortFn leb (cfilter (ple leb a) x))
              (qsortFn leb (cfilter (pgt leb a) x))
  termination_by x => clen x
  decreasing_by
    · exact Nat.lt_succ_of_le (clen_cfilter_le (ple leb a) x)
    · exact Nat.lt_succ_of_le (clen_cfilter_le (pgt leb a) x)

/-- `qsortFn x` is sorted (AoPA `ordered?` half: `join○ordered²`, `ε-lbound`).  Needs the order
    total (`htotal`) with a sound test (`hleb`) and transitive (`htrans`). -/
theorem qsort_sorted {R : A → A → Prop} {leb : A → A → Bool}
    (hleb : ∀ a b, leb a b = true → R a b)
    (htotal : ∀ a b, leb a b = false → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ x : ConsList Unit A, orderedP R (qsortFn leb x)
  | ConsList.wrap u => by rw [qsortFn_wrap]; trivial
  | ConsList.cons a x => by
      rw [qsortFn_cons]
      have ihl := qsort_sorted hleb htotal htrans (cfilter (ple leb a) x)
      have ihr := qsort_sorted hleb htotal htrans (cfilter (pgt leb a) x)
      -- every element of the sorted left list is ≤ a  (it came from `keep` = ≤a)
      have hL_le : ∀ y, inlistP (qsortFn leb (cfilter (ple leb a) x)) y → R y a := fun y hy => by
        have hy' : inlistP (cfilter (ple leb a) x) y :=
          Sort.perm_mem (Perm.symm (qsort_perm leb _)) hy
        exact hleb y a (mem_cfilter (ple leb a) hy')
      -- every element of the sorted right list is ≥ a  (it came from `drop` = >a)
      have hR_ge : ∀ y, inlistP (qsortFn leb (cfilter (pgt leb a) x)) y → R a y := fun y hy => by
        have hy' : inlistP (cfilter (pgt leb a) x) y :=
          Sort.perm_mem (Perm.symm (qsort_perm leb _)) hy
        have : (!leb y a) = true := mem_cfilter (pgt leb a) hy'
        exact htotal y a (by simpa using this)
      -- `a :: (sorted right)` is sorted
      have hMord : orderedP R (ConsList.cons a (qsortFn leb (cfilter (pgt leb a) x))) := ⟨hR_ge, ihr⟩
      -- cross condition: every left element R-below every element of `a :: right`
      refine ordered_cappend ihl hMord (fun l m hl hm => ?_)
      cases hm with
      | inl hma => rw [hma]; exact hL_le l hl
      | inr hmR => exact htrans l a m (hL_le l hl) (hR_ge m hmR)
  termination_by x => clen x
  decreasing_by
    · exact Nat.lt_succ_of_le (clen_cfilter_le (ple leb a) x)
    · exact Nat.lt_succ_of_le (clen_cfilter_le (pgt leb a) x)

/-- **The sorting specification** (shared with `A6_6c_ISort`), `sort = ordered? ∘ permute`. -/
def sortSpec (R : A → A → Prop) : dList A ⟶ dList A := perm ≫ ordered R

/-- **HEADLINE — quicksort refines the sorting spec**: `graph qsortFn ⊑ perm ≫ ordered R`.
    Mirrors AoPA's `ordered? ○ permute ⊒ fun (flatten ∘ unfoldt partition)`.  The program is the
    tree-hylomorphism `qsort_emerges`; here we prove it produces a SORTED PERMUTATION. -/
theorem qsort_refines_spec {R : A → A → Prop} {leb : A → A → Bool}
    (hleb : ∀ a b, leb a b = true → R a b)
    (htotal : ∀ a b, leb a b = false → R b a)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    (graph (qsortFn leb) : dList A ⟶ dList A) ⊑ sortSpec R := by
  rw [le_iff]; intro x y hxy
  refine ⟨qsortFn leb x, qsort_perm leb x, ?_⟩
  exact ⟨hxy.symm, qsort_sorted hleb htotal htrans x⟩

/-! ## The derivation instantiated on `ℕ` (`Nat.ble` sound, total, transitive)

  A concrete `=`-example is impractical for the WF-recursive `qsortFn` (it does not reduce under
  `rfl`/`decide` — see the SKILL note), so the sanity check is the headline itself, instantiated:
  quicksort on `ℕ` refines the `≤`-sorting spec. -/
theorem qsort_refines_spec_nat :
    (graph (qsortFn Nat.ble) : dList Nat ⟶ dList Nat) ⊑ sortSpec (· ≤ ·) :=
  qsort_refines_spec
    (fun a b h => Nat.le_of_ble_eq_true h)
    (fun a b h => by
      rcases Nat.lt_or_ge b a with hlt | hge
      · exact Nat.le_of_lt hlt
      · rw [Nat.ble_eq_true_of_le hge] at h; exact absurd h (by decide))
    (fun a b c => Nat.le_trans)

end Freyd.Alg.RelSet.QSort
