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

  Parameters mirror AoPA's `DecTotalOrder`: a DECIDABLE order `R` (`DecidableRel R`, the test
  `insert` runs), connected (`hconn`, AoPA `≰-elim`+`<-relax`) and transitive (`htrans`, `≤-trans`).
-/
module

public import AOP.A6_GenFold
public import AOP.A6_6b_SortConcrete
import AOP.CalcSteps

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.ISort

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-! ## The insertion function and insertion sort -/

/-- `insert a x` slides `a` into `x` past every element it is not `R`-below (AoPA `insert`,
    `iSort.agda`'s `Second-try.insert`). -/
public def insert (R : A → A → Prop) [DecidableRel R] (a : A) : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.cons a (ConsList.wrap ())
  | ConsList.cons b x =>
    if R a b then ConsList.cons a (ConsList.cons b x) else ConsList.cons b (insert R a x)

/-- **Insertion sort** `isortFn = foldr insert []` (AoPA `isort = foldr insert []`), a cons-list
    fold: nil ↦ nil, `cons a x ↦ insert a (isortFn x)`. -/
def isortFn (R : A → A → Prop) [DecidableRel R] : ConsList Unit A → ConsList Unit A
  | ConsList.wrap _   => ConsList.wrap ()
  | ConsList.cons a x => insert R a (isortFn R x)

/-- The insertion-sort algebra `[nil, insert]` over the carrier `list A` (`consScalarAlg` with
    base `nil` and step `insert`). -/
def insertAlg (R : A → A → Prop) [DecidableRel R] : Fobj Unit A (dList A) ⟶ dList A :=
  consScalarAlg (fun _ => ConsList.wrap ()) (insert R)

/-- **The program EMERGES from the fold-uniqueness law** (AoPA `foldR-to-foldr insert []`):
    `graph isortFn = cataR insertAlg`.  The recursion is not hand-written — `isortFn` obeys the
    cons-list fold equations (both `rfl`), so `CL.consFold_unique` emits it as the catamorphism. -/
theorem isort_emerges (R : A → A → Prop) [DecidableRel R] :
    (graph (isortFn R) : dList A ⟶ dList A) = cataR (insertAlg R) :=
  CL.consFold_unique (fun _ => ConsList.wrap ()) (insert R) (isortFn R)
    (fun _ => rfl) (fun _ _ => rfl)

/-! ## `combine`, the RELATIONAL insert, and `insert ⊑ combine` (AoPA `Combine`)

  AoPA's `combine y (a, x)` holds when `y` is `x` with `a` inserted at some position.  We give it
  as a structural relation and prove `insert ⊑ combine` (AoPA `insert⊑combine`); `combine` is the
  step of `permute` as a fold, so this is the point-free witness that `insert` permutes. -/

/-- `combine x a y` : `y` is `x` with `a` spliced in at some position (AoPA `combine`, arguments
    curried and reordered to diagram convenience). -/
@[expose] public def combineP (a : A) : ConsList Unit A → ConsList Unit A → Prop
  | ConsList.wrap _, y   => y = ConsList.cons a (ConsList.wrap ())
  | ConsList.cons b x, y =>
      y = ConsList.cons a (ConsList.cons b x) ∨
      ∃ z, combineP a x z ∧ y = ConsList.cons b z

/-- Splicing `a` into `x` yields a permutation of `a :: x` (AoPA content of `bagify-homo`). -/
public theorem combine_perm (a : A) :
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
          exact Perm.trans (Perm.swap a b x) (Perm.cons b (combine_perm a hz))

/-- **`insert ⊑ combine`** (AoPA `insert⊑combine`): the deterministic `insert` is one branch of
    the relational splice. -/
public theorem insert_le_combine (R : A → A → Prop) [DecidableRel R] (a : A) :
    ∀ x : ConsList Unit A, combineP a x (insert R a x)
  | ConsList.wrap _   => rfl
  | ConsList.cons b x => by
      show combineP a (ConsList.cons b x) (insert R a (ConsList.cons b x))
      unfold insert
      split
      · exact Or.inl rfl
      · exact Or.inr ⟨insert R a x, insert_le_combine R a x, rfl⟩

/-! ## Insertion permutes (AoPA `bagify-homo`) -/

/-- `insert a x` is a permutation of `a :: x`.  Directly from `insert ⊑ combine` and
    `combine_perm`. -/
theorem insert_perm (R : A → A → Prop) [DecidableRel R] (a : A) (x : ConsList Unit A) :
    Perm (ConsList.cons a x) (insert R a x) :=
  combine_perm a (insert_le_combine R a x)

/-! ## Insertion establishes sortedness (AoPA `insert-respects-order`, `-lbound`, `relax-lbound`)

  Reuses `ListRel.orderedP`/`inlistP` and `Sort.perm_mem` from the existing sort files. -/

/-- Membership through `insert`: an element of `insert a x` is `a` or was already in `x`.  AoPA
    handles this inside `insert-respects-lbound` by recursion; we get it free from `insert_perm`
    and the existing `Sort.perm_mem`. -/
theorem inlist_insert (R : A → A → Prop) [DecidableRel R] (a : A) (x : ConsList Unit A) {c : A}
    (h : inlistP (insert R a x) c) : c = a ∨ inlistP x c :=
  Sort.perm_mem (Perm.symm (insert_perm R a x)) h

/-- **`insert` respects and establishes sortedness** (AoPA `insert-respects-order`): if `x` is
    sorted then so is `insert a x`.  Needs the order to be transitive (`htrans`, AoPA `≤-trans`)
    and connected (`hconn`, AoPA `≰-elim`/`<-relax`). -/
theorem insert_ordered {R : A → A → Prop} [DecidableRel R] (hconn : connected R)
    (htrans : ∀ a b c, R a b → R b c → R a c) (a : A) :
    ∀ x : ConsList Unit A, orderedP R x → orderedP R (insert R a x)
  | ConsList.wrap _, _ =>
      -- insert a [] = [a] : sorted vacuously
      ⟨fun b hb => hb.elim, trivial⟩
  | ConsList.cons b x, hx => by
      show orderedP R (insert R a (ConsList.cons b x))
      unfold insert
      split
      · -- a::b::x : a below b (test) and below all of x (transitivity through b)
        rename_i h
        refine ⟨fun c hc => ?_, hx⟩
        cases hc with
        | inl hcb => rw [hcb]; exact h
        | inr hcx => exact htrans a b c h (hx.1 c hcx)
      · -- b :: insert a x : b below everything in insert a x, and insert a x sorted (IH)
        rename_i h
        refine ⟨fun c hc => ?_, insert_ordered hconn htrans a x hx.2⟩
        cases inlist_insert R a x hc with
        | inl hca => rw [hca]; exact (hconn a b).resolve_left h
        | inr hcx => exact hx.1 c hcx

/-! ## The two whole-list facts, then the refinement headline -/

/-- `isortFn x` is a permutation of `x` (AoPA `permute ⊒ perm`, the permutation half). -/
theorem isort_perm (R : A → A → Prop) [DecidableRel R] :
    ∀ x : ConsList Unit A, Perm x (isortFn R x)
  | ConsList.wrap _   => Perm.nil
  | ConsList.cons a x =>
      -- a::x  --cons a (IH)-->  a::(isortFn x)  --insert_perm-->  insert a (isortFn x)
      Perm.trans (Perm.cons a (isort_perm R x)) (insert_perm R a (isortFn R x))

/-- `isortFn x` is sorted (AoPA `ordered?` half of the derivation). -/
theorem isort_sorted {R : A → A → Prop} [DecidableRel R] (hconn : connected R)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ x : ConsList Unit A, orderedP R (isortFn R x)
  | ConsList.wrap _   => trivial
  | ConsList.cons a x =>
      insert_ordered hconn htrans a (isortFn R x) (isort_sorted hconn htrans x)

/-- **The sorting specification** (program-independent), the book's `sort = ordered? ∘ permute`
    in diagram order: `(perm ≫ ordered R) x y` iff `y` is a sorted permutation of `x`. -/
def sortSpec (R : A → A → Prop) : dList A ⟶ dList A := perm ≫ ordered R

/-- **HEADLINE — insertion sort refines the sorting spec**: `graph isortFn ⊑ perm ≫ ordered R`.
    Mirrors AoPA's `ordered? ○ permute ⊒ fun (foldr insert [])`.  The program itself is the
    catamorphism `isort_emerges`; here we prove it produces a SORTED PERMUTATION, i.e. it refines
    `sortSpec`.  Together with `isort_emerges` this is the full AoPA derivation. -/
theorem isort_refines_spec {R : A → A → Prop} [DecidableRel R] (hconn : connected R)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    (graph (isortFn R) : dList A ⟶ dList A) ⊑ sortSpec R := by
  rw [le_iff]; intro x y hxy
  -- hxy : y = isortFn x.  Witness the permutation `z := isortFn x = y`.
  refine ⟨isortFn R x, isort_perm R x, ?_⟩
  exact ⟨hxy.symm, isort_sorted hconn htrans x⟩

/-! ## Exercise 6.30 (B&dM p.157): insertion sort from `perm = ⦇[nil, add]⦈`

  The same derivation point-free, each step one declaration, for ANY `insert` meeting the exercise's
  condition; the `insert` above is one such. -/

/-- B&dM §5.6 `add = cat (𝟙×cons) exch (𝟙×cat°)`, mirrored: `add(a,x)` is `x` with `a` spliced in
    at some position, which is `combineP`. -/
@[expose] public def add : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A := fun p y => combineP p.1 p.2 y

/-- Splicing at the front: `add(a,x) ∋ a::x`. -/
theorem combine_head (a : A) : ∀ x : ConsList Unit A, combineP a x (ConsList.cons a x)
  | ConsList.wrap u => by cases u; rfl
  | ConsList.cons _ _ => Or.inl rfl

/-- A permutation of `x` with `a` spliced in is a permutation of `x` with `a` spliced in last:
    `perm` passes through `add`. -/
theorem perm_combine {s r : ConsList Unit A} (hp : Perm s r) :
    ∀ (a : A) (x : ConsList Unit A), combineP a x s → ∃ y, Perm x y ∧ combineP a y r := by
  induction hp with
  | nil => intro a x h; cases x <;> simp [combineP] at h
  | @cons b s' r' hp ih =>
    intro a x h
    cases x with
    | wrap u =>
      simp only [combineP, ConsList.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain rfl := Perm.eq_nil hp rfl
      exact ⟨ConsList.wrap u, Perm.refl _, rfl⟩
    | cons c x' =>
      simp only [combineP, ConsList.cons.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩
      · exact ⟨r', hp, combine_head _ r'⟩
      · obtain ⟨y, hy, hc⟩ := ih a x' hz
        exact ⟨ConsList.cons b y, Perm.cons b hy, Or.inr ⟨r', hc, rfl⟩⟩
  | swap b c t =>
    intro a x h
    cases x with
    | wrap u => simp [combineP] at h
    | cons d x' =>
      simp only [combineP, ConsList.cons.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩
      · exact ⟨ConsList.cons c t, Perm.refl _, Or.inr ⟨ConsList.cons b t, combine_head _ t, rfl⟩⟩
      · cases x' with
        | wrap u =>
          simp only [combineP, ConsList.cons.injEq] at hz
          obtain ⟨rfl, rfl⟩ := hz
          cases u
          exact ⟨ConsList.cons b (ConsList.wrap ()), Perm.refl _, Or.inl rfl⟩
        | cons e x'' =>
          simp only [combineP, ConsList.cons.injEq] at hz
          rcases hz with ⟨rfl, rfl⟩ | ⟨z', hz', rfl, rfl⟩
          · exact ⟨_, Perm.refl _, Or.inl rfl⟩
          · exact ⟨ConsList.cons c (ConsList.cons b x''), Perm.swap b c x'',
              Or.inr ⟨_, Or.inr ⟨_, hz', rfl⟩, rfl⟩⟩
  | trans _ _ ih1 ih2 =>
    intro a x h
    obtain ⟨y1, p1, c1⟩ := ih1 a x h
    obtain ⟨y2, p2, c2⟩ := ih2 a y1 c1
    exact ⟨y2, Perm.trans p1 p2, c2⟩

/-- **`perm = ⦇[nil, add]⦈`** (B&dM §5.6, recalled in Ex 6.30). -/
public theorem perm_add :
    (perm : dList A ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR add
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun D r => ?_, fun a x r => ?_⟩)
  · show Perm (ConsList.wrap ()) r ↔ r = ConsList.wrap D
    exact ⟨fun h => Perm.eq_nil h rfl, fun h => by obtain rfl := h; exact Perm.nil⟩
  · show Perm (ConsList.cons a x) r ↔ ∃ y, Perm x y ∧ combineP a y r
    exact ⟨fun h => perm_combine h a x (combine_head a x),
      fun ⟨y, hxy, hc⟩ => Perm.trans (Perm.cons a hxy) (combine_perm a hc)⟩

theorem combine_listP {B : Type} (Q : dE A ⟶ dE B) (a : A) :
    ∀ {x w : ConsList Unit A} {z : ConsList Unit B}, combineP a x w → listP Q w z →
      ∃ b y, Q a b ∧ listP Q x y ∧ combineP b y z
  | ConsList.wrap _, w, z, hw, hz => by
    have e : w = _ := hw; subst e
    match z, hz with
    | ConsList.cons b (ConsList.wrap u), hz => exact ⟨b, ConsList.wrap (), hz.1, trivial, by cases u; rfl⟩
    | ConsList.cons _ (ConsList.cons _ _), hz => exact hz.2.elim
    | ConsList.wrap _, hz => exact hz.elim
  | ConsList.cons c x, w, z, hw, hz => by
    simp only [combineP] at hw
    rcases hw with rfl | ⟨w', hw', rfl⟩
    · match z, hz with
      | ConsList.cons b z', hz => exact ⟨b, z', hz.1, hz.2, combine_head b z'⟩
      | ConsList.wrap _, hz => exact hz.elim
    · match z, hz with
      | ConsList.cons d z'', hz =>
        obtain ⟨b, y, hab, hy, hc⟩ := combine_listP Q a hw' hz.2
        exact ⟨b, ConsList.cons d y, hab, ⟨hz.1, hy⟩, Or.inr ⟨z'', hc, rfl⟩⟩
      | ConsList.wrap _, hz => exact hz.elim

theorem listP_combine {B : Type} (Q : dE A ⟶ dE B) (a : A) (b : B) (hab : Q a b) :
    ∀ {x : ConsList Unit A} {y z : ConsList Unit B}, listP Q x y → combineP b y z →
      ∃ w, combineP a x w ∧ listP Q w z
  | ConsList.wrap u, ConsList.wrap _, z, _, hz => by
    have e : z = _ := hz; subst e
    exact ⟨_, combine_head a (ConsList.wrap u), hab, trivial⟩
  | ConsList.wrap _, ConsList.cons _ _, _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, _, h, _ => h.elim
  | ConsList.cons c x, ConsList.cons d y, z, hxy, hz => by
    simp only [combineP] at hz
    rcases hz with rfl | ⟨z', hz', rfl⟩
    · exact ⟨_, Or.inl rfl, hab, hxy⟩
    · obtain ⟨w', hw', hl⟩ := listP_combine Q a b hab hxy.2 hz'
      exact ⟨ConsList.cons c w', Or.inr ⟨w', hw', rfl⟩, hxy.1, hl⟩

/-- `add` is strictly natural, `(𝟙×list)(Q) add = add list(Q)`: splicing looks only at the shape. -/
public theorem add_strictNatural :
    StrictNatural (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.prod (Relator.idRelator RelSet.{0})
        (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))
      (fun a => add (A := a.carrier)) := by
  intro a b Q
  dsimp only
  rw [show (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)).map Q = rprodMap Q ((Relator.comp (Relator.idRelator RelSet.{0}) listRelator).map Q) from prodMap_eq_rprodMap _ _]
  apply hom_ext; intro p z
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, hc⟩
    exact listP_combine Q p.1 q.1 h1 h2 hc
  · rintro ⟨w, hw, hz⟩
    obtain ⟨b', y, h1, h2, hc⟩ := combine_listP Q p.1 hw hz
    exact ⟨(b', y), ⟨h1, h2⟩, hc⟩

/-- `⦇[nil, add]⦈` is strictly natural, being `perm`. -/
public theorem add_cata_strictNatural :
    StrictNatural (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (fun a => (⦇(junc (sumCop (dL Unit) ⟨a.carrier × ConsList Unit a.carrier⟩) wrapR add
          : (F Unit a.carrier).obj (dList a.carrier) ⟶ dList a.carrier)⦈)) := by
  simp only [← perm_add]; exact Sort.perm_strictNatural

variable (R : A → A → Prop)

/-- Removing a spliced-in element keeps a list ordered. -/
theorem combine_ordered (a : A) :
    ∀ {x y : ConsList Unit A}, combineP a x y → orderedP R y → orderedP R x
  | ConsList.wrap _, _, _, _ => trivial
  | ConsList.cons b x, y, h, hy => by
      simp only [combineP] at h
      rcases h with rfl | ⟨z, hz, rfl⟩
      · exact hy.2
      · exact ⟨fun c hc => hy.1 c (Sort.perm_mem (combine_perm a hz) (Or.inr hc)),
          combine_ordered a hz hy.2⟩

/-- `nil ordered = nil`: the empty list is ordered. -/
public theorem wrap_ordered : (wrapR : dL Unit ⟶ dList A) ≫ ordered R = wrapR :=
  hom_ext fun _ r => ⟨fun ⟨_, hm, hmr, _⟩ => hmr ▸ hm, fun h => ⟨r, h, rfl, by subst h; trivial⟩⟩

/-- **Ex 6.30, the fusion condition**: `add ordered = (𝟙×ordered) add ordered` — a list with an
    element spliced in is ordered only if the list was. -/
public theorem ordered_add :
    add ≫ ordered R = rprodMap (𝟙 (dE A)) (ordered R) ≫ add ≫ ordered R :=
  hom_ext fun p r => ⟨fun ⟨m, hm, hmr, ho⟩ =>
      ⟨p, ⟨rfl, rfl, combine_ordered R p.1 hm ho⟩, m, hm, hmr, ho⟩,
    fun ⟨q, ⟨h1, h2, _⟩, m, hm, hmr⟩ => by
      obtain ⟨a, x⟩ := p; obtain ⟨a', y⟩ := q
      obtain rfl : a = a' := h1; obtain rfl : x = y := h2
      exact ⟨m, hm, hmr⟩⟩

/-- **Ex 6.30**: `⦇[nil, add]⦈ ordered = ⦇[nil, add ordered]⦈` — fusion, under
    `ordered_add`. -/
public theorem add_ordered_fusion :
    ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR add
        : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ ordered R
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (add ≫ ordered R)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ :=
  relCata_fusion (initial Unit A)
    (by rw [junc_comp, Fmap_comp_junc, ← ordered_add R, wrap_ordered R])

/-- **Ex 6.30**: `⦇[nil, add ordered]⦈ ⊒ ⦇[nil, insert]⦈` for any `insert` with
    `(𝟙×ordered) insert ⊑ add ordered` — fusion (6.4). -/
public theorem insert_fusion {ins : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A}
    (hins : rprodMap (𝟙 (dE A)) (ordered R) ≫ ins ⊑ add ≫ ordered R) :
    ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR ins
        : (F Unit A).obj (dList A) ⟶ dList A)⦈
      ⊑ ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (add ≫ ordered R)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  rw [← add_ordered_fusion R]
  refine relCata_le_comp (initial Unit A) ?_
  rw [Fmap_comp_junc, junc_comp, wrap_ordered R]
  exact junc_mono _ (le_of_eq rfl) hins

/-- **Exercise 6.30 (B&dM p.157)**: `perm ordered ⊒ ⦇[nil, insert]⦈` for any `insert` with
    `(𝟙×ordered) insert ⊑ add ordered`. -/
public theorem insertion_sort {ins : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A}
    (hins : rprodMap (𝟙 (dE A)) (ordered R) ≫ ins ⊑ add ≫ ordered R) :
    ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR ins
        : (F Unit A).obj (dList A) ⟶ dList A)⦈ ⊑ (perm : dList A ⟶ dList A) ≫ ordered R :=
  calc ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR ins
        : (F Unit A).obj (dList A) ⟶ dList A)⦈
        ⊑ ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (add ≫ ordered R)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ := insert_fusion R hins
    _ = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR add
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ ordered R := (add_ordered_fusion R).symm
    _ = (perm : dList A ⟶ dList A) ≫ ordered R := by rw [← perm_add]

calc_steps insertion_sort

/-- The relation `insert : list A ← A × list A` of the function `insert`. -/
@[expose] public def insertR [DecidableRel R] : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  graph fun p => insert R p.1 p.2

/-- **Ex 6.30, the `insert` asked for**: the `insert` above meets
    `(𝟙×ordered) insert ⊑ add ordered`. -/
public theorem insert_add [DecidableRel R] (hconn : connected R)
    (htrans : ∀ a b c, R a b → R b c → R a c) :
    rprodMap (𝟙 (dE A)) (ordered R) ≫ insertR R
      ⊑ add ≫ ordered R :=
  le_iff.mpr fun p r ⟨q, ⟨h1, h2, ho⟩, hr⟩ => by
    obtain ⟨a, x⟩ := p; obtain ⟨a', y⟩ := q
    obtain rfl : a = a' := h1; obtain rfl : x = y := h2
    subst hr
    exact ⟨_, insert_le_combine R a x, rfl, insert_ordered hconn htrans a x ho⟩

/-! ## Sanity checks on `ℕ` with `≤` -/

example : isortFn (· ≤ · : Nat → Nat → Prop) (ConsList.cons 3 (ConsList.cons 1 (ConsList.cons 2 (ConsList.wrap ()))))
    = ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 3 (ConsList.wrap ()))) := rfl

example : isortFn (· ≤ · : Nat → Nat → Prop)
      (ConsList.cons 2 (ConsList.cons 2 (ConsList.cons 1 (ConsList.wrap ()))))
    = ConsList.cons 1 (ConsList.cons 2 (ConsList.cons 2 (ConsList.wrap ()))) := rfl

end Freyd.Alg.RelSet.ISort
