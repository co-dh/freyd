/-
  B&dM p.207: the Gofer program for the 0/1 knapsack (§8.4), transcribed.  Gofer combinators take a
  PAIR of functions (`cross (f, g)`, `pair (f, g)`), while `merge r`, `filter p`, `addin f` are
  curried — kept as in the book.  `dupl`, `pair`, `cross` follow the book's Appendix prelude (p.265–266).
-/
module

public import AOP.A6_FinRel
public import AOP.A8_4_Knapsack

@[expose] public section

namespace Knap207

variable {α β γ δ : Type}

def cross : (α → γ) × (β → δ) → α × β → γ × δ | (f, g), (a, b) => (f a, g b)
-- the Appendix's dupl (p.266), not the diagonal
def dupl : α × (β × γ) → (α × β) × (α × γ) | (a, (b, c)) => ((a, b), (a, c))
def pair : (α → β) × (α → γ) → α → β × γ | (f, g), a => (f a, g a)
def outl : α × β → α := Prod.fst
def outr : α × β → β := Prod.snd
def plus : Int × Int → Int := fun (m, n) => m + n
def geq : Int × Int → Bool := fun (m, n) => decide (m ≥ n)
def leq : Int × Int → Bool := fun (m, n) => decide (m ≤ n)
def meet : Bool × Bool → Bool := fun (a, b) => a && b
def cons : α × List α → List α := fun (a, x) => a :: x
def nil : α → List β := fun _ => []
def wrap : α → List α := cons ∘ pair (id, nil)
#guard wrap 3 = [3]
def cpr : α × List β → List (α × β) := fun (a, ys) => ys.map (a, ·)
def catalist (start : β) (f : α × β → β) : List α → β
  | [] => start
  | a :: x => f (a, catalist start f x)
def merge (r : α × α → Bool) : List α × List α → List α
  | ([], ys) => ys
  | (xs, []) => xs
  | (x :: xs, y :: ys) =>
    if r (x, y) then x :: merge r (xs, y :: ys) else y :: merge r (x :: xs, ys)
termination_by p => p.1.length + p.2.length
def thinL (q : α × α → Bool) : List α → List α
  | a :: b :: x =>
    if q (a, b) then thinL q (a :: x)
    else if q (b, a) then thinL q (b :: x) else a :: thinL q (b :: x)
  | x => x

variable {Item : Type} (val wt : Item → Int)

/-- A packing `x` is held as `(x, (value x, weight x))`. -/
abbrev Rep (Item : Type) := List Item × (Int × Int)

def value : Rep Item → Int := outl ∘ outr
def weight : Rep Item → Int := outr ∘ outr
def r : Rep Item × Rep Item → Bool := geq ∘ cross (value, value)
def p : Rep Item × Rep Item → Bool := leq ∘ cross (weight, weight)
def q : Rep Item × Rep Item → Bool := meet ∘ pair (p, r)
def within (w : Int) : Rep Item → Bool := (fun n => decide (n ≤ w)) ∘ weight
def addin (f : Item → Int) : Item × Int → Int := plus ∘ cross (f, id)

def augment : Item × (Int × Int) → Int × Int := cross (addin val, addin wt) ∘ dupl
def cons' : Item × Rep Item → Rep Item := cross (cons, augment val wt) ∘ dupl

def start : List (Rep Item) := [([], (0, 0))]
def step (w : Int) : Item × List (Rep Item) → List (Rep Item) × List (Rep Item) :=
  pair (List.filter (within w) ∘ List.map (cons' val wt), List.map outr) ∘ cpr
def knapsack (w : Int) : List Item → Rep Item :=
  fun xs => (catalist start (thinL q ∘ merge r ∘ step val wt w) xs).head!

-- items (value, weight); capacity 10
#guard knapsack (fun i : Int × Int => i.1) (fun i => i.2) 10 [(6, 5), (5, 4), (4, 6), (3, 3)] = ([(6, 5), (5, 4)], (11, 9))

end Knap207

namespace Freyd.Alg.RelSet.Knapsack
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

/-! ## `KnapRun`: the knapsack program on `RelRep`

The fold keeps a list of packings: `step` extends each kept packing by the item when it still
fits and also leaves the item out, `RelRep.thin Q` cuts the candidates, and `RelRep.est R` reads
the most valuable packings off the last list. -/

section KnapRun

variable {Item : Type} [DecidableEq Item] (val wt : Item → Int) (w : Int)

instance decQ : ∀ xs ys : ConsList Unit Item, Decidable (Q val wt xs ys) :=
  fun xs ys => decidable_of_iff _ (Q_apply xs ys).symm

instance decR : ∀ xs ys : ConsList Unit Item, Decidable (R val xs ys) :=
  fun xs ys => decidable_of_iff _ (R_apply xs ys).symm

/-- The thinning order `Q` as a `RelRep` test. -/
def Qt : RelTest (ConsList Unit Item) (ConsList Unit Item) := .test fun xs ys => decide (Q val wt xs ys)

omit [DecidableEq Item] in
theorem rel_Qt : (Qt val wt).rel = Q val wt := hom_ext fun _ _ => decide_eq_true_iff

/-- The value order `R` as a `RelRep` test. -/
def Rt : RelTest (ConsList Unit Item) (ConsList Unit Item) := .test fun xs ys => decide (R val xs ys)

omit [DecidableEq Item] in
theorem rel_Rt : (Rt val).rel = R val := hom_ext fun _ _ => decide_eq_true_iff

/-- The step's `Λ` form: the packing with item `a` added when it still fits, and the packing without it. -/
def step (q : Item × ConsList Unit Item) : List (ConsList Unit Item) :=
  if weight wt (ConsList.cons q.1 q.2) ≤ w then [ConsList.cons q.1 q.2, q.2] else [q.2]

omit [DecidableEq Item] in
/-- `step` is the `cons` half of `S`: `cons (within w) ∪ π₂`. -/
theorem rel_step :
    (RelRep.enum (step wt w)).rel
      = (consR ≫ corefl (within (wt := wt) w)) ∪ graph fun p : Item × ConsList Unit Item => p.2 :=
  hom_ext fun q r => by
    show r ∈ step wt w q ↔ _
    unfold step
    by_cases h : weight wt (ConsList.cons q.1 q.2) ≤ w
    · rw [if_pos h]
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl ⟨_, rfl, rfl, h⟩
        · exact Or.inr rfl
      · rintro (⟨c, hc, hcr, -⟩ | hd)
        · obtain rfl : c = ConsList.cons q.1 q.2 := hc
          exact Or.inl (hcr : ConsList.cons q.1 q.2 = r).symm
        · exact Or.inr hd
    · rw [if_neg h]
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      constructor
      · rintro rfl; exact Or.inr rfl
      · rintro (⟨c, hc, -, hw⟩ | hd)
        · obtain rfl : c = ConsList.cons q.1 q.2 := hc
          exact absurd hw h
        · exact hd

omit [DecidableEq Item] in
/-- `S` is the junction of `wrap` and `step`. -/
theorem Salg_eq_junc :
    Salg wt w = junc (sumCop (dL Unit) ⟨Item × ConsList Unit Item⟩)
      (RelRep.ofFn (ConsList.wrap : Unit → ConsList Unit Item)).rel (RelRep.enum (step wt w)).rel := by
  rw [Salg_junc, RelRep.rel_ofFn, rel_step]; rfl

/-- The packings kept after the whole input: `⦇thin(Q)·Λ(S)⦈` as a function. -/
def kept : ConsList Unit Item → List (ConsList Unit Item) :=
  RelRep.foldList (RelRep.thinList fun xs ys => decide (Q val wt xs ys)) (fun u => [ConsList.wrap u]) (step wt w)

/-- `kept` is `RelRep.foldThin Q` of `wrap` and `step`. -/
theorem kept_eq :
    RelRep.foldThin (Qt val wt) (.ofFn ConsList.wrap) (.enum (step wt w)) = .enum (kept val wt w) := rfl

/-- The program: the most valuable packings among those kept. -/
def knap (xs : ConsList Unit Item) : List (ConsList Unit Item) := RelRep.estList (fun ys zs => decide (R val ys zs)) (kept val wt w xs)

/-- `knap` is `RelRep.est R` of `kept`. -/
theorem knap_eq : RelRep.est (Rt val) (.enum (kept val wt w)) = .enum (knap val wt w) := rfl

/-- `Λ(kept) ⊑ Λ⦇S⦈ thin(Q)`. -/
theorem kept_thin : Λ (RelRep.enum (kept val wt w)).rel ⊑ Λ ⦇Salg wt w⦈ ≫ thinRel (Q val wt) := by
  have h := kept_eq val wt w ▸ RelRep.rel_foldThin (Q := Qt val wt) (B := .ofFn ConsList.wrap) (S := .enum (step wt w))
    (by rw [rel_Qt]; exact Q_refl)
    (by rw [rel_Qt]; exact Q_trans)
    (by rw [rel_Qt, ← Salg_eq_junc]; exact pres_union knap_mono_cons knap_mono_drop)
  rw [← Salg_eq_junc, rel_Qt] at h
  exact h

/-- **The program meets its specification**: every packing `knap` returns is a most valuable
    packing within the capacity, `knap ⊑ Λ(subseq (within w)) est(R)`. -/
theorem knap_le (hw : 0 ≤ w) (hwt : ∀ i, 0 ≤ wt i) :
    (RelRep.enum (knap val wt w)).rel ⊑ Λ (subseq ≫ corefl (within (wt := wt) w)) ≫ est (R val) :=
  calc (RelRep.enum (knap val wt w)).rel
      = Λ (RelRep.enum (kept val wt w)).rel ≫ est (Rt val).rel := by rw [← (knap_eq val wt w)]; exact RelRep.rel_est _ _
    _ = Λ (RelRep.enum (kept val wt w)).rel ≫ est (R val) := by rw [rel_Rt]
    _ ⊑ (Λ ⦇Salg wt w⦈ ≫ thinRel (Q val wt)) ≫ est (R val) := comp_mono_right (kept_thin val wt w) _
    _ = Λ ⦇Salg wt w⦈ ≫ (thinRel (Q val wt) ≫ est (R val)) := Cat.assoc _ _ _
    _ ⊑ Λ ⦇Salg wt w⦈ ≫ est (R val) :=
      comp_mono_left _ (thinRel_comp_est_le Q_le_R (trans_of_recip_trans R_recip_trans))
    _ = Λ (subseq ≫ corefl (within (wt := wt) w)) ≫ est (R val) := knap_laws_step2 hw hwt

/-- **kept-run**: items `(value, weight)` `(6,5),(5,4),(4,6),(3,3)`, capacity `10`: the fold keeps
    seven packings, none both less valuable and heavier than another. -/
theorem run_kept :
    kept (Item := Int × Int) Prod.fst Prod.snd 10
        (ConsList.cons (6, 5) (ConsList.cons (5, 4) (ConsList.cons (4, 6) (ConsList.cons (3, 3) (ConsList.wrap ())))))
      = [ConsList.cons (5, 4) (ConsList.cons (3, 3) (ConsList.wrap ())),
         ConsList.cons (6, 5) (ConsList.cons (3, 3) (ConsList.wrap ())),
         ConsList.cons (3, 3) (ConsList.wrap ()),
         ConsList.cons (6, 5) (ConsList.cons (5, 4) (ConsList.wrap ())),
         ConsList.cons (5, 4) (ConsList.wrap ()),
         ConsList.cons (6, 5) (ConsList.wrap ()),
         ConsList.wrap ()] := by
  rfl

/-- **knap-run**: on the same items the program returns the one packing of value `11`,
    `(6,5),(5,4)` of weight `9`. -/
theorem run_knap :
    knap (Item := Int × Int) Prod.fst Prod.snd 10
        (ConsList.cons (6, 5) (ConsList.cons (5, 4) (ConsList.cons (4, 6) (ConsList.cons (3, 3) (ConsList.wrap ())))))
      = [ConsList.cons (6, 5) (ConsList.cons (5, 4) (ConsList.wrap ()))] := by
  rfl

end KnapRun

end Freyd.Alg.RelSet.Knapsack
