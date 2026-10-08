/-
  B&dM p.207: the Gofer program for the 0/1 knapsack (§8.4), transcribed.  Gofer combinators take a
  PAIR of functions (`cross (f, g)`, `pair (f, g)`), while `merge r`, `filter p`, `addin f` are
  curried — kept as in the book.  `dupl`, `pair`, `cross` follow the book's Appendix prelude (p.265–266).
-/
module

namespace Knap207

variable {α β γ δ : Type}

@[expose] public def cross : (α → γ) × (β → δ) → α × β → γ × δ | (f, g), (a, b) => (f a, g b)
-- the Appendix's dupl (p.266), not the diagonal
@[expose] public def dupl : α × (β × γ) → (α × β) × (α × γ) | (a, (b, c)) => ((a, b), (a, c))
@[expose] public def pair : (α → β) × (α → γ) → α → β × γ | (f, g), a => (f a, g a)
@[expose] public def outl : α × β → α := Prod.fst
@[expose] public def outr : α × β → β := Prod.snd
@[expose] public def plus : Int × Int → Int := fun (m, n) => m + n
@[expose] public def geq : Int × Int → Bool := fun (m, n) => decide (m ≥ n)
@[expose] public def leq : Int × Int → Bool := fun (m, n) => decide (m ≤ n)
@[expose] public def meet : Bool × Bool → Bool := fun (a, b) => a && b
@[expose] public def cons : α × List α → List α := fun (a, x) => a :: x
@[expose] public def cpr : α × List β → List (α × β) := fun (a, ys) => ys.map (a, ·)
@[expose] public def catalist (start : β) (f : α × β → β) : List α → β
  | [] => start
  | a :: x => f (a, catalist start f x)
@[expose] public def merge (r : α × α → Bool) : List α × List α → List α
  | ([], ys) => ys
  | (xs, []) => xs
  | (x :: xs, y :: ys) =>
    if r (x, y) then x :: merge r (xs, y :: ys) else y :: merge r (x :: xs, ys)
termination_by p => p.1.length + p.2.length
@[expose] public def thinL (q : α × α → Bool) : List α → List α
  | a :: b :: x =>
    if q (a, b) then thinL q (a :: x)
    else if q (b, a) then thinL q (b :: x) else a :: thinL q (b :: x)
  | x => x

variable {Item : Type} (val wt : Item → Int)

/-- A packing `x` is held as `(x, (value x, weight x))`. -/
@[expose] public abbrev Rep (Item : Type) := List Item × (Int × Int)

@[expose] public def value : Rep Item → Int := outl ∘ outr
@[expose] public def weight : Rep Item → Int := outr ∘ outr
@[expose] public def r : Rep Item × Rep Item → Bool := geq ∘ cross (value, value)
@[expose] public def p : Rep Item × Rep Item → Bool := leq ∘ cross (weight, weight)
@[expose] public def q : Rep Item × Rep Item → Bool := meet ∘ pair (p, r)
@[expose] public def within (w : Int) : Rep Item → Bool := (fun n => decide (n ≤ w)) ∘ weight
@[expose] public def addin (f : Item → Int) : Item × Int → Int := plus ∘ cross (f, id)

@[expose] public def augment : Item × (Int × Int) → Int × Int := cross (addin val, addin wt) ∘ dupl
@[expose] public def cons' : Item × Rep Item → Rep Item := cross (cons, augment val wt) ∘ dupl

@[expose] public def start : List (Rep Item) := [([], (0, 0))]
@[expose] public def step (w : Int) : Item × List (Rep Item) → List (Rep Item) × List (Rep Item) :=
  pair (List.filter (within w) ∘ List.map (cons' val wt), List.map outr) ∘ cpr
@[expose] public def knapsack (w : Int) : List Item → Rep Item :=
  fun xs => (catalist start (thinL q ∘ merge r ∘ step val wt w) xs).head!

-- items (value, weight); capacity 10
#guard knapsack (fun i : Int × Int => i.1) (fun i => i.2) 10 [(6, 5), (5, 4), (4, 6), (3, 3)] = ([(6, 5), (5, 4)], (11, 9))

end Knap207
