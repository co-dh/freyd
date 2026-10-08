/-
  B&dM p.207: the Gofer program for the 0/1 knapsack (§8.4), transcribed.  Gofer combinators take a
  PAIR of functions (`cross (f, g)`, `pair (f, g)`), while `merge r`, `filter p`, `addin f` are
  curried — kept as in the book.  `dupl`, `pair`, `cross` follow the book's Appendix prelude (p.265–266).
-/
module

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
