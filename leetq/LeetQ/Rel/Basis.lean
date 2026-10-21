/-
  The basis every verb of `LeetQ.Rel` is composed from.  Most of it is `RelRep`'s own (`AOP/A6_FinRel`):
  `R ≫ S`, `R.conv` (as a test), `R.inter T`, `R.union S`, `RelRep.corefl p` (`p?`), `R.pair S` (`⟨R,S⟩`),
  `.ofFn f` (a function as a relation), `R.dom`, `R.first`/`R.last` (`est(<)`/`est(>)` on a fibre listed in
  position order), `R.est L`, `R.override S` (`R`, else `S` where `R` is empty), `R.compT T`, and
  `Λ(R) = RelRep.transpose R`.  What is added here is what those leave out: the list as a relation, the
  orders and windows on positions, the converse of a relation out of the positions listed again, the
  complement of a domain, a composite test, and the folds of a collected fibre.
-/
import AOP.A6_FinRel

namespace LeetQ.Rel

open Freyd.Alg.RelSet (RelRep RelTest FinRel)
open scoped Freyd.Alg.RelSet.RelRep

/-- `Λ(R)`: each fibre collected, in position order. -/
scoped prefix:max "Λ" => RelRep.transpose

variable {A B : Type} [DecidableEq A] [DecidableEq B]

/-- `ix(xs) : ℕ ⇸ A`: position `i` to `xs[i]`. -/
def ix (xs : List A) : RelRep Nat A := .vec xs.toArray rfl

/-- The identity on the positions `0 … n-1`. -/
def idn (n : Nat) : RelRep Nat Nat := RelRep.corefl (decide <| · < n)

/-- `⊤ : X ⇸ ℕ` onto the positions `0 … n-1`, in order: what `Λ`, `first` and `#` range over. -/
def top {X : Type} (n : Nat) : RelRep X Nat := .enum fun _ => List.range n

/-- `≥` on positions, `i ↦ j ≤ i` in order: the prefix a running aggregate folds. -/
def ge : RelRep Nat Nat := .enum fun i => List.range (i + 1)

/-- `>` on positions, `i ↦ j < i` in order: `i` copies of `i`'s row is `⟨id, >⟩ ≫ π₁`. -/
def gt : RelRep Nat Nat := .enum List.range

/-- `W(n) = {(i,j) | i-n < j ≤ i}`, in order: the window of the moving aggregates. -/
def win (n : Nat) : RelRep Nat Nat := .enum fun i => List.range' (i + 1 - n) (min n (i + 1))

/-- `i ↦ i+k`, defined where that is a position: `pred = shift (-1)`. -/
def shift (k : Int) : RelRep Nat Nat :=
  .enum fun i => if 0 ≤ (i : Int) + k then [((i : Int) + k).toNat] else []

/-- `R°` for `R` out of the positions `0 … n-1`, listed again: each value's positions in increasing order,
    so `(cv n R).first` is the first position holding a value.  `R.conv` is only a test. -/
def cv (n : Nat) (R : RelRep Nat A) : RelRep A Nat :=
  .pairs (FinRel.ofList ((List.range n).flatMap fun i => (R.app i).map (·, i)))

/-- `(∉ dom R)?`: the coreflexive on what `R` relates to nothing. -/
def ndom (R : RelRep A B) : RelRep A A := RelRep.corefl fun a => (R.app a).isEmpty

/-- `R ≫ L ≫ S°` as a test on positions: some value of `i` is `L`-related to some value of `j`. -/
def via (R : RelRep Nat A) (L : RelTest A B) (S : RelRep Nat B) : RelTest Nat Nat := R.compT (S.compT L.conv).conv

/-- `b` before `a` in the order `lt` on values, ties broken by position: what `rank` counts. -/
def lex (lt : A → A → Bool) : RelTest (A × Nat) (A × Nat) := .test fun a b => lt b.1 a.1 || (b.1 == a.1 && b.2 < a.2)

/-- `∋ : List A ⇸ A`, a list to its members in order. -/
def mem : RelRep (List A) A := .enum id

/-- `⦇z, op⦈` on a fibre `Λ` collected. -/
def fold (z : B) (op : B → A → B) : RelRep (List A) B := .ofFn (·.foldl op z)

/-- `⦇op⦈` seeded by the first member; the empty fibre folds to nothing. -/
def fold1 (op : A → A → A) : RelRep (List A) A := .enum fun | [] => [] | x :: xs => [xs.foldl op x]

/-- The length of a collected fibre. -/
def len : RelRep (List A) Nat := fold 0 fun n _ => n + 1

end LeetQ.Rel
