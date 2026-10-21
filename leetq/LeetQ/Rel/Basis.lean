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

/-! ## Running folds in one pass -/

open Freyd.Alg.RelSet (rangeFold rangeFold_eq)

/-- `Λ(S) ≫ G` at `i` is `G` of `S`'s fibre at `i`, collected. -/
theorem app_Λ {C : Type} [DecidableEq C] (S : RelRep Nat A) (G : RelRep (List A) C) (i : Nat) :
    (Λ(S) ≫ G).app i = G.app (S.app i) := by
  rw [RelRep.app_comp, RelRep.transpose_eq, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The scan law**: the prefix at `i+1` is the prefix at `i` with `i+1`'s fibre appended, so its fold is the
    fold at `i` folded on by that fibre alone. -/
theorem scan_succ (z : B) (op : B → A → B) (R : RelRep Nat A) (i : Nat) :
    (Λ(ge ≫ R) ≫ fold z op).app (i + 1) = ((Λ(ge ≫ R) ≫ fold z op).app i).map fun w => (R.app (i + 1)).foldl op w := by
  rw [app_Λ, app_Λ, RelRep.app_comp, RelRep.app_comp]
  show [((List.range (i + 1 + 1)).flatMap R.app).foldl op z] = [((List.range (i + 1)).flatMap R.app).foldl op z].map
    fun w => (R.app (i + 1)).foldl op w
  rw [List.range_succ (n := i + 1), List.flatMap_append, List.foldl_append, List.flatMap_singleton]; rfl

/-- `Λ(≥ ≫ R) ≫ ⦇z, op⦈` on the positions `0 … n-1`, by the scan law in one pass from the left, as a `vec`:
    no prefix is listed again (`app_scanR`). -/
def scanR (n : Nat) (z : B) (op : B → A → B) (R : RelRep Nat A) : RelRep Nat B :=
  R.withFib fun g => .vec (rangeFold (fun (p : B × Array B) i => let w := (g i).foldl op p.1; (w, p.2.push w))
    n 0 (z, Array.mkEmpty n)).2 rfl

/-- **`scanR` is the running fold** at every position `i < n`. -/
theorem app_scanR (n : Nat) (z : B) (op : B → A → B) (R : RelRep Nat A) (i : Nat) (h : i < n) :
    (scanR n z op R).app i = (Λ(ge ≫ R) ≫ fold z op).app i := by
  let pf := fun m => ((List.range m).flatMap R.app).foldl op z
  have go : ∀ m, ((List.range m).foldl (fun (p : B × Array B) i => let w := (R.fib i).foldl op p.1; (w, p.2.push w))
      (z, Array.mkEmpty n)) = (pf m, ((List.range m).map fun j => pf (j + 1)).toArray) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [pf, List.range_succ, ← Array.foldl_toList, List.flatMap_append, List.foldl_append]
  rw [scanR, RelRep.withFib_eq, RelRep.app_vec, rangeFold_eq, ← List.range_eq_range']
  dsimp only
  rw [go n, cast_eq, List.getElem?_toArray, List.getElem?_map, List.getElem?_range h, app_Λ, RelRep.app_comp]
  rfl

/-- `⦇op⦈`'s state: nothing before the first member, which then seeds the fold. -/
def step1 (op : A → A → A) (o : Option A) (a : A) : Option A := some (o.elim a (op · a))

/-- `⦇op⦈` is the fold of `step1` from nothing. -/
theorem fold1_eq (op : A → A → A) (l : List A) : (fold1 op).app l = (l.foldl (step1 op) none).toList := by
  have go : ∀ (xs : List A) w, xs.foldl (step1 op) (some w) = some (xs.foldl op w) := by
    intro xs; induction xs with
    | nil => intro w; rfl
    | cons x xs ih => intro w; exact ih (op w x)
  cases l with
  | nil => rfl
  | cons x xs => exact (congrArg Option.toList (go xs x)).symm

/-- Keeping each member in turn ends at the last. -/
theorem foldl_some (l : List A) (o : Option A) : l.foldl (fun _ a => some a) o = l.getLast?.or o := by
  induction l generalizing o with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, List.getLast?_cons]; cases xs.getLast? <;> rfl

end LeetQ.Rel
