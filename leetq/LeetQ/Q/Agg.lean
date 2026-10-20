/-
  q's aggregates, scans, iterators and atomic arithmetic over `RelRep`. A q list `xs` is the relation
  `ix(xs) : i ↦ xs[i]`, held as `ql(xs)`, the `pairs` of a `FinRel`; every operation keeps it `pairs`, so
  `vals?` reads the answer back in index order. Each `#guard`'s expected value is real q's output on the
  same input (q 4.x, `tmp/agg.q`).
  * `f'` (each) and atom extension are `R ; f`, `comp` with `ofFn`; a dyadic `x f' y` is `⟨R,S⟩ ; f`.
  * `/` (over) and every aggregate are `⦇[B,S]⦈`, `RelRep.fold`, run on the values in REVERSE: q's
    iterators fold from the left, the cons-list fold from the right. `over_pairs` states the result as
    `foldl` over the value list; `sum`/`count`/`avg` follow (`sum_pairs`, `count_pairs`, `sumCount_pairs`),
    every repeat counted because a `RelRep` means a list, not a set. The grouped form is `app_selby`
    (`Q/Table.lean`).
  * `\` (scan) is the same fold into the list of partial results.
  * `':` (each-prior) and the moving windows `m*` compose with an index relation (`pred`, `win n`).
  `RelRep` needs `DecidableEq` on every carrier; `Float` has none, so a float is held as its IEEE bits
  (`QF`), the way q stores it.
-/
import AOP.A6_FinRel

namespace LeetQ.Q.Agg

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.RelRep

/-- A q float as its IEEE bits: `RelRep.comp`/`fold` need `DecidableEq`, which `Float` lacks. -/
structure QF where
  bits : UInt64
  deriving DecidableEq

def QF.of (x : Float) : QF := ⟨x.toBits⟩
def QF.f (q : QF) : Float := Float.ofBits q.bits
def QF.ofInt (x : Int) : QF := .of (Float.ofInt x)

/-- Floats read back, for comparing with q's printed output. -/
def fl (r : Option (List QF)) : Option (List Float) := r.map (·.map QF.f)

variable {V W U : Type} [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] [DecidableEq U] [FibreIndex U]

/-! ## A q list -/

/-- `ix(xs)` as pairs, `i ↦ xs[i]`. -/
def ql (xs : List V) : RelRep Nat V := .pairs (FinRel.ofList (xs.zipIdx.map Prod.swap))

omit [DecidableEq V] [FibreIndex V] in
theorem rel_ql (xs : List V) : (ql xs).rel = ix xs := (FinRel.rep_ofList _).trans (rel_zipIdx xs)

/-- The values in index order; only `pairs` is finite. -/
def vals? : RelRep Nat V → Option (List V)
  | .pairs r => some r.vals.toList
  | _ => none

/-- The index coreflexive `dom(R)` kept finite: `RelRep.dom` answers an `enum`, whose keys are all of
`Nat`, and a composite through it is never `pairs` again. -/
def idx : RelRep Nat V → Option (RelRep Nat Nat)
  | .pairs r => some (.pairs r.dom)
  | _ => none

/-! ## Each, and atom extension -/

/-- `f'R`, `f each R`: `R ; f`. -/
def each (f : V → W) (R : RelRep Nat V) : RelRep Nat W := R ≫ ofFn f

/-- `x f' y`, two lists matched by index: `⟨R,S⟩ ; f`. -/
def each2 (f : V → W → U) (R : RelRep Nat V) (S : RelRep Nat W) : RelRep Nat U := pair R S ≫ ofFn fun p => f p.1 p.2

theorem rel_each (f : V → W) (R : RelRep Nat V) : (each f R).rel = R.rel ≫ graph f := by
  rw [each, rel_comp, rel_ofFn]

theorem rel_each2 (f : V → W → U) (R : RelRep Nat V) (S : RelRep Nat W) :
    (each2 f R S).rel = rpair R.rel S.rel ≫ graph fun p => f p.1 p.2 := by
  rw [each2, rel_comp, rel_ofFn, rel_pair]

/-- `x f/: y`: each `y_j` against the whole of `x`. The inner row is a plain `List.map`: `x` is read back
first, which only `pairs` allows. -/
def eachRight (f : V → W → U) (X : RelRep Nat V) (Y : RelRep Nat W) : Option (List (List U)) := do
  let xs ← vals? X; vals? (Y ≫ ofFn fun b => xs.map (f · b))

/-- `x f\: y`: each `x_i` against the whole of `y`. -/
def eachLeft (f : V → W → U) (X : RelRep Nat V) (Y : RelRep Nat W) : Option (List (List U)) := do
  let ys ← vals? Y; vals? (X ≫ ofFn fun a => ys.map (f a ·))

/-! ## Over: the fold, left to right -/

/-- `⦇[B,S]⦈` over `R`'s values, left to right: the cons-list fold is a right fold, so the values go in
reversed. The answer is the fold's fibre; a functional `B`, `S` make it one value. -/
def foldl (B : RelRep Unit W) (S : RelRep (V × W) W) (R : RelRep Nat V) : Option (List W) :=
  (vals? R).map fun xs => (fold B S).app (CL.ofList xs.reverse)

/-- `a f/ xs`: `⦇[a, f]⦈`. -/
def over (f : W → V → W) (a : W) : RelRep Nat V → Option (List W) :=
  foldl (ofFn fun _ => a) (ofFn fun p => f p.2 p.1)

/-- `f/ xs` with no seed: the carrier is `Option V`, empty until the first value. -/
def over1 (f : V → V → V) : RelRep Nat V → Option (List (Option V)) :=
  foldl (ofFn fun _ => none) (ofFn fun p => some (p.2.elim p.1 (f · p.1)))

def count : RelRep Nat V → Option (List Nat) := over (fun n _ => n + 1) 0
def sum : RelRep Nat Int → Option (List Int) := over (· + ·) 0
def prd : RelRep Nat Int → Option (List Int) := over (· * ·) 1
def qmin : RelRep Nat Int → Option (List (Option Int)) := over1 min
def qmax : RelRep Nat Int → Option (List (Option Int)) := over1 max
def all : RelRep Nat Bool → Option (List Bool) := over (· && ·) true
def any : RelRep Nat Bool → Option (List Bool) := over (· || ·) false

/-! ## Scan: the fold into the partial results -/

/-- `a f\ xs`: the fold into the reversed partial results, the head the running value. -/
def scan (f : W → V → W) (a : W) (R : RelRep Nat V) : Option (List (List W)) :=
  (foldl (ofFn fun _ => [a]) (ofFn fun p => f (p.2.headD a) p.1 :: p.2) R).map (·.map (·.reverse.tail))

/-- `f\ xs` with no seed: the first partial result is `xs[0]`. -/
def scan1 (f : V → V → V) (R : RelRep Nat V) : Option (List (List V)) :=
  (foldl (ofFn fun _ => []) (ofFn fun p => match p.2 with
    | [] => [p.1]
    | a :: as => f a p.1 :: a :: as) R).map (·.map List.reverse)

def sums : RelRep Nat Int → Option (List (List Int)) := scan1 (· + ·)
def prds : RelRep Nat Int → Option (List (List Int)) := scan1 (· * ·)
def mins : RelRep Nat Int → Option (List (List Int)) := scan1 min
def maxs : RelRep Nat Int → Option (List (List Int)) := scan1 max

/-- `ema[a; xs]`: `e₀ = x₀`, `eᵢ = a xᵢ + (1-a) eᵢ₋₁`, a seedless scan. -/
def ema (a : Float) (R : RelRep Nat QF) : Option (List (List QF)) :=
  scan1 (fun e x => .of (a * x.f + (1 - a) * e.f)) R

/-! ## Each-prior: compose with the index before -/

/-- `i ↦ i-1`. -/
def pred : RelRep Nat Nat := .enum fun i => if i = 0 then [] else [i - 1]

/-- `f': xs`: `⟨R, (dom R ; pred ; R ; some) ∪ {0 ↦ none}⟩ ; g`. The seed pair goes first so the union,
which appends, stays in index order. -/
def eachPrior (g : V → Option V → W) (R : RelRep Nat V) : Option (RelRep Nat W) :=
  (idx R).map fun D => each2 g R (union (.pairs (FinRel.ofList [(0, none)])) (((D ≫ pred) ≫ R) ≫ ofFn some))

def deltas : RelRep Nat Int → Option (RelRep Nat Int) := eachPrior fun x p => x - p.getD 0
def ratios : RelRep Nat Int → Option (RelRep Nat QF) :=
  eachPrior fun x p => .of (Float.ofInt x / Float.ofInt (p.getD 1))

/-! ## Moving windows -/

/-- `i ↦ i, i-1, …, i-n+1`, the ones `≥ 0`. -/
def win (n : Nat) : RelRep Nat Nat := .enum fun i => (List.range (min n (i + 1))).map (i - ·)

/-- Each index's window of values: `Λ(dom R ; win n ; R)`, restricted to `dom R` again, since `Λ`
answers an `enum` over all of `Nat`. -/
def mwin (n : Nat) (R : RelRep Nat V) : Option (RelRep Nat (List V)) :=
  (idx R).map fun D => D ≫ transpose ((D ≫ win n) ≫ R)

def msum (n : Nat) (R : RelRep Nat Int) : Option (List Int) := (mwin n R).bind (vals? ∘ each List.sum)
def mavg (n : Nat) (R : RelRep Nat Int) : Option (List QF) :=
  (mwin n R).bind (vals? ∘ each fun w => QF.of (Float.ofInt w.sum / Float.ofNat w.length))
def mmin (n : Nat) (R : RelRep Nat Int) : Option (List Int) :=
  (mwin n R).bind (vals? ∘ each fun w => w.foldl min (w.headD 0))
def mmax (n : Nat) (R : RelRep Nat Int) : Option (List Int) :=
  (mwin n R).bind (vals? ∘ each fun w => w.foldl max (w.headD 0))
def mcount (n : Nat) (R : RelRep Nat V) : Option (List Nat) := (mwin n R).bind (vals? ∘ each List.length)

/-! ## Statistics -/

/-- `(Σx, n)` in one fold. -/
def sumCount : RelRep Nat Int → Option (List (Int × Nat)) := over (fun a x => (a.1 + x, a.2 + 1)) (0, 0)

def avg (R : RelRep Nat Int) : Option (List QF) :=
  (sumCount R).map (·.map fun a => .of (Float.ofInt a.1 / Float.ofNat a.2))

/-- `(Σx, Σx², n)` in one fold; `var` is the population variance `Σx²/n - (Σx/n)²`. -/
def var (R : RelRep Nat Int) : Option (List QF) :=
  (over (fun a x => (a.1 + x, a.2.1 + x * x, a.2.2 + 1)) ((0, 0, 0) : Int × Int × Nat) R).map (·.map fun a =>
    let n := Float.ofNat a.2.2; let m := Float.ofInt a.1 / n
    .of (Float.ofInt a.2.1 / n - m * m))

def dev (R : RelRep Nat Int) : Option (List QF) := (var R).map (·.map fun v => .of v.f.sqrt)

/-! ## The aggregates are left folds over the list, repeats kept

`RelRep`'s meaning is a list per key, so `over` is stated on the values themselves: every value, in index
order, each repeat counted. The Set reading of `ix(xs)` keeps the pairs `(i, xs[i])` and can say this only
through the indices; `count` and `sum` of the values' set would merge the two `1`s of `3 1 4 1 5`. -/

omit [DecidableEq U] [FibreIndex U] in
/-- **`a f/ xs = foldl f a xs`**: the reversed cons-list fold is q's left fold over every value. -/
theorem over_pairs (f : W → V → W) (a : W) (r : FinRel Nat V) :
    over f a (.pairs r) = some [r.vals.toList.foldl f a] := by
  have h : ∀ ys : List V, foldList id (fun _ => [a]) (fun p : V × W => [f p.2 p.1]) (CL.ofList ys) =
      [ys.foldr (fun y w => f w y) a] := fun ys => by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [foldList, CL.ofList_cons, CL.cfold, id] at ih ⊢; rw [ih]; rfl
  simp [over, foldl, vals?, RelRep.fold, RelRep.foldWith_eq, ofFn, h, List.foldr_reverse]

omit [DecidableEq U] [FibreIndex U] in
/-- `count R` is the length of the value list. -/
theorem count_pairs (r : FinRel Nat V) : count (.pairs r) = some [r.vals.toList.length] := by
  have h : ∀ (l : List V) n, l.foldl (fun n _ => n + 1) n = n + l.length := fun l => by
    induction l <;> simp_all [Nat.add_assoc, Nat.add_comm 1]
  rw [count, over_pairs, h, Nat.zero_add]

/-- `sum R` is the sum of the value list. -/
theorem sum_pairs (r : FinRel Nat Int) : sum (.pairs r) = some [r.vals.toList.sum] := by
  have h : ∀ (l : List Int) n, l.foldl (· + ·) n = n + l.sum := fun l => by
    induction l <;> simp_all [Int.add_assoc]
  rw [sum, over_pairs, h, Int.zero_add]

/-- `avg R`'s fold is the value list's sum and length; `avg` divides them. Stated before the division,
    since a `Float` equation drags in `Classical.choice`. -/
theorem sumCount_pairs (r : FinRel Nat Int) : sumCount (.pairs r) = some [(r.vals.toList.sum, r.vals.toList.length)] := by
  have h : ∀ (l : List Int) (a : Int × Nat), l.foldl (fun a x => (a.1 + x, a.2 + 1)) a = (a.1 + l.sum, a.2 + l.length) :=
    fun l => by induction l <;> simp_all [Int.add_assoc, Nat.add_assoc, Nat.add_comm 1]
  rw [sumCount, over_pairs, h, Int.zero_add, Nat.zero_add]

#print axioms over_pairs
#print axioms sum_pairs
#print axioms count_pairs
#print axioms sumCount_pairs

/-- `med`: the keys of `R°` sorted are the values sorted; the middle one, or the mean of the two. -/
def med : RelRep Nat Int → Option QF
  | .pairs r =>
    let ks := (SortedRel.sortByKey r.conv).keys.toList; let n := ks.length
    some (if n % 2 = 1 then .ofInt (ks.getD (n / 2) 0)
      else .of ((Float.ofInt (ks.getD (n / 2 - 1) 0) + Float.ofInt (ks.getD (n / 2) 0)) / 2))
  | _ => none

/-- `w wsum x`: `⦇+⦈(⟨W,X⟩ ; ×)`. -/
def wsum (W X : RelRep Nat Int) : Option (List Int) := sum (each2 (· * ·) W X)

def wavg (W X : RelRep Nat Int) : Option (List QF) := do
  let [s] ← wsum W X | none
  let [t] ← sum W | none
  pure [.of (Float.ofInt s / Float.ofInt t)]

/-- `(Σx, Σy, Σxy, n)` over `⟨X,Y⟩`; `cov = Σxy/n - (Σx/n)(Σy/n)`. -/
def cov (X Y : RelRep Nat Int) : Option (List QF) := do
  let P := pair X Y ≫ ofFn id
  let r ← over (fun a (p : Int × Int) => (a.1 + p.1, a.2.1 + p.2, a.2.2.1 + p.1 * p.2, a.2.2.2 + 1))
    ((0, 0, 0, 0) : Int × Int × Int × Nat) P
  pure (r.map fun a => let n := Float.ofNat a.2.2.2
    .of (Float.ofInt a.2.2.1 / n - Float.ofInt a.1 / n * (Float.ofInt a.2.1 / n)))

def cor (X Y : RelRep Nat Int) : Option (List QF) := do
  let [c] ← cov X Y | none
  let [dx] ← dev X | none
  let [dy] ← dev Y | none
  pure [.of (c.f / (dx.f * dy.f))]

/-! ## Dyadic arithmetic and comparison -/

/-- q's `div` and `mod` round toward `-∞`. -/
def qdiv : Int → Int → Int := Int.fdiv
def qmod : Int → Int → Int := Int.fmod
def qfdiv (x y : Int) : QF := .of (Float.ofInt x / Float.ofInt y)
def floor (q : QF) : Int := q.f.floor.toInt64.toInt
def ceiling (q : QF) : Int := q.f.ceil.toInt64.toInt

/-! ## q's output on the same inputs -/

def xs := ql ([3, 1, 4, 1, 5] : List Int)

#guard count xs = some [5]
#guard sum xs = some [14]
#guard prd xs = some [60]
#guard qmin xs = some [some 1]
#guard qmax xs = some [some 5]
#guard fl (avg (ql [1, 2, 3, 4])) == some [2.5]
#guard (med (ql [1, 3, 2, 4])).map QF.f == some 2.5
#guard (med xs).map QF.f == some 3
#guard fl (var (ql [1, 2, 3, 4])) == some [1.25]
#guard fl (dev (ql [2, 4, 4, 4, 5, 5, 7, 9])) == some [2]
#guard fl (wavg (ql [1, 3]) (ql [2, 6])) == some [5]
#guard wsum (ql [1, 2, 3]) (ql [4, 5, 6]) = some [32]
#guard sums xs = some [[3, 4, 8, 9, 14]]
#guard prds xs = some [[3, 3, 12, 12, 60]]
#guard mins xs = some [[3, 1, 1, 1, 1]]
#guard maxs xs = some [[3, 3, 4, 4, 5]]
#guard (deltas xs).bind vals? = some [3, -2, 3, -3, 4]
#guard fl ((ratios (ql [1, 2, 8, 4])).bind vals?) == some [1, 2, 4, 0.5]
#guard msum 2 xs = some [3, 4, 5, 5, 6]
#guard fl (mavg 2 xs) == some [3, 2, 2.5, 2.5, 3]
#guard mmin 3 xs = some [3, 1, 1, 1, 1]
#guard mmax 3 xs = some [3, 3, 4, 4, 5]
#guard mcount 3 xs = some [1, 2, 3, 3, 3]
#guard ((ema 0.5 (ql ([1, 2, 3].map QF.ofInt))).map (·.map (·.map QF.f))) == some [[1, 1.5, 2.25]]
-- q prints `1f`; `√1.25·√5` rounds a few ulps off `2.5`
#guard ((cor (ql [1, 2, 3, 4]) (ql [2, 4, 6, 8])).map (·.map fun c => decide ((c.f - 1).abs < 1e-12))) == some [true]
#guard fl (cov (ql [1, 2, 3, 4]) (ql [2, 4, 6, 8])) == some [2.5]
#guard all (ql [true, false, true]) = some [false]
#guard any (ql [true, false, true]) = some [true]
#guard all (ql [true, true, true]) = some [true]
-- iterators with a binary function
#guard over1 (· - ·) (ql ([1, 2, 3] : List Int)) = some [some (-4)]
#guard scan1 (· - ·) (ql ([1, 2, 3] : List Int)) = some [[1, -1, -4]]
#guard over (· - ·) (10 : Int) (ql [1, 2, 3]) = some [4]
#guard scan (· - ·) (10 : Int) (ql [1, 2, 3]) = some [[9, 7, 4]]
#guard vals? (each (fun x : Int => -x) (ql [1, -2, 3])) = some [-1, 2, -3]
#guard vals? (each2 (· + ·) (ql ([1, 2, 3] : List Int)) (ql [10, 20, 30])) = some [11, 22, 33]
#guard (eachPrior (fun x p => x - p.getD 0) (ql ([3, 1, 4] : List Int))).bind vals? = some [3, -2, 3]
#guard (eachPrior (fun x p => x - p.getD 10) (ql ([3, 1, 4] : List Int))).bind vals? = some [-7, -2, 3]
#guard eachRight (· + ·) (ql ([1, 2] : List Int)) (ql [10, 20]) = some [[11, 12], [21, 22]]
#guard eachLeft (· + ·) (ql ([1, 2] : List Int)) (ql [10, 20]) = some [[11, 21], [12, 22]]
-- atom extension: `R ; (a f ·)`
#guard vals? (each ((1 : Int) + ·) (ql [10, 20, 30])) = some [11, 21, 31]
#guard vals? (each (· - (10 : Int)) (ql [1, 2, 3])) = some [-9, -8, -7]
#guard vals? (each ((2 : Int) * ·) (ql [1, 2, 3])) = some [2, 4, 6]
#guard fl (vals? (each (qfdiv · 2) (ql [1, 2, 3]))) == some [0.5, 1, 1.5]
#guard vals? (each2 qdiv (ql [-7, 7, -7, 7]) (ql [2, 2, -2, -2])) = some [-4, 3, 3, -4]
#guard vals? (each2 qmod (ql [-7, 7, -7, 7]) (ql [2, 2, -2, -2])) = some [1, 1, -1, -1]
-- comparison: bool lists
def cmp (f : Int → Int → Bool) : Option (List Bool) := vals? (each2 f (ql [1, 2, 3]) (ql [2, 2, 2]))
#guard cmp (· == ·) = some [false, true, false]
#guard cmp (· < ·) = some [true, false, false]
#guard cmp (· > ·) = some [false, false, true]
#guard cmp (· != ·) = some [true, false, true]
#guard cmp (· ≤ ·) = some [true, true, false]
#guard cmp (· ≥ ·) = some [false, true, true]
#guard vals? (each2 min (ql ([1, 5, 3] : List Int)) (ql [4, 2, 6])) = some [1, 2, 3]
#guard vals? (each2 max (ql ([1, 5, 3] : List Int)) (ql [4, 2, 6])) = some [4, 5, 6]
-- monadic maps
#guard vals? (each Int.natAbs (ql ([1, -2, 3] : List Int))) = some [1, 2, 3]
#guard vals? (each Int.sign (ql ([-5, 0, 7] : List Int))) = some [-1, 0, 1]
#guard vals? (each floor (ql ([-1.5, 2.5, 3.0].map QF.of))) = some [-2, 2, 3]
#guard vals? (each ceiling (ql ([-1.5, 2.5, 3.0].map QF.of))) = some [-1, 3, 3]

-- the kernel reduces the folds; not `deltas`, `msum`: `idx` goes through `FinRel.dom`, whose `dedup` is a
-- `mergeSort`, well-founded recursion the kernel does not unfold
example : sum xs = some [14] := by decide
example : sums xs = some [[3, 4, 8, 9, 14]] := by decide

end LeetQ.Q.Agg
