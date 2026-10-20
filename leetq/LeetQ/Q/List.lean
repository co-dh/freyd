/-
  q's list verbs over `RelRep` (`AOP/A6_FinRel`). A q list of length `n` is the relation
  `f = ix(xs) : index ↦ value`, held as a `FinRel` so that `f°` enumerates too; a q null is an index
  outside `dom f`. The verbs fall in four shapes:
  * `G f` for an index relation `G` (`pull`): reverse, first, last, take, drop, cut, sublist, rotate,
    next, prev, xprev, cross, flip, join (with `G` into `Nat ⊕ Nat` and the junction `[f,g]`);
  * a search by value through `f°`: distinct `est(≤)(f°)`, group `Λ(f°)`, find, bin, binr, inter, in;
  * a sort: iasc, idesc, asc, desc, rank (`SortedRel.sortByKey`, not a relational operator);
  * a read-off (`out`): the positions of a result are `Λ(R)` flattened over `0..n-1`, which is what
    re-indexes `where`, `inter`, `except`, `distinct`.
  Every verb is total except those that enumerate `f°`, which needs `f` held as pairs (`fin?`).
  Every expected value in a `#guard` is q's own output on the same input (q 4.x, `.Q.s1`).
-/
import AOP.A6_FinRel

namespace LeetQ.Q

open Freyd Freyd.Alg Freyd.Alg.RelSet
open scoped Freyd.Alg.RelSet.RelRep

/-- The `FinRel` an answer holds, `none` when it is held as a fibre function. -/
def fin? {K V : Type} : RelRep K V → Option (FinRel K V) | .pairs r => some r | _ => none

/-- A q list: `n` indices and the relation index ↦ value; an index with an empty fibre is null. -/
structure QL (A : Type) where
  n : Nat
  r : RelRep Nat A

/-- A q list of lists, rectangular: `(i, j) ↦ value`. -/
structure QL2 (A : Type) where
  n : Nat
  m : Nat
  r : RelRep (Nat × Nat) A

namespace QL

variable {A B : Type} [DecidableEq A] [FibreIndex A] [DecidableEq B] [FibreIndex B]

/-! ## A list as `ix(xs)`, and read back -/

/-- `ix(xs)` as a `FinRel`, whose converse is again enumerable. -/
def ofList (xs : List A) : QL A := ⟨xs.length, .pairs (FinRel.ofList (xs.zipIdx.map Prod.swap))⟩

omit [DecidableEq A] [FibreIndex A] in
theorem rel_ofList (xs : List A) : (ofList xs).r.rel = ix xs := (FinRel.rep_ofList _).trans (rel_zipIdx xs)

/-- A list with nulls: a null is an index with no pair. -/
def ofListN (xs : List (Option A)) : QL A :=
  ⟨xs.length, .pairs (FinRel.ofList (xs.zipIdx.filterMap fun (a, i) => a.map (i, ·)))⟩

/-- The positions of a result: `Λ(f)` flattened over `0..n-1`. -/
def out (x : QL A) : List A := (List.range x.n).flatMap x.r.app

/-- The same with nulls: an empty fibre is `none`. -/
def outN (x : QL A) : List (Option A) := (List.range x.n).map fun i => (x.r.app i).head?

/-- `G f` read on `0..m-1`: every verb that only moves indices. -/
def pull (m : Nat) (G : RelRep Nat Nat) (x : QL A) : QL A := ⟨m, G ≫ x.r⟩

theorem rel_pull (m : Nat) (G : RelRep Nat Nat) (x : QL A) : (pull m G x).r.rel = G.rel ≫ x.r.rel :=
  RelRep.rel_comp G x.r

/-- `≤` and `≥` on indices, as tests. -/
def leR : RelTest Nat Nat := .test fun a b => decide (a ≤ b)
def geR : RelTest Nat Nat := .test fun a b => decide (a ≥ b)

/-- The partial index map `i ↦ i + k`. -/
def shift (k : Int) : RelRep Nat Nat := .enum fun i => if 0 ≤ (i : Int) + k then [((i : Int) + k).toNat] else []

/-! ## Index maps: `G f` -/

/-- `til n`: the coreflexive on `0..n-1`. -/
def til (n : Nat) : QL Nat := ⟨n, RelRep.corefl (decide <| · < n)⟩

def reverse (x : QL A) := pull x.n (.ofFn (x.n - 1 - ·)) x
def first (x : QL A) := pull 1 (.ofFn fun _ => 0) x
def last (x : QL A) := pull 1 (.ofFn fun _ => x.n - 1) x

/-- `k#x`: cyclic from the front, or from the back when `k < 0`. -/
def take (k : Int) (x : QL A) :=
  pull k.natAbs (.ofFn fun i => if 0 ≤ k then i % x.n else (x.n - k.natAbs % x.n + i) % x.n) x

def drop (k : Int) (x : QL A) := pull (x.n - k.natAbs) (.ofFn fun i => if 0 ≤ k then i + k.natAbs else i) x

/-- `cs _ x`: one `pull` per segment `[cᵢ, cᵢ₊₁)`. -/
def cut (cs : List Nat) (x : QL A) : List (QL A) :=
  (cs.zip (cs.drop 1 ++ [x.n])).map fun (s, e) => pull (e - s) (.ofFn (· + s)) x

/-- `k sublist x`: `take` clamped to the length. -/
def sublist (k : Int) (x : QL A) :=
  pull (min k.natAbs x.n) (.ofFn fun i => if 0 ≤ k then i else i + x.n - min k.natAbs x.n) x

def sublist2 (s l : Nat) (x : QL A) := pull (min l (x.n - s)) (.ofFn (· + s)) x
def rotate (k : Int) (x : QL A) := pull x.n (.ofFn fun i => (((i : Int) + k) % (x.n : Int)).toNat) x
def next (x : QL A) := pull x.n (shift 1) x
def prev (x : QL A) := pull x.n (shift (-1)) x
def xprev (k : Nat) (x : QL A) := pull x.n (shift (-(k : Int))) x

/-- `x,y`: the index map into `Nat ⊕ Nat`, then the junction `[f,g]`. -/
def join (x y : QL A) : QL A :=
  ⟨x.n + y.n, RelRep.ofFn (fun i => (if i < x.n then .inl i else .inr (i - x.n) : Nat ⊕ Nat)) ≫ x.r.junction y.r⟩

def nil : QL A := ⟨0, .enum fun _ => []⟩

/-- `raze`: the fold of `join`. -/
def raze (xs : List (QL A)) : QL A := xs.foldr join nil

/-- `x cross y`: `i ↦ (i / |y|, i mod |y|)`, then `f × g`. -/
def cross (x : QL A) (y : QL B) : QL (A × B) :=
  ⟨x.n * y.n, RelRep.ofFn (fun i => (i / y.n, i % y.n)) ≫ x.r.prod y.r⟩

/-! ## Searches by value: `f°` -/

/-- `where b`: `dom(f ∩ (=1b))` read off. -/
def whereB (b : QL Bool) : QL Nat := ofList (out ⟨b.n, (b.r.inter (.test fun _ v => v)).dom⟩)

/-- `where v`: `⟨id, f ≫ range⟩`, read off, first component. -/
def whereN (x : QL Nat) : QL Nat :=
  ofList ((out ⟨x.n, (RelRep.ofFn id).pair (x.r ≫ .enum List.range)⟩).map Prod.fst)

/-- `est(≤)(f°)`: each value keyed by its first index; `f°` enumerates only when `f` is held as pairs, and
    so does the result, a cut of it. -/
def firstIx (x : QL A) : Option (FinRel A Nat) := (fin? x.r).bind fun r => fin? (RelRep.est leR (.pairs r.conv))

/-- `distinct x`: `est(≤)(f°)`, its converse read off. -/
def distinct (x : QL A) : Option (QL A) := (firstIx x).map fun d => ofList (out ⟨x.n, .pairs d.conv⟩)

/-- `group x`: keys `distinct x`, values `distinct x ≫ Λ(f°)`. -/
def group (x : QL A) : Option (QL A × QL (List Nat)) := do
  let r ← fin? x.r
  let d ← distinct x
  pure (d, ⟨d.n, d.r ≫ (RelRep.pairs r.conv).transpose⟩)

/-- `x union y`: `distinct(x,y)`; the join is re-tabulated, because `enum` first in a composite gives
    an `enum`, whose converse is only a test, which `est` cannot enumerate. -/
def union (x y : QL A) : Option (QL A) := distinct (ofList (out (join x y)))

/-- `x inter y`: `f ≫ ran g`, read off. -/
def inter (x y : QL A) : Option (QL A) := (fin? y.r).map fun r => ofList (out ⟨x.n, x.r ≫ RelRep.ran r⟩)

/-- `x except y`: `f` cut by the complement of `ran g`, written as a negated test. -/
def except (x y : QL A) : Option (QL A) := (fin? y.r).map fun r =>
  let c := RelRep.ran r
  ofList (out ⟨x.n, x.r.inter (.test fun _ a => !c.mem a a)⟩)

/-- `x in y`: `f ≫ χ(ran g)`. -/
def in_ (x y : QL A) : Option (QL Bool) := (fin? y.r).map fun r =>
  let c := RelRep.ran r
  ⟨x.n, x.r ≫ .ofFn fun a => c.mem a a⟩

def within (x : QL Int) (lo hi : Int) : QL Bool := ⟨x.n, x.r ≫ .ofFn fun a => decide (lo ≤ a ∧ a ≤ hi)⟩

/-- `x?y`: `g ≫ est(≤)(f°)`, `|x|` on an empty fibre. -/
def find (x y : QL A) : Option (QL Nat) :=
  (firstIx x).map fun e => ofList ((outN ⟨y.n, y.r ≫ .pairs e⟩).map (·.getD x.n))

/-- `{i ∣ i < n}`: the top relation onto the indices, which makes a test enumerable. -/
def top (n : Nat) : RelRep A Nat := .enum fun _ => List.range n

/-- `x bin y`: `g ≫ est(≥)(⊤ ∩ (f ≫ ≤)°)`, `-1` on an empty fibre. -/
def bin (x y : QL Int) : QL Int :=
  let e := RelRep.est geR ((top x.n).inter (x.r.compT (.test fun c a => decide (c ≤ a))).conv)
  ofList ((outN ⟨y.n, y.r ≫ e⟩).map fun o => (o.map Int.ofNat).getD (-1))

/-- `x binr y`: `g ≫ est(≤)(⊤ ∩ (f ≫ ≥)°)`, `|x|` on an empty fibre. -/
def binr (x y : QL Int) : QL Nat :=
  let e := RelRep.est leR ((top x.n).inter (x.r.compT (.test fun c a => decide (c ≥ a))).conv)
  ofList ((outN ⟨y.n, y.r ≫ e⟩).map (·.getD x.n))

/-! ## Sorts -/

/-- `iasc x`: `f°` sorted by value, stably; the indices in that order. -/
def iasc [Ord A] [Std.TransOrd A] (x : QL A) : Option (QL Nat) :=
  (fin? x.r).map fun r => ofList (SortedRel.sortByKey r.conv).vals.toList

def idesc (x : QL Int) : Option (QL Nat) := iasc ⟨x.n, x.r ≫ .ofFn Neg.neg⟩

/-- `asc x = iasc(x) ≫ f`. -/
def asc (x : QL Int) : Option (QL Int) := (iasc x).map fun p => ⟨x.n, p.r ≫ x.r⟩
def desc (x : QL Int) : Option (QL Int) := (idesc x).map fun p => ⟨x.n, p.r ≫ x.r⟩

/-- `rank x = iasc(x)°`. -/
def rank (x : QL Int) : Option (QL Nat) := (iasc x).bind fun p => (fin? p.r).map fun r => ⟨x.n, .pairs r.conv⟩

/-! ## Neighbours and nulls -/

/-- `differ x`: `⟨f, prev⟩ ≫ (≠)`, with index `0` sent to `1b`. -/
def differ (x : QL A) : QL Bool :=
  ⟨x.n, (x.r.pair (prev x).r ≫ .ofFn fun (a, b) => !decide (a = b)).union
    (RelRep.corefl (· == 0) ≫ .ofFn fun _ => true)⟩

/-- `null x`: `χ` of the complement of `dom f`. -/
def null (x : QL A) : QL Bool := let d := x.r.dom; ⟨x.n, .ofFn fun i => !d.mem i i⟩

/-- `fills x`: `est(≥)(≥ ≫ dom f) ≫ f`, the last non-null index at or before each. -/
def fills (x : QL A) : QL A :=
  ⟨x.n, RelRep.est geR (RelRep.enum (fun i => List.range (i + 1)) ≫ x.r.dom) ≫ x.r⟩

end QL

namespace QL2

open QL

variable {A : Type} [DecidableEq A] [FibreIndex A]

def ofLists (xss : List (List A)) : QL2 A :=
  ⟨xss.length, (xss.head?.map List.length).getD 0,
    .pairs (FinRel.ofList (xss.zipIdx.flatMap fun (xs, i) => xs.zipIdx.map fun (a, j) => ((i, j), a)))⟩

def out (x : QL2 A) : List (List A) :=
  (List.range x.n).map fun i => (List.range x.m).flatMap fun j => x.r.app (i, j)

/-- `flip x`: `swap ≫ f`. -/
def flip (x : QL2 A) : QL2 A := ⟨x.m, x.n, RelRep.ofFn Prod.swap ≫ x.r⟩

end QL2

/-! ## Runs against q -/

open QL

def ints (xs : List Int) : QL Int := ofList xs

#guard (til 5).out == [0, 1, 2, 3, 4]
#guard (reverse (ints [3, 1, 4, 1, 5])).out == [5, 1, 4, 1, 3]
#guard (first (ints [3, 1, 4])).outN == [some 3]
#guard (last (ints [3, 1, 4])).outN == [some 4]
#guard (first (ints [])).outN == [none]
#guard (take 3 (til 5)).out == [0, 1, 2]
#guard (take 8 (til 5)).out == [0, 1, 2, 3, 4, 0, 1, 2]
#guard (take (-3) (til 5)).out == [2, 3, 4]
#guard (take (-7) (til 5)).out == [3, 4, 0, 1, 2, 3, 4]
#guard (take 0 (til 5)).out == []
#guard (drop 2 (til 5)).out == [2, 3, 4]
#guard (drop (-2) (til 5)).out == [0, 1, 2]
#guard (drop 7 (til 5)).out == []
#guard (cut [0, 2, 4] (til 6)).map out == [[0, 1], [2, 3], [4, 5]]
#guard (cut [1, 3] (til 6)).map out == [[1, 2], [3, 4, 5]]
#guard (join (ints [1, 2]) (ints [3, 4, 5])).out == [1, 2, 3, 4, 5]
#guard (raze [ints [1, 2], ints [3], ints [4, 5, 6]]).out == [1, 2, 3, 4, 5, 6]
#guard (whereB (ofList [false, true, true, false, true])).out == [1, 2, 4]
#guard (whereN (ofList [2, 0, 1])).out == [0, 0, 2]
#guard (distinct (ints [3, 1, 3, 2, 1])).map out == some [3, 1, 2]
#guard (group (ints [3, 1, 3, 2, 1])).map (fun (k, v) => (k.out, v.out)) == some ([3, 1, 2], [[0, 2], [1, 4], [3]])
#guard (union (ints [1, 2, 3, 2]) (ints [2, 4, 1, 5])).map out == some [1, 2, 3, 4, 5]
#guard (inter (ints [1, 2, 3, 2]) (ints [2, 3, 4])).map out == some [2, 3, 2]
#guard (except (ints [1, 2, 3, 2]) (ints [2])).map out == some [1, 3]
#guard (in_ (ints [1, 2, 5]) (ints [2, 3, 5])).map out == some [false, true, true]
#guard (within (ints [3, 1, 7]) 2 5).out == [true, false, false]
#guard (find (ints [3, 1, 4, 1, 5]) (ints [1, 5, 7])).map out == some [1, 4, 5]
#guard (bin (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).out == [-1, 0, 1, 3]
#guard (binr (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).out == [0, 0, 2, 4]
#guard (bin (ints [1, 3, 3, 5]) (ints [3])).out == [2]
#guard (binr (ints [1, 3, 3, 5]) (ints [3])).out == [1]
#guard (rank (ints [3, 1, 4, 1, 5])).map out == some [2, 0, 3, 1, 4]
#guard (iasc (ints [3, 1, 4, 1, 5])).map out == some [1, 3, 0, 2, 4]
#guard (idesc (ints [3, 1, 4, 1, 5])).map out == some [4, 2, 0, 1, 3]
#guard (asc (ints [3, 1, 4, 1, 5])).map out == some [1, 1, 3, 4, 5]
#guard (desc (ints [3, 1, 4, 1, 5])).map out == some [5, 4, 3, 1, 1]
#guard (cross (ints [1, 2]) (ints [3, 4, 5])).out == [(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]
#guard (QL2.flip (QL2.ofLists ([[1, 2, 3], [4, 5, 6]] : List (List Int)))).out == [[1, 4], [2, 5], [3, 6]]
#guard (differ (ints [1, 1, 2, 2, 2, 3, 1])).out == [true, false, true, false, false, true, true]
#guard (next (ints [1, 2, 3])).outN == [some 2, some 3, none]
#guard (prev (ints [1, 2, 3])).outN == [none, some 1, some 2]
#guard (xprev 2 (ints [1, 2, 3, 4])).outN == [none, none, some 1, some 2]
#guard (sublist 2 (til 5)).out == [0, 1]
#guard (sublist (-2) (til 5)).out == [3, 4]
#guard (sublist 10 (til 5)).out == [0, 1, 2, 3, 4]
#guard (sublist2 1 2 (til 5)).out == [1, 2]
#guard (sublist2 3 10 (til 5)).out == [3, 4]
#guard (rotate 2 (til 5)).out == [2, 3, 4, 0, 1]
#guard (rotate (-1) (til 5)).out == [4, 0, 1, 2, 3]
#guard (rotate 7 (til 5)).out == [2, 3, 4, 0, 1]
#guard (null (ofListN [some (1 : Int), none, some 3])).out == [false, true, false]
#guard (fills (ofListN [none, some (1 : Int), none, none, some 3, none])).outN ==
  [none, some 1, some 1, some 1, some 3, some 3]

example : (reverse (ofList [3, 1, 4])).out = [4, 1, 3] := by decide
example : (take (-7) (til 5)).out = [3, 4, 0, 1, 2, 3, 4] := by decide

/-- `til n` reads off as `0..n-1`. -/
theorem out_til (n : Nat) : (til n).out = List.range n := by
  simp only [out, til, RelRep.corefl, RelRep.app_enum]
  calc (List.range n).flatMap (fun k => if decide (k < n) = true then [k] else [])
      = ((List.range n).map fun k => [k]).flatten :=
        congrArg List.flatten (List.map_congr_left fun k hk => by simp [List.mem_range.1 hk])
    _ = List.range n := by generalize List.range n = l; induction l <;> simp_all

end LeetQ.Q
