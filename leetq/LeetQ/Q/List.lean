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
  Every expected value in a `#guard` is q's own output on the same input (q 4.x, `.Q.s1`).
-/
import AOP.A6_FinRel

namespace LeetQ.Q

open Freyd Freyd.Alg Freyd.Alg.RelSet

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

/-- The positions of a result: `Λ(f)` flattened over `0..n-1`; `none` on a `test`. -/
def out (x : QL A) : Option (List A) := x.r.app?.map fun f => (List.range x.n).flatMap f

/-- The same with nulls: an empty fibre is `none`. -/
def outN (x : QL A) : Option (List (Option A)) :=
  x.r.app?.map fun f => (List.range x.n).map fun i => (f i).head?

/-- `G f` read on `0..m-1`: every verb that only moves indices. -/
def pull (m : Nat) (G : RelRep Nat Nat) (x : QL A) : Option (QL A) := (G.comp x.r).map (⟨m, ·⟩)

theorem rel_pull {m : Nat} {G : RelRep Nat Nat} {x y : QL A} (h : pull m G x = some y) :
    y.r.rel = G.rel ≫ x.r.rel := by
  cases hc : G.comp x.r with
  | none => simp [pull, hc] at h
  | some T =>
    simp only [pull, hc, Option.map_some, Option.some.injEq] at h
    subst h; exact RelRep.rel_comp hc

/-- `≤` and `≥` on indices, as tests. -/
def leR : RelRep Nat Nat := .test fun a b => decide (a ≤ b)
def geR : RelRep Nat Nat := .test fun a b => decide (a ≥ b)

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
def cut (cs : List Nat) (x : QL A) : Option (List (QL A)) :=
  (cs.zip (cs.drop 1 ++ [x.n])).mapM fun (s, e) => pull (e - s) (.ofFn (· + s)) x

/-- `k sublist x`: `take` clamped to the length. -/
def sublist (k : Int) (x : QL A) :=
  pull (min k.natAbs x.n) (.ofFn fun i => if 0 ≤ k then i else i + x.n - min k.natAbs x.n) x

def sublist2 (s l : Nat) (x : QL A) := pull (min l (x.n - s)) (.ofFn (· + s)) x
def rotate (k : Int) (x : QL A) := pull x.n (.ofFn fun i => (((i : Int) + k) % (x.n : Int)).toNat) x
def next (x : QL A) := pull x.n (shift 1) x
def prev (x : QL A) := pull x.n (shift (-1)) x
def xprev (k : Nat) (x : QL A) := pull x.n (shift (-(k : Int))) x

/-- `x,y`: the index map into `Nat ⊕ Nat`, then the junction `[f,g]`. -/
def join (x y : QL A) : Option (QL A) :=
  ((RelRep.ofFn fun i => (if i < x.n then .inl i else .inr (i - x.n) : Nat ⊕ Nat)).comp (x.r.junction y.r)).map
    (⟨x.n + y.n, ·⟩)

def nil : QL A := ⟨0, .enum fun _ => []⟩

/-- `raze`: the fold of `join`. -/
def raze (xs : List (QL A)) : Option (QL A) := xs.foldrM (fun x acc => join x acc) nil

/-- `x cross y`: `i ↦ (i / |y|, i mod |y|)`, then `f × g`. -/
def cross (x : QL A) (y : QL B) : Option (QL (A × B)) :=
  ((RelRep.ofFn fun i => (i / y.n, i % y.n)).comp (x.r.prod y.r)).map (⟨x.n * y.n, ·⟩)

/-! ## Searches by value: `f°` -/

/-- `where b`: `dom(f ∩ (=1b))` read off. -/
def whereB (b : QL Bool) : Option (QL Nat) :=
  (b.r.inter (.test fun _ v => v)).dom.bind fun d => (out ⟨b.n, d⟩).map ofList

/-- `where v`: `⟨id, f ≫ range⟩`, read off, first component. -/
def whereN (x : QL Nat) : Option (QL Nat) := do
  let c ← x.r.comp (.enum List.range)
  (out ⟨x.n, (RelRep.ofFn id).pair c⟩).map fun ps => ofList (ps.map Prod.fst)

/-- `distinct x`: `est(≤)(f°)` keys each value by its first index; its converse read off. -/
def distinct (x : QL A) : Option (QL A) :=
  (RelRep.est leR x.r.conv).bind fun d => (out ⟨x.n, d.conv⟩).map ofList

/-- `group x`: keys `distinct x`, values `distinct x ≫ Λ(f°)`. -/
def group (x : QL A) : Option (QL A × QL (List Nat)) := do
  let d ← distinct x
  let t ← x.r.conv.transpose
  let v ← d.r.comp t
  pure (d, ⟨d.n, v⟩)

/-- `x union y`: `distinct(x,y)`; the join is re-tabulated, because `enum` first in a composite gives
    an `enum`, whose converse is only a test, which `est` cannot enumerate. -/
def union (x y : QL A) : Option (QL A) := join x y >>= out >>= fun l => distinct (ofList l)

/-- `x inter y`: `f ≫ ran g`, read off. -/
def inter (x y : QL A) : Option (QL A) := do
  let c ← y.r.ran
  let s ← x.r.comp c
  (out ⟨x.n, s⟩).map ofList

/-- `x except y`: `f` cut by the complement of `ran g`, written as a negated test. -/
def except (x y : QL A) : Option (QL A) := do
  let c ← y.r.ran
  (out ⟨x.n, x.r.inter (.test fun _ a => !c.mem a a)⟩).map ofList

/-- `x in y`: `f ≫ χ(ran g)`. -/
def in_ (x y : QL A) : Option (QL Bool) := do
  let c ← y.r.ran
  (x.r.comp (.ofFn fun a => c.mem a a)).map (⟨x.n, ·⟩)

def within (x : QL Int) (lo hi : Int) : Option (QL Bool) :=
  (x.r.comp (.ofFn fun a => decide (lo ≤ a ∧ a ≤ hi))).map (⟨x.n, ·⟩)

/-- `x?y`: `g ≫ est(≤)(f°)`, `|x|` on an empty fibre. -/
def find (x y : QL A) : Option (QL Nat) := do
  let e ← RelRep.est leR x.r.conv
  let s ← y.r.comp e
  (outN ⟨y.n, s⟩).map fun l => ofList (l.map (·.getD x.n))

/-- `{i ∣ i < n}`: the top relation onto the indices, which makes a test enumerable. -/
def top (n : Nat) : RelRep A Nat := .enum fun _ => List.range n

/-- `x bin y`: `g ≫ est(≥)(⊤ ∩ (f ≫ ≤)°)`, `-1` on an empty fibre. -/
def bin (x y : QL Int) : Option (QL Int) := do
  let le ← x.r.comp (.test fun c a => decide (c ≤ a))
  let e ← RelRep.est geR ((top x.n).inter le.conv)
  let s ← y.r.comp e
  (outN ⟨y.n, s⟩).map fun l => ofList (l.map fun o => (o.map Int.ofNat).getD (-1))

/-- `x binr y`: `g ≫ est(≤)(⊤ ∩ (f ≫ ≥)°)`, `|x|` on an empty fibre. -/
def binr (x y : QL Int) : Option (QL Nat) := do
  let ge ← x.r.comp (.test fun c a => decide (c ≥ a))
  let e ← RelRep.est leR ((top x.n).inter ge.conv)
  let s ← y.r.comp e
  (outN ⟨y.n, s⟩).map fun l => ofList (l.map (·.getD x.n))

/-! ## Sorts -/

/-- `iasc x`: `f°` sorted by value, stably; the indices in that order. -/
def iasc [Ord A] [Std.TransOrd A] (x : QL A) : Option (QL Nat) :=
  match x.r.conv with
  | .pairs r => some (ofList (SortedRel.sortByKey r).vals.toList)
  | _ => none

def idesc (x : QL Int) : Option (QL Nat) := (x.r.comp (.ofFn Neg.neg)) >>= fun m => iasc ⟨x.n, m⟩

/-- `asc x = iasc(x) ≫ f`. -/
def asc (x : QL Int) : Option (QL Int) := iasc x >>= fun p => (p.r.comp x.r).map (⟨x.n, ·⟩)
def desc (x : QL Int) : Option (QL Int) := idesc x >>= fun p => (p.r.comp x.r).map (⟨x.n, ·⟩)

/-- `rank x = iasc(x)°`. -/
def rank (x : QL Int) : Option (QL Nat) := iasc x >>= fun p => some ⟨x.n, p.r.conv⟩

/-! ## Neighbours and nulls -/

/-- `differ x`: `⟨f, prev⟩ ≫ (≠)`, with index `0` sent to `1b`. -/
def differ (x : QL A) : Option (QL Bool) := do
  let p ← prev x
  let ne ← (x.r.pair p.r).comp (.ofFn fun (a, b) => !decide (a = b))
  let z ← (RelRep.corefl (· == 0)).comp (.ofFn fun _ => true)
  pure ⟨x.n, ne.union z⟩

/-- `null x`: `χ` of the complement of `dom f`. -/
def null (x : QL A) : Option (QL Bool) := x.r.dom.map fun d => ⟨x.n, .ofFn fun i => !d.mem i i⟩

/-- `fills x`: `est(≥)(≥ ≫ dom f) ≫ f`, the last non-null index at or before each. -/
def fills (x : QL A) : Option (QL A) := do
  let d ← x.r.dom
  let le ← (RelRep.enum fun i => List.range (i + 1)).comp d
  let e ← RelRep.est geR le
  (e.comp x.r).map (⟨x.n, ·⟩)

end QL

namespace QL2

open QL

variable {A : Type} [DecidableEq A] [FibreIndex A]

def ofLists (xss : List (List A)) : QL2 A :=
  ⟨xss.length, (xss.head?.map List.length).getD 0,
    .pairs (FinRel.ofList (xss.zipIdx.flatMap fun (xs, i) => xs.zipIdx.map fun (a, j) => ((i, j), a)))⟩

def out (x : QL2 A) : Option (List (List A)) :=
  x.r.app?.map fun f => (List.range x.n).map fun i => (List.range x.m).flatMap fun j => f (i, j)

/-- `flip x`: `swap ≫ f`. -/
def flip (x : QL2 A) : Option (QL2 A) := ((RelRep.ofFn Prod.swap).comp x.r).map (⟨x.m, x.n, ·⟩)

end QL2

/-! ## Runs against q -/

open QL

def ints (xs : List Int) : QL Int := ofList xs

#guard (til 5).out == some [0, 1, 2, 3, 4]
#guard (reverse (ints [3, 1, 4, 1, 5])).bind out == some [5, 1, 4, 1, 3]
#guard (first (ints [3, 1, 4])).bind outN == some [some 3]
#guard (last (ints [3, 1, 4])).bind outN == some [some 4]
#guard (first (ints [])).bind outN == some [none]
#guard (take 3 (til 5)).bind out == some [0, 1, 2]
#guard (take 8 (til 5)).bind out == some [0, 1, 2, 3, 4, 0, 1, 2]
#guard (take (-3) (til 5)).bind out == some [2, 3, 4]
#guard (take (-7) (til 5)).bind out == some [3, 4, 0, 1, 2, 3, 4]
#guard (take 0 (til 5)).bind out == some []
#guard (drop 2 (til 5)).bind out == some [2, 3, 4]
#guard (drop (-2) (til 5)).bind out == some [0, 1, 2]
#guard (drop 7 (til 5)).bind out == some []
#guard (cut [0, 2, 4] (til 6)).bind (·.mapM out) == some [[0, 1], [2, 3], [4, 5]]
#guard (cut [1, 3] (til 6)).bind (·.mapM out) == some [[1, 2], [3, 4, 5]]
#guard (join (ints [1, 2]) (ints [3, 4, 5])).bind out == some [1, 2, 3, 4, 5]
#guard (raze [ints [1, 2], ints [3], ints [4, 5, 6]]).bind out == some [1, 2, 3, 4, 5, 6]
#guard (whereB (ofList [false, true, true, false, true])).bind out == some [1, 2, 4]
#guard (whereN (ofList [2, 0, 1])).bind out == some [0, 0, 2]
#guard (distinct (ints [3, 1, 3, 2, 1])).bind out == some [3, 1, 2]
#guard (group (ints [3, 1, 3, 2, 1])).map (fun (k, v) => (k.out, v.out)) == some (some [3, 1, 2], some [[0, 2], [1, 4], [3]])
#guard (union (ints [1, 2, 3, 2]) (ints [2, 4, 1, 5])).bind out == some [1, 2, 3, 4, 5]
#guard (inter (ints [1, 2, 3, 2]) (ints [2, 3, 4])).bind out == some [2, 3, 2]
#guard (except (ints [1, 2, 3, 2]) (ints [2])).bind out == some [1, 3]
#guard (in_ (ints [1, 2, 5]) (ints [2, 3, 5])).bind out == some [false, true, true]
#guard (within (ints [3, 1, 7]) 2 5).bind out == some [true, false, false]
#guard (find (ints [3, 1, 4, 1, 5]) (ints [1, 5, 7])).bind out == some [1, 4, 5]
#guard (bin (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).bind out == some [-1, 0, 1, 3]
#guard (binr (ints [1, 3, 5, 7]) (ints [0, 1, 4, 9])).bind out == some [0, 0, 2, 4]
#guard (bin (ints [1, 3, 3, 5]) (ints [3])).bind out == some [2]
#guard (binr (ints [1, 3, 3, 5]) (ints [3])).bind out == some [1]
#guard (rank (ints [3, 1, 4, 1, 5])).bind out == some [2, 0, 3, 1, 4]
#guard (iasc (ints [3, 1, 4, 1, 5])).bind out == some [1, 3, 0, 2, 4]
#guard (idesc (ints [3, 1, 4, 1, 5])).bind out == some [4, 2, 0, 1, 3]
#guard (asc (ints [3, 1, 4, 1, 5])).bind out == some [1, 1, 3, 4, 5]
#guard (desc (ints [3, 1, 4, 1, 5])).bind out == some [5, 4, 3, 1, 1]
#guard (cross (ints [1, 2]) (ints [3, 4, 5])).bind out == some [(1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]
#guard (QL2.flip (QL2.ofLists ([[1, 2, 3], [4, 5, 6]] : List (List Int)))).bind QL2.out == some [[1, 4], [2, 5], [3, 6]]
#guard (differ (ints [1, 1, 2, 2, 2, 3, 1])).bind out == some [true, false, true, false, false, true, true]
#guard (next (ints [1, 2, 3])).bind outN == some [some 2, some 3, none]
#guard (prev (ints [1, 2, 3])).bind outN == some [none, some 1, some 2]
#guard (xprev 2 (ints [1, 2, 3, 4])).bind outN == some [none, none, some 1, some 2]
#guard (sublist 2 (til 5)).bind out == some [0, 1]
#guard (sublist (-2) (til 5)).bind out == some [3, 4]
#guard (sublist 10 (til 5)).bind out == some [0, 1, 2, 3, 4]
#guard (sublist2 1 2 (til 5)).bind out == some [1, 2]
#guard (sublist2 3 10 (til 5)).bind out == some [3, 4]
#guard (rotate 2 (til 5)).bind out == some [2, 3, 4, 0, 1]
#guard (rotate (-1) (til 5)).bind out == some [4, 0, 1, 2, 3]
#guard (rotate 7 (til 5)).bind out == some [2, 3, 4, 0, 1]
#guard (null (ofListN [some (1 : Int), none, some 3])).bind out == some [false, true, false]
#guard (fills (ofListN [none, some (1 : Int), none, none, some 3, none])).bind outN ==
  some [none, some 1, some 1, some 1, some 3, some 3]

example : (reverse (ofList [3, 1, 4])).bind out = some [4, 1, 3] := by decide
example : (take (-7) (til 5)).bind out = some [3, 4, 0, 1, 2, 3, 4] := by decide

/-- `til n` reads off as `0..n-1`. -/
theorem out_til (n : Nat) : (til n).out = some (List.range n) := by
  simp only [out, til, RelRep.app?, RelRep.corefl, Option.map_some, Option.some.injEq]
  calc (List.range n).flatMap (fun k => if decide (k < n) = true then [k] else [])
      = ((List.range n).map fun k => [k]).flatten :=
        congrArg List.flatten (List.map_congr_left fun k hk => by simp [List.mem_range.1 hk])
    _ = List.range n := by generalize List.range n = l; induction l <;> simp_all

end LeetQ.Q
