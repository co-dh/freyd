/-
  Scans, folds, moving windows, grouped folds and the order verbs on the RelRep core (§3): each op is
  one qlean kernel dispatch over `val`'s column — `scanColumn` (`Scan.scan`/`scanFoR`/`scanAlp`),
  `overColumn` (`overBytes`/`Coc.over`), `overGroupsColumn` (`overGroups`), `Order.groupSizes`/
  `groupLasts`, `mwinColumn` (`Scan.mwin`/`mwinFoR`), `gradeColumn` (`grade`/`ranks`) and
  `sortedValues` (`sortValues`). No element is read at run time; a kernel's answer becomes an `Arr`
  only through `Arr.of?`, which checks its type and count instead of assuming them.
  The specs are List functions on `toList`; `#guard` runs each op against its spec.
-/
import LeetQ.Rel.Core
import QLean.Kernel.Scan
import QLean.Kernel.Sort
import QLean.Kernel.Reduce
import QLean.Kernel.Search
import QLean.Kernel.Structural

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

/-- A kernel's answer as an `Arr`: `none` when it is not `n` well-formed elements at `t`. -/
def Arr.of? (t : Ty) (n : Nat) (c : Pay t) (attr : UInt8 := 0) : Option (Arr t n) :=
  if h : t.WF n c then some { c, wf := h, attr } else none

/-- `R` with its values replaced, key kept. -/
def Rel.withVal {k v w : Ty} (R : Rel k v) (a : Arr w R.n) : Rel k w := ⟨R.n, R.key, a⟩

/-- The column of a q vector answer. -/
def vecCol : QValue → Option Column
  | .vector _ c => some c
  | _ => none

namespace Ops

variable {k : Ty} {t : QAtomicType}

/-! ## Scans: `f\x`, key kept -/

/-- `f\x` at the q dyad `f` (`+ * & | ^`), answered at `rt` (q's accumulator type). -/
def scan (f : Prim.Dyadic) (rt : QAtomicType) (R : Rel k (.atom t)) : Option (Rel k (.atom rt)) :=
  ((scanColumn f rt t R.val.c).bind (Arr.of? (.atom rt) R.n)).map R.withVal

/-! ## Folds: `f/x` -/

/-- `f/x` over the values in position order, as q's answer widened to `Int64`. -/
def over (op : Coc.Over) (R : Rel k (.atom t)) : Option Int64 := overColumn op t R.val.c

/-- `avg x`: the bits of the `float` q answers. -/
def avg (R : Rel k (.atom t)) : Option UInt64 :=
  (avgColumn t R.val.c).bind (Carrier.of? .float)

/-! ## Grouped folds over a `grp d o` key: the answer is keyed by `d`, one row per group -/

/-- The group of each of the `n` rows as `Int64`s: `o bin til n`, the largest `r` with `o[r] ≤ i`
    (`KeyCol.group`). -/
def groupIds {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Option ByteArray :=
  (Column.bytesOf .long o.c).map fun ob => binBytes 8 false true false ob (tilLongs n.toUSize)

/-- `count each` by group: `o[r+1] − o[r]`. -/
def countBy {v : Ty} : Rel k v → Option (Rel k (.atom .long))
  | ⟨n, .grp (g := g) d o _, _⟩ => do
    let ids ← groupIds o n
    pure ⟨g, d, ← Arr.of? (.atom .long) g (.bytes (Order.groupSizes g.toUSize ids))⟩
  | _ => none

/-- `last each` by group: `val[o[r+1]−1]`. `none` when a group is empty, which has no last row. -/
def lastBy : Rel k (.atom t) → Option (Rel k (.atom t))
  | ⟨n, .grp (g := g) d o _, x⟩ => do
    let ids ← groupIds o n
    let least ← overColumn .lesser .long (.bytes (Order.groupSizes g.toUSize ids))
    if 0 < g ∧ least ≤ 0 then none else
      pure ⟨g, d, ← Arr.of? (.atom t) g (← vecCol (← gatherColumn t x.c (.bytes (Order.groupLasts g.toUSize ids))))⟩
  | _ => none

/-- `select f x by k` at a `long` column: `f/` over each group's rows, the `Int64` accumulator. -/
def overBy (op : Coc.Over) : Rel k (.atom .long) → Option (Rel k (.atom .long))
  | ⟨n, .grp (g := g) d o _, x⟩ => do
    let ids ← groupIds o n
    -- `overGroups` answers each group's fold, then each group's live count; the folds are the answer
    let s ← overGroupsColumn op .long g.toUSize ids x.c
    pure ⟨g, d, ← Arr.of? (.atom .long) g (.bytes (s.extract 0 (8 * g)))⟩
  | _ => none

/-! ## Moving windows: `w mop x`, key kept -/

/-- `w msum/mcount/mavg/mdev/mmin/mmax x`, answered at `rt`; `none` where q answers another type. -/
def mwin (op : Scan.MOp) (w : Nat) (rt : QAtomicType) (R : Rel k (.atom t)) : Option (Rel k (.atom rt)) :=
  ((mwinColumn op t w R.n R.val.c).bind fun (rt', c) =>
    if rt' = rt then Arr.of? (.atom rt) R.n c else none).map R.withVal

/-! ## Order: `iasc idesc rank asc desc xasc` -/

/-- `<x` / `>x`: the stable grade, keyed by position. -/
def grade (desc : Bool) (R : Rel k (.atom t)) : Option (Rel (.atom .long) (.atom .long)) := do
  let p ← vecCol (← gradeColumn t desc R.val.c)
  pure ⟨R.n, .til R.n, ← Arr.of? (.atom .long) R.n p⟩

def iasc := @grade k t false
def idesc := @grade k t true

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order. -/
def rank (R : Rel k (.atom t)) : Option (Rel k (.atom .long)) :=
  (((gradeColumn t false R.val.c (rank := true)).bind vecCol).bind (Arr.of? (.atom .long) R.n)).map R.withVal

/-- `x` reordered by the permutation column `p`: one gather. -/
def permute {n : Nat} (p : Column) (x : Arr (.atom t) n) (attr : UInt8 := 0) : Option (Arr (.atom t) n) := do
  Arr.of? (.atom t) n (← vecCol (← gatherColumn t x.c p)) attr

/-- `asc x` / `desc x` = `(<x);x`, keyed by position. `sortValues` where the key is a bijection of
    the bits, the bitmap sort at `boolean`, the grade and a gather elsewhere. `asc` sets `s`. -/
def sort (desc : Bool) (R : Rel k (.atom t)) : Option (Rel (.atom .long) (.atom t)) := do
  let attr : UInt8 := if desc then 0 else 1
  let a ← match (sortedValues t desc R.val.c).orElse fun _ => sortedBitsColumn t desc R.val.c with
    | some v => Arr.of? (.atom t) R.n (← vecCol v) attr
    | none => permute (← vecCol (← gradeColumn t desc R.val.c)) R.val attr
  pure ⟨R.n, .til R.n, a⟩

def asc := @sort k t false
def desc := @sort k t true

/-- `xasc` on one more column of a table: `x` in the ascending order of the sort column `s`. -/
def xasc {n : Nat} {u : QAtomicType} (s : Arr (.atom t) n) (x : Arr (.atom u) n) : Option (Arr (.atom u) n) := do
  permute (← vecCol (← gradeColumn t false s.c)) x

end Ops

/-! ## The specs, on `toList` -/

namespace Spec

/-- q's long null. -/
abbrev nul : Int64 := Int64.minValue

/-- The seed, then the accumulator after each element (core has no `List.scanl`). -/
def scanl {α β : Type} (f : β → α → β) : β → List α → List β
  | a, [] => [a]
  | a, x :: xs => a :: scanl f (f a x) xs

/-- `f\x` with q's null skip: the accumulator after each element, a null leaving it unchanged. -/
def scan (step : Int64 → Int64 → Int64) (seed : Int64) (xs : List Int64) : List Int64 :=
  (scanl (fun a x => if x == nul then a else step a x) seed xs).tail

/-- `f/x` with the same skip. -/
def over (step : Int64 → Int64 → Int64) (seed : Int64) (xs : List Int64) : Int64 :=
  xs.foldl (fun a x => if x == nul then a else step a x) seed

/-- `w msum x` over no nulls: the sum of the last `w` elements up to each position. -/
def msum (w : Nat) (xs : List Int64) : List Int64 :=
  (List.range xs.length).map fun i => ((xs.take (i+1)).drop (i+1-w)).foldl (· + ·) 0

/-- `w mmin x`: the minimum of the last `w` elements up to each position. -/
def mmin (w : Nat) (xs : List Int64) : List Int64 :=
  (List.range xs.length).map fun i => ((xs.take (i+1)).drop (i+1-w)).foldl min Int64.maxValue

/-- `<x`: the stable ascending grade. -/
def iasc (xs : List Int64) : List Int64 :=
  ((List.range xs.length).mergeSort fun i j => decide (xs[i]! ≤ xs[j]!)).map Int64.ofNat

/-- `rank x`: position `i` holds where `i` stands in `<x`. -/
def rank (xs : List Int64) : List Int64 :=
  let p := (iasc xs).map Int64.toNatClampNeg
  (List.range xs.length).map fun i => Int64.ofNat (p.idxOf i)

/-- `asc x`. -/
def asc (xs : List Int64) : List Int64 := xs.mergeSort fun a b => decide (a ≤ b)

/-- The rows of each group of `o`, in group order. -/
def groups (o : List Nat) (xs : List Int64) : List (List Int64) :=
  (o.zip o.tail).map fun (a, b) => (xs.drop a).take (b - a)

/-- The last element of a scan is the fold: `scan_succ` read at the end. -/
theorem scanl_getLast? {α β : Type} (f : β → α → β) (a : β) (xs : List α) :
    (scanl f a xs).getLast? = some (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [scanl, List.foldl_cons]
    cases h : scanl f (f a x) xs with
    | nil => cases xs <;> simp [scanl] at h
    | cons y ys => rw [List.getLast?_cons_cons, ← h, ih]

/-- So the last of `Spec.scan` is `Spec.over` on a nonempty list. -/
theorem scan_getLast? (f : Int64 → Int64 → Int64) (a : Int64) (xs : List Int64) (h : xs ≠ []) :
    (scan f a xs).getLast? = some (over f a xs) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp only [scan, over, scanl, List.tail_cons, List.foldl_cons]
  exact scanl_getLast? _ _ _

end Spec

/-! ## Laws on the ops -/

namespace Ops

variable {k : Ty} {t : QAtomicType}

/-- Replacing the values keeps the keys, whatever the new values are. -/
theorem withVal_keys {v w : Ty} {R : Rel k v} {o : Option (Arr w R.n)} {S : Rel k w}
    (h : o.map R.withVal = some S) : S.toList.map Prod.fst = R.toList.map Prod.fst := by
  cases o with
  | none => cases h
  | some a =>
    cases h
    apply List.ext_getElem <;> simp [Rel.withVal, Rel.toList]

/-- `f\x` keeps the keys. -/
theorem scan_keys {f : Prim.Dyadic} {rt : QAtomicType} {R : Rel k (.atom t)} {S : Rel k (.atom rt)}
    (h : scan f rt R = some S) : S.toList.map Prod.fst = R.toList.map Prod.fst := withVal_keys h

/-- `w mop x` keeps the keys. -/
theorem mwin_keys {op : Scan.MOp} {w : Nat} {rt : QAtomicType} {R : Rel k (.atom t)} {S : Rel k (.atom rt)}
    (h : mwin op w rt R = some S) : S.toList.map Prod.fst = R.toList.map Prod.fst := withVal_keys h

/-- `rank x` keeps the keys. -/
theorem rank_keys {R : Rel k (.atom t)} {S : Rel k (.atom .long)} (h : rank R = some S) :
    S.toList.map Prod.fst = R.toList.map Prod.fst := withVal_keys h

end Ops

/-! ## Checks on small literal Rels -/

section Checks

open QLean.Column Ops

private def longs (xs : List Int64) : Column := .bytes (xs.foldl (fun b x => pushBits b x.toUInt64 8) .empty)
private def L {n : Nat} (a : Arr (.atom .long) n) : Rel (.atom .long) (.atom .long) := ⟨n, .til n, a⟩
private def vals {k v : Ty} (R : Option (Rel k v)) : List (El v) := (R.map fun R => R.val.toList).getD []

private def xs : List Int64 := [3, -1, 4, 1, -5, 9, 2, 6]
private def xn : List Int64 := [2, Int64.minValue, 7, 1]
private def xsA : Arr (.atom .long) 8 := { c := longs [3, -1, 4, 1, -5, 9, 2, 6], wf := by decide }
private def xnA : Arr (.atom .long) 4 := { c := longs [2, Int64.minValue, 7, 1], wf := by decide }
private def ysA : Arr (.atom .long) 4 := { c := longs [1, 2, 3, 6], wf := by decide }
private def zsA : Arr (.atom .long) 4 := { c := longs [1, 3, 3, 2], wf := by decide }
private def sA : Arr (.atom .long) 8 := { c := longs [2, 0, 1, 2, 0, 1, 2, 0], wf := by decide }
#guard xsA.toList == xs ∧ xnA.toList == xn

#guard vals (scan .add .long (L xsA)) == Spec.scan (· + ·) 0 xs
#guard vals (scan .add .long (L xnA)) == Spec.scan (· + ·) 0 xn
#guard vals (scan .mul .long (L xsA)) == Spec.scan (· * ·) 1 xs
#guard vals (scan .lesser .long (L xnA)) == Spec.scan min Int64.maxValue xn
#guard vals (scan .greater .long (L xnA)) == Spec.scan max (Int64.minValue + 1) xn
#guard vals (scan .fill .long (L xnA)) == Spec.scan (fun _ x => x) Spec.nul xn
#guard ((scan .add .long (L xsA)).map (·.key.toList)) == some (List.range 8 |>.map Int64.ofNat)

#guard over .add (L xsA) == some (Spec.over (· + ·) 0 xs)
#guard over .add (L xnA) == some (Spec.over (· + ·) 0 xn)
#guard over .mul (L xsA) == some (Spec.over (· * ·) 1 xs)
#guard over .lesser (L xnA) == some (Spec.over min Int64.maxValue xn)
#guard over .greater (L xsA) == some (Spec.over max (Int64.minValue + 1) xs)
#guard avg (L ysA) == some (3.0 : Float).toBits

#guard vals (mwin .msum 3 .long (L xsA)) == Spec.msum 3 xs
#guard vals (mwin .mmin 3 .long (L xsA)) == Spec.mmin 3 xs
#guard (mwin .msum 3 .int (L xsA)).isNone

#guard vals (iasc (L xsA)) == Spec.iasc xs
#guard vals (idesc (L zsA)) == [1, 2, 3, 0]
#guard vals (rank (L xsA)) == Spec.rank xs
#guard vals (asc (L xsA)) == Spec.asc xs
#guard ((asc (L xsA)).map (·.val.attr)) == some 1
#guard vals (desc (L xsA)) == (Spec.asc xs).reverse
#guard ((xasc sA xsA).map Arr.toList) == some ((Spec.iasc sA.toList).map fun i => xs[i.toNatClampNeg]!)

-- the parted list `(10 20; 30; 40 50 60)` and the groups `[0,1) [1,1) [1,3)` with an empty middle one
private def og : Arr (.atom .long) 4 := { c := longs [0, 2, 3, 6], wf := by decide }
private def gv : List Int64 := [10, 20, 30, 40, 50, Int64.minValue]
private def G : Rel (.atom .long) (.atom .long) :=
  ⟨6, .grp (.til 3) og (by decide), { c := longs [10, 20, 30, 40, 50, Int64.minValue], wf := by decide }⟩
private def oe : Arr (.atom .long) 4 := { c := longs [0, 1, 1, 3], wf := by decide }
private def E : Rel (.atom .long) (.atom .long) :=
  ⟨3, .grp (.til 3) oe (by decide), { c := longs [7, 8, 9], wf := by decide }⟩

#guard groupIds og 6 == some (ByteArray.mk #[0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 1,0,0,0,0,0,0,0,
  2,0,0,0,0,0,0,0, 2,0,0,0,0,0,0,0, 2,0,0,0,0,0,0,0])
#guard vals (countBy G) == ((Spec.groups [0, 2, 3, 6] gv).map fun g => Int64.ofNat g.length)
#guard vals (countBy E) == [1, 0, 2]
#guard ((countBy G).map (·.key.toList)) == some [0, 1, 2]
#guard vals (lastBy G) == ((Spec.groups [0, 2, 3, 6] gv).map fun g => g.getLastD 0)
#guard (lastBy E).isNone
#guard vals (overBy .add G) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over (· + ·) 0))
#guard vals (overBy .greater G) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over max (Int64.minValue + 1)))
#guard vals (overBy .add E) == [7, 0, 17]

end Checks

#print axioms Ops.scan_keys
#print axioms Ops.mwin_keys
#print axioms Ops.rank_keys
#print axioms Spec.scan_getLast?

end LeetQ.Rel
