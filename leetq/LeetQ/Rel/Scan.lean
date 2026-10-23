/-
  Scans, folds, moving windows, grouped folds and the order verbs on the RelRep core (§3): each op is
  one qlean kernel dispatch over `val`'s column — `scanColumn` (`Scan.scan`/`scanFoR`/`scanAlp`),
  `overColumn` (`overBytes`/`Coc.over`), `overGroupsColumn` (`overGroups`), `Order.groupSizes`/
  `groupLasts`, `mwinColumn` (`Scan.mwin`/`mwinFoR`), `gradeColumn` (`grade`/`ranks`) and
  `sortedValues` (`sortValues`). No element is read at run time; a kernel's answer becomes an `Arr`
  only through `Arr.of`, which checks its type and count instead of assuming them.
  The specs are List functions on `toList`; `#guard` runs each op against its spec.
-/
import LeetQ.Rel.Core
import QLean.Kernel.Scan
import QLean.Kernel.Sort
import QLean.Kernel.Reduce
import QLean.Kernel.Search
import QLean.Kernel.Structural
import QLean.Verify.Where
import QLean.Verify.Group

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

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
  ((scanColumn f rt t R.val.c).bind fun c => (Arr.of (.atom rt) R.n c "f\\x").toOption).map R.withVal

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
  (Column.bytesOf .long o.c).map (groupOf · n)

/-- `count each` by group: `o[r+1] − o[r]`. -/
def countBy {v : Ty} : Rel k v → Option (Rel k (.atom .long))
  | ⟨n, .grp (g := g) d o _, _⟩ => do
    let ids ← groupIds o n
    pure ⟨g, d, ← (Arr.of (.atom .long) g (.bytes (Order.groupSizes g.toUSize ids)) "count each").toOption⟩
  | _ => none

/-- `last each` by group: `val[o[r+1]−1]`. `none` when a group is empty, which has no last row. -/
def lastBy : Rel k (.atom t) → Option (Rel k (.atom t))
  | ⟨n, .grp (g := g) d o _, x⟩ => do
    let ids ← groupIds o n
    let least ← overColumn .lesser .long (.bytes (Order.groupSizes g.toUSize ids))
    if 0 < g ∧ least ≤ 0 then none else
      pure ⟨g, d, ← (Arr.of (.atom t) g (← vecCol (← gatherColumn t x.c (.bytes (Order.groupLasts g.toUSize ids)))) "last each").toOption⟩
  | _ => none

/-- `select f x by k` at a `long` column: `f/` over each group's rows, the `Int64` accumulator. -/
def overBy (op : Coc.Over) : Rel k (.atom .long) → Option (Rel k (.atom .long))
  | ⟨n, .grp (g := g) d o _, x⟩ => do
    let ids ← groupIds o n
    -- `overGroups` answers each group's fold, then each group's live count; the folds are the answer
    let s ← overGroupsColumn op .long (.ids g.toUSize ids) x.c
    pure ⟨g, d, ← (Arr.of (.atom .long) g (.bytes (s.extract 0 (8 * g))) "f/ by").toOption⟩
  | _ => none

/-! ## Moving windows: `w mop x`, key kept -/

/-- `w msum/mcount/mavg/mdev/mmin/mmax x`, answered at `rt`; `none` where q answers another type. -/
def mwin (op : Scan.MOp) (w : Nat) (rt : QAtomicType) (R : Rel k (.atom t)) : Option (Rel k (.atom rt)) :=
  ((mwinColumn op t w R.n R.val.c).bind fun (rt', c) =>
    if rt' = rt then (Arr.of (.atom rt) R.n c "w mop x").toOption else none).map R.withVal

/-! ## Order: `iasc idesc rank asc desc xasc` -/

/-- `<x` / `>x`: the stable grade, keyed by position. -/
def grade (desc : Bool) (R : Rel k (.atom t)) : Option (Rel (.atom .long) (.atom .long)) := do
  let p ← vecCol (← gradeColumn t desc R.val.c)
  pure ⟨R.n, .til R.n, ← (Arr.of (.atom .long) R.n p "<x").toOption⟩

def iasc := @grade k t false
def idesc := @grade k t true

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order. -/
def rank (R : Rel k (.atom t)) : Option (Rel k (.atom .long)) :=
  (((gradeColumn t false R.val.c (rank := true)).bind vecCol).bind fun c => (Arr.of (.atom .long) R.n c "rank x").toOption).map R.withVal

/-- `x` reordered by the permutation column `p`: one gather. -/
def permute {n : Nat} (p : Column) (x : Arr (.atom t) n) (attr : UInt8 := 0) : Option (Arr (.atom t) n) := do
  (Arr.of (.atom t) n (← vecCol (← gatherColumn t x.c p)) "x@p" attr).toOption

/-- `asc x` / `desc x` = `(<x);x`, keyed by position. `sortValues` where the key is a bijection of
    the bits, the bitmap sort at `boolean`, the grade and a gather elsewhere. `asc` sets `s`. -/
def sort (desc : Bool) (R : Rel k (.atom t)) : Option (Rel (.atom .long) (.atom t)) := do
  let attr : UInt8 := if desc then 0 else 1
  let a ← match (sortedValues t desc R.val.c).orElse fun _ => sortedBitsColumn t desc R.val.c with
    | some v => (Arr.of (.atom t) R.n (← vecCol v) "asc x" attr).toOption
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

/-- The longs `overBytes` folds over a dense long payload are the column's elements. -/
theorem denseElems_long {R : Rel k (.atom .long)} {b : ByteArray} (hc : R.val.c = .bytes b) :
    QLean.Verify.denseElems Ew.i64 b = R.val.toList := by
  have hn : R.n = b.size / 8 := by have := R.val.wf.2; rw [hc] at this; simp only [Column.count] at this; exact this.symm
  apply List.ext_getElem
  · rw [QLean.Verify.denseElems, List.length_map, List.length_range, Arr.length_toList, hn]; rfl
  · intro j _ _
    simp only [QLean.Verify.denseElems, List.getElem_map, List.getElem_range]
    rw [Arr.getElem_toList, Arr.get_long_bytes R.val hc]; rfl

/-- `f/x` over a dense long column, at a verb that skips the null (not `all`/`any`): `Spec.over` at the
    kernel's step and seed, from `overBytes_eq`. -/
theorem over_bytes {op : Coc.Over} (hb : op.boolCast = false) {R : Rel k (.atom .long)} {b : ByteArray}
    (hc : R.val.c = .bytes b) : over op R = some (Spec.over op.step (op.denseSeed Ew.i64 Spec.nul) R.val.toList) := by
  have he : overBytes op Ew.i64 Spec.nul b = Spec.over op.step (op.denseSeed Ew.i64 Spec.nul) R.val.toList := by
    rw [QLean.Verify.overBytes_eq, QLean.Verify.overList, hb, QLean.Verify.foldl_filter, denseElems_long hc, Spec.over]
    congr 1; funext a x; by_cases hx : x = Spec.nul <;> simp [hx]
  simp only [over, overColumn, hc, overFoR, clsOf, Coc.denseNul, Coc.nullOf, bind, Option.bind, Coc.narrowed]
  rw [he]; simp

/-- Filtering `range n` by a test that fails from `L` on is filtering `range (min n L)`. -/
theorem filter_range_min {p : Nat → Bool} {L : Nat} (hp : ∀ i, L ≤ i → p i = false) (n : Nat) :
    (List.range n).filter p = (List.range (min n L)).filter p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n < L
    · rw [Nat.min_eq_left (show n + 1 ≤ L by omega)]
    · rw [List.range_succ, List.filter_append, ih, Nat.min_eq_right (show L ≤ n by omega),
        Nat.min_eq_right (show L ≤ n + 1 by omega), List.filter_cons_of_neg (by rw [hp n (by omega)]; exact Bool.false_ne_true),
        List.filter_nil, List.append_nil]

/-- The first `m` bytes read as the whole array wherever the read ends by `m`. -/
theorem bitsAt_extract (s : ByteArray) {m o w : Nat} (h : o + w ≤ m) :
    Column.bitsAt (s.extract 0 m) o w = Column.bitsAt s o w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have e : (if h : o + w < (s.extract 0 m).size then (s.extract 0 m)[o + w] else 0) =
        (if h : o + w < s.size then s[o + w] else 0) := by
      by_cases hs : o + w < s.size
      · rw [dif_pos (by rw [ByteArray.size_extract]; omega), dif_pos hs, ByteArray.getElem_extract]
        simp only [Nat.zero_add]
      · rw [dif_neg (by rw [ByteArray.size_extract]; omega), dif_neg hs]
    simp only [Column.bitsAt] at ih ⊢
    rw [ih (by omega), e]

/-- `select f x by k` over a dense long column, at a verb that skips the null: group `j`'s answer is
    `Spec.over` of the values of the rows the kernel's ids put in group `j`, from `overGroups_spec`. -/
theorem overBy_bytes {op : Coc.Over} (hb : op.boolCast = false) {n g : Nat} {d : KeyCol k g}
    {o : Arr (.atom .long) (g+1)} {co : Cuts o n} {x : Arr (.atom .long) n} {b ids : ByteArray}
    {S : Rel k (.atom .long)} (hg : g < USize.size) (hc : x.c = .bytes b) (hi : groupIds o n = some ids)
    (h : overBy op ⟨n, .grp d o co, x⟩ = some S) :
    S.val.toList = (List.range g).map fun j => Spec.over op.step (op.denseSeed Ew.i64 Spec.nul)
      (((List.range n).filter fun i => (QLean.Verify.ids ids)[i]? == some j).map fun i => x.toList[i]!) := by
  have hn : b.size / 8 = n := by have := x.wf.2; rw [hc] at this; exact this
  have hgu : g.toUSize.toNat = g := USize.toNat_ofNat_of_lt hg
  simp only [overBy, hi, overGroupsColumn, hc, clsOf, Coc.denseNul, Coc.nullOf, Column.bytesOf, bind, Option.bind] at h
  obtain ⟨hsz, hv⟩ := QLean.Verify.overGroups_spec op Ew.i64 Spec.nul g.toUSize ids b
  generalize overGroups op Ew.i64 Int64.minValue g.toUSize ids b = s at h hsz hv
  rw [hgu] at hsz hv
  by_cases hw : (Ty.atom .long).WF g (.bytes (s.extract 0 (8 * g)))
  · rw [Arr.of, dif_pos hw] at h
    cases h
    have hw8 : Ew.width Ew.i64 = 8 := rfl
    have e : QLean.Verify.denseElems Ew.i64 b = x.toList := denseElems_long (R := ⟨n, .grp d o co, x⟩) hc
    have hx : ∀ i, i < n → x.toList[i]! = QLean.Verify.valAt Ew.i64 b i := fun i hi => by
      rw [← e, QLean.Verify.denseElems, getElem!_pos _ i (by rw [List.length_map, List.length_range, hw8, hn]; exact hi),
        List.getElem_map, List.getElem_range]; rfl
    apply List.ext_getElem
    · rw [Arr.length_toList, List.length_map, List.length_range]
    · intro j h1 _
      have hj : j < g := by rwa [Arr.length_toList] at h1
      rw [Arr.getElem_toList, Arr.get_long_bytes _ rfl, List.getElem_map, List.getElem_range,
        bitsAt_extract s (m := 8 * g) (o := j * 8) (w := 8) (by omega), (hv j hj).1]
      have hr : QLean.Verify.rowsOf op Ew.i64 Spec.nul ids b j =
          ((List.range n).filter fun i => (QLean.Verify.ids ids)[i]? == some j).filter
            fun i => QLean.Verify.valAt Ew.i64 b i != Spec.nul := by
        rw [List.filter_filter, filter_range_min (L := ids.size / 8) ?hp n, QLean.Verify.rowsOf, hw8, hn]
        · refine List.filter_congr fun i hi => ?_
          have hi := List.mem_range.1 hi
          rw [hb, Bool.false_or, Bool.and_comm, QLean.Verify.ids, List.getElem?_map,
            List.getElem?_range (by omega), Option.map_some]
          rfl
        · intro i hi
          rw [QLean.Verify.ids, List.getElem?_map, List.getElem?_eq_none (by rw [List.length_range]; exact hi)]
          rw [Option.map_none, show ((none : Option Nat) == some j) = false from rfl, Bool.and_false]
      rw [hr, QLean.Verify.foldl_filter, Spec.over,
        List.map_congr_left (fun i hi => hx i (List.mem_range.1 (List.mem_filter.1 hi).1)), List.foldl_map]
      congr 1; funext a i; by_cases hx : QLean.Verify.valAt Ew.i64 b i = Spec.nul <;> simp [hx]
  · rw [Arr.of, dif_neg hw] at h
    cases h

end Ops

/-! ## Checks on small literal Rels -/

section Checks

open QLean.Column Ops

private def L {n : Nat} (a : Arr (.atom .long) n) : Rel (.atom .long) (.atom .long) := ⟨n, .til n, a⟩
private def vals {k v : Ty} (R : Option (Rel k v)) : List (El v) := (R.map fun R => R.val.toList).getD []

private def xs : List Int64 := [3, -1, 4, 1, -5, 9, 2, 6]
private def xn : List Int64 := [2, Int64.minValue, 7, 1]
private def xsA : Arr (.atom .long) 8 := { c := .bytes <| packLongs [3, -1, 4, 1, -5, 9, 2, 6], wf := by decide }
private def xnA : Arr (.atom .long) 4 := { c := .bytes <| packLongs [2, Int64.minValue, 7, 1], wf := by decide }
private def ysA : Arr (.atom .long) 4 := { c := .bytes <| packLongs [1, 2, 3, 6], wf := by decide }
private def zsA : Arr (.atom .long) 4 := { c := .bytes <| packLongs [1, 3, 3, 2], wf := by decide }
private def sA : Arr (.atom .long) 8 := { c := .bytes <| packLongs [2, 0, 1, 2, 0, 1, 2, 0], wf := by decide }
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
private def og : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 2, 3, 6], wf := by decide }
private def gv : List Int64 := [10, 20, 30, 40, 50, Int64.minValue]
private def G : Rel (.atom .long) (.atom .long) :=
  ⟨6, .grp (.til 3) og (by decide), { c := .bytes <| packLongs [10, 20, 30, 40, 50, Int64.minValue], wf := by decide }⟩
private def oe : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 1, 1, 3], wf := by decide }
private def E : Rel (.atom .long) (.atom .long) :=
  ⟨3, .grp (.til 3) oe (by decide), { c := .bytes <| packLongs [7, 8, 9], wf := by decide }⟩

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
#print axioms Ops.over_bytes
#print axioms Ops.overBy_bytes

end LeetQ.Rel
