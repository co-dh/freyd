/-
  Scans, folds, moving windows, grouped folds and the order verbs on the RelRep core (§3): each op is
  one qlean kernel dispatch over `val`'s column — `scanColumn` (`Scan.scan`/`scanFoR`/`scanAlp`),
  `overColumn` (`overBytes`/`Coc.over`), `groupedOver` over `Groups.segs` (`overSegments`), `Ew.val`
  over a `grp` key's offsets, `mwinColumn` (`Scan.mwin`/`mwinFoR`/`mwinAlp`/`mwinBitmap`), `gradeColumn` (`grade`/`ranks`) and
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
import QLean.Verify.Structural
import QLean.Verify.BinWin

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

/-! ## Grouped folds over a `grp d o` key: the answer is keyed by `d`, one row per group

A `grp d o` key's groups are the segments of `o`, so every op here reads `o` and writes no group id
per row: `o bin til n` would be an `n`-row pass to recover what `o` already says. -/

/-- `o`'s dense payload, the `g+1` offsets the segment kernels read. -/
def offs {g : Nat} (o : Arr (.atom .long) (g+1)) : Option ByteArray := Column.bytesOf .long o.c

/-- `1_o` over `g+1` offsets: each group's end. -/
def ends (g : Nat) (ob : ByteArray) : ByteArray := ob.extract 8 (8 * (g+1))

/-- `1_deltas o`, each group's size `o[r+1] − o[r]`: one `Ew.val` pass over the offsets, which hold
    no null, so `0N` as the null changes nothing. -/
def sizes (g : Nat) (ob : ByteArray) : ByteArray :=
  Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (ends g ob) (ob.extract 0 (8 * g)) g.toUSize

/-- `count each` by group: `1_deltas o`. -/
def countBy {v : Ty} : Rel k v → Option (Rel k (.atom .long))
  | ⟨_, .grp (g := g) d o _, _⟩ => do
    pure ⟨g, d, ← (Arr.of (.atom .long) g (.bytes (sizes g (← offs o))) "count each").toOption⟩
  | _ => none

/-- `last each` by group: `x[-1+1_o]`. `none` when a group is empty, which has no last row. -/
def lastBy : Rel k (.atom t) → Option (Rel k (.atom t))
  | ⟨_, .grp (g := g) d o _, x⟩ => do
    let ob ← offs o
    let least ← overColumn .lesser .long (.bytes (sizes g ob))
    if 0 < g ∧ least ≤ 0 then none else
      let lasts := Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (ends g ob) (atomBytes Ew.i64 (-1 : Int64).toUInt64) g.toUSize
      pure ⟨g, d, ← (Arr.of (.atom t) g (← vecCol (← gatherColumn t x.c (.bytes lasts))) "last each").toOption⟩
  | _ => none

/-- `select f x by k`: `f/` over each segment's rows at every type q's grouped fold has an engine for
    (`groupedOver`: integral and float, not boolean), answered at `Coc.Over.resultType`'s type, q's
    type for `f/` of a `t`, which comes with the answer. -/
def overBy (op : Coc.Over) (R : Rel k (.atom t)) : Option ((rt : QAtomicType) × Rel k (.atom rt)) :=
  match R with
  | ⟨_, .grp (g := g) d o _, x⟩ => do
    let rt ← op.resultType false t
    let s ← groupedOver op false false t (.segs (← offs o)) x.c (tilLongs g.toUSize)
    pure ⟨rt, g, d, ← (Arr.of (.atom rt) g (.bytes s) "f/ by").toOption⟩
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

/-- `w mmin x` / `w mmax x` as q runs them, `(w-1)&':/x`: the extreme of the last `w` elements, the
    each-prior `seed` standing as the oldest element of each of the first `w-1` windows, and a tie
    keeping the older element (`better` is strict). -/
def mext (better : Int64 → Int64 → Bool) (seed : Int64) (w : Nat) (xs : List Int64) : List Int64 :=
  (List.range xs.length).map fun i =>
    let win := (xs.take (i+1)).drop (i+1-w)
    match (if i + 1 < w then seed :: win else win) with
    | e :: es => es.foldl (fun e u => if better u e then u else e) e
    | [] => seed

/-- `<x` (`desc = false`) / `>x`: the stable grade, ties in index order both ways round. -/
def grade (desc : Bool) (xs : List Int64) : List Int64 :=
  ((List.range xs.length).mergeSort fun i j => if desc then decide (xs[j]! ≤ xs[i]!) else decide (xs[i]! ≤ xs[j]!)).map
    Int64.ofNat

/-- `rank x`: position `i` holds where `i` stands in `<x`. -/
def rank (xs : List Int64) : List Int64 :=
  let p := (grade false xs).map Int64.toNatClampNeg
  (List.range xs.length).map fun i => Int64.ofNat (p.idxOf i)

/-- `asc x` (`desc = false`) / `desc x`: the stable sort, ties in the order they came both ways round. -/
def sort (desc : Bool) (xs : List Int64) : List Int64 :=
  xs.mergeSort fun a b => if desc then decide (b ≤ a) else decide (a ≤ b)

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

/-- A `long` fold that is not `all`/`any` answers at `long`. -/
theorem resultType_long {op : Coc.Over} (hb : op.boolCast = false) : op.resultType false .long = some .long := by
  cases op <;> first | rfl | cases hb

/-- `groupedOver` at `long`: the integral fold, each cell its slot's eight bytes. -/
theorem groupedOver_long {op : Coc.Over} (hb : op.boolCast = false) (gs : Groups) (c : Column) (ord : ByteArray) :
    groupedOver op false false .long gs c ord =
      (overGroupsColumn op .long gs c).map fun m => groupCells .wrap 8 gs.count m ord := by
  have hr := resultType_long hb
  cases h : overGroupsColumn op .long gs c <;> cases op <;> simp_all [groupedOver, bind, Option.bind] <;> rfl

/-- Offset `j` of `o` is the long `atI64` reads at `j` of its dense payload. -/
theorem offs_get {g : Nat} {o : Arr (.atom .long) (g+1)} {ob : ByteArray} (ho : o.c = .bytes ob) {j : Nat}
    (hj : j < g + 1) : o.toList[j]! = atI64 ob j := by
  rw [getElem!_pos _ j (by rw [Arr.length_toList]; exact hj), Arr.getElem_toList, Arr.get_long_bytes o ho, QLean.Verify.atI64_eq]

/-- **`select f x by k` over a dense long column**, at a verb that skips the null: group `j`'s answer
    is `Spec.over` of the rows of the segment of `o` that holds them, `o[j] ≤ i < o[j+1]`. No `Cuts`
    is needed: rows outside `[0, n)` and a descending pair of offsets name no row. -/
theorem overBy_bytes {op : Coc.Over} (hb : op.boolCast = false) {n g : Nat} {d : KeyCol k g}
    {o : Arr (.atom .long) (g+1)} {co : Cuts o n} {x : Arr (.atom .long) n} {b ob : ByteArray}
    {S : Rel k (.atom .long)} (hg : g < USize.size) (h63 : g < 2 ^ 63) (hc : x.c = .bytes b) (ho : o.c = .bytes ob)
    (h : overBy op ⟨n, .grp d o co, x⟩ = some ⟨.long, S⟩) :
    S.val.toList = (List.range g).map fun j => Spec.over op.step (op.denseSeed Ew.i64 Spec.nul)
      (((List.range n).filter fun i => decide ((o.toList[j]!).toNatClampNeg ≤ i ∧ i < (o.toList[j+1]!).toNatClampNeg)).map
        fun i => x.toList[i]!) := by
  have hn : b.size / 8 = n := by have := x.wf.2; rw [hc] at this; exact this
  have hob : ob.size / 8 = g + 1 := by have := o.wf.2; rw [ho] at this; exact this
  have hgu : g.toUSize.toNat = g := USize.toNat_ofNat_of_lt hg
  have hcnt : (Groups.segs ob).count.toNat = g := by simp only [Groups.count, hob, Nat.add_sub_cancel]; exact hgu
  have hm : overGroupsColumn op .long (.segs ob) x.c = some (overSegments op Ew.i64 Spec.nul ob b) := by
    simp only [overGroupsColumn, hc, clsOf, Coc.denseNul, Coc.nullOf, Column.bytesOf, bind, Option.bind]
  have hof : offs o = some ob := by simp only [offs, ho, Column.bytesOf]
  simp only [overBy, hof, resultType_long hb, groupedOver_long hb, hm, bind, Option.bind, Option.map] at h
  by_cases hw : (Ty.atom .long).WF g
      (.bytes (groupCells .wrap 8 (Groups.segs ob).count (overSegments op Ew.i64 Spec.nul ob b) (tilLongs g.toUSize)))
  · rw [Arr.of, dif_pos hw] at h
    cases h
    have e : QLean.Verify.denseElems Ew.i64 b = x.toList := denseElems_long (R := ⟨n, .grp d o co, x⟩) hc
    have hx : ∀ i, i < n → x.toList[i]! = QLean.Verify.valAt Ew.i64 b i := fun i hi => by
      rw [← e, QLean.Verify.denseElems, getElem!_pos _ i (by rw [List.length_map, List.length_range]; show i < b.size / 8; omega),
        List.getElem_map, List.getElem_range]; rfl
    obtain ⟨hsz, hel⟩ := QLean.Verify.groupCells_til (Groups.segs ob).count g.toUSize (by rw [hgu]; exact h63)
      (overSegments op Ew.i64 Spec.nul ob b)
    rw [hgu, hcnt] at hel
    rw [hgu] at hsz
    apply List.ext_getElem
    · rw [Arr.length_toList, List.length_map, List.length_range]
    · intro j h1 _
      have hj : j < g := by rwa [Arr.length_toList] at h1
      -- cell `j` of `groupCells` is slot `j` of `overSegments`: `groupCells_til` read at `j`
      have hcell := congrArg (·[j]?) hel
      simp only [QLean.Verify.elemsW, hsz, Nat.mul_div_cancel_left _ (by decide : 0 < 8), List.getElem?_map,
        List.getElem?_range hj, if_pos hj, Option.map_some, Option.some.injEq] at hcell
      -- the segment's rows, its bounds tested first and the null after
      have hf : QLean.Verify.segRowsOf op Ew.i64 Spec.nul ob b j =
          ((List.range n).filter fun i => decide ((atI64 ob j).toNatClampNeg ≤ i ∧ i < (atI64 ob (j + 1)).toNatClampNeg)).filter
            fun i => QLean.Verify.valAt Ew.i64 b i != Spec.nul := by
        rw [QLean.Verify.segRowsOf, List.filter_filter, show Ew.width Ew.i64 = 8 from rfl, hn, hb]
        exact List.filter_congr fun i _ => by simp only [Bool.and_comm, Bool.false_or]
      rw [Arr.getElem_toList, Arr.get_long_bytes _ rfl, List.getElem_map, List.getElem_range,
        hcell, (QLean.Verify.overSegments_slot op Ew.i64 Spec.nul ob b (by omega)).1, offs_get ho (by omega),
        offs_get ho (by omega), hf, QLean.Verify.foldl_filter, Spec.over, List.foldl_map]
      refine QLean.Verify.foldl_congr_mem _ (fun i hi a => ?_) _
      rw [hx i (List.mem_range.1 (List.mem_filter.1 hi).1)]
      by_cases hv : QLean.Verify.valAt Ew.i64 b i = Spec.nul <;> simp [hv]
  · rw [Arr.of, dif_neg hw] at h
    cases h

/-! ### Value laws over a long column that lists `longWords` (`bytes` or `foR`; not `alp`) -/

/-- A long column's elements, element `i` its word `i` read as a long. -/
theorem toList_words {m : Nat} (x : Arr (.atom .long) m) {B : ByteArray} {ws : List UInt64}
    (hx : longWords x.c = some ws) (hB : Verify.elemsW 8 B = ws) (hs : B.size / 8 = m) :
    x.toList = (List.range m).map fun i => (Column.bitsAt B (i * 8) 8).toInt64 := by
  rw [Arr.toList_long x hx, ← hB, Verify.elemsW, hs, List.map_map]; rfl

/-- **`<x` / `>x` over a long column**: q's stable grade, from `Order.grade`'s merge sort of `til n`
    (`ids_indices`) under `rank_i64_le_iff`. -/
theorem grade_toList {desc : Bool} {R : Rel k (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Rel (.atom .long) (.atom .long)} (h : grade desc R = some S) :
    S.val.toList = Spec.grade desc R.val.toList := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  have hg : gradeColumn .long desc R.val.c = some (.vector .long (.bytes (Order.grade .i64 desc R.n.toUSize B))) := by
    rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc]
    · rw [← hBs]; rfl
    · rfl
  simp only [grade, hg, vecCol, bind, Option.bind] at h
  generalize hP : Order.grade .i64 desc R.n.toUSize B = P at h
  by_cases hw : (Ty.atom .long).WF R.n (.bytes P)
  · rw [Arr.of, dif_pos hw] at h
    have hS : S.val.c = .bytes P := by cases h; rfl
    have hm : min R.n.toUSize.toNat (Scan.Kind.i64.avail B) = R.n := by
      rw [USize.toNat_ofNat_of_lt' hn, show Scan.Kind.i64.avail B = B.size / 8 from rfl, hBs, Nat.min_self]
    have hids : Verify.ids P = (List.range R.n).mergeSort fun i j =>
        if desc then Order.keyAt .i64 B j ≤ Order.keyAt .i64 B i else Order.keyAt .i64 B i ≤ Order.keyAt .i64 B j := by
      rw [← hP, Order.grade, hm]
      exact Verify.ids_indices _ fun i hi =>
        Nat.lt_of_lt_of_le (Nat.lt_trans (List.mem_range.1 ((List.mergeSort_perm _ _).mem_iff.1 hi)) hn)
          (by rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e])
    have e1 : S.val.toList = (Verify.ids P).map Int64.ofNat := by
      rw [Arr.toList_long_bytes _ hS, Verify.ids, Arr.n_long_bytes _ hS, List.map_map, List.map_map]
      exact List.map_congr_left fun i _ => toInt64_of_toNat rfl
    have hxs := toList_words R.val hx hBw hBs
    rw [e1, hids, Spec.grade, Arr.length_toList]
    congr 1
    have := List.map_mergeSort (f := id) (l := List.range R.n) (r := fun i j =>
        if desc then Order.keyAt .i64 B j ≤ Order.keyAt .i64 B i else Order.keyAt .i64 B i ≤ Order.keyAt .i64 B j)
      (s := fun i j => if desc then decide (R.val.toList[j]! ≤ R.val.toList[i]!)
        else decide (R.val.toList[i]! ≤ R.val.toList[j]!)) fun i hi j hj => by
      have hi' := List.mem_range.1 hi
      have hj' := List.mem_range.1 hj
      simp only [id, hxs]
      cases desc <;> simp [Order.keyAt, Scan.Kind.bitsAt, Scan.Kind.width, rank_i64_le_iff, List.getElem?_range hi',
        List.getElem?_range hj']
    simpa using this
  · rw [Arr.of, dif_neg hw] at h
    cases h

/-- **`asc x` / `desc x` over a long column**: q's stable sort, from `sortValues_spec` under
    `rank_i64_le_iff`. -/
theorem sort_toList {desc : Bool} {R : Rel k (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Rel (.atom .long) (.atom .long)} (h : sort desc R = some S) :
    S.val.toList = Spec.sort desc R.val.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  have hsv : sortedValues .long desc R.val.c =
      some (.vector .long (.bytes (Order.sortValues .i64 desc (B.size / 8).toUSize B))) := by
    simp only [sortedValues, hb]; rfl
  simp only [sort, hsv, Option.orElse, vecCol, bind, Option.bind] at h
  generalize hP : Order.sortValues .i64 desc (B.size / 8).toUSize B = P at h
  by_cases hw : (Ty.atom .long).WF R.n (.bytes P)
  · rw [Arr.of, dif_pos hw] at h
    have hS : S.val.c = .bytes P := by cases h; rfl
    have hs := Verify.sortValues_spec .i64 desc (B.size / 8).toUSize B
    rw [hP, USize.toNat_ofNat_of_lt' (by rw [hBs]; exact hn), show Scan.Kind.i64.avail B = B.size / 8 from rfl,
      Nat.min_self, show (List.range (B.size / 8)).map (Scan.Kind.i64.bitsAt B) = Verify.elemsW 8 B from rfl, hBw,
      show Scan.Kind.i64.width = 8 from rfl] at hs
    rw [Arr.toList_long _ (show longWords S.val.c = some (Verify.elemsW 8 P) by rw [hS]; rfl), hs,
      Arr.toList_long R.val hx, Spec.sort]
    exact List.map_mergeSort fun a _ b _ => by cases desc <;> simp [rank_i64_le_iff]
  · rw [Arr.of, dif_neg hw] at h
    cases h

/-- Two first-of-the-smallest of one list under `f` are one element. -/
theorem first_min_unique (f : UInt64 → Int) (L : List UInt64) {p q : Nat} {r s : UInt64}
    (hp : L[p]? = some r) (hq : L[q]? = some s) (hr : ∀ x ∈ L, f r ≤ f x) (hs : ∀ x ∈ L, f s ≤ f x)
    (hr' : ∀ (j : Nat) x, j < p → L[j]? = some x → f r < f x)
    (hs' : ∀ (j : Nat) x, j < q → L[j]? = some x → f s < f x) : r = s := by
  have h1 := hr s (List.mem_of_getElem? hq)
  have h2 := hs r (List.mem_of_getElem? hp)
  rcases Nat.lt_trichotomy p q with h | rfl | h
  · have := hs' p r h hp; omega
  · rw [hp] at hq; exact Option.some.inj hq
  · have := hr' q s h hq; omega

/-- `Spec.mext` over the words `rd` reads is `mwinExt` read back, at any order `f` the kernel's strict
    preference is and `sp` agrees with on the longs: `mwinExt_spec` and `foldl_keep_first` name the same
    first-of-the-smallest in each window. -/
theorem mext_words (f : UInt64 → Int) (sp : Int64 → Int64 → Bool)
    (hsp : ∀ a b : UInt64, sp a.toInt64 b.toInt64 = decide (f a < f b)) (seed : UInt64) (rd : Nat → UInt64)
    (w m : Nat) (hw : 0 < w) :
    Spec.mext sp seed.toInt64 w ((List.range m).map fun j => (rd j).toInt64) =
      (List.range m).map fun i =>
        (Column.bitsAt (Scan.mwinExt (fun u e => decide (f u < f e)) seed rd w m 8) (i * 8) 8).toInt64 := by
  unfold Spec.mext
  rw [List.length_map, List.length_range]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  obtain ⟨p, r, hp, hbits, hmin, hfirst⟩ := Verify.mwinExt_spec f seed rd w m 8 hw (Nat.le_refl 8) i hi
  rw [hbits, Nat.mod_eq_of_lt (by simpa using r.toNat_lt), UInt64.ofNat_toNat]
  have htd : (((List.range m).map fun j => (rd j).toInt64).take (i + 1)).drop (i + 1 - w) =
      (List.range' (i + 1 - w) (min w (i + 1))).map fun j => (rd j).toInt64 :=
    List.ext_getElem (by simp; omega) fun j h1 h2 => by simp [List.getElem_range']; try omega
  have hW : (if i + 1 < w then seed.toInt64 :: (List.range' (i + 1 - w) (min w (i + 1))).map (fun j => (rd j).toInt64)
      else (List.range' (i + 1 - w) (min w (i + 1))).map fun j => (rd j).toInt64) =
      (Verify.mwinWindow seed rd w i).map UInt64.toInt64 := by
    unfold Verify.mwinWindow; split <;> simp
  dsimp only
  rw [htd, hW]
  generalize hU : Verify.mwinWindow seed rd w i = U at hp hmin hfirst
  cases U with
  | nil => simp at hp
  | cons u0 us =>
    simp only [List.map_cons, List.foldl_map]
    obtain ⟨p', hp', hmin', hfirst'⟩ := Verify.foldl_keep_first f us u0
    rw [List.foldl_hom (f := UInt64.toInt64) (g₁ := fun e u => if decide (f u < f e) then u else e) fun x y => by
      dsimp only; rw [hsp]; split <;> rfl]
    exact congrArg _ (first_min_unique f _ hp' hp hmin' hmin hfirst' hfirst)

/-- `w mmin x` / `w mmax x` over a long column, at the order `f` the kernel's `better` is strictness of,
    `sp` its reading on longs and `seed` the each-prior seed read as a long. -/
theorem mext_toList {op : Scan.MOp} (hop : op = .mmin ∨ op = .mmax) (f : UInt64 → Int) (sp : Int64 → Int64 → Bool)
    (seed : Int64) (hk : op.better .i64 = fun u e => decide (f u < f e))
    (hsp : ∀ a b : UInt64, sp a.toInt64 b.toInt64 = decide (f a < f b)) (hs : (op.seed .i64).toInt64 = seed)
    {w : Nat} (hw : w < USize.size) {R : Rel k (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Rel k (.atom .long)} (h : mwin op w .long R = some S) :
    S.val.toList = Spec.mext sp seed w R.val.toList := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  have hd : ∀ v, v < USize.size → mwinColumn op .long v R.n R.val.c =
      if v < 1 then none else some (.long, Column.answer .long (.bytes (Scan.mwinBits op .i64 v R.n B))) := by
    intro v hv
    have hn' : R.n % 2 ^ System.Platform.numBits = R.n := Nat.mod_eq_of_lt hn
    have hv' : v % 2 ^ System.Platform.numBits = v := Nat.mod_eq_of_lt hv
    rcases hop with rfl | rfl <;> rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc] <;>
      by_cases h1 : v < 1 <;>
      simp [mwinColumn, h1, show mwinType .mmin .long = some .long from rfl,
        show mwinType .mmax .long = some .long from rfl, show scanKind .long = some .i64 from rfl,
        show Scan.MOp.readKind .mmin .i64 = .i64 from rfl, show Scan.MOp.readKind .mmax .i64 = .i64 from rfl,
        show QAtomicType.width .long = some 8 from rfl, show Scan.MOp.width .mmin .i64 = 8 from rfl,
        show Scan.MOp.width .mmax .i64 = 8 from rfl, show Scan.Kind.width .i64 = 8 from rfl, Column.bytesOf,
        Scan.mwinFoR, Scan.mwin, hBs, hn', hv', USize.toNat_ofNat_of_lt' hv, USize.toNat_ofNat_of_lt' hn] <;> rfl
  have hw1 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h0
    · simp [mwin, hd 0 (by rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e])] at h
    · exact h0
  have hE : Scan.mwinBits op .i64 w R.n B =
      Scan.mwinExt (fun u e => decide (f u < f e)) (op.seed .i64) (fun j => Column.bitsAt B (j * 8) 8) w R.n 8 := by
    have e : Scan.mwinBits op .i64 w R.n B = Scan.mwinExt (op.better .i64) (op.seed .i64) (Scan.Kind.i64.bitsAt B) w
        (min R.n (Scan.Kind.i64.avail B)) 8 := by rcases hop with rfl | rfl <;> rfl
    rw [e, hk, show Scan.Kind.i64.avail B = R.n from hBs, Nat.min_self]; rfl
  simp only [mwin, hd w hw, show ¬ w < 1 by omega, if_false, Option.bind, if_true, Option.map] at h
  generalize hA : Column.answer .long (.bytes (Scan.mwinBits op .i64 w R.n B)) = A at h
  by_cases hwf : (Ty.atom .long).WF R.n A
  · rw [Arr.of, dif_pos hwf] at h
    have hS : S.val.c = A := by cases h; rfl
    have hSn : S.n = R.n := by cases h; rfl
    have hL : longWords S.val.c = some (Verify.elemsW 8 (Scan.mwinBits op .i64 w R.n B)) := by
      rw [hS, ← hA]; exact longWords_answer _
    have hlen : (Scan.mwinBits op .i64 w R.n B).size / 8 = R.n := by
      have := congrArg List.length (Arr.toList_long S.val hL)
      rw [Arr.length_toList, hSn] at this; simpa [Verify.elemsW] using this.symm
    rw [Arr.toList_long S.val hL, Verify.elemsW, hlen, List.map_map, toList_words R.val hx hBw hBs, ← hs, hE,
      mext_words f sp hsp _ _ w R.n hw1]
    rfl
  · rw [Arr.of, dif_neg hwf] at h
    cases h

/-- **`w mmin x` over a long column**: q's `(w-1)&':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `0W`. -/
theorem mmin_toList {w : Nat} (hw : w < USize.size) {R : Rel k (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Rel k (.atom .long)}
    (h : mwin .mmin w .long R = some S) : S.val.toList = Spec.mext (· < ·) Int64.maxValue w R.val.toList :=
  mext_toList (.inl rfl) (fun u => u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt])
    (fun a b => by simp [Int64.lt_iff_toInt_lt]) rfl hw hx hn h

/-- **`w mmax x` over a long column**: q's `(w-1)|':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `-0W`. -/
theorem mmax_toList {w : Nat} (hw : w < USize.size) {R : Rel k (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Rel k (.atom .long)}
    (h : mwin .mmax w .long R = some S) : S.val.toList = Spec.mext (· > ·) (-Int64.maxValue) w R.val.toList :=
  mext_toList (.inr rfl) (fun u => -u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt,
      show (Scan.MOp.mmax == Scan.MOp.mmin) = false from rfl] <;> omega)
    (fun a b => by simp [Int64.lt_iff_toInt_lt] <;> omega) rfl hw hx hn h

end Ops

/-! ## Checks on small literal Rels -/

section Checks

open QLean.Column Ops

private def L {n : Nat} (a : Arr (.atom .long) n) : Rel (.atom .long) (.atom .long) := ⟨n, .til n, a⟩
private def vals {k v : Ty} (R : Option (Rel k v)) : List (El v) := (R.map fun R => R.val.toList).getD []
/-- An answer whose type comes with it, kept where that type is `rt`. -/
private def at? {k : Ty} (rt : QAtomicType) : Option ((r : QAtomicType) × Rel k (.atom r)) → Option (Rel k (.atom rt))
  | some ⟨r, S⟩ => if h : r = rt then some (h ▸ S) else none
  | none => none

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
#guard vals (mwin .mmin 3 .long (L xsA)) == Spec.mext (· < ·) Int64.maxValue 3 xs
#guard vals (mwin .mmax 3 .long (L xsA)) == Spec.mext (· > ·) (-Int64.maxValue) 3 xs
#guard vals (mwin .mmin 3 .long (L xnA)) == Spec.mext (· < ·) Int64.maxValue 3 xn
#guard vals (mwin .mmax 3 .long (L xnA)) == Spec.mext (· > ·) (-Int64.maxValue) 3 xn
-- q 4.1: `3 mmax 0N 0N 0N 1` is `-0W -0W 0N 1`, the seed `-0W` in each of the first two windows
private def nnA : Arr (.atom .long) 4 := { c := .bytes <| packLongs [Int64.minValue, Int64.minValue, Int64.minValue, 1], wf := by decide }
#guard vals (mwin .mmax 3 .long (L nnA)) == [-Int64.maxValue, -Int64.maxValue, Int64.minValue, 1]
-- the encoded form goes through `mwinFoR` and answers what the dense one does
private def xsF : Arr (.atom .long) 8 :=
  { c := .foR 8 (Kernel.Coc.encode 8 (packLongs xs)).1 (Kernel.Coc.encode 8 (packLongs xs)).2, wf := ⟨rfl, rfl⟩ }
#guard vals (mwin .mmin 3 .long (L xsF)) == Spec.mext (· < ·) Int64.maxValue 3 xs
#guard vals (mwin .msum 3 .long (L xsF)) == Spec.msum 3 xs
-- a boolean window is `mwinBitmap`'s bitmap: q's `2 mmax 010b` is `011b`, `2 mmin 101b` is `100b`
private def LB {n : Nat} (a : Arr (.atom .boolean) n) : Rel (.atom .long) (.atom .boolean) := ⟨n, .til n, a⟩
private def b010 : Arr (.atom .boolean) 3 := { c := .bits 3 (ByteArray.mk #[0b010]), wf := by decide }
private def b101 : Arr (.atom .boolean) 3 := { c := .bits 3 (ByteArray.mk #[0b101]), wf := by decide }
#guard vals (mwin .mmax 2 .boolean (LB b010)) == [false, true, true]
#guard vals (mwin .mmin 2 .boolean (LB b101)) == [true, false, false]
#guard vals (mwin .mcount 2 .int (LB b101)) == [1, 2, 2]
#guard (mwin .msum 3 .int (L xsA)).isNone

#guard vals (iasc (L xsA)) == Spec.grade false xs
#guard vals (idesc (L zsA)) == [1, 2, 3, 0] ∧ vals (idesc (L zsA)) == Spec.grade true zsA.toList
#guard vals (rank (L xsA)) == Spec.rank xs
#guard vals (asc (L xsA)) == Spec.sort false xs
#guard ((asc (L xsA)).map (·.val.attr)) == some 1
#guard vals (desc (L xsA)) == Spec.sort true xs
#guard ((xasc sA xsA).map Arr.toList) == some ((Spec.grade false sA.toList).map fun i => xs[i.toNatClampNeg]!)

-- the parted list `(10 20; 30; 40 50 60)` and the groups `[0,1) [1,1) [1,3)` with an empty middle one
private def og : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 2, 3, 6], wf := by decide }
private def gv : List Int64 := [10, 20, 30, 40, 50, Int64.minValue]
private def G : Rel (.atom .long) (.atom .long) :=
  ⟨6, .grp (.til 3) og (by decide), { c := .bytes <| packLongs [10, 20, 30, 40, 50, Int64.minValue], wf := by decide }⟩
private def oe : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 1, 1, 3], wf := by decide }
private def E : Rel (.atom .long) (.atom .long) :=
  ⟨3, .grp (.til 3) oe (by decide), { c := .bytes <| packLongs [7, 8, 9], wf := by decide }⟩

-- the same groups over an `int` column: `groupedOver` answers `sum` at `int`, the null skipped
private def GI : Rel (.atom .long) (.atom .int) :=
  ⟨6, .grp (.til 3) og (by decide),
    { c := .bytes <| [10, 20, 30, 40, 50, Int32.minValue].foldl (fun b (x : Int32) => Column.pushBits b x.toUInt32.toUInt64 4) .empty,
      wf := by decide }⟩
#guard vals (at? .int (overBy .add GI)) == [30, 30, 90]
#guard vals (at? .int (overBy .greater GI)) == [20, 30, 50]
#guard vals (countBy G) == ((Spec.groups [0, 2, 3, 6] gv).map fun g => Int64.ofNat g.length)
#guard vals (countBy E) == [1, 0, 2]
#guard ((countBy G).map (·.key.toList)) == some [0, 1, 2]
#guard vals (lastBy G) == ((Spec.groups [0, 2, 3, 6] gv).map fun g => g.getLastD 0)
#guard (lastBy E).isNone
#guard vals (at? .long (overBy .add G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over (· + ·) 0))
#guard vals (at? .long (overBy .greater G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over max (Int64.minValue + 1)))
#guard vals (at? .long (overBy .add E)) == [7, 0, 17]

end Checks

#print axioms Ops.scan_keys
#print axioms Ops.mwin_keys
#print axioms Ops.rank_keys
#print axioms Spec.scan_getLast?
#print axioms Ops.over_bytes
#print axioms Ops.overBy_bytes
#print axioms Ops.grade_toList
#print axioms Ops.sort_toList
#print axioms Ops.mext_words
#print axioms Ops.mmin_toList
#print axioms Ops.mmax_toList
#print axioms longWords_answer
#print axioms Arr.dense_long

end LeetQ.Rel
