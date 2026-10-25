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
import QLean.Verify.Dyad

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

/-- `R` with its values replaced, key kept. -/
def Vec.withVal {v w : QVecType} (R : Vec v) (a : Arr w R.n) : Vec w := ⟨R.n, a⟩

namespace Ops

variable {k : QVecType} {t : QAtomicType}

/-! ## Scans: `f\x`, key kept -/

/-- `f\x` at the q dyad `f` (`+ * & | ^`), answered at `rt` (q's accumulator type). -/
def scan (f : Prim.Dyadic) (rt : QAtomicType) (R : Vec (.atom t)) : Option (Vec (.atom rt)) :=
  ((scanColumn f rt t R.val.c).bind fun c => (Arr.of (.atom rt) R.n c "f\\x").toOption).map R.withVal

/-! ## Folds: `f/x` -/

/-- `f/x` over the values in position order, as q's answer widened to `Int64`. -/
def over (op : Coc.Over) (R : Vec (.atom t)) : Option Int64 := overColumn op t R.val.c

/-- `avg x`: the bits of the `float` q answers. -/
def avg (R : Vec (.atom t)) : Option UInt64 :=
  (avgColumn t R.val.c).bind (Carrier.of? .float)

/-! ## Grouped folds over a parted list: one answer per group

A `Parted`'s groups are the segments of `o`, so every op here reads `o` and writes no group id per
row: `o bin til n` would be an `n`-row pass to recover what `o` already says. A grouped dict (keys,
then one boxed vector per key) reaches them through `byKey`, which unboxes once (`Parted.ofBoxes`). -/

/-- `o`'s dense payload, the `g+1` offsets the segment kernels read. -/
def offs {g : Nat} (o : Arr (.atom .long) (g+1)) : Option ByteArray := Column.bytesOf .long o.c

/-- `1_o` over `g+1` offsets: each group's end. -/
def ends (g : Nat) (ob : ByteArray) : ByteArray := ob.extract 8 (8 * (g+1))

/-- `1_deltas o`, each group's size `o[r+1] − o[r]`: one `Ew.val` pass over the offsets, which hold
    no null, so `0N` as the null changes nothing. -/
def sizes (g : Nat) (ob : ByteArray) : ByteArray :=
  Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (ends g ob) (ob.extract 0 (8 * g)) g.toUSize

/-- `count each` by group: `1_deltas o`. -/
def countBy {v : QVecType} (P : Parted v) : Option (Arr (.atom .long) P.g) := do
  (Arr.of (.atom .long) P.g (.bytes (sizes P.g (← offs P.o))) "count each").toOption

/-- `last each` by group: `x[-1+1_o]`. `none` when a group is empty, which has no last row. -/
def lastBy (P : Parted (.atom t)) : Option (Arr (.atom t) P.g) := do
  let g := P.g
  let ob ← offs P.o
  let least ← overColumn .lesser .long (.bytes (sizes g ob))
  if 0 < g ∧ least ≤ 0 then none else
    let lasts := Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (ends g ob) (atomBytes Ew.i64 (-1 : Int64).toUInt64) g.toUSize
    (Arr.of (.atom t) g (← vecCol (← gatherColumn t P.val.c (.bytes lasts))) "last each").toOption

/-- `select f x by k`: `f/` over each segment's rows at every type q's grouped fold has an engine for
    (`groupedOver`: integral and float, not boolean), answered at `Coc.Over.resultType`'s type, q's
    type for `f/` of a `t`, which comes with the answer. -/
def overBy (op : Coc.Over) (P : Parted (.atom t)) : Option ((rt : QAtomicType) × Arr (.atom rt) P.g) := do
  let rt ← op.resultType false t
  let s ← groupedOver op false false t (.segs (← offs P.o)) P.val.c (tilLongs P.g.toUSize)
  pure ⟨rt, ← (Arr.of (.atom rt) P.g (.bytes s) "f/ by").toOption⟩

/-- A per-group answer of a grouped dict `R` (one boxed `v` vector per key): unbox once, run `f`, key the
    answer by `R.key`. The group count is re-read by `Arr.of`, one O(1) check. -/
def byKey {v w : QVecType} (R : Rel k .general) (f : (P : Parted v) → Option (Arr w P.g)) : Option (Rel k w) := do
  let P ← (Parted.ofBoxes v R.val).toOption
  pure ⟨R.n, R.key, ← (Arr.of w R.n (← f P).c "byKey").toOption⟩

/-! ## Moving windows: `w mop x`, key kept -/

/-- `w msum/mcount/mavg/mdev/mmin/mmax x`, answered at `rt`; `none` where q answers another type. -/
def mwin (op : Scan.MOp) (w : Nat) (rt : QAtomicType) (R : Vec (.atom t)) : Option (Vec (.atom rt)) :=
  ((mwinColumn op t w R.n R.val.c).bind fun (rt', c) =>
    if rt' = rt then (Arr.of (.atom rt) R.n c "w mop x").toOption else none).map R.withVal

/-! ## Order: `iasc idesc rank asc desc xasc` -/

/-- `<x` / `>x`: the stable grade, keyed by position. -/
def grade (desc : Bool) (R : Vec (.atom t)) : Option (Vec (.atom .long)) := do
  let p ← vecCol (← gradeColumn t desc R.val.c)
  pure ⟨R.n, ← (Arr.of (.atom .long) R.n p "<x").toOption⟩

def iasc := @grade t false
def idesc := @grade t true

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order. -/
def rank (R : Vec (.atom t)) : Option (Vec (.atom .long)) :=
  (((gradeColumn t false R.val.c (rank := true)).bind vecCol).bind fun c => (Arr.of (.atom .long) R.n c "rank x").toOption).map R.withVal

/-- `x` reordered by the permutation column `p`: one gather. -/
def permute {n : Nat} (p : Column) (x : Arr (.atom t) n) (attr : UInt8 := 0) : Option (Arr (.atom t) n) := do
  (Arr.of (.atom t) n (← vecCol (← gatherColumn t x.c p)) "x@p" attr).toOption

/-- `asc x` / `desc x` = `(<x);x`, keyed by position. `sortValues` where the key is a bijection of
    the bits, the bitmap sort at `boolean`, the grade and a gather elsewhere. `asc` sets `s`. -/
def sort (desc : Bool) (R : Vec (.atom t)) : Option (Vec (.atom t)) := do
  let attr : UInt8 := if desc then 0 else 1
  let a ← match (sortedValues t desc R.val.c).orElse fun _ => sortedBitsColumn t desc R.val.c with
    | some v => (Arr.of (.atom t) R.n (← vecCol v) "asc x" attr).toOption
    | none => permute (← vecCol (← gradeColumn t desc R.val.c)) R.val attr
  pure ⟨R.n, a⟩

def asc := @sort t false
def desc := @sort t true

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

/-- `w msum x` as q runs it, `q.k`'s `{y-(-x)_(0i*x#y),y:+\y}`: the total of the last `w` elements up to
    each position, a null counting `0`, and `0N` where the running total `+\` at either end of the window
    is `0N` (q's `-` carries the null). Every total wraps at `Int64`, as q's `long` `+` does. -/
def msum (w : Nat) (xs : List Int64) : List Int64 :=
  let v := xs.map fun x => if x == nul then 0 else x
  let tot (j : Nat) : Int64 := (v.take j).foldl (· + ·) 0
  (List.range xs.length).map fun i =>
    if tot (i+1) == nul || tot (i+1-w) == nul then nul else ((v.take (i+1)).drop (i+1-w)).foldl (· + ·) 0

/-- `w mcount x`, `q.k`'s `msum[x;~^y]`: how many of the last `w` elements up to each position are not
    `0N`, as q's `int`. -/
def mcount (w : Nat) (xs : List Int64) : List Int32 :=
  (List.range xs.length).map fun i => Int32.ofNat (((xs.take (i+1)).drop (i+1-w)).filter (· != nul)).length

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
def groups {α : Type} (o : List Nat) (xs : List α) : List (List α) :=
  (o.zip o.tail).map fun (a, b) => (xs.drop a).take (b - a)

/-- `count each` of the groups of `o`. -/
def countBy {α : Type} (o : List Nat) (xs : List α) : List Int64 := (groups o xs).map fun g => Int64.ofNat g.length

/-- `last each` of the groups of `o`, `0N` for an empty one. -/
def lastBy (o : List Nat) (xs : List Int64) : List Int64 := (groups o xs).map fun g => g.getLastD nul

/-- Group `j` of `o` is the rows `[o[j], o[j+1])`. -/
theorem groups_range {α : Type} (o : List Nat) (xs : List α) :
    groups o xs = (List.range (o.length - 1)).map fun j => (xs.drop o[j]!).take (o[j+1]! - o[j]!) := by
  apply List.ext_getElem (by simp [groups])
  intro j h1 h2
  simp only [groups, List.getElem_map, List.getElem_zip, List.getElem_tail, List.getElem_range]
  simp at h2
  rw [getElem!_pos o j (by omega), getElem!_pos o (j+1) (by omega)]

/-- `f/` at `min` lies at or below its seed and every element that is not `0N`. -/
theorem over_lesser_le (l : List Int64) (acc : Int64) :
    over (Coc.Over.step .lesser) acc l ≤ acc ∧
      ∀ y ∈ l, y ≠ nul → over (Coc.Over.step .lesser) acc l ≤ y := by
  induction l generalizing acc with
  | nil => exact ⟨Int64.le_refl _, by simp⟩
  | cons x l ih =>
    simp only [over, List.foldl_cons] at ih ⊢
    obtain ⟨h1, h2⟩ := ih (if x == nul then acc else Coc.Over.step .lesser acc x)
    have hs : (if x == nul then acc else Coc.Over.step .lesser acc x) ≤ acc ∧
        (x ≠ nul → (if x == nul then acc else Coc.Over.step .lesser acc x) ≤ x) := by
      by_cases hx : x = nul
      · simp [hx, Int64.le_refl]
      · simp only [hx, beq_iff_eq, if_false, Coc.Over.step, ne_eq, not_false_eq_true, forall_const]
        split <;> simp_all [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt] <;> omega
    refine ⟨Int64.le_trans h1 hs.1, fun y hy hn => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Int64.le_trans h1 (hs.2 hn)
    · exact h2 y hy hn

/-- The last of the rows `[a, b)` of `xs`, `a < b ≤ |xs|`, is row `b − 1`. -/
theorem getLastD_take_drop (xs : List Int64) (d : Int64) {a b : Nat} (h : a < b) (hb : b ≤ xs.length) :
    ((xs.drop a).take (b - a)).getLastD d = xs[b-1]! := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  simp only [List.length_take, List.length_drop, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (by omega), show a + (min (b - a) (xs.length - a) - 1) = b - 1 by omega,
    getElem!_pos xs (b-1) (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

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

variable {k : QVecType} {t : QAtomicType}
/-- The longs `overBytes` folds over a dense long payload are the column's elements. -/
theorem denseElems_long {R : Vec (.atom .long)} {b : ByteArray} (hc : R.val.c = .bytes b) :
    QLean.Verify.denseElems Ew.i64 b = R.val.toList := by
  have hn : R.n = b.size / 8 := by have := R.val.wf.2; rw [hc] at this; simp only [Column.count] at this; exact this.symm
  apply List.ext_getElem
  · rw [QLean.Verify.denseElems, List.length_map, List.length_range, Arr.length_toList, hn]; rfl
  · intro j _ _
    simp only [QLean.Verify.denseElems, List.getElem_map, List.getElem_range]
    rw [Arr.getElem_toList, Arr.get_long_bytes R.val hc]; rfl

/-- `f/x` over a dense long column, at a verb that skips the null (not `all`/`any`): `Spec.over` at the
    kernel's step and seed, from `overBytes_eq`. -/
theorem over_bytes {op : Coc.Over} (hb : op.boolCast = false) {R : Vec (.atom .long)} {b : ByteArray}
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
theorem overBy_bytes {op : Coc.Over} (hb : op.boolCast = false) {n g : Nat}
    {o : Arr (.atom .long) (g+1)} {co : Cuts o n} {x : Arr (.atom .long) n} {b ob : ByteArray}
    {S : Arr (.atom .long) g} (hg : g < USize.size) (h63 : g < 2 ^ 63) (hc : x.c = .bytes b) (ho : o.c = .bytes ob)
    (h : overBy op ⟨g, n, o, co, x⟩ = some ⟨.long, S⟩) :
    S.toList = (List.range g).map fun j => Spec.over op.step (op.denseSeed Ew.i64 Spec.nul)
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
  by_cases hw : (Column.admits (.atom .long) (.bytes (groupCells .wrap 8 (Groups.segs ob).count (overSegments op Ew.i64 Spec.nul ob b) (tilLongs g.toUSize))) = true ∧
      Column.count (.atom .long) (.bytes (groupCells .wrap 8 (Groups.segs ob).count (overSegments op Ew.i64 Spec.nul ob b) (tilLongs g.toUSize))) = g)
  · rw [Arr.of, dif_pos hw] at h
    cases h
    have e : QLean.Verify.denseElems Ew.i64 b = x.toList := denseElems_long (R := ⟨n, x⟩) hc
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

/-- The first `j ≤ m` of `til m` mapped are `til j` mapped. -/
theorem take_range_map {α : Type} (g : Nat → α) {j m : Nat} (h : j ≤ m) :
    ((List.range m).map g).take j = (List.range j).map g :=
  List.ext_getElem (by simp; omega) fun _ _ _ => by simp

/-- The window `[i+1-w, i]` of `til m` mapped, `i < m`. -/
theorem window_range_map {α : Type} (g : Nat → α) (w : Nat) {i m : Nat} (hi : i < m) :
    (((List.range m).map g).take (i + 1)).drop (i + 1 - w) = (List.range' (i + 1 - w) (min w (i + 1))).map g :=
  List.ext_getElem (by simp; omega) fun j h1 h2 => by simp [List.getElem_range']; try omega

/-- A long answer column, dense or encoded, lists its payload's eight-byte words: `longWords_answer`. -/
theorem toList_answer_long {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = Column.answer .long (.bytes b)) :
    x.toList = (List.range m).map fun i => (Column.bitsAt b (i * 8) 8).toInt64 := by
  have hL : longWords x.c = some (Verify.elemsW 8 b) := by rw [hc]; exact longWords_answer _
  have hlen : b.size / 8 = m := by
    have := congrArg List.length (Arr.toList_long x hL)
    rw [Arr.length_toList] at this; simpa [Verify.elemsW] using this.symm
  exact toList_words x hL rfl hlen

/-- A count below `2^32` read back at four bytes is q's `int` of it. -/
theorem int32_count (L : Nat) : (UInt64.ofNat (L % 2 ^ 32)).toUInt32.toInt32 = Int32.ofNat L := by
  have : (UInt64.ofNat (L % 2 ^ 32)).toUInt32 = UInt32.ofNat L := by
    apply UInt32.toNat_inj.1
    rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat', UInt32.toNat_ofNat']
    omega
  rw [this]; rfl

/-- `mwinColumn` over a long column that lists `longWords`, at a verb that reads it as `i64` and writes
    `rt`'s width: `mwinBits` over the dense payload `Arr.dense_long` names, whichever form the column is in. -/
theorem mwin_long {op : Scan.MOp} {rt : QAtomicType} {rk : Scan.Kind} (hT : mwinType op .long = some rt)
    (hk : op.readKind .i64 = .i64) (hr : scanKind rt = some rk) (hwd : op.width .i64 = rk.width)
    {R : Vec (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = R.n ∧ ∀ v, v < USize.size → mwinColumn op .long v R.n R.val.c =
      if v < 1 then none else some (rt, Column.answer rt (.bytes (Scan.mwinBits op .i64 v R.n B))) := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  refine ⟨B, hBw, hBs, fun v hv => ?_⟩
  have hn' : R.n % 2 ^ System.Platform.numBits = R.n := Nat.mod_eq_of_lt hn
  have hv' : v % 2 ^ System.Platform.numBits = v := Nat.mod_eq_of_lt hv
  rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc] <;> by_cases h1 : v < 1 <;>
    simp [mwinColumn, h1, hT, hk, hr, hwd, show scanKind .long = some .i64 from rfl,
      show QAtomicType.width .long = some 8 from rfl, show Scan.Kind.width .i64 = 8 from rfl, Column.bytesOf,
      Scan.mwinFoR, Scan.mwin, hBs, hn', USize.toNat_ofNat_of_lt' hv, USize.toNat_ofNat_of_lt' hn] <;> rfl

/-- An answer of `w mop x` over a long column, at such a verb: `w ≥ 1`, the key's count, and `Column.answer`
    of `mwinBits` over the dense payload. -/
theorem mwin_answer {op : Scan.MOp} {rt : QAtomicType} {rk : Scan.Kind} (hT : mwinType op .long = some rt)
    (hk : op.readKind .i64 = .i64) (hr : scanKind rt = some rk) (hwd : op.width .i64 = rk.width)
    {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Vec (.atom rt)} (h : mwin op w rt R = some S) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = R.n ∧ 0 < w ∧ S.n = R.n ∧
      S.val.c = Column.answer rt (.bytes (Scan.mwinBits op .i64 w R.n B)) := by
  obtain ⟨B, hBw, hBs, hd⟩ := mwin_long hT hk hr hwd hx hn
  have hw1 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h0
    · simp [mwin, hd 0 (by rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e])] at h
    · exact h0
  refine ⟨B, hBw, hBs, hw1, ?_⟩
  simp only [mwin, hd w hw, show ¬ w < 1 by omega, if_false, Option.bind, if_true, Option.map] at h
  generalize Column.answer rt (.bytes (Scan.mwinBits op .i64 w R.n B)) = A at h ⊢
  by_cases hwf : (Column.admits (.atom rt) A = true ∧ Column.count (.atom rt) A = R.n)
  · rw [Arr.of, dif_pos hwf] at h
    cases h
    exact ⟨rfl, rfl⟩
  · rw [Arr.of, dif_neg hwf] at h
    cases h

/-- **`<x` / `>x` over a long column**: q's stable grade, from `Order.grade`'s merge sort of `til n`
    (`ids_indices`) under `rank_i64_le_iff`. -/
theorem grade_toList {desc : Bool} {R : Vec (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Vec (.atom .long)} (h : grade desc R = some S) :
    S.val.toList = Spec.grade desc R.val.toList := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  have hg : gradeColumn .long desc R.val.c = some (.vector (.atom .long) (.bytes (Order.grade .i64 desc R.n.toUSize B))) := by
    rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc]
    · rw [← hBs]; rfl
    · rfl
  simp only [grade, hg, vecCol, bind, Option.bind] at h
  generalize hP : Order.grade .i64 desc R.n.toUSize B = P at h
  by_cases hw : (Column.admits (.atom .long) (.bytes P) = true ∧ Column.count (.atom .long) (.bytes P) = R.n)
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
theorem sort_toList {desc : Bool} {R : Vec (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Vec (.atom .long)} (h : sort desc R = some S) :
    S.val.toList = Spec.sort desc R.val.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long R.val hx hn
  have hsv : sortedValues .long desc R.val.c =
      some (.vector (.atom .long) (.bytes (Order.sortValues .i64 desc (B.size / 8).toUSize B))) := by
    simp only [sortedValues, hb]; rfl
  simp only [sort, hsv, Option.orElse, vecCol, bind, Option.bind] at h
  generalize hP : Order.sortValues .i64 desc (B.size / 8).toUSize B = P at h
  by_cases hw : (Column.admits (.atom .long) (.bytes P) = true ∧ Column.count (.atom .long) (.bytes P) = R.n)
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
      (List.range' (i + 1 - w) (min w (i + 1))).map fun j => (rd j).toInt64 := window_range_map _ w hi
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
    {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64} (hx : longWords R.val.c = some ws)
    (hn : R.n < USize.size) {S : Vec (.atom .long)} (h : mwin op w .long R = some S) :
    S.val.toList = Spec.mext sp seed w R.val.toList := by
  obtain ⟨B, hBw, hBs, hw1, hSn, hS⟩ := mwin_answer (rk := .i64) (by rcases hop with rfl | rfl <;> rfl)
    (by rcases hop with rfl | rfl <;> rfl) rfl (by rcases hop with rfl | rfl <;> rfl) hw hx hn h
  have hE : Scan.mwinBits op .i64 w R.n B =
      Scan.mwinExt (fun u e => decide (f u < f e)) (op.seed .i64) (fun j => Column.bitsAt B (j * 8) 8) w R.n 8 := by
    have e : Scan.mwinBits op .i64 w R.n B = Scan.mwinExt (op.better .i64) (op.seed .i64) (Scan.Kind.i64.bitsAt B) w
        (min R.n (Scan.Kind.i64.avail B)) 8 := by rcases hop with rfl | rfl <;> rfl
    rw [e, hk, show Scan.Kind.i64.avail B = R.n from hBs, Nat.min_self]; rfl
  rw [toList_answer_long S.val hS, hSn, toList_words R.val hx hBw hBs, ← hs, hE, mext_words f sp hsp _ _ w R.n hw1]

/-- **`w mmin x` over a long column**: q's `(w-1)&':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `0W`. -/
theorem mmin_toList {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Vec (.atom .long)}
    (h : mwin .mmin w .long R = some S) : S.val.toList = Spec.mext (· < ·) Int64.maxValue w R.val.toList :=
  mext_toList (.inl rfl) (fun u => u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt])
    (fun a b => by simp [Int64.lt_iff_toInt_lt]) rfl hw hx hn h

/-- **`w mmax x` over a long column**: q's `(w-1)|':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `-0W`. -/
theorem mmax_toList {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Vec (.atom .long)}
    (h : mwin .mmax w .long R = some S) : S.val.toList = Spec.mext (· > ·) (-Int64.maxValue) w R.val.toList :=
  mext_toList (.inr rfl) (fun u => -u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt,
      show (Scan.MOp.mmax == Scan.MOp.mmin) = false from rfl] <;> omega)
    (fun a b => by simp [Int64.lt_iff_toInt_lt] <;> omega) rfl hw hx hn h

/-- **`w msum x` over a long column**: q's `{y-(-x)_(0i*x#y),y:+\y}`, from `msum_i64_spec` over `mwinSum`,
    the integral engine `mwinBits` runs `msum` at `long` on. -/
theorem msum_toList {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Vec (.atom .long)}
    (h : mwin .msum w .long R = some S) : S.val.toList = Spec.msum w R.val.toList := by
  obtain ⟨B, hBw, hBs, -, hSn, hS⟩ := mwin_answer (rk := .i64) rfl rfl rfl rfl hw hx hn h
  have hM : Scan.mwinBits .msum .i64 w R.n B = Scan.mwinSum (some Int64.minValue) (fun s => (Scan.narrow 8 s).toInt64)
      (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else Scan.Kind.i64.signed (Scan.Kind.i64.bitsAt B j))
      w R.n 8 := by
    have e : Scan.mwinBits .msum .i64 w R.n B = Scan.mwinSum (some Int64.minValue) (fun s => (Scan.narrow 8 s).toInt64)
        (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else Scan.Kind.i64.signed (Scan.Kind.i64.bitsAt B j))
        w (min R.n (Scan.Kind.i64.avail B)) 8 := rfl
    rw [e, show Scan.Kind.i64.avail B = R.n from hBs, Nat.min_self]
  have hL : S.val.toList = (Verify.elemsW 8 (Scan.mwinBits .msum .i64 w R.n B)).map UInt64.toInt64 :=
    Arr.toList_long S.val (by rw [hS]; exact longWords_answer _)
  apply List.ext_getElem?
  intro i
  by_cases hi : i < R.n
  · rw [hL, List.getElem?_map, hM, Verify.msum_i64_spec B w R.n i hi, toList_words R.val hx hBw hBs]
    simp only [Spec.msum, List.length_map, List.length_range, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      List.map_map]
    rw [window_range_map _ w hi]
    simp only [take_range_map _ (show i + 1 ≤ R.n by omega), take_range_map _ (show i + 1 - w ≤ R.n by omega),
      List.foldl_map, Function.comp_def, beq_iff_eq, Bool.or_eq_true, Option.some.injEq]
    split <;> simp [Spec.nul]
  · have hl : (Spec.msum w R.val.toList).length = R.n := by
      simp only [Spec.msum, List.length_map, List.length_range]; exact Arr.length_toList _
    rw [List.getElem?_eq_none (by rw [Arr.length_toList, hSn]; omega), List.getElem?_eq_none (by omega)]

/-- **`w mcount x` over a long column**: how many of each window are not `0N`, at `int`, from `mcount_spec`
    over `mwinSum`. -/
theorem mcount_toList {w : Nat} (hw : w < USize.size) {R : Vec (.atom .long)} {ws : List UInt64}
    (hx : longWords R.val.c = some ws) (hn : R.n < USize.size) {S : Vec (.atom .int)}
    (h : mwin .mcount w .int R = some S) : S.val.toList = Spec.mcount w R.val.toList := by
  obtain ⟨B, hBw, hBs, -, hSn, hS⟩ := mwin_answer (rk := .i32) rfl rfl rfl rfl hw hx hn h
  have hM : Scan.mwinBits .mcount .i64 w R.n B =
      Scan.mwinSum none id (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else 1) w R.n 4 := by
    have e : Scan.mwinBits .mcount .i64 w R.n B = Scan.mwinSum none id
        (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else 1) w (min R.n (Scan.Kind.i64.avail B)) 4 := rfl
    rw [e, show Scan.Kind.i64.avail B = R.n from hBs, Nat.min_self]
  rw [toList_answer_int S.val hS, hSn, hM, toList_words R.val hx hBw hBs, Spec.mcount, List.length_map, List.length_range]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [show i * 4 = 4 * i from Nat.mul_comm _ _, Verify.mcount_spec .i64 B w R.n i hi, window_range_map _ w hi,
    List.filter_map, List.length_map, int32_count]
  congr 2

/-- Two longs `0 ≤ a ≤ b`: `b − a` is the difference of their naturals, no wrap. -/
theorem sub_ofNat {a b : Int64} (h0 : 0 ≤ a.toInt) (h1 : a.toInt ≤ b.toInt) :
    b - a = Int64.ofNat (b.toNatClampNeg - a.toNatClampNeg) := by
  apply Int64.toInt_inj.1
  have := Int64.toInt_lt b
  have ea : (a.toNatClampNeg : Int) = a.toInt := by rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg h0
  have eb : (b.toNatClampNeg : Int) = b.toInt := by rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg (by omega)
  rw [Int64.toInt_sub, Int.bmod_eq_of_le_mul_two (by omega) (by omega),
    Int64.toInt_ofNat_of_lt (by omega)]
  omega

/-- A long at or above `0` is not `0N`. -/
theorem ne_nul {a : Int64} (h : 0 ≤ a.toInt) : (a == Spec.nul) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro e; rw [e] at h; exact absurd h (by decide)

/-- A long at or above `0` is its natural, cast back. -/
theorem toNat_cast {a : Int64} (h : 0 ≤ a.toInt) : (a.toNatClampNeg : Int) = a.toInt := by
  rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg h

/-- Offset `m` of `o` read as a natural, through the `map` the specs take the offsets by. -/
theorem map_get! {g : Nat} (o : Arr (.atom .long) (g+1)) {m : Nat} (hm : m ≤ g) :
    (o.toList.map Int64.toNatClampNeg)[m]! = (o.toList[m]!).toNatClampNeg := by
  rw [getElem!_pos _ m (by rw [List.length_map, Arr.length_toList]; omega),
    getElem!_pos o.toList m (by rw [Arr.length_toList]; omega), List.getElem_map]

/-- Word `m` of the dense offsets `B` is offset `m`. -/
theorem offs_word {g : Nat} {o : Arr (.atom .long) (g+1)} {B : ByteArray}
    (hB : o.toList = (List.range (g+1)).map fun i => (Column.bitsAt B (i*8) 8).toInt64) {m : Nat} (hm : m < g + 1) :
    (Column.bitsAt B (m*8) 8).toInt64 = o.toList[m]! := by
  rw [hB, getElem!_pos _ m (by simpa using hm)]; simp

/-- Under `Cuts`, `sizes` lists each group's size `o[j+1] − o[j]`: no offset is `0N`, so `Ew.sub`'s null
    test never fires, and both lie in `[0, n]`, so the difference does not wrap. -/
theorem sizes_words {g n : Nat} {o : Arr (.atom .long) (g+1)} (co : Cuts o n) {B : ByteArray}
    (hB : o.toList = (List.range (g+1)).map fun i => (Column.bitsAt B (i*8) 8).toInt64) (hg : g < USize.size) :
    Verify.elemsW 8 (sizes g B) = (List.range g).map fun j =>
      (Int64.ofNat ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)).toUInt64 := by
  rw [sizes, Verify.val_i64_vv _ _ _ _ _ hg]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  rw [ends, Verify.bitsAt_extract _ (by omega), Verify.bitsAt_extract _ (by omega),
    show 8 + j * 8 = (j+1) * 8 by omega, Nat.zero_add, offs_word hB (by omega), offs_word hB (by omega)]
  obtain ⟨a0, a1, -⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
  have e0 := ne_nul a0
  have e1 := ne_nul (Int.le_trans a0 a1)
  rw [← sub_ofNat a0 a1]
  simp only [Ew.intStep, e0, e1, Bool.or_false, show (Ew.sub == Ew.add) = false by decide,
    show (Ew.sub == Ew.sub) = true by decide, if_true, Bool.false_eq_true, if_false]

/-- **`count each` by group**: `1_deltas o`, each group's size, at any value type and any offsets that list
    `longWords`. `Cuts` keeps every offset in `[0, n]`, so no `0N` reaches `Ew.sub` and no difference wraps. -/
theorem countBy_toList {v : QVecType} {n g : Nat} {o : Arr (.atom .long) (g+1)} {co : Cuts o n}
    {x : Arr v n} {wo : List UInt64} (ho : longWords o.c = some wo) (hg : g + 1 < USize.size)
    {S : Arr (.atom .long) g} (h : countBy ⟨g, n, o, co, x⟩ = some S) :
    S.toList = Spec.countBy (o.toList.map Int64.toNatClampNeg) x.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long o ho hg
  have hof : offs o = some B := hb
  simp only [countBy, hof, bind, Option.bind] at h
  by_cases hw : (Column.admits (.atom .long) (.bytes (sizes g B)) = true ∧ Column.count (.atom .long) (.bytes (sizes g B)) = g)
  · rw [Arr.of, dif_pos hw] at h
    have hS : S.c = .bytes (sizes g B) := by cases h; rfl
    rw [Arr.toList_long S (show longWords S.c = some (Verify.elemsW 8 (sizes g B)) by rw [hS]; rfl),
      sizes_words co (toList_words o ho hBw hBs) (by omega), Spec.countBy, Spec.groups_range,
      List.length_map, Arr.length_toList, Nat.add_sub_cancel, List.map_map, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.1 hj
    obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
    have c0 := toNat_cast a0
    have c1 := toNat_cast (Int.le_trans a0 a1)
    simp only [Function.comp_apply, map_get! o (show j ≤ g by omega), map_get! o (show j + 1 ≤ g by omega),
      List.length_take, List.length_drop, Arr.length_toList, Int64.toInt64_toUInt64]
    congr 1
    omega
  · rw [Arr.of, dif_neg hw] at h
    cases h

/-- **`last each` by group over a long column**: the last row of each group. An answer means no group
    is empty — `lastBy` reads that off `min` of the sizes, here `over_bytes` and `over_lesser_le` — so
    `o[j+1] − 1` names a row of group `j`. A `foR` value column reaches `gatherFoR`, which is `gatherBytes`
    over the decode `Arr.dense_long` names. -/
theorem lastBy_toList {n g : Nat} {o : Arr (.atom .long) (g+1)} {co : Cuts o n}
    {x : Arr (.atom .long) n} {wo wx : List UInt64} (ho : longWords o.c = some wo)
    (hx : longWords x.c = some wx) (hg : g + 1 < USize.size) (hn : n < USize.size) {S : Arr (.atom .long) g}
    (h : lastBy ⟨g, n, o, co, x⟩ = some S) :
    S.toList = Spec.lastBy (o.toList.map Int64.toNatClampNeg) x.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long o ho hg
  have hof : offs o = some B := hb
  have hB := toList_words o ho hBw hBs
  have hsw := sizes_words co hB (by omega)
  have hsz : (sizes g B).size / 8 = g := by simpa [Verify.elemsW] using congrArg List.length hsw
  -- `min` of the sizes, read off `over_bytes` at the sizes as a column
  let Z : Vec (.atom .long) := ⟨g, { c := .bytes (sizes g B), wf := ⟨rfl, hsz⟩ }⟩
  have hZ := over_bytes (op := .lesser) rfl (R := Z) rfl
  have hZl : Z.val.toList = (List.range g).map fun j =>
      Int64.ofNat ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg) := by
    rw [Arr.toList_long Z.val (ws := Verify.elemsW 8 (sizes g B)) rfl, hsw, List.map_map]
    simp [Function.comp_def]
  simp only [lastBy, hof, bind, Option.bind] at h
  rw [show overColumn .lesser .long (.bytes (sizes g B)) = over .lesser Z from rfl, hZ] at h
  simp only at h
  split at h
  · cases h
  rename_i hne
  -- every group holds a row: `min` of the sizes is above `0`
  have hpos : ∀ j, j < g → (o.toList[j]!).toNatClampNeg < (o.toList[j+1]!).toNatClampNeg := by
    intro j hj
    obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
    have c0 := toNat_cast a0
    have c1 := toNat_cast (Int.le_trans a0 a1)
    have hlt := Int64.toInt_lt (o.toList[j+1]!)
    have e : (Int64.ofNat ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)).toInt =
        (((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg : Nat) : Int) :=
      Int64.toInt_ofNat_of_lt (by omega)
    have hm := (Spec.over_lesser_le Z.val.toList (Coc.Over.lesser.denseSeed Ew.i64 Spec.nul)).2 _
      (by rw [hZl]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
      (fun h' => by have := congrArg Int64.toInt h'; rw [e] at this; exact absurd this (by simp))
    have h0 := fun h' => hne ⟨by omega, h'⟩
    rw [Int64.le_iff_toInt_le, e] at hm
    rw [Int64.le_iff_toInt_le] at h0
    simp at h0
    omega
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hlw := Verify.val_i64_va Ew.add Int64.minValue (ends g B) ((-1 : Int64).toUInt64) g (by omega)
  have hlz : (Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (ends g B) (atomBytes Ew.i64 (-1 : Int64).toUInt64)
      g.toUSize).size / 8 = g := by simpa [Verify.elemsW] using congrArg List.length hlw
  generalize Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (ends g B) (atomBytes Ew.i64 (-1 : Int64).toUInt64)
    g.toUSize = L at h hlw hlz
  obtain ⟨b, hxc, -, hbw, hbn⟩ := Arr.dense_long x hx hn
  have hgc : gatherColumn .long x.c (.bytes L) =
      some (.vector (.atom .long) (.bytes (gatherBytes (8 : Nat).toUSize 0x8000000000000000 b L))) := by
    rcases hxc with hxc | ⟨md, pk, hxc, rfl⟩ <;> rw [hxc]
    · rfl
    · cases hm : md.isEmpty <;> simp only [gatherColumn, foRColumn, hm] <;> rfl
  rw [hgc] at h
  simp only [vecCol] at h
  obtain ⟨-, hgj⟩ := Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8) 0x8000000000000000 b L
  rw [h8] at hgj
  generalize gatherBytes (8 : Nat).toUSize 0x8000000000000000 b L = G at h hgj
  by_cases hw : (Column.admits (.atom .long) (.bytes G) = true ∧ Column.count (.atom .long) (.bytes G) = g)
  · rw [Arr.of, dif_pos hw] at h
    have hS : S.c = .bytes G := by cases h; rfl
    rw [Arr.toList_long_bytes S hS, Spec.lastBy, Spec.groups_range, List.length_map, Arr.length_toList,
      Nat.add_sub_cancel, List.map_map, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.1 hj
    obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
    have c0 := toNat_cast a0
    have c1 := toNat_cast (Int.le_trans a0 a1)
    have hp := hpos j hj
    -- index `j` of the gather is `o[j+1] − 1`
    have hidx : Column.bitsAt L (j*8) 8 = (Ew.intStep Ew.add Int64.minValue (o.toList[j+1]!) (-1)).toUInt64 := by
      have := congrArg (·[j]?) hlw
      simp only [Verify.elemsW, hlz, List.getElem?_map, List.getElem?_range hj, Option.map_some,
        Option.some.injEq] at this
      rw [this, ends, Verify.bitsAt_extract _ (by omega), show 8 + j * 8 = (j+1) * 8 by omega,
        offs_word hB (by omega)]
      simp
    have e1 := ne_nul (Int.le_trans a0 a1)
    have hstep : Ew.intStep Ew.add Int64.minValue (o.toList[j+1]!) (-1) =
        Int64.ofNat ((o.toList[j+1]!).toNatClampNeg - 1) := by
      simp only [Ew.intStep, e1, show ((-1 : Int64) == Int64.minValue) = false by decide, Bool.or_false,
        show (Ew.add == Ew.add) = true by decide, if_true, Bool.false_eq_true, if_false]
      rw [← Int64.sub_eq_add_neg, sub_ofNat (a := 1) (by decide) (by rw [show (1 : Int64).toInt = 1 from rfl]; omega)]
      rfl
    have hto : (Int64.ofNat ((o.toList[j+1]!).toNatClampNeg - 1)).toUInt64.toNat =
        (o.toList[j+1]!).toNatClampNeg - 1 := by
      have hlt := Int64.toInt_lt (o.toList[j+1]!)
      rw [Int64.toNat_toUInt64_of_le (by rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega)]; simp),
        Int64.toNatClampNeg_ofNat_of_lt (by omega)]
    rw [Function.comp_apply, Function.comp_apply, hgj j (by omega), hidx, hstep, hto, if_pos (by omega),
      map_get! o (show j ≤ g by omega), map_get! o (show j + 1 ≤ g by omega),
      Spec.getLastD_take_drop _ _ hp (by rw [Arr.length_toList]; omega), toList_words x hx hbw hbn, getElem!_pos _ ((o.toList[j+1]!).toNatClampNeg - 1)
        (by rw [List.length_map, List.length_range]; omega), List.getElem_map, List.getElem_range]
  · rw [Arr.of, dif_neg hw] at h
    cases h

end Ops

/-! ## Checks on small literal Rels -/

section Checks

open QLean.Column Ops

private def L {n : Nat} (a : Arr (.atom .long) n) : Vec (.atom .long) := ⟨n, a⟩
private def vals {v : QVecType} (R : Option (Vec v)) : List (El v) := (R.map fun R => R.val.toList).getD []
private def av {v : QVecType} {n : Nat} (R : Option (Arr v n)) : List (El v) := (R.map Arr.toList).getD []
/-- An answer whose type comes with it, kept where that type is `rt`. -/
private def at? {n : Nat} (rt : QAtomicType) : Option ((r : QAtomicType) × Arr (.atom r) n) → Option (Arr (.atom rt) n)
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
#guard ((scan .add .long (L xsA)).map (·.n)) == some 8

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
-- q 4.1: `3 msum 2 0N 7 1` is `2 2 9 8`, `2 mcount 2 0N 7 1` is `1 1 1 2i`
#guard vals (mwin .msum 3 .long (L xnA)) == Spec.msum 3 xn ∧ Spec.msum 3 xn == [2, 2, 9, 8]
#guard vals (mwin .mcount 2 .int (L xnA)) == Spec.mcount 2 xn ∧ Spec.mcount 2 xn == [1, 1, 1, 2]
#guard vals (mwin .mcount 3 .int (L xsF)) == Spec.mcount 3 xs
-- a boolean window is `mwinBitmap`'s bitmap: q's `2 mmax 010b` is `011b`, `2 mmin 101b` is `100b`
private def LB {n : Nat} (a : Arr (.atom .boolean) n) : Vec (.atom .boolean) := ⟨n, a⟩
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
private def G : Parted (.atom .long) :=
  ⟨3, 6, og, by decide, { c := .bytes <| packLongs [10, 20, 30, 40, 50, Int64.minValue], wf := by decide }⟩
private def oe : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 1, 1, 3], wf := by decide }
private def E : Parted (.atom .long) :=
  ⟨3, 3, oe, by decide, { c := .bytes <| packLongs [7, 8, 9], wf := by decide }⟩

-- the same groups over an `int` column: `groupedOver` answers `sum` at `int`, the null skipped
private def GI : Parted (.atom .int) :=
  ⟨3, 6, og, by decide,
    { c := .bytes <| [10, 20, 30, 40, 50, Int32.minValue].foldl (fun b (x : Int32) => Column.pushBits b x.toUInt32.toUInt64 4) .empty,
      wf := by decide }⟩
#guard av (at? .int (overBy .add GI)) == [30, 30, 90]
#guard av (at? .int (overBy .greater GI)) == [20, 30, 50]
#guard av (countBy G) == Spec.countBy [0, 2, 3, 6] gv
#guard av (countBy E) == [1, 0, 2] ∧ av (countBy E) == Spec.countBy [0, 1, 1, 3] [(7 : Int64), 8, 9]
#guard (do let b ← G.box.toOption; let R : Rel (.atom .long) .general := ⟨3, { c := .bytes (packLongs [5, 6, 7]), wf := by decide }, b⟩; (byKey (v := .atom .long) R countBy).map Rel.toList) == some [(5, 2), (6, 1), (7, 3)]
#guard av (lastBy G) == Spec.lastBy [0, 2, 3, 6] gv
#guard (lastBy E).isNone
#guard av (at? .long (overBy .add G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over (· + ·) 0))
#guard av (at? .long (overBy .greater G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over max (Int64.minValue + 1)))
#guard av (at? .long (overBy .add E)) == [7, 0, 17]

end Checks

#print axioms Spec.scan_getLast?
#print axioms Ops.over_bytes
#print axioms Ops.overBy_bytes
#print axioms Ops.grade_toList
#print axioms Ops.sort_toList
#print axioms Ops.mext_words
#print axioms Ops.mmin_toList
#print axioms Ops.mmax_toList
#print axioms Ops.msum_toList
#print axioms Ops.mcount_toList
#print axioms Ops.lastBy_toList
#print axioms longWords_answer
#print axioms Arr.dense_long

end LeetQ.Rel
