/-
  Scans, folds, moving windows, grouped folds and the order verbs on the RelRep core (§3): each op is
  one qlean kernel dispatch over `val`'s column — `scanColumn` (`Scan.scan`/`scanFoR`/`scanAlp`),
  `overColumn` (`overBytes`/`Coc.over`), `groupedOver` over `Groups.segs` (`overSegments`), `Ew.val`
  over a `grp` key's offsets, `mwinColumn` (`Scan.mwin`/`mwinFoR`/`mwinAlp`/`mwinBitmap`), `gradeColumn` (`grade`/`ranks`) and
  `sortedValues` (`sortValues`). No element is read at run time; a kernel's answer becomes an `Arr`
  only through `Arr.of`, which checks its type and count instead of assuming them.
  The specs are List functions on `toList`; `#guard` runs each op against its spec.
-/
import LeetQ.Rel.Parted
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
import QLean.Verify.ScanOver
import LeetQ.Rel.KernelWF.Reduce
import LeetQ.Rel.Find
import QLean.Dep.Table

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel
open Find (atomsOf denseOf)

namespace Ops

variable {k : QAtomicType} {t : QAtomicType}

/-! ## Scans: `f\x`, key kept -/

/-- `f\x` at the q dyad `f` (`+ * & | ^`), answered at `rt` (q's accumulator type). -/
def scan (f : Prim.Dyadic) (rt : QAtomicType) {n : Nat} (R : Arr t n) : Option (Arr rt n) :=
  (scanColumn f rt t n R.enc).bind fun e => (Arr.of rt n (.vector rt n e none) "f\\x").toOption

/-! ## Folds: `f/x` -/

/-- `f/x` over the values in position order, as q's answer widened to `Int64`. -/
def over (op : Coc.Over) {n : Nat} (R : Arr t n) : Option Int64 := overColumn op t n R.enc

/-- `avg x`: the bits of the `float` q answers. -/
def avg {n : Nat} (R : Arr t n) : Option UInt64 :=
  (avgColumn t n R.enc).bind fun a => Carrier.of? .float (.atom a)

/-! ## Grouped folds over a parted list: one answer per group

A `Parted`'s groups are the segments of `o`, so every op here reads `o` and writes no group id per
row: `o bin til n` would be an `n`-row pass to recover what `o` already says. A per-group answer `A` keyed
by `keys : Arr k P.g` is the relation `⟨P.g, keys, A⟩`; a boxed list is output only (`Parted.box`). -/

/-- `o`'s dense payload, the `g+1` offsets the segment kernels read. -/
def offs {g : Nat} (o : Arr .long (g+1)) : Option ByteArray := Enc.bytesOf .long (g+1) o.enc

/-- `1_o` over `g+1` offsets: each group's end. -/
def ends (g : Nat) (ob : ByteArray) : ByteArray := ob.extract 8 (8 * (g+1))

/-- `1_deltas o`, each group's size `o[r+1] − o[r]`: one `Ew.val` pass over the offsets, which hold
    no null, so `0N` as the null changes nothing. -/
def sizes (g : Nat) (ob : ByteArray) : ByteArray :=
  Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (ends g ob) (ob.extract 0 (8 * g)) g.toUSize

/-- `x` read at the positions `ix`, a position past `n` reading q's null (`()` in a general list): the
    kernel-free gather, through `Enc.atoms` and `Enc.ofAtoms` at an atom type. -/
def pickRef {n m : Nat} (x : Arr t n) (ix : Fin m → Nat) : Arr t m :=
  if hg : t = .general then by
    subst hg
    exact Arr.mk (.gen (Array.ofFn fun j => if h : ix j < n then x.get ⟨ix j, h⟩ else .general #[])) (by simp [Enc.WF])
  else atomsOf t hg (fun j => (Enc.atoms t n x.enc).getD (ix j) (Eval.nullAtom t hg))
    (fun j => by
      simp only [Array.getD]; split
      · exact Column.atoms_type t n x.enc _ (Array.getElem_mem ..)
      · exact Verify.nullAtom_type t)
    (List.finRange m) (List.length_finRange ..)

theorem denseOf_eq {nx : Nat} {x : Arr .long nx} {b : ByteArray} (h : Enc.bytesOf .long nx x.enc = some b) :
    denseOf x = b := Option.some.inj ((Option.some_get _).trans h)

/-- A pass pushing one `ow`-byte word per element of `til m` writes `m * ow` bytes. -/
theorem foldl_push_size (f : Nat → UInt64) (ow : Nat) (how : ow ≤ 8) (m : Nat) :
    ((List.range m).foldl (fun out i => Column.pushBits out (f i) ow) ByteArray.empty).size = m * ow := by
  rw [(Verify.foldl_pushBits f ow how (List.range m) .empty).1]; simp [Nat.mul_comm]

/-- `sizes` writes one long per group. -/
theorem sizes_size {g : Nat} (B : ByteArray) (hg : g < USize.size) : (sizes g B).size = g * 8 := by
  have e : sizes g B = (List.range g).foldl (fun out i => Column.pushBits out
      ((Ew.intStep Ew.sub Int64.minValue (Column.bitsAt (ends g B) (i * 8) 8).toInt64
        (Column.bitsAt (B.extract 0 (8 * g)) (i * 8) 8).toInt64).toUInt64) 8) ByteArray.empty := by
    unfold sizes Ew.val; rw [USize.toNat_ofNat_of_lt' hg]; rfl
  rw [e, foldl_push_size _ 8 (by decide)]

/-- `count each` by group: `1_deltas o`, by the kernel where the count fits a `USize`, else the same
    differences read off `o`'s elements. -/
def countBy {v : QAtomicType} (P : Parted v) : Arr .long P.g :=
  if h : P.g < USize.size then
    Arr.mk (.bytes (sizes P.g (denseOf P.o))) (KernelWF.wf_bytes (w := 8) (by decide) rfl (sizes_size _ h))
  else atomsOf .long (by decide) QAtom.long (fun _ => rfl)
    (List.ofFn fun j : Fin P.g => P.o.get j.succ - P.o.get j.castSucc) (List.length_ofFn ..)

/-- `-1+1_o`, each group's last row, one `Ew.val` pass over the ends. -/
def lasts (g : Nat) (ob : ByteArray) : ByteArray :=
  Ew.val Ew.add Ew.i64 Ew.va Int64.minValue (ends g ob) (atomBytes Ew.i64 (-1 : Int64).toUInt64) g.toUSize

theorem lasts_size {g : Nat} (B : ByteArray) (hg : g < USize.size) : (lasts g B).size / 8 = g := by
  simpa [Verify.elemsW] using congrArg List.length (Verify.val_i64_va Ew.add Int64.minValue (ends g B) ((-1 : Int64).toUInt64) g hg)

/-- `last each` by group: `x[-1+1_o]`, on q's domain `hne`, every group holding a row (an empty one has no
    last row). The kernel at an atom type where the count fits a `USize`, else `pickRef` at `o[j+1]-1`. -/
def lastBy (P : Parted t) (_hne : ∀ j : Fin P.g, P.o.get j.castSucc < P.o.get j.succ) : Arr t P.g :=
  if h : t ≠ .general ∧ P.g < USize.size then
    let L := lasts P.g (denseOf P.o)
    Arr.mk ((gatherColumn t P.n P.val.enc (L.size / 8) (.bytes L)).get
        (KernelWF.gatherColumn_isSome P.val.wf h.1 L (Nat.div_mul_le_self ..)))
      (Eq.subst (motive := fun m => Enc.WF t m _) (lasts_size (denseOf P.o) h.2)
        (KernelWF.gatherColumn_wf P.val.wf L (Option.some_get _).symm))
  else pickRef P.val fun j => (P.o.get j.succ - 1).toUInt64.toNat

/-- `select f x by k`: `f/` over each segment's rows at every type q's grouped fold has an engine for
    (`groupedOver`: integral and float, not boolean), answered at `Coc.Over.resultType`'s type, q's
    type for `f/` of a `t`, which comes with the answer. -/
def overBy (op : Coc.Over) (P : Parted t) : Option ((rt : QAtomicType) × Arr rt P.g) := do
  let rt ← op.resultType false t
  let s ← groupedOver op false false t (.segs (← offs P.o)) P.n P.val.enc (tilLongs P.g.toUSize)
  pure ⟨rt, ← (Arr.of rt P.g (.vector rt P.g (.bytes s) none) "f/ by").toOption⟩

/-! ## Moving windows: `w mop x`, key kept -/

/-- `w msum/mcount/mavg/mdev/mmin/mmax x`, answered at `rt`; `none` where q answers another type. -/
def mwin (op : Scan.MOp) (w : Nat) (rt : QAtomicType) {n : Nat} (R : Arr t n) : Option (Arr rt n) :=
  (mwinColumn op t w n R.enc).bind fun (rt', e) =>
    if rt' = rt then (Arr.of rt n (.vector rt n e none) "w mop x").toOption else none

/-! ## Order: `iasc idesc rank asc desc xasc` -/

/-- `R`'s positions in q's order (`Carrier.le`), ties in index order both ways round: the kernel-free grade. -/
def gradeList (desc : Bool) {n : Nat} (R : Arr t n) : List (Fin n) :=
  (List.finRange n).mergeSort fun i j => if desc then Table.Carrier.le (R.get j) (R.get i) else Table.Carrier.le (R.get i) (R.get j)

/-- `<x` / `>x`: the stable grade, keyed by position. The kernel where the count fits a `USize` and the
    column is not general, which it does not grade; `gradeList` elsewhere. -/
def grade (desc : Bool) {n : Nat} (R : Arr t n) : Arr .long n :=
  if h : n < USize.size ∧ t ≠ .general then
    Arr.mk ((gradeColumn t desc n R.enc).get (KernelWF.gradeColumn_isSome h.1 R.wf h.2))
      (KernelWF.gradeColumn_wf h.1 R.wf (Option.some_get _).symm)
  else atomsOf .long (by decide) (fun i : Fin n => QAtom.long (Int64.ofNat i)) (fun _ => rfl) (gradeList desc R)
    (by simp [gradeList, List.length_mergeSort])

def iasc {n : Nat} := @grade t false n
def idesc {n : Nat} := @grade t true n

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order. -/
def rank {n : Nat} (R : Arr t n) : Arr .long n :=
  if h : n < USize.size ∧ t ≠ .general then
    Arr.mk ((gradeColumn t false n R.enc (rank := true)).get (KernelWF.gradeColumn_isSome h.1 R.wf h.2))
      (KernelWF.gradeColumn_wf h.1 R.wf (Option.some_get _).symm)
  else atomsOf .long (by decide) (fun i : Fin n => QAtom.long (Int64.ofNat ((gradeList false R).idxOf i))) (fun _ => rfl)
    (List.finRange n) (List.length_finRange ..)

/-- `x@p`, `x` read at the `n` positions `p`, one gather; a position past `n` reads q's null. The kernel at
    an atom type where `p`'s dense payload holds its `n` longs, else `pickRef`. -/
def permute {n : Nat} (p : Arr .long n) (x : Arr t n) : Arr t n :=
  if h : t ≠ .general ∧ (denseOf p).size = n * 8 then
    Arr.mk ((gatherColumn t n x.enc ((denseOf p).size / 8) (.bytes (denseOf p))).get
        (KernelWF.gatherColumn_isSome x.wf h.1 _ (Nat.div_mul_le_self ..)))
      (Eq.subst (motive := fun m => Enc.WF t m _) (by rw [h.2]; exact Nat.mul_div_cancel _ (by decide))
        (KernelWF.gatherColumn_wf x.wf _ (Option.some_get _).symm))
  else pickRef x fun j => (p.get j).toUInt64.toNat

/-- `asc x` / `desc x` = `(<x);x`, keyed by position. `sortValues` where the key is a bijection of
    the bits, the bitmap sort at `boolean`, the grade and a gather elsewhere. `asc` sets `s`. -/
def sort (desc : Bool) {n : Nat} (R : Arr t n) : Arr t n :=
  let byGrade (_ : Unit) := permute (grade desc R) R
  let a := match (sortedValues t desc n R.enc).orElse fun _ => sortedBitsColumn t desc n R.enc with
    | some e => Find.orElse e byGrade
    | none => byGrade ()
  a.markIf (if desc then 0 else 1)

def asc {n : Nat} := @sort t false n
def desc {n : Nat} := @sort t true n

/-- `xasc` on one more column of a table: `x` in the ascending order of the sort column `s`. -/
def xasc {n : Nat} {u : QAtomicType} (s : Arr t n) (x : Arr u n) : Arr u n := permute (iasc s) x

end Ops

/-! ## The specs, on `toList` -/

namespace Spec

/-- q's long null. -/
abbrev nul : Int64 := Int64.minValue

/-- The seed, then the accumulator after each element (core has no `List.scanl`). -/
def scanl {α β : Type} (f : β → α → β) : β → List α → List β
  | a, [] => [a]
  | a, x :: xs => a :: scanl f (f a x) xs

/-- `f\x` with q's null skip at any element and accumulator type, `isNull` naming the null: the
    accumulator after each element, a null leaving it unchanged. The left fold the kernel runs. -/
def scanBy {α β : Type} (isNull : α → Bool) (step : β → α → β) (seed : β) (xs : List α) : List β :=
  (scanl (fun a x => if isNull x then a else step a x) seed xs).tail

/-- `f\x` on longs: `scanBy` at `0N`, its body spelled out so it unfolds to the `scanl` it is. -/
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
def mext {α : Type} (better : α → α → Bool) (seed : α) (w : Nat) (xs : List α) : List α :=
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
  simp only [scan, scanBy, over, scanl, List.tail_cons, List.foldl_cons]
  exact scanl_getLast? _ _ _

/-- Term `j` of `scanl` is the fold over the first `j` elements. -/
theorem scanl_range {α β : Type} (f : β → α → β) (a : β) (xs : List α) :
    scanl f a xs = (List.range (xs.length + 1)).map fun j => (xs.take j).foldl f a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [scanl, ih, List.length_cons, List.range_succ_eq_map (n := xs.length + 1), List.map_cons, List.map_map]
    simp [Function.comp_def]

/-- Term `j` of `scanBy` is the null-skipping left fold of the first `j+1` elements. -/
theorem scanBy_range {α β : Type} (isNull : α → Bool) (step : β → α → β) (seed : β) (xs : List α) :
    scanBy isNull step seed xs = (List.range xs.length).map fun j =>
      (xs.take (j+1)).foldl (fun a x => if isNull x then a else step a x) seed := by
  rw [scanBy, scanl_range, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]; rfl

/-- Term `j` of `Spec.scan` is `Spec.over` of the first `j+1` elements. -/
theorem scan_range (step : Int64 → Int64 → Int64) (seed : Int64) (xs : List Int64) :
    scan step seed xs = (List.range xs.length).map fun j => over step seed (xs.take (j+1)) :=
  scanBy_range _ step seed xs

/-- The scan verb whose seed and step are the fold `op`'s: `q.k` spells `+\ *\ &\ |\` with the dyads of
    `+/ */ &/ |/`. `all`/`any` fold over `"b"$x` and have no scan. -/
def verb : Coc.Over → Option Scan.Verb
  | .add => some .sums
  | .mul => some .prds
  | .lesser => some .mins
  | .greater => some .maxs
  | _ => none

/-- A total over a count, as the bits of a `float`; `0n` for an empty count or a NaN quotient. -/
def quot (p : Int64 × Nat) : UInt64 :=
  if p.2 == 0 then QLean.nanBits else
    let r := (p.1.toFloat / p.2.toFloat).toBits
    if Bits.f64IsNaN r then QLean.nanBits else r

/-- `avg x`: the total of the elements that are not `0N`, wrapping at `Int64`, over their count. -/
def avg (xs : List Int64) : UInt64 := quot (over (· + ·) 0 xs, (xs.filter (· != nul)).length)

/-- The step and seed the long scan kernel folds at each verb (`intScan`'s, read on longs): `fills` keeps
    the last element read, from `0N`. -/
def kern : Scan.Verb → (Int64 → Int64 → Int64) × Int64
  | .sums => (Coc.Over.step .add, 0)
  | .prds => (Coc.Over.step .mul, 1)
  | .mins => (Coc.Over.step .lesser, Int64.maxValue)
  | .maxs => (Coc.Over.step .greater, -Int64.maxValue)
  | .fills => (fun _ y => y, nul)

/-- At a verb that is a fold's scan, the kernel's step and seed are the fold's. -/
theorem kern_verb {op : Coc.Over} {sv : Scan.Verb} (hv : verb op = some sv) :
    (kern sv).1 = op.step ∧ (kern sv).2 = op.seed nul := by
  cases op <;> simp only [verb, Option.some.injEq, reduceCtorEq] at hv <;> subst hv <;> exact ⟨rfl, by decide⟩

/-- The step and seed the float scan kernel folds at each verb (`fltScan`'s at `float`): a `Float`
    accumulator, each element's bits read by `Float.ofBits`. -/
def fkern : Scan.Verb → (Float → UInt64 → Float) × Float
  | .sums => (fun a x => a + Float.ofBits x, 0.0)
  | .prds => (fun a x => a * Float.ofBits x, 1.0)
  | .mins => (fun a x => if Float.ofBits x < a then Float.ofBits x else a, Float.ofBits 0x7ff0000000000000)
  | .maxs => (fun a x => if a < Float.ofBits x then Float.ofBits x else a, Float.ofBits 0xfff0000000000000)
  | .fills => (fun _ x => Float.ofBits x, Float.ofBits QLean.nanBits)

/-- A `Float` accumulator written out as the bits of q's `float`, every NaN as `0n`. -/
def femit (x : Float) : UInt64 := if Bits.f64IsNaN x.toBits then QLean.nanBits else x.toBits

/-- A float's bits with every NaN as q's `0n`: the `foR` path of `avg` divides with no NaN guard, which
    the dense path has. -/
def canon (r : UInt64) : UInt64 := if Bits.f64IsNaN r then QLean.nanBits else r

/-- The total of float words in `sumF64Total`'s order, q's one order at every encoding: `avg` picks
    `avg`'s lanes (two with a null), else `sum`'s (one with a null); eight lanes with none. -/
def fsum (avg : Bool) (xs : List UInt64) : Float := sumF64Total avg xs.length fun i => Float.ofBits (xs.getD i 0)

/-- `avg` of float words: `fsum true` over the non-NaN count, `0n` when there is none or the quotient
    is a NaN. -/
def favg (xs : List UInt64) : UInt64 :=
  let live := xs.countP fun u => !Bits.f64IsNaN u
  if live == 0 then QLean.nanBits else canon (fsum true xs / live.toFloat).toBits

/-- One element `u` into the four running totals `mwinBits`' float pass keeps: the total with the null
    skipped, the total with the null as `0.0`, the total of squares, the live count. -/
def mstep (a : Float × Float × Float × Int64) (u : UInt64) : Float × Float × Float × Int64 :=
  let nul := Scan.Kind.f64.isNull u
  let x := if nul then 0.0 else Scan.Kind.f64.toFloat u
  (if nul then a.1 else a.1 + Scan.Kind.f64.toFloat u, a.2.1 + x, a.2.2.1 + x * x, a.2.2.2 + if nul then 0 else 1)

/-- What `mwinBits` writes at a float `msum`/`mavg`/`mdev` from the totals `c` after the window's last
    element and `b` before its first: their difference, then `mavg`'s quotient by the count and `mdev`'s
    population deviation, a NaN of the last two as `0n`. -/
def memit (op : Scan.MOp) (c b : Float × Float × Float × Int64) : UInt64 :=
  match op with
  | .msum => (c.1 - b.1).toBits
  | .mavg => let a := (c.2.1 - b.2.1) / (c.2.2.2 - b.2.2.2).toFloat; if a.isNaN then QLean.nanBits else a.toBits
  | _ =>
    let k := (c.2.2.2 - b.2.2.2).toFloat
    let mn := (c.2.1 - b.2.1) / k
    let r := Float.sqrt ((c.2.2.1 - b.2.2.1) / k - mn * mn)
    if r.isNaN then QLean.nanBits else r.toBits

/-- `w msum/mavg/mdev x` on floats as q runs them, `{y-(-x)_(0i*x#y),y:+\y}`: the prefix fold `mstep` from
    zero, then at `i` `memit` of the totals after `i+1` and after `i+1−w` elements. Not a fold of each window:
    `Float` subtraction does not undo addition, so the window total is this difference and nothing else. -/
def mfloat (op : Scan.MOp) (w : Nat) (xs : List UInt64) : List UInt64 :=
  let P (j : Nat) := (xs.take j).foldl mstep (0.0, 0.0, 0.0, 0)
  (List.range xs.length).map fun i => memit op (P (i+1)) (P (i+1-w))

theorem nanBits_isNaN : Bits.f64IsNaN QLean.nanBits = true := by first | rfl | decide

/-- `quot` is already canonical. -/
theorem canon_quot (p : Int64 × Nat) : canon (quot p) = quot p := by
  by_cases h0 : (p.2 == 0) = true
  · simp [canon, quot, h0, nanBits_isNaN]
  · by_cases hr : Bits.f64IsNaN (p.1.toFloat / p.2.toFloat).toBits = true <;>
      simp [canon, quot, h0, hr, nanBits_isNaN]

/-- The unguarded quotient, made canonical, is `quot`. -/
theorem canon_raw (p : Int64 × Nat) :
    canon (if p.2 == 0 then QLean.nanBits else (p.1.toFloat / p.2.toFloat).toBits) = quot p := by
  by_cases h0 : (p.2 == 0) = true
  · simp [canon, quot, h0, nanBits_isNaN]
  · simp [canon, quot, h0]

/-- `0N` is the least long, so every other long is at least `0N + 1`. -/
theorem toInt_ne_nul (x : Int64) (h : x ≠ nul) : -9223372036854775807 ≤ x.toInt := by
  have h0 : nul.toInt ≤ x.toInt := by first | exact Int64.minValue_le_toInt x | exact Int64.minValue_le_toInt
  have hm : nul.toInt = -9223372036854775808 := by first | rfl | decide
  have hne : x.toInt ≠ nul.toInt := fun e => h (Int64.toInt_inj.1 e)
  omega

theorem toInt_nul_succ : (nul + 1).toInt = -9223372036854775807 := by first | rfl | decide

/-- `x < 0N + 1` is `x = 0N`: `Coc.countLt` at `0N + 1` counts the nulls. -/
theorem lt_nul_succ (x : Int64) : decide (x < nul + 1) = (x == nul) := by
  by_cases h : x = nul
  · subst h; decide
  · have := toInt_ne_nul x h
    rw [show (x == nul) = false by simpa using h, decide_eq_false_iff_not, Int64.lt_iff_toInt_lt, toInt_nul_succ]
    omega

/-- `max`'s step is associative. -/
theorem greater_assoc (a b c : Int64) : Coc.Over.step .greater (Coc.Over.step .greater a b) c =
    Coc.Over.step .greater a (Coc.Over.step .greater b c) := by
  simp only [Coc.Over.step]
  repeat' split
  all_goals simp only [Int64.lt_iff_toInt_lt] at *
  all_goals first
    | rfl
    | (exfalso; omega)
    | exact Int64.toInt_inj.1 (by omega)

/-- `max`'s seed `-0W = 0N + 1` is a unit on the longs that are not `0N`, which are all `skipNul` lets in. -/
theorem greater_seed (a : Int64) (h : a ≠ nul) :
    Coc.Over.step .greater (Coc.Over.seed .greater nul) a = a ∧ Coc.Over.step .greater a (Coc.Over.seed .greater nul) = a := by
  have ha := toInt_ne_nul a h
  refine ⟨?_, ?_⟩
  · show (if a < nul + 1 then nul + 1 else a) = a
    rw [if_neg (by rw [Int64.lt_iff_toInt_lt, toInt_nul_succ]; omega)]
  · show (if nul + 1 < a then a else nul + 1) = a
    by_cases hlt : nul + 1 < a
    · rw [if_pos hlt]
    · rw [if_neg hlt]
      rw [Int64.lt_iff_toInt_lt, toInt_nul_succ] at hlt
      exact Int64.toInt_inj.1 (by rw [toInt_nul_succ]; omega)

/-- `max` of two longs that are not `0N` is not `0N`. -/
theorem greater_ne (a b : Int64) (ha : a ≠ nul) (hb : b ≠ nul) : Coc.Over.step .greater a b ≠ nul := by
  simp only [Coc.Over.step]; split <;> assumption

/-- `fills` over a list with no `0N` is the identity: the kernel's short-cut. -/
theorem scan_last_id (xs : List Int64) (h : ∀ x ∈ xs, x ≠ nul) : scan (fun _ y => y) nul xs = xs := by
  have hs : ∀ (a : Int64) (l : List Int64), scanl (fun a x => if x == nul then a else x) a l =
      a :: (scanl (fun a x => if x == nul then a else x) a l).tail := fun a l => by cases l <;> rfl
  suffices H : ∀ l : List Int64, (∀ x ∈ l, x ≠ nul) → ∀ a,
      (scanl (fun a x => if x == nul then a else x) a l).tail = l from H xs h nul
  intro l
  induction l with
  | nil => intro _ a; rfl
  | cons x l ih =>
    intro h a
    have hx : (x == nul) = false := by simpa using h x (List.mem_cons_self ..)
    simp only [scanl, List.tail_cons, hx, Bool.false_eq_true, ↓reduceIte]
    rw [hs, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

end Spec

/-! ## Laws on the ops -/

namespace Ops

variable {k : QAtomicType} {t : QAtomicType}
/-- The longs `overBytes` folds over a dense long payload are the column's elements. -/
theorem denseElems_long {n : Nat} {R : Arr .long n} {b : ByteArray} (hc : R.enc = .bytes b) :
    QLean.Verify.denseElems Ew.i64 b = R.toList := by
  have hn : n = b.size / 8 := (Arr.n_long_bytes R hc).symm
  apply List.ext_getElem
  · rw [QLean.Verify.denseElems, List.length_map, List.length_range, Arr.length_toList, hn]; rfl
  · intro j _ _
    simp only [QLean.Verify.denseElems, List.getElem_map, List.getElem_range]
    rw [Arr.getElem_toList, Arr.get_long_bytes R hc]; rfl

/-- `f/x` over a dense long column, at a verb that skips the null (not `all`/`any`): `Spec.over` at the
    kernel's step and seed, from `overBytes_eq`. -/
theorem over_bytes {op : Coc.Over} (hb : op.boolCast = false) {n : Nat} {R : Arr .long n} {b : ByteArray}
    (hc : R.enc = .bytes b) : over op R = some (Spec.over op.step (op.denseSeed Ew.i64 Spec.nul) R.toList) := by
  have he : overBytes op Ew.i64 Spec.nul b = Spec.over op.step (op.denseSeed Ew.i64 Spec.nul) R.toList := by
    rw [QLean.Verify.overBytes_eq, QLean.Verify.overList, hb, QLean.Verify.foldl_filter, denseElems_long hc, Spec.over]
    congr 1; funext a x; by_cases hx : x = Spec.nul <;> simp [hx]
  simp only [over, hc, overColumn, overFoR, clsOf, Coc.denseNul, Coc.nullOf, bind, Option.bind, Coc.narrowed]
  rw [he]; simp

/-- A `long` fold that is not `all`/`any` answers at `long`. -/
theorem resultType_long {op : Coc.Over} (hb : op.boolCast = false) : op.resultType false .long = some .long := by
  cases op <;> first | rfl | cases hb

/-- `groupedOver` at `long`: the integral fold, each cell its slot's eight bytes. -/
theorem groupedOver_long {op : Coc.Over} (hb : op.boolCast = false) (gs : Groups) (n : Nat) (e : Enc) (ord : ByteArray) :
    groupedOver op false false .long gs n e ord =
      (overGroupsColumn op .long gs n e).map fun m => groupCells .wrap 8 gs.count m ord := by
  have hr := resultType_long hb
  cases h : overGroupsColumn op .long gs n e <;> cases op <;> simp_all [groupedOver, bind, Option.bind] <;> rfl

/-- Offset `j` of `o` is the long `atI64` reads at `j` of its dense payload. -/
theorem offs_get {g : Nat} {o : Arr .long (g+1)} {ob : ByteArray} (ho : o.enc = .bytes ob) {j : Nat}
    (hj : j < g + 1) : o.toList[j]! = atI64 ob j := by
  rw [getElem!_pos _ j (by rw [Arr.length_toList]; exact hj), Arr.getElem_toList, Arr.get_long_bytes o ho, QLean.Verify.atI64_eq]

/-- **`select f x by k` over a dense long column**, at a verb that skips the null: group `j`'s answer
    is `Spec.over` of the rows of the segment of `o` that holds them, `o[j] ≤ i < o[j+1]`. No `Cuts`
    is needed: rows outside `[0, n)` and a descending pair of offsets name no row. -/
theorem overBy_bytes {op : Coc.Over} (hb : op.boolCast = false) {n g : Nat}
    {o : Arr .long (g+1)} {co : Cuts o n} {x : Arr .long n} {b ob : ByteArray}
    {S : Arr .long g} (hg : g < USize.size) (h63 : g < 2 ^ 63) (hc : x.enc = .bytes b) (ho : o.enc = .bytes ob)
    (h : overBy op ⟨g, n, o, co, x⟩ = some ⟨.long, S⟩) :
    S.toList = (List.range g).map fun j => Spec.over op.step (op.denseSeed Ew.i64 Spec.nul)
      (((List.range n).filter fun i => decide ((o.toList[j]!).toNatClampNeg ≤ i ∧ i < (o.toList[j+1]!).toNatClampNeg)).map
        fun i => x.toList[i]!) := by
  have hn : b.size / 8 = n := Arr.n_long_bytes x hc
  have hob : ob.size / 8 = g + 1 := Arr.n_long_bytes o ho
  have hgu : g.toUSize.toNat = g := USize.toNat_ofNat_of_lt hg
  have hcnt : (Groups.segs ob).count.toNat = g := by simp only [Groups.count, hob, Nat.add_sub_cancel]; exact hgu
  have hm : overGroupsColumn op .long (.segs ob) n x.enc = some (overSegments op Ew.i64 Spec.nul ob b) := by
    simp only [overGroupsColumn, hc, clsOf, Coc.denseNul, Coc.nullOf, Enc.bytesOf, bind, Option.bind]
  have hof : offs o = some ob := by simp only [offs, ho, Enc.bytesOf]
  simp only [overBy, hof, resultType_long hb, groupedOver_long hb, hm, bind, Option.bind, Option.map] at h
  simp only [Arr.of] at h
  split at h
  · cases h
  rename_i A hA
  rw [show A = S by cases h; rfl] at hA
  split at hA
  · cases hA
    have e : QLean.Verify.denseElems Ew.i64 b = x.toList := denseElems_long (R := x) hc
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
  · cases hA

/-! ### Value laws over a long column that lists `longWords` (`bytes` or `foR`; not `alp`) -/

/-- A long column's elements, element `i` its word `i` read as a long. -/
theorem toList_words {m : Nat} (x : Arr .long m) {B : ByteArray} {ws : List UInt64}
    (hx : longWords m x.enc = some ws) (hB : Verify.elemsW 8 B = ws) (hs : B.size / 8 = m) :
    x.toList = (List.range m).map fun i => (Column.bitsAt B (i * 8) 8).toInt64 := by
  rw [Arr.toList_long x hx, ← hB, Verify.elemsW, hs, List.map_map]; rfl

/-- The first `j ≤ m` of `til m` mapped are `til j` mapped. -/
theorem take_range_map {α : Type} (g : Nat → α) {j m : Nat} (h : j ≤ m) :
    ((List.range m).map g).take j = (List.range j).map g :=
  List.ext_getElem (by simp; omega) fun _ _ _ => by simp

/-- **The scan engine over eight-byte words**, at any accumulator, seed, step and writer: the words
    `scanOf` writes are `Spec.scanBy` of the payload's words, each written by `emit`, from `scanOf_get`.
    The core every eight-byte layout's scan law (long, float) is an instance of. -/
theorem scanOf_words {α : Type} (b : ByteArray) {rd : Nat → UInt64} (hrd : ∀ i, rd i = Column.bitsAt b (i * 8) 8)
    (isNull : UInt64 → Bool) (seed : α) (st : α → UInt64 → α) (emit : α → UInt64) :
    Verify.elemsW 8 (Scan.scanOf (b.size / 8) 8 rd isNull seed st emit)
      = (Spec.scanBy isNull st seed (Verify.elemsW 8 b)).map emit := by
  obtain rfl : rd = fun i => Column.bitsAt b (i * 8) 8 := funext hrd
  rw [Verify.elemsW, Scan.scanOf_size, Nat.mul_div_cancel _ (by decide), Spec.scanBy_range, List.map_map,
    Verify.elemsW, List.length_map, List.length_range]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  rw [Verify.scanOf_get _ 8 (by decide) _ _ _ _ _ j hj, Function.comp_apply,
    take_range_map _ (show j + 1 ≤ b.size / 8 by omega), show 8 * 8 = 64 from rfl, Verify.ofNat_toNat_mod64]

/-- `scanOf_words` at a step and writer that read each word as a long: its words are `Spec.scan` of the
    payload's longs. -/
theorem scanOf_i64 (b : ByteArray) (seed : Int64) {st : Int64 → UInt64 → Int64} {g : Int64 → Int64 → Int64}
    (hst : ∀ a x, st a x = g a x.toInt64) {emit : Int64 → UInt64} (he : ∀ a, emit a = a.toUInt64) :
    Verify.elemsW 8 (Scan.scanOf (b.size / 8) 8 (Scan.Kind.i64.bitsAt b) Scan.Kind.i64.isNull seed st emit)
      = (Spec.scan g seed ((Verify.elemsW 8 b).map UInt64.toInt64)).map Int64.toUInt64 := by
  rw [scanOf_words b (rd := Scan.Kind.i64.bitsAt b) (fun _ => rfl),
    show Spec.scan g seed _ = Spec.scanBy (· == Spec.nul) g seed _ from rfl, Spec.scanBy_range, Spec.scanBy_range, List.map_map, List.map_map,
    List.length_map]
  refine List.map_congr_left fun j _ => ?_
  rw [Function.comp_apply, Function.comp_apply, he, ← List.map_take, List.foldl_map]
  congr 2
  funext a i
  simp [Scan.Kind.isNull, hst, Spec.nul]

/-- **The float scan kernel over a dense payload**, at each of `+\ *\ &\ |\ ^\`: its words are
    `Spec.scanBy` of the payload's words at q's NaN null and the verb's `Spec.fkern`, each accumulator
    written by `Spec.femit`. -/
theorem scan_f64_words (sv : Scan.Verb) (b : ByteArray) (hm : b.size / 8 < USize.size) :
    Verify.elemsW 8 (Scan.scan sv .f64 (b.size / 8).toUSize b)
      = (Spec.scanBy Scan.Kind.f64.isNull (Spec.fkern sv).1 (Spec.fkern sv).2 (Verify.elemsW 8 b)).map Spec.femit := by
  have hn : min (b.size / 8).toUSize.toNat (Scan.Kind.f64.avail b) = b.size / 8 := by
    rw [USize.toNat_ofNat_of_lt' hm, show Scan.Kind.f64.avail b = b.size / 8 from rfl, Nat.min_self]
  have e : Scan.scan sv .f64 (b.size / 8).toUSize b = Scan.fltScan sv .f64 b
      (min (b.size / 8).toUSize.toNat (Scan.Kind.f64.avail b)) (Scan.outKind sv .f64).width := rfl
  rw [e, hn]
  cases sv <;> exact scanOf_words b (fun _ => rfl) _ _ _ _

/-- The float scan kernel writes eight bytes per element. -/
theorem scan_f64_size (sv : Scan.Verb) (b : ByteArray)
    (hm : b.size / 8 < USize.size) : (Scan.scan sv .f64 (b.size / 8).toUSize b).size / 8 = b.size / 8 := by
  have := congrArg List.length (scan_f64_words sv b hm)
  simpa [Verify.elemsW, Spec.scanBy_range] using this

/-- `(if y < a then y else a) = (if a < y then a else y)` on longs: `mins`'s step is `min`'s. -/
theorem ite_lt_min (a y : Int64) : (if y < a then y else a) = (if a < y then a else y) := by
  by_cases h1 : y < a <;> by_cases h2 : a < y <;> simp only [h1, h2, if_true, if_false] <;>
    simp only [Int64.lt_iff_toInt_lt] at h1 h2 <;> first | omega | exact Int64.toInt_inj.1 (by omega)

/-- `(if a < y then y else a) = (if y < a then a else y)` on longs: `maxs`'s step is `max`'s. -/
theorem ite_lt_max (a y : Int64) : (if a < y then y else a) = (if y < a then a else y) := by
  by_cases h1 : y < a <;> by_cases h2 : a < y <;> simp only [h1, h2, if_true, if_false] <;>
    simp only [Int64.lt_iff_toInt_lt] at h1 h2 <;> first | omega | exact Int64.toInt_inj.1 (by omega)

/-- **The long scan kernel over a dense payload**, at each of `+\ *\ &\ |\ ^\`: its words are `Spec.scan`
    of the payload's longs at the verb's `Spec.kern`. `Alg.sums b` is the `.sums` case. -/
theorem scan_i64_words (sv : Scan.Verb) (b : ByteArray) (hm : b.size / 8 < USize.size) :
    Verify.elemsW 8 (Scan.scan sv .i64 (b.size / 8).toUSize b)
      = (Spec.scan (Spec.kern sv).1 (Spec.kern sv).2 ((Verify.elemsW 8 b).map UInt64.toInt64)).map Int64.toUInt64 := by
  have hn : min (b.size / 8).toUSize.toNat (Scan.Kind.i64.avail b) = b.size / 8 := by
    rw [USize.toNat_ofNat_of_lt' hm, show Scan.Kind.i64.avail b = b.size / 8 from rfl, Nat.min_self]
  have e : Scan.scan sv .i64 (b.size / 8).toUSize b = Scan.intScan sv .i64 b
      (min (b.size / 8).toUSize.toNat (Scan.Kind.i64.avail b)) (Scan.outKind sv .i64).width
      Int64.maxValue (-Int64.maxValue) Int64.minValue := rfl
  rw [e, hn]
  cases sv
  · exact scanOf_i64 b 0 (fun _ _ => rfl) (fun a => by simp [Scan.narrow, Scan.outKind, Scan.Kind.width])
  · exact scanOf_i64 b 1 (fun _ _ => rfl) (fun _ => rfl)
  · exact scanOf_i64 b _ (fun a x => ite_lt_min a x.toInt64) (fun _ => rfl)
  · exact scanOf_i64 b _ (fun a x => ite_lt_max a x.toInt64) (fun _ => rfl)
  · exact scanOf_i64 (g := fun _ y => y) b Spec.nul (fun _ _ => rfl) (fun _ => rfl)

/-- The long scan kernel writes eight bytes per element. -/
theorem scan_i64_size (sv : Scan.Verb) (b : ByteArray)
    (hm : b.size / 8 < USize.size) : (Scan.scan sv .i64 (b.size / 8).toUSize b).size / 8 = b.size / 8 := by
  have := congrArg List.length (scan_i64_words sv b hm)
  simpa [Verify.elemsW, Spec.scan_range] using this

/-- A long `foR` column lists `Coc.elems`, the words `Coc.over`, `countLt` and `anyNull` fold over. -/
theorem toList_elems {n : Nat} (R : Arr .long n) {md pk : ByteArray} (hc : R.enc = .foR md pk)
    (hn : n < USize.size) : R.toList = (Coc.elems md pk n.toUSize).map UInt64.toInt64 := by
  rw [Arr.toList_long R (show longWords n R.enc = some ((List.range n).map
      (Column.foRBits md pk (Column.blockStarts md))) by unfold longWords; rw [hc]),
    Coc.elems, USize.toNat_ofNat_of_lt' hn]

/-- A long column `holdsNull` clears holds no `0N`: block metadata on `foR`, one pass on `bytes`. -/
theorem nul_free {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) (h : holdsNull .long n R.enc = false) : ∀ x ∈ R.toList, x ≠ Spec.nul := by
  unfold longWords at hx
  cases hc : R.enc with
  | bytes b =>
    have h' : Scan.anyNull .i64 (b.size / 8).toUSize b = false := by rw [hc] at h; exact h
    have hm : b.size / 8 < USize.size := (Arr.n_long_bytes R hc) ▸ hn
    unfold Scan.anyNull at h'
    rw [USize.toNat_ofNat_of_lt' hm, show Scan.Kind.i64.avail b = b.size / 8 from rfl, Nat.min_self,
      Arr.n_long_bytes R hc] at h'
    rw [Arr.toList_long_bytes R hc, List.map_map]
    intro x hxm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hxm
    have := List.any_eq_false.1 h' i hi
    simpa [Scan.Kind.isNull, Scan.Kind.bitsAt, Scan.Kind.width] using this
  | foR md pk =>
    have h' : Coc.anyNull Spec.nul md pk n.toUSize = false := by rw [hc] at h; exact h
    unfold Coc.anyNull at h'
    rw [toList_elems R hc hn]
    intro x hxm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hxm
    have := List.any_eq_false.1 h' u hu
    simpa using this
  | _ => all_goals (rw [hc] at hx; cases hx)

/-- **`f\x` over a long column** (`bytes` or `foR`) at `+ * & | ^`: `Spec.scan` at the verb's `Spec.kern`.
    `^\` over a column with no `0N` is the kernel's identity short-cut, the argument handed back. -/
theorem scan_toList {f : Prim.Dyadic} {sv : Scan.Verb} (hf : scanVerb f = some sv)
    {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) {S : Arr .long n} (h : scan f .long R = some S) :
    S.toList = Spec.scan (Spec.kern sv).1 (Spec.kern sv).2 R.toList := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R hx hn
  have hm : B.size / 8 < USize.size := hBs ▸ hn
  have hk : Scan.outKind sv .i64 = .i64 := by cases sv <;> rfl
  have hL : R.toList = (Verify.elemsW 8 B).map UInt64.toInt64 := by rw [Arr.toList_long R hx, hBw]
  cases hfl : (sv == .fills && !(Scan.Kind.i64.hasNull && holdsNull .long n R.enc))
  · have hcol : scanColumn f .long .long n R.enc = some (Enc.answer .long (B.size / 8).toUSize.toNat
        (.bytes (Scan.scan sv .i64 (B.size / 8).toUSize B))) := by
      rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc] at hfl ⊢
      · rw [← hBs] at hfl ⊢; simp [scanColumn, scanWith, hf, hk, hfl, show scanKind .long = some .i64 from rfl,
          show QAtomicType.width .long = some 8 from rfl, Enc.bytesOf, Scan.scanForm]
        try simp only [show ¬ B.size < B.size / 8 * 8 from Nat.not_lt.2 (Nat.div_mul_le_self _ _), if_false]
        try (intro hs hor; subst hs; simp_all [Scan.Kind.hasNull])
        try (rw [if_neg]; intro ⟨hs, hor⟩; subst hs; simp_all [Scan.Kind.hasNull])
      · rw [hBs]
        simp [scanColumn, scanWith, hf, hk, hfl, show scanKind .long = some .i64 from rfl,
          show QAtomicType.width .long = some 8 from rfl, Scan.scanForm, Scan.scanFoR, Scan.Kind.width]
        intro hs hor; subst hs; simp_all [Scan.Kind.hasNull]
    simp only [scan, hcol, Option.bind] at h
    simp only [Arr.of] at h
    split at h
    · rename_i hw
      have hS : S.enc = Enc.answer .long (B.size / 8).toUSize.toNat
          (.bytes (Scan.scan sv .i64 (B.size / 8).toUSize B)) := by cases h; rfl
      rw [show (B.size / 8).toUSize.toNat = (Scan.scan sv .i64 (B.size / 8).toUSize B).size / 8 by
        rw [scan_i64_size sv B hm, USize.toNat_ofNat_of_lt' hm]] at hS
      have hsz : (Scan.scan sv .i64 (B.size / 8).toUSize B).size / 8 = n :=
        (show (B.size / 8).toUSize.toNat = (Scan.scan sv .i64 (B.size / 8).toUSize B).size / 8 by
          rw [scan_i64_size sv B hm, USize.toNat_ofNat_of_lt' hm]).symm.trans ((USize.toNat_ofNat_of_lt' hm).trans hBs)
      rw [hsz] at hS
      rw [Arr.toList_long S (by rw [hS]; exact longWords_answer _ hsz), scan_i64_words sv B hm, hL, List.map_map]
      exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)
    · cases h
  · have hsv : sv = .fills := by cases sv <;> first | rfl | simp at hfl
    subst hsv
    have hnn : holdsNull .long n R.enc = false := by
      cases hh : holdsNull .long n R.enc
      · rfl
      · rw [hh] at hfl; simp [Scan.Kind.hasNull] at hfl
    have hcol : scanColumn f .long .long n R.enc = some R.enc := by
      simp [scanColumn, scanWith, hf, hnn, Scan.Kind.hasNull, Scan.outKind, show scanKind .long = some .i64 from rfl]
    simp only [scan, hcol, Option.bind] at h
    simp only [Arr.of] at h
    split at h
    · have hS : S.enc = R.enc := by cases h; rfl
      rw [Arr.toList_long S (show longWords n S.enc = some ws by rw [hS]; exact hx), ← Arr.toList_long R hx]
      exact (Spec.scan_last_id _ (nul_free hx hn hnn)).symm
    · cases h

/-- **`f\x` over a float column** (`bytes` or `alp`) at `+ * & | ^`: the left fold the kernel runs,
    `Spec.scanBy` at q's NaN null and the verb's `Spec.fkern`, each accumulator written by `Spec.femit`;
    `Float` has no associativity to regroup it by. `^\` over a column with no NaN is the kernel's identity
    short-cut, the argument handed back: that it is the fold too needs `toBits ∘ ofBits = id`, which core's
    opaque `Float` does not state. Below `2³²` elements, the ALP encoder's exception-offset bound. -/
theorem scan_toList_float {f : Prim.Dyadic} {sv : Scan.Verb} (hf : scanVerb f = some sv)
    {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws)
    (hn : n < USize.size) (h32 : n < 2 ^ 32) {S : Arr .float n} (h : scan f .float R = some S) :
    S.toList = if (sv == .fills && !holdsNull .float n R.enc) = true then R.toList
      else (Spec.scanBy Scan.Kind.f64.isNull (Spec.fkern sv).1 (Spec.fkern sv).2 R.toList).map Spec.femit := by
  obtain ⟨B, hc, hBw, hBs⟩ := Arr.dense_float R hx hn
  have hm : B.size / 8 < USize.size := hBs ▸ hn
  have hk : Scan.outKind sv .f64 = .f64 := by cases sv <;> rfl
  have hL : R.toList = Verify.elemsW 8 B := by rw [Arr.toList_float R hx, hBw]
  cases hfl : (sv == .fills && !holdsNull .float n R.enc)
  · rw [if_neg Bool.false_ne_true]
    have hcol : scanColumn f .float .float n R.enc = some (Enc.answer .float (B.size / 8).toUSize.toNat
        (.bytes (Scan.scan sv .f64 (B.size / 8).toUSize B))) := by
      rcases hc with hc | ⟨md, pk, a, hc, rfl⟩ <;> rw [hc] at hfl ⊢
      · rw [← hBs] at hfl ⊢; simp [scanColumn, scanWith, hf, hk, hfl, show scanKind .float = some .f64 from rfl,
          show QAtomicType.width .float = some 8 from rfl, Enc.bytesOf, Scan.scanForm, Scan.Kind.hasNull]
        try simp only [show ¬ B.size < B.size / 8 * 8 from Nat.not_lt.2 (Nat.div_mul_le_self _ _), if_false]
        try exact Nat.div_mul_le_self _ _
      · rw [hBs]
        simp [scanColumn, scanWith, hf, hk, hfl, show scanKind .float = some .f64 from rfl,
          show QAtomicType.width .float = some 8 from rfl, Scan.scanForm, Scan.scanAlp, Scan.Kind.hasNull]
    simp only [scan, hcol, Option.bind] at h
    simp only [Arr.of] at h
    split at h
    · have hS : S.enc = Enc.answer .float (B.size / 8).toUSize.toNat
          (.bytes (Scan.scan sv .f64 (B.size / 8).toUSize B)) := by cases h; rfl
      rw [show (B.size / 8).toUSize.toNat = (Scan.scan sv .f64 (B.size / 8).toUSize B).size / 8 by
        rw [scan_f64_size sv B hm, USize.toNat_ofNat_of_lt' hm]] at hS
      have hsz : (Scan.scan sv .f64 (B.size / 8).toUSize B).size / 8 = n :=
        (show (B.size / 8).toUSize.toNat = (Scan.scan sv .f64 (B.size / 8).toUSize B).size / 8 by
          rw [scan_f64_size sv B hm, USize.toNat_ofNat_of_lt' hm]).symm.trans ((USize.toNat_ofNat_of_lt' hm).trans hBs)
      rw [hsz] at hS
      rw [Arr.toList_float S (by rw [hS]; exact floatWords_answer _ (by rw [hsz]; exact h32) hsz),
        scan_f64_words sv B hm, hL]
    · cases h
  · rw [if_pos rfl]
    have hsv : sv = .fills := by cases sv <;> first | rfl | simp at hfl
    subst hsv
    have hnn : holdsNull .float n R.enc = false := by simpa using hfl
    have hcol : scanColumn f .float .float n R.enc = some R.enc := by
      simp [scanColumn, scanWith, hf, hnn, Scan.Kind.hasNull, Scan.outKind, show scanKind .float = some .f64 from rfl]
    simp only [scan, hcol, Option.bind] at h
    simp only [Arr.of] at h
    split at h
    · have hS : S.enc = R.enc := by cases h; rfl
      rw [Arr.toList_float S (show floatWords n S.enc = some ws by rw [hS]; exact hx), ← Arr.toList_float R hx]
    · cases h

/-- `Coc.over` over a long `foR` column, at a verb that skips the null: `Spec.over` from `Over.seed`. -/
theorem over_foR {op : Coc.Over} (hb : op.boolCast = false) {n : Nat} {R : Arr .long n} {md pk : ByteArray}
    (hc : R.enc = .foR md pk) (hn : n < USize.size) :
    Coc.over op Spec.nul md pk n.toUSize = Spec.over op.step (op.seed Spec.nul) R.toList := by
  rw [Verify.over_eq, Verify.overList, hb, Verify.foldl_filter, toList_elems R hc hn, Coc.elems, List.map_map,
    Spec.over, List.foldl_map, List.foldl_map]
  congr 1; funext a x; by_cases hx : (Column.foRBits md pk (Column.blockStarts md) x).toInt64 = Spec.nul <;> simp [hx]

/-- **`f/x` over a long column** (`bytes` or `foR`), at a verb that skips the null: `Spec.over` at the
    kernel's step and `Over.seed`. -/
theorem over_long {op : Coc.Over} (hb : op.boolCast = false) {n : Nat} {R : Arr .long n} {ws : List UInt64}
    (hx : longWords n R.enc = some ws) (hn : n < USize.size) :
    over op R = some (Spec.over op.step (op.seed Spec.nul) R.toList) := by
  unfold longWords at hx
  cases hc : R.enc with
  | bytes b => rw [over_bytes hb hc, show op.denseSeed Ew.i64 Spec.nul = op.seed Spec.nul by cases op <;> rfl]
  | foR md pk =>
    have hcol : over op R = some (Coc.over op Spec.nul md pk n.toUSize) := by
      simp only [over, hc, overColumn, overFoR]; cases op <;> rfl
    rw [hcol, over_foR hb hc hn]
  | _ => all_goals (rw [hc] at hx; cases hx)

/-- **`avg x` over a dense long column**: `Spec.avg`, from `avgBits` at the long layout. -/
theorem avg_bytes {n : Nat} {R : Arr .long n} {b : ByteArray} (hc : R.enc = .bytes b) (hn : n < USize.size) :
    avg R = some (Spec.avg R.toList) := by
  have hbn : b.size / 8 = n := Arr.n_long_bytes R hc
  have hm : b.size / 8 < USize.size := hbn ▸ hn
  have hcol : avgColumn .long n R.enc = some (.float (Scan.avgBits .i64 (b.size / 8).toUSize b)) := by
    rw [hc]; rfl
  simp only [avg, hcol, Option.bind, Carrier.of?, Option.some.injEq]
  rw [Arr.toList_long_bytes R hc, List.map_map, ← hbn]
  unfold Scan.avgBits Spec.avg Spec.quot
  rw [USize.toNat_ofNat_of_lt' hm, show Scan.Kind.i64.avail b = b.size / 8 from rfl, Nat.min_self,
    ← List.countP_eq_length_filter, List.countP_map, Spec.over, List.foldl_map]
  rfl

/-- The nulls and the rest of a list make up its length. -/
theorem count_nul (xs : List Int64) :
    (xs.filter (· == Spec.nul)).length + (xs.filter (· != Spec.nul)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases hx : x = Spec.nul <;> simp [hx] <;> omega

/-- **`avg x` over a long column** (`bytes` or `foR`): `Spec.avg`, NaN made canonical. The `foR` path is
    `sum`'s fold `overFoR` over `liveFoR`'s count, `n` less `countLt` at `0N + 1`; it divides with no NaN
    guard, so the law reads the answer through `Spec.canon`. -/
theorem avg_long {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) {a : UInt64} (h : avg R = some a) : Spec.canon a = Spec.avg R.toList := by
  unfold longWords at hx
  cases hc : R.enc with
  | bytes b => rw [avg_bytes hc hn, Option.some.injEq] at h; rw [← h]; exact Spec.canon_quot _
  | foR md pk =>
    have hE := toList_elems R hc hn
    have hlen : (Coc.elems md pk n.toUSize).length = n := by
      simp [Coc.elems, USize.toNat_ofNat_of_lt' hn]
    have hcnt : (Coc.countLt md pk n.toUSize (Spec.nul + 1)).toNat = (R.toList.filter (· == Spec.nul)).length := by
      have hl : ((Coc.elems md pk n.toUSize).filter (·.toInt64 < Spec.nul + 1)).length < USize.size :=
        Nat.lt_of_le_of_lt (List.length_filter_le _ _) (by rw [hlen]; exact hn)
      rw [Coc.countLt, USize.toNat_ofNat_of_lt' hl, hE, List.filter_map, List.length_map]
      exact congrArg List.length (List.filter_congr fun u _ => by simpa using Spec.lt_nul_succ u.toInt64)
    have hlive : n - (Coc.countLt md pk n.toUSize (Spec.nul + 1)).toNat = (R.toList.filter (· != Spec.nul)).length := by
      have := count_nul R.toList
      rw [Arr.length_toList] at this; omega
    have ho : Coc.over .add Spec.nul md pk n.toUSize = Spec.over (· + ·) 0 R.toList := over_foR rfl hc hn
    have hcol : avgColumn .long n R.enc = some (.float (if (n - (Coc.countLt md pk n.toUSize (Spec.nul + 1)).toNat) == 0
        then QLean.nanBits else ((Coc.over .add Spec.nul md pk n.toUSize).toFloat /
          (n - (Coc.countLt md pk n.toUSize (Spec.nul + 1)).toNat).toFloat).toBits)) := by
      rw [hc]; rfl
    simp only [avg, hcol, Option.bind, Carrier.of?, Option.some.injEq] at h
    have e : a = (if (R.toList.filter (· != Spec.nul)).length == 0 then QLean.nanBits else
        ((Spec.over (· + ·) 0 R.toList).toFloat / ((R.toList.filter (· != Spec.nul)).length).toFloat).toBits) := by
      rw [← ho, ← hlive]; exact h.symm
    rw [e]
    exact Spec.canon_raw (Spec.over (· + ·) 0 R.toList, (R.toList.filter (· != Spec.nul)).length)
  | _ => all_goals (rw [hc] at hx; cases hx)

/-- `List.foldl` reads its step only on the list's members. -/
theorem foldl_congr_mem {α β : Type} {l : List α} {f g : β → α → β} (h : ∀ b, ∀ a ∈ l, f b a = g b a) :
    ∀ {b b' : β}, b = b' → l.foldl f b = l.foldl g b' := by
  induction l with
  | nil => intro b b' e; exact e
  | cons x l ih =>
    intro b b' e; subst e
    exact ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) (h b x (by simp))

/-- `laneSum` reads `live` and `f` only below `n`. -/
theorem laneSum_congr (lanes n : Nat) {live live' : Nat → Bool} {f f' : Nat → Float}
    (hl : ∀ i < n, live i = live' i) (hf : ∀ i < n, f i = f' i) :
    laneSum lanes n live f = laneSum lanes n live' f' := by
  have hs : ∀ (acc : Float) i, i < n → (if live i then acc + f i else acc) = (if live' i then acc + f' i else acc) :=
    fun acc i hi => by rw [hl i hi, hf i hi]
  dsimp only [laneSum]
  refine foldl_congr_mem (fun acc i hi => hs acc i ?_) (foldl_congr_mem (fun s j hj =>
    congrArg (s + ·) (foldl_congr_mem (fun acc i hi => hs acc _ ?_) rfl)) rfl)
  all_goals first
    | (simp only [List.mem_range'_1] at hi; omega)
    | (simp only [List.mem_range] at hi hj
       have h1 := Nat.mul_le_mul_right lanes (Nat.succ_le_of_lt hi)
       have h2 := Nat.div_mul_le_self n lanes
       rw [Nat.succ_mul] at h1; omega)

/-- `sumF64Total` reads its getter only below `n`. -/
theorem sumF64Total_congr (avg : Bool) (n : Nat) {f f' : Nat → Float} (h : ∀ i < n, f i = f' i) :
    sumF64Total avg n f = sumF64Total avg n f' := by
  have hl : ∀ i < n, (!Bits.f64IsNaN (f i).toBits) = !Bits.f64IsNaN (f' i).toBits := fun i hi => by rw [h i hi]
  have ha : ((List.range n).all fun i => !Bits.f64IsNaN (f i).toBits) =
      (List.range n).all fun i => !Bits.f64IsNaN (f' i).toBits :=
    Bool.eq_iff_iff.2 (by
      simp only [List.all_eq_true, List.mem_range]
      exact ⟨fun H i hi => by rw [← hl i hi]; exact H i hi, fun H i hi => by rw [hl i hi]; exact H i hi⟩)
  unfold sumF64Total; dsimp only; rw [ha]; exact laneSum_congr _ _ hl h

/-- A dense payload's total is `Spec.fsum` of its words. -/
theorem sumF64Total_words (avg : Bool) (B : ByteArray) :
    sumF64Total avg (B.size / 8) (atF64 B) = Spec.fsum avg (Verify.elemsW 8 B) := by
  unfold Spec.fsum
  rw [show (Verify.elemsW 8 B).length = B.size / 8 by simp [Verify.elemsW]]
  exact sumF64Total_congr _ _ fun i hi => by simp [atF64, Verify.elemsW, List.getD_eq_getElem?_getD, hi]

/-- **float `sum x` at every encoding** (`bytes` or `alp`): `Spec.fsum false` of the words — the dense
    `overF64 .add` and the ALP `alpSumF64 false` are both `sumF64Total false`. -/
theorem sum_float {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws)
    (hn : n < USize.size) : floatOver .add .float n R.enc = some (Spec.fsum false R.toList).toBits := by
  obtain ⟨B, hc, hBw, -⟩ := Arr.dense_float R hx hn
  rw [Arr.toList_float R hx, ← hBw, ← sumF64Total_words]
  rcases hc with hc | ⟨md, pk, a, hc, rfl⟩
  · rw [hc]; rfl
  · rw [hc]; rfl

/-- **float `avg x` at every encoding** (`bytes` or `alp`): `Spec.favg` of the words. The ALP path counts
    `alpLive`, `n` less the NaN exceptions, the decoded words' non-NaN count on a well-formed ALP blob
    (`Verify.alpLive_eq_countP`); `alpEncode64` writes one (`Verify.alpWF_alpEncode64`). -/
theorem avg_float {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws)
    (hn : n < USize.size) (hwf : ∀ md pk a, R.enc = .alp md pk a → Verify.AlpWF md pk a n) :
    avg R = some (Spec.favg R.toList) := by
  obtain ⟨B, hc, hBw, hBs⟩ := Arr.dense_float R hx hn
  have hL : R.toList = Verify.elemsW 8 B := by rw [Arr.toList_float R hx, hBw]
  rcases hc with hc | ⟨md, pk, a, hc, rfl⟩
  · have hm : B.size / 8 < USize.size := hBs ▸ hn
    have hcol : avgColumn .float n R.enc = some (QAtom.float (Spec.favg (Verify.elemsW 8 B))) := by
      rw [hc, Spec.favg, ← sumF64Total_words]
      show some (QAtom.float (Scan.avgBits .f64 (B.size / 8).toUSize B)) = _
      unfold Scan.avgBits
      rw [USize.toNat_ofNat_of_lt' hm, show Scan.Kind.f64.avail B = B.size / 8 from rfl, Nat.min_self,
        Verify.elemsW, List.countP_map]
      rfl
    simp only [avg, hcol, Option.bind, Carrier.of?, hL]
  · have hcol : avgColumn .float n R.enc = some (QAtom.float (if alpLive a n == 0 then QLean.nanBits else
        Spec.canon (alpSumF64 true md pk a n.toUSize / (alpLive a n).toFloat).toBits)) := by
      rw [hc]; rfl
    simp only [avg, hcol, Option.bind, Carrier.of?]
    have hR : R.toList = (List.range n).map (Column.alpBits md pk a (Column.blockStarts md)) := by
      have h := hx; unfold floatWords at h; rw [hc] at h; rw [Arr.toList_float R hx]; exact (Option.some.inj h).symm
    rw [Verify.alpLive_eq_countP (hwf md pk a hc), ← hR, hL, Spec.favg, ← sumF64Total_words]
    rfl

/-- The window `[i+1-w, i]` of `til m` mapped, `i < m`. -/
theorem window_range_map {α : Type} (g : Nat → α) (w : Nat) {i m : Nat} (hi : i < m) :
    (((List.range m).map g).take (i + 1)).drop (i + 1 - w) = (List.range' (i + 1 - w) (min w (i + 1))).map g :=
  List.ext_getElem (by simp; omega) fun j h1 h2 => by simp [List.getElem_range']; try omega

/-- A long answer column, dense or encoded, lists its payload's eight-byte words: `longWords_answer`. -/
theorem toList_answer_long {m : Nat} (x : Arr .long m) {b : ByteArray} (hm : b.size / 8 = m)
    (hc : x.enc = Enc.answer .long m (.bytes b)) :
    x.toList = (List.range m).map fun i => (Column.bitsAt b (i * 8) 8).toInt64 := by
  have hL : longWords m x.enc = some (Verify.elemsW 8 b) := by rw [hc]; exact longWords_answer _ hm
  exact toList_words x hL rfl hm

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
    {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws) (hn : n < USize.size) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = n ∧ ∀ v, v < USize.size → mwinColumn op .long v n R.enc =
      if v < 1 then none else some (rt, Enc.answer rt (n) (.bytes (Scan.mwinBits op .i64 v n B))) := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R hx hn
  refine ⟨B, hBw, hBs, fun v hv => ?_⟩
  have hn' : n % 2 ^ System.Platform.numBits = n := Nat.mod_eq_of_lt hn
  have hv' : v % 2 ^ System.Platform.numBits = v := Nat.mod_eq_of_lt hv
  rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc] <;> by_cases h1 : v < 1 <;>
    simp [mwinColumn, h1, hT, hk, hr, hwd, show scanKind .long = some .i64 from rfl,
      show QAtomicType.width .long = some 8 from rfl, show Scan.Kind.width .i64 = 8 from rfl, Enc.bytesOf,
      Scan.mwinFoR, Scan.mwin, hBs, hn', USize.toNat_ofNat_of_lt' hv, USize.toNat_ofNat_of_lt' hn] <;>
    first | rfl | exact ⟨_, ⟨by omega, rfl⟩, rfl⟩

/-- `mwinColumn` over a float column that lists `floatWords`, at a verb that reads it as `f64` and writes
    `rt`'s width: `mwinBits` over the dense payload `Arr.dense_float` names, `bytes` or `alp`. -/
theorem mwin_float {op : Scan.MOp} {rt : QAtomicType} {rk : Scan.Kind} (hT : mwinType op .float = some rt)
    (hk : op.readKind .f64 = .f64) (hr : scanKind rt = some rk) (hwd : op.width .f64 = rk.width)
    {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws) (hn : n < USize.size) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = n ∧ ∀ v, v < USize.size → mwinColumn op .float v n R.enc =
      if v < 1 then none else some (rt, Enc.answer rt (n) (.bytes (Scan.mwinBits op .f64 v n B))) := by
  obtain ⟨B, hc, hBw, hBs⟩ := Arr.dense_float R hx hn
  refine ⟨B, hBw, hBs, fun v hv => ?_⟩
  have hn' : n % 2 ^ System.Platform.numBits = n := Nat.mod_eq_of_lt hn
  have hv' : v % 2 ^ System.Platform.numBits = v := Nat.mod_eq_of_lt hv
  rcases hc with hc | ⟨md, pk, a, hc, hB⟩ <;> rw [hc]
  · by_cases h1 : v < 1 <;>
      simp [mwinColumn, h1, hT, hk, hr, hwd, show scanKind .float = some .f64 from rfl,
        show QAtomicType.width .float = some 8 from rfl, Enc.bytesOf, Scan.mwin, hBs, hn',
        USize.toNat_ofNat_of_lt' hv] <;> first | rfl | exact ⟨_, ⟨by omega, rfl⟩, rfl⟩
  · simp only [mwinColumn, hT, hk, hr, show scanKind .float = some .f64 from rfl,
      show QAtomicType.width .float = some 8 from rfl, Option.map_some]
    by_cases h1 : v < 1
    · rw [if_pos (by simp [h1]), if_pos h1]
    · rw [if_neg (by simp [h1, hwd]), if_neg h1, hB]
      unfold Scan.mwinAlp Scan.mwin; rw [USize.toNat_ofNat_of_lt' hv, USize.toNat_ofNat_of_lt' hn]

/-- An answer of `w mop x` from a column whose `mwinColumn` is `mwinBits` over a dense payload `B` (as
    `mwin_long` and `mwin_float` state): `w ≥ 1`, and `Column.answer` of `mwinBits` over `B`. -/
theorem mwin_answer_of {op : Scan.MOp} {t rt : QAtomicType} {k : Scan.Kind} {w : Nat} (hw : w < USize.size)
    {n : Nat} {R : Arr t n} {B : ByteArray} (hd : ∀ v, v < USize.size → mwinColumn op t v n R.enc =
      if v < 1 then none else some (rt, Enc.answer rt (n) (.bytes (Scan.mwinBits op k v n B))))
    {S : Arr rt n} (h : mwin op w rt R = some S) :
    0 < w ∧ S.enc = Enc.answer rt (n) (.bytes (Scan.mwinBits op k w n B)) := by
  have hw1 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h0
    · simp [mwin, hd 0 (by rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e])] at h
    · exact h0
  refine ⟨hw1, ?_⟩
  simp only [mwin, hd w hw, show ¬ w < 1 by omega, if_false, Option.bind, if_true] at h
  generalize Enc.answer rt (n) (.bytes (Scan.mwinBits op k w n B)) = A at h ⊢
  simp only [Arr.of] at h
  split at h
  · rename_i hw
    cases h
    rfl
  · rename_i hw
    cases h

/-- An answer of `w mop x` over a long column, at such a verb: `w ≥ 1`, the key's count, and `Column.answer`
    of `mwinBits` over the dense payload. -/
theorem mwin_answer {op : Scan.MOp} {rt : QAtomicType} {rk : Scan.Kind} (hT : mwinType op .long = some rt)
    (hk : op.readKind .i64 = .i64) (hr : scanKind rt = some rk) (hwd : op.width .i64 = rk.width)
    {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) {S : Arr rt n} (h : mwin op w rt R = some S) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = n ∧ 0 < w ∧
      S.enc = Enc.answer rt (n) (.bytes (Scan.mwinBits op .i64 w n B)) := by
  obtain ⟨B, hBw, hBs, hd⟩ := mwin_long hT hk hr hwd hx hn
  exact ⟨B, hBw, hBs, mwin_answer_of hw hd h⟩

/-- **`<x` / `>x` over a long column**: q's stable grade, from `Order.grade`'s merge sort of `til n`
    (`ids_indices`) under `rank_i64_le_iff`. -/
theorem grade_toList {desc : Bool} {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) : (grade desc R).toList = Spec.grade desc R.toList := by
  obtain ⟨B, hc, -, hBw, hBs⟩ := Arr.dense_long R hx hn
  have hg : gradeColumn .long desc n R.enc = some (.bytes (Order.grade .i64 desc n.toUSize B)) := by
    rcases hc with hc | ⟨md, pk, hc, rfl⟩ <;> rw [hc]
    · rw [← hBs]; simp [gradeColumn, Enc.bytesOf, show orderKind .long = some .i64 from rfl, show Scan.Kind.width .i64 = 8 from rfl, Nat.not_lt.2 (Nat.div_mul_le_self _ _)]
    · rfl
  have hS : (grade desc R).enc = .bytes (Order.grade .i64 desc n.toUSize B) := by
    unfold grade; rw [dif_pos ⟨hn, by decide⟩]; exact Option.some.inj ((Option.some_get _).trans hg)
  generalize hP : Order.grade .i64 desc n.toUSize B = P at hS
  generalize grade desc R = S at hS ⊢
  · have hm : min n.toUSize.toNat (Scan.Kind.i64.avail B) = n := by
      rw [USize.toNat_ofNat_of_lt' hn, show Scan.Kind.i64.avail B = B.size / 8 from rfl, hBs, Nat.min_self]
    have hids : Verify.ids P = (List.range n).mergeSort fun i j =>
        if desc then Order.keyAt .i64 B j ≤ Order.keyAt .i64 B i else Order.keyAt .i64 B i ≤ Order.keyAt .i64 B j := by
      rw [← hP, Order.grade, hm]
      exact Verify.ids_indices _ fun i hi =>
        Nat.lt_of_lt_of_le (Nat.lt_trans (List.mem_range.1 ((List.mergeSort_perm _ _).mem_iff.1 hi)) hn)
          (by rcases System.Platform.numBits_eq with e | e <;> simp [USize.size, e])
    have e1 : S.toList = (Verify.ids P).map Int64.ofNat := by
      rw [Arr.toList_long_bytes _ hS, Verify.ids, Arr.n_long_bytes _ hS, List.map_map, List.map_map]
      exact List.map_congr_left fun i _ => toInt64_of_toNat rfl
    have hxs := toList_words R hx hBw hBs
    rw [e1, hids, Spec.grade, Arr.length_toList]
    congr 1
    have := List.map_mergeSort (f := id) (l := List.range n) (r := fun i j =>
        if desc then Order.keyAt .i64 B j ≤ Order.keyAt .i64 B i else Order.keyAt .i64 B i ≤ Order.keyAt .i64 B j)
      (s := fun i j => if desc then decide (R.toList[j]! ≤ R.toList[i]!)
        else decide (R.toList[i]! ≤ R.toList[j]!)) fun i hi j hj => by
      have hi' := List.mem_range.1 hi
      have hj' := List.mem_range.1 hj
      simp only [id, hxs]
      cases desc <;> simp [Order.keyAt, Scan.Kind.bitsAt, Scan.Kind.width, rank_i64_le_iff, List.getElem?_range hi',
        List.getElem?_range hj']
    simpa using this

/-- **`asc x` / `desc x` over a long column**: q's stable sort, from `sortValues_spec` under
    `rank_i64_le_iff`. -/
theorem sort_toList {desc : Bool} {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) : (sort desc R).toList = Spec.sort desc R.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long R hx hn
  have hsv : sortedValues .long desc n R.enc =
      some (.bytes (Order.sortValues .i64 desc (B.size / 8).toUSize B)) := by
    simp only [sortedValues, hb]; rw [← hBs]; simp [show orderKind .long = some .i64 from rfl, show Scan.Kind.width .i64 = 8 from rfl, Nat.not_lt.2 (Nat.div_mul_le_self _ _)]
  -- `sortValues` pushes one word per grade entry, and the grade has the `n` entries `elemsW` reads back
  have hm : (Order.sortValues .i64 desc (B.size / 8).toUSize B).size =
      (Order.grade .i64 desc (B.size / 8).toUSize B).size / 8 * 8 := by
    unfold Order.sortValues; exact foldl_push_size _ 8 (by decide) _
  generalize hP : Order.sortValues .i64 desc (B.size / 8).toUSize B = P at hsv hm
  have hs := Verify.sortValues_spec .i64 desc (B.size / 8).toUSize B
  rw [hP, USize.toNat_ofNat_of_lt' (by rw [hBs]; exact hn), show Scan.Kind.i64.avail B = B.size / 8 from rfl,
    Nat.min_self, show (List.range (B.size / 8)).map (Scan.Kind.i64.bitsAt B) = Verify.elemsW 8 B from rfl,
    show Scan.Kind.i64.width = 8 from rfl] at hs
  have hl := congrArg List.length hs
  simp only [Verify.elemsW, List.length_map, List.length_range, List.length_mergeSort] at hl
  rw [hBw] at hs
  have hS : (sort desc R).enc = .bytes P := by
    simp only [sort, hsv, Option.orElse, Find.orElse,
      dif_pos (KernelWF.wf_bytes (t := .long) (w := 8) (by decide) rfl (show P.size = n * 8 by omega))]
    exact Arr.markIf_enc ..
  rw [Arr.toList_long _ (show longWords n (sort desc R).enc = some (Verify.elemsW 8 P) by rw [hS]; rfl), hs,
    Arr.toList_long R hx, Spec.sort]
  exact List.map_mergeSort fun a _ b _ => by cases desc <;> simp [rank_i64_le_iff]

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

/-- **The extremes' window engine over eight-byte words**, at any `keep` and seed: the words `mwinExt`
    writes are `Spec.mext keep seed` of the payload's words, each window folded oldest first as the kernel
    folds it. No order on the words is asked for, so it holds at `Float`'s IEEE comparison too. -/
theorem mwinExt_words (keep : UInt64 → UInt64 → Bool) (seed : UInt64) (b : ByteArray) {w : Nat} (hw : 0 < w) :
    Verify.elemsW 8 (Scan.mwinExt keep seed (fun j => Column.bitsAt b (j * 8) 8) w (b.size / 8) 8)
      = Spec.mext keep seed w (Verify.elemsW 8 b) := by
  rw [Scan.mwinExt, Verify.elemsW_foldl_mod _ 8 (by decide) (by decide), Spec.mext, Verify.elemsW, List.length_map,
    List.length_range]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [show 8 * 8 = 64 from rfl, Verify.ofNat_toNat_mod64]
  dsimp only
  rw [window_range_map _ w hi]
  by_cases h : i + 1 < w
  · simp only [h, if_true, show i + 1 - w = 0 by omega, Nat.sub_zero, show min w (i + 1) = i + 1 by omega]
  · simp only [h, if_false, show min w (i + 1) = (w - 1) + 1 by omega, List.range'_succ, List.map_cons,
      show i + 1 - (i + 1 - w + 1) = w - 1 by omega]

/-- `w mmin x` / `w mmax x` over a long column, at the order `f` the kernel's `better` is strictness of,
    `sp` its reading on longs and `seed` the each-prior seed read as a long. -/
theorem mext_toList {op : Scan.MOp} (hop : op = .mmin ∨ op = .mmax) (f : UInt64 → Int) (sp : Int64 → Int64 → Bool)
    (seed : Int64) (hk : op.better .i64 = fun u e => decide (f u < f e))
    (hsp : ∀ a b : UInt64, sp a.toInt64 b.toInt64 = decide (f a < f b)) (hs : (op.seed .i64).toInt64 = seed)
    {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64} (hx : longWords n R.enc = some ws)
    (hn : n < USize.size) {S : Arr .long n} (h : mwin op w .long R = some S) :
    S.toList = Spec.mext sp seed w R.toList := by
  obtain ⟨B, hBw, hBs, hw1, hS⟩ := mwin_answer (rk := .i64) (by rcases hop with rfl | rfl <;> rfl)
    (by rcases hop with rfl | rfl <;> rfl) rfl (by rcases hop with rfl | rfl <;> rfl) hw hx hn h
  have hE : Scan.mwinBits op .i64 w n B =
      Scan.mwinExt (fun u e => decide (f u < f e)) (op.seed .i64) (fun j => Column.bitsAt B (j * 8) 8) w n 8 := by
    have e : Scan.mwinBits op .i64 w n B = Scan.mwinExt (op.better .i64) (op.seed .i64) (Scan.Kind.i64.bitsAt B) w
        (min n (Scan.Kind.i64.avail B)) 8 := by rcases hop with rfl | rfl <;> rfl
    rw [e, hk, show Scan.Kind.i64.avail B = n from hBs, Nat.min_self]; rfl
  have hm : (Scan.mwinBits op .i64 w n B).size / 8 = n := by
    rw [hE, Scan.mwinExt, foldl_push_size _ 8 (by decide), Nat.mul_div_cancel _ (by decide)]
  rw [toList_answer_long S hm hS, toList_words R hx hBw hBs, ← hs, hE, mext_words f sp hsp _ _ w n hw1]

/-- **`w mmin x` over a long column**: q's `(w-1)&':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `0W`. -/
theorem mmin_toList {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64}
    (hx : longWords n R.enc = some ws) (hn : n < USize.size) {S : Arr .long n}
    (h : mwin .mmin w .long R = some S) : S.toList = Spec.mext (· < ·) Int64.maxValue w R.toList :=
  mext_toList (.inl rfl) (fun u => u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt])
    (fun a b => by simp [Int64.lt_iff_toInt_lt]) rfl hw hx hn h

/-- **`w mmax x` over a long column**: q's `(w-1)|':/x`, a tie keeping the older, the first `w-1` windows
    holding the seed `-0W`. -/
theorem mmax_toList {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64}
    (hx : longWords n R.enc = some ws) (hn : n < USize.size) {S : Arr .long n}
    (h : mwin .mmax w .long R = some S) : S.toList = Spec.mext (· > ·) (-Int64.maxValue) w R.toList :=
  mext_toList (.inr rfl) (fun u => -u.toInt64.toInt) _ _
    (by funext u e; simp [Scan.MOp.better, Scan.Kind.signed, Int64.lt_iff_toInt_lt,
      show (Scan.MOp.mmax == Scan.MOp.mmin) = false from rfl] <;> omega)
    (fun a b => by simp [Int64.lt_iff_toInt_lt] <;> omega) rfl hw hx hn h

/-- **`w mmin x` / `w mmax x` over a float column** (`bytes` or `alp`): each window folded oldest first
    under the kernel's own `better` (q's order, NaN the smallest for `&` and ignored by `|`), the first
    `w-1` windows holding the seed `0w`/`-0w`. `Float`'s comparison is opaque, so the law keeps the
    kernel's comparison of the bits rather than an order on reals. -/
theorem mext_toList_float {op : Scan.MOp} (hop : op = .mmin ∨ op = .mmax) {w : Nat} (hw : w < USize.size)
    {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws) (hn : n < USize.size)
    (h32 : n < 2 ^ 32) {S : Arr .float n} (h : mwin op w .float R = some S) :
    S.toList = Spec.mext (op.better .f64) (op.seed .f64) w R.toList := by
  obtain ⟨B, hBw, hBs, hd⟩ := mwin_float (op := op) (rt := .float) (rk := .f64) (by rcases hop with rfl | rfl <;> rfl)
    (by rcases hop with rfl | rfl <;> rfl) rfl (by rcases hop with rfl | rfl <;> rfl) hx hn
  obtain ⟨hw1, hS⟩ := mwin_answer_of hw hd h
  have hE : Scan.mwinBits op .f64 w n B =
      Scan.mwinExt (op.better .f64) (op.seed .f64) (fun j => Column.bitsAt B (j * 8) 8) w (B.size / 8) 8 := by
    have e : Scan.mwinBits op .f64 w n B = Scan.mwinExt (op.better .f64) (op.seed .f64) (Scan.Kind.f64.bitsAt B) w
        (min n (Scan.Kind.f64.avail B)) 8 := by rcases hop with rfl | rfl <;> rfl
    rw [e, show Scan.Kind.f64.avail B = n from hBs, Nat.min_self, hBs]; rfl
  have hsz : (Scan.mwinBits op .f64 w n B).size / 8 = n := by
    rw [hE, Scan.mwinExt, foldl_push_size _ 8 (by decide), Nat.mul_div_cancel _ (by decide), hBs]
  rw [Arr.toList_float S (by rw [hS]; exact floatWords_answer _ (by rw [hsz]; exact h32) hsz), hE,
    mwinExt_words _ _ B hw1, hBw, ← Arr.toList_float R hx]

/-- **`w msum x` over a long column**: q's `{y-(-x)_(0i*x#y),y:+\y}`, from `msum_i64_spec` over `mwinSum`,
    the integral engine `mwinBits` runs `msum` at `long` on. -/
theorem msum_toList {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64}
    (hx : longWords n R.enc = some ws) (hn : n < USize.size) {S : Arr .long n}
    (h : mwin .msum w .long R = some S) : S.toList = Spec.msum w R.toList := by
  obtain ⟨B, hBw, hBs, -, hS⟩ := mwin_answer (rk := .i64) rfl rfl rfl rfl hw hx hn h
  have hM : Scan.mwinBits .msum .i64 w n B = Scan.mwinSum (some Int64.minValue) (fun s => (Scan.narrow 8 s).toInt64)
      (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else Scan.Kind.i64.signed (Scan.Kind.i64.bitsAt B j))
      w n 8 := by
    have e : Scan.mwinBits .msum .i64 w n B = Scan.mwinSum (some Int64.minValue) (fun s => (Scan.narrow 8 s).toInt64)
        (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else Scan.Kind.i64.signed (Scan.Kind.i64.bitsAt B j))
        w (min n (Scan.Kind.i64.avail B)) 8 := rfl
    rw [e, show Scan.Kind.i64.avail B = n from hBs, Nat.min_self]
  have hm : (Scan.mwinBits .msum .i64 w n B).size / 8 = n := by
    rw [hM, Scan.mwinSum, foldl_push_size _ 8 (by decide), Nat.mul_div_cancel _ (by decide)]
  have hL : S.toList = (Verify.elemsW 8 (Scan.mwinBits .msum .i64 w n B)).map UInt64.toInt64 :=
    Arr.toList_long S (by rw [hS]; exact longWords_answer _ hm)
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [hL, List.getElem?_map, hM, Verify.msum_i64_spec B w n i hi, toList_words R hx hBw hBs]
    simp only [Spec.msum, List.length_map, List.length_range, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      List.map_map]
    rw [window_range_map _ w hi]
    simp only [take_range_map _ (show i + 1 ≤ n by omega), take_range_map _ (show i + 1 - w ≤ n by omega),
      List.foldl_map, Function.comp_def, beq_iff_eq, Bool.or_eq_true, Option.some.injEq]
    split <;> simp [Spec.nul]
  · have hl : (Spec.msum w R.toList).length = n := by
      simp only [Spec.msum, List.length_map, List.length_range]; exact Arr.length_toList _
    rw [List.getElem?_eq_none (by rw [Arr.length_toList]; omega), List.getElem?_eq_none (by omega)]

/-- **`w mcount x` over a long column**: how many of each window are not `0N`, at `int`, from `mcount_spec`
    over `mwinSum`. -/
theorem mcount_toList {w : Nat} (hw : w < USize.size) {n : Nat} {R : Arr .long n} {ws : List UInt64}
    (hx : longWords n R.enc = some ws) (hn : n < USize.size) {S : Arr .int n}
    (h : mwin .mcount w .int R = some S) : S.toList = Spec.mcount w R.toList := by
  obtain ⟨B, hBw, hBs, -, hS⟩ := mwin_answer (rk := .i32) rfl rfl rfl rfl hw hx hn h
  have hM : Scan.mwinBits .mcount .i64 w n B =
      Scan.mwinSum none id (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else 1) w n 4 := by
    have e : Scan.mwinBits .mcount .i64 w n B = Scan.mwinSum none id
        (fun j => if Scan.Kind.i64.isNull (Scan.Kind.i64.bitsAt B j) then 0 else 1) w (min n (Scan.Kind.i64.avail B)) 4 := rfl
    rw [e, show Scan.Kind.i64.avail B = n from hBs, Nat.min_self]
  have hm : (Scan.mwinBits .mcount .i64 w n B).size / 4 = n := by
    rw [hM, Scan.mwinSum, foldl_push_size _ 4 (by decide), Nat.mul_div_cancel _ (by decide)]
  rw [toList_answer_int S hm hS, hM, toList_words R hx hBw hBs, Spec.mcount, List.length_map, List.length_range]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [show i * 4 = 4 * i from Nat.mul_comm _ _, Verify.mcount_spec .i64 B w n i hi, window_range_map _ w hi,
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
theorem map_get! {g : Nat} (o : Arr .long (g+1)) {m : Nat} (hm : m ≤ g) :
    (o.toList.map Int64.toNatClampNeg)[m]! = (o.toList[m]!).toNatClampNeg := by
  rw [getElem!_pos _ m (by rw [List.length_map, Arr.length_toList]; omega),
    getElem!_pos o.toList m (by rw [Arr.length_toList]; omega), List.getElem_map]

/-- Word `m` of the dense offsets `B` is offset `m`. -/
theorem offs_word {g : Nat} {o : Arr .long (g+1)} {B : ByteArray}
    (hB : o.toList = (List.range (g+1)).map fun i => (Column.bitsAt B (i*8) 8).toInt64) {m : Nat} (hm : m < g + 1) :
    (Column.bitsAt B (m*8) 8).toInt64 = o.toList[m]! := by
  rw [hB, getElem!_pos _ m (by simpa using hm)]; simp

/-- Under `Cuts`, `sizes` lists each group's size `o[j+1] − o[j]`: no offset is `0N`, so `Ew.sub`'s null
    test never fires, and both lie in `[0, n]`, so the difference does not wrap. -/
theorem sizes_words {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) {B : ByteArray}
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
theorem countBy_toList {v : QAtomicType} {n g : Nat} {o : Arr .long (g+1)} {co : Cuts o n}
    {x : Arr v n} {wo : List UInt64} (ho : longWords (g+1) o.enc = some wo) (hg : g + 1 < USize.size) :
    (countBy ⟨g, n, o, co, x⟩).toList = Spec.countBy (o.toList.map Int64.toNatClampNeg) x.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long o ho hg
  have hd : denseOf o = B := denseOf_eq hb
  have hS : (countBy ⟨g, n, o, co, x⟩).enc = .bytes (sizes g B) := by
    simp only [countBy, dif_pos (show g < USize.size by omega), hd]; rfl
  · rw [Arr.toList_long _ (show longWords g (countBy ⟨g, n, o, co, x⟩).enc = some (Verify.elemsW 8 (sizes g B)) by rw [hS]; rfl),
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

/-- **`last each` by group over a long column**: the last row of each group. An answer means no group
    is empty — `lastBy` reads that off `min` of the sizes, here `over_bytes` and `over_lesser_le` — so
    `o[j+1] − 1` names a row of group `j`. A `foR` value column reaches `gatherFoR`, which is `gatherBytes`
    over the decode `Arr.dense_long` names. -/
theorem lastBy_toList {n g : Nat} {o : Arr .long (g+1)} {co : Cuts o n}
    {x : Arr .long n} {wo wx : List UInt64} (ho : longWords (g+1) o.enc = some wo)
    (hx : longWords n x.enc = some wx) (hg : g + 1 < USize.size) (hn : n < USize.size)
    (hne : ∀ j : Fin g, o.get j.castSucc < o.get j.succ) :
    (lastBy ⟨g, n, o, co, x⟩ hne).toList = Spec.lastBy (o.toList.map Int64.toNatClampNeg) x.toList := by
  obtain ⟨B, -, hb, hBw, hBs⟩ := Arr.dense_long o ho hg
  have hdo : denseOf o = B := denseOf_eq hb
  have hB := toList_words o ho hBw hBs
  -- every group holds a row: `hne` read at the offsets, which `Cuts` keeps in `[0, n]`
  have hpos : ∀ j, j < g → (o.toList[j]!).toNatClampNeg < (o.toList[j+1]!).toNatClampNeg := by
    intro j hj
    obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
    have c0 := toNat_cast a0
    have c1 := toNat_cast (Int.le_trans a0 a1)
    have e0 : o.toList[j]! = o.get ⟨j, by omega⟩ := by
      rw [getElem!_pos o.toList j (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
    have e1 : o.toList[j+1]! = o.get ⟨j+1, by omega⟩ := by
      rw [getElem!_pos o.toList (j+1) (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
    have hl : (o.toList[j]!).toInt < (o.toList[j+1]!).toInt := by
      rw [e0, e1]; exact Int64.lt_iff_toInt_lt.1 (hne ⟨j, hj⟩)
    omega
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hlw := Verify.val_i64_va Ew.add Int64.minValue (ends g B) ((-1 : Int64).toUInt64) g (by omega)
  change Verify.elemsW 8 (lasts g B) = _ at hlw
  have hlz := lasts_size (g := g) B (by omega)
  obtain ⟨b, hxc, -, hbw, hbn⟩ := Arr.dense_long x hx hn
  have hgc : gatherColumn .long n x.enc ((lasts g (denseOf o)).size / 8) (.bytes (lasts g (denseOf o))) =
      some (.bytes (gatherBytes (8 : Nat).toUSize 0x8000000000000000 b (lasts g B))) := by
    rw [hdo, hlz]
    generalize lasts g B = L at hlz
    have hL : ¬ L.size < g * 8 := by rw [← hlz]; exact Nat.not_lt.2 (Nat.div_mul_le_self _ _)
    rcases hxc with hxc | ⟨md, pk, hxc, rfl⟩ <;> rw [hxc]
    · rw [← hbn]; simp [gatherColumn, foRColumn, Enc.bytesOf, hL, Nat.not_lt.2 (Nat.div_mul_le_self _ _)] <;> rfl
    · cases hm : md.isEmpty <;> simp [gatherColumn, foRColumn, Enc.bytesOf, hm, hL] <;> rfl
  have hS : (lastBy ⟨g, n, o, co, x⟩ hne).enc = .bytes (gatherBytes (8 : Nat).toUSize 0x8000000000000000 b (lasts g B)) := by
    simp only [lastBy, dif_pos (show QAtomicType.long ≠ .general ∧ g < USize.size from ⟨by decide, by omega⟩)]
    exact Option.some.inj ((Option.some_get _).trans hgc)
  generalize lasts g B = L at hS hlw hlz
  obtain ⟨-, hgj⟩ := Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8) 0x8000000000000000 b L
  rw [h8] at hgj
  generalize gatherBytes (8 : Nat).toUSize 0x8000000000000000 b L = G at hS hgj
  · rw [Arr.toList_long_bytes _ hS, Spec.lastBy, Spec.groups_range, List.length_map, Arr.length_toList,
      Nat.add_sub_cancel, List.map_map, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj : j < g := List.mem_range.1 hj
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

/-- The state of `mwinBits`' first float pass, in the order its `MProd` keeps it: the four totals `a`, and
    the array `A` of the totals after each element. -/
abbrev mst (a : Float × Float × Float × Int64) (A : Array (Float × Float × Float × Int64)) :
    MProd Int64 (MProd Float (MProd Float (MProd Float (Array (Float × Float × Float × Int64))))) :=
  ⟨a.2.2.2, a.2.1, a.1, a.2.2.1, A⟩

/-- Any pass whose step is `mstep` on the totals and a push of the new totals leaves the prefix fold and,
    pushed after `A`, the totals after each element. -/
theorem mloop (rd : Nat → UInt64) {F : MProd Int64 (MProd Float (MProd Float (MProd Float
      (Array (Float × Float × Float × Int64))))) → Nat → MProd Int64 (MProd Float (MProd Float (MProd Float
      (Array (Float × Float × Float × Int64)))))}
    (hF : ∀ a A i, F (mst a A) i = mst (Spec.mstep a (rd i)) (A.push (Spec.mstep a (rd i)))) :
    ∀ (l : List Nat) a A, l.foldl F (mst a A) =
      mst ((l.map rd).foldl Spec.mstep a) (A ++ (Spec.scanl Spec.mstep a (l.map rd)).tail.toArray)
  | [], a, A => by simp [Spec.scanl]
  | i :: l, a, A => by
    have e : Spec.scanl Spec.mstep (Spec.mstep a (rd i)) (l.map rd) =
        Spec.mstep a (rd i) :: (Spec.scanl Spec.mstep (Spec.mstep a (rd i)) (l.map rd)).tail := by cases l <;> rfl
    rw [List.foldl_cons, hF, mloop rd hF l, List.map_cons, List.foldl_cons, Spec.scanl, List.tail_cons, e]
    simp

/-- `mloop` from the zero totals and an empty array, as `mwinBits` starts it. -/
theorem mloop0 (rd : Nat → UInt64) {F : MProd Int64 (MProd Float (MProd Float (MProd Float
      (Array (Float × Float × Float × Int64))))) → Nat → MProd Int64 (MProd Float (MProd Float (MProd Float
      (Array (Float × Float × Float × Int64)))))}
    (hF : ∀ a A i, F (mst a A) i = mst (Spec.mstep a (rd i)) (A.push (Spec.mstep a (rd i)))) (l : List Nat) (c : Nat) :
    l.foldl F ⟨0, 0.0, 0.0, 0.0, Array.emptyWithCapacity c⟩ =
      mst ((l.map rd).foldl Spec.mstep (0.0, 0.0, 0.0, 0)) (Spec.scanl Spec.mstep (0.0, 0.0, 0.0, 0) (l.map rd)).tail.toArray := by
  have := mloop rd hF l (0.0, 0.0, 0.0, 0) #[]
  simpa using this

/-- **`w msum/mavg/mdev x` over a dense `f64` payload**: `mwinBits`' two passes are the prefix fold `mstep`
    then, at each `i`, `memit` of the totals after `i+1` and after `i+1−w` elements. -/
theorem mwinBits_mfloat {op : Scan.MOp} (hop : op = .msum ∨ op = .mavg ∨ op = .mdev) (w : Nat) (B : ByteArray) :
    Scan.mwinBits op .f64 w (B.size / 8) B = (List.range (B.size / 8)).foldl (fun out i => Column.pushBits out
      (Spec.memit op (((List.range (i+1)).map (Scan.Kind.f64.bitsAt B)).foldl Spec.mstep (0.0, 0.0, 0.0, 0))
        (((List.range (i+1-w)).map (Scan.Kind.f64.bitsAt B)).foldl Spec.mstep (0.0, 0.0, 0.0, 0))) 8)
      ByteArray.empty := by
  have hm : min (B.size / 8) (Scan.Kind.f64.avail B) = B.size / 8 := by
    rw [show Scan.Kind.f64.avail B = B.size / 8 from rfl, Nat.min_self]
  have hP : ∀ j, j ≤ B.size / 8 → ((List.range' 0 (B.size / 8)).map (Scan.Kind.f64.bitsAt B)).take j =
      (List.range j).map (Scan.Kind.f64.bitsAt B) := fun j hj => by
    rw [← List.range_eq_range', ← List.map_take, List.take_range, Nat.min_eq_left hj]
  have hps : ∀ j, j < B.size / 8 → ((Spec.scanl Spec.mstep (0.0, 0.0, 0.0, 0)
      ((List.range' 0 (B.size / 8)).map (Scan.Kind.f64.bitsAt B))).tail.toArray)[j]! =
      ((List.range (j+1)).map (Scan.Kind.f64.bitsAt B)).foldl Spec.mstep (0.0, 0.0, 0.0, 0) := fun j hj => by
    rw [Spec.scanl_range, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map, List.length_map,
      List.length_range']
    rw [List.getElem!_toArray, getElem!_pos _ j (by simp; omega), List.getElem_map, List.getElem_range]
    simp only [Function.comp_apply, hP (j+1) (by omega)]
  have fext : ∀ (l : List Nat) (f g : ByteArray → Nat → ByteArray) (b : ByteArray),
      (∀ b i, i ∈ l → f b i = g b i) → l.foldl f b = l.foldl g b := by
    intro l; induction l with
    | nil => intros; rfl
    | cons x l ih =>
      intro f g b h
      rw [List.foldl_cons, List.foldl_cons, h b x (List.mem_cons_self ..)]
      exact ih f g _ fun b i hi => h b i (List.mem_cons_of_mem _ hi)
  rcases hop with rfl | rfl | rfl <;>
  · unfold Scan.mwinBits
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, map_pure,
      bind_pure_comp, hm, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    rw [mloop0 (Scan.Kind.f64.bitsAt B) ?_]
    · simp only [pure_bind]
      rw [List.range_eq_range', (fun c => rfl : ∀ c, ByteArray.emptyWithCapacity c = ByteArray.empty)]
      refine fext _ _ _ _ fun out i hi => ?_
      have hi : i < B.size / 8 := by simpa using hi
      have hb : (if i < w then ((0.0, 0.0, 0.0, 0) : Float × Float × Float × Int64) else
          ((Spec.scanl Spec.mstep (0.0, 0.0, 0.0, 0) ((List.range' 0 (B.size / 8)).map (Scan.Kind.f64.bitsAt B))).tail.toArray)[i - w]!)
          = ((List.range (i+1-w)).map (Scan.Kind.f64.bitsAt B)).foldl Spec.mstep (0.0, 0.0, 0.0, 0) := by
        split
        · rw [show i + 1 - w = 0 by omega]; rfl
        · rw [hps (i - w) (by omega), show i - w + 1 = i + 1 - w by omega]
      simp only [Array.get!Internal_eq_getElem!, hps i hi, hb]
      rfl
    · intro a A i; rfl

/-- **`w msum x` / `w mavg x` / `w mdev x` over a float column** (`bytes` or `alp`): `Spec.mfloat`, the
    prefix fold of the four totals and, at each position, `memit` of the totals at the window's two ends. -/
theorem mfloat_toList_float {op : Scan.MOp} (hop : op = .msum ∨ op = .mavg ∨ op = .mdev) {w : Nat}
    (hw : w < USize.size) {n : Nat} {R : Arr .float n} {ws : List UInt64} (hx : floatWords n R.enc = some ws)
    (hn : n < USize.size) (h32 : n < 2 ^ 32) {S : Arr .float n} (h : mwin op w .float R = some S) :
    S.toList = Spec.mfloat op w R.toList := by
  obtain ⟨B, hBw, hBs, hd⟩ := mwin_float (op := op) (rt := .float) (rk := .f64)
    (by rcases hop with rfl | rfl | rfl <;> rfl) (by rcases hop with rfl | rfl | rfl <;> rfl) rfl
    (by rcases hop with rfl | rfl | rfl <;> rfl) hx hn
  obtain ⟨-, hS⟩ := mwin_answer_of hw hd h
  subst hBs
  have hE := mwinBits_mfloat hop w B
  have hsz : (Scan.mwinBits op .f64 w (B.size / 8) B).size / 8 = B.size / 8 := by
    rw [hE, foldl_push_size _ 8 (by decide), Nat.mul_div_cancel _ (by decide)]
  rw [Arr.toList_float S (by rw [hS]; exact floatWords_answer _ (by rw [hsz]; exact h32) hsz), hE,
    Verify.elemsW_foldl_mod _ 8 (by decide) (by decide), Arr.toList_float R hx, ← hBw, Spec.mfloat, Verify.elemsW,
    List.length_map, List.length_range]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  have h1 : min (i + 1) (B.size / 8) = i + 1 := by omega
  have h2 : min (i + 1 - w) (B.size / 8) = i + 1 - w := by omega
  rw [show 8 * 8 = 64 from rfl, Verify.ofNat_toNat_mod64]
  dsimp only
  simp only [← List.map_take, List.take_range, h1, h2]
  rfl

end Ops

/-! ## Checks on small literal Rels -/

section Checks

open QLean.Column Ops

private def vals {v : QAtomicType} {n : Nat} (R : Option (Arr v n)) : List (El v) := (R.map Arr.toList).getD []
/-- An answer whose type comes with it, kept where that type is `rt`. -/
private def at? {n : Nat} (rt : QAtomicType) : Option ((r : QAtomicType) × Arr r n) → Option (Arr rt n)
  | some ⟨r, S⟩ => if h : r = rt then some (h ▸ S) else none
  | none => none

private def xs : List Int64 := [3, -1, 4, 1, -5, 9, 2, 6]
private def xn : List Int64 := [2, Int64.minValue, 7, 1]
private def xsA : Arr .long 8 := (Arr.mk (.bytes (packLongs [3, -1, 4, 1, -5, 9, 2, 6])) (by decide) : Arr .long 8)
private def xnA : Arr .long 4 := (Arr.mk (.bytes (packLongs [2, Int64.minValue, 7, 1])) (by decide) : Arr .long 4)
private def ysA : Arr .long 4 := (Arr.mk (.bytes (packLongs [1, 2, 3, 6])) (by decide) : Arr .long 4)
private def zsA : Arr .long 4 := (Arr.mk (.bytes (packLongs [1, 3, 3, 2])) (by decide) : Arr .long 4)
private def sA : Arr .long 8 := (Arr.mk (.bytes (packLongs [2, 0, 1, 2, 0, 1, 2, 0])) (by decide) : Arr .long 8)
#guard xsA.toList == xs ∧ xnA.toList == xn

#guard vals (scan .add .long xsA) == Spec.scan (· + ·) 0 xs
#guard vals (scan .add .long xnA) == Spec.scan (· + ·) 0 xn
#guard vals (scan .mul .long xsA) == Spec.scan (· * ·) 1 xs
#guard vals (scan .lesser .long xnA) == Spec.scan min Int64.maxValue xn
#guard vals (scan .greater .long xnA) == Spec.scan max (Int64.minValue + 1) xn
#guard vals (scan .fill .long xnA) == Spec.scan (fun _ x => x) Spec.nul xn

#guard over .add xsA == some (Spec.over (· + ·) 0 xs)
#guard over .add xnA == some (Spec.over (· + ·) 0 xn)
#guard over .mul xsA == some (Spec.over (· * ·) 1 xs)
#guard over .lesser xnA == some (Spec.over min Int64.maxValue xn)
#guard over .greater xsA == some (Spec.over max (Int64.minValue + 1) xs)
#guard avg ysA == some (3.0 : Float).toBits

#guard vals (mwin .msum 3 .long xsA) == Spec.msum 3 xs
#guard vals (mwin .mmin 3 .long xsA) == Spec.mext (· < ·) Int64.maxValue 3 xs
#guard vals (mwin .mmax 3 .long xsA) == Spec.mext (· > ·) (-Int64.maxValue) 3 xs
#guard vals (mwin .mmin 3 .long xnA) == Spec.mext (· < ·) Int64.maxValue 3 xn
#guard vals (mwin .mmax 3 .long xnA) == Spec.mext (· > ·) (-Int64.maxValue) 3 xn
-- q 4.1: `3 mmax 0N 0N 0N 1` is `-0W -0W 0N 1`, the seed `-0W` in each of the first two windows
private def nnA : Arr .long 4 := (Arr.mk (.bytes (packLongs [Int64.minValue, Int64.minValue, Int64.minValue, 1])) (by decide) : Arr .long 4)
#guard vals (mwin .mmax 3 .long nnA) == [-Int64.maxValue, -Int64.maxValue, Int64.minValue, 1]
-- the encoded form goes through `mwinFoR` and answers what the dense one does
private def xsF : Arr .long 8 :=
  Arr.mk (.foR (Kernel.Coc.encode 8 (packLongs xs)).1 (Kernel.Coc.encode 8 (packLongs xs)).2) (foRLongs_wf xs)
#guard vals (mwin .mmin 3 .long xsF) == Spec.mext (· < ·) Int64.maxValue 3 xs
#guard vals (mwin .msum 3 .long xsF) == Spec.msum 3 xs
-- q 4.1: `3 msum 2 0N 7 1` is `2 2 9 8`, `2 mcount 2 0N 7 1` is `1 1 1 2i`
#guard vals (mwin .msum 3 .long xnA) == Spec.msum 3 xn ∧ Spec.msum 3 xn == [2, 2, 9, 8]
#guard vals (mwin .mcount 2 .int xnA) == Spec.mcount 2 xn ∧ Spec.mcount 2 xn == [1, 1, 1, 2]
#guard vals (mwin .mcount 3 .int xsF) == Spec.mcount 3 xs
-- a boolean window is `mwinBitmap`'s bitmap: q's `2 mmax 010b` is `011b`, `2 mmin 101b` is `100b`
private def b010 : Arr .boolean 3 := (Arr.mk (.bits (ByteArray.mk #[0b010])) (by decide) : Arr .boolean 3)
private def b101 : Arr .boolean 3 := (Arr.mk (.bits (ByteArray.mk #[0b101])) (by decide) : Arr .boolean 3)
#guard vals (mwin .mmax 2 .boolean b010) == [false, true, true]
#guard vals (mwin .mmin 2 .boolean b101) == [true, false, false]
#guard vals (mwin .mcount 2 .int b101) == [1, 2, 2]
#guard (mwin .msum 3 .int xsA).isNone

#guard (iasc xsA).toList == Spec.grade false xs
#guard (idesc zsA).toList == [1, 2, 3, 0] ∧ (idesc zsA).toList == Spec.grade true zsA.toList
#guard (rank xsA).toList == Spec.rank xs
#guard (asc xsA).toList == Spec.sort false xs
#guard (asc xsA).attrCell.map (·.1) == some 1
#guard (desc xsA).toList == Spec.sort true xs
#guard (xasc sA xsA).toList == (Spec.grade false sA.toList).map fun i => xs[i.toNatClampNeg]!
-- a general list takes `pickRef`: `(7;8;9)@2 0 1`
private def gL : Arr .general 3 :=
  Arr.mk (.gen #[QValue.atom (.long 7), QValue.atom (.long 8), QValue.atom (.long 9)]) (by simp [Enc.WF])
#guard ((permute (Arr.mk (.bytes (packLongs [2, 0, 1])) (by decide) : Arr .long 3) gL).toList.map fun v : QValue => reprStr v) ==
  [9, 7, 8].map fun i => reprStr (QValue.atom (.long i))

-- the parted list `(10 20; 30; 40 50 60)` and the groups `[0,1) [1,1) [1,3)` with an empty middle one
private def og : Arr .long 4 := (Arr.mk (.bytes (packLongs [0, 2, 3, 6])) (by decide) : Arr .long 4)
private def gv : List Int64 := [10, 20, 30, 40, 50, Int64.minValue]
private def G : Parted .long :=
  ⟨3, 6, og, by decide, (Arr.mk (.bytes (packLongs [10, 20, 30, 40, 50, Int64.minValue])) (by decide) : Arr .long 6)⟩
private def oe : Arr .long 4 := (Arr.mk (.bytes (packLongs [0, 1, 1, 3])) (by decide) : Arr .long 4)
private def E : Parted .long :=
  ⟨3, 3, oe, by decide, (Arr.mk (.bytes (packLongs [7, 8, 9])) (by decide) : Arr .long 3)⟩

-- the same groups over an `int` column: `groupedOver` answers `sum` at `int`, the null skipped
private def GI : Parted .int :=
  ⟨3, 6, og, by decide,
    Arr.mk (.bytes <| [10, 20, 30, 40, 50, Int32.minValue].foldl (fun b (x : Int32) => Column.pushBits b x.toUInt32.toUInt64 4) .empty)
      (by decide)⟩
#guard vals (at? .int (overBy .add GI)) == [30, 30, 90]
#guard vals (at? .int (overBy .greater GI)) == [20, 30, 50]
#guard (countBy G).toList == Spec.countBy [0, 2, 3, 6] gv
#guard (countBy E).toList == [1, 0, 2] ∧ (countBy E).toList == Spec.countBy [0, 1, 1, 3] [(7 : Int64), 8, 9]
#guard if h : ∀ j : Fin G.g, G.o.get j.castSucc < G.o.get j.succ then (lastBy G h).toList == Spec.lastBy [0, 2, 3, 6] gv else false
#guard !decide (∀ j : Fin E.g, E.o.get j.castSucc < E.o.get j.succ)
#guard vals (at? .long (overBy .add G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over (· + ·) 0))
#guard vals (at? .long (overBy .greater G)) == ((Spec.groups [0, 2, 3, 6] gv).map (Spec.over max (Int64.minValue + 1)))
#guard vals (at? .long (overBy .add E)) == [7, 0, 17]

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
#print axioms Ops.scanOf_words
#print axioms Ops.scan_f64_words
#print axioms Ops.scan_toList_float
#print axioms floatWords_answer
#print axioms Arr.dense_float
#print axioms Ops.mwin_float
#print axioms Ops.mwin_answer_of
#print axioms Ops.mwinExt_words
#print axioms Ops.mext_toList_float
#print axioms Ops.mloop
#print axioms Ops.mwinBits_mfloat
#print axioms Ops.mfloat_toList_float
#print axioms Ops.sumF64Total_congr
#print axioms Ops.sumF64Total_words
#print axioms Ops.sum_float
#print axioms Ops.avg_float

end LeetQ.Rel
