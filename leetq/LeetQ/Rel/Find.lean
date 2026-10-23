/-
  where, distinct, find, in and bin on the RelRep core. Each verb hands its operand columns to the
  qlean kernel that owns the encoding (`whereColumn`, `distinctColumn`, `findColumn`, `memberColumn`,
  `binColumn`, which dispatch over `bits`/`syms`/`enum`/`bytes`/`foR` and the `s` attribute), after
  the small-range test: a long-class `foR` haystack whose block metadata puts it in a range of at most
  `4·max(2¹⁶, n)` is answered by direct address, no hash. A position answer is a new `Rel` keyed
  `til m`, nothing stored for the key; an answer per needle keeps the needles' key.
  The specs are List-level, on `toList`.
-/
import LeetQ.Rel.Core
import QLean.Kernel.Search
import QLean.Kernel.Sort
import QLean.Kernel.Structural
import QLean.Kernel.Elementwise
import QLean.Kernel.Scan
import QLean.Kernel.Reduce
import QLean.Verify.Where

namespace LeetQ.Rel.Find

open QLean QLean.Kernel

/-! ## Wrapping a kernel's answer -/

/-- A list of `a`s from a column a kernel wrote: key `til m`, `m` the column's own count, `attr` the
    producer's attribute (§2.4). -/
def list (a : QAtomicType) (c : Column) (attr : UInt8 := 0) : Except String (Rel (.atom .long) (.atom a)) := do
  pure ⟨_, .til _, ← Arr.of (.atom a) (Column.count a c) c "a list answer" attr⟩

/-- An answer per element of an operand, on that operand's key; the count is checked, not assumed. -/
def onKey {k : Ty} {n : Nat} (key : KeyCol k n) (a : QAtomicType) (c : Column) (verb : String) :
    Except String (Rel k (.atom a)) := do
  pure ⟨n, key, ← Arr.of (.atom a) n c verb⟩

/-- The vector payload of a dispatcher's answer at type `a`. -/
def vec (verb : String) (a : QAtomicType) : Option QValue → Except String Column
  | some (.vector b c) => if a == b then .ok c else .error s!"{verb}: the kernel answered a vector of another type"
  | some _ => .error s!"{verb}: the kernel answered a non-vector where a vector was due"
  | none => .error s!"{verb}: no qlean kernel claims this operand (q's 'type)"

/-- A dense payload of an operand, or the error naming the verb. -/
def dense (verb : String) (a : QAtomicType) (c : Column) : Except String ByteArray :=
  match Column.bytesOf a c with
  | some b => .ok b
  | none => .error s!"{verb}: the operand has no dense payload at its type"

/-! ## The small-range test and direct address -/

/-- `[min, max]` of a non-empty `foR` column read off its block metadata, O(blocks); `none` on any
    other encoding, which has no range without a pass over its elements. -/
def foRRange : Column → Option (Int64 × Int64)
  | .foR n md _ =>
    if n = 0 then none else
    let bs := List.range (Column.nblk md)
    some (bs.foldl (fun lo b => min lo (Column.baseAt md b).toInt64) Int64.maxValue,
          bs.foldl (fun hi b => max hi (Column.maxvAt md b).toInt64) Int64.minValue)
  | _ => none

/-- One long as an eight-byte payload: the atom operand of an `av`/`va` kernel call. -/
def one (v : UInt64) : ByteArray := Column.pushBits .empty v 8

/-- `T[v − lo]` = the first position of `v` in `hay` (`n` elements, all in `[lo, lo+r)`), and `n` for a
    value it does not hold. `scatterPacked` keeps the last write, so the positions go in reversed. -/
def firstTable (hay : ByteArray) (n : Nat) (lo : Int64) (r : Nat) : ByteArray :=
  let off := Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue hay (one lo.toUInt64) n.toUSize
  scatterPacked 64 (expandBytes 8 0 (one n.toUInt64) #[r]) (reverseBytes 8 off)
    (reverseBytes 8 (tilLongs n.toUSize)) 0 false

/-- Each needle's first position in the haystack `firstTable` was built from, `n` at a miss. A needle
    outside the range, the null included, reads past `T` as an unsigned index and takes the fill. -/
def probe (t : ByteArray) (n : Nat) (lo : Int64) (ndl : ByteArray) : ByteArray :=
  gatherBytes 8 n.toUInt64 t (Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue ndl (one lo.toUInt64) (ndl.size / 8).toUSize)

/-- The direct-address table of a haystack, when the small-range test admits it: a long-class `foR`
    column (no null: a block holding `0N` has base `0N` and fails the test) with
    `max − min ≤ 4·max(2¹⁶, n)`. Answers the table, `lo` and the dense haystack. -/
def direct (a : QAtomicType) (c : Column) (n : Nat) : Option (ByteArray × Int64 × ByteArray) := do
  guard (clsOf a == some Ew.i64)
  let (lo, hi) ← foRRange c
  let r := (hi.toInt - lo.toInt).toNat + 1
  guard (r ≤ 4 * max 65536 n)
  let hb ← Column.bytesOf a c
  pure (firstTable hb n lo r, lo, hb)

/-! ## The verbs -/

/-- `&x` on booleans: the positions of the set bits, `whereBits`; sorted (attribute `s`). -/
def «where» {k : Ty} (x : Rel k (.atom .boolean)) : Except String (Rel (.atom .long) (.atom .long)) := do
  list .long (← vec "&x" .long (whereColumn .boolean x.val.c)) 1

/-- q's `where` on a dense count column `cnt` (none negative): row `i` repeated `cnt[i]` times, and each
    copy's rank in its run — `Scan.scan sums`, `overBytes add`, `tilLongs`, `binBytes` of the outputs into
    the run starts (a zero count repeats a start; `bin` takes the last, the row that owns it). -/
def expand (cnt : ByteArray) : ByteArray × ByteArray :=
  let n := cnt.size / 8
  let rs := Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (Scan.scan .sums .i64 n.toUSize cnt) cnt n.toUSize
  let m := (overBytes .add Ew.i64 Int64.minValue cnt).toInt.toNat
  let p := tilLongs m.toUSize
  let i := binBytes 8 false true false rs p
  (i, Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue p (gatherBytes 8 0 rs i) m.toUSize)

/-- `&x` on counts: `expand`, after one `Ew.cmp lt 0` (`0N` included) refuses a negative count. -/
def whereCounts {k : Ty} (x : Rel k (.atom .long)) : Except String (Rel (.atom .long) (.atom .long)) := do
  let b ← dense "&x" .long x.val.c
  let neg := whereBits x.n.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va b (one 0) x.n.toUSize)
  if neg.size > 0 then throw s!"&x: count {(Column.bitsAt b ((Column.bitsAt neg 0 8).toNat * 8) 8).toInt64} at position {(Column.bitsAt neg 0 8).toNat} is negative or null (q's 'domain)"
  list .long (.bytes (expand b).1) 1

/-- `?x`: the first occurrences, in order (attribute `u`). Already unique: the operand itself. Small
    range: the positions where `T[x − lo]` is the position itself, then `x@` those. -/
def distinct {k : Ty} {a : QAtomicType} (x : Rel k (.atom a)) : Except String (Rel (.atom .long) (.atom a)) :=
  if x.val.attr == 2 then .ok ⟨x.n, .til x.n, x.val⟩ else
  match direct a x.val.c x.n with
  | some (t, lo, hb) =>
    let n := x.n.toUSize
    let p := whereBits n (Ew.cmp Ew.eq Ew.i64 Ew.vv (probe t x.n lo hb) (tilLongs n) n)
    list a (.bytes (gatherBytes 8 0 hb p)) 2
  | none => do list a (← vec "?x" a (distinctColumn a x.val.c)) 2

/-- `x?y`: each element of `y`'s first position in `x`, `count x` at a miss; on `y`'s key. -/
def find {k k' : Ty} {a : QAtomicType} (x : Rel k (.atom a)) (y : Rel k' (.atom a)) :
    Except String (Rel k' (.atom .long)) := do
  let c ← match direct a x.val.c x.n with
    | some (t, lo, _) => do pure (.bytes (probe t x.n lo (← dense "x?y" a y.val.c)))
    | none => vec "x?y" .long (findColumn a (x.val.attr == 1) x.val.c (.vector a y.val.c))
  onKey y.key .long c "x?y"

/-- `x in y`: whether each element of `x` is in `y`; on `x`'s key. -/
def «in» {k k' : Ty} {a : QAtomicType} (x : Rel k (.atom a)) (y : Rel k' (.atom a)) :
    Except String (Rel k (.atom .boolean)) := do
  let c ← match direct a y.val.c y.n with
    | some (t, lo, _) => do
      let g := probe t y.n lo (← dense "x in y" a x.val.c)
      pure (.bits x.n (Ew.cmp Ew.lt Ew.i64 Ew.va g (one y.n.toUInt64) x.n.toUSize))
    | none => vec "x in y" .boolean (memberColumn a (y.val.attr == 1) (.vector a x.val.c) y.val.c)
  onKey x.key .boolean c "x in y"

/-- `x bin y`: for each element of `y`, the last position of sorted `x` holding at most it, `-1`
    below all; `binBytes`/`foRBin`/`binBits`/`binSymColumn` by encoding. On `y`'s key. -/
def bin {k k' : Ty} {a : QAtomicType} (x : Rel k (.atom a)) (y : Rel k' (.atom a)) :
    Except String (Rel k' (.atom .long)) := do
  onKey y.key .long (← vec "x bin y" .long (binColumn a false x.val.c (.vector a y.val.c))) "x bin y"

/-! ## The List-level spec -/

/-- `&x` on booleans: the positions holding `true`. -/
def whereSpec (bs : List Bool) : List Int64 :=
  ((List.range bs.length).filter (bs.getD · false)).map Int64.ofNat

/-- `&x` on counts: position `i` related to each `j < ν(i)`, its first column. -/
def whereCountsSpec (ns : List Int64) : List Int64 :=
  (List.range ns.length).flatMap fun i => List.replicate (ns.getD i 0).toInt.toNat (Int64.ofNat i)

/-- `?x`: the first occurrences, in order. -/
def distinctSpec {α : Type} [BEq α] (xs : List α) : List α := xs.eraseDups

/-- `x?y`: the first index of each `y` in `xs`, `|xs|` at a miss. -/
def findSpec {α : Type} [BEq α] (xs ys : List α) : List Int64 := ys.map fun y => Int64.ofNat (xs.idxOf y)

/-- `x in y`. -/
def inSpec {α : Type} [BEq α] (xs ys : List α) : List Bool := xs.map ys.contains

/-- `x bin y` on a sorted `xs`: the count of elements at most `y`, less one. -/
def binSpec {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] (xs ys : List α) : List Int64 :=
  ys.map fun y => Int64.ofNat (xs.countP (· ≤ y)) - 1

/-! ## Laws read off the construction -/

/-- A position answer is keyed by `til` over its own count. -/
theorem list_key {a : QAtomicType} {c : Column} {u : UInt8} {r : Rel (.atom .long) (.atom a)}
    (h : list a c u = .ok r) : r.key = .til r.n := by
  simp only [list, bind, Except.bind, pure, Except.pure] at h; split at h
  · cases h
  · cases h; rfl

/-- An answer per operand element keeps the operand's count and key. -/
theorem onKey_key {k : Ty} {n : Nat} {key : KeyCol k n} {a : QAtomicType} {c : Column} {s : String}
    {r : Rel k (.atom a)} (h : onKey key a c s = .ok r) : ∃ e : r.n = n, e ▸ r.key = key := by
  simp only [onKey, bind, Except.bind, pure, Except.pure] at h; split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- The pairs of an answer on an operand's key, listed: the operand's keys beside the answer's values. -/
theorem onKey_toList {k : Ty} {n : Nat} {key : KeyCol k n} {a : QAtomicType} {c : Column} {s : String}
    {r : Rel k (.atom a)} (h : onKey key a c s = .ok r) : r.toList.map Prod.fst = key.toList := by
  simp only [onKey, bind, Except.bind, pure, Except.pure] at h; split at h
  · cases h
  · cases h; apply List.ext_getElem <;> simp [Rel.toList, KeyCol.toList]

/-- A list answer's column is the kernel's column. -/
theorem list_c {a : QAtomicType} {c : Column} {u : UInt8} {r : Rel (.atom .long) (.atom a)}
    (h : list a c u = .ok r) : r.val.c = c := by
  simp only [list, bind, Except.bind, pure, Except.pure, Arr.of] at h; split at h
  · cases h
  · rename_i hw; split at hw
    · cases hw; cases h; rfl
    · cases hw

/-- `&x` on booleans is `whereSpec`, from `whereBits_spec`. `x.n < USize.size` because `whereBits` takes
    its count as a `USize`. -/
theorem where_toList {k : Ty} {x : Rel k (.atom .boolean)} {r : Rel (.atom .long) (.atom .long)}
    (hn : x.n < USize.size) (h : «where» x = .ok r) : r.val.toList = whereSpec x.val.toList := by
  have hw := x.val.wf
  cases hc : x.val.c with
  | bits m bs =>
    rw [hc] at hw
    obtain rfl : m = x.n := hw.2
    simp only [«where», hc, whereColumn, vec, bind, Except.bind] at h
    have hr := list_c h
    obtain ⟨hs, hj⟩ := QLean.Verify.whereBits_spec x.n.toUSize bs
    rw [USize.toNat_ofNat_of_lt' hn] at hs hj
    have hl : r.n = ((List.range x.n).filter (Column.bitAt bs)).length := by
      have := r.val.wf.2; rw [hr] at this; simp only [Column.count, QAtomicType.width] at this; omega
    have hf : (List.range x.n).filter (x.val.toList.getD · false) = (List.range x.n).filter (Column.bitAt bs) :=
      List.filter_congr fun i hi => by
        have hi := List.mem_range.1 hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hi),
          Option.getD_some, Arr.getElem_toList, Arr.get_bool_bits x.val hc]
    have hspec : whereSpec x.val.toList = ((List.range x.n).filter (Column.bitAt bs)).map Int64.ofNat := by
      unfold whereSpec; rw [Arr.length_toList, hf]
    rw [hspec]
    apply List.ext_getElem
    · rw [List.length_map, Arr.length_toList, hl]
    · intro j h1 _
      rw [List.getElem_map, Arr.getElem_toList, Arr.get_long_bytes r.val hr]
      exact toInt64_of_toNat (hj j (by rw [Arr.length_toList] at h1; omega))
  | _ => all_goals (rw [hc] at hw; simp [Ty.WF, Column.admits] at hw)

/-! ## Checks against the spec on small literal Rels -/

section Checks

private def ans {α : Type} {k v : Ty} (f : Rel k v → α) : Except String (Rel k v) → Option α
  | .ok r => some (f r)
  | .error _ => none

private def bs : Rel (.atom .long) (.atom .boolean) := ⟨5, .til 5, { c := .bits 5 (ByteArray.mk #[0b10110]), wf := by decide }⟩
private def cs : Rel (.atom .long) (.atom .long) := ⟨3, .til 3, { c := .bytes (packLongs [2, 0, 1]), wf := by decide }⟩
private def xs : Rel (.atom .long) (.atom .long) := ⟨5, .til 5, { c := .bytes (packLongs [5, 3, 5, 9, 3]), wf := by decide }⟩
-- the same five longs Frame-of-Reference encoded: the small-range path
private def xf : Rel (.atom .long) (.atom .long) :=
  ⟨5, .til 5, { c := .foR 5 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).2, wf := ⟨rfl, rfl⟩ }⟩
private def ys : Rel (.atom .long) (.atom .long) := ⟨4, .til 4, { c := .bytes (packLongs [3, 9, 7, 0x8000000000000000]), wf := by decide }⟩
private def ss : Rel (.atom .long) (.atom .long) := ⟨4, .til 4, { c := .bytes (packLongs [1, 3, 3, 7]), wf := by decide }⟩
private def ks : Rel (.atom .long) (.atom .long) := ⟨5, .til 5, { c := .bytes (packLongs [0, 3, 5, 9, -1]), wf := by decide }⟩
private def sy : Rel (.atom .long) (.atom .symbol) :=
  ⟨3, .til 3, { c := .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], wf := by decide }⟩
private def sn : Rel (.atom .long) (.atom .symbol) :=
  ⟨2, .til 2, { c := .syms (ByteArray.mk #[97, 0, 122, 0]) #[0, 2, 4], wf := by decide }⟩

#guard ans (·.val.toList) («where» bs) == some (whereSpec bs.val.toList)
#guard ans (·.val.toList) («where» bs) == some [1, 2, 4]
#guard ans (·.val.toList) (whereCounts cs) == some (whereCountsSpec cs.val.toList)
#guard ans (·.val.toList) (whereCounts cs) == some [0, 0, 2]
private def csf : Rel (.atom .long) (.atom .long) :=
  ⟨4, .til 4, { c := .foR 4 (Coc.encode 8 (packLongs [2, 0, 3, 1])).1 (Coc.encode 8 (packLongs [2, 0, 3, 1])).2, wf := ⟨rfl, rfl⟩ }⟩
#guard ans (·.val.toList) (whereCounts csf) == some (whereCountsSpec [2, 0, 3, 1])
#guard (whereCounts ys).toOption.isNone
#guard (direct .long xf.val.c 5).isSome && (direct .long xs.val.c 5).isNone
#guard [xs, xf].all fun x => ans (·.val.toList) (distinct x) == some (distinctSpec x.val.toList)
#guard ans (·.val.toList) (distinct xf) == some [5, 3, 9]
#guard ans (·.val.toList) (distinct sy) == some (distinctSpec sy.val.toList)
#guard [xs, xf].all fun x => ans (·.val.toList) (find x ys) == some (findSpec x.val.toList ys.val.toList)
#guard ans (·.val.toList) (find xf ys) == some [1, 3, 5, 5]
#guard ans (·.val.toList) (find sy sn) == some (findSpec sy.val.toList sn.val.toList)
#guard [xs, xf].all fun x => ans (·.val.toList) («in» ys x) == some (inSpec ys.val.toList x.val.toList)
#guard ans (·.val.toList) («in» ys xf) == some [true, true, false, false]
#guard ans (·.val.toList) («in» sn sy) == some (inSpec sn.val.toList sy.val.toList)
#guard ans (·.val.toList) (bin ss ks) == some (binSpec ss.val.toList ks.val.toList)
#guard ans (·.val.toList) (bin ss ks) == some [-1, 2, 2, 3, -1]
#guard ans (·.toList.map Prod.fst) (find xf ys) == some ys.key.toList

end Checks

#print axioms find
#print axioms «in»
#print axioms distinct
#print axioms whereCounts
#print axioms bin
#print axioms list_key
#print axioms onKey_key
#print axioms onKey_toList
#print axioms where_toList

end LeetQ.Rel.Find
