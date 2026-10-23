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
import QLean.Verify.Distinct
import QLean.Verify.FindMember
import QLean.Verify.Search
import QLean.Verify.Structural

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
  scatterPacked 64 (expandBytes 8 0 (one n.toUInt64) (one r.toUInt64)) (reverseBytes 8 off)
    (reverseBytes 8 (tilLongs n.toUSize)) 0 false

/-- Each needle's first position in the haystack `firstTable` was built from, `n` at a miss. A needle
    outside the range, the null included, reads past `T` as an unsigned index and takes the fill. -/
def probe (t : ByteArray) (n : Nat) (lo : Int64) (ndl : ByteArray) : ByteArray :=
  gatherBytes 8 n.toUInt64 t (Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue ndl (one lo.toUInt64) (ndl.size / 8).toUSize)

/-- The direct-address table of a haystack, when the small-range test admits it: a long-class `foR`
    column whose minimum is not `0N` (`sub` maps the null to itself, so every offset from a `0N`
    minimum is `0N` and the table would miss every probe) with `max − min ≤ 4·max(2¹⁶, n)`.
    Answers the table, `lo` and the dense haystack. A `0N` among other values is not caught: the
    block metadata leaves the null out of `[base, maxv]` (`xn` below), which is why the laws assume
    every element inside the range. -/
def direct (a : QAtomicType) (c : Column) (n : Nat) : Option (ByteArray × Int64 × ByteArray) := do
  guard (clsOf a == some Ew.i64)
  let (lo, hi) ← foRRange c
  guard (lo != Int64.minValue)
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

/-- An answer per operand element has the kernel's column. -/
theorem onKey_c {k : Ty} {n : Nat} {key : KeyCol k n} {a : QAtomicType} {c : Column} {s : String}
    {r : Rel k (.atom a)} (h : onKey key a c s = .ok r) : r.val.c = c := by
  simp only [onKey, bind, Except.bind, pure, Except.pure, Arr.of] at h; split at h
  · cases h
  · rename_i hw; split at hw
    · cases hw; cases h; rfl
    · cases hw

/-- An injective map keeps every first index. -/
theorem idxOf_map_of_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (l : List α) (v : α) : (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih,
      show (f a == f v) = (a == v) from Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact ⟨hf a v, congrArg f⟩)]

/-- An injective map keeps membership. -/
theorem mem_map_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) {l : List α} {v : α} :
    f v ∈ l.map f ↔ v ∈ l :=
  ⟨fun h => by obtain ⟨a, ha, e⟩ := List.mem_map.1 h; exact hf _ _ e ▸ ha, fun h => List.mem_map.2 ⟨v, h, rfl⟩⟩

/-- The first occurrences under a key that identifies exactly what `f` does are `eraseDups` of `f`. -/
theorem firstsOf_map_eraseDups {α β : Type} [DecidableEq α] [BEq β] [LawfulBEq β] (g : Nat → α) (f : Nat → β)
    (hg : ∀ i j, g i = g j ↔ f i = f j) (m : Nat) :
    (Verify.firstsOf g m).map f = ((List.range m).map f).eraseDups := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold Verify.firstsOf at ih ⊢
    rw [List.range_succ, List.filter_append, List.map_append, ih, List.map_append, List.eraseDups_append]
    congr 1
    by_cases hm : f m ∈ (List.range m).map f
    · obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
      have hp : ((List.range m).all fun j => !decide (g j = g m)) = false := Bool.eq_false_iff.2 fun hall => by
        have := List.all_eq_true.1 hall j hj; simp [(hg j m).2 e] at this
      simp [List.filter_cons, hp, List.removeAll, hm]
    · have hp : ((List.range m).all fun j => !decide (g j = g m)) = true := List.all_eq_true.2 fun j hj => by
        simpa using fun e => hm (List.mem_map.2 ⟨j, hj, ((hg j m).1 e)⟩)
      simp [List.filter_cons, hp, List.removeAll, hm, List.eraseDups_cons]

/-- `(8 : USize)` is eight, at either platform width. -/
theorem usize_eight : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)

/-! ## The kernels' view of a long column -/

/-- The payloads the kernel laws read a long operand from: `bytes`, or `foR` with non-empty block
    metadata, which is what marks an operand encoded to `operandBytes`; `alp`'s decode has no law. -/
def Readable : Column → Prop
  | .bytes _ => True
  | .foR _ md _ => md.isEmpty = false
  | _ => False

/-- `elemsW 8 B = ws` word by word: `B` holds `|ws|` eight-byte words, word `i` being `ws[i]`. -/
theorem elemsW8_get {B : ByteArray} {ws : List UInt64} (h : Verify.elemsW 8 B = ws) :
    B.size / 8 = ws.length ∧ ∀ i (hi : i < ws.length), Column.bitsAt B (i * 8) 8 = ws[i] := by
  subst h; exact ⟨by simp [Verify.elemsW], fun i hi => by simp [Verify.elemsW]⟩

/-- The kernels' view of a readable long column is its words: `operand` hands `bytes` over with empty
    metadata and `foR` as it is, and `operandBytes` decodes either to `longWords` (`elemsW_operandBytes`). -/
theorem operand_long {m : Nat} (x : Arr (.atom .long) m) (h : Readable x.c) (hm : m < USize.size) :
    ∃ k md pk ws, operand .long x.c = some (k, md, pk) ∧ longWords x.c = some ws ∧
      Verify.elemsW 8 (operandBytes 8 md pk k.toUSize) = ws ∧ ws.length = m := by
  cases hc : x.c with
  | bytes b =>
    refine ⟨0, .empty, b, _, rfl, rfl, rfl, ?_⟩
    rw [Verify.elemsW, List.length_map, List.length_range]; exact Arr.n_long_bytes x hc
  | foR n md pk =>
    rw [hc] at h
    have h : md.isEmpty = false := h
    have hn : n = m := by have := x.wf.2; rw [hc] at this; exact this
    subst hn
    refine ⟨n, md, pk, _, rfl, rfl, ?_, by simp⟩
    have e := Verify.elemsW_operandBytes 8 (by rw [usize_eight]; decide) (by rw [usize_eight]; decide) md pk n hm
    rw [usize_eight] at e
    rw [e]
    simp only [Verify.operandBits, h, Bool.false_eq_true, ↓reduceIte]
    exact List.map_congr_left fun i _ => Verify.ofNat_toNat_mod64 _
  | _ => all_goals (rw [hc] at h; exact False.elim h)

/-- `x?y` at long operands, unsorted, is `probeColumns`. -/
theorem findColumn_long (x c : Column) :
    findColumn .long false x (.vector .long c) = (probeColumns .long 8 false x c).map fun out => .vector .long (.bytes out) := by
  cases x <;> rfl

/-- `x in y` at long operands, unsorted, is `probeColumns`. -/
theorem memberColumn_long (c y : Column) : memberColumn .long false (.vector .long c) y =
    (probeColumns .long 8 true y c).map fun out => .vector .boolean (.bits (Column.count .long c) out) := by
  cases y <;> rfl

/-- `x bin y` at long operands is `binOperands` over the two `operand`s. -/
theorem binColumn_long (x c : Column) : binColumn .long false x (.vector .long c) = (do
    let (hn, hm, hp) ← operand .long x
    let (kn, km, kp) ← operand .long c
    some (QValue.vector .long (.bytes (binOperands 8 false true false hm hp hn.toUSize km kp kn.toUSize)))) := by
  cases x <;> rfl

/-- `probeColumns` at long operands is the dense probe over the two decoded operands: with both
    metadata empty `operandBytes` is the pack itself, otherwise it is `foRFindVec`/`foRMemberVec`'s body. -/
theorem probeColumns_long (member : Bool) {x c : Column} {hn nn : Nat} {hm hp nm np : ByteArray}
    (hx : operand .long x = some (hn, hm, hp)) (hc : operand .long c = some (nn, nm, np)) :
    probeColumns .long 8 member x c = some (if member
      then memberVec 8 false (operandBytes 8 nm np nn.toUSize) (operandBytes 8 hm hp hn.toUSize)
      else findVec 8 false (operandBytes 8 hm hp hn.toUSize) (operandBytes 8 nm np nn.toUSize)) := by
  simp only [probeColumns, hx, hc, bind, Option.bind]
  split
  · rename_i he
    simp only [Bool.and_eq_true] at he
    simp only [operandBytes, he.1, he.2, ↓reduceIte]; rfl
  · rfl

/-- `?x`'s kernel answer on a long column: some `e` lists `x`'s words, and the answer's words are `e` at
    `firstsOf` of its rank — `distinct_spec` on `bytes`; on `foR`, `distinctFoR_spec`, whose answer
    `Column.answer` leaves encoded or decodes (`decodeW`), the same words either way. -/
theorem distinct_words {m : Nat} (x : Arr (.atom .long) m) {xs : List UInt64} (hx : longWords x.c = some xs)
    (hn : m < USize.size) : ∃ (e : Nat → UInt64) (c : Column), xs = (List.range m).map e ∧
      vec "?x" .long (distinctColumn .long x.c) = .ok c ∧
      longWords c = some ((Verify.firstsOf (fun i => Order.rank .i64 (e i)) m).map e) := by
  cases hc : x.c with
  | bytes b =>
    rw [hc] at hx; cases hx
    have hxn := Arr.n_long_bytes x hc
    refine ⟨fun i => Column.bitsAt b (i * 8) 8, .bytes (Order.distinct .i64 (b.size / 8).toUSize b),
      by rw [Verify.elemsW, hxn], rfl, ?_⟩
    have hs := Verify.distinct_spec .i64 (b.size / 8).toUSize b
    rw [USize.toNat_ofNat_of_lt' (by rw [hxn]; exact hn), show Scan.Kind.i64.avail b = b.size / 8 from rfl,
      Nat.min_self, hxn, show Scan.Kind.i64.width = 8 from rfl,
      show Scan.Kind.i64.bitsAt b = fun i => Column.bitsAt b (i * 8) 8 from rfl,
      show Order.keyAt .i64 b = fun i => Order.rank .i64 (Column.bitsAt b (i * 8) 8) from rfl] at hs
    show some (Verify.elemsW 8 (Order.distinct .i64 (b.size / 8).toUSize b)) = _
    rw [hxn, hs]
  | foR n md pk =>
    rw [hc] at hx; cases hx
    have hnm : n = m := by have := x.wf.2; rw [hc] at this; exact this
    subst hnm
    refine ⟨Verify.foRAt 8 md pk, Column.answer .long (.foR (Order.distinctFoR .i64 n.toUSize md pk).1
      (Order.distinctFoR .i64 n.toUSize md pk).2.1 (Order.distinctFoR .i64 n.toUSize md pk).2.2),
      List.map_congr_left fun i _ => (Verify.ofNat_toNat_mod64 _).symm, rfl, ?_⟩
    have hs := Verify.distinctFoR_spec .i64 (by decide) n.toUSize md pk
    rw [USize.toNat_ofNat_of_lt' hn] at hs
    generalize Order.distinctFoR .i64 n.toUSize md pk = d at hs ⊢
    obtain ⟨M, P, Q⟩ := d
    change (List.range M).map (Verify.foRAt 8 P Q) =
      (Verify.firstsOf (fun i => Order.rank .i64 (Verify.foRAt 8 md pk i)) n).map (Verify.foRAt 8 md pk) at hs
    show longWords (Column.answer .long (.foR M P Q)) = _
    rw [← hs]
    have hM : M < USize.size := by
      have := congrArg List.length hs
      rw [List.length_map, List.length_range, List.length_map] at this
      unfold Verify.firstsOf at this
      rw [this]
      exact Nat.lt_of_le_of_lt (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..))) hn
    have hans : Column.answer .long (.foR M P Q) = .foR M P Q ∨
        Column.answer .long (.foR M P Q) = .bytes (Kernel.Coc.decode 8 P Q M.toUSize) := by
      simp only [Column.answer, QAtomicType.width]
      split
      · exact .inl rfl
      · exact .inr rfl
    rcases hans with e | e <;> rw [e]
    · exact congrArg some (List.map_congr_left fun i _ => (Verify.ofNat_toNat_mod64 _).symm)
    · obtain ⟨hsz, hg⟩ := Verify.decodeW 8 (by rw [usize_eight]; decide) P Q M.toUSize
      rw [usize_eight, USize.toNat_ofNat_of_lt' hM] at hsz hg
      refine congrArg some (List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_)
      simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
      exact hg i (by simpa [Verify.elemsW, hsz] using h1)
  | _ => all_goals (rw [hc] at hx; cases hx)
/-! ## Direct address: the table and the probe -/


theorem bitsAt_one (v : UInt64) : Column.bitsAt (one v) 0 8 = v := by
  simpa using Verify.bitsAt_pushBits8 ByteArray.empty v

theorem intStep_sub (nul x y : Int64) :
    Ew.intStep Ew.sub nul x y = if x == nul || y == nul then nul else x - y := rfl

/-- `Ew.val sub` of a long vector and one long, element by element. -/
theorem val_sub_va (b : ByteArray) (c : UInt64) (n : Nat) (hn : n < USize.size) :
    Verify.elemsW 8 (Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue b (one c) n.toUSize) =
      (List.range n).map fun i =>
        (Ew.intStep Ew.sub Int64.minValue (Column.bitsAt b (i * 8) 8).toInt64 c.toInt64).toUInt64 := by
  have h := Verify.elemsW_foldl (fun i => (Ew.intStep Ew.sub Int64.minValue
    (Column.bitsAt b (i * 8) 8).toInt64 c.toInt64).toUInt64) 8 (by decide) (by decide) (List.range n)
    (fun _ _ => UInt64.toNat_lt _)
  rw [← h]; unfold Ew.val
  rw [USize.toNat_ofNat_of_lt' hn]
  congr 2; funext acc i
  show Column.pushBits acc (Ew.valStep Ew.sub Ew.i64 Int64.minValue.toUInt64 (Column.bitsAt b (i * 8) 8)
    (Column.bitsAt (one c) (0 * 8) 8)) 8 = _
  rw [Nat.zero_mul, bitsAt_one]; rfl

/-- Writing positions reversed and keeping the last write leaves the first position: `idxOf`. -/
theorem lastRev (i : Nat) : ∀ O : List Nat,
    ((((List.range O.length).filter fun k => O.reverse.getD k 0 == i).getLast?).map (O.length - 1 - ·)).getD
      O.length = O.idxOf i
  | [] => rfl
  | a :: O => by
    have ih := lastRev i O
    have hf : (List.range O.length).filter (fun k => (a :: O).reverse.getD k 0 == i) =
        (List.range O.length).filter fun k => O.reverse.getD k 0 == i :=
      List.filter_congr fun k hk => by
        have hk : k < O.length := List.mem_range.mp hk
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk : k < O.reverse.length)]
    have ha : (a :: O).reverse.getD O.length 0 = a := by simp [List.getD_eq_getElem?_getD]
    simp only [List.length_cons, List.range_succ, List.filter_append, hf, List.getLast?_append, List.idxOf_cons]
    by_cases h : a = i
    · subst h; simp
    · have hai : (a == i) = false := by simpa using h
      simp only [List.filter_cons, List.filter_nil, ha, hai, cond_false, Bool.false_eq_true, ↓reduceIte,
        List.getLast?_nil]
      rw [← ih]
      rcases hl : ((List.range O.length).filter fun k => O.reverse.getD k 0 == i).getLast? with _ | k
      · simp
      · have hk : k < O.length := List.mem_range.mp ((List.mem_filter.mp (List.mem_of_getLast? hl)).1)
        simp; omega

/-- A long's offset from `lo` as the kernel's unsigned subtraction reads it. -/
def off (lo x : Int64) : Nat := (x.toUInt64 - lo.toUInt64).toNat

theorem toInt_bmod (x : Int64) : x.toInt = Int.bmod x.toUInt64.toNat (2 ^ 64) := BitVec.toInt_eq_toNat_bmod _

theorem off_sub (lo x : Int64) : off lo x = (2 ^ 64 - lo.toUInt64.toNat + x.toUInt64.toNat) % 2 ^ 64 :=
  BitVec.toNat_sub _ _

theorem off_toInt {lo x : Int64} (h : lo ≤ x) : (off lo x : Int) = x.toInt - lo.toInt := by
  have h := Int64.le_iff_toInt_le.mp h
  have a := toInt_bmod x; have b := toInt_bmod lo; rw [off_sub]
  have ax := x.toUInt64.toNat_lt; have al := lo.toUInt64.toNat_lt
  simp only [Int.bmod] at a b; split at a <;> split at b <;> omega

theorem off_inj {lo x y : Int64} (h : off lo x = off lo y) : x = y := by
  rw [off_sub, off_sub] at h
  have ax := x.toUInt64.toNat_lt; have ay := y.toUInt64.toNat_lt; have al := lo.toUInt64.toNat_lt
  have : x.toUInt64.toNat = y.toUInt64.toNat := by omega
  simpa using congrArg UInt64.toInt64 (UInt64.toNat_inj.mp this)

theorem intStep_off {lo : Int64} (hlo : lo ≠ Int64.minValue) (y : Int64) :
    (Ew.intStep Ew.sub Int64.minValue y lo).toUInt64.toNat = if y = Int64.minValue then 2 ^ 63 else off lo y := by
  rw [intStep_sub]
  by_cases hy : y = Int64.minValue
  · subst hy; simp; rfl
  · simp [hy, hlo, off, Int64.toUInt64_sub]

theorem elemsW_one (v : UInt64) : Verify.elemsW 8 (one v) = [v] :=
  Verify.elemsW_foldl (fun _ => v) 8 (by decide) (by decide) [()] (fun _ _ => UInt64.toNat_lt _)

theorem lt_of_le_lo {lo x : Int64} (hlo : lo ≠ Int64.minValue) (h : lo ≤ x) : x ≠ Int64.minValue := by
  rintro rfl; apply hlo; apply Int64.toInt_inj.mp
  have := Int64.le_iff_toInt_le.mp h; have := lo.minValue_le_toInt; omega

/-- **The direct-address table**: `r` slots, slot `i` the first position of offset `i`, `n` at none. -/
theorem firstTable_spec (hb : ByteArray) (ws : List UInt64) (n : Nat) (lo : Int64) (r : Nat)
    (hw : Verify.elemsW 8 hb = ws) (hn : ws.length = n) (hN : n < USize.size) (hr : r < 2 ^ 63)
    (hlo : lo ≠ Int64.minValue) (hin : ∀ x ∈ ws, lo ≤ x.toInt64) :
    (firstTable hb n lo r).size / 8 = r ∧ ∀ i < r, Column.bitsAt (firstTable hb n lo r) (i * 8) 8 =
      UInt64.ofNat ((ws.map fun x => off lo x.toInt64).idxOf i) := by
  have hN64 : n < 2 ^ 64 := Nat.lt_of_lt_of_le hN USize.size_le
  generalize hO : ws.map (fun x => off lo x.toInt64) = O
  have hOn : O.length = n := by rw [← hO, List.length_map, hn]
  simp only [firstTable]
  generalize hoff : Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue hb (one lo.toUInt64) n.toUSize = of
  have hofO : (Verify.elemsW 8 of).map UInt64.toNat = O := by
    rw [← hoff, val_sub_va _ _ _ hN, List.map_map]
    apply List.ext_getElem (by simp [← hO, hn])
    intro i h1 h2
    have hi : i < ws.length := by simp at h1; omega
    simp only [List.getElem_map, List.getElem_range, Function.comp, ← hO]
    rw [(elemsW8_get hw).2 i hi]; simp only [Int64.toInt64_toUInt64]; rw [intStep_off hlo,
      if_neg (lt_of_le_lo hlo (hin _ (List.getElem_mem hi)))]
  have hofn : (Verify.elemsW 8 of).length = n := by rw [← List.length_map (f := UInt64.toNat), hofO, hOn]
  -- the destination: `r` copies of `n`
  have hr1 := elemsW8_get (elemsW_one r.toUInt64)
  have hn1 := elemsW8_get (elemsW_one n.toUInt64)
  have hrr : (Column.bitsAt (one r.toUInt64) (0 * 8) 8).toInt64.toInt.toNat = r := by
    rw [hr1.2 0 (by simp)]; simp only [List.getElem_singleton]
    have hu : ((r.toUInt64.toInt64.toUInt64.toNat : Nat) : Int) = r := by simp; omega
    rw [toInt_bmod, Int.bmod, hu]; split <;> omega
  have hdst : Verify.elemsW 8 (expandBytes 8 0 (one n.toUInt64) (one r.toUInt64)) = List.replicate r n.toUInt64 := by
    have he := Verify.expandBytes_spec 8 (by rw [usize_eight]; decide) (by rw [usize_eight]; decide) 0 (by rw [usize_eight]; simp) (one n.toUInt64) (one r.toUInt64)
    rw [usize_eight] at he; rw [he, hr1.1]
    simp only [List.length_singleton]
    rw [show List.range 1 = [0] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil, hrr, elemsW_one]; rfl
  have hd := elemsW8_get hdst
  have hix := elemsW8_get ((usize_eight ▸ Verify.reverseBytes_spec 8 (by rw [usize_eight]; decide) (by rw [usize_eight]; decide) of))
  have hsx := elemsW8_get ((usize_eight ▸ Verify.reverseBytes_spec 8 (by rw [usize_eight]; decide) (by rw [usize_eight]; decide) (tilLongs n.toUSize)))
  have htil := Verify.tilLongs_spec n.toUSize
  rw [USize.toNat_ofNat_of_lt' hN] at htil
  have htl : (Verify.elemsW 8 (tilLongs n.toUSize)).length = n := by
    rw [← List.length_map (f := UInt64.toNat), htil, List.length_range]
  simp only [List.length_reverse, hofn, htl] at hix hsx
  have hs := Verify.scatterPacked_spec 8 (by decide) 64 (USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)) (expandBytes 8 0 (one n.toUInt64) (one r.toUInt64))
    (reverseBytes 8 of) (reverseBytes 8 (tilLongs n.toUSize)) 0 false (by simp only [hix.1, USize.toNat_zero]; omega)
  simp only [List.length_replicate] at hd
  refine ⟨by rw [hs.1, hd.1], fun i hi => ?_⟩
  rw [hs.2 i (by rw [hd.1]; exact hi), hix.1]
  have hf : (List.range n).filter (fun k => (Column.bitsAt (reverseBytes 8 of) (k * 8) 8).toNat == i) =
      (List.range O.length).filter fun k => O.reverse.getD k 0 == i := by
    rw [hOn]; apply List.filter_congr; intro k hk
    have hk : k < n := List.mem_range.mp hk
    rw [hix.2 k (by simpa [hofn] using hk), ← hofO, List.getD_eq_getElem?_getD]
    simp [hofn, hk, List.getElem_reverse]
  have hl := lastRev i O
  rw [hf]
  rcases hk : ((List.range O.length).filter fun k => O.reverse.getD k 0 == i).getLast? with _ | k
  · rw [hk] at hl; simp only [Option.map_none, Option.getD_none] at hl
    simp only [hd.2 i (by simpa using hi), List.getElem_replicate, ← hl, hOn]
  · rw [hk] at hl; simp only [Option.map_some, Option.getD_some] at hl
    have hkn : k < n := by
      have := List.mem_range.mp (List.mem_filter.mp (List.mem_of_getLast? hk)).1; omega
    simp only [USize.toNat_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte]
    rw [hsx.2 k (by simpa [htl] using hkn), ← hl, hOn]
    apply UInt64.toNat_inj.mp
    have hv := List.getElem_of_eq htil (i := n - 1 - k) (by simp [htl]; omega)
    simp only [List.getElem_map, List.getElem_range] at hv
    simp [List.getElem_reverse, htl] at hv ⊢
    omega


/-- **`probe` against `firstTable`** answers each needle's first position in the haystack, `n` at a miss. -/
theorem probe_spec (hb : ByteArray) (ws : List UInt64) (n : Nat) (lo : Int64) (r : Nat)
    (hw : Verify.elemsW 8 hb = ws) (hn : ws.length = n) (hN : n < USize.size) (hr : r < 2 ^ 63)
    (hlo : lo ≠ Int64.minValue) (hin : ∀ x ∈ ws, lo ≤ x.toInt64 ∧ off lo x.toInt64 < r)
    (ndl : ByteArray) (ys : List UInt64) (hy : Verify.elemsW 8 ndl = ys) (hm : ys.length < USize.size) :
    Verify.elemsW 8 (probe (firstTable hb n lo r) n lo ndl) =
      ys.map fun y => UInt64.ofNat ((ws.map UInt64.toInt64).idxOf y.toInt64) := by
  have hN64 : n < 2 ^ 64 := Nat.lt_of_lt_of_le hN USize.size_le
  obtain ⟨hT, gT⟩ := firstTable_spec hb ws n lo r hw hn hN hr hlo fun x hx => (hin x hx).1
  have hY := elemsW8_get hy
  have hv := val_sub_va ndl lo.toUInt64 (ndl.size / 8) (by rw [hY.1]; exact hm)
  simp only [probe]
  generalize Ew.val Ew.sub Ew.i64 Ew.va Int64.minValue ndl (one lo.toUInt64) (ndl.size / 8).toUSize = g at hv
  generalize firstTable hb n lo r = T at hT gT
  have hG := elemsW8_get hv
  obtain ⟨gs, gj⟩ := Verify.gatherBytes_spec 8 (by rw [usize_eight]; decide) n.toUInt64 T g
  rw [usize_eight] at gs gj
  have hmiss : ∀ y : Int64, (∀ x ∈ ws, x.toInt64 ≠ y) → (ws.map UInt64.toInt64).idxOf y = n := by
    intro y hy; rw [List.idxOf_eq_length, List.length_map, hn]
    simp only [List.mem_map, not_exists, not_and]; exact hy
  apply List.ext_getElem (by simp [Verify.elemsW, gs, hG.1, hY.1])
  intro j h1 h2
  have hj : j < ys.length := by simpa using h2
  have hj' : j < ndl.size / 8 := by rw [hY.1]; exact hj
  simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
  rw [gj j (by rw [hG.1]; simpa using hj'), hG.2 j (by simpa using hj')]
  simp only [List.getElem_map, List.getElem_range]
  rw [hY.2 j hj]; simp only [Int64.toInt64_toUInt64]; rw [intStep_off hlo, hT]
  by_cases h0 : ys[j].toInt64 = Int64.minValue
  · rw [if_pos h0, if_neg (by omega), hmiss _ fun x hx e => lt_of_le_lo hlo (hin x hx).1 (e.trans h0)]; exact congrArg UInt64.ofNat (by simp; omega)
  · rw [if_neg h0]
    by_cases hv : off lo ys[j].toInt64 < r
    · rw [if_pos hv, gT _ hv, show ws.map (fun x => off lo x.toInt64) = (ws.map UInt64.toInt64).map (off lo) by rw [List.map_map]; rfl]
      rw [idxOf_map_of_inj (fun _ _ => off_inj)]
    · rw [if_neg hv, hmiss _ fun x hx e => hv (by rw [← e]; exact (hin x hx).2)]; exact congrArg UInt64.ofNat (by simp; omega)

theorem direct_some {c : Column} {n : Nat} {t hb : ByteArray} {lo : Int64} (h : direct .long c n = some (t, lo, hb)) :
    ∃ hi, foRRange c = some (lo, hi) ∧ lo ≠ Int64.minValue ∧ (hi.toInt - lo.toInt).toNat + 1 ≤ 4 * max 65536 n ∧
      Column.bytesOf .long c = some hb ∧ t = firstTable hb n lo ((hi.toInt - lo.toInt).toNat + 1) := by
  unfold direct at h
  have hcls : clsOf QAtomicType.long = some Ew.i64 := rfl
  cases hR : foRRange c with
  | none => simp [hR, hcls, guard, failure, bind, Option.bind] at h
  | some p =>
    obtain ⟨l, hi⟩ := p
    by_cases hl : l = Int64.minValue
    · simp [hR, hcls, hl, guard, failure, bind, Option.bind] at h
    by_cases hg : (hi.toInt - l.toInt).toNat + 1 ≤ 4 * max 65536 n
    · cases hb' : Column.bytesOf .long c with
      | none => simp [hR, hcls, hl, hg, hb', guard, failure, bind, Option.bind] at h
      | some b =>
        simp [hR, hcls, hl, hg, hb', guard, failure, bind, Option.bind] at h
        rcases h with ⟨h1, h2, h3⟩; subst_vars; exact ⟨hi, rfl, hl, hg, rfl, rfl⟩
    · simp [hR, hcls, hl, hg, guard, failure, bind, Option.bind] at h

theorem bytesOf_long {c : Column} (h : Readable c) {k : Nat} {md pk : ByteArray}
    (ho : operand .long c = some (k, md, pk)) : Column.bytesOf .long c = some (operandBytes 8 md pk k.toUSize) := by
  have he : Column.encodes QAtomicType.long = true := rfl
  cases c with
  | bytes b => simp [operand, foRColumn, Column.bytesOf] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho; rfl
  | foR n m p =>
    have h : m.isEmpty = false := h
    simp [operand, foRColumn, he] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho
    simp [operandBytes, h]; rfl
  | _ => exact False.elim h

/-- A `foR` column with empty block metadata reads its range as `[maxValue, minValue]`, which holds no
    element; so a range holding every element marks a `Readable` column. -/
theorem readable_of_range {m : Nat} (x : Arr (.atom .long) m) {lo hi : Int64} (h : foRRange x.c = some (lo, hi))
    (hin : ∀ v ∈ x.toList, lo ≤ v ∧ v ≤ hi) : Readable x.c := by
  cases hc : x.c with
  | foR n md pk =>
    rw [hc] at h
    show md.isEmpty = false
    cases he : md.isEmpty
    · rfl
    · exfalso
      have hm : md.size = 0 := by simpa [ByteArray.isEmpty] using he
      have hn : n ≠ 0 := by intro e; simp [foRRange, e] at h
      simp [foRRange, hn, Column.nblk, hm] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnm : n = m := by have := x.wf.2; rw [hc] at this; exact this
      have h0 : 0 < x.toList.length := by rw [Arr.length_toList]; omega
      obtain ⟨a, b⟩ := hin _ (List.getElem_mem h0)
      exact absurd (Int64.le_trans a b) (by decide)
  | _ => all_goals (rw [hc] at h; simp [foRRange] at h)

/-- What `direct` answering hands the direct path: the haystack's words `xs`, dense in `hb`; a range `r`
    below `2^63` holding every offset from `lo`, which is not `0N`; and `t` the `firstTable`. The
    in-range hypothesis is not implied by a well-formed `foR`, whose block metadata nothing checks. -/
theorem direct_table {m : Nat} {x : Arr (.atom .long) m} {t hb : ByteArray} {lo : Int64}
    (hd : direct .long x.c m = some (t, lo, hb))
    (hR : ∀ lo hi, foRRange x.c = some (lo, hi) → ∀ v ∈ x.toList, lo ≤ v ∧ v ≤ hi) (hn8 : 8 * m < USize.size) :
    ∃ xs r, longWords x.c = some xs ∧ Verify.elemsW 8 hb = xs ∧ xs.length = m ∧ r < 2 ^ 63 ∧
      lo ≠ Int64.minValue ∧ (∀ w ∈ xs, lo ≤ w.toInt64 ∧ off lo w.toInt64 < r) ∧ t = firstTable hb m lo r := by
  have hS := USize.size_le
  obtain ⟨hi, hR', hlo, hr4, hbx, ht⟩ := direct_some hd
  have hrg := hR lo hi hR'
  have hx := readable_of_range x hR' hrg
  obtain ⟨k, md, pk, xs, hox, hwx, hbx', hlx⟩ := operand_long x hx (by omega)
  rw [bytesOf_long hx hox] at hbx; obtain rfl := Option.some.inj hbx
  have hxl := Arr.toList_long x hwx
  refine ⟨xs, _, hwx, hbx', hlx, ?_, hlo, fun w hw => ?_, ht⟩
  · rw [Nat.max_def] at hr4; split at hr4 <;> omega
  · obtain ⟨a, b⟩ := hrg w.toInt64 (by rw [hxl]; exact List.mem_map_of_mem hw)
    refine ⟨a, ?_⟩
    have := off_toInt a; have := Int64.le_iff_toInt_le.mp b; omega

theorem find_direct {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k' (.atom .long)}
    (hy : Readable y.val.c) {t hb : ByteArray} {lo : Int64} (hd : direct .long x.val.c x.n = some (t, lo, hb))
    (hR : ∀ lo hi, foRRange x.val.c = some (lo, hi) → ∀ v ∈ x.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * x.n < USize.size) (hm : y.n < USize.size) (h : find x y = .ok r) :
    r.val.toList = findSpec x.val.toList y.val.toList := by
  have hS := USize.size_le
  obtain ⟨xs, R, hwx, hbx, hlx, hr, hlo, hin, rfl⟩ := direct_table hd hR hn8
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y.val hy hm
  unfold find at h
  rw [hd] at h
  simp only [dense, bytesOf_long hy hoy, bind, Except.bind, pure, Except.pure] at h
  rw [Arr.toList_long r.val (show longWords r.val.c = some (Verify.elemsW 8 (probe (firstTable hb x.n lo R) x.n lo
    (operandBytes 8 nmd np nk.toUSize))) by rw [onKey_c h]; rfl),
    Arr.toList_long x.val hwx, Arr.toList_long y.val hwy, findSpec,
    probe_spec _ xs x.n lo _ hbx hlx (by omega) hr hlo hin _ ys hby (by rw [hly]; exact hm)]
  simp only [List.map_map]; rfl

/-! ## The comparison bitmap -/

/-- **`Ew.cmp`'s bitmap**: bit `i` is set exactly when `i < n` and `cmpStep` holds of the two elements
    the shape reads at `i`, so the last byte's tail is zero. The byte fold is `memberVec_mem`'s. -/
theorem cmp_bitAt (op cls shape : UInt8) (a b : ByteArray) (n : USize) :
    (Ew.cmp op cls shape a b n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.cmp op cls shape a b n) i =
      (decide (i < n.toNat) && Ew.cmpStep op cls (Ew.elem cls a (Ew.shapeIdx shape i).1)
        (Ew.elem cls b (Ew.shapeIdx shape i).2)) := by
  let C : Nat → Bool := fun i => decide (i < n.toNat) &&
    Ew.cmpStep op cls (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2)
  let B : Nat → UInt8 := fun k =>
    (List.range 8).foldl (fun byte t => if C (k * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  have hf : Ew.cmp op cls shape a b n =
      (List.range ((n.toNat + 7) / 8)).foldl (fun acc k => acc.push (B k)) ByteArray.empty := rfl
  obtain ⟨hs, -, hg⟩ := Verify.foldl_push8 B (List.range ((n.toNat + 7) / 8)) ByteArray.empty
  rw [hf]
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  have h := hg (i / 8) (by simp; omega)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  have hm8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  show Column.bitAt _ i = C i
  simp only [Column.bitAt, h, Option.getD_some]
  rw [Verify.bit_eq_testBit _ _ hm8, Verify.foldl_setBit _ _ (fun t ht => List.mem_range.1 ht), UInt8.toNat_zero,
    Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, -, ht⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨e, hc⟩ := ht
    subst e
    rwa [Nat.mul_comm, Nat.div_add_mod] at hc
  · intro hc
    refine ⟨i % 8, List.mem_range.2 hm8, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, Nat.mul_comm, Nat.div_add_mod]
    exact ⟨rfl, hc⟩

theorem cmpStep_i64 (op : UInt8) (x y : UInt64) :
    Ew.cmpStep op Ew.i64 x y = (let o := compare x.toInt64 y.toInt64
      if op == Ew.eq then o == .eq else if op == Ew.ne then o != .eq
      else if op == Ew.lt then o == .lt else if op == Ew.le then o != .gt
      else if op == Ew.gt then o == .gt else o != .lt) := rfl

theorem cmpStep_lt (x y : UInt64) : Ew.cmpStep Ew.lt Ew.i64 x y = decide (x.toInt64 < y.toInt64) := by
  rw [cmpStep_i64]
  simp only [show (Ew.lt == Ew.eq) = false from rfl, show (Ew.lt == Ew.ne) = false from rfl,
    show (Ew.lt == Ew.lt) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  simp [compare, compareOfLessAndEq]
  split <;> simp_all
  split <;> simp_all

theorem cmpStep_eq (x y : UInt64) : Ew.cmpStep Ew.eq Ew.i64 x y = decide (x = y) := by
  rw [cmpStep_i64]
  simp only [show (Ew.eq == Ew.eq) = true from rfl, ↓reduceIte, compare, compareOfLessAndEq]
  by_cases hl : x.toInt64 < y.toInt64
  · have hne : x ≠ y := fun e => by subst e; exact absurd (Int64.lt_iff_toInt_lt.mp hl) (Int.lt_irrefl _)
    rw [if_pos hl]; simp [hne]
  · rw [if_neg hl]
    by_cases he : x.toInt64 = y.toInt64
    · rw [if_pos he]; simp [toInt64_inj he]
    · have hne : x ≠ y := fun e => he (e ▸ rfl)
      rw [if_neg he]; simp [hne]

/-- A word below `2^63` reads as the same long. -/
theorem toInt_ofNat_lt {I : Nat} (h : I < 2 ^ 63) : (UInt64.ofNat I).toInt64.toInt = I := by
  have hu : (UInt64.ofNat I).toInt64.toUInt64.toNat = I := by simp; omega
  rw [toInt_bmod, hu, Int.bmod]; split <;> omega

/-- `x in y` on the direct path: the probe's first positions compared below `count y`. -/
theorem in_direct {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k (.atom .boolean)}
    (hx : Readable x.val.c) {t hb : ByteArray} {lo : Int64} (hd : direct .long y.val.c y.n = some (t, lo, hb))
    (hR : ∀ lo hi, foRRange y.val.c = some (lo, hi) → ∀ v ∈ y.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * y.n < USize.size) (hm : x.n < USize.size) (h : «in» x y = .ok r) :
    r.val.toList = inSpec x.val.toList y.val.toList := by
  have hS := USize.size_le
  obtain ⟨ys, R, hwy, hby, hly, hr, hlo, hin, rfl⟩ := direct_table hd hR hn8
  obtain ⟨nk, nmd, np, xs, hox, hwx, hbx, hlx⟩ := operand_long x.val hx hm
  unfold «in» at h
  rw [hd] at h
  simp only [dense, bytesOf_long hx hox, bind, Except.bind, pure, Except.pure] at h
  have hG := probe_spec hb ys y.n lo R hby hly (by omega) hr hlo hin _ xs hbx (by rw [hlx]; exact hm)
  generalize probe (firstTable hb y.n lo R) y.n lo (operandBytes 8 nmd np nk.toUSize) = g at h hG
  obtain ⟨e, -⟩ := onKey_key h
  obtain ⟨-, hc⟩ := cmp_bitAt Ew.lt Ew.i64 Ew.va g (one y.n.toUInt64) x.n.toUSize
  rw [USize.toNat_ofNat_of_lt' hm] at hc
  obtain ⟨-, gg⟩ := elemsW8_get hG
  unfold inSpec
  rw [Arr.toList_long x.val hwx, Arr.toList_long y.val hwy]
  apply List.ext_getElem (by rw [Arr.length_toList, e]; simp [hlx])
  intro i h1 _
  have hi : i < x.n := by rw [Arr.length_toList, e] at h1; exact h1
  rw [Arr.getElem_toList, Arr.get_bool_bits r.val (onKey_c h), hc i (by omega)]
  rw [show Ew.shapeIdx Ew.va i = (i, 0) from rfl, show Ew.elem Ew.i64 g i = Column.bitsAt g (i * 8) 8 from rfl,
    show Ew.elem Ew.i64 (one y.n.toUInt64) 0 = Column.bitsAt (one y.n.toUInt64) 0 8 from rfl, bitsAt_one,
    gg i (by simp [hlx, hi]), cmpStep_lt]
  simp only [List.getElem_map, hi, decide_true, Bool.true_and]
  have hI := List.idxOf_le_length (a := xs[i].toInt64) (l := ys.map UInt64.toInt64)
  rw [List.length_map, hly] at hI
  apply Bool.eq_iff_iff.2
  have hyn : y.n.toUInt64.toInt64.toInt = y.n := toInt_ofNat_lt (by omega)
  have hl : (ys.map UInt64.toInt64).length = y.n := by simp [hly]
  rw [decide_eq_true_iff, Int64.lt_iff_toInt_lt, toInt_ofNat_lt (by omega), hyn, Int.ofNat_lt, List.contains_iff_mem, ← List.idxOf_lt_length_iff, hl]

/-- A list element is at its own first index exactly when no earlier element equals it. -/
theorem idxOf_self_iff {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α) (i : Nat) (hi : i < l.length),
    l.idxOf l[i] = i ↔ ∀ j (hj : j < i), l[j]'(by omega) ≠ l[i]
  | [], _, hi => absurd hi (by simp)
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, hi => by
    have ih := idxOf_self_iff l i (by simpa using hi)
    have hi' : i < l.length := by simpa using hi
    rw [List.getElem_cons_succ, List.idxOf_cons]
    by_cases ha : a = l[i]'hi'
    · rw [show (a == l[i]'hi') = true by simp [ha], cond_true]
      exact ⟨fun h => by omega, fun h => absurd ha (h 0 (by omega))⟩
    · rw [show (a == l[i]'hi') = false by simp [ha], cond_false, Nat.add_right_cancel_iff, ih]
      constructor
      · intro h j hj
        cases j with
        | zero => exact ha
        | succ j => exact h j (by omega)
      · intro h j hj; exact h (j + 1) (by omega)

/-- `?x` on the direct path: the positions whose probe answers the position itself are the first
    occurrences, and the gather at them lists `eraseDups`. -/
theorem distinct_direct {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)}
    {t hb : ByteArray} {lo : Int64} (hd : direct .long x.val.c x.n = some (t, lo, hb)) (hu : x.val.attr ≠ 2)
    (hR : ∀ lo hi, foRRange x.val.c = some (lo, hi) → ∀ v ∈ x.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * x.n < USize.size) (h : distinct x = .ok r) : r.val.toList = distinctSpec x.val.toList := by
  have hS := USize.size_le
  have hn : x.n < USize.size := by omega
  obtain ⟨xs, R, hwx, hbx, hlx, hr, hlo, hin, rfl⟩ := direct_table hd hR hn8
  unfold distinct at h
  rw [show (x.val.attr == 2) = false by simp [hu], hd] at h
  dsimp only at h
  have hP := probe_spec hb xs x.n lo R hbx hlx hn hr hlo hin hb xs hbx (by rw [hlx]; exact hn)
  generalize probe (firstTable hb x.n lo R) x.n lo hb = P at h hP
  obtain ⟨-, hc⟩ := cmp_bitAt Ew.eq Ew.i64 Ew.vv P (tilLongs x.n.toUSize) x.n.toUSize
  rw [USize.toNat_ofNat_of_lt' hn] at hc
  generalize Ew.cmp Ew.eq Ew.i64 Ew.vv P (tilLongs x.n.toUSize) x.n.toUSize = bits at h hc
  change list .long (.bytes (gatherBytes 8 0 hb (whereBits x.n.toUSize bits))) 2 = .ok r at h
  -- the words as a function of the position
  let e : Nat → UInt64 := fun i => xs.getD i 0
  have hxe : xs = (List.range x.n).map e :=
    List.ext_getElem (by simp [hlx]) fun i h1 _ => by simp [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  obtain ⟨-, gP⟩ := elemsW8_get hP
  obtain ⟨-, gx⟩ := elemsW8_get hbx
  have htil := Verify.tilLongs_spec x.n.toUSize
  rw [USize.toNat_ofNat_of_lt' hn] at htil
  have htl : (Verify.elemsW 8 (tilLongs x.n.toUSize)).length = x.n := by
    rw [← List.length_map (f := UInt64.toNat), htil, List.length_range]
  have gT : ∀ i < x.n, (Column.bitsAt (tilLongs x.n.toUSize) (i * 8) 8).toNat = i := fun i hi => by
    have hv := List.getElem_of_eq htil (i := i) (by simp [htl]; omega)
    simpa [Verify.elemsW] using hv
  -- bit `i` marks a first occurrence
  have hF : (List.range x.n).filter (Column.bitAt bits) = Verify.firstsOf e x.n := by
    unfold Verify.firstsOf
    apply List.filter_congr
    intro i hi'
    have hi := List.mem_range.1 hi'
    have hil : i < xs.length := by omega
    rw [hc i (by omega), show Ew.shapeIdx Ew.vv i = (i, i) from rfl,
      show Ew.elem Ew.i64 P i = Column.bitsAt P (i * 8) 8 from rfl,
      show Ew.elem Ew.i64 (tilLongs x.n.toUSize) i = Column.bitsAt (tilLongs x.n.toUSize) (i * 8) 8 from rfl,
      gP i (by simp [hil]), cmpStep_eq]
    simp only [List.getElem_map, hi, decide_true, Bool.true_and]
    rw [idxOf_map_of_inj (fun _ _ => toInt64_inj)]
    have hI := List.idxOf_le_length (a := xs[i]) (l := xs)
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, List.all_eq_true, ← UInt64.toNat_inj, gT i hi, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
      idxOf_self_iff xs i hil]
    constructor
    · intro hne j hj; have hj := List.mem_range.1 hj
      simpa [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, List.getElem?_eq_getElem (show j < xs.length by omega)] using hne j hj
    · intro hall j hj
      have := hall j (List.mem_range.2 (by omega))
      simpa [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, List.getElem?_eq_getElem (show j < xs.length by omega)] using this
  have hL : ∀ i ∈ (List.range x.n.toUSize.toNat).filter (Column.bitAt bits), i < hb.size / (8 : USize).toNat := by
    intro i hi
    have := List.mem_range.1 (List.mem_filter.1 hi).1
    rw [USize.toNat_ofNat_of_lt' hn] at this
    rw [usize_eight, (elemsW8_get hbx).1, hlx]; exact this
  obtain ⟨gs, gj⟩ := Verify.gatherBytes_whereBits 8 (by rw [usize_eight]; decide) 0 hb x.n.toUSize bits hL
  rw [usize_eight, USize.toNat_ofNat_of_lt' hn, hF] at gs gj
  have hw : Verify.elemsW 8 (gatherBytes 8 0 hb (whereBits x.n.toUSize bits)) = (Verify.firstsOf e x.n).map e := by
    apply List.ext_getElem (by
      rw [List.length_map, Verify.elemsW, List.length_map, List.length_range, gs, Nat.mul_div_cancel_left _ (by decide)])
    intro j h1 h2
    have hj : j < (Verify.firstsOf e x.n).length := by simpa using h2
    have hlt : (Verify.firstsOf e x.n)[j] < xs.length := by
      have := (List.mem_filter.1 (List.getElem_mem hj)).1; rw [hlx]; exact List.mem_range.1 this
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [gj j hj, gx _ hlt]
    show _ = xs.getD _ 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [Arr.toList_long r.val (show longWords r.val.c = _ by rw [list_c h]; exact congrArg some hw), distinctSpec,
    Arr.toList_long x.val hwx, hxe, List.map_map, List.map_map]
  exact firstsOf_map_eraseDups e (UInt64.toInt64 ∘ e) (fun i j => ⟨congrArg UInt64.toInt64, toInt64_inj⟩) x.n


/-! ## The laws, on `bytes` and on `foR` alike -/

/-- `?x` on a long column is `distinctSpec`, from `distinct_words`. Restrictions: `attr ≠ 2`, the `u`
    shortcut, whose `Arr.attr` carries no proof of uniqueness; `longWords` defined, which excludes `alp`;
    on the direct path every element inside the block range (`direct_table`); `8 · x.n < USize.size`,
    which keeps the range below `2^63`. -/
theorem distinct_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {xs : List UInt64}
    (hx : longWords x.val.c = some xs) (hu : x.val.attr ≠ 2)
    (hR : ∀ lo hi, foRRange x.val.c = some (lo, hi) → ∀ v ∈ x.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * x.n < USize.size) (h : distinct x = .ok r) : r.val.toList = distinctSpec x.val.toList := by
  have hn : x.n < USize.size := by have := USize.size_le; omega
  obtain ⟨⟨t, lo, hb⟩, hd⟩ | hd : (∃ p, direct .long x.val.c x.n = some p) ∨ direct .long x.val.c x.n = none := by
    cases e : direct .long x.val.c x.n with
    | none => exact Or.inr rfl
    | some p => exact Or.inl ⟨p, rfl⟩
  · exact distinct_direct hd hu hR hn8 h
  obtain ⟨e, c, hxe, hv, hw⟩ := distinct_words x.val hx hn
  unfold distinct at h
  rw [show (x.val.attr == 2) = false by simp [hu], hd, hv] at h
  change list .long c 2 = .ok r at h
  rw [Arr.toList_long r.val (show longWords r.val.c = _ by rw [list_c h]; exact hw), distinctSpec,
    Arr.toList_long x.val hx, hxe, List.map_map, List.map_map]
  refine firstsOf_map_eraseDups _ _ (fun i j => ⟨fun h' => ?_, fun h' => ?_⟩) x.n
  · have e' : Order.rank .i64 (e i) = Order.rank .i64 (e j) := h'
    exact Int64.le_antisymm (rank_i64_le (UInt64.le_of_eq e')) (rank_i64_le (UInt64.le_of_eq e'.symm))
  · show Order.rank .i64 (e i) = Order.rank .i64 (e j)
    rw [toInt64_inj (x := e i) (y := e j) h']

/-- `x?y` on long columns is `findSpec`, from `findVec_idxOf` over the decoded operands. Restrictions:
    `Readable` payloads; on the direct path every element inside the block range (`direct_table`);
    `x.val.attr ≠ 1`, since the `s` halving (`findSortedBytes`) has no law yet; both counts below
    `USize.size`, which the kernel indexes by, and `8 · x.n` too, which keeps the range below `2^63`. -/
theorem find_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k' (.atom .long)}
    (hx : Readable x.val.c) (hy : Readable y.val.c) (hs : x.val.attr ≠ 1)
    (hR : ∀ lo hi, foRRange x.val.c = some (lo, hi) → ∀ v ∈ x.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * x.n < USize.size) (hm : y.n < USize.size) (h : find x y = .ok r) :
    r.val.toList = findSpec x.val.toList y.val.toList := by
  have hn : x.n < USize.size := by have := USize.size_le; omega
  obtain ⟨⟨t, lo, hb⟩, hd⟩ | hd : (∃ p, direct .long x.val.c x.n = some p) ∨ direct .long x.val.c x.n = none := by
    cases e : direct .long x.val.c x.n with
    | none => exact Or.inr rfl
    | some p => exact Or.inl ⟨p, rfl⟩
  · exact find_direct hy hd hR hn8 hm h
  obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := operand_long x.val hx hn
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y.val hy hm
  unfold find at h
  rw [hd, show (x.val.attr == 1) = false by simp [hs], findColumn_long, probeColumns_long false hox hoy] at h
  generalize operandBytes 8 hmd hp hk.toUSize = Bx at h hbx
  generalize operandBytes 8 nmd np nk.toUSize = By at h hby
  change onKey y.key .long (.bytes (findVec 8 false Bx By)) "x?y" = .ok r at h
  obtain ⟨hsx, -⟩ := elemsW8_get hbx
  obtain ⟨hsy, gy⟩ := elemsW8_get hby
  obtain ⟨hF, hj⟩ := Verify.findVec_idxOf 8 false Bx By (by rw [usize_eight, hsx, hlx]; exact hn)
  rw [usize_eight] at hF hj
  simp only [hbx, Nat.le_refl, ↓reduceIte, show normalise 8 false = id from rfl, List.map_id, id_eq] at hj
  rw [Arr.toList_long r.val (show longWords r.val.c = some (Verify.elemsW 8 (findVec 8 false Bx By)) by
    rw [onKey_c h]; rfl), Arr.toList_long x.val hwx, Arr.toList_long y.val hwy, findSpec]
  apply List.ext_getElem (by simp [Verify.elemsW, hF, hsy])
  intro j h1 h2
  have hj' : j < ys.length := by simpa using h2
  simp only [List.getElem_map, Verify.elemsW, List.getElem_range]
  rw [idxOf_map_of_inj (fun _ _ => toInt64_inj)]
  exact toInt64_of_toNat (by rw [hj j (by rw [hsy]; exact hj'), gy j hj'])

/-- `x in y` on long columns is `inSpec`, from `memberVec_mem` over the decoded operands. Restrictions:
    `Readable` payloads; on the direct path every element of `y` inside the block range
    (`direct_table`); `y.val.attr ≠ 1`, since the `s` halving (`memberSortedBytes`) has no law yet; both
    counts below `USize.size`, which the kernel indexes by, and `8 · y.n` too, which keeps the range
    below `2^63`. -/
theorem in_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k (.atom .boolean)}
    (hx : Readable x.val.c) (hy : Readable y.val.c) (hs : y.val.attr ≠ 1)
    (hR : ∀ lo hi, foRRange y.val.c = some (lo, hi) → ∀ v ∈ y.val.toList, lo ≤ v ∧ v ≤ hi)
    (hn8 : 8 * y.n < USize.size) (hm : x.n < USize.size) (h : «in» x y = .ok r) :
    r.val.toList = inSpec x.val.toList y.val.toList := by
  have hn : y.n < USize.size := by have := USize.size_le; omega
  obtain ⟨⟨t, lo, hb⟩, hd⟩ | hd : (∃ p, direct .long y.val.c y.n = some p) ∨ direct .long y.val.c y.n = none := by
    cases e : direct .long y.val.c y.n with
    | none => exact Or.inr rfl
    | some p => exact Or.inl ⟨p, rfl⟩
  · exact in_direct hx hd hR hn8 hm h
  obtain ⟨hk, hmd, hp, ys, hoy, hwy, hby, hly⟩ := operand_long y.val hy hn
  obtain ⟨nk, nmd, np, xs, hox, hwx, hbx, hlx⟩ := operand_long x.val hx hm
  unfold «in» at h
  rw [hd, show (y.val.attr == 1) = false by simp [hs], memberColumn_long, probeColumns_long true hoy hox] at h
  generalize operandBytes 8 hmd hp hk.toUSize = By at h hby
  generalize operandBytes 8 nmd np nk.toUSize = Bx at h hbx
  change onKey x.key .boolean (.bits (Column.count .long x.val.c) (memberVec 8 false Bx By)) "x in y" = .ok r at h
  obtain ⟨e, -⟩ := onKey_key h
  obtain ⟨hsx, gx⟩ := elemsW8_get hbx
  obtain ⟨hsy, -⟩ := elemsW8_get hby
  obtain ⟨-, hj⟩ := Verify.memberVec_mem 8 false Bx By (by rw [usize_eight, hsy, hly]; exact hn)
  rw [usize_eight] at hj
  simp only [Nat.le_refl, ↓reduceIte, show normalise 8 false = id from rfl, List.map_id, hby, id_eq] at hj
  unfold inSpec
  rw [Arr.toList_long x.val hwx, Arr.toList_long y.val hwy]
  apply List.ext_getElem (by rw [Arr.length_toList, e]; simp [hlx])
  intro i h1 _
  have hi : i < x.n := by rw [Arr.length_toList, e] at h1; exact h1
  rw [Arr.getElem_toList, Arr.get_bool_bits r.val (onKey_c h)]
  simp only [List.getElem_map]
  rw [hj i (by rw [hsx, hlx]; omega)]
  simp only [hsx, hlx, hi, decide_true, Bool.true_and, gx i (by omega)]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, List.contains_iff_mem, mem_map_of_inj (fun _ _ => toInt64_inj)]

/-- A test that holds exactly below `p ≤ n` holds at `p` of the first `n` indices. -/
theorem countP_range_lt (q : Nat → Bool) {p n : Nat} (hp : p ≤ n) (hq : ∀ i < n, q i = decide (i < p)) :
    (List.range n).countP q = p := by
  suffices ∀ m ≤ n, (List.range m).countP q = min m p by rw [this n (Nat.le_refl n)]; omega
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.countP_append, ih (by omega), List.countP_singleton, hq m (by omega)]
    by_cases h : m < p <;> simp [h] <;> omega

/-- `x bin y` on long columns is `binSpec` over a sorted `x`, from `bitsAt_binBytes` and `binStep_spec`
    at each needle, over the operands `binOperands` decodes. Restrictions: `Readable` payloads; both counts
    below `USize.size`, which the kernel takes; `x` ascending, which is what `binSpec` assumes — on an
    unsorted `x` the answer is whatever the halving visits. -/
theorem bin_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k' (.atom .long)}
    (hx : Readable x.val.c) (hy : Readable y.val.c) (hn : x.n < USize.size) (hm : y.n < USize.size)
    (hsort : ∀ i j : Fin x.n, i ≤ j → x.val.get i ≤ x.val.get j) (h : bin x y = .ok r) :
    r.val.toList = binSpec x.val.toList y.val.toList := by
  obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := operand_long x.val hx hn
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y.val hy hm
  unfold bin at h
  rw [binColumn_long, hox, hoy] at h
  change onKey y.key .long (.bytes (binBytes 8 false true false (operandBytes 8 hmd hp hk.toUSize)
    (operandBytes 8 nmd np nk.toUSize))) "x bin y" = .ok r at h
  generalize operandBytes 8 hmd hp hk.toUSize = hb at h hbx
  generalize operandBytes 8 nmd np nk.toUSize = kb at h hby
  obtain ⟨e, -⟩ := onKey_key h
  obtain ⟨hsx, gx⟩ := elemsW8_get hbx
  have hxn : hb.size / 8 = x.n := hsx.trans hlx
  have hyn : kb.size / 8 = y.n := (elemsW8_get hby).1.trans hly
  have hle : ∀ i j (hi : i < x.n) (hj : j < x.n), (ordKey 8 false true (Column.bitsAt hb (i * 8) 8) ≤
      ordKey 8 false true (Column.bitsAt hb (j * 8) 8) ↔ x.val.get ⟨i, hi⟩ ≤ x.val.get ⟨j, hj⟩) :=
    fun i j hi hj => by
      rw [ordKey_long, ordKey_long, rank_i64_le_iff, Arr.get_long x.val hwx i hi (by omega),
        Arr.get_long x.val hwx j hj (by omega), gx i (by omega), gx j (by omega)]
  unfold binSpec
  rw [Arr.toList_long_bytes r.val (onKey_c h), Arr.toList_long x.val hwx, Arr.toList_long y.val hwy, ← hbx, ← hby,
    Verify.elemsW, Verify.elemsW, hxn, hyn, e]
  simp only [List.map_map, List.countP_map]
  apply List.map_congr_left
  intro j hj'
  have hj := List.mem_range.1 hj'
  have hk := Verify.bitsAt_binBytes 8 false true false hb kb j (by rw [usize_eight, hyn]; exact hj)
  simp only [usize_eight, Bool.false_eq_true, ↓reduceIte, Nat.mul_comm 8 j, hxn] at hk
  obtain ⟨hp', hlo, hhi⟩ := Verify.binStep_spec 8 false true false hb
    (ordKey 8 false true (Column.bitsAt kb (j * 8) 8)) x.n
    (fun i j hij hjn => (hle i j (by omega) hjn).2 (hsort ⟨i, by omega⟩ ⟨j, hjn⟩ hij))
  simp only [Bool.false_eq_true, ↓reduceIte] at hlo hhi
  have hcmp : ∀ i, i < x.n → (ordKey 8 false true (Column.bitsAt hb (i * 8) 8) ≤
      ordKey 8 false true (Column.bitsAt kb (j * 8) 8) ↔ (Column.bitsAt hb (i * 8) 8).toInt64 ≤
        (Column.bitsAt kb (j * 8) 8).toInt64) := fun i _ => by rw [ordKey_long, ordKey_long, rank_i64_le_iff]
  simp only [Function.comp_apply]
  rw [countP_range_lt _ hp' fun i hi => by
    apply Bool.eq_iff_iff.2
    simp only [Function.comp_apply, decide_eq_true_iff]
    exact ⟨fun hc => Classical.byContradiction fun hn => hhi i (by omega) hi ((hcmp i hi).2 hc),
      fun hl => (hcmp i hi).1 (hlo i hl)⟩]
  rw [hk, Int64.toInt64_toUInt64, Int.toInt64, Int64.ofInt_sub]
  rfl


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
-- `(0N; -0W)` encoded: the block metadata leaves the null out of `[base, maxv]`, so the range does not
-- hold `0N`; the laws' in-range hypothesis fails here, and `direct` takes the path anyway (open)
private def xnc := Coc.encode 8 (packLongs [0x8000000000000000, -0x7fffffffffffffff])
private def xn : Rel (.atom .long) (.atom .long) := ⟨2, .til 2, { c := .foR 2 xnc.1 xnc.2, wf := ⟨rfl, rfl⟩ }⟩
#guard foRRange xn.val.c == some (-0x7fffffffffffffff, -0x7fffffffffffffff) && (direct .long xn.val.c 2).isSome
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
#print axioms firstTable_spec
#print axioms probe_spec
#print axioms find_direct
#print axioms cmp_bitAt
#print axioms in_direct
#print axioms distinct_direct
#print axioms where_toList
#print axioms firstsOf_map_eraseDups
#print axioms distinct_toList
#print axioms find_toList
#print axioms in_toList
#print axioms bin_toList

end LeetQ.Rel.Find
