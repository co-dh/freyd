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

/-! ## The laws, on `bytes` and on `foR` alike -/

/-- `?x` on a long column is `distinctSpec`, from `distinct_words`. Restrictions: `attr ≠ 2`, the `u`
    shortcut, whose `Arr.attr` carries no proof of uniqueness; `longWords` defined, which excludes `alp`;
    `direct` declining (TODO below); `x.n < USize.size`, the count `distinct` takes. -/
theorem distinct_toList {k : Ty} {x : Rel k (.atom .long)} {r : Rel (.atom .long) (.atom .long)} {xs : List UInt64}
    (hx : longWords x.val.c = some xs) (hd : direct .long x.val.c x.n = none) (hu : x.val.attr ≠ 2)
    (hn : x.n < USize.size) (h : distinct x = .ok r) : r.val.toList = distinctSpec x.val.toList := by
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
    `Readable` payloads; `direct` declining (TODO below); `x.val.attr ≠ 1`, since the `s` halving
    (`findSortedBytes`) has no law yet; both counts below `USize.size`, which the kernel indexes by. -/
theorem find_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k' (.atom .long)}
    (hx : Readable x.val.c) (hy : Readable y.val.c) (hd : direct .long x.val.c x.n = none) (hs : x.val.attr ≠ 1)
    (hn : x.n < USize.size) (hm : y.n < USize.size) (h : find x y = .ok r) :
    r.val.toList = findSpec x.val.toList y.val.toList := by
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
    `Readable` payloads; `direct` declining (TODO below); `y.val.attr ≠ 1`, since the `s` halving
    (`memberSortedBytes`) has no law yet; both counts below `USize.size`, which the kernel indexes by. -/
theorem in_toList {k k' : Ty} {x : Rel k (.atom .long)} {y : Rel k' (.atom .long)} {r : Rel k (.atom .boolean)}
    (hx : Readable x.val.c) (hy : Readable y.val.c) (hd : direct .long y.val.c y.n = none) (hs : y.val.attr ≠ 1)
    (hn : y.n < USize.size) (hm : x.n < USize.size) (h : «in» x y = .ok r) :
    r.val.toList = inSpec x.val.toList y.val.toList := by
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
#print axioms firstsOf_map_eraseDups
#print axioms distinct_toList
#print axioms find_toList
#print axioms in_toList
#print axioms bin_toList

end LeetQ.Rel.Find
