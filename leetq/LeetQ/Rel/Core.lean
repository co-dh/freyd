/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import QLean.Value
import QLean.Dep.Val
import QLean.Kernel.Sort
import QLean.Kernel.Search
import QLean.Kernel.Structural

namespace LeetQ.Rel

open QLean QLean.Dep

/-- An element type: a q atomic type, or `gen` — q type 0, elements boxed as `QValue`. -/
inductive Ty
  | atom (a : QAtomicType)
  | gen

/-- The element at `t`: qlean's `Carrier` at an atomic type, a boxed `QValue` at `gen`. -/
@[reducible] def El : Ty → Type
  | .atom a => Carrier a
  | .gen => QValue

/-- The payload at `t`: a qlean column, or at `gen` the `Array QValue` of `QValue.list`. -/
@[reducible] def Pay : Ty → Type
  | .atom _ => Column
  | .gen => Array QValue

/-- The constructors a column of type `a` may take: `bits` for booleans, `syms` or `enum` for
    symbols, `bytes` for guids, `bytes`/`foR`/`alp` for the other fixed-width types. -/
def Column.admits : QAtomicType → Column → Bool
  | .boolean, .bits .. => true
  | .symbol, .syms .. | .symbol, .enum .. => true
  | .guid, .bytes _ => true
  | .boolean, _ | .symbol, _ | .guid, _ => false
  | _, .bytes _ | _, .foR .. | _, .alp .. => true
  | _, _ => false

/-- `c` is well-formed at `t` and holds `n` elements. -/
def Ty.WF : (t : Ty) → Nat → Pay t → Prop
  | .atom a, n, c => Column.admits a c = true ∧ Column.count a c = n
  | .gen, n, xs => xs.size = n

instance (t : Ty) (n : Nat) (c : Pay t) : Decidable (t.WF n c) := by
  cases t <;> unfold Ty.WF <;> infer_instance

/-- A column of `n` elements of type `t`. `attr` is q's attribute byte (`QValue.marked`'s codes, the
    `ctorIdx` of `Dep.Attributes.Attr`: 1 sorted, 2 unique, 3 parted, 4 grouped), set by producers and
    read by consumers (§2.4); `ix` is the `IndexCell` the first lookup builds. -/
structure Arr (t : Ty) (n : Nat) where
  c : Pay t
  wf : t.WF n c
  attr : UInt8 := 0
  ix : Option IndexCell := none

namespace Arr

variable {t : Ty} {n : Nat}

/-- Element `i`. At an atomic type it is `Column.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`. -/
def get : {t : Ty} → Arr t n → Fin n → El t
  | .atom a, x, i => ((Column.get a x.c i).bind (Carrier.of? a)).getD (Carrier.ofAtom (Column.atomOfBits_type a 0))
  | .gen, x, i => x.c[i.1]'(by have h : x.c.size = n := x.wf; omega)

/-- The elements in position order, for proofs only. -/
def toList (x : Arr t n) : List (El t) := List.ofFn x.get

theorem length_toList (x : Arr t n) : x.toList.length = n := List.length_ofFn

theorem getElem_toList (x : Arr t n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x.get ⟨i, by rw [length_toList] at h; exact h⟩ := List.getElem_ofFn ..

/-- A kernel's answer as an `Arr`, the one way in: `wf` is decided (two O(1) reads at an atomic type, the
    constructor and the count), never assumed; `what` names the producer in the error. -/
def of (t : Ty) (n : Nat) (c : Pay t) (what : String) (attr : UInt8 := 0) : Except String (Arr t n) :=
  if h : t.WF n c then .ok ⟨c, h, attr, none⟩
  else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"

end Arr

/-- Ascending offsets from `0` to `n`: `g+1` cut points of `n` positions into `g` groups. -/
def Cuts {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Prop :=
  (∀ i j, i ≤ j → o.get i ≤ o.get j) ∧ o.get 0 = 0 ∧ (o.get (Fin.last g)).toInt = n

instance {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Decidable (Cuts o n) := by
  unfold Cuts; infer_instance

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`KeyCol.group` read by `binBytes`). -/
def groupOf (o : ByteArray) (n : Nat) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n.toUSize)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = .bytes b) (i : Fin m) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  have hn : i.1 < Column.count .long (.bytes b) := by have := x.wf.2; rw [hc] at this; omega
  show ((Column.get .long x.c i.1).bind (Carrier.of? .long)).getD _ = _
  rw [hc]; simp only [Column.get, if_pos hn]; rfl

/-- Below `2^i`, xor with `2^i` sets that bit: it adds `2^i`. -/
theorem xor_two_pow_of_lt {r i : Nat} (h : r < 2 ^ i) : r ^^^ 2 ^ i = 2 ^ i + r := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j i with hj | rfl | hj
  · rw [Nat.testBit_two_pow_add_gt hj]; simp [Nat.ne_of_gt hj]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]; simp
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    rw [Nat.pow_succ] at hp
    rw [Nat.testBit_lt_two_pow (show 2 ^ i + r < 2 ^ j by omega), Nat.testBit_lt_two_pow (show r < 2 ^ j by omega)]
    simp [Nat.ne_of_lt hj]

/-- Flipping bit 63 of a 64-bit number moves it by `2^63`: up below `2^63`, down at or above. -/
theorem xor_two_pow_63 (n : Nat) (h : n < 2 ^ 64) : n ^^^ 2 ^ 63 = if n < 2 ^ 63 then n + 2 ^ 63 else n - 2 ^ 63 := by
  split
  · rw [xor_two_pow_of_lt ‹_›]; omega
  · have e : n = (n - 2 ^ 63) ^^^ 2 ^ 63 := by rw [xor_two_pow_of_lt (show n - 2 ^ 63 < 2 ^ 63 by omega)]; omega
    conv => lhs; rw [e]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `Order.rank .i64` flips the sign bit: unsigned order on ranks is signed order on longs. Both sides are
    read as naturals — the rank by `xor_two_pow_63`, the long by `toInt_eq_msb_cond` — and compared by `omega`. -/
theorem rank_i64_le {x y : UInt64} (h : Kernel.Order.rank .i64 x ≤ Kernel.Order.rank .i64 y) : x.toInt64 ≤ y.toInt64 := by
  simp only [Kernel.Order.rank] at h
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_xor, UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl,
    xor_two_pow_63 _ x.toNat_lt, xor_two_pow_63 _ y.toNat_lt] at h
  rw [Int64.le_iff_toInt_le, Int64.toInt, Int64.toInt, BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  show (if decide (2 ^ 63 ≤ x.toNat) = true then (x.toNat : Int) - (2 ^ 64 : Nat) else x.toNat) ≤
    (if decide (2 ^ 63 ≤ y.toNat) = true then (y.toNat : Int) - (2 ^ 64 : Nat) else y.toNat)
  have := x.toNat_lt; have := y.toNat_lt
  split <;> split <;> split at h <;> split at h <;> simp_all <;> omega

/-- `Cuts` from `Order.ascending`'s Lean body on the dense payload, and the two end reads. -/
theorem cuts_of_ascending {g n : Nat} (o : Arr (.atom .long) (g+1)) {b : ByteArray} (hc : o.c = .bytes b)
    (hu : g + 1 < USize.size) (ha : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true)
    (h0 : o.get 0 = 0) (hl : (o.get (Fin.last g)).toInt = n) : Cuts o n := by
  refine ⟨?_, h0, hl⟩
  have hsz : b.size / 8 = g + 1 := by have := o.wf.2; rw [hc] at this; exact this
  have adj : ∀ i (h : i + 1 < g + 1), o.get ⟨i, by omega⟩ ≤ o.get ⟨i + 1, h⟩ := by
    intro i h
    simp only [Kernel.Order.ascending, List.all_eq_true, List.mem_range] at ha
    have hm : (g + 1).toUSize.toNat = g + 1 := USize.toNat_ofNat_of_lt hu
    have := ha i (by simp only [Kernel.Scan.Kind.avail, Kernel.Scan.Kind.width, hm, hsz]; omega)
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq, Kernel.Order.keyAt, Kernel.Scan.Kind.bitsAt,
      Kernel.Scan.Kind.width] at this
    rw [Arr.get_long_bytes o hc, Arr.get_long_bytes o hc]
    exact rank_i64_le this
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  change i ≤ j at hij
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => exact Int64.le_refl _
  | succ d ih => exact Int64.le_trans (ih (by omega) (by omega)) (adj (i + d) hj)

/-- A key column of `n` keys of type `k`, storing only what q stores. -/
inductive KeyCol : Ty → Nat → Type
  /-- A list: key `i` is `i`, nothing stored. -/
  | til (n : Nat) : KeyCol (.atom .long) n
  /-- Grouped: key `i` is `d`'s key of the group holding `i`; `o` holds q's one offset per group. -/
  | grp {k : Ty} {g n : Nat} (d : KeyCol k g) (o : Arr (.atom .long) (g+1)) (wf : Cuts o n) : KeyCol k n
  /-- A dict or a multi-valued relation: an explicit key column. -/
  | arr {k : Ty} {n : Nat} (a : Arr k n) : KeyCol k n

namespace KeyCol

/-- The number of cut points after the first at or below `i`: the largest `r` with `o[r] ≤ i`, which
    under `Cuts` is the group holding `i`. -/
def group {g : Nat} (o : Arr (.atom .long) (g+1)) (i : Nat) : Nat :=
  (List.finRange g).countP fun r => (o.get r.succ).toInt ≤ i

/-- Key `i`. -/
def get : {k : Ty} → {n : Nat} → KeyCol k n → Fin n → El k
  | _, _, .til _, i => Int64.ofNat i
  | _, n, .grp (g := g) d o wf, i =>
    -- the `min` is unreachable under `Cuts`, which puts `i < o[g]` and so `group o i < g`
    if h : 0 < g then d.get ⟨min (group o i) (g - 1), by omega⟩ else absurd i.2 (by
      obtain rfl : g = 0 := by omega
      have h2 := wf.2.2; rw [show Fin.last 0 = 0 from rfl, wf.2.1] at h2; simp at h2; omega)
  | _, _, .arr a, i => a.get i

/-- The keys in position order, for proofs only. -/
def toList {k : Ty} {n : Nat} (c : KeyCol k n) : List (El k) := List.ofFn c.get

/-- A long payload as dense bytes: `bytes` as it is, `foR` decoded once (`Coc.decode`). -/
def longBytes : Column → Option ByteArray
  | .bytes b => some b
  | .foR m md pk => some (Kernel.Coc.decode 8 md pk m.toUSize)
  | _ => none

/-- `grp d o` built at run time: `Cuts` decided by `Order.ascending` on `o`'s dense payload and one read of
    each end, `cuts_of_ascending` turning the kernel's answer into the proof. `none` when `o` is not cuts of `n`. -/
def grp? {k : Ty} {g : Nat} (d : KeyCol k g) (o : Arr (.atom .long) (g+1)) (n : Nat) : Option (KeyCol k n) := do
  let b ← longBytes o.c
  if h : (Ty.atom .long).WF (g+1) (.bytes b) ∧ g + 1 < USize.size then
    let ob : Arr (.atom .long) (g+1) := ⟨.bytes b, h.1, o.attr, none⟩
    if hc : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true ∧ ob.get 0 = 0 ∧ (ob.get (Fin.last g)).toInt = n then
      some (.grp d ob (cuts_of_ascending ob rfl h.2 hc.1 hc.2.1 hc.2.2))
    else none
  else none

end KeyCol

/-- A relation from `k` to `v`: `n` positions, a key and a value at each. -/
structure Rel (k v : Ty) where
  n : Nat
  key : KeyCol k n
  val : Arr v n

namespace Rel

variable {k v : Ty}

/-- The relation `R` denotes: `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y`. -/
def Holds (R : Rel k v) (x : El k) (y : El v) : Prop := ∃ i, R.key.get i = x ∧ R.val.get i = y

/-- The pairs, in position order, for proofs only. -/
def toList (R : Rel k v) : List (El k × El v) := List.ofFn fun i => (R.key.get i, R.val.get i)

theorem holds_iff_mem_toList (R : Rel k v) (x : El k) (y : El v) : R.Holds x y ↔ (x, y) ∈ R.toList := by
  simp [Holds, toList, List.mem_ofFn]

end Rel

/-! ## Sanity checks on small literal columns -/

section Checks

open QLean.Column


private def l3 : Arr (.atom .long) 3 := { c := .bytes <| packLongs [7, -1, 42], wf := by decide }
#guard l3.toList == [7, -1, 42]

private def bs : Arr (.atom .boolean) 3 := { c := .bits 3 (ByteArray.mk #[0b101]), wf := by decide }
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr (.atom .symbol) 3 := { c := .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], wf := by decide }
private def es : Arr (.atom .symbol) 3 :=
  { c := .enum 3 blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!), wf := by decide }
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .gen 2 := { c := #[.atom (.long 1), .list #[]], wf := rfl }
#guard match gs.get 0, gs.get 1 with | .atom (.long 1), .list #[] => true | _, _ => false

-- groups `[0,1) [1,1) [1,3)` under the keys `a bc d`: the empty middle group owns no position
private def o3 : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 1, 1, 3], wf := by decide }
private def ds : Arr (.atom .symbol) 3 := { c := .syms (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7], wf := by decide }
private def grpKey : KeyCol (.atom .symbol) 3 := .grp (.arr ds) o3 (by decide)
#guard grpKey.toList == ["a", "d", "d"]
-- the parted list `(10 20; 30)`: positions `0 1 | 2`, keys `0 0 1`
private def o2 : Arr (.atom .long) 3 := { c := .bytes <| packLongs [0, 2, 3], wf := by decide }
private def parted : Rel (.atom .long) (.atom .long) := ⟨3, .grp (.til 2) o2 (by decide), { c := .bytes <| packLongs [10, 20, 30], wf := by decide }⟩
-- `grp?` decides the same `Cuts` at run time, on `bytes` and on `foR` offsets
private def o3f : Arr (.atom .long) 4 :=
  { c := .foR 4 (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).1
      (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).2, wf := ⟨rfl, rfl⟩ }
#guard [o3, o3f].all fun o => ((KeyCol.grp? (.arr ds) o 3).map KeyCol.toList) == some ["a", "d", "d"]
#guard ((KeyCol.grp? (.til 2) o2 3).map KeyCol.toList) == some [0, 0, 1]
#guard (KeyCol.grp? (.til 2) o2 4).isNone
#guard (KeyCol.grp? (.til 2) ({ c := .bytes <| packLongs [0, 2, 1], wf := by decide } : Arr (.atom .long) 3) 1).isNone
#guard (KeyCol.grp? (.til 2) ({ c := .bytes <| packLongs [1, 2, 3], wf := by decide } : Arr (.atom .long) 3) 3).isNone
#guard parted.toList == [(0, 10), (0, 20), (1, 30)]
example : parted.Holds 1 30 := (parted.holds_iff_mem_toList 1 30).2 (by decide)
#guard (Rel.mk 3 (.til 3) ss).toList == [(0, "bc"), (1, "a"), (2, "bc")]

end Checks

#print axioms Arr.get
#print axioms KeyCol.get
#print axioms KeyCol.grp?
#print axioms cuts_of_ascending
#print axioms Rel.holds_iff_mem_toList

end LeetQ.Rel
