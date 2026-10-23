/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import QLean.Value
import QLean.Dep.Val

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

end Arr

/-- Ascending offsets from `0` to `n`: `g+1` cut points of `n` positions into `g` groups. -/
def Cuts {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Prop :=
  (∀ i j, i ≤ j → o.get i ≤ o.get j) ∧ o.get 0 = 0 ∧ (o.get (Fin.last g)).toInt = n

instance {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Decidable (Cuts o n) := by
  unfold Cuts; infer_instance

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

/-- `n` longs, dense, eight bytes each. -/
private def longs (xs : List Int64) : Column := .bytes (xs.foldl (fun b x => pushBits b x.toUInt64 8) .empty)

private def l3 : Arr (.atom .long) 3 := { c := longs [7, -1, 42], wf := by decide }
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
private def o3 : Arr (.atom .long) 4 := { c := longs [0, 1, 1, 3], wf := by decide }
private def ds : Arr (.atom .symbol) 3 := { c := .syms (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7], wf := by decide }
private def grpKey : KeyCol (.atom .symbol) 3 := .grp (.arr ds) o3 (by decide)
#guard grpKey.toList == ["a", "d", "d"]
-- the parted list `(10 20; 30)`: positions `0 1 | 2`, keys `0 0 1`
private def o2 : Arr (.atom .long) 3 := { c := longs [0, 2, 3], wf := by decide }
private def parted : Rel (.atom .long) (.atom .long) := ⟨3, .grp (.til 2) o2 (by decide), { c := longs [10, 20, 30], wf := by decide }⟩
#guard parted.toList == [(0, 10), (0, 20), (1, 30)]
example : parted.Holds 1 30 := (parted.holds_iff_mem_toList 1 30).2 (by decide)
#guard (Rel.mk 3 (.til 3) ss).toList == [(0, "bc"), (1, "a"), (2, "bc")]

end Checks

#print axioms Arr.get
#print axioms KeyCol.get
#print axioms Rel.holds_iff_mem_toList

end LeetQ.Rel
