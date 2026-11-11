/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import QLean.Value
import QLean.Dep.Val
import QLean.Dep.Monadic
import QLean.Kernel.Sort
import QLean.Kernel.Search
import QLean.Kernel.Structural
import QLean.Kernel.Elementwise
import QLean.Kernel.Scan
import QLean.Verify.Encoding
import QLean.Verify.SymFind
import QLean.Verify.Alp

namespace LeetQ.Rel

open QLean QLean.Dep

/-- An element of a column of type `t`: qlean's `Carrier`, a `QValue` in a general list. -/
abbrev El := Carrier

/-- A vector of `n` elements of type `t`: qlean's typed vector, `QValue.WFAt` saying the header is `t`, `n`
    and `Enc.WF` that the payload agrees with it; a general list is `.gen xs`. q's attribute is the vector's
    own (codes 1 sorted, 2 unique, 3 parted, 4 grouped, with the `IndexCell` of its index), set by producers
    and read by consumers (§2.4). -/
abbrev Arr (t : QAtomicType) (n : Nat) := {v : QValue // v.WFAt t n}

namespace Arr

variable {t : QAtomicType} {n : Nat}

/-- The payload. The fallback is unreachable: `WFAt` holds only of a `vector`. -/
def enc (x : Arr t n) : Enc := match x.1 with | .vector _ _ e _ => e | _ => .gen #[]

/-- The payload agrees with the header. -/
theorem wf (x : Arr t n) : Enc.WF t n x.enc := by
  obtain ⟨v, h⟩ := x; cases v <;> first | exact h.2.2 | exact h.elim

/-- `e` under the header `t`, `n` and the attribute `a`. -/
def mk (e : Enc) (h : Enc.WF t n e) (a : Option (UInt8 × IndexCell) := none) : Arr t n := ⟨.vector t n e a, rfl, rfl, h⟩

/-- A general list's payload is `gen` and holds its `n` elements. -/
theorem gen_size (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs) : xs.size = n := by
  have hw := x.wf; rw [hc] at hw; exact hw

/-- Element `i`. At an atom type it is `Enc.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`, as is the general list's non-`gen` one. -/
def get (x : Arr t n) (i : Fin n) : El t :=
  match t, x with
  | .general, x => match hc : x.enc with
    | .gen xs => xs[i.1]'(by rw [gen_size x hc]; exact i.2)
    | _ => QValue.general #[]
  | t, x => ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default

/-- `get` at an atom type: `Enc.get`'s atom read back at `t`. -/
theorem get_ne (x : Arr t n) (i : Fin n) (h : t ≠ .general) :
    x.get i = ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default := by
  cases t <;> first | exact absurd rfl h | rfl

/-- The elements in position order, for proofs only. -/
def toList (x : Arr t n) : List (El t) := List.ofFn x.get

theorem length_toList (x : Arr t n) : x.toList.length = n := List.length_ofFn

/-- A kernel's answer as an `Arr`, the one way in: `WFAt` is decided (the header's two fields and
    `Enc.WF`), never assumed; `what` names the producer in the error. The vector is the kernel's, mark
    and all; a producer that knows an attribute applies it after. -/
def of (t : QAtomicType) (n : Nat) (v : QValue) (what : String) : Except String (Arr t n) :=
  match v with
  | .vector t' n' e a => if h : t' = t ∧ n' = n ∧ Enc.WF t n e then .ok ⟨.vector t' n' e a, h⟩
    else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"
  | _ => .error s!"{what}: the kernel answered a value that is not a vector"

end Arr

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`binBytes`). -/
def groupOf (o : ByteArray) (n : Nat) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n.toUSize)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

theorem packLongs_size (xs : List Int64) : (packLongs xs).size = 8 * xs.length := by
  suffices ∀ b : ByteArray, (xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) b).size = b.size + 8 * xs.length by
    simpa [packLongs] using this .empty
  induction xs with
  | nil => simp
  | cons x xs ih => intro b; rw [List.foldl_cons, ih, Column.pushBits_size, List.length_cons]; omega

/-- The column of `f` at the positions `0 … n-1`, packed by Lean with no kernel and no `List`: the reference
    beside a kernel whose count is checked. -/
def colFn (n : Nat) (f : Fin n → Int64) : Arr .long n :=
  Arr.mk (.bytes ((Array.ofFn f).foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty)) (by
    show _ = n * 8; rw [← Array.foldl_toList]
    show (packLongs (Array.ofFn f).toList).size = n * 8; rw [packLongs_size]; simp [Nat.mul_comm])

/-- `xs` Frame-of-Reference encoded is well formed: the checks' `foR` columns, which `decide` cannot
    evaluate through `Coc.encode`. -/
theorem foRLongs_wf (xs : List Int64) : Enc.WF .long xs.length
    (.foR (Kernel.Coc.encode 8 (packLongs xs)).1 (Kernel.Coc.encode 8 (packLongs xs)).2) := by
  have h := Verify.nblk_encode 8 (by decide) (by decide) (packLongs xs)
  rw [packLongs_size] at h
  refine ⟨rfl, by simp, by simp, ?_⟩
  show xs.length ≤ Column.blk * Column.nblk (Kernel.Coc.encode (8 : Nat).toUSize (packLongs xs)).1
  rw [h]; simp only [Column.blk]; omega

/-- Under `wf`, a long `bytes` column holds `b.size / 8` elements. -/
theorem Arr.n_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b) :
    b.size / 8 = m := by
  have hw := x.wf
  simp only [Enc.WF, hc, QAtomicType.width] at hw; omega

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b) (i : Fin m) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  rw [Arr.get_ne x i (by decide)]
  simp only [Enc.get, if_pos i.2, hc, QAtomicType.width]; rfl

/-- Reading a word as a long loses nothing. -/
theorem toInt64_inj {x y : UInt64} (h : x.toInt64 = y.toInt64) : x = y := by
  simpa using congrArg Int64.toUInt64 h

/-- A long payload as dense bytes: `bytes` as it is, `foR` decoded once (`Coc.decode`). -/
def longBytes (n : Nat) (e : Enc) : Option ByteArray :=
  match e with
  | .bytes b => some b
  | .foR md pk => some (Kernel.Coc.decode 8 md pk n.toUSize)
  | _ => none

/-- A side of a relation: an atomic type, a product of sides, or an array of a side. A tree, so
    `Vals (.atom t)` is `Arr t` itself and every one-column path is unchanged. A `arr b` element is an
    ARRAY of `b`: its order and multiplicity are part of the value. -/
inductive Obj
  | atom (t : QAtomicType)
  | prod (a b : Obj)
  | arr (b : Obj)
  | sum (a b : Obj)

instance : Coe QAtomicType Obj := ⟨.atom⟩

/-- The atoms the verbs name, so `.long` reads the same at `Obj` as at `QAtomicType`. -/
@[match_pattern, reducible] def Obj.long : Obj := .atom .long
@[match_pattern, reducible] def Obj.general : Obj := .atom .general

/-- An element of a side: a tuple of its atoms' elements. -/
@[reducible] def Obj.El : Obj → Type
  | .atom t => Carrier t
  | .prod a b => a.El × b.El
  | .arr b => List b.El
  | .sum a b => Sum a.El b.El

/-- The element a row reads where its side holds no value at all (a side of `0` values), the one position no
    clamp can land in: what a gather past the side reads — an atom's `default` (q's null), an empty array, a
    sum's `inl` of its left side's own. -/
def Obj.dflt : (A : Obj) → A.El
  | .atom _ => default
  | .prod a b => (a.dflt, b.dflt)
  | .arr _ => []
  | .sum a _ => .inl a.dflt

/-- `n` values of `A`, one column per atom, side by side (struct of arrays): nothing boxed. A `arr b`
    column is one flat payload of `m` values of `b` and two long columns `lo`, `hi`: row `i` is the slice
    `[lo i, hi i)` of the payload, so picking rows gathers `lo` and `hi` and copies no flat value. A `sum a b`
    column is a tag and a position per row into one of two payloads, `l` values of `a` (tag `false`) and `r`
    of `b` (tag `true`): picking rows gathers the tag and the position and copies no value. -/
@[reducible] def Vals : Obj → Nat → Type
  | .atom t, n => Arr t n
  | .prod a b, n => Vals a n × Vals b n
  | .arr b, n => (m : Nat) × Arr .long n × Arr .long n × Vals b m
  | .sum a b, n => (l : Nat) × (r : Nat) × Arr .boolean n × Arr .long n × Vals a l × Vals b r

/-- The position `k` clamped into `[0, m)`: the nearest position of a side of `m > 0` values. -/
def clampFin (k : Int64) (m : Nat) (h : 0 < m) : Fin m :=
  ⟨min (max k.toInt 0).toNat (m - 1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

/-- The value at row `i`, read across the columns. An array row is its slice clamped to `[0, m)`, so every
    `lo`, `hi` reads as an array. A sum row is its side's value at its position clamped into the side, so
    every position reads as a value of its side; a side of no values reads that side's `Obj.dflt`, the null a
    gather past the side reads, so the row keeps its tag. -/
def Vals.row : {A : Obj} → {n : Nat} → Vals A n → Fin n → A.El
  | .atom _, _, x, i => Arr.get x i
  | .prod _ _, _, x, i => (Vals.row x.1 i, Vals.row x.2 i)
  | .arr _, _, ⟨m, lo, hi, f⟩, i => (List.finRange m).filterMap fun (j : Fin m) =>
      if (lo.get i).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi.get i).toInt then some (Vals.row f j) else none
  | .sum a b, _, ⟨l, r, tag, idx, x, y⟩, i =>
    if tag.get i then .inr (if h : 0 < r then Vals.row y (clampFin (idx.get i) r h) else b.dflt)
    else .inl (if h : 0 < l then Vals.row x (clampFin (idx.get i) l h) else a.dflt)

/-- A relation from `k` to `v`: `n` positions, a key and a value at each — q's dict, two arrays at atoms,
    one column per atom of a product side, so `B×C` stored as two columns IS one side of pairs. -/
structure Rel (k v : Obj) where
  n : Nat
  key : Vals k n
  val : Vals v n

namespace Rel

variable {k v : Obj}

/-- The relation `R` denotes: `R x y ↔ ∃ i, key.row i = x ∧ val.row i = y`. -/
def Holds (R : Rel k v) (x : k.El) (y : v.El) : Prop := ∃ i, R.key.row i = x ∧ R.val.row i = y

/-- The pairs, in position order, for proofs only. -/
def toList (R : Rel k v) : List (k.El × v.El) := List.ofFn fun i => (R.key.row i, R.val.row i)

end Rel

/-! ## Payload helpers on qlean kernels -/

section Payload

open QLean.Kernel

/-- One long as an eight-byte payload: the atom operand of an `av`/`va` kernel call. -/
def one (v : UInt64) : ByteArray := Column.pushBits .empty v 8

theorem bitsAt_one (v : UInt64) : Column.bitsAt (one v) 0 8 = v := by
  simpa using Verify.bitsAt_pushBits8 ByteArray.empty v

/-- q's `where` on a dense count column `cnt` (none negative): row `i` repeated `cnt[i]` times, and each
    copy's rank in its run — `expandBytes` of `til n` by the counts, then the output position less its
    run's start (`Scan.scan sums` less the count). One linear pass, where bisecting the outputs into the
    run starts (`binBytes`) was `O(m log n)`. -/
def expand (cnt : ByteArray) : ByteArray × ByteArray :=
  let n := cnt.size / 8
  let rs := Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (Scan.scan .sums .i64 n.toUSize cnt) cnt n.toUSize
  let i := expandBytes 8 0 (tilLongs n.toUSize) cnt
  let m := i.size / 8
  (i, Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (tilLongs m.toUSize) (gatherBytes 8 0 rs i) m.toUSize)

/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : Nat) (b : ByteArray) : ByteArray := Ew.bit (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m.toUSize

end Payload

/-! ## Sanity checks on small literal columns -/

section Checks

open QLean.Column


private def l3 : Arr .long 3 := Arr.mk (.bytes <| packLongs [7, -1, 42]) (by decide)
#guard l3.toList == [7, -1, 42]

private def bs : Arr .boolean 3 := Arr.mk (.bits (ByteArray.mk #[0b101])) (by decide)
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr .symbol 3 := Arr.mk (.syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8]) (by decide)
private def es : Arr .symbol 3 :=
  Arr.mk (.enum blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!)) (by decide)
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .general 2 := Arr.mk (.gen #[(.atom (.long 1) : QValue), (.general #[] : QValue)]) rfl
#guard match id (α := QValue) (gs.get 0), id (α := QValue) (gs.get 1) with | .atom (.long 1), .general #[] _ => true | _, _ => false

#guard ss.toList.zipIdx == [("bc", 0), ("a", 1), ("bc", 2)]

end Checks

#print axioms Arr.get

end LeetQ.Rel
