/-
  The relation algebra of the RelRep design §2.3 on the core: every operator a pipeline of qlean
  kernels over a `Rel`'s two payloads, never a loop over `Arr.get`, `Column.get` or `Column.atoms`.
  A payload stays in whatever encoding carries it — `bytes`, `foR`, `alp`, `bits`, `syms`, `enum`, or
  a general list — because the three steps that touch one take every encoding: `razeColumn` joins
  them, `codes` codes them, `gatherColumn` picks rows of them. Elements are compared through joint
  CODES (`Code`): equal elements equal codes, held at the narrowest layout that already is a code — a
  bit, an enum's ids, a `foR` column's offsets, or a grouping pass's ids packed at the width of their
  count — and every step reads them at that layout; a pair of codes is one code by `composeKey`.
  The spec of each operator is the List-level relation on `toList`; `#guard`s below hold each one
  on small literal relations, and the laws that the kernels' Lean bodies make reachable are proved.
-/
import LeetQ.Rel.Find
import LeetQ.Rel.Ew
import QLean.Kernel.Sort
import QLean.Kernel.Structural
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Kernel.Coc
import QLean.Eval.Dyad
import QLean.Verify.Grade
import QLean.Verify.Chain
import LeetQ.Rel.Parted
import LeetQ.Rel.KernelWF.Reduce

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel
open LeetQ.Rel.Find (expand one)

/-! ## Long payloads: the index and count columns every step passes along -/

/-- Elements of a long payload. -/
def len (b : ByteArray) : Nat := b.size / 8

/-- A dense long payload as a part, counting `len b` elements. A part is the `(count, payload)` pair
    the kernels take, its type known where it is used. -/
def longs (b : ByteArray) : Nat × Enc := (len b, .bytes b)

/-- `x` as a part. -/
def _root_.LeetQ.Rel.Arr.part {t : QAtomicType} {n : Nat} (x : Arr t n) : Nat × Enc := (n, x.enc)

/-- `Arr.of` of a part at `t`: the count and the payload are checked, not assumed. -/
def _root_.LeetQ.Rel.Arr.ofPart (t : QAtomicType) (n : Nat) (p : Nat × Enc) (what : String) : Except String (Arr t n) :=
  Arr.of t n (.vector t p.1 p.2 none) what

/-- A literal long column, its count `xs.length` proved by `packLongs_size`. -/
def col (xs : List Int64) : Arr .long xs.length :=
  Arr.mk (.bytes (packLongs xs)) (show (packLongs xs).size = xs.length * 8 by rw [packLongs_size, Nat.mul_comm])

/-- A relation from its pairs of longs. -/
def ofPairs (ps : List (Int64 × Int64)) : Rel .long .long :=
  ⟨ps.length, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩

def nul : Int64 := Int64.minValue

def add (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul a b (len a).toUSize
def sub (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul a b (len a).toUSize
/-- `a + x` for the long `x`. -/
def addc (a : ByteArray) (x : Nat) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul a (one x.toUInt64) (len a).toUSize
def mulc (a : ByteArray) (x : Nat) : ByteArray := Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul a (one x.toUInt64) (len a).toUSize
def sums (b : ByteArray) : ByteArray := Scan.scan .sums .i64 (len b).toUSize b
/-- `src@idx` at element width `w`; a miss reads `0`. -/
def gather (w : Nat) (src idx : ByteArray) : ByteArray := gatherBytes w.toUSize 0 src idx
/-- The positions where `a` equals `b` elementwise. -/
def whereEqV (a b : ByteArray) : ByteArray :=
  whereBits (len a).toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv a b (len a).toUSize)
/-- The first `n` longs and the rest. -/
def split (b : ByteArray) (n : Nat) : ByteArray × ByteArray := (b.extract 0 (8 * n), b.extract (8 * n) b.size)

/-- The elementwise class of a sort layout. -/
def cls : Scan.Kind → UInt8
  | .bit => Ew.bits | .u8 | .c8 => Ew.u8 | .i16 => Ew.i16 | .i32 => Ew.i32 | .i64 => Ew.i64
  | .f32 => Ew.f32 | .f64 => Ew.f64

def isFloat : Scan.Kind → Bool | .f32 | .f64 => true | _ => false

/-! ## Codes: equal elements equal codes, at the layout that already is one -/

/-- `n` codes at `w` bits: a bitmap at `1`, packed ids at `2`/`4` (`Column.idAt`'s lanes, which a bitmap is
    at `1` too), dense bytes at `8`/`16`/`32`/`64`. Equal elements equal codes, every code below `card`
    (`2⁶⁴` where only the layout bounds it); at `2`/`4` bits `w = Column.idWidthOf card`. -/
structure Code where
  w : Nat
  n : Nat
  card : Nat
  b : ByteArray
  deriving Inhabited

/-- The narrowest byte layout holding the codes `0 … card-1`, for a pass (`enumIds`, `enumIdsFoR`) that
    writes a byte lane at least. -/
def codeKind (card : Nat) : Scan.Kind :=
  if card ≤ 2 ^ 8 then .u8 else if card ≤ 2 ^ 16 then .i16 else if card ≤ 2 ^ 32 then .i32 else .i64

/-- The long ids `gid`, each below `card`, packed at `codeKind card` by `enumIds`. -/
def pack (card : Nat) (gid : ByteArray) : Code :=
  let k := codeKind card
  ⟨8 * k.width, len gid, card, if k == .i64 then gid else (enumIds (len gid).toUSize card.toUSize 0 (8 * k.width).toUSize gid).1⟩

/-- A long payload as codes bounded by its layout alone. -/
def Code.ofLongs (b : ByteArray) : Code := ⟨64, len b, 2 ^ 64, b⟩

/-- The sort layout of a lane, where it has one: every lane but `2`/`4` bits. -/
def laneKind : Nat → Option Scan.Kind
  | 1 => some .bit | 8 => some .u8 | 16 => some .i16 | 32 => some .i32 | 64 => some .i64 | _ => none

/-- `n` ids below `card` packed at `w = Column.idWidthOf card` bits — an enum's ids, `groupIds`' — as a
    code where they lie. A lane of no bits (`card ≤ 1`, every id `0`) is a bitmap of zeros: the
    narrowest lane every code kernel reads. -/
def Code.ofLane (w n card : Nat) (ids : ByteArray) : Code :=
  if w == 0 then ⟨1, n, card, ByteArray.mk (Array.replicate ((n + 7) / 8) 0)⟩ else ⟨w, n, card, ids⟩

/-- `n` ids in `ng` classes as `groupIds` answers them, packed at `Column.idWidthOf ng`. -/
def Code.ofIds (ng n : Nat) (gid : ByteArray) : Code := Code.ofLane (Column.idWidthOf ng) n ng gid

/-- How many rows of `n` each class of a `groupIds` answer `(gid, firsts)` holds: `groupSizes` reading
    the ids at their width. -/
def classSizes (n : Nat) (r : ByteArray × ByteArray) : ByteArray :=
  Order.groupSizes (len r.2).toUSize (Column.idWidthOf (len r.2)).toUSize n.toUSize r.1

namespace Code

/-- The lane's sort layout, `none` at `2`/`4` bits, where the id kernels read. -/
def kind (c : Code) : Option Scan.Kind := laneKind c.w

/-- `c@i` for an in-range long index column: `gatherBits`, `gatherBytes`, `gatherPacked` at the lane. -/
def gather (c : Code) (i : ByteArray) : Code :=
  ⟨c.w, len i, c.card, match c.kind with
    | some .bit => gatherBits c.n.toUSize c.b i
    | some k => gatherBytes k.width.toUSize 0 c.b i
    | none => gatherPacked c.n.toUSize c.w.toUSize c.w.toUSize 0 c.b i⟩

/-- The first position in `c` of each of `x`'s codes, `c.n` at a miss: `findBitVec`, `findVec`, and
    `findIdsVec` at `2`/`4` bits or two lanes of different widths. -/
def find (c x : Code) : ByteArray :=
  match c.kind, x.kind with
  | some .bit, some .bit => findBitVec c.n.toUSize c.b x.n.toUSize x.b
  | some k, some k' => if k == k' then findVec k.width.toUSize false c.b x.b
    else findIdsVec c.w.toUSize c.b c.n.toUSize x.w.toUSize x.b x.n.toUSize
  | _, _ => findIdsVec c.w.toUSize c.b c.n.toUSize x.w.toUSize x.b x.n.toUSize

/-- Whether each of `x`'s codes occurs in `c`, as bits: `memberBits`, `memberVec`, `memberIdsVec`. -/
def member (x c : Code) : ByteArray :=
  match x.kind, c.kind with
  | some .bit, some .bit => memberBits x.n.toUSize x.b c.n.toUSize c.b
  | some k, some k' => if k == k' then memberVec k.width.toUSize false x.b c.b
    else memberIdsVec x.w.toUSize x.b x.n.toUSize c.w.toUSize c.b c.n.toUSize
  | _, _ => memberIdsVec x.w.toUSize x.b x.n.toUSize c.w.toUSize c.b c.n.toUSize

/-- The positions where `a` and `b` (one lane) hold one code: `Ew.cmp` at the codes' class, `eqIds` at
    `2`/`4` bits. -/
def eqAt (a b : Code) : ByteArray := whereBits a.n.toUSize <| match a.kind with
  | some k => Ew.cmp Ew.eq (cls k) Ew.vv a.b b.b a.n.toUSize
  | none => Kernel.Ew.eqIds Ew.eq Ew.vv a.b b.b a.w.toUSize a.n.toUSize

/-- Each row's class, numbered by first occurrence, and each class's first row: `groupIds` at the layout,
    `idGroups` (a direct table of `card` entries) at `2`/`4` bits. -/
def groupIds (c : Code) : ByteArray × ByteArray := match c.kind with
  | some k => Order.groupIds k c.n.toUSize c.b
  | none => Order.idGroups c.card.toUSize c.n.toUSize c.w.toUSize c.b

/-- The rows in ascending code order, stable: `grade` at the layout, `gradeLane` at `2`/`4` bits and
    where `grade` would read an `i16`/`i32` code past the sign bit as negative (`gradeLane` is unsigned). -/
def grade (c : Code) : ByteArray := match c.kind with
  | some k => if (k == .i16 || k == .i32) && 2 ^ (c.w - 1) < c.card
    then Order.gradeLane false c.n.toUSize c.w.toUSize c.b else Order.grade k false c.n.toUSize c.b
  | none => Order.gradeLane false c.n.toUSize c.w.toUSize c.b

/-- Codes of one space end to end, at the first part's lane: `concatBits`, `concatBytes`, and
    `concatIds` through each part's identity map at `2`/`4` bits, where a part starts inside a byte. -/
def cat (cs : Array Code) : Code :=
  let w := if h : 0 < cs.size then cs[0].w else 8
  ⟨w, cs.foldl (· + ·.n) 0, cs.foldl (max · ·.card) 0, match laneKind w with
    | some .bit => concatBits (cs.map (·.n)) (cs.map (·.b))
    | some _ => concatBytes (cs.map (·.b))
    | none => concatIds w.toUSize (cs.map (·.n)) (cs.map (·.w)) (cs.map fun c => Column.packIds w c.card id) (cs.map (·.b))⟩

/-- `c` cut into parts of the counts `ns` (summing to `c.n`): byte extracts at a byte lane, `cycleBits`
    and `cycleIds` below one, where a part can start inside a byte. -/
def cut {p : Nat} (c : Code) (ns : Vector Nat p) : Vector Code p :=
  if p = 1 then Vector.replicate p c else
  let part (o m : Nat) : ByteArray :=
    if m == 0 then .empty
    else if c.w % 8 == 0 then c.b.extract (c.w / 8 * o) (c.w / 8 * (o + m))
    else if c.w == 1 then cycleBits c.n.toUSize o.toUSize m.toUSize c.b
    else cycleIds c.n.toUSize o.toUSize m.toUSize c.w.toUSize c.b
  -- part `i` starts at the sum of the counts before it; the parts are few (two or three), so no running sum
  ns.mapIdx fun i m => ⟨c.w, m, c.card, part ((ns.toArray.extract 0 i).foldl (· + ·) 0) m⟩

/-- The run starts of `c` and its count: `runStartsBits`, `runStarts` at a byte lane, `runStartsIds` at
    `2`/`4` bits. -/
def runStarts (c : Code) : ByteArray := match c.kind with
  | some .bit => Kernel.runStartsBits c.n.toUSize c.b
  | some k => Kernel.runStarts k.width.toUSize false c.b
  | none => Kernel.runStartsIds c.n.toUSize c.w.toUSize c.b

end Code

/-- The rows in the order of each of `ks` in turn, ascending, by stable grades from the last key to the
    first at each code's own lane; answers the permutation of `n` rows. -/
def gradeBy (n : Nat) (ks : Array Code) : ByteArray :=
  ks.foldr (init := tilLongs n.toUSize) fun c p => gather 8 p (c.gather p).grade

/-! ## Payloads of any encoding: count, pick, join, code -/

/-- A long column's dense payload always answers: `Enc.WF .long` admits only `bytes` and `foR`. -/
theorem longBytes_isSome {n : Nat} (x : Arr .long n) : (longBytes n x.enc).isSome := by
  rcases KernelWF.long_cases x.wf with ⟨b, h⟩ | ⟨M, P, h⟩ <;> simp [h, longBytes]

/-- A general list's boxed elements: its `gen` column, which is the only one `Arr .general` admits. -/
def gens {n : Nat} (x : Arr .general n) : Array QValue :=
  (match x.enc with | .gen xs => some xs | _ => none).get
    (by obtain ⟨xs, he, -⟩ := KernelWF.general_cases x.wf; simp [he])

/-- A general list's column over `xs`. -/
def genCol (xs : Array QValue) : (n : Nat) × Arr .general n :=
  ⟨xs.size, Arr.mk (.gen xs) (by simp [Enc.WF, QAtomicType.width])⟩

/-- `x@i` for a long payload `i`: `gatherColumn`, which answers every column encoding (`gatherColumn_isSome`).
    A general list is picked by position; a position past the end reads the null, as q's `@`. -/
def pick (t : QAtomicType) (c : (n : Nat) × Arr t n) (i : ByteArray) : (n : Nat) × Arr t n :=
  if hg : t = .general then by
    subst hg; exact let xs := gens c.2; genCol ((longRows i).map fun p => xs[p]?.getD (QLean.Eval.fillOf xs))
  else
    have h := KernelWF.gatherColumn_isSome c.2.wf hg (m := len i) i (Nat.div_mul_le_self _ _)
    ⟨len i, Arr.mk ((gatherColumn t c.1 c.2.enc (len i) (.bytes i)).get h)
      (KernelWF.gatherColumn_wf c.2.wf i (Option.some_get h).symm)⟩

/-- `pick` at a type other than `general` is `gatherColumn`'s answer, which always exists. -/
theorem pick_eq_gather {t : QAtomicType} (hg : t ≠ .general) (c : (n : Nat) × Arr t n) (i : ByteArray) :
    ∃ e, gatherColumn t c.1 c.2.enc (len i) (.bytes i) = some e ∧ (pick t c i).2.part = (len i, e) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
    (KernelWF.gatherColumn_isSome c.2.wf hg (m := len i) i (Nat.div_mul_le_self _ _))
  refine ⟨e, he, ?_⟩
  unfold pick; rw [dif_neg hg]
  exact congrArg (len i, ·) (Option.some_inj.1 ((Option.some_get _).trans he))

/-- `pick` answers one row an index long: `gatherColumn` at `len i`, a general list's `longRows`. -/
theorem pick_len (t : QAtomicType) (c : (n : Nat) × Arr t n) (i : ByteArray) : (pick t c i).1 = len i := by
  by_cases hg : t = .general
  · subst hg; simp [pick, genCol, longRows, len]
  · simp [pick, hg]

/-- No element of `t`: `Enc.ofAtoms` of nothing, which picks the type's own constructor. -/
def empty (t : QAtomicType) : (n : Nat) × Arr t n :=
  if h : t = .general then h ▸ genCol #[] else
    ⟨0, Arr.mk ((Enc.ofAtoms t #[] h).get (Column.ofAtoms_isSome h (by simp)))
      (Column.ofAtoms_WF (by simp) (Option.some_get _).symm)⟩

theorem empty_len (t : QAtomicType) : (empty t).1 = 0 := by
  by_cases h : t = .general
  · subst h; simp [empty, genCol]
  · simp [empty, h]

/-- `raze` of parts of one type: `razeColumn`, which interns a symbol part to meet an interned one
    and decodes an encoded part to meet a dense one. A general list is `Array.append`; no part is `empty t`. -/
def raze (t : QAtomicType) (cs : Array ((n : Nat) × Arr t n)) : (n : Nat) × Arr t n :=
  if h0 : cs.size = 0 then empty t else
  if hg : t = .general then by subst hg; exact genCol (cs.foldl (fun xs c => xs ++ gens c.2) #[]) else
  if h1 : cs.size = 1 then cs[0] else
  let ps : Array (Nat × Enc) := cs.map (·.2.part)
  if hb : (∀ c ∈ ps, c.1 < USize.size) ∧ ps.foldl (fun s c => s + c.1) 0 < USize.size then
    have hw : ∀ c ∈ ps, Enc.WF t c.1 c.2 ∧ c.1 < USize.size := fun c hc => by
      obtain ⟨x, -, rfl⟩ := Array.mem_map.1 hc; exact ⟨x.2.wf, hb.1 _ hc⟩
    have hs := KernelWF.razeColumn_isSome (by simpa [ps] using h0) hg hw
    -- the answer itself, at the count `razeColumn_count` proves, so `raze_len` reads it off
    ⟨ps.foldl (fun s c => s + c.1) 0, ⟨(razeColumn t ps).get hs, by
      obtain ⟨n, e, he, hwf⟩ := KernelWF.razeColumn_wf hw hb.2 (Option.some_get hs).symm
      have hn := KernelWF.razeColumn_count hw (by rw [← he]; exact (Option.some_get hs).symm)
      rw [he]; subst hn; exact ⟨rfl, rfl, hwf⟩⟩⟩
  else
    -- counts past `USize` are no input a process holds; the same concatenation read through the parts'
    -- atoms and rebuilt by `Enc.ofAtoms` answers there, since `razeColumn`'s count arithmetic would wrap.
    let as := (cs.map fun (c : (n : Nat) × Arr t n) => Enc.atoms t c.1 c.2.enc).flatten
    have ha : ∀ a ∈ as, a.type = t := fun a h => by
      obtain ⟨_, hx, ha⟩ := Array.mem_flatten.1 h
      obtain ⟨c, -, rfl⟩ := Array.mem_map.1 hx
      exact Column.atoms_type _ _ _ a ha
    ⟨as.size, Arr.mk ((Enc.ofAtoms t as hg).get (Column.ofAtoms_isSome hg ha))
      (Column.ofAtoms_WF ha (Option.some_get _).symm)⟩

/-- `mapM` in `Option` over one part is the one part's answer. -/
@[simp] theorem vmapM_one {α β : Type} (f : α → Option β) (x : α) : Vector.mapM f #v[x] = (f x).map (#v[·]) := by
  have e := Vector.toArray_mapM (f := f) (xs := #v[x])
  cases h : Vector.mapM f #v[x] <;> cases h' : f x <;> simp_all [Array.mapM_eq_mapM_toList]

/-- `mapM` in `Option` over two parts: both answer, or neither pair does. -/
@[simp] theorem vmapM_two {α β : Type} (f : α → Option β) (x y : α) :
    Vector.mapM f #v[x, y] = (f x).bind fun a => (f y).map fun b => #v[a, b] := by
  have e := Vector.toArray_mapM (f := f) (xs := #v[x, y])
  cases h : Vector.mapM f #v[x, y] <;> cases h' : f x <;> cases h'' : f y <;> simp_all [Array.mapM_eq_mapM_toList]

/-- `foR` and dense parts of a long type as offsets from their joint least element, at the width of the
    joint range: `overFoR` reads a `foR` part's bounds off the block metadata, `overBytes` a dense
    part's in one pass; `foRShift`/`Ew.val add` rebase a part and `enumIdsFoR`/`enumIds` pack its
    offsets, a null to the last code — no hashing, no `foR` element decoded. Order-preserving. `none`
    where a part is neither, the range is wider than a grouping pass's ids over `total` rows would be, or
    a pass reports an offset outside `0 … card`: `codes` then takes its grouping branch, a faithful code too.
    A dense part is here because its first-appearance ids (`groupIdsColumn`) cost a table probe a row
    (measured: `ej` of two million-wide dense key columns, 1e6 rows, the codes 16.7 ms). -/
def rangeOffsets {p : Nat} (a : QAtomicType) (cs : Vector (Nat × Enc) p) (total : Nat) : Option (Vector Code p) :=
  if !(orderKind a == some .i64 && Column.encodes a) then none else
  let bound (op : Coc.Over) (c : Nat × Enc) : Option Int64 := match c.2 with
    | .bytes b => some (overBytes op Ew.i64 nul b)
    | .foR .. => overFoR op a c.1 c.2
    | _ => none
  match cs.toArray.mapM (bound .lesser) with
  | none => none
  | some los => match cs.toArray.mapM (bound .greater) with
  | none => none
  | some his =>
  let lo := los.foldl min Int64.maxValue
  let hi := his.foldl max (Int64.minValue + 1)
  if lo == nul || hi < lo then none else
  -- the codes `0 … hi-base`, then one for a null (`enumIdsFoR`'s `nullId`)
  let span (base : Int64) : Nat := (hi.toInt - base.toInt + 2).toNat
  let k := codeKind (span lo)
  if ¬ k.width ≤ (codeKind total).width then none else
  -- values already at `0` and up that fit the same width are their own offsets: no `foRShift` pass
  let base := if 0 ≤ lo && (codeKind (span 0)).width == k.width then 0 else lo
  let card := span base
  let w := 8 * k.width
  -- `bad` is the first row whose offset lies outside `0 … card`, `n` when none does
  let packed (n : Nat) : ByteArray × USize → Option Code
    | (ids, bad) => if bad.toNat != n then none else some ⟨w, n, card, ids⟩
  let part (c : Nat × Enc) : Option Code := let n := c.1; match c.2 with
    | .foR md pk => (if base == 0 then some (md, pk) else Ew.foRShift false (-base) md pk n.toUSize).bind fun (md, pk) =>
        packed n (enumIdsFoR n.toUSize card.toUSize (card - 1).toUSize w.toUSize md pk)
    | .bytes b =>
      let n := b.size / 8
      let b := if base == 0 then b else Kernel.Ew.val Ew.add Ew.i64 Ew.va nul b (one (-base).toUInt64) n.toUSize
      packed n (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b)
    | _ => none
  cs.mapM part

/-- Joint codes of the parts `cs`, one `Code` per part, in one code space:
    - `bits`: each part is its own code, a bit wide, order-preserving;
    - `foR` or dense of a long type: the offsets from the joint least element (`rangeOffsets`), order-preserving;
    - `enum`, and `syms` interned by `razeColumn`/`Column.intern`: the joint dictionary's ids at their lane;
    - anything else: one coding pass over the `raze` (`groupIdsColumn`: ids by first appearance, at any
      encoding), read at the width they are packed at (`Code.ofIds`). A general list is `findList` of
      the join against itself, its positions packed. -/
def codes {p : Nat} (t : QAtomicType) (cs : Vector ((n : Nat) × Arr t n) p) : Vector Code p :=
  if hg : t = .general then by
    subst hg; exact let all := gens (raze .general cs.toArray).2; (pack all.size (findList all all)).cut (cs.map (·.1))
  else
  match cs.mapM (fun c => match c.2.enc with | .bits b => some (⟨1, c.1, 2, b⟩ : Code) | _ => none) with
  | some bs => bs
  | none =>
  let ns := cs.map (·.1)
  let total := ns.foldl (· + ·) 0
  match rangeOffsets t (cs.map (·.2.part)) total with
  | some os => os
  | none =>
  let x := raze t cs.toArray
  -- `intern` rewrites only a `syms` payload, and always to `enum`: past this branch it is `x`'s own
  match Column.intern x.2.enc with
  | .enum _ dof ids => (Code.ofLane (Column.idWidth dof) x.1 (dof.size - 1) ids).cut ns
  | _ =>
    let (gid, fs) := (groupIdsColumn t x.1 x.2.enc).get (KernelWF.groupIdsColumn_isSome hg x.2.wf)
    (Code.ofIds (len fs) total gid).cut ns

/-- The dense payload an ARITHMETIC kernel (`Ew`, `overGroups`, `grade` by value) reads, at its sort
    layout: a boolean's bits, any other ordered type's `Column.bytesOf` (an encoded one decoded once).
    A symbol, guid or general list has no such payload; equality steps never come here (`codes`). -/
def arrDense {a : QAtomicType} {n : Nat} (x : Arr a n) : Except String (Scan.Kind × ByteArray) := do
  let some k := orderKind a | throw s!"type {a.code} has no sort layout: no arithmetic kernel reads it"
  match x.enc with
  | .bits b => pure (k, b)
  | _ => match Enc.bytesOf a n x.enc with
    | some b => pure (k, b)
    | none => throw s!"type {a.code}: Enc.bytesOf has no dense payload for this encoding"

/-- A long column's dense payload, which always answers (`longBytes_isSome`). -/
def longsOf {n : Nat} (x : Arr .long n) : ByteArray := (longBytes n x.enc).get (longBytes_isSome x)

/-- A long payload as a column of `len b` rows: `b` itself, its trailing bytes past the last long cut. -/
def longCol (b : ByteArray) : Arr .long (len b) :=
  Arr.mk (.bytes (b.extract 0 (8 * len b))) (by simp [Enc.WF, QAtomicType.width, len, ByteArray.size_extract]; omega)

/-- The slices `[lo i, hi i)` of a flat payload of `m` values clamped to `[0, m]`, as `Vals.row` reads
    them: each clamped start and the slice's count, `Ew.val` lesser/greater. -/
def slices (m : Nat) (lo hi : ByteArray) : ByteArray × ByteArray :=
  let n := (len lo).toUSize
  let clamp (b : ByteArray) : ByteArray :=
    Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul b (one m.toUInt64) n) (one 0) n
  let l := clamp lo
  (l, sub (Kernel.Ew.val Ew.greater Ew.i64 Ew.vv nul (clamp hi) l n) l)

/-! ## A side's payloads: one part per atom, each step column by column -/

/-- The parts of a side `A`: a part at an atom, a pair of parts at a product; at an array, the parts of its
    `lo` and `hi` columns and the flat payload they slice. -/
@[reducible] def Part : Obj → Type
  | .atom t => (n : Nat) × Arr t n
  | .prod a b => Part a × Part b
  | .list b => ((n : Nat) × Arr .long n) × ((n : Nat) × Arr .long n) × ((m : Nat) × Vals b m)

/-- The rows of a side's parts: its first column's count. -/
def _root_.LeetQ.Rel.Obj.count : (A : Obj) → Part A → Nat
  | .atom _, c => c.1
  | .prod a _, c => Obj.count a c.1
  | .list _, c => c.1.1

/-- `pick` of every column at the same rows; an array's `lo` and `hi`, its flat payload shared. -/
def _root_.LeetQ.Rel.Obj.pick : (A : Obj) → Part A → ByteArray → Part A
  | .atom t, c, i => Alg.pick t c i
  | .prod a b, c, i => (Obj.pick a c.1 i, Obj.pick b c.2 i)
  | .list _, c, i => (Alg.pick .long c.1 i, Alg.pick .long c.2.1 i, c.2.2)

/-- A side's columns as parts. -/
def _root_.LeetQ.Rel.Vals.parts : {A : Obj} → {n : Nat} → Vals A n → Part A
  | .atom _, n, x => ⟨n, x⟩
  | .prod _ _, _, x => (Vals.parts x.1, Vals.parts x.2)
  | .list _, n, x => (⟨n, x.2.1⟩, ⟨n, x.2.2.1⟩, ⟨x.1, x.2.2.2⟩)

/-- One column picked at the index column `i`: `len i` rows (`pick_len`). -/
def pickArr (t : QAtomicType) (c : (n : Nat) × Arr t n) (i : ByteArray) : Arr t (len i) := pick_len t c i ▸ (pick t c i).2

/-- A side's columns picked at the index column `i`: `len i` rows each; an array's `lo` and `hi`. -/
def _root_.LeetQ.Rel.Vals.pick : (A : Obj) → Part A → (i : ByteArray) → Vals A (len i)
  | .atom t, c, i => pickArr t c i
  | .prod a b, c, i => (Vals.pick a c.1 i, Vals.pick b c.2 i)
  | .list _, c, i => ⟨c.2.2.1, pickArr .long c.1 i, pickArr .long c.2.1 i, c.2.2.2⟩

/-- No row of one column (`empty_len`). -/
def emptyArr (t : QAtomicType) : Arr t 0 := empty_len t ▸ (empty t).2

/-- No row, column by column (`empty_len`). -/
def _root_.LeetQ.Rel.Vals.empty : (A : Obj) → Vals A 0
  | .atom t => emptyArr t
  | .prod a b => (Vals.empty a, Vals.empty b)
  | .list b => ⟨0, emptyArr .long, emptyArr .long, Vals.empty b⟩

/-- No element, column by column. -/
def _root_.LeetQ.Rel.Obj.empty : (A : Obj) → Part A
  | .atom t => Alg.empty t
  | .prod a b => (Obj.empty a, Obj.empty b)
  | .list b => (Alg.empty .long, Alg.empty .long, ⟨0, Vals.empty b⟩)

/-- The first `m` longs of the index column `i`, `m ≤ len i`: `i` itself when it holds `m` (no copy), else
    `extract`. Either way `m` rows (`fit_len`). -/
def fit (m : Nat) (i : ByteArray) : ByteArray := if len i = m then i else i.extract 0 (m * 8)

theorem fit_len {m : Nat} {i : ByteArray} (h : m ≤ len i) : len (fit m i) = m := by
  unfold fit; split
  · assumption
  · simp only [len, ByteArray.size_extract] at h ⊢; omega

/-- A side's columns picked at the first `m` longs of `i`. -/
def _root_.LeetQ.Rel.Vals.pickN (A : Obj) (c : Part A) (i : ByteArray) (m : Nat) (h : m ≤ len i) : Vals A m :=
  fit_len h ▸ Vals.pick A c (fit m i)

/-- A side's parts at the count `n`, column by column: a column of `n` rows is itself; one a kernel answered
    at another count is read at its first `n` rows (`pickRef`). An unproved check: only the ops after `diff`
    (`uncons`) still reads through it; the core ops pick at a proved count (`Vals.pick`). -/
def _root_.LeetQ.Rel.Vals.ofParts : (A : Obj) → (n : Nat) → Part A → Vals A n
  | .atom _, n, c => ofArr n c
  | .prod a b, n, c => (Vals.ofParts a n c.1, Vals.ofParts b n c.2)
  | .list _, n, c => ⟨c.2.2.1, ofArr n c.1, ofArr n c.2.1, c.2.2.2⟩
where
  /-- One column at the count `n`: itself, or its first `n` rows (`pickRef`). -/
  ofArr {t : QAtomicType} (n : Nat) (c : (m : Nat) × Arr t m) : Arr t n :=
    if h : c.1 = n then h ▸ c.2 else Find.pickRef c.2 fun j => j.1

/-- `raze` column by column. An array's flat payloads are razed, and each part's `lo`, `hi` move past
    the flat values of the parts before it (`addc`), so every row still slices its own values. -/
def _root_.LeetQ.Rel.Obj.raze : (A : Obj) → Array (Part A) → Part A
  | .atom t, cs => Alg.raze t cs
  | .prod a b, cs => (Obj.raze a (cs.map (·.1)), Obj.raze b (cs.map (·.2)))
  | .list b, cs =>
    let ms := cs.map (·.2.2.1)
    let m := ms.foldl (· + ·) 0
    -- the parts are few (two or three), so no running sum
    let mv (k : Nat) (c : (n : Nat) × Arr .long n) : (n : Nat) × Arr .long n :=
      let s := addc (longsOf c.2) ((ms.extract 0 k).foldl (· + ·) 0); ⟨len s, longCol s⟩
    (Alg.raze .long (cs.mapIdx fun k c => mv k c.1), Alg.raze .long (cs.mapIdx fun k c => mv k c.2.1),
      ⟨m, Vals.ofParts b m (Obj.raze b (cs.map fun c => c.2.2.2.parts))⟩)

/-- A relation's two payloads. -/
structure Cols (k v : Obj) where
  n : Nat
  key : Part k
  val : Part v

def cols {k v : Obj} (R : Rel k v) : Cols k v := ⟨R.n, R.key.parts, R.val.parts⟩

/-- The rows of `d` at the index column `i`: `len i` pairs. -/
def Cols.rows {k v : Obj} (d : Cols k v) (i : ByteArray) : Rel k v := ⟨len i, Vals.pick k d.key i, Vals.pick v d.val i⟩

/-- Two payloads as a relation keyed by an explicit column, of the key's count, through `Vals.ofParts`:
    only the ops after `diff` whose counts meet by no theorem yet (`leftDiv`, `symDiv`, `pair`, `prod`, …). -/
def ofCols (k v : Obj) (kc : Part k) (vc : Part v) : Rel k v :=
  let n := k.count kc
  ⟨n, Vals.ofParts k n kc, Vals.ofParts v n vc⟩

/-! ## The composite steps, named once -/

/-- A code's payload as the column `composeKey` reads: a bit a boolean bitmap, a byte layout the
    dense column of that width, a `2`/`4`-bit lane an interned column of `card` ids, read by `eIds`
    where they lie; `composeKey` reads no dictionary, so it holds `card` empty symbols. -/
def Code.column (c : Code) : Option (QAtomicType × (Nat × Enc)) :=
  match c.kind with
  | some .bit => some (.boolean, (c.n, .bits c.b)) | some .u8 => some (.byte, (c.n, .bytes c.b))
  | some .i16 => some (.short, (c.n, .bytes c.b)) | some .i32 => some (.int, (c.n, .bytes c.b))
  | some .i64 => some (.long, (c.n, .bytes c.b))
  | some _ => none
  | none => if Column.idWidthOf c.card == c.w then some (.symbol, (c.n, .enum .empty (Array.replicate (c.card + 1) 0) c.b))
    else none

/-- The code of each row's pair `(a, b)`: `composeKey`'s `a·|b| + b` at the width of the product of
    the bounds, packed below a byte, no grouping pass; the classes are answered too when the step
    grouped. `classes`: the caller groups the answer next. -/
def pairCode (classes : Bool) (a b : Code) : Code × Option (ByteArray × ByteArray) :=
  -- a bitmap is read as codes `0 … 1` whatever its `card`; `composeKey` writes the pair's code at
  -- the product's own width, below a byte too, so no floor on the domain
  let d₂ := max b.card 2
  let d₁ := max a.card 2
  let composed : Option Code := do
    guard (d₁ * d₂ < 2 ^ 63)
    let w := Column.idWidthOf (d₁ * d₂)
    -- grouping a composite past 16 bits hashes it, as `groupIdsPair` hashes the pair: the compose would
    -- be a pass for nothing (measured: `|R|` of 1000-wide `foR` pairs 11% slower composed)
    guard (!classes || w ≤ 16)
    let (t₁, c₁) ← a.column
    let (t₂, c₂) ← b.column
    (⟨w, a.n, d₁ * d₂, ·⟩) <$> composeKey t₁ c₁.1 c₁.2 d₁ d₂ t₂ c₂.1 c₂.2
  match composed with
  | some c => (c, none)
  -- `composeKey` declines a bound past 2⁶³ or a code outside it (a 16-bit lane past 2¹⁵ reads signed):
  -- `groupIdsPair` numbers the pairs densely instead, whatever the codes are, `groupIdsPairIds` at a lane
  -- below a byte
  | none =>
    let r := match a.kind, b.kind with
      | some ka, some kb => Order.groupIdsPair ka kb a.n.toUSize a.b b.b
      | _, _ => Order.groupIdsPairIds a.w.toUSize b.w.toUSize a.n.toUSize a.b b.b
    (Code.ofIds (len r.2) a.n r.1, some r)

/-- `|R|` of tuples: `c0` is the first column's codes per part (`codes`), `rest` the other columns'; the
    columns are folded left by `pairCode`; one code per part. One column is its own codes. -/
def tuples {p : Nat} (c0 : Vector Code p) (rest : Array (Vector Code p)) : Vector Code p :=
  if rest.isEmpty then c0 else
  (tupleCode false (Code.cat c0.toArray) (rest.map (Code.cat ·.toArray))).1.cut (c0.map (·.n))
where
  /-- The fold of the columns `c0`, then `rest`, by `pairCode`, the last step told whether its answer is
      grouped next (`classes`), and the classes when that step grouped. -/
  tupleCode (classes : Bool) (c0 : Code) (rest : Array Code) : Code × Option (ByteArray × ByteArray) :=
    match rest.back? with
    | none => (c0, none)
    | some cl => pairCode classes (rest.pop.foldl (fun a c => (pairCode false a c).1) c0) cl
  /-- The classes of the tuples of the columns `c0`, then `rest`, as `groupIds` answers them; the last
      fold step's own when it grouped, so a caller wanting the classes groups nothing twice. -/
  tupleIds (c0 : Code) (rest : Array Code) : ByteArray × ByteArray :=
    match tupleCode true c0 rest with
    | (_, some r) => r
    | (c, none) => c.groupIds

/-- Segment ids read off the codes directly: segment `j`'s codes `vc[o[j] .. o[j+1])` (`Column.resAt` at the
    code's width) normalised by `norm`, numbered by first occurrence. One long per segment. -/
def slicesRef (norm : List UInt64 → List UInt64) (vc : Code) (o : ByteArray) : ByteArray :=
  let off (j : Nat) : Nat := (Column.bitsAt o (8 * j) 8).toNat
  let seg (j : Nat) : List UInt64 := norm ((List.range (off (j + 1) - off j)).map fun t => Column.resAt vc.b 0 vc.w (off j + t))
  let segs := (List.range (len o - 1)).map seg
  packLongs (segs.map fun x => Int64.ofNat (segs.eraseDups.idxOf x))

/-- Sequence ids: segment `j` of the codes `vc` is `vc[o[j] .. o[j+1])` for the `g + 1` offsets `o`; equal
    SEQUENCES (order and repeats counted) get equal ids, numbered by first occurrence: `rankSlices`. -/
def sliceIds (vc : Code) (o : ByteArray) : ByteArray :=
  let ids := Order.rankSlices vc.w.toUSize vc.b o
  -- `rankSlices` declines (answers empty) on offsets out of order or past its payload, which no theorem
  -- yet rules out for offsets summed from counts; the reference answers there
  if ids.size = 8 * (len o - 1) then ids else slicesRef id vc o

/-- Joint codes of a side's parts, one code per part: an atom's `codes`; a product's `tuples` of its
    columns' codes, so equal tuples are equal codes exactly when every column is; an array's `sliceIds` of
    its elements' joint codes, each row's slice gathered contiguous (`expand` of the clamped counts), so
    equal arrays (equal length, equal elements position by position) are equal codes exactly. -/
def _root_.LeetQ.Rel.Obj.codes : (A : Obj) → {p : Nat} → Vector (Part A) p → Vector Code p
  | .atom t, _, cs => Alg.codes t cs
  | .prod a b, _, cs => tuples (Obj.codes a (cs.map (·.1))) #[Obj.codes b (cs.map (·.2))]
  | .list b, _, cs =>
    let ec := Obj.codes b (cs.map fun c => c.2.2.2.parts)
    let sl := cs.map fun c => slices c.2.2.1 (longsOf c.1.2) (longsOf c.2.1.2)
    let seq := Code.cat (Vector.zipWith (fun e s => let x := expand s.2; e.gather (add (gather 8 s.1 x.1) x.2)) ec sl).toArray
    let ns := cs.map (·.1.1)
    let o := concatBytes #[one 0, sums (concatBytes (sl.map (·.2)).toArray)]
    (pack (ns.foldl (· + ·) 0) (sliceIds seq o)).cut ns

/-- The permutation `p` refined stably by the values of `A` at its rows, ascending: `gradeColumn` of each
    atom (a symbol by its string, so the order is the value's, the same in every call), the last component
    first so a product sorts lexicographically. Where no kernel orders the values — a general list, an
    array — by their codes: an order of this call only. -/
def _root_.LeetQ.Rel.Obj.sortBy : (A : Obj) → Part A → ByteArray → ByteArray
  | .atom t, c, p =>
    let x := Alg.pick t c p
    match gradeColumn t false x.1 x.2.enc with
    | some (.bytes g) => gather 8 p g
    | _ => gather 8 p (codes t #v[x])[0].grade
  | .prod a b, c, p => Obj.sortBy a c.1 (Obj.sortBy b c.2 p)
  | .list b, c, p => gather 8 p (Obj.codes (.list b) #v[Obj.pick (.list b) c p])[0].grade

/-- `|R|` of several relations of one type in one code space, one code per relation. -/
def pairs {k v : Obj} {p : Nat} (ds : Vector (Cols k v) p) : Vector Code p :=
  tuples (k.codes (ds.map (·.key))) #[v.codes (ds.map (·.val))]

/-- `R` with each pair once: the first row of each class of `|R|`. -/
def Cols.nub {k v : Obj} (d : Cols k v) : Rel k v :=
  d.rows (tuples.tupleIds (k.codes #v[d.key])[0] #[(v.codes #v[d.val])[0]]).2

/-- `join(l, r)`: every pair of a left and a right row with equal codes, as two index columns —
    `groupIds`/`groupSizes`/`grade` of the right, `find` of the left in its distinct codes,
    `expand` of the matched counts, `gatherBytes` into the grouped right rows. Size `j` = matches. -/
def join (l r : Code) : ByteArray × ByteArray :=
  let g := r.groupIds
  let sizes := classSizes r.n g
  let hit := (r.gather g.2).find l
  let (li, w) := expand (gather 8 sizes hit)
  let starts := sub (sums sizes) sizes
  (li, gather 8 (Code.ofIds (len g.2) r.n g.1).grade (add (gather 8 starts (gather 8 hit li)) w))

/-- `join`'s right index column is no longer than its left: equal wherever the count fits a `USize`, which
    `add` takes (`Ew.val_size`, `gatherBytes_size`). -/
theorem gather_len (s i : ByteArray) : len (gather 8 s i) = len i := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  simp only [len, gather, KernelWF.gatherBytes_size, h8]; omega

/-- `add` answers at most its left count: equal wherever the count fits a `USize` (`Ew.val_size`). -/
theorem add_len_le (a b : ByteArray) : len (add a b) ≤ len a := by
  have hw : Kernel.Ew.width Ew.i64 = 8 := by decide
  have hu : (a.size / 8).toUSize.toNat ≤ a.size / 8 := by simp only [Nat.toUSize]; exact Nat.mod_le _ _
  simp only [len, add, KernelWF.Ew.val_size, hw]; omega

theorem join_len (l r : Code) : len (join l r).2 ≤ len (join l r).1 := by
  unfold join; dsimp only
  rw [gather_len]; exact Nat.le_trans (add_len_le _ _) (by rw [gather_len, gather_len]; exact Nat.le_refl _)

/-- `cnt(c)`: count by `c` — its distinct codes and how many rows hold each. -/
def cnt (c : Code) : Code × ByteArray :=
  let g := c.groupIds
  (c.gather g.2, classSizes c.n g)

/-- `at(cnt(c), k)`: the count of each row's `k`, `0` where `k` does not occur. -/
def atCnt (cs : Code × ByteArray) (k : Code) : ByteArray := gather 8 cs.2 (cs.1.find k)

/-- `cross(n, m)`: every pair of `n` left and `m` right rows as two index columns, `p div m` and
    `p mod m` over `til (n·m)` (`Ew.val` in place of the row's `expandBytes`/`cycleIds`). -/
def cross (n m : Nat) : ByteArray × ByteArray :=
  let p := tilLongs (n * m).toUSize
  ( Kernel.Ew.val Ew.idiv Ew.i64 Ew.va nul p (one m.toUInt64) (n * m).toUSize
  , Kernel.Ew.val Ew.imod Ew.i64 Ew.va nul p (one m.toUInt64) (n * m).toUSize)

/-- `cross`'s two index columns have one length: both `Ew.val` at the count `n·m` (`Ew.val_size`). -/
theorem cross_len (n m : Nat) : len (cross n m).2 = len (cross n m).1 := by
  simp [cross, len, KernelWF.Ew.val_size]

/-- `anti(x, y)`: the positions of `x` whose code is not in `y` — `member`, `Ew.notBits`, `whereBits`. -/
def anti (x y : Code) : ByteArray := whereBits x.n.toUSize (Ew.notBits x.n (x.member y))

/-- Dense rank of a payload in value order: `binBytes` into its sorted distinct values. -/
def drank (k : Scan.Kind) (b : ByteArray) : ByteArray :=
  let n := (b.size / k.width).toUSize
  let d := Order.distinct k n b
  binBytes k.width.toUSize (isFloat k) true false (Order.sortValues k false (d.size / k.width).toUSize d) b

/-- The rows of a code column `c` cut into one segment per distinct code: the permutation `p` that
    makes each code's rows contiguous (`grade` of its `groupIds`), the `g + 1` offsets of the
    segments in that order (`runStarts`), and each segment's first row in `c`. -/
def segments (c : Code) : ByteArray × ByteArray × ByteArray :=
  let (gid, firsts) := c.groupIds
  let g := Code.ofIds (len firsts) c.n gid
  let p := g.grade
  (p, (g.gather p).runStarts, firsts)

/-- `setIds` read off the codes directly: segment `j`'s codes `vc[o[j] .. o[j+1])` (`Column.resAt` at the
    code's width), sorted with repeats dropped, numbered by first occurrence. One long per segment. -/
def setIdsRef (vc : Code) (o : ByteArray) : ByteArray :=
  slicesRef (fun s => (s.mergeSort fun a b => decide (a ≤ b)).eraseDups) vc o

/-- `setIdsRef` writes one long per segment (`packLongs_size`). -/
theorem setIdsRef_size (vc : Code) (o : ByteArray) : (setIdsRef vc o).size = 8 * (len o - 1) := by
  simp [setIdsRef, slicesRef, packLongs_size]

/-- Set ids: the segments of the codes `vc` start at the longs `s`, the last ending at `vc.n`, so segment `j`
    is `vc[o[j] .. o[j+1])` for `o = s, n`; segments holding equal SETS get equal ids, numbered by first
    occurrence. Each segment is sorted and its repeats dropped — `grade` on (segment, code), `groupIdsPair`
    of the sorted pairs, whose ids rise by one at each new pair, so the id at a segment's first row is the
    kept rows before it — then `rankSlices` at the code's own width, which compares the normalised segments
    as sequences. One long per start. -/
def setIds (vc : Code) (s : ByteArray) : ByteArray :=
  let n := vc.n
  let o := concatBytes #[s, one n.toUInt64]
  let seg := groupOf o n
  let p := gradeBy n #[Code.ofLongs seg, vc]
  let (q, fs) := match vc.kind with
    | some k => Order.groupIdsPair .i64 k n.toUSize (gather 8 seg p) (vc.gather p).b
    | none => Order.groupIdsPairIds 64 vc.w.toUSize n.toUSize (gather 8 seg p) (vc.gather p).b
  let ids := Order.rankSlices vc.w.toUSize (vc.gather (gather 8 p fs)).b
    (gather 8 (concatBytes #[groupLongs n (q, fs), one (len fs).toUInt64]) o)
  -- `rankSlices` declines (answers empty) on offsets out of order or past its payload, which no theorem
  -- yet rules out for these gathered offsets (`rankSlices_size`'s premises); the reference answers there
  if ids.size = 8 * len s then ids else setIdsRef vc o

/-- `setIds` answers one long per start, on both branches: the kernel's by its check, the reference's by
    `setIdsRef_size`, the offsets being the starts and one long more. -/
theorem setIds_size (vc : Code) (s : ByteArray) : (setIds vc s).size = 8 * len s := by
  have hr : (setIdsRef vc (concatBytes #[s, one vc.n.toUInt64])).size = 8 * len s := by
    rw [setIdsRef_size]; simp [len, KernelWF.concatBytes_size, Find.one, Column.pushBits_size]
  unfold setIds
  split <;> (try dsimp only) <;> split <;> assumption

/-- `setIds` as a long column of `len s` rows (`setIds_size`). -/
def setIdCol (vc : Code) (s : ByteArray) : Arr .long (len s) :=
  Arr.mk (.bytes (setIds vc s)) (by simp [Enc.WF, QAtomicType.width, setIds_size]; omega)

/-- `thin(Q)` for `Q` the Pareto order over the columns `cs` of a family keyed by `key`, each column
    `(layout, payload, big)`, larger better exactly when `big`: per set, the rows no row of the set strictly
    dominates (`thinSweep` over the `segments` of the key codes). A column not of longs is
    compared by its dense rank (`drank`). Equal rows of one set are one element: the first is kept.
    Answers the kept rows' indices. -/
def thin {k : QAtomicType} (key : (m : Nat) × Arr k m) (cs : Array (Scan.Kind × ByteArray × Bool)) : Except String ByteArray := do
  let kc := (codes k #v[key])[0]
  let (p, o, _) := segments kc
  let ls := cs.map fun (kd, b, _) => gather 8 (match kd with | .i64 => b | kd => drank kd b) p
  let s := whereBits kc.n.toUSize (thinSweep ls (cs.map (·.2.2)) o)
  let t := tuples.tupleIds (kc.gather (gather 8 p s)) (ls.map fun l => Code.ofLongs (gather 8 l s))
  pure (gather 8 p (gather 8 s t.2))

/-! ## The operators -/

section Gen

variable {A B C : Obj}

/-- `R ⊑ S`: `member` of `|R|` in `|S|`, all set. -/
private def le (R S : Rel A B) : Bool :=
  let c := pairs #v[cols R, cols S]
  len (whereBits R.n.toUSize (c[0].member c[1])) == R.n

/-- `R ∩ S`: the semi-join on pairs — `member`, `whereBits`, `gatherColumn`. -/
private def inter (R S : Rel A B) : Rel A B :=
  let c := pairs #v[cols R, cols S]
  (cols R).rows (whereBits R.n.toUSize (c[0].member c[1]))

/-- `R ∪ S`: `razeColumn` of keys and of vals, the first row of each pair. -/
private def union (R S : Rel A B) : Rel A B :=
  let r := cols R; let s := cols S
  (Cols.mk (k := A) (v := B) (r.n + s.n) (A.raze #[r.key, s.key]) (B.raze #[r.val, s.val])).nub

/-- `𝟘`: no pair. -/
def zero : Rel A B := ⟨0, Vals.empty A, Vals.empty B⟩

/-- `⊤` on the universes `Ua`, `Ub`: `cross`, its two index columns of one length (`cross_len`). -/
def top {ma mb : Nat} (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  let c := cross ma mb
  ⟨len c.1, Vals.pick A Ua.parts c.1, cross_len ma mb ▸ Vals.pick B Ub.parts c.2⟩

/-- `𝟙` on `U`: key and val the one column, shared. -/
def idU {t : Obj} {m : Nat} (U : Vals t m) : Rel t t := ⟨m, U, U⟩

theorem idU_holds {t : Obj} {m : Nat} (U : Vals t m) (x y : t.El) :
    (idU U).Holds x y ↔ x = y ∧ ∃ i, U.row i = x := by
  simp only [Rel.Holds, idU]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨h1 ▸ h2, i, h1⟩, fun ⟨h, i, h1⟩ => ⟨i, h1, h ▸ h1⟩⟩

/-- `R°`: the two fields swap, nothing runs. -/
def convArr {k v : Obj} {n : Nat} (key : Vals k n) (val : Vals v n) : Rel v k := ⟨n, val, key⟩

theorem convArr_holds {k v : Obj} {n : Nat} (key : Vals k n) (val : Vals v n) (x : k.El) (y : v.El) :
    (convArr key val).Holds y x ↔ (⟨n, key, val⟩ : Rel k v).Holds x y := by
  simp only [Rel.Holds, convArr]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

/-- `R°`: `convArr`. -/
private def conv (R : Rel A B) : Rel B A := convArr R.key R.val

/-- `R ≫ S`: `join` on `R.val = S.key`, the key picked from `R`, the val from `S`. -/
private def comp (R : Rel A B) (S : Rel B C) : Rel A C :=
  let r := cols R; let s := cols S
  let c := B.codes #v[r.val, s.key]
  let ij := join c[0] c[1]
  ⟨len ij.2, Vals.pickN A r.key ij.1 (len ij.2) (join_len c[0] c[1]), Vals.pick C s.val ij.2⟩

/-- The coreflexive on the distinct elements of `x`: the first row of each code. -/
def distinctCorefl (t : Obj) (x : Part t) : Rel t t :=
  let i := (t.codes #v[x])[0].groupIds.2
  let d := Vals.pick t x i
  ⟨len i, d, d⟩

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel A B) : Rel A A := distinctCorefl A (cols R).key

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel A B) : Rel B B := distinctCorefl B (cols R).val

/-- `R ≫ corNeg(C)`, the anti-join: the rows of `R` whose value is no value of `C` (`anti` on one joint coding). -/
def antiJoin (R : Rel A B) (C : Rel B B) : Rel A B :=
  let r := cols R
  let vc := B.codes #v[r.val, (cols C).val]
  r.rows (anti vc[0] vc[1])

/-- `R − S`: the rows of `R` whose pair is no pair of `S` — `inter`'s joint pair codes, `anti` in place of `member`. -/
private def diff (R S : Rel A B) : Rel A B :=
  let c := pairs #v[cols R, cols S]
  (cols R).rows (anti c[0] c[1])

/-! ## The ops as binary operators: the only way a program writes them -/

instance : Inter (Rel A B) := ⟨inter⟩
instance : Union (Rel A B) := ⟨union⟩
instance : SDiff (Rel A B) := ⟨diff⟩
/-- `R ≫ S`: composition in diagram order, first `R` then `S`. -/
scoped infixl:80 " ≫ " => comp
/-- `R°`: the converse. -/
scoped postfix:max "°" => conv
/-- `R ⊑ S`: inclusion, decided. -/
scoped infix:50 " ⊑ " => le
/-- `R = S` as `R ⊑ S ∧ S ⊑ R`: the same pairs, whatever the row order and multiplicity. -/
instance : BEq (Rel A B) := ⟨fun R S => R ⊑ S && S ⊑ R⟩

/-- The elements of the object `A` in this program: what `𝟙` and `⊤` range over. -/
class Univ (A : Obj) where
  n : Nat
  xs : Vals A n

/-- `𝟙 : A ⟶ A`, the identity on the elements of `A`. -/
scoped notation "𝟙" => idU Univ.xs
/-- `⊤ : A ⟶ B`, every pair. -/
scoped notation "⊤" => top Univ.xs Univ.xs
/-- `∼R`: the complement of `R` in `⊤`. -/
scoped notation:max "∼" R:max => ⊤ \ R

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `⊤` on `anti(Ub, ran R)` and `Uc`. The two parts are disjoint (a counted `y` is in
    `ran R`) and meet by `∪`, whose counts are proved where a `raze` of the parts would need its own. -/
def leftDiv {mb mc : Nat} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc) : Rel B C :=
  let r := cols (cols R).nub; let s := cols (cols S).nub
  let kc := A.codes #v[r.key, s.key]
  let (i, j) := join kc[0] kc[1]
  let y := B.pick r.val i; let z := C.pick s.val j
  let ycs := B.codes #v[y, r.val, Ub.parts]
  let yc := ycs[0]; let rvc := ycs[1]; let ubc := ycs[2]
  let zc := (C.codes #v[z])[0]
  let (gid, firsts) := tuples.tupleIds yc #[zc]
  let got := classSizes yc.n (gid, firsts)
  let keep := gather 8 firsts (whereEqV got (atCnt (cnt rvc) (yc.gather firsts)))
  union ((Cols.mk (len keep) y z).rows keep) (top (Vals.pick B Ub.parts (anti ubc rvc)) Uc)

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `⊤` on `Ua` and `anti(Ub, dom S)`. -/
def rightDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  conv (leftDiv (conv S) (conv R) Ub Ua)

/-- `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres: the fibres of `R` and of `S` as `segments`
    of one value code space, their `setIds` in one call, `join` on the ids → `(x, y)`, the keys read as
    `comp` reads them (`join_len`); the vacuous term `⊤` on `anti(Ua, dom R)` and `anti(Ub, dom S)`, the
    empty fibres, met by `∪`. -/
def symDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb) : Rel A B :=
  let r := cols R; let s := cols S
  let vc := C.codes #v[r.val, s.val]
  let ac := A.codes #v[r.key, Ua.parts]; let rk := ac[0]; let uac := ac[1]
  let bc := B.codes #v[s.key, Ub.parts]; let sk := bc[0]; let ubc := bc[1]
  let (pr, orr, fr) := segments rk; let (ps, os, fs) := segments sk
  -- each `segments` offsets end at its code count, so `S`'s starts shifted by `|R|` follow `R`'s
  let ids := setIds (Code.cat #[vc[0].gather pr, vc[1].gather ps])
    (concatBytes #[orr.extract 0 (orr.size - 8), addc (os.extract 0 (os.size - 8)) r.n])
  let lc := Code.ofLongs (ids.extract 0 (8 * len fr)); let rc := Code.ofLongs (ids.extract (8 * len fr) ids.size)
  let ij := join lc rc
  let hit : Rel A B := ⟨len ij.2, Vals.pickN A (A.pick r.key fr) ij.1 (len ij.2) (join_len lc rc),
    Vals.pick B (B.pick s.key fs) ij.2⟩
  union hit (top (Vals.pick A Ua.parts (anti uac rk)) (Vals.pick B Ub.parts (anti ubc sk)))

/-- `Λ(R) : A ⟶ list B`: one row per distinct key of `R`, its cell the ARRAY of the key's values, each once,
    in ascending value order (`sortBy`), so two keys with one set of values have one array — across two
    relations too, where `sortBy` orders by value. `Cols.nub`, the values sorted, then the keys' codes
    graded stably: each key one run, whose start and end (`runStarts`) are its row's `lo`, `hi`. -/
def transpose (R : Rel A B) : Rel A (.list B) :=
  let d := cols (cols R).nub
  let kc := (A.codes #v[d.key])[0]
  let vp := B.sortBy d.val (tilLongs d.n.toUSize)
  let p := gather 8 vp (kc.gather vp).grade
  let o := (kc.gather p).runStarts
  let lo := o.extract 0 (o.size - 8)
  have h : len (o.extract 8 o.size) = len lo := by simp only [len, lo, ByteArray.size_extract]; omega
  ⟨len lo, Vals.pick A (A.pick d.key p) lo, ⟨len p, longCol lo, h ▸ longCol (o.extract 8 o.size), Vals.pick B d.val p⟩⟩

/-- `∋ : list B ⟶ B` on the arrays `X`: each array to each of its elements, one row per element (an array
    holding a value twice relates to it twice). `expand` of the clamped slice counts, each copy's rank
    added to its slice's start; the array's row read at the element's count (`add_len_le`). -/
def mem {n : Nat} (X : Vals (.list B) n) : Rel (.list B) B :=
  let s := slices X.1 (longsOf X.2.1) (longsOf X.2.2.1)
  let e := expand s.2
  let j := add (gather 8 s.1 e.1) e.2
  have h : len j ≤ len e.1 := Nat.le_trans (add_len_le _ _) (Nat.le_of_eq (gather_len _ _))
  ⟨len j, Vals.pickN (.list B) X.parts e.1 (len j) h, Vals.pick B X.2.2.2.parts j⟩

/-- `Λ(R) : A ⟶ list B`, each key of `R` to the array of its values. -/
scoped notation:max "Λ(" R ")" => transpose R
/-- `∋(R) : list B ⟶ B`, `mem` on the arrays of `Λ(R)`: `Λ(R) ≫ ∋(R) = R`. -/
scoped notation:max "∋(" R ")" => mem (Rel.val (transpose R))

end Gen

variable {A B C : QAtomicType}

/-- `⟨R, S⟩`: `join` on the keys → rows `(x, (y, z))`, both value sides kept under one `n` as the
    columns of one product side; the left index column read at the right's count (`join_len`), as `comp`. -/
def pair {A B C : Obj} (R : Rel A B) (S : Rel A C) : Rel A (.prod B C) :=
  let r := cols R; let s := cols S
  let kc := A.codes #v[r.key, s.key]
  let ij := join kc[0] kc[1]
  let h := join_len kc[0] kc[1]
  ⟨len ij.2, Vals.pickN A r.key ij.1 (len ij.2) h, (Vals.pickN B r.val ij.1 (len ij.2) h, Vals.pick C s.val ij.2)⟩

/-- `outl`: the first component's columns, nothing runs. -/
def outl {k v w : Obj} (T : Rel k (.prod v w)) : Rel k v := ⟨T.n, T.key, T.val.1⟩
/-- `outr`: the second component's columns. -/
def outr {k v w : Obj} (T : Rel k (.prod v w)) : Rel k w := ⟨T.n, T.key, T.val.2⟩

/-- The rows of `R` numbered from `k`: row `i` keyed by `k + i`, its value kept — `Ew.val` add on `til`
    at the count `m`, which the row index is too (`Ew.val_size`). Row order enters here, as in `enum`. -/
def num {A B : Obj} (R : Rel A B) (k : Nat) : Rel .long B :=
  let m := R.n.toUSize
  let s := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (tilLongs m) (one k.toUInt64) m
  let i := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (tilLongs m) (one 0) m
  have h : len s = len i := by simp only [len, s, i, KernelWF.Ew.val_size]
  have w : Kernel.Ew.width Ew.i64 = 8 := rfl
  let a : Arr .long (len s) := Arr.mk (.bytes s) (by simp [Enc.WF, QAtomicType.width, len, s, KernelWF.Ew.val_size, w])
  ⟨len i, h ▸ a, Vals.pick B R.val.parts i⟩

theorem outl_holds {k v w : Obj} (T : Rel k (.prod v w)) (x : k.El) (y : v.El) :
    (outl T).Holds x y ↔ ∃ z, T.Holds x (y, z) :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨T.val.2.row i, i, h1, by subst h2; rfl⟩, fun ⟨_, i, h1, h2⟩ => ⟨i, h1, congrArg Prod.fst h2⟩⟩

theorem outr_holds {k v w : Obj} (T : Rel k (.prod v w)) (x : k.El) (z : w.El) :
    (outr T).Holds x z ↔ ∃ y, T.Holds x (y, z) :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨T.val.1.row i, i, h1, by subst h2; rfl⟩, fun ⟨_, i, h1, h2⟩ => ⟨i, h1, congrArg Prod.snd h2⟩⟩

/-- `R × S` as a relation of its own, `(x, x') ⟶ (y, y')`: `cross` of the rows of `R` and of `S`.
    `Δ(R)` is `prod R R`. Its two index columns have one length (`cross_len`). -/
def prod {A B D E : Obj} (R : Rel A B) (S : Rel D E) : Rel (.prod A D) (.prod B E) :=
  let r := cols R; let s := cols S
  let c := cross r.n s.n
  ⟨len c.1, (Vals.pick A r.key c.1, cross_len r.n s.n ▸ Vals.pick D s.key c.2),
    (Vals.pick B r.val c.1, cross_len r.n s.n ▸ Vals.pick E s.val c.2)⟩

/-- A relation out of a sum `a + a`: a tag bit beside each key, `false` for `inl`. Read with the
    value tagged by the key's own tag it is `R + S` as well as `[R, S]`. -/
structure SumRel (k v : QAtomicType) where
  n : Nat
  tag : Arr .boolean n
  key : Arr k n
  val : Arr v n

def SumRel.toList {k v : QAtomicType} (T : SumRel k v) : List ((Bool × El k) × El v) :=
  List.ofFn fun i => ((T.tag.get i, T.key.get i), T.val.get i)

/-- `n` bits, all `x`: `Ew.cmp` of `til n` against `0`. -/
def bitsOf (x : Bool) (n : Nat) : ByteArray :=
  Ew.cmp (if x then Ew.ge else Ew.lt) Ew.i64 Ew.va (tilLongs n.toUSize) (one 0) n.toUSize

/-- The tag column of parts `ps`, each `(count, tag)`, `m` the summed count: `concatBits` of constant bit
    columns, of the summed count whatever the parts' payloads hold (`concatBits_wf`). -/
def tags (ps : Array (Nat × Bool)) (m : Nat) (h : ps.foldl (fun s p => s + p.1) 0 = m := by simp) : Arr .boolean m :=
  let bs : Array (Nat × ByteArray) := ps.map fun p => (p.1, bitsOf p.2 p.1)
  have hb : bs.foldl (fun s p => s + p.1) 0 = m := by rw [Array.foldl_map]; exact h
  Arr.mk (.bits (concatBits (bs.map (·.1)) (bs.map (·.2)))) (hb ▸ KernelWF.concatBits_wf bs)

/-- A general list's boxed elements are its count. -/
theorem gens_size {n : Nat} (x : Arr .general n) : (gens x).size = n := by
  obtain ⟨xs, he, hs⟩ := KernelWF.general_cases x.wf
  rw [show gens x = xs from Option.some_inj.1 ((Option.some_get _).trans (by simp [he])), hs]

/-- **`raze` counts the sum of its parts' counts**, on every branch: `razeColumn_count` where the counts
    fit a `USize`, `count_atoms` on the reference past it. -/
theorem raze_len (t : QAtomicType) (cs : Array ((n : Nat) × Arr t n)) :
    (raze t cs).1 = (cs.toList.map (·.1)).sum := by
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0; simp [empty_len]
  rw [dif_neg (by simpa using h0)]
  by_cases hg : t = .general
  · subst hg
    simp only [dif_pos, genCol, List.foldl_toArray']
    have key : ∀ (l : List ((n : Nat) × Arr .general n)) (acc : Array QValue),
        (l.foldl (fun xs c => xs ++ gens c.2) acc).size = acc.size + (l.map (·.1)).sum := by
      intro l; induction l with
      | nil => simp
      | cons c l ih => intro acc; simp [ih, gens_size, Nat.add_assoc]
    simp [key]
  rw [dif_neg hg]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  split
  · have key : ∀ (a : Nat) (l : List ((n : Nat) × Arr t n)),
        (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1) a = a + (l.map (·.1)).sum := by
      intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
    simpa [Arr.part] using key 0 l
  · simp
    exact congrArg List.sum (List.map_congr_left fun c _ => Column.count_atoms c.2.wf hg)

/-- `[R, S]`: the rows of `R` tagged `inl`, of `S` tagged `inr` (`tags`); keys and vals `raze`d, of
    `R.n + S.n` rows (`raze_len`). -/
def junc (R : Rel A C) (S : Rel A C) : SumRel A C :=
  let r := cols R; let s := cols S
  have hk : (raze A #[r.key, s.key]).1 = r.n + s.n := by simp [raze_len, r, s, cols, Vals.parts]
  have hv : (raze C #[r.val, s.val]).1 = r.n + s.n := by simp [raze_len, r, s, cols, Vals.parts]
  ⟨r.n + s.n, tags #[(r.n, false), (s.n, true)] _, hk ▸ (raze A #[r.key, s.key]).2, hv ▸ (raze C #[r.val, s.val]).2⟩

/-- `inl°` on `U`: `inl x ↦ x`, the tag set to `false`; `inr°` with `true`. -/
def injConv {m : Nat} (tag : Bool) (U : Arr A m) : SumRel A A :=
  ⟨m, tags #[(m, tag)] m, U, U⟩

/-- `F(f)` on a map `f` given as an `Ew` monad: the functor on values, key kept (a `grp` key too). -/
def mapVal {k : QAtomicType} {a : QAtomicType} (op : UInt8) (R : Rel k a) : Except String (Rel k a) := do
  let (vk, v) ← arrDense R.val
  let some nb := nullBits a | throw "a type with no null"
  pure ⟨R.n, R.key, ← Arr.ofPart a R.n (R.n, .bytes (Kernel.Ew.mon op (cls vk) nb.toInt64 v R.n.toUSize)) "mapVal"⟩

/-- `⦇e, f⦈` of a list when `f` is one of `Coc.Over`'s reductions: `overBytes`. -/
def foldOver {n : Nat} (op : Coc.Over) (x : Arr .long n) : Except String Int64 := do
  let (_, v) ← arrDense x
  pure (overBytes op Ew.i64 nul v)

/-- The same per key: `overGroups` over the key codes' `groupIds`, one row per distinct key. -/
def foldGroups (op : Coc.Over) (R : Rel A .long) : Except String (Rel A .long) := do
  let r := cols R; let (_, v) ← arrDense R.val
  let (gid, firsts) := (codes A #v[r.key])[0].groupIds
  let ng := len firsts
  pure (ofCols A .long (pick A r.key firsts)
    ⟨ng, ← Arr.ofPart .long ng (longs ((overGroups op Ew.i64 nul ng.toUSize (Column.idWidthOf ng).toUSize r.n gid v).extract 0 (8 * ng))) "foldGroups"⟩)

/-- `α⁻¹` of a list, `uncons`: its first element and the rest, two picks (`gatherColumn`). -/
def uncons {n : Nat} (x : Arr B (n + 1)) : Except String (Arr B 1 × Arr B n) := do
  let rest := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (tilLongs n.toUSize) (one 1) n.toUSize
  pure (Vals.ofParts (.atom B) 1 (pick B ⟨n + 1, x⟩ (one 0)), Vals.ofParts (.atom B) n (pick B ⟨n + 1, x⟩ rest))

/-- An unfold then a fold: Lean's loop, rounds of `step` until `done`, each round kernels. It ends because
    each round not `done` lowers the measure `μ`: well-founded recursion, no fuel. -/
def hylo {α : Type} (μ : α → Nat) (done : α → Bool) (step : α → α)
    (dec : ∀ x, done x = false → μ (step x) < μ x) (x : α) : α :=
  if h : done x then x else hylo μ done step dec (step x)
termination_by μ x
decreasing_by exact dec x (Bool.eq_false_iff.2 h)

/-- `f` from `a` until `done`, at most `n` rounds: `hylo` with the rounds left as its measure, so a caller
    bounds the iteration by a count instead of proving a measure of its own. -/
def iter {α : Type} (n : Nat) (done : α → Bool) (f : α → α) (a : α) : α :=
  (hylo (·.1) (fun x => x.1 == 0 || done x.2) (fun x => (x.1 - 1, f x.2))
    (fun x h => by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h; show x.1 - 1 < x.1; omega) (n, a)).2

/-- `est(≤)` (`desc`: `est(≥)`) of a family of longs: `overGroups` lesser/greater per key. -/
def est (desc : Bool) (G : Rel A .long) : Except String (Rel A .long) :=
  foldGroups (if desc then .greater else .lesser) G

/-- `Entire R` on the universe `U`: `member` of `U`'s codes in the keys', all set. -/
def entire {A B : Obj} {m : Nat} (R : Rel A B) (U : Vals A m) : Except String Bool := do
  let r := cols R
  let c := A.codes #v[U.parts, r.key]
  pure (len (whereBits m.toUSize (c[0].member c[1])) == m)

/-- `Simple R`: in `R` with each pair once, every key distinct (`groupIds` count of the key codes). -/
def simple {A B : Obj} (R : Rel A B) : Except String Bool := do
  let r := cols (cols R).nub
  pure (len (A.codes #v[r.key])[0].groupIds.2 == r.n)

def isMap {A B : Obj} {m : Nat} (R : Rel A B) (U : Vals A m) : Except String Bool := do
  pure ((← entire R U) && (← simple R))

/-- `Injective R` = `Simple R°`. -/
def injective {A B : Obj} (R : Rel A B) : Except String Bool := do simple (conv R)

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`. -/
def surjective {A B : Obj} {m : Nat} (R : Rel A B) (U : Vals B m) : Except String Bool := do
  entire (conv R) U

/-! ## Checks against the `toList` specs, on small literal relations -/

section Checks

private abbrev L := QAtomicType.long
private abbrev LL := Rel .long .long

private def seteq {α : Type} [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains
private def ok {α : Type} (x : Except String α) (p : α → Bool) : Bool := match x with | .ok v => p v | .error _ => false

-- R = {1↦10, 1↦20, 2↦10, 3↦30}, S = {1↦10, 2↦10, 2↦20, 4↦40}
private def R : LL := ⟨4, (Arr.mk (.bytes <| packLongs [1, 1, 2, 3]) (by decide)), (Arr.mk (.bytes <| packLongs [10, 20, 10, 30]) (by decide))⟩
private def S : LL := ⟨4, (Arr.mk (.bytes <| packLongs [1, 2, 2, 4]) (by decide)), (Arr.mk (.bytes <| packLongs [10, 10, 20, 40]) (by decide))⟩
-- T : b ⟶ c, {10↦7, 20↦8, 20↦9}
private def T : LL := ⟨3, (Arr.mk (.bytes <| packLongs [10, 20, 20]) (by decide)), (Arr.mk (.bytes <| packLongs [7, 8, 9]) (by decide))⟩
-- a list with a repeat, (5 3 5 9), and the same as a relation from its positions
private def U4 : Vals L 4 := (Arr.mk (.bytes <| packLongs [0, 1, 2, 3]) (by decide))
private def LsV : Arr L 4 := (Arr.mk (.bytes <| packLongs [5, 3, 5, 9]) (by decide))
private def Ls : LL := ⟨4, U4, LsV⟩
private def Ua : Vals L 4 := (Arr.mk (.bytes <| packLongs [1, 2, 3, 4]) (by decide))
private def Ub : Vals L 4 := (Arr.mk (.bytes <| packLongs [10, 20, 30, 40]) (by decide))
private def Uc : Vals L 3 := (Arr.mk (.bytes <| packLongs [7, 8, 9]) (by decide))

#guard le R S == false
#guard le (inter R S) R && le (inter R S) S
#guard seteq (inter R S).toList (R.toList.filter S.toList.contains)
#guard seteq (diff R S).toList (R.toList.filter fun p => !S.toList.contains p)
#guard (diff R R).n == 0
#guard seteq (union (inter R S) (diff R S)).toList R.toList
#guard seteq (union R S).toList (R.toList ++ S.toList) && (union R S).n == 6
#guard (zero (A := L) (B := L)).n == 0
#guard seteq (top Ua Uc).toList (Ua.toList.flatMap fun x => Uc.toList.map (x, ·))
#guard (idU Ua).toList == Ua.toList.map fun x => (x, x)
#guard seteq (conv R).toList (R.toList.map fun (x, y) => (y, x))
#guard seteq (conv Ls).toList (Ls.toList.map fun (x, y) => (y, x))
#guard seteq (comp R T).toList
  (R.toList.flatMap fun (x, y) => T.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard seteq (comp Ls Ls).toList
  (Ls.toList.flatMap fun (x, y) => Ls.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard seteq (dom R).toList [(1, 1), (2, 2), (3, 3)] && (dom R).n == 3
#guard seteq (ran S).toList [(10, 10), (20, 20), (40, 40)] && (ran S).n == 3

-- `R \ S` over `Ub × Ub`: `y (R\S) z ↔ ∀ x, x R y → x S z`
private def leftSpec (R S : LL) (Ub Uc : List Int64) : List (Int64 × Int64) :=
  Ub.flatMap fun y => (Uc.filter fun z => R.toList.all fun (x, y') => y' != y || S.toList.contains (x, z)).map (y, ·)
#guard seteq (leftDiv R S Ub Ub).toList (leftSpec R S Ub.toList Ub.toList)
#guard seteq (leftDiv R R Ub Ub).toList (leftSpec R R Ub.toList Ub.toList)
-- `R / S` (`R : a ⟶ c`, `S : b ⟶ c`): `x (R/S) y ↔ ∀ z, y S z → x R z`
#guard seteq (rightDiv R S Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => S.toList.all fun (y', z) => y' != y || R.toList.contains (x, z)).map (x, ·))
-- `R /ₛ S`: equal fibres
private def fib (R : LL) (x : Int64) : List Int64 := R.toList.filterMap fun (x', z) => if x == x' then some z else none
#guard seteq (symDiv R S Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib S y)).map (x, ·))
#guard seteq (symDiv R R Ua Ua).toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib R y)).map (x, ·))

/-- The facts of `Λ(R)`: (1) `Λ(R) ≫ ∋(R) = R`; (2) one row per distinct key of `R`; (3) each cell is the
    key's values, each once; (4) `Λ(R) ≫ Λ(R)°` relates two keys iff they have one set of values. -/
private def lamOk {A B : Obj} [BEq A.El] [BEq B.El] (R : Rel A B) : Bool :=
  let Lm := Λ(R)
  let r := R.toList; let l : List (A.El × List B.El) := Lm.toList
  let fibr (x : A.El) := r.filterMap fun (x', z) => if x == x' then some z else none
  let same := (Lm ≫ Lm°).toList
  (Lm ≫ ∋(R) == R) &&
  (l.map (·.1)).eraseDups.length == l.length && seteq (l.map (·.1)) (r.map (·.1)) &&
  l.all (fun (x, c) => seteq c (fibr x) && c.eraseDups.length == c.length) &&
  l.all (fun (x, _) => l.all fun (y, _) => same.contains (x, y) == seteq (fibr x) (fibr y))

/-- Arrays across two relations: `Λ(R₁) ≫ Λ(R₂)°` relates a key of `R₁` to a key of `R₂` iff their sets of
    values are one, and `ran (Λ(R₁) ∪ Λ(R₂))` holds each distinct set once. -/
private def crossOk {A B : Obj} [BEq A.El] [BEq B.El] (R₁ R₂ : Rel A B) : Bool :=
  let f (R : Rel A B) (x : A.El) : List B.El := R.toList.filterMap fun (x', z) => if x == x' then some z else none
  let k₁ := (R₁.toList.map (·.1)).eraseDups; let k₂ := (R₂.toList.map (·.1)).eraseDups
  let rel := (Λ(R₁) ≫ Λ(R₂)°).toList
  let sets := k₁.map (f R₁) ++ k₂.map (f R₂)
  let distinct := sets.foldl (fun acc s => if acc.any (seteq s) then acc else acc ++ [s]) ([] : List (List B.El))
  k₁.all (fun x => k₂.all fun y => rel.contains (x, y) == seteq (f R₁ x) (f R₂ y)) &&
  (ran (Λ(R₁) ∪ Λ(R₂))).n == distinct.length

-- `Λ(R)`, `∋(R)`: R with a repeated pair, R ∪ S, a key with a repeat and its values out of order (D, below),
-- a foR column, an empty relation, the family `G`, `G ≫ R`
#guard lamOk R && lamOk S && lamOk (union R R) && lamOk (union R S) && lamOk T && lamOk Ls && lamOk (conv Ls)
#guard lamOk (zero (A := L) (B := L)) && lamOk (comp R T) && lamOk (conv R)
#guard (Λ(R).toList : List (Int64 × List Int64)) == [(1, [10, 20]), (2, [10]), (3, [30])] && ∋(R).n == 4
-- arrays of pairs: `B = X×X`
#guard lamOk (pair R S) && lamOk (pair S R) && crossOk (pair R S) (pair S R) && crossOk (pair R R) (pair R S)
private def LfV : Arr L 4 := Arr.mk (.foR (Coc.encode 8 (packLongs [5, 3, 5, 9])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9])).2) (foRLongs_wf [5, 3, 5, 9])
private def Lf : LL := ⟨4, U4, LfV⟩
#guard lamOk Lf && lamOk (conv Lf) && Λ(conv Lf).n == 3
#guard Λ(union R R).n == 3 && ∋(union R R).n == 4
#guard Λ(zero (A := L) (B := L)).n == 0 && ∋(zero (A := L) (B := L)).n == 0
-- `anti`: the positions of `x` not in `y`
#guard anti (Code.ofLongs (packLongs [3, 1, 4, 1])) (Code.ofLongs (packLongs [1, 5])) == packLongs [0, 2]
-- `R ≫ corNeg(C)` at a `C` that is no coreflexive: `1` is a key of `C` and no value, so the row stays
private def Ra : LL := ⟨1, (Arr.mk (.bytes <| packLongs [0]) (by decide)), (Arr.mk (.bytes <| packLongs [1]) (by decide))⟩
private def Ca : LL := ⟨1, (Arr.mk (.bytes <| packLongs [1]) (by decide)), (Arr.mk (.bytes <| packLongs [2]) (by decide))⟩
#guard (antiJoin Ra Ca).toList == [(0, 1)]
-- `E(R)` of the family `G = {X₁ = {1, 2}, X₂ = {3}}`: `Λ(G ≫ R)`
private def G : LL := ⟨3, (Arr.mk (.bytes <| packLongs [1, 1, 2]) (by decide)), (Arr.mk (.bytes <| packLongs [1, 2, 3]) (by decide))⟩
#guard lamOk G && lamOk (comp G R) && seteq (comp Λ(comp G R) ∋(comp G R)).toList
  (G.toList.flatMap fun (s, x) => R.toList.filterMap fun (x', y) => if x == x' then some (s, y) else none)
-- arrays across two relations: `[10 20]` and `[10]` are cells of both, `[30]` and `[40]` of one
#guard seteq (comp Λ(R) (conv Λ(S))).toList [(1, 2), (2, 1)] && (ran (union Λ(R) Λ(S))).n == 4
#guard crossOk R S && crossOk S R && crossOk R R && crossOk Lf Ls && crossOk (zero (A := L) (B := L)) R
-- a list column built by hand: `[1 2] [2 1] [1 1] [1 2]`, equal as arrays only where equal position by
-- position, so rows 0 and 3 alone; `∋` one row per element, a repeat twice
private def Xs : Vals (.list L) 4 := ⟨8, col [0, 2, 4, 6], col [2, 4, 6, 8], col [1, 2, 2, 1, 1, 1, 1, 2]⟩
private def K : Rel L (.list L) := ⟨4, U4, Xs⟩
#guard (K.toList.map (·.2) : List (List Int64)) == [[1, 2], [2, 1], [1, 1], [1, 2]]
#guard seteq (comp K (conv K)).toList [(0, 0), (0, 3), (3, 0), (3, 3), (1, 1), (2, 2)] && (ran K).n == 3
#guard ((mem Xs).toList : List (List Int64 × Int64)) ==
  [([1, 2], 1), ([1, 2], 2), ([2, 1], 2), ([2, 1], 1), ([1, 1], 1), ([1, 1], 1), ([1, 2], 1), ([1, 2], 2)]
-- slices past the payload read clamped: `[-1, 1)` is `[1]`, `[3, 9)` is `[1 2]`, `[5, 2)` is empty
private def Xc : Vals (.list L) 3 := ⟨4, col [-1, 2, 5], col [1, 9, 2], col [1, 5, 1, 2]⟩
#guard ((idU Xc).toList.map (·.1) : List (List Int64)) == [[1], [1, 2], []]
#guard ((mem Xc).toList : List (List Int64 × Int64)) == [([1], 1), ([1, 2], 1), ([1, 2], 2)]
#guard (comp (idU Xc) (mem Xc)).n == 3 && (ran (idU Xc)).n == 3

#guard seteq (pair R S).toList
  (R.toList.flatMap fun (x, y) => S.toList.filterMap fun (x', z) => if x == x' then some (x, y, z) else none)
#guard seteq (outl (pair R S)).toList (R.toList.filter fun (x, _) => S.toList.any (·.1 == x))
#guard seteq (outr (pair R S)).toList (S.toList.filter fun (x, _) => R.toList.any (·.1 == x))
#guard seteq (prod R T).toList
  (R.toList.flatMap fun (x, x') => T.toList.map fun (y, y') => ((x, y), (x', y')))
#guard seteq (junc R S).toList (R.toList.map (fun (x, y) => ((false, x), y)) ++ S.toList.map fun (x, y) => ((true, x), y))
#guard (injConv true Ua).toList == Ua.toList.map fun x => ((true, x), x)

#guard ok (mapVal Ew.neg Ls) fun X => X.toList == [(0, -5), (1, -3), (2, -5), (3, -9)]
#guard ok (foldOver .add Ls.val) (· == 22)
#guard ok (foldGroups .add R) fun X => X.toList == [(1, 30), (2, 10), (3, 30)]
#guard ok (uncons LsV) fun (h, t) => h.toList == [5] && t.toList == [3, 5, 9]
-- an unfold then a fold: uncons to the end, summing the heads
-- the state is the rest and the sum; the measure is the rest's length, `0` once a step has failed, so the
-- loop ends there too (`uncons` and `foldOver` still answer `Except`)
private abbrev St := Except String (((m : Nat) × Arr L m) × Int64)
private def stM : St → Nat | .ok (xs, _) => xs.1 | .error _ => 0
private def stStep : St → St
  | .ok (⟨k + 1, x⟩, acc) => match uncons x with
    | .ok (h, t) => match foldOver .add h with
      | .ok s => .ok (⟨k, t⟩, acc + s)
      | .error e => .error e
    | .error e => .error e
  | s => s
private theorem stStep_dec : ∀ s, (stM s == 0) = false → stM (stStep s) < stM s
  | .ok (⟨k + 1, x⟩, acc), _ => by
    simp only [stStep]; split
    · split <;> simp [stM]
    · simp [stM]
  | .ok (⟨0, _⟩, _), h => by simp [stM] at h
  | .error _, h => by simp [stM] at h
#guard ok (hylo stM (stM · == 0) stStep stStep_dec (.ok (⟨_, LsV⟩, 0))) fun (_, s) => s == 22
#guard ok (est false R) fun X => X.toList == [(1, 10), (2, 10), (3, 30)]
#guard ok (est true R) fun X => X.toList == [(1, 20), (2, 10), (3, 30)]
-- thin, k = 1: per key of `R` the largest value, then the smallest
private def lc (xs : List Int64) (big : Bool) : Scan.Kind × ByteArray × Bool := (.i64, packLongs xs, big)
#guard ok (thin ⟨_, col [1, 1, 2, 3]⟩ #[lc [10, 20, 10, 30] true]) (· == packLongs [1, 2, 3])
#guard ok (thin ⟨_, col [1, 1, 2, 3]⟩ #[lc [10, 20, 10, 30] false]) (· == packLongs [0, 2, 3])
-- k = 2, one set (1,5) (3,2) (2,2) (3,1) (1,5): both larger → (1,5) and (3,2), one copy each;
-- the second smaller → (3,1) alone
private def k5 : (m : Nat) × Arr L m := ⟨_, col [1, 1, 1, 1, 1]⟩
#guard ok (thin k5 #[lc [1, 3, 2, 3, 1] true, lc [5, 2, 2, 1, 5] true]) (· == packLongs [0, 1])
#guard ok (thin k5 #[lc [1, 3, 2, 3, 1] true, lc [5, 2, 2, 1, 5] false]) (· == packLongs [3])
-- k = 3, two sets: {(1,1,1) (2,2,2) (2,2,2) (3,0,0)} keeps (2,2,2) once and (3,0,0);
-- {(0,5,0) (0,4,1) (0,4,0)} drops (0,4,0); a key interleaved: set 2's rows come first
#guard ok (thin ⟨_, col [1, 1, 1, 1, 2, 2, 2]⟩ #[lc [1, 2, 2, 3, 0, 0, 0] true, lc [1, 2, 2, 0, 5, 4, 4] true,
    lc [1, 2, 2, 0, 0, 1, 0] true]) (· == packLongs [1, 3, 4, 5])
#guard ok (thin ⟨_, col [2, 1, 2, 1, 1, 2, 1]⟩ #[lc [0, 1, 0, 2, 2, 0, 3] true, lc [5, 1, 4, 2, 2, 4, 0] true,
    lc [0, 1, 1, 2, 2, 0, 0] true]) (· == packLongs [0, 2, 3, 6])
-- setIds: segments {3 1 1} {1 3} {2} {} {} {1 3 3}: the three spellings of {1, 3} one id, `{}` one id
#guard setIds (Code.ofLongs (packLongs [3, 1, 1, 1, 3, 2, 1, 3, 3])) (packLongs [0, 3, 5, 6, 6, 6]) ==
  packLongs [0, 0, 1, 2, 2, 0]
-- Λ(R ∪ S): fibres {10 20} {10 20} {30} {40}
#guard (ran Λ(union R S)).n == 3
-- Λ of {1↦10, 2↦20, 1↦20, 2↦10, 2↦10}: both fibres {10, 20}, in another order and with a repeat
private def D : LL := ⟨5, (Arr.mk (.bytes <| packLongs [1, 2, 1, 2, 2]) (by decide)), (Arr.mk (.bytes <| packLongs [10, 20, 20, 10, 10]) (by decide))⟩
#guard (Λ(D).toList.map (·.2) : List (List Int64)) == [[10, 20], [10, 20]] && ∋(D).n == 4 && lamOk D &&
  lamOk (conv D) && lamOk (union D R) && crossOk D R && crossOk D S
-- the reference `setIds` falls back on agrees with the kernel path, repeats and order inside a set ignored
#guard let c := Code.ofLongs (packLongs [1, 2, 2, 1, 1, 2, 5, 5, 3]); let s := packLongs [0, 2, 4, 6, 8, 8]
  setIds c s == packLongs [0, 0, 0, 1, 2, 3] && setIdsRef c (packLongs [0, 2, 4, 6, 8, 8, 9]) == setIds c s

private def Ua3 : Vals L 3 := (Arr.mk (.bytes <| packLongs [3, 1, 2]) (by decide))
#guard ok (entire R Ua) (· == false) && ok (entire R Ua3) id
#guard ok (simple R) (· == false) && ok (simple (idU Ua)) id && ok (simple Ls) id
#guard ok (isMap (idU Ua) Ua) id
#guard ok (injective Ls) (· == false) && ok (injective T) id
#guard ok (surjective R Ub) (· == false) && ok (surjective (idU Ub) Ub) id

/-! ### Every other encoding: the list `i ↦ x i` of four elements in each, against its own spec -/

/-- A list over the payload `c`. -/
private def lstV (t : QAtomicType) (c : Nat × Enc) : Except String ((m : Nat) × Arr t m) := do
  let n := c.1
  pure ⟨n, ← Arr.ofPart t n c "lst"⟩
/-- The same as a relation from its positions, `tilLongs` the key. -/
private def lst (t : QAtomicType) (c : Nat × Enc) : Except String (Rel L t) := do
  let x ← lstV t c
  pure ⟨x.1, ← Arr.ofPart L x.1 (longs (tilLongs x.1.toUSize)) "lst", x.2⟩
/-- `L ≫ L°`: the pairs of positions holding one element. -/
private def same {t : QAtomicType} (X Y : Rel L t) : LL := comp X (conv Y)
-- the positions of `(p q p r)` paired with equal elements: `(0 2)` share, `1` and `3` alone
private def pqpr : List (Int64 × Int64) := [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (3, 3)]

-- boolean, `bits`: `1010b`, whose positions pair `(0 2)` and `(1 3)`
private abbrev Bo := QAtomicType.boolean
private def bitsC : Nat × Enc := (4, .bits (ByteArray.mk #[0b0101]))
#guard ok (do let x ← lst Bo bitsC; pure (same x x)) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)] && X.n == 8
#guard ok (do pure (ran (← lst Bo bitsC))) fun X => seteq X.toList [(true, true), (false, false)] && X.n == 2
#guard ok (do let x ← lst Bo bitsC; pure (union x x)) fun X => X.n == 4
#guard ok (do let x ← lst Bo bitsC; pure (symDiv x x U4 U4)) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)]

-- symbol,`syms` and `enum`: `` `bc`a`bc`d `` in both, compared across the two
private abbrev Sy := QAtomicType.symbol
private def symsC : Nat × Enc := (4, .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0, 100, 0]) #[0, 3, 5, 8, 10])
private def enumC : Nat × Enc :=
  (4, .enum (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7] (Column.packIds (Column.idWidth #[0, 2, 5, 7]) 4 fun i => [1, 0, 1, 2][i]!))
#guard ok (lst Sy enumC) fun X => X.toList == [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
-- `Λ` of `{bc, a}` met in two orders, in two relations, and of syms against enum: one array, `[a bc]`, by
-- the strings' order, not by first appearance
#guard ok (do pure (comp (ofPairs [(0, 0), (0, 1)]) (← lst Sy symsC), comp (ofPairs [(0, 1), (0, 0)]) (← lst Sy enumC)))
  fun (X, Y) => crossOk X Y && crossOk Y X && lamOk X && lamOk Y &&
    (Λ(X).toList.map (·.2) : List (List String)) == [["a", "bc"]] && (Λ(Y).toList.map (·.2) : List (List String)) == [["a", "bc"]]
#guard ok (do pure (same (← lst Sy symsC) (← lst Sy enumC))) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do let x ← lst Sy enumC; pure (same x x)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do pure (union (← lst Sy symsC) (← lst Sy enumC))) fun X => X.n == 4 &&
  seteq X.toList [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard ok (do pure (symDiv (← lst Sy symsC) (← lst Sy enumC) U4 U4)) fun X => seteq X.toList pqpr
#guard ok (do pure <| leftDiv (← lst Sy enumC) (← lst Sy symsC) (← Arr.ofPart Sy 4 symsC "U") (← Arr.ofPart Sy 4 enumC "U")) fun X =>
  seteq X.toList [("bc", "bc"), ("a", "a"), ("d", "d")]
#guard ok (do pure (top (A := .atom Sy) (B := .atom Bo) (← Arr.ofPart Sy 4 enumC "U") (← Arr.ofPart Bo 4 bitsC "U"))) (·.n == 16)
#guard ok (lst Sy enumC) fun X => Λ(conv X).n == 3 && lamOk X && lamOk (conv X)
#guard ok (lst Sy symsC) fun X => lamOk X && lamOk (conv X)
#guard ok (lst Bo bitsC) fun X => lamOk X && lamOk (conv X) && Λ(conv X).n == 2

-- the lane each encoding codes at: bits a bit; a three-symbol enum, or three distinct longs whose range
-- outruns the rows (a grouping pass's ids), a 2-bit lane; foR and dense offsets a byte
private def laneOf (t : QAtomicType) (c : Nat × Enc) : Option Nat := match Arr.ofPart t c.1 c "laneOf" with | .ok x => some (codes t #v[⟨_, x⟩])[0].w | .error _ => none
#guard laneOf Bo bitsC == some 1 && laneOf Sy enumC == some 2 && laneOf Sy symsC == some 2
#guard laneOf L Lf.val.part == some 8 && laneOf L (longs (packLongs [5, 3, 5, 9])) == some 8 &&
  laneOf L (longs (packLongs [5, 3, 5, 1099511627776])) == some 2
-- a byte code below 3 beside a bit: `composeKey`'s `a·2 + b` at domain `3·2`, no grouping pass
#guard match pairCode false ⟨8, 4, 3, ByteArray.mk #[0, 1, 2, 1]⟩ ⟨1, 4, 2, ByteArray.mk #[0b0101]⟩ with
  | (c, none) => c.w == 4 && c.card == 6 && c.b == ByteArray.mk #[0x21, 0x25] | _ => false
-- the same pair at 2 and 1 bits: the 2-bit lane read by `eIds` where it lies
#guard match pairCode false ⟨2, 4, 3, Column.packIds 2 4 ([0, 1, 2, 1][·]!)⟩ ⟨1, 4, 2, ByteArray.mk #[0b0101]⟩ with
  | (c, none) => c.w == 4 && c.b == ByteArray.mk #[0x21, 0x25] | _ => false
-- a 2-bit code cut inside a byte, gathered, graded, grouped, run-started where it lies
private def c2 : Code := ⟨2, 6, 3, Column.packIds 2 6 ([2, 0, 1, 2, 0, 2][·]!)⟩
#guard (c2.cut #v[3, 3]).toArray.map (fun p => (List.range p.n).map (Column.idAt p.b 2)) == #[[2, 0, 1], [2, 0, 2]]
#guard (Code.cat (c2.cut #v[1, 5]).toArray).b == c2.b
#guard let g := c2.gather (packLongs [5, 1]); (List.range 2).map (Column.idAt g.b 2) == [2, 0]
#guard c2.grade == packLongs [1, 4, 2, 0, 3, 5]
#guard c2.groupIds.2 == packLongs [0, 1, 2]
#guard c2.find ⟨2, 2, 3, Column.packIds 2 2 ([1, 2][·]!)⟩ == packLongs [2, 0]
#guard c2.eqAt ⟨2, 6, 3, Column.packIds 2 6 ([2, 1, 1, 0, 0, 2][·]!)⟩ == packLongs [0, 2, 4, 5]
-- two foR parts of different bases, one negative: rebased (`foRShift`), equal elements equal codes
private def Lneg : LL := ⟨4, U4, Arr.mk (.foR (Coc.encode 8 (packLongs [9, -3, 5, 5])).1 (Coc.encode 8 (packLongs [9, -3, 5, 5])).2) (foRLongs_wf [9, -3, 5, 5])⟩
#guard seteq (comp Lneg (conv Lf)).toList
  (Lneg.toList.flatMap fun (i, x) => Lf.toList.filterMap fun (j, y) => if x == y then some (i, j) else none)

-- float through ALP: `1.5 2.25 1.5 0.1`, and the same as dense bytes
private abbrev Fl := QAtomicType.float
private def fs : List Float := [1.5, 2.25, 1.5, 0.1]
private def fb : ByteArray := packLongs (fs.map (·.toBits.toInt64))
private def fd : Nat × Enc := (fs.length, .bytes fb)
-- `alpOf` and not `Column.answer`, which keeps a column this short dense
private def alpC : Nat × Enc := ((Enc.alpOf Fl fd.1 fd.2).map (fd.1, ·)).getD fd
#guard alpC.2 matches .alp ..
#guard ok (do let x ← lst Fl alpC; pure (same x x)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do pure (same (← lst Fl alpC) (← lst Fl fd))) fun X => seteq X.toList pqpr && X.n == 6
-- a float element is its IEEE bits
#guard ok (do pure (union (← lst Fl alpC) (← lst Fl fd))) fun X => X.n == 4
#guard ok (do let x ← lst Fl alpC; pure (symDiv x x U4 U4)) fun X => seteq X.toList pqpr

-- a general list, `(1; (); 1; ,2)`, elements matched by identity
private def gs : Array QValue := #[.atom (.long 1), QValue.general #[], .atom (.long 1), QValue.general #[.atom (.long 2)]]
#guard ok (do let x ← lst .general (genCol gs).2.part; pure (same x x)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do let x ← lst .general (genCol gs).2.part; pure (union x x)) fun X => X.n == 4
#guard ok (do pure (dom (conv (← lst .general (genCol gs).2.part)))) (·.n == 3)
#guard ok (do let x ← lst .general (genCol gs).2.part; pure (symDiv x x U4 U4)) fun X => seteq X.toList pqpr
#guard match lstV .general (genCol gs).2.part with | .ok ⟨_ + 1, x⟩ => ok (uncons x) fun p => p.1.toList.length == 1 && p.2.toList.length == 3 | _ => false
#guard (zero (A := .general) (B := Sy)).n == 0

end Checks

#print axioms idU_holds
#print axioms convArr_holds
#print axioms outl_holds
#print axioms outr_holds
#print axioms le
#print axioms inter
#print axioms union
#print axioms zero
#print axioms top
#print axioms conv
#print axioms comp
#print axioms dom
#print axioms ran
#print axioms leftDiv
#print axioms rightDiv
#print axioms symDiv
#print axioms transpose
#print axioms setIds_size
#print axioms pair
#print axioms prod
#print axioms junc
#print axioms injConv
#print axioms mapVal
#print axioms foldGroups
#print axioms uncons
#print axioms thin
#print axioms setIds
#print axioms tuples
#print axioms codes
#print axioms entire
#print axioms simple
#print axioms injective
#print axioms surjective

/-! ## Laws: codes are faithful, and each operator means its relation -/

section Laws

open QLean.Verify (firstsOf)

/-- An `Arr`'s element `i` depends on its payload and on `i`'s value alone. -/
theorem Arr.get_congr {t : QAtomicType} {n m : Nat} {a : Arr t n} {b : Arr t m} (hc : a.part = b.part) {i : Fin n} {j : Fin m}
    (hij : i.1 = j.1) : a.get i = b.get j := by
  obtain ⟨rfl, he⟩ := Prod.mk.inj hc
  obtain ⟨v, hv⟩ := a; obtain ⟨w, hw⟩ := b
  cases v <;> try exact hv.elim
  cases w <;> try exact hw.elim
  obtain ⟨i, _⟩ := i; obtain ⟨j, _⟩ := j
  simp only [Arr.enc] at he hij; subst he hij; cases t <;> rfl

/-- Two `Arr`s over one part have one length: the part carries it. -/
theorem Arr.n_congr {t : QAtomicType} {n m : Nat} {a : Arr t n} {b : Arr t m} (hc : a.part = b.part) : n = m :=
  (Prod.mk.inj hc).1

theorem Arr.of_c {t : QAtomicType} {n : Nat} {c : Nat × Enc} {w : String} {a : Arr t n} (h : Arr.ofPart t n c w = .ok a) : a.part = c := by
  simp only [Arr.ofPart, Arr.of] at h; split at h
  · cases h; rename_i hw; obtain ⟨-, rfl, -⟩ := hw; rfl
  · cases h

/-- A part read at its own count `n` is its payload. -/
theorem _root_.LeetQ.Rel.Vals.ofParts_atom {t : QAtomicType} {n : Nat} {c : Part (.atom t)} (h : c.1 = n) :
    (Vals.ofParts (.atom t) n c).part = c.2.part := by
  obtain ⟨m, x⟩ := c; subst h; simp [Vals.ofParts, Vals.ofParts.ofArr, Arr.part]

/-- `ofCols` keys the answer by `kc`, its values by `vc` where the two counts agree. -/
theorem ofCols_ok {k v : QAtomicType} {kc : Part (.atom k)} {vc : Part (.atom v)} (h : vc.1 = kc.1) :
    (ofCols k v kc vc).key.part = kc.2.part ∧ (ofCols k v kc vc).val.part = vc.2.part :=
  ⟨Vals.ofParts_atom rfl, Vals.ofParts_atom h⟩

/-- The generic `R°`: `ofCols` of the two payloads, swapped. -/
theorem conv_cols_holds {R : Rel A B} (x : El A) (y : El B) :
    (ofCols B A (cols R).val (cols R).key).Holds y x ↔ R.Holds x y := by
  generalize hS : ofCols B A (cols R).val (cols R).key = S
  obtain ⟨n, K, v⟩ := R
  obtain ⟨hkc, hvc⟩ := hS ▸ ofCols_ok (k := B) (v := A) (kc := (cols ⟨n, K, v⟩).val) (vc := (cols ⟨n, K, v⟩).key) rfl
  obtain ⟨m, SK, SV⟩ := S
  simp only at hkc hvc
  have hn : m = n := Arr.n_congr (a := SK) (b := v) hkc
  subst hn
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, (Arr.get_congr hvc.symm rfl).trans h2, (Arr.get_congr hkc.symm rfl).trans h1⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, (Arr.get_congr hkc rfl).trans h2, (Arr.get_congr hvc rfl).trans h1⟩

/-- **`R°` swaps the pairs**: the two fields swap (`convArr_holds`). -/
theorem conv_holds {R : Rel A B} (x : El A) (y : El B) : (conv R).Holds y x ↔ R.Holds x y :=
  convArr_holds R.key R.val x y

/-- **`groupIds`' ids are faithful**: read at the width they are packed at, two rows' ids agree exactly
    when their keys do — at every lane `idWidthOf` answers (`idAt_packIds`), sub-byte ones too. The base
    of every code a grouping pass makes (`Code.ofIds`, `classSizes`, `codes`' last branch). -/
theorem groupIds_faithful (k : Scan.Kind) (n : USize) (b : ByteArray) {i j : Nat}
    (hi : i < min n.toNat (k.avail b)) (hj : j < min n.toNat (k.avail b)) :
    Column.idAt (Order.groupIds k n b).1
        (Column.idWidthOf (firstsOf (Order.keyAt k b) (min n.toNat (k.avail b))).length) i =
      Column.idAt (Order.groupIds k n b).1
        (Column.idWidthOf (firstsOf (Order.keyAt k b) (min n.toNat (k.avail b))).length) j ↔
    Order.keyAt k b i = Order.keyAt k b j := by
  have hm64 : min n.toNat (k.avail b) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Verify.usize_lt n)
  rw [(Verify.groupIds_spec k n b).1]
  generalize min n.toNat (k.avail b) = m at hi hj hm64 ⊢
  have hL : (firstsOf (Order.keyAt k b) m).length ≤ m := by
    simpa [firstsOf] using List.length_filter_le _ (List.range m)
  have hw : (firstsOf (Order.keyAt k b) m).length - 1 <
      2 ^ Column.idWidthOf (firstsOf (Order.keyAt k b) m).length := by
    have h2 := Verify.lt_widthFor ((firstsOf (Order.keyAt k b) m).length - 1)
    have h3 := Verify.widthFor_le ((firstsOf (Order.keyAt k b) m).length - 1) (by omega)
    unfold Column.idWidthOf
    generalize Column.widthFor ((firstsOf (Order.keyAt k b) m).length - 1) = w at h2 h3 ⊢
    refine Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) ?_)
    unfold Column.laneWidth; repeat' split
    all_goals omega
  have hb : ∀ l, l < m → Verify.groupOf (Order.keyAt k b) m l <
      2 ^ Column.idWidthOf (firstsOf (Order.keyAt k b) m).length := fun l hl => by
    have := Verify.groupOf_lt (g := Order.keyAt k b) hl; omega
  rw [Verify.idAt_packIds (w := Column.idWidthOf (firstsOf (Order.keyAt k b) m).length) (Verify.laneWidth_cases _) hi (hb i hi),
    Verify.idAt_packIds (w := Column.idWidthOf (firstsOf (Order.keyAt k b) m).length) (Verify.laneWidth_cases _) hj (hb j hj),
    Verify.groupOf_eq_iff hi (Verify.groupOf_lt hj), Verify.groupOf_get (g := Order.keyAt k b) hj]

/-- **A long column's grouping ids are faithful to its elements**: `groupIds .i64` over a dense long
    payload, as `groupIdsColumn` runs it, gives two rows one id exactly when they hold one long. -/
theorem groupIds_long_faithful {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b)
    (hm : m < USize.size) (i j : Fin m) :
    Column.idAt (Order.groupIds .i64 (b.size / 8).toUSize b).1
        (Column.idWidthOf (firstsOf (Order.keyAt .i64 b) m).length) i =
      Column.idAt (Order.groupIds .i64 (b.size / 8).toUSize b).1
        (Column.idWidthOf (firstsOf (Order.keyAt .i64 b) m).length) j ↔ x.get i = x.get j := by
  have hs := Arr.n_long_bytes x hc
  have hmin : min (b.size / 8).toUSize.toNat (Scan.Kind.avail .i64 b) = m := by
    have hu : m.toUSize.toNat = m := USize.toNat_ofNat_of_lt hm
    rw [hs, hu]; simp [Scan.Kind.avail, Scan.Kind.width, hs]
  have e := groupIds_faithful .i64 (b.size / 8).toUSize b (i := i.1) (j := j.1) (by omega) (by omega)
  rw [hmin] at e
  rw [e, Verify.keyAt_eq_iff (by simp) b i.1 j.1, Arr.get_long_bytes x hc, Arr.get_long_bytes x hc]
  exact ⟨fun h => by simp only [Scan.Kind.width] at h; rw [h], fun h => toInt64_inj h⟩

/-- **Run starts group a column whose equal elements are contiguous.** `r 0 < … < r m = n` lists every
    run start of `key` below `n` and nothing else; then the run keys `key (r j)` are one-to-one and
    `key s = key (r j) ⟺ r j ≤ s < r (j+1)`. Encoding-free: each lane's kernel answers these hypotheses. -/
theorem runs_group {α : Type} {n m : Nat} (key : Nat → α) (r : Nat → Nat) (hlast : r m = n)
    (hasc : ∀ i j, i < j → j ≤ m → r i < r j) (h0 : 0 < n → r 0 = 0)
    (hstart : ∀ j, j < m → r j = 0 ∨ key (r j) ≠ key (r j - 1))
    (hall : ∀ s, s < n → (s = 0 ∨ key s ≠ key (s - 1)) → ∃ j, j < m ∧ r j = s)
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < n → key s = key u → key t = key s) :
    (∀ j j', j < m → j' < m → key (r j) = key (r j') → j = j') ∧
    (∀ s j, s < n → j < m → (key s = key (r j) ↔ r j ≤ s ∧ s < r (j + 1))) := by
  have hle : ∀ i j, i ≤ j → j ≤ m → r i ≤ r j := fun i j h hj => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact Nat.le_of_lt (hasc i j h hj)
    · exact Nat.le_refl _
  -- inside a run, every row holds its start's element
  have hin : ∀ j, j < m → ∀ s, r j ≤ s → s < r (j + 1) → key s = key (r j) := by
    intro j hj s
    induction s with
    | zero => intro h _; rw [Nat.le_zero.1 h]
    | succ s ih =>
      intro h1 h2
      rcases Nat.lt_or_eq_of_le h1 with h1 | h1
      · have hn : s + 1 < n := hlast ▸ Nat.lt_of_lt_of_le h2 (hle (j + 1) m hj (Nat.le_refl m))
        by_cases hk : key (s + 1) = key s
        · exact hk.trans (ih (Nat.le_of_lt_succ h1) (by omega))
        · exfalso
          obtain ⟨j', hj', e⟩ := hall (s + 1) hn (.inr hk)
          rcases Nat.lt_or_ge j' (j + 1) with h | h
          · have := hle j' j (by omega) (by omega); omega
          · have := hle (j + 1) j' h (by omega); omega
      · rw [← h1]
  have hcov : ∀ s, s < n → ∃ j, j < m ∧ r j ≤ s ∧ s < r (j + 1) := by
    intro s
    induction s with
    | zero =>
      intro hn
      have hm : 0 < m := Nat.pos_of_ne_zero fun e => by subst e; have := h0 hn; omega
      exact ⟨0, hm, Nat.le_of_eq (h0 hn), by have := hasc 0 (0 + 1) (by omega) hm; have := h0 hn; omega⟩
    | succ s ih =>
      intro hn
      obtain ⟨j, hj, h1, h2⟩ := ih (by omega)
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h2) with h | h
      · exact ⟨j, hj, by omega, h⟩
      · have hj1 : j + 1 < m := by
          rcases Nat.lt_or_ge (j + 1) m with h' | h'
          · exact h'
          · have : j + 1 = m := by omega
            subst this; omega
        exact ⟨j + 1, hj1, by omega, by have := hasc (j + 1) (j + 1 + 1) (by omega) hj1; omega⟩
  have hinj : ∀ j j', j < j' → j' < m → key (r j) ≠ key (r j') := by
    intro j j' hjj hj' e
    have hlt := hasc j j' hjj (by omega)
    have hn : r j' < n := hlast ▸ hasc j' m hj' (Nat.le_refl _)
    rcases hstart j' hj' with h | h
    · omega
    · exact h ((hcont (r j) (r j' - 1) (r j') (by omega) (by omega) hn e).trans e).symm
  refine ⟨fun j j' hj hj' e => ?_, fun s j hs hj => ⟨fun e => ?_, fun ⟨h1, h2⟩ => hin j hj s h1 h2⟩⟩
  · rcases Nat.lt_trichotomy j j' with h | h | h
    · exact absurd e (hinj j j' h hj')
    · exact h
    · exact absurd e.symm (hinj j' j h hj)
  · obtain ⟨j', hj', h1, h2⟩ := hcov s hs
    have e' := (hin j' hj' s h1 h2).symm.trans e
    rcases Nat.lt_trichotomy j' j with h | h | h
    · exact absurd e' (hinj j' j h hj)
    · subst h; exact ⟨h1, h2⟩
    · exact absurd e'.symm (hinj j j' h hj')

/-- **`runStarts` at a byte lane groups a column its key is faithful to.** `key` agrees with the lane's
    search key exactly where the elements do, and its equal elements are contiguous; then the starts `r`
    the kernel writes (`runStarts_spec`), read as naturals, end at the count, ascend, name one-to-one
    keys and cut the column into its runs (`runs_group`). -/
theorem runStarts_group {α : Type} (w : USize) (float : Bool) (hay : ByteArray) (h63 : hay.size / w.toNat < 2 ^ 63)
    (key : Nat → α)
    (hk : ∀ i j, i < hay.size / w.toNat → j < hay.size / w.toNat →
      (key i = key j ↔ Kernel.key w.toNat float hay i = Kernel.key w.toNat float hay j))
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < hay.size / w.toNat → key s = key u → key t = key s) :
    ∃ m, (Kernel.runStarts w float hay).size = 8 * (m + 1) ∧
      (∀ j, j ≤ m → (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt =
        (((Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt.toNat : Nat) : Int)) ∧
      (Column.bitsAt (Kernel.runStarts w float hay) (8 * m) 8).toInt64.toInt.toNat = hay.size / w.toNat ∧
      (∀ i j, i < j → j ≤ m → (Column.bitsAt (Kernel.runStarts w float hay) (8 * i) 8).toInt64.toInt.toNat <
        (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt.toNat) ∧
      (∀ j j', j < m → j' < m →
        key (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt.toNat =
          key (Column.bitsAt (Kernel.runStarts w float hay) (8 * j') 8).toInt64.toInt.toNat → j = j') ∧
      (∀ s j, s < hay.size / w.toNat → j < m →
        (key s = key (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt.toNat ↔
          (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt.toNat ≤ s ∧
            s < (Column.bitsAt (Kernel.runStarts w float hay) (8 * (j + 1)) 8).toInt64.toInt.toNat)) := by
  obtain ⟨m, hsz, hlast, hasc, h0, hst, hall⟩ := Verify.runStarts_spec w float hay h63
  generalize hay.size / w.toNat = n at h63 hk hcont hlast h0 hst hall
  -- `R j`, the start the kernel wrote at `j`, as an integer
  let R : Nat → Int := fun j => (Column.bitsAt (Kernel.runStarts w float hay) (8 * j) 8).toInt64.toInt
  change ∀ i j, i < j → j ≤ m → R i < R j at hasc
  change R m = n at hlast
  change 0 < n → 0 < m ∧ R 0 = 0 at h0
  change ∀ j, j < m → ∃ r : Nat, R j = r ∧ _ at hst
  change ∀ r, r < n → _ → ∃ j, j < m ∧ R j = r at hall
  change ∃ m, _ ∧ (∀ j, j ≤ m → R j = ((R j).toNat : Int)) ∧ (R m).toNat = n ∧
    (∀ i j, i < j → j ≤ m → (R i).toNat < (R j).toNat) ∧
    (∀ j j', j < m → j' < m → key (R j).toNat = key (R j').toNat → j = j') ∧
    (∀ s j, s < n → j < m → (key s = key (R j).toNat ↔ (R j).toNat ≤ s ∧ s < (R (j + 1)).toNat))
  -- every start is a natural below `n`, the last entry `n` itself
  have hnn : ∀ j, j ≤ m → R j = ((R j).toNat : Int) := fun j hj => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · obtain ⟨r, e, -⟩ := hst j h; rw [e]; rfl
    · rw [hlast]; rfl
  have hlt : ∀ j, j < m → (R j).toNat < n ∧ ((R j).toNat = 0 ∨ Kernel.key w.toNat float hay (R j).toNat ≠
      Kernel.key w.toNat float hay ((R j).toNat - 1)) := fun j hj => by
    obtain ⟨r, e, h1, h2⟩ := hst j hj; rw [e]; exact ⟨h1, h2⟩
  have G := runs_group key (fun j => (R j).toNat) (by dsimp only; rw [hlast]; rfl)
    (fun i j hij hj => by dsimp only; have := hasc i j hij hj; rw [hnn i (by omega), hnn j hj] at this; omega)
    (fun hn => by dsimp only; rw [(h0 hn).2]; rfl)
    (fun j hj => (hlt j hj).2.imp id fun h e => h ((hk _ _ (hlt j hj).1 (by have := (hlt j hj).1; omega)).1 e))
    (fun s hs h => by
      obtain ⟨j, hj, e⟩ := hall s hs (h.imp id fun h e => h ((hk _ _ hs (by omega)).2 e))
      exact ⟨j, hj, by dsimp only; rw [e]; rfl⟩)
    hcont
  exact ⟨m, hsz, hnn, by rw [hlast]; rfl,
    fun i j hij hj => by have := hasc i j hij hj; rw [hnn i (by omega), hnn j hj] at this; omega, G.1, G.2⟩


/-- **Sorted by a key faithful to the elements, equal elements are contiguous**: `κ` ascends along the
    rows and agrees exactly where `x` does, so a row between two equal elements holds that element. The
    `hcont` of `runs_group`, from any stable sort (`grade_mono`). -/
theorem sorted_contig {α : Type} {n : Nat} (x : Nat → α) (κ : Nat → UInt64)
    (hmono : ∀ s t, s ≤ t → t < n → κ s ≤ κ t) (hk : ∀ s t, s < n → t < n → (κ s = κ t ↔ x s = x t)) :
    ∀ s t u, s ≤ t → t ≤ u → u < n → x s = x u → x t = x s := fun s t u h1 h2 hu e => by
  have a := hmono s t h1 (by omega); have b := hmono t u h2 hu
  have c := (hk s u (by omega) hu).2 e
  rw [← c] at b
  exact ((hk s t (by omega) (by omega)).1 (UInt64.le_antisymm a b)).symm

/-- **`grade` ascends its key along its answer**: row `s` of the grade has a key no greater than row `t ≥ s`
    has (`grade_spec`, ascending). -/
theorem grade_mono (k : Scan.Kind) (n : USize) (b : ByteArray) {s t : Nat} (hst : s ≤ t)
    (ht : t < (Verify.ids (Order.grade k false n b)).length) :
    Order.keyAt k b (Verify.ids (Order.grade k false n b))[s] ≤
      Order.keyAt k b (Verify.ids (Order.grade k false n b))[t] := by
  rcases Nat.lt_or_eq_of_le hst with h | rfl
  · exact (List.pairwise_iff_getElem.1 (Verify.grade_spec k false n b).2 s t (by omega) ht h).1
  · exact UInt64.le_refl _


/-- **At an integral byte lane the search key and the sort key agree together**: both are the stored
    bits (`keyAt_eq_iff`), so `runStarts`' runs and `grade`'s order see one equality. -/
theorem key_eq_iff_keyAt {k : Scan.Kind} (hk : k = .u8 ∨ k = .c8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)
    (b : ByteArray) (i j : Nat) :
    Kernel.key k.width false b i = Kernel.key k.width false b j ↔ Order.keyAt k b i = Order.keyAt k b j := by
  rw [Verify.keyAt_eq_iff hk]
  simp only [Kernel.key, Kernel.normalise, Bool.not_false, if_true]


/-- **`overBytes lesser` is a lower bound and `greater` an upper bound of every element that is not the
    null**: the fold's step is `min`/`max`, and a null is skipped. `rangeOffsets`' `lo`/`hi`. -/
theorem overBytes_bounds (cls : UInt8) (nul : Int64) (b : ByteArray) {i : Nat} (hi : i < b.size / Ew.width cls)
    (hx : Ew.signed cls (Ew.elem cls b i) ≠ nul) :
    overBytes .lesser cls nul b ≤ Ew.signed cls (Ew.elem cls b i) ∧
      Ew.signed cls (Ew.elem cls b i) ≤ overBytes .greater cls nul b := by
  generalize hx' : (fun i => Ew.signed cls (Ew.elem cls b i)) = x at hx
  have ex : ∀ i, Ew.signed cls (Ew.elem cls b i) = x i := fun i => by rw [← hx']
  simp only [ex] at hx ⊢
  have mem : i ∈ List.range (b.size / Ew.width cls) := List.mem_range.2 hi
  unfold overBytes; simp only [ex]
  generalize List.range (b.size / Ew.width cls) = l at mem
  constructor
  · generalize Coc.Over.denseSeed .lesser cls nul = acc
    induction l generalizing acc with
    | nil => cases mem
    | cons a l ih =>
      simp only [List.foldl_cons]
      have lo : ∀ (l : List Nat) (acc : Int64), l.foldl (fun acc i => if (!Coc.Over.boolCast .lesser && x i == nul) = true then acc
          else Coc.Over.step .lesser acc (x i)) acc ≤ acc := fun l => by
        induction l with
        | nil => exact fun _ => Int64.le_refl _
        | cons c l ihl =>
          intro acc; simp only [List.foldl_cons]
          refine Int64.le_trans (ihl _) ?_
          simp only [Coc.Over.boolCast, Coc.Over.step]; split
          · exact Int64.le_refl _
          · split
            · exact Int64.le_refl _
            · rename_i h; exact Int64.le_iff_toInt_le.2 (by have := mt Int64.lt_iff_toInt_lt.2 h; omega)
      rcases List.mem_cons.1 mem with rfl | m
      · refine Int64.le_trans (lo _ _) ?_
        simp only [Coc.Over.boolCast, Coc.Over.step, beq_iff_eq, hx, Bool.not_false, Bool.true_and, if_false]; split
        next h => exact Int64.le_iff_toInt_le.2 (by have := Int64.lt_iff_toInt_lt.1 h; omega)
        next => exact Int64.le_refl _
      · exact ih m _
  · generalize Coc.Over.denseSeed .greater cls nul = acc
    induction l generalizing acc with
    | nil => cases mem
    | cons a l ih =>
      simp only [List.foldl_cons]
      have up : ∀ (l : List Nat) (acc : Int64), acc ≤ l.foldl (fun acc i => if (!Coc.Over.boolCast .greater && x i == nul) = true then acc
          else Coc.Over.step .greater acc (x i)) acc := fun l => by
        induction l with
        | nil => exact fun _ => Int64.le_refl _
        | cons c l ihl =>
          intro acc; simp only [List.foldl_cons]
          refine Int64.le_trans ?_ (ihl _)
          simp only [Coc.Over.boolCast, Coc.Over.step]; split
          · exact Int64.le_refl _
          · split
            · exact Int64.le_refl _
            · rename_i h; exact Int64.le_iff_toInt_le.2 (by have := mt Int64.lt_iff_toInt_lt.2 h; omega)
      rcases List.mem_cons.1 mem with rfl | m
      · refine Int64.le_trans ?_ (up _ _)
        simp only [Coc.Over.boolCast, Coc.Over.step, beq_iff_eq, hx, Bool.not_false, Bool.true_and, if_false]; split
        next h => exact Int64.le_iff_toInt_le.2 (by have := Int64.lt_iff_toInt_lt.1 h; omega)
        next => exact Int64.le_refl _
      · exact ih m _


/-- **`rangeOffsets`' shift, element by element**: `Ew.val add` against the one long `c` answers
    `x + c` at every element, and the null where `x` or `c` is one (`elemsW_val`, `intStep`). -/
theorem shift_elem (b : ByteArray) (c : Int64) {n : Nat} (hn : n < USize.size) {i : Nat} (hi : i < n) :
    (Column.bitsAt (Kernel.Ew.val Ew.add Ew.i64 Ew.va nul b (one c.toUInt64) n.toUSize) (i * 8) 8).toInt64 =
      if (Column.bitsAt b (i * 8) 8).toInt64 = nul ∨ c = nul then nul else (Column.bitsAt b (i * 8) 8).toInt64 + c := by
  have hu : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have e := congrArg (fun l => l[i]?) (Verify.elemsW_val Ew.add Ew.i64 Ew.va nul b (one c.toUInt64) n.toUSize)
  have hs := Verify.val_size8 Ew.add Ew.va nul b (one c.toUInt64) n.toUSize
  have hw : Ew.width Ew.i64 = 8 := by decide
  have ho : Ew.elem Ew.i64 (one c.toUInt64) 0 = c.toUInt64 := by
    simp only [Ew.elem, hw, Nat.zero_mul]; exact Find.bitsAt_one c.toUInt64
  simp only [Verify.elemsW, hw, List.getElem?_map] at e
  rw [← hs, hu, List.getElem?_range hi] at e
  simp only [Option.map_some, Option.some.injEq, Ew.shapeIdx] at e
  rw [e]
  simp only [show (Ew.va == Ew.vv) = false from rfl, show (Ew.va == Ew.va) = true from rfl, if_true,
    Bool.false_eq_true, if_false, ho]
  have hm : ∀ v : UInt64, UInt64.ofNat (v.toNat % 2 ^ (8 * 8)) = v := fun v => by
    rw [Nat.mod_eq_of_lt (by simpa using v.toNat_lt)]; exact UInt64.ofNat_toNat
  simp only [Ew.valStep, Ew.intStep, Ew.signed, Ew.elem, hw, hm,
    show (Ew.i64 == Ew.f64) = false from rfl, show (Ew.i64 == Ew.f32) = false from rfl,
    show (Ew.i64 == Ew.u8) = false from rfl, show (Ew.i64 == Ew.i16) = false from rfl,
    show (Ew.i64 == Ew.i32) = false from rfl, show (Ew.add == Ew.add) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  by_cases hx : (Column.bitsAt b (i * 8) 8).toInt64 = nul <;> by_cases hc : c = nul <;> simp [hx, hc]


/-- **`rangeOffsets`' codes are faithful**: offsets `x − base` packed by `enumIds` at a byte lane, the null
    at `card − 1`, agree exactly where the elements do, when every element that is not the null lies in
    `[base, base + card − 2]` (`overBytes_bounds`) and the kernel reported every row in range. -/
theorem offsets_faithful {n card w : Nat} {b' : ByteArray} (x : Nat → Int64) (base : Int64)
    (hn : n < USize.size) (hcard : card < USize.size) (hc0 : 1 ≤ card) (h63 : card ≤ 2 ^ 63)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (hd : card ≤ 2 ^ w) (hb : base ≠ nul)
    (hok : (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b').2 = n.toUSize)
    (hv : ∀ i, i < n → (Column.bitsAt b' (i * 8) 8).toInt64 = if x i = nul then nul else x i + -base)
    (hr : ∀ i, i < n → x i ≠ nul → base.toInt ≤ (x i).toInt ∧ (x i).toInt - base.toInt + 2 ≤ card)
    {i j : Nat} (hi : i < n) (hj : j < n) :
    Column.idAt (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b').1 w i =
      Column.idAt (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b').1 w j ↔ x i = x j := by
  have hwu : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt'
    (Nat.lt_of_lt_of_le (by rcases hw with rfl | rfl | rfl | rfl <;> decide : w < 2 ^ 32) USize.le_size)
  have hnu : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hcu : card.toUSize.toNat = card := USize.toNat_ofNat_of_lt' hcard
  have hc1 : (card - 1).toUSize.toNat = card - 1 := USize.toNat_ofNat_of_lt' (by omega)
  have code : ∀ i, i < n → Column.idAt (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b').1 w i =
      if x i = nul then card - 1 else ((x i).toInt - base.toInt).toNat := fun i hi => by
    have e := Verify.enumIds_idAt n.toUSize card.toUSize (card - 1).toUSize w.toUSize b'
      (by rw [hwu]; rcases hw with rfl | rfl | rfl | rfl <;> simp) (by rw [hcu, hwu]; exact hd)
      (by rw [hc1, hwu]; omega) hok (i := i) (by rw [hnu]; exact hi)
    rw [hwu] at e; rw [e, hv i hi, hc1]
    by_cases hx : x i = nul
    · simp only [hx, if_true, nul]
    · obtain ⟨r1, r2⟩ := hr i hi hx
      have hbl := Int64.le_toInt base; have hbu := Int64.toInt_lt base
      have hxl := Int64.le_toInt (x i); have hxu := Int64.toInt_lt (x i)
      have hbn : base.toInt ≠ -2 ^ 63 := fun h => hb (Int64.toInt_inj.1 (by rw [h]; decide))
      have hs : (x i + -base).toInt = (x i).toInt - base.toInt := by
        rw [Int64.toInt_add, Int64.toInt_neg]
        simp only [Int.bmod]; split <;> split <;> omega
      have hne : x i + -base ≠ nul := fun h => by
        have := congrArg Int64.toInt h; rw [hs] at this
        have : nul.toInt = -2 ^ 63 := by decide
        omega
      simp only [hx, if_false]
      rw [if_neg (by simpa [nul] using hne), hs]
  rw [code i hi, code j hj]
  by_cases hx : x i = nul <;> by_cases hy : x j = nul
  · simp only [hx, hy, if_true]
  · simp only [hx, hy, if_true, if_false]
    have := hr j hj hy
    exact ⟨fun h => by omega, fun h => absurd h.symm hy⟩
  · simp only [hx, hy, if_true, if_false]
    have := hr i hi hx
    exact ⟨fun h => by omega, fun h => h.elim⟩
  · simp only [hx, hy, if_false]
    have := hr i hi hx; have := hr j hj hy
    exact ⟨fun h => Int64.toInt_inj.1 (by omega), fun h => by rw [h]⟩

end Laws

#print axioms conv_holds
#print axioms groupIds_faithful
#print axioms groupIds_long_faithful
#print axioms runs_group
#print axioms runStarts_group
#print axioms sorted_contig
#print axioms grade_mono
#print axioms key_eq_iff_keyAt
#print axioms overBytes_bounds
#print axioms shift_elem
#print axioms offsets_faithful

end LeetQ.Rel.Alg
