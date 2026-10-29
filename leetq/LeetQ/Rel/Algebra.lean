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

def nul : Int64 := Int64.minValue

def add (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul a b (len a).toUSize
def sub (a b : ByteArray) : ByteArray := Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul a b (len a).toUSize
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
def cut (c : Code) (ns : Array Nat) : Array Code :=
  if ns.size == 1 then #[c] else
  let part (o m : Nat) : ByteArray :=
    if m == 0 then .empty
    else if c.w % 8 == 0 then c.b.extract (c.w / 8 * o) (c.w / 8 * (o + m))
    else if c.w == 1 then cycleBits c.n.toUSize o.toUSize m.toUSize c.b
    else cycleIds c.n.toUSize o.toUSize m.toUSize c.w.toUSize c.b
  (ns.foldl (init := (#[], 0)) fun (acc, o) m => (acc.push ⟨c.w, m, c.card, part o m⟩, o + m)).1

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

/-- A general list's boxed elements: its `gen` column, which is the only one `Arr .general` admits. -/
def gens (c : Nat × Enc) : Except String (Array QValue) :=
  match c.2 with
  | .gen xs => pure xs
  | _ => throw "a general list's payload is not a gen column"

/-- A general list's column over `xs`. -/
def genCol (xs : Array QValue) : Nat × Enc := (xs.size, .gen xs)

/-- `x@i` for an in-range long payload `i`: `gatherColumn`, which answers every column encoding. A
    general list is picked by position, which is all qlean's own `@` does there (`pickAt`, private). -/
def pick (t : QAtomicType) (c : Nat × Enc) (i : ByteArray) : Except String (Nat × Enc) :=
  match t with
  | .general => do let xs ← gens c; pure (genCol ((longRows i).map fun p => xs[p]?.getD (QValue.general #[])))
  | a => match gatherColumn a c.1 c.2 (len i) (.bytes i) with
    | some e => pure (len i, e)
    | none => throw s!"gatherColumn declines a column of type {a.code} in this encoding"

/-- `raze` of payloads of one type: `razeColumn`, which interns a symbol part to meet an interned one
    and decodes an encoded part to meet a dense one. A general list is `Array.append`. -/
def raze (t : QAtomicType) (cs : Array (Nat × Enc)) : Except String (Nat × Enc) :=
  match t with
  | .general => do pure (genCol (← cs.foldlM (fun xs c => do pure (xs ++ (← gens c))) #[]))
  | a => if h : cs.size = 1 then pure cs[0] else match razeColumn a cs with
    | some (.vector _ m e _) => pure (m, e)
    | _ => throw s!"razeColumn declines {cs.size} columns of type {a.code}"

/-- No element of `t`: `Enc.ofAtoms` of nothing, which picks the type's own constructor. -/
def empty (t : QAtomicType) : Except String (Nat × Enc) :=
  if h : t = .general then pure (genCol #[]) else match Enc.ofAtoms t #[] h with
    | some e => pure (0, e)
    | none => throw s!"Enc.ofAtoms has no empty payload of type {t.code}"


/-- `foR` and dense parts of a long type as offsets from their joint least element, at the width of the
    joint range: `overFoR` reads a `foR` part's bounds off the block metadata, `overBytes` a dense
    part's in one pass; `foRShift`/`Ew.val add` rebase a part and `enumIdsFoR`/`enumIds` pack its
    offsets, a null to the last code — no hashing, no `foR` element decoded. Order-preserving. `none`
    where a part is neither, or the range is wider than a grouping pass's ids over `total` rows would be.
    A dense part is here because its first-appearance ids (`groupIdsColumn`) cost a table probe a row
    (measured: `ej` of two million-wide dense key columns, 1e6 rows, the codes 16.7 ms). -/
def rangeOffsets (a : QAtomicType) (cs : Array (Nat × Enc)) (total : Nat) : Except String (Option (Array Code)) := do
  unless orderKind a == some .i64 && Column.encodes a do return none
  let bound (op : Coc.Over) (c : Nat × Enc) : Option Int64 := match c.2 with
    | .bytes b => some (overBytes op Ew.i64 nul b)
    | .foR .. => overFoR op a c.1 c.2
    | _ => none
  let some los := cs.mapM (bound .lesser) | return none
  let some his := cs.mapM (bound .greater) | return none
  let lo := los.foldl min Int64.maxValue
  let hi := his.foldl max (Int64.minValue + 1)
  if lo == nul || hi < lo then return none
  -- the codes `0 … hi-base`, then one for a null (`enumIdsFoR`'s `nullId`)
  let span (base : Int64) : Nat := (hi.toInt - base.toInt + 2).toNat
  let k := codeKind (span lo)
  unless k.width ≤ (codeKind total).width do return none
  -- values already at `0` and up that fit the same width are their own offsets: no `foRShift` pass
  let base := if 0 ≤ lo && (codeKind (span 0)).width == k.width then 0 else lo
  let card := span base
  let w := 8 * k.width
  let packed (kernel : String) (n : Nat) : ByteArray × USize → Except String Code
    | (ids, bad) => if bad.toNat != n then throw s!"{kernel}: the offset at {bad} lies outside 0..{card}"
      else pure ⟨w, n, card, ids⟩
  let part (c : Nat × Enc) : Option (Except String Code) := let n := c.1; match c.2 with
    | .foR m p => (if base == 0 then some (m, p) else Ew.foRShift false (-base) m p n.toUSize).map fun (m, p) =>
        packed "enumIdsFoR" n (enumIdsFoR n.toUSize card.toUSize (card - 1).toUSize w.toUSize m p)
    | .bytes b =>
      let n := b.size / 8
      let b := if base == 0 then b else Kernel.Ew.val Ew.add Ew.i64 Ew.va nul b (one (-base).toUInt64) n.toUSize
      some (packed "enumIds" n (enumIds n.toUSize card.toUSize (card - 1).toUSize w.toUSize b))
    | _ => none
  let some rs := cs.mapM part | return none
  some <$> rs.mapM id

/-- Joint codes of the parts `cs`, one `Code` per part, in one code space:
    - `bits`: each part is its own code, a bit wide, order-preserving;
    - `foR` or dense of a long type: the offsets from the joint least element (`rangeOffsets`), order-preserving;
    - `enum`, and `syms` interned by `razeColumn`/`Column.intern`: the joint dictionary's ids at their lane;
    - anything else: one coding pass over the `raze` (`groupIdsColumn`: ids by first appearance, at any
      encoding), read at the width they are packed at (`Code.ofIds`). A general list is `findList` of
      the join against itself, its positions packed. -/
def codes (t : QAtomicType) (cs : Array (Nat × Enc)) : Except String (Array Code) :=
  match t with
  | .general => do
    let all ← gens (← raze .general cs)
    pure ((pack all.size (findList all all)).cut (cs.map (·.1)))
  | a => do
    if let some bs := cs.mapM (fun c => match c.2 with | .bits b => some (⟨1, c.1, 2, b⟩ : Code) | _ => none) then
      return bs
    let ns := cs.map (·.1)
    let total := ns.foldl (· + ·) 0
    if let some os ← rangeOffsets a cs total then return os
    let (an, ae) ← raze a cs
    let ae := Column.intern ae
    if let .enum _ dof ids := ae then return (Code.ofLane (Column.idWidth dof) an (dof.size - 1) ids).cut ns
    let some (gid, fs) := groupIdsColumn a an ae
      | throw s!"groupIdsColumn declines a column of type {a.code} in this encoding"
    pure ((Code.ofIds (len fs) total gid).cut ns)

/-- The one code of a single part. -/
def single (cs : Array Code) : Except String Code :=
  if h : cs.size = 1 then pure cs[0] else throw s!"{cs.size} code parts where one was coded"

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

/-- A relation's two payloads. -/
structure Cols (k v : QAtomicType) where
  n : Nat
  key : Nat × Enc
  val : Nat × Enc

def cols {k v : QAtomicType} (R : Rel k v) : Except String (Cols k v) := pure ⟨R.n, R.key.part, R.val.part⟩

/-- The rows of `d` at the index column `i`. -/
def Cols.rows {k v : QAtomicType} (d : Cols k v) (i : ByteArray) : Except String (Cols k v) := do
  pure ⟨len i, ← pick k d.key i, ← pick v d.val i⟩

/-- Two payloads as a relation keyed by an explicit column. -/
def ofCols (k v : QAtomicType) (kc : Nat × Enc) (vc : Nat × Enc) : Except String (Rel k v) := do
  let n := kc.1
  pure ⟨n, ← Arr.ofPart k n kc "ofCols", ← Arr.ofPart v n vc "ofCols"⟩

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

/-- `|R|` of tuples: `cols[j]` is column `j`'s codes per part (`codes`); the columns are folded left by
    `pairCode`; one code per part. One column is its own codes. -/
def tuples (cols : Array (Array Code)) : Except String (Array Code) := do
  let some c0 := cols[0]? | throw "tuples: no column"
  if cols.size == 1 then return c0
  pure ((← tupleCode false (cols.map Code.cat)).1.cut (c0.map (·.n)))
where
  /-- The fold of the columns `all` by `pairCode`, the last step told whether its answer is grouped
      next (`classes`), and the classes when that step grouped. -/
  tupleCode (classes : Bool) (all : Array Code) : Except String (Code × Option (ByteArray × ByteArray)) := do
    let some c0 := all[0]? | throw "tuples: no column"
    let some cl := all.back? | throw "tuples: no column"
    if all.size == 1 then return (c0, none)
    pure (pairCode classes ((all.extract 1 (all.size - 1)).foldl (fun a c => (pairCode false a c).1) c0) cl)
  /-- The classes of the tuples of the columns `all`, as `groupIds` answers them; the last fold step's
      own when it grouped, so a caller wanting the classes groups nothing twice. -/
  tupleIds (all : Array Code) : Except String (ByteArray × ByteArray) := do
    match ← tupleCode true all with
    | (_, some r) => pure r
    | (c, none) => pure c.groupIds

/-- `|R|` of several relations of one type in one code space, one code per relation. -/
def pairs {k v : QAtomicType} (ds : Array (Cols k v)) : Except String (Array Code) := do
  tuples #[← codes k (ds.map (·.key)), ← codes v (ds.map (·.val))]

/-- `R` with each pair once: the first row of each class of `|R|`. -/
def Cols.nub {k v : QAtomicType} (d : Cols k v) : Except String (Cols k v) := do
  d.rows (← tuples.tupleIds #[← single (← codes k #[d.key]), ← single (← codes v #[d.val])]).2

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

/-- `anti(x, y)`: the positions of `x` whose code is not in `y` — `member`, `Ew.notBits`, `whereBits`. -/
def anti (x y : Code) : ByteArray := whereBits x.n.toUSize (Ew.notBits x.n (x.member y))

/-- Dense rank of a payload in value order: `binBytes` into its sorted distinct values. -/
def drank (k : Scan.Kind) (b : ByteArray) : ByteArray :=
  let n := (b.size / k.width).toUSize
  let d := Order.distinct k n b
  binBytes k.width.toUSize (isFloat k) true false (Order.sortValues k false (d.size / k.width).toUSize d) b

/-- `a + x` for the long `x`. -/
def addc (a : ByteArray) (x : Nat) : ByteArray := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul a (one x.toUInt64) (len a).toUSize

/-- The rows of a code column `c` cut into one segment per distinct code: the permutation `p` that
    makes each code's rows contiguous (`grade` of its `groupIds`), the `g + 1` offsets of the
    segments in that order (`runStarts`), and each segment's first row in `c`. -/
def segments (c : Code) : ByteArray × ByteArray × ByteArray :=
  let (gid, firsts) := c.groupIds
  let g := Code.ofIds (len firsts) c.n gid
  let p := g.grade
  (p, (g.gather p).runStarts, firsts)

/-- Set ids: segment `j` of the codes `vc` is `vc[o[j] .. o[j+1])`, and segments holding equal SETS
    get equal ids, numbered by first occurrence. Each segment is sorted and its repeats dropped —
    `grade` on (segment, code), `groupIdsPair` of the sorted pairs, whose ids rise by one at each
    new pair, so the id at a segment's first row is the kept rows before it — then `rankSlices` at the
    code's own width, which compares the normalised segments as sequences. -/
def setIds (vc : Code) (o : ByteArray) : Except String ByteArray := do
  let n := vc.n
  if o.size < 8 then throw "setIds: the offsets hold no terminator"
  let seg := groupOf o n
  let p := gradeBy n #[Code.ofLongs seg, vc]
  let (q, fs) := match vc.kind with
    | some k => Order.groupIdsPair .i64 k n.toUSize (gather 8 seg p) (vc.gather p).b
    | none => Order.groupIdsPairIds 64 vc.w.toUSize n.toUSize (gather 8 seg p) (vc.gather p).b
  let ids := Order.rankSlices vc.w.toUSize (vc.gather (gather 8 p fs)).b
    (gather 8 (concatBytes #[groupLongs n (q, fs), one (len fs).toUInt64]) o)
  if len ids == len o - 1 then pure ids
  else throw s!"rankSlices declines the {len o - 1} normalised segments of {len fs} codes"

/-- `setIds` of a stored family (one boxed set of `v` per key): one id per set, equal sets one id. -/
def setId {k : QAtomicType} (v : QAtomicType) (G : Rel k .general) : Except String ByteArray := do
  let P ← Parted.ofBoxes v G.val
  let some ob := longBytes (P.g + 1) P.o.enc | throw "setId: the offsets have no dense payload"
  setIds (← single (← codes v #[P.val.part])) ob

/-- `thin(Q)` for `Q` the Pareto order over the columns `cs` of a family keyed by `key`, larger
    better on column `c` exactly when `big[c]`: per set, the rows no row of the set strictly
    dominates (`thinSweep` over the `segments` of the key codes). A column not of longs is
    compared by its dense rank (`drank`). Equal rows of one set are one element: the first is kept.
    Answers the kept rows' indices. -/
def thin {k : QAtomicType} (key : Nat × Enc) (cs : Array (Scan.Kind × ByteArray)) (big : Array Bool) : Except String ByteArray := do
  if cs.size != big.size then throw s!"thin: {cs.size} columns but {big.size} directions"
  let kc ← single (← codes k #[key])
  let (p, o, _) := segments kc
  let ls := cs.map fun (kd, b) => gather 8 (match kd with | .i64 => b | kd => drank kd b) p
  let s := whereBits kc.n.toUSize (thinSweep ls big o)
  let t ← tuples.tupleIds (#[kc.gather (gather 8 p s)] ++ ls.map fun l => Code.ofLongs (gather 8 l s))
  pure (gather 8 p (gather 8 s t.2))

/-! ## The operators -/

variable {A B C : QAtomicType}

/-- The two parts of a joint coding of two payloads. -/
def two (cs : Array Code) : Except String (Code × Code) :=
  if h : cs.size = 2 then pure (cs[0], cs[1]) else throw s!"{cs.size} code parts where two were coded"

/-- `R ⊑ S`: `member` of `|R|` in `|S|`, all set. -/
def le (R S : Rel A B) : Except String Bool := do
  let r ← cols R; let s ← cols S
  let (pr, ps) ← two (← pairs #[r, s])
  pure (len (whereBits r.n.toUSize (pr.member ps)) == r.n)

/-- `R ∩ S`: the semi-join on pairs — `member`, `whereBits`, `gatherColumn`. -/
def inter (R S : Rel A B) : Except String (Rel A B) := do
  let r ← cols R; let s ← cols S
  let (pr, ps) ← two (← pairs #[r, s])
  let t ← r.rows (whereBits r.n.toUSize (pr.member ps))
  ofCols A B t.key t.val

/-- `R ∪ S`: `razeColumn` of keys and of vals, the first row of each pair. -/
def union (R S : Rel A B) : Except String (Rel A B) := do
  let r ← cols R; let s ← cols S
  let u ← (Cols.mk (k := A) (v := B) (r.n + s.n) (← raze A #[r.key, s.key]) (← raze B #[r.val, s.val])).nub
  ofCols A B u.key u.val

/-- `𝟘`: no pair. -/
def zero : Except String (Rel A B) := do ofCols A B (← empty A) (← empty B)

/-- `⊤` on the universes `Ua`, `Ub`: `cross`. -/
def top {ma mb : Nat} (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  let (i, j) := cross ma mb
  ofCols A B (← pick A Ua.part i) (← pick B Ub.part j)

/-- `𝟙` on `U`: key and val the one column, shared. -/
def idU {t : QAtomicType} {m : Nat} (U : Arr t m) : Rel t t := ⟨m, U, U⟩

theorem idU_holds {t : QAtomicType} {m : Nat} (U : Arr t m) (x y : El t) :
    (idU U).Holds x y ↔ x = y ∧ ∃ i, U.get i = x := by
  simp only [Rel.Holds, idU]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨h1 ▸ h2, i, h1⟩, fun ⟨h, i, h1⟩ => ⟨i, h1, h ▸ h1⟩⟩

/-- `R°`: the two fields swap, nothing runs. -/
def convArr {k v : QAtomicType} {n : Nat} (key : Arr k n) (val : Arr v n) : Rel v k := ⟨n, val, key⟩

theorem convArr_holds {k v : QAtomicType} {n : Nat} (key : Arr k n) (val : Arr v n) (x : El k) (y : El v) :
    (convArr key val).Holds y x ↔ (⟨n, key, val⟩ : Rel k v).Holds x y := by
  simp only [Rel.Holds, convArr]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

/-- `R°`: `convArr`. -/
def conv (R : Rel A B) : Except String (Rel B A) := pure (convArr R.key R.val)

/-- `R ≫ S`: `join` on `R.val = S.key`, the key picked from `R`, the val from `S`. -/
def comp (R : Rel A B) (S : Rel B C) : Except String (Rel A C) := do
  let r ← cols R; let s ← cols S
  let (rc, sc) ← two (← codes B #[r.val, s.key])
  let (i, j) := join rc sc
  ofCols A C (← pick A r.key i) (← pick C s.val j)

/-- The coreflexive on the distinct elements of `x`: the first row of each code. -/
def distinctCorefl (t : QAtomicType) (x : Nat × Enc) : Except String (Rel t t) := do
  let d ← pick t x (← single (← codes t #[x])).groupIds.2
  ofCols t t d d

/-- `dom R`: the coreflexive on the distinct keys. -/
def dom (R : Rel A B) : Except String (Rel A A) := do let r ← cols R; distinctCorefl A r.key

/-- `ran R`: the coreflexive on the distinct vals. -/
def ran (R : Rel A B) : Except String (Rel B B) := do let r ← cols R; distinctCorefl B r.val

/-- `p?` on `U`, `p x ↔ x op e` for one of `Ew`'s six comparisons: `Ew.cmp`, `whereBits`, `gatherColumn`.
    The comparison is arithmetic, so `U` is an ordered type (`arrDense`). -/
def corefl {a : QAtomicType} {m : Nat} (U : Arr a m) (op : UInt8) (e : UInt64) : Except String (Rel a a) := do
  let (k, u) ← arrDense U
  let d ← pick a U.part (whereBits m.toUSize (Ew.cmp op (cls k) Ew.va u (Column.pushBits .empty e k.width) m.toUSize))
  ofCols _ _ d d

/-- `Coreflexive R`, `R ⊑ 𝟙`: every key's code equals its val's. -/
def isCorefl (R : Rel A A) : Except String Bool := do
  let r ← cols R
  let (kc, vc) ← two (← codes A #[r.key, r.val])
  pure (len (kc.eqAt vc) == r.n)

/-- `R \ S` (`R : a ⟶ b`, `S : a ⟶ c`), by counting: `join` on the shared key → rows `(y, z)`;
    `cnt(y, z)` against `cnt(R.val)` `at` `y`; the vacuous `y ∉ ran R` with every `z` from the
    universes `Ub`, `Uc`: `cross(anti(Ub, ran R), Uc)`. -/
def leftDiv {mb mc : Nat} (R : Rel A B) (S : Rel A C) (Ub : Arr B mb) (Uc : Arr C mc) : Except String (Rel B C) := do
  let r ← (← cols R).nub; let s ← (← cols S).nub
  let (rk, sk) ← two (← codes A #[r.key, s.key])
  let (i, j) := join rk sk
  let y ← pick B r.val i; let z ← pick C s.val j
  let ycs ← codes B #[y, r.val, Ub.part]
  let some yc := ycs[0]? | throw "leftDiv: no code of y"
  let some rvc := ycs[1]? | throw "leftDiv: no code of R.val"
  let some ubc := ycs[2]? | throw "leftDiv: no code of Ub"
  let zc ← single (← codes C #[z])
  let (gid, firsts) ← tuples.tupleIds #[yc, zc]
  let got := classSizes yc.n (gid, firsts)
  let keep := gather 8 firsts (whereEqV got (atCnt (cnt rvc) (yc.gather firsts)))
  let miss := anti ubc rvc
  let (p, q) := cross (len miss) mc
  ofCols B C (← raze B #[← pick B y keep, ← pick B Ub.part (gather 8 miss p)])
    (← raze C #[← pick C z keep, ← pick C Uc.part q])

/-- `R / S = (S° \ R°)°` (`R : a ⟶ c`, `S : b ⟶ c`); its vacuous term is `cross(Ua, anti(Ub, dom S))`. -/
def rightDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  conv (← leftDiv (← conv S) (← conv R) Ub Ua)

/-- `R /ₛ S` (`R : a ⟶ c`, `S : b ⟶ c`), equal fibres: the fibres of `R` and of `S` as `segments`
    of one value code space, their `setIds` in one call, `join` on the ids → `(x, y)`; the vacuous
    term `cross(anti(Ua, dom R), anti(Ub, dom S))`, the empty fibres. -/
def symDiv {ma mb : Nat} (R : Rel A C) (S : Rel B C) (Ua : Arr A ma) (Ub : Arr B mb) : Except String (Rel A B) := do
  let r ← cols R; let s ← cols S
  let (rv, sv) ← two (← codes C #[r.val, s.val])
  let (rk, uac) ← two (← codes A #[r.key, Ua.part])
  let (sk, ubc) ← two (← codes B #[s.key, Ub.part])
  let (pr, orr, fr) := segments rk; let (ps, os, fs) := segments sk
  let ids ← setIds (Code.cat #[rv.gather pr, sv.gather ps]) (concatBytes #[orr.extract 0 (orr.size - 8), addc os r.n])
  let (i, j) := join (Code.ofLongs (ids.extract 0 (8 * len fr))) (Code.ofLongs (ids.extract (8 * len fr) ids.size))
  let ex := anti uac rk; let ey := anti ubc sk
  let (p, q) := cross (len ex) (len ey)
  ofCols A B (← raze A #[← pick A r.key (gather 8 fr i), ← pick A Ua.part (gather 8 ex p)])
    (← raze B #[← pick B s.key (gather 8 fs j), ← pick B Ub.part (gather 8 ey q)])

/-- The groups `ds` against their boxed slices of `val`: the offsets `o` a kernel wrote (`runStarts`,
    which ends with the count) decided as cuts by `Parted.of?`, then `box`. -/
def grouped {v : QAtomicType} {n : Nat} (t : QAtomicType) (ds : Nat × Enc) (o : ByteArray) (val : Arr v n) : Except String (Rel t .general) := do
  let g := ds.1
  let some P := Parted.of? (← Arr.ofPart .long (g + 1) (longs o) "grouped") val
    | throw s!"grouped: the offsets are not ascending cuts of {n} rows"
  pure ⟨g, ← Arr.ofPart t g ds "grouped", ← Arr.ofPart .general g (← P.box).part "grouped"⟩

/-- The groups of a column whose equal elements are contiguous: `grouped` with `o` the run starts
    of its codes and the count (`runStarts`) and `ds` the element at each start. -/
def runs {v : QAtomicType} {n : Nat} (t : QAtomicType) (key : Nat × Enc) (val : Arr v n) : Except String (Rel t .general) := do
  let st := (← single (← codes t #[key])).runStarts
  grouped t (← pick t key (st.extract 0 (st.size - 8))) st val

/-- A family stored as its pairs `(X, x)` sorted key-major, each pair once: the set `X` IS the
    contiguous run of its key, boxed (`runs`). `gradeBy` on (key code, value code), `gatherColumn`. -/
def family (d : Cols A B) : Except String (Rel A .general) := do
  let d ← d.nub
  let s ← d.rows (gradeBy d.n #[← single (← codes A #[d.key]), ← single (← codes B #[d.val])])
  runs A s.key (← Arr.ofPart B s.n s.val "family")

/-- `Λ(R)`: `x Λ(R) X ↔ X = {z | x R z}` — the family of `R`'s fibres, one segment per `x ∈ dom R`. -/
def transpose (R : Rel A B) : Except String (Rel A .general) := do family (← cols R)

/-- q's `=x` of a list: each distinct value against the positions holding it, boxed — `Order.group`'s
    flattened indices of the codes, cut at the values they hold (`runs`). -/
def group {n : Nat} (x : Arr B n) : Except String (Rel B .general) := do
  let c ← single (← codes B #[x.part])
  -- below a byte `group` has no lane: its indices are the stable grade of the classes by first occurrence
  let idx := match c.kind with
    | some k => (Order.group k c.n.toUSize c.b).2.1
    | none => let (gid, fs) := c.groupIds; (Code.ofIds (len fs) c.n gid).grade
  runs B (← pick B x.part idx) (← Arr.ofPart .long (len idx) (longs idx) "group")

/-- `∋` of a stored family (one boxed set of `v` per key): the pairs `(set id, element)` — the flat form
    (`Parted.ofBoxes`) and the group of each position (`groupOf`). -/
def mem {k : QAtomicType} (v : QAtomicType) (G : Rel k .general) : Except String (Rel .long v) := do
  let P ← Parted.ofBoxes v G.val
  let some ob := longBytes (P.g + 1) P.o.enc | throw "∋: the offsets have no dense payload"
  pure ⟨P.n, ← Arr.ofPart .long P.n (longs (groupOf ob P.n)) "mem", P.val⟩

/-- `E(R)` of a family `G` given as its pairs `(X, x)`: `Λ(∋ ≫ R)` = the family of `G ≫ R`. -/
def existsImage (G : Rel A B) (R : Rel B C) : Except String (Rel A .general) := do
  family (← cols (← comp G R))

/-- A table of one key and two value columns: the product `⟨R, S⟩`, `x ⟨R,S⟩ (y, z)`. -/
structure Tab (k v w : QAtomicType) where
  n : Nat
  key : Arr k n
  fst : Arr v n
  snd : Arr w n

def Tab.Holds {k v w : QAtomicType} (T : Tab k v w) (x : El k) (y : El v) (z : El w) : Prop :=
  ∃ i, T.key.get i = x ∧ T.fst.get i = y ∧ T.snd.get i = z

def Tab.toList {k v w : QAtomicType} (T : Tab k v w) : List (El k × El v × El w) :=
  List.ofFn fun i => (T.key.get i, T.fst.get i, T.snd.get i)

/-- `⟨R, S⟩`: `join` on the keys → rows `(x, y, z)`, both value columns kept under one `n`. -/
def pair (R : Rel A B) (S : Rel A C) : Except String (Tab A B C) := do
  let r ← cols R; let s ← cols S
  let (rk, sk) ← two (← codes A #[r.key, s.key])
  let (i, j) := join rk sk
  let t ← ofCols A B (← pick A r.key i) (← pick B r.val i)
  pure ⟨t.n, t.key, t.val, ← Arr.ofPart C t.n (← pick C s.val j) "pair"⟩

/-- `outl`: the first component column, nothing runs. -/
def outl {k v w : QAtomicType} (T : Tab k v w) : Rel k v := ⟨T.n, T.key, T.fst⟩
/-- `outr`: the second component column. -/
def outr {k v w : QAtomicType} (T : Tab k v w) : Rel k w := ⟨T.n, T.key, T.snd⟩

theorem outl_holds {k v w : QAtomicType} (T : Tab k v w) (x : El k) (y : El v) : (outl T).Holds x y ↔ ∃ z, T.Holds x y z :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨_, i, h1, h2, rfl⟩, fun ⟨_, i, h1, h2, _⟩ => ⟨i, h1, h2⟩⟩

theorem outr_holds {k v w : QAtomicType} (T : Tab k v w) (x : El k) (z : El w) : (outr T).Holds x z ↔ ∃ y, T.Holds x y z :=
  ⟨fun ⟨i, h1, h2⟩ => ⟨_, i, h1, rfl, h2⟩, fun ⟨_, i, h1, _, h2⟩ => ⟨i, h1, h2⟩⟩

/-- A relation between pairs, `(x, y) ⟶ (x', y')`, as four columns of one `n`. -/
structure Rel2 (k₁ k₂ v₁ v₂ : QAtomicType) where
  n : Nat
  k₁ : Arr k₁ n
  k₂ : Arr k₂ n
  v₁ : Arr v₁ n
  v₂ : Arr v₂ n

def Rel2.toList {k₁ k₂ v₁ v₂ : QAtomicType} (T : Rel2 k₁ k₂ v₁ v₂) : List ((El k₁ × El k₂) × (El v₁ × El v₂)) :=
  List.ofFn fun i => ((T.k₁.get i, T.k₂.get i), (T.v₁.get i, T.v₂.get i))

/-- `R × S` as a relation of its own: `cross` of the rows of `R` and of `S`. `Δ(R)` is `prod R R`. -/
def prod {D E : QAtomicType} (R : Rel A B) (S : Rel D E) : Except String (Rel2 A D B E) := do
  let r ← cols R; let s ← cols S
  let (i, j) := cross r.n s.n
  let m := r.n * s.n
  pure ⟨m, ← Arr.ofPart A m (← pick A r.key i) "prod", ← Arr.ofPart D m (← pick D s.key j) "prod",
    ← Arr.ofPart B m (← pick B r.val i) "prod", ← Arr.ofPart E m (← pick E s.val j) "prod"⟩

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

/-- `[R, S]`: the rows of `R` tagged `inl`, of `S` tagged `inr` — `concatBits` of constant bit columns. -/
def junc (R : Rel A C) (S : Rel A C) : Except String (SumRel A C) := do
  let r ← cols R; let s ← cols S
  let m := r.n + s.n
  pure ⟨m, ← Arr.ofPart .boolean m (m, .bits (concatBits #[r.n, s.n] #[bitsOf false r.n, bitsOf true s.n])) "junc",
    ← Arr.ofPart A m (← raze A #[r.key, s.key]) "junc", ← Arr.ofPart C m (← raze C #[r.val, s.val]) "junc"⟩

/-- `inl°` on `U`: `inl x ↦ x`, the tag set to `false`; `inr°` with `true`. -/
def injConv {m : Nat} (tag : Bool) (U : Arr A m) : Except String (SumRel A A) := do
  pure ⟨m, ← Arr.ofPart .boolean m (m, .bits (bitsOf tag m)) "injConv", U, U⟩

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
  let r ← cols R; let (_, v) ← arrDense R.val
  let (gid, firsts) := (← single (← codes A #[r.key])).groupIds
  let ng := len firsts
  ofCols A .long (← pick A r.key firsts) (longs ((overGroups op Ew.i64 nul ng.toUSize (Column.idWidthOf ng).toUSize r.n gid v).extract 0 (8 * ng)))

/-- `α⁻¹` of a list, `uncons`: its first element and the rest, two picks (`gatherColumn`). -/
def uncons {n : Nat} (x : Arr B n) : Except String (Arr B 1 × Arr B (n - 1)) := do
  if n = 0 then throw "uncons of an empty list"
  let m := n - 1
  let rest := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (tilLongs m.toUSize) (one 1) m.toUSize
  pure (← Arr.ofPart B 1 (← pick B x.part (one 0)) "uncons", ← Arr.ofPart B m (← pick B x.part rest) "uncons")

/-- An unfold then a fold: Lean's loop, at most `fuel` rounds of `step` until `done`, each round kernels. -/
def hylo {α : Type} (done : α → Except String Bool) (step : α → Except String α) : Nat → α → Except String α
  | 0, _ => throw "hylo: out of fuel"
  | fuel + 1, x => do if ← done x then pure x else hylo done step fuel (← step x)

/-- `est(≤)` (`desc`: `est(≥)`) of a family of longs: `overGroups` lesser/greater per key. -/
def est (desc : Bool) (G : Rel A .long) : Except String (Rel A .long) :=
  foldGroups (if desc then .greater else .lesser) G

/-- `Entire R` on the universe `U`: `member` of `U`'s codes in the keys', all set. -/
def entire {m : Nat} (R : Rel A B) (U : Arr A m) : Except String Bool := do
  let r ← cols R
  let (uc, kc) ← two (← codes A #[U.part, r.key])
  pure (len (whereBits m.toUSize (uc.member kc)) == m)

/-- `Simple R`: in `R` with each pair once, every key distinct (`groupIds` count of the key codes). -/
def simple (R : Rel A B) : Except String Bool := do
  let r ← (← cols R).nub
  pure (len (← single (← codes A #[r.key])).groupIds.2 == r.n)

def isMap {m : Nat} (R : Rel A B) (U : Arr A m) : Except String Bool := do
  pure ((← entire R U) && (← simple R))

/-- `Injective R` = `Simple R°`. -/
def injective (R : Rel A B) : Except String Bool := do simple (← conv R)

/-- `Surjective R` = `Entire R°` on the universe `U` of `b`. -/
def surjective {m : Nat} (R : Rel A B) (U : Arr B m) : Except String Bool := do
  entire (← conv R) U

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
private def U4 : Arr L 4 := (Arr.mk (.bytes <| packLongs [0, 1, 2, 3]) (by decide))
private def LsV : Arr L 4 := (Arr.mk (.bytes <| packLongs [5, 3, 5, 9]) (by decide))
private def Ls : LL := ⟨4, U4, LsV⟩
/-- A stored family's pairs `(key, element)`: the boxes razed (`Parted.ofBoxes`), each element beside its
    group's key. -/
private def flat {k : QAtomicType} (v : QAtomicType) (X : Rel k .general) : Except String (List (El k × El v)) := do
  let P ← Parted.ofBoxes v X.val
  pure (P.toList.filterMap fun (g, y) => X.key.toList[g.toNatClampNeg]?.map (·, y))
private def okFlat {k : QAtomicType} (v : QAtomicType) (x : Except String (Rel k .general)) (p : List (El k × El v) → Bool) : Bool :=
  match x with | .ok X => (match flat v X with | .ok l => p l | .error _ => false) | .error _ => false
private def Ua : Arr L 4 := (Arr.mk (.bytes <| packLongs [1, 2, 3, 4]) (by decide))
private def Ub : Arr L 4 := (Arr.mk (.bytes <| packLongs [10, 20, 30, 40]) (by decide))
private def Uc : Arr L 3 := (Arr.mk (.bytes <| packLongs [7, 8, 9]) (by decide))

#guard ok (le R S) (· == false)
#guard ok (inter R S) fun X => ok (le X R) id && ok (le X S) id
#guard ok (inter R S) fun X => seteq X.toList (R.toList.filter S.toList.contains)
#guard ok (union R S) fun X => seteq X.toList (R.toList ++ S.toList) && X.n == 6
#guard ok (zero (A := L) (B := L)) (·.n == 0)
#guard ok (top Ua Uc) fun X => seteq X.toList (Ua.toList.flatMap fun x => Uc.toList.map (x, ·))
#guard (idU Ua).toList == Ua.toList.map fun x => (x, x)
#guard ok (conv R) fun X => seteq X.toList (R.toList.map fun (x, y) => (y, x))
#guard ok (conv Ls) fun X => seteq X.toList (Ls.toList.map fun (x, y) => (y, x))
#guard ok (comp R T) fun X =>
  seteq X.toList (R.toList.flatMap fun (x, y) => T.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard ok (comp Ls Ls) fun X =>
  seteq X.toList (Ls.toList.flatMap fun (x, y) => Ls.toList.filterMap fun (y', z) => if y == y' then some (x, z) else none)
#guard ok (dom R) fun X => seteq X.toList [(1, 1), (2, 2), (3, 3)] && X.n == 3
#guard ok (ran S) fun X => seteq X.toList [(10, 10), (20, 20), (40, 40)] && X.n == 3
#guard ok (corefl Ua Ew.gt 2) fun X => X.toList == [(3, 3), (4, 4)]
#guard ok (isCorefl (idU Ua)) id && ok (isCorefl R) (· == false)

-- `R \ S` over `Ub × Ub`: `y (R\S) z ↔ ∀ x, x R y → x S z`
private def leftSpec (R S : LL) (Ub Uc : List Int64) : List (Int64 × Int64) :=
  Ub.flatMap fun y => (Uc.filter fun z => R.toList.all fun (x, y') => y' != y || S.toList.contains (x, z)).map (y, ·)
#guard ok (leftDiv R S Ub Ub) fun X => seteq X.toList (leftSpec R S Ub.toList Ub.toList)
#guard ok (leftDiv R R Ub Ub) fun X => seteq X.toList (leftSpec R R Ub.toList Ub.toList)
-- `R / S` (`R : a ⟶ c`, `S : b ⟶ c`): `x (R/S) y ↔ ∀ z, y S z → x R z`
#guard ok (rightDiv R S Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => S.toList.all fun (y', z) => y' != y || R.toList.contains (x, z)).map (x, ·))
-- `R /ₛ S`: equal fibres
private def fib (R : LL) (x : Int64) : List Int64 := R.toList.filterMap fun (x', z) => if x == x' then some z else none
#guard ok (symDiv R S Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib S y)).map (x, ·))
#guard ok (symDiv R R Ua Ua) fun X => seteq X.toList
  (Ua.toList.flatMap fun x => (Ua.toList.filter fun y => seteq (fib R x) (fib R y)).map (x, ·))

-- `Λ(R)`: the same pairs, each set one contiguous run of its key
#guard okFlat L (do transpose (← union R R)) fun l => seteq l R.toList && l.length == 4 &&
  (l.map (·.1)) == [1, 1, 2, 3]
#guard okFlat L (group LsV) (· == [(5, 0), (5, 2), (3, 1), (9, 3)])
#guard ok (group LsV) (·.n == 3)
private def LfV : Arr L 4 := Arr.mk (.foR (Coc.encode 8 (packLongs [5, 3, 5, 9])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9])).2) (foRLongs_wf [5, 3, 5, 9])
private def Lf : LL := ⟨4, U4, LfV⟩
#guard okFlat L (group LfV) (· == [(5, 0), (5, 2), (3, 1), (9, 3)])
#guard ok (do transpose (← union R R)) (·.n == 3)
#guard ok (do mem L (← transpose R)) fun X => X.toList.map (·.2) == [10, 20, 10, 30] && (X.toList.map (·.1)) == [0, 0, 1, 2]
#guard ok (do transpose (← zero (A := L) (B := L))) (·.n == 0)
-- `anti`: the positions of `x` not in `y`
#guard anti (Code.ofLongs (packLongs [3, 1, 4, 1])) (Code.ofLongs (packLongs [1, 5])) == packLongs [0, 2]
/-- The family of `g` sets keyed `0 … g-1`, the sets cut from `val` at the offsets `o`, boxed. -/
private def boxed {g n : Nat} (o : Arr L (g+1)) (val : Arr L n) : Except String (Rel L .general) := do
  let some P := Parted.of? o val | throw "boxed: not cuts"
  pure ⟨g, ← Arr.ofPart L g (longs (tilLongs g.toUSize)) "boxed", ← Arr.ofPart .general g (← P.box).part "boxed"⟩
-- `∋` of a stored family: the parted list `(10 20; 30)` from the core
private def o2 : Arr L 3 := (Arr.mk (.bytes <| packLongs [0, 2, 3]) (by decide))
private def parted : Except String (Rel L .general) := boxed o2 ((Arr.mk (.bytes <| packLongs [10, 20, 30]) (by decide)) : Arr L 3)
#guard ok (do mem L (← parted)) fun X => X.toList == [(0, 10), (0, 20), (1, 30)]
-- `E(R)` of the family `G = {X₁ = {1, 2}, X₂ = {3}}`
private def G : LL := ⟨3, (Arr.mk (.bytes <| packLongs [1, 1, 2]) (by decide)), (Arr.mk (.bytes <| packLongs [1, 2, 3]) (by decide))⟩
#guard okFlat L (existsImage G R) fun l => seteq l
  (G.toList.flatMap fun (s, x) => R.toList.filterMap fun (x', y) => if x == x' then some (s, y) else none)

#guard ok (pair R S) fun P => seteq P.toList
  (R.toList.flatMap fun (x, y) => S.toList.filterMap fun (x', z) => if x == x' then some (x, y, z) else none)
#guard ok (pair R S) fun P => seteq (outl P).toList (R.toList.filter fun (x, _) => S.toList.any (·.1 == x))
#guard ok (pair R S) fun P => seteq (outr P).toList (S.toList.filter fun (x, _) => R.toList.any (·.1 == x))
#guard ok (prod R T) fun P => seteq P.toList
  (R.toList.flatMap fun (x, x') => T.toList.map fun (y, y') => ((x, y), (x', y')))
#guard ok (junc R S) fun J => seteq J.toList (R.toList.map (fun (x, y) => ((false, x), y)) ++ S.toList.map fun (x, y) => ((true, x), y))
#guard ok (injConv true Ua) fun J => J.toList == Ua.toList.map fun x => ((true, x), x)

#guard ok (mapVal Ew.neg Ls) fun X => X.toList == [(0, -5), (1, -3), (2, -5), (3, -9)]
#guard ok (foldOver .add Ls.val) (· == 22)
#guard ok (foldGroups .add R) fun X => X.toList == [(1, 30), (2, 10), (3, 30)]
#guard ok (uncons LsV) fun (h, t) => h.toList == [5] && t.toList == [3, 5, 9]
-- an unfold then a fold: uncons to the end, summing the heads
#guard ok (hylo (fun (xs, _) => pure (xs.1 == 0))
    (fun ((xs : (m : Nat) × Arr L m), (acc : Int64)) => do let (h, t) ← uncons xs.2; pure (⟨_, t⟩, acc + (← foldOver .add h))) 10 (⟨_, LsV⟩, 0))
  fun (_, s) => s == 22
#guard ok (est false R) fun X => X.toList == [(1, 10), (2, 10), (3, 30)]
#guard ok (est true R) fun X => X.toList == [(1, 20), (2, 10), (3, 30)]
-- thin, k = 1: per key of `R` the largest value, then the smallest
private def lc (xs : List Int64) : Scan.Kind × ByteArray := (.i64, packLongs xs)
#guard ok (thin (k := L) (longs (packLongs [1, 1, 2, 3])) #[lc [10, 20, 10, 30]] #[true]) (· == packLongs [1, 2, 3])
#guard ok (thin (k := L) (longs (packLongs [1, 1, 2, 3])) #[lc [10, 20, 10, 30]] #[false]) (· == packLongs [0, 2, 3])
-- k = 2, one set (1,5) (3,2) (2,2) (3,1) (1,5): both larger → (1,5) and (3,2), one copy each;
-- the second smaller → (3,1) alone
private def k5 : Nat × Enc := longs (packLongs [1, 1, 1, 1, 1])
#guard ok (thin (k := L) k5 #[lc [1, 3, 2, 3, 1], lc [5, 2, 2, 1, 5]] #[true, true]) (· == packLongs [0, 1])
#guard ok (thin (k := L) k5 #[lc [1, 3, 2, 3, 1], lc [5, 2, 2, 1, 5]] #[true, false]) (· == packLongs [3])
-- k = 3, two sets: {(1,1,1) (2,2,2) (2,2,2) (3,0,0)} keeps (2,2,2) once and (3,0,0);
-- {(0,5,0) (0,4,1) (0,4,0)} drops (0,4,0); a key interleaved: set 2's rows come first
#guard ok (thin (k := L) (longs (packLongs [1, 1, 1, 1, 2, 2, 2])) #[lc [1, 2, 2, 3, 0, 0, 0], lc [1, 2, 2, 0, 5, 4, 4],
    lc [1, 2, 2, 0, 0, 1, 0]] #[true, true, true]) (· == packLongs [1, 3, 4, 5])
#guard ok (thin (k := L) (longs (packLongs [2, 1, 2, 1, 1, 2, 1])) #[lc [0, 1, 0, 2, 2, 0, 3], lc [5, 1, 4, 2, 2, 4, 0],
    lc [0, 1, 1, 2, 2, 0, 0]] #[true, true, true]) (· == packLongs [0, 2, 3, 6])
-- setId: segments {3 1 1} {1 3} {2} {} {} {1 3 3}: the three spellings of {1, 3} one id, `{}` one id
private def o6 : Arr L 7 := (Arr.mk (.bytes <| packLongs [0, 3, 5, 6, 6, 6, 9]) (by decide))
private def sets : Except String (Rel L .general) :=
  boxed o6 ((Arr.mk (.bytes <| packLongs [3, 1, 1, 1, 3, 2, 1, 3, 3]) (by decide)) : Arr L 9)
#guard ok (do setId L (← sets)) (· == packLongs [0, 0, 1, 2, 2, 0])
-- Λ(R ∪ S): fibres {10 20} {10 20} {30} {40}
#guard ok (do setId L (← transpose (← union R S))) (· == packLongs [0, 0, 1, 2])
-- Λ of {1↦10, 2↦20, 1↦20, 2↦10, 2↦10}: both fibres {10, 20}, in another order and with a repeat
private def D : LL := ⟨5, (Arr.mk (.bytes <| packLongs [1, 2, 1, 2, 2]) (by decide)), (Arr.mk (.bytes <| packLongs [10, 20, 20, 10, 10]) (by decide))⟩
#guard ok (do setId L (← transpose D)) (· == packLongs [0, 0])

private def Ua3 : Arr L 3 := (Arr.mk (.bytes <| packLongs [3, 1, 2]) (by decide))
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
private def same {t : QAtomicType} (X Y : Rel L t) : Except String LL := do comp X (← conv Y)
-- the positions of `(p q p r)` paired with equal elements: `(0 2)` share, `1` and `3` alone
private def pqpr : List (Int64 × Int64) := [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (3, 3)]

-- boolean, `bits`: `1010b`, whose positions pair `(0 2)` and `(1 3)`
private abbrev Bo := QAtomicType.boolean
private def bitsC : Nat × Enc := (4, .bits (ByteArray.mk #[0b0101]))
#guard ok (do same (← lst Bo bitsC) (← lst Bo bitsC)) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)] && X.n == 8
#guard okFlat L (do group (← lstV Bo bitsC).2) (· == [(true, 0), (true, 2), (false, 1), (false, 3)])
#guard ok (do ran (← lst Bo bitsC)) fun X => seteq X.toList [(true, true), (false, false)] && X.n == 2
#guard ok (do union (← lst Bo bitsC) (← lst Bo bitsC)) fun X => X.n == 4
#guard ok (do symDiv (← lst Bo bitsC) (← lst Bo bitsC) U4 U4) fun X =>
  seteq X.toList [(0, 0), (0, 2), (2, 0), (2, 2), (1, 1), (1, 3), (3, 1), (3, 3)]

-- symbol, `syms` and `enum`: `` `bc`a`bc`d `` in both, compared across the two
private abbrev Sy := QAtomicType.symbol
private def symsC : Nat × Enc := (4, .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0, 100, 0]) #[0, 3, 5, 8, 10])
private def enumC : Nat × Enc :=
  (4, .enum (ByteArray.mk #[97, 0, 98, 99, 0, 100, 0]) #[0, 2, 5, 7] (Column.packIds (Column.idWidth #[0, 2, 5, 7]) 4 fun i => [1, 0, 1, 2][i]!))
#guard ok (lst Sy enumC) fun X => X.toList == [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard ok (do same (← lst Sy symsC) (← lst Sy enumC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do same (← lst Sy enumC) (← lst Sy enumC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do union (← lst Sy symsC) (← lst Sy enumC)) fun X => X.n == 4 &&
  seteq X.toList [(0, "bc"), (1, "a"), (2, "bc"), (3, "d")]
#guard okFlat L (do group (← lstV Sy enumC).2) (· == [("bc", 0), ("bc", 2), ("a", 1), ("d", 3)])
#guard okFlat L (do group (← lstV Sy symsC).2) (· == [("bc", 0), ("bc", 2), ("a", 1), ("d", 3)])
#guard ok (do symDiv (← lst Sy symsC) (← lst Sy enumC) U4 U4) fun X => seteq X.toList pqpr
#guard ok (do leftDiv (← lst Sy enumC) (← lst Sy symsC) (← Arr.ofPart Sy 4 symsC "U") (← Arr.ofPart Sy 4 enumC "U")) fun X =>
  seteq X.toList [("bc", "bc"), ("a", "a"), ("d", "d")]
#guard ok (do top (← Arr.ofPart Sy 4 enumC "U") (← Arr.ofPart Bo 4 bitsC "U")) (·.n == 16)
#guard ok (do transpose (← conv (← lst Sy enumC))) (·.n == 3)

-- the lane each encoding codes at: bits a bit; a three-symbol enum, or three distinct longs whose range
-- outruns the rows (a grouping pass's ids), a 2-bit lane; foR and dense offsets a byte
private def laneOf (t : QAtomicType) (c : Nat × Enc) : Option Nat := match codes t #[c] with | .ok #[x] => some x.w | _ => none
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
#guard (c2.cut #[3, 3]).map (fun p => (List.range p.n).map (Column.idAt p.b 2)) == #[[2, 0, 1], [2, 0, 2]]
#guard (Code.cat (c2.cut #[1, 5])).b == c2.b
#guard let g := c2.gather (packLongs [5, 1]); (List.range 2).map (Column.idAt g.b 2) == [2, 0]
#guard c2.grade == packLongs [1, 4, 2, 0, 3, 5]
#guard c2.groupIds.2 == packLongs [0, 1, 2]
#guard c2.find ⟨2, 2, 3, Column.packIds 2 2 ([1, 2][·]!)⟩ == packLongs [2, 0]
#guard c2.eqAt ⟨2, 6, 3, Column.packIds 2 6 ([2, 1, 1, 0, 0, 2][·]!)⟩ == packLongs [0, 2, 4, 5]
-- two foR parts of different bases, one negative: rebased (`foRShift`), equal elements equal codes
private def Lneg : LL := ⟨4, U4, Arr.mk (.foR (Coc.encode 8 (packLongs [9, -3, 5, 5])).1 (Coc.encode 8 (packLongs [9, -3, 5, 5])).2) (foRLongs_wf [9, -3, 5, 5])⟩
#guard ok (do comp Lneg (← conv Lf)) fun X => seteq X.toList
  (Lneg.toList.flatMap fun (i, x) => Lf.toList.filterMap fun (j, y) => if x == y then some (i, j) else none)

-- float through ALP: `1.5 2.25 1.5 0.1`, and the same as dense bytes
private abbrev Fl := QAtomicType.float
private def fs : List Float := [1.5, 2.25, 1.5, 0.1]
private def fb : ByteArray := packLongs (fs.map (·.toBits.toInt64))
private def fd : Nat × Enc := (fs.length, .bytes fb)
-- `alpOf` and not `Column.answer`, which keeps a column this short dense
private def alpC : Nat × Enc := ((Enc.alpOf Fl fd.1 fd.2).map (fd.1, ·)).getD fd
#guard alpC.2 matches .alp ..
#guard ok (do same (← lst Fl alpC) (← lst Fl alpC)) fun X => seteq X.toList pqpr && X.n == 6
#guard ok (do same (← lst Fl alpC) (← lst Fl fd)) fun X => seteq X.toList pqpr && X.n == 6
-- a float element is its IEEE bits
#guard okFlat L (do group (← lstV Fl alpC).2) fun l =>
  l.map (·.2) == [0, 2, 1, 3] && l.map (·.1) == [1.5, 1.5, 2.25, 0.1].map Float.toBits
#guard ok (do union (← lst Fl alpC) (← lst Fl fd)) fun X => X.n == 4
#guard ok (do symDiv (← lst Fl alpC) (← lst Fl alpC) U4 U4) fun X => seteq X.toList pqpr

-- a general list, `(1; (); 1; ,2)`, elements matched by identity
private def gs : Array QValue := #[.atom (.long 1), QValue.general #[], .atom (.long 1), QValue.general #[.atom (.long 2)]]
#guard ok (do same (← lst .general (genCol gs)) (← lst .general (genCol gs))) fun X => seteq X.toList pqpr && X.n == 6
#guard okFlat L (do group (← lstV .general (genCol gs)).2) fun l => l.map (·.2) == [0, 2, 1, 3] && l.length == 4
#guard ok (do union (← lst .general (genCol gs)) (← lst .general (genCol gs))) fun X => X.n == 4
#guard ok (do dom (← conv (← lst .general (genCol gs)))) (·.n == 3)
#guard ok (do symDiv (← lst .general (genCol gs)) (← lst .general (genCol gs)) U4 U4) fun X => seteq X.toList pqpr
#guard match lstV .general (genCol gs) with | .ok ⟨_, x⟩ => ok (uncons x) fun p => p.1.toList.length == 1 && p.2.toList.length == 3 | .error _ => false
#guard ok (do zero (A := .general) (B := Sy)) (·.n == 0)

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
#print axioms corefl
#print axioms isCorefl
#print axioms leftDiv
#print axioms rightDiv
#print axioms symDiv
#print axioms transpose
#print axioms group
#print axioms existsImage
#print axioms pair
#print axioms prod
#print axioms junc
#print axioms injConv
#print axioms mapVal
#print axioms foldGroups
#print axioms uncons
#print axioms thin
#print axioms setIds
#print axioms setId
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

/-- `ofCols` keys the answer by `kc`, its values by `vc`. -/
theorem ofCols_ok {k v : QAtomicType} {kc : Nat × Enc} {vc : Nat × Enc} {T : Rel k v} (h : ofCols k v kc vc = .ok T) :
    T.key.part = kc ∧ T.val.part = vc := by
  unfold ofCols at h
  cases ha : Arr.ofPart k kc.1 kc "ofCols" with
  | error e => simp [ha, bind, Except.bind] at h
  | ok a =>
    cases hb : Arr.ofPart v kc.1 vc "ofCols" with
    | error e => simp [ha, hb, bind, Except.bind] at h
    | ok b =>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨Arr.of_c ha, Arr.of_c hb⟩

/-- The generic `R°`: `ofCols` of the two payloads, swapped. -/
theorem conv_cols_holds {R : Rel A B} {S : Rel B A}
    (h : (do let r ← cols R; ofCols B A r.val r.key) = .ok S) (x : El A) (y : El B) :
    S.Holds y x ↔ R.Holds x y := by
  obtain ⟨n, K, v⟩ := R
  simp only [cols, bind, Except.bind, pure, Except.pure] at h
  obtain ⟨hkc, hvc⟩ := ofCols_ok h
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
theorem conv_holds {R : Rel A B} {S : Rel B A} (h : conv R = .ok S) (x : El A) (y : El B) :
    S.Holds y x ↔ R.Holds x y := by
  simp only [conv, pure, Except.pure, Except.ok.injEq] at h
  subst h; exact convArr_holds R.key R.val x y

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

end Laws

#print axioms conv_holds
#print axioms groupIds_faithful
#print axioms groupIds_long_faithful

end LeetQ.Rel.Alg
