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
import LeetQ.Rel.KernelWF.Gather
import QLean.Kernel.Sort
import QLean.Kernel.Structural
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Kernel.Coc
import QLean.Eval.Dyad
import QLean.Verify.Grade
import QLean.Verify.Chain
import LeetQ.Rel.KernelWF.Reduce

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel

/-! ## Long payloads: the index and count columns every step passes along -/

/-- Elements of a long payload. -/
def len (b : ByteArray) : Nat := b.size / 8

/-- `x` as a part. -/
def _root_.LeetQ.Rel.Arr.part {t : QAtomicType} {n : USize} (x : Arr t n) : USize × Enc := (n, x.enc)

/-- What a stopped op answers in the logic: no element, `Enc.blank`'s payload. -/
def blankCol (t : QAtomicType) : (n : USize) × Arr t n := ⟨0, Arr.mk (Enc.blank t 0) (Enc.blank_WF t 0)⟩

/-- A literal long column, its count `xs.length` proved by `packLongs_size`; it runs where the count
    fits a `USize`. -/
def col (xs : List Int64) : Arr .long xs.length.toUSize :=
  need (xs.length < USize.size) (fun _ => s!"col: {xs.length} longs do not fit a USize")
    (fun _ => Arr.mk (Enc.blank .long _) (Enc.blank_WF .long _)) fun h =>
  Arr.mk (.bytes (packLongs xs)) (show (packLongs xs).size = xs.length.toUSize.toNat * 8 by
    rw [packLongs_size, Nat.mul_comm, USize.toNat_ofNat_of_lt' h])

/-- A relation from its pairs of longs. -/
def ofPairs (ps : List (Int64 × Int64)) : Rel .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩

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

/-! ## Codes: equal elements equal codes, at the layout that already is one -/

/-- `n` codes at `w` bits: a bitmap at `1`, packed ids at `2`/`4` (`Column.idAt`'s lanes, which a bitmap is
    at `1` too), dense bytes at `8`/`16`/`32`/`64`. Equal elements equal codes, every code below `card`
    (`2⁶⁴` where only the layout bounds it); at `2`/`4` bits `w = Column.idWidthOf card`. `card` is a `Nat`:
    it is a bound, `2⁶⁴` included, and a kernel reads it as a table size (`idGroups`) only at `2`/`4` bits. -/
structure Code where
  w : Nat
  n : USize
  card : Nat
  b : ByteArray
  deriving Inhabited

/-- The narrowest byte layout holding the codes `0 … card-1`, for a pass (`enumIds`, `enumIdsFoR`) that
    writes a byte lane at least. -/
def codeKind (card : Nat) : Scan.Kind :=
  if card ≤ 2 ^ 8 then .u8 else if card ≤ 2 ^ 16 then .i16 else if card ≤ 2 ^ 32 then .i32 else .i64

/-- The long payload `b`'s count `len b`, where it fits a `USize`, handed to `k`; a stopped run's model is
    `default`. -/
def longCount {α : Type} [Inhabited α] (what : String) (b : ByteArray) (k : USize → α) : α :=
  need (len b < USize.size) (fun _ => s!"{what}: {len b} longs do not fit a USize") (fun _ => default)
    fun _ => k (len b).toUSize

/-- The long ids `gid`, each below `card`, packed at `codeKind card` by `enumIds`. -/
def pack (card : Nat) (gid : ByteArray) : Code := longCount "pack" gid fun n =>
  let k := codeKind card
  ⟨8 * k.width, n, card, if k == .i64 then gid else (enumIds n card.toUSize 0 (8 * k.width).toUSize gid).1⟩

/-- A long payload as codes bounded by its layout alone. -/
def Code.ofLongs (b : ByteArray) : Code := longCount "Code.ofLongs" b fun n => ⟨64, n, 2 ^ 64, b⟩

/-- The sort layout of a lane, where it has one: every lane but `2`/`4` bits. -/
def laneKind : Nat → Option Scan.Kind
  | 1 => some .bit | 8 => some .u8 | 16 => some .i16 | 32 => some .i32 | 64 => some .i64 | _ => none

/-- `n` ids below `card` packed at `w = Column.idWidthOf card` bits — an enum's ids, `groupIds`' — as a
    code where they lie. A lane of no bits (`card ≤ 1`, every id `0`) is a bitmap of zeros: the
    narrowest lane every code kernel reads. -/
def Code.ofLane (w : Nat) (n : USize) (card : Nat) (ids : ByteArray) : Code :=
  if w == 0 then ⟨1, n, card, ByteArray.mk (Array.replicate ((n.toNat + 7) / 8) 0)⟩ else ⟨w, n, card, ids⟩

/-- `n` ids in `ng` classes as `groupIds` answers them, packed at `Column.idWidthOf ng`. -/
def Code.ofIds (ng : Nat) (n : USize) (gid : ByteArray) : Code := Code.ofLane (Column.idWidthOf ng) n ng gid

/-- How many rows of `n` each class of a `groupIds` answer `(gid, firsts)` holds: `groupSizes` reading
    the ids at their width. -/
def classSizes (n : USize) (r : ByteArray × ByteArray) : ByteArray :=
  Order.groupSizes (len r.2).toUSize (Column.idWidthOf (len r.2)).toUSize n r.1

namespace Code

/-- The lane's sort layout, `none` at `2`/`4` bits, where the id kernels read. -/
def kind (c : Code) : Option Scan.Kind := laneKind c.w

/-- `c@i` for an in-range long index column: `gatherBits`, `gatherBytes`, `gatherPacked` at the lane. -/
def gather (c : Code) (i : ByteArray) : Code := longCount "Code.gather" i fun m =>
  ⟨c.w, m, c.card, match c.kind with
    | some .bit => gatherBits c.n c.b i
    | some k => gatherBytes k.width.toUSize 0 c.b i
    | none => gatherPacked c.n c.w.toUSize c.w.toUSize 0 c.b i⟩

/-- The first position in `c` of each of `x`'s codes, `c.n` at a miss: `findBitVec`, `findVec`, and
    `findIdsVec` at `2`/`4` bits or two lanes of different widths. -/
def find (c x : Code) : ByteArray :=
  match c.kind, x.kind with
  | some .bit, some .bit => findBitVec c.n c.b x.n x.b
  | some k, some k' => if k == k' then findVec k.width.toUSize false c.b x.b
    else findIdsVec c.w.toUSize c.b c.n x.w.toUSize x.b x.n
  | _, _ => findIdsVec c.w.toUSize c.b c.n x.w.toUSize x.b x.n

/-- Whether each of `x`'s codes occurs in `c`, as bits: `memberBits`, `memberVec`, `memberIdsVec`. -/
def member (x c : Code) : ByteArray :=
  match x.kind, c.kind with
  | some .bit, some .bit => memberBits x.n x.b c.n c.b
  | some k, some k' => if k == k' then memberVec k.width.toUSize false x.b c.b
    else memberIdsVec x.w.toUSize x.b x.n c.w.toUSize c.b c.n
  | _, _ => memberIdsVec x.w.toUSize x.b x.n c.w.toUSize c.b c.n

/-- The positions where `a` and `b` (one lane) hold one code: `Ew.cmp` at the codes' class, `eqIds` at
    `2`/`4` bits. -/
def eqAt (a b : Code) : ByteArray := whereBits a.n <| match a.kind with
  | some k => Ew.cmp Ew.eq (cls k) Ew.vv a.b b.b a.n
  | none => Kernel.Ew.eqIds Ew.eq Ew.vv a.b b.b a.w.toUSize a.n

/-- Each row's class, numbered by first occurrence, and each class's first row: `groupIds` at the layout,
    `idGroups` (a direct table of `card` entries) at `2`/`4` bits. -/
def groupIds (c : Code) : ByteArray × ByteArray := match c.kind with
  | some k => Order.groupIds k c.n c.b
  | none => Order.idGroups c.card.toUSize c.n c.w.toUSize c.b

/-- The rows in ascending code order, stable: `grade` at the layout, `gradeLane` at `2`/`4` bits and
    where `grade` would read an `i16`/`i32` code past the sign bit as negative (`gradeLane` is unsigned). -/
def grade (c : Code) : ByteArray := match c.kind with
  | some k => if (k == .i16 || k == .i32) && 2 ^ (c.w - 1) < c.card
    then Order.gradeLane false c.n c.w.toUSize c.b else Order.grade k false c.n c.b
  | none => Order.gradeLane false c.n c.w.toUSize c.b

/-- Codes of one space end to end, at the first part's lane: `concatBits`, `concatBytes`, and
    `concatIds` through each part's identity map at `2`/`4` bits, where a part starts inside a byte; the
    parts' summed count fits a `USize`. -/
def cat (cs : Array Code) : Code :=
  let w := if h : 0 < cs.size then cs[0].w else 8
  let total := cs.foldl (fun s c => s + c.n.toNat) 0
  need (total < USize.size) (fun _ => s!"Code.cat: {total} codes do not fit a USize") (fun _ => default) fun _ =>
  ⟨w, total.toUSize, cs.foldl (max · ·.card) 0, match laneKind w with
    | some .bit => concatBits (countBytes (cs.map (·.n))) (cs.map (·.b))
    | some _ => concatBytes (cs.map (·.b))
    | none => concatIds w.toUSize (countBytes (cs.map (·.n))) (cs.map (·.w)) (cs.map fun c => Column.packIds w c.card id) (cs.map (·.b))⟩

/-- `c` cut into parts of the counts `ns` (summing to `c.n`): byte extracts at a byte lane, `cycleBits`
    and `cycleIds` below one, where a part can start inside a byte. -/
def cut {p : Nat} (c : Code) (ns : Vector USize p) : Vector Code p :=
  if p = 1 then Vector.replicate p c else
  let part (o m : USize) : ByteArray :=
    if m == 0 then .empty
    else if c.w % 8 == 0 then c.b.extract (c.w / 8 * o.toNat) (c.w / 8 * (o.toNat + m.toNat))
    else if c.w == 1 then cycleBits c.n o m c.b
    else cycleIds c.n o m c.w.toUSize c.b
  -- part `i` starts at the sum of the counts before it, below `c.n`; the parts are few (two or three), so no
  -- running sum
  ns.mapIdx fun i m => ⟨c.w, m, c.card, part ((ns.toArray.extract 0 i).foldl (· + ·) 0) m⟩

/-- The run starts of `c` and its count: `runStartsBits`, `runStarts` at a byte lane, `runStartsIds` at
    `2`/`4` bits. -/
def runStarts (c : Code) : ByteArray := match c.kind with
  | some .bit => Kernel.runStartsBits c.n c.b
  | some k => Kernel.runStarts k.width.toUSize false c.b
  | none => Kernel.runStartsIds c.n c.w.toUSize c.b

end Code

/-- The rows in the order of each of `ks` in turn, ascending, by stable grades from the last key to the
    first at each code's own lane; answers the permutation of `n` rows. -/
def gradeBy (n : USize) (ks : Array Code) : ByteArray :=
  ks.foldr (init := tilLongs n) fun c p => gather 8 p (c.gather p).grade

/-! ## Payloads of any encoding: count, pick, join, code -/

/-- A long column's dense payload always answers: `Enc.WF .long` admits only `bytes` and `foR`. -/
theorem longBytes_isSome {n : USize} (x : Arr .long n) : (longBytes n x.enc).isSome := by
  rcases KernelWF.long_cases x.wf with ⟨b, h⟩ | ⟨M, P, h⟩ <;> simp [h, longBytes]

/-- A general list's boxed elements: its `gen` column, which is the only one `Arr .general` admits. -/
def gens {n : USize} (x : Arr .general n) : Array QValue :=
  (match x.enc with | .gen xs => some xs | _ => none).get
    (by obtain ⟨xs, he, -⟩ := KernelWF.general_cases x.wf; simp [he])

/-- A general list's column over `xs`, where its count fits a `USize`. -/
def genCol (xs : Array QValue) : (n : USize) × Arr .general n :=
  need (xs.size < USize.size) (fun _ => s!"genCol: {xs.size} elements do not fit a USize")
    (fun _ => blankCol .general) fun h =>
  ⟨xs.size.toUSize, Arr.mk (.gen xs) (by simp [Enc.WF, USize.toNat_ofNat_of_lt' h])⟩

/-- `x@i` for a long payload `i`: `gatherColumn`, which answers every column encoding (`gatherColumn_isSome`),
    where the index's count fits a `USize`. A general list is picked by position; a position past the end
    reads the null, as q's `@`. -/
def pick (t : QAtomicType) (c : (n : USize) × Arr t n) (i : ByteArray) : (n : USize) × Arr t n :=
  if hg : t = .general then by
    subst hg; exact let xs := gens c.2; genCol ((longRows i).map fun p => xs[p]?.getD (QLean.Eval.fillOf xs))
  else
    need (len i < USize.size) (fun _ => s!"pick: {len i} rows do not fit a USize") (fun _ => blankCol t)
      fun hl =>
    have h := KernelWF.gatherColumn_isSome c.2.wf hg (m := (len i).toUSize) i
      (by rw [USize.toNat_ofNat_of_lt' hl]; exact Nat.div_mul_le_self _ _)
    ⟨(len i).toUSize, Arr.mk ((gatherColumn t c.1 c.2.enc (len i).toUSize (.bytes i)).get h)
      (KernelWF.gatherColumn_wf c.2.wf i (USize.toNat_ofNat_of_lt' hl) (Option.some_get h).symm)⟩

/-- `pick` at a type other than `general` is `gatherColumn`'s answer, which exists where the index's
    count fits a `USize`. -/
theorem pick_eq_gather {t : QAtomicType} (hg : t ≠ .general) (c : (n : USize) × Arr t n) (i : ByteArray)
    (hl : len i < USize.size) :
    ∃ e, gatherColumn t c.1 c.2.enc (len i).toUSize (.bytes i) = some e ∧
      (pick t c i).2.part = ((len i).toUSize, e) := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
    (KernelWF.gatherColumn_isSome c.2.wf hg (m := (len i).toUSize) i
      (by rw [USize.toNat_ofNat_of_lt' hl]; exact Nat.div_mul_le_self _ _))
  refine ⟨e, he, ?_⟩
  unfold pick; rw [dif_neg hg]; simp only [need]; rw [dif_pos hl]
  exact congrArg ((len i).toUSize, ·) (Option.some_inj.1 ((Option.some_get _).trans he))

/-- `pick` answers one row an index long: `gatherColumn` at `len i`, a general list's `longRows`. -/
theorem pick_len (t : QAtomicType) (c : (n : USize) × Arr t n) (i : ByteArray) (hl : len i < USize.size) :
    (pick t c i).1.toNat = len i := by
  by_cases hg : t = .general
  · subst hg
    have hs : ((longRows i).map fun p => (gens c.2)[p]?.getD (QLean.Eval.fillOf (gens c.2))).size = len i := by
      simp [longRows, len]
    simp only [pick, genCol, need, dif_pos (hs ▸ hl), dite_true]
    exact (USize.toNat_ofNat_of_lt' (hs ▸ hl)).trans hs
  · simp only [pick, dif_neg hg, need]; rw [dif_pos hl]; exact USize.toNat_ofNat_of_lt' hl

/-- No element of `t`: `Enc.ofAtoms` of nothing, which picks the type's own constructor. -/
def empty (t : QAtomicType) : (n : USize) × Arr t n :=
  if h : t = .general then h ▸ genCol #[] else
    ⟨0, Arr.mk ((Enc.ofAtoms t #[] h).get (Column.ofAtoms_isSome h (by simp)))
      (Column.ofAtoms_WF (by simp) (Option.some_get _).symm (Nat.lt_of_lt_of_le (by decide) USize.le_size))⟩

theorem empty_len (t : QAtomicType) : (empty t).1 = 0 := by
  by_cases h : t = .general
  · subst h; show (genCol #[]).1 = 0; simp only [genCol, need]
    rw [dif_pos (show (#[] : Array QValue).size < USize.size from Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    rfl
  · simp [empty, h]

/-- `raze` of parts of one type: `razeColumn`, which interns a symbol part to meet an interned one
    and decodes an encoded part to meet a dense one. A general list is `Array.append`; no part is `empty t`. -/
def raze (t : QAtomicType) (cs : Array ((n : USize) × Arr t n)) : (n : USize) × Arr t n :=
  if h0 : cs.size = 0 then empty t else
  if hg : t = .general then by subst hg; exact genCol (cs.foldl (fun xs c => xs ++ gens c.2) #[]) else
  if h1 : cs.size = 1 then cs[0] else
  let ps : Array (USize × Enc) := cs.map (·.2.part)
  need (ps.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0 < USize.size)
    (fun _ => s!"raze: {ps.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0} elements do not fit a USize")
    (fun _ => blankCol t) fun hb =>
    have hw : ∀ c ∈ ps, Enc.WF t c.1 c.2 := fun c hc => by
      obtain ⟨x, -, rfl⟩ := Array.mem_map.1 hc; exact x.2.wf
    have hs := KernelWF.razeColumn_isSome (by simpa [ps] using h0) hg hw hb
    -- the answer itself, at the count `razeColumn_count` proves, so `raze_len` reads it off
    ⟨(ps.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize, ⟨(razeColumn t ps).get hs, by
      obtain ⟨n, e, he, hwf⟩ := KernelWF.razeColumn_wf hw hb (Option.some_get hs).symm
      have hn := KernelWF.razeColumn_count hw hb (by rw [← he]; exact (Option.some_get hs).symm)
      have hn' : n = (ps.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize :=
        USize.toNat_inj.1 (by rw [hn, USize.toNat_ofNat_of_lt' hb])
      rw [he]; subst hn'; exact ⟨rfl, rfl, hwf⟩⟩⟩

/-- A general list's boxed elements are its count. -/
theorem gens_size {n : USize} (x : Arr .general n) : (gens x).size = n.toNat := by
  obtain ⟨xs, he, hs⟩ := KernelWF.general_cases x.wf
  rw [show gens x = xs from Option.some_inj.1 ((Option.some_get _).trans (by simp [he])), hs]

/-- **`raze` counts the sum of its parts' counts**, on every branch, where that sum fits a `USize`. -/
theorem raze_len (t : QAtomicType) (cs : Array ((n : USize) × Arr t n))
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) :
    (raze t cs).1.toNat = (cs.toList.map (·.1.toNat)).sum := by
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0; simp [empty_len]
  rw [dif_neg (by simpa using h0)]
  by_cases hg : t = .general
  · subst hg
    simp only [dif_pos, List.foldl_toArray']
    have key : ∀ (l : List ((n : USize) × Arr .general n)) (acc : Array QValue),
        (l.foldl (fun xs c => xs ++ gens c.2) acc).size = acc.size + (l.map (·.1.toNat)).sum := by
      intro l; induction l with
      | nil => simp
      | cons c l ih => intro acc; simp [ih, gens_size, Nat.add_assoc]
    have hf : (l.foldl (fun xs c => xs ++ gens c.2) #[]).size < USize.size := by
      rw [key]; simpa using hN
    simp only [genCol, need, dif_pos hf]
    rw [USize.toNat_ofNat_of_lt' hf, key]; simp
  rw [dif_neg hg]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr t n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 =
      (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk]; exact hN
  simp only [need, dif_pos hf]
  rw [USize.toNat_ofNat_of_lt' hf, hk]

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
def rangeOffsets {p : Nat} (a : QAtomicType) (cs : Vector (USize × Enc) p) (total : Nat) : Option (Vector Code p) :=
  if !(orderKind a == some .i64 && Column.encodes a) then none else
  let bound (op : Coc.Over) (c : USize × Enc) : Option Int64 := match c.2 with
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
  let packed (n : USize) : ByteArray × USize → Option Code
    | (ids, bad) => if bad != n then none else some ⟨w, n, card, ids⟩
  -- a part's count is its header's: a dense part holds `c.1` longs (`Enc.WF`)
  let part (c : USize × Enc) : Option Code := match c.2 with
    | .foR md pk => (if base == 0 then some (md, pk) else Ew.foRShift false (-base) md pk c.1).bind fun (md, pk) =>
        packed c.1 (enumIdsFoR c.1 card.toUSize (card - 1).toUSize w.toUSize md pk)
    | .bytes b =>
      let b := if base == 0 then b else Kernel.Ew.val Ew.add Ew.i64 Ew.va nul b (one (-base).toUInt64) c.1
      packed c.1 (enumIds c.1 card.toUSize (card - 1).toUSize w.toUSize b)
    | _ => none
  cs.mapM part

/-- Joint codes of the parts `cs`, one `Code` per part, in one code space:
    - `bits`: each part is its own code, a bit wide, order-preserving;
    - `foR` or dense of a long type: the offsets from the joint least element (`rangeOffsets`), order-preserving;
    - `enum`, and `syms` interned by `razeColumn`/`Column.intern`: the joint dictionary's ids at their lane;
    - anything else: one coding pass over the `raze` (`groupIdsColumn`: ids by first appearance, at any
      encoding), read at the width they are packed at (`Code.ofIds`). A general list is `findList` of
      the join against itself, its positions packed. -/
def codes {p : Nat} (t : QAtomicType) (cs : Vector ((n : USize) × Arr t n) p) : Vector Code p :=
  if hg : t = .general then by
    subst hg
    exact let all := gens (raze .general cs.toArray).2; (pack all.size (findList all all)).cut (cs.map (·.1))
  else
  match cs.mapM (fun c => match c.2.enc with | .bits b => some (⟨1, c.1, 2, b⟩ : Code) | _ => none) with
  | some bs => bs
  | none =>
  let ns := cs.map (·.1)
  let total := ns.foldl (fun s n => s + n.toNat) 0
  match rangeOffsets t (cs.map (·.2.part)) total with
  | some os => os
  | none =>
  let x := raze t cs.toArray
  -- `intern` rewrites only a `syms` payload, and always to `enum`: past this branch it is `x`'s own
  match hi : Column.intern x.2.enc with
  | .enum _ dof ids => (Code.ofLane (Column.idWidth dof) x.1 (dof.size - 1) ids).cut ns
  -- every other constructor by name, so `hi` refutes `groupIdsColumn`'s interned-dictionary premise
  | .bytes _ | .bits _ | .syms .. | .foR .. | .alp .. | .gen _ =>
    let (gid, fs) := (groupIdsColumn t x.1 x.2.enc).get
      (KernelWF.groupIdsColumn_isSome hg x.2.wf fun _ _ _ he => Enc.noConfusion (hi.symm.trans he))
    (Code.ofIds (len fs) x.1 gid).cut ns

/-- A long column's dense payload, which always answers (`longBytes_isSome`). -/
def longsOf {n : USize} (x : Arr .long n) : ByteArray := (longBytes n x.enc).get (longBytes_isSome x)

/-- A long payload as a column of `len b` rows: `b` itself, its trailing bytes past the last long cut; it
    runs where `len b` fits a `USize`. -/
def longCol (b : ByteArray) : Arr .long (len b).toUSize :=
  need (len b < USize.size) (fun _ => s!"longCol: {len b} longs do not fit a USize")
    (fun _ => Arr.mk (Enc.blank .long _) (Enc.blank_WF .long _)) fun h =>
  Arr.mk (.bytes (b.extract 0 (8 * len b))) (by
    simp only [Enc.WF, QAtomicType.width, USize.toNat_ofNat_of_lt' h]
    simp [len, ByteArray.size_extract]; omega)

/-- The slices `[lo i, hi i)` of a flat payload of `m` values clamped to `[0, m]`, as `Vals.row` reads
    them: each clamped start and the slice's count, `Ew.val` lesser/greater. -/
def slices (m : Nat) (lo hi : ByteArray) : ByteArray × ByteArray :=
  let n := (len lo).toUSize
  let clamp (b : ByteArray) : ByteArray :=
    Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul b (one m.toUInt64) n) (one 0) n
  let l := clamp lo
  (l, sub (Kernel.Ew.val Ew.greater Ew.i64 Ew.vv nul (clamp hi) l n) l)

/-! ## A side's payloads: one count per side, each step column by column -/

/-- A side `A` at its own count: one count for every column of the side, as a relation holds it. -/
@[reducible] def Part (A : Obj) : Type := (n : USize) × Vals A n

/-- A count `k` read off a payload that equals the `USize` count `m` is `m`. -/
theorem toUSize_eq {k : Nat} {m : USize} (h : k = m.toNat) : k.toUSize = m :=
  USize.toNat_inj.1 ((USize.toNat_ofNat_of_lt' (show k < USize.size from h ▸ m.toBitVec.isLt)).trans h)

/-- One column picked at the index column `i` of `m` rows (`pick_len`). -/
def pickArr (t : QAtomicType) (c : (n : USize) × Arr t n) (i : ByteArray) (m : USize) (h : len i = m.toNat) :
    Arr t m :=
  (show (pick t c i).1 = m from USize.toNat_inj.1
    ((pick_len t c i (show len i < USize.size from h ▸ m.toBitVec.isLt)).trans h)) ▸ (pick t c i).2

/-- A side's columns picked at the index column `i` of `m` rows: an array's `lo` and `hi` and a sum's tags and
    positions picked, their payloads shared whole; `Vals.pick`'s first step at a sum. -/
def _root_.LeetQ.Rel.Vals.pickShared : (A : Obj) → {n : USize} → Vals A n → (i : ByteArray) → (m : USize) →
    len i = m.toNat → Vals A m
  | .atom t, _, x, i, m, h => pickArr t ⟨_, x⟩ i m h
  | .prod a b, _, x, i, m, h => (Vals.pickShared a x.1 i m h, Vals.pickShared b x.2 i m h)
  | .arr _, _, x, i, m, h => ⟨x.1, pickArr .long ⟨_, x.2.1⟩ i m h, pickArr .long ⟨_, x.2.2.1⟩ i m h, x.2.2.2⟩
  | .sum _ _, _, x, i, m, h =>
    ⟨x.1, x.2.1, pickArr .boolean ⟨_, x.2.2.1⟩ i m h, pickArr .long ⟨_, x.2.2.2.1⟩ i m h, x.2.2.2.2.1, x.2.2.2.2.2⟩

/-- No row of one column (`empty_len`). -/
def emptyArr (t : QAtomicType) : Arr t 0 := empty_len t ▸ (empty t).2

/-- No row, column by column (`empty_len`). -/
def _root_.LeetQ.Rel.Vals.empty : (A : Obj) → Vals A 0
  | .atom t => emptyArr t
  | .prod a b => (Vals.empty a, Vals.empty b)
  | .arr b => ⟨0, emptyArr .long, emptyArr .long, Vals.empty b⟩
  | .sum a b => ⟨0, 0, emptyArr .boolean, emptyArr .long, Vals.empty a, Vals.empty b⟩

/-- The first `m` longs of the index column `i`, `m ≤ len i`: `i` itself when it holds `m` (no copy), else
    `extract`. Either way `m` rows (`fit_len`). -/
def fit (m : Nat) (i : ByteArray) : ByteArray := if len i = m then i else i.extract 0 (m * 8)

theorem fit_len {m : Nat} {i : ByteArray} (h : m ≤ len i) : len (fit m i) = m := by
  unfold fit; split
  · assumption
  · simp only [len, ByteArray.size_extract] at h ⊢; omega

/-- The long payload `b` as a column of its first `m` longs, `m ≤ len b` (`fit_len`). -/
def longsN (m : USize) (b : ByteArray) (h : m.toNat ≤ len b) : Arr .long m :=
  toUSize_eq (fit_len h) ▸ longCol (fit m.toNat b)

/-- A map of counted parts that keeps each part's count keeps their sum. -/
theorem sum_mapIdx_fst {α β : USize → Type} (cs : Array ((n : USize) × α n))
    (f : Nat → ((n : USize) × α n) → (n : USize) × β n) (h : ∀ k c, (f k c).1 = c.1) :
    ((cs.mapIdx f).toList.map (·.1.toNat)).sum = (cs.toList.map (·.1.toNat)).sum := by
  congr 1; apply List.ext_getElem <;> simp [h]

theorem sum_map_fst {α β : USize → Type} (cs : Array ((n : USize) × α n)) (f : ((n : USize) × α n) → (n : USize) × β n)
    (h : ∀ c, (f c).1 = c.1) : ((cs.map f).toList.map (·.1.toNat)).sum = (cs.toList.map (·.1.toNat)).sum := by
  simp [Function.comp_def, h]

/-- `Ew.val op` on longs at the count `n`, as a long column of `n` rows (`Ew.val_size`). -/
def valCol {n : USize} (op shape : UInt8) (a b : ByteArray) : Arr .long n :=
  Arr.mk (.bytes (Kernel.Ew.val op Ew.i64 shape nul a b n)) (by
    have hw : Kernel.Ew.width Ew.i64 = 8 := by decide
    simp [Enc.WF, QAtomicType.width, KernelWF.Ew.val_size, hw])

/-- A column of offsets into a payload of `m` values, clamped into `[0, m]` as `slices` reads them, plus the long
    `k`, at its own count: `Ew.val` lesser, greater, add, each at `n`. -/
def shiftArr {n : USize} (x : Arr .long n) (m k : Nat) : Arr .long n :=
  let c := Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul (longsOf x) (one m.toUInt64) n
  valCol Ew.add Ew.va (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul c (one 0) n) (one k.toUInt64)

/-- `til n` as a long column (`tilLongs_wf`). -/
def tilCol (n : USize) : Arr .long n := Arr.mk (.bytes (tilLongs n)) (KernelWF.tilLongs_wf n)

/-- `tilLongs n` holds `n` longs (`tilLongs_wf`). -/
theorem len_tilLongs (n : USize) : len (tilLongs n) = n.toNat := by
  have w := KernelWF.tilLongs_wf n
  simp only [Enc.WF, QAtomicType.width] at w
  simp [len, w]

/-- A boolean column's bitmap: `bits` is the one payload `Enc.WF .boolean` admits. -/
def tagBits {n : USize} (x : Arr .boolean n) : ByteArray :=
  (match x.enc with | .bits b => some b | _ => none).get (by
    have hw := x.wf; revert hw; cases x.enc <;> simp [Enc.WF])

/-- The long `z` as a one-element payload, the scalar operand of `Ew.val … va`. -/
def int (z : Int) : ByteArray := one (Int64.ofInt z).toUInt64

/-- A sum column's positions read as `Vals.row` reads them and moved: each row's position clamped into its
    own side, `[0, p₀ + τ·p₁]`, plus `o₀ + τ·o₁`, `τ` the row's tag as `0`/`1` (`widen`), each pass at `n`. -/
def place {n : USize} {A B : Obj} (x : Vals (.sum A B) n) (p₀ p₁ o₀ o₁ : Int) : Arr .long n :=
  let τ := Kernel.Ew.widen Ew.bits Ew.i64 nul nul (tagBits x.2.2.1) n
  let lin (k₀ k₁ : Int) := Kernel.Ew.val Ew.add Ew.i64 Ew.va nul (Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul τ (int k₁) n) (int k₀) n
  let c := Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul (Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (longsOf x.2.2.2.1) (lin p₀ p₁) n) (int 0) n
  valCol Ew.add Ew.vv c (lin o₀ o₁)

/-- A side's columns picked at the index column `i`, `len i` rows each, every payload holding only the cells
    the picked rows refer to, so no op that picks rows (`Rel.rows`, `≫`, `nub`, `∪`) carries a dead cell on:
    - an array: each row's clamped slice gathered contiguous (`expand` of the counts, as `mem`), the rows
      laid one after another (`sums`); a row picked twice holds its own copy;
    - a sum: each row's clamped position in its own side (`place`) gathered per side (`whereBits` of the tags),
      the row's new position its rank among the rows of its side (`sums` of the tags);
    - the payloads picked by `Vals.pick` itself, so a nested array or sum is compacted the same way.
    The new offsets' and payloads' counts are reported by `sums`, `expand`, `whereBits`: one `need` on them. -/
def _root_.LeetQ.Rel.Vals.pick : (A : Obj) → {n : USize} → Vals A n → (i : ByteArray) → (m : USize) →
    len i = m.toNat → Vals A m
  | .atom t, _, x, i, m, h => pickArr t ⟨_, x⟩ i m h
  | .prod a b, _, x, i, m, h => (Vals.pick a x.1 i m h, Vals.pick b x.2 i m h)
  | .arr b, _, x, i, m, h =>
    let s := slices x.1.toNat (longsOf (pickArr .long ⟨_, x.2.1⟩ i m h)) (longsOf (pickArr .long ⟨_, x.2.2.1⟩ i m h))
    let e := expand s.2
    let hi := sums s.2
    let ix := add (gather 8 s.1 e.1) e.2
    need (len hi = m.toNat ∧ len ix < USize.size)
      (fun _ => s!"Vals.pick: {len hi} offsets for {m} rows, or {len ix} values past a USize")
      (fun _ => ⟨0, Arr.mk (Enc.blank .long m) (Enc.blank_WF .long m), Arr.mk (Enc.blank .long m) (Enc.blank_WF .long m),
        Vals.empty b⟩) fun hk =>
    ⟨(len ix).toUSize, valCol Ew.sub Ew.vv hi s.2, toUSize_eq hk.1 ▸ longCol hi,
      Vals.pick b x.2.2.2 ix _ (USize.toNat_ofNat_of_lt' hk.2).symm⟩
  | .sum a b, _, x, i, m, h =>
    let y := Vals.pickShared (.sum a b) x i m h
    let tb := tagBits y.2.2.1
    let τ := Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m
    -- the rows of the other side before each row, then of its own: `inr` ones `sums τ - τ`, `inl` ones the rest
    let rr := sub (sums τ) τ
    let rl := sub (tilLongs m) rr
    let p := longsOf (place y ((y.1.toNat : Int) - 1) ((y.2.1.toNat : Int) - y.1.toNat) 0 0)
    let il := gather 8 p (whereBits m (Ew.notBits m tb))
    let ir := gather 8 p (whereBits m tb)
    need (len il < USize.size ∧ len ir < USize.size)
      (fun _ => s!"Vals.pick: {len il} and {len ir} values past a USize")
      (fun _ => ⟨0, 0, y.2.2.1, Arr.mk (Enc.blank .long m) (Enc.blank_WF .long m), Vals.empty a, Vals.empty b⟩) fun hk =>
    ⟨(len il).toUSize, (len ir).toUSize, y.2.2.1, valCol Ew.add Ew.vv rl (Kernel.Ew.val Ew.mul Ew.i64 Ew.vv nul τ (sub rr rl) m),
      Vals.pick a y.2.2.2.2.1 il _ (USize.toNat_ofNat_of_lt' hk.1).symm,
      Vals.pick b y.2.2.2.2.2 ir _ (USize.toNat_ofNat_of_lt' hk.2).symm⟩

/-- A side's columns picked at the first `m` longs of `i`. -/
def _root_.LeetQ.Rel.Vals.pickN (A : Obj) {n : USize} (x : Vals A n) (i : ByteArray) (m : USize) (h : m.toNat ≤ len i) :
    Vals A m :=
  Vals.pick A x (fit m.toNat i) m (fit_len h)

/-- A side picked at the index column `i`, at the count `len i` where it fits a `USize`. -/
def _root_.LeetQ.Rel.Vals.pickPart (A : Obj) {n : USize} (x : Vals A n) (i : ByteArray) : Part A :=
  need (len i < USize.size) (fun _ => s!"pick: {len i} rows do not fit a USize") (fun _ => ⟨0, Vals.empty A⟩)
    fun h => ⟨(len i).toUSize, Vals.pick A x i _ (USize.toNat_ofNat_of_lt' h).symm⟩

/-- `x` with every payload holding only the cells its rows refer to: `Vals.pick` at `til n` (`len_tilLongs`). -/
def _root_.LeetQ.Rel.Vals.compact (A : Obj) {n : USize} (x : Vals A n) : Vals A n :=
  Vals.pick A x (tilLongs n) n (len_tilLongs n)

/-- The sum column `x` with a value behind every row: where a row is tagged to a side of no values,
    `Vals.compact`, whose gather past that side reads its null as `Vals.row` does; else `x` itself. -/
def _root_.LeetQ.Rel.Vals.held {A B : Obj} {n : USize} (x : Vals (.sum A B) n) : Vals (.sum A B) n :=
  let r := len (whereBits n (tagBits x.2.2.1))
  if (x.1 = 0 ∧ r < n.toNat) ∨ (x.2.1 = 0 ∧ 0 < r) then Vals.compact (.sum A B) x else x

/-- `raze` at the parts' summed count `S`, which fits a `USize` (`raze_len`). -/
def razeTo (t : QAtomicType) (cs : Array ((n : USize) × Arr t n)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hN : S < USize.size) : Arr t S.toUSize :=
  toUSize_eq ((raze_len t cs (by rw [hs]; exact hN)).trans hs).symm ▸ (Alg.raze t cs).2

/-- `raze` column by column, at the parts' summed count (`raze_len`). An array's flat payloads are razed, and
    each part's `lo`, `hi` move past the flat values of the parts before it (`shiftArr`), so every row still
    slices its own values. A sum's tags are razed, its two payloads razed side by side, and each row's
    position clamped into its own side and moved past that side's values in the parts before it (`place`),
    so every row still reads its own value. The counts of the rows (`hN`) and of each nested payload (a `need`)
    fit a `USize`. -/
def _root_.LeetQ.Rel.Obj.raze : (A : Obj) → (cs : Array (Part A)) →
    (cs.toList.map fun c : Part A => c.1.toNat).sum < USize.size →
    Vals A (cs.toList.map fun c : Part A => c.1.toNat).sum.toUSize
  | .atom t, cs, hN => razeTo t cs rfl hN
  | .prod a b, cs, hN =>
    (sum_map_fst cs (fun c => (⟨c.1, c.2.1⟩ : Part a)) (fun _ => rfl) ▸ Obj.raze a (cs.map fun c => ⟨c.1, c.2.1⟩)
        (by rw [sum_map_fst cs (fun c => (⟨c.1, c.2.1⟩ : Part a)) (fun _ => rfl)]; exact hN),
      sum_map_fst cs (fun c => (⟨c.1, c.2.2⟩ : Part b)) (fun _ => rfl) ▸ Obj.raze b (cs.map fun c => ⟨c.1, c.2.2⟩)
        (by rw [sum_map_fst cs (fun c => (⟨c.1, c.2.2⟩ : Part b)) (fun _ => rfl)]; exact hN))
  | .arr b, cs, hN =>
    let ms := cs.map (·.2.1.toNat)
    -- the parts are few (two or three), so no running sum
    -- each part's offsets clamped into its own payload first, so a row out of range reads no other part's values
    let mv (k m : Nat) (c : (n : USize) × Arr .long n) : (n : USize) × Arr .long n :=
      ⟨c.1, shiftArr c.2 m ((ms.extract 0 k).foldl (· + ·) 0)⟩
    let lo (k : Nat) (c : Part (.arr b)) := mv k c.2.1.toNat ⟨c.1, c.2.2.1⟩
    let hi (k : Nat) (c : Part (.arr b)) := mv k c.2.1.toNat ⟨c.1, c.2.2.2.1⟩
    let fs := cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)
    need ((fs.toList.map (·.1.toNat)).sum < USize.size)
      (fun _ => s!"Obj.raze: {(fs.toList.map (·.1.toNat)).sum} values do not fit a USize")
      (fun _ => ⟨0, Arr.mk (Enc.blank .long _) (Enc.blank_WF .long _), Arr.mk (Enc.blank .long _) (Enc.blank_WF .long _),
        Vals.empty b⟩) fun hf =>
    ⟨_, razeTo .long (cs.mapIdx lo) (sum_mapIdx_fst cs lo fun _ _ => rfl) hN,
      razeTo .long (cs.mapIdx hi) (sum_mapIdx_fst cs hi fun _ _ => rfl) hN, Obj.raze b fs hf⟩
  | .sum a b, cs₀, hN =>
    -- a row of a side of no values is given its value first (`held`): no other part's value lies past it
    let held (c : Part (.sum a b)) : Part (.sum a b) := ⟨c.1, c.2.held⟩
    let cs := cs₀.map held
    have hc : (cs.toList.map (·.1.toNat)).sum = (cs₀.toList.map (·.1.toNat)).sum := sum_map_fst cs₀ held fun _ => rfl
    -- the parts are few (two or three), so no running sum
    let before (f : Part (.sum a b) → Nat) (k : Nat) : Nat := ((cs.map f).extract 0 k).foldl (· + ·) 0
    let ix (k : Nat) (c : Part (.sum a b)) : (n : USize) × Arr .long n :=
      let dl := before (·.2.1.toNat) k; let dr := before (·.2.2.1.toNat) k
      ⟨c.1, place c.2 ((c.2.1.toNat : Int) - 1) ((c.2.2.1.toNat : Int) - c.2.1.toNat) dl ((dr : Int) - dl)⟩
    let tg (c : Part (.sum a b)) : (n : USize) × Arr .boolean n := ⟨c.1, c.2.2.2.1⟩
    let ls := cs.map fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)
    let rs := cs.map fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b)
    need ((ls.toList.map (·.1.toNat)).sum < USize.size ∧ (rs.toList.map (·.1.toNat)).sum < USize.size)
      (fun _ => s!"Obj.raze: {(ls.toList.map (·.1.toNat)).sum} and {(rs.toList.map (·.1.toNat)).sum} values do not fit a USize")
      (fun _ => ⟨0, 0, Arr.mk (Enc.blank .boolean _) (Enc.blank_WF .boolean _), Arr.mk (Enc.blank .long _) (Enc.blank_WF .long _),
        Vals.empty a, Vals.empty b⟩) fun hf =>
    ⟨_, _, razeTo .boolean (cs.map tg) ((sum_map_fst cs tg fun _ => rfl).trans hc) hN,
      razeTo .long (cs.mapIdx ix) ((sum_mapIdx_fst cs ix fun _ _ => rfl).trans hc) hN, Obj.raze a ls hf.1, Obj.raze b rs hf.2⟩

/-- The rows of `R` at the index column `i`: `len i` pairs, where that count fits a `USize`. -/
def _root_.LeetQ.Rel.Rel.rows {k v : Obj} (R : Rel k v) (i : ByteArray) : Rel k v :=
  need (len i < USize.size) (fun _ => s!"rows: {len i} rows do not fit a USize") (fun _ => ⟨0, Vals.empty k, Vals.empty v⟩)
    fun h => ⟨(len i).toUSize, Vals.pick k R.key i _ (USize.toNat_ofNat_of_lt' h).symm,
      Vals.pick v R.val i _ (USize.toNat_ofNat_of_lt' h).symm⟩

/-! ## The composite steps, named once -/

/-- A code's payload as the column `composeKey` reads: a bit a boolean bitmap, a byte layout the
    dense column of that width, a `2`/`4`-bit lane an interned column of `card` ids, read by `eIds`
    where they lie; `composeKey` reads no dictionary, so it holds `card` empty symbols. -/
def Code.column (c : Code) : Option (QAtomicType × (USize × Enc)) :=
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
      | some ka, some kb => Order.groupIdsPair ka kb a.n a.b b.b
      | _, _ => Order.groupIdsPairIds a.w.toUSize b.w.toUSize a.n a.b b.b
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

/-- Sequence ids: segment `j` of the codes `vc` is `vc[o[j] .. o[j+1])` for the `g + 1` offsets `o`; equal
    SEQUENCES (order and repeats counted) get equal ids, numbered by first occurrence: `rankSlices`. -/
def sliceIds (vc : Code) (o : ByteArray) : ByteArray :=
  let ids := Order.rankSlices vc.w.toUSize vc.b o
  -- `rankSlices` declines (answers empty) on offsets out of order or past its payload: the run stops there
  need (ids.size = 8 * (len o - 1)) (fun _ => s!"sliceIds: rankSlices declined {len o - 1} offsets")
    (fun _ => ids) fun _ => ids

/-- Joint codes of a side's parts, one code per part: an atom's `codes`; a product's `tuples` of its
    columns' codes, so equal tuples are equal codes exactly when every column is; an array's `sliceIds` of
    its elements' joint codes, each row's slice gathered contiguous (`expand` of the clamped counts), so
    equal arrays (equal length, equal elements position by position) are equal codes exactly. -/
def _root_.LeetQ.Rel.Obj.codes : (A : Obj) → {p : Nat} → Vector (Part A) p → Vector Code p
  | .atom t, _, cs => Alg.codes t cs
  | .prod a b, _, cs =>
    tuples (Obj.codes a (cs.map fun c => (⟨c.1, c.2.1⟩ : Part a))) #[Obj.codes b (cs.map fun c => (⟨c.1, c.2.2⟩ : Part b))]
  | .arr b, _, cs =>
    let ec := Obj.codes b (cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b))
    let sl := cs.map fun c => slices c.2.1.toNat (longsOf c.2.2.1) (longsOf c.2.2.2.1)
    let seq := Code.cat (Vector.zipWith (fun e s => let x := expand s.2; e.gather (add (gather 8 s.1 x.1) x.2)) ec sl).toArray
    let ns := cs.map (·.1)
    let o := concatBytes #[one 0, sums (concatBytes (sl.map (·.2)).toArray)]
    (pack (ns.foldl (fun s n => s + n.toNat) 0) (sliceIds seq o)).cut ns
  | .sum a b, _, cs₀ =>
    -- a row of a side of no values is given its value first (`held`), so no row reads a miss
    let cs := cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))
    -- each side's payloads in one code space; a row gathers its own side's code at its clamped position
    -- (`place`), and the other side's at a position moved past that side, a miss read as code `0`; the
    -- tuple (tag, left, right) is then equal exactly where the tags and the own side's values are
    let lc := Obj.codes a (cs.map fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a))
    let rc := Obj.codes b (cs.map fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b))
    let gl := Vector.zipWith (fun c k => k.gather (longsOf (place c.2 ((c.2.1.toNat : Int) - 1) 0 0 c.2.1.toNat))) cs lc
    let gr := Vector.zipWith (fun c k => k.gather
      (longsOf (place c.2 ((c.2.2.1.toNat : Int) - 1) 0 c.2.2.1.toNat (-(c.2.2.1.toNat : Int))))) cs rc
    tuples (cs.map fun c => (⟨1, c.1, 2, tagBits c.2.2.2.1⟩ : Code)) #[gl, gr]

/-- The permutation `p` refined stably by the values of `A` at its rows, ascending: `gradeColumn` of each
    atom (a symbol by its string, so the order is the value's, the same in every call), the last component
    first so a product sorts lexicographically. Where no kernel orders the values — a general list, an
    array — by their codes: an order of this call only. -/
def _root_.LeetQ.Rel.Obj.sortBy : (A : Obj) → {n : USize} → Vals A n → ByteArray → ByteArray
  | .atom t, _, c, p =>
    let x := Alg.pick t ⟨_, c⟩ p
    match gradeColumn t false x.1 x.2.enc with
    | some (.bytes g) => gather 8 p g
    | _ => gather 8 p (codes t #v[x])[0].grade
  | .prod a b, _, c, p => Obj.sortBy a c.1 (Obj.sortBy b c.2 p)
  | .arr b, _, c, p => gather 8 p (Obj.codes (.arr b) #v[Vals.pickPart (.arr b) c p])[0].grade
  | .sum a b, _, c, p => gather 8 p (Obj.codes (.sum a b) #v[Vals.pickPart (.sum a b) c p])[0].grade

/-- `|R|` of several relations of one type in one code space, one code per relation. -/
def pairs {k v : Obj} {p : Nat} (ds : Vector (Rel k v) p) : Vector Code p :=
  tuples (k.codes (ds.map fun R => ⟨R.n, R.key⟩)) #[v.codes (ds.map fun R => ⟨R.n, R.val⟩)]

/-- `R` with each pair once: the first row of each class of `|R|`. -/
def _root_.LeetQ.Rel.Rel.nub {k v : Obj} (R : Rel k v) : Rel k v :=
  R.rows (tuples.tupleIds (k.codes #v[⟨_, R.key⟩])[0] #[(v.codes #v[⟨_, R.val⟩])[0]]).2

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

/-- Any `Ew.val` on longs at the left's count answers at most that count (`Ew.val_size`). -/
theorem val_len_le (op mode : UInt8) (a b : ByteArray) :
    len (Kernel.Ew.val op Ew.i64 mode nul a b (len a).toUSize) ≤ len a := by
  have hw : Kernel.Ew.width Ew.i64 = 8 := by decide
  have hu : (a.size / 8).toUSize.toNat ≤ a.size / 8 := by simp only [Nat.toUSize]; exact Nat.mod_le _ _
  simp only [len, KernelWF.Ew.val_size, hw]; omega

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
def anti (x y : Code) : ByteArray := whereBits x.n (Ew.notBits x.n (x.member y))

/-- The rows of a code column `c` cut into one segment per distinct code: the permutation `p` that
    makes each code's rows contiguous (`grade` of its `groupIds`), the `g + 1` offsets of the
    segments in that order (`runStarts`), and each segment's first row in `c`. -/
def segments (c : Code) : ByteArray × ByteArray × ByteArray :=
  let (gid, firsts) := c.groupIds
  let g := Code.ofIds (len firsts) c.n gid
  let p := g.grade
  (p, (g.gather p).runStarts, firsts)

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
    | some k => Order.groupIdsPair .i64 k n (gather 8 seg p) (vc.gather p).b
    | none => Order.groupIdsPairIds 64 vc.w.toUSize n (gather 8 seg p) (vc.gather p).b
  let ids := Order.rankSlices vc.w.toUSize (vc.gather (gather 8 p fs)).b
    (gather 8 (concatBytes #[groupLongs n (q, fs), one (len fs).toUInt64]) o)
  -- `rankSlices` declines (answers empty) on offsets out of order or past its payload — starts that do not
  -- ascend: the run stops there; the model is `len s` zero longs
  need (ids.size = 8 * len s) (fun _ => s!"setIds: rankSlices declined {len s} starts (not ascending?)")
    (fun _ => ByteArray.mk (Array.replicate (8 * len s) 0)) fun _ => ids

/-- `setIds` answers one long per start: the kernel's by its check, the stopped run's model by its size. -/
theorem setIds_size (vc : Code) (s : ByteArray) : (setIds vc s).size = 8 * len s := by
  unfold setIds
  split <;> (try dsimp only) <;> simp only [need] <;> split <;> first | assumption | simp [stop, ByteArray.size]

/-- `setIds` as a long column of `m = len s` rows (`setIds_size`). -/
def setIdCol (vc : Code) (s : ByteArray) (m : USize) (h : len s = m.toNat) : Arr .long m :=
  Arr.mk (.bytes (setIds vc s)) (by simp [Enc.WF, QAtomicType.width, setIds_size, ← h]; simp [len]; omega)

/-! ## Laws: codes are faithful, and each operator means its relation -/

section Laws

open QLean.Verify (firstsOf)

/-- An `Arr`'s element `i` depends on its payload and on `i`'s value alone. -/
theorem Arr.get_congr {t : QAtomicType} {n m : USize} {a : Arr t n} {b : Arr t m} (hc : a.part = b.part)
    {i : Fin n.toNat} {j : Fin m.toNat}
    (hij : i.1 = j.1) : a.get i = b.get j := by
  obtain ⟨rfl, he⟩ := Prod.mk.inj hc
  obtain ⟨v, hv⟩ := a; obtain ⟨w, hw⟩ := b
  cases v <;> try exact hv.elim
  cases w <;> try exact hw.elim
  obtain ⟨i, _⟩ := i; obtain ⟨j, _⟩ := j
  simp only [Arr.enc] at he hij; subst he hij; cases t <;> rfl

/-- Two `Arr`s over one part have one length: the part carries it. -/
theorem Arr.n_congr {t : QAtomicType} {n m : USize} {a : Arr t n} {b : Arr t m} (hc : a.part = b.part) : n = m :=
  (Prod.mk.inj hc).1

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
theorem groupIds_long_faithful {m : USize} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b)
    (i j : Fin m.toNat) :
    Column.idAt (Order.groupIds .i64 m b).1
        (Column.idWidthOf (firstsOf (Order.keyAt .i64 b) m.toNat).length) i =
      Column.idAt (Order.groupIds .i64 m b).1
        (Column.idWidthOf (firstsOf (Order.keyAt .i64 b) m.toNat).length) j ↔ x.get i = x.get j := by
  have hs := Arr.n_long_bytes x hc
  have hmin : min m.toNat (Scan.Kind.avail .i64 b) = m.toNat := by
    simp [Scan.Kind.avail, Scan.Kind.width, hs]
  have e := groupIds_faithful .i64 m b (i := i.1) (j := j.1) (by omega) (by omega)
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
    simp only [Ew.elem, hw, Nat.zero_mul]; exact bitsAt_one c.toUInt64
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
