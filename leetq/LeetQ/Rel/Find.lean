/-
  where, distinct, find, in and bin on the RelRep core. Each verb hands its operand columns to the
  qlean kernel that owns the encoding (`whereColumn`, `distinctColumn`, `findColumn`, `memberColumn`,
  `binColumn`, which dispatch over `bits`/`syms`/`enum`/`bytes`/`foR` and the `s` attribute), after
  the small-range test: a long-class `foR` haystack with no null whose `Coc.range` is at most
  `4·max(2¹⁶, n)` wide is answered by direct address, no hash. A position answer is a new `Rel` keyed
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
import QLean.Verify.Elementwise
import QLean.Verify.Encoding
import QLean.Verify.EwEnc
import QLean.Verify.Ids
import QLean.Dep.Table
import QLean.Dep.Monadic
import LeetQ.Rel.KernelWF.Search

namespace LeetQ.Rel.Find

open QLean QLean.Dep QLean.Kernel

/-! ## Wrapping an answer -/

/-- A vector header's count; the `0` is unreachable where `arrs` reads it, under its witness. -/
def count : QValue → Nat
  | .vector _ m _ _ => m
  | _ => 0

/-- A kernel's vector `v`, which the kernel's `_wf` theorem says is `m` well-formed elements of `t`. -/
def arr {t : QAtomicType} {m : Nat} (v : QValue) (h : ∃ e, v = .vector t m e none ∧ Enc.WF t m e) : Arr t m :=
  ⟨v, by obtain ⟨e, rfl, hw⟩ := h; exact ⟨rfl, rfl, hw⟩⟩

/-- A kernel's vector of the count it chose, under the producer's attribute `u` (§2.4). -/
def arrs {t : QAtomicType} (v : QValue) (h : ∃ m e, v = .vector t m e none ∧ Enc.WF t m e) (u : UInt8) :
    (m : Nat) × Arr t m :=
  ⟨count v, (arr v (by obtain ⟨m, e, rfl, hw⟩ := h; exact ⟨e, rfl, hw⟩)).markIf u⟩

/-- A payload a pass outside the kernels computed: its vector where `Enc.WF` holds of it, else `alt`, the
    kernels' answer to the same question. -/
def orElse {t : QAtomicType} {m : Nat} (e : Enc) (alt : Unit → Arr t m) : Arr t m :=
  if h : Enc.WF t m e then Arr.mk e h else alt ()

/-- The column of `f` over `vs`, through `Enc.ofAtoms`, which answers every count: the kernel-free answer. -/
def atomsOf {α : Type} {m : Nat} (t : QAtomicType) (hg : t ≠ .general) (f : α → QAtom) (hf : ∀ v, (f v).type = t)
    (vs : List α) (hm : vs.length = m) : Arr t m :=
  have ha : ∀ a ∈ (vs.map f).toArray, a.type = t := fun a h => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 (by simpa using h); exact hf v
  Arr.mk ((Enc.ofAtoms t (vs.map f).toArray hg).get (Column.ofAtoms_isSome hg ha))
    (by simpa [hm] using Column.ofAtoms_WF ha (Option.some_get (Column.ofAtoms_isSome hg ha)).symm)

/-- A long column's dense payload: `Enc.WF .long` admits only `bytes` and `foR`, both of which decode. -/
def denseOf {nx : Nat} (x : Arr .long nx) : ByteArray :=
  (Enc.bytesOf .long nx x.enc).get (KernelWF.bytesOf_isSome (by decide) (by decide) x.wf)

theorem arr_get {t t' : QAtomicType} {m m' : Nat} {o : Option QValue} {hs : o.isSome}
    {h : ∃ e, o.get hs = .vector t m e none ∧ Enc.WF t m e} {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : o = some (.vector t' m' e c)) : (arr (o.get hs) h).enc = e := by subst ho; rfl

theorem arrs_get {t t' : QAtomicType} {m : Nat} {o : Option QValue} {hs : o.isSome}
    {h : ∃ m e, o.get hs = .vector t m e none ∧ Enc.WF t m e} {u : UInt8} {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : o = some (.vector t' m e c)) : (arrs (o.get hs) h u).1 = m ∧ (arrs (o.get hs) h u).2.enc = e := by
  subst ho; exact ⟨rfl, Arr.markIf_enc _ _⟩

theorem orElse_enc {t : QAtomicType} {m : Nat} {e : Enc} (hw : Enc.WF t m e) (alt : Unit → Arr t m) :
    (orElse e alt).enc = e := by
  unfold orElse; rw [dif_pos hw]; rfl


/-- A list of `a`s from a vector a kernel wrote: `m` the vector's own count, `attr` the producer's
    attribute (§2.4). -/
def list (a : QAtomicType) (v : QValue) (attr : UInt8 := 0) : Except String ((m : Nat) × Arr a m) :=
  match v with
  | .vector _ m _ _ => do pure ⟨m, (← Arr.of a m v "a list answer").markIf attr⟩
  | _ => .error "a list answer: the kernel answered a non-vector where a vector was due"

/-- An answer per element of an operand of `n` elements; the count is checked, not assumed. -/
def onKey (n : Nat) (a : QAtomicType) (v : QValue) (verb : String) : Except String (Arr a n) :=
  Arr.of a n v verb

/-- A dispatcher's answer; its type and count are `Arr.of`'s to check. -/
def vec (verb : String) : Option QValue → Except String QValue
  | some v => .ok v
  | none => .error s!"{verb}: no qlean kernel claims this operand (q's 'type)"

/-- A dense payload of an operand, or the error naming the verb. -/
def dense (verb : String) (a : QAtomicType) (n : Nat) (e : Enc) : Except String ByteArray :=
  match Enc.bytesOf a n e with
  | some b => .ok b
  | none => .error s!"{verb}: the operand has no dense payload at its type"

theorem list_enc {a t : QAtomicType} {m : Nat} {e : Enc} {ac : Option (UInt8 × IndexCell)} {u : UInt8}
    {nr : Nat} {r : Arr a nr} (h : list a (.vector t m e ac) u = .ok ⟨nr, r⟩) : nr = m ∧ r.enc = e := by
  simp only [list] at h
  cases ho : Arr.of a m (.vector t m e ac) "a list answer" with
  | error _ => simp [ho, bind, Except.bind] at h
  | ok v =>
    simp only [ho, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    cases h
    simp only [Arr.of] at ho; split at ho <;> cases ho
    exact ⟨rfl, by rw [Arr.markIf_enc]; rfl⟩

theorem onKey_enc {n : Nat} {a t : QAtomicType} {m : Nat} {e : Enc} {ac : Option (UInt8 × IndexCell)}
    {s : String} {r : Arr a n} (h : onKey n a (.vector t m e ac) s = .ok r) : r.enc = e := by
  simp only [onKey, Arr.of] at h; split at h
  · cases h; rfl
  · cases h

/-! ## The small-range test and direct address -/

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
    column with block metadata (empty metadata marks an unencoded payload, which the `Coc` kernels do
    not read) that `Coc.range` bounds — non-empty and holding no null — with `max − min ≤ 4·max(2¹⁶, n)`.
    Answers the table, `lo` and the dense haystack. `lo` is then a non-null element (`range_lo_ne`),
    so `sub`, which maps the null to itself, offsets every element from it. -/
def direct (a : QAtomicType) (n : Nat) (e : Enc) : Option (ByteArray × Int64 × ByteArray) := do
  guard (clsOf a == some Ew.i64)
  let .foR md pk := e | none
  guard (!md.isEmpty)
  let (lo, hi) ← Coc.range (← Coc.nullOf a) md pk n.toUSize
  let r := (hi.toInt - lo.toInt).toNat + 1
  guard (r ≤ 4 * max 65536 n)
  let hb ← Enc.bytesOf a n e
  pure (firstTable hb n lo r, lo, hb)

/-! ## The verbs -/

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

/-! ## The verbs

Each answers on every input. A kernel's premise that `Enc.WF` does not give — a type other than a general
list, a count below `USize.size`, a type other than `symbol` for `bin` — is decided in the op; where it fails
the answer is the spec above, under q's `~` (`Carrier.identical`) and order (`Carrier.le`), built by
`Enc.ofAtoms`. A direct-address payload is taken where `Enc.WF` holds of it, else the kernels answer. -/

/-- `&x` on booleans: the positions of the set bits, `whereBits`; sorted (attribute `s`). -/
def «where» {nx : Nat} (x : Arr .boolean nx) : (m : Nat) × Arr .long m :=
  arrs ((whereColumn .boolean nx x.enc).get (KernelWF.whereColumn_isSome x.wf))
    (by obtain ⟨m, b, hv, hw⟩ := KernelWF.whereColumn_wf x.wf (Option.some_get _).symm; exact ⟨m, _, hv, hw⟩) 1

/-- The positions of `x`'s counts below zero, `0N` among them: `&x`'s precondition is that there are none
    (q's 'domain). -/
def negs {nx : Nat} (x : Arr .long nx) : ByteArray :=
  whereBits nx.toUSize (Ew.cmp Ew.lt Ew.i64 Ew.va (denseOf x) (one 0) nx.toUSize)

/-- `&x` on counts none of which is negative: `expand`; sorted (attribute `s`). -/
def whereCounts {nx : Nat} (x : Arr .long nx) (_ : (negs x).size = 0) : (m : Nat) × Arr .long m :=
  let b := (expand (denseOf x)).1
  if hw : Enc.WF .long (b.size / 8) (.bytes b) then ⟨_, (Arr.mk _ hw).markIf 1⟩
  else ⟨_, (atomsOf .long (by decide) QAtom.long (fun _ => rfl) (whereCountsSpec x.toList) rfl).markIf 1⟩

/-- `?x` by the kernels: `distinctColumn`, which answers every type but a general list; that one is
    `distinctSpec` under q's `~`. -/
def distinctK {a : QAtomicType} {nx : Nat} (x : Arr a nx) : (m : Nat) × Arr a m :=
  if hg : a = .general then by
    subst hg
    exact ⟨(@distinctSpec _ ⟨Carrier.identical⟩ x.toList).length, (Arr.mk (.gen (@distinctSpec _ ⟨Carrier.identical⟩ x.toList).toArray)
      (by simp [Enc.WF])).markIf 2⟩
  else arrs ((distinctColumn a nx x.enc).get (KernelWF.distinctColumn_isSome x.wf hg))
    (KernelWF.distinctColumn_wf x.wf (Option.some_get _).symm) 2

/-- `?x`: the first occurrences, in order (attribute `u`). Already unique: the operand itself. Small
    range: the positions where `T[x − lo]` is the position itself, then `x@` those. -/
def distinct {a : QAtomicType} {nx : Nat} (x : Arr a nx) : (m : Nat) × Arr a m :=
  if x.attrCell.map (·.1) == some 2 then ⟨nx, x⟩ else
  match direct a nx x.enc with
  | some (t, lo, hb) =>
    let n := nx.toUSize
    let g := gatherBytes 8 0 hb (whereBits n (Ew.cmp Ew.eq Ew.i64 Ew.vv (probe t nx lo hb) (tilLongs n) n))
    if hw : Enc.WF a (g.size / 8) (.bytes g) then ⟨_, (Arr.mk _ hw).markIf 2⟩ else distinctK x
  | none => distinctK x

/-- `x?y` by the kernels: `findColumn`, at a type other than a general list and a count it indexes by. -/
def findK {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) : Arr .long ny :=
  if h : a ≠ .general ∧ ny < USize.size then
    arr ((findColumn a (x.attrCell.map (·.1) == some 1) nx x.enc y.1).get
      (by rw [y.val_eq]; exact KernelWF.findColumn_isSome x.wf y.wf h.1))
      (KernelWF.findColumn_wf x.wf y.wf h.2 ((congrArg (findColumn a (x.attrCell.map (·.1) == some 1) nx x.enc) y.val_eq).symm.trans (Option.some_get _).symm))
  else atomsOf .long (by decide) QAtom.long (fun _ => rfl) (@findSpec _ ⟨Carrier.identical⟩ x.toList y.toList)
    (by simp [findSpec, Arr.length_toList])

/-- `x?y`: each element of `y`'s first position in `x`, `count x` at a miss; on `y`'s key. -/
def find {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) : Arr .long ny :=
  match direct a nx x.enc with
  | some (t, lo, _) => match Enc.bytesOf a ny y.enc with
    | some nb => orElse (.bytes (probe t nx lo nb)) fun _ => findK x y
    | none => findK x y
  | none => findK x y

/-- `x in y` by the kernels: `memberColumn`, at a type other than a general list and a count it indexes by. -/
def inK {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) : Arr .boolean nx :=
  if h : a ≠ .general ∧ nx < USize.size then
    arr ((memberColumn a (y.attrCell.map (·.1) == some 1) x.1 ny y.enc).get
      (by rw [x.val_eq]; exact KernelWF.memberColumn_isSome x.wf y.wf h.1))
      (KernelWF.memberColumn_wf x.wf y.wf h.2 ((congrArg (memberColumn a (y.attrCell.map (·.1) == some 1) · ny y.enc) x.val_eq).symm.trans (Option.some_get _).symm))
  else atomsOf .boolean (by decide) QAtom.boolean (fun _ => rfl) (@inSpec _ ⟨Carrier.identical⟩ x.toList y.toList)
    (by simp [inSpec, Arr.length_toList])

/-- `x in y`: whether each element of `x` is in `y`; on `x`'s key. -/
def «in» {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) : Arr .boolean nx :=
  match direct a ny y.enc with
  | some (t, lo, _) => match Enc.bytesOf a nx x.enc with
    | some nb => orElse (.bits (Ew.cmp Ew.lt Ew.i64 Ew.va (probe t ny lo nb) (one ny.toUInt64) nx.toUSize))
        fun _ => inK x y
    | none => inK x y
  | none => inK x y

/-- `x bin y`: for each element of `y`, the last position of sorted `x` holding at most it, `-1`
    below all; `binBytes`/`foRBin`/`binBits` by encoding, at a type other than a general list or a symbol
    and a count `binColumn` indexes by. On `y`'s key. -/
def bin {a : QAtomicType} {nx ny : Nat} (x : Arr a nx) (y : Arr a ny) : Arr .long ny :=
  if h : a ≠ .general ∧ a ≠ .symbol ∧ ny < USize.size then
    arr ((binColumn a false nx x.enc y.1).get (by rw [y.val_eq]; exact KernelWF.binColumn_isSome x.wf y.wf h.1))
      (KernelWF.binColumn_wf x.wf y.wf h.2.1 h.2.2 ((congrArg (binColumn a false nx x.enc) y.val_eq).symm.trans (Option.some_get _).symm))
  else atomsOf .long (by decide) QAtom.long (fun _ => rfl)
    (@binSpec _ ⟨fun p q => Table.Carrier.le p q = true⟩ (fun p q => inferInstanceAs (Decidable (Table.Carrier.le p q = true)))
      x.toList y.toList) (by simp [binSpec, Arr.length_toList])

theorem where_enc {nx : Nat} {x : Arr .boolean nx} {m : Nat} {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : whereColumn .boolean nx x.enc = some (.vector .long m e c)) : («where» x).1 = m ∧ («where» x).2.enc = e :=
  arrs_get ho

theorem distinctK_enc {a t : QAtomicType} {nx : Nat} {x : Arr a nx} (hg : a ≠ .general) {m : Nat} {e : Enc}
    {c : Option (UInt8 × IndexCell)} (ho : distinctColumn a nx x.enc = some (.vector t m e c)) :
    (distinctK x).1 = m ∧ (distinctK x).2.enc = e := by
  unfold distinctK; rw [dif_neg hg]; exact arrs_get ho

theorem findK_enc {a t : QAtomicType} {nx ny m : Nat} {x : Arr a nx} {y : Arr a ny} (hg : a ≠ .general)
    (hm : ny < USize.size) {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : findColumn a (x.attrCell.map (·.1) == some 1) nx x.enc y.1 = some (.vector t m e c)) : (findK x y).enc = e := by
  unfold findK; rw [dif_pos ⟨hg, hm⟩]; exact arr_get ho

theorem inK_enc {a t : QAtomicType} {nx ny m : Nat} {x : Arr a nx} {y : Arr a ny} (hg : a ≠ .general)
    (hm : nx < USize.size) {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : memberColumn a (y.attrCell.map (·.1) == some 1) x.1 ny y.enc = some (.vector t m e c)) :
    (inK x y).enc = e := by
  unfold inK; rw [dif_pos ⟨hg, hm⟩]; exact arr_get ho

theorem bin_enc {a t : QAtomicType} {nx ny m : Nat} {x : Arr a nx} {y : Arr a ny} (hg : a ≠ .general)
    (hs : a ≠ .symbol) (hm : ny < USize.size) {e : Enc} {c : Option (UInt8 × IndexCell)}
    (ho : binColumn a false nx x.enc y.1 = some (.vector t m e c)) : (bin x y).enc = e := by
  unfold bin; rw [dif_pos ⟨hg, hs, hm⟩]; exact arr_get ho

/-! ## Laws read off the construction -/

/-- `&x` on booleans is `whereSpec`, from `whereBits_spec`. `nx < USize.size` because `whereBits` takes
    its count as a `USize`. -/
theorem where_toList {nx : Nat} {x : Arr .boolean nx} (hn : nx < USize.size) :
    («where» x).2.toList = whereSpec x.toList := by
  cases he : x.enc with
  | bits bs =>
    have hr := where_enc (x := x) (show whereColumn .boolean nx x.enc = _ by rw [he]; rfl)
    generalize «where» x = R at hr ⊢
    obtain ⟨nr, r⟩ := R
    dsimp only at hr ⊢
    obtain ⟨hs, hj⟩ := QLean.Verify.whereBits_spec nx.toUSize bs
    rw [USize.toNat_ofNat_of_lt' hn] at hs hj
    have hl : nr = ((List.range nx).filter (Column.bitAt bs)).length := by rw [hr.1]; omega
    have hf : (List.range nx).filter (x.toList.getD · false) = (List.range nx).filter (Column.bitAt bs) :=
      List.filter_congr fun i hi => by
        have hi := List.mem_range.1 hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hi),
          Option.getD_some, Arr.getElem_toList, Arr.get_bool_bits x he]
    have hspec : whereSpec x.toList = ((List.range nx).filter (Column.bitAt bs)).map Int64.ofNat := by
      unfold whereSpec; rw [Arr.length_toList, hf]
    rw [hspec]
    apply List.ext_getElem
    · rw [List.length_map, Arr.length_toList, hl]
    · intro j h1 _
      rw [List.getElem_map, Arr.getElem_toList, Arr.get_long_bytes r hr.2]
      exact toInt64_of_toNat (hj j (by rw [Arr.length_toList] at h1; omega))
  | _ => all_goals (have hw := x.wf; rw [he] at hw; simp [Enc.WF, QAtomicType.width] at hw)

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

/-- The payloads at type `a` whose search path has a kernel law: at `long`, `bytes`, or `foR` with
    non-empty block metadata, which is what marks an operand encoded to `operandBytes` (`alp`'s decode
    has no law); at `boolean`, `bits` (`findBitVec`, `memberBits_mem`); at `symbol`, a `syms`/`enum`
    payload the SymFind kernels' laws are stated for (`symsOk`) whose symbols are UTF-8, so that
    `Column.get`'s `String` holds exactly their bytes (`Arr.toList_sym`). -/
def Readable (a : QAtomicType) (n : Nat) (e : Enc) : Prop :=
  match a with
  | .long => match e with
    | .bytes _ => True
    | .foR md _ => md.isEmpty = false
    | _ => False
  | .boolean => match e with
    | .bits _ => True
    | _ => False
  | .symbol => Verify.symsOk n e ∧ ∀ k ∈ Verify.symsOf n e, ∃ s : String, s.toUTF8.data.toList = k
  | _ => False

/-- q's `s#` contract where a search reads it: a column marked `s` ascends. Only the `long` search
    halves on the mark; the boolean one never reads it, so it asks nothing there. -/
def Ascends {n : Nat} : {a : QAtomicType} → Arr a n → Prop
  | .long, x => x.attrCell.map (·.1) = some 1 → ∀ i j : Fin n, i ≤ j → x.get i ≤ x.get j
  | _, _ => True

/-- `elemsW 8 B = ws` word by word: `B` holds `|ws|` eight-byte words, word `i` being `ws[i]`. -/
theorem elemsW8_get {B : ByteArray} {ws : List UInt64} (h : Verify.elemsW 8 B = ws) :
    B.size / 8 = ws.length ∧ ∀ i (hi : i < ws.length), Column.bitsAt B (i * 8) 8 = ws[i] := by
  subst h; exact ⟨by simp [Verify.elemsW], fun i hi => by simp [Verify.elemsW]⟩

/-- The kernels' view of a readable long column is its words: `operand` hands `bytes` over with empty
    metadata and `foR` as it is, and `operandBytes` decodes either to `longWords` (`elemsW_operandBytes`). -/
theorem operand_long {m : Nat} (x : Arr .long m) (h : Readable .long m x.enc) (hm : m < USize.size) :
    ∃ k md pk ws, operand .long m x.enc = some (k, md, pk) ∧ longWords m x.enc = some ws ∧
      Verify.elemsW 8 (operandBytes 8 md pk k.toUSize) = ws ∧ ws.length = m := by
  cases he : x.enc with
  | bytes b =>
    refine ⟨0, .empty, b, Verify.elemsW 8 b, by rfl, by simp only [longWords], rfl, ?_⟩
    rw [Verify.elemsW, List.length_map, List.length_range]; exact Arr.n_long_bytes x he
  | foR md pk =>
    have h : md.isEmpty = false := by simpa only [Readable, he] using h
    refine ⟨m, md, pk, (List.range m).map (Column.foRBits md pk (Column.blockStarts md)),
      by simp [operand, foRColumn, h, show Column.encodes QAtomicType.long = true from rfl],
      by simp only [longWords], ?_, by simp⟩
    have e := Verify.elemsW_operandBytes 8 (by rw [usize_eight]; decide) (by rw [usize_eight]; decide) md pk m hm
    rw [usize_eight] at e
    rw [e]
    simp only [Verify.operandBits, h, Bool.false_eq_true, ↓reduceIte]
    exact List.map_congr_left fun i _ => Verify.ofNat_toNat_mod64 _
  | _ => all_goals (simp only [Readable, he] at h)

/-- `x?y` at long operands: the halving over the dense needles where `x` is marked `s` and `worthHalving`
    claims it, `probeColumns` otherwise. -/
theorem findColumn_long (s : Bool) (xn : Nat) (xe : Enc) (m : Nat) (e : Enc) (ac : Option (UInt8 × IndexCell)) :
    findColumn .long s xn xe (.vector .long m e ac) =
    if s && worthHalving xn m then
      match Enc.bytesOf .long m e with
      | some ks => (findSorted .long 8 xn xe ks).map fun out => .vector .long (out.size / 8) (.bytes out) none
      | none => none
    else (probeColumns .long 8 false xn xe m e).map fun out => .vector .long (out.size / 8) (.bytes out) none := by
  cases xe <;> rfl

/-- `x in y` at long operands: `findColumn_long`'s choice, answering a bit per needle. -/
theorem memberColumn_long (s : Bool) (m : Nat) (e : Enc) (ac : Option (UInt8 × IndexCell)) (yn : Nat) (ye : Enc) :
    memberColumn .long s (.vector .long m e ac) yn ye =
    if s && worthHalving yn m then
      match Enc.bytesOf .long m e with
      | some ks => (memberSorted .long 8 yn ye ks).map fun out => .vector .boolean (ks.size / 8) (.bits out) none
      | none => none
    else (probeColumns .long 8 true yn ye m e).map fun out => .vector .boolean m (.bits out) none := by
  cases ye <;> rfl

/-- `x bin y` and `x binr y` at long operands are `binOperands` over the two `operand`s. -/
theorem binColumn_long (right : Bool) (xn : Nat) (xe : Enc) (m : Nat) (e : Enc) (ac : Option (UInt8 × IndexCell)) :
    binColumn .long right xn xe (.vector .long m e ac) = (do
    let (hn, hm, hp) ← operand .long xn xe
    let (kn, km, kp) ← operand .long m e
    some (QValue.vector .long m (.bytes (binOperands 8 false true right hm hp hn.toUSize km kp kn.toUSize)) none)) := by
  cases xe <;> rfl

/-- `probeColumns` at long operands is the dense probe over the two decoded operands: with both
    metadata empty `operandBytes` is the pack itself, otherwise it is `foRFindVec`/`foRMemberVec`'s body. -/
theorem probeColumns_long (member : Bool) {xn cn : Nat} {xe ce : Enc} {hn nn : Nat} {hm hp nm np : ByteArray}
    (hx : operand .long xn xe = some (hn, hm, hp)) (hc : operand .long cn ce = some (nn, nm, np)) :
    probeColumns .long 8 member xn xe cn ce = some (if member
      then memberVec 8 false (operandBytes 8 nm np nn.toUSize) (operandBytes 8 hm hp hn.toUSize)
      else findVec 8 false (operandBytes 8 hm hp hn.toUSize) (operandBytes 8 nm np nn.toUSize)) := by
  simp only [probeColumns, hx, hc, bind, Option.bind]
  split
  · rename_i he
    simp only [Bool.and_eq_true] at he
    simp only [operandBytes, he.1, he.2, ↓reduceIte]; rfl
  · rfl

/-- The probe for `x?y` at readable long columns, whatever form each is in: one word per needle of `y`, its
    first position among `x`'s words, `|x|` at a miss (`findVec_idxOf` over the two `operandBytes`). -/
theorem probe_find {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hx : Readable .long nx x.enc)
    (hy : Readable .long ny y.enc) (hn : nx < USize.size) (hm : ny < USize.size) :
    ∃ B xs ys, probeColumns .long 8 false nx x.enc ny y.enc = some B ∧ longWords nx x.enc = some xs ∧ longWords ny y.enc = some ys ∧
      (Verify.elemsW 8 B).map UInt64.toNat = ys.map xs.idxOf := by
  obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hn
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hm
  refine ⟨_, xs, ys, probeColumns_long false hox hoy, hwx, hwy, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  generalize operandBytes 8 hmd hp hk.toUSize = Bx at hbx ⊢
  generalize operandBytes 8 nmd np nk.toUSize = By at hby ⊢
  obtain ⟨hsx, -⟩ := elemsW8_get hbx
  obtain ⟨hsy, gy⟩ := elemsW8_get hby
  obtain ⟨hF, hj⟩ := Verify.findVec_idxOf 8 false Bx By (by rw [usize_eight, hsx, hlx]; exact hn)
  rw [usize_eight] at hF hj
  simp only [hbx, Nat.le_refl, ↓reduceIte, show normalise 8 false = id from rfl, List.map_id, id_eq] at hj
  apply List.ext_getElem (by simp [Verify.elemsW, hF, hsy])
  intro j h1 h2
  have hj' : j < ys.length := by simpa using h2
  simp only [List.getElem_map, Verify.elemsW, List.getElem_range]
  rw [hj j (by rw [hsy]; exact hj'), gy j hj']

/-- The probe for `x in y` at readable long columns, whatever form each is in: bit `i` says whether `x`'s
    word `i` is among `y`'s (`memberVec_mem` over the two `operandBytes`). -/
theorem probe_member {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hx : Readable .long nx x.enc)
    (hy : Readable .long ny y.enc) (hn : nx < USize.size) (hm : ny < USize.size) :
    ∃ M xs ys, probeColumns .long 8 true ny y.enc nx x.enc = some M ∧ longWords nx x.enc = some xs ∧ longWords ny y.enc = some ys ∧
      ∀ i (hi : i < xs.length), Column.bitAt M i = decide (xs[i] ∈ ys) := by
  obtain ⟨hk, hmd, hp, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hm
  obtain ⟨nk, nmd, np, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hn
  refine ⟨_, xs, ys, probeColumns_long true hoy hox, hwx, hwy, ?_⟩
  simp only [↓reduceIte]
  generalize operandBytes 8 hmd hp hk.toUSize = By at hby ⊢
  generalize operandBytes 8 nmd np nk.toUSize = Bx at hbx ⊢
  obtain ⟨hsx, gx⟩ := elemsW8_get hbx
  obtain ⟨hsy, -⟩ := elemsW8_get hby
  obtain ⟨-, hj⟩ := Verify.memberVec_mem 8 false Bx By (by rw [usize_eight, hsy, hly]; exact hm)
  rw [usize_eight] at hj
  simp only [Nat.le_refl, ↓reduceIte, show normalise 8 false = id from rfl, List.map_id, hby, id_eq] at hj
  intro i hi
  rw [hj i (by rw [hsx]; omega)]
  simp only [hsx, hi, decide_true, Bool.true_and, gx i hi]

/-- `?x`'s kernel answer on a long column: some `e` lists `x`'s words, and the answer's words are `e` at
    `firstsOf` of its rank — `distinct_spec` on `bytes`; on `foR`, `distinctFoR_spec`, whose answer
    `Enc.answer` leaves encoded or decodes (`decodeW`), the same words either way. -/
theorem distinct_words {m : Nat} (x : Arr .long m) {xs : List UInt64} (hx : longWords m x.enc = some xs)
    (hn : m < USize.size) : ∃ (e : Nat → UInt64) (k : Nat) (c : Enc), xs = (List.range m).map e ∧
      distinctColumn .long m x.enc = some (.vector .long k c none) ∧
      longWords k c = some ((Verify.firstsOf (fun i => Order.rank .i64 (e i)) m).map e) := by
  cases he : x.enc with
  | bytes b =>
    simp only [longWords, he] at hx; cases hx
    have hxn := Arr.n_long_bytes x he
    refine ⟨fun i => Column.bitsAt b (i * 8) 8, (Order.distinct .i64 (b.size / 8).toUSize b).size / 8,
      .bytes (Order.distinct .i64 (b.size / 8).toUSize b), by rw [Verify.elemsW, hxn], rfl, ?_⟩
    have hs := Verify.distinct_spec .i64 (b.size / 8).toUSize b
    rw [USize.toNat_ofNat_of_lt' (by rw [hxn]; exact hn), show Scan.Kind.i64.avail b = b.size / 8 from rfl,
      Nat.min_self, hxn, show Scan.Kind.i64.width = 8 from rfl,
      show Scan.Kind.i64.bitsAt b = fun i => Column.bitsAt b (i * 8) 8 from rfl,
      show Order.keyAt .i64 b = fun i => Order.rank .i64 (Column.bitsAt b (i * 8) 8) from rfl] at hs
    show some (Verify.elemsW 8 (Order.distinct .i64 (b.size / 8).toUSize b)) = _
    rw [hxn, hs]
  | foR md pk =>
    simp only [longWords, he] at hx; cases hx
    refine ⟨Verify.foRAt 8 md pk, (Order.distinctFoR .i64 m.toUSize md pk).1,
      Enc.answer .long (Order.distinctFoR .i64 m.toUSize md pk).1
        (.foR (Order.distinctFoR .i64 m.toUSize md pk).2.1 (Order.distinctFoR .i64 m.toUSize md pk).2.2),
      List.map_congr_left fun i _ => (Verify.ofNat_toNat_mod64 _).symm, rfl, ?_⟩
    have hs := Verify.distinctFoR_spec .i64 (by decide) m.toUSize md pk
    rw [USize.toNat_ofNat_of_lt' hn] at hs
    generalize Order.distinctFoR .i64 m.toUSize md pk = d at hs ⊢
    obtain ⟨M, P, Q⟩ := d
    change (List.range M).map (Verify.foRAt 8 P Q) =
      (Verify.firstsOf (fun i => Order.rank .i64 (Verify.foRAt 8 md pk i)) m).map (Verify.foRAt 8 md pk) at hs
    show longWords M (Enc.answer .long M (.foR P Q)) = _
    rw [← hs]
    have hM : M < USize.size := by
      have := congrArg List.length hs
      rw [List.length_map, List.length_range, List.length_map] at this
      unfold Verify.firstsOf at this
      rw [this]
      exact Nat.lt_of_le_of_lt (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..))) hn
    rcases Verify.answer_foR .long 8 M P Q rfl with e | e <;> rw [e]
    · exact congrArg some (List.map_congr_left fun i _ => (Verify.ofNat_toNat_mod64 _).symm)
    · show longWords M (.bytes (Coc.decode 8 P Q M.toUSize)) = _
      obtain ⟨hsz, hg⟩ := Verify.decodeW 8 (by rw [usize_eight]; decide) P Q M.toUSize
      rw [usize_eight, USize.toNat_ofNat_of_lt' hM] at hsz hg
      refine congrArg some (List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_)
      simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
      exact hg i (by simpa [Verify.elemsW, hsz] using h1)
  | _ => all_goals (simp [longWords, he] at hx)

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
    (reverseBytes 8 of) (reverseBytes 8 (tilLongs n.toUSize)) 0 false
    (by simp only [hix.1, hsx.1, USize.toNat_zero, Bool.false_eq_true, if_false]; omega)
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

theorem bytesOf_long {n : Nat} {e : Enc} (h : Readable .long n e) {k : Nat} {md pk : ByteArray}
    (ho : operand .long n e = some (k, md, pk)) : Enc.bytesOf .long n e = some (operandBytes 8 md pk k.toUSize) := by
  have he : Column.encodes QAtomicType.long = true := rfl
  cases e with
  | bytes b => simp [operand, foRColumn, Enc.bytesOf] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho; rfl
  | foR m p =>
    have h : m.isEmpty = false := h
    simp [operand, foRColumn, he, h] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho
    simp [operandBytes, h, Enc.bytesOf, QAtomicType.width]; rfl
  | _ => exact False.elim h

/-- A `foR` long column lists `Coc.elems`, the decode `range_bounds` speaks of. -/
theorem longWords_foR {n : Nat} {md pk : ByteArray} (h : n < USize.size) :
    longWords n (.foR md pk) = some (Coc.elems md pk n.toUSize) := by
  simp only [longWords, Coc.elems, USize.toNat_ofNat_of_lt' h]

/-- A fold whose every step keeps the accumulator or takes the element lands at the seed or an element. -/
theorem foldl_seed_or_mem (f : Int64 → UInt64 → Int64) (hf : ∀ b v, f b v = b ∨ f b v = v.toInt64) :
    ∀ (l : List UInt64) (a : Int64), l.foldl f a = a ∨ ∃ v ∈ l, l.foldl f a = v.toInt64
  | [], _ => .inl rfl
  | x :: xs, a => by
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    rcases foldl_seed_or_mem f hf xs (f a x) with h | ⟨v, hv, h⟩
    · rcases hf a x with e | e
      · exact .inl (h.trans e)
      · exact .inr (.inl (h.trans e))
    · exact .inr (.inr ⟨v, hv, h⟩)

/-- The least end of a `Coc.range` at `long` is not `0N`: it is `min`'s seed `0W` or an element,
    and `range_bounds` keeps every element off the null. -/
theorem range_lo_ne {md pk : ByteArray} {n : USize} {lo hi : Int64}
    (h : Coc.range Int64.minValue md pk n = some (lo, hi)) : lo ≠ Int64.minValue := by
  have hb := Verify.range_bounds _ md pk n lo hi h
  unfold Coc.range at h
  split at h
  · simp at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  intro hc
  rcases foldl_seed_or_mem (fun acc v => if !Coc.Over.boolCast .lesser && v.toInt64 == Int64.minValue then acc
      else Coc.Over.step .lesser acc v.toInt64) (fun b v => by
        simp only [Coc.Over.boolCast, Coc.Over.step]
        split
        · exact .inl rfl
        · split
          · exact .inl rfl
          · exact .inr rfl) (Coc.elems md pk n) (Coc.Over.seed .lesser Int64.minValue) with e | ⟨v, hv, e⟩
  · exact absurd (e.symm.trans hc) (by decide)
  · exact (hb v hv).1 (e.symm.trans hc)

theorem direct_some {n : Nat} {e : Enc} {t hb : ByteArray} {lo : Int64} (h : direct .long n e = some (t, lo, hb)) :
    ∃ md pk hi, e = .foR md pk ∧ md.isEmpty = false ∧ Coc.range Int64.minValue md pk n.toUSize = some (lo, hi) ∧
      (hi.toInt - lo.toInt).toNat + 1 ≤ 4 * max 65536 n ∧
      Enc.bytesOf .long n e = some hb ∧ t = firstTable hb n lo ((hi.toInt - lo.toInt).toNat + 1) := by
  have hcls : clsOf QAtomicType.long = some Ew.i64 := rfl
  have hnul : Coc.nullOf QAtomicType.long = some Int64.minValue := rfl
  cases e with
  | foR md pk =>
    unfold direct at h
    cases he : md.isEmpty with
    | true => simp [hcls, he, guard, failure, bind, Option.bind] at h
    | false =>
      cases hR : Coc.range Int64.minValue md pk n.toUSize with
      | none => simp [hcls, hnul, he, hR, guard, failure, bind, Option.bind] at h
      | some p =>
        obtain ⟨l, hi⟩ := p
        by_cases hg : (hi.toInt - l.toInt).toNat + 1 ≤ 4 * max 65536 n
        · cases hb' : Enc.bytesOf .long n (.foR md pk) with
          | none => simp [hcls, hnul, he, hR, hg, hb', guard, failure, bind, Option.bind] at h
          | some b =>
            simp [hcls, hnul, he, hR, hg, hb', guard, failure, bind, Option.bind] at h
            rcases h with ⟨h1, h2, h3⟩; subst_vars; exact ⟨md, pk, hi, rfl, he, hR, hg, rfl, rfl⟩
        · simp [hcls, hnul, he, hR, hg, guard, failure, bind, Option.bind] at h
  | _ => all_goals (unfold direct at h; simp [hcls, guard, bind, Option.bind] at h)

/-- What `direct` answering hands the direct path: the haystack's words `xs`, dense in `hb`; a range `r`
    below `2^63` holding every offset from `lo`, which is not `0N`; and `t` the `firstTable`. Every
    element lies in the range because `Coc.range` answered it (`range_bounds`), not by assumption. -/
theorem direct_table {m : Nat} {x : Arr .long m} {t hb : ByteArray} {lo : Int64}
    (hd : direct .long m x.enc = some (t, lo, hb)) (hn8 : 8 * m < USize.size) :
    ∃ xs r, longWords m x.enc = some xs ∧ Verify.elemsW 8 hb = xs ∧ xs.length = m ∧ r < 2 ^ 63 ∧
      lo ≠ Int64.minValue ∧ (∀ w ∈ xs, lo ≤ w.toInt64 ∧ off lo w.toInt64 < r) ∧ t = firstTable hb m lo r := by
  have hS := USize.size_le
  obtain ⟨md, pk, hi, hc, he, hR, hr4, hbx, ht⟩ := direct_some hd
  have hx : Readable .long m x.enc := by simp only [Readable, hc]; exact he
  obtain ⟨k', md', pk', xs, hox, hwx, hbx', hlx⟩ := operand_long x hx (by omega)
  rw [bytesOf_long hx hox] at hbx; obtain rfl := Option.some.inj hbx
  have hxs : xs = Coc.elems md pk m.toUSize := by
    have h' := hwx; rw [hc, longWords_foR (by omega)] at h'; exact (Option.some.inj h').symm
  refine ⟨xs, _, hwx, hbx', hlx, ?_, range_lo_ne hR, fun w hw => ?_, ht⟩
  · rw [Nat.max_def] at hr4; split at hr4 <;> omega
  · obtain ⟨-, a, b⟩ := Verify.range_bounds _ md pk _ lo hi hR w (hxs ▸ hw)
    refine ⟨a, ?_⟩
    have := off_toInt a; have := Int64.le_iff_toInt_le.mp b; omega

theorem find_direct {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hy : Readable .long ny y.enc) {t hb : ByteArray} {lo : Int64} (hd : direct .long nx x.enc = some (t, lo, hb))
    (hn8 : 8 * nx < USize.size) (hm : ny < USize.size) {nb : ByteArray} (hnb : Enc.bytesOf .long ny y.enc = some nb)
    (hw : Enc.WF .long ny (.bytes (probe t nx lo nb))) :
    (find x y).toList = findSpec x.toList y.toList := by
  have hS := USize.size_le
  have hE : (find x y).enc = .bytes (probe t nx lo nb) := by unfold find; rw [hd, hnb]; exact orElse_enc hw _
  generalize find x y = r at hE ⊢
  obtain ⟨xs, R, hwx, hbx, hlx, hr, hlo, hin, rfl⟩ := direct_table hd hn8
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hm
  obtain rfl := Option.some.inj ((bytesOf_long hy hoy).symm.trans hnb)
  rw [Arr.toList_long r (show longWords ny r.enc = some (Verify.elemsW 8 (probe (firstTable hb nx lo R) nx lo
    (operandBytes 8 nmd np nk.toUSize))) by rw [hE]; rfl),
    Arr.toList_long x hwx, Arr.toList_long y hwy, findSpec,
    probe_spec _ xs nx lo _ hbx hlx (by omega) hr hlo hin _ ys hby (by rw [hly]; exact hm)]
  simp only [List.map_map]; rfl

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
theorem in_direct {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hx : Readable .long nx x.enc) {t hb : ByteArray} {lo : Int64} (hd : direct .long ny y.enc = some (t, lo, hb))
    (hn8 : 8 * ny < USize.size) (hm : nx < USize.size) {nb : ByteArray} (hnb : Enc.bytesOf .long nx x.enc = some nb)
    (hw : Enc.WF .boolean nx (.bits (Ew.cmp Ew.lt Ew.i64 Ew.va (probe t ny lo nb) (one ny.toUInt64) nx.toUSize))) :
    («in» x y).toList = inSpec x.toList y.toList := by
  have hS := USize.size_le
  have h : («in» x y).enc = .bits (Ew.cmp Ew.lt Ew.i64 Ew.va (probe t ny lo nb) (one ny.toUInt64) nx.toUSize) := by
    unfold «in»; rw [hd, hnb]; exact orElse_enc hw _
  generalize «in» x y = r at h ⊢
  obtain ⟨ys, R, hwy, hby, hly, hr, hlo, hin, rfl⟩ := direct_table hd hn8
  obtain ⟨nk, nmd, np, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hm
  obtain rfl := Option.some.inj ((bytesOf_long hx hox).symm.trans hnb)
  have hG := probe_spec hb ys ny lo R hby hly (by omega) hr hlo hin _ xs hbx (by rw [hlx]; exact hm)
  generalize probe (firstTable hb ny lo R) ny lo (operandBytes 8 nmd np nk.toUSize) = g at h hG
  obtain ⟨-, hc⟩ := Verify.cmp_bitAt Ew.lt Ew.i64 Ew.va g (one ny.toUInt64) nx.toUSize
  rw [USize.toNat_ofNat_of_lt' hm] at hc
  obtain ⟨-, gg⟩ := elemsW8_get hG
  unfold inSpec
  rw [Arr.toList_long x hwx, Arr.toList_long y hwy]
  apply List.ext_getElem (by rw [Arr.length_toList]; simp [hlx])
  intro i h1 _
  have hi : i < nx := by rw [Arr.length_toList] at h1; exact h1
  rw [Arr.getElem_toList, Arr.get_bool_bits r h, hc i (by omega)]
  rw [show Ew.shapeIdx Ew.va i = (i, 0) from rfl, show Ew.elem Ew.i64 g i = Column.bitsAt g (i * 8) 8 from rfl,
    show Ew.elem Ew.i64 (one ny.toUInt64) 0 = Column.bitsAt (one ny.toUInt64) 0 8 from rfl, bitsAt_one,
    gg i (by simp [hlx, hi]), cmpStep_lt]
  simp only [List.getElem_map, hi, decide_true, Bool.true_and]
  have hI := List.idxOf_le_length (a := xs[i].toInt64) (l := ys.map UInt64.toInt64)
  rw [List.length_map, hly] at hI
  apply Bool.eq_iff_iff.2
  have hyn : ny.toUInt64.toInt64.toInt = ny := toInt_ofNat_lt (by omega)
  have hl : (ys.map UInt64.toInt64).length = ny := by simp [hly]
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
theorem distinct_direct {nx : Nat} {x : Arr .long nx}
    {t hb : ByteArray} {lo : Int64} (hd : direct .long nx x.enc = some (t, lo, hb)) (hu : x.attrCell.map (·.1) ≠ some 2)
    (hn8 : 8 * nx < USize.size)
    (hw : Enc.WF .long ((gatherBytes 8 0 hb (whereBits nx.toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv (probe t nx lo hb)
      (tilLongs nx.toUSize) nx.toUSize))).size / 8) (.bytes (gatherBytes 8 0 hb (whereBits nx.toUSize
      (Ew.cmp Ew.eq Ew.i64 Ew.vv (probe t nx lo hb) (tilLongs nx.toUSize) nx.toUSize))))) :
    (distinct x).2.toList = distinctSpec x.toList := by
  have hS := USize.size_le
  have hn : nx < USize.size := by omega
  have h : (distinct x).2.enc = .bytes (gatherBytes 8 0 hb (whereBits nx.toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv
      (probe t nx lo hb) (tilLongs nx.toUSize) nx.toUSize))) := by
    unfold distinct
    rw [show (x.attrCell.map (·.1) == some 2) = false by simp [hu], hd]
    dsimp only
    rw [if_neg Bool.false_ne_true, dif_pos hw]
    dsimp only; exact Arr.markIf_enc _ _
  generalize distinct x = D at h ⊢
  obtain ⟨nr, r⟩ := D
  dsimp only at h
  obtain ⟨xs, R, hwx, hbx, hlx, hr, hlo, hin, rfl⟩ := direct_table hd hn8
  have hP := probe_spec hb xs nx lo R hbx hlx hn hr hlo hin hb xs hbx (by rw [hlx]; exact hn)
  generalize probe (firstTable hb nx lo R) nx lo hb = P at h hP
  obtain ⟨-, hc⟩ := Verify.cmp_bitAt Ew.eq Ew.i64 Ew.vv P (tilLongs nx.toUSize) nx.toUSize
  rw [USize.toNat_ofNat_of_lt' hn] at hc
  generalize Ew.cmp Ew.eq Ew.i64 Ew.vv P (tilLongs nx.toUSize) nx.toUSize = bits at h hc

  -- the words as a function of the position
  let e : Nat → UInt64 := fun i => xs.getD i 0
  have hxe : xs = (List.range nx).map e :=
    List.ext_getElem (by simp [hlx]) fun i h1 _ => by simp [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  obtain ⟨-, gP⟩ := elemsW8_get hP
  obtain ⟨-, gx⟩ := elemsW8_get hbx
  have htil := Verify.tilLongs_spec nx.toUSize
  rw [USize.toNat_ofNat_of_lt' hn] at htil
  have htl : (Verify.elemsW 8 (tilLongs nx.toUSize)).length = nx := by
    rw [← List.length_map (f := UInt64.toNat), htil, List.length_range]
  have gT : ∀ i < nx, (Column.bitsAt (tilLongs nx.toUSize) (i * 8) 8).toNat = i := fun i hi => by
    have hv := List.getElem_of_eq htil (i := i) (by simp [htl]; omega)
    simpa [Verify.elemsW] using hv
  -- bit `i` marks a first occurrence
  have hF : (List.range nx).filter (Column.bitAt bits) = Verify.firstsOf e nx := by
    unfold Verify.firstsOf
    apply List.filter_congr
    intro i hi'
    have hi := List.mem_range.1 hi'
    have hil : i < xs.length := by omega
    rw [hc i (by omega), show Ew.shapeIdx Ew.vv i = (i, i) from rfl,
      show Ew.elem Ew.i64 P i = Column.bitsAt P (i * 8) 8 from rfl,
      show Ew.elem Ew.i64 (tilLongs nx.toUSize) i = Column.bitsAt (tilLongs nx.toUSize) (i * 8) 8 from rfl,
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
  have hL : ∀ i ∈ (List.range nx.toUSize.toNat).filter (Column.bitAt bits), i < hb.size / (8 : USize).toNat := by
    intro i hi
    have := List.mem_range.1 (List.mem_filter.1 hi).1
    rw [USize.toNat_ofNat_of_lt' hn] at this
    rw [usize_eight, (elemsW8_get hbx).1, hlx]; exact this
  obtain ⟨gs, gj⟩ := Verify.gatherBytes_whereBits 8 (by rw [usize_eight]; decide) 0 hb nx.toUSize bits hL
  rw [usize_eight, USize.toNat_ofNat_of_lt' hn, hF] at gs gj
  have hw : Verify.elemsW 8 (gatherBytes 8 0 hb (whereBits nx.toUSize bits)) = (Verify.firstsOf e nx).map e := by
    apply List.ext_getElem (by
      rw [List.length_map, Verify.elemsW, List.length_map, List.length_range, gs, Nat.mul_div_cancel_left _ (by decide)])
    intro j h1 h2
    have hj : j < (Verify.firstsOf e nx).length := by simpa using h2
    have hlt : (Verify.firstsOf e nx)[j] < xs.length := by
      have := (List.mem_filter.1 (List.getElem_mem hj)).1; rw [hlx]; exact List.mem_range.1 this
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [gj j hj, gx _ hlt]
    show _ = xs.getD _ 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [Arr.toList_long r (show longWords _ r.enc = _ by rw [h]; exact congrArg some hw), distinctSpec,
    Arr.toList_long x hwx, hxe, List.map_map, List.map_map]
  exact firstsOf_map_eraseDups e (UInt64.toInt64 ∘ e) (fun i j => ⟨congrArg UInt64.toInt64, toInt64_inj⟩) nx

/-! ## The halving over a haystack marked `s` -/

/-- `findSorted` over a readable long haystack is `findSortedBytes` over its `operandBytes`. -/
theorem findSorted_long {n : Nat} {e : Enc} (h : Readable .long n e) {k : Nat} {md pk : ByteArray}
    (ho : operand .long n e = some (k, md, pk)) (ks : ByteArray) :
    findSorted .long 8 n e ks = some (findSortedBytes 8 false true (operandBytes 8 md pk k.toUSize) ks) := by
  have he : Column.encodes QAtomicType.long = true := rfl
  cases e with
  | bytes b => simp [operand, foRColumn, Enc.bytesOf] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho; rfl
  | foR m p =>
    have h : m.isEmpty = false := h
    simp [operand, foRColumn, he, h] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho
    simp [findSorted, foRColumn, he, operandBytes, h]; rfl
  | _ => exact False.elim h

/-- `memberSorted` over a readable long haystack is `memberSortedBytes` over its `operandBytes`. -/
theorem memberSorted_long {n : Nat} {e : Enc} (h : Readable .long n e) {k : Nat} {md pk : ByteArray}
    (ho : operand .long n e = some (k, md, pk)) (ks : ByteArray) :
    memberSorted .long 8 n e ks = some (memberSortedBytes 8 false true ks (operandBytes 8 md pk k.toUSize)) := by
  have he : Column.encodes QAtomicType.long = true := rfl
  cases e with
  | bytes b => simp [operand, foRColumn, Enc.bytesOf] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho; rfl
  | foR m p =>
    have h : m.isEmpty = false := h
    simp [operand, foRColumn, he, h] at ho; obtain ⟨rfl, rfl, rfl⟩ := ho
    simp [memberSorted, foRColumn, he, operandBytes, h]; rfl
  | _ => exact False.elim h

/-- **The halving at a needle is its first index** over ascending words: `binStep`'s `binr` partition
    point `p` (`binStep_spec`) has every word below it under the needle and none from it on, so the
    needle is held iff word `p` equals it, and then at `p` first. -/
theorem findSortedAt_idxOf {H : ByteArray} {ws : List UInt64} (hw : Verify.elemsW 8 H = ws)
    (hsort : ∀ i j (hi : i < ws.length) (hj : j < ws.length), i ≤ j → ws[i].toInt64 ≤ ws[j].toInt64) (y : UInt64) :
    findSortedAt 8 false true H ws.length (ordKey 8 false true y) = ws.idxOf y := by
  obtain ⟨-, gw⟩ := elemsW8_get hw
  have inj : ∀ a b : UInt64, Order.rank .i64 a = Order.rank .i64 b → a = b := fun a b e =>
    toInt64_inj (Int64.le_antisymm (rank_i64_le (UInt64.le_of_eq e)) (rank_i64_le (UInt64.le_of_eq e.symm)))
  obtain ⟨hp, hlo, hhi⟩ := Verify.binStep_spec 8 false true true H (ordKey 8 false true y) ws.length
    fun i j hij hj => by
      rw [gw i (by omega), gw j hj, ordKey_long, ordKey_long, rank_i64_le_iff]; exact hsort i j (by omega) hj hij
  simp only [↓reduceIte, ordKey_long] at hp hlo hhi
  simp only [findSortedAt, ordKey_long]
  generalize binStep 8 false true true H ByteArray.empty (Order.rank .i64 y) (ws.length + 1) 0 ws.length = p at hp hlo hhi ⊢
  have hlt : ∀ j (hj : j < ws.length), j < p → ws[j] ≠ y := fun j hj hjp e => by
    have := hlo j hjp; rw [gw j hj, e] at this; exact UInt64.lt_irrefl _ this
  by_cases hc : ∃ hpn : p < ws.length, ws[p] = y
  · obtain ⟨hpn, rfl⟩ := hc
    rw [gw p hpn]
    simp only [hpn, decide_true, beq_self_eq_true, Bool.true_and, ↓reduceIte]
    exact ((idxOf_self_iff ws p hpn).2 fun j hj => hlt j _ hj).symm
  · have hny : y ∉ ws := fun hm => by
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
      by_cases hjp : j < p
      · exact hlt j hj hjp e
      · have hpn : p < ws.length := by omega
        refine hc ⟨hpn, inj _ _ (UInt64.le_antisymm ?_ ?_)⟩
        · rw [← e]; exact rank_i64_le_iff.2 (hsort p j hpn hj (by omega))
        · have := hhi p (Nat.le_refl _) hpn; rw [gw p hpn] at this; exact UInt64.not_lt.1 this
    rw [List.idxOf_eq_length hny]
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      obtain ⟨hpn, e⟩ := hcond
      rw [gw p hpn] at e; exact absurd ⟨hpn, inj _ _ e⟩ hc
    · rfl

/-- **`findSortedBytes` over ascending words is the first index of each needle**, `findSortedAt_idxOf`
    per needle, read back by `elemsW_foldl`. -/
theorem findSortedBytes_idxOf {H K : ByteArray} {ws ks : List UInt64} (hw : Verify.elemsW 8 H = ws)
    (hk : Verify.elemsW 8 K = ks)
    (hsort : ∀ i j (hi : i < ws.length) (hj : j < ws.length), i ≤ j → ws[i].toInt64 ≤ ws[j].toInt64) :
    Verify.elemsW 8 (findSortedBytes 8 false true H K) =
      ks.map fun y => UInt64.ofNat ((ws.map UInt64.toInt64).idxOf y.toInt64) := by
  obtain ⟨hsk, gk⟩ := elemsW8_get hk
  obtain ⟨hsw, -⟩ := elemsW8_get hw
  rw [show findSortedBytes 8 false true H K = (List.range (K.size / 8)).foldl (fun acc j => Column.pushBits acc
      ((findSortedAt 8 false true H (H.size / 8) (ordKey 8 false true (Column.bitsAt K (j * 8) 8)) : Int)).toInt64.toUInt64 8)
      ByteArray.empty by simp only [findSortedBytes, usize_eight],
    Verify.elemsW_foldl _ 8 (by decide) (by decide) _ (fun _ _ => UInt64.toNat_lt _)]
  apply List.ext_getElem (by simp [hsk])
  intro j h1 _
  have hj : j < ks.length := by simpa [hsk] using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [gk j hj, hsw, findSortedAt_idxOf hw hsort, idxOf_map_of_inj (fun _ _ => toInt64_inj)]
  exact UInt64.toBitVec_inj.1 (BitVec.ofInt_natCast _ _)

/-- Bit `i` of a byte-at-a-time bitmap whose bit `b·8 + t` is `C (b·8 + t)`, below `m`: `C i`. -/
theorem bitAt_packed (C : Nat → Bool) (m i : Nat) (hi : i < m) :
    Column.bitAt ((List.range ((m + 7) / 8)).foldl (fun acc b => acc.push ((List.range 8).foldl
      (fun byte t => if C (b * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0)) ByteArray.empty) i = C i := by
  let B : Nat → UInt8 := fun b =>
    (List.range 8).foldl (fun byte t => if C (b * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  show Column.bitAt ((List.range ((m + 7) / 8)).foldl (fun acc b => acc.push (B b)) ByteArray.empty) i = C i
  obtain ⟨-, -, hg⟩ := Verify.foldl_push8 B (List.range ((m + 7) / 8)) ByteArray.empty
  have hb : i / 8 < (m + 7) / 8 := by omega
  have h := hg (i / 8) (by simpa using hb)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  have hm8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
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

/-- **`memberSortedBytes` over ascending words is membership**: bit `i` is `findSortedAt_idxOf`'s index
    below the count. -/
theorem memberSortedBytes_mem {H K : ByteArray} {ws ks : List UInt64} (hw : Verify.elemsW 8 H = ws)
    (hk : Verify.elemsW 8 K = ks)
    (hsort : ∀ i j (hi : i < ws.length) (hj : j < ws.length), i ≤ j → ws[i].toInt64 ≤ ws[j].toInt64)
    (i : Nat) (hi : i < ks.length) : Column.bitAt (memberSortedBytes 8 false true K H) i = decide (ks[i] ∈ ws) := by
  obtain ⟨hsk, gk⟩ := elemsW8_get hk
  obtain ⟨hsw, -⟩ := elemsW8_get hw
  let C : Nat → Bool := fun i => decide (i < K.size / 8) &&
    decide (findSortedAt 8 false true H (H.size / 8) (ordKey 8 false true (Column.bitsAt K (i * 8) 8)) < H.size / 8)
  have e : memberSortedBytes 8 false true K H = (List.range ((K.size / 8 + 7) / 8)).foldl (fun acc b => acc.push
      ((List.range 8).foldl (fun byte t => if C (b * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0))
      ByteArray.empty := by
    simp only [memberSortedBytes, usize_eight]; rfl
  rw [e, bitAt_packed C _ i (by rw [hsk]; exact hi)]
  simp only [C, hsw, gk i hi, findSortedAt_idxOf hw hsort, hsk, hi, decide_true, Bool.true_and, List.idxOf_lt_length_iff]

/-- `eraseDups` keeps a list with no repeats. -/
theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α] : ∀ l : List α, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.eraseDups_cons, List.filter_eq_self.2 fun b hb => by
      simpa using fun e : b = a => (List.nodup_cons.1 h).1 (e ▸ hb), eraseDups_of_nodup l (List.nodup_cons.1 h).2]

/-! ## The laws, on `bytes` and on `foR` alike -/

/-- `?x` on a long column is `distinctSpec`, from `distinct_words`. Restrictions: q's `u#` contract, that
    a column marked `u` has no repeats — `c.attr` is a mark any producer sets and carries no proof, and
    under it `?x` answers `x` itself; `longWords` defined, which excludes `alp`; `8 · nx < USize.size`,
    which keeps the range below `2^63`. -/
theorem distinct_toList {nx : Nat} {x : Arr .long nx} {xs : List UInt64}
    (hx : longWords nx x.enc = some xs) (hu : x.attrCell.map (·.1) = some 2 → x.toList.Nodup)
    (hn8 : 8 * nx < USize.size) : (distinct x).2.toList = distinctSpec x.toList := by
  by_cases ha : x.attrCell.map (·.1) = some 2
  · rw [show distinct x = ⟨nx, x⟩ by simp [distinct, ha]]; exact (eraseDups_of_nodup _ (hu ha)).symm
  replace hu := ha
  have hn : nx < USize.size := by have := USize.size_le; omega
  have hK : (distinctK x).2.toList = distinctSpec x.toList := by
    obtain ⟨e, k, c, hxe, hv, hw⟩ := distinct_words x hx hn
    have hr := distinctK_enc (x := x) (by decide) hv
    generalize distinctK x = D at hr ⊢
    obtain ⟨nr, r⟩ := D
    obtain ⟨rfl, hr⟩ := hr
    rw [Arr.toList_long r (show longWords _ r.enc = _ by rw [hr]; exact hw), distinctSpec,
      Arr.toList_long x hx, hxe, List.map_map, List.map_map]
    refine firstsOf_map_eraseDups _ _ (fun i j => ⟨fun h' => ?_, fun h' => ?_⟩) nx
    · have e' : Order.rank .i64 (e i) = Order.rank .i64 (e j) := h'
      exact Int64.le_antisymm (rank_i64_le (UInt64.le_of_eq e')) (rank_i64_le (UInt64.le_of_eq e'.symm))
    · show Order.rank .i64 (e i) = Order.rank .i64 (e j)
      rw [toInt64_inj (x := e i) (y := e j) h']
  have hna : (x.attrCell.map (·.1) == some 2) = false := by simp [hu]
  cases hd : direct .long nx x.enc with
  | none => rw [show distinct x = distinctK x by unfold distinct; rw [hna, hd]; rfl]; exact hK
  | some p =>
    obtain ⟨t, lo, hb⟩ := p
    by_cases hw : Enc.WF .long ((gatherBytes 8 0 hb (whereBits nx.toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv
      (probe t nx lo hb) (tilLongs nx.toUSize) nx.toUSize))).size / 8) (.bytes (gatherBytes 8 0 hb (whereBits
      nx.toUSize (Ew.cmp Ew.eq Ew.i64 Ew.vv (probe t nx lo hb) (tilLongs nx.toUSize) nx.toUSize))))
    · exact distinct_direct hd hu hn8 hw
    · rw [show distinct x = distinctK x by unfold distinct; rw [hna, hd]; dsimp only; rw [if_neg Bool.false_ne_true, dif_neg hw]]; exact hK

/-- `x?y` on long columns is `findSpec`: `findVec_idxOf` over the decoded operands, or, where `x` is marked
    `s`, `findSortedBytes_idxOf`. Restrictions: `Readable` payloads; q's `s#` contract, that a column marked
    `s` ascends — `c.attr` carries no proof, and an amend that breaks the order drops the mark; both counts
    below `USize.size`, which the kernel indexes by, and `8 · nx` too, which keeps the range below `2^63`. -/
theorem find_long {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hx : Readable .long nx x.enc) (hy : Readable .long ny y.enc)
    (hs : x.attrCell.map (·.1) = some 1 → ∀ i j : Fin nx, i ≤ j → x.get i ≤ x.get j)
    (hn8 : 8 * nx < USize.size) (hm : ny < USize.size) :
    (find x y).toList = findSpec x.toList y.toList := by
  have hn : nx < USize.size := by have := USize.size_le; omega
  have hK : (findK x y).toList = findSpec x.toList y.toList := by
    obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hn
    obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hm
    have hc := findColumn_long (x.attrCell.map (·.1) == some 1) nx x.enc ny y.enc y.attrCell
    rw [← y.val_eq] at hc
    by_cases hw : (x.attrCell.map (·.1) == some 1 && worthHalving nx ny) = true
    · have ha : x.attrCell.map (·.1) = some 1 := by simp only [Bool.and_eq_true, beq_iff_eq] at hw; exact hw.1
      have hsx : ∀ i j (hi : i < xs.length) (hj : j < xs.length), i ≤ j → xs[i].toInt64 ≤ xs[j].toInt64 :=
        fun i j hi hj hij => by
          have := hs ha ⟨i, by omega⟩ ⟨j, by omega⟩ hij
          rwa [Arr.get_long x hwx i (by omega) hi, Arr.get_long x hwx j (by omega) hj] at this
      rw [if_pos hw, bytesOf_long hy hoy] at hc; simp only [findSorted_long hx hox] at hc
      have h := findK_enc (by decide) hm hc
      generalize findK x y = r at h ⊢
      rw [Arr.toList_long r (show longWords _ r.enc = some (Verify.elemsW 8 (findSortedBytes 8 false true
        (operandBytes 8 hmd hp hk.toUSize) (operandBytes 8 nmd np nk.toUSize))) by rw [h]; rfl),
        Arr.toList_long x hwx, Arr.toList_long y hwy, findSpec, findSortedBytes_idxOf hbx hby hsx]
      simp only [List.map_map]; rfl
    obtain ⟨B, xs', ys', hP, hwx', hwy', hB⟩ := probe_find x y hx hy hn hm
    cases hwx.symm.trans hwx'; cases hwy.symm.trans hwy'
    rw [if_neg hw, hP] at hc
    have h := findK_enc (by decide) hm hc
    generalize findK x y = r at h ⊢
    rw [Arr.toList_long r (show longWords _ r.enc = some (Verify.elemsW 8 B) by rw [h]; rfl),
      Arr.toList_long x hwx, Arr.toList_long y hwy, findSpec]
    have hl : (Verify.elemsW 8 B).length = ys.length := by simpa using congrArg List.length hB
    apply List.ext_getElem (by simp [hl])
    intro j h1 _
    have hj := List.getElem_of_eq hB (by simpa using h1)
    simp only [List.getElem_map] at hj ⊢
    rw [idxOf_map_of_inj (fun _ _ => toInt64_inj)]
    exact toInt64_of_toNat hj
  cases hd : direct .long nx x.enc with
  | none => rw [show find x y = findK x y by unfold find; rw [hd]]; exact hK
  | some p =>
    obtain ⟨t, lo, hb⟩ := p
    cases hnb : Enc.bytesOf .long ny y.enc with
    | none => rw [show find x y = findK x y by unfold find; rw [hd, hnb]]; exact hK
    | some nb =>
      by_cases hw : Enc.WF .long ny (.bytes (probe t nx lo nb))
      · exact find_direct hy hd hn8 hm hnb hw
      · rw [show find x y = findK x y by unfold find; rw [hd, hnb]; exact dif_neg hw]; exact hK

/-- `x in y` on long columns is `inSpec`: `memberVec_mem` over the decoded operands, or, where `y` is
    marked `s`, `memberSortedBytes_mem`. Restrictions: `Readable` payloads; q's `s#` contract on `y`, as in
    `find_toList`; both counts below `USize.size`, which the kernel indexes by, and `8 · ny` too, which
    keeps the range below `2^63`. -/
theorem inK_long {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hx : Readable .long nx x.enc) (hy : Readable .long ny y.enc)
    (hs : y.attrCell.map (·.1) = some 1 → ∀ i j : Fin ny, i ≤ j → y.get i ≤ y.get j)
    (hn : ny < USize.size) (hm : nx < USize.size) :
    (inK x y).toList = inSpec x.toList y.toList := by
  obtain ⟨hk, hmd, hp, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hn
  obtain ⟨nk, nmd, np, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hm
  have h := memberColumn_long (y.attrCell.map (·.1) == some 1) nx x.enc x.attrCell ny y.enc
  rw [← x.val_eq] at h
  by_cases hw : (y.attrCell.map (·.1) == some 1 && worthHalving ny nx) = true
  · have ha : y.attrCell.map (·.1) = some 1 := by simp only [Bool.and_eq_true, beq_iff_eq] at hw; exact hw.1
    have hsy : ∀ i j (hi : i < ys.length) (hj : j < ys.length), i ≤ j → ys[i].toInt64 ≤ ys[j].toInt64 :=
      fun i j hi hj hij => by
        have := hs ha ⟨i, by omega⟩ ⟨j, by omega⟩ hij
        rwa [Arr.get_long y hwy i (by omega) hi, Arr.get_long y hwy j (by omega) hj] at this
    rw [if_pos hw, bytesOf_long hx hox] at h; simp only [memberSorted_long hy hoy] at h
    replace h := inK_enc (by decide) hm h
    generalize inK x y = r at h ⊢
    generalize operandBytes 8 hmd hp hk.toUSize = By at h hby
    generalize operandBytes 8 nmd np nk.toUSize = Bx at h hbx
    unfold inSpec
    rw [Arr.toList_long x hwx, Arr.toList_long y hwy]
    apply List.ext_getElem (by rw [Arr.length_toList]; simp [hlx])
    intro i h1 _
    have hi : i < nx := by rw [Arr.length_toList] at h1; exact h1
    rw [Arr.getElem_toList, Arr.get_bool_bits r h, memberSortedBytes_mem hby hbx hsy i (by omega)]
    simp only [List.getElem_map]
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, List.contains_iff_mem, mem_map_of_inj (fun _ _ => toInt64_inj)]
  obtain ⟨M, xs', ys', hP, hwx', hwy', hM⟩ := probe_member x y hx hy hm hn
  cases hwx.symm.trans hwx'; cases hwy.symm.trans hwy'
  rw [if_neg hw, hP] at h
  replace h := inK_enc (by decide) hm h
  generalize inK x y = r at h ⊢
  unfold inSpec
  rw [Arr.toList_long x hwx, Arr.toList_long y hwy]
  apply List.ext_getElem (by rw [Arr.length_toList]; simp [hlx])
  intro i h1 _
  have hi : i < nx := by rw [Arr.length_toList] at h1; exact h1
  rw [Arr.getElem_toList, Arr.get_bool_bits r h]
  simp only [List.getElem_map]
  rw [hM i (by omega)]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, List.contains_iff_mem, mem_map_of_inj (fun _ _ => toInt64_inj)]

theorem in_long {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hx : Readable .long nx x.enc) (hy : Readable .long ny y.enc)
    (hs : y.attrCell.map (·.1) = some 1 → ∀ i j : Fin ny, i ≤ j → y.get i ≤ y.get j)
    (hn8 : 8 * ny < USize.size) (hm : nx < USize.size) :
    («in» x y).toList = inSpec x.toList y.toList := by
  have hK := inK_long hx hy hs (by have := USize.size_le; omega) hm
  cases hd : direct .long ny y.enc with
  | none => rw [show «in» x y = inK x y by unfold «in»; rw [hd]]; exact hK
  | some p =>
    obtain ⟨t, lo, hb⟩ := p
    cases hnb : Enc.bytesOf .long nx x.enc with
    | none => rw [show «in» x y = inK x y by unfold «in»; rw [hd, hnb]]; exact hK
    | some nb =>
      by_cases hw : Enc.WF .boolean nx (.bits (Ew.cmp Ew.lt Ew.i64 Ew.va (probe t ny lo nb) (one ny.toUInt64) nx.toUSize))
      · exact in_direct hx hd hn8 hm hnb hw
      · rw [show «in» x y = inK x y by unfold «in»; rw [hd, hnb]; exact dif_neg hw]; exact hK

/-! ## Boolean columns -/

/-- A readable boolean column is `bits`. -/
theorem readable_bits {n : Nat} {e : Enc} (h : Readable .boolean n e) : ∃ b, e = .bits b := by
  cases e <;> first | exact ⟨_, rfl⟩ | exact False.elim h

/-- A boolean `bits` column lists its first `m` bits. -/
theorem Arr.toList_bits {m : Nat} (x : Arr .boolean m) {b : ByteArray} (hc : x.enc = .bits b) :
    x.toList = (List.range m).map (Column.bitAt b) :=
  List.ext_getElem (by rw [Arr.length_toList]; simp) fun i h1 _ => by
    rw [Arr.getElem_toList, Arr.get_bool_bits x hc]; simp

/-- `findBit` is the first index of the needle among the first `n` bits, `n` at a miss. -/
theorem findBit_idxOf (b : ByteArray) {n : Nat} (hn : n < USize.size) (v : Bool) :
    (findBit n.toUSize b v).toNat = ((List.range n).map (Column.bitAt b)).idxOf v := by
  have hl := Verify.idxOf_le_length v ((List.range n).map (Column.bitAt b))
  rw [List.length_map, List.length_range] at hl
  unfold findBit
  rw [USize.toNat_ofNat_of_lt' hn, Verify.find?_range_getD, USize.toNat_ofNat_of_lt' (by omega)]

/-- `x?y` on boolean columns is `findSpec`: `findBitVec` writes `findBit_idxOf` per needle. -/
theorem find_bits {nx : Nat} {x : Arr .boolean nx} {ny : Nat} {y : Arr .boolean ny}
    {xb yb : ByteArray} (hxc : x.enc = .bits xb) (hyc : y.enc = .bits yb)
    (hn : nx < USize.size) (hm : ny < USize.size) :
    (find x y).toList = findSpec x.toList y.toList := by
  have hc : findColumn .boolean (x.attrCell.map (·.1) == some 1) nx x.enc y.1 =
      some (.vector .long ny (.bytes (findBitVec nx.toUSize xb ny.toUSize yb)) none) := by rw [y.val_eq, hxc, hyc]; rfl
  have hd : direct .boolean nx x.enc = none := rfl
  have h : (find x y).enc = .bytes (findBitVec nx.toUSize xb ny.toUSize yb) := by
    rw [show find x y = findK x y by unfold find; rw [hd]]; exact findK_enc (by decide) hm hc
  generalize find x y = r at h ⊢
  have hw : Verify.elemsW 8 (findBitVec nx.toUSize xb ny.toUSize yb) =
      (List.range ny).map fun j => (findBit nx.toUSize xb (Column.bitAt yb j)).toUInt64 := by
    unfold findBitVec
    rw [Verify.elemsW_foldl _ 8 (by decide) (by decide) _ (fun _ _ => UInt64.toNat_lt _), USize.toNat_ofNat_of_lt' hm]
  rw [Arr.toList_long r (show longWords _ r.enc = some _ by rw [h]; rfl), hw,
    Arr.toList_bits x hxc, Arr.toList_bits y hyc, findSpec, List.map_map, List.map_map]
  refine List.map_congr_left fun j _ => toInt64_of_toNat ?_
  rw [USize.toNat_toUInt64, findBit_idxOf xb hn]

/-- `x in y` on boolean columns is `inSpec`, from `memberBits_mem`. -/
theorem in_bits {nx : Nat} {x : Arr .boolean nx} {ny : Nat} {y : Arr .boolean ny}
    {xb yb : ByteArray} (hxc : x.enc = .bits xb) (hyc : y.enc = .bits yb)
    (hn : ny < USize.size) (hm : nx < USize.size) :
    («in» x y).toList = inSpec x.toList y.toList := by
  have hc : memberColumn .boolean (y.attrCell.map (·.1) == some 1) x.1 ny y.enc =
      some (.vector .boolean nx (.bits (memberBits nx.toUSize xb ny.toUSize yb)) none) := by rw [x.val_eq, hxc, hyc]; rfl
  have hd : direct .boolean ny y.enc = none := rfl
  have h : («in» x y).enc = .bits (memberBits nx.toUSize xb ny.toUSize yb) := by
    rw [show «in» x y = inK x y by unfold «in»; rw [hd]]; exact inK_enc (by decide) hm hc
  generalize «in» x y = r at h ⊢
  obtain ⟨-, hg⟩ := Verify.memberBits_mem nx.toUSize ny.toUSize xb yb
  rw [USize.toNat_ofNat_of_lt' hm, USize.toNat_ofNat_of_lt' hn] at hg
  unfold inSpec
  rw [Arr.toList_bits x hxc, Arr.toList_bits y hyc]
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 _
  have hi : i < nx := by rw [Arr.length_toList] at h1; exact h1
  rw [Arr.getElem_toList, Arr.get_bool_bits r h, hg i (by omega)]
  simp only [List.getElem_map, List.getElem_range, hi, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, List.contains_iff_mem]

/-- An injective map commutes with erasing repeats. -/
theorem eraseDups_map_of_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) : ∀ l : List α, (l.map f).eraseDups = l.eraseDups.map f
  | [] => rfl
  | a :: l => by
    have hp : ((fun b => !b == f a) ∘ f) = fun b => !b == a := funext fun b => by
      simp only [Function.comp_apply]; congr 1; exact Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact ⟨hf b a, congrArg f⟩)
    rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.filter_map, hp,
      eraseDups_map_of_inj hf (l.filter fun b => !b == a), List.map_cons]
termination_by l => l.length
decreasing_by simp only [List.length_cons]; have := List.length_filter_le (fun b => !b == a) l; omega

/-- `x?y` on symbol columns is `findSpec`: `findSymColumn_idxOf` over the symbols' bytes (`Arr.toList_sym`),
    which determine the strings (`toUTF8_inj`). -/
theorem find_sym {nx : Nat} {x : Arr .symbol nx} {ny : Nat} {y : Arr .symbol ny}
    (hx : Readable .symbol nx x.enc) (hy : Readable .symbol ny y.enc) (hm : ny < USize.size) :
    (find x y).toList = findSpec x.toList y.toList := by
  have hd : direct .symbol nx x.enc = none := rfl
  have hc : findColumn .symbol (x.attrCell.map (·.1) == some 1) nx x.enc y.1 =
      (findSymColumn nx x.enc ny y.enc).map fun out => .vector .long (out.size / 8) (.bytes out) none := by
    rw [y.val_eq]; rfl
  have hX := Arr.toList_sym x hx.2
  have hY := Arr.toList_sym y hy.2
  cases hf : findSymColumn nx x.enc ny y.enc with
  | none =>
    have hs := KernelWF.findColumn_isSome (s := x.attrCell.map (·.1) == some 1) (a := y.attrCell) x.wf y.wf
      (by decide : QAtomicType.symbol ≠ .general)
    rw [← y.val_eq, hc, hf] at hs; simp at hs
  | some out =>
    have h : (find x y).enc = .bytes out := by
      rw [show find x y = findK x y by unfold find; rw [hd]]; exact findK_enc (by decide) hm (by rw [hc, hf]; rfl)
    generalize find x y = r at h ⊢
    obtain ⟨hs, hv⟩ := Verify.findSymColumn_idxOf hx.1 hy.1 hf
    have hl : (Verify.symsOf ny y.enc).length = ny := by rw [← hY, List.length_map, Arr.length_toList]
    rw [Arr.toList_long r (show longWords _ r.enc = some _ by rw [h]; rfl)]
    apply List.ext_getElem (by
      rw [List.length_map, Verify.elemsW, List.length_map, List.length_range, findSpec, List.length_map,
        Arr.length_toList, hs, hl]; omega)
    intro j h1 h2
    have hj : j < (Verify.symsOf ny y.enc).length := by
      rw [hl]; rw [findSpec, List.length_map, Arr.length_toList] at h2; exact h2
    simp only [List.getElem_map, Verify.elemsW, List.getElem_range, findSpec]
    refine toInt64_of_toNat ?_
    rw [hv j hj]
    simp only [← hX, ← hY, List.getElem_map]
    exact idxOf_map_of_inj (fun _ _ => toUTF8_inj) _ _

/-- `x in y` on symbol columns is `inSpec`: `memberColumn_symbol` over the symbols' bytes. -/
theorem in_sym {nx : Nat} {x : Arr .symbol nx} {ny : Nat} {y : Arr .symbol ny}
    (hx : Readable .symbol nx x.enc) (hy : Readable .symbol ny y.enc) (hN : nx < USize.size) :
    («in» x y).toList = inSpec x.toList y.toList := by
  have hd : direct .symbol ny y.enc = none := rfl
  have hX := Arr.toList_sym x hx.2
  have hY := Arr.toList_sym y hy.2
  cases hm : memberColumn .symbol (y.attrCell.map (·.1) == some 1) x.1 ny y.enc with
  | none =>
    have hs := KernelWF.memberColumn_isSome (s := y.attrCell.map (·.1) == some 1) (a := x.attrCell) x.wf y.wf
      (by decide : QAtomicType.symbol ≠ .general)
    rw [← x.val_eq, hm] at hs; simp at hs
  | some v =>
    obtain ⟨b, rfl, hb⟩ := Verify.memberColumn_symbol hx.1 hy.1 y.wf (by rw [x.val_eq] at hm; exact hm)
    have h : («in» x y).enc = .bits b := by
      rw [show «in» x y = inK x y by unfold «in»; rw [hd]]; exact inK_enc (by decide) hN hm
    generalize «in» x y = r at h ⊢
    have hl : (Verify.symsOf nx x.enc).length = nx := by rw [← hX, List.length_map, Arr.length_toList]
    rw [Arr.toList_bits r h, inSpec]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, Arr.length_toList])
    intro i h1 _
    have hi : i < (Verify.symsOf nx x.enc).length := by rw [hl]; simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hb i hi]
    simp only [← hX, ← hY, List.getElem_map]
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, List.contains_iff_mem, mem_map_of_inj (fun _ _ => toUTF8_inj)]

/-- `?x` on a symbol column is `distinctSpec`: `distinctSyms_eraseDups` on a blob, `distinctIds_eraseDups`
    on an interned column, read back through the bytes (`Arr.toList_sym`). Restrictions: q's `u#` contract,
    as `distinct_toList`'s. -/
theorem distinct_sym {nx : Nat} {x : Arr .symbol nx}
    (hx : Readable .symbol nx x.enc) (hu : x.attrCell.map (·.1) = some 2 → x.toList.Nodup) :
    (distinct x).2.toList = distinctSpec x.toList := by
  by_cases ha : x.attrCell.map (·.1) = some 2
  · rw [show distinct x = ⟨nx, x⟩ by simp [distinct, ha]]; exact (eraseDups_of_nodup _ (hu ha)).symm
  have hX := Arr.toList_sym x hx.2
  obtain ⟨nn, nb, no, hc, he⟩ : ∃ nn nb no, distinctColumn .symbol nx x.enc =
      some (.vector .symbol nn (.syms nb no) none) ∧
      Verify.symsOf nn (.syms nb no) = (Verify.symsOf nx x.enc).eraseDups := by
    have hk := hx.1
    cases hxc : x.enc with
    | syms b o => exact ⟨_, _, _, rfl, Verify.distinctSyms_eraseDups b o⟩
    | enum d o ids => rw [hxc] at hk; exact ⟨_, _, _, rfl, Verify.distinctIds_eraseDups hk⟩
    | _ => rw [hxc] at hk; exact hk.elim
  have h := distinctK_enc (x := x) (by decide) hc
  rw [show distinct x = distinctK x by
    unfold distinct; rw [show (x.attrCell.map (·.1) == some 2) = false by simp [ha]]; rfl]
  generalize distinctK x = D at h ⊢
  obtain ⟨nr, r⟩ := D
  have hR : r.toList.map (·.toUTF8.data.toList) = (x.toList.map (·.toUTF8.data.toList)).eraseDups := by
    have hr : Verify.symsOf nr r.enc = Verify.symsOf nn (.syms nb no) := by rw [h.2]; rfl
    rw [hX, ← he, ← hr]
    refine Arr.toList_sym r fun k hk => ?_
    rw [hr, he, ← hX, eraseDups_map_of_inj (fun _ _ => toUTF8_inj)] at hk
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hk
    exact ⟨s, rfl⟩
  rw [eraseDups_map_of_inj (fun _ _ => toUTF8_inj)] at hR
  exact (List.map_inj_right (fun _ _ => toUTF8_inj)).1 hR

/-- `?x` on a boolean column is `distinctSpec`, from `bitFirsts_eraseDups`. Restrictions: q's `u#`
    contract, as `distinct_toList`'s; `nx < USize.size`, which `bitFirsts` counts by. -/
theorem distinct_bits {nx : Nat} {x : Arr .boolean nx}
    {xb : ByteArray} (hxc : x.enc = .bits xb) (hn : nx < USize.size)
    (hu : x.attrCell.map (·.1) = some 2 → x.toList.Nodup) : (distinct x).2.toList = distinctSpec x.toList := by
  by_cases ha : x.attrCell.map (·.1) = some 2
  · rw [show distinct x = ⟨nx, x⟩ by simp [distinct, ha]]; exact (eraseDups_of_nodup _ (hu ha)).symm
  have hr := distinctK_enc (x := x) (by decide)
    (show distinctColumn .boolean nx x.enc = some (.vector .boolean _ (.bits _) none) by rw [hxc]; rfl)
  rw [show distinct x = distinctK x by
    unfold distinct; rw [show (x.attrCell.map (·.1) == some 2) = false by simp [ha]]; rfl]
  generalize distinctK x = D at hr ⊢
  obtain ⟨nr, r⟩ := D
  have hnr : nr = (bitFirsts nx xb).length := hr.1
  rw [Arr.toList_bits r hr.2, distinctSpec, Arr.toList_bits x hxc]
  apply List.ext_getElem (by simp [hnr, Verify.bitFirsts_eraseDups nx xb hn])
  intro i h1 _
  have hi : i < (bitFirsts nx xb).length := by simpa [hnr] using h1
  rw [List.getElem_map, List.getElem_range, Column.bitAt_packBits _ i (by simpa using hi),
    getElem!_pos _ i (by simpa using hi)]
  simp [Column.boolOf, Verify.bitFirsts_eraseDups nx xb hn]

/-- Two lawful `==` on one type are one instance: each answers `true` exactly at equal arguments. -/
theorem beq_inst_eq {α : Type} (i₁ i₂ : BEq α) (h₁ : @LawfulBEq α i₁) (h₂ : @LawfulBEq α i₂) : i₁ = i₂ := by
  have e : ∀ a b : α, @BEq.beq α i₁ a b = @BEq.beq α i₂ a b := fun a b =>
    Bool.eq_iff_iff.2 ((@beq_iff_eq α i₁ h₁ a b).trans (@beq_iff_eq α i₂ h₂ a b).symm)
  cases i₁; cases i₂; congr; funext a b; exact e a b

/-- Under a lawful `==` the spec does not depend on which instance supplied it. -/
theorem findSpec_inst {α : Type} (i₁ i₂ : BEq α) [h₁ : @LawfulBEq α i₁] [h₂ : @LawfulBEq α i₂] (xs ys : List α) :
    @findSpec α i₁ xs ys = @findSpec α i₂ xs ys := by cases beq_inst_eq i₁ i₂ h₁ h₂; rfl

theorem inSpec_inst {α : Type} (i₁ i₂ : BEq α) [h₁ : @LawfulBEq α i₁] [h₂ : @LawfulBEq α i₂] (xs ys : List α) :
    @inSpec α i₁ xs ys = @inSpec α i₂ xs ys := by cases beq_inst_eq i₁ i₂ h₁ h₂; rfl

/-! ## The laws, over every readable type -/

/-- `x?y` is `findSpec` wherever both operands are `Readable` at their type: `find_long` (the probe, the
    direct table or the halving) at `long`, `find_bits` at `boolean`. Restrictions: `Ascends x` (q's
    `s#` contract, read at `long` only); both counts below `USize.size`, which the kernels index by, and
    `8 · nx` too, which keeps the direct range below `2^63`. -/
theorem find_toList {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny}
    (hx : Readable a nx x.enc) (hy : Readable a ny y.enc) (hs : Ascends x)
    (hn8 : 8 * nx < USize.size) (hm : ny < USize.size) :
    (find x y).toList = findSpec x.toList y.toList := by
  cases a
  case long => exact (find_long hx hy hs hn8 hm).trans (findSpec_inst _ _ _ _)
  case boolean =>
    obtain ⟨_, hxc⟩ := readable_bits hx
    obtain ⟨_, hyc⟩ := readable_bits hy
    exact (find_bits hxc hyc (by have := USize.size_le; omega) hm).trans (findSpec_inst _ _ _ _)
  case symbol => exact (find_sym hx hy hm).trans (findSpec_inst _ _ _ _)
  all_goals exact False.elim hx

/-- `x in y` is `inSpec` wherever both operands are `Readable` at their type: `in_long` at `long`,
    `in_bits` at `boolean`. Restrictions as `find_toList`'s, with `y` the haystack. -/
theorem in_toList {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny}
    (hx : Readable a nx x.enc) (hy : Readable a ny y.enc) (hs : Ascends y)
    (hn8 : 8 * ny < USize.size) (hm : nx < USize.size) :
    («in» x y).toList = inSpec x.toList y.toList := by
  cases a
  case long => exact (in_long hx hy hs hn8 hm).trans (inSpec_inst _ _ _ _)
  case boolean =>
    obtain ⟨_, hxc⟩ := readable_bits hx
    obtain ⟨_, hyc⟩ := readable_bits hy
    exact (in_bits hxc hyc (by have := USize.size_le; omega) hm).trans (inSpec_inst _ _ _ _)
  case symbol => exact (in_sym hx hy hm).trans (inSpec_inst _ _ _ _)
  all_goals exact False.elim hx

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
theorem bin_toList {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny}
    (hx : Readable .long nx x.enc) (hy : Readable .long ny y.enc) (hn : nx < USize.size) (hm : ny < USize.size)
    (hsort : ∀ i j : Fin nx, i ≤ j → x.get i ≤ x.get j) :
    (bin x y).toList = binSpec x.toList y.toList := by
  obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := operand_long x hx hn
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := operand_long y hy hm
  have hc := binColumn_long false nx x.enc ny y.enc y.attrCell
  rw [← y.val_eq, hox, hoy] at hc
  have h : (bin x y).enc = .bytes (binBytes 8 false true false (operandBytes 8 hmd hp hk.toUSize)
      (operandBytes 8 nmd np nk.toUSize)) := bin_enc (by decide) (by decide) hm (by rw [hc]; rfl)
  generalize bin x y = r at h ⊢
  generalize operandBytes 8 hmd hp hk.toUSize = hb at h hbx
  generalize operandBytes 8 nmd np nk.toUSize = kb at h hby
  obtain ⟨hsx, gx⟩ := elemsW8_get hbx
  have hxn : hb.size / 8 = nx := hsx.trans hlx
  have hyn : kb.size / 8 = ny := (elemsW8_get hby).1.trans hly
  have hle : ∀ i j (hi : i < nx) (hj : j < nx), (ordKey 8 false true (Column.bitsAt hb (i * 8) 8) ≤
      ordKey 8 false true (Column.bitsAt hb (j * 8) 8) ↔ x.get ⟨i, hi⟩ ≤ x.get ⟨j, hj⟩) :=
    fun i j hi hj => by
      rw [ordKey_long, ordKey_long, rank_i64_le_iff, Arr.get_long x hwx i hi (by omega),
        Arr.get_long x hwx j hj (by omega), gx i (by omega), gx j (by omega)]
  unfold binSpec
  rw [Arr.toList_long_bytes r h, Arr.toList_long x hwx, Arr.toList_long y hwy, ← hbx, ← hby,
    Verify.elemsW, Verify.elemsW, hxn, hyn]
  simp only [List.map_map, List.countP_map]
  apply List.map_congr_left
  intro j hj'
  have hj := List.mem_range.1 hj'
  have hk := Verify.bitsAt_binBytes 8 false true false hb kb j (by rw [usize_eight, hyn]; exact hj)
  simp only [usize_eight, Bool.false_eq_true, ↓reduceIte, Nat.mul_comm 8 j, hxn] at hk
  obtain ⟨hp', hlo, hhi⟩ := Verify.binStep_spec 8 false true false hb
    (ordKey 8 false true (Column.bitsAt kb (j * 8) 8)) nx
    (fun i j hij hjn => (hle i j (by omega) hjn).2 (hsort ⟨i, by omega⟩ ⟨j, hjn⟩ hij))
  simp only [Bool.false_eq_true, ↓reduceIte] at hlo hhi
  have hcmp : ∀ i, i < nx → (ordKey 8 false true (Column.bitsAt hb (i * 8) 8) ≤
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

private def ans {α β : Type} (f : β → α) (r : β) : Option α := some (f r)
private def wc {nx} (x : Arr .long nx) := if h : (negs x).size = 0 then some (whereCounts x h) else none

private def bs : Arr .boolean 5 := Arr.mk (.bits (ByteArray.mk #[0b10110])) (by decide)
private def cs : Arr .long 3 := Arr.mk (.bytes (packLongs [2, 0, 1])) (by decide)
private def xs : Arr .long 5 := Arr.mk (.bytes (packLongs [5, 3, 5, 9, 3])) (by decide)
-- the same five longs Frame-of-Reference encoded: the small-range path
private def xf : Arr .long 5 :=
  Arr.mk (.foR (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).1 (Coc.encode 8 (packLongs [5, 3, 5, 9, 3])).2) (foRLongs_wf [5, 3, 5, 9, 3])
private def ys : Arr .long 4 := Arr.mk (.bytes (packLongs [3, 9, 7, 0x8000000000000000])) (by decide)
private def ss : Arr .long 4 := Arr.mk (.bytes (packLongs [1, 3, 3, 7])) (by decide)
private def ks : Arr .long 5 := Arr.mk (.bytes (packLongs [0, 3, 5, 9, -1])) (by decide)
private def sy : Arr .symbol 3 :=
  Arr.mk (.syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8]) (by decide)
private def sn : Arr .symbol 2 :=
  Arr.mk (.syms (ByteArray.mk #[97, 0, 122, 0]) #[0, 2, 4]) (by decide)

#guard ans (·.2.toList) («where» bs) == some (whereSpec bs.toList)
#guard ans (·.2.toList) («where» bs) == some [1, 2, 4]
#guard (wc cs).map (·.2.toList) == some (whereCountsSpec cs.toList)
#guard (wc cs).map (·.2.toList) == some [0, 0, 2]
private def csf : Arr .long 4 :=
  Arr.mk (.foR (Coc.encode 8 (packLongs [2, 0, 3, 1])).1 (Coc.encode 8 (packLongs [2, 0, 3, 1])).2) (foRLongs_wf [2, 0, 3, 1])
#guard (wc csf).map (·.2.toList) == some (whereCountsSpec [2, 0, 3, 1])
#guard (wc ys).isNone
#guard (direct .long 5 xf.enc).isSome && (direct .long 5 xs.enc).isNone
-- `foR` columns holding `0N`: the encoder keeps it out of `[base, maxv]` as a patch exception, so
-- block metadata alone would size a table with no slot for it; `Coc.range` declines, `direct` too
private def foRL (vs : List Int64) : (m : Nat) × Arr .long m :=
  ⟨vs.length,
    Arr.mk (.foR (Coc.encode 8 (packLongs vs)).1 (Coc.encode 8 (packLongs vs)).2) (foRLongs_wf vs)⟩
private def xn := foRL [0x8000000000000000, -0x7fffffffffffffff]
private def xn3 := foRL [0x8000000000000000, -0x7fffffffffffffff, 0x8000000000000000]
private def xa := foRL [0x8000000000000000, 0x8000000000000000, 0x8000000000000000]
private def nn : Arr .long 1 := Arr.mk (.bytes (packLongs [0x8000000000000000])) (by decide)
-- operands of different lengths, each with its own
private def longs : List ((m : Nat) × Arr .long m) := [⟨_, xs⟩, ⟨_, xf⟩, xn, xn3, xa]
#guard [xn, xn3, xa].all fun x => (direct .long x.1 x.2.enc).isNone
#guard ans (·.toList) (find xn.2 nn) == some [0]
#guard ans (·.toList) («in» nn xn.2) == some [true]
#guard ans (·.2.toList) (distinct xn3.2) == some [0x8000000000000000, -0x7fffffffffffffff]
#guard ans (·.toList) (find xa.2 ys) == some [3, 3, 3, 0]
#guard ans (·.2.toList) (distinct xa.2) == some [0x8000000000000000]
#guard longs.all fun x => ans (·.2.toList) (distinct x.2) == some (distinctSpec x.2.toList)
#guard ans (·.2.toList) (distinct xf) == some [5, 3, 9]
#guard ans (·.2.toList) (distinct sy) == some (distinctSpec sy.toList)
#guard longs.all fun x => ans (·.toList) (find x.2 ys) == some (findSpec x.2.toList ys.toList)
#guard ans (·.toList) (find xf ys) == some [1, 3, 5, 5]
#guard ans (·.toList) (find sy sn) == some (findSpec sy.toList sn.toList)
#guard longs.all fun x => ans (·.toList) («in» ys x.2) == some (inSpec ys.toList x.2.toList)
#guard ans (·.toList) («in» ys xf) == some [true, true, false, false]
#guard ans (·.toList) («in» sn sy) == some (inSpec sn.toList sy.toList)
#guard ans (·.toList) (bin ss ks) == some (binSpec ss.toList ks.toList)
#guard ans (·.toList) (bin ss ks) == some [-1, 2, 2, 3, -1]
-- marked `s`: dense, and `foR` too wide for `direct`, so both take the halving (`worthHalving 4 1`)
private def sb : Arr .long 4 := Arr.mark 1 <|
  Arr.mk (.bytes (packLongs [1, 3, 3, 7])) (by decide)
private def sf : Arr .long 4 := Arr.mark 1 <| let vs : List Int64 := [1, 3000000, 3000000, 7000000]
  Arr.mk (.foR (Coc.encode 8 (packLongs vs)).1 (Coc.encode 8 (packLongs vs)).2) (foRLongs_wf vs)
private def n1 (v : Int64) := (foRL [v]).2
#guard worthHalving 4 1 && (direct .long 4 sf.enc).isNone
#guard [3, 5, 1, 7, 0x8000000000000000, 3000000].all fun v => [sb, sf].all fun x =>
  ans (·.toList) (find x (n1 v)) == some (findSpec x.toList [v]) &&
  ans (·.toList) («in» (n1 v) x) == some (inSpec [v] x.toList)
#guard ans (·.toList) (find sb (n1 3)) == some [1] && ans (·.toList) (find sf (n1 3000000)) == some [1]
#guard ans (·.toList) («in» (n1 5) sb) == some [false]
-- marked `u`: `?x` answers the column itself
private def ub : Arr .long 3 := Arr.mark 2 <| Arr.mk (.bytes (packLongs [5, 3, 9])) (by decide)
private def uf : Arr .long 3 := Arr.mark 2 <|
  Arr.mk (.foR (Coc.encode 8 (packLongs [5, 3, 9])).1 (Coc.encode 8 (packLongs [5, 3, 9])).2) (foRLongs_wf [5, 3, 9])
#guard [ub, uf].all fun x => ans (·.2.toList) (distinct x) == some (distinctSpec x.toList)
#guard ans (·.2.toList) (distinct uf) == some [5, 3, 9]
-- booleans: `findBitVec`, `memberBits`, a haystack with no `1b` and one with no `0b`
private def b1 : Arr .boolean 3 := Arr.mk (.bits (ByteArray.mk #[0b000])) (by decide)
private def bools : List ((m : Nat) × Arr .boolean m) := [⟨_, bs⟩, ⟨_, b1⟩]
#guard bools.all fun h => bools.all fun n =>
  ans (·.toList) (find h.2 n.2) == some (findSpec h.2.toList n.2.toList) &&
  ans (·.toList) («in» n.2 h.2) == some (inSpec n.2.toList h.2.toList)
#guard ans (·.toList) (find b1 bs) == some [0, 3, 3, 0, 3]

end Checks

#print axioms find
#print axioms «in»
#print axioms distinct
#print axioms whereCounts
#print axioms bin
#print axioms firstTable_spec
#print axioms probe_spec
#print axioms find_direct
#print axioms in_direct
#print axioms distinct_direct
#print axioms where_toList
#print axioms firstsOf_map_eraseDups
#print axioms distinct_toList
#print axioms find_long
#print axioms in_long
#print axioms probe_find
#print axioms probe_member
#print axioms find_bits
#print axioms in_bits
#print axioms find_sym
#print axioms in_sym
#print axioms distinct_sym
#print axioms distinct_bits
#print axioms find_toList
#print axioms in_toList
#print axioms bin_toList

end LeetQ.Rel.Find
