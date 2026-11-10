/-
  Elementwise verbs on the RelRep core (design §3 rows `x+y`, `x+a`, `-x`, `x<y`, `~x`, `f':x`) and the
  dyadic rule of §4: the same key is ONE qlean call on the value columns, different keys go through
  `align` with the triple `(f, fl, fr)`. Every op is a whole-column kernel; no element is read here.
  The spec is List-level, over `toList`, element by element through qlean's `Dep.elem` (the tested
  interpreter, `Eval.dyadAtom`).
-/
import LeetQ.Rel.Core
import QLean.Kernel.Structural
import QLean.Dep.Dyadic
import QLean.Verify.Elementwise
import LeetQ.Rel.KernelWF.Dyad
import LeetQ.Rel.KernelWF.Mon
import LeetQ.Rel.Find

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

namespace Ew

/-- One `dyadColumn` call — qlean's per-encoding dispatch (`bytes`, `foR`, ALP, `bits`, `syms`) —
    checked against the result type `rt` the caller asked for. -/
def dyad (v : Prim.Dyadic) (shape : UInt8) (t u rt : QAtomicType) (na : Nat) (a : Enc) (nb : Nat) (b : Enc)
    (n : Nat) : Except String (Arr rt n) :=
  match dyadColumn v shape t u na a nb b with
  | none => .error s!"Ew: no qlean kernel claims {repr v} at {repr t}, {repr u} (shape {shape})"
  | some (rt', c) =>
    if rt' = rt then Arr.of rt n c s!"Ew {repr v}" else .error s!"Ew {repr v}: answers {repr rt'}, not {repr rt}"

/-- The payload of a one-element vector holding `a`: how an atom reaches a kernel, once per call. -/
def atomCol (t : QAtomicType) (a : QAtom) (ht : t ≠ .general := by first | decide | assumption) :
    Except String Enc :=
  match Enc.ofAtoms t #[a] ht with
  | some c => .ok c
  | none => .error s!"Ew: Enc.ofAtoms refused an atom at {repr t}"

end Ew

variable {t u : QAtomicType} {n : Nat}

/-- `x f y` element by element: `yv` a value column on `x`'s positions. A list's or a dict's values go in
    alone; the positions or the key stay where they are. Comparisons are this at `rt = boolean`
    (`Ew.cmp` in the design is the same `dyadColumn` call, `cmpPayload` inside). -/
def Ew.val (v : Prim.Dyadic) (rt : QAtomicType) (x : Arr t n) (yv : Arr u n) :
    Except String (Arr rt n) :=
  Ew.dyad v Ew.vv t u rt n x.enc n yv.enc n

/-- `a f x`: the atom on the left, the one atom shape `av` that reaches a kernel. -/
def Ew.atomVal (v : Prim.Dyadic) (rt : QAtomicType) (a : Carrier t) (x : Arr u n)
    (ht : t ≠ .general := by first | decide | assumption) : Except String (Arr rt n) := do
  Ew.dyad v Ew.av t u rt 1 (← Ew.atomCol t (Carrier.atom a)) n x.enc n

/-- The verb `v'` with `x v a = a v' x`, where one exists. -/
def Ew.flip : Prim.Dyadic → Option Prim.Dyadic
  | .add => some .add | .mul => some .mul | .lesser => some .lesser | .greater => some .greater
  | .eq => some .eq | .ne => some .ne | .lt => some .gt | .gt => some .lt | .le => some .ge
  | .ge => some .le | _ => none

/-- `x f a`, rewritten onto `av` by `flip` (`x<a = a>x`). `-` and `%` keep `va`, which the kernel has:
    `(−a)+x` changes the type rule at temporal types (`d−d` is `int`, `d+(−d)` is `'type`) and
    `(1/a)×x` is not `x/a` bit for bit in floats. -/
def Ew.valAtom (v : Prim.Dyadic) (rt : QAtomicType) (x : Arr t n) (a : Carrier u)
    (hu : u ≠ .general := by first | decide | assumption) : Except String (Arr rt n) :=
  match Ew.flip v with
  | some vf => Ew.atomVal vf rt a x
  | none => do Ew.dyad v Ew.va t u rt n x.enc 1 (← Ew.atomCol u (Carrier.atom a)) n

/-- One `monColumn` on a well-formed payload of `m < USize.size` elements, at a name `monNames` lists and
    the type `monResultType` answers. -/
def Ew.monK (name : String) (rt : QAtomicType) {m : Nat} (e : Enc) (hw : Enc.WF t m e)
    (hname : name ∈ KernelWF.monNames) (hrt : monResultType name t = some rt) (hg : t ≠ .general)
    (hm : m < USize.size) : Arr rt m :=
  have hs := KernelWF.monColumn_isSome hname hrt hg hw hm
  Arr.mk ((monColumn name t m e).get hs).2 (KernelWF.monColumn_wf hname hg hw hm (KernelWF.monColumn_get hrt hs))

/-- `f x` for qlean's monadic kernels by name (`neg`, `abs`, `reciprocal`, `null`, …): one `monColumn`.
    Past the kernel's `USize` count, the same kernel on each element's one-element column, atom by atom. -/
def Ew.mon (name : String) (rt : QAtomicType) (x : Arr t n)
    (hname : name ∈ KernelWF.monNames := by first | decide | assumption)
    (hrt : monResultType name t = some rt := by first | rfl | assumption)
    (hg : t ≠ .general := by first | decide | assumption) : Arr rt n :=
  if hn : n < USize.size then Ew.monK name rt x.enc x.wf hname hrt hg hn
  else
    have hr := KernelWF.monResultType_ne_general hrt hg
    Find.atomsOf rt hr (fun i : Fin n =>
      let one := Find.atomsOf (m := 1) t hg (fun _ : Unit => Carrier.atom (x.get i) hg) (fun _ => by simp) [()] rfl
      Carrier.atom ((Ew.monK name rt one.enc one.wf hname hrt hg (by have := USize.size_eq; omega)).get
        ⟨0, Nat.one_pos⟩) hr)
      (fun _ => by simp) (List.finRange n) (by simp)

/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : Nat) (b : ByteArray) : ByteArray := Ew.bit (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m.toUSize

/-- `~x`: `Ew.notBits` of the column when its count fits the kernel's `USize`; else, and on a payload
    `Enc.WF .boolean` excludes, q's `not` atom by atom. -/
def Ew.not (x : Arr .boolean n) : Arr .boolean n :=
  let ref := fun (_ : Unit) => Find.atomsOf .boolean (by decide) (fun i : Fin n => .boolean !(x.get i))
    (fun _ => rfl) (List.finRange n) (by simp)
  if hn : n < USize.size then
    match x.enc with
    | .bits b => Arr.mk (.bits (Ew.notBits n b))
        (KernelWF.bits_wf (by rw [Ew.notBits, KernelWF.bit_size, USize.toNat_ofNat_of_lt' hn]))
    | _ => ref ()
  else ref ()

/-- `x op y` bit by bit on two long columns over the same positions, `op` one of qlean's `Ew.band`,
    `Ew.bor`, `Ew.bandnot` (`x & ~y`): `bitwPayload`, a dense pass; an encoded operand is decoded first.
    q has no verb for these, so they are not `Prim.Dyadic`s. Past the kernel's `USize` count, `bitwStep`
    atom by atom. -/
def Ew.bitwise (op : UInt8) (x y : Arr .long n) : Arr .long n :=
  if hn : n < USize.size then
    Arr.mk ((bitwPayload op n x.enc y.enc).get (KernelWF.bitwPayload_isSome x.wf y.wf))
      (KernelWF.bitwPayload_wf hn (Option.some_get _).symm)
  else Find.atomsOf .long (by decide)
    (fun i : Fin n => .long (Ew.bitwStep op (x.get i).toUInt64 (y.get i).toUInt64).toInt64) (fun _ => rfl)
    (List.finRange n) (by simp)

/-- The raw bits of a one-element payload, as `shiftColumn`'s `fill` takes them. -/
def Ew.atomBits (t : QAtomicType) (e : Enc) : Except String UInt64 :=
  match e with
  | .bits b => .ok (if Column.bitAt b 0 then 1 else 0)
  | _ => match Enc.bytesOf t 1 e, t.width with
    | some b, some w => .ok (Column.bitsAt b 0 w)
    | _, _ => .error s!"Ew: no fixed-width payload for an atom at {repr t}"

/-- `seed f': x`: `r[i] = x[i] f x[i-1]`, `x[-1] = seed` (`-':` with seed `0` keeps `x[0]` raw). The
    prior operand is `shiftColumn` (`shiftBytes`/`shiftFoR`/`shiftALP`/`shiftBits`) and then one
    `dyadColumn`; on two `foR`s that pair is `priorValFoR`'s body. A dense fused kernel reading the
    one payload at offset `−w` does not exist in qlean: this is two passes there. -/
def Ew.prior (v : Prim.Dyadic) (rt : QAtomicType) (seed : Carrier t) (x : Arr t n)
    (ht : t ≠ .general := by first | decide | assumption) : Except String (Arr rt n) := do
  let fill ← Ew.atomBits t (← Ew.atomCol t (Carrier.atom seed))
  match shiftColumn t 1 fill n x.enc with
  | some p => Ew.dyad v Ew.vv t t rt n x.enc n p n
  | _ => .error s!"Ew.prior: shiftColumn refused a column at {repr t}"

/-- `x f y` on two lists: one `Ew.val` when the lengths agree, q's `'length` otherwise. -/
def Ew.zip (v : Prim.Dyadic) (rt : QAtomicType) {m : Nat} (x : Arr t n) (y : Arr u m) :
    Except String (Arr rt n) :=
  if h : m = n then Ew.val v rt x (h ▸ y) else .error "'length"

/-! ## §4: different keys -/

/-- What a one-sided row answers in `align`, as a constant `e` the kernel combines it with:
    `fl a = f a eᵣ`, `fr b = eₗ g b`. `vr` is `g`, the verb of the right-only rows: `f` itself, except
    `%`, whose `fr` is the identity and so `1.0 × b`. -/
structure Lift where
  v : Prim.Dyadic
  vr : Prim.Dyadic
  er : UInt64
  el : UInt64

namespace Lift

/-- `1`, `0W` and `-0W` as raw bits at a storage class. -/
def one (c : UInt8) : UInt64 := if c == Ew.f64 then 0x3ff0000000000000 else if c == Ew.f32 then 0x3f800000 else 1
def top (c : UInt8) : UInt64 :=
  if c == Ew.f64 then 0x7ff0000000000000 else if c == Ew.f32 then 0x7f800000 else if c == Ew.i64 then 0x7fffffffffffffff
  else if c == Ew.i32 then 0x7fffffff else if c == Ew.i16 then 0x7fff else 0xff
def bot (c : UInt8) : UInt64 :=
  if c == Ew.f64 then 0xfff0000000000000 else if c == Ew.f32 then 0xff800000 else if c == Ew.i64 then 0x8000000000000001
  else if c == Ew.i32 then 0x80000001 else if c == Ew.i16 then 0x8001 else 0

/-- The triple table of §4 at operand types `t` (left) and `u` (right): `+ - * & |` fill with their
    unit (`0 0 1 0W -0W`, `fl = id`, `-`'s `fr = neg` being `0 − b`); `%` fills the left with `1` and
    takes `1.0 × b` on the right; a comparison compares against the null on both sides. -/
def ofVerb (v : Prim.Dyadic) (t u : QAtomicType) : Except String Lift := do
  let some ct := clsOf t | .error s!"align: no storage class at {repr t}"
  let some cu := clsOf u | .error s!"align: no storage class at {repr u}"
  let e (c : UInt8) : Prim.Dyadic → Option UInt64
    | .add | .sub => some 0 | .mul | .div => some (one c) | .lesser => some (top c) | .greater => some (bot c)
    | _ => none
  if (cmpOp v).isSome then
    let (some nt, some nu) := (nullBits t, nullBits u) | .error s!"align: {repr t} or {repr u} has no null"
    return ⟨v, v, nu, nt⟩
  match e cu v, e ct v with
  | some er, some el => return if v == .div then ⟨v, .mul, er, one Ew.f64⟩ else ⟨v, v, er, el⟩
  | _, _ => .error s!"align: no triple for {repr v}"

end Lift

namespace Ew

/-- A `.vector`'s count and payload out of a kernel's `QValue`. -/
def vec (what : String) : Option QValue → Except String (Nat × Enc)
  | some (.vector _ n e _) => .ok (n, e)
  | _ => .error s!"align: {what} answered no vector"

/-- `src@idx` with misses (`idx ≥ n`) filled by `fill`: `gatherBytes` on `bytes`, `gatherFoR` on `foR`. The
    source holds `n` elements, the `long` index `idx` is a count and a payload. -/
def gatherFill (t : QAtomicType) (fill : UInt64) (n : Nat) (src : Enc) (idx : Nat × Enc) : Except String (Nat × Enc) := do
  let some w := t.width | .error s!"align: {repr t} has no fixed width"
  let some ib := Enc.bytesOf .long idx.1 idx.2 | .error "align: index column has no long payload"
  match src with
  | .bytes b => return (idx.1, .bytes (gatherBytes w.toUSize fill b ib))
  | .foR m p => return (idx.1, .bytes (gatherFoR w.toUSize fill m p n.toUSize ib))
  | _ => .error s!"align: no fill-gather for this encoding at {repr t}"

end Ew

/-- `x f y` on different keys, over the key list `x.key ++ (y.key \ x.key)`: `findColumn` of `x`'s
    keys in `y`'s, `gatherFill` at `eᵣ`, one `dyadColumn` (the rows of `x`); `memberColumn`, `~`,
    `whereColumn`, `gatherColumn`, one `dyadColumn` against `eₗ` (the rows only `y` has);
    `razeColumn` of keys and of values. No `Option` is written; the spec is `alignList`. Keys equal as
    columns (`matchColumn`, whatever form each key takes) are one key: one `Ew.val`, `x.key` kept, as q
    does when the two dicts' keys match. -/
def Ew.align (L : Lift) (rt : QAtomicType) {s : QAtomicType} (x : Rel s t) (y : Rel s u)
    (ht : t ≠ .general := by first | decide | assumption) : Except String (Rel s rt) := do
  let kx := x.key.enc
  let ky := y.key.enc
  -- `matchColumn` answers `none` only where no kernel compares the two encodings: the general path is right there.
  -- Symbol keys always have one: `matchSyms`, `matchIds`, and `matchSymsIds` for a blob against an interned column
  if h : y.n = x.n then
    if matchColumn s x.n kx y.n ky == some true then return ⟨x.n, x.key, ← Ew.val L.v rt x.val (h ▸ y.val)⟩
  let ix ← Ew.vec "findColumn" (findColumn s false y.n ky x.key.1)
  let yx ← Ew.gatherFill u L.er y.n y.val.enc ix
  let l ← Ew.dyad L.v Ew.vv t u rt x.n x.val.enc yx.1 yx.2 x.n
  let some (.vector _ m (.bits b) none) := memberColumn s false y.key.1 x.n kx | .error "align: memberColumn"
  let (r, iy) ← Ew.vec "whereColumn" (whereColumn .boolean m (.bits (Ew.notBits m b)))
  let some gy := gatherColumn u y.n y.val.enc r iy | .error "align: gatherColumn answered no vector"
  let ry ← Ew.dyad L.vr Ew.av t u rt 1 (← Ew.atomCol t (Column.atomOfBits t L.el)) r gy r
  let some gk := gatherColumn s y.n ky r iy | .error "align: gatherColumn answered no vector"
  let some keys := razeColumn s #[(x.n, kx), (r, gk)] | .error "align: razeColumn answered no vector"
  let some vals := razeColumn rt #[(x.n, l.enc), (r, ry.enc)] | .error "align: razeColumn answered no vector"
  return ⟨x.n + r, ← Arr.of s (x.n + r) keys "align keys", ← Arr.of rt (x.n + r) vals "align vals"⟩

/-- `x f y` on two dicts: `align` under the verb's `Lift`, one `Ew.val` when the keys match. -/
def Ew.dyadic (v : Prim.Dyadic) (rt : QAtomicType) {s : QAtomicType} (x : Rel s t)
    (y : Rel s u) (ht : t ≠ .general := by first | decide | assumption) : Except String (Rel s rt) := do
  Ew.align (← Lift.ofVerb v t u) rt x y

/-- A verb on a dict's values alone, the key kept: `a f d` is `Ew.keyed d (Ew.atomVal v rt a ·)`, `d f a` is
    `Ew.keyed d (Ew.valAtom v rt · a)`, as q's atom-dict verbs map the values. -/
def Ew.keyed {s rt : QAtomicType} (x : Rel s t) (f : Arr t x.n → Except String (Arr rt x.n)) :
    Except String (Rel s rt) := do
  return ⟨x.n, x.key, ← f x.val⟩

/-! ## Spec over `toList` -/

/-- The aligned rows of §4 (c): `x`'s keys in order, then `y`'s keys `x` lacks; each side's value where
    present, the first on a repeated key. -/
def alignList {K A B : Type} [BEq K] (xs : List (K × A)) (ys : List (K × B)) : List (K × Option A × Option B) :=
  xs.map (fun p => (p.1, some p.2, ys.lookup p.1)) ++
    (ys.filter fun q => !xs.any (·.1 == q.1)).map fun q => (q.1, none, some q.2)

/-- `R` is `x f y` element by element: the values `Dep.elem v h` of the pairs. -/
def Ew.ValSpec (v : Prim.Dyadic) {rt : QAtomicType} (h : Eval.ewType v t u = some rt)
    (x : Arr t n) (yv : Arr u n) (R : Arr rt n) : Prop :=
  (x.toList.zip yv.toList).mapM (fun p => elem v h p.1 p.2) = .ok R.toList

/-- `R` is `x` with `f` on every value. -/
def Ew.MapSpec {rt : QAtomicType} (f : Carrier t → Carrier rt) (x : Arr t n) (R : Arr rt n) : Prop :=
  R.toList = x.toList.map f

/-- `align`'s answer has `x`'s keys first, in `x`'s order: its key list starts with `x.key`. -/
theorem alignList_keys {K A B : Type} [BEq K] (xs : List (K × A)) (ys : List (K × B)) :
    (alignList xs ys).map (·.1) = xs.map (·.1) ++ (ys.filter fun q => !xs.any (·.1 == q.1)).map (·.1) := by
  simp [alignList, Function.comp_def]

/-! ## Value laws -/

/-- **`Ew.bit`'s bitmap**: bit `i` is set exactly when `i < n` and `bitStep` holds of the two bits the
    shape reads at `i`. `Verify.cmp_bitAt`'s byte fold, at the bit engine; qlean has it for `Ew.cmp` only. -/
theorem Ew.bit_bitAt (op shape : UInt8) (a b : ByteArray) (n : USize) :
    (Ew.bit op shape a b n).size = (n.toNat + 7) / 8 ∧
    ∀ i < 8 * ((n.toNat + 7) / 8), Column.bitAt (Ew.bit op shape a b n) i =
      (decide (i < n.toNat) && Ew.bitStep op (Column.bitAt a (Ew.shapeIdx shape i).1)
        (Column.bitAt b (Ew.shapeIdx shape i).2)) := by
  let C : Nat → Bool := fun i => decide (i < n.toNat) &&
    Ew.bitStep op (Column.bitAt a (Ew.shapeIdx shape i).1) (Column.bitAt b (Ew.shapeIdx shape i).2)
  let B : Nat → UInt8 := fun k =>
    (List.range 8).foldl (fun byte t => if C (k * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  have hf : Ew.bit op shape a b n =
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

/-- `Ew.notBits m b` below `m` is `b` negated bit by bit: `≠` against the one-bit mask. -/
theorem Ew.notBits_bitAt {m : Nat} (hm : m < USize.size) (b : ByteArray) {i : Nat} (hi : i < m) :
    Column.bitAt (Ew.notBits m b) i = !Column.bitAt b i := by
  have hmu : m.toUSize.toNat = m := USize.toNat_ofNat_of_lt' hm
  have h := (Ew.bit_bitAt (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m.toUSize).2 i (by rw [hmu]; omega)
  rw [Ew.notBits, h, hmu, decide_eq_true hi, Bool.true_and, show Ew.shapeIdx Ew.av i = (0, i) from rfl]
  dsimp only
  cases Column.bitAt b i <;> decide

/-- **`~x`** is `x` with `not` on every boolean. `x.n < USize.size`: the kernel takes the count as a `USize`. -/
theorem Ew.not_spec {x : Arr .boolean n} (hn : n < USize.size) : Ew.MapSpec (fun b => !b) x (Ew.not x) := by
  unfold Ew.not
  rw [dif_pos hn]
  cases hc : x.enc
  case bits b =>
    dsimp only
    apply List.ext_getElem (by rw [List.length_map, Arr.length_toList, Arr.length_toList])
    intro i h1 h2
    rw [Arr.getElem_toList, List.getElem_map, Arr.getElem_toList, Arr.get_bool_bits _ rfl, Arr.get_bool_bits _ hc]
    rw [Arr.length_toList] at h1
    exact Ew.notBits_bitAt hn b (by omega)
  all_goals (have hw := x.wf; rw [hc] at hw; simp [Enc.WF] at hw)


/-! ## The element step at `long`: q's interpreter against the kernel's step

What `Ew.ValSpec` needs once a column law reaches `valStep`/`cmpStep`: `Dep.elem` (q's `dyadAtom`) on two
longs is the kernel's `intStep` at q's null for the value verbs and `cmpStep` at `i64` for the six
comparisons. -/

section Step
open QLean.Eval

theorem Ew.compare_toInt (a b : Int64) : compare a b = compare a.toInt b.toInt := by
  simp only [compare, compareOfLessAndEq, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj]

/-- q's null `0N` is the least long, strictly below every other. -/
theorem Ew.min_lt {y : Int64} (hy : ¬y = Int64.minValue) : Int64.minValue.toInt < y.toInt := by
  have h1 := Int64.le_iff_toInt_le.1 (Int64.minValue_le y)
  have h2 : Int64.minValue.toInt ≠ y.toInt := fun e => hy (Int64.toInt_inj.1 e).symm
  omega

/-- q's order on two longs (nulls equal and least) is `Int64`'s. -/
theorem Ew.cmpAtoms_long (x y : Int64) : cmpAtoms (.long x) (.long y) = some (compare x y) := by
  by_cases hx : x = Int64.minValue <;> by_cases hy : y = Int64.minValue <;>
    simp [cmpAtoms, hx, hy, missing, QAtom.isNull, QAtom.type, intPayload]
  all_goals rw [Ew.compare_toInt]
  · have := Ew.min_lt hy; simp only [compare, compareOfLessAndEq]; repeat' split
    all_goals first | rfl | (exfalso; omega)
  · have := Ew.min_lt hx; simp only [compare, compareOfLessAndEq]; repeat' split
    all_goals first | rfl | (exfalso; omega)

/-- The tolerance changes nothing at `long`: two longs are tolerantly equal only when equal. -/
theorem Ew.cmpTolerant_long (x y : Int64) : cmpTolerant (.long x) (.long y) = some (compare x y) := by
  simp only [cmpTolerant, Ew.cmpAtoms_long, Option.map_some]
  by_cases e : x = y
  · subst e; simp [QAtom.eqTol, QAtom.identical]
  · simp [QAtom.eqTol, QAtom.identical, e]

/-- **A value verb on two longs** is `intStep` at q's null: `+ - *` answer `0N` on a null operand and wrap
    otherwise, `& |` pick by order, `^` fills a null right operand from the left. -/
theorem Ew.dyadAtom_long_val {v : Prim.Dyadic} {op : UInt8} (hop : valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) (x y : Int64) :
    dyadAtom v (.long x) (.long y) = .ok (.long (Ew.intStep op Int64.minValue x y)) := by
  cases v <;> simp only [valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  case div => exact absurd h (by decide)
  case add | sub | mul =>
    all_goals (
      show arithAtoms _ .long (.long x) (.long y) = _
      by_cases hx : x = Int64.minValue <;> by_cases hy : y = Int64.minValue <;>
        simp [arithAtoms, hx, hy, missing, QAtom.isNull, QAtom.type, carried, isFloatPayload, nullAtom,
          Prim.clockIntoDays, intIn, temporalIn, roundedPayload, intPayload, atomOfInt, Ew.intStep, Ew.add,
          Ew.sub, Ew.mul])
  all_goals (
    simp (config := { decide := true }) [dyadAtom, toCommon, QAtom.type, Ew.cmpAtoms_long, Ew.intStep,
      QAtom.isNull]
    first
      | (split <;> rfl)
      | (rw [Ew.compare_toInt]; simp only [Int64.lt_iff_toInt_lt]
         rcases Int.lt_trichotomy x.toInt y.toInt with hl | he | hg
         · simp [compare, compareOfLessAndEq, hl, Int.not_lt.2 (Int.le_of_lt hl)]
         · obtain rfl := Int64.toInt_inj.1 he; simp
         · simp [compare, compareOfLessAndEq, hg, Int.not_lt.2 (Int.le_of_lt hg), Int.ne_of_gt hg]))

/-- **A comparison on two longs** is `cmpStep` at `i64` on their bits. -/
theorem Ew.dyadAtom_long_cmp {v : Prim.Dyadic} {op : UInt8} (hop : cmpOp v = some op) (x y : Int64) :
    dyadAtom v (.long x) (.long y) = .ok (.boolean (Ew.cmpStep op Ew.i64 x.toUInt64 y.toUInt64)) := by
  cases v <;> simp only [cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals simp (config := { decide := true }) [dyadAtom, toCommon, QAtom.type, Ew.cmpTolerant_long, Ew.cmpStep,
    Ew.signed]

/-- `Dep.elem` (`ValSpec`'s step) of a value verb on two longs is `intStep` at q's null. -/
theorem Ew.elem_long_val {v : Prim.Dyadic} {op : UInt8} (hop : valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) (x y : Int64) :
    elem v h x y = .ok (Ew.intStep op Int64.minValue x y) := by
  have hd : dyadAtom v (Carrier.atom (t := .long) x) (Carrier.atom (t := .long) y) = _ := Ew.dyadAtom_long_val hop h x y
  unfold elem; rw [dif_neg (by decide), dif_neg (by decide)]
  split
  · rename_i hz; rw [hd] at hz; cases hz
  · rename_i hz; rw [hd] at hz; cases hz; rfl

/-- `Dep.elem` of a comparison on two longs is `cmpStep` at `i64`. -/
theorem Ew.elem_long_cmp {v : Prim.Dyadic} {op : UInt8} (hop : cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) (x y : Int64) :
    elem v h x y = .ok (Ew.cmpStep op Ew.i64 x.toUInt64 y.toUInt64) := by
  have hd : dyadAtom v (Carrier.atom (t := .long) x) (Carrier.atom (t := .long) y) = _ := Ew.dyadAtom_long_cmp hop x y
  unfold elem; rw [dif_neg (by decide), dif_neg (by decide)]
  split
  · rename_i hz; rw [hd] at hz; cases hz
  · rename_i hz; rw [hd] at hz; cases hz; rfl

end Step

#print axioms Ew.not_spec
#print axioms Ew.elem_long_val
#print axioms Ew.elem_long_cmp

/-! ## Checks on small literal columns -/

section Checks

/-- A column of longs, a list of them, or a dict of longs; built through `Arr.of`'s run-time `wf`. -/
private def LA (vs : List Int64) : Except String (Arr .long vs.length) :=
  Arr.of .long _ (.vector .long vs.length (.bytes (packLongs vs)) none) "L"
private def D (ks vs : List Int64) : Except String (Rel .long .long) :=
  return ⟨vs.length, ← Arr.of .long _ (.vector .long ks.length (.bytes (packLongs ks)) none) "D",
    ← Arr.of .long _ (.vector .long vs.length (.bytes (packLongs vs)) none) "D"⟩
private def av {v n} (r : Except String (Arr v n)) : Option (List (El v)) := r.toOption.map (·.toList)
private def pairs {k v} (r : Except String (Rel k v)) : Option (List (k.El × v.El)) := r.toOption.map (·.toList)

#guard av (do Ew.zip .add .long (← LA [1, 2, 3]) (← LA [10, 20, -5])) == some [11, 22, -2]
#guard av (do Ew.zip .add .long (← LA [1, 2, 3]) (← LA [10, 20])) == none
-- the spec's side: `Dep.elem` over the zipped lists answers the same
#guard (([1, 2, 3].zip [10, 20, -5] : List (Int64 × Int64)).mapM fun p =>
  elem .add (a := .long) (b := .long) (c := .long) rfl p.1 p.2).toOption == some [11, 22, -2]
#guard av (do Ew.zip .lt .boolean (← LA [1, 2, 3]) (← LA [10, 2, -5])) == some [true, false, false]
#guard av (do Ew.atomVal (t := .long) .sub .long 10 (← LA [1, 2, 3])) == some [9, 8, 7]
#guard av (do Ew.valAtom (u := .long) .sub .long (← LA [1, 2, 3]) 1) == some [0, 1, 2]
#guard av (do Ew.valAtom (u := .long) .lt .boolean (← LA [1, 2, 3]) 2) == some [true, false, false]
#guard av (do pure (Ew.mon "neg" .long (← LA [1, -2, 3]))) == some [-1, 2, -3]
#guard av (do pure (Ew.not (← Ew.valAtom (u := .long) .lt .boolean (← LA [1, 2, 3]) 2))) == some [false, true, true]
#guard av (do Ew.prior (t := .long) .sub .long 0 (← LA [1, 4, 9, 16])) == some [1, 3, 5, 7]
#guard av (do pure (Ew.bitwise Ew.band (← LA [12, 5, -1, 0]) (← LA [10, 2, 7, -1]))) == some [8, 0, 7, 0]
#guard av (do pure (Ew.bitwise Ew.bor (← LA [12, 5, -1, 0]) (← LA [10, 2, 7, -1]))) == some [14, 7, -1, -1]
#guard av (do pure (Ew.bitwise Ew.bandnot (← LA [12, 5, -1, 0]) (← LA [10, 2, 7, -1]))) == some [4, 5, -8, 0]
-- `foR` operands: `tilColumn` writes one once it is long enough for the encoding to pay
private def tilFoR (n : Nat) : Except String (Arr .long n) := do
  let some c@(.vector _ _ (.foR ..) _) := tilColumn n | throw "tilColumn answered no foR"
  Arr.of .long n c "til"
#guard av (do Ew.val .add .long (← tilFoR 4096) (← tilFoR 4096)) == some ((List.range 4096).map (Int64.ofNat <| 2 * ·))
#guard av (do Ew.prior (t := .long) .sub .long 0 (← tilFoR 4096)) == some (0 :: List.replicate 4095 1)
#guard av (do Ew.valAtom (u := .long) .lt .boolean (← tilFoR 4096) 3) == some ((List.range 4096).map (decide <| · < 3))
-- §4: different keys, `x.key ++ (y.key \ x.key)`
#guard pairs (do Ew.dyadic .add .long (← D [1, 2, 3] [10, 20, 30]) (← D [2, 4] [5, 7])) ==
  some [(1, 10), (2, 25), (3, 30), (4, 7)]
#guard pairs (do Ew.dyadic .sub .long (← D [1, 2, 3] [10, 20, 30]) (← D [2, 4] [5, 7])) ==
  some [(1, 10), (2, 15), (3, 30), (4, -7)]
#guard pairs (do Ew.dyadic .lesser .long (← D [1, 2] [10, 20]) (← D [2, 4] [5, 7])) ==
  some [(1, 10), (2, 5), (4, 7)]
-- the spec side of the first row
#guard alignList [((1 : Int64), (10 : Int64)), (2, 20), (3, 30)] [((2 : Int64), (5 : Int64)), (4, 7)] ==
  [(1, some 10, none), (2, some 20, some 5), (3, some 30, none), (4, none, some 7)]
/-- `x+y` read off `alignList`: `+`'s unit `0` on the missing side. -/
private def addSpec (x y : Except String (Rel .long .long)) : Option (List (Int64 × Int64)) := do
  pure ((alignList (← x.toOption).toList (← y.toOption).toList).map fun (k, a, b) => (k, a.getD 0 + b.getD 0))
-- different keys, repeated or not: `x` keys `0 1 2`, `1 3 3`, `1 2 3`; `y` keys `0 1 2`, `0 0 1`, `2 4`
#guard [D [0, 1, 2] [10, 20, 30], D [1, 3, 3] [10, 20, 30], D [1, 2, 3] [10, 20, 30]].all fun x =>
  [D [0, 1, 2] [5, 7, 9], D [0, 0, 1] [5, 7, 9], D [2, 4] [5, 7]].all fun y =>
    pairs (do Ew.dyadic .add .long (← x) (← y)) == addSpec x y
#guard pairs (do Ew.dyadic .add .long (← D [1, 3, 3] [10, 20, 30]) (← D [0, 0, 1] [5, 7, 9])) ==
  some [(1, 19), (3, 20), (3, 30), (0, 5), (0, 7)]
-- equal keys: one `Ew.val` position by position, `x`'s key kept. With the repeated key `0 0 1` the general
-- path would add `y`'s first `0` to both: only the equal-key path answers `11 22 33`
#guard pairs (do Ew.dyadic .add .long (← D [0, 1, 2] [10, 20, 30]) (← D [0, 1, 2] [1, 2, 3])) ==
  some [(0, 11), (1, 22), (2, 33)]
#guard pairs (do Ew.dyadic .add .long (← D [0, 0, 1] [10, 20, 30]) (← D [0, 0, 1] [1, 2, 3])) ==
  some [(0, 11), (0, 22), (1, 33)]
-- symbol keys `a a b`, as a blob (`SS`) and interned over `a, b` (`SE`): equal keys in every pair of encodings
-- take the one-key path, which alone adds position by position across the repeated `a`
private def SK (c : QValue) (vs : List Int64) : Except String (Rel .symbol .long) :=
  return ⟨vs.length, ← Arr.of .symbol _ c "SK", ← Arr.of .long _ (.vector .long vs.length (.bytes (packLongs vs)) none) "SK"⟩
private def SS (vs : List Int64) := SK (.vector .symbol 3 (.syms (ByteArray.mk #[97, 0, 97, 0, 98, 0]) #[0, 2, 4, 6]) none) vs
private def SE (vs : List Int64) :=
  SK (.vector .symbol 3 (.enum (ByteArray.mk #[97, 0, 98, 0]) #[0, 2, 4] (Column.packIds (Column.idWidth #[0, 2, 4]) 3 fun i => [0, 0, 1][i]!)) none) vs
private def addL := Lift.ofVerb .add .long .long
#guard [SS, SE].all fun x => [SS, SE].all fun y =>
  pairs (do Ew.align (← addL) .long (← x [10, 20, 30]) (← y [1, 2, 3])) == some [("a", 11), ("a", 22), ("b", 33)]
-- different symbol keys `a b` against `b c` in every pair of encodings: the general path
private def S2 (b : ByteArray) (vs : List Int64) : List (Except String (Rel .symbol .long)) :=
  [SK (.vector .symbol 2 (.syms b #[0, 2, 4]) none) vs,
    SK (.vector .symbol 2 (.enum b #[0, 2, 4] (Column.packIds (Column.idWidth #[0, 2, 4]) 2 id)) none) vs]
#guard (S2 (ByteArray.mk #[97, 0, 98, 0]) [10, 20]).all fun x => (S2 (ByteArray.mk #[98, 0, 99, 0]) [1, 2]).all fun y =>
  pairs (do Ew.align (← addL) .long (← x) (← y)) == some [("a", 10), ("b", 21), ("c", 2)]

end Checks

#print axioms Ew.zip
#print axioms alignList_keys
#print axioms Ew.align

end LeetQ.Rel
