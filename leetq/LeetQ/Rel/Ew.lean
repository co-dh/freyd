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

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

namespace Ew

/-- One `dyadColumn` call — qlean's per-encoding dispatch (`bytes`, `foR`, ALP, `bits`, `syms`) —
    checked against the result type `rt` the caller asked for. -/
def dyad (v : Prim.Dyadic) (shape : UInt8) (t u rt : QAtomicType) (a b : Column) (n : Nat) :
    Except String (Arr (.atom rt) n) :=
  match dyadColumn v shape t u a b with
  | none => .error s!"Ew: no qlean kernel claims {repr v} at {repr t}, {repr u} (shape {shape})"
  | some (rt', c) =>
    if rt' = rt then Arr.of (.atom rt) n c s!"Ew {repr v}" else .error s!"Ew {repr v}: answers {repr rt'}, not {repr rt}"

/-- A one-element column holding `a`: how an atom reaches a kernel, once per call. -/
def atomCol (t : QAtomicType) (a : QAtom) : Except String Column :=
  match Column.ofAtoms t #[a] with
  | some c => .ok c
  | none => .error s!"Ew: Column.ofAtoms refused an atom at {repr t}"

end Ew

variable {k : Ty} {t u : QAtomicType}

/-- `x f y` on one key: `yv` is a value column on `x`'s positions. Comparisons are this at
    `rt = boolean` (`Ew.cmp` in the design is the same `dyadColumn` call, `cmpPayload` inside). -/
def Ew.val (v : Prim.Dyadic) (rt : QAtomicType) (x : Rel k (.atom t)) (yv : Arr (.atom u) x.n) :
    Except String (Rel k (.atom rt)) :=
  return ⟨x.n, x.key, ← Ew.dyad v Ew.vv t u rt x.val.c yv.c x.n⟩

/-- `a f x`: the atom on the left, the one atom shape `av` that reaches a kernel. -/
def Ew.atomVal (v : Prim.Dyadic) (rt : QAtomicType) (a : Carrier t) (x : Rel k (.atom u)) :
    Except String (Rel k (.atom rt)) :=
  return ⟨x.n, x.key, ← Ew.dyad v Ew.av t u rt (← Ew.atomCol t (Carrier.atom a)) x.val.c x.n⟩

/-- The verb `v'` with `x v a = a v' x`, where one exists. -/
def Ew.flip : Prim.Dyadic → Option Prim.Dyadic
  | .add => some .add | .mul => some .mul | .lesser => some .lesser | .greater => some .greater
  | .eq => some .eq | .ne => some .ne | .lt => some .gt | .gt => some .lt | .le => some .ge
  | .ge => some .le | _ => none

/-- `x f a`, rewritten onto `av` by `flip` (`x<a = a>x`). `-` and `%` keep `va`, which the kernel has:
    `(−a)+x` changes the type rule at temporal types (`d−d` is `int`, `d+(−d)` is `'type`) and
    `(1/a)×x` is not `x/a` bit for bit in floats. -/
def Ew.valAtom (v : Prim.Dyadic) (rt : QAtomicType) (x : Rel k (.atom t)) (a : Carrier u) :
    Except String (Rel k (.atom rt)) :=
  match Ew.flip v with
  | some vf => Ew.atomVal vf rt a x
  | none => return ⟨x.n, x.key, ← Ew.dyad v Ew.va t u rt x.val.c (← Ew.atomCol u (Carrier.atom a)) x.n⟩

/-- `f x` for qlean's monadic kernels by name (`neg`, `abs`, `reciprocal`, `null`, …): one `monColumn`. -/
def Ew.mon (name : String) (rt : QAtomicType) (x : Rel k (.atom t)) : Except String (Rel k (.atom rt)) :=
  match monColumn name t x.val.c with
  | none => .error s!"Ew.mon: no qlean kernel claims {name} at {repr t}"
  | some (rt', c) =>
    if rt' = rt then return ⟨x.n, x.key, ← Arr.of (.atom rt) x.n c s!"Ew.mon {name}"⟩
    else .error s!"Ew.mon {name}: answers {repr rt'}, not {repr rt}"

/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : Nat) (b : ByteArray) : ByteArray := Ew.bit (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m.toUSize

/-- `~x`: `Ew.notBits` of the value column. -/
def Ew.not (x : Rel k (.atom .boolean)) : Except String (Rel k (.atom .boolean)) :=
  match x.val.c with
  | .bits m b =>
    return ⟨x.n, x.key, ← Arr.of (.atom .boolean) x.n (.bits m (Ew.notBits m b)) "Ew.not"⟩
  | _ => .error "Ew.not: a boolean value column is not `bits`"

/-- The raw bits of a one-element column, as `shiftColumn`'s `fill` takes them. -/
def Ew.atomBits (t : QAtomicType) : Column → Except String UInt64
  | .bits _ b => .ok (if Column.bitAt b 0 then 1 else 0)
  | c => match Column.bytesOf t c, t.width with
    | some b, some w => .ok (Column.bitsAt b 0 w)
    | _, _ => .error s!"Ew: no fixed-width payload for an atom at {repr t}"

/-- `seed f': x`: `r[i] = x[i] f x[i-1]`, `x[-1] = seed` (`-':` with seed `0` keeps `x[0]` raw). The
    prior operand is `shiftColumn` (`shiftBytes`/`shiftFoR`/`shiftALP`/`shiftBits`) and then one
    `dyadColumn`; on two `foR`s that pair is `priorValFoR`'s body. A dense fused kernel reading the
    one payload at offset `−w` does not exist in qlean: this is two passes there. -/
def Ew.prior (v : Prim.Dyadic) (rt : QAtomicType) (seed : Carrier t) (x : Rel k (.atom t)) :
    Except String (Rel k (.atom rt)) := do
  let fill ← Ew.atomBits t (← Ew.atomCol t (Carrier.atom seed))
  match shiftColumn t 1 fill x.val.c with
  | some (.vector _ p) => return ⟨x.n, x.key, ← Ew.dyad v Ew.vv t t rt x.val.c p x.n⟩
  | _ => .error s!"Ew.prior: shiftColumn refused a column at {repr t}"

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

/-- A key column materialised: `arr` as it is, `til` written by `tilColumn`. -/
def keyCol (s : QAtomicType) : {n : Nat} → KeyCol (.atom s) n → Except String Column
  | _, .arr a => .ok a.c
  | n, .til _ => match tilColumn n with
    | some (.vector _ c) => .ok c
    | _ => .error "align: tilColumn refused"
  | _, .grp .. => .error "align: a grp key is not materialised here (step 4 writes `expandBytes` of `o`)"

/-- A `.vector`'s column out of a kernel's `QValue`. -/
def vec (what : String) : Option QValue → Except String Column
  | some (.vector _ c) => .ok c
  | _ => .error s!"align: {what} answered no vector"

/-- `src@idx` with misses (`idx ≥ n`) filled by `fill`: `gatherBytes` on `bytes`, `gatherFoR` on `foR`. -/
def gatherFill (t : QAtomicType) (fill : UInt64) (src idx : Column) : Except String Column := do
  let some w := t.width | .error s!"align: {repr t} has no fixed width"
  let some ib := Column.bytesOf .long idx | .error "align: index column has no long payload"
  match src with
  | .bytes b => return .bytes (gatherBytes w.toUSize fill b ib)
  | .foR n m p => return .bytes (gatherFoR w.toUSize fill m p n.toUSize ib)
  | _ => .error s!"align: no fill-gather for this encoding at {repr t}"

end Ew

/-- `x f y` on different keys, over the key list `x.key ++ (y.key \ x.key)`: `findColumn` of `x`'s
    keys in `y`'s, `gatherFill` at `eᵣ`, one `dyadColumn` (the rows of `x`); `memberColumn`, `~`,
    `whereColumn`, `gatherColumn`, one `dyadColumn` against `eₗ` (the rows only `y` has);
    `razeColumn` of keys and of values. No `Option` is written; the spec is `alignList`. -/
def Ew.align (L : Lift) (rt : QAtomicType) {s : QAtomicType} (x : Rel (.atom s) (.atom t)) (y : Rel (.atom s) (.atom u)) :
    Except String (Rel (.atom s) (.atom rt)) := do
  let kx ← Ew.keyCol s x.key
  let ky ← Ew.keyCol s y.key
  let ix ← Ew.vec "findColumn" (findColumn s false ky (.vector s kx))
  let yx ← Ew.gatherFill u L.er y.val.c ix
  let l ← Ew.dyad L.v Ew.vv t u rt x.val.c yx x.n
  let some (.vector _ (.bits m b)) := memberColumn s false (.vector s ky) kx | .error "align: memberColumn"
  let some (.vector _ iy) := whereColumn .boolean (.bits m (Ew.notBits m b))
    | .error "align: whereColumn"
  let r := Column.count .long iy
  let ry ← Ew.dyad L.vr Ew.av t u rt (← Ew.atomCol t (Column.atomOfBits t L.el))
    (← Ew.vec "gatherColumn" (gatherColumn u y.val.c iy)) r
  let keys ← Ew.vec "razeColumn" (razeColumn s #[kx, ← Ew.vec "gatherColumn" (gatherColumn s ky iy)])
  let vals ← Ew.vec "razeColumn" (razeColumn rt #[l.c, ry.c])
  return ⟨x.n + r, .arr (← Arr.of (.atom s) (x.n + r) keys "align keys"), ← Arr.of (.atom rt) (x.n + r) vals "align vals"⟩

/-- The dyadic rule: case 0 (both keys `til` of one length) is ONE `Ew.val`, keys untouched;
    any other pair goes through `align`. -/
def Ew.dyadic (v : Prim.Dyadic) (rt : QAtomicType) (x : Rel (.atom .long) (.atom t)) (y : Rel (.atom .long) (.atom u)) :
    Except String (Rel (.atom .long) (.atom rt)) :=
  match x.key, y.key with
  | .til _, .til _ => if h : y.n = x.n then Ew.val v rt x (h ▸ y.val) else .error "'length"
  | _, _ => do Ew.align (← Lift.ofVerb v t u) rt x y

/-! ## Spec over `toList` -/

/-- The aligned rows of §4 (c): `x`'s keys in order, then `y`'s keys `x` lacks; each side's value where
    present, the first on a repeated key. -/
def alignList {K A B : Type} [BEq K] (xs : List (K × A)) (ys : List (K × B)) : List (K × Option A × Option B) :=
  xs.map (fun p => (p.1, some p.2, ys.lookup p.1)) ++
    (ys.filter fun q => !xs.any (·.1 == q.1)).map fun q => (q.1, none, some q.2)

/-- `R` is `x f y` element by element: the keys of `x`, the values `Dep.elem v h` of the pairs. -/
def Ew.ValSpec (v : Prim.Dyadic) {rt : QAtomicType} (h : Eval.ewType v t u = some rt)
    (x : Rel k (.atom t)) (yv : Arr (.atom u) x.n) (R : Rel k (.atom rt)) : Prop :=
  R.key.toList = x.key.toList ∧ (x.val.toList.zip yv.toList).mapM (fun p => elem v h p.1 p.2) = .ok R.val.toList

/-- `R` is `x` with `f` on every value. -/
def Ew.MapSpec {rt : QAtomicType} (f : Carrier t → Carrier rt) (x : Rel k (.atom t)) (R : Rel k (.atom rt)) : Prop :=
  R.key.toList = x.key.toList ∧ R.val.toList = x.val.toList.map f

/-- The key half of both specs, for every op on one key: the answer is `⟨x.n, x.key, _⟩`. -/
def Ew.KeepsKey {v w : Ty} (x : Rel k v) (R : Rel k w) : Prop := R.n = x.n ∧ R.key.toList = x.key.toList

theorem Ew.val_key {v rt} {x : Rel k (.atom t)} {yv : Arr (.atom u) x.n} {R : Rel k (.atom rt)}
    (h : Ew.val v rt x yv = .ok R) : Ew.KeepsKey x R := by
  simp only [Ew.val, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem Ew.atomVal_key {v rt} {a : Carrier t} {x : Rel k (.atom u)} {R : Rel k (.atom rt)}
    (h : Ew.atomVal v rt a x = .ok R) : Ew.KeepsKey x R := by
  simp only [Ew.atomVal, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem Ew.valAtom_key {v rt} {x : Rel k (.atom t)} {a : Carrier u} {R : Rel k (.atom rt)}
    (h : Ew.valAtom v rt x a = .ok R) : Ew.KeepsKey x R := by
  unfold Ew.valAtom at h
  split at h
  · exact Ew.atomVal_key h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem Ew.mon_key {name rt} {x : Rel k (.atom t)} {R : Rel k (.atom rt)}
    (h : Ew.mon name rt x = .ok R) : Ew.KeepsKey x R := by
  simp only [Ew.mon, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem Ew.not_key {x R : Rel k (.atom .boolean)} (h : Ew.not x = .ok R) : Ew.KeepsKey x R := by
  simp only [Ew.not, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

theorem Ew.prior_key {v rt} {seed : Carrier t} {x : Rel k (.atom t)} {R : Rel k (.atom rt)}
    (h : Ew.prior v rt seed x = .ok R) : Ew.KeepsKey x R := by
  simp only [Ew.prior, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> exact ⟨rfl, rfl⟩)

/-- `align`'s answer has `x`'s keys first, in `x`'s order: its key list starts with `x.key`. -/
theorem alignList_keys {K A B : Type} [BEq K] (xs : List (K × A)) (ys : List (K × B)) :
    (alignList xs ys).map (·.1) = xs.map (·.1) ++ (ys.filter fun q => !xs.any (·.1 == q.1)).map (·.1) := by
  simp [alignList, Function.comp_def]


/-! ## Checks on small literal columns -/

section Checks

/-- A list of longs, or a dict of longs; built through `Arr.of`'s run-time `wf`. -/
private def L (vs : List Int64) : Except String (Rel (.atom .long) (.atom .long)) :=
  return ⟨vs.length, .til _, ← Arr.of (.atom .long) _ (.bytes (packLongs vs)) "L"⟩
private def D (ks vs : List Int64) : Except String (Rel (.atom .long) (.atom .long)) :=
  return ⟨vs.length, .arr (← Arr.of (.atom .long) _ (.bytes (packLongs ks)) "D"), ← Arr.of (.atom .long) _ (.bytes (packLongs vs)) "D"⟩
private def vals {k v} (r : Except String (Rel k v)) : Option (List (El v)) := r.toOption.map (·.val.toList)
private def pairs {k v} (r : Except String (Rel k v)) : Option (List (El k × El v)) := r.toOption.map (·.toList)

#guard vals (do Ew.dyadic .add .long (← L [1, 2, 3]) (← L [10, 20, -5])) == some [11, 22, -2]
-- the spec's side: `Dep.elem` over the zipped lists answers the same
#guard (([1, 2, 3].zip [10, 20, -5] : List (Int64 × Int64)).mapM fun p =>
  elem .add (a := .long) (b := .long) (c := .long) rfl p.1 p.2).toOption == some [11, 22, -2]
#guard vals (do Ew.dyadic .lt .boolean (← L [1, 2, 3]) (← L [10, 2, -5])) == some [true, false, false]
#guard vals (do Ew.atomVal (t := .long) .sub .long 10 (← L [1, 2, 3])) == some [9, 8, 7]
#guard vals (do Ew.valAtom (u := .long) .sub .long (← L [1, 2, 3]) 1) == some [0, 1, 2]
#guard vals (do Ew.valAtom (u := .long) .lt .boolean (← L [1, 2, 3]) 2) == some [true, false, false]
#guard vals (do Ew.mon "neg" .long (← L [1, -2, 3])) == some [-1, 2, -3]
#guard vals (do Ew.not (← Ew.valAtom (u := .long) .lt .boolean (← L [1, 2, 3]) 2)) == some [false, true, true]
#guard vals (do Ew.prior (t := .long) .sub .long 0 (← L [1, 4, 9, 16])) == some [1, 3, 5, 7]
-- `foR` operands: `tilColumn` writes one once it is long enough for the encoding to pay
private def tilFoR (n : Nat) : Except String (Rel (.atom .long) (.atom .long)) := do
  let some (.vector _ c) := tilColumn n | throw "tilColumn refused"
  unless c matches .foR .. do throw "tilColumn answered no foR"
  return ⟨n, .til n, ← Arr.of (.atom .long) n c "til"⟩
#guard vals (do Ew.dyadic .add .long (← tilFoR 4096) (← tilFoR 4096)) == some ((List.range 4096).map (Int64.ofNat <| 2 * ·))
#guard vals (do Ew.prior (t := .long) .sub .long 0 (← tilFoR 4096)) == some (0 :: List.replicate 4095 1)
#guard vals (do Ew.valAtom (u := .long) .lt .boolean (← tilFoR 4096) 3) == some ((List.range 4096).map (decide <| · < 3))
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

end Checks

#print axioms Ew.val_key
#print axioms Ew.prior_key
#print axioms alignList_keys
#print axioms Ew.align

end LeetQ.Rel
