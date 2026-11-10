/-
  RelRep design B: a k verb is a term `Prog` over the executable Rel primitives (design §1: step 1
  P1–P6, P6′, P13; step 3 P8–P12, P16, `Λ` carried as its keys beside a `Parted`, boxed only at output). `den P` is its spec in `RelSet`, `run P` executes it one `Alg.*` kernel per node.
  Objects are `Obj`, atoms and products; `pair` is `⟨R, S⟩`, `fn` an infinite map relation composed on the right,
  so `x+y` is `comp (pair x y) (fn (.dy .add h))`; a run value `RelV` is key and value columns of one length.
  `run_sound`: `run P = ok R → R.Holds = den P`, from one lemma per node; a kernel node whose kernel has
  no theorem yet (`comp`, `∩`, `∪`, `𝟘`, `⊤`, `mapVal`, `pair`, `Ew.val`, `Ew.valAtom`, `Find.where` with `pick`)
  contributes its law to `Sound P`. A coreflexive `c?` runs composed on either side: `R c?` on `R`'s value, `c? R` on its key.
-/
import LeetQ.Rel.Algebra
import LeetQ.Rel.SpecStruct
import LeetQ.Rel.SpecScan
import LeetQ.Rel.SpecFind

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Eval
open Freyd Freyd.Alg Freyd.Alg.RelSet PowerAllegory
open LeetQ.Rel.Verb (ofExcept rel_iff mk_rel til_rel where_rel)

namespace Verb
open Freyd.Alg.RelSet.ListRel (dList)

/-- `⦇e, f⦈` on lists of longs, `f` the step: the per-segment fold of design P12. -/
def fold (e : Int64) (f : Int64 → Int64 → Int64) : dList Int64 ⟶ (⟨Int64⟩ : RelSet.{0}) :=
  ⦇(junc (sumCop (CL.dL Unit) ⟨Int64 × Int64⟩) (graph fun _ => e) (graph fun q : Int64 × Int64 => f q.1 q.2)
    : Alg (CL.F Unit Int64) (⟨Int64⟩ : RelSet.{0}))⦈

end Verb

namespace Alg
variable {A B : QAtomicType}

/-- `⦇e,f⦈` of each segment of `Λ`'s carrier, `op` its kernel (`Ops.overBy`), keyed by the carrier's keys. -/
def overP (op : Kernel.Coc.Over) (F : (g : Nat) × Arr A g × Parted .long) : Except String (Rel A .long) := do
  let some r := Ops.overBy op F.2.2 | throw "f/ by: no grouped kernel for this op"
  pure ⟨F.1, F.2.1, ← Arr.ofPart .long F.1 r.2.part "f/ by"⟩

/-- `Λ(R) ≫ ∋`: the carrier built, then flattened. -/
def lamMem (R : Rel A B) : Except String (Rel A B) := do memP (← transposeP R)

/-- `Λ(R) ≫ est(≤)` (`desc`: `est(≥)`): the carrier's segments reduced by `lesser`/`greater`. -/
def lamEst (desc : Bool) (R : Rel A .long) : Except String (Rel A .long) := do
  overP (if desc then .greater else .lesser) (← transposeP R)

/-- `Λ(G) ≫ enum ≫ list(x) ≫ ⦇e,f⦈`: `G`'s positions per key, gathered through `x` in place of the
    segment values (the offsets kept), then each segment folded by `op`. -/
def lamFold (op : Kernel.Coc.Over) {n : Nat} (x : Arr .long n) (G : Rel A .long) : Except String (Rel A .long) := do
  let F ← transposeP G
  let P := F.2.2
  let (_, i) ← arrDense P.val
  let v ← Vals.ofParts (.atom .long) P.n (pick .long ⟨_, x⟩ i) "list(x)"
  overP op ⟨F.1, F.2.1, ⟨P.g, P.n, P.o, P.co, v⟩⟩

/-- `R ≫ !e`: `n#,e` beside `R`'s key (`Struct.take` of `Struct.enlist`). A boxed `e` has no atom
    column, so it is refused. -/
def cstVal {K t u : QAtomicType} (e : El u) (R : Rel K t) : Except String (Rel K u) :=
  if h : u = .general then throw "!e: no general constant" else do
    let a ← Struct.enlist u e h
    pure ⟨R.n, R.key, ← Arr.ofPart u R.n (← Struct.take (R.n : Int) a).part "!e"⟩

/-- `Λ(G) ≫ enum ≫ length`: `countBy` of the carrier's segments, keyed by the carrier's keys. -/
def lamCount (G : Rel A .long) : Except String (Rel A .long) := do
  let F ← transposeP G
  let r := Ops.countBy F.2.2
  pure ⟨F.1, F.2.1, ← Arr.ofPart .long F.1 r.part "count by"⟩

end Alg

/-- An object as an object of `RelSet`: its elements, a product the carrier `rpair` targets. -/
@[reducible] def Ob (A : Obj) : RelSet.{0} := ⟨A.El⟩

/-- A relation as `run` answers it: `Rel` itself, its `Holds` read as a `RelSet` arrow. -/
abbrev RelV (A B : Obj) := Rel A B

/-- A kernel's answer as a run value: at two atoms the columns are the same. -/
def RelV.of {A B : QAtomicType} (R : Rel A B) : RelV (.atom A) (.atom B) := ⟨R.n, R.key, R.val⟩

/-- A run value at two atoms as a kernel's argument. -/
def RelV.toRel {A B : QAtomicType} (R : RelV (.atom A) (.atom B)) : Rel A B := ⟨R.n, R.key, R.val⟩

theorem RelV.toRel_holds {A B : QAtomicType} (R : RelV (.atom A) (.atom B)) : R.toRel.Holds = R.Holds := rfl

/-- A kernel on `Rel` answering a run value. -/
def liftV {A B : QAtomicType} : Except String (Rel A B) → Except String (RelV (.atom A) (.atom B))
  | .ok R => .ok (.of R)
  | .error e => .error e

theorem liftV_ok {A B : QAtomicType} {x : Except String (Rel A B)} {T : RelV (.atom A) (.atom B)}
    (h : liftV x = .ok T) : x = .ok T.toRel := by
  cases x with
  | error e => cases h
  | ok R => cases h; rfl

/-- A position read as a long: the key `til n` of a list. -/
abbrev posL : Idx ⟶ Ob .long := graph Int64.ofNat

/-- A map code: an infinite relation, so it has no stored form and runs only composed with a finite `P`: on the
    right, `comp P (fn c)`, or, a coreflexive being its own converse, on the left, `comp (fn (.test c)) P`. -/
inductive Fn : Obj → Obj → Type
  /-- the dyadic map `v` (P6′) -/
  | dy {t u rt : QAtomicType} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) :
      Fn (.prod (.atom t) (.atom u)) (.atom rt)
  /-- `graph(f)`, `f` what the kernel `op` computes; `Alg.mapVal` keeps the value type, so `t` to `t` -/
  | mono {t : QAtomicType} (op : UInt8) (f : El t → El t) : Fn (.atom t) (.atom t)
  /-- `!e`, the constant map (`miss`, `χ`) -/
  | cst {t u : QAtomicType} (e : El u) : Fn (.atom t) (.atom u)
  /-- `π₁` -/
  | fst {A B : Obj} : Fn (.prod A B) A
  /-- `π₂` -/
  | snd {A B : Obj} : Fn (.prod A B) B
  /-- A section: `(v a)`, `x ↦ x v a`; `left`: `(a v)`, `x ↦ a v x`, the operand types of `h` swapped -/
  | sect {t u rt : QAtomicType} (left : Bool) (v : Prim.Dyadic) (h : Eval.ewType v (cond left u t) (cond left t u) = some rt)
      (a : El u) : Fn (.atom t) (.atom rt)
  /-- `c?`, the coreflexive on `{a | c(a) = true}` -/
  | test {A : Obj} (c : Fn A (.atom .boolean)) : Fn A A
  /-- `x ↦ x has t low zero bits` -/
  | lowZero (t : Nat) : Fn (.atom .long) (.atom .boolean)

/-- A verb's program: one constructor per executable primitive, the leaves stored data. -/
inductive Prog : Obj → Obj → Type
  /-- a stored relation, a dict -/
  | rel {A B : QAtomicType} (R : Rel A B) : Prog (.atom A) (.atom B)
  /-- a list `x : til n → t` -/
  | arr {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog (.atom .long) (.atom t)
  /-- `!n = 𝟙(til n)` -/
  | til (n : Nat) : Prog (.atom .long) (.atom .long)
  | idU {t : QAtomicType} {m : Nat} (U : Arr t m) : Prog (.atom t) (.atom t)
  | zero {A B : QAtomicType} : Prog (.atom A) (.atom B)
  | top {A B : QAtomicType} {ma mb : Nat} (Ua : Arr A ma) (Ub : Arr B mb) : Prog (.atom A) (.atom B)
  | comp {A B C : Obj} : Prog A B → Prog B C → Prog A C
  | conv {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom B) (.atom A)
  | inter {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom A) (.atom B) → Prog (.atom A) (.atom B)
  | union {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom A) (.atom B) → Prog (.atom A) (.atom B)
  /-- `⟨R, S⟩` (P13): one key, the two value columns side by side -/
  | pair {K A B : Obj} : Prog K A → Prog K B → Prog K (.prod A B)
  /-- a map code as a relation; a map is composed on the right, `comp P (fn c)`, not a node wrapping `P` -/
  | fn {A B : Obj} : Fn A B → Prog A B
  /-- `Λ(R) ≫ ∋` (P8, P9): `Λ` makes the keys-and-`Parted` carrier, `∋` flattens it -/
  | mem {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom A) (.atom B)
  /-- `Λ(R) ≫ est(≤)`, `desc`: `est(≥)` (P8, P10) -/
  | extr {A : QAtomicType} (desc : Bool) : Prog (.atom A) (.atom .long) → Prog (.atom A) (.atom .long)
  /-- `dom(G) ≫ Λ(G) ≫ enum ≫ list(x) ≫ ⦇e,f⦈` (P8, P11, P12), `G` keys against positions, `op` the kernel of `f`;
      `Λ` on `dom G` only, since a key that does not occur has no row (`Λ` alone gives it `e`) -/
  | fold {A : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64) (x : Arr .long n) :
      Prog (.atom A) (.atom .long) → Prog (.atom A) (.atom .long)
  /-- `enum(dom(x ≫ !1b°))` (P11): the set bits of `x`, ascending, keyed by `til m` -/
  | enum {n : Nat} (x : Arr .boolean n) : Prog (.atom .long) (.atom .long)
  /-- `R ≫ corNeg(C)`, the anti-join (P16) -/
  | anti {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom B) (.atom B) → Prog (.atom A) (.atom B)
  /-- `dom R = 𝟙 ∩ (R ≫ R°)`; `ran R` is `dom R°` -/
  | dom {A B : QAtomicType} : Prog (.atom A) (.atom B) → Prog (.atom A) (.atom A)
  /-- `enum` of the positions `j < n` whose long is in `dom C` (P11 over a computed coreflexive) -/
  | enumC (n : Nat) : Prog (.atom .long) (.atom .long) → Prog (.atom .long) (.atom .long)
  /-- `dom(G ≫ pos) ≫ Λ(G ≫ pos) ≫ enum ≫ length` (P8, P11, P12): each occurring key's count; no `Coc.Over` counts -/
  | count {A : QAtomicType} : Prog (.atom A) (.atom .long) → Prog (.atom A) (.atom .long)
  /-- `grade(⊴ₓ) = cst(til n) ≫ sort(⊴ₓ)` (P17): the stable grade of `x` under its type's strict order `lt`,
      `desc` flipping it; `x` keyed by `til n` -/
  | grade {t : QAtomicType} {n : Nat} (desc : Bool) (lt : El t → El t → Prop) (x : Arr t n) :
      Prog (.atom .long) (.atom .long)
  /-- `R ≫ (⊴) ≫ S°`, the order join (P7), `v` one of `<`, `≤`, `>`, `≥`: literal, `n·m` rows -/
  | ojoin {A B : QAtomicType} (v : Prim.Dyadic) :
      Prog (.atom A) (.atom .long) → Prog (.atom B) (.atom .long) → Prog (.atom A) (.atom B)
  /-- R6's right side: `x bin y`, `Find.bin` bisecting the ascending `x` -/
  | binJ {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) : Prog (.atom .long) (.atom .long)
  /-- R7's right side: `aj` at one long key column a side, `Struct.aj` (`Eval.groupEdge`) -/
  | ajJ {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) : Prog (.atom .long) (.atom .long)
  /-- R8's right side: the `wj` (`prev`) or `wj1` window, left row ↦ right row, `Struct.wjP`'s ranges -/
  | wjJ {nl nr : Nat} (prev : Bool) (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) : Prog (.atom .long) (.atom .long)

/-- The comparison `v` names, `𝟘` for a verb that is none. -/
def ord : Prim.Dyadic → (Ob .long ⟶ Ob .long)
  | .lt => fun a b : Int64 => a < b
  | .le => fun a b : Int64 => a ≤ b
  | .gt => fun a b : Int64 => a > b
  | .ge => fun a b : Int64 => a ≥ b
  | _ => fun _ _ => False

/-- `≥` on positions, the order `est` takes the last by. -/
abbrev geN : Idx ⟶ Idx := fun a b : Nat => a ≥ b

/-- The `wj` (`true`) and `wj1` (`false`) window on positions, `K = lk ≫ rk°` the key match:
    `wj1 = K ∩ (w₀ ≫ (≤) ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)`; `wj` opens the window at `<` and adds the prevailing
    row, `Λ(K ∩ (w₀ ≫ (≥) ≫ rt°)) ≫ est(≥)`. -/
def win {nl nr : Nat} : Bool → Arr .long nl → Arr .long nl → Arr .long nl → Arr .long nr → Arr .long nr → (Idx ⟶ Idx)
  | true, lk, w₀, w₁, rk, rt => ((lk.rel ≫ rk.rel°) ∩ (w₀.rel ≫ ord .lt ≫ rt.rel°)) ∩ (w₁.rel ≫ ord .ge ≫ rt.rel°) ∪
      (Λ ((lk.rel ≫ rk.rel°) ∩ (w₀.rel ≫ ord .ge ≫ rt.rel°)) ≫ est geN)
  | false, lk, w₀, w₁, rk, rt => ((lk.rel ≫ rk.rel°) ∩ (w₀.rel ≫ ord .le ≫ rt.rel°)) ∩ (w₁.rel ≫ ord .ge ≫ rt.rel°)

/-- A section's step: `x ↦ x v a`, `left`: `x ↦ a v x`. -/
def sectEl {t u rt : QAtomicType} : (left : Bool) → (v : Prim.Dyadic) →
    Eval.ewType v (cond left u t) (cond left t u) = some rt → El u → El t → Except String (El rt)
  | false, v, h, a, x => elem v h x a
  | true, v, h, a, x => elem v h a x

/-- `x` has `t` low zero bits, read off its bits, `0N` being `2^63` there. -/
def lowBits (t : Nat) (x : Int64) : Bool := x.toBitVec.toNat &&& (2 ^ t - 1) == 0

/-- The relation a map code names. -/
def Fn.den : {A B : Obj} → Fn A B → (Ob A ⟶ Ob B)
  | _, _, .dy v h => ofExcept fun p => elem v h p.1 p.2
  | _, _, .mono _ f => graph f
  | _, _, .cst e => Verb.cst e
  | _, _, .fst => graph Prod.fst
  | _, _, .snd => graph Prod.snd
  | _, _, .sect l v h a => ofExcept (sectEl l v h a)
  | _, _, .test c => corefl fun a => c.den a true
  | _, _, .lowZero t => ofExcept (ε := String) fun x : Int64 => .ok (lowBits t x)

namespace Prog

/-- The spec: the relation the term denotes. -/
def den : {A B : Obj} → Prog A B → (Ob A ⟶ Ob B)
  | _, _, rel R => R.Holds
  | _, _, arr x => posL° ≫ x.rel
  | _, _, til n => posL° ≫ corefl (· < n) ≫ posL
  | _, _, idU U => Verb.ran U.rel
  | _, _, zero => 𝟘
  | _, _, top Ua Ub => Ua.rel° ≫ ⊤ ≫ Ub.rel
  | _, _, comp P Q => P.den ≫ Q.den
  | _, _, conv P => P.den°
  | _, _, inter P Q => P.den ∩ Q.den
  | _, _, union P Q => P.den ∪ Q.den
  | _, _, pair P Q => rpair P.den Q.den
  | _, _, fn c => c.den
  | _, .atom B, mem P => Λ P.den ≫ ∋ (Ob B)
  | _, _, extr false P => Λ P.den ≫ est (fun a b : Int64 => a ≤ b)
  | _, _, extr true P => Λ P.den ≫ est (fun a b : Int64 => a ≥ b)
  | _, _, fold _ e f x G => Verb.dom (G.den ≫ Verb.pos) ≫ Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold e f
  | _, _, enum x => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (x.rel ≫
      (Verb.cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys ∧ (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, anti P C => P.den ≫ Verb.corNeg C.den
  | _, _, dom P => Verb.dom P.den
  | _, _, enumC n C => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (corefl (· < n) ≫ posL ≫ C.den))) ys ∧
      (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, count G => Verb.dom (G.den ≫ Verb.pos) ≫ Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.length ≫ graph Int64.ofNat
  | _, _, grade (n := n) d lt x => posL° ≫ fun i v => ∃ G, Verb.sort (Verb.stable x.rel (if d then flip lt else lt))
      (CL.ofList (List.range n)) G ∧ (ix (CL.toList G) ≫ graph Int64.ofNat) i v
  | _, _, ojoin v P Q => P.den ≫ ord v ≫ Q.den°
  | _, _, binJ x y => posL° ≫ y.rel ≫ Verb.miss ((Λ (ord .ge ≫ x.rel°) ≫ est geN) ≫ graph Int64.ofNat) (-1)
  | _, _, ajJ (nl := nl) lk lt rk rt => posL° ≫ corefl (· < nl) ≫
      Verb.miss ((Λ ((lk.rel ≫ rk.rel°) ∩ (lt.rel ≫ ord .ge ≫ rt.rel°)) ≫ est geN) ≫ graph Int64.ofNat) Int64.minValue
  | _, _, wjJ prev lk w₀ w₁ rk rt => posL° ≫ win prev lk w₀ w₁ rk rt ≫ posL

/-- `til n` as a key, refused past `USize`, where `tilLongs` would wrap. -/
def tilKey (n : Nat) : Except String (Arr .long n) :=
  if n < USize.size then Struct.til n else throw s!"til {n}: past USize"

/-- `enumC`'s kernel: `til n in C`'s keys (`Find.in`), then `Find.where` keyed by `til m`. -/
def enumIn (n : Nat) (C : Rel .long .long) : Except String (Rel .long .long) := do
  let w := Find.where (Find.«in» (← tilKey n) C.key); pure ⟨w.1, ← tilKey w.1, w.2⟩

/-- The order join's literal kernel (P7): `prod R S`, `v` on the two value columns (P6′), the rows whose bit
    is set (`Find.where`), their two keys picked. -/
def ordJoin {A B : QAtomicType} (v : Prim.Dyadic) (R : Rel A .long) (S : Rel B .long) : Except String (Rel A B) := do
  unless v matches .lt | .le | .gt | .ge do throw "order join: not a comparison"
  let T ← Alg.prod R S
  let w := Find.where (← Ew.val v .boolean T.val.1 T.val.2)
  let (_, i) ← Alg.arrDense w.2
  pure ⟨w.1, ← Vals.ofParts (.atom A) w.1 (Alg.pick A ⟨_, T.key.1⟩ i) "order join",
    ← Vals.ofParts (.atom B) w.1 (Alg.pick B ⟨_, T.key.2⟩ i) "order join"⟩

/-- `aj`'s kernel keyed by `til m`: one long key column a side. -/
def ajRun {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) : Except String ((m : Nat) × Arr .long m) :=
  Struct.aj #[⟨.long, _, lk⟩] #[⟨.long, _, rk⟩] ⟨.long, _, lt⟩ ⟨.long, _, rt⟩

/-- `wj`/`wj1`'s kernel: `Struct.wjP`'s windows as the carrier of `til nl`, flattened (`memP`). -/
def wjRun {nl nr : Nat} (prev : Bool) (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    Except String (Rel .long .long) := do
  let P ← Struct.wjP prev ⟨.long, _, w₀⟩ ⟨.long, _, w₁⟩ #[⟨.long, _, lk⟩] #[⟨.long, _, rk⟩] ⟨.long, _, rt⟩
  Alg.memP ⟨nl, ← tilKey nl, P⟩

/-- `⟨R, S⟩`: `Alg.pair`, at any sides — a product key joins on its tuple codes. -/
def pairV {K A B : Obj} (R : RelV K A) (S : RelV K B) : Except String (RelV K (.prod A B)) := Alg.pair R S

/-- A section on a value column: `Ew.valAtom`, `left`: `Ew.atomVal`, the atom the kernel's one-element operand,
    one pass over `x`, no constant column built. A boxed atom has no such operand. -/
def sectVal {t u rt : QAtomicType} {n : Nat} (l : Bool) (v : Prim.Dyadic) (a : El u) (x : Arr t n) :
    Except String (Arr rt n) :=
  if hu : u = .general then throw "sect: a general atom has no kernel operand; compose a stored constant" else
    match l with
    | false => Ew.valAtom v rt x a hu
    | true => Ew.atomVal v rt a x hu

/-- `(x & m) = 0`, `m = 2^t - 1`: the kernel reads an encoded `x` in place, the mask its atom. -/
def lowZeroArr {n : Nat} (t : Nat) (x : Arr .long n) : Except String (Arr .boolean n) :=
  match Kernel.lowZeroPayload n x.enc (UInt64.ofNat (2 ^ t - 1)) with
  | some e => Arr.of .boolean n (.vector .boolean n e none) "lowZero"
  | none => throw "lowZero: this long column has no dense payload"

/-- `x` at the rows `i`, column by column (`Obj.pick`). -/
def _root_.LeetQ.Rel.Vals.pick {n m : Nat} {A : Obj} (i : Arr .long m) (x : Vals A n) : Except String (Vals A m) := do
  Vals.ofParts A m (A.pick x.parts (← Alg.arrDense i).2) "pick"

/-- `R`'s rows whose bit in `b` is set: `Find.where`, then key and value picked (as `ordJoin`). -/
def _root_.LeetQ.Rel.RelV.sel {K A : Obj} {m : Nat} (b : Arr .boolean m) (R : RelV K A) : Except String (RelV K A) := do
  let w := Find.where b
  pure ⟨w.1, ← Vals.pick w.2 R.key, ← Vals.pick w.2 R.val⟩

/-- `R ≫ c` applied to `R`'s value columns; the key stays. -/
def _root_.LeetQ.Rel.Fn.apply {K : Obj} : {A B : Obj} → Fn A B → RelV K A → Except String (RelV K B)
  | _, _, .dy (rt := rt) v _, R => do pure ⟨R.n, R.key, ← Ew.val v rt R.val.1 R.val.2⟩
  | _, _, .mono op _, R => match K, R with
    | .atom _, R => liftV (Alg.mapVal op R.toRel)
    | .prod .., _ => throw "graph(f): no kernel keeps a product key; compose it before the key is paired"
  | _, _, .cst e, R => match K, R with
    | .atom _, R => liftV (Alg.cstVal e R.toRel)
    | .prod .., _ => throw "!e: no kernel keeps a product key; compose it before the key is paired"
  | _, _, .fst, R => pure ⟨R.n, R.key, R.val.1⟩
  | _, _, .snd, R => pure ⟨R.n, R.key, R.val.2⟩
  | _, _, .sect (t := t) (rt := rt) l v _ a, R => do pure ⟨R.n, R.key, ← sectVal (t := t) (rt := rt) l v a R.val⟩
  | _, _, .test c, R => do RelV.sel (← c.apply R).val R
  | _, _, .lowZero t, R => do pure ⟨R.n, R.key, ← lowZeroArr t R.val⟩

/-- `c? ≫ R` with `R` run: `c` on the key column, handed as a value column beside itself, then `RelV.sel`; a
    kernel that needs an atomic key refuses a product key in `Fn.apply`. -/
def testKey {A C : Obj} (c : Fn A (.atom .boolean)) (R : RelV A C) : Except String (RelV A C) := do
  RelV.sel (← c.apply (K := A) ⟨R.n, R.key, R.key⟩).val R

/-- The trailing zero bits of `n`, `k` the bits left to read. -/
def tzNat : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n % 2 = 1 then 0 else tzNat k (n / 2) + 1

/-- The trailing zero bits of `a`. -/
def tz (a : Int64) : Nat := tzNat 64 a.toBitVec.toNat

/-- `(×a)° (×a) ≫ R`: `ran(×a)` is the multiples of `2^tz(a)` (`ran_mul`). `a = 0` and `a = 0N` are refused, not
    computed: `×0` sends `0N` to `0N` and all else to `0`, and `×0N` sends all to `0N`, neither of them such a set. -/
def ranMul {C : Obj} (a : Int64) (R : RelV .long C) : Except String (RelV .long C) :=
  if a = 0 then throw "(×0)°(×0): ran(×0) is {0,0N}, not a multiples-of-2^t test; select with (=0) and (=0N)"
  else if a = Int64.minValue then throw "(×0N)°(×0N): ran(×0N) is {0N}, not a multiples-of-2^t test; select with (=0N)"
  else testKey (.lowZero (tz a)) R

/-- `P` as a coreflexive, its kernel on a run `R` beside it: `comp P R` runs `R` and applies `c` to the key. `c?` is
    one, and so is `(×a)° (×a)` with one `a`: `f° f = ran(f)` for any map `f`, and each side alone is not runnable. -/
def asTest {A B : Obj} : Prog A B → Option ((C : Obj) → RelV B C → Except String (RelV A C))
  | fn (.test c) => some fun _ R => testKey c R
  | comp (conv (fn (@Fn.sect .long .long .long false .mul _ a))) (fn (@Fn.sect .long .long .long false .mul _ a')) =>
    if (a : Int64) = (a' : Int64) then some fun _ R => ranMul a R else none
  | _ => none

/-- `P ≫ Q` with `Q` stored: `Alg.comp`, which joins one value column on one key column. -/
def compV : {A B C : Obj} → RelV A B → RelV B C → Except String (RelV A C)
  | .atom _, .atom _, .atom _, R, S => liftV (Alg.comp R.toRel S.toRel)
  | _, _, _, _, _ => throw "comp: Alg.comp needs atomic objects; a product can only be composed with `fn` on its right"

/-- The map code `Q` is, if any: `comp P (fn c)` runs `P` and applies `c`, it does not run `fn c` alone. -/
def asFn {A B : Obj} : Prog A B → Option (Fn A B)
  | fn c => some c
  | _ => none

theorem asFn_some {A B : Obj} {Q : Prog A B} {c : Fn A B} (h : Q.asFn = some c) : Q = fn c := by
  cases Q <;> first | (cases h; rfl) | cases h

/-- The literal interpreter: one kernel per node. -/
def run : {A B : Obj} → Prog A B → Except String (RelV A B)
  | _, _, rel R => pure (.of R)
  | _, _, arr (n := n) x => do pure ⟨n, ← tilKey n, x⟩
  | _, _, til n => do pure (.of (Alg.idU (← tilKey n)))
  | _, _, idU U => pure (.of (Alg.idU U))
  | _, _, zero => liftV Alg.zero
  | _, _, top Ua Ub => liftV (Alg.top Ua Ub)
  | _, _, comp P Q => match P.asTest with
    | some g => do g _ (← Q.run)
    | none => do
      let R ← P.run
      match Q.asFn with
      | some c => c.apply R
      | none => compV R (← Q.run)
  | _, _, conv P => do liftV (Alg.conv (← P.run).toRel)
  | _, _, inter P Q => do liftV (Alg.inter (← P.run).toRel (← Q.run).toRel)
  | _, _, union P Q => do liftV (Alg.union (← P.run).toRel (← Q.run).toRel)
  | _, _, pair P Q => do pairV (← P.run) (← Q.run)
  | _, _, fn _ => throw "fn: a map is an infinite relation with no stored form; compose it on the right of a finite relation, comp P (fn c)"
  | _, _, mem P => do liftV (Alg.lamMem (← P.run).toRel)
  | _, _, extr d P => do liftV (Alg.lamEst d (← P.run).toRel)
  | _, _, fold op _ _ x G => do liftV (Alg.lamFold op x (← G.run).toRel)
  | _, _, enum x => do let w := Find.where x; pure ⟨w.1, ← tilKey w.1, w.2⟩
  | _, _, anti P C => do liftV (Alg.antiJoin (← P.run).toRel (← C.run).toRel)
  | _, _, dom P => do liftV (Alg.dom (← P.run).toRel)
  | _, _, enumC n C => do liftV (enumIn n (← C.run).toRel)
  | _, _, count G => do liftV (Alg.lamCount (← G.run).toRel)
  | _, _, grade (n := n) d _ x => do
    let S := Ops.grade d x
    pure ⟨n, ← tilKey n, S⟩
  | _, _, ojoin v P Q => do liftV (ordJoin v (← P.run).toRel (← Q.run).toRel)
  | _, _, binJ (ny := ny) x y => do let r := Find.bin x y; pure ⟨ny, ← tilKey ny, r⟩
  | _, _, ajJ lk lt rk rt => do let r ← ajRun lk lt rk rt; pure ⟨r.1, ← tilKey r.1, r.2⟩
  | _, _, wjJ prev lk w₀ w₁ rk rt => liftV (wjRun prev lk w₀ w₁ rk rt)

/-- `S` lists each group of `X` as a permutation of it: defined on `dom X`, `S ⊑ dom X ≫ Λ X ≫ enum ≫ perm`.
    The kernel lists a group in code or first-appearance order (`familyP`), not by position. -/
def Segs {K : RelSet.{0}} (X : K ⟶ Idx) (S : K ⟶ ListRel.dList Nat) : Prop :=
  (∀ a, Verb.dom X a a → ∃ ys, S a ys) ∧ ∀ a ys, S a ys → (Verb.dom X ≫ Λ X ≫ Verb.enum ≫ ListRel.perm) a ys

/-- `list(R)` follows a permutation of its input with one of its output. -/
theorem listP_perm {α β : Type} {R} : ∀ {ys ys' : CL.ConsList Unit α}, ListRel.Perm ys ys' →
    ∀ {zs : CL.ConsList Unit β}, ListRel.listP R ys zs → ∃ zs', ListRel.listP R ys' zs' ∧ ListRel.Perm zs zs'
  | _, _, .nil, zs, h => ⟨zs, h, ListRel.Perm.refl zs⟩
  | _, _, .cons a p, zs, h => by
    cases zs with
    | wrap _ => exact h.elim
    | cons b w =>
      obtain ⟨w', hw', pw⟩ := listP_perm p h.2
      exact ⟨.cons b w', ⟨h.1, hw'⟩, .cons b pw⟩
  | _, _, .swap a b x, zs, h => by
    cases zs with
    | wrap _ => exact h.elim
    | cons c z =>
      cases z with
      | wrap _ => exact h.2.elim
      | cons d w => exact ⟨.cons d (.cons c w), ⟨h.2.1, h.1, h.2.2⟩, .swap c d w⟩
  | _, _, .trans p q, zs, h => by
    obtain ⟨z₁, h₁, p₁⟩ := listP_perm p h
    obtain ⟨z₂, h₂, p₂⟩ := listP_perm q h₁
    exact ⟨z₂, h₂, .trans p₁ p₂⟩

/-- A right fold whose step is left-commutative ignores the order of the list. -/
theorem foldr_perm {α γ : Type} {g : α → γ → γ} (hg : ∀ a b c, g a (g b c) = g b (g a c)) (e : γ) :
    ∀ {ys ys' : CL.ConsList Unit α}, ListRel.Perm ys ys' → (CL.toList ys).foldr g e = (CL.toList ys').foldr g e
  | _, _, .nil => rfl
  | _, _, .cons a p => congrArg (g a) (foldr_perm hg e p)
  | _, _, .swap a b _ => hg a b _
  | _, _, .trans p q => (foldr_perm hg e p).trans (foldr_perm hg e q)

/-- `list(R) ≫ ⦇e,f⦈` ignores the order of its input when `f` is left-commutative. -/
theorem listFold_perm {α : Type} {R} {e : Int64} {f : Int64 → Int64 → Int64} (hf : ∀ a b c, f a (f b c) = f b (f a c))
    (ys ys' : CL.ConsList Unit α) (b : Int64) (p : ListRel.Perm ys ys') (h : (ListRel.list R ≫ Verb.fold e f) ys b) :
    (ListRel.list R ≫ Verb.fold e f) ys' b := by
  obtain ⟨zs, hz, hb⟩ := h
  obtain ⟨zs', hz', p'⟩ := listP_perm p hz
  rw [show Verb.fold e f = graph (fun ys => (CL.toList ys).foldr f e) from (Verb.foldr_cata f e).symm] at hb ⊢
  exact ⟨zs', hz', Eq.trans hb (foldr_perm hf e p')⟩

/-- `length ≫ ofNat` ignores the order of its input. -/
theorem length_perm {α : Type} (ys ys' : CL.ConsList Unit α) (b : Int64) (p : ListRel.Perm ys ys')
    (h : (ListRel.length ≫ graph Int64.ofNat) ys b) : (ListRel.length ≫ graph Int64.ofNat) ys' b := by
  obtain ⟨c, hc, hb⟩ := h
  exact ⟨c, Eq.trans hc (clen_perm p), hb⟩
where
  clen_perm : ∀ {ys ys' : CL.ConsList Unit α}, ListRel.Perm ys ys' → ListRel.clen ys = ListRel.clen ys'
  | _, _, .nil => rfl
  | _, _, .cons _ p => congrArg (· + 1) (clen_perm p)
  | _, _, .swap _ _ _ => rfl
  | _, _, .trans p q => (clen_perm p).trans (clen_perm q)

/-- `enum` gives a set one list. -/
theorem enum_simple {s} {zs zs' : CL.ConsList Unit Nat} (h : Verb.enum s zs) (h' : Verb.enum s zs') : zs = zs' := by
  obtain ⟨hs, o⟩ := (Verb.enum_iff _ _).1 h
  have pw := (Verb.orderedP_ofList _ (CL.toList zs)).1 (by rw [Verb.ofList_toList]; exact o)
  exact (((Verb.enum_ofList s _ pw fun i => (Verb.inlistP_ofList i _).symm.trans (by rw [Verb.ofList_toList, hs])) zs').1 h'
    |>.trans (Verb.ofList_toList zs)).symm

/-- **A group listed in any order folds as `enum` lists it**, for an `L` that ignores the order. -/
theorem segs_eq {K B : RelSet.{0}} {X : K ⟶ Idx} {S : K ⟶ ListRel.dList Nat} (hS : Segs X S)
    (L : ListRel.dList Nat ⟶ B) (hL : ∀ ys ys' b, ListRel.Perm ys ys' → L ys b → L ys' b) :
    S ≫ L = Verb.dom X ≫ Λ X ≫ Verb.enum ≫ L := by
  obtain ⟨hd, hs⟩ := hS
  refine hom_ext fun a b => ⟨fun ⟨ys, h, hl⟩ => ?_, fun ⟨a', ⟨e, hx⟩, s, hc, zs, he, hl⟩ => ?_⟩
  · obtain ⟨a', hx, s, hc, zs, he, p⟩ := hs a ys h
    exact ⟨a', hx, s, hc, zs, he, hL _ _ b p.symm hl⟩
  · subst e
    obtain ⟨ys, h⟩ := hd a ⟨rfl, hx⟩
    obtain ⟨_, ⟨e', _⟩, s', hc', zs', he', p⟩ := hs a ys h
    subst e'
    rw [Λ_eq_classifier] at hc hc'
    have hss : s' = s := hc'.trans hc.symm
    subst hss
    obtain rfl := enum_simple he he'
    exact ⟨ys, h, hL _ _ b p hl⟩

/-- The kernel law a map code needs, at key `K`; `fst` and `snd` project a column and need none (`Fn.apply_sound`). -/
def _root_.LeetQ.Rel.Fn.Sound (K : Obj) : {A B : Obj} → Fn A B → Prop
  | _, _, .dy (t := t) (u := u) (rt := rt) v h => ∀ n (x : Arr t n) (y : Arr u n) V, Ew.val v rt x y = .ok V →
      Ew.ValSpec v h x y V
  | .atom t, _, .mono op f => ∀ R T : RelV K t, (Fn.mono op f).apply R = .ok T →
      @Eq (Ob K ⟶ Ob t) T.Holds (R.Holds ≫ graph f)
  | .atom t, .atom u, .cst e => ∀ (R : RelV K t) (T : RelV K u), (Fn.cst e).apply R = .ok T →
      @Eq (Ob K ⟶ Ob u) T.Holds (R.Holds ≫ Verb.cst e)
  | _, _, .fst | _, _, .snd => True
  | _, _, .sect (t := t) (rt := rt) l v h a => ∀ n (x : Arr t n) (V : Arr rt n), sectVal l v a x = .ok V →
      x.toList.mapM (sectEl l v h a) = .ok V.toList
  | A, _, .test c => ∀ R T : RelV K A, (Fn.test c).apply R = .ok T → @Eq (Ob K ⟶ Ob A) T.Holds (R.Holds ≫ (Fn.test c).den)
  | _, _, .lowZero t => ∀ n (x : Arr .long n) (V : Arr .boolean n), lowZeroArr t x = .ok V →
      x.toList.mapM (fun a => (.ok (lowBits t a) : Except String _)) = .ok V.toList

/-- The kernel laws a term's run needs and no theorem gives yet, one per kernel node; the stored leaves,
    `til`, `idU` and `°` need none (`arr_sound` … `conv_sound`). -/
def Sound : {A B : Obj} → Prog A B → Prop
  | _, _, rel _ | _, _, arr _ | _, _, til _ | _, _, idU _ | _, _, fn _ => True
  | .atom A, .atom B, zero => ∀ T : RelV A B, liftV Alg.zero = .ok T → @Eq (Ob A ⟶ Ob B) T.Holds 𝟘
  | .atom A, .atom B, top Ua Ub => ∀ T : RelV A B, liftV (Alg.top Ua Ub) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (Ua.rel° ≫ ⊤ ≫ Ub.rel)
  | _, _, conv P => P.Sound
  | A, C, comp (B := B) P Q => match P.asTest with
    | some g => Q.Sound ∧ ∀ (R : RelV B C) (T : RelV A C), g C R = .ok T →
        @Eq (Ob A ⟶ Ob C) T.Holds (@Cat.comp _ _ (Ob A) (Ob B) (Ob C) P.den R.Holds)
    | none => P.Sound ∧ match Q.asFn with
      | some c => c.Sound A
      | none => Q.Sound ∧ ∀ (R : RelV A B) (S : RelV B C) (T : RelV A C), compV R S = .ok T →
          @Eq (Ob A ⟶ Ob C) T.Holds (@Cat.comp _ _ (Ob A) (Ob B) (Ob C) R.Holds S.Holds)
  | K, _, pair (A := A) (B := B) P Q => P.Sound ∧ Q.Sound ∧ ∀ (R : RelV K A) (S : RelV K B) (T : RelV K (.prod A B)),
      pairV R S = .ok T → @Eq (Ob K ⟶ Ob (.prod A B)) T.Holds (rpair R.Holds S.Holds)
  | .atom A, .atom B, inter P Q => P.Sound ∧ Q.Sound ∧ ∀ R S T : RelV A B, liftV (Alg.inter R.toRel S.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (R.Holds ∩ S.Holds)
  | .atom A, .atom B, union P Q => P.Sound ∧ Q.Sound ∧ ∀ R S T : RelV A B, liftV (Alg.union R.toRel S.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (R.Holds ∪ S.Holds)
  | .atom A, .atom B, mem P => P.Sound ∧ ∀ R T : RelV A B, liftV (Alg.lamMem R.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (Λ (R.Holds : Ob A ⟶ Ob B) ≫ ∋ (Ob B))
  | .atom A, _, extr d P => P.Sound ∧ ∀ R T : RelV A .long, liftV (Alg.lamEst d R.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob .long) T.Holds (extr d (rel R.toRel)).den
  | .atom A, _, fold op e f x G => G.Sound ∧ (∀ a b c, f a (f b c) = f b (f a c)) ∧ ∀ R T : RelV A .long,
      liftV (Alg.lamFold op x R.toRel) = .ok T → ∃ S, Segs ((R.Holds : Ob A ⟶ Ob .long) ≫ Verb.pos) S ∧
        @Eq (Ob A ⟶ Ob .long) T.Holds (S ≫ ListRel.list x.rel ≫ Verb.fold e f)
  | _, _, enum (n := n) _ => n < USize.size
  -- False at `B = .float`, so `run_sound` says nothing there: `Carrier .float` compares bits, the kernel
  -- codes take `-0.0 = 0.0` and equal NaNs. Conditioning this clause instead would make `run_sound` false.
  | .atom A, .atom B, anti P C => P.Sound ∧ C.Sound ∧ ∀ (R : RelV A B) (S : RelV B B) (T : RelV A B),
      liftV (Alg.antiJoin R.toRel S.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds ((R.Holds : Ob A ⟶ Ob B) ≫ Verb.corNeg S.Holds)
  | .atom A, _, dom (B := B) P => P.Sound ∧ ∀ (R : RelV A B) (T : RelV A A), liftV (Alg.dom R.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob A) T.Holds (Verb.dom (R.Holds : Ob A ⟶ Ob B))
  | _, _, enumC n C => C.Sound ∧ ∀ R T : RelV .long .long, liftV (enumIn n R.toRel) = .ok T →
      @Eq (Ob .long ⟶ Ob .long) T.Holds (enumC n (rel R.toRel)).den
  | .atom A, _, count G => G.Sound ∧ ∀ R T : RelV A .long, liftV (Alg.lamCount R.toRel) = .ok T →
      ∃ S, Segs ((R.Holds : Ob A ⟶ Ob .long) ≫ Verb.pos) S ∧
        @Eq (Ob A ⟶ Ob .long) T.Holds (S ≫ ListRel.length ≫ graph Int64.ofNat)
  | _, _, grade d lt x => ∀ S, Ops.grade d x = S → @Eq (Ob .long ⟶ Ob .long) (posL° ≫ S.rel) (grade d lt x).den
  | .atom A, .atom B, ojoin v P Q => P.Sound ∧ Q.Sound ∧ ∀ (R : RelV A .long) (S : RelV B .long) (T : RelV A B),
      liftV (ordJoin v R.toRel S.toRel) = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds ((R.Holds : Ob A ⟶ Ob .long) ≫ ord v ≫ (S.Holds : Ob B ⟶ Ob .long)°)
  -- `bin_rel`'s hypotheses: the law is proved
  | _, _, binJ (nx := nx) (ny := ny) x y => Find.Readable .long nx x.enc ∧ Find.Readable .long ny y.enc ∧
      nx < USize.size ∧ ny < USize.size ∧ ∀ i j : Fin nx, i ≤ j → x.get i ≤ x.get j
  -- `aj_rel`'s conclusion on the key columns as longs; `aj_rel` states it on their words
  | _, _, ajJ (nl := nl) lk lt rk rt => ∀ r, ajRun lk lt rk rt = .ok r → r.2.rel = corefl (· < nl) ≫
      Verb.miss ((Λ ((lk.rel ≫ rk.rel°) ∩ (lt.rel ≫ ord .ge ≫ rt.rel°)) ≫ est geN) ≫ graph Int64.ofNat) Int64.minValue
  | _, _, wjJ prev lk w₀ w₁ rk rt => ∀ T : RelV .long .long, liftV (wjRun prev lk w₀ w₁ rk rt) = .ok T →
      @Eq (Ob .long ⟶ Ob .long) T.Holds (wjJ prev lk w₀ w₁ rk rt).den

/-! ## Node soundness -/

/-- `x!y = x° ≫ y` for a run value. -/
theorem mkV {k v : QAtomicType} {n : Nat} (x : Arr k n) (y : Arr v n) :
    ((⟨n, x, y⟩ : RelV k v).Holds : Ob k ⟶ Ob v) = x.rel° ≫ y.rel := mk_rel x y

/-- A list keyed by `til n` holds `posL° ≫ x`. -/
theorem arr_sound {t : QAtomicType} {n : Nat} (x : Arr t n) {k : Arr .long n} (h : tilKey n = .ok k) :
    ((⟨n, k, x⟩ : RelV .long t).Holds : Ob .long ⟶ Ob t) = posL° ≫ x.rel := by
  unfold tilKey at h; split at h
  · rw [mkV, til_rel (by assumption) h]
    exact hom_ext fun a b => ⟨fun ⟨j, ⟨_, ⟨rfl, _⟩, e⟩, hx⟩ => ⟨j, e, hx⟩,
      fun ⟨j, e, hx⟩ => ⟨j, ⟨j, ⟨rfl, ((rel_iff x j b).1 hx).1⟩, e⟩, hx⟩⟩
  · cases h

/-- `!n` holds `𝟙` on `til n`. -/
theorem til_sound {n : Nat} {k : Arr .long n} (h : tilKey n = .ok k) :
    ((RelV.of (Alg.idU k)).Holds : Ob .long ⟶ Ob .long) = posL° ≫ corefl (· < n) ≫ posL := by
  unfold tilKey at h; split at h
  · rw [show RelV.of (Alg.idU k) = ⟨n, k, k⟩ from rfl, mkV, til_rel (by assumption) h]
    exact hom_ext fun a b => ⟨fun ⟨j, ⟨_, ⟨rfl, hj⟩, ea⟩, ⟨_, ⟨rfl, _⟩, eb⟩⟩ => ⟨j, ea, j, ⟨rfl, hj⟩, eb⟩,
      fun ⟨j, ea, _, ⟨rfl, hj⟩, eb⟩ => ⟨j, ⟨j, ⟨rfl, hj⟩, ea⟩, ⟨j, ⟨rfl, hj⟩, eb⟩⟩⟩
  · cases h

/-- `𝟙` on `U` holds `ran U`. -/
theorem idU_sound {t : QAtomicType} {m : Nat} (U : Arr t m) :
    ((RelV.of (Alg.idU U)).Holds : Ob t ⟶ Ob t) = Verb.ran U.rel := by
  rw [show RelV.of (Alg.idU U) = ⟨m, U, U⟩ from rfl, mkV]
  refine hom_ext fun a b => ⟨fun ⟨j, ha, hb⟩ => ⟨?_, j, ha, hb⟩, fun ⟨e, j, ha, hb⟩ => ⟨j, ha, hb⟩⟩
  obtain ⟨_, ea⟩ := (rel_iff U j a).1 ha; obtain ⟨_, eb⟩ := (rel_iff U j b).1 hb
  exact ea.symm.trans eb

/-- `R°` holds the converse (`conv_holds`). -/
theorem conv_sound {A B : QAtomicType} {R : RelV A B} {S : RelV B A} (h : liftV (Alg.conv R.toRel) = .ok S) :
    (S.Holds : Ob B ⟶ Ob A) = ((R.Holds : Ob A ⟶ Ob B)° : Ob B ⟶ Ob A) :=
  hom_ext fun b a => Alg.conv_holds (liftV_ok h) a b

/-- `R ≫ (v)` holds its spec, from the kernel's `Ew.ValSpec` (`val_rel`), at any key. -/
theorem dy_sound {K : Obj} {t u rt : QAtomicType} {v : Prim.Dyadic} {h : Eval.ewType v t u = some rt}
    {R : RelV K (.prod t u)} {V : Arr rt R.n} (hs : Ew.ValSpec v h R.val.1 R.val.2 V) :
    ((⟨R.n, R.key, V⟩ : RelV K rt).Holds : Ob K ⟶ Ob rt) = R.Holds ≫ (Fn.dy v h).den := by
  have hv := Verb.val_rel hs
  refine hom_ext fun k c => ⟨fun ⟨i, ek, ec⟩ => ?_, fun ⟨p, ⟨i, ek, ep⟩, e⟩ => ?_⟩
  · have hi : V.rel i.1 c := (rel_iff _ _ _).2 ⟨i.2, ec⟩
    rw [hv] at hi
    obtain ⟨p, ⟨ha, hb⟩, e⟩ := hi
    obtain ⟨_, ea⟩ := (rel_iff _ _ _).1 ha; obtain ⟨_, eb⟩ := (rel_iff _ _ _).1 hb
    exact ⟨p, ⟨i, ek, Prod.ext ea eb⟩, e⟩
  · subst ep
    have hi : V.rel i.1 c := by
      rw [hv]
      exact ⟨_, ⟨(rel_iff _ _ _).2 ⟨i.2, rfl⟩, (rel_iff _ _ _).2 ⟨i.2, rfl⟩⟩, e⟩
    obtain ⟨_, ec⟩ := (rel_iff _ _ _).1 hi
    exact ⟨i, ek, ec⟩

/-- `R ≫ g`, `g` a partial map on a value column, holds its spec, from the kernel's List spec (`ix_mapM`), at any key. -/
theorem mapM_sound {K : Obj} {t rt : QAtomicType} {g : El t → Except String (El rt)} {R : RelV K t} {V : Arr rt R.n}
    (hs : (R.val : Arr t R.n).toList.mapM g = .ok V.toList) :
    ((⟨R.n, R.key, V⟩ : RelV K rt).Holds : Ob K ⟶ Ob rt) = R.Holds ≫ ofExcept g := by
  have hv : V.rel = _ := Verb.ix_mapM _ _ _ hs
  refine hom_ext fun k c => ⟨fun ⟨i, ek, ec⟩ => ?_, fun ⟨b, ⟨i, ek, eb⟩, e⟩ => ?_⟩
  · have hi : V.rel i.1 c := (rel_iff _ _ _).2 ⟨i.2, ec⟩
    rw [hv] at hi
    obtain ⟨b, hb, e⟩ := hi
    obtain ⟨_, eb⟩ := (rel_iff _ _ _).1 hb
    exact ⟨b, ⟨i, ek, eb⟩, e⟩
  · subst eb
    have hi : V.rel i.1 c := by rw [hv]; exact ⟨_, (rel_iff _ _ _).2 ⟨i.2, rfl⟩, e⟩
    obtain ⟨_, ec⟩ := (rel_iff _ _ _).1 hi
    exact ⟨i, ek, ec⟩

/-- `R ≫ c` holds its spec, from the kernel law of `c`. -/
theorem _root_.LeetQ.Rel.Fn.apply_sound {K : Obj} : ∀ {A B : Obj} (c : Fn A B) {R : RelV K A} {T : RelV K B},
    c.Sound K → c.apply R = .ok T → (T.Holds : Ob K ⟶ Ob B) = R.Holds ≫ c.den
  | _, _, .dy _ _, _, _, hs, h => by
    simp only [Fn.apply, bind, Except.bind] at h; split at h
    · cases h
    cases h; exact dy_sound (hs _ _ _ _ (by assumption))
  | _, _, .mono .., _, _, hs, h => hs _ _ h
  | _, _, .cst _, _, _, hs, h => hs _ _ h
  | _, _, .fst, R, _, _, h => by
    cases h
    exact hom_ext fun k a => ⟨fun ⟨i, ek, ea⟩ => ⟨Vals.row R.val i, ⟨i, ek, rfl⟩, ea.symm⟩,
      fun ⟨p, ⟨i, ek, ep⟩, e⟩ => ⟨i, ek, by subst ep; exact e.symm⟩⟩
  | _, _, .snd, R, _, _, h => by
    cases h
    exact hom_ext fun k a => ⟨fun ⟨i, ek, ea⟩ => ⟨Vals.row R.val i, ⟨i, ek, rfl⟩, ea.symm⟩,
      fun ⟨p, ⟨i, ek, ep⟩, e⟩ => ⟨i, ek, by subst ep; exact e.symm⟩⟩
  | _, _, .sect .., _, _, hs, h => by
    simp only [Fn.apply, bind, Except.bind] at h; split at h
    · cases h
    cases h; exact mapM_sound (hs _ _ _ (by assumption))
  | _, _, .test _, _, _, hs, h => hs _ _ h
  | _, _, .lowZero _, _, _, hs, h => by
    simp only [Fn.apply, bind, Except.bind] at h; split at h
    · cases h
    cases h; exact mapM_sound (hs _ _ _ (by assumption))

/-- `&x` runs to its spec: `Find.where` keyed by `til m` holds `enum(dom(x ≫ !1b°))` (`where_rel`). -/
theorem enum_sound {n : Nat} (x : Arr .boolean n) (hn : n < USize.size) {R : RelV .long .long}
    (h : (enum x).run = .ok R) : (R.Holds : Ob .long ⟶ Ob .long) = (enum x).den := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  cases h
  obtain ⟨⟨ys, hy⟩, hall⟩ := where_rel (x := x) hn
  rw [arr_sound (Find.where x).2 (by assumption)]
  exact hom_ext fun a b => ⟨fun ⟨j, ea, hr⟩ => ⟨j, ea, ys, hy, by rw [← hall ys hy]; exact hr⟩,
    fun ⟨j, ea, ys', hy', hr⟩ => ⟨j, ea, by rw [hall ys' hy']; exact hr⟩⟩

/-- A grade that runs is the kernel's list keyed by `til n`. -/
theorem grade_run {t : QAtomicType} {n : Nat} {d : Bool} {lt : El t → El t → Prop} {x : Arr t n} {R : RelV .long .long}
    (h : (grade d lt x).run = .ok R) : ∃ S k, Ops.grade d x = S ∧ tilKey n = .ok k ∧ R = ⟨n, k, S⟩ := by
  simp only [run, bind, Except.bind] at h
  split at h
  · cases h
  · cases h; exact ⟨_, _, rfl, by assumption, rfl⟩

/-- **A sound term runs to its spec**: the answer of `run P` holds `den P`. -/
theorem run_sound : ∀ {A B : Obj} (P : Prog A B) {R : RelV A B}, P.Sound → P.run = .ok R →
    (R.Holds : Ob A ⟶ Ob B) = P.den
  | _, _, rel _, _, _, h => by cases h; rfl
  | _, _, arr x, _, _, h => by
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    · cases h; exact arr_sound x (by assumption)
  | _, _, til _, _, _, h => by
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    · cases h; exact til_sound (by assumption)
  | _, _, idU U, _, _, h => by cases h; exact idU_sound U
  | _, _, zero, _, hs, h => by unfold Sound at hs; exact hs _ h
  | _, _, top .., _, hs, h => by unfold Sound at hs; exact hs _ h
  | _, _, comp P Q, _, hs, h => by
    unfold Sound at hs
    simp only [run, bind, Except.bind] at h
    cases hp : P.asTest with
    | some g =>
      rw [hp] at hs h
      obtain ⟨sQ, hl⟩ := hs
      simp only at h; split at h
      · cases h
      rw [hl _ _ h, run_sound Q sQ (by assumption)]; rfl
    | none =>
      rw [hp] at hs h
      obtain ⟨sP, hl⟩ := hs
      simp only at h; split at h
      · cases h
      rename_i r hr
      cases hq : Q.asFn with
      | some c =>
        rw [hq] at h hl
        rw [Fn.apply_sound c hl h, run_sound P sP hr, asFn_some hq]; rfl
      | none =>
        rw [hq] at h hl
        obtain ⟨sQ, hl⟩ := hl
        simp only at h; split at h
        · cases h
        rw [hl _ _ _ h, run_sound P sP hr, run_sound Q sQ (by assumption)]; rfl
  | _, _, conv P, _, hs, h => by
    unfold Sound at hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [conv_sound h, run_sound P hs (by assumption)]; rfl
  | _, _, inter P Q, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sQ, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound Q sQ (by assumption)]; rfl
  | _, _, union P Q, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sQ, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound Q sQ (by assumption)]; rfl
  | _, _, pair P Q, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sQ, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound Q sQ (by assumption)]; rfl
  | _, _, fn _, _, _, h => by cases h
  | _, _, mem P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, extr d P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; cases d <;> simp only [den, RelV.toRel_holds] <;> rw [run_sound P sP (by assumption)]
  | _, _, fold _ _ _ _ G, _, hs, h => by
    unfold Sound at hs; obtain ⟨sG, hf, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    obtain ⟨S, hS, hT⟩ := hl _ _ h
    rw [hT, segs_eq hS _ (listFold_perm hf)]; simp only [den]; rw [run_sound G sG (by assumption)]
  | _, _, enum x, _, hs, h => enum_sound x hs h
  | _, _, anti P C, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sC, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound C sC (by assumption)]; rfl
  | _, _, dom P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, enumC _ C, _, hs, h => by
    unfold Sound at hs; obtain ⟨sC, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; simp only [den, RelV.toRel_holds]; rw [run_sound C sC (by assumption)]
  | _, _, count G, _, hs, h => by
    unfold Sound at hs; obtain ⟨sG, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    obtain ⟨S, hS, hT⟩ := hl _ _ h
    rw [hT, segs_eq hS _ length_perm]; simp only [den]; rw [run_sound G sG (by assumption)]
  | _, _, grade .., _, hs, h => by
    unfold Sound at hs
    obtain ⟨S, k, hg, hk, rfl⟩ := grade_run h
    rw [arr_sound S hk]; exact hs S hg
  | _, _, ojoin _ P Q, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sQ, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound Q sQ (by assumption)]; rfl
  | _, _, binJ x y, _, hs, h => by
    unfold Sound at hs; obtain ⟨hx, hy, hn, hm, hsort⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    cases h
    rw [arr_sound (Find.bin x y) (by assumption), Verb.bin_rel hx hy hn hm hsort]; rfl
  | _, _, ajJ .., _, hs, h => by
    unfold Sound at hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rename_i r hr
    split at h
    · cases h
    cases h
    rw [arr_sound r.2 (by assumption), hs r hr]; rfl
  | _, _, wjJ .., _, hs, h => by unfold Sound at hs; exact hs _ h

/-! ## Verbs that need no rewrite rule (design §2, §7 line 2) -/

/-- Two positions below `2^64` with one long are one position. -/
theorem ofNat_inj {j k : Nat} (hj : j < 2 ^ 64) (hk : k < 2 ^ 64) (e : Int64.ofNat j = Int64.ofNat k) : j = k := by
  have := congrArg (fun x : Int64 => x.toBitVec.toNat) e
  simp at this; omega

/-- `ej = l ≫ r°`: `ej_rel`'s right side at one key column. -/
def ej {nl nr : Nat} (l : Arr .long nl) (r : Arr .long nr) : Prog .long .long := comp (arr l) (conv (arr r))

theorem ej_den {nl nr : Nat} (l : Arr .long nl) (r : Arr .long nr) :
    (ej l r).den = posL° ≫ l.rel ≫ r.rel° ≫ posL :=
  hom_ext fun _ _ => ⟨fun ⟨c, ⟨j, ea, hl⟩, j', eb, hr⟩ => ⟨j, ea, c, hl, j', hr, eb⟩,
    fun ⟨j, ea, c, hl, j', hr, eb⟩ => ⟨c, ⟨j, ea, hl⟩, j', eb, hr⟩⟩

/-- `x!y = x° ≫ y`: the dict is the stored `Rel`, nothing runs (`mk_rel`). -/
def dict {k v : QAtomicType} {n : Nat} (x : Arr k n) (y : Arr v n) : Prog k v := rel ⟨n, x, y⟩

theorem dict_den {k v : QAtomicType} {n : Nat} (x : Arr k n) (y : Arr v n) : (dict x y).den = x.rel° ≫ y.rel :=
  mk_rel x y

/-- `!n = 𝟙(til n)`: `til_rel`'s right side, read through the key. -/
theorem til_den (n : Nat) : (til n).den = posL° ≫ (corefl (· < n) ≫ graph Int64.ofNat) := rfl

/-- `f x = x ≫ graph(f)` (§11.1 monadic): `mon_rel`'s right side, read through the key. -/
def mon {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) : Prog .long t := comp (arr x) (fn (.mono op f))

theorem mon_den {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) :
    (mon op f x).den = posL° ≫ (x.rel ≫ graph f) :=
  hom_ext fun _ _ => ⟨fun ⟨b, ⟨j, ea, hx⟩, eb⟩ => ⟨j, ea, b, hx, eb⟩, fun ⟨j, ea, b, hx, eb⟩ => ⟨b, ⟨j, ea, hx⟩, eb⟩⟩

/-- `x v y = ⟨x, y⟩ ≫ (v)` (§11.1 dyadic): `val_rel`'s right side, read through the key. -/
def val {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) (x : Arr t n)
    (y : Arr u n) : Prog .long rt := comp (pair (arr x) (arr y)) (fn (.dy v h))

/-- `⟨P, Q ≫ !a⟩ ≫ (v) = P (v a)`, `Q` defined wherever `P` is: the atom a section's operand, no pair. -/
theorem sect_pairR {K C : RelSet.{0}} {t u rt : QAtomicType} (P : K ⟶ Ob t) (Q : K ⟶ C) (v : Prim.Dyadic)
    (h : Eval.ewType v t u = some rt) (a : El u) (hd : ∀ k b, P k b → ∃ c, Q k c) :
    rpair P (Q ≫ Verb.cst a) ≫ ofExcept (fun p : El t × El u => elem v h p.1 p.2) = P ≫ (Fn.sect false v h a).den :=
  hom_ext fun k c => ⟨fun ⟨p, ⟨hp, _, _, ea⟩, e⟩ => by cases ea; exact ⟨p.1, hp, e⟩,
    fun ⟨b, hb, e⟩ => ⟨(b, a), ⟨hb, by obtain ⟨c', hc⟩ := hd k b hb; exact ⟨c', hc, rfl⟩⟩, e⟩⟩

/-- `⟨Q ≫ !a, P⟩ ≫ (v) = P (a v)`. -/
theorem sect_pairL {K C : RelSet.{0}} {t u rt : QAtomicType} (P : K ⟶ Ob t) (Q : K ⟶ C) (v : Prim.Dyadic)
    (h : Eval.ewType v u t = some rt) (a : El u) (hd : ∀ k b, P k b → ∃ c, Q k c) :
    rpair (Q ≫ Verb.cst a) P ≫ ofExcept (fun p : El u × El t => elem v h p.1 p.2) = P ≫ (Fn.sect true v h a).den :=
  hom_ext fun k c => ⟨fun ⟨p, ⟨⟨_, _, ea⟩, hp⟩, e⟩ => by cases ea; exact ⟨p.2, hp, e⟩,
    fun ⟨b, hb, e⟩ => ⟨(a, b), ⟨by obtain ⟨c', hc⟩ := hd k b hb; exact ⟨c', hc, rfl⟩, hb⟩, e⟩⟩

theorem val_den {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt)
    (x : Arr t n) (y : Arr u n) (hn : n ≤ 2 ^ 64) :
    (val v h x y).den = posL° ≫ (rpair x.rel y.rel ≫ ofExcept fun p => elem v h p.1 p.2) :=
  hom_ext fun k c => ⟨fun ⟨p, ⟨⟨j, ea, hx⟩, j', eb, hy⟩, e⟩ => by
      have hj := ((rel_iff x j _).1 hx).1; have hj' := ((rel_iff y j' _).1 hy).1
      obtain rfl := ofNat_inj (by omega) (by omega) (ea.symm.trans eb)
      exact ⟨j, ea, p, ⟨hx, hy⟩, e⟩,
    fun ⟨j, ea, p, ⟨hx, hy⟩, e⟩ => ⟨p, ⟨⟨j, ea, hx⟩, j, ea, hy⟩, e⟩⟩

/-! ## Verbs over `Λ`, `est`, `enum`, the fold (design §2, §7 line 3) -/

/-- `last by`: `Λ(k°) ≫ est(≥) ≫ v`, the last position of each key read through `v` (`lastBy_rel`). -/
def lastBy {K t : QAtomicType} {n : Nat} (k : Arr K n) (v : Arr t n) : Prog K t := comp (extr true (conv (arr k))) (arr v)

theorem lastBy_den {K t : QAtomicType} {n : Nat} (k : Arr K n) (v : Arr t n) :
    (lastBy k v).den = (Λ (posL° ≫ k.rel)° ≫ est (fun a b : Int64 => a ≥ b)) ≫ posL° ≫ v.rel := rfl

/-- A fold node over `op`'s kernel: its seed and step are the ones `op` computes, q's null skipped
    (`overBy_rel`), so no caller can pair a kernel with a fold it does not run. -/
def foldOp {A : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) (G : Prog A .long) : Prog A .long :=
  fold op (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) x G

/-- `foldOp`'s step is left-commutative at every `op` that skips `0N` (`boolCast = false`): `+ * & |` are
    commutative and associative. So the order a kernel lists a segment in does not change its fold. -/
theorem foldOp_comm {op : Kernel.Coc.Over} (hb : op.boolCast = false) (a b c : Int64) :
    Verb.skipNul op.step a (Verb.skipNul op.step b c) = Verb.skipNul op.step b (Verb.skipNul op.step a c) := by
  have lc : ∀ x y z : Int64, op.step x (op.step y z) = op.step y (op.step x z) := by
    intro x y z
    cases op <;> simp only [Kernel.Coc.Over.boolCast, Bool.true_eq_false] at hb <;> simp only [Kernel.Coc.Over.step]
    · rw [← Int64.add_assoc, Int64.add_comm x y, Int64.add_assoc]
    · rw [← Int64.mul_assoc, Int64.mul_comm x y, Int64.mul_assoc]
    all_goals
      repeat' split
      all_goals first | rfl | (apply Int64.toInt_inj.1; simp only [Int64.lt_iff_toInt_lt] at *; omega)
  unfold Verb.skipNul
  cases ha : (a == Spec.nul) <;> cases hb' : (b == Spec.nul) <;> simp only [ha, hb', Bool.false_eq_true, ↓reduceIte] <;>
    exact lc a b c

/-- `select f x by k`: `grpL(k) ≫ list(x) ≫ ⦇e,f⦈`, `grpL(k) = Λ(k°) ≫ enum` (`overBy_rel`). -/
def selectBy {K : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (k : Arr K n) (x : Arr .long n) : Prog K .long :=
  foldOp op x (conv (arr k))

theorem selectBy_den {K : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (k : Arr K n) (x : Arr .long n) :
    (selectBy op k x).den = Verb.dom ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Λ ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫
      Verb.fold (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) :=
  rfl

/-! ## posL bridge

  `den` keys a list by longs, `posL° ≫ S`; the `*_rel` laws key it by positions, `S`. Below `2^64` `posL` is a
  bijection, so the two say one thing, and each `<verb>_prog` reads a run back into its law's right side. -/

/-- **`T = posL° ≫ S` iff `T` read at the positions below `2^64` is `S`**, for `S` defined only there. The
    `corefl` is needed because `posL` wraps: past `2^64` it hits the same longs again. -/
theorem posL_iff {B : RelSet.{0}} {S : Idx ⟶ B} {T : Ob .long ⟶ B} (hS : ∀ i b, S i b → i < 2 ^ 64) :
    T = posL° ≫ S ↔ corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ T = S := by
  constructor
  · rintro rfl
    exact hom_ext fun i b => ⟨fun ⟨_, ⟨rfl, hi⟩, _, rfl, j, ej, hs⟩ => by
        obtain rfl := ofNat_inj hi (hS j b hs) ej; exact hs,
      fun hs => ⟨i, ⟨rfl, hS i b hs⟩, _, rfl, i, rfl, hs⟩⟩
  · rintro rfl
    exact hom_ext fun a b => ⟨fun ht => ⟨a.toBitVec.toNat, (Int64.toBitVec_inj.1 (by simp)).symm, _,
        ⟨rfl, a.toBitVec.isLt⟩, _, rfl, by rw [Int64.toBitVec_inj.1 (by simp : (Int64.ofNat a.toBitVec.toNat).toBitVec = a.toBitVec)]; exact ht⟩,
      fun ⟨_, ea, _, ⟨rfl, _⟩, _, rfl, ht⟩ => by rw [ea]; exact ht⟩

/-- A key `til n` exists only below `2^64`. -/
theorem tilKey_lt {n : Nat} {k : Arr .long n} (h : tilKey n = .ok k) : n < 2 ^ 64 := by
  unfold tilKey at h; split at h
  · exact Nat.lt_of_lt_of_le (by assumption) USize.size_le
  · cases h

/-- `ej` runs to `ej_rel`'s right side, its rows the one-key tuples. -/
theorem ej_prog {nl nr : Nat} (l : Arr .long nl) (r : Arr .long nr) {R : RelV .long .long}
    (h : (ej l r).run = .ok R) (hs : (ej l r).Sound) :
    (R.Holds : Ob .long ⟶ Ob .long) = posL° ≫ ix (l.toList.map ([·])) ≫ (ix (r.toList.map ([·])))° ≫ posL := by
  rw [run_sound _ hs h, ej_den, Verb.ix_map, Verb.ix_map]
  exact hom_ext fun _ _ => ⟨fun ⟨j, ea, c, hl, j', hr, eb⟩ => ⟨j, ea, [c], ⟨c, hl, rfl⟩, j', ⟨c, hr, rfl⟩, eb⟩,
    fun ⟨j, ea, _, ⟨c, hl, rfl⟩, j', ⟨_, hr, e⟩, eb⟩ => ⟨j, ea, c, hl, j', by cases e; exact hr, eb⟩⟩

/-- `x!y` runs to `mk_rel`'s right side. -/
theorem dict_prog {k v : QAtomicType} {n : Nat} (x : Arr k n) (y : Arr v n) {R : RelV k v}
    (h : (dict x y).run = .ok R) (hs : (dict x y).Sound) : (R.Holds : Ob k ⟶ Ob v) = x.rel° ≫ y.rel :=
  (run_sound _ hs h).trans (dict_den x y)

/-- `!n` runs to `til_rel`'s right side. -/
theorem til_prog {n : Nat} (hn : n ≤ 2 ^ 64) {R : RelV .long .long} (h : (til n).run = .ok R) (hs : (til n).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = corefl (· < n) ≫ graph Int64.ofNat :=
  (posL_iff fun _ _ ⟨_, ⟨e, hi⟩, _⟩ => by subst e; exact Nat.lt_of_lt_of_le hi hn).1 ((run_sound _ hs h).trans (til_den n))

/-- `f x` runs to `mon_rel`'s right side. -/
theorem mon_prog {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) (hn : n ≤ 2 ^ 64)
    {R : RelV .long t} (h : (mon op f x).run = .ok R) (hs : (mon op f x).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob t) = x.rel ≫ graph f :=
  (posL_iff fun i _ ⟨_, hx, _⟩ => Nat.lt_of_lt_of_le ((rel_iff x i _).1 hx).1 hn).1
    ((run_sound _ hs h).trans (mon_den op f x))

/-- `x v y` runs to `val_rel`'s right side. -/
theorem val_prog {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (e : Eval.ewType v t u = some rt)
    (x : Arr t n) (y : Arr u n) (hn : n ≤ 2 ^ 64) {R : RelV .long rt} (h : (val v e x y).run = .ok R)
    (hs : (val v e x y).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob rt) = rpair x.rel y.rel ≫ ofExcept fun p => elem v e p.1 p.2 :=
  (posL_iff fun i _ ⟨_, ⟨hx, _⟩, _⟩ => Nat.lt_of_lt_of_le ((rel_iff x i _).1 hx).1 hn).1
    ((run_sound _ hs h).trans (val_den v e x y hn))

/-- `&x` runs to `where_rel`'s right side, for every list `enum` gives. -/
theorem enum_prog {n : Nat} (x : Arr .boolean n) {R : RelV .long .long} (h : (enum x).run = .ok R)
    (hs : (enum x).Sound) {ys}
    (hy : Verb.enum (Verb.cset (Verb.dom (x.rel ≫ (Verb.cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = ix (CL.toList ys) ≫ graph Int64.ofNat := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  cases h
  rw [← (where_rel (x := x) hs).2 ys hy]
  exact (posL_iff fun i _ hi => Nat.lt_trans ((rel_iff _ i _).1 hi).1 (tilKey_lt (by assumption))).1
    (arr_sound (Find.where x).2 (by assumption))
/-! ## Verbs over `!e`, `dom`, `enumC`, `count` (design §2.2–2.5) -/

/-- `P ≫ (R ∪ (Q ≫ S))` is the union of its two branches as `run` composes them: `miss` and `χ` applied. -/
theorem comp_cup {A B C D : RelSet.{0}} (P : A ⟶ B) (R : B ⟶ D) (Q : B ⟶ C) (S : C ⟶ D) :
    (P ≫ R) ∪ ((P ≫ Q) ≫ S) = P ≫ (R ∪ (Q ≫ S)) :=
  hom_ext fun _ _ => ⟨fun h => Or.elim h (fun ⟨b, hp, hr⟩ => ⟨b, hp, Or.inl hr⟩)
      (fun ⟨c, ⟨b, hp, hq⟩, hs⟩ => ⟨b, hp, Or.inr ⟨c, hq, hs⟩⟩),
    fun ⟨b, hp, h⟩ => Or.elim h (fun hr => Or.inl ⟨b, hp, hr⟩) (fun ⟨c, hq, hs⟩ => Or.inr ⟨c, ⟨b, hp, hq⟩, hs⟩)⟩

/-- `x in y = x ≫ χ(ran y)`: the hit branch `x ≫ (ran y ≫ !1b)`, the miss branch the anti-join `≫ !0b`. -/
def «in» {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) : Prog .long .boolean :=
  union (comp (arr x) (comp (idU y) (fn (.cst true)))) (comp (anti (arr x) (idU y)) (fn (.cst false)))

theorem in_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) :
    («in» x y).den = (posL° ≫ x.rel) ≫ Verb.χ (Verb.ran y.rel) :=
  comp_cup _ _ _ _

/-- `x?y = y ≫ miss(Λ(x°) ≫ est(≤), n)`: the first position, `n` where `y` misses `x`. -/
def find {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) : Prog .long .long :=
  union (comp (arr y) (extr false (conv (arr x))))
    (comp (anti (arr y) (dom (extr false (conv (arr x))))) (fn (.cst (u := .long) (Int64.ofNat nx))))

theorem find_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) :
    (find x y).den = (posL° ≫ y.rel) ≫
      Verb.miss (Λ ((posL° ≫ x.rel)°) ≫ est (fun a b : Int64 => a ≤ b)) (Int64.ofNat nx) :=
  comp_cup _ _ _ _

/-- `x@y = y ≫ miss(pos ≫ x, e)`, `e` the null of `x`'s type. -/
def index {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) : Prog .long t :=
  union (comp (arr y) (arr x)) (comp (anti (arr y) (dom (arr x))) (fn (.cst e)))

theorem index_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) :
    (index x y e).den = (posL° ≫ y.rel) ≫ Verb.miss (posL° ≫ x.rel) e :=
  comp_cup _ _ _ _

/-- Below `2^63` a long names a position the same way through `posL°` and through `pos`. -/
theorem posL_pos {t : QAtomicType} {n : Nat} (x : Arr t n) (hn : n ≤ 2 ^ 63) :
    (posL° ≫ x.rel : Ob .long ⟶ Ob t) = Verb.pos ≫ x.rel :=
  hom_ext fun a b => ⟨fun ⟨j, ea, hx⟩ => by
      have hj := ((rel_iff x j b).1 hx).1
      have h0 : (0 : Int64) ≤ Int64.ofNat j := by
        rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega)]; simp
      have hv : (Int64.ofNat j).toInt.toNat = j := by
        rw [Int64.toNat_toInt, Int64.toNatClampNeg_ofNat_of_lt (by omega)]
      subst ea
      exact ⟨j, ⟨_, ⟨rfl, h0⟩, hv.symm⟩, hx⟩,
    fun ⟨j, ⟨w, ⟨ew, h0⟩, ej⟩, hx⟩ => by
      subst ew ej
      refine ⟨_, ?_, hx⟩
      apply Int64.toInt_inj.1
      have h1 := Int64.le_iff_toInt_le.1 h0
      have h2 := Int64.toInt_lt a
      simp at h1
      dsimp only
      rw [Int64.toInt_ofNat_of_lt (by omega)]; omega⟩

/-- `x@y` runs to `index_rel`'s right side (at `e = 0N` on longs). -/
theorem index_prog {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) (hx : nx ≤ 2 ^ 63)
    (hy : ny ≤ 2 ^ 64) {R : RelV .long t} (h : (index x y e).run = .ok R) (hs : (index x y e).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob t) = y.rel ≫ Verb.miss (Verb.pos ≫ x.rel) e :=
  (posL_iff fun i _ ⟨_, hy', _⟩ => Nat.lt_of_lt_of_le ((rel_iff y i _).1 hy').1 hy).1
    ((run_sound _ hs h).trans (by rw [index_den, posL_pos x hx]; exact Cat.assoc _ _ _))

/-- `?x = enum(ran(Λ(x°) ≫ est(≤))) ≫ x`: each value's first position, ascending, read through `x`. -/
def distinct {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long t :=
  comp (enumC n (dom (conv (extr false (conv (arr x)))))) (arr x)

theorem distinct_den {t : QAtomicType} {n : Nat} (x : Arr t n) :
    (distinct x).den = (posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (corefl (· < n) ≫ posL ≫
      Verb.ran (Λ ((posL° ≫ x.rel)°) ≫ est (fun a b : Int64 => a ≤ b))))) ys ∧
      (ix (CL.toList ys) ≫ graph Int64.ofNat) i v) ≫ posL° ≫ x.rel :=
  rfl

/-- `count by k = grpL(k) ≫ length`. -/
def countBy {K : QAtomicType} {n : Nat} (k : Arr K n) : Prog K .long := count (conv (arr k))

/-- A cons-list's length is the right fold that counts its conses. -/
theorem clen_foldr {A : Type} : ∀ ys : CL.ConsList Unit A, ListRel.clen ys = (CL.toList ys).foldr (fun _ c => c + 1) 0
  | .wrap () => rfl
  | .cons a ys => by
    rw [show CL.toList (.cons a ys) = a :: CL.toList ys from rfl, List.foldr_cons, ← clen_foldr ys]; rfl

/-- `length = ⦇0, succ⦈`. -/
theorem length_cata {A : Type} : (ListRel.length : ListRel.dList A ⟶ (⟨Nat⟩ : RelSet.{0})) =
    ⦇(junc (sumCop (CL.dL Unit) ⟨A × Nat⟩) (graph fun _ => (0 : Nat)) (graph fun q : A × Nat => q.2 + 1)
      : Alg (CL.F Unit A) (⟨Nat⟩ : RelSet.{0}))⦈ := by
  exact (congrArg graph (funext clen_foldr)).trans (Verb.foldr_cata (fun _ c => c + 1) 0)

theorem countBy_den {K : QAtomicType} {n : Nat} (k : Arr K n) :
    (countBy k).den = Verb.dom ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Λ ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Verb.enum ≫
      ⦇(junc (sumCop (CL.dL Unit) ⟨Nat × Nat⟩) (graph fun _ => (0 : Nat)) (graph fun q : Nat × Nat => q.2 + 1)
        : Alg (CL.F Unit Nat) (⟨Nat⟩ : RelSet.{0}))⦈ ≫ graph Int64.ofNat := by
  rw [← length_cata]; rfl

/-- A list's rows as one group: the key `0` against every position, `(P ≫ !0)°`. -/
def whole {t : QAtomicType} (P : Prog .long t) : Prog .long .long := conv (comp P (fn (.cst (u := .long) (0 : Int64))))

/-- `#x = ⦇0, succ⦈`, at the one key `0`. -/
def size {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long .long := count (whole (arr x))

theorem size_den {t : QAtomicType} {n : Nat} (x : Arr t n) :
    (size x).den = Verb.dom (((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos) ≫ Λ (((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos) ≫ Verb.enum ≫
      ⦇(junc (sumCop (CL.dL Unit) ⟨Nat × Nat⟩) (graph fun _ => (0 : Nat)) (graph fun q : Nat × Nat => q.2 + 1)
        : Alg (CL.F Unit Nat) (⟨Nat⟩ : RelSet.{0}))⦈ ≫ graph Int64.ofNat := by
  rw [← length_cata]; rfl

/-- `f/x = ⦇e, f⦈` of the list, at the one key `0`, `e` and `f` the kernel's (`foldOp`). -/
def over {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) : Prog .long .long := foldOp op x (whole (arr x))

theorem over_den {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) :
    (over op x).den = Verb.dom (((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos) ≫ Λ ((((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos)) ≫
      Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) :=
  rfl

/-- `x` with its nulls dropped: `x (≠0N)?`. -/
def nonNul {n : Nat} (x : Arr .long n) : Prog .long .long :=
  comp (arr x) (fn (.test (.sect (u := .long) false .ne rfl Spec.nul)))

/-- `⟨⦇0,+⦈, ⦇0,succ⦈⟩ ≫ (÷)`, one key `0`, nulls skipped by both: the sum by `skipNul`, the count over
    `nonNul x`. No row where nothing counts: `count` has none there. -/
def avgDiv {n : Nat} (x : Arr .long n) : Prog .long .float := comp (pair (over .add x) (count (whole (nonNul x)))) (fn (.dy .div rfl))

/-- `avg x = !1 ≫ miss(avgDiv x, 0n)`: the key `0` always, `0n` where no element counts, as q answers. -/
def avg {n : Nat} (x : Arr .long n) : Prog .long .float :=
  union (comp (til 1) (avgDiv x)) (comp (anti (til 1) (dom (avgDiv x))) (fn (.cst QLean.nanBits)))

theorem avg_den {n : Nat} (x : Arr .long n) :
    (avg x).den = (til 1).den ≫ Verb.miss (avgDiv x).den QLean.nanBits :=
  comp_cup _ _ _ _

/-- Int64's `compare` read as its three orders. -/
theorem compare_iff (x a : Int64) : (compare x a = .lt ↔ x < a) ∧ (compare x a = .eq ↔ x = a) ∧ (compare x a = .gt ↔ a < x) := by
  have e : x = a ↔ x.toInt = a.toInt := Int64.toInt_inj.symm
  rw [Ew.compare_toInt, Int64.lt_iff_toInt_lt, Int64.lt_iff_toInt_lt, e]
  exact ⟨Int.compare_eq_lt, Int.compare_eq_eq, Int.compare_eq_gt⟩

theorem signed_i64 (x : Int64) : Kernel.Ew.signed Kernel.Ew.i64 x.toUInt64 = x := by
  simp (config := { decide := true }) [Kernel.Ew.signed]

/-- A comparison's `elem` on longs is `true` exactly where the order `ord v` holds, for the four orders. -/
theorem elem_ord {v : Prim.Dyadic} (hv : v = .lt ∨ v = .le ∨ v = .gt ∨ v = .ge) (h : Eval.ewType v .long .long = some .boolean)
    (x a : Int64) : elem v h x a = .ok true ↔ ord v x a := by
  obtain ⟨hl, he, hg⟩ := compare_iff x a
  rcases hv with rfl | rfl | rfl | rfl <;> rw [Ew.elem_long_cmp rfl h, Except.ok.injEq] <;>
    simp (config := { decide := true }) only [Kernel.Ew.cmpStep, signed_i64, ord, if_true, if_false, beq_iff_eq, bne_iff_ne,
      ne_eq, reduceCtorEq, Bool.false_eq_true]
  all_goals cases hc : compare x a <;> simp only [reduceCtorEq, not_true_eq_false, not_false_eq_true, true_iff, false_iff]
  all_goals first | exact hl.1 hc | exact he.1 hc | exact hg.1 hc | skip
  all_goals (simp only [hc, reduceCtorEq, false_iff, true_iff] at hl he hg
             simp only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] at *; omega)

/-- `≠` on longs: its `elem` is `true` exactly off `a`. -/
theorem elem_ne (h : Eval.ewType .ne .long .long = some .boolean) (x a : Int64) : elem .ne h x a = .ok true ↔ x ≠ a := by
  rw [Ew.elem_long_cmp rfl h, Except.ok.injEq]
  simp (config := { decide := true }) only [Kernel.Ew.cmpStep, signed_i64, bne_iff_ne, ne_eq, if_true, if_false]
  exact not_congr (compare_iff x a).2.1

/-- `nonNul x` holds `x` where it is not `0N`. -/
theorem nonNul_den {n : Nat} (x : Arr .long n) :
    (nonNul x).den = posL° ≫ x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul) := by
  have e := congrArg (corefl (A := Ob .long)) (funext fun c => propext (elem_ne rfl c Spec.nul))
  exact (congrArg (_ ≫ ·) e).trans (Cat.assoc _ _ _)

/-! ## Key value and group number

  The programs key a group by its key value `a`; the kernel laws (`lastBy_rel`, `overBy_rel`) key it by its
  group number `j`, under the offsets `o`. A grouping of `k` is `keys : til g → K` with `k i = keys j` exactly
  when `i` lies in group `j`, `keys` one-to-one; through it the two say one thing: `den = keys° ≫ law`. -/

/-- `pos` reads a long below `2^63` back as the position it came from. -/
theorem pos_ofNat {j : Nat} (hj : j < 2 ^ 63) (i : Nat) : Verb.pos (Int64.ofNat j) i ↔ i = j := by
  have h0 : (0 : Int64) ≤ Int64.ofNat j := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega)]; simp
  have hv : (Int64.ofNat j).toInt.toNat = j := by
    rw [Int64.toNat_toInt, Int64.toNatClampNeg_ofNat_of_lt (by omega)]
  exact ⟨fun ⟨_, ⟨e, _⟩, hi⟩ => by subst e; rw [hi]; exact hv, fun hi => ⟨_, ⟨rfl, h0⟩, hi.trans hv.symm⟩⟩

/-- Below `2^63` `ofNat` keeps the order. -/
theorem ofNat_le {z i : Nat} (hz : z < 2 ^ 63) (hi : i < 2 ^ 63) : Int64.ofNat z ≤ Int64.ofNat i ↔ z ≤ i := by
  rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)]; omega

/-- `Λ(G) ≫ est(R) ≫ T` pointwise: the `R`-greatest of `G`'s image, read through `T`. -/
theorem lamEst_iff {A B C : RelSet.{0}} (G : A ⟶ B) (R : B ⟶ B) (T : B ⟶ C) (a : A.carrier) (c : C.carrier) :
    ((Λ G ≫ est R) ≫ T) a c ↔ ∃ w, (G a w ∧ ∀ z, G a z → R w z) ∧ T w c := by
  rw [Λ_eq_classifier]
  exact ⟨fun ⟨w, ⟨_, rfl, h⟩, ht⟩ => ⟨w, h, ht⟩, fun ⟨w, h, ht⟩ => ⟨w, ⟨_, rfl, h⟩, ht⟩⟩

/-- `Λ` on what occurs, `dom X ≫ Λ X`, is `M ≫ Λ Y` when `X = M ≫ Y`, `M` simple and every `Y` image
    nonempty: a key's set of positions is its group's. -/
theorem lam_key {K : RelSet.{0}} (X : K ⟶ Idx) (M : K ⟶ Idx) (Y : Idx ⟶ Idx)
    (hM : ∀ a j j', M a j → M a j' → j = j') (hY : ∀ a j, M a j → ∃ i, Y j i)
    (hX : ∀ a i, X a i ↔ ∃ j, M a j ∧ Y j i) : (Verb.dom X ≫ Λ X : K ⟶ _) = M ≫ Λ Y := by
  rw [Λ_eq_classifier, Λ_eq_classifier]
  refine hom_ext fun a S => ⟨fun ⟨_, ⟨e, i, hi, _⟩, hS⟩ => ?_, fun ⟨j, hm, hS⟩ => ?_⟩
  · subst e
    obtain ⟨j, hm, -⟩ := (hX a i).1 hi
    have h : (fun i' => X a i') = fun i' => Y j i' := funext fun i' => propext ⟨fun h => by
      obtain ⟨j', hm', hy⟩ := (hX a i').1 h; rwa [hM a j j' hm hm'], fun h => (hX a i').2 ⟨j, hm, h⟩⟩
    exact ⟨j, hm, hS.trans h⟩
  · obtain ⟨i, hi⟩ := hY a j hm
    have hx := (hX a i).2 ⟨j, hm, hi⟩
    have h : (fun i' => X a i') = fun i' => Y j i' := funext fun i' => propext ⟨fun h => by
      obtain ⟨j', hm', hy⟩ := (hX a i').1 h; rwa [hM a j j' hm hm'], fun h => (hX a i').2 ⟨j, hm, h⟩⟩
    exact ⟨a, ⟨rfl, i, hx, hx⟩, hS.trans h.symm⟩

/-- **`last by` keys by value what `lastBy_rel` keys by group**: through a grouping `keys` of `k`. -/
theorem lastBy_grp {K t : QAtomicType} {n g : Nat} (k : Arr K n) (v : Arr t n) (keys : Arr K g)
    (o : Arr .long (g+1)) (hn : n ≤ 2 ^ 63) (hinj : ∀ j j' a, keys.rel j a → keys.rel j' a → j = j')
    (hk : ∀ a i, k.rel i a ↔ ∃ j, keys.rel j a ∧ Verb.grp o i j) :
    (lastBy k v).den = keys.rel° ≫ ((Λ ((Verb.grp o)°) ≫ est (fun a b : Nat => a ≥ b)) ≫ v.rel) := by
  refine hom_ext fun a c => (lamEst_iff _ _ _ a c).trans ⟨fun ⟨w, ⟨⟨i', ea', hk'⟩, hmax⟩, i, ea, hv⟩ => ?_,
    fun ⟨j, hkey, hr⟩ => ?_⟩
  · have hi' := ((rel_iff k i' a).1 hk').1
    have hi := ((rel_iff v i c).1 hv).1
    subst ea
    obtain rfl := ofNat_inj (by omega) (by omega) ea'
    obtain ⟨j, hkey, hg⟩ := (hk a i).1 hk'
    refine ⟨j, hkey, (lamEst_iff _ _ _ j c).2 ⟨i, ⟨hg, fun z hz => ?_⟩, hv⟩⟩
    have hkz := (hk a z).2 ⟨j, hkey, hz⟩
    have hz' := ((rel_iff k z a).1 hkz).1
    exact (ofNat_le (by omega) (by omega)).1 (hmax _ ⟨z, rfl, hkz⟩)
  · obtain ⟨i, ⟨hg, hmax⟩, hv⟩ := (lamEst_iff _ _ _ j c).1 hr
    have hki := (hk a i).2 ⟨j, hkey, hg⟩
    have hi := ((rel_iff k i a).1 hki).1
    refine ⟨Int64.ofNat i, ⟨⟨i, rfl, hki⟩, fun z hz => ?_⟩, i, rfl, hv⟩
    obtain ⟨i', ez, hkz⟩ := hz
    subst ez
    have hz' := ((rel_iff k i' a).1 hkz).1
    obtain ⟨j', hkey', hg'⟩ := (hk a i').1 hkz
    obtain rfl := hinj j j' a hkey hkey'
    exact (ofNat_le (by omega) (by omega)).2 (hmax i' hg')

/-- **`select f x by k` keys by value what `overBy_rel` keys by group**: through a grouping `keys` of `k`
    in which every key occurs. -/
theorem selectBy_grp {K : QAtomicType} {n g : Nat} (op : Kernel.Coc.Over) (k : Arr K n) (x : Arr .long n)
    (keys : Arr K g) (o : Arr .long (g+1)) (hn : n ≤ 2 ^ 63) (hinj : ∀ j j' a, keys.rel j a → keys.rel j' a → j = j')
    (hocc : ∀ j a, keys.rel j a → ∃ i, k.rel i a) (hk : ∀ a i, k.rel i a ↔ ∃ j, keys.rel j a ∧ Verb.grp o i j) :
    (selectBy op k x).den = keys.rel° ≫ Λ ((Verb.grp o)°) ≫ Verb.enum ≫ ListRel.list x.rel ≫
      Verb.fold (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) := by
  have hX : ∀ a i, ((posL° ≫ k.rel)° ≫ Verb.pos : Ob K ⟶ Idx) a i ↔ ∃ j, keys.rel° a j ∧ (Verb.grp o)° j i :=
    fun a i => ⟨fun ⟨l, ⟨i', el, hk'⟩, hp⟩ => by
        have hi' := ((rel_iff k i' a).1 hk').1
        subst el
        obtain rfl := (pos_ofNat (by omega) i).1 hp
        exact (hk a i).1 hk',
      fun h => by
        have hki := (hk a i).2 h
        have hi := ((rel_iff k i a).1 hki).1
        exact ⟨_, ⟨i, rfl, hki⟩, (pos_ofNat (by omega) i).2 rfl⟩⟩
  rw [selectBy_den, ← Cat.assoc, lam_key _ _ _ (fun a j j' h h' => hinj j j' a h h') (fun a j hkey => by
    obtain ⟨i, hki⟩ := hocc j a hkey
    obtain ⟨j', hkey', hg⟩ := (hk a i).1 hki
    exact ⟨i, by rw [hinj j j' a hkey hkey']; exact hg⟩) hX, Cat.assoc]
  rfl

/-- **`miss` is inert on the groups a key names**: read through `keys°`, `corefl(<g) ≫ miss(M, e)` is `M`
    when `M` is defined at every group some key names. -/
theorem keys_miss {K : QAtomicType} {g : Nat} {B : RelSet.{0}} (keys : Arr K g) (M : Idx ⟶ B) (e : B.carrier)
    (h : ∀ j a, keys.rel j a → ∃ c, M j c) :
    (keys.rel° ≫ corefl (· < g) ≫ Verb.miss M e : Ob K ⟶ B) = keys.rel° ≫ M :=
  hom_ext fun a c => ⟨fun ⟨j, hkey, _, ⟨rfl, _⟩, hm⟩ => ⟨j, hkey, ((Verb.miss_iff M e j c).1 hm).elim id
      fun ⟨hn, _⟩ => absurd (h j a hkey) hn⟩,
    fun ⟨j, hkey, hm⟩ => ⟨j, hkey, j, ⟨rfl, ((rel_iff keys j a).1 hkey).1⟩, (Verb.miss_iff M e j c).2 (.inl hm)⟩⟩

/-- A group `j < g` that holds a row has a last row, read through `x`: `Λ(grp o)° ≫ est(≥) ≫ x` is
    defined at `j`. -/
theorem lastEst_some {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) {t : QAtomicType} (x : Arr t n) {i j : Nat}
    (hj : j < g) (hi : Verb.grp o i j) :
    ∃ c, (Λ ((Verb.grp o)°) ≫ est (fun a b : Nat => a ≥ b) ≫ x.rel : Idx ⟶ Ob t) j c := by
  obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
  have ca := Ops.toNat_cast a0
  have cb := Ops.toNat_cast (Int.le_trans a0 a1)
  have T : ∀ z : Nat, Verb.grp o z j ↔ (o.toList[j]!).toNatClampNeg ≤ z ∧ z < (o.toList[j+1]!).toNatClampNeg :=
    fun z => eq_comm.trans (Verb.group_iff co hj z)
  have hi' := (T i).1 hi
  have hw : (o.toList[j+1]!).toNatClampNeg - 1 < n := by omega
  rw [← Cat.assoc]
  exact ⟨x.get ⟨_, hw⟩, (lamEst_iff _ _ _ j _).2 ⟨_, ⟨(T _).2 ⟨by omega, by omega⟩,
    fun z hz => Nat.le_sub_one_of_lt ((T z).1 hz).2⟩, (rel_iff x _ _).2 ⟨hw, rfl⟩⟩⟩

/-- **`last by` against `lastBy_rel`**: through a grouping `keys` of `k` in which every key occurs, the
    program is the kernel's answer on the cuts `o`, read by key value; `lastBy_rel`'s `miss` is inert there
    (`keys_miss`). -/
theorem lastBy_link {K : QAtomicType} {n g : Nat} (k : Arr K n) (v : Arr .long n) (keys : Arr K g)
    {o : Arr .long (g+1)} {co : Cuts o n} {wo wv : List UInt64} (ho : longWords (g+1) o.enc = some wo)
    (hv : longWords n v.enc = some wv) (hg : g + 1 < USize.size) (hU : n < USize.size) (hn : n ≤ 2 ^ 63)
    (hinj : ∀ j j' a, keys.rel j a → keys.rel j' a → j = j') (hocc : ∀ j a, keys.rel j a → ∃ i, k.rel i a)
    (hk : ∀ a i, k.rel i a ↔ ∃ j, keys.rel j a ∧ Verb.grp o i j) {S : Arr .long g}
    (h : Ops.lastBy ⟨g, n, o, co, v⟩ = some S) : (lastBy k v).den = keys.rel° ≫ S.rel := by
  have hne : ∀ j a, keys.rel j a → ∃ c, (Λ ((Verb.grp o)°) ≫ est (fun a b : Nat => a ≥ b) ≫ v.rel : Idx ⟶ Ob .long) j c :=
    fun j a hkey => by
      obtain ⟨i, hki⟩ := hocc j a hkey
      obtain ⟨j', hkey', hg'⟩ := (hk a i).1 hki
      obtain rfl := hinj j j' a hkey hkey'
      exact lastEst_some co v ((rel_iff keys j a).1 hkey).1 hg'
  rw [lastBy_grp k v keys o hn hinj hk, Verb.lastBy_rel ho hv hg hU h]
  exact (congrArg (keys.rel° ≫ ·) (Cat.assoc _ _ _)).trans (keys_miss keys _ _ hne).symm

/-- **`select f x by k` against `overBy_rel`**: through a grouping `keys` of `k` in which every key occurs,
    the program is the kernel's answer on the cuts `o`, read by key value. -/
theorem selectBy_link {K : QAtomicType} {n g : Nat} {op : Kernel.Coc.Over} (hb : op.boolCast = false)
    (hA : ∀ a b c, op.step (op.step a b) c = op.step a (op.step b c))
    (hl : ∀ a, op.step (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) a = a)
    (hr : ∀ a, op.step a (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) = a)
    (k : Arr K n) (x : Arr .long n) (keys : Arr K g) {o : Arr .long (g+1)} {co : Cuts o n} {b ob : ByteArray}
    (hg : g < USize.size) (h63 : g < 2 ^ 63) (hc : x.enc = .bytes b) (ho : o.enc = .bytes ob) (hn : n ≤ 2 ^ 63)
    (hinj : ∀ j j' a, keys.rel j a → keys.rel j' a → j = j') (hocc : ∀ j a, keys.rel j a → ∃ i, k.rel i a)
    (hk : ∀ a i, k.rel i a ↔ ∃ j, keys.rel j a ∧ Verb.grp o i j) {S : Arr .long g}
    (h : Ops.overBy op ⟨g, n, o, co, x⟩ = some ⟨.long, S⟩) : (selectBy op k x).den = keys.rel° ≫ S.rel := by
  rw [selectBy_grp op k x keys o hn hinj hocc hk, Verb.overBy_rel hb hA hl hr hg h63 hc ho h]
  exact hom_ext fun a c => ⟨fun ⟨j, hkey, m, hΛ, ys, he, ht⟩ =>
      ⟨j, hkey, j, ⟨rfl, ((rel_iff keys j a).1 hkey).1⟩, ys, ⟨m, hΛ, he⟩, ht⟩,
    fun ⟨j, hkey, _, ⟨rfl, _⟩, ys, ⟨m, hΛ, he⟩, ht⟩ => ⟨j, hkey, m, hΛ, ys, he, ht⟩⟩

/-! ## Verbs over `grade` (design P17, §7 line 4) -/

/-- `<x = grade(⊴ₓ)`, `lt` the strict order of `x`'s type. -/
def iasc {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) : Prog .long .long := grade false lt x

theorem iasc_den {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) :
    (iasc lt x).den = posL° ≫ fun i v => ∃ G, Verb.sort (Verb.stable x.rel lt) (CL.ofList (List.range n)) G ∧
      (ix (CL.toList G) ≫ graph Int64.ofNat) i v := rfl

/-- `>x = grade(⊵ₓ)`, `⊵ₓ` the stable order at the flipped `lt`. -/
def idesc {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) : Prog .long .long := grade true lt x

theorem idesc_den {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) :
    (idesc lt x).den = posL° ≫ fun i v => ∃ G, Verb.sort (Verb.stable x.rel (flip lt)) (CL.ofList (List.range n)) G ∧
      (ix (CL.toList G) ≫ graph Int64.ofNat) i v := rfl

/-- `rank x = (<x)°`: each position's place in the ascending grade. -/
def rank {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) : Prog .long .long := conv (iasc lt x)

theorem rank_den {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) :
    (rank lt x).den = (iasc lt x).den° := rfl

/-- `x` read in the grade of `s`: `grade(⊴ₛ) ≫ x` (R19), the one shape of `asc`, `desc`, `xasc`. -/
def xsort {t u : QAtomicType} {n : Nat} (d : Bool) (lt : El t → El t → Prop) (s : Arr t n) (x : Arr u n) :
    Prog .long u := comp (grade d lt s) (arr x)

/-- `asc x = (<x) ≫ x`. -/
def asc {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) : Prog .long t := xsort false lt x x

theorem asc_den {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) :
    (asc lt x).den = (iasc lt x).den ≫ posL° ≫ x.rel := rfl

/-- `desc x = (>x) ≫ x`. -/
def desc {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) : Prog .long t := xsort true lt x x

theorem desc_den {t : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (x : Arr t n) :
    (desc lt x).den = (idesc lt x).den ≫ posL° ≫ x.rel := rfl

/-- `s xasc x = (<s) ≫ x`: one more column read in the ascending grade of the sort column. -/
def xasc {t u : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (s : Arr t n) (x : Arr u n) : Prog .long u :=
  xsort false lt s x

theorem xasc_den {t u : QAtomicType} {n : Nat} (lt : El t → El t → Prop) (s : Arr t n) (x : Arr u n) :
    (xasc lt s x).den = (iasc lt s).den ≫ posL° ≫ x.rel := rfl

/-! ### `grade` on a long column: the kernel law from `iasc_rel`/`idesc_rel`, and the runs read back -/

/-- A run of `comp P Q` ran `P`, unless `P` is a coreflexive, which `Q`'s run is filtered by. -/
theorem comp_run {A B C : QAtomicType} {P : Prog A B} {Q : Prog B C} {R : RelV A C} (hp : P.asTest = none)
    (h : (comp P Q).run = .ok R) : ∃ R₁, P.run = .ok R₁ := by
  simp only [run, bind, Except.bind] at h; rw [hp] at h; simp only at h; split at h
  · cases h
  · exact ⟨_, by assumption⟩

/-- A list of longs that is `M` read through `ofNat` holds `ix(M) ≫ ofNat`. -/
theorem rel_ofList {n : Nat} {S : Arr .long n} {M : List Nat} (hS : S.toList = M.map Int64.ofNat) :
    (S.rel : Idx ⟶ Ob .long) = ix M ≫ graph Int64.ofNat :=
  hom_ext fun i v => by
    show S.toList[i]? = some v ↔ ∃ j, M[i]? = some j ∧ v = Int64.ofNat j
    rw [hS, List.getElem?_map]
    cases M[i]? with
    | none => simp
    | some j =>
      simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun e => ⟨j, rfl, e.symm⟩, fun ⟨_, e, e'⟩ => by cases e; exact e'.symm⟩

/-- When `sort(P)` of `til n` is the one list `M`, `grade`'s spec is `M` read as longs. -/
theorem sort_spec {n : Nat} {P : Nat → Nat → Prop} {M : List Nat}
    (hc : (Verb.cst (CL.ofList M) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
      = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort P) :
    (fun (i : Nat) (v : Int64) => ∃ G, Verb.sort P (CL.ofList (List.range n)) G ∧
      (ix (CL.toList G) ≫ graph Int64.ofNat) i v : Idx ⟶ Ob .long) = ix M ≫ graph Int64.ofNat := by
  have key : ∀ G, Verb.sort P (CL.ofList (List.range n)) G ↔ G = CL.ofList M := fun G => by
    have e : (G = CL.ofList M) ↔ ∃ m, m = CL.ofList (List.range n) ∧ Verb.sort P m G :=
      Iff.of_eq (congrArg (fun r => r () G) hc)
    exact ⟨fun h => e.2 ⟨_, rfl, h⟩, fun h => by obtain ⟨_, rfl, h'⟩ := e.1 h; exact h'⟩
  exact hom_ext fun i v => ⟨fun ⟨G, hG, hv⟩ => by obtain rfl := (key G).1 hG; rwa [CL.toList_ofList] at hv,
    fun hv => ⟨_, (key _).2 rfl, by rwa [CL.toList_ofList]⟩⟩

/-- **The long grade kernel's answer** is `M` read as longs, `M` the one list `sort(⊴ₓ)` (`⊵ₓ`) gives of
    `til n` (`iasc_rel`, `idesc_rel`), its entries below `n`. -/
theorem grade_long {n : Nat} {d : Bool} {x S : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws)
    (hn : n < USize.size) (h63 : n < 2 ^ 63) (h : Ops.grade d x = S) :
    ∃ M : List Nat, (Verb.cst (CL.ofList M) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable x.rel
          (if d then flip (fun a b : Int64 => a < b) else fun a b : Int64 => a < b))
      ∧ S.toList = M.map Int64.ofNat ∧ M.length = n ∧ ∀ j ∈ M, j < n := by
  have hl : x.toList.length < 2 ^ 63 := by rw [Arr.length_toList]; exact h63
  refine ⟨(List.range x.toList.length).mergeSort fun i j =>
      if d then decide (x.toList[j]! ≤ x.toList[i]!) else decide (x.toList[i]! ≤ x.toList[j]!), ?_,
    by rw [← h, Ops.grade_toList hx hn]; rfl, by rw [List.length_mergeSort, List.length_range, Arr.length_toList],
    fun j hj => ?_⟩
  · rw [← Verb.grade_map d _ hl, ← Ops.grade_toList (desc := d) hx hn, h]
    cases d
    · exact Verb.iasc_rel hx hn h63 h
    · exact Verb.idesc_rel hx hn h63 h
  · have := List.mem_range.1 ((List.mergeSort_perm _ _).subset hj); rwa [Arr.length_toList] at this

/-- `grade`'s kernel law holds on a dense long column: `Sound` of `<x`/`>x` is a theorem there. -/
theorem grade_sound_long {n : Nat} (d : Bool) {x : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws)
    (hn : n < USize.size) (h63 : n < 2 ^ 63) : (grade d (fun a b : Int64 => a < b) x).Sound := by
  unfold Sound; intro S h
  obtain ⟨M, hc, hS, -, -⟩ := grade_long hx hn h63 h
  exact congrArg (posL° ≫ ·) ((rel_ofList hS).trans (sort_spec hc).symm)

/-- `<x`/`>x` run to `iasc_rel`/`idesc_rel`'s right side: `G` the list `sort(⊴ₓ)` gives, read as longs. -/
theorem grade_prog {n : Nat} (d : Bool) {x : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws)
    (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : RelV .long .long}
    (h : (grade d (fun a b : Int64 => a < b) x).run = .ok R) :
    ∃ G : List Nat, (Verb.cst (CL.ofList G) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable x.rel
          (if d then flip (fun a b : Int64 => a < b) else fun a b : Int64 => a < b))
      ∧ corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = ix G ≫ graph Int64.ofNat := by
  obtain ⟨S, k, hg, hk, rfl⟩ := grade_run h
  obtain ⟨M, hc, hS, hl, -⟩ := grade_long hx hn h63 hg
  have h64 := USize.size_le
  have hb : ∀ i j, M[i]? = some j → i < 2 ^ 64 := fun i j hj => by
    have := (List.getElem?_eq_some_iff.1 hj).1; omega
  exact ⟨M, hc, (posL_iff fun i _ ⟨j, hj, _⟩ => hb i j hj).1
    ((arr_sound S hk).trans (congrArg (posL° ≫ ·) (rel_ofList hS)))⟩

/-- `asc`, `desc`, `xasc` run to `xasc_rel`'s right side: `x` read at the list `sort(⊴ₛ)` gives. -/
theorem xsort_prog {u : QAtomicType} {n : Nat} (d : Bool) {s : Arr .long n} {x : Arr u n} {ws : List UInt64}
    (hs : longWords n s.enc = some ws) (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : RelV .long u}
    (h : (xsort d (fun a b : Int64 => a < b) s x).run = .ok R) (hS : (xsort d (fun a b : Int64 => a < b) s x).Sound) :
    ∃ G : List Nat, (Verb.cst (CL.ofList G) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable s.rel
          (if d then flip (fun a b : Int64 => a < b) else fun a b : Int64 => a < b))
      ∧ corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob u) = ix G ≫ x.rel := by
  obtain ⟨_, h1⟩ := comp_run rfl h
  obtain ⟨S, _, hg, -, -⟩ := grade_run h1
  obtain ⟨M, hc, -, hl, hM⟩ := grade_long hs hn h63 hg
  have h64 := USize.size_le
  have hb : ∀ i j, M[i]? = some j → i < 2 ^ 64 := fun i j hj => by
    have := (List.getElem?_eq_some_iff.1 hj).1; omega
  refine ⟨M, hc, (posL_iff fun i _ ⟨j, hj, _⟩ => hb i j hj).1 ((run_sound _ hS h).trans ?_)⟩
  · show (grade d (fun a b : Int64 => a < b) s).den ≫ posL° ≫ x.rel = _
    rw [show (grade d (fun a b : Int64 => a < b) s).den = posL° ≫ (ix M ≫ graph Int64.ofNat) from
      congrArg (posL° ≫ ·) (sort_spec hc)]
    exact hom_ext fun a c => ⟨fun ⟨b, ⟨i, ea, j, hj, eb⟩, j', eb', hx⟩ => by
        have hj' := ((rel_iff x j' c).1 hx).1
        have hjn := hM j (List.mem_of_getElem? (hj : M[i]? = some j))
        obtain rfl := ofNat_inj (by omega) (by omega) (eb.symm.trans eb')
        exact ⟨i, ea, j, hj, hx⟩,
      fun ⟨i, ea, j, hj, hx⟩ => ⟨_, ⟨i, ea, j, hj, rfl⟩, j, rfl, hx⟩⟩
/-! ## The order join and R6–R8 (design §5, §7 line 4)

  A verb's term joins its lists by `ojoin`, keyed by longs; its rule's right side (`binJ`, `ajJ`, `wjJ`) states
  the same relation on positions read through `posL`. Below `2^63` `posL` is injective and order-preserving, so
  `posL° ≫ — ≫ posL` commutes with `∩`, `∪` and `Λ(—) ≫ est(≥)`: each rule is those three steps. -/

/-- A position relation below `2^63` on both sides, where `posL` keeps the order. -/
def Bd (W : Idx ⟶ Idx) : Prop := ∀ i j, W i j → i < 2 ^ 63 ∧ j < 2 ^ 63

theorem lt64 {i : Nat} (h : i < 2 ^ 63) : i < 2 ^ 64 := Nat.lt_trans h (by decide)

theorem arr_lt {t : QAtomicType} {n : Nat} (x : Arr t n) (hn : n ≤ 2 ^ 63) : ∀ i v, x.rel i v → i < 2 ^ 63 :=
  fun i v h => Nat.lt_of_lt_of_le ((rel_iff x i v).1 h).1 hn

theorem bd_comp {B : RelSet.{0}} {X Y : Idx ⟶ B} (hX : ∀ i v, X i v → i < 2 ^ 63) (hY : ∀ j v, Y j v → j < 2 ^ 63) :
    Bd (X ≫ Y°) := fun _ _ ⟨_, hx, hy⟩ => ⟨hX _ _ hx, hY _ _ hy⟩

theorem bd_join {B C : RelSet.{0}} {X : Idx ⟶ B} {Y : Idx ⟶ C} (o : B ⟶ C) (hX : ∀ i v, X i v → i < 2 ^ 63)
    (hY : ∀ j v, Y j v → j < 2 ^ 63) : Bd (X ≫ o ≫ Y°) := fun _ _ ⟨_, hx, _, _, hy⟩ => ⟨hX _ _ hx, hY _ _ hy⟩

theorem bd_est {W : Idx ⟶ Idx} (R : Idx ⟶ Idx) (hW : Bd W) : Bd (Λ W ≫ est R) :=
  fun i j h => hW i j ((RelSet.Λ_comp_est_apply _ _ _ _).1 h).1

/-- A join of two lists keyed by longs is the join of the lists read through `posL`. -/
theorem join_lift {B C : RelSet.{0}} (X : Idx ⟶ B) (o : B ⟶ C) (Y : Idx ⟶ C) :
    (posL° ≫ X) ≫ o ≫ (posL° ≫ Y)° = posL° ≫ (X ≫ o ≫ Y°) ≫ posL :=
  hom_ext fun _ _ => ⟨fun ⟨v, ⟨i, ea, hx⟩, w, ho, j, eb, hy⟩ => ⟨i, ea, j, ⟨v, hx, w, ho, hy⟩, eb⟩,
    fun ⟨i, ea, j, ⟨v, hx, w, ho, hy⟩, eb⟩ => ⟨v, ⟨i, ea, hx⟩, w, ho, j, eb, hy⟩⟩

theorem comp_lift {B : RelSet.{0}} (X Y : Idx ⟶ B) : (posL° ≫ X) ≫ (posL° ≫ Y)° = posL° ≫ (X ≫ Y°) ≫ posL :=
  hom_ext fun _ _ => ⟨fun ⟨v, ⟨i, ea, hx⟩, j, eb, hy⟩ => ⟨i, ea, j, ⟨v, hx, hy⟩, eb⟩,
    fun ⟨i, ea, j, ⟨v, hx, hy⟩, eb⟩ => ⟨v, ⟨i, ea, hx⟩, j, eb, hy⟩⟩

theorem lift_inter {W V : Idx ⟶ Idx} (hW : Bd W) (hV : Bd V) :
    (posL° ≫ W ≫ posL) ∩ (posL° ≫ V ≫ posL) = posL° ≫ (W ∩ V) ≫ posL :=
  hom_ext fun _ _ => ⟨fun ⟨⟨i, ea, j, hw, eb⟩, ⟨i', ea', j', hv, eb'⟩⟩ => by
      obtain rfl := ofNat_inj (lt64 (hW i j hw).1) (lt64 (hV i' j' hv).1) (ea.symm.trans ea')
      obtain rfl := ofNat_inj (lt64 (hW _ j hw).2) (lt64 (hV _ j' hv).2) (eb.symm.trans eb')
      exact ⟨_, ea, _, ⟨hw, hv⟩, eb⟩,
    fun ⟨i, ea, j, ⟨hw, hv⟩, eb⟩ => ⟨⟨i, ea, j, hw, eb⟩, ⟨i, ea, j, hv, eb⟩⟩⟩

theorem lift_union (W V : Idx ⟶ Idx) : (posL° ≫ W ≫ posL) ∪ (posL° ≫ V ≫ posL) = posL° ≫ (W ∪ V) ≫ posL :=
  hom_ext fun _ _ => ⟨fun h => h.elim (fun ⟨i, ea, j, hw, eb⟩ => ⟨i, ea, j, Or.inl hw, eb⟩)
      (fun ⟨i, ea, j, hv, eb⟩ => ⟨i, ea, j, Or.inr hv, eb⟩),
    fun ⟨i, ea, j, h, eb⟩ => h.elim (fun hw => Or.inl ⟨i, ea, j, hw, eb⟩) (fun hv => Or.inr ⟨i, ea, j, hv, eb⟩)⟩

/-- `est(≥)` on the longs of positions is `est(≥)` on the positions. -/
theorem lift_est {W : Idx ⟶ Idx} (hW : Bd W) :
    Λ (posL° ≫ W ≫ posL) ≫ est (fun a b : Int64 => a ≥ b) = posL° ≫ (Λ W ≫ est geN) ≫ posL := by
  refine hom_ext fun a b => ?_
  rw [RelSet.Λ_comp_est_apply]
  constructor
  · rintro ⟨⟨i, rfl, j, hw, rfl⟩, hm⟩
    exact ⟨i, rfl, j, (RelSet.Λ_comp_est_apply _ _ _ _).2 ⟨hw, fun k hk =>
      (ofNat_le (hW i k hk).2 (hW i j hw).2).1 (hm _ ⟨i, rfl, k, hk, rfl⟩)⟩, rfl⟩
  · rintro ⟨i, rfl, j, h, rfl⟩
    obtain ⟨hw, hm⟩ := (RelSet.Λ_comp_est_apply _ _ _ _).1 h
    refine ⟨⟨i, rfl, j, hw, rfl⟩, fun _ ⟨i', ea, k, hk, ez⟩ => ?_⟩
    obtain rfl := ofNat_inj (lt64 (hW i' k hk).1) (lt64 (hW i j hw).1) ea.symm
    subst ez
    exact (ofNat_le (hW _ k hk).2 (hW _ j hw).2).2 (hm k hk)

/-- `miss` on `til n`'s longs is `miss` on its positions. -/
theorem til_miss_lift {n : Nat} {M : Idx ⟶ Idx} (e : Int64) (hn : n ≤ 2 ^ 63) (hM : ∀ i j, M i j → i < 2 ^ 63) :
    (til n).den ≫ Verb.miss (posL° ≫ M ≫ posL) e = posL° ≫ corefl (· < n) ≫ Verb.miss (M ≫ graph Int64.ofNat) e := by
  have hat : ∀ i, i < 2 ^ 63 → ∀ c, (posL° ≫ M ≫ posL) (Int64.ofNat i) c ↔ (M ≫ graph Int64.ofNat) i c :=
    fun i hi c => ⟨fun ⟨i', ea, j, hm, eb⟩ => by
        obtain rfl := ofNat_inj (lt64 (hM i' j hm)) (lt64 hi) ea.symm; exact ⟨j, hm, eb⟩,
      fun ⟨j, hm, eb⟩ => ⟨i, rfl, j, hm, eb⟩⟩
  have key : ∀ i, i < n → ∀ c, Verb.miss (posL° ≫ M ≫ posL) e (Int64.ofNat i) c ↔
      Verb.miss (M ≫ graph Int64.ofNat) e i c := fun i hi c => by
    rw [Verb.miss_iff, Verb.miss_iff]; simp only [hat i (by omega)]
  exact hom_ext fun a c => ⟨fun ⟨_, ⟨i, ea, _, ⟨rfl, hi⟩, rfl⟩, hm⟩ => ⟨i, ea, i, ⟨rfl, hi⟩, (key i hi c).1 hm⟩,
    fun ⟨i, ea, _, ⟨rfl, hi⟩, hm⟩ => ⟨_, ⟨i, ea, i, ⟨rfl, hi⟩, rfl⟩, (key i hi c).2 hm⟩⟩

/-- **Λ-fusion under `miss`**: a list `y` before `Λ(G) ≫ est(R)` moves inside, `y ≫ G`, on `y`'s positions. -/
theorem fuse {t : QAtomicType} {ny : Nat} (y : Arr t ny) {B : RelSet.{0}} (G : Ob t ⟶ Idx) (R : Idx ⟶ Idx)
    (F : Idx ⟶ B) (e : B.carrier) :
    y.rel ≫ Verb.miss ((Λ G ≫ est R) ≫ F) e = corefl (· < ny) ≫ Verb.miss ((Λ (y.rel ≫ G) ≫ est R) ≫ F) e := by
  have hf : ∀ {i v v'}, y.rel i v → y.rel i v' → v = v' := fun h h' => by
    obtain ⟨_, ea⟩ := (rel_iff y _ _).1 h; obtain ⟨_, eb⟩ := (rel_iff y _ _).1 h'; exact ea.symm.trans eb
  have hM : ∀ i v c, y.rel i v →
      (Verb.miss ((Λ G ≫ est R) ≫ F) e v c ↔ Verb.miss ((Λ (y.rel ≫ G) ≫ est R) ≫ F) e i c) := fun i v c hv => by
    have hE : ∀ j, (Λ (y.rel ≫ G) ≫ est R) i j ↔ (Λ G ≫ est R) v j := fun j => by
      rw [RelSet.Λ_comp_est_apply, RelSet.Λ_comp_est_apply]
      constructor
      · rintro ⟨⟨v', hv', hg⟩, hm⟩; obtain rfl := hf hv hv'; exact ⟨hg, fun z hz => hm z ⟨_, hv, hz⟩⟩
      · rintro ⟨hg, hm⟩; exact ⟨⟨v, hv, hg⟩, fun z ⟨v', hv', hz⟩ => by obtain rfl := hf hv hv'; exact hm z hz⟩
    have h1 : ∀ c, ((Λ (y.rel ≫ G) ≫ est R) ≫ F) i c ↔ ((Λ G ≫ est R) ≫ F) v c :=
      fun c => ⟨fun ⟨j, h, f⟩ => ⟨j, (hE j).1 h, f⟩, fun ⟨j, h, f⟩ => ⟨j, (hE j).2 h, f⟩⟩
    rw [Verb.miss_iff, Verb.miss_iff]; simp only [h1]
  exact hom_ext fun i c => ⟨fun ⟨v, hv, hm⟩ => ⟨i, ⟨rfl, ((rel_iff y i v).1 hv).1⟩, (hM i v c hv).1 hm⟩,
    fun ⟨_, ⟨rfl, hi⟩, hm⟩ => ⟨_, (rel_iff y i _).2 ⟨hi, rfl⟩, (hM i _ c ((rel_iff y i _).2 ⟨hi, rfl⟩)).2 hm⟩⟩

/-- `miss(E, e)` on the keys `T`: `T ≫ E`, and `e` on the keys of `T` that `E` misses (`anti`). -/
def missP (T E : Prog .long .long) (e : Int64) : Prog .long .long :=
  union (comp T E) (comp (anti T (dom E)) (fn (.cst (u := .long) e)))

theorem missP_den (T E : Prog .long .long) (e : Int64) : (missP T E e).den = T.den ≫ Verb.miss E.den e :=
  comp_cup _ _ _ _

/-- `x bin y = y ≫ miss(Λ((≥) ≫ x°) ≫ est(≥), −1)`, written Λ-fused: `miss(Λ(y ≫ (≥) ≫ x°) ≫ est(≥), −1)` on `til |y|`. -/
def bin {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) : Prog .long .long :=
  missP (til ny) (extr true (ojoin .ge (arr y) (arr x))) (-1)

theorem bin_den {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) :
    (bin x y).den = (til ny).den ≫
      Verb.miss (Λ ((posL° ≫ y.rel) ≫ ord .ge ≫ (posL° ≫ x.rel)°) ≫ est (fun a b : Int64 => a ≥ b)) (-1) :=
  missP_den _ _ _

/-- **R6**: the order join of `bin` is `binJ`'s bisection, for lists below `2^63`. -/
theorem bin_R6 {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hx : nx ≤ 2 ^ 63) (hy : ny ≤ 2 ^ 63) :
    (bin x y).den = (binJ x y).den := by
  have hW := bd_join (ord .ge) (arr_lt y hy) (arr_lt x hx)
  rw [bin_den, join_lift, lift_est hW, til_miss_lift _ hy fun i j h => (bd_est _ hW i j h).1]
  show _ = posL° ≫ y.rel ≫ _
  rw [fuse y]

/-- `aj = miss(Λ((lk ≫ rk°) ∩ (lt ≫ (≥) ≫ rt°)) ≫ est(≥), 0N)` on `til |lk|`. -/
def aj {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) : Prog .long .long :=
  missP (til nl) (extr true (inter (comp (arr lk) (conv (arr rk))) (ojoin .ge (arr lt) (arr rt)))) Int64.minValue

theorem aj_den {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) :
    (aj lk lt rk rt).den = (til nl).den ≫ Verb.miss (Λ (((posL° ≫ lk.rel) ≫ (posL° ≫ rk.rel)°) ∩
      ((posL° ≫ lt.rel) ≫ ord .ge ≫ (posL° ≫ rt.rel)°)) ≫ est (fun a b : Int64 => a ≥ b)) Int64.minValue :=
  missP_den _ _ _

/-- **R7**: `aj`'s order join is `ajJ`'s per-key bisection, for tables below `2^63`. -/
theorem aj_R7 {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63) :
    (aj lk lt rk rt).den = (ajJ lk lt rk rt).den := by
  have hK := bd_comp (arr_lt lk hl) (arr_lt rk hr)
  have hJ := bd_join (ord .ge) (arr_lt lt hl) (arr_lt rt hr)
  have hKJ : Bd ((lk.rel ≫ rk.rel°) ∩ (lt.rel ≫ ord .ge ≫ rt.rel°)) := fun i j h => hK i j h.1
  rw [aj_den, comp_lift, join_lift, lift_inter hK hJ, lift_est hKJ,
    til_miss_lift _ hl fun i j h => (bd_est _ hKJ i j h).1]
  rfl

/-- `wj1 = (lk ≫ rk°) ∩ (w₀ ≫ (≤) ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)`: the window as a relation, its runs `Λ(—) ≫ enum`. -/
def wj1 {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) : Prog .long .long :=
  inter (inter (comp (arr lk) (conv (arr rk))) (ojoin .le (arr w₀) (arr rt))) (ojoin .ge (arr w₁) (arr rt))

theorem wj1_den {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    (wj1 lk w₀ w₁ rk rt).den = (((posL° ≫ lk.rel) ≫ (posL° ≫ rk.rel)°) ∩
      ((posL° ≫ w₀.rel) ≫ ord .le ≫ (posL° ≫ rt.rel)°)) ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt.rel)°) :=
  rfl

/-- `wj = (K ∩ (w₀ ≫ (<) ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)) ∪ (Λ(K ∩ (w₀ ≫ (≥) ≫ rt°)) ≫ est(≥))`, `K = lk ≫ rk°`. -/
def wj {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) : Prog .long .long :=
  union (inter (inter (comp (arr lk) (conv (arr rk))) (ojoin .lt (arr w₀) (arr rt))) (ojoin .ge (arr w₁) (arr rt)))
    (extr true (inter (comp (arr lk) (conv (arr rk))) (ojoin .ge (arr w₀) (arr rt))))

theorem wj_den {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    (wj lk w₀ w₁ rk rt).den = ((((posL° ≫ lk.rel) ≫ (posL° ≫ rk.rel)°) ∩
      ((posL° ≫ w₀.rel) ≫ ord .lt ≫ (posL° ≫ rt.rel)°)) ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt.rel)°)) ∪
      (Λ (((posL° ≫ lk.rel) ≫ (posL° ≫ rk.rel)°) ∩ ((posL° ≫ w₀.rel) ≫ ord .ge ≫ (posL° ≫ rt.rel)°)) ≫
        est (fun a b : Int64 => a ≥ b)) :=
  rfl

/-- **R8** (`wj1`): the three order joins are `wjJ`'s window ranges, for tables below `2^63`. -/
theorem wj1_R8 {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63) :
    (wj1 lk w₀ w₁ rk rt).den = (wjJ false lk w₀ w₁ rk rt).den := by
  have hK := bd_comp (arr_lt lk hl) (arr_lt rk hr)
  have h0 := bd_join (ord .le) (arr_lt w₀ hl) (arr_lt rt hr)
  have h1 := bd_join (ord .ge) (arr_lt w₁ hl) (arr_lt rt hr)
  rw [wj1_den, comp_lift, join_lift, join_lift, lift_inter hK h0, lift_inter (fun i j h => hK i j h.1) h1]
  rfl

/-- **R8** (`wj`): the window and the prevailing row are `wjJ`'s ranges, for tables below `2^63`. -/
theorem wj_R8 {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63) :
    (wj lk w₀ w₁ rk rt).den = (wjJ true lk w₀ w₁ rk rt).den := by
  have hK := bd_comp (arr_lt lk hl) (arr_lt rk hr)
  have h0 := bd_join (ord .lt) (arr_lt w₀ hl) (arr_lt rt hr)
  have h1 := bd_join (ord .ge) (arr_lt w₁ hl) (arr_lt rt hr)
  have hP := bd_join (ord .ge) (arr_lt w₀ hl) (arr_lt rt hr)
  rw [wj_den, comp_lift, join_lift, join_lift, join_lift, lift_inter hK h0, lift_inter (fun i j h => hK i j h.1) h1,
    lift_inter hK hP, lift_est (fun i j h => hK i j h.1), lift_union]
  rfl

/-- The key `i` of a window row is a left row. -/
theorem win_lt {nl nr : Nat} (prev : Bool) (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    ∀ i j, win prev lk w₀ w₁ rk rt i j → i < nl := by
  have hK : ∀ i j, (lk.rel ≫ rk.rel°) i j → i < nl := fun i _ ⟨_, h, _⟩ => ((rel_iff lk i _).1 h).1
  cases prev
  · exact fun i j h => hK i j h.1.1
  · exact fun i j h => h.elim (fun h => hK i j h.1.1) (fun h => hK i j ((RelSet.Λ_comp_est_apply _ _ _ _).1 h).1.1)

/-- `x bin y` runs to `bin_rel`'s right side. -/
theorem bin_prog {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hx : nx ≤ 2 ^ 63) (hy : ny ≤ 2 ^ 63)
    {R : RelV .long .long} (h : (bin x y).run = .ok R) (hs : (bin x y).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) =
      y.rel ≫ Verb.miss ((Λ (ord .ge ≫ x.rel°) ≫ est geN) ≫ graph Int64.ofNat) (-1) :=
  (posL_iff fun i _ ⟨_, hv, _⟩ => Nat.lt_of_lt_of_le ((rel_iff y i _).1 hv).1 (by omega : ny ≤ 2 ^ 64)).1
    ((run_sound _ hs h).trans (bin_R6 x y hx hy))

/-- `aj` runs to `aj_rel`'s right side, on the key columns as longs. -/
theorem aj_prog {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63)
    {R : RelV .long .long} (h : (aj lk lt rk rt).run = .ok R) (hs : (aj lk lt rk rt).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = corefl (· < nl) ≫
      Verb.miss ((Λ ((lk.rel ≫ rk.rel°) ∩ (lt.rel ≫ ord .ge ≫ rt.rel°)) ≫ est geN) ≫ graph Int64.ofNat) Int64.minValue :=
  (posL_iff fun _ _ ⟨_, ⟨e, hi⟩, _⟩ => by subst e; exact Nat.lt_of_lt_of_le hi (by omega : nl ≤ 2 ^ 64)).1 ((run_sound _ hs h).trans (aj_R7 lk lt rk rt hl hr))

/-- `wj1` runs to `wj1_rel`'s window, `W` on positions read through `posL`. -/
theorem wj1_prog {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63)
    {R : RelV .long .long} (h : (wj1 lk w₀ w₁ rk rt).run = .ok R) (hs : (wj1 lk w₀ w₁ rk rt).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = win false lk w₀ w₁ rk rt ≫ posL :=
  (posL_iff fun i _ ⟨j, hw, _⟩ => Nat.lt_of_lt_of_le (win_lt false lk w₀ w₁ rk rt i j hw) (by omega : nl ≤ 2 ^ 64)).1
    ((run_sound _ hs h).trans (wj1_R8 lk w₀ w₁ rk rt hl hr))

/-- `wj` runs to `wj_rel`'s window with the prevailing row, `W` on positions read through `posL`. -/
theorem wj_prog {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63)
    {R : RelV .long .long} (h : (wj lk w₀ w₁ rk rt).run = .ok R) (hs : (wj lk w₀ w₁ rk rt).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = win true lk w₀ w₁ rk rt ≫ posL :=
  (posL_iff fun i _ ⟨j, hw, _⟩ => Nat.lt_of_lt_of_le (win_lt true lk w₀ w₁ rk rt i j hw) (by omega : nl ≤ 2 ^ 64)).1
    ((run_sound _ hs h).trans (wj_R8 lk w₀ w₁ rk rt hl hr))

/-- A run of `conv P` ran `P`, and holds its converse. -/
theorem conv_run {A B : QAtomicType} {P : Prog A B} {R : RelV B A} (h : (conv P).run = .ok R) :
    ∃ R₁, P.run = .ok R₁ ∧ ∀ a b, R.Holds b a ↔ R₁.Holds a b := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  · exact ⟨_, by assumption, Alg.conv_holds (liftV_ok h)⟩

/-- `rank x` runs to `rank_rel`'s right side: read at the positions below `2^64` and back through `pos`, it is
    `(ix G)°`, `G` the list `sort(⊴ₓ)` gives. -/
theorem rank_prog {n : Nat} {x : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws)
    (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : RelV .long .long}
    (h : (rank (fun a b : Int64 => a < b) x).run = .ok R) :
    ∃ G : List Nat, (Verb.cst (CL.ofList G) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable x.rel fun a b : Int64 => a < b)
      ∧ corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) ≫ Verb.pos = (ix G)° := by
  obtain ⟨R₁, h1, hcv⟩ := conv_run h
  obtain ⟨S, k, hg, hk, rfl⟩ := grade_run h1
  obtain ⟨M, hc, hS, hl, hM⟩ := grade_long hx hn h63 hg
  have h64 := USize.size_le
  have hR : ∀ a b, R.Holds b a ↔ ∃ p, a = Int64.ofNat p ∧ ∃ m, M[p]? = some m ∧ b = Int64.ofNat m := fun a b =>
    (hcv a b).trans (Iff.of_eq (congrArg (fun r => r a b)
      ((arr_sound S hk).trans (congrArg (posL° ≫ ·) (rel_ofList hS)))))
  refine ⟨M, hc, hom_ext fun i j => ⟨fun ⟨_, ⟨rfl, hi⟩, _, rfl, w, hw, hp⟩ => ?_, fun hj => ?_⟩⟩
  · obtain ⟨p, rfl, m, hm, e⟩ := (hR w _).1 hw
    have hp' : p < n := hl ▸ (List.getElem?_eq_some_iff.1 hm).1
    have hmn := hM m (List.mem_of_getElem? hm)
    obtain rfl := ofNat_inj hi (by omega) e
    obtain rfl := (pos_ofNat (by omega) j).1 hp
    exact hm
  · have hj' := (List.getElem?_eq_some_iff.1 hj).1
    have hin := hM i (List.mem_of_getElem? hj)
    exact ⟨i, ⟨rfl, by omega⟩, _, rfl, Int64.ofNat j, (hR _ _).2 ⟨j, rfl, i, hj, rfl⟩, (pos_ofNat (by omega) j).2 rfl⟩

/-! ## `avg` against q's `avg` -/

/-- A list's rows as one group, read through `pos`: the key `0` against each position `X` holds. -/
theorem whole_iff {t : QAtomicType} (X : Idx ⟶ Ob t) (hX : ∀ i v, X i v → i < 2 ^ 63) (k : Int64) (i : Nat) :
    (((posL° ≫ X) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos : Ob .long ⟶ Idx) k i ↔ k = 0 ∧ ∃ v, X i v :=
  ⟨fun ⟨l, ⟨v, ⟨j, ej, hx⟩, hc⟩, hp⟩ => by
      subst ej
      obtain rfl := (pos_ofNat (hX j v hx) i).1 hp
      exact ⟨hc, v, hx⟩,
    fun ⟨hk, v, hx⟩ => ⟨_, ⟨v, ⟨i, rfl, hx⟩, hk⟩, (pos_ofNat (hX i v hx) i).2 rfl⟩⟩

/-- `Λ` over one group: `W` relates the key `0` alone to the positions `s`. -/
theorem whole_lam {B : RelSet.{0}} {W : Ob .long ⟶ Idx} {s : Nat → Prop} (hW : ∀ k i, W k i ↔ k = 0 ∧ s i)
    (L : ListRel.dList Nat ⟶ B) (k : Int64) (v : B.carrier) :
    (Verb.dom W ≫ Λ W ≫ Verb.enum ≫ L) k v ↔ k = 0 ∧ (∃ i, s i) ∧ ∃ zs, Verb.enum s zs ∧ L zs v := by
  have hs : (fun i => W 0 i) = s := funext fun i => propext ((hW 0 i).trans ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)
  rw [Λ_eq_classifier]
  constructor
  · rintro ⟨_, ⟨rfl, i, hi, -⟩, _, rfl, zs, he, hl⟩
    obtain ⟨rfl, h⟩ := (hW _ i).1 hi
    exact ⟨rfl, ⟨i, h⟩, zs, hs ▸ he, hl⟩
  · rintro ⟨rfl, ⟨i, h⟩, zs, he, hl⟩
    have hi := (hW 0 i).2 ⟨rfl, h⟩
    exact ⟨0, ⟨rfl, i, hi, hi⟩, _, rfl, zs, (show Verb.enum (fun i => W 0 i) zs from hs ▸ he), hl⟩

/-- `f/x` at its one key: `0` against the fold of the whole list, where the list is not empty. -/
theorem over_val {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) (hn : n ≤ 2 ^ 63) (k v : Int64) :
    (over op x).den k v ↔
      k = 0 ∧ 0 < n ∧ v = x.toList.foldr (Verb.skipNul op.step) (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) := by
  have hW : ∀ k i, ((whole (arr x)).den ≫ Verb.pos) k i ↔ k = 0 ∧ ∃ v, x.rel i v := whole_iff x.rel (arr_lt x hn)
  have hmem : ∀ i, i ∈ List.range' 0 n ↔ ∃ v, x.rel i v := fun i => by
    rw [List.mem_range'_1]
    exact ⟨fun h => ⟨_, (rel_iff x i _).2 ⟨by omega, rfl⟩⟩, fun ⟨v, h⟩ => ⟨Nat.zero_le _, by have := ((rel_iff x i v).1 h).1; omega⟩⟩
  have hE := Verb.enum_ofList _ _ List.pairwise_lt_range' hmem
  have hY : ∀ ys, ListRel.list x.rel (CL.ofList (List.range' 0 n)) ys ↔ ys = CL.ofList x.toList := fun ys => by
    have := Verb.listP_ix_range' x.toList n 0 (by rw [Arr.length_toList]; omega) ys
    rw [List.drop_zero, List.take_of_length_le (by rw [Arr.length_toList]; try omega)] at this
    exact this
  refine (whole_lam hW _ k v).trans ?_
  rw [show Verb.fold (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) = graph (fun ys =>
    (CL.toList ys).foldr (Verb.skipNul op.step) (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul)) from (Verb.foldr_cata _ _).symm]
  constructor
  · rintro ⟨rfl, ⟨i, w, hi⟩, zs, he, ys, hy, hv⟩
    obtain rfl := (hE zs).1 he
    obtain rfl := (hY ys).1 hy
    have := ((rel_iff x i w).1 hi).1
    exact ⟨rfl, by omega, by rw [hv]; simp only [CL.toList_ofList]⟩
  · rintro ⟨rfl, hn0, rfl⟩
    exact ⟨rfl, ⟨0, _, (rel_iff x 0 _).2 ⟨hn0, rfl⟩⟩, _, (hE _).2 rfl, _, (hY _).2 rfl,
      by simp only [RelSet.graph, CL.toList_ofList]⟩

/-- Counting the positions of a list that pass `p` counts the elements that pass it. -/
theorem filter_range_len {α : Type} (p : α → Bool) (d : α) : ∀ xs : List α,
    ((List.range xs.length).filter fun i => p (xs.getD i d)).length = (xs.filter p).length
  | [] => rfl
  | a :: xs => by
    have ih := filter_range_len p d xs
    simp only [List.getD_eq_getElem?_getD] at ih
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, List.filter_cons]
    cases h : p a <;> simp [h, Function.comp_def, ih]

/-- `count(whole(nonNul x))` at its one key: `0` against the number of elements that are not `0N`, where
    there is one. -/
theorem count_val {n : Nat} (x : Arr .long n) (hn : n ≤ 2 ^ 63) (k c : Int64) :
    (count (whole (nonNul x))).den k c ↔ k = 0 ∧ 0 < (x.toList.filter (· != Spec.nul)).length ∧
      c = Int64.ofNat (x.toList.filter (· != Spec.nul)).length := by
  let X : Idx ⟶ Ob .long := x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul)
  have hX : ∀ i v, X i v → i < 2 ^ 63 := fun i v ⟨w, hw, _⟩ => arr_lt x hn i w hw
  have hW : ∀ k i, ((whole (nonNul x)).den ≫ Verb.pos) k i ↔ k = 0 ∧ ∃ v, X i v := fun k i => by
    show ((((nonNul x).den ≫ _)° ≫ _) k i ↔ _)
    rw [nonNul_den]; exact whole_iff X hX k i
  let L := (List.range x.toList.length).filter fun i => x.toList.getD i 0 != Spec.nul
  have hmem : ∀ i, i ∈ L ↔ ∃ v, X i v := fun i => by
    simp only [L, List.mem_filter, List.mem_range, List.getD_eq_getElem?_getD]
    constructor
    · rintro ⟨hi, e⟩
      rw [List.getElem?_eq_getElem hi] at e
      exact ⟨_, _, List.getElem?_eq_getElem hi, rfl, by simpa using e⟩
    · rintro ⟨v, w, hw, rfl, hne⟩
      have hi : i < x.toList.length := (List.getElem?_eq_some_iff.1 hw).1
      exact ⟨hi, by rw [show x.toList[i]? = some w from hw]; simpa using hne⟩
  have hE := Verb.enum_ofList _ L ((List.pairwise_lt_range ..).filter _) hmem
  have hlen : L.length = (x.toList.filter (· != Spec.nul)).length := filter_range_len (· != Spec.nul) 0 x.toList
  have hf : ∀ l : List Nat, l.foldr (fun _ c => c + 1) 0 = l.length := fun l => by induction l <;> simp [*]
  refine (whole_lam hW _ k c).trans ?_
  rw [← hlen]
  constructor
  · rintro ⟨rfl, ⟨i, hi⟩, zs, he, m, hm, hc⟩
    obtain rfl := (hE zs).1 he
    refine ⟨rfl, List.length_pos_iff_exists_mem.2 ⟨i, (hmem i).2 hi⟩, ?_⟩
    rw [hc, show m = ListRel.clen (CL.ofList L) from hm, clen_foldr, CL.toList_ofList, hf]
  · rintro ⟨rfl, hpos, rfl⟩
    obtain ⟨i, hi⟩ := List.length_pos_iff_exists_mem.1 hpos
    exact ⟨rfl, ⟨i, (hmem i).1 hi⟩, _, (hE _).2 rfl, _, rfl, by rw [clen_foldr, CL.toList_ofList, hf]; rfl⟩

/-- `÷` on two longs that are not `0N`: the `Float.ofInt` quotient, a NaN read as `0n`. -/
theorem div_long {a b : Int64} (ha : a ≠ Spec.nul) (hb : b ≠ Spec.nul) :
    elem (a := .long) (b := .long) (c := .float) .div rfl a b =
      .ok (let r := (Float.ofInt a.toInt / Float.ofInt b.toInt).toBits; if Bits.f64IsNaN r then QLean.nanBits else r) := by
  have hd : dyadAtom .div (.long a) (.long b) =
      .ok (.float (let r := (Float.ofInt a.toInt / Float.ofInt b.toInt).toBits;
        if Bits.f64IsNaN r then QLean.nanBits else r)) := by
    have ha' : (a == Int64.minValue) = false := by simpa using ha
    have hb' : (b == Int64.minValue) = false := by simpa using hb
    simp [dyadAtom, Prim.arith, Prim.nonNumeric, arithAtoms, missing, QAtom.isNull, QAtom.type, ha', hb', isFloatPayload,
      floatIn, temporalIn, temporalScale, temporalNanos, floatPayload, intPayload, atomOfFloat]
  unfold elem
  rw [dif_neg (by decide), dif_neg (by decide)]
  split
  · rename_i e he; cases he.symm.trans hd
  · rename_i z hz; cases hz.symm.trans hd; rfl

/-- **`avg x` is q's `avg`**: the key `0` against `Spec.avg`, `0n` where no element counts. Two side
    conditions: the total is not `0N`, which `÷` reads as null like every long `0N` (no kernel route
    reads a long `0N` as `-2^63`); and `Int64.toFloat`, opaque, is `Float.ofInt ∘ toInt`. -/
theorem avg_val {n : Nat} (x : Arr .long n) (hn : n < 2 ^ 63) (hF : ∀ a : Int64, a.toFloat = Float.ofInt a.toInt)
    (hs : x.toList.foldr (Verb.skipNul (· + ·)) 0 ≠ Spec.nul) (k : Int64) (v : UInt64) :
    (avg x).den k v ↔ k = 0 ∧ v = Spec.avg x.toList := by
  have hn' : n ≤ 2 ^ 63 := Nat.le_of_lt hn
  obtain ⟨m, hm⟩ : ∃ m, (x.toList.filter (· != Spec.nul)).length = m := ⟨_, rfl⟩
  have hmn : m ≤ n := by
    rw [← hm]; have := List.length_filter_le (· != Spec.nul) x.toList; rw [Arr.length_toList] at this; exact this
  have hmo : (Int64.ofNat m).toInt = m := Int64.toInt_ofNat_of_lt (by omega)
  have hS := over_val .add x hn'
  have hC := count_val x hn'
  rw [hm] at hC
  have hM : ∀ k' w, (avgDiv x).den k' w ↔ k' = 0 ∧ 0 < m ∧
      elem (a := .long) (b := .long) (c := .float) .div rfl (x.toList.foldr (Verb.skipNul (· + ·)) 0) (Int64.ofNat m) = .ok w :=
    fun k' w => ⟨fun ⟨p, ⟨h1, h2⟩, he⟩ => by
        obtain ⟨rfl, -, e1⟩ := (hS k' p.1).1 h1
        obtain ⟨-, hm0, e2⟩ := (hC 0 p.2).1 h2
        refine ⟨rfl, hm0, ?_⟩
        rw [show x.toList.foldr (Verb.skipNul (· + ·)) 0 = p.1 from e1.symm, ← e2]; exact he,
      fun ⟨e, hm0, he⟩ => ⟨(_, Int64.ofNat m), ⟨(hS k' _).2 ⟨e, by omega, rfl⟩, (hC k' _).2 ⟨e, hm0, rfl⟩⟩, he⟩⟩
  have hq : Spec.avg x.toList = Spec.quot (x.toList.foldr (Verb.skipNul (· + ·)) 0, m) := by
    rw [← hm, ← Verb.over_foldr (· + ·) 0 Int64.add_assoc Int64.zero_add Int64.add_zero]; rfl
  have hnul : Int64.ofNat m ≠ Spec.nul := fun e => by
    have := congrArg Int64.toInt e; rw [hmo] at this; simp [Spec.nul] at this
  have hval : ∀ w, 0 < m → elem (a := .long) (b := .long) (c := .float) .div rfl
      (x.toList.foldr (Verb.skipNul (· + ·)) 0) (Int64.ofNat m) = .ok w → w = Spec.avg x.toList := fun w hm0 he => by
    rw [div_long hs hnul, hmo] at he
    cases he
    rw [hq]
    simp only [Spec.quot, beq_iff_eq, Nat.pos_iff_ne_zero.1 hm0, if_false]
    rw [hF]
    rfl
  rw [avg_den]
  constructor
  · rintro ⟨k', ⟨j, ej, j', ⟨rfl, hj⟩, ej'⟩, hmiss⟩
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    subst ej; subst ej'
    refine ⟨rfl, ?_⟩
    rcases (Verb.miss_iff _ _ _ _).1 hmiss with h | ⟨hno, rfl⟩
    · obtain ⟨-, hm0, he⟩ := (hM _ _).1 h
      exact hval v hm0 he
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos fun hm0 => hno (by
        cases hd : elem (a := .long) (b := .long) (c := .float) .div rfl (x.toList.foldr (Verb.skipNul (· + ·)) 0)
          (Int64.ofNat m) with
        | error e => exact absurd hd (by rw [div_long hs hnul]; simp)
        | ok w => exact ⟨w, (hM _ _).2 ⟨rfl, hm0, hd⟩⟩)
      rw [hq, hm0]; rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨0, ⟨0, rfl, 0, ⟨rfl, Nat.zero_lt_one⟩, rfl⟩, (Verb.miss_iff _ _ _ _).2 ?_⟩
    by_cases hm0 : 0 < m
    · exact .inl ((hM _ _).2 ⟨rfl, hm0, by rw [div_long hs hnul, ← hval _ hm0 (div_long hs hnul)]⟩)
    · refine .inr ⟨fun ⟨w, hw⟩ => hm0 ((hM _ _).1 hw).2.1, ?_⟩
      rw [hq, show m = 0 by omega]; rfl

/-- **`avg x` runs to `avg_rel`'s answer**: on a dense long column whose `Ops.avg` is `a`, the run of `avg x`
    holds the key `0` against `canon(a)`, under `avg_val`'s two side conditions. -/
theorem avg_prog {n : Nat} {x : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws) (hU : n < USize.size)
    (hn : n < 2 ^ 63) (hF : ∀ a : Int64, a.toFloat = Float.ofInt a.toInt)
    (hs : x.toList.foldr (Verb.skipNul (· + ·)) 0 ≠ Spec.nul) {a : UInt64} (ha : Ops.avg x = some a)
    {T : RelV .long .float} (h : (avg x).run = .ok T) (hS : (avg x).Sound) (k : Int64) (v : UInt64) :
    (T.Holds : Ob .long ⟶ Ob .float) k v ↔ k = 0 ∧ v = Spec.canon a := by
  rw [run_sound _ hS h, avg_val x hn hF hs, Ops.avg_long hx hU ha]

/-! ## Verbs, second half (design §2.3 `ij` to §2.5)

  The verbs of the second half that had no term yet, each from the existing constructors only. -/

/-- `ij = Λ(l ≫ r°) ≫ est(≤)`: the first right row matching each left row; unmatched left rows have none. -/
def ij {t : QAtomicType} {nl nr : Nat} (l : Arr t nl) (r : Arr t nr) : Prog .long .long :=
  extr false (comp (arr l) (conv (arr r)))

theorem ij_den {t : QAtomicType} {nl nr : Nat} (l : Arr t nl) (r : Arr t nr) :
    (ij l r).den = Λ ((posL° ≫ l.rel) ≫ (posL° ≫ r.rel)°) ≫ est (fun a b : Int64 => a ≤ b) := rfl

/-- `inits = Λ((≥)) ≫ enum` on `til n`: position `i` against every `j ≤ i`, written as the order join. -/
def inits (n : Nat) : Prog .long .long := ojoin .ge (til n) (til n)

/-- `f\x = inits ≫ list(x) ≫ ⦇e,f⦈`, `f` one of the kernel folds (`sums`, `prds`, `maxs`, `mins`). -/
def scan {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) : Prog .long .long := foldOp op x (inits n)

theorem scan_den {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) :
    (scan op x).den = Verb.dom ((til n).den ≫ ord .ge ≫ (til n).den° ≫ Verb.pos) ≫
      Λ ((til n).den ≫ ord .ge ≫ (til n).den° ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫
      Verb.fold (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) := by
  simp only [scan, foldOp, inits, den, Cat.assoc]

/-- `win(w) = (≥) ∩ (drop(w−1)° ≫ (≤))` on `til n`: `i` against `j` with `i−(w−1) ≤ j ≤ i`. The shift
    `drop(w−1)°` is the dyadic `−` against the constant `w−1`, so the window is two order joins. -/
def mwin (n w : Nat) : Prog .long .long :=
  inter (inits n) (ojoin .le (comp (til n) (fn (.sect (u := .long) false .sub rfl (Int64.ofNat (w - 1))))) (til n))

theorem mwin_den (n w : Nat) : (mwin n w).den = ((til n).den ≫ ord .ge ≫ (til n).den°) ∩
    ((comp (pair (til n) (comp (til n) (fn (.cst (u := .long) (Int64.ofNat (w - 1)))))) (fn (.dy .sub rfl))).den ≫ ord .le ≫ (til n).den°) := by
  rw [show (comp (pair (til n) (comp (til n) (fn (.cst (u := .long) (Int64.ofNat (w - 1)))))) (fn (.dy .sub rfl))).den =
    (comp (til n) (fn (.sect (u := .long) false .sub rfl (Int64.ofNat (w - 1))))).den from
    sect_pairR (t := .long) (u := .long) (rt := .long) (til n).den (til n).den .sub rfl _ fun _ b h => ⟨b, h⟩]; rfl

/-- `w msum x = Λ(win(w)) ≫ enum ≫ list(x) ≫ ⦇0,+⦈`, nulls skipped. -/
def msum {n : Nat} (w : Nat) (x : Arr .long n) : Prog .long .long := foldOp .add x (mwin n w)

theorem msum_den {n : Nat} (w : Nat) (x : Arr .long n) :
    (msum w x).den = Verb.dom ((mwin n w).den ≫ Verb.pos) ≫ Λ ((mwin n w).den ≫ Verb.pos) ≫ Verb.enum ≫
      ListRel.list x.rel ≫ Verb.fold (Kernel.Coc.Over.add.denseSeed QLean.Kernel.Ew.i64 Spec.nul)
        (Verb.skipNul Kernel.Coc.Over.add.step) := rfl

/-- `w mcount x = Λ(win(w) ∩ nonnull) ≫ enum ≫ length`; `count` has no row where the window holds no
    non-null, so q's `0` there is a `miss`. -/
def mcount {n : Nat} (w : Nat) (x : Arr .long n) : Prog .long .long :=
  missP (til n) (count (comp (mwin n w) (dom (nonNul x)))) 0

theorem mcount_den {n : Nat} (w : Nat) (x : Arr .long n) :
    (mcount w x).den = (til n).den ≫ Verb.miss (Verb.dom (((mwin n w).den ≫ Verb.dom (nonNul x).den) ≫ Verb.pos) ≫
      Λ (((mwin n w).den ≫ Verb.dom (nonNul x).den) ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.length ≫
        graph Int64.ofNat) 0 :=
  missP_den _ _ _

/-- `w mmin x = Λ(win(w) ≫ x) ≫ est(≤)` (`mmax`: `est(≥)`), over the non-null `x`, which q's `mmin` skips. -/
def mext {n : Nat} (desc : Bool) (w : Nat) (x : Arr .long n) : Prog .long .long :=
  extr desc (comp (mwin n w) (nonNul x))

theorem mmin_den {n : Nat} (w : Nat) (x : Arr .long n) :
    (mext false w x).den = Λ ((mwin n w).den ≫ posL° ≫ x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul)) ≫
      est (fun a b : Int64 => a ≤ b) := by
  show Λ ((mwin n w).den ≫ (nonNul x).den) ≫ _ = _
  rw [nonNul_den]

theorem mmax_den {n : Nat} (w : Nat) (x : Arr .long n) :
    (mext true w x).den = Λ ((mwin n w).den ≫ posL° ≫ x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul)) ≫
      est (fun a b : Int64 => a ≥ b) := by
  show Λ ((mwin n w).den ≫ (nonNul x).den) ≫ _ = _
  rw [nonNul_den]

/-- `,a = corefl(<1) ≫ !a`: an atom enlisted. A list enlisted is a `general` value, which `cst` refuses. -/
def enlist {u : QAtomicType} (a : El u) : Prog .long u := comp (til 1) (fn (.cst a))

theorem enlist_den {u : QAtomicType} (a : El u) : (enlist a).den = (til 1).den ≫ Verb.cst a := rfl

/-- `x~y` as the relation of its witnesses against it: the positions where `x <> y`, and the positions one
    list has and the other lacks. `x~y` holds iff the run is empty; the emptiness test is outside the term. -/
def matchW {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) : Prog .long .boolean :=
  union (comp (comp (pair (arr x) (arr y)) (fn (.test (.dy .ne rfl)))) (fn (.dy .ne rfl)))
    (comp (union (anti (til nx) (dom (arr y))) (anti (til ny) (dom (arr x)))) (fn (.cst true)))

/-- `T ∩ (T ≫ !1b)`, the true rows of `T = P ≫ c`, is `P c? c`, `c` simple. -/
theorem test_true {K : RelSet.{0}} {X : Obj} (P : K ⟶ Ob X) (c : Fn X (.atom .boolean))
    (hc : ∀ p b, c.den p b → c.den p true → b = true) :
    (P ≫ c.den) ∩ ((P ≫ c.den) ≫ Verb.cst true) = (P ≫ (Fn.test c).den) ≫ c.den := by
  refine hom_ext fun k b => ⟨?_, ?_⟩
  · rintro ⟨⟨p, hp, hb⟩, _, _, e⟩
    have e' : b = true := e
    have ht : c.den p true := e' ▸ hb
    exact ⟨p, ⟨p, hp, rfl, ht⟩, hb⟩
  · rintro ⟨_, ⟨p, hp, rfl, ht⟩, hb⟩
    exact ⟨⟨p, hp, hb⟩, true, ⟨p, hp, ht⟩, hc p b hb ht⟩

theorem matchW_den {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) :
    (matchW x y).den = ((comp (pair (arr x) (arr y)) (fn (.dy .ne rfl))).den ∩ ((comp (pair (arr x) (arr y)) (fn (.dy .ne rfl))).den ≫ Verb.cst true)) ∪
      ((((til nx).den ≫ Verb.corNeg (Verb.dom (posL° ≫ y.rel))) ∪
        ((til ny).den ≫ Verb.corNeg (Verb.dom (posL° ≫ x.rel)))) ≫ Verb.cst true) :=
  (congrArg (fun T : Ob .long ⟶ Ob .boolean => T ∪ _) (test_true (pair (arr x) (arr y)).den
    (Fn.dy (t := .long) (u := .long) .ne rfl) fun _ _ h h' => Except.ok.inj (h.symm.trans h'))).symm

/-- `x . (i;j) = ⟨i ≫ x, !j⟩ ≫ (@)`, a nested `x` stored flat: `v` its values, `o` its row offsets, so the
    row `i` is `o@i` and the element `v@(o@i)+j`. Nothing bounds `j` by the row's length. -/
def dot {t : QAtomicType} {g n : Nat} (o : Arr .long g) (v : Arr t n) (i j : Int64) : Prog .long t :=
  comp (comp (comp (comp (til 1) (fn (.cst (u := .long) i))) (arr o)) (fn (.sect (u := .long) false .add rfl j))) (arr v)

theorem dot_den {t : QAtomicType} {g n : Nat} (o : Arr .long g) (v : Arr t n) (i j : Int64) :
    (dot o v i j).den = (rpair ((til 1).den ≫ Verb.cst i ≫ posL° ≫ o.rel) ((til 1).den ≫ Verb.cst j) ≫
      ofExcept fun p => elem .add (rfl : Eval.ewType .add .long .long = some .long) p.1 p.2) ≫ posL° ≫ v.rel := by
  refine Eq.trans ?_ (congrArg (fun T : Ob .long ⟶ Ob .long => T ≫ posL° ≫ v.rel)
    (sect_pairR (t := .long) (u := .long) (rt := .long) ((til 1).den ≫ Verb.cst i ≫ posL° ≫ o.rel) (til 1).den .add rfl j
      fun _ _ ⟨m, hk, _⟩ => ⟨m, hk⟩)).symm
  simp only [dot, den, Cat.assoc]; rfl

/-! ## Verbs, first half (design §2.1–§2.3, up to `+x`)

  Each verb written with the existing constructors only. A verb with no term here is not expressible; the
  reason is recorded in the design's verb table (`rows-1.html`), not in a stub. -/

/-- `a v x = x (a v)`: the atom a section's operand (R2's left shape). -/
def atomL {t u rt : QAtomicType} {n : Nat} (a : El u) (v : Prim.Dyadic) (h : Eval.ewType v u t = some rt)
    (x : Arr t n) : Prog .long rt := comp (arr x) (fn (.sect true v h a))

theorem atomL_den {t u rt : QAtomicType} {n : Nat} (a : El u) (v : Prim.Dyadic) (h : Eval.ewType v u t = some rt)
    (x : Arr t n) : (atomL a v h x).den =
      rpair ((posL° ≫ x.rel) ≫ Verb.cst a) (posL° ≫ x.rel) ≫ ofExcept fun p => elem v h p.1 p.2 :=
  (sect_pairL _ _ v h a fun _ b h => ⟨b, h⟩).symm

/-- `x v a = x (v a)`. -/
def atomR {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) (x : Arr t n)
    (a : El u) : Prog .long rt := comp (arr x) (fn (.sect false v h a))

theorem atomR_den {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt)
    (x : Arr t n) (a : El u) : (atomR v h x a).den =
      rpair (posL° ≫ x.rel) ((posL° ≫ x.rel) ≫ Verb.cst a) ≫ ofExcept fun p => elem v h p.1 p.2 :=
  (sect_pairR _ _ v h a fun _ b h => ⟨b, h⟩).symm

/-- `%x = 1 % x`: `Fn.mono` keeps the value type, so the reciprocal (long → float) goes through the dyadic `%`. -/
def recip {n : Nat} (x : Arr .long n) : Prog .long .float := atomL (u := .long) (1 : Int64) .div rfl x

/-- `^x = x = 0N` on longs: the null test, the section `(=0N)`. -/
def isNul {n : Nat} (x : Arr .long n) : Prog .long .boolean := atomR .eq rfl x (u := .long) Spec.nul

/-- `til n + c`: the position map `k ↦ k + c` on `til n` (`take`/`drop`/`rot`/`rev`/`,` read through it). -/
def shiftBy (n : Nat) (c : Int64) : Prog .long .long := comp (til n) (fn (.sect (u := .long) false .add rfl c))

/-- `x v': x = ⟨x, miss(prev ≫ x, seed)⟩ ≫ (v)`, `prev = til n − 1`: position `0` has no predecessor, so
    the seed fills it. -/
def eachPrior {rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v .long .long = some rt)
    (seed : Int64) (x : Arr .long n) : Prog .long rt :=
  comp (pair (arr x) (missP (til n) (comp (shiftBy n (-1)) (arr x)) seed)) (fn (.dy v h))

theorem eachPrior_den {rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v .long .long = some rt)
    (seed : Int64) (x : Arr .long n) : (eachPrior v h seed x).den =
      rpair (posL° ≫ x.rel) ((til n).den ≫ Verb.miss ((shiftBy n (-1)).den ≫ posL° ≫ x.rel) seed) ≫
        ofExcept fun p => elem v h p.1 p.2 := by
  show rpair _ (missP (til n) (comp (shiftBy n (-1)) (arr x)) seed).den ≫ _ = _
  rw [missP_den]; rfl

/-- `miss(D, e)` on the keys `U`, any key and value type (`missP` at longs). -/
def missG {K t : QAtomicType} (U : Prog K K) (D : Prog K t) (e : El t) : Prog K t :=
  union (comp U D) (comp (anti U (dom D)) (fn (.cst e)))

theorem missG_den {K t : QAtomicType} (U : Prog K K) (D : Prog K t) (e : El t) :
    (missG U D e).den = U.den ≫ Verb.miss D.den e :=
  comp_cup _ _ _ _

/-- `d v e` on dicts: q's outer pairing, `⟨miss(d,eₗ), miss(e,eᵣ)⟩ ≫ (v)` on `dom d ∪ dom e`. -/
def dictDy {K t u rt : QAtomicType} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) (D : Prog K t)
    (E : Prog K u) (el : El t) (er : El u) : Prog K rt :=
  comp (pair (missG (union (dom D) (dom E)) D el) (missG (union (dom D) (dom E)) E er)) (fn (.dy v h))

theorem dictDy_den {K t u rt : QAtomicType} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) (D : Prog K t)
    (E : Prog K u) (el : El t) (er : El u) : (dictDy v h D E el er).den =
      rpair ((Verb.dom D.den ∪ Verb.dom E.den) ≫ Verb.miss D.den el)
        ((Verb.dom D.den ∪ Verb.dom E.den) ≫ Verb.miss E.den er) ≫ ofExcept fun p => elem v h p.1 p.2 := by
  show rpair (missG (union (dom D) (dom E)) D el).den (missG (union (dom D) (dom E)) E er).den ≫ _ = _
  rw [missG_den, missG_den]; rfl

/-- `x,y = split ≫ [x,y]`: `y` re-keyed past `x` by `(til |y| + |x|)°`, then the union. -/
def cat {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) : Prog .long t :=
  union (arr x) (comp (conv (shiftBy ny (Int64.ofNat nx))) (arr y))

theorem cat_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) :
    (cat x y).den = (posL° ≫ x.rel) ∪ ((shiftBy ny (Int64.ofNat nx)).den° ≫ posL° ≫ y.rel) := rfl

/-- `n#x = take(n) ≫ x` for `n ≤ |x|`: `til n` read through `x`. -/
def take {t : QAtomicType} {nx : Nat} (n : Nat) (x : Arr t nx) : Prog .long t := comp (til n) (arr x)

theorem take_den {t : QAtomicType} {nx : Nat} (n : Nat) (x : Arr t nx) :
    (take n x).den = (til n).den ≫ posL° ≫ x.rel := rfl

/-- `n_x = drop(n) ≫ x`: `k ↦ x[k+n]` on `til (|x|−n)`. -/
def drop {t : QAtomicType} {nx : Nat} (n : Nat) (x : Arr t nx) : Prog .long t :=
  comp (shiftBy (nx - n) (Int64.ofNat n)) (arr x)

theorem drop_den {t : QAtomicType} {nx : Nat} (n : Nat) (x : Arr t nx) :
    (drop n x).den = (shiftBy (nx - n) (Int64.ofNat n)).den ≫ posL° ≫ x.rel := rfl

/-- `r rotate x`, `r ≤ |x|`: no `mod` among the dyadic maps, so `rot(r)` is two shifted pieces,
    `k ↦ x[k+r]` below `|x|−r` and `k ↦ x[k+r−|x|]` from there. -/
def rotate {t : QAtomicType} {nx : Nat} (r : Nat) (x : Arr t nx) : Prog .long t :=
  union (drop r x) (comp (conv (shiftBy r (Int64.ofNat (nx - r)))) (arr x))

theorem rotate_den {t : QAtomicType} {nx : Nat} (r : Nat) (x : Arr t nx) :
    (rotate r x).den = (drop r x).den ∪ ((shiftBy r (Int64.ofNat (nx - r))).den° ≫ posL° ≫ x.rel) := rfl

/-- `|x = rev ≫ x`, `rev = (|x|−1) − til |x|`. -/
def revMap (n : Nat) : Prog .long .long := comp (til n) (fn (.sect (u := .long) true .sub rfl (Int64.ofNat (n - 1))))

def rev {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long t := comp (revMap n) (arr x)

theorem rev_den {t : QAtomicType} {n : Nat} (x : Arr t n) : (rev x).den = (revMap n).den ≫ posL° ≫ x.rel := rfl

/-- `@[x;i;v;y]` at distinct `i`: `(corNeg(ran i) ≫ x) ∪ (ran(i) ≫ ⟨x, i° ≫ y⟩ ≫ (v))`. The kept rows are
    `(x° ≫ corNeg(ran i))°`, since `anti` cuts on the value side. Repeated `i` pair every `y` with one `x`
    instead of folding them in order. -/
def amend {t u : QAtomicType} {nx ni : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some t) (x : Arr t nx)
    (i : Arr .long ni) (y : Arr u ni) : Prog .long t :=
  union (conv (anti (conv (arr x)) (dom (conv (arr i)))))
    (comp (pair (comp (dom (conv (arr i))) (arr x)) (comp (conv (arr i)) (arr y))) (fn (.dy v h)))

theorem amend_den {t u : QAtomicType} {nx ni : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some t)
    (x : Arr t nx) (i : Arr .long ni) (y : Arr u ni) : (amend v h x i y).den =
      ((posL° ≫ x.rel)° ≫ Verb.corNeg (Verb.dom (posL° ≫ i.rel)°))° ∪
        (rpair (Verb.dom (posL° ≫ i.rel)° ≫ posL° ≫ x.rel) ((posL° ≫ i.rel)° ≫ posL° ≫ y.rel) ≫
          ofExcept fun p => elem v h p.1 p.2) := rfl

/-- `o cut x`, flattened: each segment index against its values, `(Λ(til n ≫ (≥) ≫ o°) ≫ est(≥))° ≫ x`.
    The nested list itself is no `Prog` value; this is its `∋`. -/
def cutFlat {t : QAtomicType} {g n : Nat} (o : Arr .long g) (x : Arr t n) : Prog .long t :=
  comp (conv (extr true (ojoin .ge (til n) (arr o)))) (arr x)

theorem cutFlat_den {t : QAtomicType} {g n : Nat} (o : Arr .long g) (x : Arr t n) :
    (cutFlat o x).den = (Λ ((til n).den ≫ ord .ge ≫ (posL° ≫ o.rel)°) ≫ est (fun a b : Int64 => a ≥ b))° ≫
      posL° ≫ x.rel := rfl

/-- The comparison `v` is the converse of: `<`↔`>`, `≤`↔`≥`; `=` and `≠` are their own. -/
def mirror : Prim.Dyadic → Prim.Dyadic
  | .lt => .gt
  | .le => .ge
  | .gt => .lt
  | .ge => .le
  | v => v

/-- `R v a = R ≫ (v) ≫ â`, `â = {(a,a)}`: the value becomes `a`. `(v)` is infinite, so it runs as its section's test
    on `R`'s value followed by the constant `a`. -/
def valCmp {A : Obj} {t : QAtomicType} (v : Prim.Dyadic) (R : Prog A (.atom t)) (a : El t)
    (h : Eval.ewType v t t = some .boolean := by rfl) : Prog A (.atom t) :=
  comp (comp R (fn (.test (.sect false v h a)))) (fn (.cst a))

/-- `a v R = â ≫ (v) ≫ R`: the key becomes `a`. It runs as `(R° (mirror v) a)°`, since `(â (v) R)° = R° (mirror v) â`. -/
def keyCmp {t B : QAtomicType} (v : Prim.Dyadic) (a : El t) (R : Prog (.atom t) (.atom B))
    (h : Eval.ewType (mirror v) t t = some .boolean := by rfl) : Prog (.atom t) (.atom B) :=
  conv (valCmp (mirror v) (conv R) a h)

/-! `a v R` and `R v a`, overloading the comparisons: Lean's own reading fails on a `Prog`, these on anything else. -/
namespace Cmp

macro "cmp_notation " tk:str v:term : command => `(
  scoped notation:50 a:51 $tk:str R:51 => keyCmp $v a R
  scoped notation:50 R:51 $tk:str a:51 => valCmp $v R a)

cmp_notation " < " Prim.Dyadic.lt
cmp_notation " ≤ " Prim.Dyadic.le
cmp_notation " > " Prim.Dyadic.gt
cmp_notation " ≥ " Prim.Dyadic.ge
cmp_notation " = " Prim.Dyadic.eq
cmp_notation " ≠ " Prim.Dyadic.ne

end Cmp

/-- `(a <)? ≫ R`, q's `(where k>a)` over the key: the rows of `R` whose key is above `a`, the key kept. -/
def selKey {B : Obj} (a : Int64) (R : Prog .long B) : Prog .long B := comp (fn (.test (.sect (u := .long) true .lt rfl a))) R

/-- `R ≫ (< a)?`, the rows of `R` whose value is below `a`, the value kept. -/
def selVal {A : Obj} (R : Prog A .long) (a : Int64) : Prog A .long := comp R (fn (.test (.sect (u := .long) false .lt rfl a)))

theorem selKey_den {B : Obj} (a : Int64) (R : Prog .long B) :
    (selKey a R).den = corefl (fun x : Int64 => a < x) ≫ R.den :=
  congrArg (· ≫ R.den) (congrArg (corefl (A := Ob .long)) (funext fun x => propext (elem_ord (Or.inl rfl) rfl a x)))

theorem selVal_den {A : Obj} (R : Prog A .long) (a : Int64) :
    (selVal R a).den = R.den ≫ corefl (fun x : Int64 => x < a) :=
  congrArg (R.den ≫ ·) (congrArg (corefl (A := Ob .long)) (funext fun x => propext (elem_ord (Or.inl rfl) rfl x a)))

/-- **The bool path is the relational reading**: `(v a)?`, the test of a section, is `dom((v) ≫ a°)`, `a` the point
    `1 → long`, at the four orders. -/
theorem test_sect_dom {v : Prim.Dyadic} (hv : v = .lt ∨ v = .le ∨ v = .gt ∨ v = .ge)
    (h : Eval.ewType v .long .long = some .boolean) (a : Int64) :
    (Fn.test (.sect (t := .long) (u := .long) false v h a)).den =
      Verb.dom (ord v ≫ (Verb.cst a : (⟨Unit⟩ : RelSet.{0}) ⟶ Ob .long)°) :=
  hom_ext fun x y => ⟨fun ⟨e, hc⟩ => by
      subst e; have o := (elem_ord hv h x a).1 hc; exact ⟨rfl, (), ⟨a, o, rfl⟩, ⟨a, o, rfl⟩⟩,
    fun ⟨e, _, ⟨c, hx, hc⟩, _⟩ => by cases hc; exact ⟨e, (elem_ord hv h x a).2 hx⟩⟩

/-! ## `ran(×a)`, the multiples of `2^tz(a)` -/

/-- Two longs of one bit pattern are one long. -/
theorem bits_inj {x y : Int64} (e : x.toBitVec.toNat = y.toBitVec.toNat) : x = y :=
  Int64.toBitVec_inj.1 (BitVec.eq_of_toNat_eq e)

theorem bits_mul (x y : Int64) : (x * y).toBitVec.toNat = x.toBitVec.toNat * y.toBitVec.toNat % 2 ^ 64 := by
  simp [Int64.toBitVec_mul, BitVec.toNat_mul]

theorem bits_min : Int64.minValue.toBitVec.toNat = 2 ^ 63 := by decide

/-- `(×a)` on longs, `a` not null: q's null rule on `x` alone, else the wrapped product. -/
theorem elem_mul (h : Eval.ewType .mul .long .long = some .long) (x a : Int64) (ha : a ≠ Int64.minValue) :
    elem .mul h x a = .ok (if x = Int64.minValue then Int64.minValue else x * a) := by
  rw [Ew.elem_long_val (op := Kernel.Ew.mul) rfl h]
  simp (config := { decide := true }) [Kernel.Ew.intStep, ha]

/-- An odd number has an inverse modulo `2^n`. -/
theorem odd_inv (w : Nat) : ∀ n, ∃ i c, (2 * w + 1) * i = 1 + 2 ^ n * c
  | 0 => ⟨1, 2 * w, by simp; omega⟩
  | n + 1 => by
    obtain ⟨i, c, h⟩ := odd_inv w n
    obtain ⟨d, hd | hd⟩ : ∃ d, c = 2 * d ∨ c = 2 * d + 1 := ⟨c / 2, by omega⟩
    · exact ⟨i, d, by rw [h, hd, Nat.pow_succ]; grind⟩
    · exact ⟨i + 2 ^ n, d + w + 1, by rw [Nat.mul_add, h, hd, Nat.pow_succ]; grind⟩

/-- `n` is `2^tz(n)` times an odd number. -/
theorem tzNat_spec : ∀ k n, n ≠ 0 → n < 2 ^ k → ∃ w, n = 2 ^ tzNat k n * (2 * w + 1)
  | 0, n, h0, h => by simp at h; omega
  | k + 1, n, h0, h => by
    unfold tzNat
    split
    · exact ⟨n / 2, by simp; omega⟩
    · rename_i ho
      obtain ⟨w, hw⟩ := tzNat_spec k (n / 2) (by omega) (by rw [Nat.pow_succ] at h; omega)
      refine ⟨w, ?_⟩
      generalize tzNat k (n / 2) = s at hw
      calc n = 2 * (n / 2) := by omega
        _ = 2 * (2 ^ s * (2 * w + 1)) := by rw [← hw]
        _ = _ := by rw [Nat.pow_succ]; grind

/-- `a ≠ 0` is `2^tz(a)` times an odd number, with `tz(a) < 64`. -/
theorem tz_spec {a : Int64} (h0 : a ≠ 0) : tz a < 64 ∧ ∃ w, a.toBitVec.toNat = 2 ^ tz a * (2 * w + 1) := by
  have hn : a.toBitVec.toNat ≠ 0 := fun e => h0 (bits_inj (e.trans (by decide)))
  have hl := a.toBitVec.isLt
  obtain ⟨w, hw⟩ := tzNat_spec 64 _ hn hl
  refine ⟨(Nat.pow_lt_pow_iff_right (a := 2) (by omega)).1 (Nat.lt_of_le_of_lt ?_ hl), w, hw⟩
  rw [hw]; exact Nat.le_mul_of_pos_right _ (by omega)

/-- `(×a)` lands in the multiples of `2^t`, `0N = 2^63` among them because `t < 64`. -/
theorem mul_low {a : Int64} {t w : Nat} (ht : t < 64) (ha : a.toBitVec.toNat = 2 ^ t * (2 * w + 1)) (k : Int64) :
    (if k = Int64.minValue then Int64.minValue else k * a).toBitVec.toNat % 2 ^ t = 0 := by
  split
  · rw [bits_min]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))
  · rw [bits_mul, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), ha]
    exact Nat.mod_eq_zero_of_dvd ⟨k.toBitVec.toNat * (2 * w + 1), by grind⟩

/-- Every multiple of `2^t` is reached by `(×a)`: the odd part of `a` is invertible modulo `2^64`. `0N` is reached
    from `0N`, `0` from `0`, and any other `y` from a `k ≠ 0N`, since `0N × a` is `0` or `0N`. -/
theorem mul_onto {a y : Int64} {t w : Nat} (ha : a.toBitVec.toNat = 2 ^ t * (2 * w + 1))
    (hy : y.toBitVec.toNat % 2 ^ t = 0) : ∃ k, (if k = Int64.minValue then Int64.minValue else k * a) = y := by
  by_cases h1 : y = Int64.minValue
  · exact ⟨Int64.minValue, by rw [if_pos rfl, h1]⟩
  by_cases h2 : y = 0
  · exact ⟨0, by rw [if_neg (by decide), Int64.zero_mul, h2]⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, y.toBitVec.toNat = 2 ^ t * Z :=
    ⟨y.toBitVec.toNat / 2 ^ t, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hy)).symm⟩
  obtain ⟨i, c, hi⟩ := odd_inv w 64
  have hl := y.toBitVec.isLt
  have hk : Int64.ofNat (Z * i) * a = y := bits_inj (by
    have e : Z * i * a.toBitVec.toNat = y.toBitVec.toNat + 2 ^ 64 * (y.toBitVec.toNat * c) := by
      calc Z * i * a.toBitVec.toNat = 2 ^ t * Z * ((2 * w + 1) * i) := by rw [ha]; grind
        _ = _ := by rw [← hZ, hi]; grind
    rw [bits_mul, show (Int64.ofNat (Z * i)).toBitVec.toNat = Z * i % 2 ^ 64 by simp, Nat.mod_mul_mod, e,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl])
  refine ⟨Int64.ofNat (Z * i), ?_⟩
  rw [if_neg, hk]
  intro e
  have hb := congrArg (fun x : Int64 => x.toBitVec.toNat) hk
  simp only [e, bits_mul, bits_min] at hb
  have hz : y.toBitVec.toNat = 0 ∨ y.toBitVec.toNat = 2 ^ 63 := by omega
  exact hz.elim (fun h => h2 (bits_inj (h.trans (by decide)))) (fun h => h1 (bits_inj (h.trans bits_min.symm)))

theorem lowZero_iff (t : Nat) (x : Int64) : (Fn.lowZero t).den x true ↔ x.toBitVec.toNat % 2 ^ t = 0 := by
  show (Except.ok (lowBits t x) : Except String Bool) = .ok true ↔ _
  simp [lowBits, Nat.and_two_pow_sub_one_eq_mod]

/-- **`(×a)° (×a) = lowZero(tz(a))?`**: `f° f` is the coreflexive on `ran(f)`, and `ran(×a)` is the multiples of
    `2^tz(a)`, for `a` neither `0` nor `0N`. -/
theorem ran_mul (h : Eval.ewType .mul .long .long = some .long) (a : Int64) (h0 : a ≠ 0) (hn : a ≠ Int64.minValue) :
    (conv (fn (.sect (t := .long) (u := .long) false .mul h a))).den ≫ (fn (.sect (t := .long) (u := .long) false .mul h a)).den =
      (Fn.test (.lowZero (tz a))).den := by
  obtain ⟨ht, w, ha⟩ := tz_spec h0
  refine hom_ext fun x y => ⟨fun ⟨k, hx, hy⟩ => ?_, fun ⟨e, hc⟩ => ?_⟩
  · have hx' : elem .mul h k a = .ok x := hx
    have hy' : elem .mul h k a = .ok y := hy
    rw [elem_mul h k a hn] at hx' hy'
    cases hx'; cases hy'
    exact ⟨rfl, (lowZero_iff _ _).2 (mul_low ht ha k)⟩
  · subst e
    obtain ⟨k, hk⟩ := mul_onto ha ((lowZero_iff _ _).1 hc)
    have e : elem .mul h k a = .ok x := by rw [elem_mul h k a hn, hk]
    exact ⟨k, e, e⟩

/-- `(×2)`, the map whose range is the evens. -/
def dbl : Fn .long .long := .sect (u := .long) false .mul rfl 2

/-- The rows of `R` whose key is even: `(×2)° (×2) R`. -/
def evens {B : Obj} (R : Prog .long B) : Prog .long B := comp (comp (conv (fn dbl)) (fn dbl)) R

theorem evens_den {B : Obj} (R : Prog .long B) :
    (evens R).den = corefl (fun x : Int64 => x.toBitVec.toNat % 2 = 0) ≫ R.den :=
  congrArg (· ≫ R.den) ((ran_mul rfl 2 (by decide) (by decide)).trans
    (congrArg (corefl (A := Ob .long)) (funext fun x => propext (lowZero_iff (tz 2) x))))

/-- `=` on longs: its `elem` is `true` exactly at `a`. -/
theorem elem_eq (h : Eval.ewType .eq .long .long = some .boolean) (x a : Int64) : elem .eq h x a = .ok true ↔ x = a := by
  rw [Ew.elem_long_cmp rfl h, Except.ok.injEq]
  simp (config := { decide := true }) only [Kernel.Ew.cmpStep, signed_i64, beq_iff_eq, if_true, if_false]
  exact (compare_iff x a).2.1

/-- **`R v a` is `R ≫ o ≫ â`**, for the relation `o` the comparison's `elem` decides into `a`. -/
theorem valCmp_den_of {A : Obj} {v : Prim.Dyadic} {o : Ob .long ⟶ Ob .long} (h : Eval.ewType v .long .long = some .boolean)
    (R : Prog A .long) (a : Int64) (ho : ∀ x, elem v h x a = .ok true ↔ o x a) :
    (valCmp v R a h).den = R.den ≫ o ≫ corefl (· = a) := by
  show (R.den ≫ (Fn.test (.sect (u := .long) false v h a)).den) ≫ Verb.cst a = _
  rw [Cat.assoc]
  refine congrArg (R.den ≫ ·) (hom_ext fun x y => ⟨fun ⟨_, ⟨e, hc⟩, hy⟩ => ?_, fun ⟨_, hx, e, hc⟩ => ?_⟩)
  · subst e; subst hy; exact ⟨_, (ho x).1 hc, rfl, rfl⟩
  · subst e; subst hc; exact ⟨x, ⟨rfl, (ho x).2 hx⟩, rfl⟩

/-- **`a v R` is `â ≫ o ≫ R`**, `o` read off the mirrored comparison. -/
theorem keyCmp_den_of {B : QAtomicType} {v : Prim.Dyadic} {o : Ob .long ⟶ Ob .long}
    (h : Eval.ewType (mirror v) .long .long = some .boolean) (R : Prog .long (.atom B)) (a : Int64)
    (ho : ∀ x, elem (mirror v) h x a = .ok true ↔ o a x) :
    (keyCmp v a R h).den = corefl (· = a) ≫ o ≫ R.den := by
  show (valCmp (mirror v) (conv R) a h).den° = _
  rw [valCmp_den_of (o := fun x y => o y x) h (conv R) a ho]
  refine hom_ext fun x y => ⟨fun ⟨c, hR, d, hd, e, hc⟩ => ?_, fun ⟨d, ⟨e, hc⟩, c, hd, hR⟩ => ?_⟩
  · subst e; subst hc; exact ⟨d, ⟨rfl, rfl⟩, c, hd, hR⟩
  · subst e; subst hc; exact ⟨c, hR, x, hd, rfl, rfl⟩

/-- `R v a` denotes `R ≫ (v) ≫ â` at the four orders. -/
theorem valCmp_den {A : Obj} {v : Prim.Dyadic} (hv : v = .lt ∨ v = .le ∨ v = .gt ∨ v = .ge)
    (h : Eval.ewType v .long .long = some .boolean) (R : Prog A .long) (a : Int64) :
    (valCmp v R a h).den = R.den ≫ ord v ≫ corefl (· = a) :=
  valCmp_den_of h R a (elem_ord hv h · a)

/-- `a v R` denotes `â ≫ (v) ≫ R` at the four orders. -/
theorem keyCmp_den {B : QAtomicType} {v : Prim.Dyadic} (hv : v = .lt ∨ v = .le ∨ v = .gt ∨ v = .ge)
    (h : Eval.ewType (mirror v) .long .long = some .boolean) (R : Prog .long (.atom B)) (a : Int64) :
    (keyCmp v a R h).den = corefl (· = a) ≫ ord v ≫ R.den := by
  rcases hv with rfl | rfl | rfl | rfl <;>
    exact keyCmp_den_of (o := ord _) h R a (elem_ord (by simp [mirror]) h · a)

theorem valCmp_eq_den {A : Obj} (h : Eval.ewType .eq .long .long = some .boolean) (R : Prog A .long) (a : Int64) :
    (valCmp .eq R a h).den = R.den ≫ (fun x y : Int64 => x = y) ≫ corefl (· = a) :=
  valCmp_den_of h R a (elem_eq h · a)

theorem valCmp_ne_den {A : Obj} (h : Eval.ewType .ne .long .long = some .boolean) (R : Prog A .long) (a : Int64) :
    (valCmp .ne R a h).den = R.den ≫ (fun x y : Int64 => x ≠ y) ≫ corefl (· = a) :=
  valCmp_den_of h R a (elem_ne h · a)

theorem keyCmp_eq_den {B : QAtomicType} (h : Eval.ewType (mirror .eq) .long .long = some .boolean)
    (R : Prog .long (.atom B)) (a : Int64) :
    (keyCmp .eq a R h).den = corefl (· = a) ≫ (fun x y : Int64 => x = y) ≫ R.den :=
  keyCmp_den_of h R a fun x => (elem_eq h x a).trans eq_comm

theorem keyCmp_ne_den {B : QAtomicType} (h : Eval.ewType (mirror .ne) .long .long = some .boolean)
    (R : Prog .long (.atom B)) (a : Int64) :
    (keyCmp .ne a R h).den = corefl (· = a) ≫ (fun x y : Int64 => x ≠ y) ≫ R.den :=
  keyCmp_den_of h R a fun x => (elem_ne h x a).trans ne_comm

section Checks
open Cmp

private def D (ks vs : List Int64) : Except String (Rel .long .long) :=
  return ⟨vs.length, ← Arr.of .long _ (.vector .long ks.length (.bytes (packLongs ks)) none) "D",
    ← Arr.of .long _ (.vector .long vs.length (.bytes (packLongs vs)) none) "D"⟩
private def rows {A B : QAtomicType} (P : Except String (Prog (.atom A) (.atom B))) : Option (List (El A × El B)) :=
  (do pure (← (← P).run).toRel.toList : Except String _).toOption

#guard rows (do pure (selKey 2 (rel (← D [1, 2, 3] [10, 20, 30])))) == some [(3, 30)]
#guard rows (do pure (selVal (rel (← D [1, 2, 3] [10, 20, 30])) 25)) == some [(1, 10), (2, 20)]
#guard rows (do pure ((2 : Int64) < rel (← D [1, 2, 3] [10, 20, 30]))) == some [(2, 30)]
#guard rows (do pure (rel (← D [1, 2, 3] [10, 20, 30]) < (25 : Int64))) == some [(1, 25), (2, 25)]
#guard rows (do pure (rel (← D [1, 2, 3] [10, 20, 30]) ≤ (20 : Int64))) == some [(1, 20), (2, 20)]
#guard rows (do pure (rel (← D [1, 2, 3] [10, 20, 30]) ≠ (20 : Int64))) == some [(1, 20), (3, 20)]
#guard rows (do pure ((2 : Int64) = rel (← D [1, 2, 3] [10, 20, 30]))) == some [(2, 20)]
#guard rows (do pure (comp (fn (.test (.sect (t := .long) (u := .long) false .gt rfl 1))) (rel (← D [1, 2, 3] [10, 20, 30])))) ==
  some [(2, 20), (3, 30)]
#guard rows (do pure (comp (comp (pair (rel (← D [0, 1, 2] [10, 20, 30])) (rel (← D [0, 1, 2] [11, 20, 29])))
  (fn (.test (.dy .lt rfl)))) (fn .fst))) == some [(0, 10)]
#guard ((1 : Int64) < 2) && !((2 : Int64) ≤ 1) -- Lean's own reading still elaborates
#guard rows (do pure (evens (rel (← D [1, 2, 3, 4] [10, 20, 30, 40])))) == some [(2, 20), (4, 40)]
private def mulB (a : Int64) : Prog .long .long := fn (.sect (u := .long) false .mul rfl a)
#guard rows (do pure (comp (comp (conv (mulB 12)) (mulB 12)) (rel (← D [3, 4, 8, 16] [1, 2, 3, 4])))) == some [(4, 2), (8, 3), (16, 4)]
#guard rows (do pure (comp (comp (conv (mulB 3)) (mulB 3)) (rel (← D [3, 4] [1, 2])))) == some [(3, 1), (4, 2)]
#guard rows (do pure (comp (comp (conv (mulB 0)) (mulB 0)) (rel (← D [0, 4] [1, 2])))) == none
#guard rows (do pure (comp (comp (conv (mulB Int64.minValue)) (mulB Int64.minValue)) (rel (← D [0, 4] [1, 2])))) == none
#guard rows (do pure (comp (comp (conv (mulB 2)) (mulB 3)) (rel (← D [0, 4] [1, 2])))) == none
#guard rows (do pure (comp (conv (mulB 2)) (rel (← D [0, 4] [1, 2])))) == none

end Checks

end Prog

#print axioms Prog.enum_sound
#print axioms Prog.lastBy_den
#print axioms Prog.selectBy_den
#print axioms Prog.index_den
#print axioms Prog.run_sound
#print axioms Prog.ej_den
#print axioms Prog.dict_den
#print axioms Prog.til_den
#print axioms Prog.mon_den
#print axioms Prog.val_den
#print axioms Prog.posL_iff
#print axioms Prog.ej_prog
#print axioms Prog.dict_prog
#print axioms Prog.til_prog
#print axioms Prog.mon_prog
#print axioms Prog.val_prog
#print axioms Prog.enum_prog
#print axioms Prog.in_den
#print axioms Prog.find_den
#print axioms Prog.index_prog
#print axioms Prog.posL_pos
#print axioms Prog.length_cata
#print axioms Prog.nonNul_den
#print axioms Prog.elem_ord
#print axioms Prog.selKey_den
#print axioms Prog.selVal_den
#print axioms Prog.test_sect_dom
#print axioms Prog.ran_mul
#print axioms Prog.evens_den
#print axioms Prog.valCmp_den
#print axioms Prog.keyCmp_den
#print axioms Prog.valCmp_eq_den
#print axioms Prog.valCmp_ne_den
#print axioms Prog.keyCmp_eq_den
#print axioms Prog.keyCmp_ne_den
#print axioms Prog.lam_key
#print axioms Prog.lamEst_iff
#print axioms Prog.lastBy_grp
#print axioms Prog.selectBy_grp
#print axioms Prog.distinct_den
#print axioms Prog.countBy_den
#print axioms Prog.size_den
#print axioms Prog.over_den
#print axioms Prog.avg_den
#print axioms Prog.segs_eq
#print axioms Prog.foldOp_comm
#print axioms Prog.avg_val
#print axioms Prog.avg_prog
#print axioms Prog.iasc_den
#print axioms Prog.idesc_den
#print axioms Prog.rank_den
#print axioms Prog.asc_den
#print axioms Prog.desc_den
#print axioms Prog.xasc_den
#print axioms Prog.grade_sound_long
#print axioms Prog.grade_prog
#print axioms Prog.xsort_prog
#print axioms Prog.bin_R6
#print axioms Prog.aj_R7
#print axioms Prog.wj1_R8
#print axioms Prog.wj_R8
#print axioms Prog.bin_prog
#print axioms Prog.aj_prog
#print axioms Prog.wj1_prog
#print axioms Prog.wj_prog
#print axioms Prog.keys_miss
#print axioms Prog.lastEst_some
#print axioms Prog.lastBy_link
#print axioms Prog.selectBy_link
#print axioms Prog.rank_prog

end LeetQ.Rel
