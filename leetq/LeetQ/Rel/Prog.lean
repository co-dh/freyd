/-
  RelRep design B: a k verb is a term `Prog` over the executable Rel primitives (design §1: step 1
  P1–P6, P6′, P13; step 3 P8–P12, P16, `Λ` carried as its keys beside a `Parted`, boxed only at output). `den P` is its spec in `RelSet`, `run P` executes it one `Alg.*` kernel per node.
  `run_sound`: `run P = ok R → R.Holds = den P`, from one lemma per node; a kernel node whose kernel has
  no theorem yet (`comp`, `∩`, `∪`, `𝟘`, `⊤`, `mapVal`, `pair`, `Ew.val`) contributes its law to `Sound P`.
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
  let v ← Arr.ofPart .long P.n (← pick .long x.part i) "list(x)"
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
  let some r := Ops.countBy F.2.2 | throw "count by: no kernel"
  pure ⟨F.1, F.2.1, ← Arr.ofPart .long F.1 r.part "count by"⟩

end Alg

/-- An atomic type as an object of `RelSet`. -/
abbrev Ob (t : QAtomicType) : RelSet.{0} := ⟨El t⟩

/-- A position read as a long: the key `til n` of a list. -/
abbrev posL : Idx ⟶ Ob .long := graph Int64.ofNat

/-- A verb's program: one constructor per executable primitive, the leaves stored data. -/
inductive Prog : QAtomicType → QAtomicType → Type
  /-- a stored relation, a dict -/
  | rel {A B : QAtomicType} (R : Rel A B) : Prog A B
  /-- a list `x : til n → t` -/
  | arr {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long t
  /-- `!n = 𝟙(til n)` -/
  | til (n : Nat) : Prog .long .long
  | idU {t : QAtomicType} {m : Nat} (U : Arr t m) : Prog t t
  | zero {A B : QAtomicType} : Prog A B
  | top {A B : QAtomicType} {ma mb : Nat} (Ua : Arr A ma) (Ub : Arr B mb) : Prog A B
  | comp {A B C : QAtomicType} : Prog A B → Prog B C → Prog A C
  | conv {A B : QAtomicType} : Prog A B → Prog B A
  | inter {A B : QAtomicType} : Prog A B → Prog A B → Prog A B
  | union {A B : QAtomicType} : Prog A B → Prog A B → Prog A B
  /-- `R ≫ graph(f)`, `f` what the kernel `op` computes -/
  | map {K t : QAtomicType} (op : UInt8) (f : El t → El t) : Prog K t → Prog K t
  /-- `⟨R, S⟩ ≫ graph(v)`: the pair (P13) under a dyadic map (P6′); `⟨R,S⟩` alone is no `Rel` -/
  | dy {K t u rt : QAtomicType} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) :
      Prog K t → Prog K u → Prog K rt
  /-- `Λ(R) ≫ ∋` (P8, P9): `Λ` makes the keys-and-`Parted` carrier, `∋` flattens it -/
  | mem {A B : QAtomicType} : Prog A B → Prog A B
  /-- `Λ(R) ≫ est(≤)`, `desc`: `est(≥)` (P8, P10) -/
  | extr {A : QAtomicType} (desc : Bool) : Prog A .long → Prog A .long
  /-- `Λ(G) ≫ enum ≫ list(x) ≫ ⦇e,f⦈` (P8, P11, P12), `G` keys against positions, `op` the kernel of `f` -/
  | fold {A : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64) (x : Arr .long n) :
      Prog A .long → Prog A .long
  /-- `enum(dom(x ≫ !1b°))` (P11): the set bits of `x`, ascending, keyed by `til m` -/
  | enum {n : Nat} (x : Arr .boolean n) : Prog .long .long
  /-- `R ≫ corNeg(C)`, the anti-join (P16) -/
  | anti {A B : QAtomicType} : Prog A B → Prog B B → Prog A B
  /-- `R ≫ !e`, the constant map: the one node that changes the value type (`miss`, `χ`) -/
  | cst {K t u : QAtomicType} (e : El u) : Prog K t → Prog K u
  /-- `dom R = 𝟙 ∩ (R ≫ R°)`; `ran R` is `dom R°` -/
  | dom {A B : QAtomicType} : Prog A B → Prog A A
  /-- `enum` of the positions `j < n` whose long is in `dom C` (P11 over a computed coreflexive) -/
  | enumC (n : Nat) : Prog .long .long → Prog .long .long
  /-- `Λ(G ≫ pos) ≫ enum ≫ length` (P8, P11, P12): each key's count; no `Coc.Over` counts -/
  | count {A : QAtomicType} : Prog A .long → Prog A .long

namespace Prog

/-- The spec: the relation the term denotes. -/
def den : {A B : QAtomicType} → Prog A B → (Ob A ⟶ Ob B)
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
  | _, _, map _ f P => P.den ≫ graph f
  | _, _, dy v h P Q => rpair P.den Q.den ≫ ofExcept fun p => elem v h p.1 p.2
  | _, B, mem P => Λ P.den ≫ ∋ (Ob B)
  | _, _, extr false P => Λ P.den ≫ est (fun a b : Int64 => a ≤ b)
  | _, _, extr true P => Λ P.den ≫ est (fun a b : Int64 => a ≥ b)
  | _, _, fold _ e f x G => Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold e f
  | _, _, enum x => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (x.rel ≫
      (Verb.cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys ∧ (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, anti P C => P.den ≫ Verb.corNeg C.den
  | _, _, cst e P => P.den ≫ Verb.cst e
  | _, _, dom P => Verb.dom P.den
  | _, _, enumC n C => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (corefl (· < n) ≫ posL ≫ C.den))) ys ∧
      (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, count G => Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.length ≫ graph Int64.ofNat

/-- `til n` as a key, refused past `USize`, where `tilLongs` would wrap. -/
def tilKey (n : Nat) : Except String (Arr .long n) :=
  if n < USize.size then Struct.til n else throw s!"til {n}: past USize"

/-- `enumC`'s kernel: `til n in C`'s keys (`Find.in`), then `Find.where` keyed by `til m`. -/
def enumIn (n : Nat) (C : Rel .long .long) : Except String (Rel .long .long) := do
  let w ← Find.where (← Find.«in» (← tilKey n) C.key); pure ⟨w.1, ← tilKey w.1, w.2⟩

/-- The literal interpreter: one kernel per node. -/
def run : {A B : QAtomicType} → Prog A B → Except String (Rel A B)
  | _, _, rel R => pure R
  | _, _, arr (n := n) x => do pure ⟨n, ← tilKey n, x⟩
  | _, _, til n => do pure (Alg.idU (← tilKey n))
  | _, _, idU U => pure (Alg.idU U)
  | _, _, zero => Alg.zero
  | _, _, top Ua Ub => Alg.top Ua Ub
  | _, _, comp P Q => do Alg.comp (← P.run) (← Q.run)
  | _, _, conv P => do Alg.conv (← P.run)
  | _, _, inter P Q => do Alg.inter (← P.run) (← Q.run)
  | _, _, union P Q => do Alg.union (← P.run) (← Q.run)
  | _, _, map op _ P => do Alg.mapVal op (← P.run)
  | _, _, dy (rt := rt) v _ P Q => do
    let T ← Alg.pair (← P.run) (← Q.run)
    pure ⟨T.n, T.key, ← Ew.val v rt T.fst T.snd⟩
  | _, _, mem P => do Alg.lamMem (← P.run)
  | _, _, extr d P => do Alg.lamEst d (← P.run)
  | _, _, fold op _ _ x G => do Alg.lamFold op x (← G.run)
  | _, _, enum x => do let w ← Find.where x; pure ⟨w.1, ← tilKey w.1, w.2⟩
  | _, _, anti P C => do Alg.antiJoin (← P.run) (← C.run)
  | _, _, cst e P => do Alg.cstVal e (← P.run)
  | _, _, dom P => do Alg.dom (← P.run)
  | _, _, enumC n C => do enumIn n (← C.run)
  | _, _, count G => do Alg.lamCount (← G.run)

/-- The kernel laws a term's run needs and no theorem gives yet, one per kernel node; the stored leaves,
    `til`, `idU` and `°` need none (`arr_sound` … `conv_sound`). -/
def Sound : {A B : QAtomicType} → Prog A B → Prop
  | _, _, rel _ | _, _, arr _ | _, _, til _ | _, _, idU _ => True
  | A, B, zero => ∀ T : Rel A B, Alg.zero = .ok T → @Eq (Ob A ⟶ Ob B) T.Holds 𝟘
  | A, B, top Ua Ub => ∀ T : Rel A B, Alg.top Ua Ub = .ok T → @Eq (Ob A ⟶ Ob B) T.Holds (Ua.rel° ≫ ⊤ ≫ Ub.rel)
  | _, _, conv P => P.Sound
  | A, C, comp (B := B) P Q => P.Sound ∧ Q.Sound ∧ ∀ (R : Rel A B) (S : Rel B C) T, Alg.comp R S = .ok T →
      @Eq (Ob A ⟶ Ob C) T.Holds (@Cat.comp _ _ (Ob A) (Ob B) (Ob C) R.Holds S.Holds)
  | A, B, inter P Q => P.Sound ∧ Q.Sound ∧ ∀ R S T : Rel A B, Alg.inter R S = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (R.Holds ∩ S.Holds)
  | A, B, union P Q => P.Sound ∧ Q.Sound ∧ ∀ R S T : Rel A B, Alg.union R S = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (R.Holds ∪ S.Holds)
  | K, t, map op f P => P.Sound ∧ ∀ R T : Rel K t, Alg.mapVal op R = .ok T →
      @Eq (Ob K ⟶ Ob t) T.Holds ((R.Holds : Ob K ⟶ Ob t) ≫ graph f)
  | K, _, dy (t := t) (u := u) (rt := rt) v h P Q => P.Sound ∧ Q.Sound ∧
      (∀ (R : Rel K t) (S : Rel K u) T, Alg.pair R S = .ok T → ∀ k a b, T.Holds k a b ↔ R.Holds k a ∧ S.Holds k b) ∧
      ∀ n (x : Arr t n) (y : Arr u n) V, Ew.val v rt x y = .ok V → Ew.ValSpec v h x y V
  | A, B, mem P => P.Sound ∧ ∀ R T : Rel A B, Alg.lamMem R = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds (Λ (R.Holds : Ob A ⟶ Ob B) ≫ ∋ (Ob B))
  | A, _, extr d P => P.Sound ∧ ∀ R T : Rel A .long, Alg.lamEst d R = .ok T →
      @Eq (Ob A ⟶ Ob .long) T.Holds (extr d (rel R)).den
  | A, _, fold op e f x G => G.Sound ∧ ∀ R T : Rel A .long, Alg.lamFold op x R = .ok T →
      @Eq (Ob A ⟶ Ob .long) T.Holds (fold op e f x (rel R)).den
  | _, _, enum (n := n) _ => n < USize.size
  | A, B, anti P C => P.Sound ∧ C.Sound ∧ ∀ (R : Rel A B) (S : Rel B B) T, Alg.antiJoin R S = .ok T →
      @Eq (Ob A ⟶ Ob B) T.Holds ((R.Holds : Ob A ⟶ Ob B) ≫ Verb.corNeg S.Holds)
  | K, u, cst (t := t) e P => P.Sound ∧ ∀ (R : Rel K t) (T : Rel K u), Alg.cstVal e R = .ok T →
      @Eq (Ob K ⟶ Ob u) T.Holds ((R.Holds : Ob K ⟶ Ob t) ≫ Verb.cst e)
  | A, _, dom (B := B) P => P.Sound ∧ ∀ (R : Rel A B) T, Alg.dom R = .ok T →
      @Eq (Ob A ⟶ Ob A) T.Holds (Verb.dom (R.Holds : Ob A ⟶ Ob B))
  | _, _, enumC n C => C.Sound ∧ ∀ R T : Rel .long .long, enumIn n R = .ok T →
      @Eq (Ob .long ⟶ Ob .long) T.Holds (enumC n (rel R)).den
  | A, _, count G => G.Sound ∧ ∀ R T : Rel A .long, Alg.lamCount R = .ok T →
      @Eq (Ob A ⟶ Ob .long) T.Holds (count (rel R)).den

/-! ## Node soundness -/

/-- A list keyed by `til n` holds `posL° ≫ x`. -/
theorem arr_sound {t : QAtomicType} {n : Nat} (x : Arr t n) {k : Arr .long n} (h : tilKey n = .ok k) :
    ((⟨n, k, x⟩ : Rel .long t).Holds : Ob .long ⟶ Ob t) = posL° ≫ x.rel := by
  unfold tilKey at h; split at h
  · rw [mk_rel, til_rel (by assumption) h]
    exact hom_ext fun a b => ⟨fun ⟨j, ⟨_, ⟨rfl, _⟩, e⟩, hx⟩ => ⟨j, e, hx⟩,
      fun ⟨j, e, hx⟩ => ⟨j, ⟨j, ⟨rfl, ((rel_iff x j b).1 hx).1⟩, e⟩, hx⟩⟩
  · cases h

/-- `!n` holds `𝟙` on `til n`. -/
theorem til_sound {n : Nat} {k : Arr .long n} (h : tilKey n = .ok k) :
    ((Alg.idU k).Holds : Ob .long ⟶ Ob .long) = posL° ≫ corefl (· < n) ≫ posL := by
  unfold tilKey at h; split at h
  · rw [show Alg.idU k = ⟨n, k, k⟩ from rfl, mk_rel, til_rel (by assumption) h]
    exact hom_ext fun a b => ⟨fun ⟨j, ⟨_, ⟨rfl, hj⟩, ea⟩, ⟨_, ⟨rfl, _⟩, eb⟩⟩ => ⟨j, ea, j, ⟨rfl, hj⟩, eb⟩,
      fun ⟨j, ea, _, ⟨rfl, hj⟩, eb⟩ => ⟨j, ⟨j, ⟨rfl, hj⟩, ea⟩, ⟨j, ⟨rfl, hj⟩, eb⟩⟩⟩
  · cases h

/-- `𝟙` on `U` holds `ran U`. -/
theorem idU_sound {t : QAtomicType} {m : Nat} (U : Arr t m) :
    ((Alg.idU U).Holds : Ob t ⟶ Ob t) = Verb.ran U.rel := by
  rw [show Alg.idU U = ⟨m, U, U⟩ from rfl, mk_rel]
  refine hom_ext fun a b => ⟨fun ⟨j, ha, hb⟩ => ⟨?_, j, ha, hb⟩, fun ⟨e, j, ha, hb⟩ => ⟨j, ha, hb⟩⟩
  obtain ⟨_, ea⟩ := (rel_iff U j a).1 ha; obtain ⟨_, eb⟩ := (rel_iff U j b).1 hb
  exact ea.symm.trans eb

/-- `R°` holds the converse (`conv_holds`). -/
theorem conv_sound {A B : QAtomicType} {R : Rel A B} {S : Rel B A} (h : Alg.conv R = .ok S) :
    (S.Holds : Ob B ⟶ Ob A) = ((R.Holds : Ob A ⟶ Ob B)° : Ob B ⟶ Ob A) :=
  hom_ext fun b a => Alg.conv_holds h a b

/-- `⟨R, S⟩ ≫ graph(v)` holds its spec, from the pair's law and the kernel's `Ew.ValSpec` (`val_rel`). -/
theorem dy_sound {K t u rt : QAtomicType} {v : Prim.Dyadic} {h : Eval.ewType v t u = some rt}
    {R : Rel K t} {S : Rel K u} {T : Alg.Tab K t u} {V : Arr rt T.n}
    (hp : ∀ k a b, T.Holds k a b ↔ R.Holds k a ∧ S.Holds k b) (hs : Ew.ValSpec v h T.fst T.snd V) :
    ((⟨T.n, T.key, V⟩ : Rel K rt).Holds : Ob K ⟶ Ob rt) =
      rpair (R.Holds : Ob K ⟶ Ob t) (S.Holds : Ob K ⟶ Ob u) ≫ ofExcept fun p => elem v h p.1 p.2 := by
  rw [mk_rel, Verb.val_rel hs]
  refine hom_ext fun k c => ⟨fun ⟨j, hk, p, ⟨ha, hb⟩, e⟩ => ⟨p, (hp k p.1 p.2).1 ?_, e⟩,
    fun ⟨p, hab, e⟩ => ?_⟩
  · obtain ⟨hj, ek⟩ := (rel_iff _ j k).1 hk; obtain ⟨_, ea⟩ := (rel_iff _ j _).1 ha
    obtain ⟨_, eb⟩ := (rel_iff _ j _).1 hb
    exact ⟨⟨j, hj⟩, ek, ea, eb⟩
  · obtain ⟨i, ek, ea, eb⟩ := (hp k p.1 p.2).2 hab
    exact ⟨i.1, (rel_iff _ _ _).2 ⟨i.2, ek⟩, p, ⟨(rel_iff _ _ _).2 ⟨i.2, ea⟩, (rel_iff _ _ _).2 ⟨i.2, eb⟩⟩, e⟩

/-- `&x` runs to its spec: `Find.where` keyed by `til m` holds `enum(dom(x ≫ !1b°))` (`where_rel`). -/
theorem enum_sound {n : Nat} (x : Arr .boolean n) (hn : n < USize.size) {R : Rel .long .long}
    (h : (enum x).run = .ok R) : (R.Holds : Ob .long ⟶ Ob .long) = (enum x).den := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  rename_i w hw
  split at h
  · cases h
  cases h
  obtain ⟨⟨ys, hy⟩, hall⟩ := where_rel hn hw
  rw [arr_sound w.2 (by assumption)]
  exact hom_ext fun a b => ⟨fun ⟨j, ea, hr⟩ => ⟨j, ea, ys, hy, by rw [← hall ys hy]; exact hr⟩,
    fun ⟨j, ea, ys', hy', hr⟩ => ⟨j, ea, by rw [hall ys' hy']; exact hr⟩⟩

/-- **A sound term runs to its spec**: the answer of `run P` holds `den P`. -/
theorem run_sound : ∀ {A B : QAtomicType} (P : Prog A B) {R : Rel A B}, P.Sound → P.run = .ok R →
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
    unfold Sound at hs; obtain ⟨sP, sQ, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound Q sQ (by assumption)]; rfl
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
  | _, _, map _ _ P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, dy _ _ P Q, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sQ, hp, hv⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    cases h
    rw [dy_sound (hp _ _ _ (by assumption)) (hv _ _ _ _ (by assumption)), run_sound P sP (by assumption),
      run_sound Q sQ (by assumption)]; rfl
  | _, _, mem P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, extr d P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; cases d <;> simp only [den] <;> rw [run_sound P sP (by assumption)]
  | _, _, fold _ _ _ _ G, _, hs, h => by
    unfold Sound at hs; obtain ⟨sG, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; simp only [den]; rw [run_sound G sG (by assumption)]
  | _, _, enum x, _, hs, h => enum_sound x hs h
  | _, _, anti P C, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, sC, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    split at h
    · cases h
    rw [hl _ _ _ h, run_sound P sP (by assumption), run_sound C sC (by assumption)]; rfl
  | _, _, cst _ P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, dom P, _, hs, h => by
    unfold Sound at hs; obtain ⟨sP, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h, run_sound P sP (by assumption)]; rfl
  | _, _, enumC _ C, _, hs, h => by
    unfold Sound at hs; obtain ⟨sC, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; simp only [den]; rw [run_sound C sC (by assumption)]
  | _, _, count G, _, hs, h => by
    unfold Sound at hs; obtain ⟨sG, hl⟩ := hs
    simp only [run, bind, Except.bind] at h; split at h
    · cases h
    rw [hl _ _ h]; simp only [den]; rw [run_sound G sG (by assumption)]

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
def mon {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) : Prog .long t := map op f (arr x)

theorem mon_den {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) :
    (mon op f x).den = posL° ≫ (x.rel ≫ graph f) :=
  hom_ext fun _ _ => ⟨fun ⟨b, ⟨j, ea, hx⟩, eb⟩ => ⟨j, ea, b, hx, eb⟩, fun ⟨j, ea, b, hx, eb⟩ => ⟨b, ⟨j, ea, hx⟩, eb⟩⟩

/-- `x v y = ⟨x, y⟩ ≫ (v)` (§11.1 dyadic): `val_rel`'s right side, read through the key. -/
def val {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (h : Eval.ewType v t u = some rt) (x : Arr t n)
    (y : Arr u n) : Prog .long rt := dy v h (arr x) (arr y)

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

/-- `select f x by k`: `grpL(k) ≫ list(x) ≫ ⦇e,f⦈`, `grpL(k) = Λ(k°) ≫ enum` (`overBy_rel`). -/
def selectBy {K : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64) (k : Arr K n)
    (x : Arr .long n) : Prog K .long := fold op e f x (conv (arr k))

theorem selectBy_den {K : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64)
    (k : Arr K n) (x : Arr .long n) :
    (selectBy op e f k x).den = Λ ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold e f :=
  rfl

/-- `x@y` inside the range: `y ≫ x` through the positions (the `miss` fill is not a node yet). -/
def index {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) : Prog .long t := comp (arr y) (arr x)

theorem index_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) :
    (index x y).den = posL° ≫ y.rel ≫ posL° ≫ x.rel :=
  hom_ext fun _ _ => ⟨fun ⟨b, ⟨j, ea, hy⟩, hx⟩ => ⟨j, ea, b, hy, hx⟩, fun ⟨j, ea, b, hy, hx⟩ => ⟨b, ⟨j, ea, hy⟩, hx⟩⟩

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
theorem ej_prog {nl nr : Nat} (l : Arr .long nl) (r : Arr .long nr) {R : Rel .long .long}
    (h : (ej l r).run = .ok R) (hs : (ej l r).Sound) :
    (R.Holds : Ob .long ⟶ Ob .long) = posL° ≫ ix (l.toList.map ([·])) ≫ (ix (r.toList.map ([·])))° ≫ posL := by
  rw [run_sound _ hs h, ej_den, Verb.ix_map, Verb.ix_map]
  exact hom_ext fun _ _ => ⟨fun ⟨j, ea, c, hl, j', hr, eb⟩ => ⟨j, ea, [c], ⟨c, hl, rfl⟩, j', ⟨c, hr, rfl⟩, eb⟩,
    fun ⟨j, ea, _, ⟨c, hl, rfl⟩, j', ⟨_, hr, e⟩, eb⟩ => ⟨j, ea, c, hl, j', by cases e; exact hr, eb⟩⟩

/-- `x!y` runs to `mk_rel`'s right side. -/
theorem dict_prog {k v : QAtomicType} {n : Nat} (x : Arr k n) (y : Arr v n) {R : Rel k v}
    (h : (dict x y).run = .ok R) (hs : (dict x y).Sound) : (R.Holds : Ob k ⟶ Ob v) = x.rel° ≫ y.rel :=
  (run_sound _ hs h).trans (dict_den x y)

/-- `!n` runs to `til_rel`'s right side. -/
theorem til_prog {n : Nat} (hn : n ≤ 2 ^ 64) {R : Rel .long .long} (h : (til n).run = .ok R) (hs : (til n).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = corefl (· < n) ≫ graph Int64.ofNat :=
  (posL_iff fun _ _ ⟨_, ⟨e, hi⟩, _⟩ => by subst e; exact Nat.lt_of_lt_of_le hi hn).1 ((run_sound _ hs h).trans (til_den n))

/-- `f x` runs to `mon_rel`'s right side. -/
theorem mon_prog {t : QAtomicType} {n : Nat} (op : UInt8) (f : El t → El t) (x : Arr t n) (hn : n ≤ 2 ^ 64)
    {R : Rel .long t} (h : (mon op f x).run = .ok R) (hs : (mon op f x).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob t) = x.rel ≫ graph f :=
  (posL_iff fun i _ ⟨_, hx, _⟩ => Nat.lt_of_lt_of_le ((rel_iff x i _).1 hx).1 hn).1
    ((run_sound _ hs h).trans (mon_den op f x))

/-- `x v y` runs to `val_rel`'s right side. -/
theorem val_prog {t u rt : QAtomicType} {n : Nat} (v : Prim.Dyadic) (e : Eval.ewType v t u = some rt)
    (x : Arr t n) (y : Arr u n) (hn : n ≤ 2 ^ 64) {R : Rel .long rt} (h : (val v e x y).run = .ok R)
    (hs : (val v e x y).Sound) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob rt) = rpair x.rel y.rel ≫ ofExcept fun p => elem v e p.1 p.2 :=
  (posL_iff fun i _ ⟨_, ⟨hx, _⟩, _⟩ => Nat.lt_of_lt_of_le ((rel_iff x i _).1 hx).1 hn).1
    ((run_sound _ hs h).trans (val_den v e x y hn))

/-- `&x` runs to `where_rel`'s right side, for every list `enum` gives. -/
theorem enum_prog {n : Nat} (x : Arr .boolean n) {R : Rel .long .long} (h : (enum x).run = .ok R)
    (hs : (enum x).Sound) {ys}
    (hy : Verb.enum (Verb.cset (Verb.dom (x.rel ≫ (Verb.cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys) :
    corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob .long) = ix (CL.toList ys) ≫ graph Int64.ofNat := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  rename_i w hw
  split at h
  · cases h
  cases h
  rw [← (where_rel hs hw).2 ys hy]
  exact (posL_iff fun i _ hi => Nat.lt_trans ((rel_iff _ i _).1 hi).1 (tilKey_lt (by assumption))).1
    (arr_sound w.2 (by assumption))
/-! ## Verbs over `!e`, `dom`, `enumC`, `count` (design §2.2–2.5) -/

/-- `P ≫ (R ∪ (Q ≫ S))` is the union of its two branches as `run` composes them: `miss` and `χ` applied. -/
theorem comp_cup {A B C D : RelSet.{0}} (P : A ⟶ B) (R : B ⟶ D) (Q : B ⟶ C) (S : C ⟶ D) :
    (P ≫ R) ∪ ((P ≫ Q) ≫ S) = P ≫ (R ∪ (Q ≫ S)) :=
  hom_ext fun _ _ => ⟨fun h => Or.elim h (fun ⟨b, hp, hr⟩ => ⟨b, hp, Or.inl hr⟩)
      (fun ⟨c, ⟨b, hp, hq⟩, hs⟩ => ⟨b, hp, Or.inr ⟨c, hq, hs⟩⟩),
    fun ⟨b, hp, h⟩ => Or.elim h (fun hr => Or.inl ⟨b, hp, hr⟩) (fun ⟨c, hq, hs⟩ => Or.inr ⟨c, ⟨b, hp, hq⟩, hs⟩)⟩

/-- `x in y = x ≫ χ(ran y)`: the hit branch `x ≫ (ran y ≫ !1b)`, the miss branch the anti-join `≫ !0b`. -/
def «in» {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) : Prog .long .boolean :=
  union (comp (arr x) (cst true (idU y))) (cst false (anti (arr x) (idU y)))

theorem in_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) :
    («in» x y).den = (posL° ≫ x.rel) ≫ Verb.χ (Verb.ran y.rel) :=
  comp_cup _ _ _ _

/-- `x?y = y ≫ miss(Λ(x°) ≫ est(≤), n)`: the first position, `n` where `y` misses `x`. -/
def find {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) : Prog .long .long :=
  union (comp (arr y) (extr false (conv (arr x))))
    (cst (u := .long) (Int64.ofNat nx) (anti (arr y) (dom (extr false (conv (arr x))))))

theorem find_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr t ny) :
    (find x y).den = (posL° ≫ y.rel) ≫
      Verb.miss (Λ ((posL° ≫ x.rel)°) ≫ est (fun a b : Int64 => a ≤ b)) (Int64.ofNat nx) :=
  comp_cup _ _ _ _

/-- `x@y = y ≫ miss(pos ≫ x, e)`, `e` the null of `x`'s type: `index` with the fill. -/
def indexFill {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) : Prog .long t :=
  union (comp (arr y) (arr x)) (cst e (anti (arr y) (dom (arr x))))

theorem indexFill_den {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) :
    (indexFill x y e).den = (posL° ≫ y.rel) ≫ Verb.miss (posL° ≫ x.rel) e :=
  comp_cup _ _ _ _

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

theorem countBy_den {K : QAtomicType} {n : Nat} (k : Arr K n) :
    (countBy k).den = Λ ((posL° ≫ k.rel)° ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.length ≫ graph Int64.ofNat :=
  rfl

/-- The whole list as one group: the key `0` against every position, `(x ≫ !0)°`. -/
def whole {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long .long := conv (cst (u := .long) (0 : Int64) (arr x))

/-- `#x = ⦇0, succ⦈`, at the one key `0`. -/
def size {t : QAtomicType} {n : Nat} (x : Arr t n) : Prog .long .long := count (whole x)

theorem size_den {t : QAtomicType} {n : Nat} (x : Arr t n) :
    (size x).den = Λ (((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos) ≫ Verb.enum ≫
      ListRel.length ≫ graph Int64.ofNat :=
  rfl

/-- `f/x = ⦇e, f⦈` of the list, at the one key `0`. -/
def over {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64) (x : Arr .long n) :
    Prog .long .long := fold op e f x (whole x)

theorem over_den {n : Nat} (op : Kernel.Coc.Over) (e : Int64) (f : Int64 → Int64 → Int64) (x : Arr .long n) :
    (over op e f x).den = Λ ((((posL° ≫ x.rel) ≫ Verb.cst (B := Ob .long) (0 : Int64))° ≫ Verb.pos)) ≫
      Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold e f :=
  rfl

/-- `avg x = ⟨⦇0,+⦈, ⦇0,succ⦈⟩ ≫ (÷)`, one key `0`. -/
def avg {n : Nat} {rt : QAtomicType} (h : Eval.ewType .div .long .long = some rt) (x : Arr .long n) :
    Prog .long rt := dy .div h (over .add 0 (· + ·) x) (size x)

theorem avg_den {n : Nat} {rt : QAtomicType} (h : Eval.ewType .div .long .long = some rt) (x : Arr .long n) :
    (avg h x).den = rpair (over .add 0 (· + ·) x).den (size x).den ≫ ofExcept fun p => elem .div h p.1 p.2 :=
  rfl

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
#print axioms Prog.indexFill_den
#print axioms Prog.distinct_den
#print axioms Prog.countBy_den
#print axioms Prog.size_den
#print axioms Prog.over_den
#print axioms Prog.avg_den

end LeetQ.Rel
