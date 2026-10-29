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
  /-- `dom(G) ≫ Λ(G) ≫ enum ≫ list(x) ≫ ⦇e,f⦈` (P8, P11, P12), `G` keys against positions, `op` the kernel of `f`;
      `Λ` on `dom G` only, since a key that does not occur has no row (`Λ` alone gives it `e`) -/
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
  /-- `dom(G ≫ pos) ≫ Λ(G ≫ pos) ≫ enum ≫ length` (P8, P11, P12): each occurring key's count; no `Coc.Over` counts -/
  | count {A : QAtomicType} : Prog A .long → Prog A .long
  /-- `grade(⊴ₓ) = cst(til n) ≫ sort(⊴ₓ)` (P17): the stable grade of `x` under its type's strict order `lt`,
      `desc` flipping it; `x` keyed by `til n` -/
  | grade {t : QAtomicType} {n : Nat} (desc : Bool) (lt : El t → El t → Prop) (x : Arr t n) : Prog .long .long

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
  | _, _, fold _ e f x G => Verb.dom (G.den ≫ Verb.pos) ≫ Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.list x.rel ≫ Verb.fold e f
  | _, _, enum x => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (x.rel ≫
      (Verb.cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys ∧ (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, anti P C => P.den ≫ Verb.corNeg C.den
  | _, _, cst e P => P.den ≫ Verb.cst e
  | _, _, dom P => Verb.dom P.den
  | _, _, enumC n C => posL° ≫ fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (corefl (· < n) ≫ posL ≫ C.den))) ys ∧
      (ix (CL.toList ys) ≫ graph Int64.ofNat) i v
  | _, _, count G => Verb.dom (G.den ≫ Verb.pos) ≫ Λ (G.den ≫ Verb.pos) ≫ Verb.enum ≫ ListRel.length ≫ graph Int64.ofNat
  | _, _, grade (n := n) d lt x => posL° ≫ fun i v => ∃ G, Verb.sort (Verb.stable x.rel (if d then flip lt else lt))
      (CL.ofList (List.range n)) G ∧ (ix (CL.toList G) ≫ graph Int64.ofNat) i v

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
  | _, _, grade (n := n) d _ x => do
    let some S := Ops.grade d x | throw "<x: no grade kernel for this type"
    pure ⟨n, ← tilKey n, S⟩

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
  | _, _, grade d lt x => ∀ S, Ops.grade d x = some S → @Eq (Ob .long ⟶ Ob .long) (posL° ≫ S.rel) (grade d lt x).den

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

/-- A grade that runs is the kernel's list keyed by `til n`. -/
theorem grade_run {t : QAtomicType} {n : Nat} {d : Bool} {lt : El t → El t → Prop} {x : Arr t n} {R : Rel .long .long}
    (h : (grade d lt x).run = .ok R) : ∃ S k, Ops.grade d x = some S ∧ tilKey n = .ok k ∧ R = ⟨n, k, S⟩ := by
  simp only [run, bind, Except.bind] at h
  split at h
  · rename_i S hg
    split at h
    · cases h
    · cases h; exact ⟨S, _, hg, by assumption, rfl⟩
  · cases h

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
  | _, _, grade .., _, hs, h => by
    unfold Sound at hs
    obtain ⟨S, k, hg, hk, rfl⟩ := grade_run h
    rw [arr_sound S hk]; exact hs S hg

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

/-- A fold node over `op`'s kernel: its seed and step are the ones `op` computes, q's null skipped
    (`overBy_rel`), so no caller can pair a kernel with a fold it does not run. -/
def foldOp {A : QAtomicType} {n : Nat} (op : Kernel.Coc.Over) (x : Arr .long n) (G : Prog A .long) : Prog A .long :=
  fold op (op.denseSeed QLean.Kernel.Ew.i64 Spec.nul) (Verb.skipNul op.step) x G

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

/-- `x@y = y ≫ miss(pos ≫ x, e)`, `e` the null of `x`'s type. -/
def index {t : QAtomicType} {nx ny : Nat} (x : Arr t nx) (y : Arr .long ny) (e : El t) : Prog .long t :=
  union (comp (arr y) (arr x)) (cst e (anti (arr y) (dom (arr x))))

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
    (hy : ny ≤ 2 ^ 64) {R : Rel .long t} (h : (index x y e).run = .ok R) (hs : (index x y e).Sound) :
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
def whole {t : QAtomicType} (P : Prog .long t) : Prog .long .long := conv (cst (u := .long) (0 : Int64) P)

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

/-- `x` with its nulls dropped: the anti-join against the coreflexive `ran x ∩ (ran x ≫ !0N)` on `0N`. -/
def nonNul {n : Nat} (x : Arr .long n) : Prog .long .long :=
  anti (arr x) (inter (idU x) (cst (u := .long) Spec.nul (idU x)))

/-- `avg x = ⟨⦇0,+⦈, ⦇0,succ⦈⟩ ≫ (÷)`, one key `0`, nulls skipped by both: the sum by `skipNul`, the
    count over `nonNul x`. -/
def avg {n : Nat} {rt : QAtomicType} (h : Eval.ewType .div .long .long = some rt) (x : Arr .long n) :
    Prog .long rt := dy .div h (over .add x) (count (whole (nonNul x)))

theorem avg_den {n : Nat} {rt : QAtomicType} (h : Eval.ewType .div .long .long = some rt) (x : Arr .long n) :
    (avg h x).den = rpair (over .add x).den (count (whole (nonNul x))).den ≫ ofExcept fun p => elem .div h p.1 p.2 :=
  rfl

/-- On `x`'s values, missing the coreflexive `ran x ∩ (ran x ≫ !0N)` is being other than `0N`. -/
theorem corNeg_nul {n : Nat} (x : Arr .long n) :
    (x.rel ≫ Verb.corNeg (Verb.ran x.rel ∩ (Verb.ran x.rel ≫ Verb.cst (B := Ob .long) Spec.nul)) : Idx ⟶ Ob .long)
      = x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul) := by
  refine hom_ext fun j b => ⟨fun ⟨c, hx, hc⟩ => ?_, fun ⟨c, hx, hc⟩ => ?_⟩
  · obtain ⟨ecb, hn⟩ := hc
    subst ecb
    exact ⟨c, hx, rfl, fun hb => hn c ⟨⟨rfl, j, hx, hx⟩, c, ⟨rfl, j, hx, hx⟩, hb⟩⟩
  · obtain ⟨ecb, hb⟩ := hc
    subst ecb
    exact ⟨c, hx, rfl, fun v ⟨_, _, _, hv⟩ => hb hv⟩

/-- `nonNul x` holds `x` where it is not `0N`. -/
theorem nonNul_den {n : Nat} (x : Arr .long n) :
    (nonNul x).den = posL° ≫ x.rel ≫ corefl (fun c : Int64 => c ≠ Spec.nul) := by
  rw [← corNeg_nul]; exact Cat.assoc _ _ _

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

/-- A run of `comp P Q` ran `P`. -/
theorem comp_run {A B C : QAtomicType} {P : Prog A B} {Q : Prog B C} {R : Rel A C} (h : (comp P Q).run = .ok R) :
    ∃ R₁, P.run = .ok R₁ := by
  simp only [run, bind, Except.bind] at h; split at h
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
    (hn : n < USize.size) (h63 : n < 2 ^ 63) (h : Ops.grade d x = some S) :
    ∃ M : List Nat, (Verb.cst (CL.ofList M) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable x.rel
          (if d then flip (fun a b : Int64 => a < b) else fun a b : Int64 => a < b))
      ∧ S.toList = M.map Int64.ofNat ∧ M.length = n ∧ ∀ j ∈ M, j < n := by
  have hl : x.toList.length < 2 ^ 63 := by rw [Arr.length_toList]; exact h63
  refine ⟨(List.range x.toList.length).mergeSort fun i j =>
      if d then decide (x.toList[j]! ≤ x.toList[i]!) else decide (x.toList[i]! ≤ x.toList[j]!), ?_,
    by rw [Ops.grade_toList hx hn h]; rfl, by rw [List.length_mergeSort, List.length_range, Arr.length_toList],
    fun j hj => ?_⟩
  · rw [← Verb.grade_map d _ hl, ← Ops.grade_toList hx hn h]
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
    (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : Rel .long .long}
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
    (hs : longWords n s.enc = some ws) (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : Rel .long u}
    (h : (xsort d (fun a b : Int64 => a < b) s x).run = .ok R) (hS : (xsort d (fun a b : Int64 => a < b) s x).Sound) :
    ∃ G : List Nat, (Verb.cst (CL.ofList G) : (⟨Unit⟩ : RelSet.{0}) ⟶ ListRel.dList Nat)
        = Verb.cst (CL.ofList (List.range n)) ≫ Verb.sort (Verb.stable s.rel
          (if d then flip (fun a b : Int64 => a < b) else fun a b : Int64 => a < b))
      ∧ corefl (fun i : Nat => i < 2 ^ 64) ≫ posL ≫ (R.Holds : Ob .long ⟶ Ob u) = ix G ≫ x.rel := by
  obtain ⟨_, h1⟩ := comp_run h
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

/-- A run of `conv P` ran `P`, and holds its converse. -/
theorem conv_run {A B : QAtomicType} {P : Prog A B} {R : Rel B A} (h : (conv P).run = .ok R) :
    ∃ R₁, P.run = .ok R₁ ∧ ∀ a b, R.Holds b a ↔ R₁.Holds a b := by
  simp only [run, bind, Except.bind] at h; split at h
  · cases h
  · exact ⟨_, by assumption, Alg.conv_holds h⟩

/-- `rank x` runs to `rank_rel`'s right side: read at the positions below `2^64` and back through `pos`, it is
    `(ix G)°`, `G` the list `sort(⊴ₓ)` gives. -/
theorem rank_prog {n : Nat} {x : Arr .long n} {ws : List UInt64} (hx : longWords n x.enc = some ws)
    (hn : n < USize.size) (h63 : n < 2 ^ 63) {R : Rel .long .long}
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
#print axioms Prog.corNeg_nul
#print axioms Prog.lam_key
#print axioms Prog.lamEst_iff
#print axioms Prog.lastBy_grp
#print axioms Prog.selectBy_grp
#print axioms Prog.distinct_den
#print axioms Prog.countBy_den
#print axioms Prog.size_den
#print axioms Prog.over_den
#print axioms Prog.avg_den
#print axioms Prog.iasc_den
#print axioms Prog.idesc_den
#print axioms Prog.rank_den
#print axioms Prog.asc_den
#print axioms Prog.desc_den
#print axioms Prog.xasc_den
#print axioms Prog.grade_sound_long
#print axioms Prog.grade_prog
#print axioms Prog.xsort_prog
#print axioms Prog.keys_miss
#print axioms Prog.lastEst_some
#print axioms Prog.lastBy_link
#print axioms Prog.selectBy_link
#print axioms Prog.rank_prog

end LeetQ.Rel
