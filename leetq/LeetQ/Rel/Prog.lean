/-
  RelRep design B, step 1: a k verb is a term `Prog` over the executable Rel primitives (design §1:
  P1–P6, P6′, P13). `den P` is its spec in `RelSet`, `run P` executes it one `Alg.*` kernel per node.
  `run_sound`: `run P = ok R → R.Holds = den P`, from one lemma per node; a kernel node whose kernel has
  no theorem yet (`comp`, `∩`, `∪`, `𝟘`, `⊤`, `mapVal`, `pair`, `Ew.val`) contributes its law to `Sound P`.
-/
import LeetQ.Rel.Algebra
import LeetQ.Rel.SpecStruct

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Eval
open Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Rel.Verb (ofExcept rel_iff mk_rel til_rel)

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

/-- `til n` as a key, refused past `USize`, where `tilLongs` would wrap. -/
def tilKey (n : Nat) : Except String (Arr .long n) :=
  if n < USize.size then Struct.til n else throw s!"til {n}: past USize"

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

end Prog

#print axioms Prog.run_sound
#print axioms Prog.ej_den
#print axioms Prog.dict_den
#print axioms Prog.til_den
#print axioms Prog.mon_den
#print axioms Prog.val_den

end LeetQ.Rel
