import LeetQ.Rel.Prog

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Eval
open Freyd Freyd.Alg Freyd.Alg.RelSet PowerAllegory
open LeetQ.Rel.Verb (ofExcept rel_iff mk_rel til_rel where_rel)

namespace Prog

/-! ## The normaliser `norm` (design §3: R6–R8)

  `norm` rewrites a verb's literal order joins to the fused kernels, one rule per pattern, top-down: a node a rule
  matches is replaced whole, any other is rebuilt from its normalised children. Each rule carries its `den`
  law, so `normS P` is the rewritten term together with `(norm P).den = P.den`; the rules' one side condition is
  `Small P`, every stored list below `2^63`, where `posL` keeps the order. -/

/-- Every stored list of `P` below `2^63`: the side condition of R6–R8. -/
def Small : {A B : QAtomicType} → Prog A B → Prop
  | _, _, arr (n := n) _ => n ≤ 2 ^ 63
  | _, _, comp P Q => P.Small ∧ Q.Small
  | _, _, inter P Q => P.Small ∧ Q.Small
  | _, _, union P Q => P.Small ∧ Q.Small
  | _, _, dy _ _ P Q => P.Small ∧ Q.Small
  | _, _, anti P Q => P.Small ∧ Q.Small
  | _, _, ojoin _ P Q => P.Small ∧ Q.Small
  | _, _, conv P => P.Small
  | _, _, map _ _ P => P.Small
  | _, _, mem P => P.Small
  | _, _, extr _ P => P.Small
  | _, _, fold _ _ _ _ P => P.Small
  | _, _, cst _ P => P.Small
  | _, _, dom P => P.Small
  | _, _, enumC _ P => P.Small
  | _, _, count P => P.Small
  | _, _, _ => True

/-- `{e}` as a coreflexive on longs: `ran(til 1 ≫ !e)`, one row. -/
def pt (e : Int64) : Prog .long .long := dom (conv (cst (u := .long) e (til 1)))

theorem pt_den (e a b : Int64) : (pt e).den a b ↔ a = b ∧ a = e := by
  constructor
  · rintro ⟨hab, c, ⟨m, _, hm⟩, _⟩
    exact ⟨hab, hm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, 0, ⟨0, ⟨0, rfl, 0, ⟨rfl, by decide⟩, rfl⟩, rfl⟩, ⟨0, ⟨0, rfl, 0, ⟨rfl, by decide⟩, rfl⟩, rfl⟩⟩

/-- A position below `2^63` is never read as a negative long. -/
theorem ofNat_ne {j : Nat} (hj : j < 2 ^ 63) {e : Int64} (he : e < 0) : Int64.ofNat j ≠ e := fun h => by
  have h0 : (0 : Int64) ≤ Int64.ofNat j := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt (by omega)]; simp
  rw [h] at h0
  have := Int64.lt_iff_toInt_lt.1 he; have := Int64.le_iff_toInt_le.1 h0; omega

/-- **`miss` with its fill cut back out**: `miss(N ≫ posL, e) ≫ corNeg{e}` is `N ≫ posL` on `N`'s keys, when no
    position `N` reaches reads as `e`. -/
theorem miss_cut {n : Nat} (N : Idx ⟶ Idx) (e : Int64) (hN : ∀ i j, N i j → i < n ∧ j < 2 ^ 63) (he : e < 0) :
    corefl (· < n) ≫ Verb.miss (N ≫ graph Int64.ofNat) e ≫ Verb.corNeg (pt e).den = N ≫ posL := by
  refine hom_ext fun i c => ⟨fun ⟨_, ⟨rfl, _⟩, b, hm, ebc, hn⟩ => ?_, fun ⟨j, hj, ec⟩ => ?_⟩
  · subst ebc
    rcases (Verb.miss_iff _ _ _ _).1 hm with h | ⟨_, rfl⟩
    · exact h
    · exact (hn _ ((pt_den _ _ _).2 ⟨rfl, rfl⟩)).elim
  · refine ⟨i, ⟨rfl, (hN i j hj).1⟩, c, (Verb.miss_iff _ _ _ _).2 (Or.inl ⟨j, hj, ec⟩), rfl, fun v hv => ?_⟩
    obtain ⟨rfl, rfl⟩ := (pt_den _ _ _).1 hv
    exact ofNat_ne (hN i j hj).2 he ec.symm

/-- **R6 at its `Λ`**: `bin`'s fused order join `Λ(y ≫ (≥) ≫ x°) ≫ est(≥)` is `binJ` with its miss row `−1` cut. -/
theorem binE {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hx : nx ≤ 2 ^ 63) (hy : ny ≤ 2 ^ 63) :
    (anti (binJ x y) (pt (-1))).den = (extr true (ojoin .ge (arr y) (arr x))).den := by
  have hW := bd_join (ord .ge) (arr_lt y hy) (arr_lt x hx)
  show (posL° ≫ y.rel ≫ _) ≫ _ = Λ ((posL° ≫ y.rel) ≫ ord .ge ≫ (posL° ≫ x.rel)°) ≫ est (fun a b : Int64 => a ≥ b)
  rw [join_lift, lift_est hW, Cat.assoc, fuse y, Cat.assoc (corefl (· < ny)), miss_cut _ _ (fun i j h => ⟨?_, (bd_est _ hW i j h).2⟩) (by decide)]
  obtain ⟨_, hv, _⟩ := ((RelSet.Λ_comp_est_apply _ _ _ _).1 h).1
  exact ((rel_iff y i _).1 hv).1

/-- **R7 at its `Λ`**: `aj`'s fused order join is `ajJ` with its miss row `0N` cut. -/
theorem ajE {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) (hr : nr ≤ 2 ^ 63) :
    (anti (ajJ lk lt rk rt) (pt Int64.minValue)).den =
      (extr true (inter (comp (arr lk) (conv (arr rk))) (ojoin .ge (arr lt) (arr rt)))).den := by
  have hK := bd_comp (arr_lt lk hl) (arr_lt rk hr)
  have hJ := bd_join (ord .ge) (arr_lt lt hl) (arr_lt rt hr)
  have hKJ : Bd ((lk.rel ≫ rk.rel°) ∩ (lt.rel ≫ ord .ge ≫ rt.rel°)) := fun i j h => hK i j h.1
  show (posL° ≫ corefl (· < nl) ≫ _) ≫ _ = Λ (((posL° ≫ lk.rel) ≫ (posL° ≫ rk.rel)°) ∩
      ((posL° ≫ lt.rel) ≫ ord .ge ≫ (posL° ≫ rt.rel)°)) ≫ est (fun a b : Int64 => a ≥ b)
  rw [comp_lift, join_lift, lift_inter hK hJ, lift_est hKJ, Cat.assoc, Cat.assoc,
    miss_cut _ _ (fun i j h => ⟨?_, (bd_est _ hKJ i j h).2⟩) (by decide)]
  obtain ⟨_, hv, _⟩ := ((RelSet.Λ_comp_est_apply _ _ _ _).1 h).1.1
  exact ((rel_iff lk i _).1 hv).1

/-- Two lists with one list of values are one relation. -/
theorem rel_of_toList {t : QAtomicType} {n m : Nat} {a : Arr t n} {b : Arr t m} (h : a.toList = b.toList) :
    a.rel = b.rel := by
  show ix a.toList = ix b.toList; rw [h]

/-- `b` at the length `n`, when that is its length. -/
def asLen {t : QAtomicType} {m : Nat} (n : Nat) (b : Arr t m) : Option {c : Arr t n // c.rel = b.rel} :=
  if h : m = n then some ⟨h ▸ b, by subst h; rfl⟩ else none

/-- The rewrite rules at one node: the fused term and its law, `none` where no rule matches. A list that
    a pattern names twice (`rt` in `wj1`) must hold one list of values in both places. -/
def rule : {A B : QAtomicType} → (P : Prog A B) → Option {Q : Prog A B // P.Small → Q.den = P.den}
  | _, _, extr true (ojoin .ge (arr y) (arr x)) =>
    some ⟨anti (binJ x y) (pt (-1)), fun h => binE x y h.2 h.1⟩
  | _, _, extr true (inter (@comp _ .long _ (arr lk) (conv (arr rk))) (ojoin .ge (arr lt) (arr rt))) =>
    match asLen _ lt, asLen _ rt with
    | some ⟨lt', e1⟩, some ⟨rt', e2⟩ => some ⟨anti (ajJ lk lt' rk rt') (pt Int64.minValue), fun h => by
        rw [ajE lk lt' rk rt' h.1.1 h.1.2]
        show Λ (_ ∩ ((posL° ≫ lt'.rel) ≫ _ ≫ (posL° ≫ rt'.rel)°)) ≫ _ = _
        rw [e1, e2]; rfl⟩
    | _, _ => none
  | _, _, inter (inter (@comp _ .long _ (arr lk) (conv (arr rk))) (ojoin .le (arr w₀) (arr rt)))
      (ojoin .ge (arr w₁) (arr rt₁)) =>
    match asLen _ w₀, asLen _ w₁, asLen _ rt with
    | some ⟨w₀', e0⟩, some ⟨w₁', e1⟩, some ⟨rt', et⟩ =>
      if h1 : rt₁.toList = rt.toList then some ⟨wjJ false lk w₀' w₁' rk rt', fun h => by
        rw [← wj1_R8 lk w₀' w₁' rk rt' h.1.1.1 h.1.1.2, wj1_den, e0, e1, et]
        show _ = _ ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt₁.rel)°)
        rw [rel_of_toList h1]; rfl⟩
      else none
    | _, _, _ => none
  | _, _, union (inter (inter (@comp _ .long _ (arr lk) (conv (arr rk))) (ojoin .lt (arr w₀) (arr rt)))
        (ojoin .ge (arr w₁) (arr rt₁)))
      (extr true (inter (@comp _ .long _ (arr lk₂) (conv (arr rk₂))) (ojoin .ge (arr w₀₂) (arr rt₂)))) =>
    match asLen _ w₀, asLen _ w₁, asLen _ rt with
    | some ⟨w₀', e0⟩, some ⟨w₁', e1⟩, some ⟨rt', et⟩ =>
      if h1 : rt₁.toList = rt.toList ∧ lk₂.toList = lk.toList ∧ rk₂.toList = rk.toList ∧
          w₀₂.toList = w₀.toList ∧ rt₂.toList = rt.toList then some ⟨wjJ true lk w₀' w₁' rk rt', fun h => by
        rw [← wj_R8 lk w₀' w₁' rk rt' h.1.1.1.1 h.1.1.1.2, wj_den, e0, e1, et]
        show _ = ((_ ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt₁.rel)°)) ∪
          (Λ (((posL° ≫ lk₂.rel) ≫ (posL° ≫ rk₂.rel)°) ∩ ((posL° ≫ w₀₂.rel) ≫ ord .ge ≫ (posL° ≫ rt₂.rel)°)) ≫
            est (fun a b : Int64 => a ≥ b)))
        rw [rel_of_toList h1.1, rel_of_toList h1.2.1, rel_of_toList h1.2.2.1, rel_of_toList h1.2.2.2.1,
          rel_of_toList h1.2.2.2.2]; rfl⟩
      else none
    | _, _, _ => none
  | _, _, _ => none

/-- A rule where one matches, else `d`, the node rebuilt from its normalised children. -/
def orRule {A B : QAtomicType} (P : Prog A B) (d : {Q : Prog A B // P.Small → Q.den = P.den}) :
    {Q : Prog A B // P.Small → Q.den = P.den} :=
  (rule P).getD d

/-- `norm` with its law: top-down, a node a rule matches replaced, every other rebuilt. -/
def normS : {A B : QAtomicType} → (P : Prog A B) → {Q : Prog A B // P.Small → Q.den = P.den}
  | _, _, comp P Q => ⟨comp (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ≫ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, conv P => ⟨conv (normS P).1, fun h => by show (normS P).1.den° = _; rw [(normS P).2 h]; rfl⟩
  | _, _, inter P Q => orRule (inter P Q) ⟨inter (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ∩ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, union P Q => orRule (union P Q) ⟨union (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ∪ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, map op f P => ⟨map op f (normS P).1, fun h => by
      show (normS P).1.den ≫ graph f = _; rw [(normS P).2 h]; rfl⟩
  | _, _, dy v e P Q => ⟨dy v e (normS P).1 (normS Q).1, fun h => by
      show rpair (normS P).1.den (normS Q).1.den ≫ _ = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, mem P => ⟨mem (normS P).1, fun h => by show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, extr false P => orRule (extr false P) ⟨extr false (normS P).1, fun h => by
      show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, extr true P => orRule (extr true P) ⟨extr true (normS P).1, fun h => by
      show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, fold op e f x G => ⟨fold op e f x (normS G).1, fun h => by
      show Verb.dom ((normS G).1.den ≫ Verb.pos) ≫ Λ ((normS G).1.den ≫ Verb.pos) ≫ _ = _; rw [(normS G).2 h]; rfl⟩
  | _, _, anti P C => ⟨anti (normS P).1 (normS C).1, fun h => by
      show (normS P).1.den ≫ Verb.corNeg (normS C).1.den = _; rw [(normS P).2 h.1, (normS C).2 h.2]; rfl⟩
  | _, _, cst e P => ⟨cst e (normS P).1, fun h => by show (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, dom P => ⟨dom (normS P).1, fun h => by show Verb.dom (normS P).1.den = _; rw [(normS P).2 h]; rfl⟩
  | _, _, enumC n C => ⟨enumC n (normS C).1, fun h => by
      show posL° ≫ (fun i v => ∃ ys, Verb.enum (Verb.cset (Verb.dom (corefl (· < n) ≫ posL ≫ (normS C).1.den))) ys ∧
        (ix (CL.toList ys) ≫ graph Int64.ofNat) i v) = _
      rw [(normS C).2 h]; rfl⟩
  | _, _, count G => ⟨count (normS G).1, fun h => by
      show Verb.dom ((normS G).1.den ≫ Verb.pos) ≫ Λ ((normS G).1.den ≫ Verb.pos) ≫ _ = _; rw [(normS G).2 h]; rfl⟩
  | _, _, ojoin v P Q => ⟨ojoin v (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ≫ ord v ≫ (normS Q).1.den° = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, P => ⟨P, fun _ => rfl⟩

/-- The normal form: the fused kernels in place of the literal order joins. -/
def norm {A B : QAtomicType} (P : Prog A B) : Prog A B := (normS P).1

/-- **`norm` keeps the spec**, every stored list below `2^63`. -/
theorem norm_den {A B : QAtomicType} (P : Prog A B) (h : P.Small) : (norm P).den = P.den := (normS P).2 h

/-- A verb executed: its normal form run. -/
def exec {A B : QAtomicType} (P : Prog A B) : Except String (Rel A B) := (norm P).run

/-- **`exec` runs to the spec**: `run_sound` of the normal form, then `norm_den`. -/
theorem exec_sound {A B : QAtomicType} (P : Prog A B) {R : Rel A B} (h : P.Small) (hs : (norm P).Sound)
    (hr : exec P = .ok R) : (R.Holds : Ob A ⟶ Ob B) = P.den :=
  (run_sound _ hs hr).trans (norm_den P h)

/-- `bin` normalised: both of its order joins are `binJ`'s bisection. -/
theorem bin_norm {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) :
    norm (bin x y) = missP (til ny) (anti (binJ x y) (pt (-1))) (-1) := rfl

theorem wj1_norm {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    norm (wj1 lk w₀ w₁ rk rt) = wjJ false lk w₀ w₁ rk rt := by
  simp [norm, normS, wj1, orRule, rule, asLen]

end Prog

#print axioms Prog.norm_den
#print axioms Prog.exec_sound
#print axioms Prog.binE
#print axioms Prog.ajE

end LeetQ.Rel
