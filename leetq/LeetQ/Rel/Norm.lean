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
def Small : {A B : Obj} → Prog A B → Prop
  | _, _, arr (n := n) _ => n ≤ 2 ^ 63
  | _, _, comp P Q => P.Small ∧ Q.Small
  | _, _, inter P Q => P.Small ∧ Q.Small
  | _, _, union P Q => P.Small ∧ Q.Small
  | _, _, pair P Q => P.Small ∧ Q.Small
  | _, _, anti P Q => P.Small ∧ Q.Small
  | _, _, ojoin _ P Q => P.Small ∧ Q.Small
  | _, _, conv P => P.Small
  | _, _, mem P => P.Small
  | _, _, extr _ P => P.Small
  | _, _, fold _ _ _ _ P => P.Small
  | _, _, dom P => P.Small
  | _, _, enumC _ P => P.Small
  | _, _, count P => P.Small
  | _, _, _ => True

/-- `{e}` as a coreflexive on longs: `ran(til 1 ≫ !e)`, one row. -/
def pt (e : Int64) : Prog .long .long := dom (conv (comp (til 1) (fn (.cst (u := .long) e))))

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

/-- qlean's atom `+` on two positions whose sum is below `2^63`: neither is `0N`, the sum does not wrap. -/
theorem arith_add_ofNat {j w : Nat} (h : j + w < 2 ^ 63) :
    arithAtoms .add .long (.long (Int64.ofNat j)) (.long (Int64.ofNat w)) = .ok (.long (Int64.ofNat (j + w))) := by
  have hj := ofNat_ne (j := j) (by omega) (e := Int64.minValue) (by decide)
  have hw := ofNat_ne (j := w) (by omega) (e := Int64.minValue) (by decide)
  have tj : (Int64.ofNat j).toInt = j := Int64.toInt_ofNat_of_lt (by omega)
  have tw : (Int64.ofNat w).toInt = w := Int64.toInt_ofNat_of_lt (by omega)
  simp [arithAtoms, missing, QAtom.isNull, QAtom.type, Prim.clockIntoDays, isFloatPayload, intIn, temporalIn,
    roundedPayload, atomOfInt, intPayload, hj, hw, tj, tw, Int64.ofInt_eq_ofNat]

/-- **`j + w` on longs** (`Fn.dy .add`'s `elem`): two positions whose sum is below `2^63` add to the position `j + w`;
    the step a literal window `j ≤ i < j + w` needs. -/
theorem elem_add_ofNat {j w : Nat} (h : j + w < 2 ^ 63) :
    elem .add (a := .long) (b := .long) (c := .long) rfl (Int64.ofNat j) (Int64.ofNat w) = .ok (Int64.ofNat (j + w)) := by
  have hd : dyadAtom .add (.long (Int64.ofNat j)) (.long (Int64.ofNat w)) = .ok (.long (Int64.ofNat (j + w))) :=
    (rfl : _ = arithAtoms .add .long _ _).trans (arith_add_ofNat h)
  simp only [elem, Carrier.atom]
  rw [dif_neg (by decide), dif_neg (by decide)]
  split
  · next hz => rw [hd] at hz; cases hz
  · next z hz => rw [hd] at hz; cases hz; rfl

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

/-- `Nat.all` is a tail-recursive loop (`all_eq_allTR`); it holds exactly when every test does. -/
theorem all_true : ∀ (n : Nat) (f : (i : Nat) → i < n → Bool), Nat.all n f = true → ∀ i (h : i < n), f i h = true
  | 0, _, _, _, h => absurd h (by omega)
  | n + 1, f, hf, i, h => by
    rw [Nat.all_succ, Bool.and_eq_true] at hf
    by_cases hi : i = n
    · subst hi; exact hf.2
    · exact all_true n _ hf.1 i (by omega)

theorem of_all_true : ∀ (n : Nat) (f : (i : Nat) → i < n → Bool), (∀ i (h : i < n), f i h = true) → Nat.all n f = true
  | 0, _, _ => Nat.all_zero
  | n + 1, f, hf => by
    rw [Nat.all_succ, Bool.and_eq_true]; exact ⟨of_all_true n _ fun i h => hf i (by omega), hf n (by omega)⟩

/-- Two arrays of one length compared by an index loop: no list is built (`List` equality is not tail
    recursive and overflows the stack at ~1e6). -/
def eqAt {n : Nat} (a b : Arr .long n) : Bool := Nat.all n fun i h => decide (a.get ⟨i, h⟩ = b.get ⟨i, h⟩)

/-- The loop decides `toList` equality. -/
theorem eqAt_toList {n : Nat} {a b : Arr .long n} (h : eqAt a b = true) : a.toList = b.toList := by
  have : a.get = b.get := funext fun i => of_decide_eq_true (all_true _ _ h i.1 i.2)
  unfold Arr.toList; rw [this]

@[simp] theorem eqAt_self {n : Nat} (a : Arr .long n) : eqAt a a = true := of_all_true _ _ fun _ _ => by simp

/-- `a` and `b` one list of values. The pointer test runs first, since the two copies of a pattern's list are
    one object; the index loop `eqAt` only when they are not. -/
def sameArr {n m : Nat} (a : Arr .long n) (b : Arr .long m) : Option (PLift (a.toList = b.toList)) :=
  if hn : n = m then
    if h : withPtrEq (hn ▸ a) b (fun _ => eqAt (hn ▸ a) b) (fun e => by subst hn; subst e; simp) = true
    then some ⟨by subst hn; exact eqAt_toList h⟩ else none
  else none

/-- `b` at the length `n`, when that is its length. -/
def asLen {t : QAtomicType} {m : Nat} (n : Nat) (b : Arr t m) : Option {c : Arr t n // c.rel = b.rel} :=
  if h : m = n then some ⟨h ▸ b, by subst h; rfl⟩ else none

/-- The rewrite rules at one node: the fused term and its law, `none` where no rule matches. A list that
    a pattern names twice (`rt` in `wj1`) must hold one list of values in both places. -/
def rule : {A B : Obj} → (P : Prog A B) → Option {Q : Prog A B // P.Small → Q.den = P.den}
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
      match sameArr rt₁ rt with
      | some ⟨h1⟩ => some ⟨wjJ false lk w₀' w₁' rk rt', fun h => by
        rw [← wj1_R8 lk w₀' w₁' rk rt' h.1.1.1 h.1.1.2, wj1_den, e0, e1, et]
        show _ = _ ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt₁.rel)°)
        rw [rel_of_toList h1]; rfl⟩
      | none => none
    | _, _, _ => none
  | _, _, union (inter (inter (@comp _ .long _ (arr lk) (conv (arr rk))) (ojoin .lt (arr w₀) (arr rt)))
        (ojoin .ge (arr w₁) (arr rt₁)))
      (extr true (inter (@comp _ .long _ (arr lk₂) (conv (arr rk₂))) (ojoin .ge (arr w₀₂) (arr rt₂)))) =>
    match asLen _ w₀, asLen _ w₁, asLen _ rt with
    | some ⟨w₀', e0⟩, some ⟨w₁', e1⟩, some ⟨rt', et⟩ =>
      match sameArr rt₁ rt, sameArr lk₂ lk, sameArr rk₂ rk, sameArr w₀₂ w₀, sameArr rt₂ rt with
      | some ⟨i1⟩, some ⟨i2⟩, some ⟨i3⟩, some ⟨i4⟩, some ⟨i5⟩ => some ⟨wjJ true lk w₀' w₁' rk rt', fun h => by
        have h1 : _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨i1, i2, i3, i4, i5⟩
        rw [← wj_R8 lk w₀' w₁' rk rt' h.1.1.1.1 h.1.1.1.2, wj_den, e0, e1, et]
        show _ = ((_ ∩ ((posL° ≫ w₁.rel) ≫ ord .ge ≫ (posL° ≫ rt₁.rel)°)) ∪
          (Λ (((posL° ≫ lk₂.rel) ≫ (posL° ≫ rk₂.rel)°) ∩ ((posL° ≫ w₀₂.rel) ≫ ord .ge ≫ (posL° ≫ rt₂.rel)°)) ≫
            est (fun a b : Int64 => a ≥ b)))
        rw [rel_of_toList h1.1, rel_of_toList h1.2.1, rel_of_toList h1.2.2.1, rel_of_toList h1.2.2.2.1,
          rel_of_toList h1.2.2.2.2]; rfl⟩
      | _, _, _, _, _ => none
    | _, _, _ => none
  | _, _, _ => none

/-- `R` a map on `til n`: its keys are the positions below `n`, each with one value. -/
def MapOn (n : Nat) (R : Ob .long ⟶ Ob .long) : Prop :=
  (∀ a, (∃ c, R a c) ↔ ∃ i, i < n ∧ a = Int64.ofNat i) ∧ ∀ a c c', R a c → R a c' → c = c'

/-- `R ≫ corNeg{e}` keeps the rows of `R` whose value is not `e`. -/
theorem cut_iff (R : Ob .long ⟶ Ob .long) (e a c : Int64) : (R ≫ Verb.corNeg (pt e).den) a c ↔ R a c ∧ c ≠ e :=
  ⟨fun ⟨_, hb, ebc, hn⟩ => by subst ebc; exact ⟨hb, fun h => hn _ ((pt_den _ _ _).2 ⟨rfl, h⟩)⟩,
    fun ⟨h, hne⟩ => ⟨c, h, rfl, fun v hv => by obtain ⟨rfl, rfl⟩ := (pt_den _ _ _).1 hv; exact hne rfl⟩⟩

/-- **`miss` of a map with its fill cut**: on `til n`, `miss(R ≫ corNeg{e}, e)` is `R`, when `R` is a map on
    `til n`: a row of `R` at `e` is cut and filled back with `e`, every other row is kept. -/
theorem miss_map {n : Nat} {R : Ob .long ⟶ Ob .long} (hR : MapOn n R) (e : Int64) :
    (til n).den ≫ Verb.miss (R ≫ Verb.corNeg (pt e).den) e = R := by
  refine hom_ext fun a c => ⟨fun ⟨b, ⟨i, ea, _, ⟨rfl, hi⟩, eb⟩, hm⟩ => ?_, fun h => ?_⟩
  · obtain rfl : a = b := ea.trans eb.symm
    rcases (Verb.miss_iff _ _ _ _).1 hm with h | ⟨hn, hc⟩
    · exact ((cut_iff _ _ _ _).1 h).1
    · obtain ⟨c', hc'⟩ := (hR.1 a).2 ⟨i, hi, ea⟩
      by_cases hce : c' = e
      · rw [hc]; rwa [hce] at hc'
      · exact (hn ⟨c', (cut_iff _ _ _ _).2 ⟨hc', hce⟩⟩).elim
  · obtain ⟨i, hi, rfl⟩ := (hR.1 _).1 ⟨c, h⟩
    refine ⟨_, ⟨i, rfl, i, ⟨rfl, hi⟩, rfl⟩, (Verb.miss_iff _ _ _ _).2 ?_⟩
    by_cases hce : c = e
    · exact Or.inr ⟨fun ⟨c', hc'⟩ => ((cut_iff _ _ _ _).1 hc').2 (hR.2 _ _ _ ((cut_iff _ _ _ _).1 hc').1 h ▸ hce), hce⟩
    · exact Or.inl ((cut_iff _ _ _ _).2 ⟨h, hce⟩)

/-- `miss(Λ(W) ≫ est(≥) ≫ posL, e)` on `til n` is a map on `til n`: `est(≥)` on positions picks one, `miss` fills
    the rest. -/
theorem mapOn_miss {n : Nat} (hn : n ≤ 2 ^ 63) (W : Idx ⟶ Idx) (e : Int64) :
    MapOn n (posL° ≫ corefl (· < n) ≫ Verb.miss ((Λ W ≫ est geN) ≫ graph Int64.ofNat) e) := by
  refine ⟨fun a => ⟨fun ⟨_, i, ea, _, ⟨rfl, hi⟩, _⟩ => ⟨i, hi, ea⟩, fun ⟨i, hi, ea⟩ => ?_⟩,
    fun a c c' ⟨i, ea, _, ⟨rfl, hi⟩, hm⟩ ⟨i', ea', _, ⟨rfl, hi'⟩, hm'⟩ => ?_⟩
  · by_cases hs : ∃ c, ((Λ W ≫ est geN) ≫ graph Int64.ofNat) i c
    · obtain ⟨c, hc⟩ := hs; exact ⟨c, i, ea, i, ⟨rfl, hi⟩, (Verb.miss_iff _ _ _ _).2 (Or.inl hc)⟩
    · exact ⟨e, i, ea, i, ⟨rfl, hi⟩, (Verb.miss_iff _ _ _ _).2 (Or.inr ⟨hs, rfl⟩)⟩
  · obtain rfl := ofNat_inj (lt64 (Nat.lt_of_lt_of_le hi hn)) (lt64 (Nat.lt_of_lt_of_le hi' hn)) (ea.symm.trans ea')
    rcases (Verb.miss_iff _ _ _ _).1 hm with ⟨j, hj, rfl⟩ | ⟨hn, rfl⟩ <;>
      rcases (Verb.miss_iff _ _ _ _).1 hm' with ⟨j', hj', rfl⟩ | ⟨hn', rfl⟩
    · obtain ⟨hw, hmax⟩ := (RelSet.Λ_comp_est_apply _ _ _ _).1 hj
      obtain ⟨hw', hmax'⟩ := (RelSet.Λ_comp_est_apply _ _ _ _).1 hj'
      rw [Nat.le_antisymm (hmax' j hw) (hmax j' hw')]
    · exact (hn' ⟨_, j, hj, rfl⟩).elim
    · exact (hn ⟨_, j', hj', rfl⟩).elim
    · rfl

/-- The kernels that are maps on `til n`, with that `n`: `binJ` on `til |y|`, `ajJ` on `til |lk|`. -/
def mapOn? : (K : Prog .long .long) → Option ((n : Nat) ×' (n ≤ 2 ^ 63 → MapOn n K.den))
  | binJ (ny := ny) x y => some ⟨ny, fun h => by
      show MapOn ny (posL° ≫ y.rel ≫ _); rw [fuse y]; exact mapOn_miss h _ _⟩
  | ajJ (nl := nl) _ _ _ _ => some ⟨nl, fun h => mapOn_miss h _ _⟩
  | _ => none

/-- Two kernel nodes over one list of values each: one relation. -/
def sameKer : (K L : Prog .long .long) → Option (PLift (K.den = L.den))
  | binJ x y, binJ x' y' =>
    match sameArr x x', sameArr y y' with
    | some ⟨hx⟩, some ⟨hy⟩ => some ⟨by
        show posL° ≫ y.rel ≫ _ = posL° ≫ y'.rel ≫ _; rw [rel_of_toList hx, rel_of_toList hy]⟩
    | _, _ => none
  | ajJ (nl := nl) lk lt rk rt, ajJ (nl := nl') lk' lt' rk' rt' =>
    if h : nl = nl' then
      match sameArr lk lk', sameArr lt lt', sameArr rk rk', sameArr rt rt' with
      | some ⟨h1⟩, some ⟨h2⟩, some ⟨h3⟩, some ⟨h4⟩ => some ⟨by
          subst h; show posL° ≫ corefl (· < nl) ≫ _ = posL° ≫ corefl (· < nl) ≫ _
          rw [rel_of_toList h1, rel_of_toList h2, rel_of_toList h3, rel_of_toList h4]⟩
      | _, _, _, _ => none
    else none
  | _, _ => none

/-- **The miss rule**: `miss(E, e)` on `til n` (`missP`), where `E` rewrites to `K ≫ corNeg{e}` and `K` is a map
    on `til n`, is `K` itself: the hit branch, the miss branch's `dom E` and the union all go. The two copies of
    `E` must rewrite to one kernel. -/
def missRule : {A B : Obj} → (P : Prog A B) → Option {Q : Prog A B // P.Small → Q.den = P.den}
  | _, _, union (@comp _ .long _ (til n) E) (@comp _ .long _ (anti (til n₂) (@dom .long .long E₂)) (fn (@Fn.cst .long .long e))) =>
    match rule E, rule E₂ with
    | some ⟨anti K (@dom .long .long (@conv .long .long (@comp _ .long _ (til 1) (fn (.cst e₁))))), hQ⟩,
      some ⟨anti K₂ (@dom .long .long (@conv .long .long (@comp _ .long _ (til 1) (fn (.cst e₂))))), hQ₂⟩ =>
      match mapOn? K, sameKer K₂ K with
      | some ⟨m, hm⟩, some ⟨hKK⟩ =>
        if hc : n = m ∧ n = n₂ ∧ n ≤ 2 ^ 63 ∧ e = e₁ ∧ e = e₂ then some ⟨K, fun h => by
          obtain ⟨rfl, rfl, hn, rfl, rfl⟩ := hc
          have h1 : E.den = K.den ≫ Verb.corNeg (pt e).den := (hQ h.1.2).symm
          have h2 : E₂.den = E.den := by rw [h1, ← hQ₂ h.2.1.2, ← hKK]; rfl
          show _ = (til n).den ≫ E.den ∪ ((til n).den ≫ Verb.corNeg (Verb.dom E₂.den)) ≫ Verb.cst e
          rw [h2]
          exact calc K.den = (til n).den ≫ Verb.miss (K.den ≫ Verb.corNeg (pt e).den) e := (miss_map (hm hn) e).symm
            _ = (til n).den ≫ Verb.miss E.den e := by rw [h1]
            _ = (missP (til n) E e).den := (missP_den _ _ _).symm⟩
        else none
      | _, _ => none
    | _, _ => none
  | _, _, _ => none

/-- A rule where one matches, else `d`, the node rebuilt from its normalised children. -/
def orRule {A B : Obj} (P : Prog A B) (d : {Q : Prog A B // P.Small → Q.den = P.den}) :
    {Q : Prog A B // P.Small → Q.den = P.den} :=
  ((rule P).orElse fun _ => missRule P).getD d

/-- `norm` with its law: top-down, a node a rule matches replaced, every other rebuilt. -/
def normS : {A B : Obj} → (P : Prog A B) → {Q : Prog A B // P.Small → Q.den = P.den}
  | _, _, comp P Q => ⟨comp (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ≫ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, conv P => ⟨conv (normS P).1, fun h => by show (normS P).1.den° = _; rw [(normS P).2 h]; rfl⟩
  | _, _, inter P Q => orRule (inter P Q) ⟨inter (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ∩ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, union P Q => orRule (union P Q) ⟨union (normS P).1 (normS Q).1, fun h => by
      show (normS P).1.den ∪ (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, pair P Q => ⟨pair (normS P).1 (normS Q).1, fun h => by
      show rpair (normS P).1.den (normS Q).1.den = _; rw [(normS P).2 h.1, (normS Q).2 h.2]; rfl⟩
  | _, _, mem P => ⟨mem (normS P).1, fun h => by show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, extr false P => orRule (extr false P) ⟨extr false (normS P).1, fun h => by
      show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, extr true P => orRule (extr true P) ⟨extr true (normS P).1, fun h => by
      show Λ (normS P).1.den ≫ _ = _; rw [(normS P).2 h]; rfl⟩
  | _, _, fold op e f x G => ⟨fold op e f x (normS G).1, fun h => by
      show Verb.dom ((normS G).1.den ≫ Verb.pos) ≫ Λ ((normS G).1.den ≫ Verb.pos) ≫ _ = _; rw [(normS G).2 h]; rfl⟩
  | _, _, anti P C => ⟨anti (normS P).1 (normS C).1, fun h => by
      show (normS P).1.den ≫ Verb.corNeg (normS C).1.den = _; rw [(normS P).2 h.1, (normS C).2 h.2]; rfl⟩
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
def norm {A B : Obj} (P : Prog A B) : Prog A B := (normS P).1

/-- **`norm` keeps the spec**, every stored list below `2^63`. -/
theorem norm_den {A B : Obj} (P : Prog A B) (h : P.Small) : (norm P).den = P.den := (normS P).2 h

/-- A verb executed: its normal form run. -/
def exec {A B : Obj} (P : Prog A B) : Except String (RelV A B) := (norm P).run

/-- **`exec` runs to the spec**: `run_sound` of the normal form, then `norm_den`. -/
theorem exec_sound {A B : Obj} (P : Prog A B) {R : RelV A B} (h : P.Small) (hs : (norm P).Sound)
    (hr : exec P = .ok R) : (R.Holds : Ob A ⟶ Ob B) = P.den :=
  (run_sound _ hs hr).trans (norm_den P h)

/-! `rule` and `missRule` match through the `.atom` indices, where Lean generates no match equations, so the
    normal forms below reduce them by `whnf`, and rewrite only what a variable length keeps stuck. -/

theorem asLen_self {t : QAtomicType} {n : Nat} (b : Arr t n) : asLen n b = some ⟨b, rfl⟩ := by simp [asLen]

theorem sameArr_self {n : Nat} (a : Arr .long n) : sameArr a a = some ⟨rfl⟩ := by simp [sameArr, withPtrEq]

/-- `whnf` turns a `dite` into this recursor, where `dif_pos` no longer matches. -/
theorem decRec_pos {p : Prop} {α : Type _} {d : Decidable p} (h : p) {a : ¬p → α} {b : p → α} :
    Decidable.rec (motive := fun _ => α) a b d = b h := by
  cases d with
  | isFalse n => exact absurd h n
  | isTrue _ => rfl

theorem sameKer_bin {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) : (sameKer (binJ x y) (binJ x y)).isSome = true := by
  conv => lhs; arg 1; whnf
  simp [sameArr_self]

theorem sameKer_aj {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) :
    (sameKer (ajJ lk lt rk rt) (ajJ lk lt rk rt)).isSome = true := by
  conv => lhs; arg 1; whnf
  simp only [sameArr_self]
  rw [decRec_pos (p := nl = nl) rfl] <;> rfl

/-- A node `rule` rewrites normalises to its rewrite. -/
theorem orRule_some {A B : Obj} {P Q : Prog A B} {d} (h : (rule P).map Subtype.val = some Q) : (orRule P d).1 = Q := by
  cases e : rule P with
  | none => simp [e] at h
  | some r => simp only [e, Option.map_some, Option.some.injEq] at h; simp [orRule, e, h]

/-- A node only `missRule` rewrites normalises to its rewrite. -/
theorem orRule_miss {A B : Obj} {P Q : Prog A B} {d} (h0 : rule P = none) (h : (missRule P).map Subtype.val = some Q) :
    (orRule P d).1 = Q := by
  cases e : missRule P with
  | none => simp [e] at h
  | some r => simp only [e, Option.map_some, Option.some.injEq] at h; simp [orRule, h0, e, h]

/-- The miss rule fires when both copies of `E` rewrite to a cut of one map `K` on `til n`. -/
theorem missRule_val {n : Nat} {e : Int64} {E E₂ K K₂ : Prog .long .long}
    (hE : (rule E).map Subtype.val = some (anti K (pt e))) (hE₂ : (rule E₂).map Subtype.val = some (anti K₂ (pt e)))
    (hm : (mapOn? K).map PSigma.fst = some n) (hs : (sameKer K₂ K).isSome = true) (hn : n ≤ 2 ^ 63) :
    (missRule (union (comp (til n) E) (comp (anti (til n) (dom E₂)) (fn (@Fn.cst .long .long e))))).map Subtype.val =
      some K := by
  cases hr : rule E with
  | none => simp [hr] at hE
  | some r =>
  cases hr₂ : rule E₂ with
  | none => simp [hr₂] at hE₂
  | some r₂ =>
  cases hp : mapOn? K with
  | none => simp [hp] at hm
  | some p =>
  cases hk : sameKer K₂ K with
  | none => simp [hk] at hs
  | some k =>
  obtain ⟨Q, hQ⟩ := r; obtain ⟨Q₂, hQ₂⟩ := r₂; obtain ⟨m, hm'⟩ := p
  simp only [hr, Option.map_some, Option.some.injEq] at hE; simp only [hr₂, Option.map_some, Option.some.injEq] at hE₂
  simp only [hp, Option.map_some, Option.some.injEq] at hm
  subst hE hE₂ hm
  conv => lhs; arg 2; whnf
  rw [hr, hr₂]
  conv => lhs; arg 2; whnf
  rw [hp, hk]
  conv => lhs; arg 2; whnf
  rw [decRec_pos]
  · rfl
  · exact ⟨rfl, rfl, hn, rfl, rfl⟩

/-- `bin` normalised: one `binJ` bisection, its miss fill its own. -/
theorem bin_norm {nx ny : Nat} (x : Arr .long nx) (y : Arr .long ny) (hy : ny ≤ 2 ^ 63) :
    norm (bin x y) = binJ x y :=
  orRule_miss rfl (missRule_val (n := ny) (e := -1) (E := extr true (ojoin .ge (arr y) (arr x)))
    (E₂ := extr true (ojoin .ge (arr y) (arr x))) (K := binJ x y) (K₂ := binJ x y) rfl rfl rfl (sameKer_bin x y) hy)

/-- `aj`'s `E` rewrites to `ajJ` cut at `0N`. -/
theorem rule_aj {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) :
    (rule (extr true (inter (comp (arr lk) (conv (arr rk))) (ojoin .ge (arr lt) (arr rt))))).map Subtype.val =
      some (anti (ajJ lk lt rk rt) (pt Int64.minValue)) := by
  conv => lhs; arg 2; whnf
  simp only [asLen_self] <;> rfl

/-- `aj` normalised: one `ajJ` per-key bisection, its miss fill its own. -/
theorem aj_norm {nl nr : Nat} (lk lt : Arr .long nl) (rk rt : Arr .long nr) (hl : nl ≤ 2 ^ 63) :
    norm (aj lk lt rk rt) = ajJ lk lt rk rt :=
  orRule_miss rfl (missRule_val (n := nl) (e := Int64.minValue) (rule_aj lk lt rk rt) (rule_aj lk lt rk rt) rfl
    (sameKer_aj lk lt rk rt) hl)

/-- `wj1` normalised: its three order joins are `wjJ`'s window. -/
theorem wj1_norm {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    norm (wj1 lk w₀ w₁ rk rt) = wjJ false lk w₀ w₁ rk rt := by
  refine orRule_some (P := wj1 lk w₀ w₁ rk rt) ?_
  conv => lhs; arg 2; whnf
  simp only [asLen_self, sameArr_self] <;> rfl

/-- `wj` normalised: its window and prevailing row are `wjJ`'s. -/
theorem wj_norm {nl nr : Nat} (lk w₀ w₁ : Arr .long nl) (rk rt : Arr .long nr) :
    norm (wj lk w₀ w₁ rk rt) = wjJ true lk w₀ w₁ rk rt := by
  refine orRule_some (P := wj lk w₀ w₁ rk rt) ?_
  conv => lhs; arg 2; whnf
  simp only [asLen_self, sameArr_self] <;> rfl


end Prog

#print axioms Prog.norm_den
#print axioms Prog.exec_sound
#print axioms Prog.binE
#print axioms Prog.ajE
#print axioms Prog.miss_map
#print axioms Prog.elem_add_ofNat
#print axioms Prog.bin_norm
#print axioms Prog.aj_norm

end LeetQ.Rel
