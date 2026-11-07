/-
  §11.1 (Elementwise) and §11.2 (Search) of the RelRep design: the laws `kernel = spec` for the search
  verbs, each composing the kernel's `*_toList` (`Find`) with its List spec read as the §11 expression.
  A verb answering a list of positions (`&x`, `?x`) is stated for every list `enum` relates its set to,
  because `enum` lands in `dList`, not in `Idx ⟶ _`; `enum` is simple, so there is exactly one.
-/
import LeetQ.Rel.Spec
import AOP.A7_2_RelSet
import QLean.Verify.Chain
import QLean.Verify.Dyad
import QLean.Verify.EwEnc
import QLean.Verify.Gather

namespace LeetQ.Rel.Verb

open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-! ## vocabulary (general; to move into `Spec.lean`) -/

section Vocabulary

variable {A B : RelSet.{0}} {α : Type}

/-- The set a coreflexive holds, `{a ∣ C a a}`: what `enum(C)` enumerates. -/
def cset (C : A ⟶ A) : A.carrier → Prop := fun a => C a a

/-- `χ(ran R)` pointwise: `1b` on what `R` reaches, `0b` elsewhere. -/
theorem χ_ran_iff (R : A ⟶ B) (b0 : B.carrier) (b : Bool) :
    χ (ran R) b0 b ↔ ((∃ a, R a b0) ∧ b = true) ∨ ((¬ ∃ a, R a b0) ∧ b = false) := by
  show (∃ w, (b0 = w ∧ ∃ a, R a b0 ∧ R a w) ∧ b = true) ∨
    (∃ w, (b0 = w ∧ ∀ v, (v = b0 ∧ ∃ a, R a v ∧ R a b0) → False) ∧ b = false) ↔ _
  constructor
  · rintro (⟨_, ⟨rfl, a, h, _⟩, hb⟩ | ⟨_, ⟨rfl, hn⟩, hb⟩)
    · exact .inl ⟨⟨a, h⟩, hb⟩
    · exact .inr ⟨fun ⟨a, h⟩ => hn b0 ⟨rfl, a, h, h⟩, hb⟩
  · rintro (⟨⟨a, h⟩, hb⟩ | ⟨hn, hb⟩)
    · exact .inl ⟨b0, ⟨rfl, a, h, h⟩, hb⟩
    · exact .inr ⟨b0, ⟨rfl, fun _ ⟨_, a, _, h⟩ => hn ⟨a, h⟩⟩, hb⟩

/-- `contains` is the boolean list of `ran(ys)`: `graph(ys.contains) = χ(ran ys)`. -/
theorem ix_contains [BEq α] [LawfulBEq α] (ys : List α) :
    (graph (fun a => ys.contains a) : (⟨α⟩ : RelSet.{0}) ⟶ ⟨Bool⟩) = χ (ran (ix ys)) :=
  hom_ext fun a b => by
    refine Iff.trans ?_ (χ_ran_iff _ _ _).symm
    show b = ys.contains a ↔ _
    have hm : (∃ j, ix ys j a) ↔ ys.contains a = true := List.mem_iff_getElem?.symm.trans List.contains_iff_mem.symm
    cases hc : ys.contains a
    · have hn : ¬ ∃ j, ix ys j a := fun e => absurd (hm.1 e) (by rw [hc]; decide)
      simp only [hn, false_and, not_false_eq_true, true_and, false_or]
    · have he : ∃ j, ix ys j a := hm.2 hc
      simp only [he, true_and, not_true_eq_false, false_and, or_false]

/-- The least position holding `a` is `idxOf a`, and there is one exactly when `a ∈ xs`. -/
theorem idxOf_least [BEq α] [LawfulBEq α] (a : α) : ∀ (xs : List α) (b : Nat),
    (xs[b]? = some a ∧ ∀ z, xs[z]? = some a → b ≤ z) ↔ (a ∈ xs ∧ b = xs.idxOf a)
  | [], b => by simp
  | c :: xs, b => by
    rw [List.idxOf_cons]
    by_cases hc : c = a
    · subst hc
      simp only [beq_self_eq_true, cond_true, List.mem_cons_self, true_and]
      constructor
      · rintro ⟨_, h⟩; exact Nat.le_zero.1 (h 0 rfl)
      · rintro rfl; exact ⟨rfl, fun _ _ => Nat.zero_le _⟩
    · have hb : (c == a) = false := beq_eq_false_iff_ne.2 hc
      rw [hb, cond_false]
      cases b with
      | zero => simp [hc]
      | succ b =>
        have ih := idxOf_least a xs b
        constructor
        · rintro ⟨e, h⟩
          obtain ⟨m, hb'⟩ := ih.1 ⟨e, fun z hz => Nat.le_of_succ_le_succ (h (z+1) hz)⟩
          exact ⟨List.mem_cons_of_mem _ m, by omega⟩
        · rintro ⟨m, e⟩
          have m' : a ∈ xs := by
            rcases List.mem_cons.1 m with h | h
            · exact absurd h.symm hc
            · exact h
          obtain ⟨e1, h1⟩ := ih.2 ⟨m', by omega⟩
          refine ⟨e1, fun z hz => ?_⟩
          cases z with
          | zero => exact absurd (Option.some.inj hz) hc
          | succ z => exact Nat.succ_le_succ (h1 z hz)

/-- `idxOf` is the least position, `|xs|` at none: `graph(idxOf) = miss(Λ(xs°) ≫ est(≤), |xs|)`. -/
theorem ix_idxOf [BEq α] [LawfulBEq α] (xs : List α) :
    graph (fun a => xs.idxOf a) = miss (Λ ((ix xs)°) ≫ est (· ≤ ·)) xs.length :=
  hom_ext fun a b => by
    have key : ∀ c, (Λ ((ix xs)°) ≫ est (· ≤ ·)) a c ↔ a ∈ xs ∧ c = xs.idxOf a :=
      fun c => (Λ_comp_est_apply _ _ a c).trans (idxOf_least a xs c)
    rw [miss_iff]
    simp only [key]
    show b = xs.idxOf a ↔ _
    by_cases hm : a ∈ xs
    · simp [hm]
    · simp [hm, List.idxOf_eq_length hm]

/-- A key looked up in a key list `ks` beside values `vs`, `e` at a miss:
    `ix(xs.map (vs.getD (ks.idxOf ·) e)) = xs ≫ miss(Λ(ks°) ≫ est(≤) ≫ vs, e)`, `ks` and `vs` of one length. -/
theorem ix_lookup [BEq α] [LawfulBEq α] {β : Type} (xs ks : List α) (vs : List β) (e : β)
    (hl : ks.length = vs.length) :
    ix (xs.map fun k => vs.getD (ks.idxOf k) e) = ix xs ≫ miss ((Λ ((ix ks)°) ≫ est (· ≤ ·)) ≫ ix vs) e := by
  rw [ix_map]
  refine congrArg (ix xs ≫ ·) (hom_ext fun k b => ?_)
  have key : ∀ c, (Λ ((ix ks)°) ≫ est (· ≤ ·)) k c ↔ k ∈ ks ∧ c = ks.idxOf k :=
    fun c => (Λ_comp_est_apply _ _ k c).trans (idxOf_least k ks c)
  have hR : ∀ b', ((Λ ((ix ks)°) ≫ est (· ≤ ·)) ≫ ix vs) k b' ↔ k ∈ ks ∧ vs[ks.idxOf k]? = some b' :=
    fun b' => ⟨fun ⟨c, hc, hv⟩ => by obtain ⟨hm, rfl⟩ := (key c).1 hc; exact ⟨hm, hv⟩,
      fun ⟨hm, hv⟩ => ⟨_, (key _).2 ⟨hm, rfl⟩, hv⟩⟩
  rw [miss_iff]
  simp only [hR]
  show b = vs.getD (ks.idxOf k) e ↔ _
  by_cases hm : k ∈ ks
  · have hi : ks.idxOf k < vs.length := hl ▸ List.idxOf_lt_length_iff.2 hm
    simp [hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, eq_comm]
  · simp [hm, List.idxOf_eq_length hm, hl, List.getD_eq_getElem?_getD]

/-- On an ascending list, the positions holding at most `v` are those below `countP (· ≤ v)`. -/
theorem lt_countP_iff (v : Int64) : ∀ {xs : List Int64}, xs.Pairwise (· ≤ ·) → ∀ i,
    (∃ w, xs[i]? = some w ∧ w ≤ v) ↔ i < xs.countP (· ≤ v)
  | [], _, i => by simp
  | a :: as, hs, i => by
    rw [List.pairwise_cons] at hs
    rw [List.countP_cons]
    by_cases ha : a ≤ v
    · rw [if_pos (by simpa using ha)]
      cases i with
      | zero => simp [ha]
      | succ i => exact (lt_countP_iff v hs.2 i).trans (by omega)
    · have h0 : as.countP (· ≤ v) = 0 :=
        List.countP_eq_zero.2 fun w hw hwv => ha (Int64.le_trans (hs.1 w hw) (by simpa using hwv))
      rw [if_neg (by simpa using ha), h0]
      simp only [Nat.add_zero, Nat.not_lt_zero, iff_false]
      rintro ⟨w, hw, hwv⟩
      cases i with
      | zero => exact ha (Option.some.inj hw ▸ hwv)
      | succ i => exact ha (Int64.le_trans (hs.1 w (List.mem_of_getElem? hw)) hwv)

/-- `bin` on an ascending list is the greatest position at most `v`, `−1` at none:
    `graph(countP(≤ v) − 1) = miss(Λ((≥) ≫ xs°) ≫ est(≥) ≫ ofNat, −1)`. -/
theorem ix_bin (xs : List Int64) (hs : xs.Pairwise (· ≤ ·)) :
    (graph (fun v => Int64.ofNat (xs.countP (· ≤ v)) - 1) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩)
      = miss ((Λ (((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix xs)°) ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) (-1) :=
  hom_ext fun v b => by
    obtain ⟨c, hc⟩ : ∃ c, xs.countP (· ≤ v) = c := ⟨_, rfl⟩
    have hT : ∀ i, (((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix xs)°) v i ↔ i < c := fun i => by
      rw [← hc]
      exact ⟨fun ⟨w, hw, e⟩ => (lt_countP_iff v hs i).1 ⟨w, e, hw⟩,
        fun hi => let ⟨w, e, hw⟩ := (lt_countP_iff v hs i).2 hi; ⟨w, hw, e⟩⟩
    have hE : ∀ i, (Λ (((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix xs)°) ≫ est (· ≥ ·)) v i ↔ i + 1 = c :=
      fun i => by
        rw [Λ_comp_est_apply]
        simp only [hT]
        constructor
        · rintro ⟨h1, h2⟩; have := h2 (c - 1) (by omega); omega
        · intro e; exact ⟨by omega, fun z hz => by omega⟩
    have hC : ∀ b', ((Λ (((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix xs)°) ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) v b' ↔
        ∃ i, i + 1 = c ∧ b' = Int64.ofNat i := fun b' =>
      ⟨fun ⟨i, hi, e⟩ => ⟨i, (hE i).1 hi, e⟩, fun ⟨i, hi, e⟩ => ⟨i, (hE i).2 hi, e⟩⟩
    rw [miss_iff]
    simp only [hC]
    show b = Int64.ofNat (xs.countP (· ≤ v)) - 1 ↔ _
    rw [hc]
    cases c with
    | zero => simp
    | succ k => simp [Int64.ofNat_add]

/-- `eraseDups` is the list at the first occurrences, `firstsOf` of the list itself. -/
theorem eraseDups_firsts [BEq α] [LawfulBEq α] [DecidableEq α] [Inhabited α] (xs : List α) :
    xs.eraseDups = (Verify.firstsOf (fun i => xs[i]!) xs.length).map fun i => xs[i]! := by
  have hr : (List.range xs.length).map (fun i => xs[i]!) = xs :=
    List.ext_getElem (by simp) fun i h1 _ => by
      simp only [List.getElem_map, List.getElem_range]
      exact getElem!_pos xs i (by simpa using h1)
  rw [Find.firstsOf_map_eraseDups (fun i => xs[i]!) (fun i => xs[i]!) (fun _ _ => Iff.rfl), hr]

/-- `j` is a first occurrence: the least position of the value it holds. -/
theorem least_iff_firsts [Inhabited α] [DecidableEq α] (xs : List α) (j : Nat) :
    (∃ a, xs[j]? = some a ∧ ∀ z, xs[z]? = some a → j ≤ z) ↔ j ∈ Verify.firstsOf (fun i => xs[i]!) xs.length := by
  simp only [Verify.firstsOf, List.mem_filter, List.mem_range, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨a, e, hl⟩
    obtain ⟨hj, ej⟩ := List.getElem?_eq_some_iff.1 e
    refine ⟨hj, fun i hi he => ?_⟩
    have hi' : i < j := hi
    rw [getElem!_pos xs i (by omega), getElem!_pos xs j hj] at he
    have := hl i (List.getElem?_eq_some_iff.2 ⟨by omega, he.trans ej⟩)
    omega
  · rintro ⟨hj, hall⟩
    refine ⟨xs[j], List.getElem?_eq_getElem hj, fun z hz => ?_⟩
    obtain ⟨hz1, hz2⟩ := List.getElem?_eq_some_iff.1 hz
    refine Nat.le_of_not_lt fun hzj => hall z hzj ?_
    rw [getElem!_pos xs z hz1, getElem!_pos xs j hj, hz2]

/-- Positions in range read through `xs[·]!` are `ix xs`: `ix(L.map xs[·]!) = L ≫ xs`. -/
theorem ix_map_getElem! [Inhabited α] (L : List Nat) (xs : List α) (hL : ∀ j ∈ L, j < xs.length) :
    ix (L.map fun i => xs[i]!) = ix L ≫ ix xs :=
  (ix_map _ L).trans <| hom_ext fun k a =>
    ⟨fun ⟨j, hj, (e : a = xs[j]!)⟩ => ⟨j, hj, by
        rw [e, getElem!_pos xs j (hL j (List.mem_of_getElem? hj))]; exact List.getElem?_eq_getElem _⟩,
     fun ⟨j, hj, (e : xs[j]? = some a)⟩ => ⟨j, hj, by
        have hjl := hL j (List.mem_of_getElem? hj)
        show a = xs[j]!
        rw [getElem!_pos xs j hjl]; exact (Option.some.inj ((List.getElem?_eq_getElem hjl).symm.trans e)).symm⟩⟩

/-- The relation of a partial map: `a ↦ b` when `g a` answers `b`; where `g` errors nothing is related. -/
def ofExcept {ε β : Type} (g : α → Except ε β) : (⟨α⟩ : RelSet.{0}) ⟶ ⟨β⟩ := fun a b => g a = .ok b

/-- A `mapM` that succeeds is the list composed with the partial map: `ix(ys) = ix(l) ≫ ofExcept(g)`. -/
theorem ix_mapM {ε β : Type} (g : α → Except ε β) : ∀ (l : List α) (ys : List β), l.mapM g = .ok ys →
    ix ys = ix l ≫ ofExcept g
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hom_ext fun _ _ => ⟨fun e => (nomatch e), fun ⟨_, e, _⟩ => (nomatch e)⟩
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h
    cases ha : g a <;> cases hl : l.mapM g <;>
      simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h
    rename_i b bs
    subst h
    have ih := ix_mapM g l bs hl
    exact hom_ext fun j c => by
      cases j with
      | zero =>
        show some b = some c ↔ ∃ a', some a = some a' ∧ g a' = .ok c
        constructor
        · rintro ⟨⟩; exact ⟨a, rfl, ha⟩
        · rintro ⟨_, ⟨⟩, e⟩; rw [ha] at e; cases e; rfl
      | succ j => exact iff_of_eq (congrFun (congrFun ih j) c)

/-- Zipping is pairing: `ix(xs.zip ys) = ⟨ix xs, ix ys⟩`. -/
theorem ix_zip {β : Type} (xs : List α) (ys : List β) : ix (xs.zip ys) = rpair (ix xs) (ix ys) :=
  hom_ext fun _ p => by obtain ⟨a, b⟩ := p; exact List.getElem?_zip_eq_some

/-- Consing the seed is the previous element: `ix(s :: xs) = (shift ≫ xs) ∪ (corNeg(dom shift) ≫ !s)`. -/
theorem ix_cons (s : α) (xs : List α) :
    ix (s :: xs) = (shift ≫ ix xs) ∪ (corNeg (dom shift) ≫ (cst s : Idx ⟶ ⟨α⟩)) :=
  hom_ext fun (j : Nat) b => by
    cases j with
    | zero =>
      constructor
      · intro e
        exact Or.inr ⟨0, ⟨rfl, fun _ ⟨_, _, _, _, ⟨_, h1⟩, _⟩ => Nat.not_succ_le_zero 0 h1⟩, (Option.some.inj e).symm⟩
      · rintro (⟨_, ⟨_, ⟨_, h1⟩, _⟩, _⟩ | ⟨_, ⟨rfl, _⟩, rfl⟩)
        · exact absurd h1 (Nat.not_succ_le_zero 0)
        · rfl
    | succ j =>
      have h1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
      have h2 : j = j + 1 - 1 := (Nat.add_sub_cancel j 1).symm
      constructor
      · intro e; exact Or.inl ⟨j, ⟨j + 1, ⟨rfl, h1⟩, h2⟩, e⟩
      · rintro (⟨i, ⟨z, ⟨hz, _⟩, hi⟩, e⟩ | ⟨_, ⟨rfl, hn⟩, _⟩)
        · subst hz; subst hi; exact e
        · exact absurd (hn (j + 1) ⟨rfl, j, ⟨j + 1, ⟨rfl, h1⟩, h2⟩, ⟨j + 1, ⟨rfl, h1⟩, h2⟩⟩) id

/-- A constant on the left of a pair: `S ≫ ofExcept(g a) = ⟨!a, S⟩ ≫ ofExcept(g)`. -/
theorem pair_cst_left {C : RelSet.{0}} {β γ ε : Type} (a : α) (S : C ⟶ ⟨β⟩) (g : α → β → Except ε γ) :
    S ≫ ofExcept (g a) = rpair (cst a) S ≫ ofExcept (fun p : α × β => g p.1 p.2) :=
  hom_ext fun _ _ => ⟨fun ⟨b, hb, e⟩ => ⟨(a, b), ⟨rfl, hb⟩, e⟩,
    fun ⟨⟨_, b⟩, ⟨(ha : _ = a), hb⟩, e⟩ => ⟨b, hb, ha ▸ e⟩⟩

/-- A constant on the right of a pair: `S ≫ ofExcept(g · a) = ⟨S, !a⟩ ≫ ofExcept(g)`. -/
theorem pair_cst_right {C : RelSet.{0}} {β γ ε : Type} (a : α) (S : C ⟶ ⟨β⟩) (g : β → α → Except ε γ) :
    S ≫ ofExcept (fun b => g b a) = rpair S (cst a) ≫ ofExcept (fun p : β × α => g p.1 p.2) :=
  hom_ext fun _ _ => ⟨fun ⟨b, hb, e⟩ => ⟨(b, a), ⟨hb, rfl⟩, e⟩,
    fun ⟨⟨b, _⟩, ⟨hb, (ha : _ = a)⟩, e⟩ => ⟨b, hb, ha ▸ e⟩⟩

end Vocabulary

/-! ## §11.1 Elementwise: the List spec read as the expression

  No kernel theorem `kernel = List spec` exists yet for `Ew.mon`, `Ew.val`, `Ew.atomVal`, `Ew.valAtom` or
  `Ew.prior`; each law below takes that List spec as its hypothesis and proves the expression from it.
  A dyadic `f` is q's `Dep.elem`, a partial map (it can raise), read as `ofExcept`. -/

section Elementwise

variable {t u rt : QAtomicType} {n : Nat}

/-- `-x`, `%x`, … `= x ≫ f`, from the List spec `Ew.MapSpec`. -/
theorem mon_rel {f : Carrier t → Carrier rt} {x : Arr t n} {R : Arr rt n} (hs : Ew.MapSpec f x R) :
    R.rel = x.rel ≫ graph f :=
  calc R.rel = ix (x.toList.map f) := congrArg ix hs
    _ = x.rel ≫ graph f := ix_map ..

/-- `x+y = ⟨x, y⟩ ≫ (+)`, from the List spec `Ew.ValSpec`. -/
theorem val_rel {v : Prim.Dyadic} {h : Eval.ewType v t u = some rt} {x : Arr t n} {yv : Arr u n} {R : Arr rt n}
    (hs : Ew.ValSpec v h x yv R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
  calc R.rel = ix (x.toList.zip yv.toList) ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
        ix_mapM _ _ _ hs
    _ = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
        congrArg (· ≫ _) (ix_zip _ _)

/-- `a+x = ⟨!a, x⟩ ≫ (+)`, from the List spec `x.mapM (a f ·)`. -/
theorem atomVal_rel {v : Prim.Dyadic} {h : Eval.ewType v t u = some rt} {a : Carrier t} {x : Arr u n}
    {R : Arr rt n} (hs : x.toList.mapM (fun b => elem v h a b) = .ok R.toList) :
    R.rel = rpair (cst a) x.rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
  calc R.rel = x.rel ≫ ofExcept (elem v h a) := ix_mapM _ _ _ hs
    _ = rpair (cst a) x.rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
        pair_cst_left a x.rel (elem v h)

/-- `x+a = ⟨x, !a⟩ ≫ (+)`, from the List spec `x.mapM (· f a)`. -/
theorem valAtom_rel {v : Prim.Dyadic} {h : Eval.ewType v t u = some rt} {x : Arr t n} {a : Carrier u}
    {R : Arr rt n} (hs : x.toList.mapM (fun b => elem v h b a) = .ok R.toList) :
    R.rel = rpair x.rel (cst a) ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
  calc R.rel = x.rel ≫ ofExcept (fun b => elem v h b a) := ix_mapM _ _ _ hs
    _ = rpair x.rel (cst a) ≫ ofExcept (fun p : Carrier t × Carrier u => elem v h p.1 p.2) :=
        pair_cst_right a x.rel (elem v h)

/-- `seed f': x = ⟨x, prev⟩ ≫ f`, `prev = (shift ≫ x) ∪ (corNeg(dom shift) ≫ !seed)`, from the List spec
    `zip(x, seed :: x).mapM f`. -/
theorem prior_rel {v : Prim.Dyadic} {h : Eval.ewType v t t = some rt} {seed : Carrier t} {x : Arr t n}
    {R : Arr rt n} (hs : (x.toList.zip (seed :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst seed)) ≫
      ofExcept (fun p : Carrier t × Carrier t => elem v h p.1 p.2) :=
  calc R.rel = ix (x.toList.zip (seed :: x.toList)) ≫ ofExcept (fun p : Carrier t × Carrier t => elem v h p.1 p.2) :=
        ix_mapM _ _ _ hs
    _ = rpair x.rel (ix (seed :: x.toList)) ≫ ofExcept (fun p : Carrier t × Carrier t => elem v h p.1 p.2) :=
        congrArg (· ≫ _) (ix_zip _ _)
    _ = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst seed)) ≫
          ofExcept (fun p : Carrier t × Carrier t => elem v h p.1 p.2) :=
        congrArg (fun P => rpair x.rel P ≫ ofExcept (fun p : Carrier t × Carrier t => elem v h p.1 p.2)) (ix_cons _ _)

end Elementwise

/-! ## §11.1 Elementwise: kernel ⇒ List spec

  Each kernel theorem follows the one `dyadColumn`/`monColumn` path a column of one encoding takes, down
  to `Build.run` (qlean's `run_val`), and reads the answer back whichever form `Column.answer` leaves it in.
  Restricted to dense long `bytes` operands. -/

section Kernel

/-- q's null at `long` is the least long. -/
theorem nullPayload_long : Kernel.nullPayload .long = Int64.minValue := by decide

/-- A `long` answer `payload` lists the dense chain's words, encoded (`foRBits_encode_bits`) or decoded
    back (`elemsW_decode_encode`) by `Column.answer`. -/
theorem longWords_payload (bld : Kernel.Ew.Build) (last : Kernel.Ew.Stage) {n : Nat} (hn : n < USize.size)
    (hs : (bld.run last n.toUSize).size / 8 = n) :
    longWords n (Kernel.payload .long n.toUSize (bld, last)) = some (Verify.elemsW 8 (bld.run last n.toUSize)) := by
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hp : Kernel.payload .long n.toUSize (bld, last) = Enc.answer .long n
      (.foR (bld.runEnc last n.toUSize (8 : Nat).toUSize).1 (bld.runEnc last n.toUSize (8 : Nat).toUSize).2) := by
    simp only [Kernel.payload, hN]; rfl
  rw [hp]
  rcases Verify.answer_foR .long 8 n _ _ rfl with e | e <;> rw [e] <;> unfold longWords
  · simp only [Verify.elemsW]
    refine congrArg some ?_
    rw [hs]
    refine List.map_congr_left fun i hi => UInt64.toNat_inj.1 ?_
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    exact Verify.foRBits_encode_bits 8 (by decide) (by decide) _ i (Nat.lt_of_lt_of_eq (List.mem_range.1 hi) hs.symm)
  · exact congrArg some (Verify.runEnc_elems bld last n.toUSize 8 (by decide) (by decide) n.toUSize (by rw [hN, hs]))

/-- `dyadColumn` on two dense long columns of one count, at a value verb whose result is `long`: the
    one-stage `eVal` chain over the two payloads. -/
theorem dyadColumn_long_vv {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (a b : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.bytes a) n (.bytes b) =
      some (.long, .vector .long n (Kernel.payload .long n.toUSize ({ inputs := #[a, b] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) none) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va)]

/-- What `Ew.dyad` answers is the payload `dyadColumn` returned, once its type is the one asked for. -/
theorem dyad_enc {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat} {a b e : Enc}
    {R : Arr rt n} (hd : Kernel.dyadColumn v shape t u na a nb b = some (rt, .vector rt n e none))
    (hv : Ew.dyad v shape t u rt na a nb b n = .ok R) : R.enc = e := by
  unfold Ew.dyad at hv
  simp only [hd, ↓reduceIte, Arr.of] at hv
  split at hv
  · cases hv; rfl
  · cases hv

/-- The reading every `long` value kernel ends in: an answer listing the dense `vv` chain over two
    payloads that list the operands' words is `ValSpec`, whichever encoding the payloads came from. -/
theorem val_spec_words {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {A B : ByteArray}
    (hn : n < USize.size) (hx : longWords n x.enc = some (Verify.elemsW 8 A))
    (hy : longWords n yv.enc = some (Verify.elemsW 8 B)) (hA : A.size / 8 = n) (hB : B.size / 8 = n)
    (hR : longWords n R.enc = some (Verify.elemsW 8
      (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue A B n.toUSize))) :
    Ew.ValSpec v h x yv R := by
  rw [Verify.val_i64_vv _ _ _ _ _ hn] at hR
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.intStep op Int64.minValue p.1 p.2) := funext fun p => Ew.elem_long_val hop h p.1 p.2
  unfold Ew.ValSpec
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    Arr.toList_long R hR, Arr.toList_long x hx, Arr.toList_long yv hy]
  exact congrArg Except.ok (List.ext_getElem (by simp [Verify.elemsW, hA, hB]) fun i _ _ => by
    simp [Verify.elemsW])

/-- A boolean answer whose bitmap is the `i64` comparison pass over `p` and `q` lists that pass's steps. -/
theorem toList_cmp_bits {op shape : UInt8} {n : Nat} {R : Arr .boolean n} {p q : ByteArray} (hn : n < USize.size)
    (hc : R.enc = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 shape p q n.toUSize)) :
    R.toList = (List.range n).map fun i => Kernel.Ew.cmpStep op Kernel.Ew.i64
      (Kernel.Ew.elem Kernel.Ew.i64 p (Kernel.Ew.shapeIdx shape i).1)
      (Kernel.Ew.elem Kernel.Ew.i64 q (Kernel.Ew.shapeIdx shape i).2) := by
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 h2
  have hi : i < n := by simpa using h2
  rw [Arr.getElem_toList, Arr.get_bool_bits R hc, (Verify.cmp_bitAt _ _ _ _ _ _).2 i (by rw [hN]; omega)]
  simp [hN, hi]

/-- The reading every `long` comparison kernel ends in: a bitmap of the dense `vv` comparison over two
    payloads that list the operands' words is `ValSpec`. -/
theorem cmp_spec_words {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {A B : ByteArray} (hn : n < USize.size) (hx : longWords n x.enc = some (Verify.elemsW 8 A))
    (hy : longWords n yv.enc = some (Verify.elemsW 8 B)) (hA : A.size / 8 = n) (hB : B.size / 8 = n)
    (hc : R.enc = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv A B n.toUSize)) :
    Ew.ValSpec v h x yv R := by
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 p.1.toUInt64 p.2.toUInt64) :=
    funext fun p => Ew.elem_long_cmp hop h p.1 p.2
  unfold Ew.ValSpec
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    toList_cmp_bits hn hc, Arr.toList_long x hx, Arr.toList_long yv hy]
  exact congrArg Except.ok (List.ext_getElem (by simp [Verify.elemsW, hA, hB]) fun i _ _ => by
    simp [Verify.elemsW, Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16,
      Kernel.Ew.i32, Kernel.Ew.f32, Kernel.Ew.shapeIdx, Kernel.Ew.vv, Kernel.Ew.va, Kernel.Ew.av])

/-- A `long` answer whose chain runs as the dense `vv` value pass over `A` and `B` lists that pass's words. -/
theorem longWords_run_val {bld : Kernel.Ew.Build} {last : Kernel.Ew.Stage} {op : UInt8} {n : Nat}
    {A B : ByteArray} {C : Enc} (hn : n < USize.size) (hC : C = Kernel.payload .long n.toUSize (bld, last))
    (hrun : bld.run last n.toUSize =
      Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.nullPayload .long) A B n.toUSize) :
    longWords n C = some (Verify.elemsW 8
      (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue A B n.toUSize)) := by
  have hs : (bld.run last n.toUSize).size / 8 = n := by
    rw [hrun, ← Verify.val_size8, USize.toNat_ofNat_of_lt' hn]
  rw [hC, longWords_payload _ _ hn hs, hrun, nullPayload_long]

/-- **`Ew.val` at `long` on dense columns is `ValSpec`**: `dyadColumn_long_vv`, `run_val`, read by
    `val_spec_words`. -/
theorem val_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a b : ByteArray}
    (ha : x.enc = .bytes a) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  have hrun := Verify.run_val ({ inputs := #[a, b] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 Kernel.Ew.vv 0 1
    (Kernel.nullPayload .long) (by decide) (by decide) n.toUSize
  simp only [show (#[a, b] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, b] : Array ByteArray)[(1 : UInt8).toNat]! = b from rfl] at hrun
  exact val_spec_words hop h hn (by simp only [longWords, ha]) (by simp only [longWords, hb])
    (Arr.n_long_bytes x ha) (Arr.n_long_bytes yv hb) (longWords_run_val hn (dyad_enc (dyadColumn_long_vv hop hr n a b) hv) hrun)

/-- `dyadColumn` on two dense long columns of one count, at a comparison: the one-stage `eCmp` chain over
    the two payloads, answered as a bitmap. -/
theorem dyadColumn_long_vv_cmp {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (a b : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.bytes a) n (.bytes b) =
      some (.boolean, .vector .boolean n (Kernel.payload .boolean n.toUSize ({ inputs := #[a, b] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1, nul := 0 })) none) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource, Kernel.Ew.Build.input,
    Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va)]

/-- **A comparison at `long` on dense columns is `ValSpec`**: `dyadColumn_long_vv_cmp`, `run_cmp`, read by
    `cmp_spec_words`. -/
theorem cmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a b : ByteArray} (ha : x.enc = .bytes a) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  have hrun := Verify.run_cmp ({ inputs := #[a, b] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 Kernel.Ew.vv 0 1 0
    (by decide) (by decide) n.toUSize
  simp only [show (#[a, b] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, b] : Array ByteArray)[(1 : UInt8).toNat]! = b from rfl] at hrun
  exact cmp_spec_words hop h hn (by simp only [longWords, ha]) (by simp only [longWords, hb])
    (Arr.n_long_bytes x ha) (Arr.n_long_bytes yv hb)
    (by rw [dyad_enc (dyadColumn_long_vv_cmp hop hr n a b) hv, ← hrun]; simp [Kernel.payload])

/-- `x+y = ⟨x, y⟩ ≫ (+)` from the kernel: `val_rel` of `val_spec_long`. Dense long columns. -/
theorem val_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a b : ByteArray}
    (ha : x.enc = .bytes a) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (val_spec_long hop h ha hb hn hv)

/-- `x<y = ⟨x, y⟩ ≫ (<)` from the kernel: `val_rel` of `cmp_spec_long`. Dense long columns. -/
theorem cmp_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a b : ByteArray} (ha : x.enc = .bytes a) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (cmp_spec_long hop h ha hb hn hv)

/-- A long `foR` column lists the words of its decode at eight bytes, which holds `n` of them. -/
theorem longWords_of_foR {n : Nat} {e : Enc} {md pk : ByteArray} (hc : e = .foR md pk) (hn : n < USize.size) :
    longWords n e = some (Verify.elemsW 8 (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize)) ∧
      (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize).size / 8 = n := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk n.toUSize
  rw [h8, USize.toNat_ofNat_of_lt' hn] at hsz hg
  refine ⟨?_, by rw [hsz]; omega⟩
  simp only [longWords, hc]
  refine congrArg some (List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_)
  simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
  rw [hg i (by simpa using h1), Verify.ofNat_toNat_mod64]

/-- An encoded long answer lists its decode's words, whether `Enc.answer` keeps it or decodes it. -/
theorem longWords_answer_foR (m p : ByteArray) {n : Nat} (hn : n < USize.size) :
    longWords n (Enc.answer .long n (.foR m p)) =
      some (Verify.elemsW 8 (Kernel.Coc.decode (8 : Nat).toUSize m p n.toUSize)) := by
  rcases Verify.answer_foR .long 8 n m p rfl with e | e <;> rw [e]
  · exact (longWords_of_foR rfl hn).1
  · simp only [longWords]

/-- `dyadColumn` on two `foR` long columns of one count, at a value verb whose result is `long`:
    `foRValPayload`, which keeps `+ - *` encoded where `foRValVV` answers and decodes block by block
    (`foRVal`) otherwise. -/
theorem dyadColumn_long_vv_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (ma pa mb pb : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.foR ma pa) n (.foR mb pb) =
      some (.long, .vector .long n (match (if op == Kernel.Ew.add || op == Kernel.Ew.sub || op == Kernel.Ew.mul then
          Kernel.Ew.foRValVV op ma pa mb pb n.toUSize else none) with
        | some (m, p) => Enc.answer .long n (.foR m p)
        | none => Enc.answer .long n (.bytes (Kernel.Ew.foRVal op Kernel.Ew.i64 (Kernel.nullPayload .long)
            ma pa mb pb n.toUSize))) none) := by
  rcases hvv : Kernel.Ew.foRValVV op ma pa mb pb (USize.ofNat n) with _ | ⟨m, p⟩
  all_goals cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals simp only [Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul, Kernel.Ew.div, Kernel.Ew.fill, Kernel.Ew.lesser,
    Kernel.Ew.greater] at hvv
  all_goals simp [hr, hvv, Kernel.dyadColumn, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul,
    Kernel.Ew.div, Kernel.Ew.fill, Kernel.Ew.lesser, Kernel.Ew.greater]

/-- `dyadColumn` on two `foR` long columns of one count, at a comparison: `foRCmpVV`'s bitmap. -/
theorem dyadColumn_long_vv_cmp_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (ma pa mb pb : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.foR ma pa) n (.foR mb pb) =
      some (.boolean, .vector .boolean n (.bits (Kernel.Ew.foRCmpVV op ma pa mb pb n.toUSize)) none) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource, Kernel.Ew.Build.input,
    Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or]

/-- What `dyadColumn_long_vv_foR` answers lists the dense `vv` pass over the two decodes, kept encoded
    (`foRValVV_spec`) or decoded block by block (`foRVal`). -/
theorem longWords_val_foR (op : UInt8) (ma pa mb pb : ByteArray) {n : Nat} (hn : n < USize.size) :
    longWords n (match (if op == Kernel.Ew.add || op == Kernel.Ew.sub || op == Kernel.Ew.mul then
          Kernel.Ew.foRValVV op ma pa mb pb n.toUSize else none) with
        | some (m, p) => Enc.answer .long n (.foR m p)
        | none => Enc.answer .long n (.bytes (Kernel.Ew.foRVal op Kernel.Ew.i64 (Kernel.nullPayload .long)
            ma pa mb pb n.toUSize))) =
      some (Verify.elemsW 8 (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue
        (Kernel.Coc.decode (8 : Nat).toUSize ma pa n.toUSize) (Kernel.Coc.decode (8 : Nat).toUSize mb pb n.toUSize)
        n.toUSize)) := by
  split
  · rename_i m p hvv
    have hvv' : Kernel.Ew.foRValVV op ma pa mb pb n.toUSize = some (m, p) := by
      split at hvv
      · exact hvv
      · cases hvv
    rw [longWords_answer_foR m p hn]
    exact congrArg some (Verify.foRValVV_spec op ma pa mb pb n.toUSize m p hvv')
  · have hF : Kernel.Ew.foRVal op Kernel.Ew.i64 (Kernel.nullPayload .long) ma pa mb pb n.toUSize =
        Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue
          (Kernel.Coc.decode (8 : Nat).toUSize ma pa n.toUSize) (Kernel.Coc.decode (8 : Nat).toUSize mb pb n.toUSize)
          n.toUSize := by
      rw [nullPayload_long]; rfl
    have hs : (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue
        (Kernel.Coc.decode (8 : Nat).toUSize ma pa n.toUSize) (Kernel.Coc.decode (8 : Nat).toUSize mb pb n.toUSize)
        n.toUSize).size / 8 = n := by
      rw [← Verify.val_size8, USize.toNat_ofNat_of_lt' hn]
    rw [hF]
    exact longWords_answer _ hs

/-- **`Ew.val` at `long` on two `foR` columns is `ValSpec`**: `longWords_val_foR`, read by `val_spec_words`. -/
theorem val_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {ma pa mb pb : ByteArray}
    (ha : x.enc = .foR ma pa) (hb : yv.enc = .foR mb pb) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  obtain ⟨hy, hys⟩ := longWords_of_foR hb hn
  exact val_spec_words hop h hn hx hy hxs hys
    (by rw [dyad_enc (dyadColumn_long_vv_foR hop hr n ma pa mb pb) hv]; exact longWords_val_foR op ma pa mb pb hn)

/-- **A comparison at `long` on two `foR` columns is `ValSpec`**: `foRCmpVV`'s bitmap, read by
    `cmp_spec_words`. -/
theorem cmp_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {ma pa mb pb : ByteArray} (ha : x.enc = .foR ma pa) (hb : yv.enc = .foR mb pb) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  have hR : R.enc = .bits (Kernel.Ew.foRCmpVV op ma pa mb pb n.toUSize) := by
    unfold Ew.val at hv
    rw [ha, hb] at hv
    exact dyad_enc (dyadColumn_long_vv_cmp_foR hop hr n ma pa mb pb) hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  obtain ⟨hy, hys⟩ := longWords_of_foR hb hn
  exact cmp_spec_words hop h hn hx hy hxs hys (by rw [hR]; rfl)

/-- `x+y = ⟨x, y⟩ ≫ (+)` from the kernel on two `foR` columns: `val_rel` of `val_spec_long_foR`. -/
theorem val_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {ma pa mb pb : ByteArray}
    (ha : x.enc = .foR ma pa) (hb : yv.enc = .foR mb pb) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (val_spec_long_foR hop h ha hb hn hv)

/-- `x<y = ⟨x, y⟩ ≫ (<)` from the kernel on two `foR` columns: `val_rel` of `cmp_spec_long_foR`. -/
theorem cmp_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {ma pa mb pb : ByteArray} (ha : x.enc = .foR ma pa) (hb : yv.enc = .foR mb pb) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (cmp_spec_long_foR hop h ha hb hn hv)

/-! ### A mixed pair: one dense and one `foR` operand

  `zipPass` reads the `foR` side through an `eDecode` stage, so the chain has two stages: the decode, then
  the verb, which names the decode's answer by `slot0`. -/

/-- A build with one stage `d` of its own writes a two-stage program: `d`, then `last` (`Verify.prog_one`'s
    proof, one record longer). -/
theorem prog_two (b : Kernel.Ew.Build) (d : Kernel.Ew.Stage) (hb : b.stages = #[d]) (last : Kernel.Ew.Stage) :
    (b.prog last).size / Kernel.Ew.stageBytes = 2 ∧ Kernel.Ew.stageAt (b.prog last) 0 = d ∧
      Kernel.Ew.stageAt (b.prog last) 1 = last := by
  refine ⟨?_, by rw [Verify.stageAt_prog b last 0 (by simp [hb])]; simp [hb],
    by rw [Verify.stageAt_prog b last 1 (by simp [hb])]; simp [hb]⟩
  have hL : ∀ x ∈ (b.stages.push last).toList.map Kernel.Ew.Stage.bytes, x.size = Kernel.Ew.stageBytes :=
    fun x hx => by obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx; exact Verify.stage_bytes_size s
  have hs := (Verify.foldl_append_get Kernel.Ew.stageBytes _ hL ByteArray.empty).1
  have hp : b.prog last = ((b.stages.push last).toList.map Kernel.Ew.Stage.bytes).foldl (· ++ ·)
      ByteArray.empty := by
    simp only [Kernel.Ew.Build.prog, ← Array.foldl_toList, Array.toList_map]
  rw [hp, hs]; simp [hb, Kernel.Ew.stageBytes]

/-- **A decode stage then a value stage is `Ew.val`** over the payloads the value stage names, `slot0` naming
    the decode of the two inputs the decode stage names. -/
theorem run_val_decode (b : Kernel.Ew.Build) (d : Kernel.Ew.Stage) (hb : b.stages = #[d])
    (hd : d.engine = Kernel.Ew.eDecode) (hda : d.a < Kernel.Ew.slot0) (hdb : d.b < Kernel.Ew.slot0)
    (op cls shape sa sb : UInt8) (nul : Int64) (hsa : sa < Kernel.Ew.slot0 ∨ sa = Kernel.Ew.slot0)
    (hsb : sb < Kernel.Ew.slot0 ∨ sb = Kernel.Ew.slot0) (n : USize) :
    b.run { engine := Kernel.Ew.eVal, op, cls, shape, a := sa, b := sb, nul } n =
      Kernel.Ew.val op cls shape nul
        (if sa < Kernel.Ew.slot0 then b.inputs[sa.toNat]!
          else Kernel.Coc.decode (Kernel.Ew.width d.cls).toUSize b.inputs[d.a.toNat]! b.inputs[d.b.toNat]! n)
        (if sb < Kernel.Ew.slot0 then b.inputs[sb.toNat]!
          else Kernel.Coc.decode (Kernel.Ew.width d.cls).toUSize b.inputs[d.a.toNat]! b.inputs[d.b.toNat]! n) n := by
  obtain ⟨hk, h0, h1⟩ := prog_two b d hb { engine := Kernel.Ew.eVal, op, cls, shape, a := sa, b := sb, nul }
  simp only [Kernel.Ew.Build.run, Kernel.Ew.chain, hk, show List.range 2 = [0, 1] from rfl, List.foldl_cons,
    List.foldl_nil]
  rw [h0, h1]
  rcases hsa with hsa | rfl <;> rcases hsb with hsb | rfl <;>
    simp [*, Kernel.Ew.eVal, Kernel.Ew.eCmp, Kernel.Ew.eMon, Kernel.Ew.eWiden, Kernel.Ew.eBit,
      Kernel.Ew.eFloor, Kernel.Ew.eCast, Kernel.Ew.eTick, Kernel.Ew.eIds, Kernel.Ew.ePack, Kernel.Ew.eDecode]

/-- **A decode stage then a comparison stage is `Ew.cmp`** over the payloads the comparison names
    (`run_val_decode` at `eCmp`). -/
theorem run_cmp_decode (b : Kernel.Ew.Build) (d : Kernel.Ew.Stage) (hb : b.stages = #[d])
    (hd : d.engine = Kernel.Ew.eDecode) (hda : d.a < Kernel.Ew.slot0) (hdb : d.b < Kernel.Ew.slot0)
    (op cls shape sa sb : UInt8) (nul : Int64) (hsa : sa < Kernel.Ew.slot0 ∨ sa = Kernel.Ew.slot0)
    (hsb : sb < Kernel.Ew.slot0 ∨ sb = Kernel.Ew.slot0) (n : USize) :
    b.run { engine := Kernel.Ew.eCmp, op, cls, shape, a := sa, b := sb, nul } n =
      Kernel.Ew.cmp op cls shape
        (if sa < Kernel.Ew.slot0 then b.inputs[sa.toNat]!
          else Kernel.Coc.decode (Kernel.Ew.width d.cls).toUSize b.inputs[d.a.toNat]! b.inputs[d.b.toNat]! n)
        (if sb < Kernel.Ew.slot0 then b.inputs[sb.toNat]!
          else Kernel.Coc.decode (Kernel.Ew.width d.cls).toUSize b.inputs[d.a.toNat]! b.inputs[d.b.toNat]! n) n := by
  obtain ⟨hk, h0, h1⟩ := prog_two b d hb { engine := Kernel.Ew.eCmp, op, cls, shape, a := sa, b := sb, nul }
  simp only [Kernel.Ew.Build.run, Kernel.Ew.chain, hk, show List.range 2 = [0, 1] from rfl, List.foldl_cons,
    List.foldl_nil]
  rw [h0, h1]
  rcases hsa with hsa | rfl <;> rcases hsb with hsb | rfl <;>
    simp [*, Kernel.Ew.eVal, Kernel.Ew.eCmp, Kernel.Ew.eMon, Kernel.Ew.eWiden, Kernel.Ew.eBit,
      Kernel.Ew.eFloor, Kernel.Ew.eCast, Kernel.Ew.eTick, Kernel.Ew.eIds, Kernel.Ew.ePack, Kernel.Ew.eDecode]

/-- The decode stage `operandSource` adds for a `foR` long operand whose payloads are inputs `a` and `b`. -/
abbrev decodeStage (a b : UInt8) : Kernel.Ew.Stage := { engine := Kernel.Ew.eDecode, cls := Kernel.Ew.i64, a, b }

/-- `dyadColumn` on a dense and a `foR` long column, either order, at a value verb whose result is `long`:
    `zipPass`'s decode stage, then the `eVal` stage reading the dense input and `slot0`. -/
theorem dyadColumn_long_vv_mixed {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (a md pk : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.bytes a) n (.foR md pk) =
      some (.long, .vector .long n (Kernel.payload .long n.toUSize ({ stages := #[decodeStage 1 2], inputs := #[a, md, pk] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := Kernel.Ew.slot0,
          nul := Kernel.nullPayload .long })) none) ∧
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.foR md pk) n (.bytes a) =
      some (.long, .vector .long n (Kernel.payload .long n.toUSize ({ stages := #[decodeStage 0 1], inputs := #[md, pk, a] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := Kernel.Ew.slot0, b := 2,
          nul := Kernel.nullPayload .long })) none) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals constructor
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.Ew.Build.input, Kernel.Ew.Build.add, Kernel.Ew.i64, Kernel.Ew.bits, QAtomicType.width, Kernel.Ew.width, Kernel.Ew.u8, Kernel.Ew.i16,
    Kernel.Ew.i32, Kernel.Ew.f32, decodeStage,
    (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va), Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or]

/-- `dyadColumn` on a dense and a `foR` long column, either order, at a comparison: the decode stage, then the
    `eCmp` stage reading the dense input and `slot0`. -/
theorem dyadColumn_long_vv_cmp_mixed {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (a md pk : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.bytes a) n (.foR md pk) =
      some (.boolean, .vector .boolean n (Kernel.payload .boolean n.toUSize ({ stages := #[decodeStage 1 2], inputs := #[a, md, pk] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := Kernel.Ew.slot0,
          nul := 0 })) none) ∧
    Kernel.dyadColumn v Kernel.Ew.vv .long .long n (.foR md pk) n (.bytes a) =
      some (.boolean, .vector .boolean n (Kernel.payload .boolean n.toUSize ({ stages := #[decodeStage 0 1], inputs := #[md, pk, a] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := Kernel.Ew.slot0, b := 2,
          nul := 0 })) none) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals constructor
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource, Kernel.Ew.Build.input,
    Kernel.Ew.Build.add, Kernel.Ew.i64, Kernel.Ew.bits, QAtomicType.width, Kernel.Ew.width, Kernel.Ew.u8, Kernel.Ew.i16,
    Kernel.Ew.i32, Kernel.Ew.f32, decodeStage, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or]

/-- **`x f y` at `long` on a dense `x` and a `foR` `y` is `ValSpec`**: `dyadColumn_long_vv_mixed`,
    `run_val_decode`, read by `val_spec_words`. -/
theorem val_spec_long_bF {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a md pk : ByteArray}
    (ha : x.enc = .bytes a) (hb : yv.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  have hR := dyad_enc (dyadColumn_long_vv_mixed hop hr n a md pk).1 hv
  obtain ⟨hy, hys⟩ := longWords_of_foR hb hn
  have hrun := (run_val_decode { stages := #[decodeStage 1 2], inputs := #[a, md, pk] } _ rfl rfl (by decide)
    (by decide) op Kernel.Ew.i64 Kernel.Ew.vv 0 Kernel.Ew.slot0 (Kernel.nullPayload .long) (.inl (by decide))
    (.inr rfl) n.toUSize).trans (show _ = Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.nullPayload .long) a
      (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) n.toUSize by rw [if_pos (by decide), if_neg (by decide)]; rfl)
  exact val_spec_words hop h hn (by simp only [longWords, ha]) hy (Arr.n_long_bytes x ha) hys
    (longWords_run_val hn hR hrun)

/-- The answer of a `foR` long operand `f` a dense `b` lists the dense `vv` pass over the decode and `b`
    (`run_val_decode`). -/
theorem longWords_Fb {op : UInt8} {n : Nat} {md pk b : ByteArray} {C : Enc} (hn : n < USize.size)
    (hC : C = Kernel.payload .long n.toUSize ({ stages := #[decodeStage 0 1], inputs := #[md, pk, b] },
      { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := Kernel.Ew.slot0, b := 2,
        nul := Kernel.nullPayload .long })) :
    longWords n C = some (Verify.elemsW 8 (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue
      (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) b n.toUSize)) :=
  longWords_run_val hn hC ((run_val_decode { stages := #[decodeStage 0 1], inputs := #[md, pk, b] } _ rfl rfl
    (by decide) (by decide) op Kernel.Ew.i64 Kernel.Ew.vv Kernel.Ew.slot0 2 (Kernel.nullPayload .long) (.inr rfl)
    (.inl (by decide)) n.toUSize).trans (show _ = Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.nullPayload .long)
      (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) b n.toUSize by rw [if_neg (by decide), if_pos (by decide)]; rfl))

/-- **`x f y` at `long` on a `foR` `x` and a dense `y` is `ValSpec`**: `longWords_Fb`, read by `val_spec_words`. -/
theorem val_spec_long_Fb {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {md pk b : ByteArray}
    (ha : x.enc = .foR md pk) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  exact val_spec_words hop h hn hx (by simp only [longWords, hb]) hxs (Arr.n_long_bytes yv hb)
    (longWords_Fb hn (dyad_enc (dyadColumn_long_vv_mixed hop hr n b md pk).2 hv))

/-- **`x<y` at `long` on a dense `x` and a `foR` `y` is `ValSpec`**: `run_cmp_decode`, read by
    `cmp_spec_words`. -/
theorem cmp_spec_long_bF {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a md pk : ByteArray} (ha : x.enc = .bytes a) (hb : yv.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  have hR := dyad_enc (dyadColumn_long_vv_cmp_mixed hop hr n a md pk).1 hv
  obtain ⟨hy, hys⟩ := longWords_of_foR hb hn
  have hrun := (run_cmp_decode { stages := #[decodeStage 1 2], inputs := #[a, md, pk] } _ rfl rfl (by decide)
    (by decide) op Kernel.Ew.i64 Kernel.Ew.vv 0 Kernel.Ew.slot0 0 (.inl (by decide)) (.inr rfl) n.toUSize).trans
    (show _ = Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv a (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize)
      n.toUSize by rw [if_pos (by decide), if_neg (by decide)]; rfl)
  exact cmp_spec_words hop h hn (by simp only [longWords, ha]) hy (Arr.n_long_bytes x ha) hys
    (by rw [hR, ← hrun]; simp [Kernel.payload])

/-- The bitmap of a `foR` long operand `<` a dense `b` is the dense `vv` comparison over the decode and `b`
    (`run_cmp_decode`). -/
theorem bits_Fb {op : UInt8} {n : Nat} {md pk b : ByteArray} {C : Enc}
    (hC : C = Kernel.payload .boolean n.toUSize ({ stages := #[decodeStage 0 1], inputs := #[md, pk, b] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := Kernel.Ew.slot0, b := 2,
        nul := 0 })) :
    C = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize)
      b n.toUSize) := by
  rw [hC, ← (run_cmp_decode { stages := #[decodeStage 0 1], inputs := #[md, pk, b] } _ rfl rfl (by decide)
    (by decide) op Kernel.Ew.i64 Kernel.Ew.vv Kernel.Ew.slot0 2 0 (.inr rfl) (.inl (by decide)) n.toUSize).trans
    (show _ = Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) b
      n.toUSize by rw [if_neg (by decide), if_pos (by decide)]; rfl)]
  simp [Kernel.payload]

/-- **`x<y` at `long` on a `foR` `x` and a dense `y` is `ValSpec`**: `bits_Fb`, read by `cmp_spec_words`. -/
theorem cmp_spec_long_Fb {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {md pk b : ByteArray} (ha : x.enc = .foR md pk) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.val at hv
  rw [ha, hb] at hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  exact cmp_spec_words hop h hn hx (by simp only [longWords, hb]) hxs (Arr.n_long_bytes yv hb)
    (bits_Fb (dyad_enc (dyadColumn_long_vv_cmp_mixed hop hr n b md pk).2 hv))

/-- `x+y = ⟨x, y⟩ ≫ (+)` from the kernel on a dense `x` and a `foR` `y`: `val_rel` of `val_spec_long_bF`. -/
theorem val_rel_long_bF {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a md pk : ByteArray}
    (ha : x.enc = .bytes a) (hb : yv.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (val_spec_long_bF hop h ha hb hn hv)

/-- `x+y = ⟨x, y⟩ ≫ (+)` from the kernel on a `foR` `x` and a dense `y`: `val_rel` of `val_spec_long_Fb`. -/
theorem val_rel_long_Fb {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {md pk b : ByteArray}
    (ha : x.enc = .foR md pk) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (val_spec_long_Fb hop h ha hb hn hv)

/-- `x<y = ⟨x, y⟩ ≫ (<)` from the kernel on a dense `x` and a `foR` `y`: `val_rel` of `cmp_spec_long_bF`. -/
theorem cmp_rel_long_bF {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a md pk : ByteArray} (ha : x.enc = .bytes a) (hb : yv.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (cmp_spec_long_bF hop h ha hb hn hv)

/-- `x<y = ⟨x, y⟩ ≫ (<)` from the kernel on a `foR` `x` and a dense `y`: `val_rel` of `cmp_spec_long_Fb`. -/
theorem cmp_rel_long_Fb {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {md pk b : ByteArray} (ha : x.enc = .foR md pk) (hb : yv.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (cmp_spec_long_Fb hop h ha hb hn hv)

/-- A one-stage `eMon` chain is `Ew.mon` over the input payload it names (`Verify.run_val`'s proof). -/
theorem run_mon (b : Kernel.Ew.Build) (hb : b.stages = #[]) (op cls sa : UInt8) (nul : Int64)
    (ha : sa < Kernel.Ew.slot0) (n : USize) :
    b.run { engine := Kernel.Ew.eMon, op, cls, a := sa, nul } n = Kernel.Ew.mon op cls nul b.inputs[sa.toNat]! n := by
  obtain ⟨hk, h0⟩ := Verify.prog_one b hb { engine := Kernel.Ew.eMon, op, cls, a := sa, nul }
  simp only [Kernel.Ew.Build.run, Kernel.Ew.chain, hk, show List.range 1 = [0] from rfl, List.foldl_cons,
    List.foldl_nil]
  rw [h0]
  simp [ha, Kernel.Ew.eMon, Kernel.Ew.eVal, Kernel.Ew.eCmp]

/-- `Ew.mon` at `i64`, element by element: `monStep` of element `i` (`Verify.val_i64_vv`'s proof). -/
theorem mon_i64 (op : UInt8) (nul : Int64) (a : ByteArray) (n : Nat) (hn : n < USize.size) :
    Verify.elemsW 8 (Kernel.Ew.mon op Kernel.Ew.i64 nul a n.toUSize) =
      (List.range n).map fun i => Kernel.Ew.monStep op Kernel.Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8) := by
  rw [← Verify.elemsW_foldl (fun i => Kernel.Ew.monStep op Kernel.Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8))
    8 (by decide) (by decide) (List.range n) (fun _ _ => UInt64.toNat_lt _)]
  unfold Kernel.Ew.mon
  rw [USize.toNat_ofNat_of_lt' hn]
  rfl

/-- `monColumn "neg"` on a dense long column: the one-stage `eMon` chain over its payload. -/
theorem monColumn_neg_long (n : Nat) (a : ByteArray) :
    Kernel.monColumn "neg" .long n (.bytes a) = some (.long, Kernel.payload .long n.toUSize
      ({ inputs := #[a] },
        { engine := Kernel.Ew.eMon, op := Kernel.Ew.neg, cls := Kernel.Ew.i64, a := 0, nul := Kernel.nullPayload .long })) := by
  simp [Kernel.monColumn, Kernel.monResultType, Kernel.negType, Kernel.monPayload, Kernel.negAbsPayload,
    Kernel.mapPass, Kernel.operandSource, Kernel.clsOf, Kernel.Ew.Build.input, show Prim.nonNumeric .long = false by decide]

/-! ### Dicts with different keys: the kernels of `align`'s gather/fill branch -/

/-- `gatherFill` from a long source, `bytes` or `foR` (`longWords`), at a dense index: word `j` is the
    source's word at index word `j`, `fill` past the end (`elemsW_gatherBytes`; `gatherFoR` is `gatherBytes`
    on the decode). -/
theorem gatherFill_long {m : Nat} (y : Arr .long m) {ys : List UInt64} (hy : longWords m y.enc = some ys)
    (hm : m < USize.size) {fill : UInt64} {idx C : Nat × Enc} {ib : ByteArray}
    (hi : Enc.bytesOf .long idx.1 idx.2 = some ib) (hv : Ew.gatherFill .long fill m y.enc idx = .ok C) :
    ∃ B, C = (idx.1, .bytes B) ∧ B.size = 8 * (ib.size / 8) ∧
      Verify.elemsW 8 B = (Verify.elemsW 8 ib).map fun k => ys.getD k.toNat fill := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  -- both encodings gather from a dense payload `B0` of words `ys`: `bytes` itself, `foR` its decode
  obtain ⟨B0, hB0, hC⟩ : ∃ B0, Verify.elemsW 8 B0 = ys ∧
      C = (idx.1, .bytes (Kernel.gatherBytes (8 : Nat).toUSize fill B0 ib)) := by
    obtain ⟨B0, hB0 | ⟨md, pk, he, rfl⟩, -, hw0, -⟩ := Arr.dense_long y hy hm
    all_goals simp only [Ew.gatherFill, show QAtomicType.width .long = some 8 from rfl, hi, bind, Except.bind,
      pure, Except.pure] at hv
    · rw [hB0] at hv; cases hv; exact ⟨B0, hw0, rfl⟩
    · rw [he] at hv; cases hv
      exact ⟨_, hw0, rfl⟩
  subst hC
  refine ⟨_, rfl, ?_, ?_⟩
  · have := (Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8) fill B0 ib).1
    rwa [h8] at this
  · have e := Verify.elemsW_gatherBytes (8 : Nat).toUSize (by rw [h8]; decide) (by rw [h8]; exact Nat.le_refl 8)
      fill B0 ib
    rw [h8] at e
    rw [e, hB0]
    exact List.map_congr_left fun k _ => Verify.ofNat_toNat_mod64 _

/-- `x@i` at long, source and index each `bytes` or `foR` (`longWords`): word `j` is the source's word at index
    word `j` read unsigned, `0N` past the end (`gatherColumn_fixed_shape`, `elemsW_gatherBytes`). The index
    need only fit its count (`countFits`), which a dense index does at any length. -/
theorem gatherColumn_long {m k : Nat} (x : Arr .long m) {xs is : List UInt64} (hx : longWords m x.enc = some xs)
    (hm : m < USize.size) (i : Arr .long k) (hi : longWords k i.enc = some is) (hfi : Verify.countFits k i.enc)
    {c : Enc} (h : Kernel.gatherColumn .long m x.enc k i.enc = some c) :
    ∃ B, c = .bytes B ∧ B.size = k * 8 ∧
      Verify.elemsW 8 B = is.map fun j => xs.getD j.toNat 0x8000000000000000 := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hA : ∀ M P a, x.enc = .alp M P a → Column.alpF32 a = (8 == 4) := fun _ _ _ he => by
    simp [longWords, he] at hx
  obtain ⟨src, ix, hsrc, hix, rfl⟩ := Verify.gatherColumn_fixed_shape (t := .long) (w := 8) rfl m x.enc k i.enc c
    hA h
  obtain ⟨B, -, hB, hBw, -⟩ := Arr.dense_long x hx hm
  obtain rfl : B = src := Option.some.inj (hB.symm.trans hsrc)
  have hix8 : Verify.elemsW 8 ix = is := by
    rw [Verify.elemsW_index k i.enc i.wf hfi ix hix, Struct.raw_long i.wf hi]
  have hlen : is.length = k := by rw [← Arr.length_toList i, Arr.toList_long i hi, List.length_map]
  have hk8 : ix.size / 8 = k := by
    have := congrArg List.length hix8; simp only [Verify.elemsW, List.length_map, List.length_range] at this; omega
  have e := Verify.elemsW_gatherBytes (8 : Nat).toUSize (by rw [h8]; decide) (by rw [h8]; exact Nat.le_refl 8)
    ((Kernel.nullBits .long).getD 0) B ix
  have hs := (Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8)
    ((Kernel.nullBits .long).getD 0) B ix).1
  rw [h8] at e hs
  refine ⟨_, rfl, by rw [hs, hk8, Nat.mul_comm], ?_⟩
  rw [e, hBw, hix8]
  exact List.map_congr_left fun k _ => Verify.ofNat_toNat_mod64 _

section FoRRaze
open QLean.Kernel

/-- A residual read only looks at the bytes of its own field. -/
theorem resAt_congr {A B : ByteArray} {s s' w j : Nat}
    (h : ∀ k < (j * w + w + 7) / 8, A[s + k]? = B[s' + k]?) : Column.resAt A s w j = Column.resAt B s' w j := by
  unfold Column.resAt
  exact Verify.foldl_congr_mem _ (fun k hk a => by
    rw [List.mem_range'_1] at hk; rw [h k (by omega)]) _

/-- A block that ends inside `A` reads the same out of `A ++ B`. -/
theorem resAt_append_left {A B : ByteArray} {s w j : Nat} (hs : s + Column.blk * w / 8 ≤ A.size)
    (hj : j < Column.blk) : Column.resAt (A ++ B) s w j = Column.resAt A s w j :=
  resAt_congr fun k hk => Verify.ba_append_left _ _ _ (by
    have := Nat.mul_le_mul_right w (show j + 1 ≤ Column.blk from hj)
    rw [Nat.succ_mul] at this; simp only [Column.blk] at hs this; omega)

/-- A block of `B`, read in `A ++ B` past `A`. -/
theorem resAt_append_right (A B : ByteArray) (s w j : Nat) :
    Column.resAt (A ++ B) (A.size + s) w j = Column.resAt B s w j :=
  resAt_congr fun k _ => by rw [Nat.add_assoc]; exact Verify.ba_append_right _ _ _

theorem blockStart_succ (m : ByteArray) (b : Nat) :
    Column.blockStart m (b + 1) = Column.blockStart m b + Column.blk * Column.widthAt m b / 8 := by
  simp [Column.blockStart, Nat.fold_succ]

/-- Block starts past `a`, of a metadata whose widths there are `m'`'s. -/
theorem blockStart_add {m m' : ByteArray} (a : Nat) : ∀ d, (∀ c < d, Column.widthAt m (a + c) = Column.widthAt m' c) →
    Column.blockStart m (a + d) = Column.blockStart m a + Column.blockStart m' d
  | 0, _ => by simp [Column.blockStart]
  | d + 1, h => by
    rw [← Nat.add_assoc, blockStart_succ, blockStart_succ, blockStart_add a d fun c hc => h c (by omega),
      h d (by omega), Nat.add_assoc]

theorem blockStart_mono (m : ByteArray) {a b : Nat} (h : a ≤ b) : Column.blockStart m a ≤ Column.blockStart m b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [blockStart_succ]; omega

/-- An element the patch list does not hold: its block's base and frame plus its residual. -/
theorem foRBits_none {md pk : ByteArray} {i : Nat} (he : Column.foRExc md pk i = none)
    (hb : i / Column.blk ≤ Column.nblk md) :
    Column.foRBits md pk (Column.blockStarts md) i = Column.baseAt md (i / Column.blk) +
      Column.foRFrame md pk (i / Column.blk) +
      Column.resAt pk (Column.blockStart md (i / Column.blk)) (Column.widthAt md (i / Column.blk)) (i % Column.blk) := by
  simp only [Column.foRBits, he, Verify.blockStarts_get md hb]

/-- A pack with no patch list: element `i` is its block's base plus its residual. -/
theorem foRBits_plain {md pk : ByteArray} {i : Nat} (hp : pk.size ≤ Column.blockStart md (Column.nblk md))
    (hb : i / Column.blk ≤ Column.nblk md) :
    Column.foRBits md pk (Column.blockStarts md) i = Column.baseAt md (i / Column.blk) +
      Column.resAt pk (Column.blockStart md (i / Column.blk)) (Column.widthAt md (i / Column.blk)) (i % Column.blk) := by
  rw [foRBits_none (by simp [Column.foRExc, hp]) hb, show Column.foRFrame md pk (i / Column.blk) = 0 by
    simp [Column.foRFrame, hp], UInt64.add_zero]

/-- A writer-form pack reaches at least to its last block's end. -/
theorem foRWF_le {n : Nat} {md pk : ByteArray} (s : Verify.FoRWF n md pk) :
    Column.blockStart md (Column.nblk md) ≤ pk.size := by
  rcases s.size with h | h
  · omega
  · revert h; cases Coc.foRTail (Column.nblk md) pk (Column.blockStart md (Column.nblk md)) <;> simp <;> omega

/-- The patch list and the frames are read past the last block's residuals, out of the pack's size and the
    bytes there: two packs of one size that agree there agree on both. -/
theorem foRExc_congr {m A B : ByteArray} (hs : A.size = B.size)
    (h : ∀ k, A[Column.blockStart m (Column.nblk m) + k]? = B[Column.blockStart m (Column.nblk m) + k]?) (i b : Nat) :
    Column.foRExc m A i = Column.foRExc m B i ∧ Column.foRFrame m A b = Column.foRFrame m B b := by
  have key : ∀ d w, Column.bitsAt A (Column.blockStart m (Column.nblk m) + d) w =
      Column.bitsAt B (Column.blockStart m (Column.nblk m) + d) w :=
    fun d w => Column.bitsAt_congr B A _ w fun k _ => by rw [Nat.add_assoc]; exact h _
  have key0 : ∀ w, Column.bitsAt A (Column.blockStart m (Column.nblk m)) w =
      Column.bitsAt B (Column.blockStart m (Column.nblk m)) w := fun w => key 0 w
  exact ⟨by unfold Column.foRExc; simp only [hs, Nat.add_assoc, key, key0],
    by unfold Column.foRFrame; simp only [hs, Nat.add_assoc, key, key0]⟩

/-- The words a `foR` part of `n` elements denotes. -/
abbrev foRWords (n : Nat) (md pk : ByteArray) : List UInt64 := (List.range n).map (Column.foRBits md pk (Column.blockStarts md))

theorem widthAt_lt (m : ByteArray) (b : Nat) : Column.widthAt m b < 256 := UInt8.toNat_lt_size _

/-- A part's blocks as `moveFoR` copies them. -/
abbrev blocksOf (m : ByteArray) : Array (UInt64 × UInt64 × UInt64 × Nat) :=
  (Array.range (Column.nblk m)).map fun b => (Column.baseAt m b, Column.maxvAt m b, Column.bsumAt m b, Column.widthAt m b)

theorem blockStart_zero (m : ByteArray) : Column.blockStart m 0 = 0 := by simp [Column.blockStart]

/-- Two writer-form parts' blocks in turn and their packs in turn, the first filling its blocks: the words in turn. -/
theorem moved_words {n0 n1 : Nat} {m0 p0 m1 p1 : ByteArray} (s0 : Verify.FoRWF n0 m0 p0) (s1 : Verify.FoRWF n1 m1 p1)
    (z0 : p0.size = Column.blockStart m0 (Column.nblk m0)) (z1 : p1.size = Column.blockStart m1 (Column.nblk m1))
    (hn0 : n0 % Column.blk = 0) (nul : UInt64) (sumn : Nat) :
    foRWords (n0 + n1) (Coc.foRMeta nul sumn (blocksOf m0 ++ blocksOf m1)) (p0 ++ p1) =
      foRWords n0 m0 p0 ++ foRWords n1 m1 p1 := by
  have hw : ∀ b (h : b < (blocksOf m0 ++ blocksOf m1).size), (blocksOf m0 ++ blocksOf m1)[b].2.2.2 < 256 := by
    intro b h; simp only [Array.getElem_append, blocksOf]; split <;> simp [widthAt_lt]
  obtain ⟨hnb, hrd⟩ := Verify.foRMeta_reads nul sumn _ hw
  generalize Coc.foRMeta nul sumn (blocksOf m0 ++ blocksOf m1) = M at hnb hrd ⊢
  have hsz : (blocksOf m0 ++ blocksOf m1).size = Column.nblk m0 + Column.nblk m1 := by simp [blocksOf]
  have e0 : ∀ b < Column.nblk m0, Column.baseAt M b = Column.baseAt m0 b ∧ Column.widthAt M b = Column.widthAt m0 b := by
    intro b hb; obtain ⟨x, y⟩ := hrd b (by omega); rw [x, y]; simp [blocksOf, hb]
  have e1 : ∀ b < Column.nblk m1, Column.baseAt M (Column.nblk m0 + b) = Column.baseAt m1 b ∧
      Column.widthAt M (Column.nblk m0 + b) = Column.widthAt m1 b := by
    intro b hb; obtain ⟨x, y⟩ := hrd (Column.nblk m0 + b) (by omega); rw [x, y]; simp [blocksOf]
  have st0 : ∀ b ≤ Column.nblk m0, Column.blockStart M b = Column.blockStart m0 b := fun b hb => by
    have := blockStart_add (m := M) (m' := m0) 0 b fun c hc => by rw [Nat.zero_add]; exact (e0 c (by omega)).2
    rw [Nat.zero_add, blockStart_zero, Nat.zero_add] at this; exact this
  have st1 : ∀ b ≤ Column.nblk m1, Column.blockStart M (Column.nblk m0 + b) = p0.size + Column.blockStart m1 b :=
    fun b _ => by rw [blockStart_add _ b fun c hc => (e1 c (by omega)).2, st0 _ (Nat.le_refl _), z0]
  have hP : (p0 ++ p1).size ≤ Column.blockStart M (Column.nblk M) := by
    rw [hnb, hsz, st1 _ (Nat.le_refl _), ByteArray.size_append, z1]; exact Nat.le_refl _
  have hN0 : n0 = Column.blk * Column.nblk m0 := by rw [s0.nblk]; simp only [Column.blk] at hn0 ⊢; omega
  simp only [foRWords]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hb : i / Column.blk < Column.nblk m0 := by rw [hN0] at hi; simp only [Column.blk] at hi ⊢; omega
    rw [foRBits_plain hP (by rw [hnb, hsz]; omega), foRBits_plain (Nat.le_of_eq z0) (Nat.le_of_lt hb), st0 _ (Nat.le_of_lt hb), (e0 _ hb).1,
      (e0 _ hb).2, resAt_append_left (by rw [← blockStart_succ, z0]; exact blockStart_mono _ hb)
        (Nat.mod_lt _ (by decide))]
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hq : (n0 + i) / Column.blk = Column.nblk m0 + i / Column.blk ∧ (n0 + i) % Column.blk = i % Column.blk := by
      rw [hN0]; simp only [Column.blk]; omega
    have hb : i / Column.blk < Column.nblk m1 := by rw [s1.nblk]; simp only [Column.blk] at hi ⊢; omega
    simp only [Function.comp_apply]
    rw [foRBits_plain hP (by rw [hnb, hsz, hq.1]; omega), foRBits_plain (Nat.le_of_eq z1) (Nat.le_of_lt hb), hq.1, hq.2, st1 _ (Nat.le_of_lt hb),
      (e1 _ hb).1, (e1 _ hb).2, resAt_append_right]

/-- **`moveFoR` joins the words**: it claims only writer-form parts with no patch list, the first filling its
    blocks, and moves them whole. -/
theorem moveFoR_words {n0 n1 : Nat} {m0 p0 m1 p1 M P : ByteArray}
    (h : moveFoR #[((n0, m0), p0), ((n1, m1), p1)] = some (M, P)) :
    foRWords (n0 + n1) M P = foRWords n0 m0 p0 ++ foRWords n1 m1 p1 := by
  simp only [moveFoR] at h
  split at h
  · cases h
  rename_i hc
  have hn0 : n0 % Column.blk = 0 := by
    exact Decidable.byContradiction fun hne => hc (by simp [hne])
  have s0 : Verify.FoRWF n0 m0 p0 := Verify.foRStd_iff.1 (Decidable.byContradiction fun hne => hc (by simp [hne]))
  have s1 : Verify.FoRWF n1 m1 p1 := Verify.foRStd_iff.1 (Decidable.byContradiction fun hne => hc (by simp [hne]))
  have l0 : ¬ Column.blockStart m0 (Column.nblk m0) < p0.size := fun hl => hc (by simp [hl])
  have l1 : ¬ Column.blockStart m1 (Column.nblk m1) < p1.size := fun hl => hc (by simp [hl])
  have e0 := foRWF_le s0; have e1 := foRWF_le s1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
  have hbs : ∀ (f : Nat → ByteArray → UInt64 × UInt64 × UInt64 × Nat),
      (#[((n0, m0), p0), ((n1, m1), p1)] : Array _).foldl (init := (#[] : Array (UInt64 × UInt64 × UInt64 × Nat)))
        (fun acc p => acc ++ (Array.range (Column.nblk p.1.2)).map fun b => f b p.1.2) =
      (Array.range (Column.nblk m0)).map (f · m0) ++ (Array.range (Column.nblk m1)).map (f · m1) := by
    intro f; simp
  have hb := hbs fun b m => (Column.baseAt m b, Column.maxvAt m b, Column.bsumAt m b, Column.widthAt m b)
  simp only at hb
  rw [hb, show concatBytes (#[((n0, m0), p0), ((n1, m1), p1)].map (·.2)) = p0 ++ p1 by
    simp [concatBytes, ByteArray.empty_append]]
  exact moved_words s0 s1 (by omega) (by omega) hn0 _ _

/-- A residual holds `w` bits. -/
theorem resAt_lt (P : ByteArray) (s w j : Nat) : (Column.resAt P s w j).toNat < 2 ^ w := by
  unfold Column.resAt
  generalize List.range' _ _ = l
  suffices ∀ a : UInt64, a.toNat < 2 ^ w → (l.foldl (fun acc k =>
      acc ||| (Nat.div ((P[s + k]?.getD 0).toNat * 2 ^ (8 * k)) (2 ^ (j * w)) % 2 ^ w).toUInt64) a).toNat < 2 ^ w from
    this 0 (by simpa using Nat.two_pow_pos w)
  induction l with
  | nil => exact fun a h => h
  | cons k l ih =>
    intro a ha; apply ih; rw [UInt64.toNat_or]
    refine Nat.or_lt_two_pow ha ?_
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos w))

/-- An element's low `w` bytes: what a `w`-byte decode keeps of a `foR` word. -/
abbrev lowBytes (w : Nat) (a : UInt64) : UInt64 := UInt64.ofNat (a.toNat % 2 ^ (8 * w))

theorem lowBytes8 (l : List UInt64) : l.map (lowBytes 8) = l :=
  (List.map_congr_left fun a _ => Verify.ofNat_toNat_mod64 a).trans (List.map_id _)

theorem decode_words {w n : Nat} (hw : 0 < w ∧ w ≤ 8) (m p : ByteArray) (hn : n < USize.size) :
    (Coc.decode w.toUSize m p n.toUSize).size = w * n ∧
      Verify.elemsW w (Coc.decode w.toUSize m p n.toUSize) = (foRWords n m p).map (lowBytes w) := by
  obtain ⟨hsz, hg⟩ := Verify.decodeW w.toUSize (by rw [Verify.toUSize_toNat_of_le8 w hw.2]; exact hw.2) m p n.toUSize
  rw [Verify.toUSize_toNat_of_le8 w hw.2, USize.toNat_ofNat_of_lt' hn] at hsz hg
  refine ⟨hsz, List.ext_getElem (by simp [Verify.elemsW, hsz, Nat.mul_div_cancel_left n hw.1]) fun i h1 _ => ?_⟩
  simp only [Verify.elemsW, hsz, Nat.mul_div_cancel_left n hw.1, List.length_map, List.length_range] at h1
  simp only [Verify.elemsW, foRWords, List.getElem_map, List.getElem_range]
  rw [hg i h1]

/-- **`appendFoR` joins the words**: the tail's words written as residuals into the first part's last block. It
    claims only a writer-form first part with no exception past its count in that block; a patch list rides along
    at the same offset, so every element the first part had reads the same. -/
theorem appendFoR_words {n0 n1 : Nat} {m0 p0 m1 p1 M P : ByteArray} (hn1 : n1 < USize.size)
    (h : appendFoR n0 m0 p0 (Coc.decode (8 : Nat).toUSize m1 p1 n1.toUSize) = some (M, P)) :
    foRWords (n0 + n1) M P = foRWords n0 m0 p0 ++ foRWords n1 m1 p1 := by
  obtain ⟨hTs, hTw⟩ := decode_words (w := 8) (by decide) m1 p1 hn1
  rw [lowBytes8] at hTw
  generalize Coc.decode (8 : Nat).toUSize m1 p1 n1.toUSize = T at hTs hTw h
  have hv : ∀ j < n1, Column.bitsAt T (j * 8) 8 = Column.foRBits m1 p1 (Column.blockStarts m1) j := by
    intro j hj
    have := congrArg (·[j]?) hTw
    simp only [Verify.elemsW, foRWords, List.getElem?_map, List.getElem?_range (show j < T.size / 8 by omega),
      List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this
  have hm : T.size / 8 = n1 := by omega
  simp only [appendFoR, hm] at h
  split at h; · cases h
  rename_i hc1
  split at h; · cases h
  rename_i hc2
  obtain ⟨hM, hPe⟩ := Prod.mk.inj (Option.some.inj h)
  subst hM hPe
  have hlo : ¬ n0 % Column.blk = 0 := fun e => hc1 (by simp [e])
  have hlm : n0 % Column.blk + n1 ≤ Column.blk := Nat.not_lt.1 fun e => hc1 (by simp [e])
  have s0 : Verify.FoRWF n0 m0 p0 := Verify.foRStd_iff.1 (Decidable.byContradiction fun e => hc1 (by simp [e]))
  have hexc : ∀ j < Column.blk - n0 % Column.blk, Column.foRExc m0 p0 (n0 + j) = none := fun j hj =>
    Option.not_isSome_iff_eq_none.1 fun e => hc1 (by
      rw [Bool.or_eq_true]; exact .inr (List.any_eq_true.2 ⟨j, List.mem_range.2 hj, e⟩))
  have hle := foRWF_le s0
  simp only [List.any_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, not_exists, not_and,
    not_or, Nat.not_le] at hc2
  generalize hb : n0 / Column.blk = b at *
  have hbn : b < Column.nblk m0 := by rw [s0.nblk, ← hb]; simp only [Column.blk] at hlo ⊢; omega
  have hse : Column.blockStart m0 b + Column.blk * Column.widthAt m0 b / 8 ≤ Column.blockStart m0 (Column.nblk m0) := by
    rw [← blockStart_succ]; exact blockStart_mono _ hbn
  have hw64 : Column.widthAt m0 b ≤ 64 := s0.width b hbn
  generalize hs : Column.blockStart m0 b = s at *
  generalize hw : Column.widthAt m0 b = w at *
  generalize hF : Column.foRFrame m0 p0 b = F at *
  generalize hE : p0.extract 0 s = E
  have hEs : E.size = s := by rw [← hE, ByteArray.size_extract]; omega
  have hp0 : p0 = E ++ p0.extract s p0.size := by
    rw [← hE, ← ByteArray.extract_eq_extract_append_extract s (Nat.zero_le _) (by omega), ByteArray.extract_zero_size]
  have hp1 : p0 = p0.extract 0 (s + Column.blk * w / 8) ++ p0.extract (s + Column.blk * w / 8) p0.size := by
    rw [← ByteArray.extract_eq_extract_append_extract _ (Nat.zero_le _) (by omega), ByteArray.extract_zero_size]
  generalize hX : p0.extract 0 (s + Column.blk * w / 8) = X at hp1
  have hXs : X.size = s + Column.blk * w / 8 := by rw [← hX, ByteArray.size_extract]; omega
  generalize hC : p0.extract (s + Column.blk * w / 8) p0.size = C at hp1
  generalize hQ : Coc.packRes w _ = Q
  have hQs : Q.size = Column.blk * w / 8 := by rw [← hQ, Verify.packRes_size]
  have hCs : C.size = p0.size - (s + Column.blk * w / 8) := by rw [← hC, ByteArray.size_extract]; omega
  have hcong := foRExc_congr (m := m0) (A := E ++ Q ++ C) (B := p0)
    (by rw [ByteArray.size_append, ByteArray.size_append, hEs, hQs, hCs]; omega) (fun k => by
      conv => rhs; rw [hp1]
      rw [Verify.ba_append_right' _ _ _ (by rw [ByteArray.size_append, hEs, hQs]; omega),
        Verify.ba_append_right' _ _ _ (by rw [hXs]; omega), ByteArray.size_append, hEs, hQs, hXs])
  have hQk : ∀ k < Column.blk * w / 8, (E ++ Q ++ C)[s + k]? = Q[k]? := fun k hk => by
    rw [Verify.ba_append_left _ _ _ (by rw [ByteArray.size_append, hEs, hQs]; omega), ← hEs, Verify.ba_append_right]
  have hpk := fun j (hj : j < Column.blk) => Verify.resAt_packRes w hw64 _ (E ++ Q ++ C) s
    (fun k hk => by rw [hQk k hk, ← hQ]) j hj
  have tn : ∀ a : UInt64, (a.toNat).toUInt64 = a := fun a => by simp
  have cancel : ∀ a c : UInt64, a + (c - a) = c := fun a c => by rw [UInt64.add_comm]; exact UInt64.sub_add_cancel c a
  simp only [foRWords]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hib : i / Column.blk ≤ b := by rw [← hb]; exact Nat.div_le_div_right (Nat.le_of_lt hi)
    cases hx : Column.foRExc m0 p0 i with
    | some v => simp only [Column.foRBits, (hcong i 0).1, hx]
    | none =>
    rw [foRBits_none ((hcong i 0).1.trans hx) (by omega), foRBits_none hx (by omega), (hcong 0 (i / Column.blk)).2]
    congr 1
    rcases Nat.lt_or_eq_of_le hib with hlt | heq
    · have hend : Column.blockStart m0 (i / Column.blk) + Column.blk * Column.widthAt m0 (i / Column.blk) / 8 ≤ s := by
        rw [← blockStart_succ, ← hs]; exact blockStart_mono _ hlt
      have hj := Nat.mod_lt i (show 0 < Column.blk by decide)
      rw [resAt_append_left (by rw [ByteArray.size_append, hEs]; omega) hj, resAt_append_left (by rw [hEs]; exact hend) hj]
      conv => rhs; rw [hp0]
      rw [resAt_append_left (by rw [hEs]; exact hend) hj]
    · have hj : i % Column.blk < n0 % Column.blk := by rw [← hb] at heq; simp only [Column.blk] at heq ⊢; omega
      rw [heq, hs, hw, hpk _ (Nat.mod_lt _ (by decide))]
      simp only [Nat.not_le.2 hj, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
      rw [Nat.mod_eq_of_lt (resAt_lt _ _ _ _), tn]
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    have hq : (n0 + i) / Column.blk = b ∧ (n0 + i) % Column.blk = n0 % Column.blk + i := by
      rw [← hb]; simp only [Column.blk] at hlm hlo ⊢; omega
    simp only [Function.comp_apply]
    rw [foRBits_none ((hcong (n0 + i) 0).1.trans (hexc i (by omega))) (by rw [hq.1]; omega), hq.1, hq.2, hs, hw,
      (hcong 0 b).2, hF, hpk _ (by omega)]
    simp only [Nat.le_add_right, decide_true, Nat.add_lt_add_iff_left, hi, Bool.and_self, if_true,
      Nat.add_sub_cancel_left]
    rw [Nat.mod_eq_of_lt ((hc2 i hi).2), tn, cancel, hv i hi]

theorem encode_words {w : Nat} (hw : 1 < w ∧ w ≤ 8) (x : ByteArray) (hn : x.size / w < USize.size) :
    (foRWords (x.size / w) (Coc.encode w.toUSize x).1 (Coc.encode w.toUSize x).2).map (lowBytes w) =
      Verify.elemsW w x := by
  rw [← (decode_words ⟨by omega, hw.2⟩ _ _ hn).2, Verify.elemsW_decode_encode w hw.1 hw.2 x _
    (by rw [USize.toNat_ofNat_of_lt' hn])]

/-- A part at a type `encodes` takes: `bytes` of `w * n` bytes, or `foR`. -/
theorem fixed_parts {t : QAtomicType} {w n : Nat} (hw : t.width = some w) (he : Column.encodes t = true)
    (x : Arr t n) : (∃ B, x.enc = .bytes B ∧ B.size = w * n) ∨ ∃ md pk, x.enc = .foR md pk := by
  have hwf := x.wf
  generalize x.enc = e at hwf ⊢
  cases t <;> cases e <;> simp_all [Enc.WF, Column.encodes, QAtomicType.width, Nat.mul_comm]

theorem alp_fixed {t : QAtomicType} (he : Column.encodes t = true) : Column.alpEncodes t = false := by
  cases t <;> simp_all [Column.encodes, Column.alpEncodes]

theorem width_fixed {t : QAtomicType} {w : Nat} (hw : t.width = some w) (he : Column.encodes t = true) :
    1 < w ∧ w ≤ 8 := by
  cases t <;> simp_all [Column.encodes, QAtomicType.width] <;> omega

/-- A part at a type `alpEncodes` takes: `bytes` of `w * n` bytes, `foR` (which `WF` admits at every fixed width
    but boolean and guid), or `alp`. -/
theorem alp_parts {t : QAtomicType} {w n : Nat} (hw : t.width = some w) (ha : Column.alpEncodes t = true)
    (x : Arr t n) : (∃ B, x.enc = .bytes B ∧ B.size = w * n) ∨ (∃ md pk, x.enc = .foR md pk) ∨
      ∃ md pk a, x.enc = .alp md pk a := by
  have hwf := x.wf
  generalize x.enc = e at hwf ⊢
  cases t <;> cases e <;> simp_all [Enc.WF, Column.alpEncodes, QAtomicType.width, Nat.mul_comm]

theorem alp_width {t : QAtomicType} {w : Nat} (hw : t.width = some w) (ha : Column.alpEncodes t = true) :
    w = 4 ∨ w = 8 := by
  cases t <;> simp_all [Column.alpEncodes, QAtomicType.width] <;> omega

/-- `alpDecode` at a width `w ≤ 8`: `w * n` bytes, word `i` of them `alpBits` cut to `w` bytes. -/
theorem alpDecode_words {w : Nat} (hw : 0 < w ∧ w ≤ 8) (M P a : ByteArray) {n : Nat} (hn : n < USize.size) :
    (Coc.alpDecode w.toUSize M P a n.toUSize).size = w * n ∧ ∀ i < n,
      Column.bitsAt (Coc.alpDecode w.toUSize M P a n.toUSize) (i * w) w =
        UInt64.ofNat ((Column.alpBits M P a #[] i).toNat % 2 ^ (8 * w)) := by
  have hwU := Verify.toUSize_toNat_of_le8 w hw.2
  have hnU := USize.toNat_ofNat_of_lt' hn
  have hl : (Coc.alpElems M P a n.toUSize).length = n := by simp [Coc.alpElems, hnU]
  obtain ⟨hs, -, hg⟩ := Verify.foldl_pushBits id w.toUSize.toNat (by rw [hwU]; exact hw.2)
    (Coc.alpElems M P a n.toUSize) ByteArray.empty
  refine ⟨?_, fun i hi => ?_⟩
  · rw [← Verify.alpDecode_eq] at hs
    rw [hs, hwU, hl, show ByteArray.empty.size = 0 from rfl, Nat.zero_add]
  · have := hg i (by rw [hl]; exact hi)
    rw [← Verify.alpDecode_eq, hwU, show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Nat.mul_comm w i] at this
    rw [this]; simp [Coc.alpElems, hnU, alpBits_starts]

/-- `concatALP`'s width and flag at an ALP element width: four bytes is `real`'s `f32`. -/
theorem alpFlag {w : Nat} (hw : w = 4 ∨ w = 8) :
    (if w.toUSize == 4 then (4 : USize) else 8) = w.toUSize ∧ (if w.toUSize == 4 then 4 else 8) = w := by
  have h4 : (4 : USize).toNat = 4 := Verify.toUSize_toNat_of_le8 4 (by decide)
  rcases hw with rfl | rfl
  · rw [show ((4 : Nat).toUSize == 4) = true from beq_self_eq_true _]; exact ⟨rfl, rfl⟩
  · have h8 := Verify.toUSize_toNat_of_le8 8 (by decide)
    rw [show ((8 : Nat).toUSize == 4) = false from beq_eq_false_iff_ne.2 fun h => by
      have := congrArg USize.toNat h; rw [h8, h4] at this; exact absurd this (by decide)]
    exact ⟨rfl, rfl⟩

/-- `razeColumn`'s dense arm: both parts' dense forms, joined. -/
theorem raze_dense {t : QAtomicType} {w na nb : Nat} {ea eb : Enc} {v : QValue} (hw : t.width = some w)
    (hd : (match t.width, (#[(na, ea), (nb, eb)] : Array (Nat × Enc)).mapM fun (n, e) => Enc.bytesOf t n e with
      | some w, some ps =>
        if ((#[(na, ea), (nb, eb)] : Array (Nat × Enc)).zip ps).any fun ((n, _), b) => b.size < n * w then none
        else some (QValue.vector t ((#[(na, ea), (nb, eb)] : Array (Nat × Enc)).foldl (· + ·.1) 0)
          (.bytes (concatBytes ps)) none)
      | _, _ => none) = some v) :
    ∃ D0 D1, Enc.bytesOf t na ea = some D0 ∧ Enc.bytesOf t nb eb = some D1 ∧
      v = .vector t (na + nb) (.bytes (concatBytes #[D0, D1])) none := by
  rw [hw] at hd
  cases h0 : Enc.bytesOf t na ea <;> cases h1 : Enc.bytesOf t nb eb <;> simp_all

/-- `razeColumn` at a type `encodes` takes: the dense join, or `concatFoR`'s answer where `encodedParts` claims. -/
theorem raze_fixed {t : QAtomicType} {w na nb : Nat} {ea eb : Enc} {v : QValue} (hw : t.width = some w)
    (he : Column.encodes t = true) (h : razeColumn t #[(na, ea), (nb, eb)] = some v) :
    (∃ D0 D1, Enc.bytesOf t na ea = some D0 ∧ Enc.bytesOf t nb eb = some D1 ∧
      v = .vector t (na + nb) (.bytes (concatBytes #[D0, D1])) none) ∨
    ∃ n ns ms ps es, encodedParts t #[(na, ea), (nb, eb)] = some (false, n, ns, ms, ps, es) ∧
      v = .vector t n (Enc.answer t n (.foR (concatFoR w.toUSize ns ms ps).1 (concatFoR w.toUSize ns ms ps).2)) none := by
  have halp := alp_fixed he
  unfold razeColumn at h
  simp only [show (#[(na, ea), (nb, eb)] : Array (Nat × Enc)).isEmpty = false from rfl, Bool.false_eq_true,
    if_false] at h
  split at h
  · simp [Column.encodes] at he
  · simp [Column.encodes] at he
  cases hE : encodedParts t #[(na, ea), (nb, eb)] with
  | none => simp only [hE] at h; exact .inl (raze_dense hw h)
  | some r =>
    obtain ⟨alp, n, ns, ms, ps, as⟩ := r
    have hal : alp = false := by
      have key : ∀ {α β : Type} (o : Option α) (f : α → β) (r : β),
          (o.bind fun x => some (false, f x)) = some (alp, r) → alp = false := by
        intro α β o f r h; cases o <;> simp_all
      have := hE; simp [encodedParts, halp] at this
      exact key _ _ _ this.2
    subst hal
    simp only [hE, hw, Bool.false_eq_true, if_false] at h
    by_cases hd : denseCheaper 5 n w (straddles ns) = true
    · simp only [hd, if_true] at h; left; cases h0 : Enc.bytesOf t na ea <;> cases h1 : Enc.bytesOf t nb eb <;> simp_all
    · simp only [hd, Bool.false_eq_true, if_false, Option.some.injEq] at h
      exact .inr ⟨n, ns, ms, ps, as, rfl, h.symm⟩

/-- `razeColumn` at a type `alpEncodes` takes: the dense join, or `concatALP`'s answer where `encodedParts` claims. -/
theorem raze_alp {t : QAtomicType} {w na nb : Nat} {ea eb : Enc} {v : QValue} (hw : t.width = some w)
    (ha : Column.alpEncodes t = true) (h : razeColumn t #[(na, ea), (nb, eb)] = some v) :
    (∃ D0 D1, Enc.bytesOf t na ea = some D0 ∧ Enc.bytesOf t nb eb = some D1 ∧
      v = .vector t (na + nb) (.bytes (concatBytes #[D0, D1])) none) ∨
    ∃ n ns ms ps es, encodedParts t #[(na, ea), (nb, eb)] = some (true, n, ns, ms, ps, es) ∧
      v = .vector t n (Enc.answer t n (.alp (concatALP w.toUSize ns ms ps es).1 (concatALP w.toUSize ns ms ps es).2.1
        (concatALP w.toUSize ns ms ps es).2.2)) none := by
  unfold razeColumn at h
  simp only [show (#[(na, ea), (nb, eb)] : Array (Nat × Enc)).isEmpty = false from rfl, Bool.false_eq_true,
    if_false] at h
  split at h
  · simp [Column.alpEncodes] at ha
  · simp [Column.alpEncodes] at ha
  cases hE : encodedParts t #[(na, ea), (nb, eb)] with
  | none => simp only [hE] at h; exact .inl (raze_dense hw h)
  | some r =>
    obtain ⟨alp, n, ns, ms, ps, as⟩ := r
    have hal : alp = true := by
      have key : ∀ {α β : Type} (o : Option α) (f : α → β) (r : β),
          (o.bind fun x => some (true, f x)) = some (alp, r) → alp = true := by
        intro α β o f r h; cases o <;> simp_all
      have := hE; simp [encodedParts, ha] at this
      exact key _ _ _ this.2
    subst hal
    simp only [hE, hw, ↓reduceIte] at h
    by_cases hd : denseCheaper 8 n 8 (straddles ns) = true
    · simp only [hd, if_true] at h; left; cases h0 : Enc.bytesOf t na ea <;> cases h1 : Enc.bytesOf t nb eb <;> simp_all
    · simp only [hd, Bool.false_eq_true, if_false, Option.some.injEq] at h
      exact .inr ⟨n, ns, ms, ps, as, rfl, h.symm⟩

/-- An ALP answer's dense form, whichever form `answer` leaves it in, is its decode at the type's width. -/
theorem bytesOf_answer_alp {t : QAtomicType} {w n : Nat} (hw : t.width = some w) (M P A : ByteArray) :
    Enc.bytesOf t n (Enc.answer t n (.alp M P A)) = some (Coc.alpDecode w.toUSize M P A n.toUSize) := by
  simp only [Enc.answer, hw]
  repeat' split
  all_goals simp_all [Enc.bytesOf, QAtomicType.width]

/-- `concatALP` of two parts: their decodes at `w`, joined, encoded again. -/
theorem concatALP_pair {w : Nat} (hw48 : w = 4 ∨ w = 8) (n0 n1 : Nat) (m0 k0 a0 m1 k1 a1 : ByteArray) :
    concatALP w.toUSize #[n0, n1] #[m0, m1] #[k0, k1] #[a0, a1] = Coc.alpEncodeAt (w.toUSize == 4)
      (Coc.alpDecode w.toUSize m0 k0 a0 n0.toUSize ++ Coc.alpDecode w.toUSize m1 k1 a1 n1.toUSize) := by
  -- explicit rewrites: a `simp` that reads `#[m0, m1][0]!` inside `alpDecode` leaves the kernel a timeout
  have hr : ∀ f : Nat → ByteArray, (Array.range (min #[n0, n1].size (min #[m0, m1].size
      (min #[k0, k1].size #[a0, a1].size)))).map f = #[f 0, f 1] := fun f => by
    apply Array.ext'; simp [Array.toList_range]; rfl
  have j : ∀ x y : ByteArray, #[x, y].foldl (· ++ ·) ByteArray.empty = x ++ y := fun x y => by
    simp [ByteArray.empty_append]
  simp only [concatALP, (alpFlag hw48).1]
  congr 1
  rw [hr, concatBytes, show #[m0, m1][0]! = m0 by simp, show #[m0, m1][1]! = m1 by simp,
    show #[k0, k1][0]! = k0 by simp, show #[k0, k1][1]! = k1 by simp, show #[a0, a1][0]! = a0 by simp,
    show #[a0, a1][1]! = a1 by simp, show #[n0, n1][0]! = n0 by simp, show #[n0, n1][1]! = n1 by simp]
  exact j _ _

/-- `concatALP`'s answer lists the parts' words in turn: the parts are decoded at `w`, joined, and the join
    encoded again, which qlean's round trip `elemsW_alpDecode_alpEncodeAt` reads back. No flag hypothesis on the
    parts: a part is read at `w` whatever width its blob was written at. -/
theorem raze_alp_answer {t : QAtomicType} {w n0 n1 : Nat} (hw : t.width = some w) (hw48 : w = 4 ∨ w = 8)
    {m0 k0 a0 m1 k1 a1 D0 D1 : ByteArray} (hn : n0 + n1 < 2 ^ 32)
    (e0 : Verify.elemsW w (Coc.alpDecode w.toUSize m0 k0 a0 n0.toUSize) = Verify.elemsW w D0)
    (e1 : Verify.elemsW w (Coc.alpDecode w.toUSize m1 k1 a1 n1.toUSize) = Verify.elemsW w D1) :
    ∃ D, Enc.bytesOf t (n0 + n1) (Enc.answer t (n0 + n1)
      (.alp (concatALP w.toUSize #[n0, n1] #[m0, m1] #[k0, k1] #[a0, a1]).1
        (concatALP w.toUSize #[n0, n1] #[m0, m1] #[k0, k1] #[a0, a1]).2.1
        (concatALP w.toUSize #[n0, n1] #[m0, m1] #[k0, k1] #[a0, a1]).2.2)) = some D ∧
      Verify.elemsW w D = Verify.elemsW w D0 ++ Verify.elemsW w D1 := by
  have hw0 : 0 < w ∧ w ≤ 8 := by omega
  have hU : n0 + n1 < USize.size := Nat.lt_of_lt_of_le hn USize.le_size
  obtain ⟨hE, hF⟩ := alpFlag hw48
  have s0 := (alpDecode_words hw0 m0 k0 a0 (n := n0) (by omega)).1
  have s1 := (alpDecode_words hw0 m1 k1 a1 (n := n1) (by omega)).1
  have hC := concatALP_pair hw48 n0 n1 m0 k0 a0 m1 k1 a1
  have hX : (Coc.alpDecode w.toUSize m0 k0 a0 n0.toUSize ++ Coc.alpDecode w.toUSize m1 k1 a1 n1.toUSize).size / w =
      n0 + n1 := by rw [ByteArray.size_append, s0, s1, ← Nat.mul_add, Nat.mul_div_cancel_left _ hw0.1]
  refine ⟨_, bytesOf_answer_alp hw _ _ _, ?_⟩
  rw [hC, ← hX, Verify.elemsW_alpDecode_alpEncodeAt (w.toUSize == 4) w hF _ (by rw [hX]; exact hn),
    Verify.elemsW_append w hw0.1 _ _ (by rw [s0]; simp), e0, e1]

theorem concatFoR_words {w n0 n1 : Nat} {m0 p0 m1 p1 : ByteArray} (hw : 1 < w ∧ w ≤ 8)
    (hn : n0 + n1 < USize.size) :
    (foRWords (n0 + n1) (concatFoR w.toUSize #[n0, n1] #[m0, m1] #[p0, p1]).1
      (concatFoR w.toUSize #[n0, n1] #[m0, m1] #[p0, p1]).2).map (lowBytes w) =
      (foRWords n0 m0 p0 ++ foRWords n1 m1 p1).map (lowBytes w) := by
  have hz : (#[n0, n1].zip #[m0, m1]).zip #[p0, p1] = #[((n0, m0), p0), ((n1, m1), p1)] := by simp
  have hw0 : 0 < w ∧ w ≤ 8 := ⟨by omega, hw.2⟩
  obtain ⟨d0s, d0w⟩ := decode_words hw0 m0 p0 (n := n0) (by omega)
  obtain ⟨d1s, d1w⟩ := decode_words hw0 m1 p1 (n := n1) (by omega)
  simp only [concatFoR, hz]
  split
  · rename_i out hmv; obtain ⟨M, P⟩ := out; rw [moveFoR_words hmv]
  · have g0 : (#[((n0, m0), p0), ((n1, m1), p1)] : Array ((Nat × ByteArray) × ByteArray)).get!Internal 0 =
        ((n0, m0), p0) := rfl
    have tl : concatBytes (Array.map (fun p : (Nat × ByteArray) × ByteArray => Coc.decode 8 p.fst.snd p.snd p.fst.fst.toUSize)
        ((#[((n0, m0), p0), ((n1, m1), p1)] : Array ((Nat × ByteArray) × ByteArray)).extract 1)) =
        Coc.decode (8 : Nat).toUSize m1 p1 n1.toUSize := by
      simp [concatBytes, ByteArray.empty_append]; rfl
    simp only [g0, tl]
    split
    · rename_i out hap; obtain ⟨M, P⟩ := out; rw [appendFoR_words (by omega) hap]
    · rw [show concatBytes ((#[((n0, m0), p0), ((n1, m1), p1)] : Array _).map
          (fun p => Coc.decode w.toUSize p.1.2 p.2 p.1.1.toUSize)) =
          Coc.decode w.toUSize m0 p0 n0.toUSize ++ Coc.decode w.toUSize m1 p1 n1.toUSize by
        simp [concatBytes, ByteArray.empty_append]]
      have hX : (Coc.decode w.toUSize m0 p0 n0.toUSize ++ Coc.decode w.toUSize m1 p1 n1.toUSize).size / w = n0 + n1 := by
        rw [ByteArray.size_append, d0s, d1s, ← Nat.mul_add, Nat.mul_div_cancel_left _ hw0.1]
      rw [← hX, encode_words hw _ (by rw [hX]; exact hn), Verify.elemsW_append w hw0.1 _ _ (by rw [d0s]; simp),
        d0w, d1w, List.map_append]

/-- `concatFoR`'s answer at width `w` lists the parts' cut words in turn, through either form `answer` gives it. -/
theorem raze_answer {t : QAtomicType} {w n0 n1 : Nat} (hw : t.width = some w) (hw8 : 1 < w ∧ w ≤ 8)
    {m0 m1 k0 k1 D0 D1 : ByteArray} (hn : n0 + n1 < USize.size)
    (e0 : (foRWords n0 m0 k0).map (lowBytes w) = Verify.elemsW w D0)
    (e1 : (foRWords n1 m1 k1).map (lowBytes w) = Verify.elemsW w D1) :
    ∃ D, Enc.bytesOf t (n0 + n1) (Enc.answer t (n0 + n1) (.foR (concatFoR w.toUSize #[n0, n1] #[m0, m1] #[k0, k1]).1
      (concatFoR w.toUSize #[n0, n1] #[m0, m1] #[k0, k1]).2)) = some D ∧
      Verify.elemsW w D = Verify.elemsW w D0 ++ Verify.elemsW w D1 := by
  refine ⟨_, ?_, (decode_words ⟨by omega, hw8.2⟩ _ _ hn).2.trans (by rw [concatFoR_words hw8 hn, List.map_append, e0, e1])⟩
  rcases Verify.answer_foR t w (n0 + n1) _ _ hw with e | e <;> rw [e] <;> simp [Enc.bytesOf, hw]

/-- **`razeColumn` joins the words** at every type `encodes` takes (each Frame-of-Reference width): the
    answer's dense form lists the parts' `w`-byte words in turn, whatever their payloads. -/
theorem razeColumn_words {t : QAtomicType} {w na nb : Nat} (hw : t.width = some w) (he : Column.encodes t = true)
    (p : Arr t na) (q : Arr t nb) {v : QValue} {D0 D1 : ByteArray} (h0 : Enc.bytesOf t na p.enc = some D0)
    (h1 : Enc.bytesOf t nb q.enc = some D1) (hn : na + nb < USize.size)
    (h : razeColumn t #[(na, p.enc), (nb, q.enc)] = some v) :
    ∃ e D, v = .vector t (na + nb) e none ∧ Enc.bytesOf t (na + nb) e = some D ∧
      Verify.elemsW w D = Verify.elemsW w D0 ++ Verify.elemsW w D1 := by
  have hw8 := width_fixed hw he
  have hw0 : 0 < w ∧ w ≤ 8 := ⟨by omega, hw8.2⟩
  have fp := fixed_parts hw he p; have fq := fixed_parts hw he q
  generalize p.enc = ea at fp h0 h
  generalize q.enc = eb at fq h1 h
  have sz : ∀ {n} (e : Enc) {D}, Enc.bytesOf t n e = some D → ((∃ B, e = .bytes B ∧ B.size = w * n) ∨
      ∃ md pk, e = .foR md pk) → n < USize.size → D.size = w * n := by
    intro n e D hD he hn
    rcases he with ⟨B, rfl, hB⟩ | ⟨md, pk, rfl⟩
    · simp only [Enc.bytesOf, Option.some.injEq] at hD; rw [← hD, hB]
    · simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hD; rw [← hD]
      exact (decode_words hw0 md pk hn).1
  have s0 := sz ea h0 fp (by omega); have s1 := sz eb h1 fq (by omega)
  rcases raze_fixed hw he h with ⟨E0, E1, e0, e1, rfl⟩ | ⟨n, ns, ms, ps, es, hE, rfl⟩
  · simp only [e0, Option.some.injEq] at h0; simp only [e1, Option.some.injEq] at h1; subst h0 h1
    refine ⟨_, _, rfl, rfl, ?_⟩
    rw [Struct.elemsW_concatBytes w hw0.1 _ (by simp [s0, s1])]; simp
  · have hal := alp_fixed he
    -- a `bytes` part is met encoded: `encode`'s words cut to `w` bytes are its own
    have eA : ∀ {k} (A : ByteArray), A.size = w * k → k < USize.size →
        (foRWords k (Coc.encode w.toUSize A).1 (Coc.encode w.toUSize A).2).map (lowBytes w) = Verify.elemsW w A := by
      intro k A hA hk
      have := encode_words hw8 A (by rw [hA, Nat.mul_div_cancel_left _ hw0.1]; exact hk)
      rwa [hA, Nat.mul_div_cancel_left _ hw0.1] at this
    rcases fp with ⟨A, rfl, hA⟩ | ⟨m0, k0, rfl⟩ <;> rcases fq with ⟨B, rfl, hB⟩ | ⟨m1, k1, rfl⟩ <;>
      simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at h0 h1 <;> subst h0 h1 <;>
      simp [encodedParts, Enc.encode, Enc.bytesOf, hw, he, hal] at hE
    all_goals obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hE
    · obtain ⟨D, hD, hDw⟩ := raze_answer hw hw8 hn (eA _ hA (by omega)) (decode_words hw0 _ _ (by omega)).2.symm
      exact ⟨_, D, rfl, hD, hDw⟩
    · obtain ⟨D, hD, hDw⟩ := raze_answer hw hw8 hn (decode_words hw0 _ _ (by omega)).2.symm (eA _ hB (by omega))
      exact ⟨_, D, rfl, hD, hDw⟩
    · obtain ⟨D, hD, hDw⟩ := raze_answer hw hw8 hn (decode_words hw0 _ _ (by omega)).2.symm
        (decode_words hw0 _ _ (by omega)).2.symm
      exact ⟨_, D, rfl, hD, hDw⟩

/-- **`razeColumn` joins the words** at the ALP types (`real` at four bytes, `float` and `datetime` at eight): the
    answer's dense form lists the parts' words in turn, whatever their payloads, below `2³²` elements (the bound
    an ALP blob stores its offsets at). -/
theorem razeColumn_alp {t : QAtomicType} {w na nb : Nat} (hw : t.width = some w) (ha : Column.alpEncodes t = true)
    (p : Arr t na) (q : Arr t nb) {v : QValue} {D0 D1 : ByteArray} (h0 : Enc.bytesOf t na p.enc = some D0)
    (h1 : Enc.bytesOf t nb q.enc = some D1) (hn : na + nb < 2 ^ 32)
    (h : razeColumn t #[(na, p.enc), (nb, q.enc)] = some v) :
    ∃ e D, v = .vector t (na + nb) e none ∧ Enc.bytesOf t (na + nb) e = some D ∧
      Verify.elemsW w D = Verify.elemsW w D0 ++ Verify.elemsW w D1 := by
  have hw48 := alp_width hw ha
  have hw0 : 0 < w ∧ w ≤ 8 := by omega
  have hU : na + nb < USize.size := Nat.lt_of_lt_of_le hn USize.le_size
  have fp := alp_parts hw ha p; have fq := alp_parts hw ha q
  generalize p.enc = ea at fp h0 h
  generalize q.enc = eb at fq h1 h
  have sz : ∀ {n} (e : Enc) {D}, Enc.bytesOf t n e = some D → ((∃ B, e = .bytes B ∧ B.size = w * n) ∨
      (∃ md pk, e = .foR md pk) ∨ ∃ md pk al, e = .alp md pk al) → n < USize.size → D.size = w * n := by
    intro n e D hD he hn
    rcases he with ⟨B, rfl, hB⟩ | ⟨md, pk, rfl⟩ | ⟨md, pk, al, rfl⟩
    · simp only [Enc.bytesOf, Option.some.injEq] at hD; rw [← hD, hB]
    · simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hD; rw [← hD]
      exact (decode_words hw0 md pk hn).1
    · simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hD; rw [← hD]
      exact (alpDecode_words hw0 md pk al hn).1
  have s0 := sz ea h0 fp (by omega); have s1 := sz eb h1 fq (by omega)
  rcases raze_alp hw ha h with ⟨E0, E1, e0, e1, rfl⟩ | ⟨n, ns, ms, ps, es, hE, rfl⟩
  · simp only [e0, Option.some.injEq] at h0; simp only [e1, Option.some.injEq] at h1; subst h0 h1
    refine ⟨_, _, rfl, rfl, ?_⟩
    rw [Struct.elemsW_concatBytes w hw0.1 _ (by simp [s0, s1])]; simp
  · -- a `bytes` part is met encoded by `alpOf`: decoded at its count it is itself (the round trip)
    have hAE : ∀ A, (if w = 4 then Coc.alpEncode32 A else Coc.alpEncode64 A) = Coc.alpEncodeAt (w == 4) A :=
      fun A => by rcases hw48 with rfl | rfl <;> rfl
    have eA : ∀ {k} (A : ByteArray), A.size = w * k → k < 2 ^ 32 →
        Verify.elemsW w (Coc.alpDecode w.toUSize (Coc.alpEncodeAt (w == 4) A).1 (Coc.alpEncodeAt (w == 4) A).2.1
          (Coc.alpEncodeAt (w == 4) A).2.2 k.toUSize) = Verify.elemsW w A := by
      intro k A hA hk
      have hk' : A.size / w = k := by rw [hA, Nat.mul_div_cancel_left _ hw0.1]
      have := Verify.elemsW_alpDecode_alpEncodeAt (w == 4) w (by rcases hw48 with rfl | rfl <;> rfl) A
        (by rw [hk']; exact hk)
      rwa [hk'] at this
    rcases fp with ⟨A, rfl, hA⟩ | ⟨m0, k0, rfl⟩ | ⟨m0, k0, a0, rfl⟩ <;>
      rcases fq with ⟨B, rfl, hB⟩ | ⟨m1, k1, rfl⟩ | ⟨m1, k1, a1, rfl⟩ <;>
      simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at h0 h1 <;> subst h0 h1 <;>
      simp [encodedParts, Enc.alpOf, Enc.bytesOf, hw, ha] at hE
    all_goals ((try simp only [hAE] at hE); obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hE)
    · obtain ⟨D, hD, hDw⟩ := raze_alp_answer hw hw48 hn (eA _ hA (by omega)) rfl
      exact ⟨_, D, rfl, hD, hDw⟩
    · obtain ⟨D, hD, hDw⟩ := raze_alp_answer hw hw48 hn rfl (eA _ hB (by omega))
      exact ⟨_, D, rfl, hD, hDw⟩
    · obtain ⟨D, hD, hDw⟩ := raze_alp_answer hw hw48 hn rfl rfl
      exact ⟨_, D, rfl, hD, hDw⟩

/-- An `Arr` whose element `i` is the atom of `D`'s word `i` lists those atoms. -/
theorem toList_words {t : QAtomicType} {w n : Nat} (hw : t.width = some w) (hw0 : 0 < w) (x : Arr t n)
    {D : ByteArray} (hs : D.size = w * n) (hg : ∀ i < n, Enc.get t n x.enc i =
      some (Column.atomOfBits t (Column.bitsAt D (i * w) w) (QAtomicType.ne_general_of_width hw))) :
    x.toList = (Verify.elemsW w D).map fun v =>
      (Carrier.of? t (.atom (Column.atomOfBits t v (QAtomicType.ne_general_of_width hw)))).getD default := by
  apply List.ext_getElem (by rw [Arr.length_toList]; simp [Verify.elemsW, hs, Nat.mul_div_cancel_left n hw0])
  intro i h1 _
  rw [Arr.getElem_toList, Arr.get_ne x _ (QAtomicType.ne_general_of_width hw),
    hg i (by rw [Arr.length_toList] at h1; exact h1)]
  simp [Verify.elemsW]

/-- Under `wf`, a column at a type `encodes` or `alpEncodes` takes lists its dense form's `w`-byte words, each read
    as an atom. -/
theorem toList_fixed {t : QAtomicType} {w n : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true)
    (x : Arr t n) {D : ByteArray} (hD : Enc.bytesOf t n x.enc = some D) (hn : n < USize.size) :
    x.toList = (Verify.elemsW w D).map fun v =>
      (Carrier.of? t (.atom (Column.atomOfBits t v (QAtomicType.ne_general_of_width hw)))).getD default := by
  have hw8 : 0 < w ∧ w ≤ 8 :=
    he.elim (fun he => by have := width_fixed hw he; omega) (fun ha => by have := alp_width hw ha; omega)
  have hg := QAtomicType.ne_general_of_width hw
  have hb : t ≠ .boolean := by rintro rfl; simp [Column.encodes, Column.alpEncodes] at he
  have hgu : t ≠ .guid := by rintro rfl; simp [Column.encodes, Column.alpEncodes] at he
  have parts : (∃ B, x.enc = .bytes B ∧ B.size = w * n) ∨ (∃ md pk, x.enc = .foR md pk) ∨
      ∃ md pk a, x.enc = .alp md pk a :=
    he.elim (fun he => (fixed_parts hw he x).elim .inl (.inr ∘ .inl)) (alp_parts hw · x)
  obtain ⟨hs, hg'⟩ : D.size = w * n ∧
      ∀ i < n, Enc.get t n x.enc i = some (Column.atomOfBits t (Column.bitsAt D (i * w) w) hg) := by
    rcases parts with ⟨B, hc, hB⟩ | ⟨md, pk, hc⟩ | ⟨md, pk, a, hc⟩
    · rw [hc] at hD ⊢; simp only [Enc.bytesOf, Option.some.injEq] at hD; subst hD
      refine ⟨hB, fun i hi => ?_⟩
      cases t <;> simp_all [Enc.get, QAtomicType.width, Column.encodes, Column.alpEncodes]
    · rw [hc] at hD ⊢; simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hD; subst hD
      obtain ⟨hs, hg'⟩ := Verify.decodeW w.toUSize (by rw [Verify.toUSize_toNat_of_le8 w hw8.2]; exact hw8.2) md pk n.toUSize
      rw [Verify.toUSize_toNat_of_le8 w hw8.2, USize.toNat_ofNat_of_lt' hn] at hs hg'
      refine ⟨hs, fun i hi => ?_⟩
      rw [hg' i hi, Verify.atomOfBits_mod hw hb hgu, ← foRBits_starts]
      cases t <;> simp_all [Enc.get, QAtomicType.width, Column.encodes, Column.alpEncodes]
    · rw [hc] at hD ⊢; simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hD; subst hD
      obtain ⟨hs, hg'⟩ := alpDecode_words hw8 md pk a hn
      refine ⟨hs, fun i hi => ?_⟩
      rw [hg' i hi, Verify.atomOfBits_mod hw hb hgu]
      cases t <;> simp_all [Enc.get, QAtomicType.width, Column.encodes, Column.alpEncodes]
  exact toList_words hw hw8.1 x hs hg'

/-- **`razeColumn` as lists** at every type `encodes` or `alpEncodes` takes: the answer read as an `Arr` is the
    parts in turn. An ALP join is bounded by `2³²` elements. -/
theorem raze_toList_fixed {t : QAtomicType} {na nb : Nat} (he : Column.encodes t = true ∨ Column.alpEncodes t = true)
    (p : Arr t na) (q : Arr t nb) {v : QValue} (hn : na + nb < USize.size)
    (h32 : Column.alpEncodes t = true → na + nb < 2 ^ 32) (h : razeColumn t #[(na, p.enc), (nb, q.enc)] = some v)
    (V : Arr t (na + nb)) (hV : V.1 = v) : V.toList = p.toList ++ q.toList := by
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by
    rcases he with he | he <;> cases t <;> simp_all [Column.encodes, Column.alpEncodes, QAtomicType.width]
  have dense : ∀ {n} (x : Arr t n), ∃ D, Enc.bytesOf t n x.enc = some D := fun x => by
    rcases he with he | ha
    · rcases fixed_parts hw he x with ⟨B, hc, -⟩ | ⟨md, pk, hc⟩ <;> simp [Enc.bytesOf, hc, hw]
    · rcases alp_parts hw ha x with ⟨B, hc, -⟩ | ⟨md, pk, hc⟩ | ⟨md, pk, a, hc⟩ <;>
        simp [Enc.bytesOf, hc, hw]
  obtain ⟨D0, h0⟩ := dense p; obtain ⟨D1, h1⟩ := dense q
  obtain ⟨e, D, rfl, hD, hDw⟩ := he.elim (fun he => razeColumn_words hw he p q h0 h1 hn h)
    (fun ha => razeColumn_alp hw ha p q h0 h1 (h32 ha) h)
  have hVe : V.enc = e := by simp only [Arr.enc, hV]
  rw [toList_fixed hw he V (hVe ▸ hD) hn, toList_fixed hw he p h0 (by omega), toList_fixed hw he q h1 (by omega),
    hDw, List.map_append]

/-- Under `wf`, a boolean column is `bits`. -/
theorem bits_arr {n : Nat} (x : Arr .boolean n) : ∃ b, x.enc = .bits b := by
  have hwf := x.wf
  generalize x.enc = e at hwf ⊢
  cases e <;> simp_all [Enc.WF]

theorem get_bits {n : Nat} (x : Arr .boolean n) {b : ByteArray} (hc : x.enc = .bits b) (i : Fin n) :
    x.get i = (Carrier.of? .boolean (.atom (.boolean (Column.bitAt b i)))).getD default := by
  rw [Arr.get_ne x i (by decide), hc]; simp [Enc.get, i.2]

/-- `concatBits`' bit `j`: the first part's below its count, the second's past it. -/
theorem concatBits_at {na nb j : Nat} (b0 b1 : ByteArray) (hj : j < na + nb) :
    Column.bitAt (concatBits #[na, nb] #[b0, b1]) j =
      if j < na then Column.bitAt b0 j else Column.bitAt b1 (j - na) := by
  simp only [concatBits]
  rw [Verify.bitAt_packOf _ _ _ (by simp; omega)]
  split
  · simp; rw [List.getElem?_append_left (by simp; omega)]; simp [*]
  · simp; rw [List.getElem?_append_right (by simp; omega)]; simp [show j - na < nb by omega]

/-- **`razeColumn` at boolean as lists**: `concatBits` lays the parts' bits down in turn. -/
theorem raze_toList_bits {na nb : Nat} (p : Arr .boolean na) (q : Arr .boolean nb) {v : QValue}
    (h : razeColumn .boolean #[(na, p.enc), (nb, q.enc)] = some v) (V : Arr .boolean (na + nb)) (hV : V.1 = v) :
    V.toList = p.toList ++ q.toList := by
  obtain ⟨b0, h0⟩ := bits_arr p; obtain ⟨b1, h1⟩ := bits_arr q
  rw [h0, h1] at h
  simp [razeColumn] at h
  subst h
  have hVc : V.enc = .bits (concatBits #[na, nb] #[b0, b1]) := by simp only [Arr.enc, hV]
  apply List.ext_getElem (by rw [List.length_append, Arr.length_toList, Arr.length_toList, Arr.length_toList])
  intro j h1' _
  rw [Arr.length_toList] at h1'
  rw [Arr.getElem_toList, get_bits V hVc, List.getElem_append, concatBits_at _ _ h1']
  by_cases hj : j < na
  · rw [dif_pos (by rw [Arr.length_toList]; exact hj), if_pos hj, Arr.getElem_toList, get_bits p h0]
  · rw [dif_neg (by rw [Arr.length_toList]; exact hj), if_neg hj, Arr.getElem_toList, get_bits q h1]
    have hl : p.toList.length = na := Arr.length_toList p
    simp only [hl]

/-- **`razeColumn` as lists** at boolean and at every type `encodes` or `alpEncodes` takes. -/
theorem raze_toList {t : QAtomicType} {na nb : Nat}
    (ht : Column.encodes t = true ∨ Column.alpEncodes t = true ∨ t = .boolean) (p : Arr t na)
    (q : Arr t nb) {v : QValue} (hn : na + nb < USize.size) (h32 : Column.alpEncodes t = true → na + nb < 2 ^ 32)
    (h : razeColumn t #[(na, p.enc), (nb, q.enc)] = some v)
    (V : Arr t (na + nb)) (hV : V.1 = v) : V.toList = p.toList ++ q.toList := by
  rcases ht with he | he | rfl
  · exact raze_toList_fixed (.inl he) p q hn h32 h V hV
  · exact raze_toList_fixed (.inr he) p q hn h32 h V hV
  · exact raze_toList_bits p q h V hV

end FoRRaze

/-- A successful `Except` bind ran both halves (qlean's `Verify.bind_ok` is at its own `R` only). -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} (h : (x >>= f) = .ok v) :
    ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `align` off the matching-keys case, unfolded: `findColumn`, `gatherFill` at `eᵣ` and one `dyad` give the
    rows of `x`; `memberColumn`, `~`, `whereColumn`, `gatherColumn` and one `dyad` against `eₗ` the rows only
    `y` has; `razeColumn` joins the keys and the values. -/
theorem align_gather {L : Lift} {rt s t u : QAtomicType} {x : Rel s t} {y : Rel s u} {R : Rel s rt}
    (ht : t ≠ .general) (hv : Ew.align L rt x y ht = .ok R)
    (hm : ∀ _ : y.n = x.n, Kernel.matchColumn s x.n x.key.enc y.n y.key.enc ≠ some true) :
    ∃ (ix yx : Nat × Enc) (l : Arr rt x.n) (ty : QAtomicType) (m : Nat) (b : ByteArray) (r : Nat) (iy ac gy : Enc)
      (ry : Arr rt r) (gk : Enc) (keys vals : QValue) (K : Arr s (x.n + r)) (V : Arr rt (x.n + r)),
      Ew.vec "findColumn" (Kernel.findColumn s false y.n y.key.enc x.key.1) = .ok ix ∧
      Ew.gatherFill u L.er y.n y.val.enc ix = .ok yx ∧
      Ew.dyad L.v Kernel.Ew.vv t u rt x.n x.val.enc yx.1 yx.2 x.n = .ok l ∧
      Kernel.memberColumn s false y.key.1 x.n x.key.enc = some (.vector ty m (.bits b) none) ∧
      Ew.vec "whereColumn" (Kernel.whereColumn .boolean m (.bits (Ew.notBits m b))) = .ok (r, iy) ∧
      Ew.atomCol t (Column.atomOfBits t L.el) = .ok ac ∧
      Kernel.gatherColumn u y.n y.val.enc r iy = some gy ∧
      Ew.dyad L.vr Kernel.Ew.av t u rt 1 ac r gy r = .ok ry ∧
      Kernel.gatherColumn s y.n y.key.enc r iy = some gk ∧
      Kernel.razeColumn s #[(x.n, x.key.enc), (r, gk)] = some keys ∧
      Kernel.razeColumn rt #[(x.n, l.enc), (r, ry.enc)] = some vals ∧
      Arr.of s (x.n + r) keys "align keys" = .ok K ∧ Arr.of rt (x.n + r) vals "align vals" = .ok V ∧
      R = ⟨x.n + r, K, V⟩ := by
  unfold Ew.align at hv
  dsimp only at hv
  split at hv
  split at hv
  · rename_i h hc; exact absurd (beq_iff_eq.1 hc) (hm h)
  all_goals
    try simp only [pure_bind] at hv
    obtain ⟨ix, hix, hv⟩ := bind_ok hv
    obtain ⟨yx, hyx, hv⟩ := bind_ok hv
    obtain ⟨l, hl, hv⟩ := bind_ok hv
    split at hv
    all_goals first | (cases hv; done) | skip
    rename_i ty m b hmem
    obtain ⟨⟨r, iy⟩, hw, hv⟩ := bind_ok hv
    dsimp only at hv
    split at hv
    all_goals first | (cases hv; done) | skip
    rename_i gy hgy
    obtain ⟨ac, hac, hv⟩ := bind_ok hv
    obtain ⟨ry, hry, hv⟩ := bind_ok hv
    split at hv
    all_goals first | (cases hv; done) | skip
    rename_i gk hgk
    split at hv
    all_goals first | (cases hv; done) | skip
    rename_i keys hkeys
    split at hv
    all_goals first | (cases hv; done) | skip
    rename_i vals hvals
    obtain ⟨K, hK, hv⟩ := bind_ok hv
    obtain ⟨V, hV, hv⟩ := bind_ok hv
    exact ⟨ix, yx, l, ty, m, b, r, iy, ac, gy, ry, gk, keys, vals, K, V, hix, hyx, hl, hmem, hw, hac, hgy, hry, hgk,
      hkeys, hvals, hK, hV, (Except.ok.inj hv).symm⟩

/-- **The rows of `x` in `align`, long keys and long `y` values: `⟨x, x.key ≫ miss(Λ(y.key°) est(≤) y, eᵣ)⟩ ≫ f`.**
    Each key of `x` meets `y`'s value at the key's first position in `y.key`, `eᵣ` where `y` lacks it
    (`probe_find`, `gatherFill_long`, `ix_lookup`); `hlaw` is any value law of the encodings at hand. -/
theorem align_left_rel {L : Lift} {rt t : QAtomicType} {x : Rel .long t} {y : Rel .long .long} {ix yx : Nat × Enc}
    {l : Arr rt x.n} (he : Eval.ewType L.v t .long = some rt) (hkx : Find.Readable .long x.n x.key.enc)
    (hky : Find.Readable .long y.n y.key.enc) (hyv : Find.Readable .long y.n y.val.enc)
    (hnx : x.n < USize.size) (hny : y.n < USize.size)
    (hix : Ew.vec "findColumn" (Kernel.findColumn .long false y.n y.key.enc x.key.1) = .ok ix)
    (hyx : Ew.gatherFill .long L.er y.n y.val.enc ix = .ok yx)
    (hl : Ew.dyad L.v Kernel.Ew.vv t .long rt x.n x.val.enc yx.1 yx.2 x.n = .ok l)
    (hlaw : ∀ (Y : Arr .long x.n) l, Ew.val L.v rt x.val Y = .ok l → Ew.ValSpec L.v he x.val Y l) :
    l.rel = rpair x.val.rel (x.key.rel ≫ miss ((Λ (y.key.rel°) ≫ est (· ≤ ·)) ≫ y.val.rel) L.er.toInt64) ≫
      ofExcept (fun p : Carrier t × Carrier .long => elem L.v he p.1 p.2) := by
  obtain ⟨B, ky, kx, hp, hwy, hwx, hB⟩ := Find.probe_find y.key x.key hky hkx hny hnx
  rw [x.key.val_eq, Find.findColumn_long] at hix
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp, Option.map_some, Ew.vec, Except.ok.injEq] at hix
  subst hix
  obtain ⟨_, _, _, vs, -, hwv, -, hlv⟩ := Find.operand_long y.val hyv hny
  obtain ⟨G, rfl, hG, hGw⟩ := gatherFill_long y.val hwv hny (ib := B) (by simp [Enc.bytesOf]) hyx
  have hkx : kx.length = x.n := by rw [← Arr.length_toList x.key, Arr.toList_long x.key hwx, List.length_map]
  have hky : ky.length = y.n := by rw [← Arr.length_toList y.key, Arr.toList_long y.key hwy, List.length_map]
  have hn : B.size / 8 = x.n := by
    have := congrArg List.length hB; simp only [Verify.elemsW, List.length_map, List.length_range] at this; omega
  simp only [hn] at hl
  let Y : Arr .long x.n := Arr.mk (.bytes G) (by show G.size = x.n * 8; omega)
  have hY : Y.rel = x.key.rel ≫ miss ((Λ (y.key.rel°) ≫ est (· ≤ ·)) ≫ y.val.rel) L.er.toInt64 := by
    simp only [Arr.rel]
    rw [Arr.toList_long Y (ws := Verify.elemsW 8 G) rfl, Arr.toList_long x.key hwx, Arr.toList_long y.key hwy,
      Arr.toList_long y.val hwv, ← ix_lookup _ _ _ _ (by simp [hky, hlv])]
    refine congrArg ix ?_
    calc (Verify.elemsW 8 G).map UInt64.toInt64
        = ((Verify.elemsW 8 B).map UInt64.toNat).map fun i => (vs.getD i L.er).toInt64 := by
          rw [hGw, List.map_map, List.map_map]; rfl
      _ = (kx.map UInt64.toInt64).map fun k =>
            (vs.map UInt64.toInt64).getD ((ky.map UInt64.toInt64).idxOf k) L.er.toInt64 := by
          rw [hB, List.map_map, List.map_map]
          refine List.map_congr_left fun k _ => ?_
          simp only [Function.comp, Find.idxOf_map_of_inj (fun a b h => toInt64_inj h), List.getD_eq_getElem?_getD,
            List.getElem?_map, Option.getD_map]
  rw [val_rel (hlaw Y l hl), hY]

/-- The positions `K` holds whose value no position of `J` holds: `dom K ∩ corNeg(dom(K ≫ J°))`. -/
theorem cset_only {A B C : RelSet.{0}} (K : A ⟶ B) (J : C ⟶ B) (i : A.carrier) :
    cset (dom K ∩ corNeg (dom (K ≫ J°))) i ↔ (∃ k, K i k) ∧ ¬ ∃ k, K i k ∧ ∃ p, J p k := by
  show ((i = i ∧ ∃ k, K i k ∧ K i k) ∧
    (i = i ∧ ∀ v, (v = i ∧ ∃ p, (∃ k, K v k ∧ J p k) ∧ (∃ k, K i k ∧ J p k)) → False)) ↔ _
  constructor
  · rintro ⟨⟨-, k, hk, -⟩, -, hn⟩
    exact ⟨⟨k, hk⟩, fun ⟨k, hk, p, hp⟩ => hn i ⟨rfl, p, ⟨k, hk, hp⟩, ⟨k, hk, hp⟩⟩⟩
  · rintro ⟨⟨k, hk⟩, hn⟩
    exact ⟨⟨rfl, k, hk, hk⟩, rfl, fun _ ⟨_, p, _, ⟨k, hk, hp⟩⟩ => hn ⟨k, hk, p, hp⟩⟩

/-- `memberColumn`, `~` and `whereColumn` at long keys `kx`, `ky`: the ascending positions `F` of `ky` whose key
    `kx` lacks, the one list `enum(dom(ky) ∩ corNeg(dom(ky ≫ kx°)))` gives, as an index column `I` (`probe_member`,
    `notBits_bitAt`, `whereBits_spec`). -/
theorem only_rows {nx ny : Nat} (kx : Arr .long nx) (ky : Arr .long ny) {ty : QAtomicType} {m : Nat}
    {b : ByteArray} {r : Nat} {iy : Enc} (hkx : Find.Readable .long nx kx.enc) (hky : Find.Readable .long ny ky.enc)
    (hnx : nx < USize.size) (hny : ny < USize.size)
    (hmem : Kernel.memberColumn .long false ky.1 nx kx.enc = some (.vector ty m (.bits b) none))
    (hw : Ew.vec "whereColumn" (Kernel.whereColumn .boolean m (.bits (Ew.notBits m b))) = .ok (r, iy)) :
    ∃ F : List Nat, (∀ ys, enum (cset (dom ky.rel ∩ corNeg (dom (ky.rel ≫ kx.rel°)))) ys ↔ ys = CL.ofList F) ∧
      (∀ j ∈ F, j < ny) ∧ r ≤ ny ∧ ∃ I : Arr .long r, I.enc = iy ∧ longWords r iy = some (F.map UInt64.ofNat) := by
  obtain ⟨M, kyw, kxw, hp, hwy, hwx, hM⟩ := Find.probe_member ky kx hky hkx hny hnx
  rw [ky.val_eq, Find.memberColumn_long] at hmem
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp, Option.map_some, Option.some.injEq,
    QValue.vector.injEq, Enc.bits.injEq, and_true] at hmem
  obtain ⟨-, hm, hb⟩ := hmem
  subst m b
  have hN : ny = kyw.length := by rw [← Arr.length_toList ky, Arr.toList_long ky hwy, List.length_map]
  have hNU : ny < USize.size := hny
  obtain ⟨hs, hj⟩ := Verify.whereBits_spec ny.toUSize (Ew.notBits ny M)
  rw [USize.toNat_ofNat_of_lt' hNU] at hs hj
  generalize hF : (List.range ny).filter (Column.bitAt (Ew.notBits ny M)) = F at hs hj
  simp only [Kernel.whereColumn, Ew.vec, Except.ok.injEq, Prod.mk.injEq] at hw
  generalize Kernel.whereBits ny.toUSize (Ew.notBits ny M) = P at hs hj hw
  obtain ⟨rfl, rfl⟩ := hw
  have mem : ∀ i, i ∈ F ↔ cset (dom ky.rel ∩ corNeg (dom (ky.rel ≫ kx.rel°))) i := fun i => by
    rw [cset_only, ← hF, List.mem_filter, List.mem_range]
    show _ ↔ (∃ k, ky.toList[i]? = some k) ∧ ¬ ∃ k, ky.toList[i]? = some k ∧ ∃ p, kx.toList[p]? = some k
    rw [Arr.toList_long ky hwy, Arr.toList_long kx hwx]
    by_cases hik : i < kyw.length
    · rw [Ew.notBits_bitAt hNU M (by omega), hM i hik]
      simp only [List.getElem?_map, List.getElem?_eq_getElem hik, Option.map_some, Option.some.injEq,
        exists_eq', true_and, exists_eq_left', Bool.not_eq_true', decide_eq_false_iff_not]
      have hx : (∃ p : Nat, Option.map UInt64.toInt64 kxw[p]? = some kyw[i].toInt64) ↔ kyw[i] ∈ kxw := by
        rw [← Find.mem_map_of_inj (fun a b h => toInt64_inj h) (l := kxw), List.mem_iff_getElem?]
        simp only [List.getElem?_map]
      exact ⟨fun h hp => h.2 (hx.1 hp), fun h => ⟨by omega, fun hm => h (hx.2 hm)⟩⟩
    · simp only [List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_lt hik), Option.map_none, reduceCtorEq,
        exists_false, false_and, iff_false, not_and]
      intro h; omega
  have pw : F.Pairwise (· < ·) := hF ▸ (List.pairwise_lt_range ..).filter _
  have hPw : Verify.elemsW 8 P = F.map UInt64.ofNat := by
    apply List.ext_getElem (by simp only [Verify.elemsW, List.length_map, List.length_range, hs]; omega)
    intro j h1 h2
    simp only [List.length_map] at h2
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [← hj j h2, UInt64.ofNat_toNat]
  have hFl : F.length ≤ ny := by rw [← hF]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  refine ⟨F, enum_ofList _ F pw mem, fun j h => ?_, show P.size / 8 ≤ ny by omega,
    Arr.mk (.bytes P) (by show P.size = P.size / 8 * 8; omega), rfl, by simp only [longWords, hPw]⟩
  rw [← hF, List.mem_filter, List.mem_range] at h; omega

/-- `z@I` at long, the index `I` the positions `F` of `z` as words: `ix(F) ≫ z` (`gatherColumn_long`,
    `ix_map_getElem!`). -/
theorem gather_rel {k n : Nat} (z : Arr .long k) {zs : List UInt64} (hz : longWords k z.enc = some zs)
    (hk : k < USize.size) (I : Arr .long n) {F : List Nat} (hI : longWords n I.enc = some (F.map UInt64.ofNat))
    (hF : ∀ j ∈ F, j < k) (hn : n < USize.size) {c : Enc} (h : Kernel.gatherColumn .long k z.enc n I.enc = some c) :
    ∃ G : Arr .long n, G.enc = c ∧ G.rel = ix F ≫ z.rel := by
  obtain ⟨B, rfl, hBs, hBw⟩ := gatherColumn_long z hz hk I hI (Struct.countFits_long I hI hn) h
  have hzl : zs.length = k := by rw [← Arr.length_toList z, Arr.toList_long z hz, List.length_map]
  let G : Arr .long n := Arr.mk (.bytes B) (by show B.size = n * 8; omega)
  refine ⟨G, rfl, ?_⟩
  show ix G.toList = ix F ≫ ix z.toList
  rw [Arr.toList_long G (ws := Verify.elemsW 8 B) rfl, hBw, Arr.toList_long z hz, List.map_map, List.map_map,
    ← ix_map_getElem! F _ (fun j h => by have := hF j h; rw [List.length_map, hzl]; omega)]
  refine congrArg ix (List.map_congr_left fun j hj => ?_)
  have hjl : j < zs.length := by have := hF j hj; omega
  have h64 : j < 2 ^ 64 := by have := hF j hj; have := USize.size_le; omega
  simp only [Function.comp, UInt64.toNat_ofNat_of_lt' h64, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hjl, Option.getD_some]
  rw [getElem!_pos _ j (by rw [List.length_map]; exact hjl), List.getElem_map]

/-- **The rows only `y` has in `align`, long keys and long `y` values:
    `enum(dom(y.key) ∩ corNeg(dom(y.key ≫ x.key°))) ≫ ⟨!eₗ, y⟩ ≫ f`.** `memberColumn`, `~` and `whereColumn`
    enumerate the positions of `y` whose key `x` lacks (`probe_member`, `notBits_bitAt`, `whereBits_spec`),
    `gatherColumn` reads `y` there (`gatherColumn_long`), and the `av` dyad pairs each with `eₗ`; `hlaw` is any value
    law of `a f y` at the encoding at hand. -/
theorem align_right_rel {L : Lift} {rt t : QAtomicType} {x : Rel .long t} {y : Rel .long .long} {ty : QAtomicType}
    {m : Nat} {b : ByteArray} {r : Nat} {iy ac gy : Enc} {ry : Arr rt r} (ht : t ≠ .general) {el : Carrier t}
    (hel : Carrier.atom el = Column.atomOfBits t L.el) (he : Eval.ewType L.vr t .long = some rt)
    (hkx : Find.Readable .long x.n x.key.enc) (hky : Find.Readable .long y.n y.key.enc)
    (hyv : Find.Readable .long y.n y.val.enc) (hnx : x.n < USize.size) (hny : y.n < USize.size)
    (hmem : Kernel.memberColumn .long false y.key.1 x.n x.key.enc = some (.vector ty m (.bits b) none))
    (hw : Ew.vec "whereColumn" (Kernel.whereColumn .boolean m (.bits (Ew.notBits m b))) = .ok (r, iy))
    (hac : Ew.atomCol t (Column.atomOfBits t L.el) ht = .ok ac)
    (hgy : Kernel.gatherColumn .long y.n y.val.enc r iy = some gy)
    (hry : Ew.dyad L.vr Kernel.Ew.av t .long rt 1 ac r gy r = .ok ry)
    (hlaw : ∀ (Y : Arr .long r) z, Ew.atomVal L.vr rt el Y ht = .ok z →
      Y.toList.mapM (fun c => elem L.vr he el c) = .ok z.toList) :
    (∃ ys, enum (cset (dom y.key.rel ∩ corNeg (dom (y.key.rel ≫ x.key.rel°)))) ys) ∧
    ∀ ys, enum (cset (dom y.key.rel ∩ corNeg (dom (y.key.rel ≫ x.key.rel°)))) ys →
      ry.rel = ix (CL.toList ys) ≫
        (rpair (cst el) y.val.rel ≫ ofExcept (fun p : Carrier t × Carrier .long => elem L.vr he p.1 p.2)) := by
  obtain ⟨F, henum, hFn, hIn, I, hIc, hI⟩ := only_rows x.key y.key hkx hky hnx hny hmem hw
  obtain ⟨_, _, _, yvw, -, hwv, -, -⟩ := Find.operand_long y.val hyv hny
  subst hIc
  obtain ⟨G, rfl, hG⟩ := gather_rel y.val hwv hny I hI hFn (by omega) hgy
  have hat : Ew.atomVal L.vr rt el G ht = .ok ry := by
    unfold Ew.atomVal; rw [hel]; simp only [hac, bind, Except.bind]; exact hry
  refine ⟨⟨_, (henum _).2 rfl⟩, fun ys hy => ?_⟩
  obtain rfl := (henum ys).1 hy
  rw [CL.toList_ofList]
  calc ry.rel = G.rel ≫ ofExcept (elem L.vr he el) := ix_mapM _ _ _ (hlaw G ry hat)
    _ = ix F ≫ (y.val.rel ≫ ofExcept (elem L.vr he el)) := by rw [hG, Cat.assoc]
    _ = _ := by rw [pair_cst_left el y.val.rel (elem L.vr he)]

/-- **`align` on different keys, long keys and long `y` values: the keys `x.key ++ y.key` at the rows only `y`
    has, the values the rows of `x` (`align_left_rel`) then those rows (`align_right_rel`).** `hlaw`/`hlawr` are
    value laws of the `vv`/`av` dyads at the encodings at hand. Keys and values are joined by `raze_toList`, which
    `hrt` admits: `rt` boolean or a type `encodes` or `alpEncodes` takes (symbol has no raze law yet); `h32` bounds
    an ALP join. -/
theorem align_rel {L : Lift} {rt t : QAtomicType} {x : Rel .long t} {y : Rel .long .long} {R : Rel .long rt}
    (ht : t ≠ .general) (hv : Ew.align L rt x y ht = .ok R)
    (hm : ∀ _ : y.n = x.n, Kernel.matchColumn .long x.n x.key.enc y.n y.key.enc ≠ some true) {el : Carrier t}
    (hel : Carrier.atom el = Column.atomOfBits t L.el) (he : Eval.ewType L.v t .long = some rt)
    (hr : Eval.ewType L.vr t .long = some rt) (hkx : Find.Readable .long x.n x.key.enc)
    (hky : Find.Readable .long y.n y.key.enc) (hyv : Find.Readable .long y.n y.val.enc)
    (hnx : x.n < USize.size) (hny : y.n < USize.size) (hnk : x.n + y.n < USize.size)
    (hlaw : ∀ (Y : Arr .long x.n) l, Ew.val L.v rt x.val Y = .ok l → Ew.ValSpec L.v he x.val Y l)
    (hlawr : ∀ {n : Nat} (Y : Arr .long n) r, Ew.atomVal L.vr rt el Y ht = .ok r →
      Y.toList.mapM (fun c => elem L.vr hr el c) = .ok r.toList)
    (hrt : Column.encodes rt = true ∨ Column.alpEncodes rt = true ∨ rt = .boolean)
    (h32 : Column.alpEncodes rt = true → x.n + y.n < 2 ^ 32) :
    ∃ (n : Nat) (l : Arr rt x.n) (gk : Arr .long n) (ry : Arr rt n) (K : Arr .long (x.n + n)) (V : Arr rt (x.n + n)),
      R = ⟨x.n + n, K, V⟩ ∧ K.toList = x.key.toList ++ gk.toList ∧ V.toList = l.toList ++ ry.toList ∧
      l.rel = rpair x.val.rel (x.key.rel ≫ miss ((Λ (y.key.rel°) ≫ est (· ≤ ·)) ≫ y.val.rel) L.er.toInt64) ≫
        ofExcept (fun p : Carrier t × Carrier .long => elem L.v he p.1 p.2) ∧
      (∃ ys, enum (cset (dom y.key.rel ∩ corNeg (dom (y.key.rel ≫ x.key.rel°)))) ys) ∧
      ∀ ys, enum (cset (dom y.key.rel ∩ corNeg (dom (y.key.rel ≫ x.key.rel°)))) ys →
        gk.rel = ix (CL.toList ys) ≫ y.key.rel ∧ ry.rel = ix (CL.toList ys) ≫
          (rpair (cst el) y.val.rel ≫ ofExcept (fun p : Carrier t × Carrier .long => elem L.vr hr p.1 p.2)) := by
  obtain ⟨ixc, yx, l, ty, m, b, r, iy, ac, gy, ry, gk, keys, vals, K, V, hix, hyx, hl, hmem, hw, hac, hgy, hry, hgk,
    hkeys, hvals, hK, hV, rfl⟩ := align_gather ht hv hm
  have hR := align_right_rel ht hel hr hkx hky hyv hnx hny hmem hw hac hgy hry (hlawr (n := r))
  obtain ⟨F, henum, hFn, hIn, I, hIc, hI⟩ := only_rows x.key y.key hkx hky hnx hny hmem hw
  obtain ⟨_, _, _, kyw, -, hwy, -, -⟩ := Find.operand_long y.key hky hny
  subst hIc
  obtain ⟨G, rfl, hG⟩ := gather_rel y.key hwy hny I hI hFn (by omega) hgk
  refine ⟨r, l, G, ry, K, V, rfl, raze_toList (.inl rfl) x.key G (by omega)
    (fun h => absurd h (by decide)) hkeys K (Struct.of_val hK),
    raze_toList hrt l ry (by omega) (fun ha => by have := h32 ha; omega) hvals V (Struct.of_val hV),
    align_left_rel he hkx hky hyv hnx hny hix hyx hl hlaw, hR.1, fun ys hy => ⟨?_, hR.2 ys hy⟩⟩
  obtain rfl := (henum ys).1 hy
  rw [CL.toList_ofList]; exact hG

/-! ### Dicts with different keys: a miss sent to a point outside `S` stays a miss -/

/-- `miss(R, n) ≫ miss(S, e) = miss(R ≫ S, e)` when `R` lands where `S` is defined and `n` is not: the
    gather/fill branch of `align`, `R` the found position of a key, `n` the not-found position. -/
theorem miss_comp {A B C : RelSet.{0}} (R : A ⟶ B) (S : B ⟶ C) (n : B.carrier) (e : C.carrier)
    (hR : ∀ a b, R a b → ∃ c, S b c) (hn : ¬ ∃ c, S n c) : miss R n ≫ miss S e = miss (R ≫ S) e :=
  hom_ext fun a c => by
    change (∃ b, miss R n a b ∧ miss S e b c) ↔ miss (R ≫ S) e a c
    simp only [miss_iff]
    constructor
    · rintro ⟨b, hb | ⟨hnone, rfl⟩, hc | ⟨hnc, rfl⟩⟩
      · exact Or.inl ⟨b, hb, hc⟩
      · exact absurd (hR a b hb) hnc
      · exact absurd ⟨c, hc⟩ hn
      · exact Or.inr ⟨fun ⟨_, b', hb', _⟩ => hnone ⟨b', hb'⟩, rfl⟩
    · rintro (⟨b, hb, hc⟩ | ⟨hnone, rfl⟩)
      · exact ⟨b, Or.inl hb, Or.inl hc⟩
      · refine ⟨n, Or.inr ⟨fun ⟨b, hb⟩ => ?_, rfl⟩, Or.inr ⟨hn, rfl⟩⟩
        obtain ⟨c', hc'⟩ := hR a b hb
        exact hnone ⟨c', b, hb, hc'⟩

/-! ### Dicts with matching keys: the key kept, the verb on the values -/

/-- `Lift.ofVerb` keeps the verb itself for the rows both sides have. -/
theorem lift_v {v : Prim.Dyadic} {t u : QAtomicType} {L : Lift} (h : Lift.ofVerb v t u = .ok L) : L.v = v := by
  unfold Lift.ofVerb at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h <;> first | rfl | (split <;> rfl))

/-- `align` on keys `matchColumn` finds equal: one `Ew.val` of the values, `x`'s key kept. -/
theorem align_match {L : Lift} {rt s t u : QAtomicType} {x : Rel s t} {y : Rel s u} {R : Rel s rt} (ht : t ≠ .general)
    (hv : Ew.align L rt x y ht = .ok R) (h : y.n = x.n) (hm : Kernel.matchColumn s x.n x.key.enc y.n y.key.enc = some true) :
    ∃ V, Ew.val L.v rt x.val (h ▸ y.val) = .ok V ∧ R = ⟨x.n, x.key, V⟩ := by
  unfold Ew.align at hv
  dsimp only at hv; rw [dif_pos h] at hv
  simp only [hm, beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hv
  split at hv
  · cases hv
  · rename_i V hV
    exact ⟨V, hV, (Except.ok.inj hv).symm⟩

/-- **`d f e` on dicts with matching keys is `Ew.val` of the values, `d`'s key kept** (`align_match`, `lift_v`). -/
theorem dyadic_match {v : Prim.Dyadic} {rt s t u : QAtomicType} {x : Rel s t} {y : Rel s u} {R : Rel s rt}
    (ht : t ≠ .general) (hv : Ew.dyadic v rt x y ht = .ok R) (h : y.n = x.n)
    (hm : Kernel.matchColumn s x.n x.key.enc y.n y.key.enc = some true) :
    ∃ V, Ew.val v rt x.val (h ▸ y.val) = .ok V ∧ R = ⟨x.n, x.key, V⟩ := by
  unfold Ew.dyadic at hv
  cases hL : Lift.ofVerb v t u with
  | error e => simp [hL, bind, Except.bind] at hv
  | ok L =>
    simp only [hL, bind, Except.bind] at hv
    rw [← lift_v hL]
    exact align_match ht hv h hm

/-- `d f e = ⟨d, e⟩ ≫ f` on the values of dicts with matching keys, `d`'s key kept: any value law `hlaw` of
    the encodings at hand (`val_spec_long`, `cmp_spec_long_foR`, …) read through `dyadic_match` and `val_rel`. -/
theorem dyadic_rel {v : Prim.Dyadic} {rt s t u : QAtomicType} {x : Rel s t} {y : Rel s u} {R : Rel s rt}
    (ht : t ≠ .general) (he : Eval.ewType v t u = some rt) (hv : Ew.dyadic v rt x y ht = .ok R) (h : y.n = x.n)
    (hm : Kernel.matchColumn s x.n x.key.enc y.n y.key.enc = some true)
    (hlaw : ∀ V, Ew.val v rt x.val (h ▸ y.val) = .ok V → Ew.ValSpec v he x.val (h ▸ y.val) V) :
    ∃ V, R = ⟨x.n, x.key, V⟩ ∧ Ew.ValSpec v he x.val (h ▸ y.val) V ∧
      V.rel = rpair x.val.rel (h ▸ y.val).rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v he p.1 p.2) :=
  let ⟨V, hV, hR⟩ := dyadic_match ht hv h hm
  ⟨V, hR, hlaw V hV, val_rel (hlaw V hV)⟩

/-! ### An atom and a dict: the key kept, the verb on the values -/

/-- `Ew.keyed x f` answers `f` of `x`'s values under `x`'s key. -/
theorem keyed_ok {s rt t : QAtomicType} {x : Rel s t} {f : Arr t x.n → Except String (Arr rt x.n)} {R : Rel s rt}
    (hv : Ew.keyed x f = .ok R) : ∃ V, f x.val = .ok V ∧ R = ⟨x.n, x.key, V⟩ := by
  unfold Ew.keyed at hv
  simp only [bind, Except.bind, pure, Except.pure] at hv
  split at hv
  · cases hv
  · rename_i V hV
    exact ⟨V, hV, (Except.ok.inj hv).symm⟩

/-- `a f d = ⟨!a, d⟩ ≫ f` on `d`'s values, `d`'s key kept: any value law `hlaw` of the encoding at hand
    (`atomVal_spec_long`, `atomVal_spec_long_foR`, …) read through `keyed_ok` and `atomVal_rel`. -/
theorem atomDict_rel {v : Prim.Dyadic} {rt s t u : QAtomicType} {a : Carrier t} {x : Rel s u} {R : Rel s rt}
    (ht : t ≠ .general) (he : Eval.ewType v t u = some rt) (hv : Ew.keyed x (Ew.atomVal v rt a · ht) = .ok R)
    (hlaw : ∀ V, Ew.atomVal v rt a x.val ht = .ok V → x.val.toList.mapM (fun b => elem v he a b) = .ok V.toList) :
    ∃ V, R = ⟨x.n, x.key, V⟩ ∧
      V.rel = rpair (cst a) x.val.rel ≫ ofExcept (fun p : Carrier t × Carrier u => elem v he p.1 p.2) :=
  let ⟨V, hV, hR⟩ := keyed_ok hv
  ⟨V, hR, atomVal_rel (hlaw V hV)⟩

/-- `d f a = ⟨d, !a⟩ ≫ f` on `d`'s values, `d`'s key kept: any value law `hlaw` of the encoding at hand
    (`valAtom_spec_long`, `valAtom_spec_long_foR`, …) read through `keyed_ok` and `valAtom_rel`. -/
theorem dictAtom_rel {v : Prim.Dyadic} {rt s t u : QAtomicType} {a : Carrier u} {x : Rel s t} {R : Rel s rt}
    (hu : u ≠ .general) (he : Eval.ewType v t u = some rt) (hv : Ew.keyed x (Ew.valAtom v rt · a hu) = .ok R)
    (hlaw : ∀ V, Ew.valAtom v rt x.val a hu = .ok V → x.val.toList.mapM (fun b => elem v he b a) = .ok V.toList) :
    ∃ V, R = ⟨x.n, x.key, V⟩ ∧
      V.rel = rpair x.val.rel (cst a) ≫ ofExcept (fun p : Carrier t × Carrier u => elem v he p.1 p.2) :=
  let ⟨V, hV, hR⟩ := keyed_ok hv
  ⟨V, hR, valAtom_rel (hlaw V hV)⟩

/-- The column `Ew.mon` answers is the one `monColumn` builds. -/
theorem mon_enc {name : String} {t rt : QAtomicType} {n : Nat} {x : Arr t n} {R : Arr rt n} {C : Enc}
    (hd : Kernel.monColumn name t n x.enc = some (rt, C)) (hv : Ew.mon name rt x = .ok R) : R.enc = C := by
  unfold Ew.mon at hv
  simp only [hd, ↓reduceIte, Arr.of] at hv
  split at hv
  · cases hv; rfl
  · cases hv

/-- The reading every `long` map kernel ends in: an answer listing `g` of each word of `X`, which lists `x`'s
    words, is `MapSpec g`. -/
theorem map_spec_words {g : Int64 → Int64} {n : Nat} {x R : Arr .long n} {X : ByteArray}
    (hx : longWords n x.enc = some (Verify.elemsW 8 X)) (hX : X.size / 8 = n)
    (hR : longWords n R.enc = some ((List.range n).map fun i => (g (Column.bitsAt X (i * 8) 8).toInt64).toUInt64)) :
    Ew.MapSpec (t := .long) (rt := .long) g x R := by
  unfold Ew.MapSpec
  rw [Arr.toList_long R hR, Arr.toList_long x hx]
  exact List.ext_getElem (by simp [Verify.elemsW, hX]) fun i _ _ => by simp [Verify.elemsW]

/-- The reading every one-operand `long` kernel ends in: `map_spec_words` under q's element `F = pure ∘ g`. -/
theorem mapM_spec_words {ε : Type} {F : Int64 → Except ε Int64} {g : Int64 → Int64} (hF : ∀ y, F y = pure (g y))
    {n : Nat} {x R : Arr .long n} {X : ByteArray} (hx : longWords n x.enc = some (Verify.elemsW 8 X))
    (hX : X.size / 8 = n)
    (hR : longWords n R.enc = some ((List.range n).map fun i => (g (Column.bitsAt X (i * 8) 8).toInt64).toUInt64)) :
    x.toList.mapM F = .ok R.toList := by
  rw [show F = fun y => pure (g y) from funext hF, List.mapM_pure, map_spec_words hx hX hR]; rfl

/-- **`-x` at `long` on a dense column is `MapSpec`** of `monStep`'s `neg`, which `Verify.negAtom_long`
    proves is q's `neg`: `0N` stays `0N`, everything else is `0 - x`. -/
theorem neg_spec_long {n : Nat} {x R : Arr .long n} {a : ByteArray} (ha : x.enc = .bytes a)
    (hn : n < USize.size) (hv : Ew.mon "neg" .long x = .ok R) :
    Ew.MapSpec (t := .long) (rt := .long) (fun y : Int64 =>
      (Kernel.Ew.monStep Kernel.Ew.neg Kernel.Ew.i64 Int64.minValue.toUInt64 y.toUInt64).toInt64) x R := by
  have hR := mon_enc (by rw [ha]; exact monColumn_neg_long _ _) hv
  have hrun := run_mon ({ inputs := #[a] } : Kernel.Ew.Build) rfl Kernel.Ew.neg Kernel.Ew.i64 0
    (Kernel.nullPayload .long) (by decide) n.toUSize
  simp only [show (#[a] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl] at hrun
  have hs : (Kernel.Ew.mon Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) a n.toUSize).size / 8 = n := by
    have := congrArg List.length (mon_i64 Kernel.Ew.neg (Kernel.nullPayload .long) a n hn)
    simpa [Verify.elemsW] using this
  rw [← hrun] at hs
  have hw := longWords_payload _ _ hn hs
  rw [← hR, hrun, mon_i64 _ _ _ _ hn, nullPayload_long] at hw
  exact map_spec_words (by simp only [longWords, ha]) (Arr.n_long_bytes x ha) (by rw [hw]; simp)

/-- `-x = x ≫ neg` from the kernel: `mon_rel` of `neg_spec_long`. Dense long column. -/
theorem neg_rel_long {n : Nat} {x R : Arr .long n} {a : ByteArray} (ha : x.enc = .bytes a)
    (hn : n < USize.size) (hv : Ew.mon "neg" .long x = .ok R) :
    R.rel = x.rel ≫ graph (fun y : Int64 =>
      (Kernel.Ew.monStep Kernel.Ew.neg Kernel.Ew.i64 Int64.minValue.toUInt64 y.toUInt64).toInt64) :=
  mon_rel (neg_spec_long ha hn hv)

/-- `Ew.val` at `i64` with one long atom on the left (`av`): element `i` is `intStep` of the atom and
    element `i` (`Verify.val_i64_va`'s mirror). -/
theorem val_i64_av (op : UInt8) (nul : Int64) (c : UInt64) (b : ByteArray) (n : Nat) (hn : n < USize.size) :
    Verify.elemsW 8 (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.av nul (Kernel.atomBytes Kernel.Ew.i64 c) b n.toUSize) =
      (List.range n).map fun i =>
        (Kernel.Ew.intStep op nul c.toInt64 (Column.bitsAt b (i * 8) 8).toInt64).toUInt64 := by
  rw [← Verify.elemsW_foldl (fun i => (Kernel.Ew.intStep op nul c.toInt64 (Column.bitsAt b (i * 8) 8).toInt64).toUInt64)
    8 (by decide) (by decide) (List.range n) (fun _ _ => UInt64.toNat_lt _)]
  unfold Kernel.Ew.val
  rw [USize.toNat_ofNat_of_lt' hn]
  congr 2; funext acc i
  show Column.pushBits acc (Kernel.Ew.valStep op Kernel.Ew.i64 nul.toUInt64
    (Column.bitsAt (Column.pushBits ByteArray.empty c 8) ByteArray.empty.size 8) (Column.bitsAt b (i * 8) 8)) 8 = _
  rw [Verify.bitsAt_pushBits8]; rfl

/-- The one-element column `Ew.atomCol` builds for a long: its bits, the payload `atomBytes` names. -/
theorem atomCol_long (k : Int64) :
    Ew.atomCol .long (Carrier.atom (t := .long) k) =
      .ok (.bytes (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64)) := by
  simp [Ew.atomCol, Enc.ofAtoms, Carrier.atom, QAtom.type, Column.bitsOf, Kernel.atomBytes, Kernel.Ew.width,
    Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32, Kernel.Ew.f32] <;> rfl

/-- `dyadColumn` on a long atom column (left) and a dense long column, at a value verb: the one-stage
    `eVal` chain at `av`. The atom reaches the chain by `operandAt` when `n ≠ 1` and as a chain input
    when `n = 1`; both name its payload as input `0`. -/
theorem dyadColumn_long_av {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (c b : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long 1 (.bytes c) n (.bytes b) =
      some (.long, .vector .long n (Kernel.payload .long n.toUSize ({ inputs := #[c, b] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) none) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va), *]

/-- A long answer of a one-stage `eVal` chain over two inputs is its `Ew.val` words read as longs:
    `run_val`, `val_size8`, `longWords_payload`. -/
theorem toList_val_long {op shape : UInt8} {n : Nat} {R : Arr .long n} (p q : ByteArray) (hn : n < USize.size)
    (hR : R.enc = Kernel.payload .long n.toUSize ({ inputs := #[p, q] },
      { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape, a := 0, b := 1, nul := Kernel.nullPayload .long })) :
    R.toList = (Verify.elemsW 8 (Kernel.Ew.val op Kernel.Ew.i64 shape (Kernel.nullPayload .long) p q n.toUSize)).map
      UInt64.toInt64 := by
  have hrun := Verify.run_val ({ inputs := #[p, q] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 shape 0 1
    (Kernel.nullPayload .long) (by decide) (by decide) n.toUSize
  simp only [show (#[p, q] : Array ByteArray)[(0 : UInt8).toNat]! = p from rfl,
    show (#[p, q] : Array ByteArray)[(1 : UInt8).toNat]! = q from rfl] at hrun
  have hs : (Kernel.Ew.val op Kernel.Ew.i64 shape (Kernel.nullPayload .long) p q n.toUSize).size / 8 = n := by
    rw [← Verify.val_size8, USize.toNat_ofNat_of_lt' hn]
  rw [← hrun] at hs
  have hw := longWords_payload _ _ hn hs
  rw [← hR, hrun] at hw
  rw [Arr.toList_long R hw]

/-- **`a f x` at `long` on a dense column is its List spec** `x.mapM (a f ·)`: `atomCol_long`,
    `dyadColumn_long_av`, `run_val`, `val_i64_av`, and q's element `Ew.elem_long_val`. -/
theorem atomVal_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.enc = .bytes b) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.atomVal at hv
  rw [atomCol_long, hb] at hv
  simp only [bind, Except.bind] at hv
  have hR := dyad_enc (dyadColumn_long_av hop hr n _ b) hv
  have hel : (fun y : Int64 => elem v h k y) =
      fun y => pure (Kernel.Ew.intStep op Int64.minValue k y) := funext fun y => Ew.elem_long_val hop h k y
  rw [show (fun y : Carrier .long => elem v h k y) = _ from hel, List.mapM_pure, toList_val_long _ _ hn hR,
    val_i64_av _ _ _ _ _ hn, nullPayload_long, Arr.toList_long_bytes x hb]
  exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by simp)

/-- `a+x = ⟨!a, x⟩ ≫ (+)` from the kernel: `atomVal_rel` of `atomVal_spec_long`. Dense long column. -/
theorem atomVal_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.enc = .bytes b) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomVal_spec_long hop h hb hn hv)

/-- `dyadColumn` on a dense long column and a long atom column (right), at a value verb other than `^`
    (q's `x^atom` is `'nyi`): the one-stage `eVal` chain at `va`. -/
theorem dyadColumn_long_va {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op) (hf : v ≠ .fill)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (b c : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.va .long .long n (.bytes b) 1 (.bytes c) =
      some (.long, .vector .long n (Kernel.payload .long n.toUSize ({ inputs := #[b, c] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.va, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) none) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd rfl hf | exact absurd hr (by decide) | skip
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.va = Kernel.Ew.vv), *]

/-- `+ * & |` on two longs commute, nulls included: `intStep` swaps its operands. -/
theorem intStep_comm {op : UInt8}
    (hc : op = Kernel.Ew.add ∨ op = Kernel.Ew.mul ∨ op = Kernel.Ew.lesser ∨ op = Kernel.Ew.greater)
    (nul x y : Int64) : Kernel.Ew.intStep op nul x y = Kernel.Ew.intStep op nul y x := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp [Kernel.Ew.intStep, Bool.or_comm, Int64.add_comm]
  · simp [Kernel.Ew.intStep, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul, Bool.or_comm, Int64.mul_comm]
  all_goals
    simp only [Kernel.Ew.intStep, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul, Kernel.Ew.fill, Kernel.Ew.lesser,
      Kernel.Ew.greater]
    simp (config := { decide := true }) only [↓reduceIte, reduceCtorEq]
    by_cases h1 : x < y <;> by_cases h2 : y < x <;> simp only [h1, h2, ↓reduceIte]
    all_goals (rw [Int64.lt_iff_toInt_lt] at h1 h2; first | (exfalso; omega) | exact Int64.toInt_inj.1 (by omega))

/-- **`x f a` at `long` on a dense column is its List spec** `x.mapM (· f a)`. `Ew.flip` sends `+ * & |` to
    `atomVal` (`intStep_comm`); `-` and `^` keep `va` (`dyadColumn_long_va`, `Verify.val_i64_va`), where `^`
    raises. -/
theorem valAtom_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.enc = .bytes b) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
    x.toList.mapM (fun y => elem v h y k) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  have hsw : ∀ (hc : op = Kernel.Ew.add ∨ op = Kernel.Ew.mul ∨ op = Kernel.Ew.lesser ∨ op = Kernel.Ew.greater),
      (fun y : Carrier .long => elem v h y k) = fun y => elem v h k y := fun hc => funext fun y => by
    rw [Ew.elem_long_val hop h, Ew.elem_long_val hop h, intStep_comm hc]
  unfold Ew.valAtom at hv
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd h (by decide) | skip
  case add | mul | lesser | greater =>
    all_goals (simp only [Ew.flip] at hv; rw [hsw (by simp)]; exact atomVal_spec_long rfl h hb hn hv)
  all_goals (
    simp only [Ew.flip] at hv
    rw [atomCol_long, hb] at hv
    simp only [bind, Except.bind] at hv)
  case fill => simp [Ew.dyad, Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.Ew.va] at hv
  case sub =>
    have hR := dyad_enc (dyadColumn_long_va rfl (by decide) hr n b _) hv
    have hel : (fun y : Int64 => elem .sub h y k) =
        fun y => pure (Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue y k) :=
      funext fun y => Ew.elem_long_val rfl h y k
    rw [show (fun y : Carrier .long => elem .sub h y k) = _ from hel, List.mapM_pure, toList_val_long _ _ hn hR,
      Verify.val_i64_va _ _ _ _ _ hn, nullPayload_long, Arr.toList_long_bytes x hb]
    exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by simp)

/-- `x+a = ⟨x, !a⟩ ≫ (+)` from the kernel: `valAtom_rel` of `valAtom_spec_long`. Dense long column. -/
theorem valAtom_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.enc = .bytes b) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (valAtom_spec_long hop h hb hn hv)

/-- A long atom's seed bits, as `Ew.prior` reads them for `shiftColumn`'s `fill`. -/
theorem atomBits_long (s : Int64) :
    Ew.atomBits .long (.bytes (Kernel.atomBytes Kernel.Ew.i64 s.toUInt64)) = .ok s.toUInt64 := by
  simp only [Ew.atomBits, Enc.bytesOf, QAtomicType.width]
  exact congrArg Except.ok (Verify.bitsAt_pushBits8 ByteArray.empty _)

/-- A `B` listing `A`'s words one behind `s` has `A`'s count, and word `i` of `B` is word `i` of `s :: A`. -/
theorem shift_words {n : Nat} {s : Int64} {A B : ByteArray} (hA : A.size / 8 = n)
    (hB : Verify.elemsW 8 B = Verify.elemsW 8 (Kernel.shiftBytes (8 : Nat).toUSize s.toUInt64 1 A)) :
    B.size / 8 = n ∧ ∀ i < n, Column.bitsAt B (i * 8) 8 =
      (s.toUInt64 :: (List.range n).map fun i => Column.bitsAt A (i * 8) 8)[i]?.getD 0 := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have he := Verify.shiftBytes_one (8 : Nat).toUSize (by rw [h8]; decide) (by rw [h8]; decide) s.toUInt64
    (by rw [h8]; exact UInt64.toNat_lt _) A
  rw [h8, ← hB] at he
  have hl : B.size / 8 = n := by
    have := congrArg List.length he
    simpa [Verify.elemsW, hA] using this
  refine ⟨hl, fun i hi => ?_⟩
  have e := congrArg (fun l => l[i]?.getD 0) he
  simp only [List.getElem?_dropLast, List.length_cons, Verify.elemsW, List.length_map, List.length_range, hA,
    Nat.add_sub_cancel, if_pos hi] at e
  rw [← e]
  simp [Verify.elemsW, hl, hi]

/-- The reading every `long` `seed f': x` kernel ends in: an answer listing the dense `vv` pass over `A`, which
    lists `x`'s words, and a `B` listing `A`'s words one behind `seed`, is the List spec. -/
theorem prior_spec_words {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {A B : ByteArray}
    (hn : n < USize.size) (hx : longWords n x.enc = some (Verify.elemsW 8 A)) (hA : A.size / 8 = n)
    (hB : Verify.elemsW 8 B = Verify.elemsW 8 (Kernel.shiftBytes (8 : Nat).toUSize s.toUInt64 1 A))
    (hR : longWords n R.enc = some (Verify.elemsW 8
      (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue A B n.toUSize))) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  obtain ⟨_, hsb⟩ := shift_words hA hB
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.intStep op Int64.minValue p.1 p.2) := funext fun p => Ew.elem_long_val hop h p.1 p.2
  rw [Verify.val_i64_vv _ _ _ _ _ hn] at hR
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    Arr.toList_long R hR, Arr.toList_long x hx]
  refine congrArg Except.ok (List.ext_getElem (by simp [Verify.elemsW, hA]) fun i h1 h2 => ?_)
  have hi : i < n := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, hsb i hi]
  cases i with
  | zero => simp [Verify.elemsW, hA, hi]
  | succ j => simp [Verify.elemsW, hA, show j < n by omega]

/-- The reading every `long` `seed <': x` kernel ends in: a bitmap of the dense `vv` comparison over `A`, which
    lists `x`'s words, and a `B` listing `A`'s words one behind `seed`, is the List spec. -/
theorem priorCmp_spec_words {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {A B : ByteArray} (hn : n < USize.size) (hx : longWords n x.enc = some (Verify.elemsW 8 A)) (hA : A.size / 8 = n)
    (hB : Verify.elemsW 8 B = Verify.elemsW 8 (Kernel.shiftBytes (8 : Nat).toUSize s.toUInt64 1 A))
    (hc : R.enc = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv A B n.toUSize)) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  obtain ⟨_, hsb⟩ := shift_words hA hB
  have hE : ∀ (c : ByteArray) j, Kernel.Ew.elem Kernel.Ew.i64 c j = Column.bitsAt c (j * 8) 8 := fun _ _ => by
    simp [Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32, Kernel.Ew.f32]
  have hs : ∀ i, Kernel.Ew.shapeIdx Kernel.Ew.vv i = (i, i) := fun i => by simp [Kernel.Ew.shapeIdx]
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 p.1.toUInt64 p.2.toUInt64) :=
    funext fun p => Ew.elem_long_cmp hop h p.1 p.2
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    toList_cmp_bits hn hc, Arr.toList_long x hx]
  refine congrArg Except.ok (List.ext_getElem (by simp [Verify.elemsW, hA]) fun i h1 h2 => ?_)
  have hi : i < n := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, hs, hE, hsb i hi]
  cases i with
  | zero => simp [Verify.elemsW, hA, hi]
  | succ j => simp [Verify.elemsW, hA, show j < n by omega]

/-- `shiftColumn` by one on a dense long column: the dense `shiftBytes`, `fill` first. -/
theorem shiftColumn_long_bytes {n : Nat} {a : ByteArray} (fill : UInt64) (hs : a.size / 8 = n) :
    Kernel.shiftColumn .long 1 fill n (.bytes a) = some (.bytes (Kernel.shiftBytes 8 fill 1 a)) := by
  have hl : ¬ a.size < n * 8 := by omega
  simp [Kernel.shiftColumn, Kernel.foRColumn, Kernel.denseWidth, Enc.bytesOf, QAtomicType.width, hl] <;> rfl

/-- **`seed f': x` at `long` on a dense column is its List spec** `zip(x, seed :: x).mapM f`: the seed's bits
    (`atomCol_long`, `bitsAt_pushBits8`), `shiftColumn_long_bytes` and `shiftBytes_one` for the prior operand,
    then `dyadColumn_long_vv`, `val_i64_vv` and q's element `Ew.elem_long_val`. -/
theorem prior_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {a : ByteArray}
    (ha : x.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [atomBits_long] at hv
  simp only at hv
  rw [ha, shiftColumn_long_bytes _ (Arr.n_long_bytes x ha)] at hv
  simp only at hv
  have hrun := Verify.run_val ({ inputs := #[a, Kernel.shiftBytes 8 s.toUInt64 1 a] } : Kernel.Ew.Build) rfl op
    Kernel.Ew.i64 Kernel.Ew.vv 0 1 (Kernel.nullPayload .long) (by decide) (by decide) n.toUSize
  simp only [show (#[a, Kernel.shiftBytes 8 s.toUInt64 1 a] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, Kernel.shiftBytes 8 s.toUInt64 1 a] : Array ByteArray)[(1 : UInt8).toNat]! =
      Kernel.shiftBytes 8 s.toUInt64 1 a from rfl] at hrun
  exact prior_spec_words hop h hn (by simp only [longWords, ha]) (Arr.n_long_bytes x ha) rfl
    (longWords_run_val hn (dyad_enc (dyadColumn_long_vv hop hr n a _) hv) hrun)

/-- `seed f': x = ⟨x, prev⟩ ≫ f` from the kernel: `prior_rel` of `prior_spec_long`. Dense long column. -/
theorem prior_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {a : ByteArray}
    (ha : x.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (prior_spec_long hop h ha hn hv)

/-- `shiftColumn` by one on a `foR` long column: the dense `shiftBytes` of the decode where `denseCheaper` (or
    an empty metadata) sends it, else `shiftFoR`'s blocks, which `Enc.answer` keeps or decodes. The dense
    branch needs the decode to fill the header count (`hs`), else the kernel refuses. -/
theorem shiftColumn_long_foR (n : Nat) (md pk : ByteArray) (fill : UInt64)
    (hs : ¬ (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize).size < n * 8) :
    Kernel.shiftColumn .long 1 fill n (.foR md pk) = some (.bytes
      (Kernel.shiftBytes (8 : Nat).toUSize fill 1 (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize))) ∨
    Kernel.shiftColumn .long 1 fill n (.foR md pk) = some (Enc.answer .long n (.foR
      (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 fill).1
      (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 fill).2)) := by
  unfold Kernel.shiftColumn
  by_cases hm : md.isEmpty
  · left; simp [hm, hs, Kernel.foRColumn, Kernel.denseWidth, Enc.bytesOf, QAtomicType.width, Column.encodes] <;> rfl
  · cases hd : Kernel.denseCheaper 5 n 8 ((n + Column.blk - 1) / Column.blk)
    · right; simp [hm, hd, Kernel.foRColumn, Kernel.denseWidth, Enc.bytesOf, QAtomicType.width, Column.encodes] <;> rfl
    · left; simp [hm, hd, hs, Kernel.foRColumn, Kernel.denseWidth, Enc.bytesOf, QAtomicType.width, Column.encodes] <;> rfl

/-- **`seed f': x` at `long` on a `foR` column is its List spec** `zip(x, seed :: x).mapM f`: the prior operand
    is dense (`longWords_Fb`) or `shiftFoR`'s blocks (`shiftFoR_spec`), kept encoded (`longWords_val_foR`) or
    decoded (`longWords_Fb`), each read by `prior_spec_words`. -/
theorem prior_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [atomBits_long] at hv
  simp only at hv
  rw [ha] at hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  have hF := Verify.shiftFoR_spec 8 (by decide) (by decide) md pk n.toUSize 1 s.toUInt64
  rcases shiftColumn_long_foR n md pk s.toUInt64 (by omega) with hs | hs <;> rw [hs] at hv <;> simp only at hv
  · exact prior_spec_words hop h hn hx hxs rfl
      (longWords_Fb hn (dyad_enc (dyadColumn_long_vv_mixed hop hr n _ md pk).2 hv))
  · rcases Verify.answer_foR .long 8 n (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 s.toUInt64).1
      (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 s.toUInt64).2 rfl with e | e <;> rw [e] at hv
    · exact prior_spec_words hop h hn hx hxs hF (by
        rw [dyad_enc (dyadColumn_long_vv_foR hop hr n md pk _ _) hv]; exact longWords_val_foR op _ _ _ _ hn)
    · exact prior_spec_words hop h hn hx hxs hF
        (longWords_Fb hn (dyad_enc (dyadColumn_long_vv_mixed hop hr n _ md pk).2 hv))

/-- `seed f': x = ⟨x, prev⟩ ≫ f` from the kernel: `prior_rel` of `prior_spec_long_foR`. `foR` column. -/
theorem prior_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (prior_spec_long_foR hop h ha hn hv)

/-- A comparison at `i64` read the other way round is the flipped comparison: `x<y = y>x` (`Ew.flip`). -/
theorem cmpStep_flip {v vf : Prim.Dyadic} {op opf : UInt8} (hop : Kernel.cmpOp v = some op)
    (hf : Ew.flip v = some vf) (hopf : Kernel.cmpOp vf = some opf) (x y : UInt64) :
    Kernel.Ew.cmpStep op Kernel.Ew.i64 x y = Kernel.Ew.cmpStep opf Kernel.Ew.i64 y x := by
  have hsw : ∀ a b : Int64, compare b a = (compare a b).swap := fun a b => by
    rw [Ew.compare_toInt, Ew.compare_toInt]
    simp only [compare, compareOfLessAndEq]
    by_cases h1 : a.toInt < b.toInt <;> by_cases h2 : b.toInt < a.toInt <;> by_cases h3 : a.toInt = b.toInt <;>
      simp [h1, h2, h3, Ordering.swap] <;> omega
  cases v <;> simp only [Ew.flip, Option.some.injEq, reduceCtorEq] at hf <;> subst hf <;>
    simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop hopf <;> subst hop hopf
  all_goals
    unfold Kernel.Ew.cmpStep
    rw [hsw (Kernel.Ew.signed Kernel.Ew.i64 x) (Kernel.Ew.signed Kernel.Ew.i64 y)]
    generalize compare (Kernel.Ew.signed Kernel.Ew.i64 x) (Kernel.Ew.signed Kernel.Ew.i64 y) = o
    cases o <;> simp (config := { decide := true }) [Kernel.Ew.i64, Kernel.Ew.f64, Kernel.Ew.f32, Kernel.Ew.eq,
      Kernel.Ew.ne, Kernel.Ew.lt, Kernel.Ew.le, Kernel.Ew.gt, Kernel.Ew.ge, Ordering.swap]

/-- `Dep.elem` of a comparison on two longs, its operands swapped, is the flipped comparison. -/
theorem elem_cmp_flip {v vf : Prim.Dyadic} {op opf : UInt8} (h : Eval.ewType v .long .long = some .boolean)
    (hop : Kernel.cmpOp v = some op) (hf : Ew.flip v = some vf) (hopf : Kernel.cmpOp vf = some opf)
    (h' : Eval.ewType vf .long .long = some .boolean) (y k : Int64) : elem v h y k = elem vf h' k y := by
  rw [Ew.elem_long_cmp hop h, Ew.elem_long_cmp hopf h', cmpStep_flip hop hf hopf]

/-- A boolean answer of a one-stage `eCmp` chain over two inputs is `cmpStep` of the elements the shape
    reads (`run_cmp`, `cmp_bitAt`). -/
theorem toList_cmp_long {op shape : UInt8} {n : Nat} {R : Arr .boolean n} (p q : ByteArray) (hn : n < USize.size)
    (hR : R.enc = Kernel.payload .boolean n.toUSize ({ inputs := #[p, q] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape, a := 0, b := 1, nul := 0 })) :
    R.toList = (List.range n).map fun i => Kernel.Ew.cmpStep op Kernel.Ew.i64
      (Kernel.Ew.elem Kernel.Ew.i64 p (Kernel.Ew.shapeIdx shape i).1)
      (Kernel.Ew.elem Kernel.Ew.i64 q (Kernel.Ew.shapeIdx shape i).2) := by
  have hrun := Verify.run_cmp ({ inputs := #[p, q] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 shape 0 1 0
    (by decide) (by decide) n.toUSize
  simp only [show (#[p, q] : Array ByteArray)[(0 : UInt8).toNat]! = p from rfl,
    show (#[p, q] : Array ByteArray)[(1 : UInt8).toNat]! = q from rfl] at hrun
  exact toList_cmp_bits hn (by rw [hR, ← hrun]; simp [Kernel.payload])

/-- The long atom's one element, as the comparison engine reads it at index `0`. -/
theorem elem_atomBytes_long (k : Int64) :
    Kernel.Ew.elem Kernel.Ew.i64 (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64) 0 = k.toUInt64 := by
  simp only [Kernel.Ew.elem, Nat.zero_mul]
  exact Verify.bitsAt_pushBits8 ByteArray.empty _

/-- `dyadColumn` on a long atom column (left) and a dense long column, at a comparison: the one-stage
    `eCmp` chain at `av`. -/
theorem dyadColumn_long_av_cmp {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (c b : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long 1 (.bytes c) n (.bytes b) =
      some (.boolean, .vector .boolean n (Kernel.payload .boolean n.toUSize ({ inputs := #[c, b] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1, nul := 0 })) none) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.foRPair, Kernel.zipPass, Kernel.operandSource, Kernel.operandAt,
    Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va), *]

/-- **`a<x` at `long` on a dense column is its List spec** `x.mapM (a < ·)`: `atomCol_long`,
    `dyadColumn_long_av_cmp`, `toList_cmp_long`, and q's element `Ew.elem_long_cmp`. -/
theorem atomCmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.atomVal at hv
  rw [atomCol_long, hb] at hv
  simp only [bind, Except.bind] at hv
  have hR := dyad_enc (dyadColumn_long_av_cmp hop hr n _ b) hv
  have hel : (fun y : Int64 => elem v h k y) = fun y => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 k.toUInt64 y.toUInt64) :=
    funext fun y => Ew.elem_long_cmp hop h k y
  rw [show (fun y : Carrier .long => elem v h k y) = _ from hel, List.mapM_pure, toList_cmp_long _ _ hn hR,
    Arr.toList_long_bytes x hb]
  refine congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => ?_)
  have hs : Kernel.Ew.shapeIdx Kernel.Ew.av i = (0, i) := by simp [Kernel.Ew.shapeIdx, Kernel.Ew.av, Kernel.Ew.vv, Kernel.Ew.va]
  simp only [List.getElem_map, List.getElem_range, hs, elem_atomBytes_long]
  simp [Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32, Kernel.Ew.f32]

/-- `a<x = ⟨!a, x⟩ ≫ (<)` from the kernel: `atomVal_rel` of `atomCmp_spec_long`. Dense long column. -/
theorem atomCmp_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomCmp_spec_long hop h hb hn hv)

/-- **`x<a` at `long` on a dense column is its List spec** `x.mapM (· < a)`: `Ew.flip` sends every comparison
    to `atomVal` of the flipped one (`elem_cmp_flip`, `atomCmp_spec_long`). -/
theorem cmpAtom_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.valAtom v .boolean (u := .long) x k = .ok R) :
    x.toList.mapM (fun y => elem v h y k) = .ok R.toList := by
  unfold Ew.valAtom at hv
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals
    simp only [Ew.flip] at hv
    exact (congrArg x.toList.mapM (funext fun y => elem_cmp_flip h rfl rfl rfl (by decide) y k)).trans
      (atomCmp_spec_long rfl (by decide) hb hn hv)

/-- `x<a = ⟨x, !a⟩ ≫ (<)` from the kernel: `valAtom_rel` of `cmpAtom_spec_long`. Dense long column. -/
theorem cmpAtom_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.valAtom v .boolean (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (cmpAtom_spec_long hop h hb hn hv)

/-! ### Atom forms on a `foR` column

  `foRValPayload` reads the vector and the atom through `foRPair`: `*` tries `foRScale`, `+ -` try
  `foRShift`, and whatever they decline, and every other verb, answers `foRValAtom`'s dense payload. The
  comparisons answer `foRCmp`'s bitmap. -/

/-- `x-k` is `x+(-k)` at q's null, null `k` included: `-0N` is `0N`. -/
theorem intStep_sub_neg (x k : Int64) :
    Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue x k = Kernel.Ew.intStep Kernel.Ew.add Int64.minValue x (-k) := by
  have hk : (-k == Int64.minValue) = (k == Int64.minValue) := by
    by_cases e : k = Int64.minValue
    · subst e; decide
    · have e' : -k ≠ Int64.minValue := fun h' => e (by
        have h2 := congrArg (fun z : Int64 => -z) h'
        simp only [Int64.neg_neg] at h2
        rw [h2]; decide)
      rw [beq_eq_false_iff_ne.2 e, beq_eq_false_iff_ne.2 e']
  simp only [Kernel.Ew.intStep, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul, Kernel.Ew.fill, Kernel.Ew.lesser,
    Kernel.Ew.greater]
  simp (config := { decide := true }) only [↓reduceIte, reduceCtorEq]
  rw [hk, Int64.sub_eq_add_neg]

/-- `cmpFlip` swaps a comparison's operands. -/
theorem cmpStep_cmpFlip {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op) (x y : UInt64) :
    Kernel.Ew.cmpStep (Kernel.Ew.cmpFlip op) Kernel.Ew.i64 x y = Kernel.Ew.cmpStep op Kernel.Ew.i64 y x := by
  have hsw : ∀ a b : Int64, compare b a = (compare a b).swap := fun a b => by
    rw [Ew.compare_toInt, Ew.compare_toInt]
    simp only [compare, compareOfLessAndEq]
    by_cases h1 : a.toInt < b.toInt <;> by_cases h2 : b.toInt < a.toInt <;> by_cases h3 : a.toInt = b.toInt <;>
      simp [h1, h2, h3, Ordering.swap] <;> omega
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals
    unfold Kernel.Ew.cmpStep Kernel.Ew.cmpFlip
    rw [hsw (Kernel.Ew.signed Kernel.Ew.i64 y) (Kernel.Ew.signed Kernel.Ew.i64 x)]
    generalize compare (Kernel.Ew.signed Kernel.Ew.i64 y) (Kernel.Ew.signed Kernel.Ew.i64 x) = o
    cases o <;> simp (config := { decide := true }) [Kernel.Ew.i64, Kernel.Ew.f64, Kernel.Ew.f32, Kernel.Ew.eq,
      Kernel.Ew.ne, Kernel.Ew.lt, Kernel.Ew.le, Kernel.Ew.gt, Kernel.Ew.ge, Ordering.swap]

/-- `dyadColumn` on a long atom column (left) and a `foR` long column, at a value verb whose result is `long`:
    `foRValPayload`'s atom branch at `av`. -/
theorem dyadColumn_long_av_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (c md pk : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long 1 (.bytes c) n (.foR md pk) =
      some (.long, .vector .long n (match (if op == Kernel.Ew.mul then
            Kernel.Ew.foRScale (Kernel.Ew.elem Kernel.Ew.i64 c 0).toInt64 md pk n.toUSize
          else if op == Kernel.Ew.add || op == Kernel.Ew.sub then
            Kernel.Ew.foRShift (op == Kernel.Ew.sub) (Kernel.Ew.elem Kernel.Ew.i64 c 0).toInt64 md pk n.toUSize
          else none) with
        | some (m, p) => Enc.answer .long n (.foR m p)
        | none => Enc.answer .long n (.bytes (Kernel.Ew.foRValAtom op Kernel.Ew.i64 Kernel.Ew.av
            (Kernel.nullPayload .long) md pk n.toUSize
            (Kernel.atomBytes Kernel.Ew.i64 (Kernel.Ew.elem Kernel.Ew.i64 c 0))))) none) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul,
    Kernel.Ew.div, Kernel.Ew.fill, Kernel.Ew.lesser, Kernel.Ew.greater, *]
  -- at `n = 1` the atom and the vector both pass `dyadCount`, and `simp` leaves the `some` outside the match
  all_goals first
    | (refine ⟨_, .inl ?_, rfl⟩; split <;> simp [*])
    | (left; split <;> simp [*])
    | (right; split <;> simp [*])

/-- `dyadColumn` on a `foR` long column and a long atom column (right), at `-`, the one value verb `Ew.flip`
    leaves at `va`: `foRShift` of the negated atom, else `foRValAtom`. -/
theorem dyadColumn_long_va_sub_foR (n : Nat) (md pk c : ByteArray) :
    Kernel.dyadColumn .sub Kernel.Ew.va .long .long n (.foR md pk) 1 (.bytes c) =
      some (.long, .vector .long n (match Kernel.Ew.foRShift false (-(Kernel.Ew.elem Kernel.Ew.i64 c 0).toInt64) md pk
          n.toUSize with
        | some (m, p) => Enc.answer .long n (.foR m p)
        | none => Enc.answer .long n (.bytes (Kernel.Ew.foRValAtom Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va
            (Kernel.nullPayload .long) md pk n.toUSize
            (Kernel.atomBytes Kernel.Ew.i64 (Kernel.Ew.elem Kernel.Ew.i64 c 0))))) none) := by
  have hr : Kernel.resultType .sub .long .long = some .long := by decide
  by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.va = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.va = Kernel.Ew.av),
    (by decide : (Kernel.Ew.va == Kernel.Ew.av) = false),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or, Kernel.Ew.add, Kernel.Ew.sub, Kernel.Ew.mul, *]
  all_goals first
    | (refine ⟨_, .inl ?_, rfl⟩; split <;> simp [*])
    | (left; split <;> simp [*])
    | (right; split <;> simp [*])

/-- `dyadColumn` on a long atom column (left) and a `foR` long column, at a comparison: `foRCmp`'s bitmap of
    the flipped comparison. -/
theorem dyadColumn_long_av_cmp_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (c md pk : ByteArray) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long 1 (.bytes c) n (.foR md pk) =
      some (.boolean, .vector .boolean n (.bits (Kernel.Ew.foRCmp (Kernel.Ew.cmpFlip op)
        (Kernel.Ew.elem Kernel.Ew.i64 c 0).toInt64 md pk n.toUSize)) none) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.foRPair, Kernel.zipPass, Kernel.operandSource, Kernel.operandAt,
    Enc.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va),
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or, *]

/-- The dense payload `foRValAtom` answers, at `long`, is `Ew.val` over the decoded vector and the atom, and
    holds `n` words. -/
theorem foRValAtom_long (op shape : UInt8) (md pk atom : ByteArray) {n : Nat} (hn : n < USize.size) :
    (Kernel.Ew.foRValAtom op Kernel.Ew.i64 shape (Kernel.nullPayload .long) md pk n.toUSize atom).size / 8 = n ∧
    Kernel.Ew.foRValAtom op Kernel.Ew.i64 shape (Kernel.nullPayload .long) md pk n.toUSize atom =
      if shape == Kernel.Ew.va
      then Kernel.Ew.val op Kernel.Ew.i64 shape Int64.minValue (Kernel.Coc.decode 8 md pk n.toUSize) atom n.toUSize
      else Kernel.Ew.val op Kernel.Ew.i64 shape Int64.minValue atom (Kernel.Coc.decode 8 md pk n.toUSize) n.toUSize := by
  have he : Kernel.Ew.foRValAtom op Kernel.Ew.i64 shape (Kernel.nullPayload .long) md pk n.toUSize atom =
      if shape == Kernel.Ew.va
      then Kernel.Ew.val op Kernel.Ew.i64 shape Int64.minValue (Kernel.Coc.decode 8 md pk n.toUSize) atom n.toUSize
      else Kernel.Ew.val op Kernel.Ew.i64 shape Int64.minValue atom (Kernel.Coc.decode 8 md pk n.toUSize)
        n.toUSize := by
    rw [nullPayload_long]; rfl
  refine ⟨?_, he⟩
  rw [he]
  split <;> rw [← Verify.val_size8, USize.toNat_ofNat_of_lt' hn]

/-- **`a f x` at `long` on a `foR` column is its List spec** `x.mapM (a f ·)`: `foRScale_spec` (`k*x` read as
    `x*k`, `intStep_comm`), `foRShift_spec`, or `foRValAtom`, each read by `mapM_spec_words`. -/
theorem atomVal_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  have hk : k.toUInt64.toInt64 = k := by simp
  have h8 : (8 : Nat).toUSize = (8 : USize) := rfl
  unfold Ew.atomVal at hv
  rw [atomCol_long, ha] at hv
  simp only [bind, Except.bind] at hv
  have hR := dyad_enc (dyadColumn_long_av_foR hop hr n _ md pk) hv
  rw [elem_atomBytes_long, hk] at hR
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  rw [h8] at hx hxs
  refine mapM_spec_words (fun y => Ew.elem_long_val hop h k y) hx hxs ?_
  rw [hR]
  split
  · rename_i m p hvv
    rw [longWords_answer_foR m p hn, h8]
    refine congrArg some ?_
    split at hvv
    · rename_i hm
      rw [Verify.foRScale_spec k md pk _ m p hvv,
        show Column.pushBits ByteArray.empty k.toUInt64 8 = Kernel.atomBytes Kernel.Ew.i64 k.toUInt64 from rfl,
        Verify.val_i64_va _ _ _ _ _ hn]
      refine List.map_congr_left fun i _ => ?_
      rw [beq_iff_eq.1 hm, hk, intStep_comm (Or.inr (Or.inl rfl))]
    · split at hvv
      · rename_i _ has
        rw [Verify.foRShift_spec _ k md pk _ m p hvv,
          show Column.pushBits ByteArray.empty k.toUInt64 8 = Kernel.atomBytes Kernel.Ew.i64 k.toUInt64 from rfl]
        rcases (by simpa using has : op = Kernel.Ew.add ∨ op = Kernel.Ew.sub) with rfl | rfl
        · rw [if_neg (by decide), Verify.val_i64_va _ _ _ _ _ hn]
          refine List.map_congr_left fun i _ => ?_
          rw [hk, intStep_comm (Or.inl rfl)]
        · rw [if_pos (by decide), val_i64_av _ _ _ _ _ hn]
          simp only [hk]
      · cases hvv
  · obtain ⟨hs, he⟩ := foRValAtom_long op Kernel.Ew.av md pk (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64) hn
    have hw := longWords_answer (Kernel.Ew.foRValAtom op Kernel.Ew.i64 Kernel.Ew.av (Kernel.nullPayload .long) md pk
      n.toUSize (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64)) hs
    rw [hw, he, if_neg (by decide), val_i64_av _ _ _ _ _ hn]
    simp only [hk]

/-- `a+x = ⟨!a, x⟩ ≫ (+)` from the kernel: `atomVal_rel` of `atomVal_spec_long_foR`. `foR` column. -/
theorem atomVal_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomVal_spec_long_foR hop h ha hn hv)

/-- **`x f a` at `long` on a `foR` column is its List spec** `x.mapM (· f a)`. `Ew.flip` sends `+ * & |` to
    `atomVal_spec_long_foR`; `x-k` is `foRShift` of `-k` (`intStep_sub_neg`) or `foRValAtom` at `va`. -/
theorem valAtom_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
    x.toList.mapM (fun y => elem v h y k) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  have hsw : ∀ (hc : op = Kernel.Ew.add ∨ op = Kernel.Ew.mul ∨ op = Kernel.Ew.lesser ∨ op = Kernel.Ew.greater),
      (fun y : Carrier .long => elem v h y k) = fun y => elem v h k y := fun hc => funext fun y => by
    rw [Ew.elem_long_val hop h, Ew.elem_long_val hop h, intStep_comm hc]
  have hk : k.toUInt64.toInt64 = k := by simp
  have h8 : (8 : Nat).toUSize = (8 : USize) := rfl
  unfold Ew.valAtom at hv
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd h (by decide) | skip
  case add | mul | lesser | greater =>
    all_goals (simp only [Ew.flip] at hv; rw [hsw (by simp)]; exact atomVal_spec_long_foR rfl h ha hn hv)
  all_goals (
    simp only [Ew.flip] at hv
    rw [atomCol_long, ha] at hv
    simp only [bind, Except.bind] at hv)
  case fill => simp [Ew.dyad, Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.Ew.va] at hv
  case sub =>
    have hR := dyad_enc (dyadColumn_long_va_sub_foR n md pk _) hv
    rw [elem_atomBytes_long, hk] at hR
    obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
    rw [h8] at hx hxs
    refine mapM_spec_words (fun y => Ew.elem_long_val rfl h y k) hx hxs ?_
    rw [hR]
    split
    · rename_i m p hvv
      rw [longWords_answer_foR m p hn, h8, Verify.foRShift_spec _ _ md pk _ m p hvv, if_neg (by decide),
        show Column.pushBits ByteArray.empty (-k).toUInt64 8 = Kernel.atomBytes Kernel.Ew.i64 (-k).toUInt64 from rfl,
        Verify.val_i64_va _ _ _ _ _ hn]
      refine congrArg some (List.map_congr_left fun i _ => ?_)
      rw [intStep_sub_neg]; simp
    · obtain ⟨hs, he⟩ := foRValAtom_long Kernel.Ew.sub Kernel.Ew.va md pk (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64) hn
      have hw := longWords_answer (Kernel.Ew.foRValAtom Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va
        (Kernel.nullPayload .long) md pk n.toUSize (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64)) hs
      rw [hw, he, if_pos (by decide), Verify.val_i64_va _ _ _ _ _ hn]
      simp only [hk]

/-- `x+a = ⟨x, !a⟩ ≫ (+)` from the kernel: `valAtom_rel` of `valAtom_spec_long_foR`. `foR` column. -/
theorem valAtom_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {md pk : ByteArray}
    (ha : x.enc = .foR md pk) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (valAtom_spec_long_foR hop h ha hn hv)

/-- **`a<x` at `long` on a `foR` column is its List spec** `x.mapM (a < ·)`: `foRCmp_bitAt` of the flipped
    comparison (`cmpStep_cmpFlip`). -/
theorem atomCmp_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  have hk : k.toUInt64.toInt64 = k := by simp
  have h8 : (8 : Nat).toUSize = (8 : USize) := rfl
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  unfold Ew.atomVal at hv
  rw [atomCol_long, ha] at hv
  simp only [bind, Except.bind] at hv
  have hR := dyad_enc (dyadColumn_long_av_cmp_foR hop hr n _ md pk) hv
  rw [elem_atomBytes_long, hk] at hR
  have hc : R.enc = .bits (Kernel.Ew.foRCmp (Kernel.Ew.cmpFlip op) k md pk n.toUSize) := by rw [hR]
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  rw [h8] at hx hxs
  have hel : (fun y : Int64 => elem v h k y) = fun y => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 k.toUInt64 y.toUInt64) :=
    funext fun y => Ew.elem_long_cmp hop h k y
  rw [show (fun y : Carrier .long => elem v h k y) = _ from hel, List.mapM_pure, Arr.toList_long x hx]
  refine congrArg Except.ok (List.ext_getElem (by rw [Arr.length_toList]; simp [Verify.elemsW, hxs]) fun i h1 h2 => ?_)
  have hi : i < n := by rw [Arr.length_toList] at h2; exact h2
  rw [Arr.getElem_toList, Arr.get_bool_bits R hc, (Verify.foRCmp_bitAt _ _ _ _ _).2 i (by rw [hN]; omega),
    cmpStep_cmpFlip hop]
  simp [hN, hi, Verify.elemsW, hxs, Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16,
    Kernel.Ew.i32, Kernel.Ew.f32]

/-- `a<x = ⟨!a, x⟩ ≫ (<)` from the kernel: `atomVal_rel` of `atomCmp_spec_long_foR`. `foR` column. -/
theorem atomCmp_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomCmp_spec_long_foR hop h ha hn hv)

/-- **`x<a` at `long` on a `foR` column is its List spec** `x.mapM (· < a)`: `Ew.flip`, then
    `atomCmp_spec_long_foR`. -/
theorem cmpAtom_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.valAtom v .boolean (u := .long) x k = .ok R) :
    x.toList.mapM (fun y => elem v h y k) = .ok R.toList := by
  unfold Ew.valAtom at hv
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals
    simp only [Ew.flip] at hv
    exact (congrArg x.toList.mapM (funext fun y => elem_cmp_flip h rfl rfl rfl (by decide) y k)).trans
      (atomCmp_spec_long_foR rfl (by decide) ha hn hv)

/-- `x<a = ⟨x, !a⟩ ≫ (<)` from the kernel: `valAtom_rel` of `cmpAtom_spec_long_foR`. `foR` column. -/
theorem cmpAtom_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.valAtom v .boolean (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (cmpAtom_spec_long_foR hop h ha hn hv)

/-- `monColumn "neg"` on a `foR` long column: `negAbsPayload`'s encoded branch, `foRMonEnc`, which re-encodes
    the dense `Ew.mon` over the decode. -/
theorem monColumn_neg_foR (n : Nat) (md pk : ByteArray) :
    Kernel.monColumn "neg" .long n (.foR md pk) = some (.long, Enc.answer .long n
      (.foR (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).1
        (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).2)) := by
  simp [Kernel.monColumn, Kernel.monResultType, Kernel.negType, Kernel.monPayload, Kernel.negAbsPayload,
    Kernel.mapPass, Kernel.operandSource, Kernel.clsOf, Kernel.Ew.Build.input, show Prim.nonNumeric .long = false by decide,
    Option.orElse_eq_orElse, Option.orElse_eq_or, Option.some_or]

/-- **`-x` at `long` on a `foR` column is `MapSpec`** of `monStep`'s `neg`: `foRMonEnc` re-encodes `Ew.mon` over
    the decode (`decode_of_encode8`), whose words `mon_i64` reads. -/
theorem neg_spec_long_foR {n : Nat} {x R : Arr .long n} {md pk : ByteArray} (ha : x.enc = .foR md pk)
    (hn : n < USize.size) (hv : Ew.mon "neg" .long x = .ok R) :
    Ew.MapSpec (t := .long) (rt := .long) (fun y : Int64 =>
      (Kernel.Ew.monStep Kernel.Ew.neg Kernel.Ew.i64 Int64.minValue.toUInt64 y.toUInt64).toInt64) x R := by
  have h8 : (8 : Nat).toUSize = (8 : USize) := rfl
  have hR := mon_enc (by rw [ha]; exact monColumn_neg_foR _ _ _) hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  rw [h8] at hx hxs
  have hw := longWords_answer_foR
    (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).1
    (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).2 hn
  rw [← hR, h8] at hw
  have hM : (Kernel.Ew.mon Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) (Kernel.Coc.decode 8 md pk n.toUSize)
      n.toUSize).size / 8 = n := by
    have := congrArg List.length (mon_i64 Kernel.Ew.neg (Kernel.nullPayload .long) (Kernel.Coc.decode 8 md pk n.toUSize) n hn)
    simpa [Verify.elemsW] using this
  have he := Verify.decode_of_encode8
    (x := Kernel.Ew.mon Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) (Kernel.Coc.decode 8 md pk n.toUSize)
      n.toUSize)
    (m := (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).1)
    (p := (Kernel.Ew.foRMonEnc Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) md pk n.toUSize).2)
    (n := n.toUSize) rfl (by rw [hM, USize.toNat_ofNat_of_lt' hn])
  rw [he, mon_i64 _ _ _ _ hn, nullPayload_long] at hw
  exact map_spec_words hx hxs (by rw [hw]; simp)

/-- `-x = x ≫ neg` from the kernel: `mon_rel` of `neg_spec_long_foR`. `foR` column. -/
theorem neg_rel_long_foR {n : Nat} {x R : Arr .long n} {md pk : ByteArray} (ha : x.enc = .foR md pk)
    (hn : n < USize.size) (hv : Ew.mon "neg" .long x = .ok R) :
    R.rel = x.rel ≫ graph (fun y : Int64 =>
      (Kernel.Ew.monStep Kernel.Ew.neg Kernel.Ew.i64 Int64.minValue.toUInt64 y.toUInt64).toInt64) :=
  mon_rel (neg_spec_long_foR ha hn hv)

/-- **`seed <': x` at `long` on a dense column is its List spec** `zip(x, seed :: x).mapM (<)`:
    `prior_spec_long`'s prior operand, then `dyadColumn_long_vv_cmp` and `toList_cmp_long`. -/
theorem priorCmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {a : ByteArray} (ha : x.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [atomBits_long] at hv
  simp only at hv
  rw [ha, shiftColumn_long_bytes _ (Arr.n_long_bytes x ha)] at hv
  simp only at hv
  have hrun := Verify.run_cmp ({ inputs := #[a, Kernel.shiftBytes 8 s.toUInt64 1 a] } : Kernel.Ew.Build) rfl op
    Kernel.Ew.i64 Kernel.Ew.vv 0 1 0 (by decide) (by decide) n.toUSize
  simp only [show (#[a, Kernel.shiftBytes 8 s.toUInt64 1 a] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, Kernel.shiftBytes 8 s.toUInt64 1 a] : Array ByteArray)[(1 : UInt8).toNat]! =
      Kernel.shiftBytes 8 s.toUInt64 1 a from rfl] at hrun
  exact priorCmp_spec_words (B := Kernel.shiftBytes 8 s.toUInt64 1 a) hop h hn (by simp only [longWords, ha])
    (Arr.n_long_bytes x ha) rfl
    (by rw [dyad_enc (dyadColumn_long_vv_cmp hop hr n a _) hv, ← hrun]; simp [Kernel.payload])

/-- `seed <': x = ⟨x, prev⟩ ≫ (<)` from the kernel: `prior_rel` of `priorCmp_spec_long`. Dense long column. -/
theorem priorCmp_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {a : ByteArray} (ha : x.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (priorCmp_spec_long hop h ha hn hv)

/-- **`seed <': x` at `long` on a `foR` column is its List spec**: `prior_spec_long_foR`'s prior operand, the
    comparison bitmap of `bits_Fb` or `foRCmpVV`, read by `priorCmp_spec_words`. -/
theorem priorCmp_spec_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [atomBits_long] at hv
  simp only at hv
  rw [ha] at hv
  obtain ⟨hx, hxs⟩ := longWords_of_foR ha hn
  have hF := Verify.shiftFoR_spec 8 (by decide) (by decide) md pk n.toUSize 1 s.toUInt64
  rcases shiftColumn_long_foR n md pk s.toUInt64 (by omega) with hs | hs <;> rw [hs] at hv <;> simp only at hv
  · exact priorCmp_spec_words hop h hn hx hxs rfl
      (bits_Fb (dyad_enc (dyadColumn_long_vv_cmp_mixed hop hr n _ md pk).2 hv))
  · rcases Verify.answer_foR .long 8 n (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 s.toUInt64).1
      (Kernel.shiftFoR (8 : Nat).toUSize md pk n.toUSize 1 s.toUInt64).2 rfl with e | e <;> rw [e] at hv
    · exact priorCmp_spec_words hop h hn hx hxs hF
        (by rw [dyad_enc (dyadColumn_long_vv_cmp_foR hop hr n md pk _ _) hv]; rfl)
    · exact priorCmp_spec_words hop h hn hx hxs hF
        (bits_Fb (dyad_enc (dyadColumn_long_vv_cmp_mixed hop hr n _ md pk).2 hv))

/-- `seed <': x = ⟨x, prev⟩ ≫ (<)` from the kernel: `prior_rel` of `priorCmp_spec_long_foR`. `foR` column. -/
theorem priorCmp_rel_long_foR {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {md pk : ByteArray} (ha : x.enc = .foR md pk) (hn : n < USize.size)
    (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (priorCmp_spec_long_foR hop h ha hn hv)

/-- **`&x` on dense long counts is `whereCountsSpec`**: `expandBytes_spec` repeats `til n`'s element `i`
    `x[i]` times (a negative count none, as the spec's `toNat`), and `tilLongs_spec` reads element `i` as `i`.
    The kernel's refusal of a negative count only narrows when it answers. -/
theorem whereCounts_toList {nx : Nat} {x : Arr .long nx} {b : ByteArray} {nr : Nat} {r : Arr .long nr}
    (hb : x.enc = .bytes b) (hn : nx < USize.size) (h : Find.whereCounts x = .ok ⟨nr, r⟩) :
    r.toList = Find.whereCountsSpec x.toList := by
  simp only [Find.whereCounts, Find.dense, hb, Enc.bytesOf, bind, Except.bind] at h
  split at h
  · cases h
  obtain ⟨hnr, hr⟩ := Find.list_enc h
  subst hnr
  have hw : longWords ((Find.expand b).1.size / 8) r.enc = some (Verify.elemsW 8 (Find.expand b).1) := by rw [hr]; rfl
  have hsz : b.size / 8 = nx := by have := Arr.n_long_bytes x hb; omega
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have he := Verify.expandBytes_spec 8 (by rw [h8]; decide) (by rw [h8]; decide) 0 (by rw [h8]; decide)
    (Kernel.tilLongs (b.size / 8).toUSize) b
  rw [h8] at he
  have hl : (Verify.elemsW 8 (Kernel.tilLongs nx.toUSize)).length = nx := by
    have := congrArg List.length (Verify.tilLongs_spec nx.toUSize)
    simpa [USize.toNat_ofNat_of_lt' hn] using this
  have ht : ∀ i < nx, ((Verify.elemsW 8 (Kernel.tilLongs nx.toUSize)).getD i 0).toInt64 = Int64.ofNat i :=
    fun i hi => toInt64_of_toNat <| by
      have hi' : i < (Verify.elemsW 8 (Kernel.tilLongs nx.toUSize)).length := by rw [hl]; exact hi
      have e := congrArg (fun l => l[i]?) (Verify.tilLongs_spec nx.toUSize)
      simp only [USize.toNat_ofNat_of_lt' hn, List.getElem?_map, List.getElem?_range hi,
        List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at e
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some, e]
  rw [Arr.toList_long r hw, Arr.toList_long_bytes x hb]
  unfold Find.expand Find.whereCountsSpec
  simp only
  rw [he, hsz, List.map_flatMap, List.length_map, List.length_map, List.length_range]
  simp only [List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
  have hi : i < nx := List.mem_range.1 hi
  rw [List.map_replicate, ht i hi]
  simp [List.getD_eq_getElem?_getD, hi]

/-- Position `j` of `i` repeated `f i` times, `i < n`, is the group `i` whose segment `[c i, c (i+1))` holds
    `j`, counted as the cuts `c (r+1) ≤ j`; `c` the exclusive prefix sums of `f`. -/
theorem flatMap_replicate_getElem? (f c : Nat → Nat) (h0 : c 0 = 0) (hs : ∀ i, c (i+1) = c i + f i) :
    ∀ n j a, ((List.range n).flatMap fun i => List.replicate (f i) i)[j]? = some a ↔
      j < c n ∧ a = (List.range n).countP fun r => c (r+1) ≤ j := by
  have hm : ∀ {a b}, a ≤ b → c a ≤ c b := fun h => by
    induction h with
    | refl => exact Nat.le_refl _
    | step _ ih => rw [hs]; omega
  have hl : ∀ n, ((List.range n).flatMap fun i => List.replicate (f i) i).length = c n := fun n => by
    induction n with
    | zero => simp [h0]
    | succ n ih => simp [List.range_succ, List.flatMap_append, ih, hs]
  intro n
  induction n with
  | zero => intro j a; simp [h0]
  | succ n ih =>
    intro j a
    have hn : c n ≤ c (n+1) := hm (Nat.le_succ n)
    rw [List.range_succ, List.flatMap_append, List.countP_append, List.getElem?_append, hl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_cons, List.countP_nil]
    by_cases hj : j < c n
    · rw [if_pos hj, ih]
      have : ¬ c (n+1) ≤ j := by omega
      simp [this, hj, show j < c (n+1) by omega]
    · rw [if_neg hj, List.getElem?_replicate]
      have hall : ((List.range n).countP fun r => c (r+1) ≤ j) = n := by
        have e := (List.countP_eq_length (p := fun r => decide (c (r+1) ≤ j)) (l := List.range n)).2
          fun r hr => by have := hm (show r+1 ≤ n from List.mem_range.1 hr); simp only [decide_eq_true_eq]; omega
        rwa [List.length_range] at e
      rw [hall, hs n]
      by_cases hk : j < c n + f n
      · simp [show j - c n < f n by omega, hk, show ¬ c n + f n ≤ j by omega, eq_comm]
      · simp [show ¬ j - c n < f n by omega, hk]

/-- The offsets of `&x` on counts, `0, +\(0|x)`: the exclusive prefix sums, a negative count read as `0`. -/
def whereOffsets (ns : List Int64) (i : Nat) : Nat := ((List.range i).map fun k => (ns.getD k 0).toInt.toNat).sum

/-- **`&x` on counts `= corefl(< Σ(0|x)) ≫ grp(o)`**, the group read as a long: output position `j` goes to
    the input position whose segment holds it, the segments cut at `o = 0, +\(0|x)` (as `cut` reads them).
    Stated for every dense long `o` holding the offsets; `whereCounts_toList` and `flatMap_replicate_getElem?`. -/
theorem whereCounts_rel {nx : Nat} {x : Arr .long nx} {b : ByteArray} {nr : Nat} {r : Arr .long nr}
    (hb : x.enc = .bytes b) (hn : nx < USize.size) (h : Find.whereCounts x = .ok ⟨nr, r⟩)
    (o : Arr .long (nx+1)) (ho : ∀ i : Fin (nx+1), (o.get i).toInt = whereOffsets x.toList i) :
    r.rel = corefl (· < whereOffsets x.toList nx) ≫ grp o ≫ graph Int64.ofNat := by
  let f := fun k => (x.toList.getD k 0).toInt.toNat
  have hs : ∀ i, whereOffsets x.toList (i+1) = whereOffsets x.toList i + f i := fun i => by
    simp [whereOffsets, List.range_succ, f]
  have hgrp : ∀ j, Parted.group o j = (List.range nx).countP fun r => whereOffsets x.toList (r+1) ≤ j := fun j => by
    unfold Parted.group
    rw [show List.range nx = (List.finRange nx).map Fin.val from List.ext_getElem (by simp) (fun _ _ _ => by simp),
      List.countP_map]
    congr 1; funext r
    simp [Function.comp, ho r.succ]
  have key : ∀ j a, ((List.range nx).flatMap fun i => List.replicate (f i) i)[j]? = some a ↔
      j < whereOffsets x.toList nx ∧ a = Parted.group o j := fun j a =>
    (flatMap_replicate_getElem? f (whereOffsets x.toList) rfl hs nx j a).trans (by rw [hgrp j])
  have hr : r.rel = ix (((List.range nx).flatMap fun i => List.replicate (f i) i).map Int64.ofNat) := by
    show ix r.toList = _
    rw [whereCounts_toList hb hn h]
    unfold Find.whereCountsSpec
    rw [Arr.length_toList]
    simp [List.map_flatMap, List.map_replicate, f]
  rw [hr, ix_map]
  refine hom_ext fun j c => ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨hj, rfl⟩ := (key j a).1 ha
    exact ⟨j, ⟨rfl, hj⟩, _, rfl, rfl⟩
  · rintro ⟨_, ⟨rfl, hj⟩, _, rfl, rfl⟩
    exact ⟨_, (key j _).2 ⟨hj, rfl⟩, rfl⟩

-- The value laws `atomDict_rel`/`dictAtom_rel` take, filled by the encoding's own law.
example {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op) (h : Eval.ewType v .long .long = some .long)
    {k : Int64} {x : Rel .symbol .long} {R : Rel .symbol .long} {b : ByteArray} (hb : x.val.enc = .bytes b)
    (hn : x.n < USize.size) (hv : Ew.keyed x (Ew.atomVal v .long (t := .long) k · (by decide)) = .ok R) :=
  atomDict_rel (by decide) h hv fun _ hV => atomVal_spec_long hop h hb hn hV

example {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op) (h : Eval.ewType v .long .long = some .long)
    {k : Int64} {x : Rel .symbol .long} {R : Rel .symbol .long} {md pk : ByteArray} (ha : x.val.enc = .foR md pk)
    (hn : x.n < USize.size) (hv : Ew.keyed x (Ew.valAtom v .long (u := .long) · k (by decide)) = .ok R) :=
  dictAtom_rel (by decide) h hv fun _ hV => valAtom_spec_long_foR hop h ha hn hV

end Kernel

/-- `?x = enum(F) ≫ x`, `F = ran(Λ(x°) ≫ est(≤))` the first position of each value: every list
    `enum` relates `F` to gives the answer, and there is one. Restrictions as `distinct_toList`'s:
    long columns. -/
theorem distinct_rel {nx : Nat} {x : Arr .long nx} {nr : Nat} {r : Arr .long nr} {xs : List UInt64}
    (hx : longWords nx x.enc = some xs) (hu : x.attrCell.map (·.1) = some 2 → x.toList.Nodup)
    (hn8 : 8 * nx < USize.size) (h : Find.distinct x = .ok ⟨nr, r⟩) :
    (∃ ys, enum (cset (ran (Λ (x.rel°) ≫ est (· ≤ ·)))) ys) ∧
    ∀ ys, enum (cset (ran (Λ (x.rel°) ≫ est (· ≤ ·)))) ys → r.rel = ix (CL.toList ys) ≫ x.rel := by
  have hS : ∀ j, cset (ran (Λ (x.rel°) ≫ est (· ≤ ·))) j ↔
      j ∈ Verify.firstsOf (fun i => x.toList[i]!) x.toList.length := fun j =>
    ⟨fun ⟨_, a, h1, _⟩ => (least_iff_firsts _ j).1 ⟨a, (Λ_comp_est_apply _ _ a j).1 h1⟩,
     fun hj => let ⟨a, ha⟩ := (least_iff_firsts _ j).2 hj
       ⟨rfl, a, (Λ_comp_est_apply _ _ a j).2 ha, (Λ_comp_est_apply _ _ a j).2 ha⟩⟩
  have hP : (Verify.firstsOf (fun i => x.toList[i]!) x.toList.length).Pairwise (· < ·) :=
    (List.pairwise_lt_range ..).filter _
  have hlt : ∀ j ∈ Verify.firstsOf (fun i => x.toList[i]!) x.toList.length, j < x.toList.length :=
    fun j hj => List.mem_range.1 (List.mem_filter.1 hj).1
  have he := enum_ofList _ _ hP fun j => (hS j).symm
  refine ⟨⟨_, (he _).2 rfl⟩, fun ys hy => ?_⟩
  have hys : CL.toList ys = Verify.firstsOf (fun i => x.toList[i]!) x.toList.length := by
    rw [(he ys).1 hy, CL.toList_ofList]
  calc r.rel = ix (Find.distinctSpec x.toList) := congrArg ix (Find.distinct_toList hx hu hn8 h)
    _ = ix ((Verify.firstsOf (fun i => x.toList[i]!) x.toList.length).map fun i => x.toList[i]!) :=
        congrArg ix (eraseDups_firsts _)
    _ = ix (Verify.firstsOf (fun i => x.toList[i]!) x.toList.length) ≫ x.rel := ix_map_getElem! _ _ hlt
    _ = ix (CL.toList ys) ≫ x.rel := by rw [hys]

/-! ## §11.2 Search: the List spec read as the expression -/

/-- `x in y = x ≫ χ(ran y)`. Restrictions as `in_toList`'s. -/
theorem in_rel {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny} {r : Arr .boolean nx}
    (hx : Find.Readable a nx x.enc) (hy : Find.Readable a ny y.enc) (hs : Find.Ascends y)
    (hn8 : 8 * ny < USize.size) (hm : nx < USize.size) (h : Find.«in» x y = .ok r) :
    r.rel = x.rel ≫ χ (ran y.rel) :=
  calc r.rel = ix (Find.inSpec x.toList y.toList) := congrArg ix (Find.in_toList hx hy hs hn8 hm h)
    _ = x.rel ≫ graph (fun v => y.toList.contains v) := ix_map ..
    _ = x.rel ≫ χ (ran y.rel) := congrArg (x.rel ≫ ·) (ix_contains _)

/-- `x?y = y ≫ miss(Λ(x°) ≫ est(≤), n)`, the position read as a long. Restrictions as `find_toList`'s. -/
theorem find_rel {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny} {r : Arr .long ny}
    (hx : Find.Readable a nx x.enc) (hy : Find.Readable a ny y.enc) (hs : Find.Ascends x)
    (hn8 : 8 * nx < USize.size) (hm : ny < USize.size) (h : Find.find x y = .ok r) :
    r.rel = y.rel ≫ miss (Λ (x.rel°) ≫ est (· ≤ ·)) nx ≫ graph Int64.ofNat :=
  calc r.rel = ix (Find.findSpec x.toList y.toList) := congrArg ix (Find.find_toList hx hy hs hn8 hm h)
    _ = y.rel ≫ graph (fun v => Int64.ofNat (x.toList.idxOf v)) := ix_map ..
    _ = y.rel ≫ graph (fun v => x.toList.idxOf v) ≫ graph Int64.ofNat := congrArg (y.rel ≫ ·) (graph_comp ..).symm
    _ = y.rel ≫ miss (Λ (x.rel°) ≫ est (· ≤ ·)) x.toList.length ≫ graph Int64.ofNat :=
        congrArg (fun R => y.rel ≫ R ≫ graph Int64.ofNat) (ix_idxOf _)
    _ = y.rel ≫ miss (Λ (x.rel°) ≫ est (· ≤ ·)) nx ≫ graph Int64.ofNat := by rw [Arr.length_toList]

/-- `x bin y = y ≫ miss(Λ((≥) ≫ x°) ≫ est(≥), −1)`, the position read as a long. Restrictions as
    `bin_toList`'s: long columns, `x` ascending. -/
theorem bin_rel {nx : Nat} {x : Arr .long nx} {ny : Nat} {y : Arr .long ny} {r : Arr .long ny}
    (hx : Find.Readable .long nx x.enc) (hy : Find.Readable .long ny y.enc) (hn : nx < USize.size) (hm : ny < USize.size)
    (hsort : ∀ i j : Fin nx, i ≤ j → x.get i ≤ x.get j) (h : Find.bin x y = .ok r) :
    r.rel = y.rel ≫ miss ((Λ ((· ≥ ·) ≫ x.rel°) ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) (-1) :=
  have hp : x.toList.Pairwise (· ≤ ·) := List.pairwise_iff_getElem.2 fun i j hi hj hij => by
    rw [Arr.getElem_toList, Arr.getElem_toList]
    exact hsort _ _ (Nat.le_of_lt hij)
  calc r.rel = ix (Find.binSpec x.toList y.toList) := congrArg ix (Find.bin_toList hx hy hn hm hsort h)
    _ = y.rel ≫ graph (fun v => Int64.ofNat (x.toList.countP (· ≤ v)) - 1) := ix_map ..
    _ = y.rel ≫ miss ((Λ ((· ≥ ·) ≫ x.rel°) ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) (-1) :=
        congrArg (y.rel ≫ ·) (ix_bin _ hp)

/-- `&x = enum(dom(x ≫ 1b°))` on booleans, the positions read as longs: every list `enum` relates
    the set to is the answer, and there is one. -/
theorem where_rel {nx : Nat} {x : Arr .boolean nx} {nr : Nat} {r : Arr .long nr}
    (hn : nx < USize.size) (h : Find.«where» x = .ok ⟨nr, r⟩) :
    (∃ ys, enum (cset (dom (x.rel ≫ (cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys) ∧
    ∀ ys, enum (cset (dom (x.rel ≫ (cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°))) ys →
      r.rel = ix (CL.toList ys) ≫ graph Int64.ofNat := by
  obtain ⟨L, hL, he⟩ := enum_where hn h
  have hS : cset (dom (x.rel ≫ (cst true : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨El .boolean⟩)°)) = fun i => x.rel i true :=
    funext fun i => propext ⟨fun ⟨_, _, ⟨b, hb, (e : b = true)⟩, _⟩ => e ▸ hb, fun hi => ⟨rfl, (), ⟨true, hi, rfl⟩, ⟨true, hi, rfl⟩⟩⟩
  rw [hS]
  refine ⟨⟨_, (he _).2 rfl⟩, fun ys hy => ?_⟩
  obtain rfl := (he ys).1 hy
  calc r.rel = ix (L.map Int64.ofNat) := congrArg ix hL
    _ = ix L ≫ graph Int64.ofNat := ix_map ..
    _ = ix (CL.toList (CL.ofList L)) ≫ graph Int64.ofNat := by rw [CL.toList_ofList]

#print axioms in_rel
#print axioms find_rel
#print axioms bin_rel
#print axioms where_rel
#print axioms distinct_rel
#print axioms mon_rel
#print axioms val_rel
#print axioms atomVal_rel
#print axioms valAtom_rel
#print axioms prior_rel
#print axioms val_spec_long
#print axioms cmp_spec_long
#print axioms val_rel_long
#print axioms cmp_rel_long
#print axioms neg_spec_long
#print axioms neg_rel_long
#print axioms atomVal_spec_long
#print axioms atomVal_rel_long
#print axioms valAtom_spec_long
#print axioms valAtom_rel_long
#print axioms intStep_comm
#print axioms prior_spec_long
#print axioms prior_rel_long
#print axioms whereCounts_toList
#print axioms flatMap_replicate_getElem?
#print axioms whereCounts_rel
#print axioms cmpStep_flip
#print axioms elem_cmp_flip
#print axioms toList_cmp_long
#print axioms elem_atomBytes_long
#print axioms dyadColumn_long_av_cmp
#print axioms atomCmp_spec_long
#print axioms atomCmp_rel_long
#print axioms cmpAtom_spec_long
#print axioms cmpAtom_rel_long
#print axioms priorCmp_spec_long
#print axioms priorCmp_rel_long
#print axioms dyad_enc
#print axioms longWords_of_foR
#print axioms longWords_answer_foR
#print axioms val_spec_words
#print axioms cmp_spec_words
#print axioms dyadColumn_long_vv_foR
#print axioms dyadColumn_long_vv_cmp_foR
#print axioms val_rel_long_foR
#print axioms cmp_rel_long_foR

#print axioms intStep_sub_neg
#print axioms cmpStep_cmpFlip
#print axioms mapM_spec_words
#print axioms foRValAtom_long
#print axioms atomVal_rel_long_foR
#print axioms valAtom_rel_long_foR
#print axioms atomCmp_rel_long_foR
#print axioms cmpAtom_rel_long_foR
#print axioms neg_rel_long_foR

#print axioms prog_two
#print axioms run_val_decode
#print axioms run_cmp_decode
#print axioms dyadColumn_long_vv_mixed
#print axioms dyadColumn_long_vv_cmp_mixed
#print axioms longWords_run_val
#print axioms longWords_Fb
#print axioms longWords_val_foR
#print axioms val_rel_long_bF
#print axioms val_rel_long_Fb
#print axioms cmp_rel_long_bF
#print axioms cmp_rel_long_Fb
#print axioms atomBits_long
#print axioms prior_spec_words
#print axioms shiftColumn_long_foR
#print axioms prior_rel_long_foR
#print axioms val_rel_long
#print axioms cmp_rel_long
#print axioms prior_rel_long

#print axioms shift_words
#print axioms toList_cmp_bits
#print axioms bits_Fb
#print axioms priorCmp_spec_words
#print axioms priorCmp_rel_long
#print axioms priorCmp_rel_long_foR
#print axioms mon_enc
#print axioms map_spec_words
#print axioms neg_rel_long
#print axioms lift_v
#print axioms align_match
#print axioms dyadic_match
#print axioms dyadic_rel
#print axioms keyed_ok
#print axioms miss_comp
#print axioms atomDict_rel
#print axioms dictAtom_rel
#print axioms gatherFill_long
#print axioms bind_ok
#print axioms align_gather
#print axioms ix_lookup
#print axioms align_left_rel
#print axioms gatherColumn_long
#print axioms enum_ofList
#print axioms cset_only

/-- `Ew.vec` answers only on a vector, whose count and payload it passes on. -/
theorem vec_some {w : String} {o : Option QValue} {p : Nat × Enc} (h : Ew.vec w o = .ok p) :
    ∃ t a, o = some (.vector t p.1 p.2 a) := by
  unfold Ew.vec at h; split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

#print axioms vec_some
#print axioms only_rows
#print axioms gather_rel
#print axioms align_right_rel
#print axioms align_rel
#print axioms moveFoR_words
#print axioms appendFoR_words
#print axioms encode_words
#print axioms foRExc_congr
#print axioms lowBytes8
#print axioms decode_words
#print axioms fixed_parts
#print axioms alp_fixed
#print axioms width_fixed
#print axioms raze_fixed
#print axioms concatFoR_words
#print axioms raze_answer
#print axioms razeColumn_words
#print axioms toList_fixed
#print axioms alp_parts
#print axioms alp_width
#print axioms alpDecode_words
#print axioms alpFlag
#print axioms raze_dense
#print axioms raze_alp
#print axioms bytesOf_answer_alp
#print axioms concatALP_pair
#print axioms raze_alp_answer
#print axioms razeColumn_alp
#print axioms toList_words
#print axioms raze_toList_fixed
#print axioms bits_arr
#print axioms get_bits
#print axioms concatBits_at
#print axioms raze_toList_bits
#print axioms raze_toList

end LeetQ.Rel.Verb
