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
    longWords (Kernel.payload .long n.toUSize (bld, last)) = some (Verify.elemsW 8 (bld.run last n.toUSize)) := by
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hp : Kernel.payload .long n.toUSize (bld, last) = Column.answer ⟨.long, n,
      .foR (bld.runEnc last n.toUSize (8 : Nat).toUSize).1 (bld.runEnc last n.toUSize (8 : Nat).toUSize).2, none⟩ := by
    simp only [Kernel.payload, hN]; rfl
  rw [hp]
  rcases Verify.answer_foR .long 8 n _ _ rfl (a := none) with e | e <;> rw [e] <;> unfold longWords
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
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (a b : ByteArray)
    (pa pb : Option (UInt8 × IndexCell)) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long ⟨.long, n, .bytes a, pa⟩ ⟨.long, n, .bytes b, pb⟩ =
      some (.long, Kernel.payload .long n.toUSize ({ inputs := #[a, b] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va)]

/-- **`Ew.val` at `long` on dense columns is `ValSpec`**: one `dyadColumn` call, `run_val`, `val_i64_vv`,
    and q's element `Ew.elem_long_val`. -/
theorem val_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a b : ByteArray}
    (ha : x.c.enc = .bytes a) (hb : yv.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  have hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[a, b] },
      { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1,
        nul := Kernel.nullPayload .long }) := by
    unfold Ew.val Ew.dyad at hv
    rw [Arr.c_eq x ha, Arr.c_eq yv hb, dyadColumn_long_vv hop hr] at hv
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hrun := Verify.run_val ({ inputs := #[a, b] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 Kernel.Ew.vv 0 1
    (Kernel.nullPayload .long) (by decide) (by decide) n.toUSize
  simp only [show (#[a, b] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, b] : Array ByteArray)[(1 : UInt8).toNat]! = b from rfl] at hrun
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hs : (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv (Kernel.nullPayload .long) a b n.toUSize).size / 8 = n := by
    rw [← Verify.val_size8, hN]
  rw [← hrun] at hs
  have hw := longWords_payload _ _ hn hs
  rw [← hR, hrun, Verify.val_i64_vv _ _ _ _ _ hn, nullPayload_long] at hw
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.intStep op Int64.minValue p.1 p.2) := funext fun p => Ew.elem_long_val hop h p.1 p.2
  have hRl : R.toList = (List.range n).map fun i => Kernel.Ew.intStep op Int64.minValue
      (Column.bitsAt a (i * 8) 8).toInt64 (Column.bitsAt b (i * 8) 8).toInt64 := by
    rw [Arr.toList_long R hw]; simp
  unfold Ew.ValSpec
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure, hRl,
    Arr.toList_long_bytes x ha, Arr.toList_long_bytes yv hb]
  exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by simp)

/-- `dyadColumn` on two dense long columns of one count, at a comparison: the one-stage `eCmp` chain over
    the two payloads, answered as a bitmap. -/
theorem dyadColumn_long_vv_cmp {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (a b : ByteArray)
    (pa pb : Option (UInt8 × IndexCell)) :
    Kernel.dyadColumn v Kernel.Ew.vv .long .long ⟨.long, n, .bytes a, pa⟩ ⟨.long, n, .bytes b, pb⟩ =
      some (.boolean, Kernel.payload .boolean n.toUSize ({ inputs := #[a, b] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1, nul := 0 })) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource, Kernel.Ew.Build.input,
    Kernel.Ew.i64, Kernel.Ew.bits, (by decide : ¬Kernel.Ew.vv = Kernel.Ew.va)]

/-- **A comparison at `long` on dense columns is `ValSpec`**: one `dyadColumn` call, `run_cmp`, `cmp_bitAt`,
    and q's element `Ew.elem_long_cmp`. -/
theorem cmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a b : ByteArray} (ha : x.c.enc = .bytes a) (hb : yv.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) : Ew.ValSpec v h x yv R := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  have hR : R.c = Kernel.payload .boolean n.toUSize ({ inputs := #[a, b] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1, nul := 0 }) := by
    unfold Ew.val Ew.dyad at hv
    rw [Arr.c_eq x ha, Arr.c_eq yv hb, dyadColumn_long_vv_cmp hop hr] at hv
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hrun := Verify.run_cmp ({ inputs := #[a, b] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 Kernel.Ew.vv 0 1 0
    (by decide) (by decide) n.toUSize
  simp only [show (#[a, b] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl,
    show (#[a, b] : Array ByteArray)[(1 : UInt8).toNat]! = b from rfl] at hrun
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hc : R.c.enc = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 Kernel.Ew.vv a b n.toUSize) := by
    rw [hR, ← hrun]; simp [Kernel.payload]
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 p.1.toUInt64 p.2.toUInt64) :=
    funext fun p => Ew.elem_long_cmp hop h p.1 p.2
  have hRl : R.toList = (List.range n).map fun i => Kernel.Ew.cmpStep op Kernel.Ew.i64
      (Kernel.Ew.elem Kernel.Ew.i64 a i) (Kernel.Ew.elem Kernel.Ew.i64 b i) := by
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2
    have hi : i < n := by simpa using h2
    rw [Arr.getElem_toList, Arr.get_bool_bits R hc, (Verify.cmp_bitAt _ _ _ _ _ _).2 i (by rw [hN]; omega)]
    simp [hN, hi, Kernel.Ew.shapeIdx, Kernel.Ew.vv, Kernel.Ew.va, Kernel.Ew.av]
  unfold Ew.ValSpec
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure, hRl,
    Arr.toList_long_bytes x ha, Arr.toList_long_bytes yv hb]
  exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by
    simp [Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32,
      Kernel.Ew.f32])

/-- `x+y = ⟨x, y⟩ ≫ (+)` from the kernel: `val_rel` of `val_spec_long`. Dense long columns. -/
theorem val_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {x yv R : Arr .long n} {a b : ByteArray}
    (ha : x.c.enc = .bytes a) (hb : yv.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .long x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (val_spec_long hop h ha hb hn hv)

/-- `x<y = ⟨x, y⟩ ≫ (<)` from the kernel: `val_rel` of `cmp_spec_long`. Dense long columns. -/
theorem cmp_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {x yv : Arr .long n} {R : Arr .boolean n}
    {a b : ByteArray} (ha : x.c.enc = .bytes a) (hb : yv.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.val v .boolean x yv = .ok R) :
    R.rel = rpair x.rel yv.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  val_rel (cmp_spec_long hop h ha hb hn hv)

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
theorem monColumn_neg_long (n : Nat) (a : ByteArray) (pa : Option (UInt8 × IndexCell)) :
    Kernel.monColumn "neg" .long ⟨.long, n, .bytes a, pa⟩ = some (.long, Kernel.payload .long n.toUSize
      ({ inputs := #[a] },
        { engine := Kernel.Ew.eMon, op := Kernel.Ew.neg, cls := Kernel.Ew.i64, a := 0, nul := Kernel.nullPayload .long })) := by
  simp [Kernel.monColumn, Kernel.monResultType, Kernel.negType, Kernel.monPayload, Kernel.negAbsPayload,
    Kernel.mapPass, Kernel.operandSource, Kernel.clsOf, Kernel.Ew.Build.input, show Prim.nonNumeric .long = false by decide]

/-- **`-x` at `long` on a dense column is `MapSpec`** of `monStep`'s `neg`, which `Verify.negAtom_long`
    proves is q's `neg`: `0N` stays `0N`, everything else is `0 - x`. -/
theorem neg_spec_long {n : Nat} {x R : Arr .long n} {a : ByteArray} (ha : x.c.enc = .bytes a)
    (hn : n < USize.size) (hv : Ew.mon "neg" .long x = .ok R) :
    Ew.MapSpec (t := .long) (rt := .long) (fun y : Int64 =>
      (Kernel.Ew.monStep Kernel.Ew.neg Kernel.Ew.i64 Int64.minValue.toUInt64 y.toUInt64).toInt64) x R := by
  have hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[a] },
      { engine := Kernel.Ew.eMon, op := Kernel.Ew.neg, cls := Kernel.Ew.i64, a := 0, nul := Kernel.nullPayload .long }) := by
    unfold Ew.mon at hv
    rw [Arr.c_eq x ha, monColumn_neg_long] at hv
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hrun := run_mon ({ inputs := #[a] } : Kernel.Ew.Build) rfl Kernel.Ew.neg Kernel.Ew.i64 0
    (Kernel.nullPayload .long) (by decide) n.toUSize
  simp only [show (#[a] : Array ByteArray)[(0 : UInt8).toNat]! = a from rfl] at hrun
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hs : (Kernel.Ew.mon Kernel.Ew.neg Kernel.Ew.i64 (Kernel.nullPayload .long) a n.toUSize).size / 8 = n := by
    have := congrArg List.length (mon_i64 Kernel.Ew.neg (Kernel.nullPayload .long) a n hn)
    simpa [Verify.elemsW] using this
  rw [← hrun] at hs
  have hw := longWords_payload _ _ hn hs
  rw [← hR, hrun, mon_i64 _ _ _ _ hn, nullPayload_long] at hw
  unfold Ew.MapSpec
  rw [Arr.toList_long R hw, Arr.toList_long_bytes x ha]
  simp

/-- `-x = x ≫ neg` from the kernel: `mon_rel` of `neg_spec_long`. Dense long column. -/
theorem neg_rel_long {n : Nat} {x R : Arr .long n} {a : ByteArray} (ha : x.c.enc = .bytes a)
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
      .ok ⟨.long, 1, .bytes (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64), none⟩ := by
  simp [Ew.atomCol, Column.ofAtoms, Carrier.atom, QAtom.type, Column.bitsOf, Kernel.atomBytes, Kernel.Ew.width,
    Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32, Kernel.Ew.f32] <;> rfl

/-- `dyadColumn` on a long atom column (left) and a dense long column, at a value verb: the one-stage
    `eVal` chain at `av`. The atom reaches the chain by `operandAt` when `n ≠ 1` and as a chain input
    when `n = 1`; both name its payload as input `0`. -/
theorem dyadColumn_long_av {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (c b : ByteArray)
    (pa pb : Option (UInt8 × IndexCell)) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long ⟨.long, 1, .bytes c, pa⟩ ⟨.long, n, .bytes b, pb⟩ =
      some (.long, Kernel.payload .long n.toUSize ({ inputs := #[c, b] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd hr (by decide) | skip
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Column.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va), *]

/-- A long answer of a one-stage `eVal` chain over two inputs is its `Ew.val` words read as longs:
    `run_val`, `val_size8`, `longWords_payload`. -/
theorem toList_val_long {op shape : UInt8} {n : Nat} {R : Arr .long n} (p q : ByteArray) (hn : n < USize.size)
    (hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[p, q] },
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
    (hb : x.c.enc = .bytes b) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  unfold Ew.atomVal Ew.dyad at hv
  rw [atomCol_long, Arr.c_eq x hb] at hv
  simp only [bind, Except.bind] at hv
  rw [dyadColumn_long_av hop hr] at hv
  have hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[Kernel.atomBytes Kernel.Ew.i64 k.toUInt64, b] },
      { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1,
        nul := Kernel.nullPayload .long }) := by
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hel : (fun y : Int64 => elem v h k y) =
      fun y => pure (Kernel.Ew.intStep op Int64.minValue k y) := funext fun y => Ew.elem_long_val hop h k y
  rw [show (fun y : Carrier .long => elem v h k y) = _ from hel, List.mapM_pure, toList_val_long _ _ hn hR,
    val_i64_av _ _ _ _ _ hn, nullPayload_long, Arr.toList_long_bytes x hb]
  exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by simp)

/-- `a+x = ⟨!a, x⟩ ≫ (+)` from the kernel: `atomVal_rel` of `atomVal_spec_long`. Dense long column. -/
theorem atomVal_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.c.enc = .bytes b) (hn : n < USize.size) (hv : Ew.atomVal v .long (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomVal_spec_long hop h hb hn hv)

/-- `dyadColumn` on a dense long column and a long atom column (right), at a value verb other than `^`
    (q's `x^atom` is `'nyi`): the one-stage `eVal` chain at `va`. -/
theorem dyadColumn_long_va {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op) (hf : v ≠ .fill)
    (hr : Kernel.resultType v .long .long = some .long) (n : Nat) (b c : ByteArray)
    (pb pa : Option (UInt8 × IndexCell)) :
    Kernel.dyadColumn v Kernel.Ew.va .long .long ⟨.long, n, .bytes b, pb⟩ ⟨.long, 1, .bytes c, pa⟩ =
      some (.long, Kernel.payload .long n.toUSize ({ inputs := #[b, c] },
        { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.va, a := 0, b := 1,
          nul := Kernel.nullPayload .long })) := by
  cases v <;> simp only [Kernel.valOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals first | exact absurd rfl hf | exact absurd hr (by decide) | skip
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.valPayload, Kernel.cmpOp,
    Kernel.valOp, Kernel.clsOf, Kernel.scales, Kernel.tickIn, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible,
    Kernel.promotable, Kernel.foRValPayload, Kernel.foRPair, Kernel.foRPairVV, Kernel.zipPass, Kernel.operandSource,
    Kernel.operandAt, Column.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
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
    (hb : x.c.enc = .bytes b) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
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
    rw [atomCol_long, Arr.c_eq x hb] at hv
    simp only [bind, Except.bind] at hv)
  case fill => simp [Ew.dyad, Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.Ew.va] at hv
  case sub =>
    unfold Ew.dyad at hv
    rw [dyadColumn_long_va rfl (by decide) hr] at hv
    have hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[b, Kernel.atomBytes Kernel.Ew.i64 k.toUInt64] },
        { engine := Kernel.Ew.eVal, op := Kernel.Ew.sub, cls := Kernel.Ew.i64, shape := Kernel.Ew.va, a := 0, b := 1,
          nul := Kernel.nullPayload .long }) := by
      simp only [↓reduceIte] at hv
      unfold Arr.of at hv
      split at hv
      · cases hv; rfl
      · cases hv
    have hel : (fun y : Int64 => elem .sub h y k) =
        fun y => pure (Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue y k) :=
      funext fun y => Ew.elem_long_val rfl h y k
    rw [show (fun y : Carrier .long => elem .sub h y k) = _ from hel, List.mapM_pure, toList_val_long _ _ hn hR,
      Verify.val_i64_va _ _ _ _ _ hn, nullPayload_long, Arr.toList_long_bytes x hb]
    exact congrArg Except.ok (List.ext_getElem (by simp) fun i _ _ => by simp)

/-- `x+a = ⟨x, !a⟩ ≫ (+)` from the kernel: `valAtom_rel` of `valAtom_spec_long`. Dense long column. -/
theorem valAtom_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {k : Int64} {x R : Arr .long n} {b : ByteArray}
    (hb : x.c.enc = .bytes b) (hn : n < USize.size) (hv : Ew.valAtom v .long (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (valAtom_spec_long hop h hb hn hv)

/-- `shiftColumn` by one on a dense long column: the dense `shiftBytes`, `fill` first. -/
theorem shiftColumn_long_bytes (n : Nat) (a : ByteArray) (fill : UInt64) (p : Option (UInt8 × IndexCell)) :
    Kernel.shiftColumn .long 1 fill ⟨.long, n, .bytes a, p⟩ =
      some (.vector ⟨.long, n, .bytes (Kernel.shiftBytes 8 fill 1 a), none⟩) := by
  simp [Kernel.shiftColumn, Kernel.foRColumn, Kernel.denseWidth, Column.bytesOf, QAtomicType.width] <;> rfl

/-- **`seed f': x` at `long` on a dense column is its List spec** `zip(x, seed :: x).mapM f`: the seed's bits
    (`atomCol_long`, `bitsAt_pushBits8`), `shiftColumn_long_bytes` and `shiftBytes_one` for the prior operand,
    then `dyadColumn_long_vv`, `val_i64_vv` and q's element `Ew.elem_long_val`. -/
theorem prior_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {a : ByteArray}
    (ha : x.c.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .long := by
    cases v <;> first | rfl | exact absurd h (by decide) | exact absurd hop (by simp [Kernel.valOp])
  have hfill : Ew.atomBits .long ⟨.long, 1, .bytes (Kernel.atomBytes Kernel.Ew.i64 s.toUInt64), none⟩ =
      .ok s.toUInt64 := by
    simp only [Ew.atomBits, Column.bytesOf, QAtomicType.width]
    exact congrArg Except.ok (Verify.bitsAt_pushBits8 ByteArray.empty _)
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [hfill] at hv
  simp only at hv
  rw [Arr.c_eq x ha, shiftColumn_long_bytes] at hv
  simp only at hv
  unfold Ew.dyad at hv
  rw [dyadColumn_long_vv hop hr] at hv
  have hR : R.c = Kernel.payload .long n.toUSize ({ inputs := #[a, Kernel.shiftBytes 8 s.toUInt64 1 a] },
      { engine := Kernel.Ew.eVal, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1,
        nul := Kernel.nullPayload .long }) := by
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hsz : a.size / 8 = n := by have := Arr.n_long_bytes x ha; omega
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have he := Verify.shiftBytes_one 8 (by rw [h8]; decide) (by rw [h8]; decide) s.toUInt64 (by rw [h8]; exact UInt64.toNat_lt _) a
  rw [h8] at he
  have hsb : ∀ i < n, Column.bitsAt (Kernel.shiftBytes 8 s.toUInt64 1 a) (i * 8) 8 =
      (s.toUInt64 :: (List.range n).map fun i => Column.bitsAt a (i * 8) 8)[i]?.getD 0 := by
    intro i hi
    have e := congrArg (fun l => l[i]?.getD 0) he
    simp only [List.getElem?_dropLast, List.length_cons, Verify.elemsW, List.length_map, List.length_range, hsz,
      Nat.add_sub_cancel, if_pos hi] at e
    rw [← e]
    simp [Verify.elemsW, Verify.shiftBytes_size, hsz, hi]
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.intStep op Int64.minValue p.1 p.2) := funext fun p => Ew.elem_long_val hop h p.1 p.2
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    toList_val_long _ _ hn hR, Verify.val_i64_vv _ _ _ _ _ hn, nullPayload_long, Arr.toList_long_bytes x ha]
  refine congrArg Except.ok (List.ext_getElem (by simp) fun i h1 h2 => ?_)
  have hi : i < n := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, hsb i hi]
  cases i with
  | zero => simp
  | succ j => simp [Verify.elemsW, hsz, show j < n by omega]

/-- `seed f': x = ⟨x, prev⟩ ≫ f` from the kernel: `prior_rel` of `prior_spec_long`. Dense long column. -/
theorem prior_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (h : Eval.ewType v .long .long = some .long) {n : Nat} {s : Int64} {x R : Arr .long n} {a : ByteArray}
    (ha : x.c.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .long (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (prior_spec_long hop h ha hn hv)

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
    (hR : R.c = Kernel.payload .boolean n.toUSize ({ inputs := #[p, q] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape, a := 0, b := 1, nul := 0 })) :
    R.toList = (List.range n).map fun i => Kernel.Ew.cmpStep op Kernel.Ew.i64
      (Kernel.Ew.elem Kernel.Ew.i64 p (Kernel.Ew.shapeIdx shape i).1)
      (Kernel.Ew.elem Kernel.Ew.i64 q (Kernel.Ew.shapeIdx shape i).2) := by
  have hrun := Verify.run_cmp ({ inputs := #[p, q] } : Kernel.Ew.Build) rfl op Kernel.Ew.i64 shape 0 1 0
    (by decide) (by decide) n.toUSize
  simp only [show (#[p, q] : Array ByteArray)[(0 : UInt8).toNat]! = p from rfl,
    show (#[p, q] : Array ByteArray)[(1 : UInt8).toNat]! = q from rfl] at hrun
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hc : R.c.enc = .bits (Kernel.Ew.cmp op Kernel.Ew.i64 shape p q n.toUSize) := by
    rw [hR, ← hrun]; simp [Kernel.payload]
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 h2
  have hi : i < n := by simpa using h2
  rw [Arr.getElem_toList, Arr.get_bool_bits R hc, (Verify.cmp_bitAt _ _ _ _ _ _).2 i (by rw [hN]; omega)]
  simp [hN, hi]

/-- The long atom's one element, as the comparison engine reads it at index `0`. -/
theorem elem_atomBytes_long (k : Int64) :
    Kernel.Ew.elem Kernel.Ew.i64 (Kernel.atomBytes Kernel.Ew.i64 k.toUInt64) 0 = k.toUInt64 := by
  simp only [Kernel.Ew.elem, Nat.zero_mul]
  exact Verify.bitsAt_pushBits8 ByteArray.empty _

/-- `dyadColumn` on a long atom column (left) and a dense long column, at a comparison: the one-stage
    `eCmp` chain at `av`. -/
theorem dyadColumn_long_av_cmp {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (hr : Kernel.resultType v .long .long = some .boolean) (n : Nat) (c b : ByteArray)
    (pa pb : Option (UInt8 × IndexCell)) :
    Kernel.dyadColumn v Kernel.Ew.av .long .long ⟨.long, 1, .bytes c, pa⟩ ⟨.long, n, .bytes b, pb⟩ =
      some (.boolean, Kernel.payload .boolean n.toUSize ({ inputs := #[c, b] },
        { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1, nul := 0 })) := by
  cases v <;> simp only [Kernel.cmpOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop
  all_goals by_cases h1 : n = 1
  all_goals first | subst h1 | have h2 : 1 ≠ n := Ne.symm h1
  all_goals simp [Kernel.dyadColumn, hr, Kernel.dyadPayload, Kernel.dyadCount, Kernel.cmpPayload, Kernel.cmpOp,
    Kernel.clsOf, Kernel.ticksMeet, Kernel.tickAgrees, Kernel.convertible, Kernel.promotable, Kernel.foRCmpPayload,
    Kernel.alpCmpPayload, Kernel.foRPairVV, Kernel.foRPair, Kernel.zipPass, Kernel.operandSource, Kernel.operandAt,
    Column.bytesOf, Kernel.Ew.Build.input, Kernel.Ew.i64, Kernel.Ew.bits,
    (by decide : ¬Kernel.Ew.av = Kernel.Ew.vv), (by decide : ¬Kernel.Ew.av = Kernel.Ew.va), *]

/-- **`a<x` at `long` on a dense column is its List spec** `x.mapM (a < ·)`: `atomCol_long`,
    `dyadColumn_long_av_cmp`, `toList_cmp_long`, and q's element `Ew.elem_long_cmp`. -/
theorem atomCmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    x.toList.mapM (fun y => elem v h k y) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  unfold Ew.atomVal Ew.dyad at hv
  rw [atomCol_long, Arr.c_eq x hb] at hv
  simp only [bind, Except.bind] at hv
  rw [dyadColumn_long_av_cmp hop hr] at hv
  have hR : R.c = Kernel.payload .boolean n.toUSize ({ inputs := #[Kernel.atomBytes Kernel.Ew.i64 k.toUInt64, b] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.av, a := 0, b := 1, nul := 0 }) := by
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
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
    {b : ByteArray} (hb : x.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.atomVal v .boolean (t := .long) k x = .ok R) :
    R.rel = rpair (cst k) x.rel ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  atomVal_rel (atomCmp_spec_long hop h hb hn hv)

/-- **`x<a` at `long` on a dense column is its List spec** `x.mapM (· < a)`: `Ew.flip` sends every comparison
    to `atomVal` of the flipped one (`elem_cmp_flip`, `atomCmp_spec_long`). -/
theorem cmpAtom_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {k : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {b : ByteArray} (hb : x.c.enc = .bytes b) (hn : n < USize.size)
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
    {b : ByteArray} (hb : x.c.enc = .bytes b) (hn : n < USize.size)
    (hv : Ew.valAtom v .boolean (u := .long) x k = .ok R) :
    R.rel = rpair x.rel (cst k) ≫ ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  valAtom_rel (cmpAtom_spec_long hop h hb hn hv)

/-- **`seed <': x` at `long` on a dense column is its List spec** `zip(x, seed :: x).mapM (<)`:
    `prior_spec_long`'s prior operand, then `dyadColumn_long_vv_cmp` and `toList_cmp_long`. -/
theorem priorCmp_spec_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {a : ByteArray} (ha : x.c.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    (x.toList.zip (s :: x.toList)).mapM (fun p => elem v h p.1 p.2) = .ok R.toList := by
  have hr : Kernel.resultType v .long .long = some .boolean := by
    cases v <;> first | rfl | exact absurd hop (by simp [Kernel.cmpOp])
  have hfill : Ew.atomBits .long ⟨.long, 1, .bytes (Kernel.atomBytes Kernel.Ew.i64 s.toUInt64), none⟩ =
      .ok s.toUInt64 := by
    simp only [Ew.atomBits, Column.bytesOf, QAtomicType.width]
    exact congrArg Except.ok (Verify.bitsAt_pushBits8 ByteArray.empty _)
  unfold Ew.prior at hv
  rw [atomCol_long] at hv
  simp only [bind, Except.bind] at hv
  rw [hfill] at hv
  simp only at hv
  rw [Arr.c_eq x ha, shiftColumn_long_bytes] at hv
  simp only at hv
  unfold Ew.dyad at hv
  rw [dyadColumn_long_vv_cmp hop hr] at hv
  have hR : R.c = Kernel.payload .boolean n.toUSize ({ inputs := #[a, Kernel.shiftBytes 8 s.toUInt64 1 a] },
      { engine := Kernel.Ew.eCmp, op, cls := Kernel.Ew.i64, shape := Kernel.Ew.vv, a := 0, b := 1, nul := 0 }) := by
    simp only [↓reduceIte] at hv
    unfold Arr.of at hv
    split at hv
    · cases hv; rfl
    · cases hv
  have hsz : a.size / 8 = n := by have := Arr.n_long_bytes x ha; omega
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have he := Verify.shiftBytes_one 8 (by rw [h8]; decide) (by rw [h8]; decide) s.toUInt64 (by rw [h8]; exact UInt64.toNat_lt _) a
  rw [h8] at he
  have hsb : ∀ i < n, Column.bitsAt (Kernel.shiftBytes 8 s.toUInt64 1 a) (i * 8) 8 =
      (s.toUInt64 :: (List.range n).map fun i => Column.bitsAt a (i * 8) 8)[i]?.getD 0 := by
    intro i hi
    have e := congrArg (fun l => l[i]?.getD 0) he
    simp only [List.getElem?_dropLast, List.length_cons, Verify.elemsW, List.length_map, List.length_range, hsz,
      Nat.add_sub_cancel, if_pos hi] at e
    rw [← e]
    simp [Verify.elemsW, Verify.shiftBytes_size, hsz, hi]
  have hE : ∀ (c : ByteArray) j, Kernel.Ew.elem Kernel.Ew.i64 c j = Column.bitsAt c (j * 8) 8 := fun _ _ => by
    simp [Kernel.Ew.elem, Kernel.Ew.width, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.i32, Kernel.Ew.f32]
  have hs : ∀ i, Kernel.Ew.shapeIdx Kernel.Ew.vv i = (i, i) := fun i => by simp [Kernel.Ew.shapeIdx]
  have hel : (fun p : Int64 × Int64 => elem v h p.1 p.2) =
      fun p => pure (Kernel.Ew.cmpStep op Kernel.Ew.i64 p.1.toUInt64 p.2.toUInt64) :=
    funext fun p => Ew.elem_long_cmp hop h p.1 p.2
  rw [show (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) = _ from hel, List.mapM_pure,
    toList_cmp_long _ _ hn hR, Arr.toList_long_bytes x ha]
  refine congrArg Except.ok (List.ext_getElem (by simp) fun i h1 h2 => ?_)
  have hi : i < n := by simpa using h2
  simp only [List.getElem_map, List.getElem_range, hs, hE, hsb i hi]
  cases i with
  | zero => simp
  | succ j => simp [Verify.elemsW, hsz, show j < n by omega]

/-- `seed <': x = ⟨x, prev⟩ ≫ (<)` from the kernel: `prior_rel` of `priorCmp_spec_long`. Dense long column. -/
theorem priorCmp_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.cmpOp v = some op)
    (h : Eval.ewType v .long .long = some .boolean) {n : Nat} {s : Int64} {x : Arr .long n} {R : Arr .boolean n}
    {a : ByteArray} (ha : x.c.enc = .bytes a) (hn : n < USize.size) (hv : Ew.prior v .boolean (t := .long) s x = .ok R) :
    R.rel = rpair x.rel ((shift ≫ x.rel) ∪ (corNeg (dom shift) ≫ cst s)) ≫
      ofExcept (fun p : Carrier .long × Carrier .long => elem v h p.1 p.2) :=
  prior_rel (priorCmp_spec_long hop h ha hn hv)

/-- **`&x` on dense long counts is `whereCountsSpec`**: `expandBytes_spec` repeats `til n`'s element `i`
    `x[i]` times (a negative count none, as the spec's `toNat`), and `tilLongs_spec` reads element `i` as `i`.
    The kernel's refusal of a negative count only narrows when it answers. -/
theorem whereCounts_toList {nx : Nat} {x : Arr .long nx} {b : ByteArray} {nr : Nat} {r : Arr .long nr}
    (hb : x.c.enc = .bytes b) (hn : nx < USize.size) (h : Find.whereCounts x = .ok ⟨nr, r⟩) :
    r.toList = Find.whereCountsSpec x.toList := by
  simp only [Find.whereCounts, Find.dense, Arr.c_eq x hb, Column.bytesOf, bind, Except.bind] at h
  split at h
  · cases h
  have hr := Find.list_c h
  have hw : longWords r.c = some (Verify.elemsW 8 (Find.expand b).1) := by rw [hr]; rfl
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
    (hb : x.c.enc = .bytes b) (hn : nx < USize.size) (h : Find.whereCounts x = .ok ⟨nr, r⟩)
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

end Kernel

/-- `?x = enum(F) ≫ x`, `F = ran(Λ(x°) ≫ est(≤))` the first position of each value: every list
    `enum` relates `F` to gives the answer, and there is one. Restrictions as `distinct_toList`'s:
    long columns. -/
theorem distinct_rel {nx : Nat} {x : Arr .long nx} {nr : Nat} {r : Arr .long nr} {xs : List UInt64}
    (hx : longWords x.c = some xs) (hu : x.c.attr.map (·.1) = some 2 → x.toList.Nodup)
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
  refine ⟨⟨CL.ofList _, (enum_iff _ _).2 ⟨funext fun j => propext ((hS j).trans (inlistP_ofList j _).symm),
    (orderedP_ofList _ _).2 hP⟩⟩, fun ys hy => ?_⟩
  obtain ⟨hS', ho⟩ := (enum_iff _ _).1 hy
  have hys : CL.toList ys = Verify.firstsOf (fun i => x.toList[i]!) x.toList.length :=
    eq_of_pairwise_lt (by rw [← orderedP_ofList, ofList_toList]; exact ho) hP fun j => by
      rw [← inlistP_ofList, ofList_toList, ← hS']; exact hS j
  calc r.rel = ix (Find.distinctSpec x.toList) := congrArg ix (Find.distinct_toList hx hu hn8 h)
    _ = ix ((Verify.firstsOf (fun i => x.toList[i]!) x.toList.length).map fun i => x.toList[i]!) :=
        congrArg ix (eraseDups_firsts _)
    _ = ix (Verify.firstsOf (fun i => x.toList[i]!) x.toList.length) ≫ x.rel := ix_map_getElem! _ _ hlt
    _ = ix (CL.toList ys) ≫ x.rel := by rw [hys]

/-! ## §11.2 Search: the List spec read as the expression -/

/-- `x in y = x ≫ χ(ran y)`. Restrictions as `in_toList`'s. -/
theorem in_rel {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny} {r : Arr .boolean nx}
    (hx : Find.Readable a x.c) (hy : Find.Readable a y.c) (hs : Find.Ascends y)
    (hn8 : 8 * ny < USize.size) (hm : nx < USize.size) (h : Find.«in» x y = .ok r) :
    r.rel = x.rel ≫ χ (ran y.rel) :=
  calc r.rel = ix (Find.inSpec x.toList y.toList) := congrArg ix (Find.in_toList hx hy hs hn8 hm h)
    _ = x.rel ≫ graph (fun v => y.toList.contains v) := ix_map ..
    _ = x.rel ≫ χ (ran y.rel) := congrArg (x.rel ≫ ·) (ix_contains _)

/-- `x?y = y ≫ miss(Λ(x°) ≫ est(≤), n)`, the position read as a long. Restrictions as `find_toList`'s. -/
theorem find_rel {a : QAtomicType} [BEq (El a)] [LawfulBEq (El a)]
    {nx : Nat} {x : Arr a nx} {ny : Nat} {y : Arr a ny} {r : Arr .long ny}
    (hx : Find.Readable a x.c) (hy : Find.Readable a y.c) (hs : Find.Ascends x)
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
    (hx : Find.Readable .long x.c) (hy : Find.Readable .long y.c) (hn : nx < USize.size) (hm : ny < USize.size)
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

end LeetQ.Rel.Verb
