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

end LeetQ.Rel.Verb
