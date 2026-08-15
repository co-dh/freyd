/-
  RelInterp — an INTERPRETER THAT RUNS RELATION ALGEBRA (prototype).

  Question answered here: can we have an AST of allegory / relational-algebra terms plus an
  evaluator that COMPUTES them — and run LeetCode solutions in it?

  Three layers:

  1. **The executable model `FinRel`** — objects are finite cardinalities (`FinObj`, carrier
     `Fin card`), morphisms are `Bool`-valued matrices `Fin m → Fin n → Bool`.  This is the
     decidable, `#eval`-runnable counterpart of `Rel(Set)` (`AOP.A6_1_RelSet`, whose
     `Prop`-valued morphisms cannot be executed).  `FinRel` instantiates the SAME classes as
     the rest of the repo: `Allegory`, `DistributiveAllegory`, `DivisionAllegory`,
     `PowerAllegory` — all proven below, mathlib-free.

  2. **The term language `RE`** — a deep AST with primitive constructors
     atom / id / comp / conv / meet / join / bot / top / div / eps.
     Everything else in the Freyd/B&dM vocabulary is DERIVED syntax using the book definitions
     verbatim: `leftDiv S R = (R°/S°)°` (§2.312), `A R = R /ₛ ∋ = (R/∋) ∩ (∋/R)°`
     (§2.331/§2.41), `min R = ∋ ∩ (∋°\R)` and `max R = min R°` (B&dM §7.1, `AOP.A7_1`).

  3. **`eval`** — maps each constructor to the corresponding INSTANCE operation.  Soundness is
     therefore FREE: every equation derivable from the allegory axioms holds of evaluated terms
     because the target is a proven allegory.  There is no separate soundness proof to write.

  Infinite carriers (`Int`, lists): a term is run on a FIXED instance by bounding the universe —
  e.g. the profits of an n-day stock instance live in a known finite range and are
  offset-encoded into `Fin k`.  See the LC 121 demos.

  This file is the INTERPRETER only.  The demos and case-study fixtures that RUN it — the
  relational DIVISION query, LC 207 cycle detection, the LC 121 spec/fold runs — live in
  `rel/RelInterpDemo.lean` (`#eval` + `by decide`).
-/
import Freyd.S2_30
import Freyd.S2_40

set_option linter.unusedVariables false

namespace Freyd.Alg.FinRel

open Freyd

/-! ## Executable bounded quantifiers over `Fin n` -/

/-- Executable `∃ i : Fin n, f i`. -/
def anyFin (n : Nat) (f : Fin n → Bool) : Bool := (List.ofFn f).any fun b => b

/-- Executable `∀ i : Fin n, f i`. -/
def allFin (n : Nat) (f : Fin n → Bool) : Bool := (List.ofFn f).all fun b => b

theorem anyFin_iff {n : Nat} {f : Fin n → Bool} : anyFin n f = true ↔ ∃ i, f i = true := by
  simp only [anyFin, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨i, hfi⟩, hx⟩; exact ⟨i, by rw [hfi]; exact hx⟩
  · rintro ⟨i, hi⟩; exact ⟨true, ⟨i, hi⟩, rfl⟩

theorem allFin_iff {n : Nat} {f : Fin n → Bool} : allFin n f = true ↔ ∀ i, f i = true := by
  simp only [allFin, List.all_eq_true, List.mem_ofFn]
  constructor
  · intro h i; exact h (f i) ⟨i, rfl⟩
  · rintro h x ⟨i, rfl⟩; exact h i

/-- Two `Bool`s are equal iff equi-true — the bridge from pointwise logic to morphism equality. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Boolean implication `a → b` as `!a || b`. -/
theorem impB_iff {a b : Bool} : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> simp

/-- Extensionality for `Bool`-valued relations. -/
theorem bool_fun_ext {α β : Type} {R S : α → β → Bool}
    (h : ∀ x y, R x y = true ↔ S x y = true) : R = S :=
  funext fun x => funext fun y => bool_eq_of_iff (h x y)

/-! ## The executable finite allegory `FinRel`

  An object is a finite cardinality; the carrier is `Fin card`.  A morphism is a Boolean
  matrix.  Bundled (not a bare `Nat`) so the instances live here, mirroring `RelSet`. -/

/-- An object of `FinRel`: a finite cardinality, carrier `Fin card`. -/
structure FinObj : Type where
  card : Nat

instance : Cat FinObj where
  Hom a b := Fin a.card → Fin b.card → Bool
  id _ := fun x y => decide (x = y)
  comp {a b c} R S := fun x z => anyFin b.card fun y => R x y && S y z
  id_comp R := bool_fun_ext fun x z => by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hxy, hR⟩ := Bool.and_eq_true_iff.mp hy
      exact (decide_eq_true_iff.mp hxy) ▸ hR
    · intro h
      exact anyFin_iff.mpr ⟨x, Bool.and_eq_true_iff.mpr ⟨decide_eq_true_iff.mpr rfl, h⟩⟩
  comp_id R := bool_fun_ext fun x z => by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hR, hyz⟩ := Bool.and_eq_true_iff.mp hy
      exact (decide_eq_true_iff.mp hyz) ▸ hR
    · intro h
      exact anyFin_iff.mpr ⟨z, Bool.and_eq_true_iff.mpr ⟨h, decide_eq_true_iff.mpr rfl⟩⟩
  assoc R S T := bool_fun_ext fun x w => by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hRS, hT⟩ := Bool.and_eq_true_iff.mp hy
      obtain ⟨z, hz⟩ := anyFin_iff.mp hRS
      obtain ⟨hR, hS⟩ := Bool.and_eq_true_iff.mp hz
      exact anyFin_iff.mpr ⟨z, Bool.and_eq_true_iff.mpr
        ⟨hR, anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hS, hT⟩⟩⟩⟩
    · intro h
      obtain ⟨z, hz⟩ := anyFin_iff.mp h
      obtain ⟨hR, hST⟩ := Bool.and_eq_true_iff.mp hz
      obtain ⟨y, hy⟩ := anyFin_iff.mp hST
      obtain ⟨hS, hT⟩ := Bool.and_eq_true_iff.mp hy
      exact anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr
        ⟨anyFin_iff.mpr ⟨z, Bool.and_eq_true_iff.mpr ⟨hR, hS⟩⟩, hT⟩⟩

@[simp] theorem comp_apply {a b c : FinObj} (R : a ⟶ b) (S : b ⟶ c) (x : Fin a.card)
    (z : Fin c.card) : (R ≫ S) x z = anyFin b.card (fun y => R x y && S y z) := rfl

@[simp] theorem id_apply {a : FinObj} (x y : Fin a.card) :
    (Cat.id a : a ⟶ a) x y = decide (x = y) := rfl

private theorem bool_absorb₁ : ∀ a b : Bool, (a || (b && a)) = a := by decide
private theorem bool_absorb₂ : ∀ a b : Bool, ((a || b) && a) = a := by decide

instance : Allegory FinObj where
  recip R := fun y x => R x y
  inter R S := fun x y => R x y && S x y
  recip_recip _ := rfl
  recip_comp R S := bool_fun_ext fun z x => by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hR, hS⟩ := Bool.and_eq_true_iff.mp hy
      exact anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hS, hR⟩⟩
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hS, hR⟩ := Bool.and_eq_true_iff.mp hy
      exact anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hR, hS⟩⟩
  recip_inter _ _ := rfl
  inter_idem R := funext fun x => funext fun y => Bool.and_self _
  inter_comm R S := funext fun x => funext fun y => Bool.and_comm _ _
  inter_assoc R S T := funext fun x => funext fun y => (Bool.and_assoc _ _ _).symm
  semidistrib R S T := bool_fun_ext fun x z => by
    constructor
    · intro h
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hR, hST⟩ := Bool.and_eq_true_iff.mp hy
      obtain ⟨hS, hT⟩ := Bool.and_eq_true_iff.mp hST
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hR, hS⟩⟩, h⟩,
        anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hR, hT⟩⟩⟩
    · intro h
      exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  modular R S T := bool_fun_ext fun x z => by
    constructor
    · intro h
      obtain ⟨hRS, hT⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨y, hy⟩ := anyFin_iff.mp hRS
      obtain ⟨hR, hS⟩ := Bool.and_eq_true_iff.mp hy
      refine Bool.and_eq_true_iff.mpr ⟨h, anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨?_, hS⟩⟩⟩
      exact Bool.and_eq_true_iff.mpr ⟨hR, anyFin_iff.mpr ⟨z, Bool.and_eq_true_iff.mpr ⟨hT, hS⟩⟩⟩
    · intro h
      exact (Bool.and_eq_true_iff.mp h).1

@[simp] theorem recip_apply {a b : FinObj} (R : a ⟶ b) (y : Fin b.card) (x : Fin a.card) :
    R° y x = R x y := rfl

@[simp] theorem inter_apply {a b : FinObj} (R S : a ⟶ b) (x : Fin a.card) (y : Fin b.card) :
    (R ∩ S) x y = (R x y && S x y) := rfl

/-- The allegory order in `FinRel` is pointwise Boolean implication. -/
theorem le_iff {a b : FinObj} {R S : a ⟶ b} :
    R ⊑ S ↔ ∀ x y, R x y = true → S x y = true := by
  constructor
  · intro h x y hR
    have e : (R x y && S x y) = R x y := congrFun (congrFun h x) y
    have he : (R x y && S x y) = true := by rw [e]; exact hR
    exact (Bool.and_eq_true_iff.mp he).2
  · intro h
    exact bool_fun_ext fun x y => ⟨fun hRS => (Bool.and_eq_true_iff.mp hRS).1,
      fun hR => Bool.and_eq_true_iff.mpr ⟨hR, h x y hR⟩⟩

instance : DistributiveAllegory FinObj :=
  { (inferInstance : Allegory FinObj) with
    zero := fun _ _ => false
    union := fun R S => fun x y => R x y || S x y
    zero_comp := fun R => bool_fun_ext fun x z =>
      ⟨fun h => by
        obtain ⟨y, hy⟩ := anyFin_iff.mp h
        exact (Bool.and_eq_true_iff.mp hy).1,
       fun h => nomatch h⟩
    comp_zero := fun R => bool_fun_ext fun x z =>
      ⟨fun h => by
        obtain ⟨y, hy⟩ := anyFin_iff.mp h
        exact (Bool.and_eq_true_iff.mp hy).2,
       fun h => nomatch h⟩
    union_idem := fun R => funext fun x => funext fun y => Bool.or_self _
    union_comm := fun R S => funext fun x => funext fun y => Bool.or_comm _ _
    union_assoc := fun R S T => funext fun x => funext fun y => (Bool.or_assoc _ _ _).symm
    union_inter_absorb := fun R S => funext fun x => funext fun y => bool_absorb₁ _ _
    inter_union_absorb := fun R S => funext fun x => funext fun y => bool_absorb₂ _ _
    comp_union_distrib := fun R S T => bool_fun_ext fun x z => by
      constructor
      · intro h
        obtain ⟨y, hy⟩ := anyFin_iff.mp h
        obtain ⟨hR, hST⟩ := Bool.and_eq_true_iff.mp hy
        exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hST).elim
          (fun hS => Or.inl (anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hR, hS⟩⟩))
          (fun hT => Or.inr (anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hR, hT⟩⟩)))
      · intro h
        refine (Bool.or_eq_true_iff.mp h).elim (fun hS => ?_) (fun hT => ?_)
        · obtain ⟨y, hy⟩ := anyFin_iff.mp hS
          obtain ⟨hR, hS'⟩ := Bool.and_eq_true_iff.mp hy
          exact anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr
            ⟨hR, Bool.or_eq_true_iff.mpr (Or.inl hS')⟩⟩
        · obtain ⟨y, hy⟩ := anyFin_iff.mp hT
          obtain ⟨hR, hT'⟩ := Bool.and_eq_true_iff.mp hy
          exact anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr
            ⟨hR, Bool.or_eq_true_iff.mpr (Or.inr hT')⟩⟩
    inter_union_distrib := fun R S T => funext fun x => funext fun y =>
      Bool.and_or_distrib_left _ _ _
    zero_union := fun R => funext fun x => funext fun y => Bool.false_or _ }

@[simp] theorem union_apply {a b : FinObj} (R S : a ⟶ b) (x : Fin a.card) (y : Fin b.card) :
    (R ∪ S) x y = (R x y || S x y) := rfl

instance : DivisionAllegory FinObj :=
  { (inferInstance : DistributiveAllegory FinObj) with
    div := fun {a b c} R S => fun x y => allFin c.card fun z => !(S y z) || R x z
    div_comp_le := fun R S => le_iff.mpr fun x z h => by
      obtain ⟨y, hy⟩ := anyFin_iff.mp h
      obtain ⟨hdiv, hS⟩ := Bool.and_eq_true_iff.mp hy
      exact impB_iff.mp (allFin_iff.mp hdiv z) hS
    le_div := fun T R S h => le_iff.mpr fun x y hT =>
      allFin_iff.mpr fun z => impB_iff.mpr fun hS =>
        le_iff.mp h x z (anyFin_iff.mpr ⟨y, Bool.and_eq_true_iff.mpr ⟨hT, hS⟩⟩) }

@[simp] theorem div_apply {a b c : FinObj} (R : a ⟶ c) (S : b ⟶ c) (x : Fin a.card)
    (y : Fin b.card) :
    (DivisionAllegory.div R S) x y = allFin c.card (fun z => !(S y z) || R x z) := rfl

/-! ## Power objects: subsets of `Fin n` coded as the bits of a number `< 2^n` -/

/-- The power object `[a]`: subsets of `Fin card` as bit-codes in `Fin (2^card)`. -/
def pow (a : FinObj) : FinObj := ⟨2 ^ a.card⟩

/-- EXECUTABLE membership `∋ : [a] ⟶ a` — bit `y` of the code `P`. -/
def epsB (a : FinObj) : pow a ⟶ a := fun P y => P.val.testBit y.val

/-- Encode a predicate on `Fin n` as a number `< 2^n` (little-endian bits). -/
def encNat : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => (f ⟨0, Nat.succ_pos n⟩).toNat + 2 * encNat n (fun i => f i.succ)

theorem encNat_lt : ∀ (n : Nat) (f : Fin n → Bool), encNat n f < 2 ^ n
  | 0, _ => Nat.zero_lt_one
  | n + 1, f => by
    have ih := encNat_lt n (fun i => f i.succ)
    have ht : (f ⟨0, Nat.succ_pos n⟩).toNat < 2 := by
      cases f ⟨0, Nat.succ_pos n⟩ <;> decide
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    show (f ⟨0, Nat.succ_pos n⟩).toNat + 2 * encNat n (fun i => f i.succ) < 2 ^ (n + 1)
    omega

theorem encNat_testBit : ∀ (n : Nat) (f : Fin n → Bool) (i : Fin n),
    (encNat n f).testBit i.val = f i
  | n + 1, f, ⟨0, h0⟩ => by
    have e0 : (⟨0, h0⟩ : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := rfl
    rw [e0]
    show ((f ⟨0, Nat.succ_pos n⟩).toNat + 2 * encNat n (fun i => f i.succ)).testBit 0
      = f ⟨0, Nat.succ_pos n⟩
    rw [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    cases f ⟨0, Nat.succ_pos n⟩ <;> rfl
  | n + 1, f, ⟨i + 1, hi⟩ => by
    show ((f ⟨0, Nat.succ_pos n⟩).toNat + 2 * encNat n (fun j => f j.succ)).testBit (i + 1)
      = f ⟨i + 1, hi⟩
    rw [Nat.testBit_add_one]
    have ht : (f ⟨0, Nat.succ_pos n⟩).toNat < 2 := by
      cases f ⟨0, Nat.succ_pos n⟩ <;> decide
    have hdiv : ((f ⟨0, Nat.succ_pos n⟩).toNat + 2 * encNat n (fun j => f j.succ)) / 2
        = encNat n (fun j => f j.succ) := by omega
    rw [hdiv]
    exact encNat_testBit n (fun j => f j.succ) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- The graph of a function as an executable relation (cf. `RelSet.graph`). -/
def graphB {a b : FinObj} (f : Fin a.card → Fin b.card) : a ⟶ b := fun x y => decide (y = f x)

theorem graphB_map {a b : FinObj} (f : Fin a.card → Fin b.card) : Map (graphB f) := by
  refine ⟨?_, ?_⟩
  · -- Entire: dom (graphB f) = 1
    show dom (graphB f) = Cat.id a
    refine bool_fun_ext fun x x' => ⟨fun h => (Bool.and_eq_true_iff.mp h).1, fun h => ?_⟩
    refine Bool.and_eq_true_iff.mpr ⟨h, anyFin_iff.mpr ⟨f x, Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true_iff.mpr rfl, decide_eq_true_iff.mpr ?_⟩⟩⟩
    rw [decide_eq_true_iff.mp h]
  · -- Simple: single-valued
    show (graphB f)° ≫ graphB f ⊑ Cat.id b
    refine le_iff.mpr fun y y' h => ?_
    obtain ⟨x, hx⟩ := anyFin_iff.mp h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hx
    exact decide_eq_true_iff.mpr
      ((decide_eq_true_iff.mp h1).trans (decide_eq_true_iff.mp h2).symm)

/-- `∋` is straight: bit-codes with the same members are equal (`Nat.eq_of_testBit_eq`). -/
theorem epsB_straight (b : FinObj) : Straight (epsB b) := by
  show (epsB b /ₛ epsB b) ⊑ Cat.id (pow b)
  rw [le_iff]
  intro P Q h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  -- h1 : Q ⊆ P (right division), h2 : P ⊆ Q (converse leg)
  refine decide_eq_true_iff.mpr (Fin.ext (Nat.eq_of_testBit_eq fun i => ?_))
  match Nat.decLt i b.card with
  | .isTrue hi =>
    have hQP := impB_iff.mp (allFin_iff.mp h1 ⟨i, hi⟩)
    have hPQ := impB_iff.mp (allFin_iff.mp h2 ⟨i, hi⟩)
    exact bool_eq_of_iff ⟨hPQ, hQP⟩
  | .isFalse hi =>
    have hP : P.val.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le P.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))
    have hQ : Q.val.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le Q.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))
    rw [hP, hQ]

/-- `∋` is thick: every relation is classified by the graph of its encoded image. -/
theorem epsB_thick {b c : FinObj} (R : c ⟶ b) :
    ∃ f : c ⟶ pow b, Map f ∧ f ≫ epsB b = R := by
  refine ⟨graphB (fun x => ⟨encNat b.card (fun v => R x v), encNat_lt _ _⟩), graphB_map _, ?_⟩
  refine bool_fun_ext fun x v => ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨P, hP⟩ := anyFin_iff.mp h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hP
    rw [decide_eq_true_iff.mp h1] at h2
    have h2' : (encNat b.card (fun v => R x v)).testBit v.val = true := h2
    rw [encNat_testBit b.card (fun v => R x v) v] at h2'
    exact h2'
  · refine anyFin_iff.mpr ⟨⟨encNat b.card (fun v => R x v), encNat_lt _ _⟩,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true_iff.mpr rfl, ?_⟩⟩
    show (encNat b.card (fun v => R x v)).testBit v.val = true
    rw [encNat_testBit b.card (fun v => R x v) v]
    exact h

/-- `FinRel` is a POWER ALLEGORY — so all `∋`/`Λ` laws hold of the executable model too. -/
instance : PowerAllegory FinObj :=
  { (inferInstance : DivisionAllegory FinObj) with
    powerObj := pow
    eps := epsB
    eps_straight := epsB_straight
    eps_thick := fun R _ => epsB_thick R }

/-! ## The term language: a deep AST of relation-algebra expressions

  Primitive constructors only for the operations of the classes above (plus `⊤`, which exists
  in the finite model).  `leftDiv`, `Λ = A`, `min`, `max` are DERIVED syntax below — the book
  definitions verbatim — so running the B&dM spec vocabulary costs no new evaluator code. -/

/-- Relation-algebra expressions over `FinRel`, indexed by source and target object. -/
inductive RE : FinObj → FinObj → Type where
  /-- Ground data: a finite Boolean relation (the "database"). -/
  | atom {a b : FinObj} (R : a ⟶ b) : RE a b
  | id (a : FinObj) : RE a a
  | comp {a b c : FinObj} : RE a b → RE b c → RE a c
  | conv {a b : FinObj} : RE a b → RE b a
  | meet {a b : FinObj} : RE a b → RE a b → RE a b
  | join {a b : FinObj} : RE a b → RE a b → RE a b
  | bot (a b : FinObj) : RE a b
  | top (a b : FinObj) : RE a b
  /-- Right division `R/S` (§2.31). -/
  | div {a b c : FinObj} : RE a c → RE b c → RE a b
  /-- Membership `∋ : [a] ⟶ a` (§2.41). -/
  | eps (a : FinObj) : RE (pow a) a

/-- **The interpreter.**  Each constructor is evaluated by the corresponding operation of the
    PROVEN allegory instances above, so every consequence of the allegory axioms holds of the
    results by construction — soundness is free.  Total and executable. -/
def eval : {a b : FinObj} → RE a b → (a ⟶ b)
  | _, _, .atom R => R
  | _, _, .id a => Cat.id a
  | _, _, .comp e f => eval e ≫ eval f
  | _, _, .conv e => (eval e)°
  | _, _, .meet e f => eval e ∩ eval f
  | _, _, .join e f => eval e ∪ eval f
  | _, _, .bot _ _ => 𝟘
  | _, _, .top _ _ => fun _ _ => true
  | _, _, .div e f => DivisionAllegory.div (eval e) (eval f)
  | _, _, .eps a => epsB a

/-! ### Soundness for free: the allegory laws hold of evaluated terms via the instances -/

example {a b c : FinObj} (e : RE a b) (f : RE b c) :
    eval (.conv (.comp e f)) = eval (.comp (.conv f) (.conv e)) :=
  Allegory.recip_comp (eval e) (eval f)

example {a b c : FinObj} (T : RE a b) (R : RE a c) (S : RE b c) :
    eval T ⊑ eval (.div R S) ↔ eval (.comp T S) ⊑ eval R :=
  le_div_iff (eval T) (eval R) (eval S)

example {a : FinObj} : eval (.eps a) = ∋ a := rfl

/-! ### The B&dM spec vocabulary as DERIVED syntax (book definitions verbatim) -/

/-- Left division `S\R = (R°/S°)°` (§2.312, `Freyd.S2_3.leftDiv` verbatim). -/
def leftDivE {a b c : FinObj} (S : RE a b) (R : RE a c) : RE b c :=
  .conv (.div (.conv R) (.conv S))

/-- Power transpose `Λ`: `A R = R /ₛ ∋ = (R/∋) ∩ ((∋/R)°)` (§2.331 + §2.41 verbatim). -/
def AE {a b : FinObj} (R : RE a b) : RE a (pow b) :=
  .meet (.div R (.eps b)) (.conv (.div (.eps b) R))

/-- B&dM §7.1 `min R = ∋ ∩ (∋°\R)` (`AOP.A7_1.minRel` verbatim). -/
def minRelE {a : FinObj} (R : RE a a) : RE (pow a) a :=
  .meet (.eps a) (leftDivE (.conv (.eps a)) R)

/-- B&dM §7.1 `max R = min R°` (`AOP.A7_1.maxRel` verbatim). -/
def maxRelE {a : FinObj} (R : RE a a) : RE (pow a) a := minRelE (.conv R)

/-- The derived syntax means what the book means: `eval (leftDivE S R) = S\R`. -/
theorem eval_leftDivE {a b c : FinObj} (S : RE a b) (R : RE a c) :
    eval (leftDivE S R) = leftDiv (eval S) (eval R) := rfl

/-- `eval (AE R) = Λ(eval R)` — the §2.41 power transpose, on the nose. -/
theorem eval_AE {a b : FinObj} (R : RE a b) : eval (AE R) = Λ (eval R) := rfl

/-- `eval (minRelE R)` is B&dM's `min R = ∋ ∩ (∋°\R)` (`AOP.A7_1.minRel`'s body, which is
    stated there under `UnguardedPowerLCDA`; `FinRel` has no computable arbitrary `Sup`, so we
    state the body directly). -/
theorem eval_minRelE {a : FinObj} (R : RE a a) :
    eval (minRelE R) = (∋ a ∩ leftDiv ((∋ a)°) (eval R)) := rfl

/-! ### Pointwise semantics of the spec vocabulary — the general TRANSPORT layer

  What `Λ`, `max`, and the whole extremum shape `A R ≫ max D` mean POINTWISE in `FinRel`.
  These lemmas eliminate the `2^card` powerset-code quantifier (the witness subset is exactly
  the `encNat`-encoded image), so a run of a spec term is not just a number but a predicate:
  `A R ≫ max D` accepts `v` iff `v` is `R`-achievable and `D`-dominates every `R`-achievable
  value.  A bounded encoding `R` of an abstract spec then transports along a per-problem
  `R x v ↔ abstract-spec (decode v)` lemma to a THEOREM about the evaluated term — see
  `rel.AutoDeriveSearch`, where LC 121's instance is chained to `L121.solve_correct`. -/

/-- `Λ` pointwise: `A R` relates `x` to exactly the bit-code of its `R`-image. -/
theorem Λ_apply {a b : FinObj} (R : a ⟶ b) (x : Fin a.card) (P : Fin (pow b).card) :
    Λ R x P = true ↔ ∀ v, epsB b P v = R x v := by
  show (allFin b.card (fun v => !(epsB b P v) || R x v)
     && allFin b.card (fun v => !(R x v) || epsB b P v)) = true ↔ _
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact fun v => bool_eq_of_iff
      ⟨fun hP => impB_iff.mp (allFin_iff.mp h1 v) hP,
       fun hR => impB_iff.mp (allFin_iff.mp h2 v) hR⟩
  · intro h
    refine Bool.and_eq_true_iff.mpr
      ⟨allFin_iff.mpr fun v => impB_iff.mpr fun hP => ?_,
       allFin_iff.mpr fun v => impB_iff.mpr fun hR => ?_⟩
    · rw [← h v]; exact hP
    · rw [h v]; exact hR

/-- `max` pointwise: `eval (maxRelE d)` relates a bit-code `P` to `w` iff `w ∈ P` and `w`
    `d`-dominates every member of `P` (B&dM §7.1 `max D = min D°`, executably). -/
theorem maxRelE_apply {a : FinObj} (d : RE a a) (P : Fin (pow a).card) (w : Fin a.card) :
    eval (maxRelE d) P w = true ↔
      (epsB a P w = true ∧ ∀ z, epsB a P z = true → eval d w z = true) := by
  show (epsB a P w && allFin a.card (fun z => !(epsB a P z) || eval d w z)) = true ↔ _
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨h1, fun z hz => impB_iff.mp (allFin_iff.mp h2 z) hz⟩
  · rintro ⟨h1, h2⟩
    exact Bool.and_eq_true_iff.mpr ⟨h1, allFin_iff.mpr fun z => impB_iff.mpr (h2 z)⟩

/-- **The general spec-transport lemma**: the extremum shape `A e ≫ max d` pointwise accepts
    `(x, v)` iff `v` is `e`-achievable from `x` and `d`-dominates every `e`-achievable value.
    The existential over `2^card` subset codes is discharged by the encoded image itself
    (`encNat`), so no powerset reasoning survives into the statement. -/
theorem Λ_comp_maxRel_apply {a b : FinObj} (e : RE a b) (d : RE b b)
    (x : Fin a.card) (v : Fin b.card) :
    eval (.comp (AE e) (maxRelE d)) x v = true ↔
      (eval e x v = true ∧ ∀ z, eval e x z = true → eval d v z = true) := by
  show anyFin (pow b).card (fun P => eval (AE e) x P && eval (maxRelE d) P v) = true ↔ _
  constructor
  · intro h
    obtain ⟨P, hP⟩ := anyFin_iff.mp h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hP
    have hA := (Λ_apply (eval e) x P).mp h1
    obtain ⟨hmem, hdom⟩ := (maxRelE_apply d P v).mp h2
    exact ⟨by rw [← hA v]; exact hmem, fun z hz => hdom z (by rw [hA z]; exact hz)⟩
  · rintro ⟨h1, h2⟩
    refine anyFin_iff.mpr ⟨⟨encNat b.card (fun u => eval e x u), encNat_lt _ _⟩,
      Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · exact (Λ_apply (eval e) x _).mpr fun u => encNat_testBit b.card (fun u => eval e x u) u
    · refine (maxRelE_apply d _ v).mpr ⟨?_, fun z hz => h2 z ?_⟩
      · show (encNat b.card (fun u => eval e x u)).testBit v.val = true
        rw [encNat_testBit b.card (fun u => eval e x u) v]; exact h1
      · have hz' : (encNat b.card (fun u => eval e x u)).testBit z.val = true := hz
        rw [encNat_testBit b.card (fun u => eval e x u) z] at hz'; exact hz'


/-! ## Demo 4 — the DERIVED PROGRAM run by STRUCTURAL FOLD (polynomial, NO powerset)

  Verdict (c), CORRECTED.  The spec term `A spec ≫ max D` (Demo 3) is exponential ONLY because
  `A spec` enumerates `2^|Val|` subset codes.  The DERIVED program is a CATAMORPHISM, and a
  catamorphism does not need a global matrix over the infinite initial algebra `SL ℤ` — a `cata`
  term is evaluated AT a concrete input by FOLDING the input structure: polynomial, no subset
  enumeration.

  So the model needs a SECOND, applicative evaluator (`evalP`) that runs a recursion-scheme term
  by structural recursion, alongside the matrix evaluator `eval`.  The two are bridged by the AoP
  derivation `solve = A spec ≫ max D` (proven in `leet.L121`); here we RUN both on the same
  small instance and check they agree — the derivation's correctness, now runnable on both sides. -/

namespace ProgEval

/-- Non-empty snoc-list — the initial algebra of `F A X = A ⊕ X × A`, the datatype `leet.L121`
    folds over (`wrap` = single price, `snoc` = append a price). -/
inductive SL (A : Type) : Type where
  | wrap : A → SL A
  | snoc : SL A → A → SL A

/-- The structural fold (catamorphism `⦇base, step⦈`) over `SL`: `base` at the leaf, `step` at
    every `snoc`.  This is the value-level meaning of a `cata` term. -/
def foldSL {A C : Type} (base : A → C) (step : C → A → C) : SL A → C
  | .wrap a    => base a
  | .snoc xs a => step (foldSL base step xs) a

/-- Binary tree — the initial algebra of `F A X = 1 ⊕ X × A × X`, the tree functor of
    `AOP.A6_TreeBin` whose folds the tree LeetCode files (`leet.L104`, `leet.L543`, …) are.
    The interpreter-side carrier mirroring `SL`. -/
inductive TB (A : Type) : Type where
  | nil  : TB A
  | node : TB A → A → TB A → TB A

/-- The structural fold (catamorphism `⦇base, node⦈`) over `TB`: `base` at every `nil`, `node`
    at every node, folded children in place — the tree counterpart of `foldSL`. -/
def foldTB {A C : Type} (base : C) (node : C → A → C → C) : TB A → C
  | .nil        => base
  | .node l a r => node (foldTB base node l) a (foldTB base node r)

/-- A value-level PROGRAM term: ground maps (`fn` = a `Map` atom), diagram-order composition
    (`comp` = `≫`), and the `cata`/`cataT` recursion schemes.  This is the "efficient program"
    fragment, disjoint from the finite-matrix `RE` (a `cata` has no finite matrix; it has a fold). -/
inductive Prog : Type → Type → Type 1 where
  | fn    {I O : Type} (f : I → O) : Prog I O
  | comp  {I M O : Type} : Prog I M → Prog M O → Prog I O
  | cata  {A C : Type} (base : A → C) (step : C → A → C) : Prog (SL A) C
  | cataT {A C : Type} (base : C) (node : C → A → C → C) : Prog (TB A) C
  | pair  {I O₁ O₂ : Type} : Prog I O₁ → Prog I O₂ → Prog I (O₁ × O₂)

/-- **The applicative evaluator**: run a program term AT an input by recursing on the term, and
    for `cata` on the INPUT STRUCTURE.  Total, structural, no enumeration. -/
def evalP : {I O : Type} → Prog I O → I → O
  | _, _, .fn f           => f
  | _, _, .comp p q       => fun x => evalP q (evalP p x)
  | _, _, .cata base step  => foldSL base step
  | _, _, .cataT base node => foldTB base node
  | _, _, .pair p q        => fun x => (evalP p x, evalP q x)

/-- The interpreter runs the catamorphism structurally: `evalP (cata …) = fold`. -/
theorem evalP_cata {A C : Type} (base : A → C) (step : C → A → C) :
    evalP (Prog.cata base step) = foldSL base step := rfl

/-- Tree counterpart: `evalP (cataT …) = foldTB`. -/
theorem evalP_cataT {A C : Type} (base : C) (node : C → A → C → C) :
    evalP (Prog.cataT base node) = foldTB base node := rfl

/-! ### The pairing former and its derived product / zip-fold (two-input problems)

  `Prog.pair p q = ⟨p,q⟩` is the point-free product mediator — the one former needed to consume
  a PAIR of inputs (or read one input twice), which the plain applicative fragment lacks (a term
  can otherwise never use its input twice).  It is a genuine, TOTAL `Prog` constructor (unlike the
  fuel-bounded `hyloF`/`anaSL`… schemes below, whose `Option` output would infect `Prog.comp`).
  `prodP`/`zipCata` are derived helpers reused by the two-input LeetCode runs (`rel/LeetRunPair`). -/

/-- The product β-law: `⟨p,q⟩` runs both sub-programs on the same input and tuples, so
    `⟨p,q⟩ ≫ π₁ = p` and `⟨p,q⟩ ≫ π₂ = q` pointwise, definitionally. -/
theorem evalP_pair {I O₁ O₂ : Type} (p : Prog I O₁) (q : Prog I O₂) (x : I) :
    evalP (Prog.pair p q) x = (evalP p x, evalP q x) := rfl

/-- The product of programs `p × q = ⟨π₁ ≫ p, π₂ ≫ q⟩`, derived from the pairing former. -/
def prodP {I₁ I₂ O₁ O₂ : Type} (p : Prog I₁ O₁) (q : Prog I₂ O₂) :
    Prog (I₁ × I₂) (O₁ × O₂) :=
  .pair (.comp (.fn Prod.fst) p) (.comp (.fn Prod.snd) q)

/-- Read an `SL` outermost-first (last snoc first) — the order a function-carrier zip fold
    consumes elements, used to transport the SECOND input to the `List` the carrier awaits.
    Composed with head-outermost loading (`Run2.consOf`) it reads the original list in order. -/
def revListOf {A : Type} : SL A → List A
  | .wrap a    => [a]
  | .snoc xs a => a :: revListOf xs

/-- **The zip-fold scheme** — the curried-two-input trick as ONE term: fold the FIRST input
    into a FUNCTION carrier `K` that awaits the second, transport the second input to the
    outermost-first `List`, and close with the problem's application map:
    `(⦇base, step⦈ × revListOf) ≫ close`. -/
def zipCata {A B K C : Type} (base : A → K) (step : K → A → K) (close : K → List B → C) :
    Prog (SL A × SL B) C :=
  .comp (prodP (.cata base step) (.fn revListOf)) (.fn fun p => close p.1 p.2)

/-- What the scheme means: the first input is genuinely FOLDED (`foldSL`), the second closed
    over — definitionally. -/
theorem evalP_zipCata {A B K C : Type} (base : A → K) (step : K → A → K)
    (close : K → List B → C) (xs : SL A) (ys : SL B) :
    evalP (zipCata base step close) (xs, ys) = close (foldSL base step xs) (revListOf ys) := rfl

/-! ### Int helpers and the Int-list loader (used by the `LeetRun*` files and the ProgEval demos) -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

/-- Build a price list in day order. -/
def slOf (first : Int) (rest : List Int) : SL Int := rest.foldl SL.snoc (SL.wrap first)

/-! ### The `hylo` scheme (unfold-then-fold), showing the fragment is not cata-only -/

/-- A fuel-bounded HYLOMORPHISM over the same functor: unfold seed `s` via coalgebra `g` (a leaf
    `A`, or a sub-seed `S` carrying an `A`), then fold with `base`/`step`.  Fuel bounds the
    recursion depth, so it is total with no well-foundedness proof (cf. `AOP.A6_GenHylo`). -/
def hyloF {S A C : Type} (g : S → A ⊕ (S × A)) (base : A → C) (step : C → A → C) :
    Nat → S → Option C
  | 0,        _ => none
  | fuel + 1, s => match g s with
    | .inl a       => some (base a)
    | .inr (s', a) => match hyloF g base step fuel s' with
        | some c => some (step c a)
        | none   => none

/-! ### The Nat axis: `cataNat` and the unary bridge `natSL`

  L62/L70/L338-style problems fold over `Nat` — the initial algebra of `G X = 1 ⊕ X` — not over
  the input LIST.  `natSL n` writes `n` in unary as an `SL Unit` so the term language's `cata`
  runs a Nat-fold; `foldSL_natSL` is its defining law against the genuine `Nat.rec` fold
  `cataNat`.  (The single canonical copy — the `LeetRun*` files previously each carried an ad-hoc
  `natSL`.) -/

/-- The genuine fold over `Nat` — the initial algebra of `G X = 1 ⊕ X` — i.e. `Nat.rec` with a
    constant-in-the-index step (iteration): `base` at `zero`, `step` at every `succ`. -/
def cataNat {C : Type} (base : C) (step : C → C) : Nat → C
  | 0 => base
  | n + 1 => step (cataNat base step n)

/-- The unary bridge: `n` as an `SL Unit` — `wrap () = zero`, each snoc = one successor — so the
    term language's `cata` can run Nat-folds. -/
def natSL : Nat → SL Unit
  | 0 => .wrap ()
  | n + 1 => .snoc (natSL n) ()

/-- **The bridge law**: folding the unary bridge IS the Nat catamorphism — `Prog.cata` over
    `natSL n` computes `cataNat base step n`. -/
theorem foldSL_natSL {C : Type} (base : C) (step : C → C) :
    ∀ n, foldSL (fun _ : Unit => base) (fun c _ => step c) (natSL n) = cataNat base step n
  | 0 => rfl
  | n + 1 => by
    show step (foldSL (fun _ : Unit => base) (fun c _ => step c) (natSL n))
      = step (cataNat base step n)
    rw [foldSL_natSL base step n]

/-! ### The unfold evaluators (anamorphisms), co-located with `hyloF`

  Like `hyloF`, these are STANDALONE functions, NOT `Prog` constructors: fuel puts `Option` in
  the OUTPUT type (`none` = fuel exhausted, or a rejected parser seed), which would infect every
  downstream `Prog.comp`.  So the interpreter is a documented TWO-TIER design — the total `Prog`
  formers (`fn`/`comp`/`cata`/`cataT`/`pair`) plus these partial fuel-schemes for corecursion.
  Each is total by structural recursion on the fuel (kernel-reducible, `decide`-runnable, no
  `WellFounded`); one per (functor × effect) the unfold LeetCode problems need. -/

/-- The SL-functor UNFOLD (anamorphism): drive the coalgebra `g` from the seed, materialising
    the nonempty snoc-list it generates — `.inl a` ends with the leaf `wrap a`, `.inr (s', a)`
    emits `a` (at the snoc end) and continues from `s'`.  The unfold half of `hyloF`. -/
def anaSL {S A : Type} (g : S → A ⊕ (S × A)) : Nat → S → Option (SL A)
  | 0, _ => none
  | fuel + 1, s => match g s with
    | .inl a => some (.wrap a)
    | .inr (s', a) => match anaSL g fuel s' with
      | some xs => some (.snoc xs a)
      | none => none

/-- **A hylo is the unfold then `foldSL`**: the fused `hyloF` factors through the SL materialised
    by `anaSL` — same coalgebra, same fuel, on the nose.  (Deforestation, read right to left.) -/
theorem hyloF_eq_ana_fold {S A C : Type} (g : S → A ⊕ (S × A)) (base : A → C)
    (step : C → A → C) : ∀ (fuel : Nat) (s : S),
    hyloF g base step fuel s = (anaSL g fuel s).map (foldSL base step)
  | 0, _ => rfl
  | fuel + 1, s => by
    show (match g s with
      | .inl a => some (base a)
      | .inr (s', a) => match hyloF g base step fuel s' with
        | some c => some (step c a)
        | none => none)
      = (match g s with
        | .inl a => some (SL.wrap a)
        | .inr (s', a) => match anaSL g fuel s' with
          | some xs => some (SL.snoc xs a)
          | none => none).map (foldSL base step)
    cases g s with
    | inl a => rfl
    | inr p =>
      obtain ⟨s', a⟩ := p
      show (match hyloF g base step fuel s' with
        | some c => some (step c a)
        | none => none)
        = (match anaSL g fuel s' with
          | some xs => some (SL.snoc xs a)
          | none => none).map (foldSL base step)
      rw [hyloF_eq_ana_fold g base step fuel s']
      cases anaSL g fuel s' with
      | none => rfl
      | some xs => rfl

/-- The list-functor UNFOLD (anamorphism): coalgebra `S → 1 ⊕ (E × S)` (as `Option (E × S)`) —
    seed → nil, or emit one element + new seed — producing a possibly-empty `List E`. -/
def anaL {S E : Type} (g : S → Option (E × S)) : Nat → S → Option (List E)
  | 0, _ => none
  | fuel + 1, s => match g s with
    | none => some []
    | some (e, s') => (anaL g fuel s').map (e :: ·)

/-- `anaL` in the Kleisli category of `Option` — a PARSER's list unfold: the coalgebra may
    additionally REJECT the seed (`none` = malformed input), distinct from stopping
    (`some none`) and emitting (`some (some (e, s'))`). -/
def anaP {S E : Type} (g : S → Option (Option (E × S))) : Nat → S → Option (List E)
  | 0, _ => none
  | fuel + 1, s => match g s with
    | none => none
    | some none => some []
    | some (some (e, s')) => (anaP g fuel s').map (e :: ·)

/-- The tree-functor PARSER unfold, seed threaded as state: the coalgebra answers "nil, leftover
    `s'`" (`some (none, s')`), "node labelled `a`, descend left from `s'`" (`some (some a, s')`),
    or rejects (`none`); the RIGHT child's seed is the LEFT child's leftover — the state
    threading a plain coalgebra `S → 1 ⊕ (S × A × S)` cannot express, since a token stream
    yields the right seed only after the left parse.  Returns the tree with its leftover. -/
def anaT {S A : Type} (g : S → Option (Option A × S)) : Nat → S → Option (TB A × S)
  | 0, _ => none
  | fuel + 1, s => match g s with
    | none => none
    | some (none, s') => some (.nil, s')
    | some (some a, s') =>
      match anaT g fuel s' with
      | none => none
      | some (l, s1) =>
        match anaT g fuel s1 with
        | none => none
        | some (r, s2) => some (.node l a r, s2)

end ProgEval

end Freyd.Alg.FinRel
