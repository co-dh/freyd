/-
  Freyd & Scedrov, *Categories and Allegories* §1.572
  The category **R** of recursive functions.

  Objects: the extended natural numbers 0, 1, 2, …, ω (von Neumann: α = {β | β < α}),
  encoded as `ExtNat := Option Nat` (`some n` = the finite ordinal n, `none` = ω).
  Morphisms: recursive functions; any function from a finite natural number is
  understood to be recursive (book convention).

  **R is an AC regular category** (§1.572): given x : α → β define e : α → α by
  e(n) = min{ i ≤ n | x(i) = x(n) }; then e² = e, ex = x, e and x have the same
  level, and §1.571 (`ac_factorization_via_idempotent`) applies.

  Computability is hand-rolled (STRICTLY MATHLIB-FREE): Kleene's n-ary μ-recursive
  codes `RecCode` with a big-step evaluation relation `Eval`.  `Recursive` means
  "computed by a code that converges on every input".
-/

import Freyd.S1_57

open Freyd

namespace Freyd.Rcat

/-! ## Part 1: μ-recursive codes and their semantics -/

/-- Input vectors: `k`-tuples of naturals. -/
abbrev Vec (k : Nat) := Fin k → Nat

/-- Prepend a value to an input vector. -/
def vcons {k : Nat} (a : Nat) (v : Vec k) : Vec (k + 1) := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨j+1, h⟩ => v ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first entry of an input vector. -/
def vtail {k : Nat} (v : Vec (k + 1)) : Vec k := fun i => v i.succ

@[simp] theorem vcons_zero {k : Nat} (a : Nat) (v : Vec k) : vcons a v 0 = a := rfl

@[simp] theorem vcons_one {k : Nat} (a : Nat) (v : Vec (k + 1)) : vcons a v 1 = v 0 := rfl

@[simp] theorem vcons_succ {k : Nat} (a : Nat) (v : Vec k) (i : Fin k) :
    vcons a v i.succ = v i := rfl

@[simp] theorem vtail_vcons {k : Nat} (a : Nat) (v : Vec k) : vtail (vcons a v) = v := rfl

theorem vcons_head_tail {k : Nat} (v : Vec (k + 1)) : vcons (v 0) (vtail v) = v := by
  funext i
  rcases i with ⟨(_ | j), h⟩
  · rfl
  · rfl

/-- Kleene's μ-recursive codes, `k` = arity.  `zero` is arity-polymorphic (the
    constantly-0 function), `succ` is unary successor, `proj i` the i-th projection,
    `comp` composition, `prec` primitive recursion on the FIRST argument, `mu`
    unbounded minimization on a new first argument. -/
inductive RecCode : Nat → Type where
  | zero {k : Nat} : RecCode k
  | succ : RecCode 1
  | proj {k : Nat} (i : Fin k) : RecCode k
  | comp {k m : Nat} (f : RecCode m) (gs : Fin m → RecCode k) : RecCode k
  | prec {k : Nat} (g : RecCode k) (h : RecCode (k + 2)) : RecCode (k + 1)
  | mu {k : Nat} (f : RecCode (k + 1)) : RecCode k

/-- Big-step convergence: `Eval c v y` means code `c` on input `v` halts with output `y`.
    `prec g h`: value at `0::v` is `g v`; at `(n+1)::v` it is `h (n :: r :: v)` where `r`
    is the value at `n::v`.  `mu f`: the least `y` with `f (y::v) = 0`, all smaller
    arguments converging to a nonzero value (witnessed by `r · + 1`). -/
inductive Eval : {k : Nat} → RecCode k → Vec k → Nat → Prop where
  | zero {k : Nat} {v : Vec k} : Eval .zero v 0
  | succ {v : Vec 1} : Eval .succ v (v 0 + 1)
  | proj {k : Nat} (i : Fin k) {v : Vec k} : Eval (.proj i) v (v i)
  | comp {k m : Nat} {f : RecCode m} {gs : Fin m → RecCode k} {v : Vec k} {y : Nat}
      (w : Vec m) (hg : ∀ j, Eval (gs j) v (w j)) (hf : Eval f w y) :
      Eval (.comp f gs) v y
  | prec_zero {k : Nat} {g : RecCode k} {h : RecCode (k + 2)} {v : Vec (k + 1)} {y : Nat}
      (h0 : v 0 = 0) (hg : Eval g (vtail v) y) : Eval (.prec g h) v y
  | prec_succ {k : Nat} {g : RecCode k} {h : RecCode (k + 2)} {v : Vec (k + 1)} {n r y : Nat}
      (h0 : v 0 = n + 1) (hr : Eval (.prec g h) (vcons n (vtail v)) r)
      (hh : Eval h (vcons n (vcons r (vtail v))) y) : Eval (.prec g h) v y
  | mu {k : Nat} {f : RecCode (k + 1)} {v : Vec k} {y : Nat} (r : Nat → Nat)
      (hy : Eval f (vcons y v) 0) (hlt : ∀ i, i < y → Eval f (vcons i v) (r i + 1)) :
      Eval (.mu f) v y

/-- `Eval` is single-valued (functionality). -/
theorem Eval.det {k : Nat} {c : RecCode k} {v : Vec k} {y₁ : Nat}
    (h₁ : Eval c v y₁) : ∀ {y₂ : Nat}, Eval c v y₂ → y₁ = y₂ := by
  induction h₁ with
  | zero => intro y₂ h₂; cases h₂; rfl
  | succ => intro y₂ h₂; cases h₂; rfl
  | proj i => intro y₂ h₂; cases h₂; rfl
  | comp w hg hf ihg ihf =>
    intro y₂ h₂
    cases h₂ with
    | comp w' hg' hf' =>
      have hw : w = w' := funext fun j => ihg j (hg' j)
      exact ihf (hw ▸ hf')
  | prec_zero h0 hg ihg =>
    intro y₂ h₂
    cases h₂ with
    | prec_zero h0' hg' => exact ihg hg'
    | prec_succ h0' hr' hh' => omega
  | prec_succ h0 hr hh ihr ihh =>
    rename_i n r y
    intro y₂ h₂
    cases h₂ with
    | prec_zero h0' hg' => omega
    | prec_succ h0' hr' hh' =>
      rename_i n' r'
      have hn : n = n' := by omega
      subst hn
      have hrr : r = r' := ihr hr'
      subst hrr
      exact ihh hh'
  | mu r hy hlt ihy ihlt =>
    rename_i y
    intro y₂ h₂
    cases h₂ with
    | mu r' hy' hlt' =>
      rcases Nat.lt_trichotomy y y₂ with h | h | h
      · exact absurd (ihy (hlt' _ h)) (by omega)
      · exact h
      · exact absurd (ihlt _ h hy') (by omega)

/-! ### Recursive functions -/

/-- A `k`-ary function is RECURSIVE if some code converges to its value on every input. -/
def RecursiveV {k : Nat} (f : Vec k → Nat) : Prop := ∃ c : RecCode k, ∀ v, Eval c v (f v)

/-- Unary recursive functions ℕ → ℕ. -/
def Recursive1 (f : Nat → Nat) : Prop := RecursiveV fun v : Vec 1 => f (v 0)

/-- Binary recursive functions ℕ → ℕ → ℕ. -/
def Recursive2 (f : Nat → Nat → Nat) : Prop := RecursiveV fun v : Vec 2 => f (v 0) (v 1)

theorem RecursiveV.congr {k : Nat} {f g : Vec k → Nat} (hf : RecursiveV f)
    (h : ∀ v, f v = g v) : RecursiveV g := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, fun v => h v ▸ hc v⟩

theorem Recursive1.congr {f g : Nat → Nat} (hf : Recursive1 f) (h : ∀ n, f n = g n) :
    Recursive1 g := RecursiveV.congr hf fun v => h (v 0)

theorem Recursive2.congr {f g : Nat → Nat → Nat} (hf : Recursive2 f)
    (h : ∀ a b, f a b = g a b) : Recursive2 g := RecursiveV.congr hf fun v => h (v 0) (v 1)

theorem RecursiveV.proj {k : Nat} (i : Fin k) : RecursiveV (fun v : Vec k => v i) :=
  ⟨.proj i, fun _ => .proj i⟩

/-- Code for the constant function `c`. -/
def constCode (k c : Nat) : RecCode k :=
  match c with
  | 0 => .zero
  | c + 1 => .comp .succ fun _ => constCode k c

theorem evalConst (k c : Nat) (v : Vec k) : Eval (constCode k c) v c := by
  induction c with
  | zero => exact .zero
  | succ c ih => exact .comp (fun _ => c) (fun _ => ih) .succ

theorem RecursiveV.const (k c : Nat) : RecursiveV (fun _ : Vec k => c) :=
  ⟨constCode k c, fun v => evalConst k c v⟩

theorem Recursive1.const (c : Nat) : Recursive1 fun _ => c := RecursiveV.const 1 c

/-- Closure under composition (general form). -/
theorem RecursiveV.comp {k m : Nat} {f : Vec m → Nat} {gs : Fin m → Vec k → Nat}
    (hf : RecursiveV f) (hgs : ∀ j, RecursiveV (gs j)) :
    RecursiveV (fun v => f fun j => gs j v) := by
  obtain ⟨cf, hcf⟩ := hf
  exact ⟨.comp cf (fun j => Classical.choose (hgs j)),
    fun v => .comp (fun j => gs j v) (fun j => Classical.choose_spec (hgs j) v) (hcf _)⟩

theorem Recursive1.comp {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => g (f n) :=
  RecursiveV.comp (f := fun w : Vec 1 => g (w 0)) (gs := fun _ v => f (v 0)) hg fun _ => hf

/-- Unary post-composition at any arity. -/
theorem RecursiveV.comp1 {k : Nat} {F : Nat → Nat} {f : Vec k → Nat}
    (hF : Recursive1 F) (hf : RecursiveV f) : RecursiveV (fun v => F (f v)) :=
  RecursiveV.comp (f := fun w : Vec 1 => F (w 0)) (gs := fun _ v => f v) hF fun _ => hf

/-- Binary combination at any arity: from a recursive binary `H` and recursive
    arguments, `v ↦ H (f v) (g v)` is recursive. -/
theorem RecursiveV.comp2 {k : Nat} {H : Nat → Nat → Nat} {f g : Vec k → Nat}
    (hH : Recursive2 H) (hf : RecursiveV f) (hg : RecursiveV g) :
    RecursiveV (fun v => H (f v) (g v)) := by
  obtain ⟨cH, hcH⟩ := hH
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨cg, hcg⟩ := hg
  refine ⟨.comp cH (fun j => if j.val = 0 then cf else cg), fun v => ?_⟩
  refine .comp (vcons (f v) (fun _ => g v)) (fun j => ?_) ?_
  · rcases j with ⟨jv, hj⟩
    match jv, hj with
    | 0, _ => exact hcf v
    | 1, _ => exact hcg v
  · exact hcH (vcons (f v) fun _ => g v)

theorem Recursive1.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat}
    (hH : Recursive2 H) (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => H (f n) (g n) :=
  RecursiveV.comp2 (f := fun v : Vec 1 => f (v 0)) (g := fun v : Vec 1 => g (v 0)) hH hf hg

theorem Recursive2.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat → Nat}
    (hH : Recursive2 H) (hf : Recursive2 f) (hg : Recursive2 g) :
    Recursive2 fun a b => H (f a b) (g a b) :=
  RecursiveV.comp2 (f := fun v : Vec 2 => f (v 0) (v 1)) (g := fun v : Vec 2 => g (v 0) (v 1))
    hH hf hg

theorem Recursive2.swap {f : Nat → Nat → Nat} (hf : Recursive2 f) :
    Recursive2 fun a b => f b a :=
  Recursive2.comp2 hf (show Recursive2 fun _ b => b from RecursiveV.proj 1) (show Recursive2 fun a _ => a from RecursiveV.proj 0)

theorem Recursive2.ofFst {f : Nat → Nat} (hf : Recursive1 f) : Recursive2 fun a _ => f a :=
  RecursiveV.comp1 (f := fun v : Vec 2 => v 0) hf (RecursiveV.proj 0)

theorem Recursive2.ofSnd {f : Nat → Nat} (hf : Recursive1 f) : Recursive2 fun _ b => f b :=
  RecursiveV.comp1 (f := fun v : Vec 2 => v 1) hf (RecursiveV.proj 1)

/-! ### Arithmetic base: addition, predecessor, truncated subtraction, multiplication -/

/-- Addition code: recursion on the first argument, `add (n+1) b = add n b + 1`. -/
def addCode : RecCode 2 := .prec (.proj 0) (.comp .succ fun _ => .proj 1)

theorem evalAdd_aux : ∀ (n : Nat) (w : Vec 1), Eval addCode (vcons n w) (w 0 + n) := by
  intro n w
  induction n with
  | zero => exact .prec_zero rfl (.proj 0)
  | succ n ih =>
    exact .prec_succ rfl ih (.comp (fun _ => w 0 + n) (fun _ => .proj 1) .succ)

theorem evalAdd (v : Vec 2) : Eval addCode v (v 1 + v 0) := by
  have := evalAdd_aux (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

theorem Recursive2.add : Recursive2 fun a b => a + b := by
  refine RecursiveV.congr (g := fun v : Vec 2 => v 0 + v 1) ⟨addCode, fun v => evalAdd v⟩ ?_
  intro v
  exact Nat.add_comm (v 1) (v 0)

/-- Predecessor code (unary): `pred 0 = 0`, `pred (n+1) = n`. -/
def predCode : RecCode 1 := .prec .zero (.proj 0)

theorem evalPred_aux : ∀ (n : Nat) (w : Vec 0), Eval predCode (vcons n w) (n - 1) := by
  intro n w
  cases n with
  | zero => exact .prec_zero rfl .zero
  | succ n => exact .prec_succ rfl (evalPred_aux n w) (.proj 0)

theorem evalPred (v : Vec 1) : Eval predCode v (v 0 - 1) := by
  have := evalPred_aux (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

/-- Truncated subtraction, recursion on the FIRST argument: `rsub n a = a - n`. -/
def rsubCode : RecCode 2 := .prec (.proj 0) (.comp predCode fun _ => .proj 1)

theorem evalRsub_aux : ∀ (n : Nat) (w : Vec 1), Eval rsubCode (vcons n w) (w 0 - n) := by
  intro n w
  induction n with
  | zero => exact .prec_zero rfl (.proj 0)
  | succ n ih =>
    have hstep : Eval (.comp predCode fun _ => .proj 1)
        (vcons n (vcons (w 0 - n) w)) (w 0 - (n + 1)) := by
      have : w 0 - (n + 1) = (w 0 - n) - 1 := by omega
      rw [this]
      exact .comp (fun _ => w 0 - n) (fun _ => .proj (1 : Fin 3)) (evalPred _)
    exact .prec_succ rfl ih hstep

theorem Recursive2.sub : Recursive2 fun a b => a - b := by
  have h : Recursive2 fun a b => b - a :=
    ⟨rsubCode, fun v => by
      have := evalRsub_aux (v 0) (vtail v)
      rwa [vcons_head_tail v] at this⟩
  exact Recursive2.swap h

/-- Multiplication code: `mul 0 b = 0`, `mul (n+1) b = mul n b + b`. -/
def mulCode : RecCode 2 :=
  .prec .zero (.comp addCode fun j => if j.val = 0 then .proj 1 else .proj 2)

theorem evalMul_aux : ∀ (n : Nat) (w : Vec 1), Eval mulCode (vcons n w) (n * w 0) := by
  intro n w
  induction n with
  | zero =>
    rw [Nat.zero_mul]
    exact .prec_zero rfl .zero
  | succ n ih =>
    have hstep : Eval (.comp addCode fun j : Fin 2 => if j.val = 0 then .proj 1 else .proj 2)
        (vcons n (vcons (n * w 0) w)) ((n + 1) * w 0) := by
      refine .comp (vcons (n * w 0) fun _ => w 0) (fun j => ?_) ?_
      · rcases j with ⟨jv, hj⟩
        match jv, hj with
        | 0, _ => exact .proj (1 : Fin 3)
        | 1, _ => exact .proj (2 : Fin 3)
      · have : (n + 1) * w 0 = w 0 + n * w 0 := by
          rw [Nat.succ_mul, Nat.add_comm]
        rw [this]
        exact evalAdd _
    exact .prec_succ rfl ih hstep

theorem Recursive2.mul : Recursive2 fun a b => a * b :=
  ⟨mulCode, fun v => by
    have := evalMul_aux (v 0) (vtail v)
    rwa [vcons_head_tail v] at this⟩

/-! ### Derived pointwise combinators (unary level) -/

theorem Recursive1.add {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n + g n := Recursive1.comp2 Recursive2.add hf hg

theorem Recursive1.mul {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n * g n := Recursive1.comp2 Recursive2.mul hf hg

theorem Recursive1.sub {f g : Nat → Nat} (hf : Recursive1 f) (hg : Recursive1 g) :
    Recursive1 fun n => f n - g n := Recursive1.comp2 Recursive2.sub hf hg

/-- The equality indicator `1` if `a = b` else `0`, arithmetically:
    `1 - ((a-b)+(b-a))`. -/
def eqInd (a b : Nat) : Nat := 1 - ((a - b) + (b - a))

theorem eqInd_eq {a b : Nat} (h : a = b) : eqInd a b = 1 := by simp [eqInd, h]

theorem eqInd_ne {a b : Nat} (h : a ≠ b) : eqInd a b = 0 := by
  unfold eqInd; omega

theorem Recursive2.eqInd : Recursive2 Rcat.eqInd :=
  Recursive2.comp2 (H := fun a b => a - b) Recursive2.sub
    (Recursive2.comp2 (H := fun _ _ => (1 : Nat)) (Recursive2.ofFst (Recursive1.const 1))
      (show Recursive2 fun a _ => a from RecursiveV.proj 0) (show Recursive2 fun _ b => b from RecursiveV.proj 1))
    (Recursive2.comp2 Recursive2.add Recursive2.sub (Recursive2.swap Recursive2.sub))

/-- `if n = c then a else w n` is recursive when `w` is (constant-case update). -/
theorem Recursive1.ifEqConst (c a : Nat) {w : Nat → Nat} (hw : Recursive1 w) :
    Recursive1 fun n => if n = c then a else w n := by
  have hind : Recursive1 fun n => eqInd n c :=
    Recursive1.comp2 Recursive2.eqInd (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const c)
  have harith : Recursive1 fun n => a * eqInd n c + w n * (1 - eqInd n c) :=
    Recursive1.add (Recursive1.mul (Recursive1.const a) hind)
      (Recursive1.mul hw (Recursive1.sub (Recursive1.const 1) hind))
  refine harith.congr fun n => ?_
  by_cases h : n = c
  · rw [if_pos h, eqInd_eq h]; simp
  · rw [if_neg h, eqInd_ne h]; simp

/-- Finite tables belong to any unary function class containing zero and closed
    under extensional equality and replacement at one argument. -/
theorem finTable_of {P : (Nat → Nat) → Prop}
    (zero : P fun _ => 0)
    (congr : ∀ {f g}, P f → (∀ n, f n = g n) → P g)
    (replace : ∀ c a {w}, P w → P fun n => if n = c then a else w n)
    (m : Nat) (t : Fin m → Nat) :
    P fun j => if h : j < m then t ⟨j, h⟩ else 0 := by
  induction m with
  | zero =>
    refine congr zero fun n => ?_
    rw [dif_neg (by omega)]
  | succ m ih =>
    have prev := ih fun i => t i.castSucc
    have next := replace m (t ⟨m, Nat.lt_succ_self m⟩) prev
    refine congr next fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      rw [if_pos rfl, dif_pos (Nat.lt_succ_self j)]
    · rw [if_neg hjm]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (Nat.lt_succ_of_lt hj)]
        rfl
      · rw [dif_neg hj, dif_neg (by omega)]

/-- Any finite lookup table (0 outside its domain) is recursive.  This is the
    formal content of the book's "any function from a finite natural number is
    understood to be recursive". -/
theorem Recursive1.finTable (m : Nat) (t : Fin m → Nat) :
    Recursive1 fun j => if h : j < m then t ⟨j, h⟩ else 0 :=
  finTable_of (Recursive1.const 0) (fun h e => h.congr e) Recursive1.ifEqConst m t

/-- Closure under total minimization: if `t` is a recursive binary test and `f n`
    is the least `i` with `t i n = 0` (which always exists), then `f` is recursive.
    This is the only place unbounded search enters. -/
theorem Recursive1.mu {t : Nat → Nat → Nat} (ht : Recursive2 t) {f : Nat → Nat}
    (hzero : ∀ n, t (f n) n = 0) (hpos : ∀ n i, i < f n → t i n ≠ 0) : Recursive1 f := by
  obtain ⟨ct, hct⟩ := ht
  refine ⟨.mu ct, fun v => ?_⟩
  refine .mu (fun i => t i (v 0) - 1) ?_ ?_
  · have h := hct (vcons (f (v 0)) v)
    simpa [hzero (v 0)] using h
  · intro i hi
    have h := hct (vcons i v)
    have hne := hpos (v 0) i hi
    have : t i (v 0) - 1 + 1 = t i (v 0) := by omega
    rw [this]
    simpa using h

/-! ## Part 2: least elements, primitive recursion helper, Cantor pairing, div/mod -/

/-- Every inhabited predicate on ℕ has a least witness (classical, no decidability). -/
theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ i, i < n → ¬P i := by
  obtain ⟨n, hn⟩ := h
  have aux : ∀ b, (∃ i, i ≤ b ∧ P i) → ∃ m, P m ∧ ∀ i, i < m → ¬P i := by
    intro b
    induction b with
    | zero =>
      rintro ⟨i, hi, hPi⟩
      have : i = 0 := by omega
      subst this
      exact ⟨0, hPi, by omega⟩
    | succ b ih =>
      rintro ⟨i, hi, hPi⟩
      rcases Classical.em (∃ j, j ≤ b ∧ P j) with hj | hj
      · exact ih hj
      · have hib : i = b + 1 := by
          rcases Nat.lt_or_ge i (b + 1) with h' | h'
          · exact absurd ⟨i, by omega, hPi⟩ hj
          · omega
        subst hib
        exact ⟨b + 1, hPi, fun j hjlt hPj => hj ⟨j, by omega, hPj⟩⟩
  exact aux n ⟨n, Nat.le_refl n, hn⟩

/-- The least witness of an inhabited predicate. -/
noncomputable def theLeast (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  Classical.choose (exists_least h)

/-- Defining spec of `theLeast` (first half of `Classical.choose_spec`): the least witness
    satisfies `P`.  Kept — it is the specification of the `theLeast` choice-def, not an alias. -/
theorem theLeast_mem (P : Nat → Prop) (h : ∃ n, P n) : P (theLeast P h) :=
  (Classical.choose_spec (exists_least h)).1

/-- Defining spec of `theLeast` (second half of `Classical.choose_spec`): nothing below it
    satisfies `P`.  Kept — specification of the choice-def, not an alias. -/
theorem theLeast_min (P : Nat → Prop) (h : ∃ n, P n) :
    ∀ i, i < theLeast P h → ¬P i :=
  (Classical.choose_spec (exists_least h)).2

theorem theLeast_le (P : Nat → Prop) (h : ∃ n, P n) {n : Nat} (hn : P n) :
    theLeast P h ≤ n := by
  rcases Nat.lt_or_ge n (theLeast P h) with h' | h'
  · exact absurd hn (theLeast_min P h n h')
  · exact h'

/-- The least witness is unique: anything satisfying the least-characterization is it. -/
theorem theLeast_unique (P : Nat → Prop) (h : ∃ n, P n) {n : Nat}
    (hn : P n) (hmin : ∀ i, i < n → ¬P i) : theLeast P h = n := by
  have h₁ := theLeast_le P h hn
  rcases Nat.lt_or_ge (theLeast P h) n with h' | h'
  · exact absurd (theLeast_mem P h) (hmin _ h')
  · omega

/-! ### Unary primitive recursion -/

/-- Unary primitive recursion: `natIter g0 H 0 = g0`, `natIter g0 H (n+1) = H n (natIter g0 H n)`. -/
def natIter (g0 : Nat) (H : Nat → Nat → Nat) : Nat → Nat
  | 0 => g0
  | n + 1 => H n (natIter g0 H n)

theorem Recursive1.natIter (g0 : Nat) {H : Nat → Nat → Nat} (hH : Recursive2 H) :
    Recursive1 (Rcat.natIter g0 H) := by
  obtain ⟨cH, hcH⟩ := hH
  refine ⟨.prec (constCode 0 g0) cH, fun v => ?_⟩
  have key : ∀ (n : Nat) (w : Vec 0),
      Eval (.prec (constCode 0 g0) cH) (vcons n w) (Rcat.natIter g0 H n) := by
    intro n w
    induction n with
    | zero => exact .prec_zero rfl (evalConst 0 g0 w)
    | succ n ih =>
      refine .prec_succ rfl ih ?_
      exact hcH (vcons n (vcons (Rcat.natIter g0 H n) w))
  have := key (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

/-! ### Cantor pairing -/

/-- Triangular numbers: `tri s = 0 + 1 + ⋯ + s`. -/
def tri : Nat → Nat := natIter 0 fun s r => r + (s + 1)

@[simp] theorem tri_zero : tri 0 = 0 := rfl

@[simp] theorem tri_succ (s : Nat) : tri (s + 1) = tri s + (s + 1) := rfl

theorem Recursive1.tri : Recursive1 Rcat.tri :=
  Recursive1.natIter 0 (Recursive2.comp2 Recursive2.add (show Recursive2 fun _ b => b from RecursiveV.proj 1)
    (Recursive2.comp2 Recursive2.add (show Recursive2 fun a _ => a from RecursiveV.proj 0)
      (Recursive2.ofFst (Recursive1.const 1))))

theorem le_tri (s : Nat) : s ≤ tri s := by
  cases s with
  | zero => exact Nat.le_refl 0
  | succ s => rw [tri_succ]; omega

theorem tri_mono {s t : Nat} (h : s ≤ t) : tri s ≤ tri t := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h' | h'
    · have := ih (by omega)
      rw [tri_succ]; omega
    · have : s = t + 1 := by omega
      subst this; exact Nat.le_refl _

/-- Cantor pairing: `cp a b = tri (a+b) + b`, a bijection ℕ×ℕ → ℕ. -/
def cp (a b : Nat) : Nat := tri (a + b) + b

theorem Recursive2.cp : Recursive2 Rcat.cp := by
  have h : Recursive2 fun a b => Rcat.tri (a + b) + b :=
    Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 (Recursive2.ofSnd Recursive1.tri) (show Recursive2 fun a _ => a from RecursiveV.proj 0) Recursive2.add)
      (show Recursive2 fun _ b => b from RecursiveV.proj 1)
  exact h.congr fun _ _ => rfl

/-- The "weight" of a code: the least `s` with `c < tri (s+1)`; equals `a+b` for `c = cp a b`. -/
noncomputable def cw (c : Nat) : Nat :=
  theLeast (fun s => c < tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩

theorem cw_lt (c : Nat) : c < tri (cw c + 1) :=
  theLeast_mem (fun s => c < tri (s + 1)) _

theorem tri_cw_le (c : Nat) : tri (cw c) ≤ c := by
  cases hcw : cw c with
  | zero => rw [tri_zero]; omega
  | succ s =>
    have hmin : ¬c < tri (s + 1) :=
      theLeast_min (fun s => c < tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩ s
        (show s < cw c by omega)
    omega

theorem cw_cp (a b : Nat) : cw (cp a b) = a + b := by
  refine theLeast_unique _ _ ?_ ?_
  · show cp a b < tri (a + b + 1)
    rw [tri_succ]
    unfold cp
    omega
  · intro s hs
    show ¬cp a b < tri (s + 1)
    have : tri (s + 1) ≤ tri (a + b) := tri_mono (by omega)
    unfold cp
    omega

/-- Second Cantor projection. -/
noncomputable def csnd (c : Nat) : Nat := c - tri (cw c)

/-- First Cantor projection. -/
noncomputable def cfst (c : Nat) : Nat := cw c - csnd c

theorem csnd_cp (a b : Nat) : csnd (cp a b) = b := by
  unfold csnd
  rw [cw_cp]
  unfold cp
  omega

theorem cfst_cp (a b : Nat) : cfst (cp a b) = a := by
  unfold cfst
  rw [csnd_cp, cw_cp]
  omega

theorem csnd_le_cw (c : Nat) : csnd c ≤ cw c := by
  have h1 := cw_lt c
  have h2 := tri_cw_le c
  rw [tri_succ] at h1
  unfold csnd
  omega

theorem cp_surj (c : Nat) : cp (cfst c) (csnd c) = c := by
  have h1 := tri_cw_le c
  have h2 := csnd_le_cw c
  unfold cp cfst
  have : cw c - csnd c + csnd c = cw c := by omega
  rw [this]
  unfold csnd
  omega

theorem Recursive1.cw : Recursive1 Rcat.cw := by
  refine Recursive1.mu (t := fun s c => (c + 1) - Rcat.tri (s + 1)) ?_ ?_ ?_
  · exact Recursive2.comp2 Recursive2.sub
      (Recursive2.comp2 Recursive2.add (show Recursive2 fun _ b => b from RecursiveV.proj 1) (Recursive2.ofFst (Recursive1.const 1)))
      (Recursive2.ofFst (Recursive1.comp (f := fun s => s + 1)
        (Recursive1.add (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const 1)) Recursive1.tri))
  · intro c
    show (c + 1) - Rcat.tri (Rcat.cw c + 1) = 0
    have := cw_lt c
    omega
  · intro c s hs
    show (c + 1) - Rcat.tri (s + 1) ≠ 0
    have hmin : ¬c < Rcat.tri (s + 1) :=
      theLeast_min (fun s => c < Rcat.tri (s + 1)) ⟨c, by have := le_tri (c + 1); omega⟩ s hs
    omega

theorem Recursive1.csnd : Recursive1 Rcat.csnd :=
  (Recursive1.sub (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.comp Recursive1.cw Recursive1.tri)).congr
    fun _ => rfl

theorem Recursive1.cfst : Recursive1 Rcat.cfst :=
  (Recursive1.sub Recursive1.cw Recursive1.csnd).congr fun _ => rfl

/-! ### Division and remainder by a positive constant -/

theorem Recursive1.divConst (m : Nat) : Recursive1 fun c => c / (m + 1) := by
  refine Recursive1.mu (t := fun q c => (c + 1) - (m + 1) * (q + 1)) ?_ ?_ ?_
  · exact Recursive2.comp2 Recursive2.sub
      (Recursive2.comp2 Recursive2.add (show Recursive2 fun _ b => b from RecursiveV.proj 1) (Recursive2.ofFst (Recursive1.const 1)))
      (Recursive2.comp2 Recursive2.mul (Recursive2.ofFst (Recursive1.const (m + 1)))
        (Recursive2.comp2 Recursive2.add (show Recursive2 fun a _ => a from RecursiveV.proj 0)
          (Recursive2.ofFst (Recursive1.const 1))))
  · intro c
    show (c + 1) - (m + 1) * (c / (m + 1) + 1) = 0
    have h1 := Nat.div_add_mod c (m + 1)
    have h2 := Nat.mod_lt c (y := m + 1) (by omega)
    have h3 : (m + 1) * (c / (m + 1) + 1) = (m + 1) * (c / (m + 1)) + (m + 1) :=
      Nat.mul_succ _ _
    omega
  · intro c q hq
    show (c + 1) - (m + 1) * (q + 1) ≠ 0
    have h1 : (q + 1) * (m + 1) ≤ (c / (m + 1)) * (m + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (c / (m + 1)) * (m + 1) ≤ c := Nat.div_mul_le_self c (m + 1)
    have h3 : (m + 1) * (q + 1) = (q + 1) * (m + 1) := Nat.mul_comm _ _
    omega

theorem Recursive1.modConst (m : Nat) : Recursive1 fun c => c % (m + 1) := by
  have h : Recursive1 fun c => c - (c / (m + 1)) * (m + 1) :=
    Recursive1.sub (show Recursive1 fun n => n from RecursiveV.proj 0)
      (Recursive1.mul (Recursive1.divConst m) (Recursive1.const (m + 1)))
  refine h.congr fun c => ?_
  have h1 := Nat.div_add_mod c (m + 1)
  have h3 : (m + 1) * (c / (m + 1)) = (c / (m + 1)) * (m + 1) := Nat.mul_comm _ _
  omega

/-! ## Part 3: the category R

  Objects: extended naturals `some n` (the finite ordinal `n`, carrier `Fin n`)
  and `none` (ω, carrier ℕ).  A morphism is a function between the carriers that
  is recursive; per the book, ANY function from a finite natural number counts
  as recursive, so the condition only bites on domain ω. -/

/-- The extended natural numbers 0, 1, 2, …, ω — the objects of R. -/
def ExtNat : Type := Option Nat

/-- The finite ordinal ω-object.  Book notation: ω. -/
def omega : ExtNat := none

/-- The finite ordinal object `n = {0, …, n-1}` (von Neumann). -/
def fin (n : Nat) : ExtNat := some n

/-- Carrier of an extended natural: `El (some n) = Fin n`, `El ω = ℕ`.
    (`@[reducible]` so that arithmetic on `El none` elaborates as on `Nat`.) -/
@[reducible] def El : ExtNat → Type := fun α =>
  match α with
  | some n => Fin n
  | none => Nat

/-- Uniform embedding of every carrier into ℕ. -/
def toNat : {α : ExtNat} → El α → Nat := fun {α} =>
  match α with
  | some _ => Fin.val
  | none => id

theorem toNat_inj : ∀ {α : ExtNat} {a b : El α}, toNat a = toNat b → a = b := by
  intro α
  match α with
  | some n => intro a b h; exact Fin.ext h
  | none => intro a b h; exact h

theorem toNat_lt {n : Nat} (a : El (some n)) : toNat a < n := a.isLt

/-- The morphism condition: from ω the induced ℕ→ℕ function must be recursive;
    from a finite natural everything is a morphism (book convention). -/
def IsMor : (α β : ExtNat) → (El α → El β) → Prop := fun α _ f =>
  match α, f with
  | some _, _ => True
  | none, f => Recursive1 fun k => toNat (f k)

/-- Morphisms of R: recursive functions between the carriers. -/
def Mor (α β : ExtNat) : Type := {f : El α → El β // IsMor α β f}

theorem Mor.ext {α β : ExtNat} {f g : Mor α β} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (funext h)

theorem isMor_finite {n : Nat} {β : ExtNat} (f : El (some n) → El β) : IsMor (some n) β f :=
  trivial

/-- Any function ω → Fin m whose values are recursive composed with any table is a
    morphism-composite: the workhorse for composing through a finite object. -/
theorem recursive1_finComp {m : Nat} {f : Nat → Fin m} (hf : Recursive1 fun k => (f k).val)
    (t : Fin m → Nat) : Recursive1 fun k => t (f k) := by
  have htab := Recursive1.finTable m t
  have hcomp := Recursive1.comp (f := fun k => (f k).val)
    (g := fun j => if h : j < m then t ⟨j, h⟩ else 0) hf htab
  refine hcomp.congr fun k => ?_
  show (if h : (f k).val < m then t ⟨(f k).val, h⟩ else 0) = t (f k)
  rw [dif_pos (f k).isLt]

/-- Composites of morphisms are morphisms. -/
theorem isMor_comp {α β γ : ExtNat} (f : Mor α β) (g : Mor β γ) :
    IsMor α γ fun a => g.1 (f.1 a) := by
  match α with
  | some n => exact trivial
  | none =>
    match β with
    | none =>
      exact Recursive1.comp (f := fun k => toNat (f.1 k)) (g := fun k => toNat (g.1 k)) f.2 g.2
    | some m =>
      exact recursive1_finComp (f := fun k => f.1 k) f.2 fun j => toNat (g.1 j)

instance : Cat ExtNat where
  Hom := Mor
  id α := ⟨fun a => a, by
    match α with
    | some n => exact trivial
    | none => exact (show Recursive1 fun n => n from RecursiveV.proj 0)⟩
  comp f g := ⟨fun a => g.1 (f.1 a), isMor_comp f g⟩
  id_comp f := Mor.ext fun _ => rfl
  comp_id f := Mor.ext fun _ => rfl
  assoc f g h := Mor.ext fun _ => rfl

/-- Pointwise evaluation of a composite. -/
theorem comp_fn {α β γ : ExtNat} (f : α ⟶ β) (g : β ⟶ γ) (a : El α) :
    (f ≫ g).1 a = g.1 (f.1 a) := rfl

theorem id_fn {α : ExtNat} (a : El α) : (Cat.id α).1 a = a := rfl

/-- Pointwise consequence of a morphism equation. -/
theorem Mor.congr {α β : ExtNat} {f g : α ⟶ β} (h : f = g) (a : El α) : f.1 a = g.1 a := by
  rw [h]

/-! ## Part 4: R is cartesian — terminator and binary products

  The terminator is the ordinal 1.  The product of two extended naturals must
  again be an extended natural: `n×m = n*m`, `ω×ω ≅ ω` by Cantor pairing,
  `(n+1)×ω ≅ ω ≅ ω×(m+1)` by division with remainder, and `0×α = 0 = α×0`. -/

instance : HasTerminal ExtNat where
  one := some 1
  trm X := ⟨fun _ => ⟨0, Nat.one_pos⟩, by
    match X with
    | some n => exact trivial
    | none => exact Recursive1.const 0⟩
  uniq f g := Mor.ext fun a => by
    apply toNat_inj
    have h1 : toNat (f.1 a) < 1 := toNat_lt _
    have h2 : toNat (g.1 a) < 1 := toNat_lt _
    omega

/-- Product data for a pair of extended naturals: a product object together with a
    recursive pairing bijection.  `encN` is the pairing seen through `toNat`; its
    recursiveness makes the universal `pair` map a morphism. -/
structure ProdData (α β : ExtNat) where
  obj : ExtNat
  enc : El α → El β → El obj
  dec₁ : El obj → El α
  dec₂ : El obj → El β
  dec₁_enc : ∀ a b, dec₁ (enc a b) = a
  dec₂_enc : ∀ a b, dec₂ (enc a b) = b
  enc_dec : ∀ c, enc (dec₁ c) (dec₂ c) = c
  dec₁_mor : IsMor obj α dec₁
  dec₂_mor : IsMor obj β dec₂
  encN : Nat → Nat → Nat
  encN_rec : Recursive2 encN
  encN_spec : ∀ a b, toNat (enc a b) = encN (toNat a) (toNat b)

/-- `n × m = n*m` (finite × finite): `(i,j) ↦ i*m + j`. -/
def prodFinFin (n m : Nat) : ProdData (some n) (some m) where
  obj := some (n * m)
  enc i j := ⟨i.val * m + j.val, by
    have h1 : i.val * m + j.val < (i.val + 1) * m := by
      rw [Nat.succ_mul]
      have := j.isLt
      omega
    have h2 : (i.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m i.isLt
    omega⟩
  dec₁ c := ⟨c.val / m, by
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        have := c.isLt
        omega
      · exact h
    exact (Nat.div_lt_iff_lt_mul hm).mpr c.isLt⟩
  dec₂ c := ⟨c.val % m, by
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        have := c.isLt
        omega
      · exact h
    exact Nat.mod_lt _ hm⟩
  dec₁_enc i j := by
    apply Fin.ext
    show (i.val * m + j.val) / m = i.val
    rw [Nat.mul_comm i.val m, Nat.mul_add_div (by have := j.isLt; omega)]
    rw [Nat.div_eq_of_lt j.isLt]
    omega
  dec₂_enc i j := by
    apply Fin.ext
    show (i.val * m + j.val) % m = j.val
    rw [Nat.mul_comm i.val m, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt j.isLt
  enc_dec c := by
    apply Fin.ext
    show (c.val / m) * m + c.val % m = c.val
    have h1 := Nat.div_add_mod c.val m
    have h2 : m * (c.val / m) = (c.val / m) * m := Nat.mul_comm _ _
    omega
  dec₁_mor := trivial
  dec₂_mor := trivial
  encN a b := a * m + b
  encN_rec := Recursive2.comp2 Recursive2.add
    (Recursive2.comp2 Recursive2.mul (show Recursive2 fun a _ => a from RecursiveV.proj 0) (Recursive2.ofFst (Recursive1.const m)))
    (show Recursive2 fun _ b => b from RecursiveV.proj 1)
  encN_spec _ _ := rfl

/-- `0 × ω = 0`. -/
def prodZeroOmega (n : Nat) (h : n = 0) : ProdData (some n) none where
  obj := some 0
  enc a _ := h ▸ a
  dec₁ c := c.elim0
  dec₂ c := c.elim0
  dec₁_enc a _ := (h ▸ a).elim0
  dec₂_enc a _ := (h ▸ a).elim0
  enc_dec c := c.elim0
  dec₁_mor := trivial
  dec₂_mor := trivial
  encN _ _ := 0
  encN_rec := RecursiveV.const 2 0
  encN_spec a _ := (h ▸ a).elim0

/-- Helper (plain-Nat, so `omega` applies): quotient of `k*(d+1) + v` by `d+1`. -/
theorem mulAdd_div (d k v : Nat) (hv : v < d + 1) : (k * (d + 1) + v) / (d + 1) = k := by
  rw [Nat.mul_comm k (d + 1), Nat.mul_add_div (Nat.succ_pos d), Nat.div_eq_of_lt hv]
  omega

/-- Helper (plain-Nat): remainder of `k*(d+1) + v` by `d+1`. -/
theorem mulAdd_mod (d k v : Nat) (hv : v < d + 1) : (k * (d + 1) + v) % (d + 1) = v := by
  rw [Nat.mul_comm k (d + 1), Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hv

/-- Helper (plain-Nat): division with remainder reassembles. -/
theorem div_mul_add_mod (d c : Nat) : (c / (d + 1)) * (d + 1) + c % (d + 1) = c := by
  have h1 := Nat.div_add_mod c (d + 1)
  have h2 : (d + 1) * (c / (d + 1)) = (c / (d + 1)) * (d + 1) := Nat.mul_comm _ _
  omega

/-- `(n+1) × ω = ω`: `(i,k) ↦ k*(n+1) + i` (division with remainder by `n+1`). -/
noncomputable def prodFinOmega (n : Nat) : ProdData (some (n + 1)) none where
  obj := none
  enc i k := k * (n + 1) + i.val
  dec₁ c := ⟨c % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
  dec₂ c := c / (n + 1)
  dec₁_enc i k := Fin.ext (mulAdd_mod n k i.val i.isLt)
  dec₂_enc i k := mulAdd_div n k i.val i.isLt
  enc_dec c := div_mul_add_mod n c
  dec₁_mor := Recursive1.modConst n
  dec₂_mor := Recursive1.divConst n
  encN a b := b * (n + 1) + a
  encN_rec := Recursive2.comp2 Recursive2.add
    (Recursive2.comp2 Recursive2.mul (show Recursive2 fun _ b => b from RecursiveV.proj 1) (Recursive2.ofFst (Recursive1.const (n + 1))))
    (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  encN_spec _ _ := rfl

/-- `ω × 0 = 0`. -/
def prodOmegaZero (m : Nat) (h : m = 0) : ProdData none (some m) where
  obj := some 0
  enc _ b := h ▸ b
  dec₁ c := c.elim0
  dec₂ c := c.elim0
  dec₁_enc _ b := (h ▸ b).elim0
  dec₂_enc _ b := (h ▸ b).elim0
  enc_dec c := c.elim0
  dec₁_mor := trivial
  dec₂_mor := trivial
  encN _ _ := 0
  encN_rec := RecursiveV.const 2 0
  encN_spec _ b := (h ▸ b).elim0

/-- `ω × (m+1) = ω`: `(k,j) ↦ k*(m+1) + j`. -/
noncomputable def prodOmegaFin (m : Nat) : ProdData none (some (m + 1)) where
  obj := none
  enc k j := k * (m + 1) + j.val
  dec₁ c := c / (m + 1)
  dec₂ c := ⟨c % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
  dec₁_enc k j := mulAdd_div m k j.val j.isLt
  dec₂_enc k j := Fin.ext (mulAdd_mod m k j.val j.isLt)
  enc_dec c := div_mul_add_mod m c
  dec₁_mor := Recursive1.divConst m
  dec₂_mor := Recursive1.modConst m
  encN a b := a * (m + 1) + b
  encN_rec := Recursive2.comp2 Recursive2.add
    (Recursive2.comp2 Recursive2.mul (show Recursive2 fun a _ => a from RecursiveV.proj 0) (Recursive2.ofFst (Recursive1.const (m + 1))))
    (show Recursive2 fun _ b => b from RecursiveV.proj 1)
  encN_spec _ _ := rfl

/-- `ω × ω = ω` by the Cantor pairing (recursive in both directions). -/
noncomputable def prodOmegaOmega : ProdData none none where
  obj := none
  enc := cp
  dec₁ := cfst
  dec₂ := csnd
  dec₁_enc := cfst_cp
  dec₂_enc := csnd_cp
  enc_dec c := cp_surj c
  dec₁_mor := Recursive1.cfst
  dec₂_mor := Recursive1.csnd
  encN := cp
  encN_rec := Recursive2.cp
  encN_spec _ _ := rfl

/-- The product of any two extended naturals. -/
noncomputable def prodData : (α β : ExtNat) → ProdData α β
  | some n, some m => prodFinFin n m
  | some 0, none => prodZeroOmega 0 rfl
  | some (n + 1), none => prodFinOmega n
  | none, some 0 => prodOmegaZero 0 rfl
  | none, some (m + 1) => prodOmegaFin m
  | none, none => prodOmegaOmega

/-- The universal pairing map is a morphism (via `encN`). -/
theorem pair_isMor {X α β : ExtNat} (pd : ProdData α β) (f : X ⟶ α) (g : X ⟶ β) :
    IsMor X pd.obj fun w => pd.enc (f.1 w) (g.1 w) := by
  match X with
  | some n => exact trivial
  | none =>
    have h : Recursive1 fun k => pd.encN (toNat (f.1 k)) (toNat (g.1 k)) :=
      Recursive1.comp2 pd.encN_rec f.2 g.2
    exact h.congr fun k => (pd.encN_spec _ _).symm

noncomputable instance : HasBinaryProducts ExtNat where
  prod α β := (prodData α β).obj
  fst {α β} := ⟨(prodData α β).dec₁, (prodData α β).dec₁_mor⟩
  snd {α β} := ⟨(prodData α β).dec₂, (prodData α β).dec₂_mor⟩
  pair {X α β} f g := ⟨fun w => (prodData α β).enc (f.1 w) (g.1 w), pair_isMor _ f g⟩
  fst_pair {X α β} f g := Mor.ext fun w => (prodData α β).dec₁_enc _ _
  snd_pair {X α β} f g := Mor.ext fun w => (prodData α β).dec₂_enc _ _
  pair_uniq {X α β} f g h h₁ h₂ := Mor.ext fun w => by
    have e1 : (prodData α β).dec₁ (h.1 w) = f.1 w := Mor.congr h₁ w
    have e2 : (prodData α β).dec₂ (h.1 w) = g.1 w := Mor.congr h₂ w
    calc h.1 w = (prodData α β).enc ((prodData α β).dec₁ (h.1 w)) ((prodData α β).dec₂ (h.1 w)) :=
          ((prodData α β).enc_dec _).symm
      _ = (prodData α β).enc (f.1 w) (g.1 w) := by rw [e1, e2]

/-! ## Part 5: R has equalizers

  The equalizer of `x, y : α → β` is the decidable subset `{i | x i = y i}` of the
  carrier of `α`, re-presented as an extended natural: its increasing enumeration
  is a recursive mono into `α`.  If the subset is bounded the equalizer object is
  its (finite) size; otherwise it is ω and the enumeration is computed by genuine
  unbounded μ-search.  The universal lift is the rank function (count of members
  below), recursive by primitive recursion. -/

/-- Support test: is `u` the code of an element of the carrier of `α`? -/
def suppChi : ExtNat → Nat → Bool
  | some n, u => decide (u < n)
  | none, _ => true

@[simp] theorem suppChi_some (n u : Nat) : suppChi (some n) u = decide (u < n) := rfl

@[simp] theorem suppChi_none (u : Nat) : suppChi none u = true := rfl

/-- The element of `El α` coded by `u` (given the support test). -/
def elOf : {α : ExtNat} → (u : Nat) → suppChi α u = true → El α := fun {α} =>
  match α with
  | some _ => fun u h => ⟨u, of_decide_eq_true h⟩
  | none => fun u _ => u

theorem toNat_elOf : ∀ {α : ExtNat} (u : Nat) (h : suppChi α u = true), toNat (elOf u h) = u := by
  intro α
  match α with
  | some n => intro u h; rfl
  | none => intro u h; rfl

theorem suppChi_toNat : ∀ {α : ExtNat} (a : El α), suppChi α (toNat a) = true := by
  intro α
  match α with
  | some n => intro a; exact decide_eq_true a.isLt
  | none => intro a; rfl

/-- A morphism as a ℕ→ℕ function (0 outside the support). -/
def morN : {α β : ExtNat} → Mor α β → Nat → Nat := fun {α _} =>
  match α with
  | some n => fun x u => if h : u < n then toNat (x.1 ⟨u, h⟩) else 0
  | none => fun x u => toNat (x.1 u)

theorem morN_rec {α β : ExtNat} (x : Mor α β) : Recursive1 (morN x) := by
  match α with
  | some n => exact Recursive1.finTable n fun i => toNat (x.1 i)
  | none => exact x.2

theorem morN_spec : ∀ {α β : ExtNat} (x : Mor α β) (a : El α), morN x (toNat a) = toNat (x.1 a) := by
  intro α
  match α with
  | some n =>
    intro β x a
    show (if h : a.val < n then toNat (x.1 ⟨a.val, h⟩) else 0) = toNat (x.1 a)
    rw [dif_pos a.isLt]
  | none => intro β x a; rfl

/-- The agreement set of `x, y : α → β` as a Boolean predicate on codes. -/
def agreeChi {α β : ExtNat} (x y : Mor α β) : Nat → Bool := fun u =>
  suppChi α u && (morN x u == morN y u)

theorem agreeChi_supp {α β : ExtNat} {x y : Mor α β} {u : Nat}
    (h : agreeChi x y u = true) : suppChi α u = true :=
  (Bool.and_eq_true_iff.mp h).1

theorem agreeChi_toNat {α β : ExtNat} (x y : Mor α β) (a : El α) :
    agreeChi x y (toNat a) = true ↔ x.1 a = y.1 a := by
  unfold agreeChi
  rw [suppChi_toNat a, Bool.true_and, morN_spec x a, morN_spec y a]
  constructor
  · intro h
    exact toNat_inj (beq_iff_eq.mp h)
  · intro h
    rw [h]
    exact beq_self_eq_true _

theorem agreeChi_elOf {α β : ExtNat} (x y : Mor α β) {u : Nat}
    (h : agreeChi x y u = true) :
    x.1 (elOf u (agreeChi_supp h)) = y.1 (elOf u (agreeChi_supp h)) := by
  have := (agreeChi_toNat x y (elOf u (agreeChi_supp h)))
  rw [toNat_elOf] at this
  exact this.mp h

/-- The numeric characteristic function of the agreement set is recursive. -/
theorem agreeChi_rec {α β : ExtNat} (x y : Mor α β) :
    Recursive1 fun u => if agreeChi x y u then 1 else 0 := by
  have hsupp : Recursive1 fun u => if suppChi α u then 1 else 0 := by
    match α with
    | some n =>
      have htab := Recursive1.finTable n fun _ => 1
      refine htab.congr fun u => ?_
      rw [suppChi_some]
      by_cases h : u < n
      · rw [dif_pos h, if_pos (decide_eq_true h)]
      · rw [dif_neg h, if_neg (by simpa using h)]
    | none => exact (Recursive1.const 1).congr fun u => rfl
  have heq : Recursive1 fun u => eqInd (morN x u) (morN y u) :=
    Recursive1.comp2 Recursive2.eqInd (morN_rec x) (morN_rec y)
  have h := Recursive1.mul hsupp heq
  refine h.congr fun u => ?_
  unfold agreeChi
  by_cases hs : suppChi α u = true
  · rw [hs, Bool.true_and, if_pos rfl, Nat.one_mul]
    by_cases hm : morN x u = morN y u
    · rw [eqInd_eq hm, if_pos (by rw [hm]; exact beq_self_eq_true _)]
    · rw [eqInd_ne hm, if_neg (by
        intro hc
        exact hm (beq_iff_eq.mp hc))]
  · have hs' : suppChi α u = false := by
      cases h' : suppChi α u
      · rfl
      · exact absurd h' hs
    rw [hs', if_neg (by simp), Bool.false_and, if_neg (by simp), Nat.zero_mul]

/-! ### Rank and enumeration of a Boolean subset of ℕ -/

/-- `rankOf χ v` = number of members of `{i | χ i}` below `v`. -/
def rankOf (χ : Nat → Bool) : Nat → Nat := natIter 0 fun v r => r + (if χ v then 1 else 0)

@[simp] theorem rankOf_zero (χ : Nat → Bool) : rankOf χ 0 = 0 := rfl

theorem rankOf_succ (χ : Nat → Bool) (v : Nat) :
    rankOf χ (v + 1) = rankOf χ v + (if χ v then 1 else 0) := rfl

theorem rankOf_rec {χ : Nat → Bool} (h : Recursive1 fun v => if χ v then 1 else 0) :
    Recursive1 (rankOf χ) :=
  Recursive1.natIter 0 (Recursive2.comp2 Recursive2.add (show Recursive2 fun _ b => b from RecursiveV.proj 1) (Recursive2.ofFst h))

theorem rankOf_mono (χ : Nat → Bool) {v w : Nat} (h : v ≤ w) : rankOf χ v ≤ rankOf χ w := by
  induction w with
  | zero =>
    have : v = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ w ih =>
    rcases Nat.lt_or_ge v (w + 1) with h' | h'
    · have := ih (by omega)
      rw [rankOf_succ]
      omega
    · have : v = w + 1 := by omega
      subst this; exact Nat.le_refl _

theorem rankOf_lt_of_mem (χ : Nat → Bool) {v w : Nat} (hv : χ v = true) (hvw : v < w) :
    rankOf χ v < rankOf χ w := by
  have h1 : rankOf χ (v + 1) = rankOf χ v + 1 := by
    rw [rankOf_succ, if_pos hv]
  have h2 : rankOf χ (v + 1) ≤ rankOf χ w := rankOf_mono χ (by omega)
  omega

theorem rankOf_inj_mem (χ : Nat → Bool) {v w : Nat} (hv : χ v = true) (hw : χ w = true)
    (h : rankOf χ v = rankOf χ w) : v = w := by
  rcases Nat.lt_trichotomy v w with h' | h' | h'
  · exact absurd h (by have := rankOf_lt_of_mem χ hv h'; omega)
  · exact h'
  · exact absurd h (by have := rankOf_lt_of_mem χ hw h'; omega)

theorem rankOf_surj (χ : Nat → Bool) {k b : Nat} (hk : k < rankOf χ b) :
    ∃ v, v < b ∧ χ v = true ∧ rankOf χ v = k := by
  induction b with
  | zero => rw [rankOf_zero] at hk; omega
  | succ b ih =>
    rw [rankOf_succ] at hk
    by_cases hb : χ b = true
    · rw [if_pos hb] at hk
      rcases Nat.lt_or_ge k (rankOf χ b) with h' | h'
      · obtain ⟨v, h1, h2, h3⟩ := ih h'
        exact ⟨v, by omega, h2, h3⟩
      · have : k = rankOf χ b := by omega
        exact ⟨b, by omega, hb, this.symm⟩
    · rw [if_neg hb] at hk
      obtain ⟨v, h1, h2, h3⟩ := ih (by omega)
      exact ⟨v, by omega, h2, h3⟩

theorem rankOf_unbounded (χ : Nat → Bool) (hunb : ∀ b, ∃ v, b ≤ v ∧ χ v = true) :
    ∀ k, ∃ v, χ v = true ∧ rankOf χ v = k := by
  have grow : ∀ k, ∃ b, k < rankOf χ b := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v, _, hv⟩ := hunb 0
      exact ⟨v + 1, by rw [rankOf_succ, if_pos hv]; omega⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨v, hbv, hv⟩ := hunb b
      refine ⟨v + 1, ?_⟩
      have h1 : rankOf χ b ≤ rankOf χ v := rankOf_mono χ hbv
      rw [rankOf_succ, if_pos hv]
      omega
  intro k
  obtain ⟨b, hb⟩ := grow k
  obtain ⟨v, _, h2, h3⟩ := rankOf_surj χ hb
  exact ⟨v, h2, h3⟩

/-- The `k`-th member (in increasing order) of the subset `{i | χ i}`. -/
noncomputable def enumOf (χ : Nat → Bool) (k : Nat)
    (h : ∃ v, χ v = true ∧ rankOf χ v = k) : Nat :=
  theLeast _ h

/-- The enumeration inverts the rank on members. -/
theorem enumOf_of_mem (χ : Nat → Bool) {u : Nat} (hu : χ u = true)
    (h : ∃ v, χ v = true ∧ rankOf χ v = rankOf χ u) : enumOf χ (rankOf χ u) h = u :=
  rankOf_inj_mem χ (theLeast_mem _ h).1 hu (theLeast_mem _ h).2

/-- The enumeration of an (everywhere-inhabited-rank) recursive subset is recursive —
    genuine unbounded μ-search. -/
theorem enumOf_recursive {χ : Nat → Bool} (ht : Recursive1 fun v => if χ v then 1 else 0)
    (hex : ∀ k, ∃ v, χ v = true ∧ rankOf χ v = k) :
    Recursive1 fun k => enumOf χ k (hex k) := by
  refine Recursive1.mu
    (t := fun v k => (1 - (if χ v then 1 else 0)) + ((rankOf χ v - k) + (k - rankOf χ v)))
    ?_ ?_ ?_
  · exact Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 Recursive2.sub (Recursive2.ofFst (Recursive1.const 1))
        (Recursive2.ofFst ht))
      (Recursive2.comp2 Recursive2.add
        (Recursive2.comp2 Recursive2.sub (Recursive2.ofFst (rankOf_rec ht)) (show Recursive2 fun _ b => b from RecursiveV.proj 1))
        (Recursive2.comp2 Recursive2.sub (show Recursive2 fun _ b => b from RecursiveV.proj 1) (Recursive2.ofFst (rankOf_rec ht))))
  · intro k
    show (1 - (if χ (enumOf χ k (hex k)) then 1 else 0)) +
      ((rankOf χ (enumOf χ k (hex k)) - k) + (k - rankOf χ (enumOf χ k (hex k)))) = 0
    rw [show χ (enumOf χ k (hex k)) = true from (theLeast_mem _ (hex k)).1,
      show rankOf χ (enumOf χ k (hex k)) = k from (theLeast_mem _ (hex k)).2]
    simp
  · intro k i hi
    show (1 - (if χ i then 1 else 0)) + ((rankOf χ i - k) + (k - rankOf χ i)) ≠ 0
    have hmin := theLeast_min (fun v => χ v = true ∧ rankOf χ v = k) (hex k) i hi
    by_cases hχ : χ i = true
    · have hrk : rankOf χ i ≠ k := fun hr => hmin ⟨hχ, hr⟩
      rw [hχ, if_pos rfl]
      omega
    · have hχ' : χ i = false := by
        cases h' : χ i
        · rfl
        · exact absurd h' hχ
      rw [hχ', if_neg (by simp)]
      omega

/-! ### The equalizer of `x, y : α → β` -/

section Equalizer

variable {α β : ExtNat} (x y : α ⟶ β)

/-- The `k`-th member of the agreement set, as an element of `El α`. -/
noncomputable def eqEnum (k : Nat)
    (h : ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k) : El α :=
  elOf (enumOf (agreeChi x y) k h) (agreeChi_supp (theLeast_mem _ h).1)

theorem eqEnum_agree (k : Nat) (h : ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k) :
    x.1 (eqEnum x y k h) = y.1 (eqEnum x y k h) :=
  agreeChi_elOf x y (theLeast_mem _ h).1

theorem eqEnum_inj {k k' : Nat}
    (h : ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k)
    (h' : ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k')
    (heq : eqEnum x y k h = eqEnum x y k' h') : k = k' := by
  have h1 : enumOf (agreeChi x y) k h = enumOf (agreeChi x y) k' h' := by
    rw [← show toNat (eqEnum x y k h) = enumOf (agreeChi x y) k h from toNat_elOf _ _,
      ← show toNat (eqEnum x y k' h') = enumOf (agreeChi x y) k' h' from toNat_elOf _ _, heq]
  rw [← show rankOf (agreeChi x y) (enumOf (agreeChi x y) k h) = k from (theLeast_mem _ h).2,
    ← show rankOf (agreeChi x y) (enumOf (agreeChi x y) k' h') = k' from (theLeast_mem _ h').2, h1]

/-- Enumerating the rank of an agreeing element recovers it. -/
theorem eqEnum_rank {a : El α} (ha : agreeChi x y (toNat a) = true)
    (h : ∃ v, agreeChi x y v = true ∧
      rankOf (agreeChi x y) v = rankOf (agreeChi x y) (toNat a)) :
    eqEnum x y (rankOf (agreeChi x y) (toNat a)) h = a := by
  apply toNat_inj
  rw [show toNat (eqEnum x y (rankOf (agreeChi x y) (toNat a)) h) =
    enumOf (agreeChi x y) (rankOf (agreeChi x y) (toNat a)) h from toNat_elOf _ _]
  exact enumOf_of_mem _ ha _

/-- The lift function (the rank of the code) is a morphism from any cone domain. -/
theorem eqLift_isMor {X γ : ExtNat} (q : X ⟶ α) (g : El X → El γ)
    (hg : ∀ w, toNat (g w) = rankOf (agreeChi x y) (toNat (q.1 w))) :
    IsMor X γ g := by
  match X, q, g, hg with
  | some d, q, g, hg => exact trivial
  | none, q, g, hg =>
    have h : Recursive1 fun w => rankOf (agreeChi x y) (toNat (q.1 w)) :=
      Recursive1.comp (f := fun w => toNat (q.1 w)) q.2 (rankOf_rec (agreeChi_rec x y))
    exact h.congr fun w => (hg w).symm

/-- Cone codes agree. -/
theorem cone_agree (c : EqualizerCone x y) (w : El c.dom) :
    agreeChi x y (toNat (c.map.1 w)) = true :=
  (agreeChi_toNat x y (c.map.1 w)).mpr (Mor.congr c.eq w)

/-- Bounded (finite) case: the agreement set lies below `b`; the equalizer object
    is the finite ordinal `rankOf χ b`, with the increasing enumeration as the
    (automatically recursive: finite domain) equalizer map. -/
noncomputable def eqFinite (b : Nat) (hb : ∀ v, agreeChi x y v = true → v < b) :
    HasEqualizer x y :=
  have hexF : ∀ k : Fin (rankOf (agreeChi x y) b),
      ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k.val := fun k =>
    let ⟨v, _, h2, h3⟩ := rankOf_surj (agreeChi x y) k.isLt
    ⟨v, h2, h3⟩
  have liftLt : ∀ (c : EqualizerCone x y) (w : El c.dom),
      rankOf (agreeChi x y) (toNat (c.map.1 w)) < rankOf (agreeChi x y) b := fun c w =>
    rankOf_lt_of_mem _ (cone_agree x y c w) (hb _ (cone_agree x y c w))
  { cone := ⟨some (rankOf (agreeChi x y) b),
      ⟨fun k => eqEnum x y k.val (hexF k), trivial⟩,
      Mor.ext fun k => eqEnum_agree x y k.val (hexF k)⟩
    lift := fun c =>
      ⟨fun w => ⟨rankOf (agreeChi x y) (toNat (c.map.1 w)), liftLt c w⟩,
        eqLift_isMor x y c.map _ fun _ => rfl⟩
    fac := fun c => Mor.ext fun w =>
      eqEnum_rank x y (cone_agree x y c w) _
    uniq := fun c m hm => Mor.ext fun w => by
      have h1 : eqEnum x y (m.1 w).val (hexF (m.1 w)) = c.map.1 w := Mor.congr hm w
      have h2 : eqEnum x y (rankOf (agreeChi x y) (toNat (c.map.1 w)))
          (hexF ⟨_, liftLt c w⟩) = c.map.1 w :=
        eqEnum_rank x y (cone_agree x y c w) _
      exact Fin.ext (eqEnum_inj x y _ _ (h1.trans h2.symm)) }

/-- Unbounded (infinite) case: the equalizer object is ω; the increasing
    enumeration is recursive by unbounded μ-search. -/
noncomputable def eqInfinite (hunb : ∀ b, ∃ v, b ≤ v ∧ agreeChi x y v = true) :
    HasEqualizer x y :=
  have hex : ∀ k, ∃ v, agreeChi x y v = true ∧ rankOf (agreeChi x y) v = k :=
    rankOf_unbounded _ hunb
  have mapFn_mor : IsMor none α fun k => eqEnum x y k (hex k) :=
    (enumOf_recursive (agreeChi_rec x y) hex).congr fun k =>
      (toNat_elOf _ _ : toNat (eqEnum x y k (hex k)) = _).symm
  { cone := ⟨none, ⟨fun k => eqEnum x y k (hex k), mapFn_mor⟩,
      Mor.ext fun k => eqEnum_agree x y k (hex k)⟩
    lift := fun c =>
      ⟨fun w => rankOf (agreeChi x y) (toNat (c.map.1 w)),
        eqLift_isMor x y c.map _ fun _ => rfl⟩
    fac := fun c => Mor.ext fun w =>
      eqEnum_rank x y (cone_agree x y c w) _
    uniq := fun c m hm => Mor.ext fun w => by
      have h1 : eqEnum x y (m.1 w) (hex (m.1 w)) = c.map.1 w := Mor.congr hm w
      have h2 : eqEnum x y (rankOf (agreeChi x y) (toNat (c.map.1 w)))
          (hex _) = c.map.1 w :=
        eqEnum_rank x y (cone_agree x y c w) _
      exact eqEnum_inj x y _ _ (h1.trans h2.symm) }

open Classical in
/-- The equalizer of `x, y`: finite or ω according to whether the agreement set
    is bounded (a classically-decided case split; `Classical.choice` is in budget). -/
noncomputable def eqOf : HasEqualizer x y :=
  if h : ∃ b, ∀ v, agreeChi x y v = true → v < b then
    eqFinite x y h.choose h.choose_spec
  else
    eqInfinite x y fun b => by
      apply Classical.byContradiction
      intro hno
      exact h ⟨b, fun v hv => by
        apply Classical.byContradiction
        intro hvb
        exact hno ⟨v, by omega, hv⟩⟩

end Equalizer

noncomputable instance : HasEqualizers ExtNat := ⟨fun _ _ x y => eqOf x y⟩

/-- **R is cartesian** (first half of §1.572's claim). -/
noncomputable instance : CartesianCategory ExtNat := {}

/-! ## Part 6: R is AC regular (§1.572)

  Given `x : α → β` define `e : α → α` by `e(n) = min{ i ≤ n | x(i) = x(n) }`.
  Then `e² = e`, `ex = x`, and `e` and `x` have the same level, so §1.571
  (`ac_factorization_via_idempotent`) applies: every morphism factors as a
  left-invertible followed by a monic.  From the factorization we CONSTRUCT
  images (Freyd: "the image of x has been constructed, somehow, as a subobject
  of A"), pullback-transfer of covers, and choice/projectivity of all objects. -/

/-- The least index with the same `F`-value as `k` (exists: `k` itself qualifies).
    Since the witness `k` bounds it, this is the book's `min{ i ≤ n | x(i) = x(n) }`. -/
noncomputable def leastAgree (F : Nat → Nat) (k : Nat) : Nat :=
  theLeast (fun i => F i = F k) ⟨k, rfl⟩

theorem leastAgree_agree (F : Nat → Nat) (k : Nat) : F (leastAgree F k) = F k :=
  theLeast_mem (fun i => F i = F k) ⟨k, rfl⟩

theorem leastAgree_congr (F : Nat → Nat) {j k : Nat} (h : F j = F k) :
    leastAgree F j = leastAgree F k := by
  refine theLeast_unique _ _ ?_ ?_
  · show F (leastAgree F k) = F j
    rw [leastAgree_agree F k, h]
  · intro i hi
    show ¬F i = F j
    rw [h]
    exact theLeast_min (fun i => F i = F k) ⟨k, rfl⟩ i hi

theorem leastAgree_idem (F : Nat → Nat) (k : Nat) :
    leastAgree F (leastAgree F k) = leastAgree F k :=
  leastAgree_congr F (leastAgree_agree F k)

/-- Support is downward closed. -/
theorem suppChi_of_le : ∀ {α : ExtNat} {u v : Nat}, u ≤ v → suppChi α v = true →
    suppChi α u = true := by
  intro α
  match α with
  | some n =>
    intro u v huv hv
    exact decide_eq_true (by have := of_decide_eq_true hv; omega)
  | none => intro u v _ _; rfl

/-- §1.572's idempotent: `e(a) = min{ i ≤ a | x(i) = x(a) }` (through the code of `a`). -/
noncomputable def idemFn {α β : ExtNat} (x : Mor α β) : El α → El α := fun a =>
  elOf (leastAgree (morN x) (toNat a))
    (suppChi_of_le (theLeast_le _ _ rfl) (suppChi_toNat a))

/-- `ex = x` pointwise. -/
theorem idemFn_absorb {α β : ExtNat} (x : Mor α β) (a : El α) :
    x.1 (idemFn x a) = x.1 a := by
  apply toNat_inj
  rw [← morN_spec x (idemFn x a), ← morN_spec x a,
    show toNat (idemFn x a) = leastAgree (morN x) (toNat a) from toNat_elOf _ _]
  exact leastAgree_agree (morN x) (toNat a)

/-- `e² = e` pointwise. -/
theorem idemFn_idem {α β : ExtNat} (x : Mor α β) (a : El α) :
    idemFn x (idemFn x a) = idemFn x a := by
  apply toNat_inj
  rw [show toNat (idemFn x (idemFn x a)) = leastAgree (morN x) (toNat (idemFn x a)) from
      toNat_elOf _ _,
    show toNat (idemFn x a) = leastAgree (morN x) (toNat a) from toNat_elOf _ _]
  exact leastAgree_idem _ _

/-- `e` merges exactly as much as `x` does. -/
theorem idemFn_congr {α β : ExtNat} (x : Mor α β) {a b : El α} (h : x.1 a = x.1 b) :
    idemFn x a = idemFn x b := by
  apply toNat_inj
  rw [show toNat (idemFn x a) = leastAgree (morN x) (toNat a) from toNat_elOf _ _,
    show toNat (idemFn x b) = leastAgree (morN x) (toNat b) from toNat_elOf _ _]
  exact leastAgree_congr _ (by rw [morN_spec x a, morN_spec x b, h])

/-- `e` is recursive: unbounded μ-search for the least agreeing index
    (it terminates because the input itself agrees). -/
theorem idemFn_isMor {α β : ExtNat} (x : Mor α β) : IsMor α α (idemFn x) := by
  match α, x with
  | some n, x => exact trivial
  | none, x =>
    have h : Recursive1 fun k => leastAgree (morN x) k := by
      refine Recursive1.mu
        (t := fun i k => (morN x i - morN x k) + (morN x k - morN x i)) ?_ ?_ ?_
      · exact Recursive2.comp2 Recursive2.add
          (Recursive2.comp2 Recursive2.sub (Recursive2.ofFst (morN_rec x))
            (Recursive2.ofSnd (morN_rec x)))
          (Recursive2.comp2 Recursive2.sub (Recursive2.ofSnd (morN_rec x))
            (Recursive2.ofFst (morN_rec x)))
      · intro k
        show (morN x (leastAgree (morN x) k) - morN x k) +
          (morN x k - morN x (leastAgree (morN x) k)) = 0
        rw [leastAgree_agree (morN x) k]
        omega
      · intro k i hi
        show (morN x i - morN x k) + (morN x k - morN x i) ≠ 0
        have := (Classical.choose_spec
          (exists_least (P := fun i => morN x i = morN x k) ⟨k, rfl⟩)).2 i hi
        omega
    exact h.congr fun k => (toNat_elOf _ _ : toNat (idemFn x k) = _).symm

/-- §1.572's idempotent as a morphism of R. -/
noncomputable def eMor {α β : ExtNat} (x : α ⟶ β) : α ⟶ α := ⟨idemFn x, idemFn_isMor x⟩

/-- Generic (any category with pullbacks): if `kp₁(u) ≫ w = kp₂(u) ≫ w` then
    `level(u) ⊂ level(w)` — the kernel-pair comparison is a pullback lift. -/
theorem kernelPairRel_le_of_comm {𝒟 : Type u} [Cat.{v} 𝒟] [HasTerminal 𝒟]
    [HasBinaryProducts 𝒟] [HasPullbacks 𝒟] {A B C : 𝒟} (u : A ⟶ B) (w : A ⟶ C)
    (h : kp₁ (f := u) ≫ w = kp₂ (f := u) ≫ w) :
    (kernelPairRel u) ⊂ (kernelPairRel w) :=
  ⟨⟨(HasPullbacks.has w w).lift ⟨_, kp₁ (f := u), kp₂ (f := u), h⟩,
    kp_lift_p₁ _ _ h, kp_lift_p₂ _ _ h⟩⟩

noncomputable instance : HasPullbacks ExtNat :=
  ⟨fun f g => products_equalizers_implies_pullbacks f g⟩

/-- `e` and `x` have the same level (§1.572; the two `⊂` of §1.571's hypothesis). -/
theorem eMor_same_level {α β : ExtNat} (x : α ⟶ β) :
    (kernelPairRel (eMor x)) ⊂ (kernelPairRel x) ∧
    (kernelPairRel x) ⊂ (kernelPairRel (eMor x)) := by
  constructor
  · refine kernelPairRel_le_of_comm (eMor x) x ?_
    refine Mor.ext fun w => ?_
    show x.1 ((kp₁ (f := eMor x)).1 w) = x.1 ((kp₂ (f := eMor x)).1 w)
    have hsq : idemFn x ((kp₁ (f := eMor x)).1 w) = idemFn x ((kp₂ (f := eMor x)).1 w) :=
      Mor.congr (kp_sq (f := eMor x)) w
    calc x.1 ((kp₁ (f := eMor x)).1 w)
        = x.1 (idemFn x ((kp₁ (f := eMor x)).1 w)) := (idemFn_absorb x _).symm
      _ = x.1 (idemFn x ((kp₂ (f := eMor x)).1 w)) := by rw [hsq]
      _ = x.1 ((kp₂ (f := eMor x)).1 w) := idemFn_absorb x _
  · refine kernelPairRel_le_of_comm x (eMor x) ?_
    refine Mor.ext fun w => ?_
    show idemFn x ((kp₁ (f := x)).1 w) = idemFn x ((kp₂ (f := x)).1 w)
    exact idemFn_congr x (Mor.congr (kp_sq (f := x)) w)

/-- **§1.572, the factorization**: every morphism of R factors as a left-invertible
    followed by a monic — §1.571 instantiated with `e(n) = min{ i ≤ n | x(i) = x(n) }`. -/
theorem rFactorization {α β : ExtNat} (x : α ⟶ β) :
    ∃ (C : ExtNat) (p : α ⟶ C) (n : C ⟶ β),
      (∃ s : C ⟶ α, s ≫ p = Cat.id C) ∧ Monic n ∧ p ≫ n = x :=
  ac_factorization_via_idempotent
    (fun x => ⟨eMor x, Mor.ext fun a => idemFn_idem x a, Mor.ext fun a => idemFn_absorb x a,
      (eMor_same_level x).1, (eMor_same_level x).2⟩) x

/-- The factorization data, extracted by choice. -/
noncomputable def facData {α β : ExtNat} (x : α ⟶ β) :
    Σ' (C : ExtNat) (p : α ⟶ C) (n : C ⟶ β) (s : C ⟶ α),
      s ≫ p = Cat.id C ∧ Monic n ∧ p ≫ n = x :=
  Classical.choice <| by
    obtain ⟨C, p, n, ⟨s, hs⟩, hn, hfac⟩ := rFactorization x
    exact ⟨⟨C, p, n, s, hs, hn, hfac⟩⟩

/-- Images, CONSTRUCTED from the factorization: the image of `x` is the monic
    leg `n`; minimality holds because the split `s` retracts any competitor. -/
noncomputable instance : HasImages ExtNat where
  image {α β} x := ⟨(facData x).1, (facData x).2.2.1, (facData x).2.2.2.2.2.1⟩
  isImage {α β} x := by
    obtain ⟨C, p, n, s, hs, hn, hfac⟩ := facData x
    constructor
    · exact ⟨p, hfac⟩
    · rintro S ⟨g, hg⟩
      refine ⟨s ≫ g, ?_⟩
      show (s ≫ g) ≫ S.arr = n
      calc (s ≫ g) ≫ S.arr = s ≫ (g ≫ S.arr) := Cat.assoc _ _ _
        _ = s ≫ x := by rw [hg]
        _ = s ≫ (p ≫ n) := by rw [hfac]
        _ = (s ≫ p) ≫ n := (Cat.assoc _ _ _).symm
        _ = Cat.id C ≫ n := by rw [hs]
        _ = n := Cat.id_comp n

/-- **AC**: every cover of R splits (covers are exactly the split epis). -/
theorem cover_split {α β : ExtNat} (f : α ⟶ β) (hc : Cover f) :
    ∃ s : β ⟶ α, s ≫ f = Cat.id β := by
  obtain ⟨C, p, n, s, hs, hn, hfac⟩ := facData f
  have hiso : IsIso n := hc n p hn hfac
  obtain ⟨ninv, hn1, hn2⟩ := hiso
  refine ⟨ninv ≫ s, ?_⟩
  calc (ninv ≫ s) ≫ f = ninv ≫ (s ≫ f) := Cat.assoc _ _ _
    _ = ninv ≫ (s ≫ (p ≫ n)) := by rw [hfac]
    _ = ninv ≫ ((s ≫ p) ≫ n) := by rw [Cat.assoc]
    _ = ninv ≫ (Cat.id C ≫ n) := by rw [hs]
    _ = ninv ≫ n := by rw [Cat.id_comp]
    _ = Cat.id β := hn2

/-- Pullbacks transfer covers: covers split, and split epis transfer along any
    pullback square (Freyd §1.57: "left-invertibles are always covers and are
    always transferred by pullbacks"). -/
instance : PullbacksTransferCovers ExtNat where
  pullbacks_transfer_covers {A B C} {f g} c hpb hf := by
    obtain ⟨s, hs⟩ := cover_split f hf
    have hw : (g ≫ s) ≫ f = Cat.id C ≫ g := by
      rw [Cat.assoc, hs, Cat.comp_id, Cat.id_comp]
    obtain ⟨u, ⟨_, hu2⟩, _⟩ := hpb ⟨C, g ≫ s, Cat.id C, hw⟩
    intro D m g' hm hgm
    exact cover_of_section c.π₂ u hu2 m g' hm hgm

/-- **§1.572 headline (positive part)**: R is a regular category. -/
noncomputable instance : RegularCategory ExtNat := {}

theorem all_choice : ∀ C : ExtNat, Choice C :=
  choice_iff_projective.mpr (fun _ _ f hcov => cover_split f hcov)

/-- **§1.572 headline**: R is an AC regular category. -/
noncomputable instance : ACRegularCategory ExtNat := { all_choice := all_choice }

end Freyd.Rcat
