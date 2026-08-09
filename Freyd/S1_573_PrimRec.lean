/-
  Freyd & Scedrov, *Categories and Allegories* §1.573–§1.574
  The category **P** of primitive recursive functions and its idempotent-splitting
  completion **P̂** = Spl(P).

  §1.573: replacing 'recursive' by 'primitive recursive' in §1.572 gives a category P
  that is NOT cartesian (equalizers can fail).  But given `x, y : ω → α` and `n` with
  `x(n) = y(n)` (if there is no such `n`, then 0 is the equalizer), the function
      `e(i) = i` if `x(i) = y(i)`, `n` otherwise
  satisfies `e² = e`, `ex = ey`, and every `z : β → ω` with `zx = zy` has `ze = z` —
  precisely what is needed for `x, y` to acquire an equalizer once all idempotents are
  split.  P̂ := Spl(P) (equivalent to the category of all primitive recursive subsets
  of ω) is cartesian.

  §1.574: the representable functor `P̂(ω̂, −) : P̂ → 𝒮` is faithful.

  The primitive recursive fragment is carved out of §1.572's Kleene codes by the
  mu-freeness predicate `IsPrim`, so every evaluation lemma of `S1_572_Recursive`
  transfers as-is; only the closure lemmas that USED `mu` (Cantor weight `cw`,
  division/remainder by a constant) are re-done mu-free, by unary primitive recursion
  (`natIter`) in place of unbounded search.

  SKIPPED (classical Ackermann-scale formalizations, out of scope here):
  • §1.573's negative half — "P is not cartesian" — needs a function growing faster
    than every primitive recursive function to defeat all candidate equalizers.
  • §1.574's one-to-one onto `x : ω → ω` in P with `x⁻¹ ∉ P` (whence R is a category
    of fractions of P), for the same reason.
  • "representation of regular categories": P̂'s regular structure is not developed
    here, only its cartesian structure (§1.573) and the faithfulness of `P̂(ω̂, −)`.
-/

import Freyd.S1_572_Recursive
import Freyd.S1_28
import Freyd.S1_39
import Freyd.S1_55
import Freyd.S2_21c

open Freyd Freyd.Rcat

namespace Freyd.Pcat

/-! ## Part 1: primitive recursive codes = the mu-free Kleene codes -/

/-- Mu-freeness: `IsPrim c` iff the code `c` contains no `mu`.  A `Prop`-valued
    predicate over §1.572's `RecCode` (rather than a separate inductive) so that every
    evaluation lemma about explicit codes (`evalAdd`, `evalConst`, …) transfers as-is. -/
def IsPrim : {k : Nat} → RecCode k → Prop
  | _, .zero      => True
  | _, .succ      => True
  | _, .proj _    => True
  | _, .comp f gs => IsPrim f ∧ ∀ j, IsPrim (gs j)
  | _, .prec g h  => IsPrim g ∧ IsPrim h
  | _, .mu _      => False

/-- Primitive recursive codes are TOTAL: `Eval` converges on every input.
    (Structural induction; the recursion of `prec` is an inner induction on the
    first argument, and `comp` assembles its finitely many subvalues by the
    constructive finite choice `S2_21c.finChoice`.) -/
theorem IsPrim.total : ∀ {k : Nat} (c : RecCode k), IsPrim c → ∀ v, ∃ y, Eval c v y := by
  intro k c
  induction c with
  | zero => exact fun _ _ => ⟨0, .zero⟩
  | succ => exact fun _ v => ⟨v 0 + 1, .succ⟩
  | proj i => exact fun _ v => ⟨v i, .proj i⟩
  | comp f gs ihf ihg =>
    intro h v
    obtain ⟨w, hw⟩ := S2_21c.finChoice fun j => ihg j (h.2 j) v
    obtain ⟨y, hy⟩ := ihf h.1 w
    exact ⟨y, .comp w hw hy⟩
  | prec g hs ihg ihh =>
    intro h v
    have key : ∀ (n : Nat) (w : Vec _), ∃ y, Eval (.prec g hs) (vcons n w) y := by
      intro n w
      induction n with
      | zero =>
        obtain ⟨y, hy⟩ := ihg h.1 w
        exact ⟨y, .prec_zero rfl hy⟩
      | succ n ihn =>
        obtain ⟨r, hr⟩ := ihn
        obtain ⟨y, hy⟩ := ihh h.2 (vcons n (vcons r w))
        exact ⟨y, .prec_succ rfl hr hy⟩
    obtain ⟨y, hy⟩ := key (v 0) (vtail v)
    exact ⟨y, by rwa [vcons_head_tail] at hy⟩
  | mu f ih => exact fun h => h.elim

/-! ### Primitive recursive functions -/

/-- A `k`-ary function is PRIMITIVE RECURSIVE if some mu-free code converges to its
    value on every input (§1.572's `RecursiveV` with the code constrained to `IsPrim`). -/
def PrimRecV {k : Nat} (f : Vec k → Nat) : Prop :=
  ∃ c : RecCode k, IsPrim c ∧ ∀ v, Eval c v (f v)

/-- Unary primitive recursive functions ℕ → ℕ. -/
def PrimRec1 (f : Nat → Nat) : Prop := PrimRecV fun v : Vec 1 => f (v 0)

/-- Binary primitive recursive functions ℕ → ℕ → ℕ. -/
def PrimRec2 (f : Nat → Nat → Nat) : Prop := PrimRecV fun v : Vec 2 => f (v 0) (v 1)

/-- Primitive recursive functions are recursive. -/
theorem PrimRecV.recursiveV {k : Nat} {f : Vec k → Nat} : PrimRecV f → RecursiveV f
  | ⟨c, _, hc⟩ => ⟨c, hc⟩

theorem PrimRecV.congr {k : Nat} {f g : Vec k → Nat} (hf : PrimRecV f)
    (h : ∀ v, f v = g v) : PrimRecV g := by
  obtain ⟨c, hp, hc⟩ := hf
  exact ⟨c, hp, fun v => h v ▸ hc v⟩

theorem PrimRec1.congr {f g : Nat → Nat} (hf : PrimRec1 f) (h : ∀ n, f n = g n) :
    PrimRec1 g := PrimRecV.congr hf fun v => h (v 0)

theorem PrimRec2.congr {f g : Nat → Nat → Nat} (hf : PrimRec2 f)
    (h : ∀ a b, f a b = g a b) : PrimRec2 g := PrimRecV.congr hf fun v => h (v 0) (v 1)

theorem PrimRecV.proj {k : Nat} (i : Fin k) : PrimRecV (fun v : Vec k => v i) :=
  ⟨.proj i, trivial, fun _ => .proj i⟩

theorem PrimRec1.id : PrimRec1 fun n => n := PrimRecV.proj 0

theorem isPrim_constCode (k c : Nat) : IsPrim (constCode k c) := by
  induction c with
  | zero => trivial
  | succ c ih => exact ⟨trivial, fun _ => ih⟩

theorem PrimRecV.const (k c : Nat) : PrimRecV (fun _ : Vec k => c) :=
  ⟨constCode k c, isPrim_constCode k c, fun v => evalConst k c v⟩

theorem PrimRec1.const (c : Nat) : PrimRec1 fun _ => c := PrimRecV.const 1 c

/-! ### Closure under composition.  Unlike §1.572's `RecursiveV.comp` (which chooses an
    arbitrary finite family of codes by `Classical.choose`), we only ever compose through
    explicit one- and two-code families, keeping the closure lemmas choice-free. -/

theorem PrimRec1.comp {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => g (f n) := by
  obtain ⟨cf, pf, hcf⟩ := hf
  obtain ⟨cg, pg, hcg⟩ := hg
  exact ⟨.comp cg fun _ => cf, ⟨pg, fun _ => pf⟩,
    fun v => .comp (fun _ => f (v 0)) (fun _ => hcf v) (hcg _)⟩

/-- Unary post-composition at any arity. -/
theorem PrimRecV.comp1 {k : Nat} {F : Nat → Nat} {f : Vec k → Nat}
    (hF : PrimRec1 F) (hf : PrimRecV f) : PrimRecV (fun v => F (f v)) := by
  obtain ⟨cF, pF, hcF⟩ := hF
  obtain ⟨cf, pf, hcf⟩ := hf
  exact ⟨.comp cF fun _ => cf, ⟨pF, fun _ => pf⟩,
    fun v => .comp (fun _ => f v) (fun _ => hcf v) (hcF _)⟩

/-- Binary combination at any arity: from a primitive recursive binary `H` and
    primitive recursive arguments, `v ↦ H (f v) (g v)` is primitive recursive. -/
theorem PrimRecV.comp2 {k : Nat} {H : Nat → Nat → Nat} {f g : Vec k → Nat}
    (hH : PrimRec2 H) (hf : PrimRecV f) (hg : PrimRecV g) :
    PrimRecV (fun v => H (f v) (g v)) := by
  obtain ⟨cH, pH, hcH⟩ := hH
  obtain ⟨cf, pf, hcf⟩ := hf
  obtain ⟨cg, pg, hcg⟩ := hg
  refine ⟨.comp cH (fun j => if j.val = 0 then cf else cg),
    ⟨pH, fun j => by dsimp only; split <;> assumption⟩, fun v => ?_⟩
  refine .comp (vcons (f v) (fun _ => g v)) (fun j => ?_) ?_
  · rcases j with ⟨jv, hj⟩
    match jv, hj with
    | 0, _ => exact hcf v
    | 1, _ => exact hcg v
  · exact hcH (vcons (f v) fun _ => g v)

theorem PrimRec1.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat}
    (hH : PrimRec2 H) (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => H (f n) (g n) :=
  PrimRecV.comp2 (f := fun v : Vec 1 => f (v 0)) (g := fun v : Vec 1 => g (v 0)) hH hf hg

theorem PrimRec2.comp2 {H : Nat → Nat → Nat} {f g : Nat → Nat → Nat}
    (hH : PrimRec2 H) (hf : PrimRec2 f) (hg : PrimRec2 g) :
    PrimRec2 fun a b => H (f a b) (g a b) :=
  PrimRecV.comp2 (f := fun v : Vec 2 => f (v 0) (v 1)) (g := fun v : Vec 2 => g (v 0) (v 1))
    hH hf hg

theorem PrimRec2.swap {f : Nat → Nat → Nat} (hf : PrimRec2 f) :
    PrimRec2 fun a b => f b a :=
  PrimRec2.comp2 hf (show PrimRec2 fun _ b => b from PrimRecV.proj 1) (show PrimRec2 fun a _ => a from PrimRecV.proj 0)

theorem PrimRec2.ofFst {f : Nat → Nat} (hf : PrimRec1 f) : PrimRec2 fun a _ => f a :=
  PrimRecV.comp1 (f := fun v : Vec 2 => v 0) hf (PrimRecV.proj 0)

theorem PrimRec2.ofSnd {f : Nat → Nat} (hf : PrimRec1 f) : PrimRec2 fun _ b => f b :=
  PrimRecV.comp1 (f := fun v : Vec 2 => v 1) hf (PrimRecV.proj 1)

/-! ### Arithmetic base (the §1.572 codes are all mu-free) -/

theorem isPrim_addCode : IsPrim addCode := ⟨trivial, trivial, fun _ => trivial⟩

theorem PrimRec2.add : PrimRec2 fun a b => a + b := by
  refine PrimRecV.congr (g := fun v : Vec 2 => v 0 + v 1)
    ⟨addCode, isPrim_addCode, fun v => evalAdd v⟩ ?_
  intro v
  exact Nat.add_comm (v 1) (v 0)

theorem isPrim_predCode : IsPrim predCode := ⟨trivial, trivial⟩

theorem PrimRec2.sub : PrimRec2 fun a b => a - b := by
  have h : PrimRec2 fun a b => b - a :=
    ⟨rsubCode, ⟨trivial, isPrim_predCode, fun _ => trivial⟩, fun v => by
      have := evalRsub_aux (v 0) (vtail v)
      rwa [vcons_head_tail v] at this⟩
  exact h.swap

theorem PrimRec2.mul : PrimRec2 fun a b => a * b :=
  ⟨mulCode, ⟨trivial, isPrim_addCode, fun j => by dsimp only; split <;> trivial⟩, fun v => by
    have := evalMul_aux (v 0) (vtail v)
    rwa [vcons_head_tail v] at this⟩

theorem PrimRec1.add {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n + g n := PrimRec1.comp2 PrimRec2.add hf hg

theorem PrimRec1.mul {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n * g n := PrimRec1.comp2 PrimRec2.mul hf hg

theorem PrimRec1.sub {f g : Nat → Nat} (hf : PrimRec1 f) (hg : PrimRec1 g) :
    PrimRec1 fun n => f n - g n := PrimRec1.comp2 PrimRec2.sub hf hg

theorem PrimRec2.eqInd : PrimRec2 Rcat.eqInd :=
  PrimRec2.comp2 (H := fun a b => a - b) PrimRec2.sub
    (PrimRec2.comp2 (H := fun _ _ => (1 : Nat)) (PrimRec2.ofFst (PrimRec1.const 1))
      (show PrimRec2 fun a _ => a from PrimRecV.proj 0) (show PrimRec2 fun _ b => b from PrimRecV.proj 1))
    (PrimRec2.comp2 PrimRec2.add PrimRec2.sub (PrimRec2.swap PrimRec2.sub))

/-- `if n = c then a else w n` is primitive recursive when `w` is. -/
theorem PrimRec1.ifEqConst (c a : Nat) {w : Nat → Nat} (hw : PrimRec1 w) :
    PrimRec1 fun n => if n = c then a else w n := by
  have hind : PrimRec1 fun n => eqInd n c :=
    PrimRec1.comp2 PrimRec2.eqInd PrimRec1.id (PrimRec1.const c)
  have harith : PrimRec1 fun n => a * eqInd n c + w n * (1 - eqInd n c) :=
    PrimRec1.add (PrimRec1.mul (PrimRec1.const a) hind)
      (PrimRec1.mul hw (PrimRec1.sub (PrimRec1.const 1) hind))
  refine harith.congr fun n => ?_
  by_cases h : n = c
  · rw [if_pos h, eqInd_eq h]; simp
  · rw [if_neg h, eqInd_ne h]; simp

/-- Any finite lookup table (0 outside its domain) is primitive recursive — the book's
    "any function from a finite natural number" convention, in P. -/
theorem PrimRec1.finTable (m : Nat) (t : Fin m → Nat) :
    PrimRec1 fun j => if h : j < m then t ⟨j, h⟩ else 0 :=
  finTable_of (PrimRec1.const 0) (fun h e => h.congr e) PrimRec1.ifEqConst m t

/-- Unary primitive recursion (`natIter`) preserves primitive recursiveness —
    §1.572's `Recursive1.natIter` restricted to mu-free codes. -/
theorem PrimRec1.natIter (g0 : Nat) {H : Nat → Nat → Nat} (hH : PrimRec2 H) :
    PrimRec1 (Rcat.natIter g0 H) := by
  obtain ⟨cH, pH, hcH⟩ := hH
  refine ⟨.prec (constCode 0 g0) cH, ⟨isPrim_constCode 0 g0, pH⟩, fun v => ?_⟩
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

theorem PrimRec1.tri : PrimRec1 Rcat.tri :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add (show PrimRec2 fun _ b => b from PrimRecV.proj 1)
    (PrimRec2.comp2 PrimRec2.add (show PrimRec2 fun a _ => a from PrimRecV.proj 0) (PrimRec2.ofFst (PrimRec1.const 1))))

/-! ## Part 2: the Cantor projections and div/mod are primitive recursive

  §1.572 computed the Cantor weight `cw` and `·/(m+1)`, `·%(m+1)` by unbounded
  mu-search.  Here they are re-done mu-free: each satisfies a first-order recursion,
  so `natIter` (= a `prec` code) suffices — bounded search is not even needed. -/

/-- Mu-free Cantor weight: the diagonal index of `c`, by unary primitive recursion —
    it increments exactly when `c+1` reaches the next triangular number. -/
def cwP : Nat → Nat := natIter 0 fun c r => r + eqInd (c + 1) (tri (r + 1))

theorem cwP_zero : cwP 0 = 0 := rfl

theorem cwP_succ (c : Nat) : cwP (c + 1) = cwP c + eqInd (c + 1) (tri (cwP c + 1)) := rfl

theorem PrimRec1.cwP : PrimRec1 Pcat.cwP :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add (show PrimRec2 fun _ b => b from PrimRecV.proj 1)
    (PrimRec2.comp2 PrimRec2.eqInd
      (PrimRec2.ofFst (PrimRec1.add PrimRec1.id (PrimRec1.const 1)))
      (PrimRec2.ofSnd (PrimRec1.comp
        (PrimRec1.add PrimRec1.id (PrimRec1.const 1)) PrimRec1.tri))))

/-- `cwP` sandwiches `c` between consecutive triangular numbers. -/
theorem cwP_spec (c : Nat) : tri (cwP c) ≤ c ∧ c < tri (cwP c + 1) := by
  induction c with
  | zero =>
    rw [cwP_zero]
    refine ⟨Nat.le_refl 0, ?_⟩
    rw [tri_succ, tri_zero]
    omega
  | succ c ih =>
    rw [cwP_succ]
    by_cases h : c + 1 = tri (cwP c + 1)
    · rw [eqInd_eq h]
      have hstep : tri (cwP c + 1 + 1) = tri (cwP c + 1) + (cwP c + 1 + 1) :=
        tri_succ (cwP c + 1)
      exact ⟨by omega, by omega⟩
    · rw [eqInd_ne h, Nat.add_zero]
      exact ⟨by omega, by omega⟩

theorem cwP_eq_cw (c : Nat) : cwP c = cw c := by
  refine (theLeast_unique (fun s => c < tri (s + 1))
    ⟨c, by have := le_tri (c + 1); omega⟩ (cwP_spec c).2 fun i hi => ?_).symm
  show ¬c < tri (i + 1)
  have h1 : tri (i + 1) ≤ tri (cwP c) := tri_mono (by omega)
  have h2 := (cwP_spec c).1
  omega

theorem PrimRec1.cw : PrimRec1 Rcat.cw := PrimRec1.cwP.congr cwP_eq_cw

theorem PrimRec1.csnd : PrimRec1 Rcat.csnd :=
  (PrimRec1.sub PrimRec1.id (PrimRec1.comp PrimRec1.cw PrimRec1.tri)).congr
    fun _ => rfl

theorem PrimRec1.cfst : PrimRec1 Rcat.cfst :=
  (PrimRec1.sub PrimRec1.cw PrimRec1.csnd).congr fun _ => rfl

theorem PrimRec2.cp : PrimRec2 Rcat.cp := by
  have h : PrimRec2 fun a b => Rcat.tri (a + b) + b :=
    PrimRec2.comp2 PrimRec2.add
      (PrimRec2.comp2 (PrimRec2.ofSnd PrimRec1.tri) (show PrimRec2 fun a _ => a from PrimRecV.proj 0) PrimRec2.add)
      (show PrimRec2 fun _ b => b from PrimRecV.proj 1)
  exact h.congr fun _ _ => rfl

/-! ### Division and remainder by a positive constant, mu-free -/

/-- Mu-free remainder mod `m+1`: unary recursion cycling through `0, 1, …, m, 0, …`. -/
def modP (m : Nat) : Nat → Nat :=
  natIter 0 fun _ r => (r + 1) * (1 - eqInd (r + 1) (m + 1))

theorem modP_succ (m c : Nat) :
    modP m (c + 1) = (modP m c + 1) * (1 - eqInd (modP m c + 1) (m + 1)) := rfl

theorem PrimRec1.modP (m : Nat) : PrimRec1 (Pcat.modP m) := by
  have hA : PrimRec2 fun (_ r : Nat) => r + 1 :=
    PrimRec2.comp2 PrimRec2.add (show PrimRec2 fun _ b => b from PrimRecV.proj 1) (PrimRec2.ofFst (PrimRec1.const 1))
  exact PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.mul hA
    (PrimRec2.comp2 PrimRec2.sub (PrimRec2.ofFst (PrimRec1.const 1))
      (PrimRec2.comp2 PrimRec2.eqInd hA (PrimRec2.ofFst (PrimRec1.const (m + 1))))))

theorem modP_eq (m c : Nat) : Pcat.modP m c = c % (m + 1) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have hq := Nat.div_add_mod c (m + 1)
    rw [modP_succ, ih]
    have hmc : (c / (m + 1)) * (m + 1) = (m + 1) * (c / (m + 1)) := Nat.mul_comm _ _
    by_cases h : c % (m + 1) + 1 = m + 1
    · rw [h, eqInd_eq rfl]
      have hsucc : (c / (m + 1) + 1) * (m + 1) = (m + 1) * (c / (m + 1)) + (m + 1) := by
        rw [Nat.succ_mul, Nat.mul_comm]
      have hc1 : c + 1 = (c / (m + 1) + 1) * (m + 1) + 0 := by omega
      rw [hc1, mulAdd_mod m _ 0 (Nat.succ_pos m)]
      simp
    · rw [eqInd_ne h]
      have hmod : c % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
      have hc1 : c + 1 = (c / (m + 1)) * (m + 1) + (c % (m + 1) + 1) := by omega
      rw [hc1, mulAdd_mod m _ _ (by omega)]
      simp

theorem PrimRec1.modConst (m : Nat) : PrimRec1 fun c => c % (m + 1) :=
  (PrimRec1.modP m).congr (modP_eq m)

/-- Mu-free quotient by `m+1`: increments exactly when the remainder wraps around. -/
def divP (m : Nat) : Nat → Nat := natIter 0 fun c r => r + eqInd (modP m c) m

theorem divP_succ (m c : Nat) : divP m (c + 1) = divP m c + eqInd (modP m c) m := rfl

theorem PrimRec1.divP (m : Nat) : PrimRec1 (Pcat.divP m) :=
  PrimRec1.natIter 0 (PrimRec2.comp2 PrimRec2.add (show PrimRec2 fun _ b => b from PrimRecV.proj 1)
    (PrimRec2.ofFst (PrimRec1.comp2 PrimRec2.eqInd (PrimRec1.modP m)
      (PrimRec1.const m))))

theorem divP_eq (m c : Nat) : Pcat.divP m c = c / (m + 1) := by
  induction c with
  | zero => rw [Nat.zero_div]; rfl
  | succ c ih =>
    have hq := Nat.div_add_mod c (m + 1)
    have hmod : c % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
    have hmc : (c / (m + 1)) * (m + 1) = (m + 1) * (c / (m + 1)) := Nat.mul_comm _ _
    rw [divP_succ, ih, modP_eq]
    by_cases h : c % (m + 1) = m
    · rw [eqInd_eq h]
      have hsucc : (c / (m + 1) + 1) * (m + 1) = (m + 1) * (c / (m + 1)) + (m + 1) := by
        rw [Nat.succ_mul, Nat.mul_comm]
      have hc1 : c + 1 = (c / (m + 1) + 1) * (m + 1) + 0 := by omega
      rw [hc1, mulAdd_div m _ 0 (Nat.succ_pos m)]
    · rw [eqInd_ne h, Nat.add_zero]
      have hc1 : c + 1 = (c / (m + 1)) * (m + 1) + (c % (m + 1) + 1) := by omega
      rw [hc1, mulAdd_div m _ _ (by omega)]

theorem PrimRec1.divConst (m : Nat) : PrimRec1 fun c => c / (m + 1) :=
  (PrimRec1.divP m).congr (divP_eq m)

/-! ## Part 3: the category P (§1.573)

  Same objects as R (the extended naturals), morphisms the primitive recursive
  functions.  `PObj` is a separate (semireducible) alias of `ExtNat` so that P's
  `Cat` instance cannot collide with R's. -/

/-- Objects of P: the extended naturals 0, 1, 2, …, ω. -/
def PObj : Type := ExtNat

/-- Morphism condition of P: from ω the induced ℕ→ℕ function must be primitive
    recursive; from a finite ordinal everything is a morphism (book convention). -/
def IsPMor : (α β : ExtNat) → (El α → El β) → Prop := fun α _ f =>
  match α, f with
  | some _, _ => True
  | none, f => PrimRec1 fun k => toNat (f k)

/-- Every P-morphism is an R-morphism. -/
theorem IsPMor.isMor : ∀ {α β : ExtNat} {f : El α → El β}, IsPMor α β f → IsMor α β f := by
  intro α
  match α with
  | some n => intro β f _; exact trivial
  | none => intro β f h; exact PrimRecV.recursiveV h

/-- Morphisms of P: primitive recursive functions between the carriers. -/
def PMor (α β : ExtNat) : Type := {f : El α → El β // IsPMor α β f}

theorem PMor.ext {α β : ExtNat} {f g : PMor α β} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (funext h)

theorem isPMor_finite {n : Nat} {β : ExtNat} (f : El (some n) → El β) :
    IsPMor (some n) β f := trivial

/-- Composing through a finite object stays primitive recursive (finite tables). -/
theorem primrec1_finComp {m : Nat} {f : Nat → Fin m} (hf : PrimRec1 fun k => (f k).val)
    (t : Fin m → Nat) : PrimRec1 fun k => t (f k) := by
  have htab := PrimRec1.finTable m t
  have hcomp := PrimRec1.comp (f := fun k => (f k).val)
    (g := fun j => if h : j < m then t ⟨j, h⟩ else 0) hf htab
  refine hcomp.congr fun k => ?_
  show (if h : (f k).val < m then t ⟨(f k).val, h⟩ else 0) = t (f k)
  rw [dif_pos (f k).isLt]

/-- Composites of P-morphisms are P-morphisms. -/
theorem isPMor_comp {α β γ : ExtNat} (f : PMor α β) (g : PMor β γ) :
    IsPMor α γ fun a => g.1 (f.1 a) := by
  match α with
  | some n => exact trivial
  | none =>
    match β with
    | none =>
      exact PrimRec1.comp (f := fun k => toNat (f.1 k)) (g := fun k => toNat (g.1 k)) f.2 g.2
    | some m =>
      exact primrec1_finComp (f := fun k => f.1 k) f.2 fun j => toNat (g.1 j)

instance : Cat PObj where
  Hom := PMor
  id α := ⟨fun a => a, by
    match α with
    | some n => exact trivial
    | none => exact PrimRec1.id⟩
  comp f g := ⟨fun a => g.1 (f.1 a), isPMor_comp f g⟩
  id_comp f := PMor.ext fun _ => rfl
  comp_id f := PMor.ext fun _ => rfl
  assoc f g h := PMor.ext fun _ => rfl

/-- Pointwise evaluation of a composite in P. -/
theorem pcomp_fn {α β γ : PObj} (f : α ⟶ β) (g : β ⟶ γ) (a : El α) :
    (f ≫ g).1 a = g.1 (f.1 a) := rfl

theorem pid_fn {α : PObj} (a : El α) : (Cat.id α).1 a = a := rfl

/-- Pointwise consequence of a P-morphism equation. -/
theorem PMor.congr {α β : ExtNat} {f g : PMor α β} (h : f = g) (a : El α) :
    f.1 a = g.1 a := by rw [h]

/-! ### P has a terminator and binary products (§1.573: products are NOT the problem;
    only equalizers fail).  R's `ProdData` bijections transfer: their decodings and
    numeric pairings are primitive recursive in every case. -/

instance : HasTerminal PObj where
  one := (some 1 : ExtNat)
  trm X := ⟨fun _ => ⟨0, Nat.one_pos⟩, by
    match X with
    | some n => exact trivial
    | none => exact PrimRec1.const 0⟩
  uniq f g := PMor.ext fun a => by
    apply toNat_inj
    have h1 : toNat (f.1 a) < 1 := toNat_lt _
    have h2 : toNat (g.1 a) < 1 := toNat_lt _
    omega

/-- §1.572's `ProdData` bijection together with primitive recursiveness of its
    projections and its numeric pairing: product data for P. -/
structure PProdData (α β : ExtNat) where
  pd : ProdData α β
  dec₁_pmor : IsPMor pd.obj α pd.dec₁
  dec₂_pmor : IsPMor pd.obj β pd.dec₂
  encN_prim : PrimRec2 pd.encN

/-- All six §1.572 product bijections are primitive recursive. -/
noncomputable def pprodData : (α β : ExtNat) → PProdData α β
  | some n, some m =>
    ⟨prodFinFin n m, trivial, trivial,
      (PrimRec2.comp2 PrimRec2.add
        (PrimRec2.comp2 PrimRec2.mul (show PrimRec2 fun a _ => a from PrimRecV.proj 0) (PrimRec2.ofFst (PrimRec1.const m)))
        (show PrimRec2 fun _ b => b from PrimRecV.proj 1) : PrimRec2 fun a b => a * m + b)⟩
  | some 0, none => ⟨prodZeroOmega 0 rfl, trivial, trivial, PrimRecV.const 2 0⟩
  | some (n + 1), none =>
    ⟨prodFinOmega n, PrimRec1.modConst n, PrimRec1.divConst n,
      (PrimRec2.comp2 PrimRec2.add
        (PrimRec2.comp2 PrimRec2.mul (show PrimRec2 fun _ b => b from PrimRecV.proj 1) (PrimRec2.ofFst (PrimRec1.const (n + 1))))
        (show PrimRec2 fun a _ => a from PrimRecV.proj 0) : PrimRec2 fun a b => b * (n + 1) + a)⟩
  | none, some 0 => ⟨prodOmegaZero 0 rfl, trivial, trivial, PrimRecV.const 2 0⟩
  | none, some (m + 1) =>
    ⟨prodOmegaFin m, PrimRec1.divConst m, PrimRec1.modConst m,
      (PrimRec2.comp2 PrimRec2.add
        (PrimRec2.comp2 PrimRec2.mul (show PrimRec2 fun a _ => a from PrimRecV.proj 0) (PrimRec2.ofFst (PrimRec1.const (m + 1))))
        (show PrimRec2 fun _ b => b from PrimRecV.proj 1) : PrimRec2 fun a b => a * (m + 1) + b)⟩
  | none, none => ⟨prodOmegaOmega, PrimRec1.cfst, PrimRec1.csnd, PrimRec2.cp⟩

/-- The universal pairing map is a P-morphism (via the primitive recursive `encN`). -/
theorem pair_isPMor {X α β : ExtNat} (ppd : PProdData α β) (f : PMor X α) (g : PMor X β) :
    IsPMor X ppd.pd.obj fun w => ppd.pd.enc (f.1 w) (g.1 w) := by
  match X with
  | some n => exact trivial
  | none =>
    have h : PrimRec1 fun k => ppd.pd.encN (toNat (f.1 k)) (toNat (g.1 k)) :=
      PrimRec1.comp2 ppd.encN_prim f.2 g.2
    exact h.congr fun k => (ppd.pd.encN_spec _ _).symm

noncomputable instance : HasBinaryProducts PObj where
  prod α β := (pprodData α β).pd.obj
  fst {α β} := ⟨(pprodData α β).pd.dec₁, (pprodData α β).dec₁_pmor⟩
  snd {α β} := ⟨(pprodData α β).pd.dec₂, (pprodData α β).dec₂_pmor⟩
  pair {X α β} f g := ⟨fun w => (pprodData α β).pd.enc (f.1 w) (g.1 w), pair_isPMor _ f g⟩
  fst_pair {X α β} f g := PMor.ext fun w => (pprodData α β).pd.dec₁_enc _ _
  snd_pair {X α β} f g := PMor.ext fun w => (pprodData α β).pd.dec₂_enc _ _
  pair_uniq {X α β} f g h h₁ h₂ := PMor.ext fun w => by
    have e1 : (pprodData α β).pd.dec₁ (h.1 w) = f.1 w := PMor.congr h₁ w
    have e2 : (pprodData α β).pd.dec₂ (h.1 w) = g.1 w := PMor.congr h₂ w
    calc h.1 w
        = (pprodData α β).pd.enc ((pprodData α β).pd.dec₁ (h.1 w))
            ((pprodData α β).pd.dec₂ (h.1 w)) := ((pprodData α β).pd.enc_dec _).symm
      _ = (pprodData α β).pd.enc (f.1 w) (g.1 w) := by rw [e1, e2]

/-! ## Part 4: the §1.573 equalizer idempotent

  Given `x, y : ω → α` in P and `n` with `x(n) = y(n)`, the book's
      `e(i) = i` if `x(i) = y(i)`, `n` otherwise
  satisfies `e² = e`, `ex = ey`, and `ze = z` for every `z : β → ω` with `zx = zy`
  (the book's line reads "ze = e" — a typo for `ze = z`).  If there is no such `n`,
  then 0 is the equalizer of `x, y` (already in P). -/

/-- ω as an object of P. -/
def omegaP : PObj := (none : ExtNat)

section EqIdem

variable {α : PObj} (x y : omegaP ⟶ α)

/-- §1.573's idempotent: `e(i) = i` if `x(i) = y(i)`, else the agreement witness `n`. -/
def eqIdemFn (n : Nat) : Nat → Nat := fun i =>
  if toNat (x.1 i) = toNat (y.1 i) then i else n

/-- `e` is primitive recursive: arithmetization of the definition-by-cases. -/
theorem eqIdemFn_prim (n : Nat) : PrimRec1 (eqIdemFn x y n) := by
  have hind : PrimRec1 fun i => eqInd (toNat (x.1 i)) (toNat (y.1 i)) :=
    PrimRec1.comp2 PrimRec2.eqInd x.2 y.2
  have harith : PrimRec1 fun i =>
      i * eqInd (toNat (x.1 i)) (toNat (y.1 i)) +
        n * (1 - eqInd (toNat (x.1 i)) (toNat (y.1 i))) :=
    PrimRec1.add (PrimRec1.mul PrimRec1.id hind)
      (PrimRec1.mul (PrimRec1.const n) (PrimRec1.sub (PrimRec1.const 1) hind))
  refine harith.congr fun i => ?_
  show _ = if toNat (x.1 i) = toNat (y.1 i) then i else n
  by_cases h : toNat (x.1 i) = toNat (y.1 i)
  · rw [if_pos h, eqInd_eq h]; simp
  · rw [if_neg h, eqInd_ne h]; simp

/-- The §1.573 idempotent as a morphism of P. -/
def eqIdem (n : Nat) : omegaP ⟶ omegaP := ⟨eqIdemFn x y n, eqIdemFn_prim x y n⟩

/-- `e² = e` (§1.573). -/
theorem eqIdem_idem {n : Nat} (hn : x.1 n = y.1 n) :
    eqIdem x y n ≫ eqIdem x y n = eqIdem x y n :=
  PMor.ext fun i => by
    show eqIdemFn x y n (eqIdemFn x y n i) = eqIdemFn x y n i
    by_cases h : toNat (x.1 i) = toNat (y.1 i)
    · simp only [show eqIdemFn x y n i = i from if_pos (congrArg toNat (toNat_inj h))]
    · simp only [show eqIdemFn x y n i = n from if_neg fun hc => h (congrArg toNat (toNat_inj hc)),
        show eqIdemFn x y n n = n from if_pos (congrArg toNat hn)]

/-- `ex = ey` (§1.573; diagram order: `e ≫ x = e ≫ y`). -/
theorem eqIdem_equalizes {n : Nat} (hn : x.1 n = y.1 n) :
    eqIdem x y n ≫ x = eqIdem x y n ≫ y :=
  PMor.ext fun i => by
    show x.1 (eqIdemFn x y n i) = y.1 (eqIdemFn x y n i)
    by_cases h : toNat (x.1 i) = toNat (y.1 i)
    · rw [show eqIdemFn x y n i = i from if_pos (congrArg toNat (toNat_inj h))]; exact toNat_inj h
    · rw [show eqIdemFn x y n i = n from if_neg fun hc => h (congrArg toNat (toNat_inj hc))]; exact hn

/-- §1.573's universal property: any `z : β → ω` with `zx = zy` satisfies `ze = z`. -/
theorem eqIdem_univ {β : PObj} (z : β ⟶ omegaP) (hz : z ≫ x = z ≫ y) (n : Nat) :
    z ≫ eqIdem x y n = z :=
  PMor.ext fun w => by
    show eqIdemFn x y n (z.1 w) = z.1 w
    exact if_pos (congrArg toNat (PMor.congr hz w))

/-- Any function into the empty carrier is (vacuously) a P-morphism: its very
    existence from ω is contradictory. -/
theorem isPMor_ofEmpty {γ : ExtNat} (f : El γ → El (some 0)) : IsPMor γ (some 0) f := by
  match γ with
  | some d => exact trivial
  | none => exact (f 0).elim0

/-- §1.573, degenerate case: if `x, y` NEVER agree, then 0 is their equalizer —
    already in P, no splitting needed. -/
def eqNowhere (hne : ∀ i : Nat, x.1 i ≠ y.1 i) : HasEqualizer x y where
  cone := ⟨(some 0 : ExtNat), ⟨fun w => w.elim0, trivial⟩, PMor.ext fun w => w.elim0⟩
  lift c := ⟨fun w => absurd (PMor.congr c.eq w) (hne (c.map.1 w)), isPMor_ofEmpty _⟩
  fac c := PMor.ext fun w => absurd (PMor.congr c.eq w) (hne (c.map.1 w))
  uniq _ m _ := PMor.ext fun w => (m.1 w).elim0

end EqIdem

/-! ## Part 5: P̂ = Spl(P), the idempotent-splitting completion (§1.573)

  Objects: pairs `(α, e)` with `e` a primitive recursive idempotent on `α`;
  morphisms `(α, e) → (β, f)`: P-morphisms `φ` absorbing the idempotents,
  `e ≫ φ = φ = φ ≫ f`; the identity of `(α, e)` is `e` itself.  P embeds fully
  and faithfully via `α ↦ (α, 1)`, and every idempotent of P̂ splits. -/

/-- Objects of P̂: a P-object with a primitive recursive idempotent on it. -/
structure PhatObj where
  carrier : PObj
  e : carrier ⟶ carrier
  idem : e ≫ e = e

/-- Morphisms `(α,e) → (β,f)` of P̂: P-morphisms `φ` with `e ≫ φ = φ = φ ≫ f`. -/
def PhatHom (E F : PhatObj) : Type :=
  {φ : E.carrier ⟶ F.carrier // E.e ≫ φ = φ ∧ φ ≫ F.e = φ}

theorem PhatHom.ext {E F : PhatObj} {φ ψ : PhatHom E F} (h : φ.1 = ψ.1) : φ = ψ :=
  Subtype.ext h

instance : Cat PhatObj where
  Hom := PhatHom
  id E := ⟨E.e, E.idem, E.idem⟩
  comp {E F G} φ ψ := ⟨φ.1 ≫ ψ.1,
    by rw [← Cat.assoc, φ.2.1], by rw [Cat.assoc, ψ.2.2]⟩
  id_comp φ := PhatHom.ext φ.2.1
  comp_id φ := PhatHom.ext φ.2.2
  assoc φ ψ χ := PhatHom.ext (Cat.assoc _ _ _)

/-- The embedding P → P̂ on objects: identity idempotents. -/
def embP (α : PObj) : PhatObj := ⟨α, Cat.id α, Cat.id_comp _⟩

def embPFunctor : Functor PObj PhatObj where
  obj := embP
  map f := ⟨f, Cat.id_comp f, Cat.comp_id f⟩
  map_id _ := PhatHom.ext rfl
  map_comp _ _ := PhatHom.ext rfl

theorem embP_full : Full embPFunctor := fun h => ⟨h.1, PhatHom.ext rfl⟩

theorem embP_embedding : Embedding embPFunctor := fun _ _ h => congrArg Subtype.val h

/-- P ↪ P̂ is a full and faithful embedding. -/
theorem embP_faithful : Faithful embPFunctor :=
  full_embedding_faithful embPFunctor embP_embedding embP_full

/-- All idempotents of P̂ split (§1.281 data) — the defining property of Spl(P). -/
theorem phat_idem_split {E : PhatObj} (Φ : E ⟶ E) (h : Idempotent Φ) :
    SplitIdempotent Φ := by
  have h1 : Φ.1 ≫ Φ.1 = Φ.1 := congrArg Subtype.val h
  refine ⟨⟨E.carrier, Φ.1, h1⟩, ⟨Φ.1, Φ.2.1, h1⟩, ⟨Φ.1, h1, Φ.2.2⟩, ?_, ?_⟩
  · exact PhatHom.ext h1
  · exact PhatHom.ext h1

/-! ### P̂ has a terminator and binary products (they lift from P) -/

instance : HasTerminal PhatObj where
  one := embP one
  trm E := ⟨HasTerminal.trm E.carrier, HasTerminal.uniq _ _, Cat.comp_id _⟩
  uniq f g := PhatHom.ext (HasTerminal.uniq f.1 g.1)

/-- Post-composition into a pair (products are natural in the source). -/
theorem comp_pair {𝒞 : Type u} [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] {X Y A B : 𝒞}
    (h : X ⟶ Y) (f : Y ⟶ A) (g : Y ⟶ B) : h ≫ pair f g = pair (h ≫ f) (h ≫ g) :=
  Freyd.pair_uniq _ _ _ (by rw [Cat.assoc, Freyd.fst_pair]) (by rw [Cat.assoc, Freyd.snd_pair])

/-- The product idempotent `e×f` on the carrier product. -/
noncomputable def eProd (E F : PhatObj) :
    prod E.carrier F.carrier ⟶ prod E.carrier F.carrier :=
  pair (Freyd.fst ≫ E.e) (Freyd.snd ≫ F.e)

theorem eProd_absorb_fst (E F : PhatObj) :
    eProd E F ≫ (Freyd.fst ≫ E.e) = Freyd.fst ≫ E.e := by
  rw [← Cat.assoc, show eProd E F ≫ Freyd.fst = Freyd.fst ≫ E.e from Freyd.fst_pair _ _,
    Cat.assoc, E.idem]

theorem eProd_absorb_snd (E F : PhatObj) :
    eProd E F ≫ (Freyd.snd ≫ F.e) = Freyd.snd ≫ F.e := by
  rw [← Cat.assoc, show eProd E F ≫ Freyd.snd = Freyd.snd ≫ F.e from Freyd.snd_pair _ _,
    Cat.assoc, F.idem]

theorem eProd_idem (E F : PhatObj) : eProd E F ≫ eProd E F = eProd E F := by
  show eProd E F ≫ pair (Freyd.fst ≫ E.e) (Freyd.snd ≫ F.e) = eProd E F
  rw [comp_pair, eProd_absorb_fst, eProd_absorb_snd]
  rfl

/-- The product of P̂: carrier product with the product idempotent. -/
noncomputable def phatProd (E F : PhatObj) : PhatObj :=
  ⟨prod E.carrier F.carrier, eProd E F, eProd_idem E F⟩

noncomputable instance : HasBinaryProducts PhatObj where
  prod := phatProd
  fst {E F} := ⟨Freyd.fst ≫ E.e, eProd_absorb_fst E F, by rw [Cat.assoc, E.idem]⟩
  snd {E F} := ⟨Freyd.snd ≫ F.e, eProd_absorb_snd E F, by rw [Cat.assoc, F.idem]⟩
  pair {X E F} φ ψ := ⟨pair φ.1 ψ.1,
    by rw [comp_pair, φ.2.1, ψ.2.1],
    by
      have h1 : pair φ.1 ψ.1 ≫ (Freyd.fst ≫ E.e) = φ.1 := by
        rw [← Cat.assoc, Freyd.fst_pair, φ.2.2]
      have h2 : pair φ.1 ψ.1 ≫ (Freyd.snd ≫ F.e) = ψ.1 := by
        rw [← Cat.assoc, Freyd.snd_pair, ψ.2.2]
      show pair φ.1 ψ.1 ≫ pair (Freyd.fst ≫ E.e) (Freyd.snd ≫ F.e) = pair φ.1 ψ.1
      rw [comp_pair, h1, h2]⟩
  fst_pair {X E F} φ ψ := PhatHom.ext (by
    show pair φ.1 ψ.1 ≫ (Freyd.fst ≫ E.e) = φ.1
    rw [← Cat.assoc, Freyd.fst_pair, φ.2.2])
  snd_pair {X E F} φ ψ := PhatHom.ext (by
    show pair φ.1 ψ.1 ≫ (Freyd.snd ≫ F.e) = ψ.1
    rw [← Cat.assoc, Freyd.snd_pair, ψ.2.2])
  pair_uniq {X E F} φ ψ h h₁ h₂ := PhatHom.ext (by
    have habs : h.1 ≫ eProd E F = h.1 := h.2.2
    have hfst : h.1 ≫ Freyd.fst = φ.1 :=
      calc h.1 ≫ Freyd.fst = (h.1 ≫ eProd E F) ≫ Freyd.fst := by rw [habs]
        _ = h.1 ≫ (eProd E F ≫ Freyd.fst) := Cat.assoc _ _ _
        _ = h.1 ≫ (Freyd.fst ≫ E.e) := by
          rw [show eProd E F ≫ Freyd.fst = Freyd.fst ≫ E.e from Freyd.fst_pair _ _]
        _ = φ.1 := congrArg Subtype.val h₁
    have hsnd : h.1 ≫ Freyd.snd = ψ.1 :=
      calc h.1 ≫ Freyd.snd = (h.1 ≫ eProd E F) ≫ Freyd.snd := by rw [habs]
        _ = h.1 ≫ (eProd E F ≫ Freyd.snd) := Cat.assoc _ _ _
        _ = h.1 ≫ (Freyd.snd ≫ F.e) := by
          rw [show eProd E F ≫ Freyd.snd = Freyd.snd ≫ F.e from Freyd.snd_pair _ _]
        _ = ψ.1 := congrArg Subtype.val h₂
    show h.1 = pair φ.1 ψ.1
    exact Freyd.pair_uniq φ.1 ψ.1 h.1 hfst hsnd)

/-! ### P̂ has equalizers — §1.573's idempotent, generalized to any split object

  For `x, y : (γ,d) ⇉ (β,f)` the agreement set is the set of `d`-FIXED points on
  which `x, y` agree (all values of P̂-morphisms into `(γ,d)` are `d`-fixed).  With a
  witness `a₀` in it, the book's idempotent
      `e′(a) = a` if `d(a) = a` and `x(a) = y(a)`, else `a₀`
  is primitive recursive, and `(γ, e′)` equalizes `x, y`; with no witness, the empty
  object `(0, 1)` does. -/

section SpltFn

variable {γ β : ExtNat} (d : PMor γ γ) (u v : PMor γ β)

/-- The §1.573 idempotent, generalized: fix the `d`-fixed points where `u, v` agree,
    send everything else to the witness `a₀`. -/
def spltFn (a₀ : El γ) : El γ → El γ := fun a =>
  if toNat (d.1 a) = toNat a ∧ toNat (u.1 a) = toNat (v.1 a) then a else a₀

/-- Values of `spltFn` lie in the agreement set (given that the witness does). -/
theorem spltFn_mem (a₀ : El γ) (h₀d : d.1 a₀ = a₀) (h₀uv : u.1 a₀ = v.1 a₀) (a : El γ) :
    d.1 (spltFn d u v a₀ a) = spltFn d u v a₀ a ∧
      u.1 (spltFn d u v a₀ a) = v.1 (spltFn d u v a₀ a) := by
  by_cases h : toNat (d.1 a) = toNat a ∧ toNat (u.1 a) = toNat (v.1 a)
  · rw [show spltFn d u v a₀ a = a from
      if_pos ⟨congrArg toNat (toNat_inj h.1), congrArg toNat (toNat_inj h.2)⟩]
    exact ⟨toNat_inj h.1, toNat_inj h.2⟩
  · -- `h` is exactly the negated if-condition; the show refolds `spltFn` for rw's syntactic match
    rw [show spltFn d u v a₀ a = a₀ from if_neg h]
    exact ⟨h₀d, h₀uv⟩

theorem spltFn_idem (a₀ : El γ) (h₀d : d.1 a₀ = a₀) (h₀uv : u.1 a₀ = v.1 a₀) (a : El γ) :
    spltFn d u v a₀ (spltFn d u v a₀ a) = spltFn d u v a₀ a :=
  if_pos ⟨congrArg toNat (spltFn_mem d u v a₀ h₀d h₀uv a).1,
    congrArg toNat (spltFn_mem d u v a₀ h₀d h₀uv a).2⟩

/-- `spltFn` is a P-morphism (arithmetization of the definition-by-cases). -/
theorem spltFn_pmor (a₀ : El γ) : IsPMor γ γ (spltFn d u v a₀) := by
  match γ, d, u, v, a₀ with
  | some n, _, _, _, _ => exact trivial
  | none, d, u, v, a₀ =>
    have hind1 : PrimRec1 fun k => eqInd (toNat (d.1 k)) k :=
      PrimRec1.comp2 PrimRec2.eqInd d.2 PrimRec1.id
    have hind2 : PrimRec1 fun k => eqInd (toNat (u.1 k)) (toNat (v.1 k)) :=
      PrimRec1.comp2 PrimRec2.eqInd u.2 v.2
    have ht : PrimRec1 fun k =>
        eqInd (toNat (d.1 k)) k * eqInd (toNat (u.1 k)) (toNat (v.1 k)) :=
      PrimRec1.mul hind1 hind2
    have harith : PrimRec1 fun k =>
        k * (eqInd (toNat (d.1 k)) k * eqInd (toNat (u.1 k)) (toNat (v.1 k))) +
          a₀ * (1 - eqInd (toNat (d.1 k)) k * eqInd (toNat (u.1 k)) (toNat (v.1 k))) :=
      PrimRec1.add (PrimRec1.mul PrimRec1.id ht)
        (PrimRec1.mul (PrimRec1.const a₀) (PrimRec1.sub (PrimRec1.const 1) ht))
    have hpt : ∀ k : Nat,
        k * (eqInd (toNat (d.1 k)) k * eqInd (toNat (u.1 k)) (toNat (v.1 k))) +
          a₀ * (1 - eqInd (toNat (d.1 k)) k * eqInd (toNat (u.1 k)) (toNat (v.1 k)))
          = spltFn d u v a₀ k := by
      intro k
      by_cases h1 : toNat (d.1 k) = k
      · by_cases h2 : toNat (u.1 k) = toNat (v.1 k)
        · have : spltFn d u v a₀ k = k := if_pos ⟨h1, h2⟩
          rw [eqInd_eq h1, eqInd_eq h2, this]
          simp
        · have : spltFn d u v a₀ k = a₀ := if_neg fun hc => h2 hc.2
          rw [eqInd_eq h1, eqInd_ne h2, this]
          simp
      · have : spltFn d u v a₀ k = a₀ := if_neg fun hc => h1 hc.1
        rw [eqInd_ne h1, this]
        simp
    exact harith.congr hpt

end SpltFn

section PhatEqualizer

variable {E F : PhatObj} (x y : E ⟶ F)

/-- Values of cone maps into `(γ,d)` are `d`-fixed and `x,y`-agreeing. -/
theorem cone_mem (c : EqualizerCone x y) (w : El c.dom.carrier) :
    E.e.1 (c.map.1.1 w) = c.map.1.1 w ∧
      x.1.1 (c.map.1.1 w) = y.1.1 (c.map.1.1 w) :=
  ⟨PMor.congr c.map.2.2 w, PMor.congr (congrArg Subtype.val c.eq) w⟩

variable (a₀ : El E.carrier)

/-- The generalized §1.573 idempotent as a P-morphism on the carrier. -/
def phatEqIdemP : E.carrier ⟶ E.carrier :=
  ⟨spltFn E.e x.1 y.1 a₀, spltFn_pmor E.e x.1 y.1 a₀⟩

variable (h₀d : E.e.1 a₀ = a₀) (h₀uv : x.1.1 a₀ = y.1.1 a₀)

/-- The equalizer object of P̂: the carrier of `E` with the §1.573 idempotent. -/
def phatEqObj : PhatObj :=
  ⟨E.carrier, phatEqIdemP x y a₀,
    PMor.ext (spltFn_idem E.e x.1 y.1 a₀ h₀d h₀uv)⟩

/-- The equalizing map `(carrier, e′) → E` of P̂ (underlying function `e′`). -/
def phatEqMap : phatEqObj x y a₀ h₀d h₀uv ⟶ E := by
  refine ⟨phatEqIdemP (E := E) (F := F) x y a₀, PMor.ext ?_, PMor.ext ?_⟩
  · exact spltFn_idem E.e x.1 y.1 a₀ h₀d h₀uv
  · exact fun a => (spltFn_mem E.e x.1 y.1 a₀ h₀d h₀uv a).1

/-- §1.573 executed in P̂: with an agreement witness `a₀`, `(carrier, e′)`
    equalizes `x, y`. -/
def phatEqWitness : HasEqualizer x y where
  cone :=
    ⟨phatEqObj x y a₀ h₀d h₀uv, phatEqMap x y a₀ h₀d h₀uv,
      PhatHom.ext (PMor.ext fun a => (spltFn_mem E.e x.1 y.1 a₀ h₀d h₀uv a).2)⟩
  lift c :=
    ⟨c.map.1, c.map.2.1,
      PMor.ext fun w => if_pos ⟨congrArg toNat (cone_mem x y c w).1,
        congrArg toNat (cone_mem x y c w).2⟩⟩
  fac c := PhatHom.ext (PMor.ext fun w =>
    if_pos ⟨congrArg toNat (cone_mem x y c w).1, congrArg toNat (cone_mem x y c w).2⟩)
  uniq c m hm := PhatHom.ext (PMor.ext fun w =>
    calc m.1.1 w = spltFn E.e x.1 y.1 a₀ (m.1.1 w) := (PMor.congr m.2.2 w).symm
      _ = c.map.1.1 w := PMor.congr (congrArg Subtype.val hm) w)

/-- No agreement anywhere: the empty object `(0, 1)` equalizes `x, y` in P̂. -/
def phatEqEmpty (hno : ∀ a : El E.carrier, ¬(E.e.1 a = a ∧ x.1.1 a = y.1.1 a)) :
    HasEqualizer x y where
  cone :=
    ⟨embP (some 0 : ExtNat),
      ⟨⟨fun w => w.elim0, isPMor_finite _⟩,
        PMor.ext fun w => w.elim0, PMor.ext fun w => w.elim0⟩,
      PhatHom.ext (PMor.ext fun w => w.elim0)⟩
  lift c :=
    ⟨⟨fun w => absurd (cone_mem x y c w) (hno _), isPMor_ofEmpty _⟩,
      PMor.ext fun w => absurd (cone_mem x y c w) (hno _),
      PMor.ext fun w => absurd (cone_mem x y c w) (hno _)⟩
  fac c := PhatHom.ext (PMor.ext fun w => absurd (cone_mem x y c w) (hno _))
  uniq _ m _ := PhatHom.ext (PMor.ext fun w => (m.1.1 w).elim0)

open Classical in
/-- Equalizers in P̂ — §1.573: splitting all idempotents repairs the equalizers.
    (The case split on inhabitation of the agreement set is classical, exactly as
    for R's equalizers in §1.572.) -/
noncomputable def phatEqOf : HasEqualizer x y :=
  if h : ∃ a : El E.carrier, E.e.1 a = a ∧ x.1.1 a = y.1.1 a then
    phatEqWitness x y h.choose h.choose_spec.1 h.choose_spec.2
  else
    phatEqEmpty x y fun a ha => h ⟨a, ha⟩

end PhatEqualizer

noncomputable instance : HasEqualizers PhatObj := ⟨fun _ _ x y => phatEqOf x y⟩

/-- **§1.573 headline**: P̂ = Spl(P) is a cartesian category. -/
noncomputable instance phatCartesian : CartesianCategory PhatObj := {}

/-- §1.573 as stated in the book: a parallel pair from ω in P acquires an equalizer
    once the idempotents are split. -/
noncomputable example {α : PObj} (x y : omegaP ⟶ α) :
    HasEqualizer (embPFunctor.map x) (embPFunctor.map y) := phatEqOf _ _

/-! ## Part 6: §1.574 — the functor P̂ → 𝒮 represented by ω is faithful

  We formalize the faithfulness of the representable functor `P̂(ω̂, −)`.  (The book
  further calls it a "set-valued representation of regular categories"; P̂'s regular
  structure is not developed here.  The companion §1.574 claims — a one-to-one onto
  `x : ω → ω` in P with `x⁻¹ ∉ P`, whence R is a category of fractions of P — need an
  Ackermann-style growth argument and are not formalized; see the header.) -/

/-- ω̂: the image of ω in P̂. -/
def omegaPhat : PhatObj := embP omegaP

/-- The set-valued functor `P̂(ω̂, −)` represented by ω̂. -/
def phatPoints (E : PhatObj) : Type := omegaPhat ⟶ E

def phatPointsFunctor : Functor PhatObj Type where
  obj := phatPoints
  map φ := fun h => h ≫ φ
  map_id _ := funext fun h => Cat.comp_id h
  map_comp φ ψ := funext fun h => (Cat.assoc h φ ψ).symm

/-- The constant point of `E` through the idempotent: `k ↦ e(a)`. -/
def pointAt {E : PhatObj} (a : El E.carrier) : phatPoints E :=
  ⟨⟨fun _ => E.e.1 a, PrimRec1.const (toNat (E.e.1 a))⟩,
    PMor.ext fun _ => rfl,
    PMor.ext fun _ => PMor.congr E.idem a⟩

/-- **§1.574**: the representable functor `P̂(ω̂,−) : P̂ → 𝒮` is faithful — it
    separates maps (the repo's cross-universe faithfulness for 𝒮-valued functors). -/
theorem phatPoints_separates : SeparatesMaps phatPointsFunctor := by
  intro E F φ ψ h
  refine PhatHom.ext (PMor.ext fun a => ?_)
  have hpt : pointAt a ≫ φ = pointAt a ≫ ψ := congrFun h (pointAt a)
  have h0 : φ.1.1 (E.e.1 a) = ψ.1.1 (E.e.1 a) :=
    PMor.congr (congrArg Subtype.val hpt) (0 : Nat)
  calc φ.1.1 a = φ.1.1 (E.e.1 a) := (PMor.congr φ.2.1 a).symm
    _ = ψ.1.1 (E.e.1 a) := h0
    _ = ψ.1.1 a := PMor.congr ψ.2.1 a

end Freyd.Pcat
