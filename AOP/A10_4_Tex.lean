/-
  Bird & de Moor, *Algebra of Programming* §10.4  The TeX problem (book pp. 259-263) — a worked
  program in the Set model, over CONS-lists of digits.

  `intern` reads a decimal as the nearest multiple of `2⁻¹⁶`; `extern` is its shortest inverse —
  the shortest decimal whose internal representation is the given multiple.  The specification is
  `min R·Λ(intern°)`, mirrored `Λ (intern°) ≫ est R` with `R ≜ length ≤ length°`, and the
  derivation is three steps: pull the MAP `interval` out of the transpose (B&dM p.260, `round°`
  itself is not a map), fuse `inrange° val` into the fold `⦇[arb,step]⦈` (p.260), and apply
  Theorem 10.1 at `Q ≜ (l°!°r) ∪ 𝟙` (p.262), which prefers stopping whenever stopping is legal.

  THE OBJECT `Real`.  Every real the problem reaches is `m/(w·10ᵏ)` with `w ≜ 2¹⁷`: `interval n`
  is `(2n∓1)/w`, and each digit of a decimal divides by a further ten.  `Real` is therefore built
  here as those fractions — `(m,k)` denoting `m/(w·10ᵏ)`, quotiented by cross-multiplication — and
  not as a general real line, which would need a completion nothing in §10.4 uses.  The scale `w`
  is carried in the denominator rather than multiplying `r`, so `round r = n ⟺ 2n−1 < wr < 2n+1`
  is read off as `(2n−1)/w < r < (2n+1)/w`; the two are the same inequality.

  THE TYPE RESTRICTION (10.9).  Following B&dM p.261, `Interval` is the pairs `(a,b)` with
  `0<b<1` and `a<b`, and `step_legal` is what types `step : Digit×Interval⟶Interval`.  Over it the
  p.260 fusion is an inclusion, `⦇[arb,step]⦈⊑val inrange°`: a decimal's value lies inside every
  interval its digits fold to, but an interval wider than one digit's cell is folded to by no
  decimal.  What makes the restriction harmless is `tex_restrict`: the shortest decimal among
  those `⦇[arb,step]⦈°` allows is a shortest one among ALL decimals inside the interval.
-/
module

public import AOP.A10_1
public import AOP.A6_ConsList
import AOP.CalcSteps

namespace Freyd.Alg.RelSet.Tex

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL

/-! ## `Real` (`tex-defn`) -/

/-- **tex-defn**: `w≜2¹⁷`. -/
@[expose] public def w : Int := 131072

/-- `10ᵏ`, the decimal part of a representative's denominator. -/
@[expose] public def sc (k : Nat) : Int := (10 : Int) ^ k

public theorem sc_pos (k : Nat) : 0 < sc k := Int.pow_pos (by decide)

public theorem sc_zero : sc 0 = 1 := rfl

public theorem sc_succ (k : Nat) : sc (k + 1) = sc k * 10 := by
  simp [sc, Int.pow_succ]

/-- A real of this problem, as a representative: `(m,k)` denotes `m/(w·10ᵏ)`. -/
@[expose] public abbrev PreReal : Type := Int × Nat

/-- Two representatives denote the same real. -/
@[expose] public def preEq (x y : PreReal) : Prop := x.1 * sc y.2 = y.1 * sc x.2

/-- `<` on representatives. -/
@[expose] public def preLt (x y : PreReal) : Prop := x.1 * sc y.2 < y.1 * sc x.2

public theorem cancel_right {a b c : Int} (hc : 0 < c) (h : a * c = b * c) : a = b :=
  Int.eq_of_mul_eq_mul_right (by omega) h

public theorem preEq_trans {x y z : PreReal} (h1 : preEq x y) (h2 : preEq y z) : preEq x z := by
  refine cancel_right (sc_pos y.2) ?_
  calc x.1 * sc z.2 * sc y.2
      = x.1 * sc y.2 * sc z.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = y.1 * sc x.2 * sc z.2 := by rw [h1]
    _ = y.1 * sc z.2 * sc x.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = z.1 * sc y.2 * sc x.2 := by rw [h2]
    _ = z.1 * sc x.2 * sc y.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

public theorem preLt_trans {x y z : PreReal} (h1 : preLt x y) (h2 : preLt y z) : preLt x z := by
  refine (Int.mul_lt_mul_right (sc_pos y.2)).mp ?_
  have a1 : x.1 * sc y.2 * sc z.2 < y.1 * sc x.2 * sc z.2 :=
    (Int.mul_lt_mul_right (sc_pos z.2)).mpr h1
  have a2 : y.1 * sc z.2 * sc x.2 < z.1 * sc y.2 * sc x.2 :=
    (Int.mul_lt_mul_right (sc_pos x.2)).mpr h2
  have e1 : x.1 * sc z.2 * sc y.2 = x.1 * sc y.2 * sc z.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : y.1 * sc x.2 * sc z.2 = y.1 * sc z.2 * sc x.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e3 : z.1 * sc y.2 * sc x.2 = z.1 * sc x.2 * sc y.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e2] at a1
  rw [e3] at a2
  rw [e1]
  exact Int.lt_trans a1 a2

public instance realSetoid : Setoid PreReal where
  r := preEq
  iseqv := ⟨fun _ => rfl, fun h => h.symm, preEq_trans⟩

/-- **tex-defn**: the object `Real` — the fractions `m/(w·10ᵏ)`. -/
@[expose] public abbrev Real : RelSet.{0} := ⟨Quotient realSetoid⟩

@[expose] public def mkR (x : PreReal) : Real.carrier := Quotient.mk realSetoid x

public theorem preLt_of_preEq_left {x x' y : PreReal} (h : preEq x x') (hlt : preLt x y) :
    preLt x' y := by
  have h1 : x.1 * sc y.2 * sc x'.2 < y.1 * sc x.2 * sc x'.2 :=
    (Int.mul_lt_mul_right (sc_pos x'.2)).mpr hlt
  have e1 : x.1 * sc y.2 * sc x'.2 = x'.1 * sc y.2 * sc x.2 := by
    calc x.1 * sc y.2 * sc x'.2
        = x.1 * sc x'.2 * sc y.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = x'.1 * sc x.2 * sc y.2 := by rw [h]
      _ = x'.1 * sc y.2 * sc x.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : y.1 * sc x.2 * sc x'.2 = y.1 * sc x'.2 * sc x.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1, e2] at h1
  exact (Int.mul_lt_mul_right (sc_pos x.2)).mp h1

public theorem preLt_of_preEq_right {x y y' : PreReal} (h : preEq y y') (hlt : preLt x y) :
    preLt x y' := by
  have h1 : x.1 * sc y.2 * sc y'.2 < y.1 * sc x.2 * sc y'.2 :=
    (Int.mul_lt_mul_right (sc_pos y'.2)).mpr hlt
  have e1 : x.1 * sc y.2 * sc y'.2 = x.1 * sc y'.2 * sc y.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : y.1 * sc x.2 * sc y'.2 = y'.1 * sc x.2 * sc y.2 := by
    calc y.1 * sc x.2 * sc y'.2
        = y.1 * sc y'.2 * sc x.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = y'.1 * sc y.2 * sc x.2 := by rw [h]
      _ = y'.1 * sc x.2 * sc y.2 := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1, e2] at h1
  exact (Int.mul_lt_mul_right (sc_pos y.2)).mp h1

/-- `<` on `Real`, the relation every inequality of §10.4 is read through. -/
@[expose] public def rlt : Real ⟶ Real := fun x y =>
  Quotient.liftOn₂ x y preLt fun _ _ _ _ hac hbd =>
    propext ⟨fun h => preLt_of_preEq_right hbd (preLt_of_preEq_left hac h),
      fun h => preLt_of_preEq_right hbd.symm (preLt_of_preEq_left hac.symm h)⟩

public theorem rlt_mk (x y : PreReal) : rlt (mkR x) (mkR y) ↔ preLt x y := Iff.rfl

public theorem rlt_trans {x y z : Real.carrier} : rlt x y → rlt y z → rlt x z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c
  exact preLt_trans

/-! ## `zero`, `shift` and the inverse of `shift` (`tex-defn`) -/

/-- **tex-defn**: `zero`, the value of the empty decimal. -/
@[expose] public def zeroR : Real.carrier := mkR (0, 0)

/-- `1`, the upper bound (10.9) puts on an interval. -/
@[expose] public def oneR : Real.carrier := mkR (w, 0)

@[expose] public def shiftPre (d : Int) (x : PreReal) : PreReal :=
  (d * w * sc x.2 + x.1, x.2 + 1)

public theorem shiftPre_congr (d : Int) {x y : PreReal} (h : preEq x y) :
    preEq (shiftPre d x) (shiftPre d y) := by
  show (d * w * sc x.2 + x.1) * sc (y.2 + 1) = (d * w * sc y.2 + y.1) * sc (x.2 + 1)
  rw [sc_succ, sc_succ, Int.add_mul, Int.add_mul]
  have h' : x.1 * (sc y.2 * 10) = y.1 * (sc x.2 * 10) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, h]
  rw [h']
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- **tex-defn**: `shift(d,r)=(d+r)/10`. -/
@[expose] public def shiftFn (d : Int) (r : Real.carrier) : Real.carrier :=
  Quotient.liftOn r (fun x => mkR (shiftPre d x))
    fun _ _ h => Quotient.sound (shiftPre_congr d h)

@[expose] public def unshiftPre (d : Int) (x : PreReal) : PreReal :=
  (10 * x.1 - d * w * sc x.2, x.2)

public theorem unshiftPre_congr (d : Int) {x y : PreReal} (h : preEq x y) :
    preEq (unshiftPre d x) (unshiftPre d y) := by
  show (10 * x.1 - d * w * sc x.2) * sc y.2 = (10 * y.1 - d * w * sc y.2) * sc x.2
  rw [Int.sub_mul, Int.sub_mul]
  have h' : 10 * x.1 * sc y.2 = 10 * y.1 * sc x.2 := by
    calc 10 * x.1 * sc y.2 = 10 * (x.1 * sc y.2) := by rw [Int.mul_assoc]
      _ = 10 * (y.1 * sc x.2) := by rw [h]
      _ = 10 * y.1 * sc x.2 := by rw [Int.mul_assoc]
  have e : d * w * sc x.2 * sc y.2 = d * w * sc y.2 * sc x.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h', e]

/-- `10a−d`, the inverse of `shiftFn d` — the step the program takes when it emits `d`. -/
@[expose] public def unshift (d : Int) (r : Real.carrier) : Real.carrier :=
  Quotient.liftOn r (fun x => mkR (unshiftPre d x))
    fun _ _ h => Quotient.sound (unshiftPre_congr d h)

public theorem shift_unshift (d : Int) (r : Real.carrier) : shiftFn d (unshift d r) = r := by
  refine Quotient.inductionOn r ?_
  intro x
  refine Quotient.sound ?_
  show (d * w * sc x.2 + (10 * x.1 - d * w * sc x.2)) * sc x.2 = x.1 * sc (x.2 + 1)
  have e : d * w * sc x.2 + (10 * x.1 - d * w * sc x.2) = 10 * x.1 := by omega
  rw [e, sc_succ]
  simp [Int.mul_assoc, Int.mul_comm]

/-- `shiftFn d` is strictly monotone, and that is the whole content of the fusion's step case. -/
public theorem shift_lt_shift (d : Int) (x y : Real.carrier) :
    rlt (shiftFn d x) (shiftFn d y) ↔ rlt x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  show (d * w * sc a.2 + a.1) * sc (b.2 + 1) < (d * w * sc b.2 + b.1) * sc (a.2 + 1)
    ↔ a.1 * sc b.2 < b.1 * sc a.2
  rw [sc_succ, sc_succ, Int.add_mul, Int.add_mul]
  have e : d * w * sc a.2 * (sc b.2 * 10) = d * w * sc b.2 * (sc a.2 * 10) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have f1 : a.1 * (sc b.2 * 10) = a.1 * sc b.2 * 10 := by rw [Int.mul_assoc]
  have f2 : b.1 * (sc a.2 * 10) = b.1 * sc a.2 * 10 := by rw [Int.mul_assoc]
  rw [e, f1, f2]
  constructor
  · intro h
    exact (Int.mul_lt_mul_right (by decide : (0:Int) < 10)).mp (by omega)
  · intro h
    have h2 : a.1 * sc b.2 * 10 < b.1 * sc a.2 * 10 :=
      (Int.mul_lt_mul_right (by decide : (0:Int) < 10)).mpr h
    omega

public theorem lt_shift_iff (d : Int) (a r : Real.carrier) :
    rlt a (shiftFn d r) ↔ rlt (unshift d a) r := by
  rw [← shift_lt_shift d (unshift d a) r, shift_unshift]

public theorem shift_lt_iff (d : Int) (r b : Real.carrier) :
    rlt (shiftFn d r) b ↔ rlt r (unshift d b) := by
  rw [← shift_lt_shift d r (unshift d b), shift_unshift]

public theorem unshift_shift (d : Int) (r : Real.carrier) : unshift d (shiftFn d r) = r := by
  refine Quotient.inductionOn r ?_
  intro x
  refine Quotient.sound ?_
  show (10 * (d * w * sc x.2 + x.1) - d * w * sc (x.2 + 1)) * sc x.2 = x.1 * sc (x.2 + 1)
  rw [sc_succ]
  have e1 : d * w * (sc x.2 * 10) = 10 * (d * w * sc x.2) := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have e : 10 * (d * w * sc x.2 + x.1) - d * w * (sc x.2 * 10) = 10 * x.1 := by
    rw [e1, Int.mul_add]; omega
  rw [e]
  simp [Int.mul_assoc, Int.mul_comm]

public theorem unshift_lt (d : Int) {x y : Real.carrier} (h : rlt x y) :
    rlt (unshift d x) (unshift d y) := by
  rw [← shift_lt_shift d, shift_unshift, shift_unshift]; exact h

/-- `<` on `Real` is decided by the integers under it, so the case split needs no choice. -/
public theorem rlt_em (x y : Real.carrier) : rlt x y ∨ ¬ rlt x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact Decidable.em (a.1 * sc b.2 < b.1 * sc a.2)

public theorem rlt_irrefl (x : Real.carrier) : ¬ rlt x x := by
  refine Quotient.inductionOn x ?_
  intro a h
  exact Int.lt_irrefl _ (h : a.1 * sc a.2 < a.1 * sc a.2)

/-- `x<y≤z ⟹ x<z`, with `y≤z` read as `¬ z<y`. -/
public theorem rlt_le_trans {x y z : Real.carrier} : rlt x y → ¬ rlt z y → rlt x z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c h1 h2
  have h1' : a.1 * sc b.2 < b.1 * sc a.2 := h1
  have h2' : ¬ c.1 * sc b.2 < b.1 * sc c.2 := h2
  show a.1 * sc c.2 < c.1 * sc a.2
  refine (Int.mul_lt_mul_right (sc_pos b.2)).mp ?_
  have a1 : a.1 * sc b.2 * sc c.2 < b.1 * sc a.2 * sc c.2 :=
    (Int.mul_lt_mul_right (sc_pos c.2)).mpr h1'
  have a2 : b.1 * sc c.2 * sc a.2 ≤ c.1 * sc b.2 * sc a.2 :=
    Int.mul_le_mul_of_nonneg_right (Int.not_lt.mp h2') (Int.le_of_lt (sc_pos a.2))
  have e1 : a.1 * sc c.2 * sc b.2 = a.1 * sc b.2 * sc c.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : b.1 * sc a.2 * sc c.2 = b.1 * sc c.2 * sc a.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e3 : c.1 * sc b.2 * sc a.2 = c.1 * sc a.2 * sc b.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1]; rw [e2] at a1; rw [e3] at a2
  exact Int.lt_of_lt_of_le a1 a2

/-- `x≤y<z ⟹ x<z`, with `x≤y` read as `¬ y<x`. -/
public theorem le_rlt_trans {x y z : Real.carrier} : ¬ rlt y x → rlt y z → rlt x z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro a b c h1 h2
  have h1' : ¬ b.1 * sc a.2 < a.1 * sc b.2 := h1
  have h2' : b.1 * sc c.2 < c.1 * sc b.2 := h2
  show a.1 * sc c.2 < c.1 * sc a.2
  refine (Int.mul_lt_mul_right (sc_pos b.2)).mp ?_
  have a1 : a.1 * sc b.2 * sc c.2 ≤ b.1 * sc a.2 * sc c.2 :=
    Int.mul_le_mul_of_nonneg_right (Int.not_lt.mp h1') (Int.le_of_lt (sc_pos c.2))
  have a2 : b.1 * sc c.2 * sc a.2 < c.1 * sc b.2 * sc a.2 :=
    (Int.mul_lt_mul_right (sc_pos a.2)).mpr h2'
  have e1 : a.1 * sc c.2 * sc b.2 = a.1 * sc b.2 * sc c.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : b.1 * sc a.2 * sc c.2 = b.1 * sc c.2 * sc a.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e3 : c.1 * sc b.2 * sc a.2 = c.1 * sc a.2 * sc b.2 := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1]; rw [e2] at a1; rw [e3] at a2
  exact Int.lt_of_le_of_lt a1 a2

/-- `(e+1)/10≤(d+0)/10` for `e+1≤d`: the cell of a smaller leading digit ends where a larger one's
    begins. -/
public theorem shift_le_digit (e d : Int) (h : e + 1 ≤ d) :
    ¬ rlt (shiftFn d zeroR) (shiftFn e oneR) := by
  show ¬ (d * w * sc 0 + 0) * sc (0 + 1) < (e * w * sc 0 + w) * sc (0 + 1)
  simp only [sc_succ, sc_zero, w, Int.mul_one, Int.one_mul, Int.add_zero]
  omega

public theorem zero_le_shift (e : Int) (he : 0 ≤ e) : ¬ rlt (shiftFn e zeroR) zeroR := by
  show ¬ (e * w * sc 0 + 0) * sc 0 < 0 * sc (0 + 1)
  simp only [sc_succ, sc_zero, w, Int.mul_one, Int.one_mul, Int.add_zero]
  omega

public theorem shift_one_le_one (e : Int) (he : e ≤ 9) : ¬ rlt oneR (shiftFn e oneR) := by
  show ¬ w * sc (0 + 1) < (e * w * sc 0 + w) * sc 0
  simp only [sc_succ, sc_zero, w, Int.mul_one, Int.one_mul]
  omega

/-! ## The objects and arrows of §10.4 (`tex-defn`) -/

/-- **tex-defn**: a digit. -/
@[expose] public abbrev Digit : Type := Fin 10

/-- **tex-defn**: the carrier of `Decimal` — a cons-list of digits.  It carries a name of its own
    because the note draws ONE wire from `[0,2¹⁶)` to `Decimal` and never opens the list. -/
@[expose] public def Dec : Type := ConsList Unit Digit

-- **tex-defn**: the object `Decimal`.  NOTATION over the list relator's object, not a `def` at
-- `RelSet`: a named object draws as one opaque wire, and `Decimal` IS a list of digits, so the
-- term stays structural and every panel peels it into the list lane over `Digit`.
macro:max "Decimal" : term => `(Freyd.Alg.RelSet.ListRel.dList Digit)

/-- **tex-defn**: the object `[0,2¹⁶)`. -/
@[expose] public def Ix : RelSet.{0} := ⟨Fin 65536⟩

/-- **tex-defn**: a pair `(a,b)`.  A structure and not `Real×Real` for the reason `Dec` is a name:
    the note draws `Interval` as ONE wire, and a product carrier is what a circuit opens into two. -/
public structure Iv where
  lo : Real.carrier
  hi : Real.carrier

/-- **(10.9)**: the pairs `(a,b)` with `0<b<1` and `a<b`. -/
@[expose] public def Legal (p : Iv) : Prop :=
  rlt zeroR p.hi ∧ rlt p.hi oneR ∧ rlt p.lo p.hi

/-- **tex-defn**: the object `Interval` — the pairs `(a,b)` satisfying (10.9) (B&dM p.261). -/
@[expose] public def Interval : RelSet.{0} := ⟨{p : Iv // Legal p}⟩

/-- `interval n` satisfies (10.9): `0<(2n+1)/2¹⁷<1` for `n<2¹⁶`. -/
public theorem interval_legal (n : Fin 65536) :
    Legal ⟨mkR (2 * (n.val : Int) - 1, 0), mkR (2 * (n.val : Int) + 1, 0)⟩ := by
  have hn := n.isLt
  refine ⟨?_, ?_, ?_⟩
  · show (0 : Int) * sc 0 < (2 * (n.val : Int) + 1) * sc 0
    rw [sc_zero]; omega
  · show (2 * (n.val : Int) + 1) * sc 0 < w * sc 0
    rw [sc_zero]; simp only [w]; omega
  · show (2 * (n.val : Int) - 1) * sc 0 < (2 * (n.val : Int) + 1) * sc 0
    rw [sc_zero]; omega

/-- **tex-defn**: `interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`. -/
@[expose] public def intervalFn (n : Fin 65536) : Interval.carrier :=
  ⟨⟨mkR (2 * (n.val : Int) - 1, 0), mkR (2 * (n.val : Int) + 1, 0)⟩, interval_legal n⟩

/-- **tex-defn**: `interval`, a map. -/
@[expose] public def interval : Ix ⟶ Interval := graph intervalFn

public theorem interval_map : Map interval := graph_map intervalFn

/-- **tex-defn**: `r inrange (a,b)⟺a<r<b`. -/
@[expose] public def inrange : Interval ⟶ Real := fun p r => rlt p.1.lo r ∧ rlt r p.1.hi

/-- **tex-defn**: `round r=n⟺2n−1<2¹⁷r<2n+1`, read as `(2n−1)/2¹⁷<r<(2n+1)/2¹⁷`. -/
@[expose] public def round : Real ⟶ Ix := fun r n =>
  rlt (mkR (2 * (n.val : Int) - 1, 0)) r ∧ rlt r (mkR (2 * (n.val : Int) + 1, 0))

/-- **tex-defn**: `round°=interval inrange` — `round` is not a map, but `interval` is, and that
    is what lets the next step take `interval` out of the transpose. -/
public theorem round_recip : (round)° = interval ≫ inrange := by
  apply hom_ext
  intro n r
  exact ⟨fun h => ⟨intervalFn n, rfl, h⟩, fun h => by obtain ⟨p, hp, hq⟩ := h; subst hp; exact hq⟩

/-- **tex-defn**: `zero : 𝟏⟶Real`, the value of the empty decimal. -/
@[expose] public def zero : dL Unit ⟶ Real := graph fun _ => zeroR

/-- **tex-defn**: `shift : Digit×Real⟶Real`, the map `shiftFn` is the graph of. -/
@[expose] public def shift : (⟨Digit × Real.carrier⟩ : RelSet.{0}) ⟶ Real :=
  graph fun p => shiftFn (p.1.val : Int) p.2

/-- The coproduct `1+(Digit×Real)` the algebra `[zero,shift]` is the case analysis over. -/
@[expose] public abbrev copR : Coproduct ((F Unit Digit).obj Real) (dL Unit)
    (⟨Digit × Real.carrier⟩ : RelSet.{0}) := sumCop (dL Unit) ⟨Digit × Real.carrier⟩

/-- **tex-defn**: `val≜⦇[zero,shift]⦈`. -/
@[expose] public def val : Decimal ⟶ Real := cataR (junc copR zero shift)

/-- **tex-defn**: `intern≜val round`. -/
@[expose] public def intern : Decimal ⟶ Ix := val ≫ round

/-- **(10.9)** for `arb`: `a<0<b` already gives `a<b`, so a pair `arb` returns is legal as soon as
    `b<1` — "we can always restrict `arb` so that it returns an interval satisfying (10.9)". -/
public theorem arb_legal (p : Iv) (hb : rlt p.hi oneR)
    (harb : rlt p.lo zeroR ∧ rlt zeroR p.hi) : Legal p :=
  ⟨harb.2, hb, rlt_trans harb.1 harb.2⟩

/-- **(10.9)** for `step` (B&dM p.261): if `(a',b')` satisfies (10.9) then so does
    `((d+a')/10,(d+b')/10)`, which is what types `step : Digit×Interval⟶Interval`. -/
public theorem step_legal (d : Digit) (q : Iv) (h : Legal q) :
    Legal ⟨shiftFn (d.val : Int) q.lo, shiftFn (d.val : Int) q.hi⟩ := by
  obtain ⟨h0, h1, hab⟩ := h
  refine ⟨?_, ?_, (shift_lt_shift _ _ _).mpr hab⟩
  · show rlt zeroR (shiftFn (d.val : Int) q.2)
    revert h0
    refine Quotient.inductionOn q.2 ?_
    intro b hb
    have hb' : (0:Int) * sc b.2 < b.1 * sc 0 := hb
    have hd : (0:Int) ≤ (d.val : Int) := by omega
    have hnn : 0 ≤ (d.val : Int) * (w * sc b.2) :=
      Int.mul_nonneg hd (Int.le_of_lt (Int.mul_pos (by decide) (sc_pos b.2)))
    show (0:Int) * sc (b.2 + 1) < ((d.val : Int) * w * sc b.2 + b.1) * sc 0
    rw [sc_zero] at hb' ⊢
    rw [show (d.val : Int) * w * sc b.2 = (d.val : Int) * (w * sc b.2) from Int.mul_assoc _ _ _]
    omega
  · show rlt (shiftFn (d.val : Int) q.2) oneR
    revert h1
    refine Quotient.inductionOn q.2 ?_
    intro b hb
    have hb' : b.1 * sc 0 < w * sc b.2 := hb
    have hd : (d.val : Int) ≤ 9 := by omega
    have hmul : (d.val : Int) * (w * sc b.2) ≤ 9 * (w * sc b.2) :=
      Int.mul_le_mul_of_nonneg_right hd (Int.le_of_lt (Int.mul_pos (by decide) (sc_pos b.2)))
    show ((d.val : Int) * w * sc b.2 + b.1) * sc 0 < w * sc (b.2 + 1)
    rw [sc_zero] at hb' ⊢
    rw [sc_succ]
    have hw : w * (sc b.2 * 10) = 10 * (w * sc b.2) := by
      simp [Int.mul_comm, Int.mul_left_comm]
    rw [show (d.val : Int) * w * sc b.2 = (d.val : Int) * (w * sc b.2) from Int.mul_assoc _ _ _,
      hw]
    omega

/-- **tex-defn**: `step(d,(a,b))=((d+a)/10,(d+b)/10)`, legal by `step_legal`. -/
@[expose] public def stepFn (p : Digit × Interval.carrier) : Interval.carrier :=
  ⟨⟨shiftFn (p.1.val : Int) p.2.1.lo, shiftFn (p.1.val : Int) p.2.1.hi⟩, step_legal p.1 p.2.1 p.2.2⟩

/-- **tex-defn**: `arb : 𝟏⟶Interval` — B&dM p.260's first fusion condition `arb=zero inrange°`, so
    `(a,b)` is an `arb` iff `a<0<b`. -/
@[expose] public def arb : dL Unit ⟶ Interval := fun _ p => rlt p.1.lo zeroR ∧ rlt zeroR p.1.hi

/-- **tex-defn**: `step : Digit×Interval⟶Interval`, the map `stepFn` is the graph of. -/
@[expose] public def step : (⟨Digit × Interval.carrier⟩ : RelSet.{0}) ⟶ Interval := graph stepFn

/-- The coproduct `1+(Digit×Interval)` the algebra `[arb,step]` is the case analysis over: the
    pattern functor's object action IS that sum, and `sumCop`'s injections are this file's `l`
    and `r`. -/
@[expose] public abbrev cop : Coproduct ((F Unit Digit).obj Interval) (dL Unit)
    (⟨Digit × Interval.carrier⟩ : RelSet.{0}) := sumCop (dL Unit) ⟨Digit × Interval.carrier⟩

/-- **tex-defn**: `H≜⦇[arb,step]⦈°`. -/
@[expose] public def H : Interval ⟶ Decimal := (cataR (junc cop arb step))°

/-- `length`, the number of digits of a decimal. -/
@[expose] public def length : ConsList Unit Digit → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons _ x => length x + 1

/-- **tex-defn**: `R≜length≤length°` — a shortest decimal is wanted. -/
@[expose] public def R : Decimal ⟶ Decimal := fun xs ys => length xs ≤ length ys

public theorem R_refl : 𝟙 Decimal ⊑ R :=
  le_iff.mpr fun x y h => by
    rw [id_apply] at h
    subst h; exact Nat.le_refl _

public theorem R_trans : R ≫ R ⊑ R :=
  le_iff.mpr fun x z h => by
    obtain ⟨y, h1, h2⟩ := h
    exact Nat.le_trans (h1 : length x ≤ length y) h2

/-- **tex-defn**: `l : 𝟏⟶FX`, the left injection of `FX=1+(Digit×X)`. -/
@[expose] public def l {X : RelSet.{0}} : dL Unit ⟶ (F Unit Digit).obj X := graph Sum.inl

/-- **tex-defn**: `r : Digit×X⟶FX`, the right injection. -/
@[expose] public def r {X : RelSet.{0}} : (⟨Digit × X.carrier⟩ : RelSet.{0}) ⟶ (F Unit Digit).obj X :=
  graph Sum.inr

/-- **`r` is LAX natural** in `X`: `F(S)` acts on the pair arm as `𝟙×S`. -/
public theorem r_laxNatural :
    LaxNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.const (dE Digit)) (Relator.idRelator RelSet.{0})))
      (Relator.prod (Relator.const (dE Digit)) (Relator.idRelator RelSet.{0}))
      (fun a : RelSet.{0} => r (X := a)) := by
  intro x y S
  rw [F_eq_sum_prod]
  refine le_iff.mpr fun p v h => ?_
  obtain ⟨q, hpq, hr⟩ := h
  have hv : v = Sum.inr q := hr
  subst hv
  refine ⟨Sum.inr p, rfl, ?_⟩
  obtain ⟨d, a⟩ := p
  obtain ⟨d', b⟩ := q
  simp [Relator.prod, Relator.const, Relator.idRelator, RelProd.pair, prodMap, graph,
    instPositiveAllegory, instHasRelProd] at hpq
  show Fmap Unit Digit S (Sum.inr (d, a)) (Sum.inr (d', b))
  exact hpq

/-- **`l°` is LAX natural** in `X`: `F(S)` leaves the leaf alone. -/
public theorem l_recip_laxNatural :
    LaxNatural (Relator.const (dL Unit))
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (Relator.const (dE Digit)) (Relator.idRelator RelSet.{0})))
      (fun a : RelSet.{0} => (l (X := a))°) := by
  intro x y S
  rw [F_eq_sum_prod]
  refine le_iff.mpr fun u t h => ?_
  obtain ⟨v, huv, hl⟩ := h
  have hv : v = Sum.inl t := hl
  subst hv
  match u, huv with
  | Sum.inl t', _ => cases t; cases t'; exact ⟨(), rfl, by simp [Relator.const]⟩
  | Sum.inr _, huv => exact huv.elim

/-- **tex-defn**: `! : Digit×Interval⟶𝟏`. -/
@[expose] public def bang : (⟨Digit × Interval.carrier⟩ : RelSet.{0}) ⟶ dL Unit :=
  graph fun _ => ()

/-- **tex-defn**: `Q≜(l°!°r) ∪ 𝟙` — with this `Q` the inhabitant of the terminal object is
    preferred whenever it is there, which is "stop as soon as stopping is legal". -/
@[expose] public def Q : (F Unit Digit).obj Interval ⟶ (F Unit Digit).obj Interval :=
  (l° ≫ bang° ≫ r) ∪ 𝟙 ((F Unit Digit).obj Interval)

/-! ## Fusion (B&dM p.260): `⦇[arb,step]⦈` refines `val inrange°` -/

/-- **tex-fusion**, the `zero` branch: `zero inrange°=arb`, B&dM p.260's first fusion condition,
    which determines `arb`. -/
public theorem tex_fusion_zero : zero ≫ (inrange)° = arb := by
  apply hom_ext
  intro u p
  exact ⟨fun ⟨_, hz, hin⟩ => by subst hz; exact hin, fun h => ⟨zeroR, rfl, h⟩⟩

/-- **tex-fusion**, the `shift` branch (B&dM pp.260-261): `(𝟙×inrange°)step⊑shift inrange°` —
    `10a−d<r<10b−d ⟹ a<(d+r)/10<b` for `(a,b)=step(d,(10a−d,10b−d))`.  Only an inclusion over
    `Interval`: `(10a−d,10b−d)` satisfies (10.9) only when `d<10b<d+1`. -/
public theorem tex_fusion_shift :
    rprodMap (𝟙 (dE Digit)) (inrange)° ≫ step ⊑ shift ≫ (inrange)° :=
  le_iff.mpr fun x p h => by
    obtain ⟨d, rr⟩ := x
    obtain ⟨⟨d', q2⟩, ⟨hd, hin⟩, hp⟩ := h
    rw [id_apply] at hd
    subst hd
    have hp' : p = stepFn (d, q2) := hp
    subst hp'
    exact ⟨shiftFn (d.val : Int) rr, rfl, (shift_lt_shift _ _ _).mpr hin.1,
      (shift_lt_shift _ _ _).mpr hin.2⟩

/-- **tex-fusion**, the fusion condition (B&dM p.260): `F(inrange°)[arb,step]⊑[zero,shift] inrange°`.
    One `calc` step per hint: the relator slides into the bracket, the `shift` branch, the `zero`
    branch, composition distributes into the case analysis. -/
public theorem tex_fusion_condition :
    (F Unit Digit).map (inrange)° ≫ junc cop arb step ⊑ junc copR zero shift ≫ (inrange)° :=
  calc (F Unit Digit).map (inrange)° ≫ junc cop arb step
      = junc copR arb (rprodMap (𝟙 (dE Digit)) (inrange)° ≫ step) :=
        Fmap_comp_junc Unit Digit _ _ _
    _ ⊑ junc copR arb (shift ≫ (inrange)°) := junc_mono _ (le_refl arb) tex_fusion_shift
    _ = junc copR (zero ≫ (inrange)°) (shift ≫ (inrange)°) := by rw [tex_fusion_zero]
    _ = junc copR zero shift ≫ (inrange)° := (junc_comp _ _ _ _).symm

calc_steps tex_fusion_condition

/-- **tex-fusion** (B&dM p.260): `⦇[arb,step]⦈⊑val inrange°` — every interval a decimal's digits
    fold to has the decimal's value strictly inside it, because
    `F(inrange°)[arb,step]⊑[zero,shift] inrange°`. -/
public theorem tex_fusion : cataR (junc cop arb step) ⊑ val ≫ (inrange)° := by
  show cataR (junc cop arb step) ⊑ cataR (junc copR zero shift) ≫ (inrange)°
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact relCata_le_comp (initial Unit Digit) tex_fusion_condition


/-! ## Theorem 10.1 at `[nil,cons]` (B&dM pp. 261-262) -/

/-- `α≜[nil,cons]` is monotonic on `R`: `cons` adds one digit on either side. -/
public theorem tex_mono : Freyd.Alg.Pres (F := F Unit Digit) alphaR R :=
  le_iff.mpr fun u z h => by
    obtain ⟨v, hFv, hcon⟩ := h
    have hz : z = con v := hcon
    subst hz
    refine ⟨con u, rfl, ?_⟩
    match u, v, hFv with
    | Sum.inl _, Sum.inl _, hd => exact Nat.le_of_eq (by rw [show _ = _ from hd])
    | Sum.inr a, Sum.inr b, hd =>
      obtain ⟨he, hR⟩ := hd
      show length (ConsList.cons a.1 a.2) ≤ length (ConsList.cons b.1 b.2)
      exact Nat.succ_le_succ (hR : length a.2 ≤ length b.2)

/-- `F(X)` leaves the `nil` summand alone: `l F(X)=l` — definition of `F`. -/
public theorem l_Fmap (X : Interval ⟶ Decimal) : l ≫ (F Unit Digit).map X = l := by
  apply hom_ext
  intro t g
  constructor
  · rintro ⟨_, hl, hF⟩
    subst hl
    match g, hF with
    | Sum.inl t', hF => have ht : t = t' := hF; subst ht; rfl
  · intro h
    subst h
    exact ⟨Sum.inl t, rfl, rfl⟩

/-- `l` reaches only `nil`, so `l°l⊑𝟙`. -/
public theorem l_recip_l {Y : RelSet.{0}} : (l : dL Unit ⟶ (F Unit Digit).obj Y)° ≫ l ⊑ 𝟙 _ :=
  le_iff.mpr fun u f h => by
    obtain ⟨t, h1, h2⟩ := h
    have e : u = f := (h1 : u = Sum.inl t).trans (h2 : f = Sum.inl t).symm
    subst e
    rw [id_apply]

/-- On `𝟏`, `!°!⊑𝟙` — the universal property of `!`. -/
public theorem bang_recip_bang : bang° ≫ bang ⊑ 𝟙 (dL Unit) :=
  le_iff.mpr fun t t' _ => by cases t; cases t'; rw [id_apply]

/-- `r F(X) α⊑! l α R`: `l α` is `nil`, and `length(nil)=0` is at most any length. -/
public theorem r_le_nil (X : Interval ⟶ Decimal) :
    r ≫ (F Unit Digit).map X ≫ alphaR ⊑ bang ≫ l ≫ alphaR ≫ R :=
  le_iff.mpr fun _ _ _ => ⟨(), rfl, Sum.inl (), rfl, ConsList.wrap (), rfl, Nat.zero_le _⟩

/-- **B&dM p.262**: the greedy condition for `Q≜(l°!°r) ∪ 𝟙`, the book's hints one `calc` step
    each.  The `𝟙` half is reflexivity of `R`; the other half says that where stopping is legal the
    empty decimal is no longer than whatever the recursion would have produced — `len(nil)=0`. -/
public theorem tex_greedy (X : Interval ⟶ Decimal) :
    Q ≫ (F Unit Digit).map X ≫ alphaR ⊑ (F Unit Digit).map X ≫ alphaR ≫ R :=
  calc Q ≫ (F Unit Digit).map X ≫ alphaR
      = ((l° ≫ bang° ≫ r) ∪ 𝟙 ((F Unit Digit).obj Interval)) ≫ (F Unit Digit).map X ≫ alphaR := by
        rw [Q]
    _ = (l° ≫ bang° ≫ r ≫ (F Unit Digit).map X ≫ alphaR) ∪ ((F Unit Digit).map X ≫ alphaR) := by
        rw [union_comp_distrib, Cat.assoc, Cat.assoc, Cat.id_comp]
    _ ⊑ (l° ≫ bang° ≫ r ≫ (F Unit Digit).map X ≫ alphaR) ∪ ((F Unit Digit).map X ≫ alphaR ≫ R) :=
        union_mono (le_refl _) (by
          simpa only [Cat.comp_id, Cat.assoc] using
            comp_mono_left ((F Unit Digit).map X ≫ alphaR) R_refl)
    _ ⊑ (l° ≫ bang° ≫ bang ≫ l ≫ alphaR ≫ R) ∪ ((F Unit Digit).map X ≫ alphaR ≫ R) :=
        union_mono (comp_mono_left _ (comp_mono_left _ (r_le_nil X))) (le_refl _)
    _ ⊑ (l° ≫ l ≫ alphaR ≫ R) ∪ ((F Unit Digit).map X ≫ alphaR ≫ R) :=
        union_mono (comp_mono_left _ (by
          simpa only [Cat.id_comp, Cat.assoc] using
            comp_mono_right bang_recip_bang (l ≫ alphaR ≫ R))) (le_refl _)
    _ = (l° ≫ l ≫ (F Unit Digit).map X ≫ alphaR ≫ R) ∪ ((F Unit Digit).map X ≫ alphaR ≫ R) := by
        rw [← l_Fmap X, Cat.assoc]
    _ ⊑ ((F Unit Digit).map X ≫ alphaR ≫ R) ∪ ((F Unit Digit).map X ≫ alphaR ≫ R) :=
        union_mono (by
          simpa only [Cat.id_comp, Cat.assoc] using
            comp_mono_right l_recip_l ((F Unit Digit).map X ≫ alphaR ≫ R)) (le_refl _)
    _ = (F Unit Digit).map X ≫ alphaR ≫ R := DistributiveAllegory.union_idem _

calc_steps tex_greedy

/-- `H=⦇[arb,step]⦈°⦇α⦈` collapses to `⦇[arb,step]⦈°` by reflection
    (`AOP.A6_ConsList.cataR_con`). -/
public theorem tex_H : _root_.Freyd.Alg.H (F := F Unit Digit) (junc cop arb step) alphaR = H := by
  show (relCata (F := F Unit Digit) (junc cop arb step))° ≫ relCata (F := F Unit Digit) (graph con) = H
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con]
  exact Cat.comp_id _

/-! ## `tex-laws` (B&dM pp. 260-262) -/

/-- `round°` is not a map, but `interval` is, so it comes out of the transpose —
    `Λ(intern°) = interval Λ(inrange val°)`. -/
public theorem Λ_intern_recip : Λ ((intern)°) = interval ≫ Λ (inrange ≫ (val)°) := by
  have h : (intern)° = interval ≫ (inrange ≫ (val)°) := by
    show (val ≫ round)° = interval ≫ (inrange ≫ (val)°)
    rw [Allegory.recip_comp, round_recip, Cat.assoc]
  rw [h, Λ_fusion interval_map]

/-- A decimal's value `r` lies in `[0,1)`. -/
public theorem val_bounds (y : Dec) (r : Real.carrier) (h : val y r) :
    ¬ rlt r zeroR ∧ rlt r oneR := by
  induction y generalizing r with
  | wrap u =>
    have hr : r = zeroR := (ListRel.junc_sum_inl zero shift u r).mp h
    subst hr
    exact ⟨rlt_irrefl _, by show (0 : Int) * sc 0 < w * sc 0; rw [sc_zero]; simp only [w]; omega⟩
  | cons e y ih =>
    obtain ⟨r', hr', hs⟩ := h
    have hr : r = shiftFn (e.val : Int) r' := (ListRel.junc_sum_inr zero shift (e, r') r).mp hs
    subst hr
    obtain ⟨h0, h1⟩ := ih r' hr'
    exact ⟨fun hlt => zero_le_shift (e.val : Int) (by omega) (le_rlt_trans (fun h => h0 ((shift_lt_shift _ _ _).mp h)) hlt),
      rlt_le_trans ((shift_lt_shift _ _ _).mpr h1) (shift_one_le_one (e.val : Int) (by omega))⟩

/-- If a decimal `y` has its value in `p`, and `H` gives `p` some decimal at all, then `H` gives `p`
    a decimal no longer than `y`: follow `y`'s digits while they agree with `p`'s, and stop at the
    first that differs — there `p`'s remainder already contains `0`. -/
public theorem tex_short (y : Dec) : ∀ (r : Real.carrier) (p : Interval.carrier) (x : Dec),
    val y r → inrange p r → H p x → ∃ z, H p z ∧ length z ≤ length y := by
  induction y with
  | wrap u =>
    intro r p x hv hin _
    have hr : r = zeroR := (ListRel.junc_sum_inl zero shift u r).mp hv
    subst hr
    exact ⟨ConsList.wrap (), (ListRel.junc_sum_inl arb step () p).mpr hin, Nat.le_refl _⟩
  | cons e y ih =>
    intro r p x hv hin hx
    obtain ⟨r', hr', hs⟩ := hv
    have hr : r = shiftFn (e.val : Int) r' := (ListRel.junc_sum_inr zero shift (e, r') r).mp hs
    subst hr
    obtain ⟨v0, v1⟩ := val_bounds y r' hr'
    rcases rlt_em p.1.lo zeroR with ha | ha
    · exact ⟨ConsList.wrap (), (ListRel.junc_sum_inl arb step () p).mpr ⟨ha, p.2.1⟩, Nat.zero_le _⟩
    · cases x with
      | wrap u => exact absurd ((ListRel.junc_sum_inl arb step u p).mp hx).1 ha
      | cons d x' =>
        obtain ⟨p1, hx', hst⟩ := hx
        have hp : p = stepFn (d, p1) := (ListRel.junc_sum_inr arb step (d, p1) p).mp hst
        subst hp
        by_cases hed : e = d
        · subst hed
          obtain ⟨z', hz', hlen⟩ := ih r' p1 x' hr'
            ⟨(shift_lt_shift _ _ _).mp hin.1, (shift_lt_shift _ _ _).mp hin.2⟩ hx'
          exact ⟨ConsList.cons e z', ⟨p1, hz', (ListRel.junc_sum_inr arb step (e, p1) _).mpr rfl⟩,
            Nat.succ_le_succ hlen⟩
        · have hne : (e.val : Int) ≠ (d.val : Int) := fun h => hed (Fin.ext (by omega))
          have hlo : rlt p1.1.lo zeroR := by
            rcases Int.lt_or_gt_of_ne hne with hlt | hgt
            · have h1 : rlt (shiftFn (d.val : Int) p1.1.lo) (shiftFn (e.val : Int) oneR) :=
                rlt_trans hin.1 ((shift_lt_shift _ _ _).mpr v1)
              exact (shift_lt_shift _ _ _).mp
                (rlt_le_trans h1 (shift_le_digit (e.val : Int) (d.val : Int) (by omega)))
            · exfalso
              have h1 : rlt (shiftFn (d.val : Int) p1.1.hi) (shiftFn (d.val : Int) oneR) :=
                (shift_lt_shift _ _ _).mpr p1.2.2.1
              have h2 := rlt_le_trans h1 (shift_le_digit (d.val : Int) (e.val : Int) (by omega))
              have h3 := rlt_le_trans h2 (fun h => v0 ((shift_lt_shift _ _ _).mp h))
              exact rlt_irrefl _ (rlt_trans h3 hin.2)
          exact ⟨ConsList.cons d (ConsList.wrap ()),
            ⟨p1, (ListRel.junc_sum_inl arb step () p1).mpr ⟨hlo, p1.2.1⟩,
              (ListRel.junc_sum_inr arb step (d, p1) _).mpr rfl⟩,
            Nat.succ_le_succ (Nat.zero_le _)⟩

/-- The type restriction (10.9): `Λ(H) est(R)⊑Λ(inrange val°) est(R)` — a shortest decimal among
    those the fold's converse `H` gives an interval is a shortest among all decimals inside it
    (`tex_short`), and it is inside it by fusion. -/
public theorem tex_restrict : Λ H ≫ est R ⊑ Λ (inrange ≫ (val)°) ≫ est R := by
  refine le_iff.mpr fun p x h => ?_
  rw [Λ_comp_est_apply] at h ⊢
  obtain ⟨hx, hmin⟩ := h
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨r, hv, hin⟩ := le_iff.mp tex_fusion x p hx
    exact ⟨r, hin, hv⟩
  · obtain ⟨r, hin, hv⟩ := hy
    obtain ⟨z, hz, hlen⟩ := tex_short y r p x hv hin hx
    exact Nat.le_trans (hmin z hz) hlen

/-- Theorem 10.1's prefixed point at `M≜Λ(H) est(R)`: `Λ([arb,step]°) est(Q) F(M) α ⊑ M`.  The
    SPECIFICATION sits in the recursive slot: with `H` there the tail is unconstrained, and the
    body does not refine `M`. -/
public theorem tex_body_prefixed :
    Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map (Λ H ≫ est R) ≫ alphaR
      ⊑ Λ H ≫ est R := by
  rw [← tex_H]
  exact greedy_dp_prefixed (graph_map con) tex_mono R_trans (tex_greedy _)

/-- **tex-laws** (B&dM p.262): `extern` is the least fixed point of
    `(μX : interval Λ([arb,step]°) est(Q) F(X) α)`, and it refines the specification
    `Λ(intern°) est(R)` — a shortest decimal whose internal representation is the given `n`.
    The fixed point is `f` (`tex_f`), and on points `extern(n)=f(2n−1,2n+1)` (`tex_extern`).
    One `calc` step per hint: Theorem 10.1's prefixed point, the type restriction (10.9),
    `interval` out of the transpose. -/
public theorem tex_laws :
    interval ≫ mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR)
      ⊑ Λ ((intern)°) ≫ est R :=
  calc interval ≫ mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR)
      ⊑ interval ≫ Λ H ≫ est R := comp_mono_left _ (mu_le tex_body_prefixed)
    _ ⊑ interval ≫ Λ (inrange ≫ (val)°) ≫ est R := comp_mono_left _ tex_restrict
    _ = Λ ((intern)°) ≫ est R := by rw [Λ_intern_recip, Cat.assoc]

calc_steps tex_laws

/-! ## `f` on points (B&dM p.263, `tex-extern`) -/

/-- `d=⌊10b⌋`, stated by the inequalities `0<10b−d<1` that make `(10a−d,10b−d)` satisfy (10.9):
    `Real` has no floor function, and Exercise 10.12 (`digit_unique`) is that these pin `d` down. -/
@[expose] public def IsDigit (d : Digit) (b : Real.carrier) : Prop :=
  rlt zeroR (unshift (d.val : Int) b) ∧ rlt (unshift (d.val : Int) b) oneR

/-- **tex-extern**: `f(a,b)=[]` if `a<0`, else `[d]⧺f(10a−d,10b−d)` with `d=⌊10b⌋` — the least
    relation satisfying the book's two clauses.  The base case is `a<0`, not `a≤0`: at `a=0` the
    empty decimal's value `0` is not strictly inside `(a,b)`. -/
public inductive fR : Iv → Dec → Prop
  | nil {a b : Real.carrier} : rlt a zeroR → fR ⟨a, b⟩ (ConsList.wrap ())
  | cons {a b : Real.carrier} {x : Dec} (d : Digit) : ¬ rlt a zeroR → IsDigit d b →
      fR ⟨unshift (d.val : Int) a, unshift (d.val : Int) b⟩ x → fR ⟨a, b⟩ (ConsList.cons d x)

/-- **tex-extern**: `f : Interval⟶Decimal`, the arrow `fR` is on the pairs (10.9) admits. -/
@[expose] public def f : Interval ⟶ Decimal := fun p x => fR p.1 x

/-- **tex-extern** (B&dM p.263): `f(a,b)=[]` if `a<0`, and `[d]⧺f(10a−d,10b−d)` with `d=⌊10b⌋`
    otherwise — the two clauses `fR` is the least relation satisfying. -/
public theorem f_eq (a b : Real.carrier) (xs : Dec) :
    fR ⟨a, b⟩ xs ↔ (rlt a zeroR ∧ xs = ConsList.wrap ()) ∨
      (¬ rlt a zeroR ∧ ∃ d ys, IsDigit d b ∧ fR ⟨unshift (d.val : Int) a, unshift (d.val : Int) b⟩ ys
        ∧ xs = ConsList.cons d ys) := by
  constructor
  · intro h
    cases h with
    | nil ha => exact Or.inl ⟨ha, rfl⟩
    | cons d ha hd hy => exact Or.inr ⟨ha, d, _, hd, hy, rfl⟩
  · rintro (⟨ha, rfl⟩ | ⟨ha, d, ys, hd, hy, rfl⟩)
    · exact fR.nil ha
    · exact fR.cons d ha hd hy

/-- **Exercise 10.12**: `0≤10b−d₁<1` and `0≤10b−d₂<1` imply `d₁=d₂`. -/
public theorem digit_unique {d e : Digit} {b : Real.carrier} (hd : IsDigit d b)
    (he : IsDigit e b) : d = e := by
  revert hd he
  refine Quotient.inductionOn b ?_
  intro m hd he
  have key : ∀ {x y W N : Int}, 0 < W → ¬ N - x * W < 0 → N - y * W < W → x ≤ y := by
    intro x y W N hW h1 h2
    refine Int.not_lt.mp fun hlt => ?_
    have h3 : (y + 1) * W ≤ x * W := Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hW)
    rw [Int.add_mul, Int.one_mul] at h3
    omega
  have hW : 0 < w * sc m.2 := Int.mul_pos (by decide) (sc_pos _)
  have lo : ∀ c : Digit, IsDigit c (mkR m) → ¬ 10 * m.1 - (c.val : Int) * (w * sc m.2) < 0 := by
    intro c hc
    have h : (0 : Int) * sc m.2 < (10 * m.1 - (c.val : Int) * w * sc m.2) * sc 0 := hc.1
    rw [sc_zero, Int.mul_one, Int.zero_mul, Int.mul_assoc] at h
    omega
  have hi : ∀ c : Digit, IsDigit c (mkR m) → 10 * m.1 - (c.val : Int) * (w * sc m.2) < w * sc m.2 := by
    intro c hc
    have h : (10 * m.1 - (c.val : Int) * w * sc m.2) * sc 0 < w * sc m.2 := hc.2
    rwa [sc_zero, Int.mul_one, Int.mul_assoc] at h
  have h1 := key hW (lo d hd) (hi e he)
  have h2 := key hW (lo e he) (hi d hd)
  exact Fin.ext (by omega)

/-- `f` is simple: the two clauses never both apply, and Exercise 10.12 fixes the digit. -/
public theorem f_simple {p : Iv} {x y : Dec} (hx : fR p x) (hy : fR p y) : x = y := by
  induction hx generalizing y with
  | nil ha =>
    cases hy with
    | nil _ => rfl
    | cons _ ha' _ _ => exact absurd ha ha'
  | cons d ha hd _ ih =>
    cases hy with
    | nil ha' => exact absurd ha' ha
    | cons e _ he hy' =>
      have hde := digit_unique hd he
      subst hde
      rw [ih hy']

/-- `Q` on points: `l(t)` is below every `r(s)`, and everything is below itself. -/
public theorem Q_apply (u z : ((F Unit Digit).obj Interval).carrier) :
    Q u z ↔ (∃ t, u = Sum.inl t ∧ ∃ s, z = Sum.inr s) ∨ u = z := by
  rw [Q, union_apply, id_apply]
  constructor
  · rintro (⟨t, hl, s, _, hr⟩ | h)
    · exact Or.inl ⟨t, hl, s, hr⟩
    · exact Or.inr h
  · rintro (⟨t, hl, s, hr⟩ | h)
    · exact Or.inl ⟨t, hl, s, rfl, hr⟩
    · exact Or.inr h

/-- The greedy body on points: `est(Q)` picks a one-step decomposition `u` of `p` that is
    `Q`-below every other, and `F(X)α` builds the decimal from it. -/
public theorem body_apply (X : Interval ⟶ Decimal) (p : Interval.carrier) (x : Dec) :
    (Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR) p x ↔
      ∃ u, (junc cop arb step u p ∧ ∀ z, junc cop arb step z p → Q u z)
        ∧ ∃ v, Fmap Unit Digit X u v ∧ x = con v := by
  rw [← Cat.assoc]
  show (∃ u, (Λ ((junc cop arb step)°) ≫ est Q) p u ∧ ∃ v, Fmap Unit Digit X u v ∧ x = con v) ↔ _
  simp only [Λ_comp_est_apply]
  exact Iff.rfl

/-- **tex-extern** (B&dM p.263): the least solution of the greedy recursion is `f` — at `(a,b)`
    with `a<0` stopping is legal and `Q` prefers it, and otherwise `[arb,step]°` offers the one
    decomposition `(⌊10b⌋,(10a−d,10b−d))` that (10.9) admits. -/
public theorem tex_f :
    mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR) = f := by
  have hmono : Monotonic (fun X : Interval ⟶ Decimal =>
      Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR) := by
    intro X Y h
    exact comp_mono_left _ (comp_mono_left _ (comp_mono_right ((F Unit Digit).map_mono h) _))
  have hle : (Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map f ≫ alphaR) ⊑ f :=
    le_iff.mpr fun p x h => by
      rw [body_apply] at h
      obtain ⟨u, ⟨hT, hmin⟩, v, hF, rfl⟩ := h
      cases u with
      | inl t =>
        have ha := ((ListRel.junc_sum_inl arb step t p).mp hT).1
        cases v with
        | inl t' => cases t'; exact fR.nil (b := p.1.hi) ha
        | inr _ => exact (hF : False).elim
      | inr s =>
        obtain ⟨d, q⟩ := s
        have hp : p = stepFn (d, q) := (ListRel.junc_sum_inr arb step (d, q) p).mp hT
        have ha : ¬ rlt p.1.lo zeroR := fun ha => by
          have h := hmin (Sum.inl ()) ((ListRel.junc_sum_inl arb step () p).mpr ⟨ha, p.2.1⟩)
          rw [Q_apply] at h
          rcases h with ⟨t, h1, _⟩ | h1 <;> cases h1
        cases v with
        | inl _ => exact (hF : False).elim
        | inr w' =>
          obtain ⟨d', y⟩ := w'
          obtain ⟨hd, hy⟩ := (hF : d = d' ∧ f q y)
          have hd' : d = d' := hd
          subst hd' hp
          have e1 := unshift_shift (d.val : Int) q.1.lo
          have e2 := unshift_shift (d.val : Int) q.1.hi
          refine fR.cons (a := shiftFn (d.val : Int) q.1.lo) (b := shiftFn (d.val : Int) q.1.hi) d ha
            ⟨by rw [e2]; exact q.2.1, by rw [e2]; exact q.2.2.1⟩ ?_
          rw [e1, e2]; exact hy
  have key : ∀ (pp : Iv) (x : Dec), fR pp x → ∀ h : Legal pp,
      mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR) ⟨pp, h⟩ x := by
    intro pp x hf
    induction hf with
    | nil ha =>
      intro h
      apply le_iff.mp (mu_prefixed hmono)
      rw [body_apply]
      refine ⟨Sum.inl (), ⟨(ListRel.junc_sum_inl arb step () _).mpr ⟨ha, h.1⟩, fun z _ => ?_⟩,
        Sum.inl (), (rfl : () = ()), rfl⟩
      rw [Q_apply]
      rcases z with z | s
      · cases z; exact Or.inr rfl
      · exact Or.inl ⟨(), rfl, s, rfl⟩
    | @cons a b x d ha hd _ ih =>
      intro h
      have hq : Legal ⟨unshift (d.val : Int) a, unshift (d.val : Int) b⟩ :=
        ⟨hd.1, hd.2, unshift_lt _ h.2.2⟩
      have hp : (⟨⟨a, b⟩, h⟩ : Interval.carrier) = stepFn (d, ⟨_, hq⟩) := by
        apply Subtype.ext
        show (⟨a, b⟩ : Iv) = ⟨shiftFn _ (unshift _ a), shiftFn _ (unshift _ b)⟩
        rw [shift_unshift, shift_unshift]
      apply le_iff.mp (mu_prefixed hmono)
      rw [body_apply]
      refine ⟨Sum.inr (d, ⟨_, hq⟩), ⟨?_, fun z hz => ?_⟩, Sum.inr (d, x), ⟨rfl, ih hq⟩, rfl⟩
      · rw [hp]; exact (ListRel.junc_sum_inr arb step (d, ⟨_, hq⟩) _).mpr rfl
      · rw [Q_apply]; right
        rcases z with t | ⟨e, q2⟩
        · exact absurd ((ListRel.junc_sum_inl arb step t _).mp hz).1 ha
        · have h2 : (⟨⟨a, b⟩, h⟩ : Interval.carrier) = stepFn (e, q2) :=
            (ListRel.junc_sum_inr arb step (e, q2) _).mp hz
          have ha' : a = shiftFn (e.val : Int) q2.1.lo :=
            congrArg (fun p : Interval.carrier => p.1.lo) h2
          have hb : b = shiftFn (e.val : Int) q2.1.hi :=
            congrArg (fun p : Interval.carrier => p.1.hi) h2
          have he : IsDigit e b := by
            rw [hb]
            exact ⟨by rw [unshift_shift]; exact q2.2.1, by rw [unshift_shift]; exact q2.2.2.1⟩
          have hde := digit_unique hd he
          subst hde
          have hq2 : q2 = ⟨_, hq⟩ := by
            apply Subtype.ext
            show q2.1 = ⟨unshift _ a, unshift _ b⟩
            rw [ha', hb, unshift_shift, unshift_shift]
          rw [hq2]
  apply hom_ext
  intro p x
  exact ⟨fun h => le_iff.mp (mu_le hle) p x h, fun h => key p.1 x h p.2⟩

/-! ## The program in integer arithmetic (B&dM p.263) -/

namespace Prog

/-- The pairs `(p,q)` the program reaches, representing `(p/w,q/w)`: `q−p>0` and `q<w` are what
    make the recursion stop, since the width `q−p` grows tenfold at each digit and `q−p<q<w`
    while `p≥0`. -/
@[expose] public def Rep : Type := {x : Int × Int // 0 < x.2 - x.1 ∧ x.2 < w}

/-- `d`, as a digit. -/
@[expose] public def dig (d : Int) (h : 0 ≤ d ∧ d < 10) : Digit := ⟨d.toNat, by omega⟩

public theorem dig_val (d : Int) (h : 0 ≤ d ∧ d < 10) : ((dig d h).val : Int) = d := by
  show ((d.toNat : Nat) : Int) = d
  omega

-- `omega` over `/` pulls in `Classical.choice`, so the division is replaced by its two bounds
-- once, here, and every later arithmetic step sees `d` as a plain variable.
/-- `0≤10q−w·d<w` for `d=(10q) div w`: the division's defining bounds. -/
public theorem div_bounds (q : Int) :
    0 ≤ 10 * q - w * (10 * q / w) ∧ 10 * q - w * (10 * q / w) < w := by
  have e := Int.emod_add_mul_ediv (10 * q) w
  have h1 := Int.emod_nonneg (10 * q) (show w ≠ 0 by decide)
  have h2 := Int.emod_lt_of_pos (10 * q) (show 0 < w by decide)
  generalize 10 * q / w = d at *
  generalize 10 * q % w = r at *
  generalize w * d = m at *
  exact ⟨by omega, by omega⟩

/-- The width `q−p` grows tenfold at a digit, and stays below `w` while `p≥0`. -/
public theorem measure_lt (p q e : Int) (hp : ¬ p < 0) (h : 0 < q - p ∧ q < w) :
    (w - ((10 * q - e) - (10 * p - e))).toNat < (w - (q - p)).toNat := by
  omega

public theorem dig_ok (p q d : Int) (hp : ¬ p < 0) (h : 0 < q - p ∧ q < w) (hd : d = 10 * q / w) :
    0 ≤ d ∧ d < 10 := by
  subst hd; have hb := div_bounds q; generalize 10 * q / w = d at *; simp only [w] at *; exact ⟨by omega, by omega⟩

public theorem next_ok (p q d : Int) (h : 0 < q - p ∧ q < w) (hd : d = 10 * q / w) :
    0 < (10 * q - w * d) - (10 * p - w * d) ∧ 10 * q - w * d < w := by
  subst hd; have hb := Prog.div_bounds q; generalize 10 * q / w = d at *; exact ⟨by omega, by omega⟩

/-- **tex-extern**: the program's `f(p,q)=[]` if `p<0`, else `[d]⧺f(10p−w·d,10q−w·d)` with
    `d=(10q) div w`.  The book's Gofer has `p<=0`; `p<0` is kept because it is the rational line's
    `a<0` under `a=p/w`, and at `p=0` the empty decimal's value `0` is not strictly above `a`. -/
@[expose] public def f (x : Rep) : Dec :=
  if hp : x.1.1 < 0 then ConsList.wrap ()
  else ConsList.cons (dig (10 * x.1.2 / w) (dig_ok x.1.1 x.1.2 _ hp x.2 rfl))
    (f ⟨(10 * x.1.1 - w * (10 * x.1.2 / w), 10 * x.1.2 - w * (10 * x.1.2 / w)),
      next_ok x.1.1 x.1.2 _ x.2 rfl⟩)
termination_by (w - (x.1.2 - x.1.1)).toNat
decreasing_by exact measure_lt _ _ _ hp x.2

/-- The pairs the program reaches from `interval n=(2n−1,2n+1)`: after `k` digits the width is
    `q−p=2·10ᵏ` and `2ᵏ` exactly divides `q`, until the width passes `w`.  This is what keeps
    `10q/w` off the integers (Exercise 10.14), so the digit leaves `10b−d>0`. -/
@[expose] public def Reach (p q : Int) : Prop :=
  ∃ m : Int, (q - p = 2 ∧ q = 2 * m + 1) ∨ (q - p = 20 ∧ q = 2 * (2 * m + 1))
    ∨ (q - p = 200 ∧ q = 4 * (2 * m + 1)) ∨ (q - p = 2000 ∧ q = 8 * (2 * m + 1))
    ∨ (q - p = 20000 ∧ q = 16 * (2 * m + 1)) ∨ w ≤ q - p

/-- On a reached pair with `p≥0`, `0<10q−w·d` for `d=(10q) div w`. -/
public theorem digit_strict (p q : Int) (hp : ¬ p < 0) (h : 0 < q - p ∧ q < w)
    (hr : Reach p q) : 0 < 10 * q - w * (10 * q / w) := by
  have hb := div_bounds q
  generalize 10 * q / w = d at *
  obtain ⟨m, hm⟩ := hr
  simp only [w] at *
  omega

/-- The next pair `(10p−w·d,10q−w·d)` is reached too. -/
public theorem reach_next (p q : Int) (hp : ¬ p < 0) (h : 0 < q - p ∧ q < w) (hr : Reach p q) :
    Reach (10 * p - w * (10 * q / w)) (10 * q - w * (10 * q / w)) := by
  generalize 10 * q / w = d
  obtain ⟨m, h1 | h2 | h3 | h4 | h5 | h6⟩ := hr
  · exact ⟨5 * m + 2 - 32768 * d, Or.inr (Or.inl ⟨by simp only [w]; omega, by simp only [w]; omega⟩)⟩
  · exact ⟨5 * m + 2 - 16384 * d,
      Or.inr (Or.inr (Or.inl ⟨by simp only [w]; omega, by simp only [w]; omega⟩))⟩
  · exact ⟨5 * m + 2 - 8192 * d,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only [w]; omega, by simp only [w]; omega⟩)))⟩
  · exact ⟨5 * m + 2 - 4096 * d,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only [w]; omega, by simp only [w]; omega⟩))))⟩
  · exact ⟨0, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp only [w]; omega)))))⟩
  · exfalso; simp only [w] at *; omega

/-- **tex-extern**: the program's first clause, `f(p,q)=[]` if `p<0`. -/
public theorem f_nil (p q : Int) (h : 0 < q - p ∧ q < w) (hp : p < 0) :
    f ⟨(p, q), h⟩ = ConsList.wrap () := by
  rw [f]; exact dif_pos hp

/-- **tex-extern**: the program's second clause, `f(p,q)=[d]⧺f(10p−w·d,10q−w·d)` where
    `d=(10q) div w`. -/
public theorem f_cons (p q : Int) (h : 0 < q - p ∧ q < w) (hp : ¬ p < 0) :
    f ⟨(p, q), h⟩ = ConsList.cons (dig (10 * q / w) (dig_ok p q _ hp h rfl))
      (f ⟨(10 * p - w * (10 * q / w), 10 * q - w * (10 * q / w)), next_ok p q _ h rfl⟩) := by
  rw [f]; exact dif_neg hp

/-- **tex-extern**: `interval n=(2n−1,2n+1)`, the representation of `interval`'s pair. -/
@[expose] public def interval (n : Fin 65536) : Rep :=
  ⟨(2 * (n.val : Int) - 1, 2 * (n.val : Int) + 1), by simp only [w]; exact ⟨by omega, by omega⟩⟩

/-- **tex-extern**: `extern=f·interval`, the Gofer program. -/
@[expose] public def extern (n : Fin 65536) : Dec := f (interval n)

end Prog

/-- `p/w` is `(p,0)`, and `10a−d` on it is `(10p−w·d)/w` — the representation step of p.263. -/
public theorem unshift_mkR (d p : Int) : unshift d (mkR (p, 0)) = mkR (10 * p - w * d, 0) := by
  refine Quotient.sound ?_
  show (10 * p - d * w * sc 0) * sc 0 = (10 * p - w * d) * sc 0
  rw [Int.mul_comm d w, sc_zero]; simp only [Int.mul_one]

/-- **tex-extern**: on the pairs it reaches, the integer `f` computes the rational one under
    `(p,q)↦(p/w,q/w)`. -/
public theorem f_agree (p q : Int) (h : 0 < q - p ∧ q < w) (hr : Prog.Reach p q) :
    fR ⟨mkR (p, 0), mkR (q, 0)⟩ (Prog.f ⟨(p, q), h⟩) := by
  by_cases hp : p < 0
  · rw [Prog.f_nil p q h hp]
    refine fR.nil ?_
    show p * sc 0 < 0 * sc 0
    rw [sc_zero]; omega
  · rw [Prog.f_cons p q h hp]
    have hv := Prog.dig_val (10 * q / w) (Prog.dig_ok p q _ hp h rfl)
    have ih := f_agree (10 * p - w * (10 * q / w)) (10 * q - w * (10 * q / w))
      (Prog.next_ok p q _ h rfl) (Prog.reach_next p q hp h hr)
    refine fR.cons _ ?_ ⟨?_, ?_⟩ ?_
    · show ¬ p * sc 0 < 0 * sc 0
      rw [sc_zero]; omega
    · rw [hv, unshift_mkR]
      show (0 : Int) * sc 0 < (10 * q - w * (10 * q / w)) * sc 0
      simp only [sc_zero, Int.mul_one]; exact Prog.digit_strict p q hp h hr
    · rw [hv, unshift_mkR]
      show (10 * q - w * (10 * q / w)) * sc 0 < w * sc 0
      rw [sc_zero, Int.mul_one, Int.mul_one]; exact (Prog.div_bounds q).2
    · rw [hv, unshift_mkR, unshift_mkR]
      exact ih
termination_by (w - (q - p)).toNat
decreasing_by exact Prog.measure_lt _ _ _ hp h

/-- **tex-extern**: `extern≜f·interval` in integer arithmetic, as an arrow `[0,2¹⁶)⟶Decimal`. -/
@[expose] public def extern : Ix ⟶ Decimal := graph Prog.extern

/-- **tex-extern** (B&dM p.263): `extern=interval f` — the rational `f` after `interval` is the
    integer program, `extern(n)=f(2n−1,2n+1)`. -/
public theorem tex_extern : interval ≫ f = extern := by
  apply hom_ext
  intro n x
  have hn : f (intervalFn n) (Prog.extern n) :=
    f_agree (2 * (n.val : Int) - 1) (2 * (n.val : Int) + 1) (Prog.interval n).2
      ⟨n.val, Or.inl ⟨by omega, rfl⟩⟩
  constructor
  · rintro ⟨p, hp, hf⟩
    have hp' : p = intervalFn n := hp
    subst hp'
    exact f_simple hf hn
  · intro hx
    have hx' : x = Prog.extern n := hx
    subst hx'
    exact ⟨intervalFn n, rfl, hn⟩

-- printing-only unexpanders: §10.4's names as the book writes them.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.Legal] public meta def unexpandLegal : Unexpander
  | `($_ $args*) => `($(mkIdent `Legal) $args*)
  | _ => `($(mkIdent `Legal))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.round] public meta def unexpandRound : Unexpander
  | `($_ $args*) => `($(mkIdent `round) $args*)
  | _ => `($(mkIdent `round))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.shiftFn] public meta def unexpandShiftFn : Unexpander
  | `($_ $d $r) => `($(mkIdent `shift) ($d, $r))
  | _ => `($(mkIdent `shift))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.Iv.lo] public meta def unexpandIvLo : Unexpander
  | `($_ $args*) => `($(mkIdent `lo) $args*)
  | _ => `($(mkIdent `lo))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.Iv.hi] public meta def unexpandIvHi : Unexpander
  | `($_ $args*) => `($(mkIdent `hi) $args*)
  | _ => `($(mkIdent `hi))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tex.stepFn] public meta def unexpandStepFn : Unexpander
  | `($_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))

end Freyd.Alg.RelSet.Tex
