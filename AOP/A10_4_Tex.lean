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

  THE TYPE RESTRICTION (10.9).  B&dM's fusion (p.260) is over ALL pairs `(a,b)`, and the
  restriction to `0<b<1, a<b` is the SEPARATE p.261 observation that `[arb,step]` maps `Interval`
  into itself (`arb_legal`, `step_legal` below).  It is not part of the fusion — `⦇[arb,step]⦈`
  cut down to (10.9) is strictly smaller than `inrange° val` — so `Interval` is the pairs, and
  (10.9) is a property of them.
-/
module

public import AOP.A10_1
public import AOP.A6_ConsList

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
@[expose] public def shift (d : Int) (r : Real.carrier) : Real.carrier :=
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

/-- `10a−d`, the inverse of `shift d` — the step the program takes when it emits `d`. -/
@[expose] public def unshift (d : Int) (r : Real.carrier) : Real.carrier :=
  Quotient.liftOn r (fun x => mkR (unshiftPre d x))
    fun _ _ h => Quotient.sound (unshiftPre_congr d h)

public theorem shift_unshift (d : Int) (r : Real.carrier) : shift d (unshift d r) = r := by
  refine Quotient.inductionOn r ?_
  intro x
  refine Quotient.sound ?_
  show (d * w * sc x.2 + (10 * x.1 - d * w * sc x.2)) * sc x.2 = x.1 * sc (x.2 + 1)
  have e : d * w * sc x.2 + (10 * x.1 - d * w * sc x.2) = 10 * x.1 := by omega
  rw [e, sc_succ]
  simp [Int.mul_assoc, Int.mul_comm]

/-- `shift d` is strictly monotone, and that is the whole content of the fusion's step case. -/
public theorem shift_lt_shift (d : Int) (x y : Real.carrier) :
    rlt (shift d x) (shift d y) ↔ rlt x y := by
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
    rlt a (shift d r) ↔ rlt (unshift d a) r := by
  rw [← shift_lt_shift d (unshift d a) r, shift_unshift]

public theorem shift_lt_iff (d : Int) (r b : Real.carrier) :
    rlt (shift d r) b ↔ rlt r (unshift d b) := by
  rw [← shift_lt_shift d r (unshift d b), shift_unshift]

/-! ## The objects and arrows of §10.4 (`tex-defn`) -/

/-- **tex-defn**: a digit. -/
@[expose] public abbrev Digit : Type := Fin 10

/-- **tex-defn**: the carrier of `Decimal` — a cons-list of digits.  It carries a name of its own
    because the note draws ONE wire from `[0,2¹⁶)` to `Decimal` and never opens the list. -/
@[expose] public def Dec : Type := ConsList Unit Digit

/-- **tex-defn**: the object `Decimal`. -/
@[expose] public def Decimal : RelSet.{0} := ⟨Dec⟩

/-- **tex-defn**: the object `[0,2¹⁶)`. -/
@[expose] public def Ix : RelSet.{0} := ⟨Fin 65536⟩

/-- **tex-defn**: a pair `(a,b)`.  A structure and not `Real×Real` for the reason `Dec` is a name:
    the note draws `Interval` as ONE wire, and a product carrier is what a circuit opens into two. -/
public structure Iv where
  lo : Real.carrier
  hi : Real.carrier

/-- **tex-defn**: the object `Interval` — the pairs `(a,b)`. -/
@[expose] public def Interval : RelSet.{0} := ⟨Iv⟩

/-- **tex-defn**: `interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`. -/
@[expose] public def intervalFn (n : Fin 65536) : Interval.carrier :=
  ⟨mkR (2 * (n.val : Int) - 1, 0), mkR (2 * (n.val : Int) + 1, 0)⟩

/-- **tex-defn**: `interval`, a map. -/
@[expose] public def interval : Ix ⟶ Interval := graph intervalFn

public theorem interval_map : Map interval := graph_map intervalFn

/-- **tex-defn**: `r inrange (a,b)⟺a<r<b`. -/
@[expose] public def inrange : Interval ⟶ Real := fun p r => rlt p.lo r ∧ rlt r p.hi

/-- **tex-defn**: `round r=n⟺2n−1<2¹⁷r<2n+1`, read as `(2n−1)/2¹⁷<r<(2n+1)/2¹⁷`. -/
@[expose] public def round : Real ⟶ Ix := fun r n =>
  rlt (mkR (2 * (n.val : Int) - 1, 0)) r ∧ rlt r (mkR (2 * (n.val : Int) + 1, 0))

/-- **tex-defn**: `round°=interval inrange` — `round` is not a map, but `interval` is, and that
    is what lets the next step take `interval` out of the transpose. -/
public theorem round_recip : (round)° = interval ≫ inrange := by
  apply hom_ext
  intro n r
  exact ⟨fun h => ⟨intervalFn n, rfl, h⟩, fun h => by obtain ⟨p, hp, hq⟩ := h; subst hp; exact hq⟩

/-- **tex-defn**: `[zero,shift]`, the algebra of `val`. -/
@[expose] public def valAlgFn : (Fobj Unit Digit Real).carrier → Real.carrier
  | Sum.inl _ => zeroR
  | Sum.inr p => shift (p.1.val : Int) p.2

/-- **tex-defn**: `val≜⦇[zero,shift]⦈`. -/
@[expose] public def val : Decimal ⟶ Real := cataR (graph valAlgFn)

/-- **tex-defn**: `intern≜val round`. -/
@[expose] public def intern : Decimal ⟶ Ix := val ≫ round

/-- **tex-defn**: `step(d,(a,b))=((d+a)/10,(d+b)/10)`. -/
@[expose] public def stepFn (p : Digit × Interval.carrier) : Interval.carrier :=
  ⟨shift (p.1.val : Int) p.2.lo, shift (p.1.val : Int) p.2.hi⟩

/-- **tex-defn**: `arb : 𝟏⟶Interval` — B&dM p.260's first fusion condition `arb=zero inrange°`, so
    `(a,b)` is an `arb` iff `a<0<b`. -/
@[expose] public def arb : dL Unit ⟶ Interval := fun _ p => rlt p.lo zeroR ∧ rlt zeroR p.hi

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
@[expose] public def len : ConsList Unit Digit → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons _ x => len x + 1

/-- **tex-defn**: `R≜length≤length°` — a shortest decimal is wanted. -/
@[expose] public def R : Decimal ⟶ Decimal := fun x y => len x ≤ len y

public theorem R_refl : 𝟙 Decimal ⊑ R :=
  le_iff.mpr fun x y h => by
    rw [id_apply] at h
    subst h; exact Nat.le_refl _

public theorem R_trans : R ≫ R ⊑ R :=
  le_iff.mpr fun x z h => by
    obtain ⟨y, h1, h2⟩ := h
    exact Nat.le_trans (h1 : len x ≤ len y) h2

/-- **tex-defn**: `l : 𝟏⟶F(Interval)`, the left injection of `FX=1+(Digit×X)`. -/
@[expose] public def l : dL Unit ⟶ (F Unit Digit).obj Interval := graph Sum.inl

/-- **tex-defn**: `r : Digit×Interval⟶F(Interval)`, the right injection. -/
@[expose] public def r : (⟨Digit × Interval.carrier⟩ : RelSet.{0}) ⟶ (F Unit Digit).obj Interval :=
  graph Sum.inr

/-- **tex-defn**: `! : Digit×Interval⟶𝟏`. -/
@[expose] public def bang : (⟨Digit × Interval.carrier⟩ : RelSet.{0}) ⟶ dL Unit :=
  graph fun _ => ()

/-- **tex-defn**: `Q≜(l°!°r) ∪ 𝟙` — with this `Q` the inhabitant of the terminal object is
    preferred whenever it is there, which is "stop as soon as stopping is legal". -/
@[expose] public def Q : (F Unit Digit).obj Interval ⟶ (F Unit Digit).obj Interval :=
  (l° ≫ bang° ≫ r) ∪ 𝟙 ((F Unit Digit).obj Interval)

/-! ## (10.9): `[arb,step]` maps `Interval` into itself (B&dM p.261) -/

/-- **(10.9)**: the pairs `(a,b)` with `0<b<1` and `a<b`. -/
@[expose] public def Legal (p : Interval.carrier) : Prop :=
  rlt zeroR p.hi ∧ rlt p.hi oneR ∧ rlt p.lo p.hi

/-- **(10.9)** for `arb`: `arb` can always be restricted so that it returns a legal interval —
    `a<0<b` already gives `a<b`, so only `b<1` has to be asked for. -/
public theorem arb_legal (p : Interval.carrier) (hb : rlt p.hi oneR)
    (harb : rlt p.lo zeroR ∧ rlt zeroR p.hi) : Legal p :=
  ⟨harb.2, hb, rlt_trans harb.1 harb.2⟩

/-- **(10.9)** for `step` (B&dM p.261): if `(a',b')` satisfies (10.9) then so does
    `step(d,(a',b'))`, which is what types `[arb,step] : Interval⟵1+(Digit×Interval)`. -/
public theorem step_legal (d : Digit) (q : Interval.carrier) (h : Legal q) :
    Legal (stepFn (d, q)) := by
  obtain ⟨h0, h1, hab⟩ := h
  refine ⟨?_, ?_, (shift_lt_shift _ _ _).mpr hab⟩
  · show rlt zeroR (shift (d.val : Int) q.2)
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
  · show rlt (shift (d.val : Int) q.2) oneR
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

/-! ## Fusion (B&dM p.260): `inrange° val` is a fold on cons-lists -/

/-- **tex-laws**, second step: `val inrange°=⦇[arb,step]⦈` — the converse of `val`, cut down to
    intervals, is a fold, because `shift d` is an order-isomorphism whose inverse is `10a−d`.
    B&dM's two fusion conditions are `arb=zero inrange°` and
    `shift inrange°=(𝟙×inrange°)step`, both true by construction of `[arb,step]`. -/
public theorem tex_fusion : val ≫ (inrange)° = cataR (junc cop arb step) := by
  apply hom_ext
  intro x
  induction x with
  | wrap u =>
    intro p
    constructor
    · rintro ⟨rr, hv, hin⟩
      have hr : rr = zeroR := hv
      subst hr
      exact Or.inl ⟨u, rfl, hin⟩
    · rintro (⟨t, ht, ha⟩ | ⟨q, hq, _⟩)
      · obtain rfl := Sum.inl.inj ht
        exact ⟨zeroR, rfl, ha⟩
      · have h : Sum.inl u = Sum.inr q := hq
        exact nomatch h
  | cons d y ih =>
    intro p
    constructor
    · rintro ⟨rr, hv, hin⟩
      obtain ⟨r', hy, hstep⟩ := hv
      have hrr : rr = shift (d.val : Int) r' := hstep
      subst hrr
      refine ⟨⟨unshift (d.val : Int) p.lo, unshift (d.val : Int) p.hi⟩, ?_, ?_⟩
      · refine (ih _).mp ⟨r', hy, ?_, ?_⟩
        · exact (lt_shift_iff _ _ _).mp hin.1
        · exact (shift_lt_iff _ _ _).mp hin.2
      · refine Or.inr ⟨(d, ⟨unshift (d.val : Int) p.lo, unshift (d.val : Int) p.hi⟩), rfl, ?_⟩
        show p = stepFn (d, ⟨unshift (d.val : Int) p.lo, unshift (d.val : Int) p.hi⟩)
        show p = (⟨shift (d.val : Int) (unshift (d.val : Int) p.lo),
          shift (d.val : Int) (unshift (d.val : Int) p.hi)⟩ : Interval.carrier)
        rw [shift_unshift, shift_unshift]
        rfl
    · rintro ⟨q, hq, (⟨t, ht, _⟩ | ⟨q', hq', hp⟩)⟩
      · have h : Sum.inr (d, q) = Sum.inl t := ht
        exact nomatch h
      · obtain rfl := Sum.inr.inj hq'
        obtain ⟨r', hy, hin⟩ := (ih q).mpr hq
        have hp' : p = stepFn (d, q) := hp
        subst hp'
        refine ⟨shift (d.val : Int) r', ⟨r', hy, rfl⟩, ?_, ?_⟩
        · exact (shift_lt_shift _ _ _).mpr hin.1
        · exact (shift_lt_shift _ _ _).mpr hin.2

/-! ## Theorem 10.1 at `[nil,cons]` (B&dM pp. 261-262) -/

/-- `α≜[nil,cons]` is monotonic on `R`: `cons` adds one digit on either side. -/
public theorem tex_mono : MonotonicAlg (F := F Unit Digit) alphaR R :=
  le_iff.mpr fun u z h => by
    obtain ⟨v, hFv, hcon⟩ := h
    have hz : z = con v := hcon
    subst hz
    refine ⟨con u, rfl, ?_⟩
    match u, v, hFv with
    | Sum.inl _, Sum.inl _, hd => exact Nat.le_of_eq (by rw [show _ = _ from hd])
    | Sum.inr a, Sum.inr b, hd =>
      obtain ⟨he, hR⟩ := hd
      show len (ConsList.cons a.1 a.2) ≤ len (ConsList.cons b.1 b.2)
      exact Nat.succ_le_succ (hR : len a.2 ≤ len b.2)

/-- **B&dM p.262**: the greedy condition for `Q≜(l°!°r) ∪ 𝟙`.  The `𝟙` half is reflexivity of
    `R`; the other half says that where stopping is legal the empty decimal is no longer than
    whatever the recursion would have produced — `len(nil)=0`. -/
public theorem tex_greedy (X : Interval ⟶ Decimal) :
    Q ≫ (F Unit Digit).map X ≫ alphaR ⊑ (F Unit Digit).map X ≫ alphaR ≫ R :=
  le_iff.mpr fun u z h => by
    obtain ⟨v, hQ, hrest⟩ := h
    obtain ⟨v', hFv, hcon⟩ := hrest
    have hz : z = con v' := hcon
    subst hz
    rcases hQ with hQ | hQ
    · -- `l° ≫ bang° ≫ r`: the source is the terminal inhabitant, so `nil` is available
      obtain ⟨t, hl, hrest2⟩ := hQ
      obtain ⟨s, _, _⟩ := hrest2
      have hu : u = Sum.inl t := hl
      subst hu
      refine ⟨Sum.inl t, rfl, con (Sum.inl t), rfl, ?_⟩
      show len (ConsList.wrap t) ≤ len (con v')
      exact Nat.zero_le _
    · -- `𝟙`: `R` is reflexive
      rw [id_apply] at hQ
      subst hQ
      exact ⟨v', hFv, con v', rfl, Nat.le_refl _⟩

/-- `H=⦇[arb,step]⦈°⦇α⦈` collapses to `⦇[arb,step]⦈°` by reflection
    (`AOP.A6_ConsList.cataR_con`). -/
public theorem tex_H : _root_.Freyd.Alg.H (F := F Unit Digit) (junc cop arb step) alphaR = H := by
  show (relCata (F := F Unit Digit) (junc cop arb step))° ≫ relCata (F := F Unit Digit) (graph con) = H
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con]
  exact Cat.comp_id _

/-! ## `tex-laws` (B&dM pp. 260-262) -/

/-- **tex-laws**, first step: `round°` is not a map, but `interval` is, so it comes out of the
    transpose — `Λ(intern°) est(R) = interval Λ(inrange val°) est(R)`. -/
public theorem tex_laws_step1 :
    Λ ((intern)°) ≫ est R = interval ≫ Λ (inrange ≫ (val)°) ≫ est R := by
  have h : (intern)° = interval ≫ (inrange ≫ (val)°) := by
    show (val ≫ round)° = interval ≫ (inrange ≫ (val)°)
    rw [Allegory.recip_comp, round_recip, Cat.assoc]
  rw [h, Λ_fusion interval_map, Cat.assoc]

/-- **tex-laws**, second step: fusion replaces `inrange val°` by the fold's converse `H`. -/
public theorem tex_laws_step2 :
    interval ≫ Λ (inrange ≫ (val)°) ≫ est R = interval ≫ Λ H ≫ est R := by
  have h : inrange ≫ (val)° = H := by
    show inrange ≫ (val)° = (cataR (junc cop arb step))°
    rw [← tex_fusion, Allegory.recip_comp, Allegory.recip_recip]
  rw [h]

/-- **tex-laws**, third step (Theorem 10.1): the greedy body is a prefixed point of the
    specification, so the least fixed point refines it. -/
public theorem tex_laws_step3 :
    interval ≫ mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR)
      ⊑ interval ≫ Λ H ≫ est R := by
  have key := greedy_dp (F := F Unit Digit) (F_preservesRecip Unit Digit) (initial Unit Digit)
    (h := alphaR) (T := (junc cop arb step)) (R := R) (Q := Q) (graph_map con) tex_mono R_trans
    (by rw [tex_H]; exact tex_greedy _)
  rw [tex_H] at key
  exact comp_mono_left _ key

/-- **tex-laws** (B&dM p.262): `extern` is the least fixed point of
    `(μX : interval Λ([arb,step]°) est(Q) F(X) α)`, and it refines the specification
    `Λ(intern°) est(R)` — a shortest decimal whose internal representation is the given `n`.
    Reading it off on points (`extern(n)=f(2n−1,2n+1)`, B&dM p.263) is not formalised here. -/
public theorem tex_laws :
    interval ≫ mu (fun X : Interval ⟶ Decimal =>
        Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR)
      ⊑ Λ ((intern)°) ≫ est R := by
  rw [tex_laws_step1, tex_laws_step2]
  exact tex_laws_step3

end Freyd.Alg.RelSet.Tex
