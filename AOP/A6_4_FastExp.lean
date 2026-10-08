/-
  Bird & de Moor, *Algebra of Programming* §6.4  Fast exponentiation and modulus computation
  (book pp. 144-146), in the Set model `Rel(Set)`.

  The SPECIFICATIONS are graphs: `exp(a) = a^(−)` and `mod(b) = (−) mod b`.  The programs are
  DERIVED from them by the book's three-step argument, stated once for any map `f : Nat ⟶ Nat`
  and algebra `[g,h]` with the fusion conditions `zero f = g`, `shift f = (f×𝟙)h`:

    `f ⊒ convert°convert f = convert°⦇[g,h]⦈ = (μX : zero°g ∪ shift°(X×𝟙)h)`

  — `convert` simple; fusion; Corollary 6.1 over `F(X) = 𝟏+(X×Bit)`.  `exp` is it at
  `[g,h] ≜ [one,op(a)]`, `mod` at `[zero,op(b)]`, each discharging its two side conditions by
  arithmetic.  `Bin = listl Bit` is `SnocList Unit Bit`, and `convert = ⦇[zero,shift]⦈`.
-/
module

public import AOP.A6_SnocList
import AOP.A6_3

namespace Freyd.Alg.RelSet.FastExp

open Freyd Freyd.Alg.RelSet.SL

/-- A binary digit `{0,1}`. -/
@[expose] public abbrev Bit : Type := Fin 2
/-- The natural numbers as an object. -/
@[expose] public abbrev dNat : RelSet.{0} := ⟨Nat⟩
/-- `Nat×Bit`, the pair arm of `F(Nat)`. -/
@[expose] public abbrev dNB : RelSet.{0} := ⟨Nat × Bit⟩

/-- `Bin`, the binary-number datatype `1 + Bin × Bit`, is `SnocList Unit Bit`. -/
@[expose] public abbrev Bin : RelSet.{0} := dSL Unit Bit

/-- `I = initial Unit Bit`, the initial algebra of `F X = 1 + X × Bit`. -/
abbrev I : InitialAlgebra (F Unit Bit) := initial Unit Bit

/-- The coproduct `𝟏+(X×Bit)` every algebra of this section is a case analysis over. -/
@[expose] public abbrev cop (C : RelSet.{0}) :
    Coproduct ((F Unit Bit).obj C) (dL Unit) ⟨C.carrier × Bit⟩ := sumCop _ _

/-- `zero : 𝟏 ⟶ Nat`. -/
@[expose] public def zero : dL Unit ⟶ dNat := graph fun _ => 0
/-- `one : 𝟏 ⟶ Nat`. -/
@[expose] public def one : dL Unit ⟶ dNat := graph fun _ => 1
/-- `shift(n,d) = 2×n+d`. -/
@[expose] public def shift : dNB ⟶ dNat := graph fun p => 2 * p.1 + p.2.val

/-- **B&dM p.144**: `convert = ⦇[zero,shift]⦈ : Bin ⟶ Nat`. -/
@[expose] public def convert : Bin ⟶ dNat := relCata (junc (cop dNat) zero shift)

/-- **B&dM p.144**: the specification `exp(a)(b) = a^b`. -/
@[expose] public def exp (a : Nat) : dNat ⟶ dNat := graph fun b => a ^ b

/-- **B&dM p.145**: the specification `mod(b)(a) = a mod b`. -/
@[expose] public def mod (b : Nat) : dNat ⟶ dNat := graph fun a => a % b

namespace Exp
/-- **B&dM p.144**: `op(a)(n,d) = (d=0 → n², a×n²)`. -/
@[expose] public def op (a : Nat) : dNB ⟶ dNat :=
  graph fun p => if p.2.val = 0 then p.1 ^ 2 else a * p.1 ^ 2
end Exp

namespace Modulus
/-- **B&dM p.145**: `op(b)(r,d) = (n≥b → n−b, n)` where `n = 2×r+d`. -/
@[expose] public def op (b : Nat) : dNB ⟶ dNat :=
  graph fun p => if 2 * p.1 + p.2.val ≥ b then 2 * p.1 + p.2.val - b else 2 * p.1 + p.2.val
end Modulus

/-! ## The derivation, for any map `f` and algebra `[g,h]` -/

variable {f : dNat ⟶ dNat} {g : dL Unit ⟶ dNat} {h : dNB ⟶ dNat}

/-- `convert` is simple: a fold of a map algebra is a map. -/
public theorem convert_simple : Simple convert := by
  have hm : Map (junc (cop dNat) zero shift) := junc_map _ (graph_map _) (graph_map _)
  unfold convert; rw [← cataR_eq_relCata]
  exact le_iff.mpr fun r r' ⟨dec, h1, h2⟩ => cataFold_functional _ hm dec r r' h1 h2

/-- **B&dM p.144, fusion**: `convert f = ⦇[g,h]⦈` when `zero f = g` and `shift f = (f×𝟙)h`. -/
public theorem convert_fusion (hg : zero ≫ f = g) (hh : shift ≫ f = rprodMap f (𝟙 (dE Bit)) ≫ h) :
    convert ≫ f = relCata (junc (cop dNat) g h) :=
  relCata_fusion I (by
    rw [junc_comp, hg, hh, Fmap_eq_sumMap, sumMap_junc]
    show _ = junc _ (𝟙 _ ≫ g) (prodMap (relProd _ _) (relProd _ _) f (𝟙 (dE Bit)) ≫ h)
    rw [Cat.id_comp, prodMap_eq_rprodMap])

/-- `F(X) = 𝟏+(X×Bit)` as the sum relator on `cop`: the same objects, and on arrows `F` agrees
    with it by `Fmap_eq_sumMap`. -/
abbrev Fsum : Relator RelSet.{0} RelSet.{0} :=
  Relator.sumOn (G := Relator.const (dL Unit))
    (H := Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bit))) cop

/-- `I` read as the initial algebra of `Fsum`: the same carrier, structure map and folds. -/
noncomputable abbrev Isum : InitialAlgebra Fsum where
  t := I.t
  α := I.α
  α_map := I.α_map
  cata := I.cata
  cata_map := I.cata_map
  cata_comm f hf := (I.cata_comm f hf).trans (by rw [Fmap_eq_sumMap])
  cata_unique f hf h hh hc := I.cata_unique f hf h hh (hc.trans (by rw [Fmap_eq_sumMap]))

/-- The fold over `Fsum` is the fold over `F`: the transposed algebras agree by `Fmap_eq_sumMap`. -/
theorem relCata_Isum {A : RelSet.{0}} (R : (F Unit Bit).obj A ⟶ A) :
    relCata (I := Isum) R = relCata (I := I) R := by
  unfold relCata; (simp only [Fmap_eq_sumMap]) <;> rfl

/-- **B&dM p.145**: `convert°⦇[g,h]⦈ = (μX : zero°g ∪ shift°(X×𝟙)h)` — Corollary 6.1
    over `F(X) = 𝟏+(X×Bit)`. -/
public theorem convert_recip_cata :
    convert° ≫ relCata (junc (cop dNat) g h)
      = mu (fun X : dNat ⟶ dNat => (zero° ≫ g) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ h)) := by
  unfold convert; rw [← relCata_Isum, ← relCata_Isum]
  refine (hylo_eq_mu_coprod (G := Relator.const (dL Unit))
    (H := Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bit))) cop Isum
    (S₁ := zero) (S₂ := shift)).trans ?_
  congr 1; funext X
  show (zero° ≫ 𝟙 _ ≫ g) ∪ (shift° ≫ prodMap (relProd _ _) (relProd _ _) X (𝟙 (dE Bit)) ≫ h) = _
  rw [Cat.id_comp, prodMap_eq_rprodMap]

/-- **B&dM p.144–145**: the divide-and-conquer program refines the specification `f`. -/
public theorem convert_program (hh : shift ≫ f = rprodMap f (𝟙 (dE Bit)) ≫ h) :
    mu (fun X : dNat ⟶ dNat => (zero° ≫ zero ≫ f) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ h)) ⊑ f :=
  calc mu (fun X : dNat ⟶ dNat => (zero° ≫ zero ≫ f) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ h))
        = convert° ≫ relCata (junc (cop dNat) (zero ≫ f) h) := convert_recip_cata.symm
    _ = convert° ≫ convert ≫ f := by rw [convert_fusion rfl hh]
    _ ⊑ 𝟙 dNat ≫ f := by rw [← Cat.assoc]; exact comp_mono_right convert_simple f
    _ = f := Cat.id_comp _

calc_steps convert_program

/-! ## Fast exponentiation -/

/-- The `shift` fusion condition for a graph: `shift graph(φ) = (graph(φ)×𝟙)graph(k)` as soon as
    `φ(2n+d) = k(φ(n),d)` — the pointwise equation each program below checks by arithmetic. -/
theorem shift_graph (φ : Nat → Nat) (k : Nat × Bit → Nat)
    (hk : ∀ n (d : Bit), φ (2 * n + d.val) = k (φ n, d)) :
    shift ≫ (graph φ : dNat ⟶ dNat) = rprodMap (graph φ) (𝟙 (dE Bit)) ≫ (graph k : dNB ⟶ dNat) := by
  apply hom_ext; rintro ⟨n, d⟩ m
  constructor
  · rintro ⟨j, hj, hm⟩
    refine ⟨(φ n, d), ⟨rfl, (id_apply d d).mpr rfl⟩, ?_⟩
    show m = k (φ n, d)
    rw [hm, hj]; exact hk n d
  · rintro ⟨⟨q, e⟩, hq, hm⟩
    obtain ⟨h1, h2⟩ := hq
    have h2 : d = e := (id_apply d e).mp h2
    refine ⟨2 * n + d.val, rfl, ?_⟩
    show m = φ (2 * n + d.val)
    have h1 : q = φ n := h1
    have hm : m = k (q, e) := hm
    rw [hm, hk, h1, h2]

/-- **B&dM p.145**, fusion condition: `zero exp(a) = one` — `a⁰ = 1`. -/
public theorem exp_zero (a : Nat) : zero ≫ exp a = one := by
  unfold zero exp one; rw [graph_comp]; rfl

/-- **B&dM p.145**, fusion condition: `shift exp(a) = (exp(a)×𝟙)op(a)` — `a^(2n+d)` is
    `(aⁿ)²` or `a×(aⁿ)²`. -/
public theorem exp_shift (a : Nat) : shift ≫ exp a = rprodMap (exp a) (𝟙 (dE Bit)) ≫ Exp.op a :=
  shift_graph _ _ fun n d => by
    show a ^ (2 * n + d.val) = if d.val = 0 then (a ^ n) ^ 2 else a * (a ^ n) ^ 2
    rw [Nat.pow_add, Nat.mul_comm 2 n, Nat.pow_mul]
    obtain ⟨d, hd⟩ := d
    match d, hd with
    | 0, _ => simp
    | 1, _ => simp [Nat.mul_comm]

/-- **B&dM p.145**: fast exponentiation, `(μX : zero°one ∪ shift°(X×𝟙)op(a)) ⊑ exp(a)`. -/
public theorem exp_program (a : Nat) :
    mu (fun X : dNat ⟶ dNat => (zero° ≫ one) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ Exp.op a))
      ⊑ exp a :=
  by have e := convert_program (exp_shift a); rwa [exp_zero] at e

/-! ## Modulus computation -/

/-- **B&dM p.145**, fusion condition: `zero mod(b) = zero` — `0 mod b = 0`. -/
public theorem mod_zero (b : Nat) : zero ≫ mod b = zero := by
  unfold zero mod; rw [graph_comp]; simp

/-- **B&dM p.145**, fusion condition: `shift mod(b) = (mod(b)×𝟙)op(b)` — with `r = a mod b` and
    `n = 2r+d < 2b`, `(2a+d) mod b` is `n−b` or `n`. -/
public theorem mod_shift (b : Nat) :
    shift ≫ mod b = rprodMap (mod b) (𝟙 (dE Bit)) ≫ Modulus.op b :=
  shift_graph _ _ fun a d => by
    show (2 * a + d.val) % b
      = if 2 * (a % b) + d.val ≥ b then 2 * (a % b) + d.val - b else 2 * (a % b) + d.val
    have hn : (2 * a + d.val) % b = (2 * (a % b) + d.val) % b := by
      have e : 2 * a + d.val = (2 * (a % b) + d.val) + b * (2 * (a / b)) := by
        have := Nat.mod_add_div a b
        rw [Nat.mul_left_comm b 2]; generalize b * (a / b) = t at this ⊢; omega
      rw [e, Nat.add_mul_mod_self_left]
    have hd := d.isLt
    rw [hn]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hr := Nat.mod_lt a hb
      split
      · rw [Nat.mod_eq_sub_mod (by assumption), Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)

/-- **B&dM p.145**: fast modulus, `(μX : zero°zero ∪ shift°(X×𝟙)op(b)) ⊑ mod(b)`. -/
public theorem mod_program (b : Nat) :
    mu (fun X : dNat ⟶ dNat => (zero° ≫ zero) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ Modulus.op b))
      ⊑ mod b :=
  by have e := convert_program (mod_shift b); rwa [mod_zero] at e

end Freyd.Alg.RelSet.FastExp
