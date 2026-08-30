/-
  Bird & de Moor, *Algebra of Programming* §6.4  Fast exponentiation and modulus computation
  (book pp. 144-146) — worked programs in the Set model `Rel(Set)`.

  To compute `a^b` (and `a mod b`) in `O(log b)` steps rather than `O(b)`, B&dM route the naive
  catamorphism through an intermediate BINARY datatype `Bin = listl Bit` (`Bit = {0,1}`), the
  initial algebra of `F X = 1 + (X × Bit)` — i.e. `SnocList Unit Bit` from `AOP.A6_SnocList`.
  `convert : Nat ← Bin = ⦇[zero, shift]⦈` evaluates a bit-list (`shift(n,d) = 2n+d`); then

    `exp a = ⦇[one, op a]⦈ · convert°`   with   `op a (n,d) = (d=0 → n², a·n²)`

  is a HYLOMORPHISM, and by the hylomorphism theorem (`AOP.A6_3.hylo_eq_mu`) it equals the
  divide-and-conquer least fixed point — the fast recursion.  `mod b` is the same with the algebra
  `[zero, op b]`, `op b (r,d) = (n ≥ b → n-b, n)`, `n = 2r+d`.  This section demonstrates that a
  divide-and-conquer scheme is introduced by folding through a suitable intermediate datatype.
-/
module

public import AOP.A6_SnocList
public import AOP.A6_3

namespace Freyd.Alg.RelSet.FastExp

open Freyd Freyd.Alg.RelSet.SL

/-- A binary digit `{0,1}`. -/
@[expose] public abbrev Bit : Type := Fin 2
/-- The natural numbers as an object. -/
@[expose] public abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- `Bin`, the binary-number datatype `1 + Bin × Bit`, is `SnocList Unit Bit`. -/
abbrev dBin : RelSet.{0} := dSL Unit Bit

/-- `I = initial Unit Bit`, the initial algebra of `F X = 1 + X × Bit`. -/
abbrev I : InitialAlgebra (F Unit Bit) := initial Unit Bit

/-- The `convert` algebra `[zero, shift]`: `zero ↦ 0`, `shift (n, d) ↦ 2n + d`. -/
def con_conv : (Fobj Unit Bit dNat).carrier → Nat
  | Sum.inl _ => 0
  | Sum.inr p => 2 * p.1 + p.2.val

/-- `convert = ⦇[zero, shift]⦈ : Bin → ℕ` evaluates a bit-list as a binary number. -/
def convAlg : (F Unit Bit).obj dNat ⟶ dNat := graph con_conv

/-- The exponentiation algebra `[one, op a]`: `one ↦ 1`, `op a (n, d) = (d = 0 → n², a·n²)`. -/
def con_exp (a : Nat) : (Fobj Unit Bit dNat).carrier → Nat
  | Sum.inl _ => 1
  | Sum.inr p => if p.2.val = 0 then p.1 ^ 2 else a * p.1 ^ 2

def expAlg (a : Nat) : (F Unit Bit).obj dNat ⟶ dNat := graph (con_exp a)

/-- The modulus algebra `[zero, op b]`: `zero ↦ 0`, `op b (r, d) = (n ≥ b → n-b, n)`, `n = 2r+d`. -/
def con_mod (b : Nat) : (Fobj Unit Bit dNat).carrier → Nat
  | Sum.inl _ => 0
  | Sum.inr p => if 2 * p.1 + p.2.val ≥ b then 2 * p.1 + p.2.val - b else 2 * p.1 + p.2.val

def modAlg (b : Nat) : (F Unit Bit).obj dNat ⟶ dNat := graph (con_mod b)

/-- **Fast exponentiation (B&dM p.145)**: `exp a = ⦇[one, op a]⦈ · convert°`, a hylomorphism. -/
def exp (a : Nat) : dNat ⟶ dNat := (relCata convAlg)° ≫ relCata (expAlg a)

/-- **Fast modulus (B&dM p.145)**: `mod b = ⦇[zero, op b]⦈ · convert°`, a hylomorphism. -/
def modFast (b : Nat) : dNat ⟶ dNat := (relCata convAlg)° ≫ relCata (modAlg b)

/-- **§6.4 (B&dM p.145)**: fast exponentiation IS the divide-and-conquer least fixed point.  By
    the hylomorphism theorem, `exp a = μX : op-a · F(X) · shift°` (mirrored) — the `O(log b)`
    recursion `exp a b = 1 if b=0, op a (exp a (b div 2), b mod 2) otherwise`, once the coproduct
    is split into a conditional (which needs the disjoint-ranges/junc machinery). -/
theorem exp_eq_mu (a : Nat) :
    exp a = mu (fun X : dNat ⟶ dNat => convAlg° ≫ (F Unit Bit).map X ≫ expAlg a) :=
  hylo_eq_mu (F_preservesRecip Unit Bit) I (expAlg a) convAlg

/-- **§6.4 (B&dM p.146)**: fast modulus IS the divide-and-conquer least fixed point, by the
    hylomorphism theorem — the `O(log a)` recursion for `a mod b`. -/
theorem mod_eq_mu (b : Nat) :
    modFast b = mu (fun X : dNat ⟶ dNat => convAlg° ≫ (F Unit Bit).map X ≫ modAlg b) :=
  hylo_eq_mu (F_preservesRecip Unit Bit) I (modAlg b) convAlg

end Freyd.Alg.RelSet.FastExp
