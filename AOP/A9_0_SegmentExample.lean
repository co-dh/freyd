/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one worked instance: segmenting a list.

  The base functor is the list functor `F(X) = 𝟏 + [a]×X` (`CL.F Unit (ConsList Unit A)`), and
  `T = [nil, cat]` with `cat` at B&dM's restricted type `list⁺ A × list A` (p.128, `catNE`), so
  `T°` cuts a non-empty prefix off a list every way and `⦇T⦈` is `concat` (`concatNE`).
  WIP: the algebra `h` is still to be chosen; only the `T` side is here.
-/
module

public import AOP.A9_1

namespace Freyd.Alg.RelSet.Segment

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-- **`T = [nil, cat] : FA⟶A`**, `A = [a]`: `inl(()) ↦ []`, `inr(xs,ys) ↦ xs⧺ys` with `xs`
    non-empty, so `T°` cuts off a non-empty prefix every way. -/
@[expose] public def T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A :=
  junc (sumCop (dL Unit) ⟨ConsList Unit A × ConsList Unit A⟩) wrapR catNE

/-- **`⦇T⦈ = concat`**: folding with `T` flattens a list of non-empty segments. -/
public theorem fold_T :
    (⦇(T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈
      : (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0}) ⟶ dList A) = concatNE := rfl

/-- **`⦇T⦈° = partition`**: unfolding with `T°` segments a list every way. -/
public theorem fold_T_recip :
    (⦇(T : (F Unit (ConsList Unit A)).obj (dList A) ⟶ dList A)⦈)°
      = (partition : dList A ⟶ (⟨ConsList Unit (ConsList Unit A)⟩ : RelSet.{0})) := by
  rw [fold_T, partition_concat]

end Freyd.Alg.RelSet.Segment
