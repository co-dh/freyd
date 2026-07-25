/-
  Bird & de Moor, *Algebra of Programming* Ex 5.20 (book pp. 124, 126): power transposes
  of the relational-product relator, `cup` and `cap`, and the general "cp"-pattern.

  Setting: `Λ` (Freyd's `A`, the power transpose) needs an `UnguardedPowerAllegory`
  (`Freyd.S2_4`/`AOP.A4_6`); the relational product `RelProd`/`topMor` (§5.2, `AOP.A5_2`)
  needs a `TabularUnitaryDivisionAllegory` (`Freyd.S2_3`).  Both classes already share
  `DivisionAllegory` as a common ancestor (`UnguardedPowerAllegory → PowerAllegory →
  DivisionAllegory ← TabularUnitaryDivisionAllegory`), so merging them into ONE class —
  exactly `Freyd.S2_41b`'s `TabularUnitaryPowerAllegory` pattern, but merged one level
  deeper (at `DivisionAllegory` instead of `DistributiveAllegory`, since A5_2 needs
  `topMor`, genuine division-allegory data, not just distributivity) — collapses the
  `Allegory` diamond to a single instance.
-/
import AOP.A5_2
import Freyd.S2_40
import AOP.A4_6
import Freyd.S2_41b

universe u

namespace Freyd.Alg

/-- Merge class for Ex 5.20: a tabular unitary DIVISION allegory (gives `topMor`/`RelProd`,
    `AOP.A5_2`) whose power-object membership is additionally UNGUARDED (gives `A`/`∋`
    unconditionally, `AOP.A4_6`'s calculus).  Diamond-safe by the same structure-inheritance
    merge as `Freyd.S2_41b.TabularUnitaryPowerAllegory`. -/
class TabularUnitaryUnguardedDivisionPowerAllegory (𝒜 : Type u) extends
    TabularUnitaryDivisionAllegory 𝒜, UnguardedPowerAllegory 𝒜

section
variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-- Diamond check: `RelProd`/`topMor` (division-allegory side) and `A`/`∋`
    (unguarded-power side) resolve on the SAME `Allegory 𝒜`. -/
noncomputable example (a b : 𝒜) : RelProd a b := relProd a b
noncomputable example (a c : 𝒜) (R : c ⟶ a) : c ⟶ PowerAllegory.powerObj a := A R
example (a : 𝒜) (f : a ⟶ PowerAllegory.powerObj a) : Prop := Map f

end

variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-! ## Ex 5.20  `cup` (book p.124): the union relator, transposed

  For a chosen relational product `P` of `[a]` with itself, `cup P : P.p ⟶ [a]` is the
  power transpose of `(outl≫∋) ∪ (outr≫∋)` — the relation "belongs to the first OR the
  second set".  `A_union` shows this recovers `Λ(R∪S)` when fed the pair of transposes. -/

/-- **Ex 5.20** (B&dM p.124): `cup P = Λ((∈·outl) ∪ (∈·outr))`, mirrored. -/
noncomputable def cup {a : 𝒜} (P : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)) :
    P.p ⟶ PowerAllegory.powerObj a :=
  A ((P.outl ≫ ∋ a) ∪ (P.outr ≫ ∋ a))

/-- **Ex 5.20**: `Λ(R∪S) = cup·⟨ΛR,ΛS⟩`, mirrored: `A (R∪S) = pair(A R)(A S) ≫ cup P`. -/
theorem A_union {a c : 𝒜} (R S : c ⟶ a)
    (P : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)) :
    A (R ∪ S) = P.pair (A R) (A S) ≫ cup P := by
  have hpair : Map (P.pair (A R) (A S)) := P.pair_map (A_is_map' R) (A_is_map' S)
  have hmap : Map (P.pair (A R) (A S) ≫ cup P) := map_comp hpair (A_is_map' _)
  symm; apply A_unique _ _ hmap
  rw [Cat.assoc, show cup P ≫ ∋ a = (P.outl ≫ ∋ a) ∪ (P.outr ≫ ∋ a) from A_eps_eq' _,
    DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
    RelProd.pair_outl, RelProd.pair_outr, (A_is_map' S).1, (A_is_map' R).1,
    Cat.id_comp, Cat.id_comp, A_eps_eq', A_eps_eq']

/-! ## Ex 5.20  `cap` (book p.126): the intersection relator, transposed

  Same skeleton as `cup`, with `∩` in place of `∪`.  The distribution step now needs
  `P.pair (A R) (A S)` to be a MAP (`simple_dist_inter`), since plain intersection does not
  distribute over composition in a general allegory the way union does. -/

/-- **Ex 5.20**: `cap P = Λ((∈·outl) ∩ (∈·outr))`, mirrored. -/
noncomputable def cap {a : 𝒜} (P : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)) :
    P.p ⟶ PowerAllegory.powerObj a :=
  A ((P.outl ≫ ∋ a) ∩ (P.outr ≫ ∋ a))

/-- **Ex 5.20**: `Λ(R∩S) = cap·⟨ΛR,ΛS⟩`, mirrored: `A (R∩S) = pair(A R)(A S) ≫ cap P`. -/
theorem A_inter {a c : 𝒜} (R S : c ⟶ a)
    (P : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)) :
    A (R ∩ S) = P.pair (A R) (A S) ≫ cap P := by
  have hpair : Map (P.pair (A R) (A S)) := P.pair_map (A_is_map' R) (A_is_map' S)
  have hmap : Map (P.pair (A R) (A S) ≫ cap P) := map_comp hpair (A_is_map' _)
  symm; apply A_unique _ _ hmap
  rw [Cat.assoc, show cap P ≫ ∋ a = (P.outl ≫ ∋ a) ∩ (P.outr ≫ ∋ a) from A_eps_eq' _,
    simple_dist_inter hpair.2, ← Cat.assoc, ← Cat.assoc,
    RelProd.pair_outl, RelProd.pair_outr, (A_is_map' S).1, (A_is_map' R).1,
    Cat.id_comp, Cat.id_comp, A_eps_eq', A_eps_eq']

/-! ## The general "cp"-pattern (B&dM p.126)

  `cup`, `cap` and `cross` are all instances of transposing a RELATOR's action on `∈`
  along its own object map.  We record the general pattern and its one universal fact
  (the transpose is always a map); the individual laws (`A_union`, `A_inter`) are proved
  directly above rather than derived from this, since deriving them uniformly would need
  `Relator.PreservesRecip`/naturality hypotheses on `F` beyond what is needed here. -/

/-- **General cp-pattern** (B&dM p.126): for a relator `F : 𝒜 ⟶ 𝒜` (endo-relator), the
    transpose of `F`'s action on membership, `cp F a : F[a] ⟶ [F a]`.  `cup`/`cap`/`cross`
    are the instances for the various product relators (`F = Δ`, `∩`, `×`). -/
noncomputable def cpMap (F : Relator 𝒜 𝒜) (a : 𝒜) :
    F.obj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj (F.obj a) :=
  A (F.map (∋ a))

theorem cpMap_is_map (F : Relator 𝒜 𝒜) (a : 𝒜) : Map (cpMap F a) := A_is_map' _

end Freyd.Alg
