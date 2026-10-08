/-
  Bird & de Moor, *Algebra of Programming* Ex 5.20 (book pp. 124, 126): power transposes
  of the relational-product relator, `cup` and `cap`, and the general "cp"-pattern.

  Setting: `Λ`, the power transpose, needs an `UnguardedPowerAllegory`
  (`Freyd.S2_4`/`AOP.A4_6`); the relational product `RelProd`/`topMor` (§5.2, `AOP.A5_2`)
  needs a `TabularUnitaryDivisionAllegory` (`Freyd.S2_3`).  Both classes already share
  `DivisionAllegory` as a common ancestor (`UnguardedPowerAllegory → PowerAllegory →
  DivisionAllegory ← TabularUnitaryDivisionAllegory`), so merging them into ONE class —
  exactly `Freyd.S2_41b`'s `TabularUnitaryPowerAllegory` pattern, but merged one level
  deeper (at `DivisionAllegory` instead of `DistributiveAllegory`, since A5_2 needs
  `topMor`, genuine division-allegory data, not just distributivity) — collapses the
  `Allegory` diamond to a single instance.
-/
module

public import AOP.A5_2
-- the cp-pattern at a SUM of relators: `Relator.sum`/`junc` (§5.3) and `P` on a map (§5.4).
public import AOP.A5_3
public import AOP.A5_4_PowerRel
public import Freyd.S2_147_MapCat

universe u

namespace Freyd.Alg
open PowerAllegory

/-- Merge class for Ex 5.20: a tabular unitary DIVISION allegory (gives `topMor`/`RelProd`,
    `AOP.A5_2`) whose power-object membership is additionally UNGUARDED (gives `Λ`/`∋`
    unconditionally, `AOP.A4_6`'s calculus).  Diamond-safe by the same structure-inheritance
    merge as `Freyd.S2_41b.TabularUnitaryPowerAllegory`. -/
public class TabularUnitaryUnguardedDivisionPowerAllegory (𝒜 : Type u) extends
    TabularUnitaryDivisionAllegory 𝒜, UnguardedPowerAllegory 𝒜

section
variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-- Diamond check: `RelProd`/`topMor` (division-allegory side) and `Λ`/`∋`
    (unguarded-power side) resolve on the SAME `Allegory 𝒜`. -/
example (A B : 𝒜) : Nonempty (RelProd A B) := relProd_nonempty A B
noncomputable example (A C : 𝒜) (R : C ⟶ A) : C ⟶ P A := Λ R
example (A : 𝒜) (f : A ⟶ P A) : Prop := Map f

end

variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-! ## Ex 5.20  `cup` (book p.124): the union relator, transposed

  For a chosen relational product `P` of `[a]` with itself, `cup pr : pr.p ⟶ [a]` is the
  power transpose of `(outl≫∋) ∪ (outr≫∋)` — the relation "belongs to the first OR the
  second set".  `Λ_union` shows this recovers `Λ(R∪S)` when fed the pair of transposes. -/

/-- **Ex 5.20** (B&dM p.124): `cup pr = Λ((∈·outl) ∪ (∈·outr))`, mirrored. -/
@[expose] public noncomputable def cup {A : 𝒜} (pr : RelProd (P A) (P A)) :
    pr.p ⟶ P A :=
  Λ ((pr.outl ≫ ∋ A) ∪ (pr.outr ≫ ∋ A))

/-- **Ex 5.20**: `Λ(R∪S) = cup·⟨ΛR,ΛS⟩`, mirrored: `Λ (R∪S) = pair(Λ R)(Λ S) ≫ cup pr`. -/
public theorem Λ_union {A C : 𝒜} (R S : C ⟶ A)
    (pr : RelProd (P A) (P A)) :
    Λ (R ∪ S) = pr.pair (Λ R) (Λ S) ≫ cup pr := by
  have hpair : Map (pr.pair (Λ R) (Λ S)) := pr.pair_map (Λ_is_map' R) (Λ_is_map' S)
  have hmap : Map (pr.pair (Λ R) (Λ S) ≫ cup pr) := map_comp hpair (Λ_is_map' _)
  symm; apply Λ_unique _ _ hmap
  rw [Cat.assoc, show cup pr ≫ ∋ A = (pr.outl ≫ ∋ A) ∪ (pr.outr ≫ ∋ A) from Λ_eps_eq' _,
    DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
    RelProd.pair_outl, RelProd.pair_outr, (Λ_is_map' S).1, (Λ_is_map' R).1,
    Cat.id_comp, Cat.id_comp, Λ_eps_eq', Λ_eps_eq']

/-! ## Ex 5.20  `cap` (book p.126): the intersection relator, transposed

  Same skeleton as `cup`, with `∩` in place of `∪`.  The distribution step now needs
  `pr.pair (Λ R) (Λ S)` to be a MAP (`simple_dist_inter`), since plain intersection does not
  distribute over composition in a general allegory the way union does. -/

/-- **Ex 5.20**: `cap pr = Λ((∈·outl) ∩ (∈·outr))`, mirrored. -/
noncomputable def cap {A : 𝒜} (pr : RelProd (P A) (P A)) :
    pr.p ⟶ P A :=
  Λ ((pr.outl ≫ ∋ A) ∩ (pr.outr ≫ ∋ A))

/-- **Ex 5.20**: `Λ(R∩S) = cap·⟨ΛR,ΛS⟩`, mirrored: `Λ (R∩S) = pair(Λ R)(Λ S) ≫ cap pr`. -/
theorem Λ_inter {A C : 𝒜} (R S : C ⟶ A)
    (pr : RelProd (P A) (P A)) :
    Λ (R ∩ S) = pr.pair (Λ R) (Λ S) ≫ cap pr := by
  have hpair : Map (pr.pair (Λ R) (Λ S)) := pr.pair_map (Λ_is_map' R) (Λ_is_map' S)
  have hmap : Map (pr.pair (Λ R) (Λ S) ≫ cap pr) := map_comp hpair (Λ_is_map' _)
  symm; apply Λ_unique _ _ hmap
  rw [Cat.assoc, show cap pr ≫ ∋ A = (pr.outl ≫ ∋ A) ∩ (pr.outr ≫ ∋ A) from Λ_eps_eq' _,
    simple_dist_inter hpair.2, ← Cat.assoc, ← Cat.assoc,
    RelProd.pair_outl, RelProd.pair_outr, (Λ_is_map' S).1, (Λ_is_map' R).1,
    Cat.id_comp, Cat.id_comp, Λ_eps_eq', Λ_eps_eq']

/-! ## The general "cp"-pattern (B&dM p.126)

  `cup`, `cap` and `cross` are all instances of transposing a RELATOR's action on `∈`
  along its own object map.  We record the general pattern and its one universal fact
  (the transpose is always a map); the individual laws (`Λ_union`, `Λ_inter`) are proved
  directly above rather than derived from this, since deriving them uniformly would need
  `Relator.PreservesRecip`/naturality hypotheses on `F` beyond what is needed here. -/

/-- **General cp-pattern** (B&dM p.126): for a relator `F : 𝒜 ⟶ 𝒜` (endo-relator), the
    transpose of `F`'s action on membership, `cp F a : F[a] ⟶ [F a]`.  `cup`/`cap`/`cross`
    are the instances for the various product relators (`F = Δ`, `∩`, `×`). -/
@[expose] public noncomputable def cpMap (F : Relator 𝒜 𝒜) (A : 𝒜) :
    F.obj (P A) ⟶ P (F.obj A) :=
  Λ (F.map (∋ A))

public theorem cpMap_is_map (F : Relator 𝒜 𝒜) (A : 𝒜) : Map (cpMap F A) := Λ_is_map' _

/-- `cpr ≜ cp(A×𝟙)` and `cpl ≜ cp(𝟙×A)` (B&dM p.126): the cross product at a product relator
    with one factor held at `A` — the value beside a set is paired with each member. -/
@[expose] public noncomputable def cprMap [HasRelProd 𝒜] (A B : 𝒜) :=
  cpMap (Relator.prod (Relator.const A) (Relator.idRelator 𝒜)) B

@[inherit_doc cprMap, expose] public noncomputable def cplMap [HasRelProd 𝒜] (A B : 𝒜) :=
  cpMap (Relator.prod (Relator.idRelator 𝒜) (Relator.const A)) B

/-! ## The cp-pattern at a SUM of relators (B&dM p.126, used at p.198)

  `Relator.sum` asks the ambient allegory to CHOOSE a coproduct for each pair of objects
  (`PositiveAllegory`), which the Ex 5.20 setting above does not carry.  Merging the two
  classes by structure inheritance — the same move as `TabularUnitaryUnguardedDivisionPowerAllegory`
  itself — keeps a single `Allegory 𝒜` underneath. -/

/-- The Ex 5.20 setting with CHOSEN coproducts, so `Relator.sum` and `cpMap` speak of one
    allegory. -/
public class PositiveTabularUnitaryUnguardedDivisionPowerAllegory (𝒜 : Type u) extends
    TabularUnitaryUnguardedDivisionPowerAllegory 𝒜, PositiveAllegory 𝒜

section
variable {𝒜 : Type u} [PositiveTabularUnitaryUnguardedDivisionPowerAllegory 𝒜]

/-- **`Λ(F+G)(∋) = [ΛF(∋)·Pu₁, ΛG(∋)·Pu₂]`**: the cross product of a SUM of relators is the
    junc of the summands' own cross products, each followed by its injection.  `Λ[R,S] =
    [ΛR,ΛS]` (`Λ_junc`) splits the transpose; an injection is a map (`Coproduct.u₁_map`), so
    `P` on it is `E` (`powerRel_map`) and absorption (`Λ_absorption`) pulls it back inside its
    own `Λ`.  At B&dM p.198's `F(A,X) = A + A×X` this is the `path-defn` step `ΛF(∋,𝟙) =
    𝟙+cpl`: the left summand's relator is the identity, whose cross product is `Λ(∋) = 𝟙`, and
    the right one's is `−×X`, whose cross product is `cpl`. -/
public theorem cpMap_sum_eq_junc (G H : Relator 𝒜 𝒜) (A : 𝒜) :
    cpMap (Relator.sum G H) A
      = junc (PositiveAllegory.has_coproduct
                (G.obj (P A)) (H.obj (P A)))
          (cpMap G A ≫ powerRel (PositiveAllegory.has_coproduct (G.obj A) (H.obj A)).u₁)
          (cpMap H A ≫ powerRel (PositiveAllegory.has_coproduct (G.obj A) (H.obj A)).u₂) := by
  simp only [cpMap]
  show Λ (junc (PositiveAllegory.has_coproduct
        (G.obj (P A)) (H.obj (P A)))
      (G.map (∋ A) ≫ (PositiveAllegory.has_coproduct (G.obj A) (H.obj A)).u₁)
      (H.map (∋ A) ≫ (PositiveAllegory.has_coproduct (G.obj A) (H.obj A)).u₂)) = _
  rw [Λ_junc, powerRel_map (Coproduct.u₁_map _), powerRel_map (Coproduct.u₂_map _),
    Λ_absorption, Λ_absorption]

end

-- printing-only: the note's `cp(F)` is `cpMap F A`: the object `A` is the wire under the bead, so
-- only `F` is printed.  B&dM p.126 writes `cpr`/`cpl` at `A×−`/`−×A`; the objects are the wires.
open Lean PrettyPrinter in
@[app_unexpander cpMap] public meta def unexpandCpMap : Unexpander
  | `($_ $F $_) => `($(mkIdent `cp) $F)
  | `($_ $F) => `($(mkIdent `cp) $F)
  | _ => `($(mkIdent `cp))
open Lean PrettyPrinter in
@[app_unexpander cprMap] public meta def unexpandCprMap : Unexpander | _ => `($(mkIdent `cpr))
open Lean PrettyPrinter in
@[app_unexpander cplMap] public meta def unexpandCplMap : Unexpander | _ => `($(mkIdent `cpl))

end Freyd.Alg
