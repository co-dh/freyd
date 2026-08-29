/-
  Bird & de Moor §5.7 in the set model: what the category of MONOTONE relations is NOT.

  `AOP.A5_7` builds `OrdObj`/`MonoHom` and their slide rules abstractly.  The facts that bound
  them — the hom-sets have no MEET, the tensor has no monotone MERGE, and the terminal object is
  the EMPTY one — are refutations and concrete constructions, so they need a concrete allegory
  and live here, after `Rel(Set)`, instead of dragging the §6.1 set model into a §5.7 module.
-/
module

public import AOP.A5_7
public import AOP.A6_1_RelSet

namespace Freyd.Alg

-- `reducible` so instance search sees through `ordMerge.carrier.carrier` to `Option Bool`; without
-- it `decide` cannot find `DecidableEq` on the elements below.
/-- The order `{(p,r),(q,r)}` on `{p,q,r}` — spelled `p,q,r = none, some false, some true` — in
    which two DISTINCT elements improve to the SAME one.  Both refutations below turn on that. -/
@[expose, reducible] public def ordMerge : OrdObj RelSet.{0} :=
  ⟨⟨Option Bool⟩, fun x y => x ≠ some true ∧ y = some true⟩

-- `⊑` asserts a WITNESS exists: at `0` both `X` and `Y` have one (`p` for `X`, `q` for `Y`),
-- and being different they are exactly what the meet drops.
/-- **The `∩` case of `monotonic_union` is FALSE, not merely unproved.**  Source `A = {0,1}` with
    `Ta = {(0,1)}` (spelled `0,1 = false,true`), target `ordMerge`, `X = {(0,p),(1,r)}`,
    `Y = {(0,q),(1,r)}`.  `X` and `Y` are monotone, but `X ∩ Y = {(1,r)}` is not: `Ta ≫ (X∩Y)`
    relates `0` to `r` while `(X∩Y) ≫ Tb` relates `0` to nothing. -/
public theorem inter_not_monotonic :
    ∃ (a b : OrdObj RelSet.{0}) (X Y : MonoHom a b),
      ¬ (a.ord ≫ (X.val ∩ Y.val) ⊑ (X.val ∩ Y.val) ≫ b.ord) := by
  refine ⟨⟨⟨Bool⟩, fun x y => x = false ∧ y = true⟩, ordMerge,
    ⟨fun x y => y = cond x (some true) none, ?_⟩,
    ⟨fun x y => y = cond x (some true) (some false), ?_⟩, ?_⟩
  · refine RelSet.le_iff.mpr ?_
    rintro x z ⟨y, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨none, rfl, by decide, rfl⟩
  · refine RelSet.le_iff.mpr ?_
    rintro x z ⟨y, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨some false, rfl, by decide, rfl⟩
  · intro h
    obtain ⟨y, ⟨hX, hY⟩, -⟩ := RelSet.le_iff.mp h false (some true) ⟨true, ⟨rfl, rfl⟩, rfl, rfl⟩
    exact absurd (hX.symm.trans hY) (by decide)

-- Two DIFFERENT elements improve to the SAME one, so the merge accepts them after improving and
-- refuses them before; copy has no such freedom, which is why `pair_slides` goes through.
/-- **The MERGE does not slide** — the other half of `inter_not_monotonic`, since `∩` is copy,
    run both, merge.  Over `ordMerge`, with `merge ((x,y),z)` iff `x=y=z`: `((p,q),r)` lies in
    `(T×T) ≫ merge` (take `p→r` and `q→r`, both landing on `r`) but not in `merge ≫ T`, which
    already needs `p=q`.  Contrast `pair_slides` at `𝟙`, the lax copy law, which holds. -/
public theorem merge_not_monotonic :
    ∃ (a : OrdObj RelSet.{0}) (merge : (relProd a.carrier a.carrier).p ⟶ a.carrier),
      ¬ (prodMap (relProd a.carrier a.carrier) (relProd a.carrier a.carrier) a.ord a.ord ≫ merge
          ⊑ merge ≫ a.ord) := by
  refine ⟨ordMerge, fun x z => x.1 = z ∧ x.2 = z, ?_⟩
  intro h
  rw [RelSet.prodMap_eq_rprodMap] at h
  obtain ⟨z, ⟨hp, hq⟩, -⟩ := RelSet.le_iff.mp h (none, some false) (some true)
    ⟨(some true, some true), ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩, rfl, rfl⟩
  exact absurd (hp.trans hq.symm) (by decide)

/-- The EMPTY object, carrying the only relation there is on `Empty`. -/
@[expose] public def ordEmpty : OrdObj RelSet.{0} := ⟨⟨Empty⟩, fun _ y => y.elim⟩

/-- `Rel(Set)`'s ONE-element object is not terminal — an arrow `a ⟶ 1` is a subset of `a`, not a
    single arrow — but the EMPTY object is, here and in `Rel(Set)` itself: any two relations
    `a ⟶ ∅` are equal by `funext`, and the monotonicity side condition is vacuous. -/
public theorem ordEmpty_terminal (a : OrdObj RelSet.{0}) :
    ∃ X : MonoHom a ordEmpty, ∀ Y : MonoHom a ordEmpty, Y = X :=
  ⟨⟨fun _ y => y.elim, RelSet.le_iff.mpr fun _ y => y.elim⟩,
   fun _ => Subtype.ext (funext fun _ => funext fun y => y.elim)⟩

end Freyd.Alg
