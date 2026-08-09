/-
  §2.218 R3 (positive) — every stage of the §2.218 cofinal ω-tower is a
  `DisjointBinaryCoproduct` (positive) when stage 0 is.  Companion to `stageHasImages`
  (`Freyd/CapDataRegular.lean`), upgraded from `HasImages` to `DisjointBinaryCoproduct` via
  `ratCapDisjointBinaryCoproduct` (RatCapPositive).

  INSTANCE-DIAMOND NOTE.  `ratCapHasImages` derives its output `Cat`'s base `[HasPullbacks 𝒞]` from
  the transparent `[PreRegularCategory 𝒞]` = `(stage n).pre`, so `stageHasImages` recurses with no
  friction.  `ratCapDisjointBinaryCoproduct`'s output `Cat` (`ratCapCat P`) instead derives that base
  `[HasPullbacks 𝒞]` from the `[DisjointBinaryCoproduct 𝒞]` argument (`ratCapPosPinPb`).  In the
  successor case that argument is the (opaque) recursive stage-`n` coproduct, whose pre-regular
  structure the kernel cannot reduce to `(stage n).pre`.  We close this by THREADING the full
  pre-regular-structure equality `dbcPreReg dₙ = (stage n).pre` through the recursion and discharging
  the successor through `succ_component`, which takes the previous pre-regular structure as an
  explicit *variable* `pr` so that `subst` makes the `ratCapDisjointBinaryCoproduct` result land on
  `(stage (n+1)).cat` on the nose — no surviving `cast`.  The base equality is `rfl` for the real
  §2.218 consumer (which builds `b` from the same `[DisjointBinaryCoproduct A]`). -/
module

public import Freyd.S1_543_CapDataRegular
public import Freyd.S2_218_RatCapPositive

open Freyd
open Freyd.Colim
open Freyd.CofinalProj
open Freyd.LaxColim (ratCapDisjointBinaryCoproduct)

namespace Freyd

universe u

/-- The pre-regular structure carried by a `DisjointBinaryCoproduct` (its regular structure, forgotten
    to pre-regular).  This is exactly the `[PreRegularCategory 𝒞]` whose pullbacks
    `ratCapDisjointBinaryCoproduct`'s output `Cat` is built over (`ratCapPosPinPb` reduces to its
    `toHasPullbacks`). -/
@[expose] public def dbcPreReg {𝒞 : Type u} {inst : Cat.{u} 𝒞} (d : @DisjointBinaryCoproduct 𝒞 inst) :
    @PreRegularCategory 𝒞 inst :=
  @RegularCategory.toPreRegularCategory 𝒞 inst d.toPositivePreLogos.toPreLogos.toRegularCategory

/-- **The §1.547 uniform successor of a disjoint binary coproduct.**  Given a small category `C` with
    a chosen pre-regular structure `pr` (as a *variable*) and a `DisjointBinaryCoproduct dC` whose own
    pre-regular structure equals `pr`, the next tower stage `(uniformStepFun ⟨C, ct, pr⟩)` is again a
    disjoint binary coproduct, and its pre-regular structure is the stage's `preT`.  Stating `pr` as a
    variable lets `subst hpre` align `dC`'s base pullbacks with `pr`'s on the nose, so the
    `ratCapDisjointBinaryCoproduct` result fits the stage `Cat` without a residual `cast`. -/
@[expose] public noncomputable def succ_component {C : Type u} (ct : Cat.{u} C) (pr : @PreRegularCategory C ct)
    (dC : @DisjointBinaryCoproduct C ct) (hpre : dbcPreReg dC = pr) :
    PSigma fun d : @DisjointBinaryCoproduct (uniformStepFun ⟨C, ct, pr⟩).T
        (uniformStepFun ⟨C, ct, pr⟩).catT =>
      dbcPreReg d = (uniformStepFun ⟨C, ct, pr⟩).preT := by
  subst hpre
  letI iS : PreRegBundle.{u} := ⟨C, ct, dbcPreReg dC⟩
  letI : Cat C := ct
  letI : PreRegularCategory C := dbcPreReg dC
  letI : DisjointBinaryCoproduct C := dC
  letI : HasEqualizers C := products_pullbacks_implies_equalizers
  letI : DecidableEq C := (wsCover iS).dec
  letI : Nonempty (WSList C) := ⟨(wsCover iS).base⟩
  exact ⟨ratCapDisjointBinaryCoproduct (cofinalProjSystem (S := C))
      (fun {_ _} h => cofinalProjSystem_cover h), rfl⟩

/-- **Tower of disjoint binary coproducts, with the threaded pre-regular-structure equality.** -/
@[expose] public noncomputable def stageDisjointAux (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre) :
    ∀ n, PSigma fun d : @DisjointBinaryCoproduct (stageBundle uniformStepFun b n).carrier
        (stageBundle uniformStepFun b n).cat =>
      dbcPreReg d = (stageBundle uniformStepFun b n).pre
  | 0 => ⟨hb0, hpb0⟩
  | (n + 1) =>
    let prev := stageDisjointAux b hb0 hpb0 n
    succ_component (stageBundle uniformStepFun b n).cat (stageBundle uniformStepFun b n).pre
      prev.1 prev.2

/-- **Every stage of the cofinal ω-tower is a disjoint binary coproduct (positive).**  `hpb0` is `rfl`
    for the §2.218 consumer (whose `b.pre` is `hb0`'s own pre-regular structure). -/
@[expose] public noncomputable def stageDisjoint (b : PreRegBundle.{u})
    (hb0 : @DisjointBinaryCoproduct b.carrier b.cat) (hpb0 : dbcPreReg hb0 = b.pre) (n : Nat) :
    @DisjointBinaryCoproduct (stageBundle uniformStepFun b n).carrier
      (stageBundle uniformStepFun b n).cat :=
  (stageDisjointAux b hb0 hpb0 n).1

end Freyd
