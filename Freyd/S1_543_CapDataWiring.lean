/-
  Freyd & Scedrov, *Categories and Allegories* §1.543/§1.546/§1.547 — WIRING.

  This file discharges `Freyd.capData_exists` — `∀ A, Nonempty (CapData A)` — by wiring the §1.547
  UNIFORM capitalization successor into the ω-tower fixpoint.  It lives DOWNSTREAM of
  `Capitalization.lean` because every ingredient it consumes transitively imports `Capitalization`
  (the uniform step, the cofinal cover, the well-points reduction, the cofinal `hstage`).  An
  upstream placement is impossible (it would create an import cycle); `RelativeCapitalization.lean`'s
  own notes anticipate "`capData_exists` relocated here".

  COMPLETE — `capitalization_lemma` is SORRY-FREE (axioms `[propext, Classical.choice, Quot.sound]`).
  The §1.546 density `FibreDensity (wsCover S)` is discharged by `wsCover_fibreDensity`; every step
  (the uniform `CapStep`, its pre-regular target, faithfulness, finite-limit preservation; the cofinal
  cover `wsCover`; the ω-tower preservation package `towerH*`; the cofinal `hstage`; the capital
  fixpoint `tower_capital_of_cofinal`; the `CapData` packaging `capData_of_tower`) is Sorry-free.

  Assembled term (read top-down):
    * `hFD : ∀ S, FibreDensity (wsCover S)`              — `wsCover_fibreDensity` (the §1.546 density).
    * `ccs : CofinalCapStep`                             — `step := uniformStep ∘ wsCover`,
        `wellPoints := stepWellPoints_of_fibreDensity ∘ hFD`.
    * `capData_of_tower A ccs.step b rfl <package> hcap` — the `CapData A`, where
        `<package>` = the eight `towerH*` ω-tower preservation hyps + `towerHcanon`, and
        `hcap := tower_capital_of_cofinal A ccs b <package> (hstage_of_cofinal b ccs <package>)`.
-/
module

public import Freyd.S1_543_UniformWellPoints
public import Freyd.S1_543_CofinalHstage
public import Freyd.S1_546_FibreDensityProof

universe u

namespace Freyd

open Freyd.CofinalProj (wsCover)
open Freyd.UniformCap (uniformStep)
open Freyd.UniformWellPoints (FibreDensity stepWellPoints_of_fibreDensity)

/-- **§1.543 capitalization data exists** — every small pre-regular `A` admits a `CapData A`.

    The §1.547 UNIFORM successor `uniformStep (wsCover S)` glues the slices `S/(∏U)` over every
    finite set `U` of well-supported objects (cofinal in the subset order, hence pointing EVERY
    well-supported `B`, not merely a countable suffix).  Bundled with the points-acquisition
    obligation it forms a `CofinalCapStep`; the ω-tower it generates is pre-regular
    (`towerH*` package) and **capital** (`tower_capital_of_cofinal`, via the cofinal `hstage`),
    packaged into `Nonempty (CapData A)` by `capData_of_tower`.

    The §1.546 stage-local density `FibreDensity (wsCover S)` (every proper fibre mono is missed by a
    fibre point at a later stage) is `wsCover_fibreDensity`; the whole lemma is Sorry-free. -/
public theorem capData_exists (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    Nonempty (CapData.{u} A) := by
  -- §1.546 fibre-density, for every bundle's cofinal cover `wsCover S` (Sorry-free: `wsCover_fibreDensity`).
  have hFD : ∀ (S : PreRegBundle.{u}),
      letI := S.cat; letI := S.pre; letI := (wsCover S).dec
      FibreDensity (wsCover S) := fun S => Freyd.CofinalProj.wsCover_fibreDensity S
  -- The cofinal capitalizing successor: uniform step per bundle, well-points from `hFD`.
  let ccs : CofinalCapStep.{u} :=
    { step := fun S =>
        letI := S.cat; letI := S.pre; letI := (wsCover S).dec
        uniformStep (wsCover S)
      wellPoints := fun S =>
        letI := S.cat; letI := S.pre; letI := (wsCover S).dec
        stepWellPoints_of_fibreDensity (wsCover S) (hFD S) }
  let b : PreRegBundle.{u} := ⟨A, inferInstance, inferInstance⟩
  -- The ω-tower preservation package for `ccs.step`, packaged into a `CapData` by `capData_of_tower`;
  -- its `hcap` (capital closure) is the last hole, filled by the cofinal fixpoint below.
  refine ⟨capData_of_tower A ccs.step b rfl
    (towerHasTerminal b ccs.step)
    (fun {i j} hij => towerHtpres b ccs.step hij)
    (towerHp b ccs.step)
    (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
    (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q)
    (towerHe b ccs.step)
    (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
    (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
    (towerHcanon b ccs.step)
    ?_⟩
  -- `hcap : Capital (towerSystem b ccs.step).Obj` — the §1.543 fixpoint, from the cofinal `hstage`.
  exact tower_capital_of_cofinal A ccs b
    (towerHasTerminal b ccs.step)
    (fun {i j} hij => towerHtpres b ccs.step hij)
    (towerHp b ccs.step)
    (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
    (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q)
    (towerHe b ccs.step)
    (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
    (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
    (towerHcanon b ccs.step)
    (hstage_of_cofinal b ccs
      (towerHasTerminal b ccs.step)
      (fun {i j} hij => towerHtpres b ccs.step hij)
      (towerHp b ccs.step)
      (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
      (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q)
      (towerHe b ccs.step)
      (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
      (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
      (towerHcanon b ccs.step))

/-- **§1.54 / §1.543 Capitalization Lemma** (small case, object universe = morphism universe).
    Every small pre-regular category `A` admits a faithful representation into a capital
    pre-regular category `Ā`.  Reduced to `capData_exists` (the §1.547/§1.543 construction above,
    relocated here — downstream of the §1.547 uniform-successor pieces, which a
    `Capitalization.lean` placement could not reach) via `capitalization_of_capData` (the colimit
    packaging, in `Capitalization.lean`). -/
public theorem capitalization_lemma (A : Type u) [Cat.{u} A] [PreRegularCategory A] :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hP : PreRegularCategory Ā),
      @Capital.{u, u} Ā hC (hP.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F :=
  (capData_exists A).elim (fun cd => capitalization_of_capData cd)

end Freyd

