/-
  §1.543 / §2.218 R3 — the capitalization `Ā` is REGULAR.

  `capData_exists` (CapDataWiring) builds the cofinal ω-tower and a PRE-regular capital `Ā`.  Here we
  upgrade it to REGULAR by supplying the per-stage images obligation `hi` of `capData_of_tower_regular`:
    * stage 0 = `A`               — has images since `[RegularCategory A]`,
    * stage n+1 = `ratCapCat …`   — has images by `ratCapHasImages` (RatCapImages), given the inductive
                                    `HasImages` of stage n.
  By induction every tower stage has images (`stageHasImages`), so the colimit `Ā` is `RegularCategory`.
  This discharges the `[RegularCategory Ā]` hypothesis of §2.218 `repr_in_power_of_sets`. -/
module

public import Freyd.S1_543_CapDataWiring
public import Freyd.S1_543_RatCapImages

open Freyd
open Freyd.Colim
open Freyd.CofinalProj
open Freyd.UniformCap (uniformStep)
open Freyd.UniformWellPoints (FibreDensity stepWellPoints_of_fibreDensity)
open Freyd.LaxColim (ratCapHasImages)

namespace Freyd

universe u

/-- The §1.547 uniform cofinal successor as a step function — definitionally `capData_exists`'s
    `ccs.step` (`uniformStep (wsCover S)`, with `S`'s structure + the `Classical.decEq` exception). -/
@[expose] public noncomputable def uniformStepFun (S : PreRegBundle.{u}) : CapStep S.carrier :=
  letI := S.cat; letI := S.pre; letI := (wsCover S).dec
  uniformStep (wsCover S)

/-- **Every stage of the cofinal ω-tower has images.**  Stage 0 = `A` (the supplied `hb0`); stage
    `n+1 = ratCapCat (cofinalProjSystem stage_n)` has images by `ratCapHasImages`, inductively. -/
@[expose] public noncomputable def stageHasImages (b : PreRegBundle.{u}) (hb0 : @HasImages b.carrier b.cat) :
    ∀ n, @HasImages (stageBundle uniformStepFun b n).carrier (stageBundle uniformStepFun b n).cat
  | 0 => hb0
  | (n + 1) => by
    letI hpreN : PreRegularCategory (stageBundle uniformStepFun b n).carrier :=
      (stageBundle uniformStepFun b n).pre
    letI : @HasImages (stageBundle uniformStepFun b n).carrier (stageBundle uniformStepFun b n).cat :=
      stageHasImages b hb0 n
    letI : HasEqualizers (stageBundle uniformStepFun b n).carrier :=
      products_pullbacks_implies_equalizers
    letI : HasPullbacks (stageBundle uniformStepFun b n).carrier := hpreN.toHasPullbacks
    letI := (wsCover (stageBundle uniformStepFun b n)).dec
    letI : Nonempty (WSList (stageBundle uniformStepFun b n).carrier) :=
      ⟨(wsCover (stageBundle uniformStepFun b n)).base⟩
    exact ratCapHasImages (cofinalProjSystem (S := (stageBundle uniformStepFun b n).carrier))
      (fun {_ _} h => cofinalProjSystem_cover h)

/-- **§1.54 + §2.218 R3 — the REGULAR Capitalization Lemma.**  Every small REGULAR `A` admits a faithful
    representation into a REGULAR, CAPITAL `Ā`.  (Same cofinal construction as `capitalization_lemma`,
    upgraded with the per-stage images `stageHasImages`.) -/
theorem capitalization_lemma_regular (A : Type u) [Cat.{u} A] [RegularCategory A] :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hR : RegularCategory Ā),
      @Capital.{u, u} Ā hC (hR.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  have hFD : ∀ (S : PreRegBundle.{u}),
      letI := S.cat; letI := S.pre; letI := (wsCover S).dec
      FibreDensity (wsCover S) := fun S => Freyd.CofinalProj.wsCover_fibreDensity S
  let ccs : CofinalCapStep.{u} :=
    { step := uniformStepFun
      wellPoints := fun S =>
        letI := S.cat; letI := S.pre; letI := (wsCover S).dec
        stepWellPoints_of_fibreDensity (wsCover S) (hFD S) }
  let b : PreRegBundle.{u} := ⟨A, inferInstance, inferInstance⟩
  exact capData_of_tower_regular A ccs.step b rfl
    (towerHasTerminal b ccs.step)
    (fun {i j} hij => towerHtpres b ccs.step hij)
    (towerHp b ccs.step)
    (fun {i j} hij a c z uu vv h1 h2 => towerHppres b ccs.step hij a c z uu vv h1 h2)
    (fun {i j} hij a c z p q => towerHppresPair b ccs.step hij a c z p q)
    (towerHe b ccs.step)
    (fun {i j} hij _ _ f g z uu vv h => towerHepres b ccs.step hij f g z uu vv h)
    (fun {i j} hij _ _ f g z k hk => towerHepresLift b ccs.step hij f g z k hk)
    (towerHcanon b ccs.step)
    (tower_capital_of_cofinal A ccs b
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
        (towerHcanon b ccs.step)))
    (fun i => stageHasImages b RegularCategory.toHasImages i.down)

end Freyd
