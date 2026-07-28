/-
  `diag.CB_Allegory` — THE BRIDGE: every cartesian bicategory of relations is an allegory.

  This is the acceptance criterion of the whole `diag` programme (`diag/PLAN.md`): the diagrammatic
  theory must PROVE the allegory results, not merely picture them.  Once `allegoryOfCartBicat` is
  available, every theorem of `Freyd/S2_10.lean` — and everything downstream of it in the AOP
  chapter-4 corpus — holds in the diagrammatic setting.

  Nothing here is assumed.  In particular the MODULAR LAW is a theorem: adding it as a `CartBicat`
  field would make this bridge circular, and Freyd's own presentation takes it as an axiom precisely
  because an allegory has no Frobenius structure to derive it from.  What derives it is the Frobenius
  equation (41) together with the lax copy inequation (42); see `CartBicat.nabla_slide_conv`
  (`diag/CB.lean`), which carries the argument.

  `Frobenius.pdf` p. 4 asserts "The Frobenius law implies the modular law [CW87, remark 2.9(ii)]"
  but does not prove it, and CW87 is not in the repo — every occurrence of "modular law" in
  `Frobenius.pdf` USES the law rather than deriving it.  The derivation below is therefore
  reconstructed, not transcribed.
-/
import diag.CB_Derived
import Freyd.S2_10

universe v u

namespace Freyd.Diag

open Freyd
open SymMonCat
open CartBicat

variable {𝒞 : Type u} [CartBicat.{v} 𝒞]

/-- SEMI-DISTRIBUTIVITY, `R(S ∩ T) ≤ RS ∩ RT` — Freyd's `semidistrib` (§2.11), and eq. (3) on p. 4
    of functorialSemanticsForRelationalTheories.pdf.  `R(S ∩ T)` is below `RS` and below `RT` by
    monotonicity of composition, so it is below their greatest lower bound.  The lax inequation (42)
    is what makes `∩` a greatest lower bound in the first place (via `meet_idem`). -/
theorem semidistrib_of_lax {a b c : 𝒞} (R : a ⟶ b) (S T : b ⟶ c) :
    (R ≫ meet S T) ≤ (meet (R ≫ S) (R ≫ T)) :=
  meet_glb (OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («meet_≤_left» S T))
    (OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («meet_≤_right» S T))

/-- THE MODULAR LAW, `RS ∩ T ≤ (R ∩ TS°)S` — Freyd's `modular` (§2.11), DERIVED.

    Strip the shared prefix `Δ_a;(R ⊗ T)` off both sides — `(RS) ⊗ T` factors as `(R ⊗ T);(S ⊗ 𝟙)`
    and `R ⊗ (TS°)` as `(R ⊗ T);(𝟙 ⊗ S°)` — and what is left is exactly `nabla_slide_conv`,
    `(S ⊗ 𝟙);∇ ≤ (𝟙 ⊗ S°);∇;S`.  That is where the Frobenius equation and the lax copy inequation
    are spent; everything here is bookkeeping. -/
theorem modular_of_frobenius {a b c : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (meet (R ≫ S) T) ≤ (meet R (T ≫ conv S) ≫ S) := by
  have hL : meet (R ≫ S) T
      = (Δ a ≫ (R ⊗ₕ T)) ≫ (S ⊗ₕ 𝟙 c) ≫ ∇ c := by
    dsimp [meet]
    calc Δ a ≫ ((R ≫ S) ⊗ₕ T) ≫ ∇ c
        = Δ a ≫ ((R ⊗ₕ T) ≫ (S ⊗ₕ 𝟙 c)) ≫ ∇ c := by
          rw [← tensHom_comp, Cat.comp_id]
      _ = (Δ a ≫ (R ⊗ₕ T)) ≫ (S ⊗ₕ 𝟙 c) ≫ ∇ c := by simp only [Cat.assoc]
  have hR : meet R (T ≫ conv S) ≫ S
      = (Δ a ≫ (R ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S := by
    dsimp [meet]
    calc (Δ a ≫ (R ⊗ₕ (T ≫ conv S)) ≫ ∇ b) ≫ S
        = (Δ a ≫ ((R ⊗ₕ T) ≫ (𝟙 b ⊗ₕ conv S)) ≫ ∇ b) ≫ S := by
          rw [← tensHom_comp, Cat.comp_id]
      _ = (Δ a ≫ (R ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S := by simp only [Cat.assoc]
  -- A THREE-LINK `calc` rather than `rw [hL, hR]; exact …`, so the argument sits in the proof TERM
  -- where `diag-export --proof` can draw it — and draw it with `R`, `S` and `T` all present, which
  -- is what the modular law is about.  `nabla_slide_conv` alone mentions only `S`.  The reshaping
  -- links are stated at `=`, so the drawn chain shows the middle step as the one inequality.
  calc meet (R ≫ S) T
      = (Δ a ≫ (R ⊗ₕ T)) ≫ (S ⊗ₕ 𝟙 c) ≫ ∇ c := hL
    _ ≤ (Δ a ≫ (R ⊗ₕ T)) ≫ (𝟙 b ⊗ₕ conv S) ≫ ∇ b ≫ S :=
        OrderedCat.comp_mono (OrderedCat.«≤_refl» _) («∇_slide_conv» S)
    _ = meet R (T ≫ conv S) ≫ S := hR.symm

/-- **Every cartesian bicategory of relations is an allegory.**  `recip := conv`, `inter :=
    meet`; all ten `Allegory` fields are theorems of `diag.CB`/`diag.CB_Derived`.

    A `def`, NOT a global instance, so that it cannot form a diamond with the hand-built
    `Allegory RelSet` (`AOP/A6_1_RelSet.lean`) — the same precedent as
    `Freyd.Alg.semiSimpleAllegory_of_tabular` (`Freyd/S2_10.lean`).  Phase 4's agreement theorems
    `conv_eq_recip` and `meet_eq_inter` (`diag/RelSetCB.lean`) say the two agree on `Rel(Set)`
    anyway.

    Freyd states `inter_assoc`, `semidistrib` and `modular` in equality form; `meet_assoc`
    is the mirror bracketing, and `«meet_eq_left_of_≤»` converts the two `≤` forms. -/
def allegoryOfCartBicat (𝒞 : Type u) [CartBicat.{v} 𝒞] : Freyd.Alg.Allegory 𝒞 :=
  { (inferInstance : Cat.{v} 𝒞) with
    recip := conv
    inter := meet
    recip_recip := conv_conv
    recip_comp := conv_comp
    recip_inter := conv_inter
    inter_idem := meet_idem
    inter_comm := meet_comm
    inter_assoc := fun R S T => (meet_assoc R S T).symm
    semidistrib := fun R S T => by
      -- `R(S ∩ T) ≤ RS` and `≤ RT`, so intersecting it with either changes nothing.
      have hS : (R ≫ meet S T) ≤ (R ≫ S) :=
        OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («meet_≤_left» S T)
      have hT : (R ≫ meet S T) ≤ (R ≫ T) :=
        OrderedCat.comp_mono (OrderedCat.«≤_refl» R) («meet_≤_right» S T)
      calc R ≫ meet S T
          = meet (R ≫ meet S T) (R ≫ T) := («meet_eq_left_of_≤» hT).symm
        _ = meet (meet (R ≫ S) (R ≫ meet S T)) (R ≫ T) := by
              rw [meet_comm (R ≫ S), «meet_eq_left_of_≤» hS]
    modular := fun R S T => by
      have h := modular_of_frobenius R S T
      exact («meet_eq_left_of_≤» h).symm }

end Freyd.Diag
