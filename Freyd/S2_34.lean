module

public import Freyd.S2_165_Spl
public import Freyd.S2_147_MapCat

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* — §2.341 (representation of pre-tabular /
  semi-simple division allegories).

  BOOK §2.341.  "If A is a pre-tabular division allegory we may therefore represent it in a
  tabular division allegory, namely `Spl(Cor(A))`.  If A is semi-simple we may faithfully
  represent it in `PRel(Rel)`."

  This file ASSEMBLES the headline from the pieces already proven in `Freyd.Spl`/`Freyd.S2_21`:

    • §2.166/§2.167  `SplCorObj.tabular_of_preTabular`  : `SplCorObj 𝒜 = Spl(Cor 𝒜)` is the
      TABULAR reflection of a pre-tabular `𝒜`.
    • §2.34           `instDivisionSpl` / `splDiv`       : pointwise right division descends to
      the splitting completion; here we descend it to the COREFLEXIVE sub-completion
      `SplCorObj 𝒜` (`instDivisionSplCor`), so `Spl(Cor 𝒜)` is a DIVISION allegory.
    • §2.34           `embHom` faithful (`embHom_injective`) and division-preserving
      (`embHom_div`) : the canonical embedding `𝒜 ↪ Spl(Cor 𝒜)`.

  Part 1 (`preTabularDivision_repr`): for a pre-tabular division allegory `𝒜` (bundled as
  `PreTabularDivisionAllegory`, sharing one `Allegory` base to avoid the instance diamond),
  `Spl(Cor 𝒜)` is a `TabularDivisionAllegory` and `corEmb : 𝒜 → Spl(Cor 𝒜)` is a faithful,
  division-preserving `AllegoryFunctor`.

  Part 2 (`semiSimple_faithful_Spl_repr`): for a semi-simple `𝒜`, the FULL splitting
  completion `Spl 𝒜 = SplObj 𝒜` is TABULAR (§2.16(10), `splObj_tabular_of_semiSimple`) and
  `splEmb : 𝒜 → Spl 𝒜` is faithful.  This is the repo's nearest `Spl` analog of the book's
  `PRel(Rel)`; the exact target needs a faithful representation of an arbitrary tabular
  allegory into `Rel(Set)` itself — see the closing note.

  Conventions: diagram-order `R ≫ S`, reciprocation `R°`, order `R ⊑ S`, division `R / S`.
  Mathlib-free.
-/

                       --   SplCorObj.tabular_of_preTabular, splObj_tabular_of_semiSimple


namespace Freyd.Alg

open Cat

/-! ## A pre-tabular division allegory, bundled

  Carrying `[PreTabularAllegory 𝒜]` and `[DivisionAllegory 𝒜]` as *separate* hypotheses
  creates an instance diamond: each `extends Allegory 𝒜`, so the two `Cat.Hom` types on `𝒜`
  differ and `SplCorObj 𝒜` built through each path is a DIFFERENT type.  Following the
  `SemiSimpleDivisionAllegory` precedent (S2_4.lean), we fuse them into one class that shares
  a single `Allegory` base. -/

/-- A **PRE-TABULAR DIVISION ALLEGORY** (§2.341 hypothesis): simultaneously a
    `DivisionAllegory` and a `PreTabularAllegory` over the **same** `Allegory` base. -/
public class PreTabularDivisionAllegory (𝒜 : Type u)
    extends DivisionAllegory 𝒜, PreTabularAllegory 𝒜

/-- A **TABULAR DIVISION ALLEGORY** (§2.341 target): a `DivisionAllegory` that is also
    `TabularAllegory`, over one shared `Allegory` base — Freyd's "tabular division allegory". -/
public class TabularDivisionAllegory (𝒜 : Type u)
    extends DivisionAllegory 𝒜, TabularAllegory 𝒜

/-! ## §2.34 (coreflexive case)  `Spl(Cor 𝒜)` is a distributive / division allegory

  `SplCorObj 𝒜 = { E : SplObj 𝒜 // Coreflexive E.idem.e }` has homs `SplHom E.1 F.1` — exactly
  the `SplObj`-homs of the underlying objects.  Union, zero and division are therefore the same
  pointwise operations `splUnion`/`splZero`/`splDiv` used for `SplObj` (`instDistributiveSpl`,
  `instDivisionSpl`), and every law again reduces to the base `𝒜` law via `SplHom.ext`. -/

/-- Order on `SplCorObj 𝒜` is read off the underlying `𝒜`-morphisms (the coreflexive analogue
    of `splLe_iff`): `Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R`. -/
public theorem splCorLe_iff {𝒜 : Type u} [Allegory 𝒜] {E F : SplCorObj 𝒜} (Φ Ψ : E ⟶ F) :
    Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R := by
  show splInter Φ Ψ = Φ ↔ Φ.R ∩ Ψ.R = Φ.R
  exact ⟨fun h => congrArg SplHom.R h, fun h => SplHom.ext h⟩

/-- **§2.21 (coreflexive)**: if `𝒜` is distributive then so is `Spl(Cor 𝒜)`, with union and
    zero taken pointwise (`splUnion`, `splZero`).  Each law descends via `SplHom.ext`. -/
@[expose] public instance instDistributiveSplCor {𝒜 : Type u} [DistributiveAllegory 𝒜] :
    DistributiveAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    zero := splZero
    union := splUnion
    zero_comp := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ≫ R.R = 𝟘; exact DistributiveAllegory.zero_comp _
    comp_zero := fun R => by
      apply SplHom.ext; show R.R ≫ (𝟘 : _ ⟶ _) = 𝟘; exact DistributiveAllegory.comp_zero _
    union_idem := fun R => by
      apply SplHom.ext; show R.R ∪ R.R = R.R; exact DistributiveAllegory.union_idem _
    union_comm := fun R S => by
      apply SplHom.ext; show R.R ∪ S.R = S.R ∪ R.R; exact DistributiveAllegory.union_comm _ _
    union_assoc := fun R S T => by
      apply SplHom.ext; show R.R ∪ (S.R ∪ T.R) = (R.R ∪ S.R) ∪ T.R
      exact DistributiveAllegory.union_assoc _ _ _
    union_inter_absorb := fun R S => by
      apply SplHom.ext; show R.R ∪ (S.R ∩ R.R) = R.R
      exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun R S => by
      apply SplHom.ext; show (R.R ∪ S.R) ∩ R.R = R.R
      exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ≫ (S.R ∪ T.R) = (R.R ≫ S.R) ∪ (R.R ≫ T.R)
      exact DistributiveAllegory.comp_union_distrib _ _ _
    inter_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ∩ (S.R ∪ T.R) = (R.R ∩ S.R) ∪ (R.R ∩ T.R)
      exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ∪ R.R = R.R; exact DistributiveAllegory.zero_union _ }

/-- **§2.34 (coreflexive)**: if `𝒜` is a DIVISION allegory then so is `Spl(Cor 𝒜)`, with right
    division taken pointwise (`splDiv`).  Both §2.31 laws reduce to the base `div_comp_le` /
    `le_div`, exactly as for the full `SplObj 𝒜` (`instDivisionSpl`). -/
@[expose] public noncomputable instance instDivisionSplCor {𝒜 : Type u} [DivisionAllegory 𝒜] :
    DivisionAllegory (SplCorObj 𝒜) :=
  { instDistributiveSplCor with
    div := fun Φ Ψ => splDiv Φ Ψ
    div_comp_le := fun {E F G} Φ Ψ => by
      rw [splCorLe_iff]
      show (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R ⊑ Φ.R
      calc (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R
          = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ (F.1.idem.e ≫ Ψ.R) := by simp only [Cat.assoc]
        _ = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ Ψ.R := by rw [Ψ.fixed_left]
        _ ⊑ E.1.idem.e ≫ Φ.R := comp_mono_left _ (DivisionAllegory.div_comp_le _ _)
        _ = Φ.R := Φ.fixed_left
    le_div := fun {E F G} T Φ Ψ h => by
      rw [splCorLe_iff] at h ⊢
      show T.R ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e
      have hbase : T.R ⊑ Φ.R / Ψ.R := DivisionAllegory.le_div T.R Φ.R Ψ.R h
      calc T.R = E.1.idem.e ≫ T.R ≫ F.1.idem.e := T.fixed.symm
        _ ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e :=
            comp_mono_left _ (comp_mono_right hbase _) }

/-- **§2.166 + §2.34**: for a pre-tabular division allegory `𝒜`, `Spl(Cor 𝒜)` is a
    TABULAR DIVISION allegory — the §2.341 target.  Tabularity from
    `SplCorObj.tabular_of_preTabular`, division from `instDivisionSplCor`; both rest on the
    same `Allegory (SplCorObj 𝒜)` (`SplCorObj.instAllegorySplCor`). -/
@[expose] public noncomputable instance instTabularDivisionSplCor {𝒜 : Type u} [PreTabularDivisionAllegory 𝒜] :
    TabularDivisionAllegory (SplCorObj 𝒜) :=
  { instDivisionSplCor, SplCorObj.tabular_of_preTabular with }

/-! ## §2.34  The canonical embedding `𝒜 ↪ Spl(Cor 𝒜)` -/

/-- The embedded object `a ↦ (a, 1_a)` lands in the COREFLEXIVE sub-completion: its idempotent
    is `1_a`, which is coreflexive (`1_a ⊑ 1_a`). -/
def corEmbObj {𝒜 : Type u} [Allegory 𝒜] (a : 𝒜) : SplCorObj 𝒜 :=
  ⟨embObj a, le_refl _⟩

/-- **§2.34**: the canonical embedding `𝒜 → Spl(Cor 𝒜)`, `a ↦ (a, 1_a)`, `R ↦ R`.  It is an
    allegory functor (preserves `id`, `≫`, `°`, `∩`) — every law is the corresponding `embHom`
    fact (`embHom_id`/`embHom_comp`/`embHom_recip`/`embHom_inter`), since `Spl(Cor 𝒜)` inherits
    `splComp`/`splRecip`/`splInter` from `SplObj 𝒜`. -/
def corEmb (𝒜 : Type u) [Allegory 𝒜] : AllegoryFunctor 𝒜 (SplCorObj 𝒜) where
  obj := corEmbObj
  map {a b} R := embHom R
  map_id a := by apply SplHom.ext; rfl
  map_comp R S := by apply SplHom.ext; rfl
  map_recip R := by apply SplHom.ext; rfl
  map_inter R S := by apply SplHom.ext; rfl

/-- **§2.167**: the embedding `𝒜 ↪ Spl(Cor 𝒜)` is FAITHFUL (`embHom_injective`). -/
theorem corEmb_faithful (𝒜 : Type u) [Allegory 𝒜] : (corEmb 𝒜).Faithful :=
  fun _ _ h => embHom_injective h

/-- **§2.34**: the embedding `𝒜 ↪ Spl(Cor 𝒜)` PRESERVES DIVISION.  On embedded objects the
    idempotent is `1`, so `splDiv`'s `E.e ≫ (R/S) ≫ F.e` collapses to `R/S` (`embHom_div`). -/
theorem corEmb_div {𝒜 : Type u} [DivisionAllegory 𝒜] {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) :
    (corEmb 𝒜).map (R / S) = (corEmb 𝒜).map R / (corEmb 𝒜).map S :=
  embHom_div R S

/-! ## §2.341 (part 1) — the headline for pre-tabular division allegories -/

/-- **§2.341 (pre-tabular case)**: a pre-tabular division allegory `𝒜` is represented in a
    TABULAR DIVISION allegory, namely `Spl(Cor 𝒜)`, by a FAITHFUL, DIVISION-PRESERVING
    allegory functor.

    Bundled: the target `SplCorObj 𝒜` carries a `TabularDivisionAllegory` instance
    (`instTabularDivisionSplCor`), and `corEmb` is the faithful (`corEmb_faithful`),
    division-preserving (`corEmb_div`) `AllegoryFunctor`. -/
theorem preTabularDivision_repr (𝒜 : Type u) [PreTabularDivisionAllegory 𝒜] :
    ∃ F : AllegoryFunctor 𝒜 (SplCorObj 𝒜),
      F.Faithful ∧
      ∀ {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c), F.map (R / S) = F.map R / F.map S :=
  ⟨corEmb 𝒜, corEmb_faithful 𝒜, fun R S => corEmb_div R S⟩

/-! ## §2.341 (part 2) — the semi-simple case

  For a semi-simple `𝒜`, the FULL splitting completion `Spl 𝒜 = SplObj 𝒜` is tabular
  (Freyd §2.16(10), `splObj_tabular_of_semiSimple`), and `𝒜 ↪ Spl 𝒜` is faithful. -/

/-- The canonical embedding `𝒜 → Spl 𝒜 = SplObj 𝒜`, `a ↦ (a, 1_a)`, `R ↦ R` (an allegory
    functor). -/
def splEmb (𝒜 : Type u) [Allegory 𝒜] : AllegoryFunctor 𝒜 (SplObj 𝒜) where
  obj := embObj
  map {a b} R := embHom R
  map_id a := by apply SplHom.ext; rfl
  map_comp R S := by apply SplHom.ext; rfl
  map_recip R := by apply SplHom.ext; rfl
  map_inter R S := by apply SplHom.ext; rfl

/-- `splEmb` is FAITHFUL (`embHom_injective`). -/
theorem splEmb_faithful (𝒜 : Type u) [Allegory 𝒜] : (splEmb 𝒜).Faithful :=
  fun _ _ h => embHom_injective h

/-- The target `Spl 𝒜 = SplObj 𝒜` of the semi-simple representation is a TABULAR allegory
    (Freyd §2.16(10)).  A `def` (not a `theorem`) since `TabularAllegory` is `Type`-valued. -/
def semiSimple_Spl_tabular (𝒜 : Type u) [SemiSimpleAllegory 𝒜] :
    TabularAllegory (SplObj 𝒜) :=
  splObj_tabular_of_semiSimple

/-- **§2.341 (semi-simple case)**: a semi-simple allegory `𝒜` is faithfully represented in the
    TABULAR allegory `Spl 𝒜 = SplObj 𝒜` (the repo's nearest `Spl` analog of `PRel(Rel)`).
    `Spl 𝒜` is tabular by §2.16(10) (`semiSimple_Spl_tabular` / `splObj_tabular_of_semiSimple`)
    and the embedding `splEmb` is faithful (`splEmb_faithful`).

    NOTE on the exact `PRel(Rel)` target: the book lands in `PRel(Rel) = Spl(Rel(Set))`.
    Reaching it needs a faithful representation of the (arbitrary) tabular allegory `Spl 𝒜`
    into `Rel(Set)`; the repo currently provides such a representation only for a tabular
    UNITARY DISTRIBUTIVE allegory and only into a POWER of `Rel(Set)`
    (`tabular_repr_in_power_of_sets_distributive`, S2_218_Tabular.lean).  Composing that with
    `splEmb` would require `Spl 𝒜` unitary + distributive (not implied by `𝒜` semi-simple),
    so the exact `PRel(Rel)` landing is left open. -/
theorem semiSimple_faithful_Spl_repr (𝒜 : Type u) [SemiSimpleAllegory 𝒜] :
    ∃ F : AllegoryFunctor 𝒜 (SplObj 𝒜), F.Faithful :=
  ⟨splEmb 𝒜, splEmb_faithful 𝒜⟩

end Freyd.Alg
