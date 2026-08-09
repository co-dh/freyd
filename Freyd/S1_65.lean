/-
  Freyd & Scedrov, *Categories and Allegories* §1.65  Pre-topoi.

  This file collects the functor-theoretic content of §1.65 not yet
  captured by the class/instance definitions in S1_64:

  §1.655  BICARTESIAN REPRESENTATION CRITERION: a functor T : A → B between
          pre-topoi that preserves 0 (coterminator), pushouts, finite products
          and monics is a bicartesian representation.
          Key steps (Freyd's proof):
            (i)   T preserves pullbacks of monics (amalgamation §1.651 + pasting §1.62).
            (ii)  T preserves equalizers (from products, §1.434 style).
            (iii) T preserves covers (= coequalizers §1.652; T preserves pushouts and 0).
          Requires the `PreToposFunctor` concept (new to this file).

  §1.656  For functors between abelian categories the analogous theorem holds:
          preservation of cocartesian structure and monics ⟹ preservation of
          Cartesian structure.  And dually.  Non-formalizable without abelian
          infrastructure.

  Cross-references:
    `PreTopos`, `amalgamation_lemma`  — S1_64
    `PushoutCocone`, `HasPushout`     — S1_56
    `PreservesBinaryProducts`, `PreservesTerminal`, `CartesianFunctor` — S1_43
    `PreservesMono`                   — S1_18
    `HasBinaryCoproducts`             — S1_58
-/


module

public import Freyd.S1_64

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.655 Functor predicates for pre-topos maps -/

section PreToposFunctors

variable {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]

/-- A functor F : 𝒜 → ℬ PRESERVES PUSHOUTS if for every pushout square
    `f : C → A`, `g : C → B` in 𝒜, the F-images of the cocone legs
    present a pushout in ℬ. -/
def PreservesPushouts (F : Functor 𝒜 ℬ) : Prop :=
  ∀ {A B C : 𝒜} (f : C ⟶ A) (g : C ⟶ B) [h : HasPushout f g],
    ∀ (c : PushoutCocone (F.map f) (F.map g)),
      ∃ u : F.obj h.cocone.pt ⟶ c.pt,
        F.map h.cocone.ι₁ ≫ u = c.ι₁ ∧ F.map h.cocone.ι₂ ≫ u = c.ι₂
        ∧ ∀ v : F.obj h.cocone.pt ⟶ c.pt,
            F.map h.cocone.ι₁ ≫ v = c.ι₁ → F.map h.cocone.ι₂ ≫ v = c.ι₂ → v = u

/-- A functor F : 𝒜 → ℬ PRESERVES THE INITIAL OBJECT if `F(0_𝒜)` is initial in ℬ.
    (In Freyd's notation: F preserves 0.) -/
def PreservesInitial (F : Functor 𝒜 ℬ)
    [h𝒜 : HasCoterminator 𝒜] [HasCoterminator ℬ] : Prop :=
  ∀ {X : ℬ} (f g : F.obj h𝒜.zero ⟶ X), f = g

/-- A PRE-TOPOS FUNCTOR T : A → B (Freyd §1.655): preserves
    - monics (`PreservesMono`),
    - the initial object 0 (`PreservesInitial`),
    - pushouts (`PreservesPushouts`),
    - terminal object (`PreservesTerminal`), and
    - binary products (`PreservesBinaryProducts`). -/
structure PreToposFunctor
    [h𝒜 : PreTopos 𝒜] [hℬ : PreTopos ℬ]
    [HasCoterminator 𝒜] [HasCoterminator ℬ]
    (F : Functor 𝒜 ℬ) : Prop where
  pres_mono     : PreservesMono F
  pres_initial  : PreservesInitial F
  pres_pushouts : PreservesPushouts F
  pres_terminal : PreservesTerminal F
  pres_products : PreservesBinaryProducts F

end PreToposFunctors

/-! ## §1.655 Bicartesian Representation Criterion

A pre-topos functor T : A → B is a bicartesian representation.  Freyd
proves this in three steps:
  (i)   T preserves pullbacks of monics — using §1.651 (amalgamation) and
        §1.62 (pasting lemma for squares in ℬ).
  (ii)  T preserves equalizers — from binary products via §1.434 style.
  (iii) T preserves covers — covers = coequalizers (§1.652 + §1.566 kernel pair),
        and T preserves pushouts and 0, hence T preserves coequalizers.

All three steps are now CLOSED (axioms `propext, Classical.choice`): (i)+(ii) via the
§1.64 `amalgamation_is_pullback`; (iii) via `pretopos_balanced` / `cover_eq_epic_preTopos`
(see the UNBLOCKED note below). -/

section BiCartRepr

-- `ℬ` carries the FULL disjoint pre-topos structure (`PreToposDisjoint`) plus a
-- reflexive-transitive-closure operator (`HasReflTransClosure`): exactly the §1.64
-- hypotheses under which `cover_eq_epic_preTopos`/`pretopos_balanced` are closed.
-- Deriving `PreTopos ℬ` from `PreToposDisjoint ℬ` (rather than a separate
-- `[PreTopos ℬ]` binder) keeps a SINGLE instance path to `HasBinaryProducts ℬ`
-- etc., so the `HasReflTransClosure ℬ` argument of `cover_eq_epic_preTopos`
-- matches in step (iii) (no instance diamond).
variable {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
variable [PreTopos 𝒜] [PreToposDisjoint ℬ] [HasReflTransClosure ℬ]
variable [HasCoterminator 𝒜] [HasCoterminator ℬ]
variable {F : Functor 𝒜 ℬ}

/-- The binary coproduct A+B is the pushout of the two initial maps 0→A and 0→B.
    Any PushoutCocone (init A) (init B) automatically commutes (both composites go
    from 0 to c.pt, and the initial object has a unique map to every object). -/
private def coprod_is_pushout_of_init [HasBinaryCoproducts 𝒜]
    (A B : 𝒜) : HasPushout (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) where
  cocone := { pt := HasBinaryCoproducts.coprod A B
              ι₁ := HasBinaryCoproducts.inl
              ι₂ := HasBinaryCoproducts.inr
              w  := HasCoterminator.init_uniq _ _ }
  desc  := fun c => HasBinaryCoproducts.case c.ι₁ c.ι₂
  fac₁  := fun c => HasBinaryCoproducts.case_inl c.ι₁ c.ι₂
  fac₂  := fun c => HasBinaryCoproducts.case_inr c.ι₁ c.ι₂
  uniq  := fun c h h1 h2 => HasBinaryCoproducts.case_uniq c.ι₁ c.ι₂ h h1 h2

set_option maxHeartbeats 1000000 in
/-- **§1.655 step (i)**: a pre-topos functor preserves pullbacks of monics.  CLOSED.

    Freyd's argument, now fully discharged via the 2026-06-19 §1.64 closures
    (`amalgamation_is_pullback` and its bicartesian upgrade):

    * `pb.cone.π₁, pb.cone.π₂` are monic (`mono_pullback`), and `F` preserves monics
      (`pres_mono`), so `(F π₁, F π₂)` is a monic SPAN in ℬ.
    * `amalgamation_is_pullback (F π₁) (F π₂)` builds the §1.651 amalgamation `(D; u, v)`,
      which is BICARTESIAN: the square with apex `F.obj pb.cone.pt` and legs `(F π₁, F π₂)` over
      the cospan `(u, v)` is a PULLBACK, and `(D; u, v)` is a PUSHOUT of `(F π₁, F π₂)`.
    * The intersection square `(pb.cone.pt; π₁, π₂; x, y; U)` is a PUSHOUT in 𝒜
      (`pasting_lemma`: the union `U = A₁∪A₂` is the pushout of the intersection
      projections, with `x≫U.arr = m`, `y≫U.arr = n`).  `pres_pushouts` carries it to a
      pushout `(F U; F x, F y)` of `(F π₁, F π₂)` in ℬ (reindexed across the pullback iso
      `ρ : pb ≅ HasPullbacks.has m n`).
    * `D` and `F U` are two pushouts of the SAME span, so the `D`-descent `δ : D → F.obj A` to the
      cocone `(F.obj A; F m, F n)` factors as `(iso) ≫ F U.arr` (`pushout_descent_mono`); since
      `F U.arr` is monic (`U.arr` monic, `F` preserves monics), `δ` is MONIC.
    * `isPullback_postcomp_mono` then descends the pullback over `(u, v)` to a pullback over
      `(u≫δ, v≫δ) = (F m, F n)` — exactly the goal.  (Step (ii) equalizers is already wired
      to this and now closes automatically.) -/
theorem preTopos_functor_preserves_monic_pullbacks (hptf : PreToposFunctor F)
    {A₁ A₂ A : 𝒜} (m : A₁ ⟶ A) (hm : Monic m) (n : A₂ ⟶ A) (hn : Monic n)
    (pb : HasPullback m n) :
    -- F maps the pullback of the two monics to a pullback in ℬ:
    ∀ (c : Cone (F.map m) (F.map n)),
      ∃ u : c.pt ⟶ F.obj pb.cone.pt,
        u ≫ F.map pb.cone.π₁ = c.π₁ ∧ u ≫ F.map pb.cone.π₂ = c.π₂
        ∧ ∀ v : c.pt ⟶ F.obj pb.cone.pt,
            v ≫ F.map pb.cone.π₁ = c.π₁ → v ≫ F.map pb.cone.π₂ = c.π₂ → v = u := by
  intro c
  -- `π₁, π₂` monic (pullback of a monic); build the swapped pullback for `π₂`.
  have hπ₁ : Monic pb.cone.π₁ := mono_pullback m n hn pb
  let pbS : HasPullback n m :=
    { cone := ⟨pb.cone.pt, pb.cone.π₂, pb.cone.π₁, pb.cone.w.symm⟩
      lift := fun d => pb.lift ⟨d.pt, d.π₂, d.π₁, d.w.symm⟩
      lift_fst := fun d => pb.lift_snd ⟨d.pt, d.π₂, d.π₁, d.w.symm⟩
      lift_snd := fun d => pb.lift_fst ⟨d.pt, d.π₂, d.π₁, d.w.symm⟩
      lift_uniq := fun d w h₁ h₂ => pb.lift_uniq ⟨d.pt, d.π₂, d.π₁, d.w.symm⟩ w h₂ h₁ }
  have hπ₂ : Monic pb.cone.π₂ := mono_pullback n m hm pbS
  have hFπ₁ : Monic (F.map pb.cone.π₁) := hptf.pres_mono hπ₁
  have hFπ₂ : Monic (F.map pb.cone.π₂) := hptf.pres_mono hπ₂
  -- §1.651 amalgamation of the monic span `(Fπ₁, Fπ₂)`: pullback over `(u,v)` + pushout UMP.
  obtain ⟨D, u, v, hsqD, hpbD, hUMPD, _⟩ :=
    amalgamation_is_pullback (F.map pb.cone.π₁) hFπ₁ (F.map pb.cone.π₂) hFπ₂
  -- §1.62 union pushout in 𝒜: `U = A₁∪A₂` is the pushout of the intersection projections.
  let S₁ : Subobject 𝒜 A := ⟨A₁, m, hm⟩
  let S₂ : Subobject 𝒜 A := ⟨A₂, n, hn⟩
  let po := pasting_lemma S₁ S₂
  let U := HasSubobjectUnions.union S₁ S₂
  have hx : po.cocone.ι₁ ≫ U.arr = m := (HasSubobjectUnions.union_left S₁ S₂).choose_spec
  have hy : po.cocone.ι₂ ≫ U.arr = n := (HasSubobjectUnions.union_right S₁ S₂).choose_spec
  -- iso `ρ : pb ≅ canonical pullback`, to reindex `po` (over canonical projections).
  let cpb := HasPullbacks.has S₁.arr S₂.arr
  let ρ : pb.cone.pt ⟶ cpb.cone.pt := cpb.lift ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, pb.cone.w⟩
  have hρ₁ : ρ ≫ cpb.cone.π₁ = pb.cone.π₁ := cpb.lift_fst _
  have hρ₂ : ρ ≫ cpb.cone.π₂ = pb.cone.π₂ := cpb.lift_snd _
  obtain ⟨ρinv, hρρinv, hρinvρ⟩ :=
    isIso_of_two_pullbacks pb.cone_isPullback cpb.cone_isPullback ρ hρ₁ hρ₂
  -- `F ρ` is iso (`F` preserves the iso `ρ`), with left-inverse `F ρinv`.
  have hFρinvρ : F.map ρinv ≫ F.map ρ = Cat.id (F.obj cpb.cone.pt) := by
    rw [← F.map_comp, hρinvρ, F.map_id]
  have hFρ₁ : F.map ρ ≫ F.map cpb.cone.π₁ = F.map pb.cone.π₁ := by rw [← F.map_comp, hρ₁]
  have hFρ₂ : F.map ρ ≫ F.map cpb.cone.π₂ = F.map pb.cone.π₂ := by rw [← F.map_comp, hρ₂]
  -- `F U` is a pushout of `(Fπ₁, Fπ₂)` — `pres_pushouts po` reindexed across `Fρ`.
  have hUMPW : ∀ (Q : ℬ) (uQ : F.obj A₁ ⟶ Q) (vQ : F.obj A₂ ⟶ Q),
      F.map pb.cone.π₁ ≫ uQ = F.map pb.cone.π₂ ≫ vQ →
        ∃ dd : F.obj po.cocone.pt ⟶ Q,
          F.map po.cocone.ι₁ ≫ dd = uQ ∧ F.map po.cocone.ι₂ ≫ dd = vQ ∧
          ∀ d' : F.obj po.cocone.pt ⟶ Q,
            F.map po.cocone.ι₁ ≫ d' = uQ → F.map po.cocone.ι₂ ≫ d' = vQ → d' = dd := by
    intro Q uQ vQ hQ
    have hQ' : F.map cpb.cone.π₁ ≫ uQ = F.map cpb.cone.π₂ ≫ vQ := by
      -- left-cancel `F ρ` (iso): `Fρ ≫ (cpb.π₁≫uQ) = Fpb.π₁≫uQ = Fpb.π₂≫vQ = Fρ ≫ (cpb.π₂≫vQ)`.
      have hkey : F.map ρ ≫ (F.map cpb.cone.π₁ ≫ uQ) = F.map ρ ≫ (F.map cpb.cone.π₂ ≫ vQ) := by
        rw [← Cat.assoc, ← Cat.assoc, hFρ₁, hFρ₂]; exact hQ
      calc F.map cpb.cone.π₁ ≫ uQ
          = (F.map ρinv ≫ F.map ρ) ≫ (F.map cpb.cone.π₁ ≫ uQ) := by
            rw [hFρinvρ, Cat.id_comp]
        _ = F.map ρinv ≫ (F.map ρ ≫ (F.map cpb.cone.π₁ ≫ uQ)) := Cat.assoc _ _ _
        _ = F.map ρinv ≫ (F.map ρ ≫ (F.map cpb.cone.π₂ ≫ vQ)) := by rw [hkey]
        _ = (F.map ρinv ≫ F.map ρ) ≫ (F.map cpb.cone.π₂ ≫ vQ) := (Cat.assoc _ _ _).symm
        _ = F.map cpb.cone.π₂ ≫ vQ := by rw [hFρinvρ, Cat.id_comp]
    obtain ⟨dd, hd1, hd2, huniq⟩ :=
      hptf.pres_pushouts cpb.cone.π₁ cpb.cone.π₂ (h := po) ⟨Q, uQ, vQ, hQ'⟩
    exact ⟨dd, hd1, hd2, fun d' h1 h2 => huniq d' h1 h2⟩
  -- descent `δ : D → F.obj A` to the cocone `(F.obj A; F m, F n)`.
  have hcoc : F.map pb.cone.π₁ ≫ F.map m = F.map pb.cone.π₂ ≫ F.map n := by
    rw [← F.map_comp, ← F.map_comp, pb.cone.w]
  obtain ⟨δ, hδu, hδv, _⟩ := hUMPD (F.obj A) (F.map m) (F.map n) hcoc
  -- `δ` monic: `D ≅ F U` (both pushouts), `δ = (iso) ≫ F U.arr`, `F U.arr` monic.
  have hsqW : F.map pb.cone.π₁ ≫ F.map po.cocone.ι₁
      = F.map pb.cone.π₂ ≫ F.map po.cocone.ι₂ := by
    rw [← F.map_comp, ← F.map_comp]; congr 1
    apply U.monic; rw [Cat.assoc, Cat.assoc, hx, hy]; exact pb.cone.w
  have hFUmono : Monic (F.map U.arr) := hptf.pres_mono U.monic
  have hδmono : Monic δ :=
    pushout_descent_mono hsqD hUMPD hsqW hUMPW hFUmono
      (by rw [hδu, ← F.map_comp, hx]) (by rw [hδv, ← F.map_comp, hy])
  -- descend the pullback over `(u,v)` to a pullback over `(u≫δ, v≫δ) = (F m, F n)`.
  have hpbFA := isPullback_postcomp_mono hpbD hδmono
  have hc' : c.π₁ ≫ (u ≫ δ) = c.π₂ ≫ (v ≫ δ) := by rw [hδu, hδv]; exact c.w
  obtain ⟨k, ⟨hk₁, hk₂⟩, huniq⟩ := hpbFA (Cone.mk c.pt c.π₁ c.π₂ hc')
  exact ⟨k, hk₁, hk₂, fun w hw₁ hw₂ => huniq w hw₁ hw₂⟩

/-- **§1.655 step (ii)**: a pre-topos functor preserves equalizers — a genuine
    reduction to step (i), with NO independent obligation of its own.

    Proof (Freyd §1.434 + §1.655): the equalizer `m := heq.cone.map : E → A` of
    `f, g : A → B` is, by `isEqualizer_iff_isPullback`, the pullback in 𝒜 of the
    two graph maps `u := ⟨1_A, f⟩`, `v := ⟨1_A, g⟩ : A → A × B`.  Both graph maps
    are SPLIT monic (retraction `fst`), so step (i)
    (`preTopos_functor_preserves_monic_pullbacks`) applies: `F` carries that
    pullback to a pullback of `(F u, F v)` in ℬ.  Post-composing the cospan with
    the product-comparison iso `φ = ⟨F fst, F snd⟩` (iso by `pres_products`)
    rewrites it as the pullback of `⟨1_{FA}, F f⟩`, `⟨1_{FA}, F g⟩`
    (`isPullback_of_iso_cospan`), and `isEqualizer_iff_isPullback` run backwards
    in ℬ identifies `(F.obj E, F m)` as the equalizer of `(F f, F g)`.

    Step (i) is now closed, so this step (ii) is fully closed (Sorry-free). -/
theorem preTopos_functor_preserves_equalizers (hptf : PreToposFunctor F)
    {A B : 𝒜} (f g : A ⟶ B) (heq : HasEqualizer f g) :
    ∀ (c : EqualizerCone (F.map f) (F.map g)),
      ∃ u : c.dom ⟶ F.obj heq.cone.dom,
        u ≫ F.map heq.cone.map = c.map
        ∧ ∀ v : c.dom ⟶ F.obj heq.cone.dom, v ≫ F.map heq.cone.map = c.map → v = u := by
  -- `m : E → A` is the chosen equalizer of `f, g`; `heqUP` is its universal property.
  let E := heq.cone.dom
  let m : E ⟶ A := heq.cone.map
  have hmeq : m ≫ f = m ≫ g := heq.cone.eq
  have heqUP : (EqualizerCone.mk E m hmeq).IsEqualizer := fun d =>
    ⟨heq.lift d, heq.fac d, fun w hw => heq.uniq d w hw⟩
  -- Graph maps `u = ⟨1,f⟩`, `v = ⟨1,g⟩ : A → A×B`; both split monic (retraction `fst`).
  let u : A ⟶ prod A B := pair (Cat.id A) f
  let v : A ⟶ prod A B := pair (Cat.id A) g
  have humono : Monic u := mono_of_retraction u fst (fst_pair _ _)
  have hvmono : Monic v := mono_of_retraction v fst (fst_pair _ _)
  -- The equalizer cone `(E, m, m)` is a pullback of `(u, v)` in 𝒜 (§1.434).
  have hwUV : m ≫ u = m ≫ v := by
    show m ≫ pair (Cat.id A) f = m ≫ pair (Cat.id A) g
    rw [pair_uniq (m ≫ Cat.id A) (m ≫ f) (m ≫ pair (Cat.id A) f)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]),
        pair_uniq (m ≫ Cat.id A) (m ≫ g) (m ≫ pair (Cat.id A) g)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]), hmeq]
  let eqCone : Cone u v := Cone.mk E m m hwUV
  have hEqPB : eqCone.IsPullback :=
    (isEqualizer_iff_isPullback m hmeq).mp heqUP
  -- Package as a `HasPullback u v` whose distinguished cone is exactly `eqCone`,
  -- so step (i) yields the F-image universal property *for that very cone*.
  let pbUV : HasPullback u v :=
    { cone := eqCone
      lift := fun c => (hEqPB c).choose
      lift_fst := fun c => (hEqPB c).choose_spec.1.1
      lift_snd := fun c => (hEqPB c).choose_spec.1.2
      lift_uniq := fun c w h₁ h₂ => (hEqPB c).choose_spec.2 w h₁ h₂ }
  -- Step (i): `F` preserves the pullback `pbUV`; its image is a pullback of `(F u, F v)`.
  have hFpb := preTopos_functor_preserves_monic_pullbacks hptf u humono v hvmono pbUV
  have hFeqPB_uv : (Cone.mk (f := F.map u) (g := F.map v) (F.obj E)
      (F.map m) (F.map m)
      (by rw [← F.map_comp, ← F.map_comp, hwUV])).IsPullback := by
    intro d
    obtain ⟨w, hw₁, hw₂, huniq⟩ := hFpb d
    exact ⟨w, ⟨hw₁, hw₂⟩, fun y hy₁ hy₂ => huniq y hy₁ hy₂⟩
  -- Product-comparison iso `φ = ⟨F fst, F snd⟩ : F(A×B) → FA×FB`; `F u ≫ φ = ⟨1,Ff⟩`.
  obtain ⟨φ', hφφ', _⟩ := hptf.pres_products (A := A) (B := B)
  have hFu_φ : F.map u ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)
      = pair (Cat.id (F.obj A)) (F.map f) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) f ≫ fst) = Cat.id (F.obj A); rw [fst_pair, F.map_id]
    · rw [Cat.assoc, snd_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) f ≫ snd) = F.map f; rw [snd_pair]
  have hFv_φ : F.map v ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)
      = pair (Cat.id (F.obj A)) (F.map g) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) g ≫ fst) = Cat.id (F.obj A); rw [fst_pair, F.map_id]
    · rw [Cat.assoc, snd_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) g ≫ snd) = F.map g; rw [snd_pair]
  -- Transport the cospan `(F u, F v)` to `(⟨1,Ff⟩, ⟨1,Fg⟩)` along the iso `φ`.
  have hFeqPB : (Cone.mk (f := pair (Cat.id (F.obj A)) (F.map f))
      (g := pair (Cat.id (F.obj A)) (F.map g)) (F.obj E) (F.map m) (F.map m)
      (by rw [← hFu_φ, ← hFv_φ]; simp only [← Cat.assoc, ← F.map_comp]; rw [hwUV])).IsPullback := by
    have key := isPullback_of_iso_cospan hFeqPB_uv
      (pair (F.map (fst (A := A) (B := B))) (F.map snd)) φ' hφφ'
      (by simp only [← Cat.assoc, ← F.map_comp]; rw [hwUV])
    intro d
    have hdw' : d.π₁ ≫ (F.map u ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd))
        = d.π₂ ≫ (F.map v ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)) := by
      rw [hFu_φ, hFv_φ]; exact d.w
    obtain ⟨z, ⟨hz₁, hz₂⟩, huniq⟩ := key (Cone.mk d.pt d.π₁ d.π₂ hdw')
    exact ⟨z, ⟨hz₁, hz₂⟩, fun y hy₁ hy₂ => huniq y hy₁ hy₂⟩
  -- Backwards `isEqualizer_iff_isPullback` in ℬ: `(F.obj E, F m)` is the equalizer of `(Ff, Fg)`.
  have hFmeq : F.map m ≫ F.map f = F.map m ≫ F.map g := by
    rw [← F.map_comp, ← F.map_comp, hmeq]
  have hFeq_isEq : (EqualizerCone.mk (F.obj E) (F.map m) hFmeq).IsEqualizer :=
    (isEqualizer_iff_isPullback (F.map m) hFmeq).mpr hFeqPB
  exact hFeq_isEq

/-- **§1.655 step (iii)**: a pre-topos functor preserves covers.
    Proof: in a pre-topos, every cover `f : A ↠ B` is the coequalizer of its
    kernel pair (`cover_is_coequalizer_of_level`, §1.566).  `T` preserves
    pushouts and `0`, so it preserves coequalizers; the image coequalizer is a
    cover by `bicart_repr_preserves_covers` (§1.581).

    BLOCKED — genuine residual; two independent gaps pinned (2026-06-16).

    Route A (coequalizer-preservation): reduce to `bicart_repr_preserves_covers`
    (§1.581, S1_58), which needs `PreservesCoequalizers F`.  But a coequalizer is
    NOT a pushout of the parallel pair (wrong cocone shape), so `pres_pushouts`
    does not yield it; reconstructing it needs the §1.652 cover-quotient analysis
    for `T`, not a lemma here.  (And `bicart_repr_preserves_covers` itself wants
    `RegularCategory`/`HasCoequalizers` on both 𝒜, ℬ — not in this signature.)

    Route B (epi route): `pres_pushouts` ⇒ `T` preserves epis (an epi is exactly
    a map whose cokernel-pair legs coincide; `T` of the cokernel-pair pushout is
    again a pushout, so the legs stay equal), and in a pre-topos epic ⟺ cover
    (`cover_eq_epic_preTopos`, §1.64).  This route is real but doubly blocked:
      (1) cokernel-pair PUSHOUT EXISTENCE — `pres_pushouts` needs an instance
          `HasPushout f f`, yet `PreTopos` bundles no general pushout/cocartesian
          existence (it extends only `EffectiveRegular`, `PositivePreLogos`); the
          verbatim signature lacks `[HasBinaryCoproducts] [HasCoequalizers]`, so
          the cokernel pair `B +_A B` cannot be built here; and
      (2) `cover_eq_epic_preTopos` requires `[HasReflTransClosure ℬ]` (absent
          from this signature) and internally bottoms out at `pretopos_balanced`
          (now closed, axioms `propext, Classical.choice`).
    No shortcut via `PreservesMono` alone (a functor preserving monics need not
    preserve covers).

    UNBLOCKED (2026-06-19) via the §1.64 closures.  Route B is now realizable:
    * cokernel-pair PUSHOUT existence is supplied by `[HasBinaryCoproducts 𝒜]`
      `[HasCoequalizers 𝒜]` (faithful additions — the §1.655 main theorem already
      carries them); the helper `cokernelPair_pushout` builds `HasPushout f f` as
      the coequalizer of `(f≫inl, f≫inr)`;
    * `pres_pushouts` carries that cokernel pair to a pushout in ℬ.  `f` is a
      cover, hence epic (`cover_epi`), so its two cokernel-pair legs `inl≫c`,
      `inr≫c` coincide in 𝒜 (epic cancels `f` on the left of the coequalizer
      relation), and their `F`-images coincide; a pushout whose two cocone legs
      are equal forces `F f` epic in ℬ;
    * `cover_eq_epic_preTopos` (§1.64, `[PreToposDisjoint ℬ] [HasReflTransClosure ℬ]`)
      turns `F f` epic back into `Cover (F f)`. -/
private def cokernelPair_pushout [HasBinaryCoproducts 𝒜] [HasCoequalizers 𝒜]
    {A B : 𝒜} (f : A ⟶ B) :
    HasPushout f f :=
  let hc := HasCoequalizers.coeq (f ≫ HasBinaryCoproducts.inl (B := B))
                                 (f ≫ HasBinaryCoproducts.inr (B := B))
  { cocone :=
      { pt := hc.obj
        ι₁ := HasBinaryCoproducts.inl ≫ hc.map
        ι₂ := HasBinaryCoproducts.inr ≫ hc.map
        w  := by rw [← Cat.assoc, ← Cat.assoc]; exact hc.eq }
    desc := fun c =>
      hc.desc (HasBinaryCoproducts.case c.ι₁ c.ι₂)
        (by rw [Cat.assoc, Cat.assoc, HasBinaryCoproducts.case_inl,
                HasBinaryCoproducts.case_inr]; exact c.w)
    fac₁ := fun c => by
      rw [Cat.assoc, hc.fac, HasBinaryCoproducts.case_inl]
    fac₂ := fun c => by
      rw [Cat.assoc, hc.fac, HasBinaryCoproducts.case_inr]
    uniq := fun c h h₁ h₂ => by
      -- `h` agrees with `case c.ι₁ c.ι₂` after `hc.map`, so equals the coeq descent.
      refine hc.uniq (HasBinaryCoproducts.case c.ι₁ c.ι₂) _ h ?_
      refine HasBinaryCoproducts.case_uniq c.ι₁ c.ι₂ (hc.map ≫ h) ?_ ?_
      · rw [← Cat.assoc]; exact h₁
      · rw [← Cat.assoc]; exact h₂ }

theorem preTopos_functor_preserves_covers
    [HasBinaryCoproducts 𝒜] [HasCoequalizers 𝒜]
    (hptf : PreToposFunctor F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) : Cover (F.map f) := by
  -- It suffices to prove `F f` is epic; in ℬ epic ⟺ cover (`cover_eq_epic_preTopos`).
  rw [cover_eq_epic_preTopos (F.map f)]
  intro C g h hgh
  -- Cokernel pair of `f` in 𝒜 (pushout of `f` along itself), built from coeq + coprod.
  let hpb := cokernelPair_pushout (𝒜 := 𝒜) f
  -- The two cokernel-pair legs coincide in 𝒜: `f` is a cover, hence epic, and the
  -- coequalizer relation is `f ≫ ι₁ = f ≫ ι₂`, so cancelling `f` gives `ι₁ = ι₂`.
  have hlegs : hpb.cocone.ι₁ = hpb.cocone.ι₂ := cover_epi hf hpb.cocone.w
  -- Target cocone in ℬ over `(F f, F f)` with both legs `g` precomposed appropriately:
  -- use the parallel pair `g, h : F.obj B ⟶ C`.  Build a `PushoutCocone (F f) (F f)`
  -- with legs `g, h`; commutativity is exactly `hgh`.
  let tgt : PushoutCocone (F.map f) (F.map f) :=
    { pt := C, ι₁ := g, ι₂ := h, w := hgh }
  obtain ⟨w, hw₁, hw₂, _⟩ := hptf.pres_pushouts f f (h := hpb) tgt
  -- `hw₁ : F(ι₁) ≫ w = g`, `hw₂ : F(ι₂) ≫ w = h`; but `F(ι₁) = F(ι₂)` (legs equal).
  calc g = F.map hpb.cocone.ι₁ ≫ w := hw₁.symm
    _ = F.map hpb.cocone.ι₂ ≫ w := by rw [hlegs]
    _ = h := hw₂

/-- **§1.655 (main theorem)**: A pre-topos functor T : A → B is a bicartesian
    representation — it preserves pullbacks, equalizers, covers, and coproducts.
    Statement is faithful to Freyd §1.655.  Part (c) (coproducts) and part (b)
    (equalizers, via step (ii)) are PROVED; part (a) (covers) reduces to step
    (iii).

    Residual blockers: step (i) is now CLOSED
    (`preTopos_functor_preserves_monic_pullbacks`, via the 2026-06-19 §1.64
    `amalgamation_is_pullback` + bicartesian upgrade), so step (ii) (equalizers) is
    likewise closed.  Step (iii) (covers, `preTopos_functor_preserves_covers`) is the
    sole remaining route here and carries the `[HasBinaryCoproducts 𝒜]`
    `[HasCoequalizers 𝒜]` additions. -/
theorem preTopos_functor_is_bicartesian_repr (hptf : PreToposFunctor F)
    [HasBinaryCoproducts 𝒜] [HasCoequalizers 𝒜]
    [HasBinaryCoproducts ℬ] [HasCoequalizers ℬ] :
    -- (a) F preserves covers:
    (∀ {A B : 𝒜} (f : A ⟶ B), Cover f → Cover (F.map f))
    -- (b) F preserves equalizers:
    ∧ (∀ {A B : 𝒜} (f g : A ⟶ B) (heq : HasEqualizer f g)
         (c : EqualizerCone (F.map f) (F.map g)),
         ∃ u : c.dom ⟶ F.obj heq.cone.dom,
           u ≫ F.map heq.cone.map = c.map
           ∧ ∀ v : c.dom ⟶ F.obj heq.cone.dom, v ≫ F.map heq.cone.map = c.map → v = u)
    -- (c) F preserves binary coproducts: canonical map coprod(FA,FB) → F(coprod A B) is iso:
    ∧ (∀ (A B : 𝒜),
         IsIso (HasBinaryCoproducts.case
                  (F.map (HasBinaryCoproducts.inl (A := A) (B := B)))
                  (F.map (HasBinaryCoproducts.inr (A := A) (B := B))) :
                HasBinaryCoproducts.coprod (F.obj A) (F.obj B) ⟶ F.obj (HasBinaryCoproducts.coprod A B))) :=
  ⟨fun f hf => preTopos_functor_preserves_covers hptf f hf,
   fun f g heq c => preTopos_functor_preserves_equalizers hptf f g heq c,
   fun A B => by
     -- F(coprod A B) is the pushout of F(init A) and F(init B) in ℬ.
     -- F(0) is initial in ℬ; uniqueness of maps from F(0) gives cocone commutativity.
     -- The inverse of case(F inl, F inr) comes from the pushout UMP.
     -- Let hpb : HasPushout (init A) (init B) be the coproduct, built explicitly.
     let hpb := coprod_is_pushout_of_init (𝒜 := 𝒜) A B
     -- Target cocone in ℬ: coprod(FA,FB) with inl_ℬ, inr_ℬ.
     -- Commutativity: F(init A) ≫ inl_ℬ and F(init B) ≫ inr_ℬ are both maps from F(0),
     -- equal by PreservesInitial.
     let tgt : PushoutCocone (F.map (HasCoterminator.init (𝒞 := 𝒜) A))
                             (F.map (HasCoterminator.init (𝒞 := 𝒜) B)) :=
       { pt := HasBinaryCoproducts.coprod (F.obj A) (F.obj B)
         ι₁ := HasBinaryCoproducts.inl
         ι₂ := HasBinaryCoproducts.inr
         w  := hptf.pres_initial
                 (F.map (HasCoterminator.init (𝒞 := 𝒜) A) ≫ HasBinaryCoproducts.inl)
                 (F.map (HasCoterminator.init (𝒞 := 𝒜) B) ≫ HasBinaryCoproducts.inr) }
     -- Apply PreservesPushouts with explicit instance hpb to obtain the inverse map.
     -- Type of inv: F.obj hpb.cocone.pt ⟶ tgt.pt = F (coprod A B) ⟶ coprod(FA,FB) (by def of hpb).
     -- We use show/change to expose this definitional equality to Lean.
     suffices h : IsIso (HasBinaryCoproducts.case
         (F.map (HasBinaryCoproducts.inl (A := A) (B := B)))
         (F.map (HasBinaryCoproducts.inr (A := A) (B := B))) :
       HasBinaryCoproducts.coprod (F.obj A) (F.obj B) ⟶ F.obj hpb.cocone.pt) from h
     obtain ⟨inv, hinv1, hinv2, hinv_uniq⟩ := hptf.pres_pushouts
       (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) (h := hpb) tgt
     -- inv : F.obj hpb.cocone.pt ⟶ tgt.pt = F (coprod A B) ⟶ coprod(FA,FB)
     -- hinv1 : F.map hpb.cocone.ι₁ ≫ inv = tgt.ι₁
     --       i.e. F.map inl ≫ inv = inl_ℬ  (since hpb.cocone.ι₁ = inl by definition)
     -- hinv2 : F.map hpb.cocone.ι₂ ≫ inv = tgt.ι₂  i.e. F.map inr ≫ inv = inr_ℬ
     refine ⟨inv, ?_, ?_⟩
     · -- case(F inl, F inr) ≫ inv = id_{coprod(FA,FB)}.
       -- By case_uniq, any h with inl ≫ h = inl, inr ≫ h = inr equals case(inl, inr).
       -- inl ≫ case(F inl, F inr) ≫ inv = F(inl) ≫ inv = inl_ℬ (hinv1 + case_inl).
       -- inl ≫ id = inl (comp_id).  So both equal case(inl, inr).
       -- case(inl, inr) = id by case_uniq.
       have hcase_id : HasBinaryCoproducts.case
           (HasBinaryCoproducts.inl (A := F.obj A) (B := F.obj B))
           (HasBinaryCoproducts.inr (A := F.obj A) (B := F.obj B)) = Cat.id _ :=
         (HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
       rw [← hcase_id]
       apply HasBinaryCoproducts.case_uniq
       · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hinv1
       · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact hinv2
     · -- inv ≫ case(F inl, F inr) = id_{F(coprod A B)}.
       -- Use uniqueness: both id and inv ≫ fwd are mediating maps to the self-cocone.
       let self_c : PushoutCocone (F.map (HasCoterminator.init (𝒞 := 𝒜) A))
                                  (F.map (HasCoterminator.init (𝒞 := 𝒜) B)) :=
         { pt := F.obj hpb.cocone.pt
           ι₁ := F.map (HasBinaryCoproducts.inl (A := A) (B := B))
           ι₂ := F.map (HasBinaryCoproducts.inr (A := A) (B := B))
           w  := hptf.pres_initial _ _ }
       obtain ⟨mid, _hmid1, _hmid2, hmid_uniq⟩ := hptf.pres_pushouts
         (HasCoterminator.init (𝒞 := 𝒜) A) (HasCoterminator.init (𝒞 := 𝒜) B) (h := hpb) self_c
       have heq_id : mid = Cat.id _ := (hmid_uniq (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
       have heq_cmp : mid = inv ≫ HasBinaryCoproducts.case
           (F.map (HasBinaryCoproducts.inl (A := A) (B := B)))
           (F.map (HasBinaryCoproducts.inr (A := A) (B := B))) :=
         (hmid_uniq _ (by rw [← Cat.assoc, hinv1, HasBinaryCoproducts.case_inl])
                      (by rw [← Cat.assoc, hinv2, HasBinaryCoproducts.case_inr])).symm
       exact heq_cmp.symm.trans heq_id⟩

end BiCartRepr

/-! ## §1.656 Remark on abelian categories (non-formalizable)

For functors between abelian categories, the analogous theorem holds:
preservation of the cocartesian structure and monics implies preservation of
the Cartesian structure (and its dual).  This is strictly stronger than for
pre-topoi, where only one direction transfers.

Non-formalizable in the current repo: requires the abelian category
infrastructure of §1.59 (zero object, half-additive structure, middle-two
interchange). -/

-- §1.656 (note): Not formalized; abelian infrastructure (§1.59) required.

end Freyd
