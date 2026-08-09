/-
  §1.543 — PER-STAGE FIBRE FACTS for the lax base-change slice system `laxOfProjSystem' P`.

  `RatCapHcanon.lean` (the `hcanon`-assembly) consumes three per-stage facts about the fibres
  `(laxOfProjSystem' P).A i = Over (P.pr i)` and the transition functors `(laxOfProjSystem' P).functF
  hij`, which act on arrows as `baseChangeMap (P.proj hij)` — the slice base-change (pullback) functor
  `g*` along the projection `g = P.proj hij : P.pr j ⟶ P.pr i`:

    1. `projStage_preservesMono` — `g*` preserves monos.  `g* = baseChangeObj g` is the RIGHT adjoint
       of strict reindexing `Σ_g = reindexObj g` (`bcTranspose`/`bcLift`, `RatCapPreReg`); a right
       adjoint preserves monos.  Constructively: a parallel pair into `g* x` with equal composites
       with `g* φ` transposes (`bcTranspose_natural`) to a parallel pair whose composites with `φ`
       agree; `φ` mono cancels it; `bcTranspose_inj` brings the equality back.

    2. `projStage_PTC` — each fibre transfers covers.  `Over (P.pr i)` is `overPreRegular`, and
       `PreRegularCategory` extends `PullbacksTransferCovers`; extract that field.

    3. `projStage_conservative` — `g*` reflects isos AMONG MONOS, given `g` a cover (`hpc`).  Base-
       change along an arbitrary `g` is NOT conservative, but along a COVER it reflects isos among
       monos (`BaseChangeDescent.isIso_of_baseChange_isIso_of_cover`) — exactly what the mono-
       restricted `hcons` of `laxColim_hcanon_of_stage` needs.  The cover-projection witness `hpc`
       is the legitimate §1.547 premise (capitalization makes the product-projections covers).

  `projStage_faithful`/`projStage_preservesCover` round out the five per-stage facts; the assembly
  `ratCapPreRegular_of_projCover P hpc : PreRegularCategory (ratCapCat P)` closes GAP 1.

  Mathlib-free; built on the repo's own `Cat` + `RatCapPreReg` + `SliceRegular` +
  `CapitalizationLaxColimit` + `BaseChangeDescent` + `RatCapHcanon`.
-/
module

public import Freyd.S1_543_RatCapPreReg
public import Freyd.S1_53_BaseChangeDescent
public import Freyd.S1_543_RatCapHcanon

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]

/-\! ## Fibre and transition shape

  For `L := laxOfProjSystem' P`, the fibre `L.A i` is the slice `Over (P.pr i)` and the transition
  `L.functF hij` acts on arrows as `baseChangeMap (P.proj hij)` — `g*` along the projection. -/
section Stage

variable (P : ProjSystem ι D 𝒞)

/-- The base map of the `i ≤ j` transition: the projection `P.proj hij : P.pr j ⟶ P.pr i`. -/
@[expose] public abbrev sproj {i j : ι} (hij : D.le i j) : P.pr j ⟶ P.pr i := P.proj hij

/-- `(laxOfProjSystem' P).functF hij` acts on arrows as `baseChangeMap (P.proj hij)`. -/
public theorem stage_functF_map {i j : ι} (hij : D.le i j) {X Y : Over (P.pr i)} (m : X ⟶ Y) :
    ((laxOfProjSystem' P).functF hij).map m
      = baseChangeMap (sproj P hij) m := rfl

/-\! ### 2. Monic preservation — `g*` is a right adjoint (`Σ_g ⊣ g*`)

  A parallel pair `u v : z ⟶ g* x` with `u ⊚ g*φ = v ⊚ g*φ` transposes, via `bcTranspose_natural`, to
  `bcTranspose u ⊚ φ = bcTranspose v ⊚ φ`; `φ` mono cancels `φ`; `bcTranspose_inj` reflects to
  `u = v`. -/
public theorem projStage_preservesMono {i j : ι} (hij : D.le i j)
    {x y : (laxOfProjSystem' P).A i} (φ : x ⟶ y)
    (hφ : Monic φ) :
    Monic (((laxOfProjSystem' P).functF hij).map φ) := by
  rw [stage_functF_map P hij φ]
  intro z u v huv
  apply bcTranspose_inj (sproj P hij)
  have h1 := bcTranspose_natural (sproj P hij) u φ
  have h2 := bcTranspose_natural (sproj P hij) v φ
  have key : bcTranspose (sproj P hij) (u ⊚ baseChangeMap (sproj P hij) φ)
      = bcTranspose (sproj P hij) (v ⊚ baseChangeMap (sproj P hij) φ) := by
    show bcTranspose (sproj P hij) (OverHom.comp u (baseChangeMap (sproj P hij) φ)) = _
    rw [show OverHom.comp u (baseChangeMap (sproj P hij) φ)
          = OverHom.comp v (baseChangeMap (sproj P hij) φ) from huv]
  rw [h1, h2] at key
  exact hφ _ _ key

/-\! ### 3. Per-stage `PullbacksTransferCovers`

  Each fibre `Over (P.pr i)` is `overPreRegular` (`SliceRegular`), and `PreRegularCategory` extends
  `PullbacksTransferCovers`; so the fibre `PullbacksTransferCovers` instance is the `overPreRegular`
  one.  Needs `[PreRegularCategory 𝒞]` (the source-fibre slice pre-regularity hypothesis). -/
public theorem projStage_PTC [PreRegularCategory 𝒞] (i : ι) :
    @PullbacksTransferCovers ((laxOfProjSystem' P).A i) ((laxOfProjSystem' P).catA i) :=
  (inferInstance : @PullbacksTransferCovers (Over (P.pr i)) (overCat (P.pr i)))

/-\! ### 1. Conservativity — `g*` reflects isos AMONG MONOS (given `g` a cover)

  This is the fibre fact that is FALSE for a base-change along an arbitrary `g`, but TRUE once `g` is
  a COVER and the map `φ` is a mono — exactly the shape the downstream `hcanon` assembly now demands
  (`RatCapHcanon.homInclL_cover_reflects`/`homInclL_isIso_reflects'` apply `hcons` only to the
  cover-factorization mono `m'`, and the projections arising from §1.547 product capitalization ARE
  covers, supplied here as the explicit hypothesis `hpc : Cover (P.proj hij)`).

  The proof is `BaseChangeDescent.isIso_of_baseChange_isIso_of_cover`: base-change along a cover
  reflects isos among monos.  The fibre `IsIso`/`Monic` are definitionally the slice `OverIso`/
  `OverMono`, and `Functor.map φ = baseChangeMap (P.proj hij) φ` (`stage_functF_map`). -/
public theorem projStage_conservative [PreRegularCategory 𝒞] {i j : ι} (hij : D.le i j)
    (hpc : Cover (sproj P hij))
    {x y : (laxOfProjSystem' P).A i} (φ : x ⟶ y) (hφmono : Monic φ)
    (hiso : IsIso (((laxOfProjSystem' P).functF hij).map φ)) :
    IsIso φ := by
  rw [stage_functF_map P hij φ] at hiso
  exact isIso_of_baseChange_isIso_of_cover (sproj P hij) hpc φ hφmono hiso

/-\! ### 4. Faithfulness — `g*` is faithful (given `g` a cover)

  Two over-maps `p q : x ⟶ y` with `g* p = g* q` agree.  The slice base-change pullback projection
  `π₁ˣ : x ×_{pr i} (pr j) ⟶ x.dom` is the `fst`-leg of the pullback of the cover `g = P.proj hij`
  along `x.hom`, hence a cover (`coverProj_of_cover`).  The naturality square `(g* p).f ≫ π₁ʸ =
  π₁ˣ ≫ p.f` (`lift_fst` of `baseChangeCone`) turns `g* p = g* q` into `π₁ˣ ≫ p.f = π₁ˣ ≫ q.f`;
  the cover `π₁ˣ` is epic (`cover_epi`), so `p.f = q.f`, hence `p = q` (`OverHom.ext`). -/
public theorem projStage_faithful [PreRegularCategory 𝒞] {i j : ι} (hij : D.le i j)
    (hpc : Cover (sproj P hij))
    {x y : (laxOfProjSystem' P).A i} (p q : x ⟶ y)
    (heq : ((laxOfProjSystem' P).functF hij).map p
        = ((laxOfProjSystem' P).functF hij).map q) :
    p = q := by
  rw [stage_functF_map P hij p, stage_functF_map P hij q] at heq
  -- the X-pullback of `(x.hom, g)`: its `fst`-leg `π₁ˣ` is a cover (pullback of the cover `g`).
  let PX := HasPullbacks.has x.hom (sproj P hij)
  have hπ₁X_cover : Cover PX.cone.π₁ := coverProj_of_cover PX.cone_isPullback hpc
  -- naturality squares `(g* p).f ≫ π₁ʸ = π₁ˣ ≫ p.f` (and same for `q`).
  let PY := HasPullbacks.has y.hom (sproj P hij)
  have hp : (baseChangeMap (sproj P hij) p).f ≫ PY.cone.π₁ = PX.cone.π₁ ≫ p.f :=
    PY.lift_fst (baseChangeCone (sproj P hij) p)
  have hq : (baseChangeMap (sproj P hij) q).f ≫ PY.cone.π₁ = PX.cone.π₁ ≫ q.f :=
    PY.lift_fst (baseChangeCone (sproj P hij) q)
  -- equal `g*`-images ⇒ equal underlying ⇒ `π₁ˣ ≫ p.f = π₁ˣ ≫ q.f`.
  have hfeq : (baseChangeMap (sproj P hij) p).f = (baseChangeMap (sproj P hij) q).f :=
    congrArg OverHom.f heq
  have hcancel : PX.cone.π₁ ≫ p.f = PX.cone.π₁ ≫ q.f := by rw [← hp, ← hq, hfeq]
  exact OverHom.ext (cover_epi hπ₁X_cover hcancel)

/-- **`g*` is UNCONDITIONALLY conservative when `g` is a cover** (no mono restriction).  For a cover
    transition the mono-restricted `projStage_conservative` upgrades to full conservativity: `g* φ`
    iso ⟹ `g* φ` mono ⟹ `φ` mono (a faithful functor — `projStage_faithful`, since `g` cover ⟹ `g*`
    faithful — reflects monos) ⟹ `φ` iso (mono-restricted descent).  This is the unconditional
    `hcons` shape `RatCapHcanon.stageInclFunctorL_faithful` / `capData_of_cofinalSystem` consume.
    (The §1.543 generic "g* not conservative" obstruction needed `g` NOT a cover; here `g` IS.) -/
public theorem projStage_conservative_full [PreRegularCategory 𝒞] {i j : ι} (hij : D.le i j)
    (hpc : Cover (sproj P hij))
    {x y : (laxOfProjSystem' P).A i} (φ : x ⟶ y)
    (hiso : IsIso (((laxOfProjSystem' P).functF hij).map φ)) :
    IsIso φ := by
  obtain ⟨inv, hinv1, hinv2⟩ := hiso
  -- `φ` is monic: a faithful functor (`projStage_faithful`) reflects monos, and `g* φ` is monic (iso).
  have hmonoφ : Monic φ := by
    intro Z a b hab
    apply projStage_faithful P hij hpc a b
    have hcomp : ((laxOfProjSystem' P).functF hij).map (a ≫ φ)
        = ((laxOfProjSystem' P).functF hij).map (b ≫ φ) := by rw [hab]
    rw [((laxOfProjSystem' P).functF hij).map_comp a φ,
        ((laxOfProjSystem' P).functF hij).map_comp b φ] at hcomp
    calc ((laxOfProjSystem' P).functF hij).map a
        = (((laxOfProjSystem' P).functF hij).map a
            ≫ ((laxOfProjSystem' P).functF hij).map φ) ≫ inv := by
          rw [Cat.assoc, hinv1, Cat.comp_id]
      _ = (((laxOfProjSystem' P).functF hij).map b
            ≫ ((laxOfProjSystem' P).functF hij).map φ) ≫ inv := by rw [hcomp]
      _ = ((laxOfProjSystem' P).functF hij).map b := by
          rw [Cat.assoc, hinv1, Cat.comp_id]
  exact projStage_conservative P hij hpc φ hmonoφ ⟨inv, hinv1, hinv2⟩

/-\! ### 5. Cover preservation — `g*` preserves covers (given `g` a cover)

  `g* m` is a cover in `Over (pr j)` iff its underlying arrow `(g* m).f` is a base cover
  (`cover_f_of_cover`/`cover_of_cover_f`).  `(g* m).f : x ×_{pr i}(pr j) ⟶ y ×_{pr i}(pr j)` sits in
  the pullback square `π₁ˣ ≫ m.f = (g* m).f ≫ π₁ʸ`, which IS a pullback (pasting the two base-change
  pullbacks).  `m.f` is a cover (`cover_f_of_cover`), so `PullbacksTransferCovers` makes the opposite
  leg `(g* m).f` a cover, lifting back to a slice cover (`cover_of_cover_f`). -/
public theorem projStage_preservesCover [PreRegularCategory 𝒞] {i j : ι} (hij : D.le i j)
    {x y : (laxOfProjSystem' P).A i} (φ : x ⟶ y) (hφ : Cover φ) :
    Cover (((laxOfProjSystem' P).functF hij).map φ) := by
  rw [stage_functF_map P hij φ]
  -- it suffices to show the underlying arrow `(g* φ).f` is a base cover.
  apply cover_of_cover_f
  -- `φ.f` is a base cover (slice cover ⇒ base cover).
  have hφf : Cover φ.f := cover_f_of_cover φ hφ
  -- the pullback square `(g* φ).f / π₁ˣ / π₁ʸ / φ.f` over the cospan `(φ.f, π₁ʸ)`.
  let PX := HasPullbacks.has x.hom (sproj P hij)
  let PY := HasPullbacks.has y.hom (sproj P hij)
  -- projection equations: `(g* φ).f ≫ π₁ʸ = π₁ˣ ≫ φ.f` and `(g* φ).f ≫ π₂ʸ = π₂ˣ`.
  have hfst : (baseChangeMap (sproj P hij) φ).f ≫ PY.cone.π₁ = PX.cone.π₁ ≫ φ.f :=
    PY.lift_fst (baseChangeCone (sproj P hij) φ)
  have hsnd : (baseChangeMap (sproj P hij) φ).f ≫ PY.cone.π₂ = PX.cone.π₂ :=
    PY.lift_snd (baseChangeCone (sproj P hij) φ)
  -- the cone over `(φ.f, π₁ʸ)` with apex `x ×C`, legs `(π₁ˣ, (g* φ).f)`.
  let cn : Cone φ.f PY.cone.π₁ :=
    ⟨PX.cone.pt, PX.cone.π₁, (baseChangeMap (sproj P hij) φ).f, by rw [hfst]⟩
  -- it IS a pullback (pasting the two base-change pullbacks).
  have hpb : cn.IsPullback := by
    intro d
    -- `d : Cone φ.f π₁ʸ`, i.e. `d.π₁ : d.pt → x.dom`, `d.π₂ : d.pt → y×C`, `d.π₁ ≫ φ.f = d.π₂ ≫ π₁ʸ`.
    -- lift `(d.π₁, d.π₂ ≫ π₂ʸ)` into the X-pullback (cospan `(x.hom, g)`).
    have hwX : d.π₁ ≫ x.hom = (d.π₂ ≫ PY.cone.π₂) ≫ (sproj P hij) := by
      rw [← φ.w, ← Cat.assoc, d.w, Cat.assoc, PY.cone.w, Cat.assoc]
    let u : d.pt ⟶ PX.cone.pt := PX.lift ⟨d.pt, d.π₁, d.π₂ ≫ PY.cone.π₂, hwX⟩
    have hu₁ : u ≫ PX.cone.π₁ = d.π₁ := PX.lift_fst _
    have hu₂' : u ≫ PX.cone.π₂ = d.π₂ ≫ PY.cone.π₂ := PX.lift_snd _
    refine ⟨u, ⟨hu₁, ?_⟩, ?_⟩
    · -- `u ≫ (g* φ).f = d.π₂` by Y-pullback monicity (both lift the same Y-cone, via π₁ʸ, π₂ʸ).
      let dY : Cone y.hom (sproj P hij) := ⟨d.pt, d.π₂ ≫ PY.cone.π₁, d.π₂ ≫ PY.cone.π₂,
        by rw [Cat.assoc, Cat.assoc, PY.cone.w]⟩
      have hUC : u ≫ (baseChangeMap (sproj P hij) φ).f = PY.lift dY :=
        PY.lift_uniq dY _ (by rw [Cat.assoc, hfst, ← Cat.assoc, hu₁, d.w]) (by rw [Cat.assoc, hsnd, hu₂'])
      have hdC : d.π₂ = PY.lift dY := PY.lift_uniq dY _ rfl rfl
      show u ≫ (baseChangeMap (sproj P hij) φ).f = d.π₂
      rw [hUC, hdC]
    · -- the reverse: any `v` with `v ≫ π₁ˣ = d.π₁`, `v ≫ (g*φ).f = d.π₂` equals `u` (both lift the
      -- same X-cone: agree on `π₁ˣ` (= `d.π₁`) and `π₂ˣ` (= `d.π₂ ≫ π₂ʸ`, via `hsnd`)).
      intro v hv₁ hv₂
      have hvπ₂ : v ≫ PX.cone.π₂ = d.π₂ ≫ PY.cone.π₂ := by
        have h := congrArg (· ≫ PY.cone.π₂) hv₂
        simp only at h
        rw [Cat.assoc, hsnd] at h
        exact h
      have hv_eq : v = PX.lift ⟨d.pt, d.π₁, d.π₂ ≫ PY.cone.π₂, hwX⟩ :=
        PX.lift_uniq ⟨d.pt, d.π₁, d.π₂ ≫ PY.cone.π₂, hwX⟩ v hv₁ hvπ₂
      have hu_eq : u = PX.lift ⟨d.pt, d.π₁, d.π₂ ≫ PY.cone.π₂, hwX⟩ :=
        PX.lift_uniq ⟨d.pt, d.π₁, d.π₂ ≫ PY.cone.π₂, hwX⟩ u hu₁ hu₂'
      rw [hv_eq, hu_eq]
  -- transfer the cover `φ.f` across the pullback to the opposite leg `cn.π₂ = (g* φ).f`.
  show Cover cn.π₂
  exact PullbacksTransferCovers.pullbacks_transfer_covers cn hpb hφf

end Stage

/-! ## PART C — `PreRegularCategory (ratCapCat P)` from cover-projections

  Wiring the five per-stage facts (Part B) through `laxColim_hcanon_of_stage` (Part A) discharges the
  `hcanon` hypothesis of `ratCapPreRegular`, yielding `PreRegularCategory (ratCapCat P)` outright,
  modulo the explicit §1.547 cover-projection hypothesis `hpc : ∀ {i j} (h), Cover (P.proj h)`.

  Universe note: `laxColim_hcanon_of_stage` lives in the single-universe section, so the index `ι`
  here sits in `Type w` (the §1.547 index universe), matching the hom-universe of `𝒞`. -/
section ProjCover

universe w'

variable {ι : Type w'} {D : Directed ι}
variable {𝒞 : Type w'} [Cat.{w'} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]

/-- **§1.543 GAP 1, assembled.**  Given a directed product-projection system `P` whose projections
    are covers (`hpc`, the §1.547 cover-projection content), the rational-capitalization colimit
    category `ratCapCat P` is pre-regular.  All five per-stage facts about base-change `g*`
    (faithful, mono-restricted conservative, mono-preserving, cover-preserving, fibre-PTC) are
    supplied by the `projStage_*` lemmas; `laxColim_hcanon_of_stage` (Part A) assembles them into the
    canonical-pullback cover-transfer `hcanon`, which `ratCapPreRegular` consumes. -/
@[expose] public noncomputable def ratCapPreRegular_of_projCover [Nonempty ι] (P : ProjSystem ι D 𝒞)
    (hpc : ∀ {i j : ι} (h : D.le i j), Cover (P.proj h)) :
    @PreRegularCategory (Obj (laxOfProjSystem' P)) (ratCat P) :=
  ratCapPreRegular P
    (laxColim_hcanon_of_stage (laxOfProjSystem' P) (coherentProj P)
      (ratLaxTerminalData P) (ratLaxProductData P) (ratLaxEqualizerData P)
      (fun {_i _j} hij {_x _y} p q heq => projStage_faithful P hij (hpc hij) p q heq)
      (fun {_i _j} hij {_x _y} φ hm hiso => projStage_conservative P hij (hpc hij) φ hm hiso)
      (fun {_i _j} hij {_x _y} φ hm => projStage_preservesMono P hij φ hm)
      (fun {_i _j} hij {_x _y} φ hc => projStage_preservesCover P hij φ hc)
      (fun i => projStage_PTC P i))

end ProjCover

end Freyd.LaxColim
