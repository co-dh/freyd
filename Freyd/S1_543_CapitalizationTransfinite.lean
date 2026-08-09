module

public import Freyd.S1_543_Capitalization

/-! # §1.543 — the capital-closure fixpoint `hwall_cap`, transfinite analysis

  This file isolates and analyses the capital-closure fixpoint `hwall_cap` of Freyd's §1.543: the
  obligation that the ω-tower colimit `Ā = (towerSystem b nextStep).Obj` is **capital** — every
  well-supported object of `Ā` is well-pointed (`Capital 𝒞 := ∀ A, WellSupported A → WellPointed A`,
  S1_52.lean).  NOTE: §1.543 itself is now PROVEN Sorry-free — `Freyd.capData_exists` /
  `Freyd.capitalization_lemma` are discharged in `Freyd/CapDataWiring.lean`; this file is the
  standalone transfinite diagnostic of the `hwall_cap` ingredient (not a remaining hole in the lemma).

  ## The precise obstruction (diagnosed, not re-derived)

  Two facts about the *current* construction make `hwall_cap` genuinely UNPROVABLE as it stands.  This
  file records them honestly rather than faking a close, and builds the real reduction infrastructure.

  1. **`CapStep` carries no points-acquisition data.**  Inspect `Freyd.CapStep` (Capitalization.lean
     L716): its fields are `T`/`step`/`stepFun`/`stepFaithful` plus the five preservation fields
     (`stepTerminal`/`stepTerminalArrow`/`stepProds`/`stepEqs`/`stepMono`/`stepCover`).  There is NO
     field asserting that the successor adds a point to (well-supported objects of) `S`.  From the
     abstract `nextStep`/tower package one therefore CANNOT derive that any object becomes
     well-pointed.  The missing obligation is recorded below as `StepWellPoints`.

  2. **The concrete `nextStep` is not cofinal.**  `Freyd.nextStep S := nextStepOfEnum
     (Classical.choose (exists_wellSupported_enum S.carrier)) …`, and `exists_wellSupported_enum` is
     proven by the CONSTANT-`1` witness `⟨fun _ => 1, …⟩` (Capitalization.lean L2246).
     `Classical.choose` may pick that constant enumeration, whose inner colimit points essentially no
     well-supported object.  Even a non-constant `ℕ`-enumeration is cofinal over the well-supported
     objects only when they are ℕ-enumerable; for an uncountable carrier it is not.

  ## What this file delivers (mathlib-free; see the IMPORT note)

  * `StepWellPoints` / `CofinalCapStep` — the points-acquisition obligation the bare `CapStep` omits,
    stated against the book's own `WellPointed`, bundled with the uniform successor.
  * `StageRelCap` / `wellPointed_of_stage` — the cover-survival reduction from Freyd's RELATIVE-CAP
    hypothesis (def 1.545): if every *proper* mono into a later-stage pushforward of `A₀` is missed by
    a point at SOME *still-later* stage, the colimit object `objIncl i A₀` is well-pointed.  This is
    strictly weaker than full well-pointedness of the pushforward at each stage (which would force the
    missing point to live at the same stage as the mono — false after one §1.547 step).  The genuine
    reusable categorical content of Freyd's fixpoint, now stated against the honest §1.546/1.547
    interface; proven Sorry-free (the colimit-mono / point-factorization alignment to a common stage).
  * `tower_capital_of_cofinal` — the OUTER ω-fixpoint: from a cofinal points-acquiring tower in which
    every well-supported colimit object's stage representative stays well-pointed at all later stages,
    the colimit is capital.  Reduces `hwall_cap` to the single hypothesis bundle that is exactly
    obstruction (1)+(2); proven Sorry-free *on top of* `wellPointed_of_stage`.

  ## IMPORT note (why this file stays mathlib-free)

  The project lakefile (`lakefile.toml`) has NO mathlib dependency and `lake-manifest.json` lists no
  packages — the repo is fully standalone.  CLAUDE.md *permits* `Mathlib.SetTheory.Ordinal.*` in this
  one transfinite file, but pulling all of mathlib into a previously dependency-free project would add
  the full mathlib download/build to a project whose CLAUDE.md mandates "keep every other file
  mathlib-free so builds stay fast", and core/Std Lean does NOT ship the well-ordering theorem
  (`WellOrderingRel` is mathlib-only; verified).  The genuinely transfinite step — a `<+:`-monotone
  chain over `Infl 𝒞` COFINAL over an uncountable object set — needs a well-ordering of the objects so
  the chain at ordinal `α` is the initial segment `[B_β : β < α]` (prefixes ↔ ordinal `≤`).  That one
  step is the irreducible residual; everything else here is mathlib-free and proven. -/

namespace Freyd

open Colim

universe u

/-! ## The points-acquisition obligation the missing `CapStep` field would carry -/

/-- **The points-acquisition obligation of a capitalizing successor.**  Given a `CapStep S` whose next
    stage is `st.T`, this asserts that for every well-supported object `A` of `S`, its image
    `st.stepFun.obj A` is **well-pointed** in `st.T` (the book's `WellPointed`, S1_52.lean).  This is the
    field `CapStep` lacks; the concrete `nextStep` satisfies it only when its inner enumeration is
    cofinal over the well-supported objects (obstruction (2)). -/
@[expose] public def StepWellPoints {S : Type u} [Cat.{u} S] [PreRegularCategory S] (st : CapStep S) : Prop :=
  letI : Cat st.T := st.catT
  letI : PreRegularCategory st.T := st.preT
  ∀ A : S, WellSupported A → WellPointed (st.stepFun.obj A)

/-- **A cofinal capitalizing successor** — the data the §1.543 fixpoint genuinely consumes: the
    uniform `CapStep` successor (exactly `nextStep`'s content, already Sorry-free in
    Capitalization.lean) bundled with the points-acquisition obligation `StepWellPoints` for every
    bundle.  Producing a `CofinalCapStep` is the whole remaining work of §1.543: for the constant-`1` /
    countable enumeration the current `nextStep` uses, `wellPoints` FAILS over an uncountable carrier
    (obstruction (2)); closing it needs the transfinite cofinal `<+:`-chain over `Infl 𝒞`. -/
public structure CofinalCapStep where
  /-- the uniform successor — `nextStep`'s content. -/
  step : ∀ (S : PreRegBundle.{u}), CapStep S.carrier
  /-- the obligation the bare `CapStep` omits: each rung points every well-supported object. -/
  wellPoints : ∀ (S : PreRegBundle.{u}), StepWellPoints (step S)

/-- **Freyd's RELATIVE-CAP condition (§1.545/1.547), per stage object.**  For a `CatSystem` `C`, a
    stage `i`, and an object `A₀` of stage `i`, this says: every *proper* mono `m'` into a pushforward
    `C.F hij A₀` (at any later stage `j ≥ i`) is MISSED by a point `pt` of a *still-later* pushforward
    `C.F hjk (C.F hij A₀)` — `pt` does not factor through the pushed mono `(functF hjk).map m'`.

    This is strictly WEAKER than asking every `C.F hij A₀` be `WellPointed` (which would force the
    missing point to live at stage `j` itself).  Def 1.545 only guarantees each subobject is missed at
    *some later* stage — exactly what one §1.547 relative-capitalization step provides; after one step
    the stage is NOT fully well-pointed.  This is the honest hypothesis `wellPointed_of_stage` consumes. -/
@[expose] public def StageRelCap {ι : Type u} {D : Colim.Directed ι} (C : Colim.CatSystem.{u, u} ι D)
    (ht : ∀ i, HasTerminal (C.A i)) (i : ι) (A₀ : C.A i) : Prop :=
  ∀ {j} (hij : D.le i j) {E' : C.A j} (m' : E' ⟶ C.F hij A₀),
    @Monic (C.A j) (C.catA j) _ _ m' → ¬ @IsIso (C.A j) (C.catA j) _ _ m' →
    ∃ (k : ι) (hjk : D.le j k)
      (pt : @HasTerminal.one (C.A k) (C.catA k) (ht k) ⟶ C.F hjk (C.F hij A₀)),
      ¬ ∃ y, y ≫ C.Fmap hjk m' = pt

/-! ## Cover-survival of well-pointedness through the colimit -/

/-- **A map factors through a mono iff the pullback leg over it is an isomorphism.**
    Pure category theory.  For a pullback cone `c` of the cospan `(f : A ⟶ C, g : B ⟶ C)` with
    `f` MONIC, `g` factors through `f` (`∃ y, y ≫ f = g`) iff `c.π₂` (the leg over `g`) is an
    isomorphism.  Forward: a factor `y` makes `(y, 1_B) : B → c.pt` a section of `c.π₂`, and since
    `f` mono forces `c.π₂` mono (pullback of a mono is mono), a split-mono section makes `c.π₂` iso.
    Backward: `y := c.π₂⁻¹ ≫ c.π₁` factors `g` (using the square `c.w` and `π₂⁻¹ ≫ π₂ = 1`). -/
public theorem factor_iff_pullback_π₂_iso {𝒞 : Type u} [Cat.{u} 𝒞] {A B C : 𝒞}
    {f : A ⟶ C} {g : B ⟶ C} (hf : Monic f) (c : Cone f g) (hpb : c.IsPullback) :
    (∃ y : B ⟶ A, y ≫ f = g) ↔ IsIso c.π₂ := by
  constructor
  · rintro ⟨y, hy⟩
    -- `(y, 1_B)` is a cone over `(f, g)`; its lift `s : B → c.pt` is a section of `c.π₂`.
    obtain ⟨s, ⟨hs₁, hs₂⟩, _⟩ := hpb ⟨B, y, Cat.id B, by rw [hy, Cat.id_comp]⟩
    -- `c.π₂` is monic: pullback of the mono `f`.  `u ≫ π₂ = v ≫ π₂` and the square give
    -- `u ≫ π₁ = v ≫ π₁` (cancel `f`), so `u = v` by the pullback's uniqueness.
    have hπ₂mono : Monic c.π₂ := by
      intro W u v huv
      have h₁ : u ≫ c.π₁ = v ≫ c.π₁ := by
        apply hf
        rw [Cat.assoc, c.w, ← Cat.assoc, huv, Cat.assoc, ← c.w, Cat.assoc]
      obtain ⟨_, _, huniq⟩ := hpb ⟨W, u ≫ c.π₁, u ≫ c.π₂, by rw [Cat.assoc, c.w, Cat.assoc]⟩
      rw [huniq u rfl rfl, huniq v h₁.symm huv.symm]
    -- `s ≫ c.π₂ = 1_B` (`hs₂`), so `c.π₂` is split mono; a monic split mono is iso.
    refine ⟨s, ?_, hs₂⟩
    -- `c.π₂ ≫ s = 1` from `(c.π₂ ≫ s) ≫ c.π₂ = c.π₂ = 1 ≫ c.π₂` and `c.π₂` mono.
    exact hπ₂mono _ _ (by rw [Cat.assoc, hs₂, Cat.comp_id, Cat.id_comp])
  · rintro ⟨inv, hinv₁, hinv₂⟩
    -- `y := inv ≫ c.π₁` factors `g`: `y ≫ f = inv ≫ (π₁ ≫ f) = inv ≫ (π₂ ≫ g) = (inv ≫ π₂) ≫ g = g`.
    exact ⟨inv ≫ c.π₁, by rw [Cat.assoc, c.w, ← Cat.assoc, hinv₂, Cat.id_comp]⟩

variable {ι : Type u} {D : Directed ι}

/-- **The stage inclusion reflects monos** (conservativity route, no faithfulness needed).  If
    `homInclObj g` is monic in the colimit and transitions are conservative (`hcons`), then `g` is
    monic at its stage.  `g` monic ⟺ the diagonal into a kernel-pair level is iso
    (`mono_iff_level_diag_iso`).  The stage kernel-pair pullback of `(g, g)` is preserved by the stage
    inclusion (`objIncl_preserves_pullbacks`), so its `homInclObj`-image is a level of `homInclObj g`
    whose diagonal is `homInclObj kp_diag`.  `homInclObj g` monic forces that colimit diagonal iso;
    iso-reflection (`homInclObj_isIso_reflects`, via `hcons`) brings it back to the stage diagonal. -/
public theorem homInclObj_mono_reflects (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ C.Fmap hij (hp i).fst = v ≫ C.Fmap hij (hp i).fst →
        u ≫ C.Fmap hij (hp i).snd = v ≫ C.Fmap hij (hp i).snd → u = v)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ C.Fmap hij (hp i).fst = p ∧ r ≫ C.Fmap hij (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ C.Fmap hij (eqMap f g) = v ≫ C.Fmap hij (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
        (k : z ⟶ C.F hij X)
        (_hk : k ≫ C.Fmap hij f = k ≫ C.Fmap hij g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ C.Fmap hij (eqMap f g) = k)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    {K : ι} {x y : C.A K} (g : x ⟶ y)
    (hm : @Monic C.Obj (colimitCat C hC) (C.objIncl K x) (C.objIncl K y) (homInclObj C hC g)) :
    @Monic (C.A K) (C.catA K) x y g := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal (C.A K) := ht K
  letI : HasBinaryProducts (C.A K) := hp K
  letI : HasEqualizers (C.A K) := he K
  letI : HasPullbacks (C.A K) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  -- the chosen kernel-pair pullback of `(g, g)` (matches `objIncl_preserves_pullbacks`'s `P`)
  let P := products_equalizers_implies_pullbacks g g
  -- stage kernel-pair level of `g`, built directly on `P.cone` (so `Ls.c.pt` is `P.cone.pt`
  -- syntactically, matching the colimit cone below)
  let Ls : Level g :=
    { c := P.cone, hpb := P.cone_isPullback, δ := P.lift diagCone,
      δ₁ := P.lift_fst diagCone, δ₂ := P.lift_snd diagCone }
  -- the colimit cone (the `homInclObj`-image of `P.cone`); its cospan is inferred from the legs
  let cc := Cone.mk (f := homInclObj C hC g) (g := homInclObj C hC g)
      (C.objIncl K P.cone.pt) (homInclObj C hC P.cone.π₁) (homInclObj C hC P.cone.π₂)
      (show colimComp C hC (homInclObj C hC P.cone.π₁) (homInclObj C hC g)
          = colimComp C hC (homInclObj C hC P.cone.π₂) (homInclObj C hC g) by
        rw [← homInclObj_comp C hC P.cone.π₁ g, ← homInclObj_comp C hC P.cone.π₂ g, P.cone.w])
  have hcc_pb : cc.IsPullback :=
    objIncl_preserves_pullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift K g g
  -- the two collapse equations of the colimit diagonal `homInclObj Ls.δ` against `cc`
  have e₁ : Ls.δ ≫ P.cone.π₁ = Cat.id x := Ls.δ₁
  have e₂ : Ls.δ ≫ P.cone.π₂ = Cat.id x := Ls.δ₂
  have hδ₁ : homInclObj C hC Ls.δ ≫ cc.π₁ = Cat.id (C.objIncl K x) := by
    show colimComp C hC (homInclObj C hC Ls.δ) (homInclObj C hC P.cone.π₁) = _
    rw [← homInclObj_comp C hC Ls.δ P.cone.π₁, e₁]; exact homInclObj_id C hC x
  have hδ₂ : homInclObj C hC Ls.δ ≫ cc.π₂ = Cat.id (C.objIncl K x) := by
    show colimComp C hC (homInclObj C hC Ls.δ) (homInclObj C hC P.cone.π₂) = _
    rw [← homInclObj_comp C hC Ls.δ P.cone.π₂, e₂]; exact homInclObj_id C hC x
  -- `homInclObj g` mono ⇒ colimit level diagonal `homInclObj Ls.δ` iso (`mono_iff_level_diag_iso`)
  -- `homInclObj g` mono ⇒ the colimit diagonal `homInclObj Ls.δ` is iso, with inverse `cc.π₁`.
  -- (forward direction of `mono_iff_level_diag_iso`, inlined to dodge the `Level` elaboration of a
  -- non-stage hom whose `⟶`-codomain is not syntactically exposed).
  have hLcδ : @IsIso C.Obj (colimitCat C hC) (C.objIncl K x) (C.objIncl K Ls.c.pt)
      (homInclObj C hC Ls.δ) := by
    refine ⟨cc.π₁, hδ₁, ?_⟩
    -- `cc.π₁ ≫ homInclObj Ls.δ = id`: both are the unique self-lift of the pullback cone `cc`.
    have hπ : cc.π₁ = cc.π₂ := hm _ _ cc.w
    obtain ⟨_, _, huniq⟩ := hcc_pb cc
    have hid : Cat.id cc.pt = _ := huniq (Cat.id cc.pt) (Cat.id_comp _) (Cat.id_comp _)
    have hcomp : cc.π₁ ≫ homInclObj C hC Ls.δ = _ := huniq (cc.π₁ ≫ homInclObj C hC Ls.δ)
      (by rw [Cat.assoc, hδ₁, Cat.comp_id])
      (by rw [Cat.assoc, hδ₂, Cat.comp_id, hπ])
    rw [hcomp, ← hid]
  -- iso-reflection (`hcons`) brings it to the stage diagonal; `Ls.δ` iso ⇒ `g` mono
  have hLsδ : IsIso Ls.δ := homInclObj_isIso_reflects C hC hcons Ls.δ hLcδ
  intro W u v huv
  exact (mono_iff_level_diag_iso Ls).2 hLsδ u v huv

/-- **Cover-survival reduction (the §1.543 fixpoint core), from Freyd's RELATIVE-CAP hypothesis.**
    For a coherent `CatSystem` `C` whose transitions are conservative (`hcons`) — so the colimit is
    pre-regular and its stage inclusions reflect covers — a colimit object represented at stage `i` as
    `objIncl i A₀` is well-pointed in `C.Obj`, PROVIDED `StageRelCap C ht i A₀` (`hRC`): every *proper*
    mono into a pushforward `C.F hij A₀` (any later stage `j ≥ i`) is MISSED by a point of a
    *still-later* pushforward `C.F hjk (C.F hij A₀)`.

    WHY relative-cap, NOT full well-pointedness of the pushforward.  Freyd def 1.545 only guarantees
    each subobject is missed at SOME later stage; after one §1.547 relative-capitalization step the
    stage is not fully well-pointed.  The earlier (over-strong) form `hWP : ∀ j ≥ i, WellPointed
    (C.F hij A₀)` forced the missing point to live at the SAME stage `j` as the mono.  The proof only
    ever needs ONE point missing ONE reflected mono, and it can come from any later stage — so the
    honest relative-cap form (point at a later stage `k`) suffices.

    PROOF SHAPE.  Take a colimit mono `m : E ⟶ objIncl i A₀`, `¬ IsIso m`.  Align it
    (`colimHom_as_homInclObj`) to a stage-`K` mono `mNK : E₀ ⟶ C.F (i→K) A₀` (mono reflected by
    `homInclObj_mono_reflects`; `¬ IsIso` reflected by `hcons`).  `hRC (i→K)` supplies a LATER stage
    `k ≥ K` and a point `pt : 1 → C.F (K→k) (C.F (i→K) A₀)` missing the PUSHED mono
    `mNk = (functF (K→k)).map mNK`.  Push the whole mono to stage `k` (the colimit mono `m` is
    invariant under the push, `homInclObj_push_heq`); `homInclObj pt` is a colimit point of
    `objIncl i A₀` (`objIncl_terminal_eq`) not factoring through `m` — a colimit factorization would
    reflect (via the stage pullback of `(mNk, pt)`, preserved by `objIncl_preserves_pullbacks`, and
    `homInclObj_isIso_reflects`) to a stage factorization of `pt` through `mNk`, contradicting `hRC`. -/
public theorem wellPointed_of_stage
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (uu vv : z ⟶ C.F hij ((hp i).prod a c)),
      uu ≫ (C.Fmap hij (hp i).fst) = vv ≫ (C.Fmap hij (hp i).fst) →
      uu ≫ (C.Fmap hij (hp i).snd) = vv ≫ (C.Fmap hij (hp i).snd) → uu = vv)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij c),
      ∃ r : z ⟶ C.F hij ((hp i).prod a c),
        r ≫ (C.Fmap hij (hp i).fst) = p ∧ r ≫ (C.Fmap hij (hp i).snd) = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (uu vv : z ⟶ C.F hij (eqObj f g)),
      uu ≫ (C.Fmap hij (eqMap f g)) = vv ≫ (C.Fmap hij (eqMap f g)) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (k : z ⟶ C.F hij X) (_hk : k ≫ (C.Fmap hij f) = k ≫ (C.Fmap hij g)),
      ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.Fmap hij (eqMap f g)) = k)
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        ∀ {X Y Z : C.Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (i : ι) (A₀ : C.A i)
    (hRC : StageRelCap C ht i A₀) :
    letI : Cat C.Obj := colimitCat C hC
    @WellPointed C.Obj (colimitCat C hC)
      ((colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        hcanon).toHasTerminal) (C.objIncl i A₀) := by
  letI : Cat C.Obj := colimitCat C hC
  intro E m hm hniso
  -- align the colimit mono `m : E ⟶ objIncl i A₀` to a stage-`N` germ `mN : xE ⟶ xA`
  obtain ⟨N, xE, xA, mN, eE, eA, hHEq⟩ := colimHom_as_homInclObj C hC m
  subst eE
  -- common stage `K ≥ N, i` where the codomain rep `xA` agrees with the pushforward `F (i→K) A₀`
  obtain ⟨K, hNK, hiK, hAeq⟩ := Quotient.exact eA
  dsimp only [CatSystem.objSystem] at hAeq
  -- push `mN` to stage `K`; `m` is its stage-`K` inclusion (transported by the object equalities)
  let mNK := C.Fmap hNK mN
  have hcodXE : C.objIncl K (C.F hNK xE) = C.objIncl N xE := C.objIncl_compat hNK xE
  have hcodXA : C.objIncl K (C.F hNK xA) = C.objIncl i A₀ := (C.objIncl_compat hNK xA).trans eA
  have hmeq : castHom hcodXE hcodXA (homInclObj C hC mNK) = m :=
    castHom_of_heq hcodXE hcodXA ((homInclObj_push_heq C hC hNK mN).trans hHEq)
  -- `homInclObj mNK` inherits `Monic` and `¬IsIso` from `m` (cast along the object equalities)
  have hmNK_eq : homInclObj C hC mNK = castHom hcodXE.symm hcodXA.symm m := by
    rw [← hmeq, castHom_castHom, castHom_rfl]
  have hm' : @Monic C.Obj (colimitCat C hC) (C.objIncl K (C.F hNK xE)) (C.objIncl K (C.F hNK xA))
      (homInclObj C hC mNK) := by
    rw [hmNK_eq]; exact mono_castHom hcodXE.symm hcodXA.symm m hm
  have hniso' : ¬ @IsIso C.Obj (colimitCat C hC) (C.objIncl K (C.F hNK xE)) (C.objIncl K (C.F hNK xA))
      (homInclObj C hC mNK) := by
    rw [hmNK_eq]; exact fun h => hniso (isIso_of_castHom hcodXE.symm hcodXA.symm m h)
  -- reflect `Monic`/`¬IsIso` to the stage germ `mNK`
  have hmNK_mono : @Monic (C.A K) (C.catA K) (C.F hNK xE) (C.F hNK xA) mNK :=
    homInclObj_mono_reflects C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcons
      (K := K) (x := C.F hNK xE) (y := C.F hNK xA) mNK hm'
  have hmNK_niso : ¬ @IsIso (C.A K) (C.catA K) _ _ mNK := fun h => by
    obtain ⟨g', hg1, hg2⟩ := h
    exact hniso' (homInclObj_isIso_of_stage C hC mNK g' hg1 hg2)
  -- **RELATIVE-CAP step (§1.547).**  `hRC` at stage `K`, applied to the aligned stage mono
  -- (`hAeq ▸ mNK : C.F hNK xE ⟶ C.F hiK A₀`), supplies a LATER stage `k ≥ K` and a point `pt` of the
  -- pushforward `C.F hKk (C.F hNK xA)` MISSING the pushed mono `mNk = (functF hKk).map mNK` — NOT a
  -- point at stage `K` itself.  We then push the whole mono to stage `k` and run the colimit-mono
  -- contradiction there (the colimit mono `m` is invariant under the push, `homInclObj_push_heq`).
  -- Rewrite `mNK` to a mono into `C.F hiK A₀` so `hRC hiK` applies; the result transports back.
  -- generalize the codomain to a fresh object so `hAeq` can rewrite the existential goal uniformly.
  obtain ⟨k, hKk, pt, hpt⟩ : ∃ (k : ι) (hKk : D.le K k)
      (pt : @HasTerminal.one (C.A k) (C.catA k) (ht k) ⟶ C.F hKk (C.F hNK xA)),
      ¬ ∃ y, y ≫ C.Fmap hKk mNK = pt := by
    -- clear the `m`-aligned facts (they mention `C.F hNK xA` via casts) so only `mNK`,
    -- `hmNK_mono`, `hmNK_niso` depend on the rewritten codomain and get carried through `rw [hAeq]`.
    clear hmeq hmNK_eq hm' hniso' hHEq
    clear_value mNK
    -- rewrite the GOAL + the two carried facts' codomain `C.F hNK xA → C.F hiK A₀`; then `hRC hiK`.
    revert mNK hmNK_mono hmNK_niso; rw [hAeq]; intro mNK hmNK_mono hmNK_niso
    exact hRC hiK mNK hmNK_mono hmNK_niso
  -- push the mono to stage `k`: `mNk : C.F hKk (C.F hNK xE) ⟶ C.F hKk (C.F hNK xA)`
  let mNk := C.Fmap hKk mNK
  -- colimit-object equalities at stage `k`: `objIncl k (F hKk ·) = objIncl i A₀ / objIncl N xE`
  have hcodXEk : C.objIncl k (C.F hKk (C.F hNK xE)) = C.objIncl N xE :=
    (C.objIncl_compat hKk (C.F hNK xE)).trans hcodXE
  have hcodXAk : C.objIncl k (C.F hKk (C.F hNK xA)) = C.objIncl i A₀ :=
    (C.objIncl_compat hKk (C.F hNK xA)).trans hcodXA
  -- `homInclObj mNk = castHom (homInclObj mNK)` (push-invariance), so colimit mono/niso transfer
  have hmNk_push : homInclObj C hC mNk
      = castHom (C.objIncl_compat hKk (C.F hNK xE)).symm (C.objIncl_compat hKk (C.F hNK xA)).symm
          (homInclObj C hC mNK) :=
    (castHom_of_heq (C.objIncl_compat hKk (C.F hNK xE)).symm (C.objIncl_compat hKk (C.F hNK xA)).symm
      ((homInclObj_push_heq C hC hKk mNK).symm)).symm
  have hmk' : @Monic C.Obj (colimitCat C hC) (C.objIncl k (C.F hKk (C.F hNK xE)))
      (C.objIncl k (C.F hKk (C.F hNK xA))) (homInclObj C hC mNk) := by
    rw [hmNk_push]
    exact mono_castHom (C.objIncl_compat hKk (C.F hNK xE)).symm
      (C.objIncl_compat hKk (C.F hNK xA)).symm (homInclObj C hC mNK) hm'
  -- reflect `Monic` to the stage germ `mNk`
  have hmNk_mono : @Monic (C.A k) (C.catA k) (C.F hKk (C.F hNK xE)) (C.F hKk (C.F hNK xA)) mNk :=
    homInclObj_mono_reflects C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcons
      (K := k) (x := C.F hKk (C.F hNK xE)) (y := C.F hKk (C.F hNK xA)) mNk hmk'
  -- the colimit terminal `one` is `objIncl k (ht k).one` (`objIncl_terminal_eq`)
  have hone : C.objIncl k (ht k).one
      = @HasTerminal.one C.Obj (colimitCat C hC)
          (colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
            hcanon).toHasTerminal :=
    objIncl_terminal_eq C hC ht htpres k (Classical.choice hne)
  -- the colimit point: `homInclObj pt`, transported to `one ⟶ objIncl i A₀`
  refine ⟨castHom hone hcodXAk (homInclObj C hC pt), ?_⟩
  -- a colimit factorization of the point through `m` reflects, via the pullback of `(mNk, pt)`
  -- (preserved by the stage inclusion) and `homInclObj_isIso_reflects`, to a stage factorization of
  -- `pt` through `mNk` — contradicting `hpt`.
  rintro ⟨y, hy⟩
  -- `m = homInclObj mNk` (modulo casts): combine `hmeq` (`m = castHom (homInclObj mNK)`) with the push.
  have hmeqk : castHom hcodXEk hcodXAk (homInclObj C hC mNk) = m := by
    rw [hmNk_push, castHom_castHom]
    simpa only [hcodXEk, hcodXAk] using hmeq
  -- pullback of `(mNk, pt)` at stage `k`; its `homInclObj`-image is a colimit pullback of `(m, point)`
  let P' := products_equalizers_implies_pullbacks mNk pt
  have hP'_colim := objIncl_preserves_pullbacks C hC ht htpres hp hppres hppres_pair he hepres
    hepres_lift k mNk pt
  -- the stage factorization, obtained by reflecting `IsIso (homInclObj P'.cone.π₂)` to the stage
  apply hpt
  -- transport the colimit factorization `y ≫ m = point` to `y' ≫ homInclObj mNk = homInclObj pt`
  have hyt : castHom hone.symm hcodXEk.symm y ≫ homInclObj C hC mNk = homInclObj C hC pt := by
    rw [← hmeqk] at hy
    have : castHom hone.symm hcodXEk.symm y ≫ homInclObj C hC mNk
        = castHom hone.symm hcodXAk.symm (y ≫ castHom hcodXEk hcodXAk (homInclObj C hC mNk)) := by
      rw [← castHom_comp hone.symm hcodXEk.symm hcodXAk.symm y
        (castHom hcodXEk hcodXAk (homInclObj C hC mNk)), castHom_castHom, castHom_rfl]
    rw [this, hy, castHom_castHom, castHom_rfl]
  -- `homInclObj mNk` mono + the colimit pullback ⇒ factorization ⇒ `IsIso (homInclObj P'.cone.π₂)`
  have hcolim_iso : @IsIso C.Obj (colimitCat C hC) _ _ (homInclObj C hC P'.cone.π₂) :=
    (factor_iff_pullback_π₂_iso hmk'
      (Cone.mk (f := homInclObj C hC mNk) (g := homInclObj C hC pt)
        (C.objIncl k P'.cone.pt) (homInclObj C hC P'.cone.π₁) (homInclObj C hC P'.cone.π₂)
        (by
          show colimComp C hC (homInclObj C hC P'.cone.π₁) (homInclObj C hC mNk)
            = colimComp C hC (homInclObj C hC P'.cone.π₂) (homInclObj C hC pt)
          rw [← homInclObj_comp C hC P'.cone.π₁ mNk, ← homInclObj_comp C hC P'.cone.π₂ pt,
            P'.cone.w]))
      hP'_colim).1 ⟨castHom hone.symm hcodXEk.symm y, hyt⟩
  -- reflect to the stage `IsIso P'.cone.π₂`, then the stage factor_iff gives the stage factorization
  have hstage_iso : IsIso P'.cone.π₂ := homInclObj_isIso_reflects C hC hcons P'.cone.π₂ hcolim_iso
  exact (factor_iff_pullback_π₂_iso hmNk_mono P'.cone P'.cone_isPullback).2 hstage_iso

/-! ## The outer ω-fixpoint: a cofinal points-acquiring tower has a capital colimit -/

/-- **Outer fixpoint, reduced to the per-object stage-pointing hypothesis.**  Given the cofinal
    points-acquiring successor `ccs` and the hypothesis `hstage` that every well-supported colimit
    object's representing stage object satisfies `StageRelCap` (def 1.545: each proper subobject of a
    later-stage pushforward is missed by a point at a still-later stage — this is precisely where
    `ccs.wellPoints` and the cofinal enumeration would be consumed — obstruction (1)+(2): each rung
    re-points everything), the ω-tower colimit is **capital**.  The conclusion is byte-for-byte the
    book's `Capital` (S1_52.lean) — no weakening.  Proven Sorry-free *on top of* `wellPointed_of_stage`:
    the residual is confined to that one lemma plus the explicit `hstage` premise (the cofinal-coverage
    obligation, not hidden in a `Sorry`). -/
public theorem tower_capital_of_cofinal
    (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    (ccs : CofinalCapStep.{u}) (b : PreRegBundle.{u})
    (ht : ∀ i, HasTerminal ((towerSystem b ccs.step).A i))
    (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
      (towerSystem b ccs.step).F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts ((towerSystem b ccs.step).A i))
    (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b ccs.step).A i)
      (z : (towerSystem b ccs.step).A j)
      (uu vv : z ⟶ (towerSystem b ccs.step).F hij ((hp i).prod a c)),
      uu ≫ (towerSystem b ccs.step).Fmap hij (hp i).fst =
        vv ≫ (towerSystem b ccs.step).Fmap hij (hp i).fst →
      uu ≫ (towerSystem b ccs.step).Fmap hij (hp i).snd =
        vv ≫ (towerSystem b ccs.step).Fmap hij (hp i).snd → uu = vv)
    (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b ccs.step).A i)
      (z : (towerSystem b ccs.step).A j)
      (p : z ⟶ (towerSystem b ccs.step).F hij a) (q : z ⟶ (towerSystem b ccs.step).F hij c),
      ∃ r : z ⟶ (towerSystem b ccs.step).F hij ((hp i).prod a c),
        r ≫ (towerSystem b ccs.step).Fmap hij (hp i).fst = p ∧
        r ≫ (towerSystem b ccs.step).Fmap hij (hp i).snd = q)
    (he : ∀ i, HasEqualizers ((towerSystem b ccs.step).A i))
    (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b ccs.step).A i}
      (f g : X ⟶ Y) (z : (towerSystem b ccs.step).A j)
      (uu vv : z ⟶ (towerSystem b ccs.step).F hij (eqObj f g)),
      uu ≫ (towerSystem b ccs.step).Fmap hij (eqMap f g) =
        vv ≫ (towerSystem b ccs.step).Fmap hij (eqMap f g) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b ccs.step).A i}
      (f g : X ⟶ Y) (z : (towerSystem b ccs.step).A j)
      (k : z ⟶ (towerSystem b ccs.step).F hij X)
      (_hk : k ≫ (towerSystem b ccs.step).Fmap hij f =
        k ≫ (towerSystem b ccs.step).Fmap hij g),
      ∃ r : z ⟶ (towerSystem b ccs.step).F hij (eqObj f g),
        r ≫ (towerSystem b ccs.step).Fmap hij (eqMap f g) = k)
    (hcanon : letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
        letI : HasPullbacks (towerSystem b ccs.step).Obj :=
          colimitHasPullbacks _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
        ∀ {X Y Z : (towerSystem b ccs.step).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hstage : ∀ (X : (towerSystem b ccs.step).Obj),
        letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
        letI : PreRegularCategory (towerSystem b ccs.step).Obj :=
          colimitPreRegular _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
        WellSupported X →
        StageRelCap (towerSystem b ccs.step) ht
          (colimOut (towerSystem b ccs.step) X).1 (colimOut (towerSystem b ccs.step) X).2) :
    letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
    letI : PreRegularCategory (towerSystem b ccs.step).Obj :=
      colimitPreRegular _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
        hepres hepres_lift hcanon
    Capital (𝒞 := (towerSystem b ccs.step).Obj) := by
  -- Every well-supported colimit object `X` is `objIncl n X₀` at its representing stage
  -- (`colimOut_spec`); `hstage` supplies well-pointedness of `X₀`'s pushforward at all later stages;
  -- `wellPointed_of_stage` carries it to the colimit.  The `colimOut_spec` rewrite identifies
  -- `objIncl n X₀` with `X`.
  intro X hXws
  -- `wellPointed_of_stage` at `X`'s representing stage gives `WellPointed (objIncl n X₀)`; rewrite the
  -- representative `objIncl n X₀ = X` (`colimOut_spec`) into the GOAL, then close with the lemma.
  rw [← colimOut_spec (towerSystem b ccs.step) X]
  exact wellPointed_of_stage (towerSystem b ccs.step) (towerCoherent b ccs.step)
    ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    (fun {i j} hij {x y} φ hiso => towerHcons b ccs.step hij φ hiso)
    (colimOut (towerSystem b ccs.step) X).1 (colimOut (towerSystem b ccs.step) X).2
    (hstage X hXws)

/-! ## Generic wiring: any cofinal directed system has a capital colimit

  The two declarations below are the verbatim generalizations of `tower_capital_of_cofinal` and
  `capData_of_tower` from the concrete ℕ `towerSystem` to an ARBITRARY coherent `CatSystem`.  They
  carry no new proof obligation beyond `wellPointed_of_stage` (already proven generically) plus the
  explicit `hstage` premise.  Their purpose is to isolate the single residual of §1.543 to one
  honest task — **exhibit a cofinal directed system** (an `ι`, `D`, `C`, base embedding, and the
  per-object stage-pointing witness `hstage`) — with no `Sorry` hidden in the colimit bookkeeping. -/

/-- **Generic outer fixpoint.**  For any coherent `CatSystem C` with the full `colimitPreRegular`
    preservation package and the two reflection hypotheses (`hcons`/`hmono`), if every well-supported
    colimit object's representing stage object stays well-pointed at all later stages (`hstage` — the
    cofinal-coverage obligation), the colimit category is **capital**.  Verbatim generalization of
    `tower_capital_of_cofinal`; the residual is confined to `wellPointed_of_stage` and the explicit
    `hstage` premise, isolating §1.543's gap to "construct a cofinal system". -/
theorem capital_of_cofinalSystem {ι : Type u} {D : Colim.Directed ι}
    (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent) [Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (uu vv : z ⟶ C.F hij ((hp i).prod a c)),
      uu ≫ (C.Fmap hij (hp i).fst) = vv ≫ (C.Fmap hij (hp i).fst) →
      uu ≫ (C.Fmap hij (hp i).snd) = vv ≫ (C.Fmap hij (hp i).snd) → uu = vv)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij c),
      ∃ r : z ⟶ C.F hij ((hp i).prod a c),
        r ≫ (C.Fmap hij (hp i).fst) = p ∧ r ≫ (C.Fmap hij (hp i).snd) = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (uu vv : z ⟶ C.F hij (eqObj f g)),
      uu ≫ (C.Fmap hij (eqMap f g)) = vv ≫ (C.Fmap hij (eqMap f g)) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (k : z ⟶ C.F hij X) (_hk : k ≫ (C.Fmap hij f) = k ≫ (C.Fmap hij g)),
      ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.Fmap hij (eqMap f g)) = k)
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        ∀ {X Y Z : C.Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    -- `_hmono` (stage push of monos) is part of the cofinal-system reflection package a caller
    -- supplies; the weakened `wellPointed_of_stage` no longer needs it (monos reflect from the colimit).
    (_hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    (hstage : ∀ (X : C.Obj),
        letI : Cat C.Obj := colimitCat C hC
        letI : PreRegularCategory C.Obj :=
          colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
        WellSupported X →
        StageRelCap C ht (colimOut C X).1 (colimOut C X).2) :
    letI : Cat C.Obj := colimitCat C hC
    letI : PreRegularCategory C.Obj :=
      colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    Capital (𝒞 := C.Obj) := by
  intro X hXws
  rw [← colimOut_spec C X]
  exact wellPointed_of_stage C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    hcons (colimOut C X).1 (colimOut C X).2 (hstage X hXws)

/-- **Generic `CapData` assembly.**  Packages a base stage `i₀`, a faithful start `A → C.A i₀`, the
    transition faithfulness/conservativity, the preservation package, and the generic capital colimit
    (`capital_of_cofinalSystem`) into the `CapData A` the §1.543 reduction
    (`capitalization_of_capData`) consumes.  Verbatim generalization of `capData_of_tower` to an
    arbitrary cofinal directed system; the only remaining input is exhibiting such a system together
    with its stage-pointing witness `hstage`. -/
theorem capData_of_cofinalSystem (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    {ι : Type u} {D : Colim.Directed ι} (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent)
    [hne : Nonempty ι] (i₀ : ι) (base : A → C.A i₀)
    (baseFun : @Functor A (C.A i₀) _ (C.catA i₀))
    (baseFaithful : @Faithful A _ (C.A i₀) (C.catA i₀) baseFun)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
      C.Fmap hij p = C.Fmap hij q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (uu vv : z ⟶ C.F hij ((hp i).prod a c)),
      uu ≫ (C.Fmap hij (hp i).fst) = vv ≫ (C.Fmap hij (hp i).fst) →
      uu ≫ (C.Fmap hij (hp i).snd) = vv ≫ (C.Fmap hij (hp i).snd) → uu = vv)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij c),
      ∃ r : z ⟶ C.F hij ((hp i).prod a c),
        r ≫ (C.Fmap hij (hp i).fst) = p ∧ r ≫ (C.Fmap hij (hp i).snd) = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (uu vv : z ⟶ C.F hij (eqObj f g)),
      uu ≫ (C.Fmap hij (eqMap f g)) = vv ≫ (C.Fmap hij (eqMap f g)) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (k : z ⟶ C.F hij X) (_hk : k ≫ (C.Fmap hij f) = k ≫ (C.Fmap hij g)),
      ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.Fmap hij (eqMap f g)) = k)
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        ∀ {X Y Z : C.Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hstage : ∀ (X : C.Obj),
        letI : Cat C.Obj := colimitCat C hC
        letI : PreRegularCategory C.Obj :=
          colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
        WellSupported X →
        StageRelCap C ht (colimOut C X).1 (colimOut C X).2) :
    Nonempty (CapData.{u} A) :=
  ⟨{ ι := ι, D := D, C := C, hC := hC, hne := hne, i₀ := i₀
     base := base, baseFun := baseFun, baseFaithful := baseFaithful
     hfaith := hfaith, hcons := hcons
     ht := ht, htpres := htpres, hp := hp, hppres := hppres, hppres_pair := hppres_pair
     he := he, hepres := hepres, hepres_lift := hepres_lift, hcanon := hcanon
     capital := capital_of_cofinalSystem C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
       hcanon hcons hmono hstage }⟩

/-- **§1.543 generic regular capitalization (the `hi`-threaded entry point).**  Same cofinal-system
    data as `capData_of_cofinalSystem`, but with TWO additional regular ingredients —
      * `hi`       : every stage `C.A i` HAS IMAGES (the *regular*, not merely pre-regular, structure
                     of the stages — `CapStep.stepImages` for the §1.547 successor stages);
      * `hcovpres` : the transitions PRESERVE COVERS (`PreservesCovers`) —
    it produces a genuine `RegularCategory Ā` (= pre-regular + `HasImages`), still capital and with the
    faithful `A → Ā`.  This is exactly the §2.218 R3(a) discharge: a `CapData` whose colimit has images
    (`Colim.colimitHasImages`, transition image-preservation *derived* from `hmono`+`hcovpres` via
    `capitalization_of_capData_regular_of_covers`).  The `hi` is the last structural ingredient that
    upgrades the capital target from pre-regular to regular; it is threaded HERE at the generic
    cofinal-system level (every concrete tower supplies it from its per-stage `stepImages`). -/
theorem capitalization_regular_of_cofinalSystem (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    {ι : Type u} {D : Colim.Directed ι} (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent)
    [hne : Nonempty ι] (i₀ : ι) (base : A → C.A i₀)
    (baseFun : @Functor A (C.A i₀) _ (C.catA i₀))
    (baseFaithful : @Faithful A _ (C.A i₀) (C.catA i₀) baseFun)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
      C.Fmap hij p = C.Fmap hij q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    (hcovpres : ∀ {i j : ι} (hij : D.le i j),
        @PreservesCovers _ _ (C.catA i) (C.catA j) (C.functF hij))
    (hi : ∀ i, @HasImages (C.A i) (C.catA i))
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hppres : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (uu vv : z ⟶ C.F hij ((hp i).prod a c)),
      uu ≫ (C.Fmap hij (hp i).fst) = vv ≫ (C.Fmap hij (hp i).fst) →
      uu ≫ (C.Fmap hij (hp i).snd) = vv ≫ (C.Fmap hij (hp i).snd) → uu = vv)
    (hppres_pair : ∀ {i j} (hij : D.le i j) (a c : C.A i) (z : C.A j)
      (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij c),
      ∃ r : z ⟶ C.F hij ((hp i).prod a c),
        r ≫ (C.Fmap hij (hp i).fst) = p ∧ r ≫ (C.Fmap hij (hp i).snd) = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (uu vv : z ⟶ C.F hij (eqObj f g)),
      uu ≫ (C.Fmap hij (eqMap f g)) = vv ≫ (C.Fmap hij (eqMap f g)) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {X Y : C.A i} (f g : X ⟶ Y) (z : C.A j)
      (k : z ⟶ C.F hij X) (_hk : k ≫ (C.Fmap hij f) = k ≫ (C.Fmap hij g)),
      ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.Fmap hij (eqMap f g)) = k)
    (hcanon : letI : Cat C.Obj := colimitCat C hC
        letI : HasPullbacks C.Obj :=
          colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        ∀ {X Y Z : C.Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
            Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hstage : ∀ (X : C.Obj),
        letI : Cat C.Obj := colimitCat C hC
        letI : PreRegularCategory C.Obj :=
          colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
        WellSupported X →
        StageRelCap C ht (colimOut C X).1 (colimOut C X).2) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hR : RegularCategory Ā),
      @Capital.{u, u} Ā hC (hR.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  -- Build the pre-regular `CapData` AS A RECORD LITERAL (not via `capData_of_cofinalSystem`'s
  -- `Nonempty`), so its `.ι`/`.D`/`.C` fields are DEFINITIONALLY `ι`/`D`/`C`; this lets `hi`/`hmono`/
  -- `hcovpres` (stated over `C`) land directly into the regular reduction without a transport.
  letI cd : CapData.{u} A :=
    { ι := ι, D := D, C := C, hC := hC, hne := hne, i₀ := i₀
      base := base, baseFun := baseFun, baseFaithful := baseFaithful
      hfaith := hfaith, hcons := hcons
      ht := ht, htpres := htpres, hp := hp, hppres := hppres, hppres_pair := hppres_pair
      he := he, hepres := hepres, hepres_lift := hepres_lift, hcanon := hcanon
      capital := capital_of_cofinalSystem C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
        hcanon hcons hmono hstage }
  -- `cd.C ≡ C` definitionally, so `hi`/`hmono`/`hcovpres` over `C` ARE the per-`cd` ingredients the
  -- regular reduction consumes (`capitalization_of_capData_regular_of_covers` derives transition
  -- image-preservation from cover+mono preservation via `Colim.transitions_preserve_images`).
  exact capitalization_of_capData_regular_of_covers cd hi
    (fun {i j} hij {x y} {φ} hφ => hmono hij φ hφ)
    (fun {i j} hij {x y} f hf => hcovpres hij f hf)

end Freyd
