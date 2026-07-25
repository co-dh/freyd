import Freyd.S1_543_CapitalizationTransfinite
import Freyd.S1_51
import Freyd.S1_41

/-! # §1.543 — the `hstage` bridge: `StepWellPoints` ⟹ `StageRelCap`

  `tower_capital_of_cofinal` (CapitalizationTransfinite.lean) and `capData_of_cofinalSystem` consume
  an `hstage` premise — for every well-supported colimit object `X`, the stage representative
  `(colimOut X).2` satisfies Freyd's RELATIVE-CAP condition `StageRelCap` (def 1.545).  That premise
  is exactly where a `CofinalCapStep`'s points-acquisition data `wellPoints : ∀ S, StepWellPoints
  (step S)` is meant to be consumed.  This file builds the missing derivation

      `hstage_of_cofinal : ∀ X, WellSupported X → StageRelCap (towerSystem b ccs.step) ht … …`

  from `ccs.wellPoints`.  The mathematical content is entirely in `wellPoints`; the rest is the
  cover / point survival bookkeeping through the ω-tower's difference-recursion casts:

  * `wellSupported_step` — a `CapStep` sends well-supported objects to well-supported objects (it
    preserves covers `stepCover` and the terminal, so `term (step A) = step (term A) ≫ iso`).
  * `wellSupported_transN` / `wellSupported_pushforward` — iterate that through the tower transition
    `C.F hij` (a `stageCast` of the difference functor `transN`).
  * `wellSupported_stage_of_colim` — descend a colimit object's well-supportedness to its stage
    representative (cover reflects via `homInclObj_cover_reflects`; the colimit terminal is the
    stage-terminal inclusion, `colimTerminalAtStage`).
  * `stageRelCap_succ_of_wellPointed` — the core: at the single successor `j → j+1`, push the proper
    mono `m'` (`stepMono`; properness reflected by `stepFaithful`'s reflects-iso half), apply
    `WellPointed (ccs.step Z)`, and transport the missing point into the `StageRelCap` shape (k=j+1).

  Mathlib-free; the only choice principle is `Classical.choice`, already pervasive in the colimit
  layer (`colimTerminalAtStage` / `objIncl_terminal_eq`). -/

namespace Freyd

open Colim

universe u

/-! ## Cover / well-supportedness survival through a single `CapStep` -/

/-- `WellSupported` does not depend on which terminal is chosen (terminals are uniquely isomorphic,
    and `term A` to either one differs by that iso, which cover-composition absorbs). -/
theorem wellSupported_terminal_invariant {𝒞 : Type u} [Cat.{u} 𝒞] (h1 h2 : HasTerminal 𝒞) {A : 𝒞}
    (hws : @WellSupported _ _ h1 A) : @WellSupported _ _ h2 A := by
  have hterm : h2.trm A = h1.trm A ≫ h2.trm h1.one := h2.uniq _ _
  show Cover (h2.trm A); rw [hterm]
  obtain ⟨einv, hee, heinv⟩ :=
    (⟨h1.trm h2.one, h1.uniq _ _, h2.uniq _ _⟩ : @IsIso _ _ h1.one h2.one (h2.trm h1.one))
  intro C m g hm hgm
  have hmono' : Monic (m ≫ einv) := by
    intro W a c hac; apply hm
    have hc : (a ≫ m ≫ einv) ≫ h2.trm h1.one = (c ≫ m ≫ einv) ≫ h2.trm h1.one := by rw [hac]
    calc a ≫ m = a ≫ m ≫ (einv ≫ h2.trm h1.one) := by rw [heinv, Cat.comp_id]
      _ = (a ≫ m ≫ einv) ≫ h2.trm h1.one := by rw [Cat.assoc, Cat.assoc]
      _ = (c ≫ m ≫ einv) ≫ h2.trm h1.one := hc
      _ = c ≫ m ≫ (einv ≫ h2.trm h1.one) := by rw [Cat.assoc, Cat.assoc]
      _ = c ≫ m := by rw [heinv, Cat.comp_id]
  have hfact : g ≫ (m ≫ einv) = h1.trm A := h1.uniq _ _
  have hmiso : IsIso (m ≫ einv) := hws (m ≫ einv) g hmono' hfact
  have hmeq : m = (m ≫ einv) ≫ h2.trm h1.one := by rw [Cat.assoc, heinv, Cat.comp_id]
  rw [hmeq]; exact isIso_comp hmiso ⟨einv, hee, heinv⟩

/-- `WellPointed` does not depend on which terminal is chosen: a point at `h2.one` transports to a
    point at `h1.one` by pre-composing with the terminal iso, and a factorization back. -/
theorem wellPointed_terminal_invariant {𝒞 : Type u} [Cat.{u} 𝒞] (h1 h2 : HasTerminal 𝒞) {A : 𝒞}
    (hwp : @WellPointed _ _ h1 A) : @WellPointed _ _ h2 A := by
  intro Dd m hm hniso
  obtain ⟨x, hx⟩ := hwp m hm hniso
  refine ⟨h1.trm h2.one ≫ x, ?_⟩
  rintro ⟨y, hy⟩
  refine hx ⟨h2.trm h1.one ≫ y, ?_⟩
  have hid : h2.trm h1.one ≫ h1.trm h2.one = Cat.id h1.one := h1.uniq _ _
  calc (h2.trm h1.one ≫ y) ≫ m = h2.trm h1.one ≫ (y ≫ m) := Cat.assoc _ _ _
    _ = h2.trm h1.one ≫ (h1.trm h2.one ≫ x) := by rw [hy]
    _ = (h2.trm h1.one ≫ h1.trm h2.one) ≫ x := (Cat.assoc _ _ _).symm
    _ = Cat.id h1.one ≫ x := by rw [hid]
    _ = x := Cat.id_comp x

/-- **A `CapStep` preserves well-supportedness.**  `term (step A) : step A ⟶ 1_T`.  `step (term A)`
    is a cover (`stepCover`, since `term A` is one); `step 1` is terminal in `T` (`stepTerminal` +
    `stepTerminalArrow`), so `term (step A) = step (term A) ≫ iso` and cover ∘ iso is a cover. -/
theorem wellSupported_step {S : Type u} [Cat.{u} S] [PreRegularCategory S]
    (st : CapStep S) {A : S} (hws : WellSupported A) :
    letI : Cat st.T := st.catT
    letI : PreRegularCategory st.T := st.preT
    WellSupported (st.stepFun.obj A) := by
  letI : Cat st.T := st.catT
  letI : PreRegularCategory st.T := st.preT
  have hcov : Cover (st.stepFun.map (term A)) := st.stepCover (term A) hws
  have hiso : IsIso (term (st.stepFun.obj (HasTerminal.one)) : st.stepFun.obj HasTerminal.one ⟶ HasTerminal.one) :=
    ⟨st.stepTerminalArrow HasTerminal.one, st.stepTerminal _ _ _, term_uniq _ _⟩
  have hterm_eq : term (st.stepFun.obj A)
      = st.stepFun.map (term A) ≫ (term (st.stepFun.obj HasTerminal.one)) := term_uniq _ _
  show Cover (term (st.stepFun.obj A))
  rw [hterm_eq]; exact cover_comp_iso_cat hcov hiso

/-- Well-supportedness survives the difference recursion `transN n d` (a composite of `d` rungs,
    each preserving it by `wellSupported_step`).  Stated against each stage's bundled terminal. -/
theorem wellSupported_transN (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u}) (n : Nat) :
    ∀ (d : Nat) (A : (stageBundle ccs.step b n).carrier)
      (_hws : @WellSupported _ (stageBundle ccs.step b n).cat
        (stageBundle ccs.step b n).pre.toHasTerminal A),
      @WellSupported _ (stageBundle ccs.step b (n+d)).cat
        (stageBundle ccs.step b (n+d)).pre.toHasTerminal (transN ccs.step b n d A)
  | 0, _, hws => hws
  | (d+1), A, hws =>
    wellSupported_step (ccs.step (stageBundle ccs.step b (n+d)))
      (wellSupported_transN b ccs n d A hws)

/-- Well-supportedness transports across the stage-carrier cast `stageCast` (carriers are literally
    equal once `m = n`). -/
theorem wellSupported_stageCast (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u}) {m n : Nat}
    (h : m = n) (A : (stageBundle ccs.step b m).carrier)
    (hws : @WellSupported _ (stageBundle ccs.step b m).cat
      (stageBundle ccs.step b m).pre.toHasTerminal A) :
    @WellSupported _ (stageBundle ccs.step b n).cat (stageBundle ccs.step b n).pre.toHasTerminal
      (stageCast b ccs.step h A) := by
  subst h; exact hws

/-- **The tower pushforward `C.F hij A₀` is well-supported** (each stage's bundled terminal), from
    `A₀` well-supported at stage `i`.  `C.F hij` is `stageCast` of `transN`, so combine
    `wellSupported_transN` and `wellSupported_stageCast`. -/
theorem wellSupported_pushforward (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u})
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) (A₀ : (towerSystem b ccs.step).A i)
    (hws : @WellSupported _ (stageBundle ccs.step b i.down).cat
      (stageBundle ccs.step b i.down).pre.toHasTerminal A₀) :
    @WellSupported _ (stageBundle ccs.step b j.down).cat
      (stageBundle ccs.step b j.down).pre.toHasTerminal ((towerSystem b ccs.step).F hij A₀) := by
  have hij' : i.down ≤ j.down := hij
  have heq : (towerSystem b ccs.step).F hij A₀
      = stageCast b ccs.step (Nat.add_sub_cancel' hij')
          (transN ccs.step b i.down (j.down - i.down) A₀) := rfl
  rw [heq]
  show @WellSupported _ _ _ (stageCast b ccs.step (Nat.add_sub_cancel' hij') _)
  exact wellSupported_stageCast b ccs (Nat.add_sub_cancel' hij') _
    (wellSupported_transN b ccs i.down (j.down - i.down) A₀ hws)

/-! ## Descending a colimit object's well-supportedness to its stage representative -/

/-- A `HasTerminal` on the colimit whose chosen `.one` is the stage-`n` terminal's inclusion
    `objIncl n (ht n).one` (a genuine colimit terminal by `objIncl_terminal_eq`).  Used so the
    colimit `term` of `objIncl n A₀` is, by uniqueness, the inclusion `homInclObj (term A₀)`, whose
    cover reflects to a stage cover. -/
noncomputable def colimTerminalAtStage {ι : Type u} {D : Colim.Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one) (n : ι) :
    letI : Cat C.Obj := colimitCat C hC
    HasTerminal C.Obj := by
  letI : Cat C.Obj := colimitCat C hC
  letI htCol : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  have heq : C.objIncl n (ht n).one = htCol.one :=
    objIncl_terminal_eq C hC ht htpres n (Classical.choice hne)
  refine @HasTerminal.mk C.Obj _ (C.objIncl n (ht n).one)
    (fun X => htCol.trm X ≫ (heq ▸ (Cat.id htCol.one : htCol.one ⟶ htCol.one))) ?_
  intro X; rw [heq]; exact fun f g => htCol.uniq f g

/-- **Descent of well-supportedness.**  If the colimit object `objIncl n A₀` is well-supported (over
    `colimitHasTerminal`), so is its stage representative `A₀` (over `ht n`).  The colimit `term` of
    `objIncl n A₀` is the inclusion `homInclObj (term A₀)` (uniqueness into the colimit terminal,
    which is `objIncl n (ht n).one` by `colimTerminalAtStage`); its cover reflects to a stage cover
    of `term A₀` (`homInclObj_cover_reflects`, transitions conservative `hcons` / mono-preserving
    `hmono`). -/
theorem wellSupported_stage_of_colim {ι : Type u} {D : Colim.Directed ι}
    (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    (n : ι) (A₀ : C.A n)
    (hwsCol : letI : Cat C.Obj := colimitCat C hC
      @WellSupported C.Obj (colimitCat C hC) (colimitHasTerminal C hC ht htpres)
        (C.objIncl n A₀)) :
    @WellSupported (C.A n) (C.catA n) (ht n) A₀ := by
  letI : Cat C.Obj := colimitCat C hC
  letI htCol : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  letI htStage : HasTerminal C.Obj := colimTerminalAtStage C hC ht htpres n
  letI : HasTerminal (C.A n) := ht n
  have hwsStage : @WellSupported C.Obj _ htStage (C.objIncl n A₀) :=
    wellSupported_terminal_invariant htCol htStage hwsCol
  show Cover (term A₀)
  refine homInclObj_cover_reflects C hC hcons hmono (term A₀) ?_
  intro Cc m g hm hgm
  exact hwsStage m g hm (hgm.trans (htStage.uniq _ _))

/-! ## The single-successor relative-cap step -/

/-- The tower transition at a successor `j → j+1` is, on objects, the rung `stageStep j = ccs.step`
    (modulo the difference cast `j.down + (j+1-j) = j+1`, dropped via `eq_of_heq`). -/
theorem towerF_succ_eq (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u}) (j : Nat)
    (z : (towerSystem b ccs.step).A ⟨j⟩) :
    (towerSystem b ccs.step).F
        (show uliftNatDirected.le (⟨j⟩ : ULift Nat) ⟨j+1⟩ from Nat.le_succ j) z
      = stageStep ccs.step b j z := by
  apply eq_of_heq
  show HEq (towerF b ccs.step (Nat.le_succ j) z) _
  unfold towerF
  have hgen : ∀ {m n : Nat} (h : m = n) (w : (stageBundle ccs.step b m).carrier),
      HEq (h ▸ w : (stageBundle ccs.step b n).carrier) w := by intro m n h w; subst h; rfl
  refine HEq.trans (hgen _ _) ?_
  show HEq (transN ccs.step b j ((j+1) - j) z) _
  have he : (j+1) - j = 1 := by omega
  rw [he]
  show HEq (stageStep ccs.step b (j+0) (transN ccs.step b j 0 z)) _
  rfl

/-- The tower transition at a successor `j → j+1` is, on morphisms, the rung `ccs.step.stepFun.map`
    (HEq, since endpoints differ by `towerF_succ_eq`). -/
theorem towerFunctF_succ_map_heq (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u}) (j : Nat)
    {x y : (towerSystem b ccs.step).A ⟨j⟩} (g : x ⟶ y) :
    HEq ((towerSystem b ccs.step).Fmap
          (show uliftNatDirected.le (⟨j⟩ : ULift Nat) ⟨j+1⟩ from Nat.le_succ j) g)
      (@Functor.map _ _ (stageBundle ccs.step b j).cat
        (ccs.step (stageBundle ccs.step b j)).catT
        (ccs.step (stageBundle ccs.step b j)).stepFun _ _ g) := by
  show HEq (towerFmap b ccs.step (Nat.le_succ j) g) _
  unfold towerFmap
  refine (stageCastHom_heq b ccs.step _ _).trans ?_
  show HEq ((transNFun ccs.step b j ((j+1)-j)).map g) _
  have he : (j+1) - j = 1 := by omega
  rw [he]
  rfl

/-- **Core successor step.**  From `WellPointed (ccs.step Z)` (the data `ccs.wellPoints` provides for
    a well-supported `Z` at stage `j`), produce the `StageRelCap` witness at `k = j+1` for any proper
    mono `m' : E' ⟶ Z`: push `m'` to stage `j+1` (`stepMono`; properness reflected by
    `stepFaithful`'s reflects-iso half), apply `WellPointed` to get a missing point, and transport it
    (terminal-invariance + `towerF_succ_eq`/`towerFunctF_succ_map_heq` casts) into the goal shape. -/
theorem stageRelCap_succ_of_wellPointed (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u})
    (ht : ∀ i, HasTerminal ((towerSystem b ccs.step).A i)) (j : Nat)
    (Z : (towerSystem b ccs.step).A ⟨j⟩)
    (hwp : @WellPointed _ (ccs.step (stageBundle ccs.step b j)).catT
        (ccs.step (stageBundle ccs.step b j)).preT.toHasTerminal
        (@Functor.obj _ _ (stageBundle ccs.step b j).cat
          (ccs.step (stageBundle ccs.step b j)).catT
          (ccs.step (stageBundle ccs.step b j)).stepFun Z))
    {E' : (towerSystem b ccs.step).A ⟨j⟩} (m' : E' ⟶ Z)
    (hmono : @Monic _ (stageBundle ccs.step b j).cat _ _ m')
    (hniso : ¬ @IsIso _ (stageBundle ccs.step b j).cat _ _ m') :
    ∃ (pt : @HasTerminal.one _ ((towerSystem b ccs.step).catA ⟨j+1⟩) (ht ⟨j+1⟩)
        ⟶ (towerSystem b ccs.step).F
            (show uliftNatDirected.le (⟨j⟩ : ULift Nat) ⟨j+1⟩ from Nat.le_succ j) Z),
      ¬ ∃ y, y ≫ (towerSystem b ccs.step).Fmap
        (show uliftNatDirected.le (⟨j⟩ : ULift Nat) ⟨j+1⟩ from Nat.le_succ j) m' = pt := by
  letI := (stageBundle ccs.step b j).cat
  letI : Cat (ccs.step (stageBundle ccs.step b j)).T := (ccs.step (stageBundle ccs.step b j)).catT
  have hjk : uliftNatDirected.le (⟨j⟩ : ULift Nat) ⟨j+1⟩ := Nat.le_succ j
  have hsm : @Monic _ (ccs.step (stageBundle ccs.step b j)).catT _ _
      ((ccs.step (stageBundle ccs.step b j)).stepFun.map m') :=
    (ccs.step (stageBundle ccs.step b j)).stepMono m' hmono
  have hsniso : ¬ @IsIso _ (ccs.step (stageBundle ccs.step b j)).catT _ _
      ((ccs.step (stageBundle ccs.step b j)).stepFun.map m') :=
    fun h => hniso ((ccs.step (stageBundle ccs.step b j)).stepFaithful.2 m' h)
  -- transport `WellPointed` to the goal's terminal `ht ⟨j+1⟩` (defeq category) and extract a point
  have hwp' : @WellPointed _ ((towerSystem b ccs.step).catA ⟨j+1⟩) (ht ⟨j+1⟩)
      ((ccs.step (stageBundle ccs.step b j)).stepFun.obj Z) :=
    wellPointed_terminal_invariant _ (ht ⟨j+1⟩) hwp
  obtain ⟨pt0, hpt0⟩ := hwp' ((ccs.step (stageBundle ccs.step b j)).stepFun.map m') hsm hsniso
  have heqZ : (towerSystem b ccs.step).F hjk Z =
      (ccs.step (stageBundle ccs.step b j)).stepFun.obj Z :=
    towerF_succ_eq b ccs j Z
  have heqE : (towerSystem b ccs.step).F hjk E' =
      (ccs.step (stageBundle ccs.step b j)).stepFun.obj E' :=
    towerF_succ_eq b ccs j E'
  have hmapeq : castHom heqE heqZ ((towerSystem b ccs.step).Fmap hjk m')
      = (ccs.step (stageBundle ccs.step b j)).stepFun.map m' :=
    castHom_of_heq heqE heqZ (towerFunctF_succ_map_heq b ccs j m')
  refine ⟨castHom rfl heqZ.symm pt0, ?_⟩
  rintro ⟨y, hy⟩
  apply hpt0
  refine ⟨castHom rfl heqE y, ?_⟩
  rw [← hmapeq, castHom_comp, hy, castHom_castHom, castHom_rfl]

/-! ## The `hstage` bridge -/

/-- **`hstage` from `CofinalCapStep`.**  The exact `StageRelCap` premise that
    `tower_capital_of_cofinal` / `capData_of_cofinalSystem` consume, derived from `ccs.wellPoints`.
    Given a well-supported colimit object `X`, its stage representative `A₀ = (colimOut X).2`
    satisfies relative-cap: for a later stage `j ≥ n` and a proper mono `m'` into the pushforward
    `C.F hnj A₀`, choose `k = j+1`.  The pushforward is well-supported (`wellSupported_pushforward`
    from the descent `wellSupported_stage_of_colim`), so `ccs.wellPoints` makes its successor image
    well-pointed; `stageRelCap_succ_of_wellPointed` then supplies the missing point.

    The hypothesis block is byte-for-byte the `hstage` premise at
    `CapitalizationTransfinite.tower_capital_of_cofinal` (lines 439-446); this lemma discharges it. -/
theorem hstage_of_cofinal (b : PreRegBundle.{u}) (ccs : CofinalCapStep.{u})
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
            Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    ∀ (X : (towerSystem b ccs.step).Obj),
        letI : Cat (towerSystem b ccs.step).Obj := colimitCat _ (towerCoherent b ccs.step)
        letI : PreRegularCategory (towerSystem b ccs.step).Obj :=
          colimitPreRegular _ (towerCoherent b ccs.step) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
        WellSupported X →
        StageRelCap (towerSystem b ccs.step) ht
          (colimOut (towerSystem b ccs.step) X).1 (colimOut (towerSystem b ccs.step) X).2 := by
  intro X hXws
  -- `A₀ := (colimOut X).2` at stage `n := (colimOut X).1`; `objIncl n A₀ = X` (`colimOut_spec`).
  -- `StageRelCap`: given `j ≥ n` and a proper stage-`j` mono `m'` into `C.F hnj A₀`.
  intro j hnj E' m' hm' hniso'
  -- Descend `WellSupported X` to `A₀` (stage `n`, `ht n`) via `wellSupported_stage_of_colim`
  -- (`colimOut_spec` identifies `X` with `objIncl n A₀`).
  have hwsA₀ : @WellSupported _ ((towerSystem b ccs.step).catA (colimOut (towerSystem b ccs.step) X).1)
      (ht (colimOut (towerSystem b ccs.step) X).1) (colimOut (towerSystem b ccs.step) X).2 := by
    refine wellSupported_stage_of_colim (towerSystem b ccs.step) (towerCoherent b ccs.step)
      ht htpres (fun {i j} hij {x y} φ h => towerHcons b ccs.step hij φ h)
      (fun {i j} hij {x y} φ h => towerHmono b ccs.step hij φ h)
      (colimOut (towerSystem b ccs.step) X).1 (colimOut (towerSystem b ccs.step) X).2 ?_
    rw [colimOut_spec (towerSystem b ccs.step) X]; exact hXws
  -- transport to the bundled terminal, then push forward to stage `j`
  have hwsA₀' : @WellSupported _
      (stageBundle ccs.step b (colimOut (towerSystem b ccs.step) X).1.down).cat
      (stageBundle ccs.step b (colimOut (towerSystem b ccs.step) X).1.down).pre.toHasTerminal
      (colimOut (towerSystem b ccs.step) X).2 :=
    wellSupported_terminal_invariant (ht (colimOut (towerSystem b ccs.step) X).1) _ hwsA₀
  have hwsZ : @WellSupported _ (stageBundle ccs.step b j.down).cat
      (stageBundle ccs.step b j.down).pre.toHasTerminal
      ((towerSystem b ccs.step).F hnj (colimOut (towerSystem b ccs.step) X).2) :=
    wellSupported_pushforward b ccs hnj (colimOut (towerSystem b ccs.step) X).2 hwsA₀'
  -- `ccs.wellPoints` makes the successor image well-pointed
  have hwp : @WellPointed _ (ccs.step (stageBundle ccs.step b j.down)).catT
      (ccs.step (stageBundle ccs.step b j.down)).preT.toHasTerminal
      (@Functor.obj _ _ (stageBundle ccs.step b j.down).cat
        (ccs.step (stageBundle ccs.step b j.down)).catT
        (ccs.step (stageBundle ccs.step b j.down)).stepFun
        ((towerSystem b ccs.step).F hnj (colimOut (towerSystem b ccs.step) X).2)) :=
    ccs.wellPoints (stageBundle ccs.step b j.down)
      ((towerSystem b ccs.step).F hnj (colimOut (towerSystem b ccs.step) X).2) hwsZ
  -- choose `k = j+1`; the successor step supplies the missing point
  refine ⟨⟨j.down + 1⟩, Nat.le_succ j.down, ?_⟩
  exact stageRelCap_succ_of_wellPointed b ccs ht j.down
    ((towerSystem b ccs.step).F hnj (colimOut (towerSystem b ccs.step) X).2) hwp m' hm' hniso'

end Freyd
