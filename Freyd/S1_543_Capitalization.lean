/-
  Freyd & Scedrov, *Categories and Allegories* §1.543  The CAPITALIZATION LEMMA.

  Every small pre-regular category `A` admits a FAITHFUL functor into a CAPITAL
  pre-regular category `Ā`.

  This file assembles the transfinite iteration from the pieces already built in
  the repo:

    * `S1_54.lean §1.544`  — one slice step `A → A/B` separates morphisms when `B`
      is well-supported (`slice_embedding_separates`).
    * `CatColimit.lean`    — directed colimit of categories (`CatSystem`, `Coherent`,
      `colimitCat`, `objIncl`, `homInclObj`).
    * `CatColimitRegular.lean` — the colimit of a coherent system of pre-regular
      categories is pre-regular (`colimitPreRegular`), faithfulness of the stage
      inclusion (`homInclObj_injective`), and cover reflection
      (`homInclObj_cover_reflects`, `colimHom_cover_reflects`).

  The construction is organised around the abstract successor-step interface
  `CapStep` (§1.545 relative capitalization, packaged), the directed system it
  generates (§1.543 iteration), the colimit (`colimitPreRegular`), and the capital
  closure argument (§1.543 fixpoint).

  CATEGORY THEORY stays on this repo's own `Cat`.  We deliberately do NOT import
  mathlib: the directed-colimit machinery in `CatColimit*` already supplies a
  `Directed`-indexed colimit, so the iteration is expressed over a hand-built
  directed index rather than mathlib ordinals.  (The §1.543 mathlib exception in
  CLAUDE.md is *available*, but mathlib is not a dependency of this repo and the
  colimit machinery is `Directed`-indexed, not ordinal-indexed, so importing it
  would buy nothing here.)

  STATUS.  The whole categorical assembly is now proved Sorry-free:

    * `faithful_comp`           — faithful functors compose to faithful functors.
    * `stageInclFaithful`       — the colimit stage-inclusion `A i → Ā` is faithful,
      given that every transition functor is faithful (via `homInclObj_injective`
      and `homInclObj_isIso_reflects`).
    * the ω-tower `CatSystem` itself: `towerSystem` (objects `towerObj`, transitions
      `towerF`/`towerFunctF`, with `F_refl`/`F_trans` the difference-cast bookkeeping)
      and its coherence `towerCoherent` — both `propext`/`Quot.sound`-only (constructive,
      no `Classical.choice`).  The Nat-difference casts are handled by the helpers
      `stageCast`/`stageCastHom`, `transN_add`, `transNFun_map_add`, and the carrier-equal
      congruence lemmas.
    * `capData_of_tower` — assembles a full `CapData A` from the tower plus the
      `colimitPreRegular` preservation package and the capital closure: `base = id`
      (stage 0 is `A`), `hfaith`/`hcons` from `transNFaithful` via `towerHfaith`/`towerHcons`.

  `capData_exists` is thereby reduced to the two genuine §1.543 ingredients, BOTH now
  discharged (downstream, in `Freyd/CapDataWiring.lean`, where the §1.547 uniform successor
  is reachable):
    (1) the uniform pre-regular-preserving successor `nextStep` (§1.544/§1.545 slice
        successor `A ↦ A*`, buildable from `overPreRegular`) together with the per-`i≤j`
        tower preservation package; and
    (2) the capital closure of the colimit (§1.543 fixpoint via `colimHom_cover_reflects`),
        over the colimit pre-regular structure that (1) supplies.
  §1.543 is now PROVEN: `Freyd.capitalization_lemma` / `Freyd.capData_exists` are
  Sorry-free (axioms `[propext, Classical.choice, Quot.sound]`).  The former in-place
  `capData_exists` body in this file (with its two `Sorry` walls) is RETAINED only as the
  big reference block comment below (around the `RELOCATED` marker), and is dead code.
-/

module

public import Freyd.S1_10
public import Freyd.S1_18
public import Freyd.S1_31
public import Freyd.S1_33
public import Freyd.S1_52
public import Freyd.S1_53_SliceRegular
public import Freyd.S1_543_CatColimit
public import Freyd.S2_154_SmallRegCat
public import Freyd.S1_543_CatColimitRegular
public import Freyd.S1_544_Inflation

open Freyd
open Freyd.Colim

universe v u

namespace Freyd

/-! ## Glue lemma: faithful functors compose

  `Faithful = Embedding ∧ reflects-iso` (§1.33).  Both properties compose, so a
  composite of faithful functors is faithful.  This is needed to thread the
  faithfulness of `A = A₀ → Ā` through the (finitely or transfinitely many)
  successor steps and the final colimit inclusion. -/

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟] {ℰ : Type u} [Cat.{v} ℰ]

/-- Faithful functors compose.  `embedding_comp` (§1.31) gives the embedding half;
    iso-reflection composes directly (`G` reflects iso, then `F` reflects iso). -/
public theorem faithful_comp {F : Functor 𝒞 𝒟} {G : Functor 𝒟 ℰ}
    (fF : Faithful F) (fG : Faithful G) : Faithful (compFunctor F G) := by
  refine ⟨embedding_comp fF.1 fG.1, ?_⟩
  intro A B f hiso
  -- `(G∘F).map f` iso ⟹ `F.map f` iso (G reflects) ⟹ `f` iso (F reflects).
  exact fF.2 f (fG.2 (F.map f) hiso)

end Freyd

/-! ## The colimit stage-inclusion is faithful

  This is the §1.543 step-5 ingredient: each injection `A i → Ā` of a stage into the
  transfinite colimit is faithful.  We work entirely with the existing
  `CatColimitRegular` API:

    * object part is `C.objIncl i`,
    * morphism part is `homInclObj C hC`,
    * functoriality is `homInclObj_comp`,
    * embedding (injectivity on homs) is `homInclObj_injective`,
    * iso-reflection is `homInclObj_consIso`.

  Both injectivity and iso-reflection are *conditional on the transitions being
  faithful* (`hfaith`) and `hcons`/`hmono`; those hypotheses hold in our iteration
  because every successor step is a faithful pre-regular embedding. -/

namespace Freyd.Colim

universe w

variable {ι : Type u} {D : Directed ι}

/-- The object part of the stage-`i` inclusion `A i → Ā`. -/
abbrev stageInclObj (C : CatSystem ι D) (i : ι) : C.A i → C.Obj := C.objIncl i

/-- **The stage inclusion sends identities to identities.**  Needed to package the
    stage inclusion `(objIncl i, homInclObj)` as an honest `Functor`.  Compute
    `homInclObj (Cat.id x)` at the canonical witness via `homInclObj_eq`; the germ is
    a `castHom` of `functF.map (Cat.id x) = Cat.id (...)`, which is the identity germ
    `colimId` of `objIncl i x` after absorbing the cast and transition. -/
public theorem homInclObj_id (C : CatSystem ι D) (hC : C.Coherent) {i : ι} (x : C.A i) :
    homInclObj C hC (Cat.id x) = colimId C hC (C.objIncl i x) := by
  let w := hioWitness C hC x x
  -- compute `homInclObj (id)` at the witness `w`; its germ is the identity at stage `w.K`.
  rw [homInclObj_eq C hC (Cat.id x) w]
  have hgerm : w.germ (Cat.id x) = Cat.id (C.F w.hpx (colimOut C (C.objIncl i x)).2) := by
    unfold HioWitness.germ
    rw [C.Fmap_id w.hix]
    exact castHom_of_heq _ _ (by rw [w.hgx])
  rw [hgerm]
  -- both sides are identity germs of the SAME hom-colimit `HomColim … (out).2 (out).2`;
  -- `colimId` is the id germ at the trivial bound `(out).1`, and `homIncl_compat` +
  -- `homTr_id` push it up to the bound `w.K`.
  unfold colimId homClassId
  have key := homIncl_compat C hC (colimOut C (C.objIncl i x)).2 (colimOut C (C.objIncl i x)).2
    (a := ⟨(colimOut C (C.objIncl i x)).1, D.refl _, D.refl _⟩)
    (b := ⟨w.K, w.hpx, w.hpx⟩) w.hpx (Cat.id _)
  rw [homTr_id] at key
  -- `key` is exactly the goal: the witness bound `⟨w.K, w.hpx, w.hpy⟩` and `⟨w.K, w.hpx, w.hpx⟩`
  -- coincide proof-irrelevantly, and the trivial bound `⟨(out).1, refl, refl⟩` is `colimId`.
  exact key


/-- **The stage inclusion `A i → Ā` is an honest `Functor`.**  Object part `objIncl i`,
    morphism part `homInclObj`, identity by `homInclObj_id`, composition by
    `homInclObj_comp`.  (The `colimitCat` instance on `C.Obj` is supplied via `letI`.) -/
@[expose] public noncomputable def stageInclFunctor (C : CatSystem ι D) (hC : C.Coherent) (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    Functor (C.A i) C.Obj :=
  letI : Cat C.Obj := colimitCat C hC
  { obj := C.objIncl i
    map := fun {_ _} g => homInclObj C hC g
    map_id := fun x => homInclObj_id C hC x
    map_comp := fun {_ _ _} g g' => homInclObj_comp C hC g g' }

/-- **§1.543 step 5 — the stage inclusion `A i → Ā` is FAITHFUL.**  Embedding half is
    `homInclObj_injective` (needs transitions faithful, `hfaith`); reflects-iso half is
    `homInclObj_isIso_reflects` (needs transitions conservative, `hcons`).  This is the
    fact that the colimit injection of a stage is faithful — directly usable for the
    composite `A = A₀ → Ā`. -/
public theorem stageInclFaithful (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        C.Fmap hij p = C.Fmap hij q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    Faithful (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := colimitCat C hC
  refine ⟨?_, ?_⟩
  · intro x y g g' h
    exact homInclObj_injective C hC hfaith g g' h
  · intro x y g hiso
    exact homInclObj_isIso_reflects C hC hcons g hiso

/-- **The stage terminal is the colimit terminal.**  For any two stages `i j`,
    `objIncl i (ht i).one = objIncl j (ht j).one`.  Both are carried to `objIncl k (ht k).one`
    at a common bound `k` (via `objIncl_compat` + the on-the-nose `htpres`). -/
public theorem objIncl_terminal_eq (C : CatSystem.{u, u} ι D) (_hC : C.Coherent)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one) (i j : ι) :
    C.objIncl i (ht i).one = C.objIncl j (ht j).one := by
  -- common bound `k ≥ i, j`; `objIncl k (ht k).one = objIncl k (F (ht i).one) = objIncl i (ht i).one`
  -- (and symmetrically for `j`), using `htpres : F (ht i).one = (ht k).one` and `objIncl_compat`.
  obtain ⟨k, hik, hjk⟩ := D.bound i j
  have hi : C.objIncl i (ht i).one = C.objIncl k (ht k).one := by
    rw [← htpres hik, C.objIncl_compat hik]
  have hj : C.objIncl j (ht j).one = C.objIncl k (ht k).one := by
    rw [← htpres hjk, C.objIncl_compat hjk]
  rw [hi, hj]

/-- **`objIncl i` preserves the terminal, as `PreservesTerminal`.**  The colimit terminal is
    `objIncl i₀ (ht i₀).one`; every stage terminal `objIncl i (ht i).one` equals it
    (`objIncl_terminal_eq`), so the colimit's terminal uniqueness `(colimitHasTerminal …).uniq`
    transports to give `PreservesTerminal (objIncl i)`. -/
theorem objIncl_preservesTerminal (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one) (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasTerminal (C.A i) := ht i
    letI : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
    PreservesTerminal (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := colimitCat C hC
  letI htiOne : HasTerminal (C.A i) := ht i
  letI htCol : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  -- `PreservesTerminal (objIncl i)` unfolds to `∀ X (f g : X ⟶ objIncl i one), f = g`.
  -- `objIncl i one = objIncl i (ht i).one = colimit terminal`, so the colimit's uniqueness applies
  -- after rewriting the codomain.
  intro X f g
  -- `objIncl i one` equals the colimit terminal `htCol.one`; abstract that target object so the
  -- substitution motive is well-formed, then close by the colimit's terminal uniqueness.
  suffices h : ∀ (T : C.Obj) (_ : T = htCol.one) (f g : X ⟶ T), f = g from
    h _ (objIncl_terminal_eq C hC ht htpres i (Classical.choice hne)) f g
  rintro T rfl f g
  exact htCol.uniq f g

/-- **`objIncl i` preserves binary products, as `PreservesBinaryProducts`.**  Repackage
    `objIncl_preserves_products` (the `IsIso (pair …)` fact) under the `stageInclFunctor`
    `Functor` instance so the §1.43/§1.437 machinery applies. -/
public theorem objIncl_preservesBinaryProducts (C : CatSystem.{u, u} ι D) (hC : C.Coherent)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ C.Fmap hij (hp i).fst = v ≫ C.Fmap hij (hp i).fst →
        u ≫ C.Fmap hij (hp i).snd = v ≫ C.Fmap hij (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ C.Fmap hij (hp i).fst = p ∧ r ≫ C.Fmap hij (hp i).snd = q)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasBinaryProducts (C.A i) := hp i
    letI : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hpres hpres_pair
    PreservesBinaryProducts (stageInclFunctor C hC i) :=
  fun {a b} => objIncl_preserves_products C hC hp hpres hpres_pair i a b

/-- **`objIncl i` preserves equalizers, as `PreservesEqualizers`.**  Convert the
    `EqualizerCone.IsEqualizer` form (`objIncl_preserves_equalizers`) to the comparison-map
    iso form `PreservesEqualizers` wants, via `isIso_of_two_equalizers` against the chosen
    equalizer of `(homInclObj f, homInclObj g)`. -/
public theorem objIncl_preservesEqualizers (C : CatSystem.{u, u} ι D) (hC : C.Coherent)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ C.Fmap hij (eqMap f g) = v ≫ C.Fmap hij (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_ : k ≫ C.Fmap hij f = k ≫ C.Fmap hij g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ C.Fmap hij (eqMap f g) = k)
    (i : ι) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasEqualizers (C.A i) := he i
    letI : HasEqualizers C.Obj := colimitHasEqualizers C hC he hepres hepres_lift
    PreservesEqualizers (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasEqualizers (C.A i) := he i
  letI : HasEqualizers C.Obj := colimitHasEqualizers C hC he hepres hepres_lift
  intro a b f g
  -- the image cone (objIncl(eqObj f g), homInclObj (eqMap f g)) is an equalizer (item (3))
  have himg := objIncl_preserves_equalizers C hC he hepres hepres_lift i f g
  -- the chosen equalizer comparison map `k` factors `homInclObj (eqMap f g)`; both are
  -- equalizers, so `k` is iso (`isIso_of_two_equalizers`).
  let eqD := HasEqualizers.eq (C.objIncl i a) (C.objIncl i b)
    (stageInclFunctor C hC i |>.map f) (stageInclFunctor C hC i |>.map g)
  exact isIso_of_two_equalizers himg (chosenEqualizer_isEqualizer _ _) _ (eqD.fac _)

/-- **`objIncl i` preserves pullbacks (M3-cov ingredient (3), assembled).**  The
    `objIncl i`-image of the §1.432 *stage* pullback of a cospan `(f, g)` in `C.A i` is a
    pullback cone in `colimitCat`.  Assembles `objIncl_preserves_products` and
    `objIncl_preserves_equalizers` (repackaged as `PreservesBinaryProducts` /
    `PreservesEqualizers` of `stageInclFunctor i`) through the generic
    `image_chosenPullback_isPullback`. -/
public theorem objIncl_preserves_pullbacks (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ C.Fmap hij (hp i).fst = v ≫ C.Fmap hij (hp i).fst →
        u ≫ C.Fmap hij (hp i).snd = v ≫ C.Fmap hij (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ C.Fmap hij (hp i).fst = p ∧ r ≫ C.Fmap hij (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ C.Fmap hij (eqMap f g) = v ≫ C.Fmap hij (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_ : k ≫ C.Fmap hij f = k ≫ C.Fmap hij g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ C.Fmap hij (eqMap f g) = k)
    (i : ι) {a b c : C.A i} (f : a ⟶ c) (g : b ⟶ c) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasTerminal (C.A i) := ht i
    letI : HasBinaryProducts (C.A i) := hp i
    letI : HasEqualizers (C.A i) := he i
    letI : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
    letI : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hpres hpres_pair
    letI : HasEqualizers C.Obj := colimitHasEqualizers C hC he hepres hepres_lift
    (Cone.mk (f := homInclObj C hC f) (g := homInclObj C hC g)
      (C.objIncl i (products_equalizers_implies_pullbacks f g).cone.pt)
      (homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₁)
      (homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₂)
      (by
          show colimComp C hC (homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₁)
              (homInclObj C hC f)
            = colimComp C hC (homInclObj C hC (products_equalizers_implies_pullbacks f g).cone.π₂)
              (homInclObj C hC g)
          rw [← homInclObj_comp C hC (products_equalizers_implies_pullbacks f g).cone.π₁ f,
              ← homInclObj_comp C hC (products_equalizers_implies_pullbacks f g).cone.π₂ g,
              (products_equalizers_implies_pullbacks f g).cone.w])).IsPullback := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal (C.A i) := ht i
  letI : HasBinaryProducts (C.A i) := hp i
  letI : HasEqualizers (C.A i) := he i
  letI : HasTerminal C.Obj := colimitHasTerminal C hC ht htpres
  letI : HasBinaryProducts C.Obj := colimitHasBinaryProducts C hC hp hpres hpres_pair
  letI : HasEqualizers C.Obj := colimitHasEqualizers C hC he hepres hepres_lift
  exact image_chosenPullback_isPullback (stageInclFunctor C hC i)
    (objIncl_preservesBinaryProducts C hC hp hpres hpres_pair i)
    (objIncl_preservesEqualizers C hC he hepres hepres_lift i) f g

-- The single `whnf` of the §1.432 chosen colimit pullback cone (cascading through
-- `colimitHasBinaryProducts`/`colimitHasEqualizers`) costs ~8s / well over the default heartbeat
-- budget; paying it ONCE here (the §1.543 elaboration-performance fix) keeps every downstream
-- `hcanon`-discharge cheap.
set_option maxHeartbeats 4000000 in
/-- **Generic `hcanon` discharge — the canonical colimit pullback's `π₂` is a cover.**

  Assembles the full M3-cov argument, eliminating the `hcanon` hypothesis of
  `colimitPreRegular`.  For a cospan `(f, g)` in `colimitCat` with `f` a cover:
    * align `(f, g)` to a genuine STAGE cospan `(fN, gN)` at a shared codomain stage `N`
      (`colimHom_cospan_as_homInclObj`), with `homInclObj fN ≅ f`, `homInclObj gN ≅ g`;
    * `f`'s cover REFLECTS to a stage cover of `fN` (`homInclObj_cover_reflects`, via the
      conservativity/mono hyps), transported across the HEq;
    * the §1.432 STAGE pullback `P = products_equalizers_implies_pullbacks fN gN` has `P.cone.π₂`
      a STAGE cover by the per-stage `PullbacksTransferCovers` hypothesis `hstagePTC`;
    * every later transition `functF hNL` PRESERVES that cover (`hcovpres`), so `homInclObj P.cone.π₂`
      is a COLIMIT cover (`homInclObj_cover_of_stage`);
    * the `objIncl N`-image of `P.cone` is a pullback of `(homInclObj fN, homInclObj gN)`
      (`objIncl_preserves_pullbacks`), hence — after the HEq identification — a WITNESS pullback cone
      of `(f, g)` whose `π₂` is a cover;
    * `canonicalPullback_cover_of_witness` upgrades this to the canonical pullback's `π₂`.

  The witness route uses only the `Cone.IsPullback` INTERFACE, never forcing `whnf` of the giant
  `colimitHasPullbacks` instance — that is the §1.543 elaboration-performance fix. -/
public theorem colimitCanonicalCover (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
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
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ C.Fmap hij (eqMap f g) = v ≫ C.Fmap hij (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_ : k ≫ C.Fmap hij f = k ≫ C.Fmap hij g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ C.Fmap hij (eqMap f g) = k)
    -- faithfulness / conservativity / mono-preservation of every transition (cover reflection)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        C.Fmap hij p = C.Fmap hij q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        IsIso (C.Fmap hij φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    -- per-stage `PullbacksTransferCovers` (the stages are pre-regular)
    (hstagePTC : ∀ (i : ι), letI : HasTerminal (C.A i) := ht i;
        letI : HasBinaryProducts (C.A i) := hp i; letI : HasEqualizers (C.A i) := he i;
        letI : HasPullbacks (C.A i) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩;
        PullbacksTransferCovers (C.A i))
    -- transition functors preserve covers
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Cover φ → Cover (C.Fmap hij φ)) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasPullbacks C.Obj :=
      colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
    ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ := by
  letI : Cat C.Obj := colimitCat C hC
  intro A B Z f g hf
  -- SEALED accessor: replace the goal's `(colimitHasPullbacks …).has f g` by
  -- `products_equalizers_implies_pullbacks f g` via the ALREADY-PROVEN equation — the `whnf` cost of
  -- the finite-limit cascade was paid ONCE in `colimitHasPullbacks_has` (the §1.543 perf fix), so this
  -- `rw` is cheap and the subsequent reasoning never re-forces it.
  rw [colimitHasPullbacks_has C hC ht htpres hp hppres hppres_pair he hepres hepres_lift f g]
  -- align `(f, g)` to a stage cospan `(fN, gN)` sharing codomain `xZ` at stage `N`
  obtain ⟨N, xA, xB, xZ, fN, gN, eA, eB, eZ, hfHEq, hgHEq⟩ :=
    colimHom_cospan_as_homInclObj C hC f g
  -- identify the colimit objects with the stage `objIncl`-images, turning the HEqs into Eqs
  subst eA; subst eB; subst eZ
  have hfeq : homInclObj C hC fN = f := eq_of_heq hfHEq
  have hgeq : homInclObj C hC gN = g := eq_of_heq hgHEq
  subst hfeq; subst hgeq
  -- `f = homInclObj fN` is a cover ⇒ `fN` is a STAGE cover (cover reflection)
  have hfN_cov : Cover fN := homInclObj_cover_reflects C hC hcons hmono fN hf
  -- the §1.432 stage pullback of `(fN, gN)`; its `π₂` is a stage cover by per-stage PTC
  letI : HasTerminal (C.A N) := ht N
  letI : HasBinaryProducts (C.A N) := hp N
  letI : HasEqualizers (C.A N) := he N
  letI hpullN : HasPullbacks (C.A N) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
  letI : PullbacksTransferCovers (C.A N) := hstagePTC N
  let P := products_equalizers_implies_pullbacks fN gN
  have hP2_cov : Cover P.cone.π₂ :=
    PullbacksTransferCovers.pullbacks_transfer_covers _ P.cone_isPullback hfN_cov
  -- lift the stage cover `P.cone.π₂` to a COLIMIT cover of its inclusion (cover-preservation)
  have hPincl_cov : @Cover C.Obj (colimitCat C hC) _ _ (homInclObj C hC P.cone.π₂) :=
    homInclObj_cover_of_stage C hC hfaith P.cone.π₂
      (fun {j} hNj => hcovpres hNj P.cone.π₂ hP2_cov)
  -- the `objIncl N`-image of `P.cone` is a pullback of `(homInclObj fN, homInclObj gN)`, a WITNESS
  -- cone whose `π₂ = homInclObj P.cone.π₂` carries the lifted cover.
  have hwit := objIncl_preserves_pullbacks C hC ht htpres hp hppres hppres_pair
    he hepres hepres_lift N fN gN
  -- the goal is `Cover (products_equalizers_implies_pullbacks (homInclObj fN) (homInclObj gN)).cone.π₂`
  -- — a NAMED `HasPullback` term (no instance synthesis, no cascade).  Compare its chosen cone to the
  -- WITNESS germ cone (`hwit`) and transport the lifted `π₂`-cover (`pullback_comparison_iso` +
  -- `cover_precomp_iso`).  (The single ~8s `whnf` of the §1.432 chosen cone is paid here.)
  intro D' m g hm hgm
  exact hasPullback_cover_of_witness _ hwit hPincl_cov m g hm hgm

end Freyd.Colim

/-! ## §1.543 The capitalization data, and the reduction to it

  We isolate everything the transfinite §1.543 construction must produce into a single
  structure `CapData A`.  It bundles a directed system of pre-regular categories whose
  colimit is the capitalization `Ā` of `A`:

    * the directed index and `CatSystem` `C`, its coherence `hC`, and nonemptiness;
    * a base index `i₀` and a faithful functor `base : A → A_{i₀}` (the start of the tower);
    * the full `colimitPreRegular` preservation package (terminal / products / equalizers /
      pullback-covers preserved by every transition) so the colimit is pre-regular;
    * the faithfulness data of the transitions (`hfaith`, `hcons`) so each stage injects
      faithfully into the colimit;
    * the capital proof for the colimit (`capital` — every well-supported object of `Ā`
      is well-pointed); this is the §1.543 fixpoint/closure conclusion.

  Given a `CapData A`, the capitalization lemma is immediate:
    * `Ā = C.Obj` with the `colimitCat` instance;
    * pre-regular by `colimitPreRegular`;
    * capital by the bundled proof;
    * the faithful functor `A → Ā` is `objIncl i₀ ∘ base`, faithful by `faithful_comp`
      of `base` (bundled faithful) with `stageInclFunctor i₀` (faithful by
      `stageInclFaithful`).

  The one thing this needed for a Sorry-free §1.543 was `capData_exists : ∀ A, CapData A` —
  the cofinal capitalizing tower and its capital-closure fixpoint.  That is now PROVEN
  Sorry-free in `Freyd/CapDataWiring.lean` (it had to live downstream, where the §1.547
  uniform successor is reachable), so `capitalization_lemma` — which reduces to it — is
  likewise proven (axioms `[propext, Classical.choice, Quot.sound]`). -/

namespace Freyd

open Freyd.Colim
open Freyd.S2_154

/-! ## §1.547 (B-package) — discharging `hcanon` for the inner `OrdChain`-slice colimit

  The generic bridge `Freyd.Colim.colimitCanonicalCover` proves the canonical-pullback cover transfer
  (`hcanon`) of the inner colimit `S*` from: the 8 limit-preservation hypotheses, the per-stage
  `PullbacksTransferCovers`, the transition cover-preservation, and the transition cover-reflection
  (faithful / conservative / mono-preserving).  For the concrete `ordChainSliceSystem` ALL of these are
  now in hand Sorry-free EXCEPT the cover-reflection pair `hfaith`/`hcons`:

    * `hmono`     = `ordChainHmono`        (Sorry-free, `Inflation`)
    * `hcovpres`  = `ordChainHcovpres`     (Sorry-free, `Inflation`; from `catMap_cover`, the
                    `catMap_isPullback` cover transfer)
    * `hstagePTC` = `ordChainStagePTC`     (Sorry-free, `Inflation`; `overPullbacksTransferCovers`)

  `hfaith`/`hcons` are the cover-REFLECTION half: the strict suffix-append transition `catMap d` is
  faithful / conservative iff the projection `catForget (X.dom) d : ∏(X.dom ++ d) ⟶ ∏X.dom` is epic, i.e.
  iff the appended suffix `∏d` is WELL-SUPPORTED — exactly the well-supportedness `§1.55`'s slice
  `sliceEmbedFaithful` requires, and which the relative-capitalization successor `nextStep` (`hwall_step`,
  still open) supplies for its chain but the BARE `OrdChain`/`PrefixChain` does not carry.  We therefore
  take `hfaith`/`hcons` as honest explicit hypotheses (NOT a `Sorry`): given them, `colimitCanonicalCover`
  discharges `hcanon` end-to-end. -/

/-- **Discharge of `hcanon` for `ordChainSliceSystem`**, modulo the cover-reflection pair `hfaith`/`hcons`
    (well-supported suffix).  Supplies the bridge `colimitCanonicalCover` with the Sorry-free per-stage PTC
    (`ordChainStagePTC`), transition cover-preservation (`ordChainHcovpres`) and mono-preservation
    (`ordChainHmono`), plus the 8 limit-preservation hypotheses already proven for the inner system. -/
theorem ordChainCanonicalCover {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]
    {ι : Type u} {D : Directed ι} (O : OrdChain D 𝒞) [Nonempty ι]
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : (ordChainSliceSystem O).A i} (p q : x ⟶ y),
        ((ordChainSliceSystem O).functF hij).map p = ((ordChainSliceSystem O).functF hij).map q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : (ordChainSliceSystem O).A i} (φ : x ⟶ y),
        IsIso (((ordChainSliceSystem O).functF hij).map φ) → IsIso φ) :
    letI : Cat (ordChainSliceSystem O).Obj := colimitCat _ (ordChainSliceCoherent O)
    letI : HasPullbacks (ordChainSliceSystem O).Obj :=
      colimitHasPullbacks _ (ordChainSliceCoherent O)
        (ordChainHasTerminal O) (ordChainHtpres O) (ordChainHasProducts O)
        (ordChainHppres O) (ordChainHppresPair O)
        (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
    ∀ {X Y Z : (ordChainSliceSystem O).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ :=
  colimitCanonicalCover (ordChainSliceSystem O) (ordChainSliceCoherent O)
    (ordChainHasTerminal O) (ordChainHtpres O) (ordChainHasProducts O)
    (ordChainHppres O) (ordChainHppresPair O)
    (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
    (fun {_ _} hij {_ _} p q h => hfaith hij p q h)
    (fun {_ _} hij {_ _} φ h => hcons hij φ h)
    (fun {_ _} hij {_ _} φ h => ordChainHmono O hij φ h)
    (fun i => ordChainStagePTC O i)
    (fun {_ _} hij {_ _} φ h => ordChainHcovpres O hij φ h)

/-- **`hcanon` discharge for the ℕ-chain `chainSliceSystem`** (the `uliftNatDirected` specialization),
    modulo the same well-supported-suffix cover-reflection pair.  Feeds directly into the protected
    `chainSlicePreRegular`. -/
theorem chainCanonicalCover {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]
    (P : PrefixChain 𝒞)
    (hfaith : ∀ {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
        {x y : (chainSliceSystem P).A i} (p q : x ⟶ y),
        ((chainSliceSystem P).functF hij).map p = ((chainSliceSystem P).functF hij).map q → p = q)
    (hcons : ∀ {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
        {x y : (chainSliceSystem P).A i} (φ : x ⟶ y),
        IsIso (((chainSliceSystem P).functF hij).map φ) → IsIso φ) :
    letI : Cat (chainSliceSystem P).Obj := colimitCat _ (chainSliceCoherent P)
    letI : HasPullbacks (chainSliceSystem P).Obj :=
      colimitHasPullbacks _ (chainSliceCoherent P)
        (chainHasTerminal P) (chainHtpres P) (chainHasProducts P)
        (chainHppres P) (chainHppresPair P)
        (chainHasEqualizers P) (chainHepres P) (chainHepresLift P)
    ∀ {X Y Z : (chainSliceSystem P).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ :=
  ordChainCanonicalCover P.toOrdChain hfaith hcons

/-- **`hcanon` discharge for the ℕ-chain, with the cover-reflection pair NOW SUPPLIED from a
    per-transition WELL-SUPPORTED-SUFFIX hypothesis** (§1.546 KEY UNLOCK).  The transition
    faithfulness / conservativity (`chainHfaith`/`chainHcons`) follow whenever every appended suffix
    product `∏(prefixSuffix (chain i) (chain j))` is well-supported — which, for the
    relative-capitalization chain whose appended objects ARE the well-supported `B`'s, holds.  This
    turns `chainCanonicalCover`'s two explicit `hfaith`/`hcons` hypotheses into the single, concrete,
    book-faithful precondition `hwsuf`. -/
theorem chainCanonicalCoverWS {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞] [HasEqualizers 𝒞]
    (P : PrefixChain 𝒞)
    (hwsuf : ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
        WellSupported
          (listProd (𝒞 := 𝒞) (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j)))) :
    letI : Cat (chainSliceSystem P).Obj := colimitCat _ (chainSliceCoherent P)
    letI : HasPullbacks (chainSliceSystem P).Obj :=
      colimitHasPullbacks _ (chainSliceCoherent P)
        (chainHasTerminal P) (chainHtpres P) (chainHasProducts P)
        (chainHppres P) (chainHppresPair P)
        (chainHasEqualizers P) (chainHepres P) (chainHepresLift P)
    ∀ {X Y Z : (chainSliceSystem P).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ :=
  chainCanonicalCover P
    (fun {_ _} hij {_ _} p q h => chainHfaith P hij (hwsuf hij) p q h)
    (fun {_ _} hij {_ _} φ hiso => chainHcons P hij (hwsuf hij) φ hiso)

/-- **§1.547 (B-package) — the inner ℕ-chain-slice colimit `S*` is PRE-REGULAR, Sorry-free, with the
    LAST remaining hypothesis `hcanon` now DISCHARGED** from the §1.546 well-supported-suffix condition
    (`chainCanonicalCoverWS`).  This is the relative-capitalization successor `S → S*` at the level of
    pre-regular structure, reduced to the single concrete book precondition `hwsuf`: every appended
    suffix is well-supported (true for the relative-capitalization chain, whose appended objects are the
    well-supported `B`'s).  No `hcanon` hypothesis remains. -/
noncomputable def chainSlicePreRegularWS {𝒞 : Type u} [Cat.{u} 𝒞] [PreRegularCategory 𝒞]
    [HasEqualizers 𝒞] (P : PrefixChain 𝒞)
    (hwsuf : ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
        WellSupported
          (listProd (𝒞 := 𝒞) (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j)))) :
    @PreRegularCategory (chainSliceSystem P).Obj (colimitCat _ (chainSliceCoherent P)) :=
  chainSlicePreRegular P (chainCanonicalCoverWS P hwsuf)

/-- The data the §1.543 transfinite construction produces: a directed system of pre-regular
    categories, faithful in its transitions, whose colimit is capital, with a faithful base
    embedding of `A`.  See the module docstring for the field-by-field meaning. -/
public structure CapData (A : Type u) [Cat.{u} A] [PreRegularCategory A] where
  /-- directed index of the tower -/
  ι : Type u
  D : Directed ι
  /-- the tower itself as a coherent system of categories.  Objects and morphisms share the
      universe `u`: the directed-colimit machinery (`CatSystem`/`colimitCat`) requires the
      object and morphism universes to coincide (`catA : Cat.{u} (A i)` with `A i : Type u`),
      so the §1.543 capitalization is built for *small* categories with `Cat.{u}` on `Type u`. -/
  C : CatSystem.{u, u} ι D
  hC : C.Coherent
  hne : Nonempty ι
  /-- the base stage and the faithful start `A → A_{i₀}` -/
  i₀ : ι
  base : A → C.A i₀
  baseFun : Functor A (C.A i₀)
  baseFaithful : Faithful baseFun
  /-- every transition is faithful on morphisms and conservative — so stages inject faithfully -/
  hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
    C.Fmap hij p = C.Fmap hij q → p = q
  hcons : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
    IsIso (C.Fmap hij φ) → IsIso φ
  /-- the `colimitPreRegular` preservation package -/
  ht : ∀ i, HasTerminal (C.A i)
  htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one
  hp : ∀ i, HasBinaryProducts (C.A i)
  hppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (u v : z ⟶ C.F hij ((hp i).prod a b)),
    u ≫ C.Fmap hij (hp i).fst = v ≫ C.Fmap hij (hp i).fst →
    u ≫ C.Fmap hij (hp i).snd = v ≫ C.Fmap hij (hp i).snd → u = v
  hppres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
    (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
    ∃ r : z ⟶ C.F hij ((hp i).prod a b),
      r ≫ C.Fmap hij (hp i).fst = p ∧ r ≫ C.Fmap hij (hp i).snd = q
  he : ∀ i, HasEqualizers (C.A i)
  hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
    (u v : z ⟶ C.F hij (eqObj f g)),
    u ≫ C.Fmap hij (eqMap f g) = v ≫ C.Fmap hij (eqMap f g) → u = v
  hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
    (k : z ⟶ C.F hij A)
    (_hk : k ≫ C.Fmap hij f = k ≫ C.Fmap hij g),
    ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ C.Fmap hij (eqMap f g) = k
  hcanon : letI : Cat C.Obj := colimitCat C hC
      letI : HasPullbacks C.Obj :=
        colimitHasPullbacks C hC ht htpres hp hppres hppres_pair he hepres hepres_lift
    ∀ {A B Z : C.Obj} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂
  /-- the §1.543 capital-closure conclusion for the colimit -/
  capital : letI : Cat C.Obj := colimitCat C hC
      letI : PreRegularCategory C.Obj :=
        colimitPreRegular C hC ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon
    Capital (𝒞 := C.Obj)

/-- **§1.543 reduction.**  From the capitalization data, assemble the capital pre-regular
    target `Ā = C.Obj` and the faithful representation `A → Ā = objIncl i₀ ∘ base`. -/
public theorem capitalization_of_capData {A : Type u} [Cat.{u} A] [PreRegularCategory A]
    (cd : CapData.{u} A) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hP : PreRegularCategory Ā),
      @Capital.{u, u} Ā hC (hP.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  haveI := cd.hne
  letI : Cat cd.C.Obj := colimitCat cd.C cd.hC
  letI hPre : PreRegularCategory cd.C.Obj :=
    colimitPreRegular cd.C cd.hC cd.ht cd.htpres cd.hp cd.hppres cd.hppres_pair
      cd.he cd.hepres cd.hepres_lift cd.hcanon
  refine ⟨cd.C.Obj, _, hPre, cd.capital, ?_⟩
  -- the faithful representation is `objIncl i₀ ∘ base`
  refine ⟨compFunctor cd.baseFun (stageInclFunctor cd.C cd.hC cd.i₀), ?_⟩
  exact faithful_comp cd.baseFaithful
    (stageInclFaithful cd.C cd.hC cd.hfaith cd.hcons cd.i₀)

/-- **§1.543 reduction, REGULAR form.**  Same as `capitalization_of_capData`, but upgrades the
    target from `PreRegularCategory Ā` to `RegularCategory Ā` (= pre-regular + `HasImages`) using the
    colimit image machinery (`Colim.colimitHasImages`).  Beyond the `CapData`, it consumes the
    per-stage image data the colimit `HasImages` needs — `hi` (every stage has images), `hmono`
    (transitions preserve monos, the `PreservesMono` form), and `himgpres` (transitions preserve
    images) — which a *regular* (not merely pre-regular) tower supplies.  This is the assembly that
    makes §2.218 R3(a) discharge once the §1.543 tower is shown to be image-preserving (the slice
    successors are regular, hence the rungs preserve images).  Returns a genuine `RegularCategory Ā`
    (capital, with the faithful `A → Ā`). -/
public theorem capitalization_of_capData_regular {A : Type u} [Cat.{u} A] [PreRegularCategory A]
    (cd : CapData.{u} A)
    (hi : ∀ i, HasImages (cd.C.A i))
    (hmono : ∀ {i j : cd.ι} (hij : cd.D.le i j),
        @PreservesMono _ (cd.C.catA i) _ (cd.C.catA j) (cd.C.functF hij))
    (himgpres : ∀ {i j : cd.ι} (hij : cd.D.le i j) {X Y : cd.C.A i} (f : X ⟶ Y),
        IsImage ((cd.C.functF hij).map f)
          (Subobject.map (cd.C.functF hij) (hmono hij)
            (@image _ (cd.C.catA i) (hi i) _ _ f))) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hR : RegularCategory Ā),
      @Capital.{u, u} Ā hC (hR.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  haveI := cd.hne
  letI : Cat cd.C.Obj := colimitCat cd.C cd.hC
  letI hPre : PreRegularCategory cd.C.Obj :=
    colimitPreRegular cd.C cd.hC cd.ht cd.htpres cd.hp cd.hppres cd.hppres_pair
      cd.he cd.hepres cd.hepres_lift cd.hcanon
  letI hImg : HasImages cd.C.Obj :=
    Colim.colimitHasImages cd.C cd.hC hi cd.hfaith hmono himgpres
  letI hReg : RegularCategory cd.C.Obj := { hPre with toHasImages := hImg }
  -- `hReg.toHasTerminal` is `hPre.toHasTerminal` definitionally, so `cd.capital` lands directly.
  refine ⟨cd.C.Obj, _, hReg, cd.capital, ?_⟩
  exact ⟨compFunctor cd.baseFun (stageInclFunctor cd.C cd.hC cd.i₀),
    faithful_comp cd.baseFaithful (stageInclFaithful cd.C cd.hC cd.hfaith cd.hcons cd.i₀)⟩

/-- **§1.543 reduction, REGULAR form — image-preservation DERIVED.**  Same conclusion as
    `capitalization_of_capData_regular` (a genuine `RegularCategory Ā`, capital, faithful `A → Ā`),
    but it does NOT take `himgpres` as a hypothesis: the transition image-preservation is *derived*
    from cover-preservation (`hcovpres`) via `Colim.transitions_preserve_images`.  KEY INSIGHT
    (§2.218 R3(a)): a functor that preserves COVERS + MONOS, with pullbacks in the target, preserves
    the image factorization (image = cover-then-mono; `coverMono_isImage`).  The §1.543 tower
    transitions already preserve covers (`hcovpres`) and monos (`hmono`); so the only genuinely new
    inputs beyond a pre-regular `CapData` are `hi` (each stage has IMAGES — the regular, not merely
    pre-regular, structure of the slice successors) and the `PreservesMono`/`PreservesCovers` forms.
    The per-stage target pullbacks `coverMono_isImage` needs are built from `cd.hp`/`cd.he`
    (`products_equalizers_implies_pullbacks`). -/
public theorem capitalization_of_capData_regular_of_covers {A : Type u} [Cat.{u} A] [PreRegularCategory A]
    (cd : CapData.{u} A)
    (hi : ∀ i, HasImages (cd.C.A i))
    (hmono : ∀ {i j : cd.ι} (hij : cd.D.le i j),
        @PreservesMono _ (cd.C.catA i) _ (cd.C.catA j) (cd.C.functF hij))
    (hcovpres : ∀ {i j : cd.ι} (hij : cd.D.le i j),
        @PreservesCovers _ _ (cd.C.catA i) (cd.C.catA j) (cd.C.functF hij)) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hR : RegularCategory Ā),
      @Capital.{u, u} Ā hC (hR.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  -- derive `himgpres` per transition from cover + mono preservation + target stage pullbacks.
  have himgpres : ∀ {i j : cd.ι} (hij : cd.D.le i j) {X Y : cd.C.A i} (f : X ⟶ Y),
      IsImage ((cd.C.functF hij).map f)
        (Subobject.map (cd.C.functF hij) (hmono hij)
          (@image _ (cd.C.catA i) (hi i) _ _ f)) := by
    intro i j hij X Y f
    letI : Cat (cd.C.A i) := cd.C.catA i
    letI : Cat (cd.C.A j) := cd.C.catA j
    letI : HasImages (cd.C.A i) := hi i
    -- target-stage pullbacks from products + equalizers (`products_equalizers_implies_pullbacks`).
    letI : HasBinaryProducts (cd.C.A j) := cd.hp j
    letI : HasEqualizers (cd.C.A j) := cd.he j
    letI : HasPullbacks (cd.C.A j) := ⟨fun f g => products_equalizers_implies_pullbacks f g⟩
    exact Colim.transitions_preserve_images (cd.C.functF hij)
      (hmono hij) (hcovpres hij) f
  exact capitalization_of_capData_regular cd hi hmono himgpres

/-! ## §1.543 The ω-tower scaffolding for the transfinite recursion

  The transfinite recursion `A₀ = A`, `A_{α+1} = (A_α)*`, `A_λ = colim_{β<λ}` is, at the
  *successor* level, an ω-indexed tower: a sequence of stages `S : ℕ → Type u` with
  faithful pre-regular-preserving transitions `S n → S (n+1)`.  We make the directed
  index, the per-step interface, and the reduction of `CapData` to "a tower whose colimit
  is capital" explicit.  This isolates the two genuine walls — (i) building the step
  sequence (needs `PreRegularCategory (Over B)` for the slice successor; a parallel
  obligation) and (ii) the capital-closure of the colimit — from the directed-colimit
  bookkeeping, which is already in hand. -/

namespace Colim

/-- `ℕ` with its usual order is a directed preorder: reflexive, transitive, and any two
    naturals have a common upper bound (their max).  This is the index of the ω-tower. -/
def natDirected : Directed Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  bound i j := ⟨Nat.max i j, Nat.le_max_left i j, Nat.le_max_right i j⟩

end Colim

/-! ### The single successor-step interface `CapStep`

  One rung of the tower: a faithful, pre-regular-preserving functor `S → T` between two
  *small* pre-regular categories.  This is exactly Freyd's `A_α → A_{α+1} = (A_α)*`
  (§1.545 relative capitalization, §1.544 faithful slice embedding).  We carry the *single-step*
  versions of every hypothesis `colimitPreRegular` consumes (terminal / products / equalizers
  preserved by the one functor `step`), so that an ω-sequence of `CapStep`s, once its transitions
  are iterated, supplies the whole `colimitPreRegular` preservation package.

  Producing the `step` from `S` is the parallel obligation that needs `PreRegularCategory (Over B)`
  for the slice successor; here `CapStep` is the *interface*, so the construction below is
  decoupled from that open sub-step. -/
public structure CapStep (S : Type u) [Cat.{u} S] [PreRegularCategory S] where
  /-- the next stage `T = S*` -/
  T : Type u
  catT : Cat.{u} T
  preT : @PreRegularCategory T catT
  /-- the successor functor `S → T` and its functoriality -/
  step : S → T
  stepFun : @Functor S T _ catT
  /-- §1.544: the step is faithful (separates morphisms; conservative) -/
  stepFaithful : @Faithful S _ T catT stepFun
  -- §1.543 single-step PRESERVATION package.  These are the per-rung ingredients the OUTER ω-tower
  -- composes (`preservesTerminal_comp`/`preservesBinaryProducts_comp`/`preservesEqualizers_comp`) and
  -- then converts (`preservesBinaryProducts_jointly_monic`/`…_pair`, `preservesEqualizers_mono`/`…_lift`,
  -- `htpres_of_eq`) into the `colimitPreRegular` package over `towerSystem`.  `stepMono`/`stepCover` feed
  -- the `colimitCanonicalCover` bridge (`hmono`/`hcovpres`) that discharges the tower's `hcanon`.
  /-- the step preserves the terminal (`PreservesTerminal`, uniqueness form): `step 1` is terminal
      in `T`.  The OUTER tower does NOT use the bundled `preT`-terminal as its per-stage terminal;
      instead it chooses `ht (i+1) := step (ht i)` recursively (`stepHasTerminal` below), so the
      `htpres` object-equality `step (ht i).one = (ht (i+1)).one` holds by definition — this field
      only certifies that that chosen object is genuinely terminal. -/
  stepTerminal :
    @PreservesTerminal S T _ catT stepFun
      (PreRegularCategory.toHasTerminal)
      (@PreRegularCategory.toHasTerminal T catT preT)
  /-- the EXISTENCE half of "`step 1` is terminal": a map `X ⟶ step 1` from every object of `T`.
      `stepTerminal` (uniqueness) + `stepTerminalArrow` (existence) together exhibit `step 1` as a
      genuine terminal object, so the tower can choose `ht (i+1).one := step (ht i).one` recursively
      with `HasTerminal` data, making `htpres` an on-the-nose object equality (`colimitHasTerminal`
      requires the strict form). -/
  stepTerminalArrow :
    ∀ (X : T), @Cat.Hom T catT X (stepFun.obj (@HasTerminal.one S _ (PreRegularCategory.toHasTerminal)))
  /-- the step preserves binary products (`hppres`/`hppres_pair`). -/
  stepProds :
    @PreservesBinaryProducts S T _ catT stepFun
      (PreRegularCategory.toHasBinaryProducts)
      (@PreRegularCategory.toHasBinaryProducts T catT preT)
  /-- the step preserves equalizers (`hepres`/`hepres_lift`). -/
  stepEqs :
    @PreservesEqualizers S T _ catT stepFun
      (products_pullbacks_implies_equalizers)
      (@products_pullbacks_implies_equalizers T catT
        (@PreRegularCategory.toHasBinaryProducts T catT preT)
        (@PreRegularCategory.toHasPullbacks T catT preT))
  /-- the step preserves monos (`hmono`, for the canonical-cover bridge). -/
  stepMono : ∀ {x y : S} (φ : x ⟶ y), Monic φ → @Monic T catT _ _ (stepFun.map φ)
  /-- the step preserves covers (`hcovpres`, for the canonical-cover bridge). -/
  stepCover : ∀ {x y : S} (φ : x ⟶ y), Cover φ → @Cover T catT _ _ (stepFun.map φ)
  -- NOTE (§1.543 decoupling): a `stepImages : @HasImages T catT` field was added here at f68ad3c for
  -- the REGULAR upgrade (`nextStepRegular`/§2.218 R3a).  It was REMOVED to keep `CapStep` at its
  -- pre-regular shape: the §1.547 cofinal successor `UniformCap.uniformStep` targets a merely
  -- pre-regular lax colimit which has no `HasImages` (would need `HasImages S` + a `laxColimHasImages`),
  -- so demanding images here blocked the sorry-free `capData_exists`.  The regular-path image data is
  -- re-homed onto the standalone `RegCapStep` structure below; the bare `CapStep` is pre-regular only.

/-! ### The ω-tower of stages generated by a uniform successor functor

  Freyd's relative capitalization `(-)*` is a *uniform* construction: it sends any small
  pre-regular category to a faithful pre-regular extension.  We model this as a single
  polymorphic `nextStep : ∀ S, CapStep S`, and iterate it.  `stageBundle A nextStep n`
  is the `n`-th stage as a bundled `(Type u, Cat, PreRegular)`; `stageTy`/`stageCat`/`stagePre`
  project the pieces. -/

/-- A bundled small pre-regular category: carrier, `Cat` instance, `PreRegularCategory` instance.
    Used to carry the dependent stages of the ω-tower through `Nat.rec`. -/
public structure PreRegBundle where
  carrier : Type u
  cat : Cat.{u} carrier
  pre : @PreRegularCategory carrier cat

attribute [instance] PreRegBundle.cat PreRegBundle.pre

/-- Forget images: a §2.154 small regular category is a `PreRegBundle`. -/
def Freyd.S2_154.SmallRegCat.toPreRegBundle (S : SmallRegCat.{u}) : PreRegBundle.{u} :=
  ⟨S.carrier, S.cat, inferInstance⟩

variable {A : Type u} [Cat.{u} A] [PreRegularCategory A]

/-- The `n`-th stage of the ω-tower, as a bundle.  `stage 0 = A`; `stage (n+1)` is the
    successor `(stage n)*` chosen by `nextStep`. -/
@[expose] public def stageBundle (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    PreRegBundle.{u} → Nat → PreRegBundle.{u}
  | b, 0 => b
  | b, (n+1) =>
    let s := nextStep (stageBundle nextStep b n)
    ⟨s.T, s.catT, s.preT⟩

/-- The single-step functor from stage `n` to stage `n+1`. -/
@[expose] public def stageStep (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (b : PreRegBundle.{u})
    (n : Nat) : (stageBundle nextStep b n).carrier → (stageBundle nextStep b (n+1)).carrier :=
  let s := nextStep (stageBundle nextStep b n)
  @Functor.obj _ _ _ s.catT s.stepFun

/-- One rung `stageStep n` as a bundled functor. -/
@[expose] public def stageStepFun (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    @Functor _ _ (stageBundle nextStep b n).cat (stageBundle nextStep b (n+1)).cat :=
  (nextStep (stageBundle nextStep b n)).stepFun

/-- The bundled iterated transition, defined before its object-map projection. -/
@[expose] public def rawTransNFun (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d, @Functor _ _ (stageBundle nextStep b n).cat (stageBundle nextStep b (n+d)).cat
  | 0 => idFunctor
  | (d+1) =>
    compFunctor (rawTransNFun nextStep b n d) (stageStepFun nextStep b (n+d))

/-- The iterated transition `stage n → stage (n+d)`, by recursion on the difference `d`:
    compose `d` consecutive `stageStep`s.  This is the object map of the tower's transition
    functor; expressing transitions by *difference* (rather than by a `≤`-proof) keeps the
    recursion mathlib-free (`Nat.leRec` is not in core). -/
@[expose] public def transN (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d : Nat, (stageBundle nextStep b n).carrier → (stageBundle nextStep b (n+d)).carrier
  | d => (rawTransNFun nextStep b n d).obj

@[simp] theorem transN_zero (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) (x : (stageBundle nextStep b n).carrier) :
    transN nextStep b n 0 x = x := rfl

@[simp] public theorem transN_succ (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n d : Nat) (x : (stageBundle nextStep b n).carrier) :
    transN nextStep b n (d+1) x = stageStep nextStep b (n+d) (transN nextStep b n d x) := rfl

/-- One rung `stageStep n` is faithful (§1.544). -/
public theorem stageStepFaithful (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    @Faithful _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+1)).cat
      (stageStepFun nextStep b n) :=
  (nextStep (stageBundle nextStep b n)).stepFaithful

/-- The rung functor `stageStep`'s `.map` respects heterogeneous equality of arguments at
    carrier-equal stages.  (Both objects and morphisms transport along the stage equality `m = n`.) -/
public theorem stageStepFun_map_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) {x y : (stageBundle nextStep b m).carrier} {x' y' : (stageBundle nextStep b n).carrier}
    (hx : HEq x x') (hy : HEq y y') {g : x ⟶ y} {g' : x' ⟶ y'} (hg : HEq g g') :
    HEq ((stageStepFun nextStep b m).map g) ((stageStepFun nextStep b n).map g') := by
  subst hmn
  -- same stage now; the endpoints coincide, so `g ≈ g'` forces `g = g'`
  cases eq_of_heq hx; cases eq_of_heq hy; cases eq_of_heq hg; rfl

/-- The iterated transition `transN n d` is a functor: a composite of the `d` rung functors. -/
@[expose] public def transNFun (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d, @Functor _ _ (stageBundle nextStep b n).cat (stageBundle nextStep b (n+d)).cat
  | d => rawTransNFun nextStep b n d

/-- The iterated transition `transN n d` is faithful: a composite of faithful rungs. -/
public theorem transNFaithful (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (n : Nat) :
    ∀ d, @Faithful _ (stageBundle nextStep b n).cat _ (stageBundle nextStep b (n+d)).cat
      (transNFun nextStep b n d)
  | 0 => ⟨fun _ _ h => h, fun _ h => h⟩
  | (d+1) => by
    refine ⟨fun f g h => ?_, fun f hiso => ?_⟩
    · -- embedding: hG (hF f) = hG (hF g) ⟹ (faithful hG) hF f = hF g ⟹ (faithful hF) f = g
      exact (transNFaithful nextStep b n d).1 f g
        ((stageStepFaithful nextStep b (n+d)).1 _ _ h)
    · exact (transNFaithful nextStep b n d).2 f
        ((stageStepFaithful nextStep b (n+d)).2 _ hiso)

/-! ### The ω-tower as a `CatSystem` over `ULift Nat`, and the reduction of `capData_exists`

  The colimit machinery indexes by `ι : Type u`, so the ω-tower's index is `ULift.{u} Nat`
  (carrying `Nat`'s order).  From a uniform successor functor `nextStep`, the stages
  `stageBundle` and iterated transitions `transN` provide the object/morphism data; what
  remains to turn them into a `CatSystem` is the *cast-coherence* of expressing the
  difference-recursion transition `transN n (j-i)` as a `≤`-indexed `F i j`, and lifting the
  single-step preservation in `CapStep` to arbitrary `i ≤ j`.  These — together with the
  §1.543 capital-closure of the resulting colimit — are the residual sub-obligations,
  isolated as the explicit hypotheses of `capData_of_nextStep`. -/

-- `uliftNatDirected` now lives upstream in `Freyd.CatColimitRegular` (so `Freyd.Inflation`'s inner
-- chain-slice `CatSystem` can share the same `ℕ`-index without importing `Capitalization`).

variable (b : PreRegBundle.{u})

/-- The object family of the ω-tower `CatSystem`: stage `i` is `(stageBundle b i.down).carrier`. -/
@[expose] public def towerObj (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (i : ULift.{u} Nat) :
    Type u := (stageBundle nextStep b i.down).carrier

/-- The `≤`-indexed transition `towerObj i → towerObj j` for `i ≤ j`: run the difference
    recursion `transN i.down (j.down - i.down)` and cast its codomain `stage (i.down+(j.down-i.down))`
    to `stage j.down` along `i.down + (j.down - i.down) = j.down` (from `i.down ≤ j.down`). -/
@[expose] public def towerF (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down) :
    towerObj b nextStep i → towerObj b nextStep j :=
  fun x => (Nat.add_sub_cancel' hij ▸ transN nextStep b i.down (j.down - i.down) x :
    (stageBundle nextStep b j.down).carrier)

/-! ### Cast helpers for the difference recursion

  Two ingredients turn the difference-recursion `transN` into a `≤`-indexed `CatSystem.F`:

    * `stageCast` / `stageCastHom` — transport an object / morphism across the *Nat*-equality
      `m = n` between stage carriers `stage m = stage n`.  (The carriers are literally equal as
      types once `m = n`, so this is `Eq.rec`; `stageCastHom` is the morphism version, and
      `stageCastHom_heq` exposes it as `HEq`-to-the-original for the coherence proofs.)
    * `transN_add` — the iterated transition splits additively, `transN n (d+e) = transN (n+d) e ∘
      transN n d`, modulo the carrier identification `(n+d)+e = n+(d+e)`.  This is the object-level
      content of `CatSystem.F_trans`.

  All `Coherent` content reduces to these plus `transNFun`'s functoriality (already proven). -/

/-- Transport an object across the stage-carrier equality induced by `m = n : Nat`. -/
@[expose] public def stageCast (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat} (h : m = n)
    (x : (stageBundle nextStep b m).carrier) : (stageBundle nextStep b n).carrier := h ▸ x

@[simp] theorem stageCast_rfl (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m : Nat}
    (x : (stageBundle nextStep b m).carrier) : stageCast b nextStep (rfl : m = m) x = x := rfl

/-- The object transport is heterogeneously the original object. -/
public theorem stageCast_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    HEq (stageCast b nextStep h x) x := by subst h; rfl

/-- Transport a *morphism* across the stage-carrier equality induced by `m = n : Nat`. -/
@[expose] public def stageCastHom (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat} (h : m = n)
    {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y) :
    stageCast b nextStep h x ⟶ stageCast b nextStep h y := by
  subst h; exact g

/-- The morphism transport is heterogeneously the original morphism. -/
public theorem stageCastHom_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y) :
    HEq (stageCastHom b nextStep h g) g := by subst h; rfl

/-- The morphism transport preserves identities. -/
public theorem stageCastHom_id (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    stageCastHom b nextStep h (Cat.id x) = Cat.id (stageCast b nextStep h x) := by subst h; rfl

/-- The morphism transport distributes over composition. -/
public theorem stageCastHom_comp (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y z : (stageBundle nextStep b m).carrier} (f : x ⟶ y) (g : y ⟶ z) :
    stageCastHom b nextStep h (f ≫ g) =
      stageCastHom b nextStep h f ≫ stageCastHom b nextStep h g := by subst h; rfl

/-- `stageStep` commutes with the stage-cast: applying the successor rung after a cast equals
    casting after the successor rung (the carriers `stage m`, `stage n` agree once `m = n`). -/
public theorem stageStep_stageCast (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) (x : (stageBundle nextStep b m).carrier) :
    stageStep nextStep b n (stageCast b nextStep h x) =
      stageCast b nextStep (by omega : m + 1 = n + 1) (stageStep nextStep b m x) := by
  subst h; rfl

/-- The iterated transition splits additively (object level).  `transN n (d+e)` first runs
    `transN n d` to stage `n+d`, then `transN (n+d) e` to stage `(n+d)+e`, which is `stage (n+(d+e))`
    after the carrier identification `(n+d)+e = n+(d+e)`. -/
public theorem transN_add (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d : Nat) :
    ∀ (e : Nat) (x : (stageBundle nextStep b n).carrier),
      transN nextStep b n (d + e) x =
        stageCast b nextStep (by omega)
          (transN nextStep b (n + d) e (transN nextStep b n d x))
  | 0, x => by simp [transN, rawTransNFun, stageCast]
  | (e+1), x => by
    -- LHS: `transN n (d+(e+1)) = stageStep (n+(d+e)) (transN n (d+e) x)`
    show stageStep nextStep b (n + (d + e)) (transN nextStep b n (d + e) x) = _
    rw [transN_add nextStep n d e x, stageStep_stageCast]
    -- both sides are a `stageCast` (= `Eq.rec`) of the SAME underlying object
    -- `stageStep (n+d+e) (transN (n+d) e (transN n d x))`, over carrier-equal Nat indices, hence
    -- equal after dropping both casts via `eqRec_heq`.
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    show HEq (stageStep nextStep b (n + d + e) _) _
    rw [transN_succ]
    exact (stageCast_heq b nextStep _ _).symm

/-- Object additivity of the difference recursion, HEq form (drops the `stageCast` from
    `transN_add`). -/
public theorem transN_add_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d e : Nat)
    (x : (stageBundle nextStep b n).carrier) :
    HEq (transN nextStep b n (d + e) x)
      (transN nextStep b (n + d) e (transN nextStep b n d x)) := by
  rw [transN_add b nextStep n d e x]; exact stageCast_heq b nextStep _ _

/-- `transN _ d` respects heterogeneous equality of base objects at carrier-equal stages. -/
public theorem transN_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) (d : Nat) {x : (stageBundle nextStep b m).carrier}
    {y : (stageBundle nextStep b n).carrier} (hxy : HEq x y) :
    HEq (transN nextStep b m d x) (transN nextStep b n d y) := by subst hmn; rw [eq_of_heq hxy]

/-- `transNFun _ d`'s `.map` respects heterogeneous equality of base morphisms at carrier-equal
    stages (endpoints HEq, morphism HEq). -/
public theorem transNFun_map_congr_heq (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (hmn : m = n) {x y : (stageBundle nextStep b m).carrier}
    {x' y' : (stageBundle nextStep b n).carrier} (hx : HEq x x') (hy : HEq y y')
    {d : Nat} {g : x ⟶ y} {g' : x' ⟶ y'} (hg : HEq g g') :
    HEq ((transNFun nextStep b m d).map g) ((transNFun nextStep b n d).map g') := by
  subst hmn; cases eq_of_heq hx; cases eq_of_heq hy; cases eq_of_heq hg; rfl

/-- The morphism map of the `≤`-indexed transition `towerF hij`: map `g` by the difference
    functor `transNFun i.down (j.down-i.down)`, then transport along the carrier equality. -/
@[expose] public def towerFmap (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down)
    {x y : towerObj b nextStep i} (g : @Cat.Hom _ (stageBundle nextStep b i.down).cat x y) :
    @Cat.Hom _ (stageBundle nextStep b j.down).cat (towerF b nextStep hij x) (towerF b nextStep hij y) :=
  stageCastHom b nextStep (Nat.add_sub_cancel' hij)
    ((transNFun nextStep b i.down (j.down - i.down)).map g)

/-- `towerF hij` is a functor (object map `towerF`, morphism map `towerFmap`): a stage-cast of the
    difference functor `transNFun`, which is itself a functor; the cast `stageCastHom` is
    functorial (`subst` reduces it to identity). -/
@[expose] public def towerFunctF (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : i.down ≤ j.down) :
    @Functor _ _ ((stageBundle nextStep b i.down).cat) ((stageBundle nextStep b j.down).cat) where
  obj := towerF b nextStep hij
  map g := towerFmap b nextStep hij g
  map_id x := by
    unfold towerFmap
    rw [(transNFun nextStep b i.down (j.down - i.down)).map_id]
    exact stageCastHom_id _ _ _ _
  map_comp g g' := by
    unfold towerFmap
    rw [(transNFun nextStep b i.down (j.down - i.down)).map_comp, stageCastHom_comp]

/-- **The ω-tower as a `CatSystem`** over `ULift.{u} Nat`.  Objects `towerObj`, transitions
    `towerF`/`towerFunctF`; the object coherence `F_refl`/`F_trans` is exactly the difference-cast
    bookkeeping (`transN_zero`/`transN_add`). -/
@[expose] public def towerSystem (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    CatSystem.{u, u} (ULift.{u} Nat) uliftNatDirected where
  A i := towerObj b nextStep i
  catA i := (stageBundle nextStep b i.down).cat
  F hij := towerF b nextStep hij
  Fmap hij := (towerFunctF b nextStep hij).map
  Fmap_id hij := (towerFunctF b nextStep hij).map_id
  Fmap_comp hij := (towerFunctF b nextStep hij).map_comp
  F_refl {i} x := by
    -- `j = i`, so the difference is `0`, `transN 0 = id`, cast over `i+0=i`.
    show stageCast b nextStep _ (transN nextStep b i.down (i.down - i.down) _) = x
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    rw [Nat.sub_self]; rfl
  F_trans {i j k} hij hjk x := by
    have hij' : i.down ≤ j.down := hij
    have hjk' : j.down ≤ k.down := hjk
    -- `transN i.down (k.down-i.down) = transN (i.down+(j.down-i.down)) (k.down-j.down) ∘ transN …`
    -- with `(j.down-i.down)+(k.down-j.down) = k.down-i.down`.
    show stageCast b nextStep _ (transN nextStep b i.down (k.down - i.down) x) =
      stageCast b nextStep _ (transN nextStep b j.down (k.down - j.down)
        (stageCast b nextStep _ (transN nextStep b i.down (j.down - i.down) x)))
    apply eq_of_heq
    refine (stageCast_heq b nextStep _ _).trans ?_
    -- split the difference additively and discharge casts heterogeneously
    have hsplit : k.down - i.down = (j.down - i.down) + (k.down - j.down) := by omega
    rw [hsplit, transN_add b nextStep i.down (j.down - i.down) (k.down - j.down) x]
    refine (stageCast_heq b nextStep _ _).trans ?_
    -- now match: both run `transN j.down (k.down-j.down)` on transported `transN i.down …`; the
    -- inner `i.down+(j.down-i.down) = j.down`, so the inner cast is heterogeneously transparent.
    refine HEq.symm ((stageCast_heq b nextStep _ _).trans ?_)
    -- congruence under `transN _ (k.down-j.down)` for HEq-equal arguments at carrier-eq stages
    -- (`j.down = i.down + (j.down - i.down)`); the inner cast is HEq-transparent.
    exact transN_congr_heq b nextStep (by omega : j.down = i.down + (j.down - i.down))
      (k.down - j.down) (stageCast_heq b nextStep _ _)

/-- Morphism-level additivity of the difference functor, HEq form.  `(transNFun n (d+e)).map g`
    equals `(transNFun (n+d) e).map ((transNFun n d).map g)` heterogeneously (carriers agree once
    `(n+d)+e = n+(d+e)`).  Proven by induction on `e` from `transN_add`/functoriality. -/
public theorem transNFun_map_add (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n d : Nat) :
    ∀ (e : Nat) {x y : (stageBundle nextStep b n).carrier} (g : x ⟶ y),
      HEq ((transNFun nextStep b n (d + e)).map g)
        ((transNFun nextStep b (n + d) e).map ((transNFun nextStep b n d).map g))
  | 0, x, y, g => by
    -- `transNFun (n+d) 0 = id` functor, `d+0 = d`
    simp only [Nat.add_zero]
    refine HEq.symm ?_
    show HEq ((transNFun nextStep b n d).map g) _
    rfl
  | (e+1), x, y, g => by
    -- `transNFun n (d+(e+1))).map = stageStep-rung.map ∘ (transNFun n (d+e)).map`
    show HEq ((stageStepFun nextStep b (n + (d + e))).map ((transNFun nextStep b n (d + e)).map g)) _
    -- and RHS `transNFun (n+d) (e+1)).map = rung.map ∘ (transNFun (n+d) e).map`
    refine HEq.symm ?_
    show HEq ((stageStepFun nextStep b (n + d + e)).map
      ((transNFun nextStep b (n + d) e).map ((transNFun nextStep b n d).map g))) _
    -- the two rungs are at carrier-equal indices `n+d+e = n+(d+e)`; their `.map` agree on
    -- HEq-equal arguments (`transNFun_map_add` at `e`), with endpoints related by `transN_add_heq`.
    refine (stageStepFun_map_congr_heq nextStep (by omega : n + (d + e) = n + d + e)
      (transN_add_heq b nextStep n d e x) (transN_add_heq b nextStep n d e y)
      (transNFun_map_add nextStep n d e g)).symm

/-- The ω-tower system is `Coherent`: identity transition acts as identity on morphisms,
    composite transitions compose — both via the `stageCastHom`-is-`HEq`-the-original principle
    and the functoriality `transNFun`/`transN_add`. -/
public theorem towerCoherent (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    (towerSystem b nextStep).Coherent where
  refl_map {i x x'} g := by
    -- `(functF (refl)).map g = towerFmap (refl) g = stageCastHom (transNFun (i-i)).map g`; with
    -- `i-i=0`, `transNFun 0 = id`, and the cast is `HEq`-trivial.
    show HEq ((towerSystem b nextStep).Fmap (uliftNatDirected.refl i) g) g
    change HEq (towerFmap b nextStep (uliftNatDirected.refl i) g) g
    unfold towerFmap
    refine (stageCastHom_heq b nextStep _ _).trans ?_
    rw [Nat.sub_self]; rfl
  trans_map {i j k} hij hjk x x' g := by
    have hij' : i.down ≤ j.down := hij
    have hjk' : j.down ≤ k.down := hjk
    show HEq (towerFmap b nextStep (uliftNatDirected.trans hij hjk) g)
      ((towerFunctF b nextStep hjk).map ((towerFunctF b nextStep hij).map g))
    -- LHS underlying = `(transNFun (k-i)).map g`; RHS underlying =
    -- `(transNFun (k-j)).map ((transNFun (j-i)).map g)`.  Both casts drop via `stageCastHom_heq`.
    unfold towerFmap towerFunctF
    refine (stageCastHom_heq b nextStep _ _).trans ?_
    show HEq ((transNFun nextStep b i.down (k.down - i.down)).map g) _
    refine HEq.symm ((stageCastHom_heq b nextStep _ _).trans ?_)
    show HEq ((transNFun nextStep b j.down (k.down - j.down)).map
      (stageCastHom b nextStep _ ((transNFun nextStep b i.down (j.down - i.down)).map g))) _
    -- the inner `stageCastHom` is `HEq`-transparent; then additivity `(j-i)+(k-j)=k-i`.
    refine HEq.symm ?_
    have hadd : (j.down - i.down) + (k.down - j.down) = k.down - i.down := by omega
    -- rewrite the LHS difference via additivity (carrier `i + (j-i) = j`)
    have key := transNFun_map_add b nextStep i.down (j.down - i.down) (k.down - j.down) g
    rw [hadd] at key
    refine key.trans ?_
    -- now match `(transNFun (i+(j-i)) (k-j)).map ((transNFun (j-i)).map g)` against the RHS, whose
    -- rung is at stage `j.down`; carriers agree (`i+(j-i)=j`) and inner arg is HEq-transparent.
    refine transNFun_map_congr_heq b nextStep (by omega) ?_ ?_ ?_
    · exact (stageCast_heq b nextStep _ _).symm
    · exact (stageCast_heq b nextStep _ _).symm
    · exact (stageCastHom_heq b nextStep _ _).symm

/-- The morphism transport `stageCastHom h` is injective (it is `Eq.rec`, hence an isomorphism). -/
public theorem stageCastHom_injective (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g g' : x ⟶ y)
    (heq : stageCastHom b nextStep h g = stageCastHom b nextStep h g') : g = g' := by
  subst h; exact heq

/-- The morphism transport `stageCastHom h` reflects isos (it is itself an iso). -/
public theorem stageCastHom_isIso_reflects (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) {m n : Nat}
    (h : m = n) {x y : (stageBundle nextStep b m).carrier} (g : x ⟶ y)
    (hiso : @IsIso _ (stageBundle nextStep b n).cat _ _ (stageCastHom b nextStep h g)) :
    @IsIso _ (stageBundle nextStep b m).cat _ _ g := by subst h; exact hiso

/-- The tower transition `towerFunctF hij` is faithful on morphisms: drop the cast
    (`stageCastHom_injective`), then the iterated functor is faithful (`transNFaithful`). -/
public theorem towerHfaith (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (p q : x ⟶ y)
    (h : (towerSystem b nextStep).Fmap hij p = (towerSystem b nextStep).Fmap hij q) :
    p = q :=
  (transNFaithful nextStep b i.down (j.down - i.down)).1 p q
    (stageCastHom_injective b nextStep _ _ _ h)

/-- The tower transition `towerFunctF hij` is conservative: drop the cast, then the iterated
    functor reflects isos (`transNFaithful`). -/
public theorem towerHcons (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (φ : x ⟶ y)
    (hiso : @IsIso _ ((towerSystem b nextStep).catA j) _ _ ((towerSystem b nextStep).Fmap hij φ)) :
    @IsIso _ ((towerSystem b nextStep).catA i) _ _ φ :=
  (transNFaithful nextStep b i.down (j.down - i.down)).2 φ
    (stageCastHom_isIso_reflects b nextStep _ _ hiso)

/-! ### Lifting the single-step terminal to *any* terminal of `S`

  `CapStep.stepTerminal`/`stepTerminalArrow` certify that `step` sends the *bundled* terminal
  `one : S` to a genuine terminal of `T`.  The ω-tower, however, chooses its stage-`(n+1)` terminal
  as `step (ht n).one` where `ht n` is the *recursively* chosen terminal of stage `n` — which is
  NOT the bundled terminal at successor stages.  Since any two terminals of `S` are isomorphic and
  `step` is a functor (sends isos to isos), `step (htS.one)` is terminal for ANY `HasTerminal S`,
  giving the recursion a strict `HasTerminal` at each stage. -/

/-- **A `CapStep` sends any terminal of `S` to a terminal of `T`.**  From `s.stepTerminal`
    (uniqueness) and `s.stepTerminalArrow` (existence) — stated about the *bundled* terminal — plus
    the unique iso between any terminal `htS.one` and the bundled `one`, transported through the
    functor `s.stepFun`. -/
@[expose] public noncomputable def capStepHasTerminal {S : Type u} [Cat.{u} S] [PreRegularCategory S]
    (s : CapStep S) (htS : HasTerminal S) :
    @HasTerminal s.T s.catT := by
  letI : Cat s.T := s.catT
  letI bundled : HasTerminal S := PreRegularCategory.toHasTerminal
  -- the comparison arrow `step htS.one ⟶ step (bundled.one)` is `step (bundled.trm htS.one)`; it is
  -- iso (functor of the unique terminal iso `htS.one ≅ bundled.one`).
  let base : @Cat.Hom _ _ htS.one bundled.one := bundled.trm htS.one
  let cmp : @Cat.Hom _ s.catT (s.stepFun.obj htS.one) (s.stepFun.obj bundled.one) := s.stepFun.map base
  have hiso : @IsIso _ s.catT _ _ cmp := by
    refine functor_preserves_iso (F := s.stepFun) base ?_
    exact ⟨htS.trm bundled.one, htS.uniq _ (Cat.id _), bundled.uniq _ (Cat.id _)⟩
  -- choose the inverse (goal is `Type`, so eliminate the existential via `Classical.choose`).
  let inv : @Cat.Hom _ s.catT (s.stepFun.obj bundled.one) (s.stepFun.obj htS.one) := Classical.choose hiso
  have hinv₁ : cmp ≫ inv = Cat.id _ := (Classical.choose_spec hiso).1
  refine @HasTerminal.mk s.T s.catT (s.stepFun.obj htS.one) (fun X => s.stepTerminalArrow X ≫ inv) ?_
  -- uniqueness into `step htS.one`: post-compose with the mono `cmp`, reducing to `stepTerminal`.
  intro X f g
  have hmono : @Monic _ s.catT _ _ cmp := mono_of_retraction _ inv hinv₁
  exact hmono f g (s.stepTerminal X (f ≫ cmp) (g ≫ cmp))

/-! ### The tower's strict per-stage terminal and on-the-nose `htpres`

  The ω-tower needs `htpres : F hij (ht i).one = (ht j).one` as an *object equality*.  This forces
  the terminal to thread through the recursion: `ht 0 := b.pre.toHasTerminal`, and at the successor,
  `ht (n+1).one := stageStep n (ht n).one = step (ht n).one`, certified terminal by
  `capStepHasTerminal` (any terminal of stage `n` maps to a terminal of stage `n+1`).  Then the
  single-step `htpres` is definitional; the general `i ≤ j` form follows by difference induction. -/

/-- **The tower's strict per-stage terminal (raw `Nat` form).**  `ht 0 = b.pre.toHasTerminal`;
    `ht (n+1) = capStepHasTerminal (nextStep stage_n) (ht n)`, whose `.one` is `step (ht n).one`. -/
@[expose] public noncomputable def towerHasTerminalN (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    ∀ n : Nat, @HasTerminal _ (stageBundle nextStep b n).cat
  | 0 => (stageBundle nextStep b 0).pre.toHasTerminal
  | (n+1) =>
    capStepHasTerminal (nextStep (stageBundle nextStep b n)) (towerHasTerminalN nextStep n)

/-- The successor stage terminal is, on the nose, the `stageStep`-image of the previous one. -/
public theorem towerHasTerminalN_succ_one (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n : Nat) :
    (towerHasTerminalN b nextStep (n+1)).one
      = stageStep nextStep b n (towerHasTerminalN b nextStep n).one := rfl

/-- **The tower's strict per-stage terminal**, packaged over the `ULift Nat` index. -/
@[expose] public noncomputable def towerHasTerminal (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    ∀ i : ULift.{u} Nat, HasTerminal ((towerSystem b nextStep).A i) :=
  fun i => towerHasTerminalN b nextStep i.down

/-- **The tower's on-the-nose terminal preservation** `F hij (ht i).one = (ht j).one`, by induction
    on the difference `d = j.down - i.down`.  `F hij` is `stageCast ∘ transN i.down d`; we prove the
    HEq form `transN i.down d (ht i).one ≈ (ht (i.down+d)).one` and discharge the cast. -/
public theorem towerHtpresN (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n : Nat) :
    ∀ d : Nat, HEq (transN nextStep b n d (towerHasTerminalN b nextStep n).one)
      (towerHasTerminalN b nextStep (n+d)).one
  | 0 => by show HEq (towerHasTerminalN b nextStep n).one _; rfl
  | (d+1) => by
    -- `transN n (d+1) x = stageStep (n+d) (transN n d x)`.  IH gives `transN n d (ht n).one ≈ (ht (n+d)).one`,
    -- so `stageStep (n+d)` of it ≈ `stageStep (n+d) (ht (n+d)).one = (ht (n+d+1)).one`.
    show HEq (stageStep nextStep b (n+d) (transN nextStep b n d (towerHasTerminalN b nextStep n).one)) _
    have ih := towerHtpresN nextStep n d
    -- congruence of `stageStep (n+d)` under HEq of its arg at the SAME stage; then unfold the
    -- successor terminal's `.one`.
    have hcong : HEq (stageStep nextStep b (n+d)
        (transN nextStep b n d (towerHasTerminalN b nextStep n).one))
        (stageStep nextStep b (n+d) (towerHasTerminalN b nextStep (n+d)).one) := by
      rw [eq_of_heq ih]
    exact hcong.trans (by rw [towerHasTerminalN_succ_one]; show HEq _ _; rfl)

/-- **`towerHtpres`** in the `CatSystem.F`-indexed form `colimitHasTerminal` consumes. -/
public theorem towerHtpres (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) :
    (towerSystem b nextStep).F hij (towerHasTerminal b nextStep i).one
      = (towerHasTerminal b nextStep j).one := by
  have hij' : i.down ≤ j.down := hij
  -- `F hij x = stageCast (i+(j-i)=j) (transN i.down (j.down-i.down) x)`; drop the cast (HEq), apply
  -- the HEq additivity `towerHtpresN`, and land at `(ht (i.down+(j.down-i.down))).one = (ht j.down).one`.
  show stageCast b nextStep (Nat.add_sub_cancel' hij')
    (transN nextStep b i.down (j.down - i.down) (towerHasTerminalN b nextStep i.down).one)
    = (towerHasTerminalN b nextStep j.down).one
  apply eq_of_heq
  refine (stageCast_heq b nextStep _ _).trans ?_
  refine (towerHtpresN b nextStep i.down (j.down - i.down)).trans ?_
  -- `i.down + (j.down - i.down) = j.down`, so the two terminals coincide (HEq at carrier-equal stages).
  have he : i.down + (j.down - i.down) = j.down := Nat.add_sub_cancel' hij'
  rw [he]

/-! ### Lifting single-step preservation to the iterated transition `transNFun`/`transN`

  Each rung `stageStep n = (nextStep stage_n).step` preserves products / equalizers / monos / covers
  (the `CapStep` fields).  The iterated transition `transN n d` is the composite of `d` rungs, so it
  preserves all of these — by induction on `d`, composing rungs with
  `preservesBinaryProducts_comp`/`preservesEqualizers_comp` (products / equalizers) and direct
  composition (monos / covers).  The per-stage finite-limit instances come from the bundled
  `PreRegularCategory` (`(stageBundle …).pre`). -/

/-- Each stage of the tower has equalizers (from products + pullbacks of the bundled pre-regular). -/
@[expose] public noncomputable instance stageHasEqualizers (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (n : Nat) : @HasEqualizers _ (stageBundle nextStep b n).cat :=
  @products_pullbacks_implies_equalizers _ (stageBundle nextStep b n).cat
    (stageBundle nextStep b n).pre.toHasBinaryProducts
    (stageBundle nextStep b n).pre.toHasPullbacks

/-- **The iterated transition `transN n d` preserves binary products.**  Composite of `d` rungs,
    each preserving products (`CapStep.stepProds`), via `preservesBinaryProducts_comp`. -/
public theorem transN_preservesBinaryProducts (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (n d : Nat) :
    @PreservesBinaryProducts _ _ (stageBundle nextStep b n).cat (stageBundle nextStep b (n+d)).cat
      (transNFun nextStep b n d)
      (stageBundle nextStep b n).pre.toHasBinaryProducts
      (stageBundle nextStep b (n+d)).pre.toHasBinaryProducts := by
  induction d with
  | zero =>
    -- `transN n 0 = id`, `transNFun n 0 = id`-functor; `.map fst = fst`, so the comparison
    -- `pair fst snd = id` is iso.
    intro A B
    letI := (stageBundle nextStep b (n+0)).pre.toHasBinaryProducts
    show @IsIso _ (stageBundle nextStep b (n+0)).cat _ _
      (pair ((transNFun nextStep b n 0).map fst) ((transNFun nextStep b n 0).map snd))
    rw [show (transNFun nextStep b n 0).map (fst (A := A) (B := B)) = fst from rfl,
      show (transNFun nextStep b n 0).map (snd (A := A) (B := B)) = snd from rfl, pair_fst_snd]
    exact ⟨Cat.id _, Cat.id_comp _, Cat.id_comp _⟩
  | succ d ihF =>
    -- `transN n (d+1) = stageStep (n+d) ∘ transN n d`; compose the two preservations (the goal's
    -- `transNFun n (d+1)` is defeq to the composite functor `compFunctor`).
    letI := transNFun nextStep b n d
    letI := stageStepFun nextStep b (n+d)
    intro A B
    exact preservesBinaryProducts_comp (𝒜 := (stageBundle nextStep b n).carrier)
      (ℬ := (stageBundle nextStep b (n+d)).carrier)
      (ℰ := (stageBundle nextStep b (n+d+1)).carrier)
      (transNFun nextStep b n d) (stageStepFun nextStep b (n+d)) ihF
      (nextStep (stageBundle nextStep b (n+d))).stepProds (A := A) (B := B)

/-- **The iterated transition `transN n d` preserves equalizers.**  Composite of `d` rungs, each
    preserving equalizers (`CapStep.stepEqs`), via `preservesEqualizers_comp`. -/
public theorem transN_preservesEqualizers (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (n d : Nat) :
    @PreservesEqualizers _ _ (stageBundle nextStep b n).cat (stageBundle nextStep b (n+d)).cat
      (transNFun nextStep b n d)
      (stageHasEqualizers b nextStep n) (stageHasEqualizers b nextStep (n+d)) := by
  induction d with
  | zero =>
    -- `transNFun n 0 = id`-functor: `.map f = f`, `.map g = g`, `.map (eqMap f g) = eqMap f g`; the
    -- comparison is the lift of the chosen equalizer into itself, iso (two equalizers).
    intro A B f g
    letI := stageHasEqualizers b nextStep (n+0)
    -- the comparison cone `c = {dom := eqObj f g, map := eqMap f g}` IS the chosen equalizer of
    -- `(f, g)` (transN n 0 = id), so its lift into the chosen equalizer is iso (two equalizers).
    exact isIso_of_two_equalizers (chosenEqualizer_isEqualizer
      ((transNFun nextStep b n 0).map f) ((transNFun nextStep b n 0).map g))
      (chosenEqualizer_isEqualizer ((transNFun nextStep b n 0).map f)
        ((transNFun nextStep b n 0).map g)) _
      ((HasEqualizers.eq _ _ ((transNFun nextStep b n 0).map f)
        ((transNFun nextStep b n 0).map g)).fac _)
  | succ d ihF =>
    -- the rung's `stepEqs` is stated w.r.t. its `preT`-derived equalizers, defeq to `stageHasEqualizers`.
    letI := transNFun nextStep b n d
    letI := stageStepFun nextStep b (n+d)
    intro A B f g
    exact preservesEqualizers_comp (𝒜 := (stageBundle nextStep b n).carrier)
      (ℬ := (stageBundle nextStep b (n+d)).carrier)
      (ℰ := (stageBundle nextStep b (n+d+1)).carrier)
      (transNFun nextStep b n d) (stageStepFun nextStep b (n+d)) ihF
      (nextStep (stageBundle nextStep b (n+d))).stepEqs f g

/-- **The iterated transition `transN n d` preserves monos.**  Composite of `d` mono-preserving
    rungs (`CapStep.stepMono`). -/
public theorem transN_preservesMono (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n : Nat) :
    ∀ (d : Nat) {x y : (stageBundle nextStep b n).carrier} (φ : x ⟶ y),
      @Monic _ (stageBundle nextStep b n).cat _ _ φ →
      @Monic _ (stageBundle nextStep b (n+d)).cat _ _ ((transNFun nextStep b n d).map φ)
  | 0, _, _, _, hφ => hφ
  | (d+1), _, _, φ, hφ =>
    (nextStep (stageBundle nextStep b (n+d))).stepMono _
      (transN_preservesMono nextStep n d φ hφ)

/-- **The iterated transition `transN n d` preserves covers.**  Composite of `d` cover-preserving
    rungs (`CapStep.stepCover`). -/
public theorem transN_preservesCover (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (n : Nat) :
    ∀ (d : Nat) {x y : (stageBundle nextStep b n).carrier} (φ : x ⟶ y),
      @Cover _ (stageBundle nextStep b n).cat _ _ φ →
      @Cover _ (stageBundle nextStep b (n+d)).cat _ _ ((transNFun nextStep b n d).map φ)
  | 0, _, _, _, hφ => hφ
  | (d+1), _, _, φ, hφ =>
    (nextStep (stageBundle nextStep b (n+d))).stepCover _
      (transN_preservesCover nextStep n d φ hφ)

/-! ### Transporting the iterated preservation across the `stageCast` to the tower transition

  The tower transition `towerF hij = stageCast h ∘ transN i.down (j.down - i.down)` with
  `h : i.down + (j.down - i.down) = j.down`, and `towerFunctF hij .map = stageCastHom h ∘ transNFun
  .map`.  Since `stageCast`/`stageCastHom` are `Eq.rec` (collapse under `subst h`), the iterated
  preservation transfers to the tower transition; we `subst` the difference-equality to reduce each
  tower hypothesis to the `transN`-level fact. -/

/-- **The `stageCast`-transported difference functor preserves binary products** (generic over the
    target stage equality `h : m + d = n`).  `subst h` collapses both `stageCast` and `stageCastHom`
    (they are `Eq.rec`), reducing to `transN_preservesBinaryProducts`. -/
public theorem stageCast_transN_preservesBinaryProducts
    (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (m d n : Nat) (h : m + d = n) :
    @PreservesBinaryProducts _ _ (stageBundle nextStep b m).cat (stageBundle nextStep b n).cat
      { obj := fun x => stageCast b nextStep h (transN nextStep b m d x)
        map := fun {x y} g => stageCastHom b nextStep h ((transNFun nextStep b m d).map g)
        map_id := fun x => by
          rw [(transNFun nextStep b m d).map_id]
          exact stageCastHom_id _ _ _ _
        map_comp := fun f g => by
          rw [(transNFun nextStep b m d).map_comp, stageCastHom_comp] }
      (stageBundle nextStep b m).pre.toHasBinaryProducts
      (stageBundle nextStep b n).pre.toHasBinaryProducts := by
  subst h
  -- `stageCast`/`stageCastHom` at `rfl` are the identity; the functor is `transNFun m d`.
  exact transN_preservesBinaryProducts b nextStep m d

/-- **`towerF hij` preserves binary products.**  `towerF`/`towerFunctF` ARE the `stageCast`-transport
    of `transN`/`transNFun` (definitionally), so apply the generic transport. -/
public theorem towerF_preservesBinaryProducts (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) :
    @PreservesBinaryProducts _ _ (stageBundle nextStep b i.down).cat
      (stageBundle nextStep b j.down).cat (towerFunctF b nextStep hij)
      (stageBundle nextStep b i.down).pre.toHasBinaryProducts
      (stageBundle nextStep b j.down).pre.toHasBinaryProducts :=
  stageCast_transN_preservesBinaryProducts b nextStep i.down (j.down - i.down) j.down
    (Nat.add_sub_cancel' hij)

/-- **The `stageCast`-transported difference functor preserves equalizers** (generic). -/
public theorem stageCast_transN_preservesEqualizers
    (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) (m d n : Nat) (h : m + d = n) :
    @PreservesEqualizers _ _ (stageBundle nextStep b m).cat (stageBundle nextStep b n).cat
      { obj := fun x => stageCast b nextStep h (transN nextStep b m d x)
        map := fun {x y} g => stageCastHom b nextStep h ((transNFun nextStep b m d).map g)
        map_id := fun x => by
          rw [(transNFun nextStep b m d).map_id]
          exact stageCastHom_id _ _ _ _
        map_comp := fun f g => by
          rw [(transNFun nextStep b m d).map_comp, stageCastHom_comp] }
      (stageHasEqualizers b nextStep m) (stageHasEqualizers b nextStep n) := by
  subst h
  exact transN_preservesEqualizers b nextStep m d

/-- **`towerF hij` preserves equalizers.**  Apply the generic transport. -/
public theorem towerF_preservesEqualizers (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) :
    @PreservesEqualizers _ _ (stageBundle nextStep b i.down).cat
      (stageBundle nextStep b j.down).cat (towerFunctF b nextStep hij)
      (stageHasEqualizers b nextStep i.down) (stageHasEqualizers b nextStep j.down) :=
  stageCast_transN_preservesEqualizers b nextStep i.down (j.down - i.down) j.down
    (Nat.add_sub_cancel' hij)

/-! ### The destructured tower preservation package

  Convert `towerF_preserves{BinaryProducts,Equalizers}` to the exact destructured hypotheses the
  `colimitPreRegular`/`capData_of_tower` package consumes (`hppres`/`hppres_pair`/`hepres`/
  `hepres_lift`), and lift `transN_preserves{Monic,Cover}` across the cast for the canonical-cover
  bridge (`hmono`/`hcovpres`). -/

/-- The tower's per-stage binary products (the bundled pre-regular's). -/
@[expose] public noncomputable def towerHp (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (i : ULift.{u} Nat) : HasBinaryProducts ((towerSystem b nextStep).A i) :=
  (stageBundle nextStep b i.down).pre.toHasBinaryProducts

/-- The tower's per-stage equalizers. -/
@[expose] public noncomputable def towerHe (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (i : ULift.{u} Nat) : HasEqualizers ((towerSystem b nextStep).A i) :=
  stageHasEqualizers b nextStep i.down

/-- **`hppres`** (joint monicity of `(F fst, F snd)`) from `towerF_preservesBinaryProducts`. -/
public theorem towerHppres (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a c : (towerSystem b nextStep).A i) (z : (towerSystem b nextStep).A j)
    (uu vv : z ⟶ (towerSystem b nextStep).F hij ((towerHp b nextStep i).prod a c))
    (hf : uu ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).fst =
        vv ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).fst)
    (hs : uu ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).snd =
        vv ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).snd) : uu = vv :=
  (@preservesBinaryProducts_jointly_monic _ _ (stageBundle nextStep b i.down).cat
    (stageBundle nextStep b j.down).cat (towerHp b nextStep i) (towerHp b nextStep j)
    (towerFunctF b nextStep hij)
    (towerF_preservesBinaryProducts b nextStep hij) a c) uu vv hf hs

/-- **`hppres_pair`** (pairing through `(F fst, F snd)`) from `towerF_preservesBinaryProducts`. -/
public theorem towerHppresPair (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a c : (towerSystem b nextStep).A i) (z : (towerSystem b nextStep).A j)
    (p : z ⟶ (towerSystem b nextStep).F hij a) (q : z ⟶ (towerSystem b nextStep).F hij c) :
    ∃ r : z ⟶ (towerSystem b nextStep).F hij ((towerHp b nextStep i).prod a c),
      r ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).fst = p ∧
      r ≫ (towerSystem b nextStep).Fmap hij (towerHp b nextStep i).snd = q :=
  @preservesBinaryProducts_pair _ _ (stageBundle nextStep b i.down).cat
    (stageBundle nextStep b j.down).cat (towerHp b nextStep i) (towerHp b nextStep j)
    (towerFunctF b nextStep hij)
    (towerF_preservesBinaryProducts b nextStep hij) a c z p q

/-- **`hepres`** (joint monicity of `F (eqMap)`) from `towerF_preservesEqualizers`. -/
public theorem towerHepres (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {X Y : (towerSystem b nextStep).A i} (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
    (uu vv : z ⟶ (towerSystem b nextStep).F hij
      (@eqObj _ ((towerSystem b nextStep).catA i) (towerHe b nextStep i) _ _ f g))
    (h : uu ≫ ((towerSystem b nextStep).functF hij).map
          (@eqMap _ ((towerSystem b nextStep).catA i) (towerHe b nextStep i) _ _ f g) =
        vv ≫ ((towerSystem b nextStep).functF hij).map
          (@eqMap _ ((towerSystem b nextStep).catA i) (towerHe b nextStep i) _ _ f g)) :
    uu = vv :=
  (@preservesEqualizers_mono _ _ (stageBundle nextStep b i.down).cat
    (stageBundle nextStep b j.down).cat (towerHe b nextStep i) (towerHe b nextStep j)
    (towerFunctF b nextStep hij)
    (towerF_preservesEqualizers b nextStep hij) X Y f g) uu vv h

/-- **`hepres_lift`** (lifting through `F (eqMap)`) from `towerF_preservesEqualizers`. -/
public theorem towerHepresLift (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {X Y : (towerSystem b nextStep).A i} (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
    (k : z ⟶ (towerSystem b nextStep).F hij X)
    (hk : k ≫ ((towerSystem b nextStep).functF hij).map f =
        k ≫ ((towerSystem b nextStep).functF hij).map g) :
    ∃ r : z ⟶ (towerSystem b nextStep).F hij
        (@eqObj _ ((towerSystem b nextStep).catA i) (towerHe b nextStep i) _ _ f g),
      r ≫ ((towerSystem b nextStep).functF hij).map
        (@eqMap _ ((towerSystem b nextStep).catA i) (towerHe b nextStep i) _ _ f g) = k :=
  @preservesEqualizers_lift _ _ (stageBundle nextStep b i.down).cat
    (stageBundle nextStep b j.down).cat (towerHe b nextStep i) (towerHe b nextStep j)
    (towerFunctF b nextStep hij)
    (towerF_preservesEqualizers b nextStep hij) X Y f g z k hk

/-- The cast `stageCastHom h` preserves monos (it is `Eq.rec`, an iso). -/
public theorem stageCastHom_preservesMono (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {m n : Nat} (h : m = n) {x y : (stageBundle nextStep b m).carrier} (φ : x ⟶ y)
    (hφ : @Monic _ (stageBundle nextStep b m).cat _ _ φ) :
    @Monic _ (stageBundle nextStep b n).cat _ _ (stageCastHom b nextStep h φ) := by
  subst h; exact hφ

/-- The cast `stageCastHom h` preserves covers. -/
public theorem stageCastHom_preservesCover (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {m n : Nat} (h : m = n) {x y : (stageBundle nextStep b m).carrier} (φ : x ⟶ y)
    (hφ : @Cover _ (stageBundle nextStep b m).cat _ _ φ) :
    @Cover _ (stageBundle nextStep b n).cat _ _ (stageCastHom b nextStep h φ) := by
  subst h; exact hφ

/-- **`hmono`** (the tower transition preserves monos): `towerFunctF.map φ = stageCastHom
    ((transNFun).map φ)`; `transN_preservesMono` gives the inner mono, `stageCastHom` preserves it. -/
public theorem towerHmono (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (φ : x ⟶ y)
    (hφ : @Monic _ ((towerSystem b nextStep).catA i) _ _ φ) :
    @Monic _ ((towerSystem b nextStep).catA j) _ _ (((towerSystem b nextStep).functF hij).map φ) :=
  stageCastHom_preservesMono b nextStep (Nat.add_sub_cancel' (show i.down ≤ j.down from hij))
    ((transNFun nextStep b i.down (j.down - i.down)).map φ)
    (transN_preservesMono b nextStep i.down (j.down - i.down) φ hφ)

/-- **`hcovpres`** (the tower transition preserves covers). -/
public theorem towerHcovpres (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {x y : (towerSystem b nextStep).A i} (φ : x ⟶ y)
    (hφ : @Cover _ ((towerSystem b nextStep).catA i) _ _ φ) :
    @Cover _ ((towerSystem b nextStep).catA j) _ _ (((towerSystem b nextStep).functF hij).map φ) :=
  stageCastHom_preservesCover b nextStep (Nat.add_sub_cancel' (show i.down ≤ j.down from hij))
    ((transNFun nextStep b i.down (j.down - i.down)).map φ)
    (transN_preservesCover b nextStep i.down (j.down - i.down) φ hφ)

/-- **`hcanon` for the ω-tower**, via the generic `colimitCanonicalCover` bridge: the on-the-nose
    terminal/products/equalizers preservation (above), cover-reflection `towerHfaith`/`towerHcons`,
    mono-preservation `towerHmono`, per-stage `PullbacksTransferCovers` (the bundled pre-regular's),
    and cover-preservation `towerHcovpres`. -/
public theorem towerHcanon (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier) :
    letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
    letI : HasPullbacks (towerSystem b nextStep).Obj :=
      colimitHasPullbacks _ (towerCoherent b nextStep) (towerHasTerminal b nextStep)
        (fun {_ _} hij => towerHtpres b nextStep hij) (towerHp b nextStep)
        (fun {_ _} hij a c z uu vv h1 h2 => towerHppres b nextStep hij a c z uu vv h1 h2)
        (fun {_ _} hij a c z p q => towerHppresPair b nextStep hij a c z p q)
        (towerHe b nextStep)
        (fun {_ _} hij _ _ f g z uu vv h => towerHepres b nextStep hij f g z uu vv h)
        (fun {_ _} hij _ _ f g z k hk => towerHepresLift b nextStep hij f g z k hk)
    ∀ {X Y Z : (towerSystem b nextStep).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂ :=
  colimitCanonicalCover (towerSystem b nextStep) (towerCoherent b nextStep)
    (towerHasTerminal b nextStep) (fun {_ _} hij => towerHtpres b nextStep hij)
    (towerHp b nextStep)
    (fun {_ _} hij a c z uu vv h1 h2 => towerHppres b nextStep hij a c z uu vv h1 h2)
    (fun {_ _} hij a c z p q => towerHppresPair b nextStep hij a c z p q)
    (towerHe b nextStep)
    (fun {_ _} hij _ _ f g z uu vv h => towerHepres b nextStep hij f g z uu vv h)
    (fun {_ _} hij _ _ f g z k hk => towerHepresLift b nextStep hij f g z k hk)
    (fun {_ _} hij _ _ p q h => towerHfaith b nextStep hij p q h)
    (fun {_ _} hij _ _ φ h => towerHcons b nextStep hij φ h)
    (fun {_ _} hij _ _ φ h => towerHmono b nextStep hij φ h)
    (fun i => (stageBundle nextStep b i.down).pre.toPullbacksTransferCovers)
    (fun {_ _} hij _ _ φ h => towerHcovpres b nextStep hij φ h)

/-- **§1.543 assembly from the tower.**  Given a uniform successor functor `nextStep` (the slice
    successor `(-)*`) and the full `colimitPreRegular` preservation package for the tower it
    generates, *plus* the capital-closure of the tower's colimit, the `CapData A` is assembled
    entirely from the now-built `towerSystem`/`towerCoherent`:
      * `base = id` (stage 0 is `A`), faithful by `idFunctor`/`Faithful.id`;
      * `hfaith`/`hcons` are `towerHfaith`/`towerHcons` (cast-drop + `transNFaithful`);
      * the preservation package and `capital` are passed through verbatim.
    This isolates the two genuine §1.543 ingredients — the successor `nextStep` and the capital
    closure `hcap` — as the *only* inputs; everything categorical (cast-coherence, faithfulness,
    colimit pre-regularity) is discharged here, and both inputs are themselves now supplied
    Sorry-free in `Freyd/CapDataWiring.lean`, so §1.543 is proven. -/
@[expose] public noncomputable def capData_of_tower (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (hb : b = ⟨A, inferInstance, inferInstance⟩)
    (ht : ∀ i, HasTerminal ((towerSystem b nextStep).A i))
    (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
      (towerSystem b nextStep).F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts ((towerSystem b nextStep).A i))
    (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst →
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd → uu = vv)
    (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (p : z ⟶ (towerSystem b nextStep).F hij a) (q : z ⟶ (towerSystem b nextStep).F hij c),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c),
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst = p ∧
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers ((towerSystem b nextStep).A i))
    (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij (eqObj f g)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) =
        vv ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j) (k : z ⟶ (towerSystem b nextStep).F hij X)
      (_hk : k ≫ ((towerSystem b nextStep).functF hij).map f =
        k ≫ ((towerSystem b nextStep).functF hij).map g),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij (eqObj f g),
        r ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) = k)
    (hcanon : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : HasPullbacks (towerSystem b nextStep).Obj :=
          colimitHasPullbacks _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
      ∀ {X Y Z : (towerSystem b nextStep).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcap : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : PreRegularCategory (towerSystem b nextStep).Obj :=
          colimitPreRegular _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
      Capital (𝒞 := (towerSystem b nextStep).Obj)) :
    CapData.{u} A := by
  -- stage 0 of the tower is `A` (since `b.carrier = A`), so the base embedding is the identity.
  subst hb
  exact
    { ι := ULift.{u} Nat
      D := uliftNatDirected
      C := towerSystem _ nextStep
      hC := towerCoherent _ nextStep
      hne := ⟨⟨0⟩⟩
      i₀ := ⟨0⟩
      base := id
      baseFun := idFunctor
      baseFaithful := ⟨fun _ _ h => h, fun _ h => h⟩
      hfaith := fun {i j} hij {x y} p q h => towerHfaith _ nextStep hij p q h
      hcons := fun {i j} hij {x y} φ hiso => towerHcons _ nextStep hij φ hiso
      ht := ht, htpres := htpres, hp := hp, hppres := hppres, hppres_pair := hppres_pair
      he := he, hepres := hepres, hepres_lift := hepres_lift, hcanon := hcanon, capital := hcap }

/-- **§1.543 — tower ⟹ `RegularCategory Ā`, image hypotheses ELIMINATED to the single `hi`.**

    `capData_of_tower` builds a (pre-regular) `CapData A` from the ω-tower preservation package.
    This packages the SAME inputs PLUS `hi` (every tower stage has IMAGES) and concludes a genuine
    `RegularCategory Ā` (capital, faithful `A → Ā`).  The transition mono/cover preservation needed
    by the image machinery is NOT a new hypothesis — it is supplied internally by the tower's own
    `towerHmono`/`towerHcovpres`, and the image-preservation is DERIVED from cover-preservation
    (`Colim.transitions_preserve_images`, via `capitalization_of_capData_regular_of_covers`).

    Hence the ONLY residual to make §2.218 R3(a) (`RegularCategory Ā`) unconditional is `hi`: each
    stage of the tower must have images.  Stage 0 is `A` (regular, if `[RegularCategory A]`); each
    successor `nextStep S` is a directed colimit of slices `S/B` (`overRegular`/`overHasImages` make
    the slices regular when `S` is), so its `HasImages` is itself a `colimitHasImages` of the inner
    slice system — derivable but requiring `CapStep`/`PreRegBundle` to *carry* the per-stage regular
    structure (an instance-level extension of those structures, deliberately not done here). -/
public theorem capData_of_tower_regular (A : Type u) [Cat.{u} A] [PreRegularCategory A]
    (nextStep : ∀ (S : PreRegBundle.{u}), CapStep S.carrier)
    (b : PreRegBundle.{u}) (hb : b = ⟨A, inferInstance, inferInstance⟩)
    (ht : ∀ i, HasTerminal ((towerSystem b nextStep).A i))
    (htpres : ∀ {i j} (hij : uliftNatDirected.le i j),
      (towerSystem b nextStep).F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts ((towerSystem b nextStep).A i))
    (hppres : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst →
      uu ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd =
        vv ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd → uu = vv)
    (hppres_pair : ∀ {i j} (hij : uliftNatDirected.le i j) (a c : (towerSystem b nextStep).A i)
      (z : (towerSystem b nextStep).A j)
      (p : z ⟶ (towerSystem b nextStep).F hij a) (q : z ⟶ (towerSystem b nextStep).F hij c),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij ((hp i).prod a c),
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).fst = p ∧
        r ≫ ((towerSystem b nextStep).functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers ((towerSystem b nextStep).A i))
    (hepres : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j)
      (uu vv : z ⟶ (towerSystem b nextStep).F hij (eqObj f g)),
      uu ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) =
        vv ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) → uu = vv)
    (hepres_lift : ∀ {i j} (hij : uliftNatDirected.le i j) {X Y : (towerSystem b nextStep).A i}
      (f g : X ⟶ Y) (z : (towerSystem b nextStep).A j) (k : z ⟶ (towerSystem b nextStep).F hij X)
      (_hk : k ≫ ((towerSystem b nextStep).functF hij).map f =
        k ≫ ((towerSystem b nextStep).functF hij).map g),
      ∃ r : z ⟶ (towerSystem b nextStep).F hij (eqObj f g),
        r ≫ ((towerSystem b nextStep).functF hij).map (eqMap f g) = k)
    (hcanon : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : HasPullbacks (towerSystem b nextStep).Obj :=
          colimitHasPullbacks _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift
      ∀ {X Y Z : (towerSystem b nextStep).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂)
    (hcap : letI : Cat (towerSystem b nextStep).Obj := colimitCat _ (towerCoherent b nextStep)
        letI : PreRegularCategory (towerSystem b nextStep).Obj :=
          colimitPreRegular _ (towerCoherent b nextStep) ht htpres hp hppres hppres_pair he
            hepres hepres_lift hcanon
      Capital (𝒞 := (towerSystem b nextStep).Obj))
    (hi : ∀ i, HasImages ((towerSystem b nextStep).A i)) :
    ∃ (Ā : Type u) (hC : Cat.{u} Ā) (hR : RegularCategory Ā),
      @Capital.{u, u} Ā hC (hR.toHasTerminal) ∧
      ∃ F : @Functor A Ā _ hC, @Faithful.{u, u} A _ Ā hC F := by
  -- normalize `b = ⟨A,…⟩` everywhere FIRST, so `capData_of_tower`'s internal `subst` and the
  -- `towerHmono`/`towerHcovpres` references all sit over the SAME bundle (`cd.C = towerSystem b _`).
  subst hb
  letI cd : CapData.{u} A :=
    capData_of_tower A nextStep _ rfl ht htpres hp hppres hppres_pair he hepres hepres_lift hcanon hcap
  refine capitalization_of_capData_regular_of_covers cd hi
    (fun {i j} hij => ?_) (fun {i j} hij => ?_)
  · exact fun {x y} {φ} hφ => towerHmono _ nextStep hij φ hφ
  · exact fun {x y} φ hφ => towerHcovpres _ nextStep hij φ hφ

/-! ## §1.546/§1.547  The uniform successor `nextStep` (RELOCATED from `RelativeCapitalization`)

  `nextStep : ∀ (S : PreRegBundle), CapStep S.carrier` and its supporting construction live HERE —
  in `Capitalization`, after `CapStep`/`PreRegBundle`, before `capData_exists` — so that
  `capData_exists`/`hwall_step` can NAME the §1.546/§1.547 successor in place (`RelativeCapitalization`
  imports `Capitalization` for `CapStep`, so it sits downstream and was unreachable from here).

  Everything below depends only on `CapStep` (above), the chain machinery (`PrefixChain`/
  `chainSliceSystem`/`chainHfaith`/`chainHcons` in `Inflation`, `chainSlicePreRegularWS` above) and
  the slice/inflation upstream — all already imported.  Pure relocation; no semantics changed. -/

section NextStep
variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
variable [PullbacksTransferCovers 𝒞]

/-- `∏[] = 1` is well-supported: `term 1 = id 1`, and the identity is a cover (a monic it
    factors through is split epi + mono = iso).  Inlined (`iso_cover` lives in the `HasImages`
    section of `S1_56`, unavailable here). -/
public theorem wellSupported_one : WellSupported (𝒞 := 𝒞) (listProd ([] : List 𝒞)) := by
  show Cover (term (HasTerminal.one : 𝒞))
  rw [show term (HasTerminal.one : 𝒞) = Cat.id HasTerminal.one from term_uniq _ _]
  intro C m g hm hgm
  -- `g ≫ m = id`, so `m` is split epi; `m` mono ⟹ `m` iso (`m ≫ g = id` by cancelling `m`).
  refine ⟨g, hm (m ≫ g) (Cat.id C) ?_, hgm⟩
  rw [Cat.assoc, hgm, Cat.id_comp]; exact Cat.comp_id m

omit [PullbacksTransferCovers 𝒞] in
/-- **Composition of covers is a cover** (images-free; `cover_comp`/`cover_mono_diagonal` in
    `S1_56` inherit a `HasImages` section variable, so we inline the pullback-diagonal fill that
    needs only `HasPullbacks`).  `f ≫ g` factors through a mono `m` via `h ≫ m = f ≫ g`; the
    pullback of `g` along `m` gives a mono `π₁` that `f` is a cover onto, hence `π₁` iso, hence a
    fill `f ≫ k = h`, and `g` a cover forces `m` iso.  (`omit`s the ambient `PullbacksTransferCovers`
    — genuinely unused; dropping it lets `S1_48_RationalCapitalization`'s `cover_comp''` forward
    to this lemma instead of re-proving it verbatim.) -/
public theorem cover_comp' {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Cover f) (hg : Cover g) :
    Cover (f ≫ g) := by
  intro C m h hm hfac
  -- diagonal fill: `f ≫ g = h ≫ m`, pullback of `g, m`, `π₁` mono (pullback of mono `m`).
  let pb := HasPullbacks.has g m
  -- `π₁` is mono (pullback of the mono `m`), inlined (`pullback_fst_mono` needs `HasImages`):
  have hπmono : Monic pb.cone.π₁ := by
    intro W p q hpq
    have hpq2 : p ≫ pb.cone.π₂ = q ≫ pb.cone.π₂ := by
      apply hm
      calc (p ≫ pb.cone.π₂) ≫ m = p ≫ (pb.cone.π₁ ≫ g) := by rw [Cat.assoc, ← pb.cone.w]
        _ = (q ≫ pb.cone.π₁) ≫ g := by rw [← Cat.assoc, hpq]
        _ = (q ≫ pb.cone.π₂) ≫ m := by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]
    let cn : Cone g m := ⟨W, p ≫ pb.cone.π₁, p ≫ pb.cone.π₂, by rw [Cat.assoc, Cat.assoc, pb.cone.w]⟩
    rw [pb.lift_uniq cn p rfl rfl, pb.lift_uniq cn q hpq.symm hpq2.symm]
  let u := pb.lift ⟨X, f, h, by rw [hfac]⟩
  have hu₁ : u ≫ pb.cone.π₁ = f := pb.lift_fst _
  obtain ⟨inv, _, hinvπ⟩ : IsIso pb.cone.π₁ := hf pb.cone.π₁ u hπmono hu₁
  -- `inv ≫ π₂` fills `(inv≫π₂) ≫ m = g`; then `g` a cover through `m` forces `m` iso.
  refine hg m (inv ≫ pb.cone.π₂) hm ?_
  rw [Cat.assoc, ← pb.cone.w, ← Cat.assoc, hinvπ, Cat.id_comp]

/-- **The product of two well-supported objects is well-supported.**  `term (B×D)` factors as
    `fst ≫ term B`; `fst : B×D → B` is a cover (`prod_fst_cover`, needs `D` well-supported) and
    `term B` is a cover (`B` well-supported), so the composite is a cover. -/
public theorem wellSupported_prod {B D : 𝒞} (hB : WellSupported B) (hD : WellSupported D) :
    WellSupported (prod B D) := by
  show Cover (term (prod B D))
  rw [show term (prod B D) = (fst : prod B D ⟶ B) ≫ term B from term_uniq _ _]
  exact cover_comp' (prod_fst_cover hD) hB

/-- **`∏U` is well-supported when every member of `U` is.** -/
theorem wellSupported_listProd : ∀ {U : List 𝒞}, (∀ B ∈ U, WellSupported B) →
    WellSupported (listProd U)
  | [],     _ => wellSupported_one
  | B :: U, h => by
      rw [listProd_cons]
      exact wellSupported_prod (h B (List.mem_cons.2 (Or.inl rfl)))
        (wellSupported_listProd (fun C hC => h C (List.mem_cons.2 (Or.inr hC))))

/-! ### The faithful base embedding `S → innerSliceObj ([] : Infl S)`

  Stage 0 of the chain (`chain 0 = []`) is `innerSliceObj [] = Over ([] : Infl S)`, the slice
  over the terminal of the inflation.  `S` embeds faithfully there by the inflation cross-section
  `infl : X ↦ [X]` (`inflFunctor`) followed by the (forgetting-nothing) slice over the terminal:
  `X ↦ ⟨[X], term⟩`, `f ↦ ⟨inflFunctor.map f, …⟩`.  Faithful because `infl` separates morphisms
  (`fst : X×1 → X` is a cover, `1` well-supported) and reflects isos. -/

/-- The object part of the base embedding: `X ↦ ⟨[X], term [X]⟩ : innerSliceObj ([] : Infl 𝒞)`. -/
def baseSliceObj (X : 𝒞) : innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞) :=
  ⟨(infl X : Infl 𝒞), term (infl X : Infl 𝒞)⟩

/-- The morphism part of the base embedding: `f : X → Y` becomes the over-hom whose underlying
    `Infl`-arrow is `inflFunctor.map f : [X] ⟶ [Y]` (commutes with `term` by `term_uniq`). -/
def baseSliceMap {X Y : 𝒞} (f : X ⟶ Y) :
    OverHom (baseSliceObj (𝒞 := 𝒞) X) (baseSliceObj Y) :=
  ⟨(inflFunctor.map f : (infl X : Infl 𝒞) ⟶ infl Y), term_uniq _ _⟩

/-- The base embedding `S → innerSliceObj []` is a functor: its underlying `Infl`-arrows are
    `inflFunctor`'s, so the laws transport along `OverHom.ext` (a slice equation is its underlying
    equation). -/
def baseSliceFunctor : Functor 𝒞 (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) where
  obj := baseSliceObj
  map {X Y} f := baseSliceMap f
  map_id X := OverHom.ext (by
    show (inflFunctor.map (Cat.id X) : (infl X : Infl 𝒞) ⟶ infl X) = Cat.id (infl X : Infl 𝒞)
    exact inflFunctor.map_id X)
  map_comp {X Y Z} f g := OverHom.ext (by
    show (inflFunctor.map (f ≫ g) : (infl X : Infl 𝒞) ⟶ infl Z)
        = (baseSliceMap f ⊚ baseSliceMap g).f
    exact inflFunctor.map_comp f g)

/-- `infl : 𝒞 → Infl 𝒞` (the cross-section `X ↦ [X]`, underlying `(·)×1`) SEPARATES MORPHISMS:
    `inflFunctor.map f = inflFunctor.map g ⟹ f = g`.  `inflFunctor.map h = pair (fst ≫ h) snd`
    (`prodRight 1`); projecting along `fst` gives `fst ≫ f = fst ≫ g`, and `fst : X×1 → X` is a
    cover (`prod_fst_cover`, `1` well-supported), hence epic (`cover_epi`).  Inlined here (the
    `S1_54` `slice_embedding_separates` it mirrors sits DOWNSTREAM — `S1_54` imports `Capitalization`). -/
theorem infl_separates {X Y : 𝒞} (f g : X ⟶ Y)
    (h : (inflFunctor.map f : (infl X : Infl 𝒞) ⟶ infl Y) = inflFunctor.map g) : f = g := by
  -- `inflFunctor.map h = pair (fst ≫ h) snd : prod X 1 ⟶ prod Y 1` (defeq by `inflHom_eq`).
  have hpair : pair ((fst : prod X HasTerminal.one ⟶ X) ≫ f) snd
      = pair ((fst : prod X HasTerminal.one ⟶ X) ≫ g) snd := h
  have hfst : (fst : prod X HasTerminal.one ⟶ X) ≫ f = (fst : prod X HasTerminal.one ⟶ X) ≫ g := by
    rw [← fst_pair ((fst : prod X HasTerminal.one ⟶ X) ≫ f) snd, hpair, fst_pair]
  exact cover_epi (prod_fst_cover wellSupported_one) hfst

/-- **`(·)×1` reflects isomorphisms**: `IsIso (pair (fst ≫ f) snd) ⟹ IsIso f`.  From `f×1` iso get
    `f×1` mono ⟹ `f` mono (`infl_separates`); and `fst_C ≫ f = (f×1) ≫ fst_D` makes `f` a cover
    (iso∘cover, right-factor); `monic_cover_iso` gives `f` iso.  (The `B = 1` case of `S1_54`'s
    `prodRight_reflects_iso`, inlined since `S1_54` is downstream of `Capitalization`.) -/
theorem inflMap_reflects_iso {C D : 𝒞} (f : C ⟶ D)
    (hiso : IsIso (pair ((fst : prod C HasTerminal.one ⟶ C) ≫ f) snd)) : IsIso f := by
  obtain ⟨inv, hinv1, _hinv2⟩ := hiso
  have hfBmono : Monic (pair ((fst : prod C HasTerminal.one ⟶ C) ≫ f) snd) :=
    mono_of_retraction _ inv hinv1
  have hfmono : Monic f := by
    intro Z u v huv
    refine infl_separates u v (hfBmono _ _ ?_)
    have e : (inflFunctor.map (u ≫ f) : (infl Z : Infl 𝒞) ⟶ infl D)
        = inflFunctor.map (v ≫ f) := by rw [huv]
    rw [inflFunctor.map_comp, inflFunctor.map_comp] at e
    exact e
  have hfcover : Cover f := by
    have hstep : (fst : prod C HasTerminal.one ⟶ C) ≫ f
        = pair ((fst : prod C HasTerminal.one ⟶ C) ≫ f) snd ≫ (fst : prod D HasTerminal.one ⟶ D) :=
      (fst_pair ((fst : prod C HasTerminal.one ⟶ C) ≫ f) snd).symm
    have hcov : Cover ((fst : prod C HasTerminal.one ⟶ C) ≫ f) := by
      rw [hstep]; exact cover_precomp_iso ⟨inv, hinv1, _hinv2⟩ (prod_fst_cover wellSupported_one)
    intro K m h hm hfac
    exact hcov m ((fst : prod C HasTerminal.one ⟶ C) ≫ h) hm (by rw [Cat.assoc, hfac])
  exact monic_cover_iso f hfcover hfmono

/-- **The base embedding `S → innerSliceObj []` is FAITHFUL.**  Embedding: equality of slice-images
    gives equality of underlying `Infl`-arrows `inflFunctor.map f = inflFunctor.map g`, separated by
    `infl_separates`.  Reflects-iso: a slice iso has iso underlying `inflFunctor.map f = pair (fst≫f) snd`,
    and `inflMap_reflects_iso` (with `1` well-supported) descends to `f`. -/
theorem baseSliceFaithful :
    Faithful (baseSliceFunctor (𝒞 := 𝒞)) := by
  refine ⟨?_, ?_⟩
  · -- embedding
    intro X Y f g h
    exact infl_separates f g (congrArg OverHom.f h)
  · -- reflects iso
    intro X Y f hiso
    have hfiso : IsIso (baseSliceMap f).f := overIso_underlying hiso
    exact inflMap_reflects_iso f hfiso

/-! ### The base embedding `S → innerSliceObj []` is a `CartesianFunctor`

  RELOCATED from `Freyd.RelativeCapitalization` (where it sat downstream and was unreachable from
  `nextStepOfEnum`).  All dependencies (`overHasTerminal`/`overHasBinaryProducts`/`overHasEqualizers`
  in `S1_44`/`SliceRegular`, `infl_preserves_isPullback` in `Inflation`,
  `sliceForget_reflects_isPullback_terminal` in `SliceRegular`,
  `pullbacks_terminal_implies_cartesianFunctor` in `S1_43`) are imported here.  Pure relocation. -/

/-- **The base embedding `S → innerSliceObj []` preserves the terminal.**  `baseSliceObj one =
    ⟨[1], term [1]⟩`; maps into it in `Over []` are determined by their underlying `Infl`-arrow, and
    two such agree because both projections land in the `𝒞`-terminal `1` (`term_uniq`). -/
theorem baseSliceObjPresTerminal :
    letI : HasTerminal (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) := overHasTerminal _
    @PreservesTerminal 𝒞 (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) _ _ baseSliceFunctor
      _ (overHasTerminal _) := by
  letI : HasTerminal (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) := overHasTerminal _
  intro X f g
  apply OverHom.ext
  show f.f = g.f
  have h1 : f.f ≫ (fst : prod HasTerminal.one HasTerminal.one ⟶ _) = g.f ≫ fst := term_uniq _ _
  have h2 : f.f ≫ (snd : prod HasTerminal.one HasTerminal.one ⟶ _) = g.f ≫ snd := term_uniq _ _
  exact fst_snd_jointly_monic f.f g.f h1 h2

section BaseSliceCartesian
variable [HasEqualizers 𝒞]

/-- `innerSliceObj [] = Over []` is Cartesian (terminal/products/equalizers from the `over*`
    instances, given `[HasEqualizers 𝒞]`). -/
@[expose] public instance innerSliceCartesianNilLoc : CartesianCategory (innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) where
  toHasTerminal := overHasTerminal _
  toHasBinaryProducts := overHasBinaryProducts _
  toHasEqualizers := overHasEqualizers _

/-- `𝒞` is Cartesian (terminal + binary products + equalizers, all in scope this section). -/
@[expose] public instance baseCartesianSelfLoc : CartesianCategory 𝒞 where
  toHasTerminal := inferInstance
  toHasBinaryProducts := inferInstance
  toHasEqualizers := inferInstance

/-- **Fact 1, the one missing obligation `hpull`.**  The `baseSliceObj`-image of the §1.432 chosen
    pullback cone of `(f, g)` is a pullback in `innerSliceObj [] = Over ([] : Infl 𝒞)`. -/
theorem baseSliceObj_pres_pullback {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) :
    Cone.IsPullback (𝒞 := innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞))
      { pt := baseSliceObj (products_equalizers_implies_pullbacks f g).cone.pt
        π₁ := baseSliceFunctor.map (products_equalizers_implies_pullbacks f g).cone.π₁
        π₂ := baseSliceFunctor.map (products_equalizers_implies_pullbacks f g).cone.π₂
        w  := by rw [← baseSliceFunctor.map_comp, ← baseSliceFunctor.map_comp,
                     (products_equalizers_implies_pullbacks f g).cone.w] } := by
  let P := products_equalizers_implies_pullbacks f g
  apply sliceForget_reflects_isPullback_terminal (𝒞 := Infl 𝒞)
  exact infl_preserves_isPullback P.cone P.cone_isPullback

/-- **§1.543 Fact 1.**  The faithful base embedding `S → innerSliceObj []` is a `CartesianFunctor`. -/
theorem baseSliceObjCartFunctor :
    CartesianFunctor (F := baseSliceFunctor (𝒞 := 𝒞)) :=
  pullbacks_terminal_implies_cartesianFunctor
    (F := baseSliceFunctor) (fun f g => baseSliceObj_pres_pullback f g)
    baseSliceObjPresTerminal

/-- An isomorphism is a cover (a mono it factors through is split epi + mono = iso).  Inlined here
    (`iso_cover` lives in `S1_56`, outside `Capitalization`'s import closure). -/
theorem isIso_is_cover {X Y : 𝒞} {e : X ⟶ Y} (he : IsIso e) : Cover e := by
  obtain ⟨e', he₁, he₂⟩ := he
  intro C m g hm hgm
  -- `m` iso with inverse `e' ≫ g`: `(e'≫g)≫m = e'≫(g≫m) = e'≫e = id`; and `m≫(e'≫g) = id` by mono.
  have hinvm : (e' ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, he₂]
  refine ⟨e' ≫ g, hm (m ≫ (e' ≫ g)) (Cat.id C) ?_, hinvm⟩
  rw [Cat.assoc, hinvm, Cat.comp_id, Cat.id_comp]

/-- **`baseSliceObj` preserves covers.**  `baseSliceMap φ` is a slice cover iff its underlying
    `Infl`-arrow `inflFunctor.map φ = pair (fst≫φ) snd = φ×1` is a cover (slice cover correspondence
    `cover_of_cover_f`); `φ×1 = fst ≫ φ ≫ (fst)⁻¹` conjugates `φ` by the `×1` unitors (`iso_cover`/
    `cover_comp'`), so `Cover φ ⟹ Cover (φ×1)` in `S`, then `coverC_to_inflCover` lifts it to `Infl S`. -/
theorem baseSlice_preservesCover [HasEqualizers 𝒞] {X Y : 𝒞} (φ : X ⟶ Y) (hφ : Cover φ) :
    Cover (𝒞 := innerSliceObj (𝒞 := 𝒞) ([] : List 𝒞)) (baseSliceFunctor.map φ) := by
  -- (1) `φ×1 = pair (fst≫φ) snd` is a cover in `S`: `(φ×1) ≫ fst = fst ≫ φ`, both `fst` iso.
  have hfstY : IsIso (fst : prod Y HasTerminal.one ⟶ Y) := prod_one_iso_right
  obtain ⟨invY, hinvY₁, hinvY₂⟩ := hfstY
  -- `φ×1 = fst_X ≫ (φ ≫ invY)` (cancel the iso `fst_Y` on the right of `(φ×1)≫fst = fst≫φ`).
  have hfact : pair ((fst : prod X HasTerminal.one ⟶ X) ≫ φ) snd
      = (fst : prod X HasTerminal.one ⟶ X) ≫ (φ ≫ invY) := by
    refine (pair_uniq _ _ _ ?_ ?_).symm
    · -- `(fst ≫ (φ ≫ invY)) ≫ fst = fst ≫ φ`: `invY ≫ fst = id`.
      rw [Cat.assoc, Cat.assoc, hinvY₂, Cat.comp_id]
    · -- `(fst ≫ (φ ≫ invY)) ≫ snd = snd`: both sides land in the terminal `1`.
      exact term_uniq _ _
  have hcov𝒞 : Cover (𝒞 := 𝒞) (pair ((fst : prod X HasTerminal.one ⟶ X) ≫ φ) snd) := by
    rw [hfact]
    exact cover_precomp_iso prod_one_iso_right
      (cover_comp' hφ (isIso_is_cover ⟨_, hinvY₂, hinvY₁⟩))
  -- (2) lift to a cover in `Infl S` (`coverC_to_inflCover`); the underlying arrow IS `inflFunctor.map φ`.
  have hcovInfl : Cover (𝒞 := Infl 𝒞) (X := (infl X : Infl 𝒞)) (Y := infl Y)
      (inflFunctor.map φ) := coverC_to_inflCover hcov𝒞
  -- (3) slice cover from underlying cover (`cover_of_cover_f`); `(baseSliceMap φ).f = inflFunctor.map φ`.
  intro Z m g hm hgm
  exact cover_of_cover_f (baseSliceMap φ) hcovInfl m g hm hgm

end BaseSliceCartesian

/-- **`PreservesEqualizers` is independent of the TARGET `HasEqualizers` instance.**  The two
    `HasEqualizers ℬ` instances give the SAME source comparison domain `F (eqObj f g)` (the source
    instance is fixed) and two chosen target equalizers of `(F f, F g)`; both are equalizers
    (`chosenEqualizer_isEqualizer`), so the comparison map for `e₂` is iso whenever the one for `e₁`
    is (`isIso_of_two_equalizers` against the shared cone `(F (eqObj f g), F (eqMap f g))`).  Lets the
    `objIncl`/comp equalizer-preservation (stated for `colimitHasEqualizers`) feed a field whose
    target equalizers are the `products_pullbacks_implies_equalizers` instance. -/
public theorem preservesEqualizers_target_irrel {𝒜 ℬ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ]
    (F : Functor 𝒜 ℬ) [heS : HasEqualizers 𝒜]
    (e₁ e₂ : HasEqualizers ℬ)
    (h : @PreservesEqualizers 𝒜 ℬ _ _ F heS e₁) :
    @PreservesEqualizers 𝒜 ℬ _ _ F heS e₂ := by
  intro A B f g
  -- the shared image cone `(F (eqObj f g), F (eqMap f g))` over `(F f, F g)`.
  let cone1 : EqualizerCone (F.map f) (F.map g) :=
    { dom := F.obj (eqObj f g), map := F.map (eqMap f g)
      eq := by rw [← F.map_comp, ← F.map_comp, eqMap_eq] }
  let cD1 := e₁.eq (F.obj A) (F.obj B) (F.map f) (F.map g)
  let cD2 := e₂.eq (F.obj A) (F.obj B) (F.map f) (F.map g)
  -- `cD1.cone` is an equalizer of `(F f, F g)` (its universal property).
  have hcD1 : cD1.cone.IsEqualizer := fun d => ⟨cD1.lift d, cD1.fac d, fun v hv => cD1.uniq d v hv⟩
  have hcD2 : cD2.cone.IsEqualizer := fun d => ⟨cD2.lift d, cD2.fac d, fun v hv => cD2.uniq d v hv⟩
  -- `e₁`'s comparison `k₁ := cD1.lift cone1 : F(eqObj) → cD1.dom` is iso (`h`); `k₁ ≫ cD1.map = cone1.map`.
  have hk1iso : IsIso (cD1.lift cone1) := h f g
  obtain ⟨k₁', hk₁k₁', hk₁'k₁⟩ := hk1iso
  -- transport `cD1.cone` (apex cD1.dom) onto apex `F(eqObj)` along `k₁` → `cone1` is an equalizer.
  have hcone1 : cone1.IsEqualizer := by
    have := isEqualizer_iso_apex (e := cD1.cone.map) (hfe := cD1.cone.eq)
      hcD1 (cD1.lift cone1) k₁' hk₁k₁' hk₁'k₁
    exact isEqualizer_map_congr (cD1.fac cone1) this
  -- the `e₂`-comparison `cD2.lift cone1` satisfies `· ≫ cD2.map = cone1.map`; both `cone1` and `cD2.cone`
  -- are equalizers, so it is iso — that IS the `e₂`-preservation goal.
  exact isIso_of_two_equalizers hcone1 hcD2 (cD2.lift cone1) (cD2.fac cone1)

/-- **Terminal preservation composes** (uniqueness form, with `G` preserving monos).  `F one_𝒜` is
    weakly terminal in `ℬ` (`hF`: maps into it are unique), so `term (F one_𝒜) : F one_𝒜 ⟶ one_ℬ` is
    monic; `G` preserves it (`hGmono`), and `hG` collapses maps into `G one_ℬ`, so any two maps into
    `G (F one_𝒜)` agree after the mono `G (term …)`, hence agree.  `preservesTerminal_comp` (in
    `CatColimitRegular`) is the on-the-nose form; this is the uniqueness form the `CapStep` field needs
    for the composite `objIncl i0 ∘ baseSliceObj`. -/
public theorem preservesTerminal_uniq_comp {𝒜 ℬ ℰ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ] [Cat.{u} ℰ]
    (F : Functor 𝒜 ℬ) (G : Functor ℬ ℰ)
    [HasTerminal 𝒜] [HasTerminal ℬ] [HasTerminal ℰ]
    (hpF : PreservesTerminal F) (hpG : PreservesTerminal G) (hGmono : PreservesMono G) :
    PreservesTerminal (compFunctor F G) := by
  intro X f g
  -- `t := term (F one) : F one ⟶ one_ℬ` is monic (maps into `F one` are unique, `hpF`).
  have htmono : Monic (term (F.obj (one : 𝒜))) := by
    intro Y p q _; exact hpF Y p q
  have hGtmono : Monic (G.map (term (F.obj (one : 𝒜)))) := hGmono htmono
  -- post-compose with the mono `G t`; the two composites land in `G one_ℬ`, equal by `hpG`.
  apply hGtmono
  exact hpG X (f ≫ G.map (term (F.obj (one : 𝒜)))) (g ≫ G.map (term (F.obj (one : 𝒜))))

/-- **`objIncl i` preserves monos**, given the transition mono-preservation `hmono`.  A stage mono
    `φ` stays left-cancellable under every later transition (`hmono` makes `(functF hij).map φ`
    monic), which is exactly the `hcancel` hypothesis of `homInclObj_mono_of_stage`. -/
public theorem objIncl_preservesMono {ι : Type u} {D : Colim.Directed ι}
    (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Monic φ → Monic (C.Fmap hij φ))
    (i : ι) :
    letI : Cat C.Obj := Colim.colimitCat C hC
    @PreservesMono (C.A i) (C.catA i) C.Obj (Colim.colimitCat C hC)
      (stageInclFunctor C hC i) := by
  letI : Cat C.Obj := Colim.colimitCat C hC
  intro x y φ hφ
  -- `(stageInclFunctor i).map φ = homInclObj φ`; use the stage-mono lift with `hcancel` from `hmono`.
  exact Colim.homInclObj_mono_of_stage C hC φ
    (fun {j} hij z u v huv => hmono hij φ hφ u v huv)

/-- **`objIncl i` preserves covers**, given the transition cover-preservation `hcovpres` and
    faithfulness `hfaith`.  A stage cover stays a cover under every later transition (`hcovpres`),
    which is the `hcov` hypothesis of `homInclObj_cover_of_stage`. -/
public theorem objIncl_preservesCover {ι : Type u} {D : Colim.Directed ι}
    (C : Colim.CatSystem.{u, u} ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        C.Fmap hij p = C.Fmap hij q → p = q)
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (φ : x ⟶ y),
        Cover φ → Cover (C.Fmap hij φ))
    {i : ι} {x y : C.A i} (φ : x ⟶ y) (hφ : Cover φ) :
    letI : Cat C.Obj := Colim.colimitCat C hC
    @Cover C.Obj (Colim.colimitCat C hC) _ _ ((stageInclFunctor C hC i).map φ) :=
  Colim.homInclObj_cover_of_stage C hC hfaith φ (fun hij => hcovpres hij φ hφ)

/-- **A pullback-preserving functor preserves monos.**  `f` monic ⟺ its canonical level diagonal
    `δ` is iso (`mono_iff_level_diag_iso`); `T` carries the level to a level of `T f` (`Level.map`,
    using `PreservesPullbacks T`), whose diagonal is `T δ` — iso by `functor_preserves_iso`; so
    `T f` is monic.  (`reflectsMono` in `S1_45` is the converse; this is the forward direction,
    needing no properness hypothesis.) -/
theorem preservesPullbacks_preservesMono {𝒜 ℬ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ]
    [HasTerminal 𝒜] [HasBinaryProducts 𝒜] [HasPullbacks 𝒜]
    (T : Functor 𝒜 ℬ) (hpb : PreservesPullbacks T) :
    PreservesMono T := by
  intro A B f hf
  let L := canonicalLevel f
  have hδ : IsIso L.δ := (mono_iff_level_diag_iso L).1 hf
  have hTδ : IsIso (T.map L.δ) := functor_preserves_iso (F := T) L.δ hδ
  -- `(L.map T hpb).δ = hT.map L.δ`, so the image-level diagonal is iso ⟹ `T f` monic.
  intro W p q hpq
  exact (mono_iff_level_diag_iso (L.map T hpb)).2 hTδ p q hpq

/-- Transport `Cone.IsPullback` across propositional equalities of the two legs (same apex). -/
public theorem isPullback_legs_congr {𝒟 : Type u} [Cat.{u} 𝒟] {A B C : 𝒟} {f : A ⟶ C} {g : B ⟶ C}
    {p : 𝒟} {π₁ π₁' : p ⟶ A} {π₂ π₂' : p ⟶ B} (h₁ : π₁ = π₁') (h₂ : π₂ = π₂')
    {w : π₁ ≫ f = π₂ ≫ g} (hc : (Cone.mk p π₁ π₂ w).IsPullback) :
    -- The cospan is named: a public statement elaborates in the public scope, where this `by` runs
    -- before `Cone.mk`'s implicits are solved and the goal still reads `π₁' ≫ ?f = π₂' ≫ ?g`.
    (Cone.mk (f := f) (g := g) p π₁' π₂' (by rw [← h₁, ← h₂]; exact w)).IsPullback := by
  subst h₁; subst h₂; exact hc

/-- **Chosen-pullback preservation upgrades to all-pullback preservation.**  If a functor `F`
    sends the §1.432 *chosen* pullback (`products_equalizers_implies_pullbacks`) of every cospan to
    a pullback cone, then `F` preserves ALL pullbacks.  An arbitrary pullback `c` of `(f, g)` is
    canonically iso (apex) to the chosen `P` (`isIso_of_two_pullbacks`); `isPullback_of_iso_apex`
    transports the chosen image-pullback along the `F`-image of that apex iso, and
    `isPullback_legs_congr` rewrites the transported legs `F m ≫ F P.πᵢ` to `F c.πᵢ`.  DRY hub for
    `baseSlice_preservesPullbacks` and (via `objIncl_preserves_pullbacks`)
    `objIncl_preservesPullbacks_generic`. -/
public theorem preservesPullbacks_of_chosenPullback {𝒜 ℬ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ]
    [HasBinaryProducts 𝒜] [HasEqualizers 𝒜] (F : Functor 𝒜 ℬ)
    (hchosen : ∀ {A B C : 𝒜} (f : A ⟶ C) (g : B ⟶ C),
      (Cone.mk (f := F.map f) (g := F.map g)
        (F.obj (products_equalizers_implies_pullbacks f g).cone.pt)
        (F.map (products_equalizers_implies_pullbacks f g).cone.π₁)
        (F.map (products_equalizers_implies_pullbacks f g).cone.π₂)
        (by rw [← F.map_comp, ← F.map_comp,
                (products_equalizers_implies_pullbacks f g).cone.w])).IsPullback) :
    PreservesPullbacks F := by
  intro A B C f g c hc
  let P := products_equalizers_implies_pullbacks f g
  have hP : P.cone.IsPullback := P.cone_isPullback
  obtain ⟨m, ⟨hm₁, hm₂⟩, _⟩ := hP c
  have hmiso : IsIso m := isIso_of_two_pullbacks hc hP m hm₁ hm₂
  have hPimg := hchosen f g
  have hmimg : IsIso (F.map m) := functor_preserves_iso (F := F) m hmiso
  obtain ⟨n, hn₁, hn₂⟩ := hmimg
  have hwleg : F.map P.cone.π₁ ≫ F.map f = F.map P.cone.π₂ ≫ F.map g := by
    rw [← F.map_comp, ← F.map_comp, P.cone.w]
  have hc' := isPullback_of_iso_apex hPimg (F.map m) n hn₁ hn₂
    (by show (F.map m ≫ F.map P.cone.π₁) ≫ F.map f
          = (F.map m ≫ F.map P.cone.π₂) ≫ F.map g
        rw [Cat.assoc, Cat.assoc, hwleg])
  have hleg₁ : F.map m ≫ F.map P.cone.π₁ = F.map c.π₁ := by rw [← F.map_comp, hm₁]
  have hleg₂ : F.map m ≫ F.map P.cone.π₂ = F.map c.π₂ := by rw [← F.map_comp, hm₂]
  exact isPullback_legs_congr hleg₁ hleg₂ hc'

/-- **`baseSliceObj` preserves pullbacks** (all cones).  The chosen-pullback preservation
    `baseSliceObj_pres_pullback` upgraded to all cones by the DRY hub
    `preservesPullbacks_of_chosenPullback`. -/
theorem baseSlice_preservesPullbacks [HasEqualizers 𝒞] :
    PreservesPullbacks (baseSliceFunctor (𝒞 := 𝒞)) :=
  preservesPullbacks_of_chosenPullback baseSliceFunctor (fun f g => baseSliceObj_pres_pullback f g)

/-! ### The enumeration `PrefixChain` and the well-supported-suffix condition `hwsuf`

  An enumeration `enum : ℕ → S` of (well-supported) objects yields the `take`-prefix chain
  `chain n := (List.range n).map enum = [enum 0, …, enum (n-1)]`.  It is a `PrefixChain`
  (`chain n <+: chain (n+1)` is `chain n ++ [enum n]`), starts at `chain 0 = []`, and — when every
  `enum k` is well-supported — every appended suffix `prefixSuffix (chain i) (chain j)` is a list of
  well-supported objects, so `∏(suffix)` is well-supported (`wellSupported_listProd`): exactly the
  `hwsuf` precondition `chainSlicePreRegularWS` consumes.  This is the §1.547 cofinal enumeration:
  for an enumeration that hits every well-supported `B`, the inner colimit acquires a point of every
  such `B` (`enumChain_acquires`), Freyd's relative-capitalization payoff. -/

/-- The `take`-prefix chain of an enumeration `enum : ℕ → S`: `chain n = [enum 0, …, enum (n-1)]`. -/
def enumPrefix (enum : Nat → 𝒞) (n : Nat) : List 𝒞 := (List.range n).map enum

@[simp] theorem enumPrefix_zero (enum : Nat → 𝒞) : enumPrefix enum 0 = [] := rfl

/-- `chain (n+1) = chain n ++ [enum n]` (append the next factor). -/
theorem enumPrefix_succ (enum : Nat → 𝒞) (n : Nat) :
    enumPrefix enum (n + 1) = enumPrefix enum n ++ [enum n] := by
  show (List.range (n + 1)).map enum = (List.range n).map enum ++ [enum n]
  rw [List.range_succ, List.map_append]; rfl

/-- The enumeration `PrefixChain` over `S` (objects are `Infl S = List S`).  Instances are bound
    EXPLICITLY (`@`-style) so the generalized signature carries `[Cat]/[HasTerminal]/[HasBinaryProducts]`
    at the SAME universe — relying on the `variable` auto-inclusion dropped them, which left the
    return `PrefixChain 𝒞` re-synthesizing those at a `max`-universe metavar at every use site. -/
def enumChain {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [PullbacksTransferCovers 𝒞] (enum : Nat → 𝒞) : PrefixChain 𝒞 where
  chain := enumPrefix enum
  step n := by rw [enumPrefix_succ]; exact List.prefix_append _ _

/-- Every entry of an appended suffix is some `enum k` (a member of a longer `take`-prefix). -/
theorem enumPrefix_suffix_mem (enum : Nat → 𝒞) {i j : Nat} (B : 𝒞)
    (hB : B ∈ prefixSuffix (enumPrefix enum i) (enumPrefix enum j)) : ∃ k, enum k = B := by
  -- the suffix is a `drop` of a `map enum`, so its members are members of `map enum`.
  have : B ∈ enumPrefix enum j := List.mem_of_mem_drop hB
  obtain ⟨k, _, hk⟩ := List.mem_map.1 this
  exact ⟨k, hk⟩

/-- `(enumPrefix enum (n+1)).length = n+1` (a `take`-prefix of length `n+1`). -/
theorem enumPrefix_length (enum : Nat → 𝒞) (n : Nat) : (enumPrefix enum n).length = n := by
  show ((List.range n).map enum).length = n
  rw [List.length_map, List.length_range]

/-- **The well-supported-suffix condition `hwsuf` for an enumeration of well-supported objects.**
    If every `enum k` is well-supported, every appended suffix `∏(prefixSuffix (chain i) (chain j))`
    is well-supported (`wellSupported_listProd`), which is exactly the precondition
    `chainSlicePreRegularWS` consumes to give the inner colimit `S*` a `PreRegularCategory`. -/
theorem enumChain_hwsuf (enum : Nat → 𝒞) (hws : ∀ k, WellSupported (enum k))
    {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j) :
    WellSupported
      (listProd (𝒞 := 𝒞)
        (prefixSuffix ((enumChain enum).toOrdChain.chain i) ((enumChain enum).toOrdChain.chain j))) := by
  apply wellSupported_listProd
  intro B hB
  obtain ⟨k, hk⟩ := enumPrefix_suffix_mem enum B hB
  rw [← hk]; exact hws k

end NextStep

/-! ### Assembling the uniform successor `nextStep`

  The inner colimit `S* = (chainSliceSystem (enumChain enum)).Obj` of the enumeration chain is a
  concrete `PreRegularCategory` (`chainSlicePreRegularWS`, fed `enumChain_hwsuf`), and `S` embeds
  faithfully via the base embedding into stage 0 composed with the (faithful) colimit stage-0
  inclusion (`baseSliceFaithful` ∘ `stageInclFaithful`).  That data is exactly a `CapStep S`.

  The two successor defs take `S`/`[PreRegularCategory S]` as EXPLICIT binders so `CapStep S`
  synthesizes its `[PreRegularCategory S]` and the chain-machinery instances resolve through
  `PreRegularCategory.extends`, with the universe pinned by the binders (a section-`variable` form
  left a `PrefixChain.{max …}` metavar — two live `HasTerminal` instances at a `max`-of-two-universes
  metavar).  Re-opening clean (NO `{𝒞}`/`[HasTerminal 𝒞] …` `variable`) pins the universe. -/

/-- **The relative-capitalization successor from an enumeration of well-supported objects.**
    `S* = (chainSliceSystem (enumChain enum)).Obj`, pre-regular by `chainSlicePreRegularWS` (fed
    `enumChain_hwsuf`).  The faithful embedding `S → S*` is the base embedding `S → innerSliceObj []`
    (stage 0; the enumeration chain has `chain 0 = []` DEFINITIONALLY, so `(chainSliceSystem _).A ⟨0⟩
    = innerSliceObj []` by `rfl` — no cast) followed by the faithful colimit stage-0 inclusion
    (`baseSliceFaithful` ∘ `stageInclFaithful`).  Sorry-free.  For an enumeration that hits every
    well-supported `B`, this is Freyd's §1.547 relative capitalization (the inner colimit acquires a
    point of every enumerated `B`).  `Classical`/ordinals are NOT used here — the enumeration is an
    explicit input. -/
noncomputable def nextStepOfEnum {S : Type u} [Cat.{u} S] [hreg : RegularCategory S]
    (enum : Nat → S) (hws : ∀ k, WellSupported (enum k)) : CapStep S := by
  letI hpre : PreRegularCategory S := inferInstance
  -- pin the four mixins at universe `u` (from the bundled `hpre`) so the chain machinery's
  -- instance args resolve monomorphically — otherwise `PrefixChain S` lands at a `max`-universe.
  letI : HasTerminal.{u,u} S := hpre.toHasTerminal
  letI : HasBinaryProducts.{u,u} S := hpre.toHasBinaryProducts
  letI : HasPullbacks.{u,u} S := hpre.toHasPullbacks
  letI : PullbacksTransferCovers.{u,u} S := hpre.toPullbacksTransferCovers
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  let P : PrefixChain S := enumChain (𝒞 := S) enum
  letI : Cat (chainSliceSystem P).Obj := colimitCat _ (chainSliceCoherent P)
  -- the well-supported-suffix precondition (discharges `hcanon` via `chainSlicePreRegularWS`).
  have hwsuf : ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
      WellSupported (listProd (𝒞 := S)
        (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j))) :=
    fun {i j} hij => enumChain_hwsuf enum hws hij
  -- stage 0: `chain 0 = []`, so `(chainSliceSystem P).A ⟨0⟩ = innerSliceObj []` definitionally.
  let i0 : ULift.{u} Nat := ⟨0⟩
  -- explicit `.{u,u}` universes: `stageIncl*`'s two universe params (`ι`, the colimit's `w`) are
  -- not pinned by unification here, leaving a `PrefixChain.{max …}` constraint; both are `u`.
  let hF0 : @Functor ((chainSliceSystem P).A i0) (chainSliceSystem P).Obj _ _ :=
    @stageInclFunctor.{u, u} (ULift.{u} Nat) uliftNatDirected
      (chainSliceSystem P) (chainSliceCoherent P) i0
  have hfaith0 : @Faithful ((chainSliceSystem P).A i0) _ (chainSliceSystem P).Obj _
      hF0 :=
    @stageInclFaithful.{u, u} (ULift.{u} Nat) uliftNatDirected (chainSliceSystem P) (chainSliceCoherent P)
      (fun {_ _} hij {_ _} p q h => chainHfaith P hij (hwsuf hij) p q h)
      (fun {_ _} hij {_ _} φ hiso => chainHcons P hij (hwsuf hij) φ hiso) i0
  exact
    { T := (chainSliceSystem P).Obj
      catT := colimitCat _ (chainSliceCoherent P)
      preT := chainSlicePreRegularWS (𝒞 := S) P hwsuf
      step := (chainSliceSystem P).objIncl i0 ∘ baseSliceObj (𝒞 := S)
      stepFun := compFunctor (baseSliceFunctor (𝒞 := S)) hF0
      stepFaithful := faithful_comp (F := baseSliceFunctor (𝒞 := S)) (G := hF0)
        (baseSliceFaithful (𝒞 := S)) hfaith0
      stepTerminal := by
        letI : HasTerminal (chainSliceSystem P).Obj :=
          colimitHasTerminal (chainSliceSystem P) (chainSliceCoherent P)
            (chainHasTerminal P) (chainHtpres P)
        letI : HasTerminal (innerSliceObj (𝒞 := S) ([] : List S)) := overHasTerminal _
        intro X f g
        exact preservesTerminal_uniq_comp (F := baseSliceFunctor (𝒞 := S))
          (G := hF0)
          (baseSliceObjCartFunctor (𝒞 := S)).pres_terminal
          (objIncl_preservesTerminal (chainSliceSystem P) (chainSliceCoherent P)
            (chainHasTerminal P) (chainHtpres P) i0)
          (objIncl_preservesMono (chainSliceSystem P) (chainSliceCoherent P)
            (fun {i j} hij {x y} φ hφ => ordChainHmono P.toOrdChain hij φ hφ) i0) X f g
      stepTerminalArrow := by
        -- EXISTENCE: a map `X ⟶ step one = X ⟶ objIncl i0 (baseSliceObj one)`.  Use the colimit
        -- terminal's `trm X` to land at `objIncl i0 (chainHasTerminal i0).one` (= colimit terminal
        -- by `objIncl_terminal_eq`), then the `objIncl i0`-image of a STAGE arrow
        -- `g : (chainHasTerminal i0).one ⟶ baseSliceObj one` in `Over []`.
        letI htCol : HasTerminal (chainSliceSystem P).Obj :=
          colimitHasTerminal (chainSliceSystem P) (chainSliceCoherent P)
            (chainHasTerminal P) (chainHtpres P)
        intro X
        -- stage arrow `g` in `(chainSliceSystem P).A i0 = innerSliceObj []`: an `OverHom` from the
        -- stage terminal `⟨[], id⟩` to `baseSliceObj one = ⟨[one], term⟩`.  Underlying `[] ⟶ [one]`
        -- is `pair (term _) (term _) : 1 ⟶ one×1`; the over-condition is `term`-uniqueness (`[]` term).
        let g : @Cat.Hom _ ((chainSliceSystem P).catA i0) (chainHasTerminal P i0).one
            (baseSliceObj (𝒞 := S) one) :=
          (⟨pair (term (listProd (𝒞 := S) ([] : List S))) (term (listProd (𝒞 := S) ([] : List S))),
            term_uniq _ _⟩ : OverHom _ _)
        -- target `objIncl i0 (chainHasTerminal i0).one = htCol.one` (the colimit terminal): both
        -- equal `objIncl (Classical.choice) (...).one` (the colimit terminal's apex) by
        -- `objIncl_terminal_eq`; `htCol.one` IS that apex definitionally.
        have hEq : htCol.one = (chainSliceSystem P).objIncl i0 (chainHasTerminal P i0).one :=
          objIncl_terminal_eq.{u} (chainSliceSystem P) (chainSliceCoherent P) (chainHasTerminal P)
            (chainHtpres P) (Classical.choice (inferInstanceAs (Nonempty (ULift.{u} Nat)))) i0
        exact castHom rfl hEq (htCol.trm X) ≫ (@stageInclFunctor.{u, u} (ULift.{u} Nat)
          uliftNatDirected (chainSliceSystem P) (chainSliceCoherent P) i0).map g
      stepProds := by
        letI : HasBinaryProducts (chainSliceSystem P).Obj :=
          (chainSlicePreRegularWS (𝒞 := S) P hwsuf).toHasBinaryProducts
        apply preservesBinaryProducts_comp (F := baseSliceFunctor (𝒞 := S))
          (G := hF0)
          (baseSliceObjCartFunctor (𝒞 := S)).pres_products
        exact objIncl_preservesBinaryProducts (chainSliceSystem P) (chainSliceCoherent P)
          (chainHasProducts P) (chainHppres P) (chainHppresPair P) i0
      stepEqs := by
        -- compose the two rung equalizer-preservations (target = `colimitHasEqualizers`), then
        -- transfer to the field's target instance `products_pullbacks_implies_equalizers`.
        letI heCol : HasEqualizers (chainSliceSystem P).Obj :=
          colimitHasEqualizers (chainSliceSystem P) (chainSliceCoherent P)
            (chainHasEqualizers P) (chainHepres P) (chainHepresLift P)
        let hGF := compFunctor (baseSliceFunctor (𝒞 := S)) hF0
        have hcomp : PreservesEqualizers hGF := by
          apply preservesEqualizers_comp (F := baseSliceFunctor (𝒞 := S))
            (G := hF0)
            (baseSliceObjCartFunctor (𝒞 := S)).pres_equalizers
          exact objIncl_preservesEqualizers (chainSliceSystem P) (chainSliceCoherent P)
            (chainHasEqualizers P) (chainHepres P) (chainHepresLift P) i0
        intro A' B' f g
        exact preservesEqualizers_target_irrel
          hGF heCol _ hcomp f g
      -- stepMono: `Monic (homInclObj i0 (baseSliceMap φ))` from `Monic φ`.  `baseSliceObj` preserves
      -- monos (pullback-preserving, `preservesPullbacks_preservesMono`+`baseSlice_preservesPullbacks`);
      -- `objIncl i0` lifts the stage mono to a colimit mono (`objIncl_preservesMono`+`ordChainHmono`).
      stepMono := fun {x y} φ hφ =>
        objIncl_preservesMono (chainSliceSystem P) (chainSliceCoherent P)
          (fun {i j} hij {x y} ψ hψ => ordChainHmono P.toOrdChain hij ψ hψ) i0
          (preservesPullbacks_preservesMono (baseSliceFunctor (𝒞 := S))
            (baseSlice_preservesPullbacks (𝒞 := S)) hφ)
      -- stepCover: `Cover (homInclObj i0 (baseSliceMap φ))` from `Cover φ`.  `baseSliceObj` preserves
      -- covers (`baseSlice_preservesCover`, via `coverC_to_inflCover`/`cover_of_cover_f`); `objIncl i0`
      -- lifts the stage cover to a colimit cover (`objIncl_preservesCover`, via `homInclObj_cover_of_stage`
      -- with `chainHfaith`/`ordChainHcovpres`).
      stepCover := fun {x y} φ hφ =>
        objIncl_preservesCover (chainSliceSystem P) (chainSliceCoherent P)
          (fun {i j} hij {p q} a b h => chainHfaith P hij (hwsuf hij) a b h)
          (fun {i j} hij {x y} ψ hψ => ordChainHcovpres P.toOrdChain hij ψ hψ) (i := i0)
          (φ := baseSliceFunctor.map φ) (baseSlice_preservesCover (𝒞 := S) φ hφ)
      -- (§1.543 decoupling) the former `stepImages :=` fill (the inner-slice-colimit `HasImages`,
      -- `chainSliceHasImages`) is removed with the `CapStep.stepImages` field; the regular path now
      -- gets this image data through `nextStepImages`/`RegCapStep` below, not through `CapStep`. }
       }

/-! ### The uniform polymorphic successor `nextStep`

  `nextStep : ∀ (S : PreRegBundle), CapStep S.carrier` is the uniform §1.546/§1.547 relative-
  capitalization successor the outer ω-tower (`stageBundle`/`towerSystem`) iterates.  It is
  `nextStepOfEnum` fed a Classical-chosen enumeration of well-supported objects.  ANY enumeration
  into well-supported objects works (the constant `1`-enumeration is always available, so the choice
  set is nonempty); `Classical.choice` picks one.

  COFINALITY CAVEAT (NOT a defect of `nextStep` itself): a *single* `ℕ`-indexed
  `enum` can be cofinal among the well-supported objects only when they are ℕ-enumerable.  For an
  uncountable carrier, pointing EVERY well-supported `B` needs the cofinal (object-indexed)
  successor, not this legacy `ℕ`-chain.  That cofinal route — and with it the capital fixpoint —
  is built downstream in `Freyd/CapDataWiring.lean` (`uniformStep`/`tower_capital_of_cofinal`),
  which is where §1.543 is closed PROVEN Sorry-free.  This legacy `nextStep` is nonetheless a
  genuine faithful pre-regular successor for every `S`, Sorry-free. -/

/-- A well-supported-valued enumeration of `S` always exists: the constant terminator `fun _ => 1`
    (`1` is well-supported, `wellSupported_one`).  This makes the `nextStep` choice set nonempty. -/
theorem exists_wellSupported_enum (S : Type u) [Cat.{u} S] [PreRegularCategory S] :
    ∃ enum : Nat → S, ∀ k, WellSupported (enum k) :=
  ⟨fun _ => HasTerminal.one, fun _ => wellSupported_one⟩

/-- **The uniform relative-capitalization successor `nextStep S : CapStep S.carrier`** — Freyd's
    `S ↦ S*` as the single polymorphic rung the outer ω-tower iterates.  `nextStepOfEnum` applied to
    a `Classical.choice`-picked well-supported enumeration (always available, `exists_wellSupported_enum`).
    Faithful pre-regular embedding `S → S*`, Sorry-free.  This is the §1.546/§1.547 keystone. -/
noncomputable def nextStep (S : SmallRegCat.{u}) : CapStep S.carrier :=
  nextStepOfEnum (Classical.choose (exists_wellSupported_enum S.carrier))
    (Classical.choose_spec (exists_wellSupported_enum S.carrier))

-- (§1.543 decoupling) `nextStepRegular` / `nextStep_hasImages` are COMMENTED OUT.  They were the only
-- consumers of the removed `CapStep.stepImages` field (and have ZERO consumers themselves — the §2.218
-- `RegularCategory Ā` path is not yet load-bearing).  They read the successor target's `HasImages` out
-- of the `CapStep` field; with images re-homed off `CapStep` (the field blocked the sorry-free
-- pre-regular `capData_exists`), reinstating them requires exposing `nextStepOfEnum`'s internal
-- `chainSliceHasImages` (its `PrefixChain P` is built internally).  Left out until the regular path is
-- needed; the pre-regular `capData_exists`/`capitalization_lemma` below do not use them.
--
-- noncomputable def nextStepRegular (S : SmallRegCat.{u}) :
--     @RegularCategory (nextStep S).T (nextStep S).catT := …  (used (nextStep S).stepImages)
-- noncomputable def nextStep_hasImages (S : SmallRegCat.{u}) :
--     @HasImages (nextStep S).T (nextStep S).catT := (nextStep S).stepImages

-- `capData_exists` (the §1.543 discharge) is RELOCATED to `Freyd.CapDataWiring` — it must reference
-- the §1.547 uniform successor (`uniformStep`/`wsCover`/`stepWellPoints_of_fibreDensity`), the
-- cofinal `hstage` (`hstage_of_cofinal`) and the capital fixpoint (`tower_capital_of_cofinal`), all
-- of which transitively IMPORT this file, so an in-place discharge here would be an import cycle.
-- The Sorry-free ω-tower package (`towerH*`/`capData_of_tower` above) is what that wiring consumes;
-- `Freyd.nextStep` here is the legacy countable successor, superseded by the cofinal `uniformStep`.
-- See `Freyd.CapDataWiring.capData_exists` — now PROVEN Sorry-free (the §1.546 `FibreDensity` input
-- it consumes is itself proven in `Freyd.FibreDensityProof`).

end Freyd
