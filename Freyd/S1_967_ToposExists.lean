/-
  Freyd & Scedrov, *Categories and Allegories* — internal disjunction `∨ : Ω×Ω → Ω`,
  the direct image `∃_f`, and (toward) binary coproducts, in a topos.

  Built on top of the now-available Sorry-free topos primitives:
    * `HasImages 𝒞`              (`InternalForallTopos.toposHasImages`)
    * `HasSubobjectUnions 𝒞`     (`ToposColimits.toposHasSubobjectUnions`)
    * the subobject classifier `Sub(A) ≅ Hom(A,Ω)` (`S1_91`: `subChar`, `classify_surjective`,
      `le_iff_classify`, `classify_eq_of_le_le`, `classify_invImg`).

  GOAL 1  internal disjunction `orChar : Ω×Ω → Ω` as `χ_{Sfst ∪ Ssnd}`, where
          `Sfst = fst#(true-sub)` and `Ssnd = snd#(true-sub)` are the two "coordinate true"
          subobjects of `Ω×Ω`.  Its lattice UMP is recorded below.

  GOAL 2  direct image `∃_f S := image (S.arr ≫ f)` for `f : A → B`, `S ⊆ A`, with the
          Galois adjunction `∃_f S ≤ T ↔ S ≤ f# T`.
-/

import Freyd.S1_91
import Freyd.S1_92
import Freyd.S1_45
import Freyd.S1_60
import Freyd.S1_94_InterIntersection
import Freyd.S1_94_InternalForallTopos
import Freyd.S1_95_ToposColimits
import Freyd.S1_946_ForallAlong
import Freyd.S1_56
import Freyd.S1_61
import Freyd.S1_94
import Freyd.S1_944_ToposStrictZero
import Freyd.S1_934_PartialMapClassifier

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## A topos is a pre-logos

  The §1.6 `PreLogos` structure (regular + subobject lattices + inverse image preserves
  finite unions and the empty join) is assembled here from the now-available topos primitives:
    * `RegularCategory` — `topos_is_regular_real` (`InternalForallTopos`/`S1_94`);
    * `HasSubobjectUnions` — `ToposColimits.toposHasSubobjectUnions`;
    * bottom `∅_A := bottomSub A` with `bottomSub_le` and the cross-base iso
      `bottomSub_dom_iso` (§1.944, `ToposStrictZero`);
    * `f#(S∪T) = f#S ∪ f#T` — the FRAME LAW `ForallAlong.invImage_preserves_union`
      (forward) and `inverseImage_mono` (reverse);
    * `f#(∅_B) ≅ ∅_A` — `invImage_bottomSub_dom_iso` (§1.946, `ToposStrictZero`).
  This is the `PreLogos 𝒞` instance the rest of the file (and the §1.621 disjoint-gluing
  copairing) needs, previously the missing link flagged in the residual note below. -/
/-- The frame law in the `inverseImage_preserves_unions` (PreLogos-field) shape, proved with
    the canonical topos instances OUTSIDE the structure builder to avoid the
    `PreLogos`-self-reference diamond.  FORWARD = `ForallAlong.invImage_preserves_union`
    (`f#` is a left adjoint), REVERSE = monotonicity (`inverseImage_mono`). -/
theorem topos_invImage_preserves_unions {A B : 𝒞} (f : A ⟶ B) :
    inverseImage_preserves_unions f := by
  intro S T
  refine And.intro ?_ ?_
  · exact invImage_preserves_union f S T
      (HasPullbacks.has f _) (HasPullbacks.has f _) (HasPullbacks.has f _)
  · -- `invImg_le` (PreLogos-free; `InverseImage f X = invImg f X (HasPullbacks.has ..)` defeq).
    exact HasSubobjectUnions.union_min _ _ _
      (invImg_le f S (HasSubobjectUnions.union S T) (HasPullbacks.has f _) (HasPullbacks.has f _)
        (HasSubobjectUnions.union_left S T))
      (invImg_le f T (HasSubobjectUnions.union S T) (HasPullbacks.has f _) (HasPullbacks.has f _)
        (HasSubobjectUnions.union_right S T))

noncomputable def toposPreLogos : PreLogos 𝒞 :=
  -- Build `RegularCategory` from the CANONICAL topos instances (`{ }` — all super-classes
  -- `HasImages`/`PullbacksTransferCovers`/… are already instances), so the resulting
  -- `PreLogos.toHasPullbacks`/`toHasImages` coincide with the topos's and there is no
  -- instance-diamond against `InverseImage`/`invImg`.  Bind `hReg`/`hUni` first so the
  -- forward field references during structure elaboration do not trigger a `PreLogos` search.
  let hReg : RegularCategory 𝒞 := { }
  letI _hUni : HasSubobjectUnions 𝒞 := toposHasSubobjectUnions
  { hReg with
    union       := HasSubobjectUnions.union
    union_left  := HasSubobjectUnions.union_left
    union_right := HasSubobjectUnions.union_right
    union_min   := HasSubobjectUnions.union_min
    bottom         := bottomSub (𝒞 := 𝒞)
    bottom_min     := @bottomSub_le 𝒞 _ _
    bottom_dom_iso := @bottomSub_dom_iso 𝒞 _ _
    invImage_preserves_union  := @topos_invImage_preserves_unions 𝒞 _ _
    invImage_preserves_bottom := @invImage_bottomSub_dom_iso 𝒞 _ _ }

/-- Make `toposPreLogos` available to instance search (so the §1.61 `DisjointGluing`
    relational layer and `disjoint_cover_is_coproduct` resolve under `[Topos 𝒞]`). -/
noncomputable instance : PreLogos 𝒞 := toposPreLogos

/-! ## Subobject ↔ classifier glue

  Every `χ : A → Ω` is `subChar` of *some* subobject (the pullback of `true` along `χ`).
  We package this choice as `subOfChar χ` with `subChar (subOfChar χ) = χ`, the workhorse
  for naming subobjects by their characteristic map. -/

/-- The subobject of `A` classified by `χ` (pullback of `true` along `χ`). -/
noncomputable def subOfChar {A : 𝒞} (χ : A ⟶ omega (𝒞 := 𝒞)) : Subobject 𝒞 A :=
  ⟨(classify_surjective χ).choose,
   (classify_surjective χ).choose_spec.choose,
   (classify_surjective χ).choose_spec.choose_spec.choose⟩

/-- A subobject equals (as `le` both ways) the subobject named by its own classifier — and
    more usefully: two subobjects with the same classifier are mutually `≤`. -/
theorem le_le_of_subChar_eq {A : 𝒞} {S T : Subobject 𝒞 A}
    (h : subChar S = subChar T) : S.le T ∧ T.le S := by
  constructor
  · rw [le_iff_classify]
    have : subChar S = subChar T := h
    show S.arr ≫ subChar T = _
    rw [← h]; exact (classify_sq S.arr S.monic)
  · rw [le_iff_classify]
    show T.arr ≫ subChar S = _
    rw [h]; exact (classify_sq T.arr T.monic)

/-! ## GOAL 1 — Internal disjunction `∨ : Ω×Ω → Ω` -/

/-- The "first coordinate is true" subobject of `Ω×Ω`: classified by `fst`. -/
noncomputable def trueFst : Subobject 𝒞 (prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞))) :=
  subOfChar fst

/-- The "second coordinate is true" subobject of `Ω×Ω`: classified by `snd`. -/
noncomputable def trueSnd : Subobject 𝒞 (prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞))) :=
  subOfChar snd

/-- **Internal disjunction** `∨ : Ω×Ω → Ω`: the classifier of the union of the two
    coordinate-true subobjects `{(⊤,·)} ∪ {(·,⊤)}` of `Ω×Ω`. -/
noncomputable def orChar : prod (omega (𝒞 := 𝒞)) (omega (𝒞 := 𝒞)) ⟶ omega (𝒞 := 𝒞) :=
  subChar (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) (trueSnd (𝒞 := 𝒞)))

/-- **`orChar` UMP, forward half (Sorry-free).**  `pair χ_S χ_T ≫ orChar` classifies a
    subobject of `A` that *contains* `S ∪ T`: i.e. `S ∪ T ≤ (pair χ_S χ_T)# (trueFst ∪ trueSnd)`,
    the subobject named by `⟨χ_S, χ_T⟩ ≫ orChar`.

    This is one half of `χ_{S∪T} = ⟨χ_S,χ_T⟩ ≫ orChar`.  The other half (`≤` the union)
    is exactly inverse-image-preserving-unions along `pair χ_S χ_T`, which is the frame /
    join-distributivity law `f#(X∪Y) ≤ f#X ∪ f#Y` — NOT a consequence of the bare join
    lattice laws, and not available at this layer (no `PreLogos 𝒞` instance for a topos yet;
    see residual note at end of file).  We therefore record the provable half here and the
    full equation as a precise residual rather than fake it. -/
theorem orChar_classifies_ge {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    (HasSubobjectUnions.union S T).le
      (invImg (pair (subChar S) (subChar T))
        (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd) hpU) := by
  -- S ≅ P# trueFst  and  T ≅ P# trueSnd  (same classifier).  P := pair χ_S χ_T.
  let P := pair (subChar S) (subChar T)
  have hSchar : subChar (invImg P trueFst hpF) = subChar S := by
    have h1 : subChar (invImg P trueFst hpF) = P ≫ subChar trueFst := classify_invImg P trueFst hpF
    rw [h1, show subChar (trueFst (𝒞 := 𝒞)) = fst from (classify_surjective _).choose_spec.choose_spec.choose_spec]
    exact fst_pair (subChar S) (subChar T)
  have hTchar : subChar (invImg P trueSnd hpS) = subChar T := by
    have h1 : subChar (invImg P trueSnd hpS) = P ≫ subChar trueSnd := classify_invImg P trueSnd hpS
    rw [h1, show subChar (trueSnd (𝒞 := 𝒞)) = snd from (classify_surjective _).choose_spec.choose_spec.choose_spec]
    exact snd_pair (subChar S) (subChar T)
  have hS_le : S.le (invImg P trueFst hpF) := (le_le_of_subChar_eq hSchar.symm).1
  have hT_le : T.le (invImg P trueSnd hpS) := (le_le_of_subChar_eq hTchar.symm).1
  have hF_le := invImg_le P trueFst (HasSubobjectUnions.union trueFst trueSnd) hpF hpU
    (HasSubobjectUnions.union_left trueFst trueSnd)
  have hG_le := invImg_le P trueSnd (HasSubobjectUnions.union trueFst trueSnd) hpS hpU
    (HasSubobjectUnions.union_right trueFst trueSnd)
  exact HasSubobjectUnions.union_min S T _ (Subobject.le_trans hS_le hF_le) (Subobject.le_trans hT_le hG_le)

/-- **`orChar` UMP, reverse half (now Sorry-free via the frame law).**  `(pair χ_S χ_T)#(trueFst∪trueSnd)
    ≤ S ∪ T`: inverse image preserves unions (`ForallAlong.invImage_preserves_union`), and each
    `(pair χ_S χ_T)# trueFst ≅ S`, `(pair χ_S χ_T)# trueSnd ≅ T`. -/
theorem orChar_classifies_le {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    (invImg (pair (subChar S) (subChar T))
        (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd) hpU).le
      (HasSubobjectUnions.union S T) := by
  let P := pair (subChar S) (subChar T)
  -- frame law: P#(trueFst∪trueSnd) ≤ P#trueFst ∪ P#trueSnd.
  have hframe := invImage_preserves_union P trueFst trueSnd hpU hpF hpS
  -- P#trueFst ≅ S, P#trueSnd ≅ T  (same classifier, as in orChar_classifies_ge).
  have hSchar : subChar (invImg P trueFst hpF) = subChar S := by
    have h1 : subChar (invImg P trueFst hpF) = P ≫ subChar trueFst := classify_invImg P trueFst hpF
    rw [h1, show subChar (trueFst (𝒞 := 𝒞)) = fst from (classify_surjective _).choose_spec.choose_spec.choose_spec]
    exact fst_pair (subChar S) (subChar T)
  have hTchar : subChar (invImg P trueSnd hpS) = subChar T := by
    have h1 : subChar (invImg P trueSnd hpS) = P ≫ subChar trueSnd := classify_invImg P trueSnd hpS
    rw [h1, show subChar (trueSnd (𝒞 := 𝒞)) = snd from (classify_surjective _).choose_spec.choose_spec.choose_spec]
    exact snd_pair (subChar S) (subChar T)
  have hFS : (invImg P trueFst hpF).le S := (le_le_of_subChar_eq hSchar).1
  have hGT : (invImg P trueSnd hpS).le T := (le_le_of_subChar_eq hTchar).1
  -- P#trueFst ∪ P#trueSnd ≤ S ∪ T  (union_min + union_left/right).
  have hunion_le : (HasSubobjectUnions.union (invImg P trueFst hpF) (invImg P trueSnd hpS)).le
      (HasSubobjectUnions.union S T) :=
    HasSubobjectUnions.union_min _ _ _
      (Subobject.le_trans hFS (HasSubobjectUnions.union_left S T))
      (Subobject.le_trans hGT (HasSubobjectUnions.union_right S T))
  exact Subobject.le_trans hframe hunion_le

/-- **`orChar` UMP (full, Sorry-free).**  `χ_{S∪T} = ⟨χ_S, χ_T⟩ ≫ orChar`: the internal
    disjunction `orChar` correctly classifies the union of any two subobjects via their
    classifiers.  Combines `orChar_classifies_ge` (≥) and `orChar_classifies_le` (≤). -/
theorem orChar_ump {A : 𝒞} (S T : Subobject 𝒞 A)
    (hpU : HasPullback (pair (subChar S) (subChar T))
      (HasSubobjectUnions.union (trueFst (𝒞 := 𝒞)) trueSnd).arr)
    (hpF : HasPullback (pair (subChar S) (subChar T)) (trueFst (𝒞 := 𝒞)).arr)
    (hpS : HasPullback (pair (subChar S) (subChar T)) (trueSnd (𝒞 := 𝒞)).arr) :
    subChar (HasSubobjectUnions.union S T)
      = pair (subChar S) (subChar T) ≫ orChar (𝒞 := 𝒞) := by
  -- orChar = subChar(trueFst∪trueSnd); ⟨χ_S,χ_T⟩ ≫ orChar = subChar (P#(trueFst∪trueSnd)).
  rw [orChar, ← classify_invImg (pair (subChar S) (subChar T))
    (HasSubobjectUnions.union trueFst trueSnd) hpU]
  -- χ_{S∪T} = χ_{P#(trueFst∪trueSnd)} by mutual ≤ (the two UMP halves).
  exact classify_eq_of_le_le
    (orChar_classifies_ge S T hpU hpF hpS)
    (orChar_classifies_le S T hpU hpF hpS)

/-! ## GOAL 2 — Direct image `∃_f` and the adjunction `∃_f ⊣ f#` -/

/-- **Direct image** `∃_f S ⊆ B` of a subobject `S ⊆ A` along `f : A → B`: the image of the
    composite `S ↣ A → B`.  (= the upstream `S1_60.existsAlong`; one canonical `image (arr ≫ f)`.) -/
noncomputable def directImage {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) : Subobject 𝒞 B :=
  existsAlong f S

/-- `S ≤ f# (∃_f S)`: the unit of the adjunction.  `S.arr ≫ f` factors through its own image. -/
theorem directImage_unit {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A)
    (hp : HasPullback f (directImage f S).arr) :
    S.le (invImg f (directImage f S) hp) := by
  -- S.arr ≫ f factors through directImage; lift it into the pullback f# (∃_f S).
  obtain ⟨u, hu⟩ := image_allows (S.arr ≫ f)
  -- the cone (S.dom, S.arr, u) over (f, (∃_f S).arr) commutes: S.arr ≫ f = u ≫ (∃_f S).arr.
  refine ⟨hp.lift ⟨S.dom, S.arr, u, hu.symm⟩, ?_⟩
  exact hp.lift_fst _

/-- The **Galois adjunction** `∃_f ⊣ f#`: `∃_f S ≤ T ↔ S ≤ f# T`. -/
theorem directImage_adjunction {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 A) (T : Subobject 𝒞 B)
    (hp : HasPullback f T.arr) :
    (directImage f S).le T ↔ S.le (invImg f T hp) := by
  constructor
  · -- ∃_f S ≤ T : compose S ≤ f#(∃_f S) ≤ f# T (inverse image monotone).
    intro hle
    have hpI : HasPullback f (directImage f S).arr := HasPullbacks.has _ _
    exact Subobject.le_trans (directImage_unit f S hpI) (invImg_le f (directImage f S) T hpI hp hle)
  · -- S ≤ f# T : then S.arr ≫ f factors through T, so T is an upper bound — image is minimal.
    intro hle
    -- f# T allows S.arr (S ≤ f# T), and (f# T).arr ≫ f factors through T via π₂.
    obtain ⟨k, hk⟩ := hle           -- k ≫ (f#T).arr = S.arr
    -- T allows S.arr ≫ f : via k ≫ π₂ (the second pullback leg lands in T).
    refine image_min (S.arr ≫ f) T ?_
    refine ⟨k ≫ hp.cone.π₂, ?_⟩
    -- (k ≫ π₂) ≫ T.arr = k ≫ (π₁ ≫ f) = (k ≫ π₁) ≫ f = S.arr ≫ f.
    -- `(invImg f T hp).arr` is definitionally `hp.cone.π₁`, so `hk : k ≫ π₁ = S.arr`.
    have hk' : k ≫ hp.cone.π₁ = S.arr := hk
    rw [Cat.assoc, ← hp.cone.w, ← Cat.assoc, hk']

/-! ## RESIDUALS — binary coproducts: what is DONE, and the one remaining piece

  DELIVERED Sorry-free (axioms ⊆ {propext, Classical.choice}):
    * `orChar` / `orChar_ump`  — internal disjunction `∨ : Ω×Ω → Ω` with its FULL UMP
      `χ_{S∪T} = ⟨χ_S,χ_T⟩ ≫ orChar` (closed via the now-proven frame law
      `ForallAlong.invImage_preserves_union`).
    * `directImage` / `directImage_unit` / `directImage_adjunction` — `∃_f ⊣ f#` (FULL).

  Binary coproducts `A + B ⊂ [A]×[B]` (GOAL 3 below), DELIVERED Sorry-free:
    * `coprodSub` / `coprodObj` / `coprodArr`  — the CARRIER `A+B = union (image inlRaw)
      (image inrRaw) ⊆ [A]×[B]` and its monic embedding.
    * `coprodInl` / `coprodInr`  — the two INJECTIONS, with `coprodInl_arr`/`coprodInr_arr`
      (`inl ≫ embed = inlRaw`, `inr ≫ embed = inrRaw`) and monicity `coprodInl_monic`/
      `coprodInr_monic`.
    * `coprod_jointly_epi`  — the INJECTIONS ARE JOINTLY EPIC (the `case_uniq` content):
      any two `h,k : A+B → X` with `inl≫h=inl≫k` and `inr≫h=inr≫k` are equal.  Proved
      ELEMENTARILY (equalizer of `h,k` + `image_min` + `union_min`; no frame law needed).
    * `casePMf`/`casePMg` + `casePMf_sq`/`casePMg_sq` — `f`,`g` as partial maps `A+B ⇀ X`
      (injections are monic) with their classify β-squares `inl ≫ χf = f ≫ η`, etc.

  THE ONE REMAINING PIECE — the copairing `case f g : A+B → X` (existence of a map with
  `inl ≫ case = f`, `inr ≫ case = g`).  This is the genuine §1.935 amalgamation and is NOT
  reducible to the join-lattice/PMC data already present, for a precise reason:

    To build `case` one must GLUE `f : A → X` and `g : B → X` into a single map out of
    `A+B`.  `A+B` is the subobject JOIN `union (image inl)(image inr)`; but a subobject join
    carries only a *map-IN* universal property (`union_left/right/min` — containment), NOT a
    *map-OUT* (colimit) one.  So there is no way to define the value `(A+B) → X` from `f,g`
    using `union`.  The partial-map classifier reduces only TOTALITY of a candidate
    `χ : A+B → X̃` (it factors through `η : X ↪ X̃` exactly on its domain of definition); it
    does NOT produce the candidate.  Producing `χ` (= the join `χf ∨ χg` of the two partial
    classifiers as a single TOTAL map) is exactly the missing amalgamation, and it requires
    the DISJOINTNESS of the two injection images (`image inl ⊓ image inr = ⊥` in `Sub(A+B)`,
    i.e. `({a},∅) ≠ (∅,{b})`, a non-degeneracy fact: a singleton is not the empty subobject)
    together with the union-COVER (`entire (A+B) = union (image inl)(image inr)`, the
    frame-law `f#`-union fact at `coprodArr`) to certify that the glued map is well-defined
    and total.  This "join of two partial maps over a disjoint cover" is precisely Freyd's
    §1.935 value-object amalgamation; it is the SINGLE residual.

  PRECISE MISSING-LEMMA SIGNATURE (closes `case`, hence the whole instance):

      theorem case_morphism_exists {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
          ∃ c : coprodObj A B ⟶ X, coprodInl A B ≫ c = f ∧ coprodInr A B ≫ c = g

  With `case_morphism_exists` in hand, `case := (case_morphism_exists f g).choose`, the two
  β-laws are its `.choose_spec`, and `case_uniq` is `coprod_jointly_epi`.  That assembles
  `instance toposHasBinaryCoproducts : HasBinaryCoproducts 𝒞`, and then
  `S1_95.topos_is_positive` becomes `exact toposHasBinaryCoproducts` — unblocking §1.954
  coequalizers (with `HasReflTransClosure`), §1.955 `topos_is_bicartesian`, and the strict
  coterminator `0`. -/

/-! ## GOAL 3 — Binary coproducts `A + B ⊂ [A] × [B]`

  Carrier:  `A + B := union (image inlRaw) (image inrRaw)  ⊆  [A] × [B]`, where
    * `inlRaw a := ({a}, ∅)`   — `pair (singletonMap A) (term A ≫ emptyName B)`,
    * `inrRaw b := (∅, {b})`   — `pair (term B ≫ emptyName A) (singletonMap B)`,
  with `∅ := nameOf (bottomSub _)` the global name of the empty subobject (the empty
  relation `1 → [·]`).  `coprodInl`/`coprodInr` are the two injections, factoring through
  the carrier by `union_left`/`union_right`. -/

/-- The global NAME `1 → [A]` of the empty subobject `∅ ⊆ A` (the empty element of `[A]`). -/
noncomputable def emptyName (A : 𝒞) : one (𝒞 := 𝒞) ⟶ powObj A :=
  nameOf (bottomSub A).arr (bottomSub A).monic

/-- The raw left injection `A → [A]×[B]`, `a ↦ ({a}, ∅)`. -/
noncomputable def inlRaw (A B : 𝒞) : A ⟶ prod (powObj A) (powObj B) :=
  pair (singletonMap A) (term A ≫ emptyName B)

/-- The raw right injection `B → [A]×[B]`, `b ↦ (∅, {b})`. -/
noncomputable def inrRaw (A B : 𝒞) : B ⟶ prod (powObj A) (powObj B) :=
  pair (term B ≫ emptyName A) (singletonMap B)

/-- The CARRIER subobject `A + B ⊆ [A]×[B]`: the union of the two singleton-image
    subobjects. -/
noncomputable def coprodSub (A B : 𝒞) : Subobject 𝒞 (prod (powObj A) (powObj B)) :=
  HasSubobjectUnions.union (image (inlRaw A B)) (image (inrRaw A B))

/-- The coproduct OBJECT `A + B` (domain of the carrier subobject). -/
noncomputable def coprodObj (A B : 𝒞) : 𝒞 := (coprodSub A B).dom

/-- The carrier inclusion `A + B ↪ [A]×[B]` (monic). -/
noncomputable def coprodArr (A B : 𝒞) : coprodObj A B ⟶ prod (powObj A) (powObj B) :=
  (coprodSub A B).arr

theorem coprodArr_monic (A B : 𝒞) : Monic (coprodArr A B) := (coprodSub A B).monic

/-- The chosen factorization `image (inlRaw) ≤ coprodSub` (from `union_left`). -/
noncomputable def imLeftToCarrier (A B : 𝒞) : (image (inlRaw A B)).dom ⟶ coprodObj A B :=
  (HasSubobjectUnions.union_left (image (inlRaw A B)) (image (inrRaw A B))).choose

theorem imLeftToCarrier_fac (A B : 𝒞) :
    imLeftToCarrier A B ≫ coprodArr A B = (image (inlRaw A B)).arr :=
  (HasSubobjectUnions.union_left (image (inlRaw A B)) (image (inrRaw A B))).choose_spec

noncomputable def imRightToCarrier (A B : 𝒞) : (image (inrRaw A B)).dom ⟶ coprodObj A B :=
  (HasSubobjectUnions.union_right (image (inlRaw A B)) (image (inrRaw A B))).choose

theorem imRightToCarrier_fac (A B : 𝒞) :
    imRightToCarrier A B ≫ coprodArr A B = (image (inrRaw A B)).arr :=
  (HasSubobjectUnions.union_right (image (inlRaw A B)) (image (inrRaw A B))).choose_spec

/-- **Left injection** `inl : A → A + B`: factor `inlRaw` through its image, then into the
    carrier union. -/
noncomputable def coprodInl (A B : 𝒞) : A ⟶ coprodObj A B :=
  image.lift (inlRaw A B) ≫ imLeftToCarrier A B

/-- **Right injection** `inr : B → A + B`. -/
noncomputable def coprodInr (A B : 𝒞) : B ⟶ coprodObj A B :=
  image.lift (inrRaw A B) ≫ imRightToCarrier A B

/-- `coprodInl ≫ carrier-inclusion = inlRaw`: the left injection composed with the carrier
    embedding is the raw map `a ↦ ({a}, ∅)`. -/
theorem coprodInl_arr (A B : 𝒞) : coprodInl A B ≫ coprodArr A B = inlRaw A B := by
  rw [coprodInl, Cat.assoc, imLeftToCarrier_fac, image.lift_fac]

theorem coprodInr_arr (A B : 𝒞) : coprodInr A B ≫ coprodArr A B = inrRaw A B := by
  rw [coprodInr, Cat.assoc, imRightToCarrier_fac, image.lift_fac]

/-- `inlRaw` is monic: `inlRaw ≫ fst = singletonMap A`, which is monic. -/
theorem inlRaw_monic (A B : 𝒞) : Monic (inlRaw A B) := by
  intro W u v huv
  refine singletonMap_monic A u v ?_
  have : (u ≫ inlRaw A B) ≫ fst = (v ≫ inlRaw A B) ≫ fst := by rw [huv]
  rwa [Cat.assoc, Cat.assoc, inlRaw, fst_pair] at this

/-- `inrRaw` is monic: `inrRaw ≫ snd = singletonMap B`, which is monic. -/
theorem inrRaw_monic (A B : 𝒞) : Monic (inrRaw A B) := by
  intro W u v huv
  refine singletonMap_monic B u v ?_
  have : (u ≫ inrRaw A B) ≫ snd = (v ≫ inrRaw A B) ≫ snd := by rw [huv]
  rwa [Cat.assoc, Cat.assoc, inrRaw, snd_pair] at this

/-- **`inl` is monic.**  `coprodInl ≫ coprodArr = inlRaw` is monic, so `coprodInl` is. -/
theorem coprodInl_monic (A B : 𝒞) : Monic (coprodInl A B) := by
  intro W u v huv
  refine inlRaw_monic A B u v ?_
  rw [← coprodInl_arr, ← Cat.assoc, ← Cat.assoc, huv]

/-- **`inr` is monic.** -/
theorem coprodInr_monic (A B : 𝒞) : Monic (coprodInr A B) := by
  intro W u v huv
  refine inrRaw_monic A B u v ?_
  rw [← coprodInr_arr, ← Cat.assoc, ← Cat.assoc, huv]

/-- **Joint epimorphism of the injections.**  `coprodInl` and `coprodInr` are jointly epic:
    any two maps out of `A + B` agreeing after `inl` and `inr` are equal.  This is the
    cover-by-injections fact (`case_uniq` content), proved elementarily via the equalizer of
    the two maps: both injections factor through it, so their image subobjects lie in it, so the
    whole carrier (the union of those images) lies in it — forcing the equalizer to be entire. -/
theorem coprod_jointly_epi {A B X : 𝒞} (h k : coprodObj A B ⟶ X)
    (hl : coprodInl A B ≫ h = coprodInl A B ≫ k)
    (hr : coprodInr A B ≫ h = coprodInr A B ≫ k) : h = k := by
  -- E = equalizer of h, k, with monic inclusion e : E ↪ A+B.
  let e : eqObj h k ⟶ coprodObj A B := eqMap h k
  have he_mono : Monic e := eqMap_monic h k
  let E : Subobject 𝒞 (coprodObj A B) := ⟨eqObj h k, e, he_mono⟩
  -- both injections factor through E.
  let l₁ : A ⟶ eqObj h k := eqLift h k (coprodInl A B) hl
  have hl₁ : l₁ ≫ e = coprodInl A B := eqLift_fac h k _ hl
  let l₂ : B ⟶ eqObj h k := eqLift h k (coprodInr A B) hr
  have hl₂ : l₂ ≫ e = coprodInr A B := eqLift_fac h k _ hr
  -- ⟨E, e ≫ coprodArr⟩ : a subobject of [A]×[B] (e and coprodArr both monic).
  have hec_mono : Monic (e ≫ coprodArr A B) := by
    intro W u v huv
    exact he_mono u v ((coprodArr_monic A B) _ _ (by rw [Cat.assoc, Cat.assoc, huv]))
  let Ec : Subobject 𝒞 (prod (powObj A) (powObj B)) := ⟨eqObj h k, e ≫ coprodArr A B, hec_mono⟩
  -- inlRaw and inrRaw both factor through Ec (via l₁, l₂), so the two image subobjects ≤ Ec.
  have him_l : (image (inlRaw A B)).le Ec := by
    refine image_min (inlRaw A B) Ec ⟨l₁, ?_⟩
    show l₁ ≫ (e ≫ coprodArr A B) = inlRaw A B
    rw [← Cat.assoc, hl₁, coprodInl_arr]
  have him_r : (image (inrRaw A B)).le Ec := by
    refine image_min (inrRaw A B) Ec ⟨l₂, ?_⟩
    show l₂ ≫ (e ≫ coprodArr A B) = inrRaw A B
    rw [← Cat.assoc, hl₂, coprodInr_arr]
  -- the carrier (union of the two images) lies in Ec.
  have hcarrier_le : (coprodSub A B).le Ec := HasSubobjectUnions.union_min _ _ _ him_l him_r
  -- coprodSub = ⟨coprodObj, coprodArr⟩, so we get j : coprodObj → E with j ≫ (e ≫ coprodArr) = coprodArr.
  obtain ⟨j, hj⟩ := hcarrier_le
  -- j ≫ e = id (coprodArr monic), so e is split epi; combined with monic ⇒ e iso.
  have hje : j ≫ e = Cat.id (coprodObj A B) := by
    apply coprodArr_monic A B
    rw [Cat.assoc]
    show (j ≫ (e ≫ coprodArr A B)) = Cat.id (coprodObj A B) ≫ coprodArr A B
    rw [Cat.id_comp]
    exact hj
  -- j ≫ e = id (coprodObj); compose with the equalizer identity to cancel.
  have heq_hk : e ≫ h = e ≫ k := eqMap_eq h k
  calc h = (j ≫ e) ≫ h := by rw [hje]; exact (Cat.id_comp h).symm
    _ = j ≫ (e ≫ h) := (Cat.assoc _ _ _)
    _ = j ≫ (e ≫ k) := by rw [heq_hk]
    _ = (j ≫ e) ≫ k := (Cat.assoc _ _ _).symm
    _ = k := by rw [hje]; exact Cat.id_comp k

/-! ### Copairing `case f g` via the partial-map classifier of `X`

  Given `f : A → X`, `g : B → X`, pick a lawful PMC `(X̃, η : X ↪ X̃)` for `X`.  The two
  injections are monic, so `f`/`g` are genuine partial maps `A+B ⇀ X`:
    `Pf := ⟨A, coprodInl, f⟩`,  `Pg := ⟨B, coprodInr, g⟩`.
  Their classifiers `χf := classify Pf`, `χg := classify Pg : A+B → X̃` satisfy the β-square
    `coprodInl ≫ χf = f ≫ η`,  `coprodInr ≫ χg = g ≫ η`.  -/

/-- The left partial map `A+B ⇀ X` carried by `f` (defined on the `inl` copy of `A`). -/
noncomputable def casePMf {A B X : 𝒞} (f : A ⟶ X) : PartialMap 𝒞 (coprodObj A B) X :=
  ⟨A, coprodInl A B, coprodInl_monic A B, f⟩

/-- The right partial map `A+B ⇀ X` carried by `g`. -/
noncomputable def casePMg {A B X : 𝒞} (g : B ⟶ X) : PartialMap 𝒞 (coprodObj A B) X :=
  ⟨B, coprodInr A B, coprodInr_monic A B, g⟩

theorem casePMg_sq {A B X : 𝒞} (L : LawfulPMC 𝒞 X) (g : B ⟶ X) :
    coprodInr A B ≫ L.classify (casePMg (A := A) g) = g ≫ L.eta :=
  L.classify_sq (casePMg (A := A) g)

/-! ### Copairing `[f,g]` as the graph of a functional, total relation

  The honest map-OUT.  We avoid the map-IN-only `union` colimit gap by building the
  copairing as the unique morphism whose GRAPH is the subobject

      `caseUnionSub f g := union (image (pair inl f)) (image (pair inr g)) ⊆ (A+B) × X`,

  the union of the two "partial graphs".  Tabulating that subobject as a relation
  `caseRel : (A+B) ⇸ X` (left leg `U.arr ≫ fst`, right leg `U.arr ≫ snd`), the two facts

    * `caseRel.colA` is a COVER  (TOTALITY: both injections factor through it, and the
       injections jointly cover `A+B` — `coprod_injections_cover`); and
    * `caseRel.colA` is MONIC    (FUNCTIONALITY / single-valuedness: the two partial
       graphs agree wherever their first coordinates coincide),

  make `caseRel` the graph of a unique morphism `c : A+B → X`
  (`functional_total_relation_is_graph`, classifier-free), and the two β-laws
  `inl ≫ c = f`, `inr ≫ c = g` fall out of the two image-factorizations.  No subobject
  map-OUT, no global non-degeneracy is used: functionality is the *local agreement*
  fact, vacuous on the disjoint part and forced by collapse on any overlap. -/

/-- The left "partial graph" subobject `{(inl a, f a)} ⊆ (A+B) × X`. -/
noncomputable def graphInlSub {A B X : 𝒞} (f : A ⟶ X) : Subobject 𝒞 (prod (coprodObj A B) X) :=
  image (pair (coprodInl A B) f)

/-- The right "partial graph" subobject `{(inr b, g b)} ⊆ (A+B) × X`. -/
noncomputable def graphInrSub {A B X : 𝒞} (g : B ⟶ X) : Subobject 𝒞 (prod (coprodObj A B) X) :=
  image (pair (coprodInr A B) g)

/-- The copairing graph `{(inl a, f a)} ∪ {(inr b, g b)} ⊆ (A+B) × X`. -/
noncomputable def caseUnionSub {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    Subobject 𝒞 (prod (coprodObj A B) X) :=
  HasSubobjectUnions.union (graphInlSub f) (graphInrSub g)

/-- The copairing relation `(A+B) ⇸ X` tabulated by the union graph. -/
noncomputable def caseRel {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    BinRel 𝒞 (coprodObj A B) X where
  src  := (caseUnionSub f g).dom
  colA := (caseUnionSub f g).arr ≫ fst
  colB := (caseUnionSub f g).arr ≫ snd
  isMonicPair := by
    intro W u v hA hB
    refine (caseUnionSub f g).monic u v ?_
    have hfst : (u ≫ (caseUnionSub f g).arr) ≫ fst = (v ≫ (caseUnionSub f g).arr) ≫ fst := by
      simpa [Cat.assoc] using hA
    have hsnd : (u ≫ (caseUnionSub f g).arr) ≫ snd = (v ≫ (caseUnionSub f g).arr) ≫ snd := by
      simpa [Cat.assoc] using hB
    calc u ≫ (caseUnionSub f g).arr
        = pair ((u ≫ (caseUnionSub f g).arr) ≫ fst) ((u ≫ (caseUnionSub f g).arr) ≫ snd) :=
          (pair_uniq _ _ _ rfl rfl)
      _ = pair ((v ≫ (caseUnionSub f g).arr) ≫ fst) ((v ≫ (caseUnionSub f g).arr) ≫ snd) := by
          rw [hfst, hsnd]
      _ = v ≫ (caseUnionSub f g).arr := (pair_uniq _ _ _ rfl rfl).symm

/-- **Injections jointly cover `A+B`.**  A monic `m : C ↣ A+B` through which both
    `coprodInl` and `coprodInr` factor is an iso.  (Same equalizer/`union_min` argument as
    `coprod_jointly_epi`, repackaged as a covering statement: the images of the two
    injections inside `A+B` union to the whole carrier.) -/
theorem coprod_injections_cover {A B C : 𝒞} (m : C ⟶ coprodObj A B) (hm : Monic m)
    (sl : A ⟶ C) (hsl : sl ≫ m = coprodInl A B)
    (sr : B ⟶ C) (hsr : sr ≫ m = coprodInr A B) : IsIso m := by
  -- `Cm := ⟨C, m ≫ coprodArr⟩ ⊆ [A]×[B]` (composite of two monics).
  have hmc_mono : Monic (m ≫ coprodArr A B) := by
    intro W u v huv
    exact hm u v ((coprodArr_monic A B) _ _ (by rw [Cat.assoc, Cat.assoc, huv]))
  let Cm : Subobject 𝒞 (prod (powObj A) (powObj B)) := ⟨C, m ≫ coprodArr A B, hmc_mono⟩
  -- Both raw injections factor through `Cm`: `inlRaw = sl ≫ (m ≫ coprodArr)` etc.
  have him_l : (image (inlRaw A B)).le Cm := by
    refine image_min (inlRaw A B) Cm ⟨sl, ?_⟩
    show sl ≫ (m ≫ coprodArr A B) = inlRaw A B
    rw [← Cat.assoc, hsl, coprodInl_arr]
  have him_r : (image (inrRaw A B)).le Cm := by
    refine image_min (inrRaw A B) Cm ⟨sr, ?_⟩
    show sr ≫ (m ≫ coprodArr A B) = inrRaw A B
    rw [← Cat.assoc, hsr, coprodInr_arr]
  -- The carrier (union of the two images) lies in `Cm`.
  have hcarrier_le : (coprodSub A B).le Cm := HasSubobjectUnions.union_min _ _ _ him_l him_r
  obtain ⟨j, hj⟩ := hcarrier_le
  -- `j ≫ m = id` (cancel the monic `coprodArr`), so `m` is split epi; with `m` monic, iso.
  have hjm : j ≫ m = Cat.id (coprodObj A B) := by
    apply coprodArr_monic A B
    rw [Cat.assoc]
    show (j ≫ (m ≫ coprodArr A B)) = Cat.id (coprodObj A B) ≫ coprodArr A B
    rw [Cat.id_comp]; exact hj
  -- `m ≫ j = id`: `(m ≫ j) ≫ m = m ≫ (j ≫ m) = m = id ≫ m`, cancel `m` monic.
  have hmj : m ≫ j = Cat.id C := hm _ _ (by
    rw [Cat.assoc, hjm, Cat.comp_id, Cat.id_comp])
  exact ⟨j, hmj, hjm⟩

/-- The left injection factors through the copairing relation's left leg. -/
theorem caseRel_inl_factor {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    ∃ s : A ⟶ (caseRel f g).src, s ≫ (caseRel f g).colA = coprodInl A B := by
  -- `pair inl f` factors through its image `graphInlSub ≤ caseUnionSub`.
  obtain ⟨w, hw⟩ := HasSubobjectUnions.union_left (graphInlSub f) (graphInrSub g)
  -- hw : w ≫ (caseUnionSub f g).arr = (graphInlSub f).arr = (image (pair inl f)).arr
  refine ⟨image.lift (pair (coprodInl A B) f) ≫ w, ?_⟩
  have hsU : (image.lift (pair (coprodInl A B) f) ≫ w) ≫ (caseUnionSub f g).arr
      = pair (coprodInl A B) f := by
    rw [Cat.assoc]
    show image.lift (pair (coprodInl A B) f)
        ≫ (w ≫ (HasSubobjectUnions.union (graphInlSub f) (graphInrSub g)).arr) = _
    rw [hw]; exact image.lift_fac _
  show (image.lift (pair (coprodInl A B) f) ≫ w) ≫ ((caseUnionSub f g).arr ≫ fst) = coprodInl A B
  rw [← Cat.assoc, hsU]; exact fst_pair _ _

/-- The right injection factors through the copairing relation's left leg. -/
theorem caseRel_inr_factor {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    ∃ s : B ⟶ (caseRel f g).src, s ≫ (caseRel f g).colA = coprodInr A B := by
  obtain ⟨w, hw⟩ := HasSubobjectUnions.union_right (graphInlSub f) (graphInrSub g)
  refine ⟨image.lift (pair (coprodInr A B) g) ≫ w, ?_⟩
  have hsU : (image.lift (pair (coprodInr A B) g) ≫ w) ≫ (caseUnionSub f g).arr
      = pair (coprodInr A B) g := by
    rw [Cat.assoc]
    show image.lift (pair (coprodInr A B) g)
        ≫ (w ≫ (HasSubobjectUnions.union (graphInlSub f) (graphInrSub g)).arr) = _
    rw [hw]; exact image.lift_fac _
  show (image.lift (pair (coprodInr A B) g) ≫ w) ≫ ((caseUnionSub f g).arr ≫ fst) = coprodInr A B
  rw [← Cat.assoc, hsU]; exact fst_pair _ _

/-- **TOTALITY.**  `caseRel.colA` is a cover: both injections factor through it and they
    jointly cover `A+B`. -/
theorem caseRel_colA_cover {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    Cover (caseRel f g).colA := by
  intro C m gg hm hgm
  -- Both injections factor through `caseRel.colA = gg ≫ m`, hence through the monic `m`.
  obtain ⟨sl₀, hsl₀⟩ := caseRel_inl_factor f g
  obtain ⟨sr₀, hsr₀⟩ := caseRel_inr_factor f g
  refine coprod_injections_cover m hm (sl₀ ≫ gg) ?_ (sr₀ ≫ gg) ?_
  · rw [Cat.assoc, hgm, hsl₀]
  · rw [Cat.assoc, hgm, hsr₀]

/-! ### Disjointness of the two injections

  The §1.621 disjointness `image inl ⊓ image inr = ⊥`, in the form the pasting lemma
  `DisjointGluing.disjoint_cover_is_coproduct` wants: the pullback of `coprodInl`, `coprodInr`
  has apex `≅ (bottom (A+B)).dom = 0`.  PROVEN from the EMPTY-SINGLETON non-degeneracy, with
  NO `DisjointBinaryCoproduct` class assumption: a common point `(a,b)` with `inl a = inr b`
  forces (post-`coprodArr`, take `fst`) `{a} = ∅` in `[A]`; but `a ∈ {a} = ⊤` (`mem_singleton_self`)
  while `a ∈ ∅ = ⊥`, so the apex maps to `0`, hence is `≅ 0` by strict-initiality. -/
theorem coprodInjections_disjoint (A B : 𝒞) :
    Isomorphic (HasPullbacks.has (coprodInl A B) (coprodInr A B)).cone.pt
      (bottomSub (coprodObj A B)).dom := by
  let pb := HasPullbacks.has (coprodInl A B) (coprodInr A B)
  let I : 𝒞 := pb.cone.pt
  let p₁ : I ⟶ A := pb.cone.π₁
  let p₂ : I ⟶ B := pb.cone.π₂
  have hsq : p₁ ≫ coprodInl A B = p₂ ≫ coprodInr A B := pb.cone.w
  -- post-compose the monic `coprodArr`:  p₁ ≫ inlRaw = p₂ ≫ inrRaw.
  have hraw : p₁ ≫ inlRaw A B = p₂ ≫ inrRaw A B := by
    rw [← coprodInl_arr, ← coprodInr_arr, ← Cat.assoc, ← Cat.assoc, hsq]
  -- take `fst`:  p₁ ≫ {·}_A = (p₂ ≫ term) ≫ emptyName A = term I ≫ emptyName A  (= "{p₁} = ∅_A").
  have hfst : p₁ ≫ singletonMap A = term I ≫ emptyName A := by
    have h : (p₁ ≫ inlRaw A B) ≫ fst = (p₂ ≫ inrRaw A B) ≫ fst := by rw [hraw]
    rw [Cat.assoc, Cat.assoc, inlRaw, inrRaw, fst_pair, fst_pair] at h
    rw [h, ← Cat.assoc]; congr 1; exact term_uniq (p₂ ≫ term B) (term I)
  -- "p₁ ∈ ∅_A = ⊤":  p₁ ≫ χ_{∅_A} = ⊤∘! .  (membershipMap (emptyName A) = χ_{∅_A}; then
  --   p₁ ≫ χ_{∅_A} = ⟨p₁, term ≫ emptyName A⟩ ≫ eval = ⟨p₁, p₁ ≫ {·}⟩ ≫ eval = ⊤∘! by mem_singleton_self.)
  have hmem : membershipMap (emptyName A) =
      HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic :=
    membershipMap_nameOf _ _
  have hp₁_class : p₁ ≫ HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic
      = term I ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    have h1 : p₁ ≫ HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic
        = pair p₁ (term I ≫ emptyName A) ≫ eval_exp A (omega (𝒞 := 𝒞)) := by
      rw [← hmem, membershipMap, ← Cat.assoc]
      congr 1
      exact pair_uniq _ _ _
        (by rw [Cat.assoc, fst_pair, Cat.comp_id])
        (by rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (p₁ ≫ term A) (term I)])
    rw [h1, ← hfst, mem_singleton_self]
  -- classifier UMP lifts `p₁` through `∅_A`:  e : I → (bottomSub A).dom.
  obtain ⟨e, ⟨he_arr, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback (bottomSub A).arr (bottomSub A).monic
      ⟨I, p₁, term I, hp₁_class⟩
  -- e : I → ∅_A.dom ≅ ∅_1.dom = 0;  strict-initiality ⇒ I ≅ 0 ≅ ∅_{A+B}.dom.
  obtain ⟨θ, hθ⟩ := bottomSub_dom_iso A (one : 𝒞)
  let z : I ⟶ (bottomSub (one : 𝒞)).dom := e ≫ θ
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  have hI_iso_Z : Isomorphic I (bottomSub (one : 𝒞)).dom := ⟨z, hz_iso⟩
  exact isomorphic_trans hI_iso_Z (bottomSub_dom_iso (one : 𝒞) (coprodObj A B))

/-- **§1.621 disjointness, elementwise (topos form).**  If two generalized elements are
    identified across the two injections (`p ≫ coprodInl = q ≫ coprodInr`), their common
    domain `X` is INITIAL: any two maps out of `X` agree.  Lifts `(p, q)` into the pullback
    of `(coprodInl, coprodInr)` — which `coprodInjections_disjoint` shows is `≅ 0` — then
    `(bottomSub one).dom`'s strict-coterminator uniqueness collapses maps out of `X`.  Keeps
    the pullback/instance plumbing INSIDE the topos layer, so callers never compose across
    two `HasPullbacks` instances. -/
theorem coprodInjections_disjoint_elt {A B X : 𝒞} (p : X ⟶ A) (q : X ⟶ B)
    (hpq : p ≫ coprodInl A B = q ≫ coprodInr A B) :
    ∀ {Y : 𝒞} (u v : X ⟶ Y), u = v := by
  let pb := HasPullbacks.has (coprodInl A B) (coprodInr A B)
  let w : X ⟶ pb.cone.pt := pb.lift ⟨X, p, q, hpq⟩
  obtain ⟨f0, _⟩ := coprodInjections_disjoint A B
  obtain ⟨θ, _⟩ := bottomSub_dom_iso (coprodObj A B) (one : 𝒞)
  let m' : X ⟶ (bottomSub (one : 𝒞)).dom := (w ≫ f0) ≫ θ
  obtain ⟨mi, hm1, _hm2⟩ := strict_coterminator_bottomSub_one m'
  intro Y u v
  have key : ∀ z : X ⟶ Y, z = m' ≫ (mi ≫ z) := by
    intro z; rw [← Cat.assoc, hm1, Cat.id_comp]
  rw [key u, key v,
      strictCoterminator_hom_unique strict_coterminator_bottomSub_one (mi ≫ u) (mi ≫ v)]

/-- The two injections as SUBOBJECTS of `A+B` (monic). -/
noncomputable def inlSubobj (A B : 𝒞) : Subobject 𝒞 (coprodObj A B) :=
  ⟨A, coprodInl A B, coprodInl_monic A B⟩
noncomputable def inrSubobj (A B : 𝒞) : Subobject 𝒞 (coprodObj A B) :=
  ⟨B, coprodInr A B, coprodInr_monic A B⟩

/-- **§1.621 cover**: `image inl ∪ image inr = A+B` — the union of the two injection
    subobjects is ENTIRE (its inclusion is iso), since both injections factor through it and
    they jointly cover the carrier (`coprod_injections_cover`). -/
theorem coprodInjections_union_entire (A B : 𝒞) :
    (HasSubobjectUnions.union (inlSubobj A B) (inrSubobj A B)).IsEntire := by
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left (inlSubobj A B) (inrSubobj A B)
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right (inlSubobj A B) (inrSubobj A B)
  exact coprod_injections_cover _ (HasSubobjectUnions.union (inlSubobj A B) (inrSubobj A B)).monic
    l₁ hl₁ l₂ hl₂

/-- **The copairing `c : A+B → X`** with `inl ≫ c = f`, `inr ≫ c = g`, plus uniqueness.
    Freyd's §1.621 disjoint-complemented-union pasting (`disjoint_cover_is_coproduct`),
    instantiated at the two injection subobjects with disjointness `coprodInjections_disjoint`
    and joint cover `coprodInjections_union_entire`. -/
theorem case_morphism_exists {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    ∃ c : coprodObj A B ⟶ X, coprodInl A B ≫ c = f ∧ coprodInr A B ≫ c = g :=
  let ⟨c, h1, h2, _⟩ :=
    disjoint_cover_is_coproduct (inlSubobj A B) (inrSubobj A B)
      (coprodInjections_disjoint A B) (coprodInjections_union_entire A B) f g
  ⟨c, h1, h2⟩

/-- **FUNCTIONALITY.**  `caseRel.colA` is monic: the union graph is single-valued.  The two
    partial graphs agree wherever their first coordinates coincide — and that agreement is
    realized by the honest copairing `c` (`case_morphism_exists`, from §1.621 disjoint gluing):
    `caseRel ⊆ graph c`, and a graph is simple, so `caseRel` is simple, i.e. `colA` is monic. -/
theorem caseRel_colA_monic {A B X : 𝒞} (f : A ⟶ X) (g : B ⟶ X) :
    Monic (caseRel f g).colA := by
  obtain ⟨c, hcl, hcr⟩ := case_morphism_exists f g
  -- The graph subobject `G = {(p, p ≫ c)} ⊆ (A+B)×X`, carried by the monic `pair id c`.
  have hG_mono : Monic (pair (Cat.id (coprodObj A B)) c) := by
    intro W u v huv
    have h : (u ≫ pair (Cat.id (coprodObj A B)) c) ≫ fst
        = (v ≫ pair (Cat.id (coprodObj A B)) c) ≫ fst := by rw [huv]
    rwa [Cat.assoc, Cat.assoc, fst_pair, Cat.comp_id, Cat.comp_id] at h
  let G : Subobject 𝒞 (prod (coprodObj A B) X) := ⟨coprodObj A B, pair (Cat.id _) c, hG_mono⟩
  -- Both partial graphs factor through `G` (via `inl`/`inr`), since `inl ≫ c = f`, `inr ≫ c = g`.
  have hInl_G : (graphInlSub f).le G :=
    image_min (pair (coprodInl A B) f) G ⟨coprodInl A B,
      pair_uniq (coprodInl A B) f (coprodInl A B ≫ G.arr)
        (by show (coprodInl A B ≫ pair (Cat.id _) c) ≫ fst = coprodInl A B
            rw [Cat.assoc, fst_pair, Cat.comp_id])
        (by show (coprodInl A B ≫ pair (Cat.id _) c) ≫ snd = f
            rw [Cat.assoc, snd_pair, hcl])⟩
  have hInr_G : (graphInrSub g).le G :=
    image_min (pair (coprodInr A B) g) G ⟨coprodInr A B,
      pair_uniq (coprodInr A B) g (coprodInr A B ≫ G.arr)
        (by show (coprodInr A B ≫ pair (Cat.id _) c) ≫ fst = coprodInr A B
            rw [Cat.assoc, fst_pair, Cat.comp_id])
        (by show (coprodInr A B ≫ pair (Cat.id _) c) ≫ snd = g
            rw [Cat.assoc, snd_pair, hcr])⟩
  -- so the union `caseUnionSub = U` factors through `G`:  j with `j ≫ G.arr = U.arr`.
  obtain ⟨j, hj⟩ := HasSubobjectUnions.union_min (graphInlSub f) (graphInrSub g) G hInl_G hInr_G
  -- KEY: `caseRel.colA ≫ c = caseRel.colB`, i.e. `U.arr ≫ fst ≫ c = U.arr ≫ snd`.
  have hkey : (caseRel f g).colA ≫ c = (caseRel f g).colB := by
    show (((HasSubobjectUnions.union (graphInlSub f) (graphInrSub g)).arr) ≫ fst) ≫ c
        = (HasSubobjectUnions.union (graphInlSub f) (graphInrSub g)).arr ≫ snd
    rw [← hj, Cat.assoc, Cat.assoc, Cat.assoc]
    -- `G.arr ≫ fst ≫ c = pair id c ≫ fst ≫ c = c` and `G.arr ≫ snd = pair id c ≫ snd = c`.
    show j ≫ (pair (Cat.id _) c ≫ (fst ≫ c)) = j ≫ (pair (Cat.id _) c ≫ snd)
    rw [← Cat.assoc (pair (Cat.id _) c) fst c, fst_pair, Cat.id_comp, snd_pair]
  -- `caseRel ≤ graph c` (witness `colA`), and graphs are simple ⟹ caseRel simple ⟹ colA monic.
  rw [← tabulated_is_simple_iff_left_monic (caseRel f g).colA (caseRel f g).colB
    (caseRel f g).isMonicPair]
  have hle : RelLe (caseRel f g) (graph c) :=
    ⟨⟨(caseRel f g).colA, Cat.comp_id _, hkey⟩⟩
  exact rel_le_trans (compose_le (reciprocal_mono hle) hle) (graph_is_map c).2

/-! ## GOAL 3 (assembled) — a topos has binary coproducts

  The carrier `A+B = coprodObj A B`, injections `coprodInl`/`coprodInr`, copairing
  `case f g := (case_morphism_exists f g).choose` with its two β-laws (`.choose_spec`) and
  uniqueness `coprod_jointly_epi`.  Sorry-free; axioms `[propext, Classical.choice]`. -/
noncomputable instance toposHasBinaryCoproducts : HasBinaryCoproducts 𝒞 where
  coprod   := coprodObj
  inl      := coprodInl _ _
  inr      := coprodInr _ _
  case f g := (case_morphism_exists f g).choose
  case_inl f g := (case_morphism_exists f g).choose_spec.1
  case_inr f g := (case_morphism_exists f g).choose_spec.2
  case_uniq f g h hl hr := coprod_jointly_epi h ((case_morphism_exists f g).choose)
    (by rw [hl, (case_morphism_exists f g).choose_spec.1])
    (by rw [hr, (case_morphism_exists f g).choose_spec.2])

end Freyd
