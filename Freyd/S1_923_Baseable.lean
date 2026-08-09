/-
  Freyd & Scedrov, *Categories and Allegories* §1.923 — KEYSTONE (SORRY-FREE).

  In a topos (terminal + binary products + subobject classifier + a power object
  `[C]` for every `C`), EVERY object `B` is BASEABLE — i.e. the exponential `B^A`
  exists for every `A`.  This is the input to `S1_92 :: topos_has_exponentials`.

  We follow Freyd's ACTUAL argument (book p.9343-9359, Kock's simplification
  "exponentiation is a consequence of power-objects"), NOT functional/total
  relations:

    (1) Any object `P` carrying a UNIVERSAL relation targeted at `C` is baseable,
        with `P^A ≅ [A×C]`.  The bijection
          `Hom(A×X, P) ≅ BinRel(A×X, C) ≅ BinRel(X, A×C) ≅ Hom(X, [A×C])`
        is built from the relation transpose `relCurry`/`relUncurry` (axiom-free),
        its naturality `relCurry_natural`, and universality of the relation.
        ⟹ `baseable_of_universalRel`; specialized to `∈_C` ⟹ `baseable_powerObj`.
    (2) `Ω = [1]`: the universal subobject `t : 1 ↣ Ω` is a universal relation
        targeted at `1` (`trueRel_universal`), so `Ω` is baseable (`baseable_omega`).
    (3) Every `B` is the equalizer of `χ_{·} , ⊤∘! : [B] ⇉ Ω`, the classifying
        square of the singleton mono `{·} : B ↣ [B]` (`all_baseable`).
    (4) `[B]` and `Ω` baseable + §1.859 equalizer-closure
        (`baseable_equalizer_is_baseable`) ⟹ `B` baseable.

  ⟹ `all_baseable : ∀ B, Baseable B`, which `S1_92` feeds to
  `exponentials_of_all_baseable` to close `topos_has_exponentials`.  Axiom profile
  of the whole line: `Classical.choice` only — NO `SorryAx`.
-/

module

public import Freyd.S1_91
public import Freyd.S1_85

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section Baseable923

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
variable [∀ C : 𝒞, HasPowerObject C] [HasEqualizers 𝒞]

/-! ## Power-object correspondence as a bijection (genuine, power-object-only)

  For any `Z, C`, the universality of `∈_C` (`HasPowerObject.is_universal`) makes
  `powerClassify : BinRel 𝒞 Z C → (Z ⟶ [C])` and `f ↦ relPullback f ∈_C` mutually
  inverse up to `RelHom`.  These lemmas are exactly what `(D2)` needs, proved here
  with NO dependence on `exp`/`Topos`. -/

/-- `powerClassify` classifies `R` up to relation iso.  Stated directly from the
    universality field `classify_exists`, with NO `[Topos 𝒞]` hypothesis (unlike the
    S1_91 uses of this same fact, which sit under a file-wide `[Topos 𝒞]`), so it
    depends only on power objects. -/
public theorem powerClassify_pullback_iso {C Z : 𝒞} (R : BinRel 𝒞 Z C) :
    RelHom R (relPullback (powerClassify R) HasPowerObject.mem) ∧
    RelHom (relPullback (powerClassify R) HasPowerObject.mem) R :=
  (HasPowerObject.is_universal.classify_exists Z R).choose_spec

/-- **Maps into `[C]` are determined by their relation**: if `f g : Z ⟶ [C]` pull
    `∈_C` back to iso relations, they are equal. -/
theorem powerObj_hom_ext {C Z : 𝒞} (f g : Z ⟶ HasPowerObject.powerObj (C := C))
    (h : RelHom (relPullback f HasPowerObject.mem) (relPullback g HasPowerObject.mem) ∧
         RelHom (relPullback g HasPowerObject.mem) (relPullback f HasPowerObject.mem)) :
    f = g :=
  HasPowerObject.is_universal.classify_unique Z (relPullback f HasPowerObject.mem) f g
    ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
     ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩
    ⟨h.1, h.2⟩

/-! ## Relation reindexing `BinRel(A×X, B) ≅ BinRel(X, A×B)` (curry on relations)

  The exponential `B^A` from a power object rests on the "uncurry" bijection on
  RELATIONS: a relation `R ⊆ (A×X) × B` (= a possibly-partial multivalued map
  `A×X ⇀ B`) is the same data as a relation `R̂ ⊆ X × (A×B)` (the A-index folded
  into the target).  This is a pure product-rearrangement of the jointly-monic
  span and is `RelHom`-iso, axiom-clean.  It is the load-bearing isomorphism that
  feeds the power object `[A×B]`: `Hom(X,[A×B]) ≅ BinRel(X,A×B) ≅ BinRel(A×X,B)`. -/

/-- Fold the `A`-index of a relation `R ⊆ (A×X) × B` into its target:
    `R̂ ⊆ X × (A×B)`, with `colA := R.colA ≫ snd : src → X` and
    `colB := ⟨R.colA ≫ fst, R.colB⟩ : src → A×B`. -/
@[expose] public def relUncurry {A X B : 𝒞} (R : BinRel 𝒞 (prod A X) B) : BinRel 𝒞 X (prod A B) where
  src  := R.src
  colA := R.colA ≫ snd
  colB := pair (R.colA ≫ fst) R.colB
  isMonicPair := by
    intro W f g hX hAB
    -- agreement on X (hX) and on A×B (hAB) ⟹ agreement on the original (A×X, B) legs.
    apply R.isMonicPair f g
    · -- f ≫ R.colA = g ≫ R.colA : agree after fst (from hAB) and after snd (from hX).
      apply fst_snd_jointly_monic (f ≫ R.colA) (g ≫ R.colA)
      · have := congrArg (· ≫ fst) hAB
        simpa only [Cat.assoc, fst_pair] using this
      · rw [Cat.assoc, Cat.assoc]; exact hX
    · -- f ≫ R.colB = g ≫ R.colB : agree after snd of the A×B leg.
      have := congrArg (· ≫ snd) hAB
      simpa only [Cat.assoc, snd_pair] using this

/-- Inverse: unfold a relation `S ⊆ X × (A×B)` to `Š ⊆ (A×X) × B`, with
    `colA := ⟨S.colB ≫ fst, S.colA⟩ : src → A×X` and `colB := S.colB ≫ snd`. -/
@[expose] public def relCurry {A X B : 𝒞} (S : BinRel 𝒞 X (prod A B)) : BinRel 𝒞 (prod A X) B where
  src  := S.src
  colA := pair (S.colB ≫ fst) S.colA
  colB := S.colB ≫ snd
  isMonicPair := by
    intro W f g hAX hB
    apply S.isMonicPair f g
    · -- f ≫ S.colA = g ≫ S.colA : the X-coordinate of the A×X leg (snd).
      have := congrArg (· ≫ snd) hAX
      simpa only [Cat.assoc, snd_pair] using this
    · -- f ≫ S.colB = g ≫ S.colB : agree after fst (from hAX) and snd (from hB).
      apply fst_snd_jointly_monic (f ≫ S.colB) (g ≫ S.colB)
      · have := congrArg (· ≫ fst) hAX
        simpa only [Cat.assoc, fst_pair] using this
      · rw [Cat.assoc, Cat.assoc]; exact hB

/-- `relCurry` and `relUncurry` are mutually inverse on the nose (same `src`,
    legs equal by product-eta).  Stated as the two round-trip equalities of the
    *spans* (`colA`,`colB`), which is what the `RelHom` bijection needs. -/
public theorem relCurry_uncurry {A X B : 𝒞} (R : BinRel 𝒞 (prod A X) B) :
    (relCurry (relUncurry R)).colA = R.colA ∧ (relCurry (relUncurry R)).colB = R.colB := by
  refine ⟨?_, ?_⟩
  · show pair ((pair (R.colA ≫ fst) R.colB) ≫ fst) (R.colA ≫ snd) = R.colA
    rw [fst_pair]; exact (pair_uniq _ _ R.colA rfl rfl).symm
  · show (pair (R.colA ≫ fst) R.colB) ≫ snd = R.colB
    rw [snd_pair]

public theorem relUncurry_curry {A X B : 𝒞} (S : BinRel 𝒞 X (prod A B)) :
    (relUncurry (relCurry S)).colA = S.colA ∧ (relUncurry (relCurry S)).colB = S.colB := by
  refine ⟨?_, ?_⟩
  · show (pair (S.colB ≫ fst) S.colA) ≫ snd = S.colA
    rw [snd_pair]
  · show pair ((pair (S.colB ≫ fst) S.colA) ≫ fst) (S.colB ≫ snd) = S.colB
    rw [fst_pair]; exact (pair_uniq _ _ S.colB rfl rfl).symm

/-! ## Local `RelHom` plumbing (clean under bare power-object hypotheses)

  The S1_91 lemmas `relHom_trans`/`relHom_pullback`/`powerClassify_natural` live
  AFTER a file-level `variable [Topos 𝒞]`, so they silently require a full topos;
  under our bare `[∀ C, HasPowerObject C]` they are not applicable.  We re-bank the
  three we need here (the proofs use only products/pullbacks, no classifier). -/

/-- Transitivity of `RelHom` (local, classifier-free). -/
public theorem relHom_trans923 {A C : 𝒞} {R S T : BinRel 𝒞 A C}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨h, hA, hB⟩ := h₁; obtain ⟨k, kA, kB⟩ := h₂
  exact ⟨h ≫ k, by rw [Cat.assoc, kA, hA], by rw [Cat.assoc, kB, hB]⟩

/-- `RelHom` is preserved by pulling back along a fixed `g` (local copy). -/
public theorem relHom_pullback923 {A C X : 𝒞} (g : X ⟶ A) {R S : BinRel 𝒞 A C}
    (h : RelHom R S) : RelHom (relPullback g R) (relPullback g S) := by
  obtain ⟨w, hwA, hwB⟩ := h
  let P  := HasPullbacks.has g R.colA
  let P' := HasPullbacks.has g S.colA
  have hsq : P.cone.π₁ ≫ g = (P.cone.π₂ ≫ w) ≫ S.colA :=
    calc P.cone.π₁ ≫ g = P.cone.π₂ ≫ R.colA := P.cone.w
      _ = P.cone.π₂ ≫ (w ≫ S.colA) := congrArg (P.cone.π₂ ≫ ·) hwA.symm
      _ = (P.cone.π₂ ≫ w) ≫ S.colA := (Cat.assoc P.cone.π₂ w S.colA).symm
  let c : Cone g S.colA := ⟨P.cone.pt, P.cone.π₁, P.cone.π₂ ≫ w, hsq⟩
  refine ⟨P'.lift c, P'.lift_fst c, ?_⟩
  show P'.lift c ≫ (P'.cone.π₂ ≫ S.colB) = P.cone.π₂ ≫ R.colB
  calc P'.lift c ≫ (P'.cone.π₂ ≫ S.colB)
      = (P'.lift c ≫ P'.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
    _ = (P.cone.π₂ ≫ w) ≫ S.colB := congrArg (· ≫ S.colB) (P'.lift_snd c)
    _ = P.cone.π₂ ≫ (w ≫ S.colB) := Cat.assoc _ _ _
    _ = P.cone.π₂ ≫ R.colB := congrArg (P.cone.π₂ ≫ ·) hwB

/-- **Naturality of `Λ`** (local, classifier-free): `Λ(relPullback g R) = g ≫ Λ(R)`. -/
public theorem powerClassify_natural923 {C A X : 𝒞} (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    powerClassify (relPullback g R) = g ≫ powerClassify R := by
  have hR := powerClassify_pullback_iso R
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (powerClassify R) HasPowerObject.mem
  have hf : RelHom (relPullback g R)
              (relPullback (g ≫ powerClassify R) HasPowerObject.mem) ∧
            RelHom (relPullback (g ≫ powerClassify R) HasPowerObject.mem)
              (relPullback g R) :=
    ⟨relHom_trans923 (relHom_pullback923 g hR.1) hc1,
     relHom_trans923 hc2 (relHom_pullback923 g hR.2)⟩
  exact HasPowerObject.is_universal.classify_unique X (relPullback g R) _ _
    (powerClassify_pullback_iso (relPullback g R)) hf

/-! ## Step A — image-free "functional-total relation is a graph"

  A relation `R ⊆ Y × B` whose left leg `R.colA : R.src → Y` is BOTH monic and a
  cover is (single-valued + total =) a MAP, hence the graph of a unique morphism
  `m := R.colA⁻¹ ≫ R.colB`.  This is `tabulated_left_iso_eq_graph` (S1_56:647),
  but reproved INLINE here so as to avoid that lemma's enclosing `[HasImages 𝒞]`
  section.  No images are used: just `monic_cover_iso` (S1_51:70) to split the leg
  and product/graph rewrites. -/

/-- **Step A**: a functional-total relation `R` (left leg monic + cover) is the
    graph of a unique morphism `m : Y ⟶ B`, with mutual `RelHom`s `R ↔ graph m`. -/
public theorem functional_total_relation_is_graph {Y B : 𝒞} (R : BinRel 𝒞 Y B)
    (hmono : Monic R.colA) (hcover : Cover R.colA) :
    ∃ m : Y ⟶ B, (RelHom R (graph m) ∧ RelHom (graph m) R) ∧
      ∀ m' : Y ⟶ B, (RelHom R (graph m') ∧ RelHom (graph m') R) → m' = m := by
  -- The left leg is iso since it is a monic cover.
  obtain ⟨ainv, ha_ainv, hainv_a⟩ := monic_cover_iso R.colA hcover hmono
  refine ⟨ainv ≫ R.colB, ⟨?_, ?_⟩, ?_⟩
  · -- RelHom R (graph (ainv ≫ R.colB)): witness R.colA.
    refine ⟨R.colA, ?_, ?_⟩
    · dsimp [graph]; rw [Cat.comp_id]
    · dsimp [graph]
      calc R.colA ≫ (ainv ≫ R.colB) = (R.colA ≫ ainv) ≫ R.colB := (Cat.assoc _ _ _).symm
        _ = Cat.id _ ≫ R.colB := by rw [ha_ainv]
        _ = R.colB := Cat.id_comp _
  · -- RelHom (graph (ainv ≫ R.colB)) R: witness ainv.
    refine ⟨ainv, ?_, ?_⟩
    · dsimp [graph]; rw [hainv_a]
    · rfl
  · -- Uniqueness: any m' with RelHom (graph m') R gives a section of R.colA = ainv.
    rintro m' ⟨_, ⟨w, hwA, hwB⟩⟩
    -- hwA : w ≫ R.colA = (graph m').colA = id Y ; hwB : w ≫ R.colB = m'
    dsimp [graph] at hwA hwB
    -- w is a section of R.colA, which is iso, so w = ainv.
    have hw_eq : w = ainv := by
      calc w = w ≫ Cat.id _ := (Cat.comp_id _).symm
        _ = w ≫ (R.colA ≫ ainv) := by rw [ha_ainv]
        _ = (w ≫ R.colA) ≫ ainv := (Cat.assoc _ _ _).symm
        _ = Cat.id _ ≫ ainv := by rw [hwA]
        _ = ainv := Cat.id_comp _
    rw [← hwB, hw_eq]

/-! ## Step B — the singleton map `{·} : B ↣ [B]` (classifier-free)

  `singletonMap923 B := Λ(graph (id B)) : B ⟶ [B]` names the diagonal relation
  `Δ_B = graph(id B) ⊆ B × B`.  Built purely from power objects (no classifier,
  no `exp`/`curry`), it is the power-object analogue of `singletonMapCat`
  (S1_92), and is MONIC: precomposing it with `h, k : X ⟶ B` names the graphs of
  `h, k` (via `powerClassify_natural` + `relPullback h (graph id) ≅ graph h`), so
  equal names force `h = k`. -/

/-- The singleton (description) map `{·} : B ⟶ [B]`, naming the diagonal. -/
@[expose] public noncomputable def singletonMap923 (B : 𝒞) : B ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (graph (Cat.id B))

/-- Pulling the diagonal `graph (id B)` back along `h : X ⟶ B` gives `graph h`
    (up to relation iso, both directions).  The pullback of `Δ_B` along `h` is
    `{(x) | (h x, x)} = graph h`; concretely the pullback span has a section. -/
public theorem relPullback_graph_id {X B : 𝒞} (h : X ⟶ B) :
    RelHom (graph h) (relPullback h (graph (Cat.id B))) ∧
    RelHom (relPullback h (graph (Cat.id B))) (graph h) := by
  -- graph h : src=X, colA=id X, colB=h.  relPullback h (graph id): pullback of
  -- (h : X→B) and (graph id).colA = id B; its apex ≅ X with π₁ a section.
  have hsq : (Cat.id X) ≫ h = h ≫ (graph (Cat.id B)).colA := by
    dsimp [graph]; rw [Cat.id_comp, Cat.comp_id]
  constructor
  · -- graph h ⊂ relPullback: witness `s := lift ⟨X, id X, h, hsq⟩ : X → pb.pt`.
    refine ⟨(HasPullbacks.has h (graph (Cat.id B)).colA).lift ⟨X, Cat.id X, h, hsq⟩, ?_, ?_⟩
    · -- s ≫ colA = s ≫ π₁ = id X = (graph h).colA
      dsimp [relPullback, graph]
      exact (HasPullbacks.has h (Cat.id B)).lift_fst _
    · -- s ≫ colB = s ≫ (π₂ ≫ id) = (s ≫ π₂) = h = (graph h).colB
      dsimp [relPullback, graph]
      rw [Cat.comp_id]
      exact (HasPullbacks.has h (Cat.id B)).lift_snd ⟨X, Cat.id X, h, hsq⟩
  · -- relPullback ⊂ graph h: witness π₁ : pb.pt → X.
    refine ⟨(HasPullbacks.has h (graph (Cat.id B)).colA).cone.π₁, ?_, ?_⟩
    · -- π₁ ≫ (graph h).colA = π₁ ≫ id X = π₁ = colA
      dsimp [relPullback, graph]; rw [Cat.comp_id]
    · -- π₁ ≫ (graph h).colB = π₁ ≫ h = π₂ ≫ id = colB
      have hw := (HasPullbacks.has h (graph (Cat.id B)).colA).cone.w
      dsimp [relPullback, graph] at hw ⊢
      rw [Cat.comp_id, hw, Cat.comp_id]

/-- Naming a graph: `h ≫ singletonMap923 B = Λ(graph h)`. -/
public theorem singletonMapNaming923 {X B : 𝒞} (h : X ⟶ B) :
    h ≫ singletonMap923 B = powerClassify (graph h) := by
  rw [singletonMap923, ← powerClassify_natural923 (graph (Cat.id B)) h]
  -- Goal: Λ(relPullback h (graph id)) = Λ(graph h).  Both classify the relation
  -- `relPullback h (graph id)` (the RHS via the iso to `graph h`); classify_unique.
  obtain ⟨hf, hg⟩ := relPullback_graph_id h  -- graph h ↔ relPullback h (graph id)
  apply HasPowerObject.is_universal.classify_unique X (relPullback h (graph (Cat.id B)))
  · exact powerClassify_pullback_iso _
  · -- relPullback h (graph id) ↔ relPullback (Λ(graph h)) ∈, via graph h.
    exact ⟨relHom_trans923 hg (powerClassify_pullback_iso (graph h)).1,
           relHom_trans923 (powerClassify_pullback_iso (graph h)).2 hf⟩

/-- **Step B**: the singleton map `{·} : B ↣ [B]` is MONIC.  If `h, k : X ⟶ B`
    have `h ≫ {·} = k ≫ {·}`, both name `graph h` resp. `graph k`; the names being
    equal makes `graph h ≅ graph k`, whose right legs are `h, k`, forcing `h = k`. -/
public theorem singletonMapMonic923 (B : 𝒞) : Monic (singletonMap923 (𝒞 := 𝒞) B) := by
  intro X h k hΔ
  -- Λ(graph h) = Λ(graph k).
  have hΛ : powerClassify (graph h) = powerClassify (graph k) := by
    rw [← singletonMapNaming923, ← singletonMapNaming923]; exact hΔ
  -- Hence graph h ≅ graph k (both classify the same name).
  have hiso : RelHom (graph h) (graph k) := by
    have h1 := (powerClassify_pullback_iso (graph h)).1   -- graph h ⊂ relPullback Λ(graph h) mem
    have h2 := (powerClassify_pullback_iso (graph k)).2   -- relPullback Λ(graph k) mem ⊂ graph k
    rw [hΛ] at h1
    exact relHom_trans923 h1 h2
  -- A RelHom graph h → graph k gives a witness w with w ≫ id = id (so w = id) and w ≫ k = h.
  obtain ⟨w, hwA, hwB⟩ := hiso
  dsimp [graph] at hwA hwB
  -- hwA : w ≫ id X = id X  ⟹ w = id X ; hwB : w ≫ k = h.
  have hw : w = Cat.id X := by rw [← Cat.comp_id w]; exact hwA
  rw [← hwB, hw, Cat.id_comp]

/-! ## Keystone route (Freyd §1.923, Kock's simplification)

  Freyd's ACTUAL argument that a topos is exponential (book p.9343-9359): every
  POWER OBJECT `[C]` is directly baseable via the representability iso
  `[C]^A ≅ [A×C]`, hence `Ω = [1]` is baseable, and every object `B` is the
  equalizer of `χ_{·} , ⊤∘! : [B] ⇉ Ω` (the classifying square of the singleton
  mono `{·}:B↣[B]`).  Baseability is closed under equalizers (§1.859), so every
  `B` is baseable.  No functional/total relations needed. -/

/-- **Baseable transports across isomorphism.**  If `B ≅ B'` and `B'` is baseable,
    so is `B`: the representing object/eval for `B` at `A` are those of `B'`, with
    `ev` post-composed by the iso `B' → B`. -/
public theorem baseable_of_iso {B B' : 𝒞} (e : B ⟶ B') (e' : B' ⟶ B)
    (he : e ≫ e' = Cat.id B) (he' : e' ≫ e = Cat.id B') (hB' : Baseable B') :
    Baseable B := by
  intro A
  obtain ⟨E, ev, hu⟩ := hB' A
  refine ⟨E, ev ≫ e', ?_⟩
  intro X φ
  obtain ⟨g, hg, hg_uniq⟩ := hu X (φ ≫ e)
  refine ⟨g, ?_, ?_⟩
  · -- prodMap g ≫ (ev ≫ e') = (prodMap g ≫ ev) ≫ e' = (φ ≫ e) ≫ e' = φ.
    rw [← Cat.assoc, hg, Cat.assoc, he, Cat.comp_id]
  · intro g' hg'
    apply hg_uniq
    -- prodMap g' ≫ ev = φ ≫ e, from prodMap g' ≫ (ev ≫ e') = φ.
    have : (prodMap A X E g' ≫ ev) ≫ e' = φ := by rw [Cat.assoc]; exact hg'
    calc prodMap A X E g' ≫ ev
        = (prodMap A X E g' ≫ ev) ≫ Cat.id B' := (Cat.comp_id _).symm
      _ = (prodMap A X E g' ≫ ev) ≫ (e' ≫ e) := by rw [he']
      _ = ((prodMap A X E g' ≫ ev) ≫ e') ≫ e := (Cat.assoc _ _ _).symm
      _ = φ ≫ e := by rw [this]

/-! ### Naturality of `relCurry` against the `prodMap`-pullback (load-bearing)

  For `g : X ⟶ P` and `S : BinRel 𝒞 P (A×C)`, the two `BinRel 𝒞 (A×X) C`
  *  `relPullback (prodMap A X P g) (relCurry S)`  and
  *  `relCurry (relPullback g S)`
  are isomorphic as relations.  This is the §1.923 representability iso made
  concrete: it says transposing-then-reindexing equals reindexing-then-transposing.
  Both sides have the SAME `src` up to a canonical iso of pullback apices; we build
  the two `RelHom`s by hand from the pullback universal properties. -/
public theorem relCurry_natural {A X P C : 𝒞} (g : X ⟶ P) (S : BinRel 𝒞 P (prod A C)) :
    RelHom (relPullback (prodMap A X P g) (relCurry S)) (relCurry (relPullback g S)) ∧
    RelHom (relCurry (relPullback g S)) (relPullback (prodMap A X P g) (relCurry S)) := by
  -- LHS apex: PL := pullback of (prodMap A X P g) and (relCurry S).colA = pair (S.colB≫fst) S.colA.
  -- RHS inner apex: PR := pullback of (g) and S.colA.  relCurry (relPullback g S) has src = PR.pt.
  let cS  := relCurry S
  let PL  := HasPullbacks.has (prodMap A X P g) cS.colA
  let PR  := HasPullbacks.has g S.colA
  -- Abbreviations for the four legs.
  -- cS.colA = pair (S.colB ≫ fst) S.colA : S.src → prod A P
  -- relPullback g S : src=PR.pt, colA = PR.π₁ (→X), colB = PR.π₂ ≫ S.colB (→ prod A C).
  -- relCurry (relPullback g S) : colA = pair ((PR.π₂≫S.colB)≫fst) PR.π₁, colB = (PR.π₂≫S.colB)≫snd.
  have hcSA : cS.colA = pair (S.colB ≫ fst) S.colA := rfl
  -- ===== forward: PL.pt → PR.pt =====
  -- From PL: PL.π₁ : PL.pt → prod A X,  PL.π₂ : PL.pt → S.src,
  -- square wPL : PL.π₁ ≫ prodMap g = PL.π₂ ≫ cS.colA.
  have wPL : PL.cone.π₁ ≫ (prodMap A X P g) = PL.cone.π₂ ≫ cS.colA := PL.cone.w
  -- The X-coordinate of PL.π₁ : (PL.π₁ ≫ snd) : PL.pt → X.  Its image under g equals PL.π₂≫S.colA.
  -- Indeed (PL.π₁≫snd)≫g = PL.π₁≫(prodMap g ≫ snd) = PL.π₁≫(snd≫g)... use prodMap_snd.
  have fwd_sq : (PL.cone.π₁ ≫ snd) ≫ g = PL.cone.π₂ ≫ S.colA := by
    calc (PL.cone.π₁ ≫ snd) ≫ g
        = PL.cone.π₁ ≫ (snd ≫ g) := Cat.assoc _ _ _
      _ = PL.cone.π₁ ≫ (prodMap A X P g ≫ snd) := by rw [prodMap_snd]
      _ = (PL.cone.π₁ ≫ prodMap A X P g) ≫ snd := (Cat.assoc _ _ _).symm
      _ = (PL.cone.π₂ ≫ cS.colA) ≫ snd := by rw [wPL]
      _ = PL.cone.π₂ ≫ (pair (S.colB ≫ fst) S.colA ≫ snd) := Cat.assoc _ _ _
      _ = PL.cone.π₂ ≫ S.colA := by rw [snd_pair]
  let fwdCone : Cone g S.colA := ⟨PL.cone.pt, PL.cone.π₁ ≫ snd, PL.cone.π₂, fwd_sq⟩
  refine ⟨⟨PR.lift fwdCone, ?_, ?_⟩, ?_⟩
  · -- colA: (lift) ≫ (relCurry (relPullback g S)).colA = (relPullback (prodMap g) cS).colA = PL.π₁.
    -- (relCurry (relPullback g S)).colA = pair ((PR.π₂≫S.colB)≫fst) PR.π₁.
    -- We must show: lift ≫ pair ((PR.π₂≫S.colB)≫fst) PR.π₁ = PL.π₁.
    -- Check via fst, snd jointly monic.
    apply fst_snd_jointly_monic
    · -- ≫ fst.  LHS ≫ fst = lift ≫ ((PR.π₂≫S.colB)≫fst);  PL.π₁ ≫ fst.
      show (PR.lift fwdCone ≫ (relCurry (relPullback g S)).colA) ≫ fst = PL.cone.π₁ ≫ fst
      show (PR.lift fwdCone ≫ pair ((PR.cone.π₂ ≫ S.colB) ≫ fst) PR.cone.π₁) ≫ fst = PL.cone.π₁ ≫ fst
      rw [Cat.assoc, fst_pair, ← Cat.assoc, ← Cat.assoc, PR.lift_snd]
      -- now: (PL.π₂ ≫ S.colB) ≫ fst = PL.π₁ ≫ fst.  From wPL ≫ fst.
      have hfp : cS.colA ≫ fst = S.colB ≫ fst := by rw [hcSA, fst_pair]
      calc (PL.cone.π₂ ≫ S.colB) ≫ fst
          = PL.cone.π₂ ≫ (S.colB ≫ fst) := Cat.assoc _ _ _
        _ = PL.cone.π₂ ≫ (cS.colA ≫ fst) := by rw [hfp]
        _ = (PL.cone.π₂ ≫ cS.colA) ≫ fst := (Cat.assoc _ _ _).symm
        _ = (PL.cone.π₁ ≫ prodMap A X P g) ≫ fst := by rw [wPL]
        _ = PL.cone.π₁ ≫ (prodMap A X P g ≫ fst) := Cat.assoc _ _ _
        _ = PL.cone.π₁ ≫ fst := by rw [prodMap_fst]
    · -- ≫ snd.  LHS ≫ snd = lift ≫ PR.π₁ = PL.π₁ ≫ snd.
      show (PR.lift fwdCone ≫ pair ((PR.cone.π₂ ≫ S.colB) ≫ fst) PR.cone.π₁) ≫ snd = PL.cone.π₁ ≫ snd
      rw [Cat.assoc, snd_pair, PR.lift_fst]
  · -- colB: lift ≫ (relCurry (relPullback g S)).colB = (relPullback (prodMap g) cS).colB.
    -- (relCurry (relPullback g S)).colB = (PR.π₂ ≫ S.colB) ≫ snd.
    -- (relPullback (prodMap g) cS).colB = PL.π₂ ≫ cS.colB = PL.π₂ ≫ (S.colB ≫ snd).
    show PR.lift fwdCone ≫ ((PR.cone.π₂ ≫ S.colB) ≫ snd) = PL.cone.π₂ ≫ cS.colB
    show PR.lift fwdCone ≫ ((PR.cone.π₂ ≫ S.colB) ≫ snd) = PL.cone.π₂ ≫ (S.colB ≫ snd)
    rw [← Cat.assoc, ← Cat.assoc, PR.lift_snd, Cat.assoc]
  · -- ===== backward: PR.pt → PL.pt =====
    -- Build a PL-cone over (prodMap g, cS.colA) with apex PR.pt:
    --   π₁ := pair (PR.π₂ ≫ S.colB ≫ fst) PR.π₁ : PR.pt → prod A X
    --   π₂ := PR.π₂ : PR.pt → S.src
    -- square: π₁ ≫ prodMap g = π₂ ≫ cS.colA.
    have wPR : PR.cone.π₁ ≫ g = PR.cone.π₂ ≫ S.colA := PR.cone.w
    have bwd_sq : pair (PR.cone.π₂ ≫ (S.colB ≫ fst)) PR.cone.π₁ ≫ (prodMap A X P g)
                = PR.cone.π₂ ≫ cS.colA := by
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, prodMap_fst, fst_pair, hcSA, Cat.assoc, fst_pair]
      · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair, wPR,
            hcSA, Cat.assoc, snd_pair]
    let bwdCone : Cone (prodMap A X P g) cS.colA :=
      ⟨PR.cone.pt, pair (PR.cone.π₂ ≫ (S.colB ≫ fst)) PR.cone.π₁, PR.cone.π₂, bwd_sq⟩
    refine ⟨PL.lift bwdCone, ?_, ?_⟩
    · -- colA: lift ≫ (relPullback (prodMap g) cS).colA = lift ≫ PL.π₁ = bwdCone.π₁.
      show PL.lift bwdCone ≫ PL.cone.π₁ = pair ((PR.cone.π₂ ≫ S.colB) ≫ fst) PR.cone.π₁
      rw [PL.lift_fst]; show pair (PR.cone.π₂ ≫ (S.colB ≫ fst)) PR.cone.π₁ = _; rw [Cat.assoc]
    · -- colB: lift ≫ (relPullback (prodMap g) cS).colB = (lift ≫ PL.π₂) ≫ cS.colB.
      show PL.lift bwdCone ≫ (PL.cone.π₂ ≫ cS.colB) = (PR.cone.π₂ ≫ S.colB) ≫ snd
      rw [← Cat.assoc, PL.lift_snd]
      show PR.cone.π₂ ≫ (S.colB ≫ snd) = (PR.cone.π₂ ≫ S.colB) ≫ snd
      rw [Cat.assoc]

/-- The `relCurry∘relUncurry` round trip is the identity relation, both ways.
    (`relCurry (relUncurry R)` shares `src` with `R` on the nose; legs equal by
    `relCurry_uncurry`.) -/
public theorem relCurry_uncurry_iso {A X B : 𝒞} (R : BinRel 𝒞 (prod A X) B) :
    RelHom R (relCurry (relUncurry R)) ∧ RelHom (relCurry (relUncurry R)) R := by
  obtain ⟨hA, hB⟩ := relCurry_uncurry R
  refine ⟨⟨Cat.id R.src, ?_, ?_⟩, ⟨Cat.id R.src, ?_, ?_⟩⟩
  · show Cat.id R.src ≫ (relCurry (relUncurry R)).colA = R.colA; rw [Cat.id_comp, hA]
  · show Cat.id R.src ≫ (relCurry (relUncurry R)).colB = R.colB; rw [Cat.id_comp, hB]
  · show Cat.id R.src ≫ R.colA = (relCurry (relUncurry R)).colA; rw [Cat.id_comp, hA]
  · show Cat.id R.src ≫ R.colB = (relCurry (relUncurry R)).colB; rw [Cat.id_comp, hB]

/-- The `relUncurry∘relCurry` round trip is the identity relation, both ways. -/
public theorem relUncurry_curry_iso {A X B : 𝒞} (S : BinRel 𝒞 X (prod A B)) :
    RelHom S (relUncurry (relCurry S)) ∧ RelHom (relUncurry (relCurry S)) S := by
  obtain ⟨hA, hB⟩ := relUncurry_curry S
  refine ⟨⟨Cat.id S.src, ?_, ?_⟩, ⟨Cat.id S.src, ?_, ?_⟩⟩
  · show Cat.id S.src ≫ (relUncurry (relCurry S)).colA = S.colA; rw [Cat.id_comp, hA]
  · show Cat.id S.src ≫ (relUncurry (relCurry S)).colB = S.colB; rw [Cat.id_comp, hB]
  · show Cat.id S.src ≫ S.colA = (relUncurry (relCurry S)).colA; rw [Cat.id_comp, hA]
  · show Cat.id S.src ≫ S.colB = (relUncurry (relCurry S)).colB; rw [Cat.id_comp, hB]

/-- `relCurry` is functorial on `RelHom`: a witness `R ⊂ S` of relations to `A×C`
    transports to `relCurry R ⊂ relCurry S` (same witness, repackaged legs). -/
public theorem relCurry_relHom {A X C : 𝒞} {R S : BinRel 𝒞 X (prod A C)} (h : RelHom R S) :
    RelHom (relCurry R) (relCurry S) := by
  obtain ⟨w, hA, hB⟩ := h
  -- relCurry R: src=R.src, colA = pair (R.colB≫fst) R.colA, colB = R.colB≫snd.
  refine ⟨w, ?_, ?_⟩
  · -- w ≫ (relCurry S).colA = (relCurry R).colA.
    show w ≫ pair (S.colB ≫ fst) S.colA = pair (R.colB ≫ fst) R.colA
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair, ← Cat.assoc, hB]
    · rw [Cat.assoc, snd_pair, snd_pair, hA]
  · -- w ≫ (relCurry S).colB = (relCurry R).colB.
    show w ≫ (S.colB ≫ snd) = R.colB ≫ snd
    rw [← Cat.assoc, hB]

/-- `relUncurry` is functorial on `RelHom`. -/
public theorem relUncurry_relHom {A X C : 𝒞} {R S : BinRel 𝒞 (prod A X) C} (h : RelHom R S) :
    RelHom (relUncurry R) (relUncurry S) := by
  obtain ⟨w, hA, hB⟩ := h
  -- relUncurry R: src=R.src, colA = R.colA≫snd, colB = pair (R.colA≫fst) R.colB.
  refine ⟨w, ?_, ?_⟩
  · show w ≫ (S.colA ≫ snd) = R.colA ≫ snd
    rw [← Cat.assoc, hA]
  · show w ≫ pair (S.colA ≫ fst) S.colB = pair (R.colA ≫ fst) R.colB
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair, ← Cat.assoc, hA]
    · rw [Cat.assoc, snd_pair, snd_pair, hB]

/-! ### Generic universal-relation classifier (for `Ω` as well as `[C]`)

  `Ω` (the subobject classifier) and `[C]` are BOTH baseable for the SAME reason:
  each carries a UNIVERSAL relation targeted at some `C` (`∈_C` for `[C]`;
  `⟨1, true, !⟩` targeted at `1` for `Ω`).  We package the §1.923 argument over an
  arbitrary `IsUniversalRel U` and instantiate it twice. -/

/-- Classifying map of `R` by a universal relation `U : BinRel P C`. -/
@[expose] public noncomputable def univClassify923 {P C : 𝒞} {U : BinRel 𝒞 P C} (hU : IsUniversalRel U)
    {Z : 𝒞} (R : BinRel 𝒞 Z C) : Z ⟶ P :=
  (hU.classify_exists Z R).choose

public theorem univClassifyIso923 {P C : 𝒞} {U : BinRel 𝒞 P C} (hU : IsUniversalRel U)
    {Z : 𝒞} (R : BinRel 𝒞 Z C) :
    RelHom R (relPullback (univClassify923 hU R) U) ∧
    RelHom (relPullback (univClassify923 hU R) U) R :=
  (hU.classify_exists Z R).choose_spec

/-- Naturality of `univClassify923`: `Λ(relPullback g R) = g ≫ Λ(R)`. -/
theorem univClassifyNatural923 {P C A X : 𝒞} {U : BinRel 𝒞 P C} (hU : IsUniversalRel U)
    (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    univClassify923 hU (relPullback g R) = g ≫ univClassify923 hU R := by
  have hR := univClassifyIso923 hU R
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (univClassify923 hU R) U
  exact hU.classify_unique X (relPullback g R) _ _
    (univClassifyIso923 hU (relPullback g R))
    ⟨relHom_trans923 (relHom_pullback923 g hR.1) hc1,
     relHom_trans923 hc2 (relHom_pullback923 g hR.2)⟩

/-- Extensionality: maps into `P` are determined by the `U`-relation they pull back. -/
public theorem univHomExt923 {P C Z : 𝒞} {U : BinRel 𝒞 P C} (hU : IsUniversalRel U)
    (f g : Z ⟶ P)
    (h : RelHom (relPullback f U) (relPullback g U) ∧ RelHom (relPullback g U) (relPullback f U)) :
    f = g :=
  hU.classify_unique Z (relPullback f U) f g
    ⟨⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩,
     ⟨Cat.id _, by rw [Cat.id_comp], by rw [Cat.id_comp]⟩⟩
    ⟨h.1, h.2⟩

/-- **β-relation lemma** for a universal `U : BinRel P C`.  For `h : X ⟶ [A×C]` and
    `ev := Λ_U(relCurry ∈_{A×C})`, the relation classified by `prodMap h ≫ ev` is
    `relCurry (relPullback h ∈_{A×C})`. -/
public theorem betaRelU {A X C P : 𝒞} {U : BinRel 𝒞 P C} (hU : IsUniversalRel U)
    (h : X ⟶ HasPowerObject.powerObj (C := prod A C)) :
    RelHom (relPullback (prodMap A X _ h ≫ univClassify923 hU (relCurry (HasPowerObject.mem (C := prod A C)))) U)
           (relCurry (relPullback h (HasPowerObject.mem (C := prod A C)))) ∧
    RelHom (relCurry (relPullback h (HasPowerObject.mem (C := prod A C))))
           (relPullback (prodMap A X _ h ≫ univClassify923 hU (relCurry (HasPowerObject.mem (C := prod A C)))) U) := by
  have hev_iso := univClassifyIso923 hU (relCurry (HasPowerObject.mem (C := prod A C)))
  obtain ⟨hpc1, hpc2⟩ := relPullback_comp (prodMap A X _ h)
    (univClassify923 hU (relCurry (HasPowerObject.mem (C := prod A C)))) U
  obtain ⟨hnat1, hnat2⟩ := relCurry_natural h (HasPowerObject.mem (C := prod A C))
  refine ⟨?_, ?_⟩
  · exact relHom_trans923 hpc2 (relHom_trans923 (relHom_pullback923 _ hev_iso.2) hnat1)
  · exact relHom_trans923 hnat2 (relHom_trans923 (relHom_pullback923 _ hev_iso.1) hpc1)

/-- **(1) An object carrying a universal relation targeted at `C` is baseable**
    (Freyd §1.923, Kock).  The representing object of `(A × −, P)` is `[A × C]`, and
    `ev := Λ_U(relCurry ∈_{A×C})`.  The β/η bijection is the representability iso
    `P^A ≅ [A×C]`, assembled from the relation transpose `relCurry`/`relUncurry`,
    its naturality `relCurry_natural`, and the universality of `U`. -/
public theorem baseable_of_universalRel {P C : 𝒞} (U : BinRel 𝒞 P C) (hU : IsUniversalRel U) :
    Baseable P := by
  intro A
  refine ⟨HasPowerObject.powerObj (C := prod A C),
          univClassify923 hU (relCurry (HasPowerObject.mem (C := prod A C))), ?_⟩
  intro X f
  -- g := Λ(relUncurry (relPullback f U)) : X → [A×C].
  refine ⟨powerClassify (relUncurry (relPullback f U)), ?_, ?_⟩
  · -- β: prodMap g ≫ ev = f.
    apply univHomExt923 hU
    let g := powerClassify (relUncurry (relPullback f U))
    have hg_iso  := powerClassify_pullback_iso (relUncurry (relPullback f U))
    obtain ⟨hcu1, hcu2⟩ := relCurry_uncurry_iso (relPullback f U)
    obtain ⟨hβ1, hβ2⟩ := betaRelU (A := A) (C := C) hU g
    refine ⟨?_, ?_⟩
    · exact relHom_trans923 hβ1 (relHom_trans923 (relCurry_relHom hg_iso.2) hcu2)
    · exact relHom_trans923 hcu1 (relHom_trans923 (relCurry_relHom hg_iso.1) hβ2)
  · -- η/uniqueness.
    intro g' hg'
    apply HasPowerObject.is_universal.classify_unique X
            (relUncurry (relPullback f U))
            g' (powerClassify (relUncurry (relPullback f U)))
    · obtain ⟨hβ1, hβ2⟩ := betaRelU (A := A) (C := C) hU g'
      rw [hg'] at hβ1 hβ2
      obtain ⟨huc1, huc2⟩ := relUncurry_curry_iso (relPullback g' (HasPowerObject.mem (C := prod A C)))
      refine ⟨?_, ?_⟩
      · exact relHom_trans923 (relUncurry_relHom hβ1) huc2
      · exact relHom_trans923 huc1 (relUncurry_relHom hβ2)
    · exact ⟨(powerClassify_pullback_iso _).1, (powerClassify_pullback_iso _).2⟩

/-- **(1′) Every power object `[C]` is baseable.** -/
public theorem baseable_powerObj (C : 𝒞) : Baseable (HasPowerObject.powerObj (C := C)) :=
  baseable_of_universalRel HasPowerObject.mem HasPowerObject.is_universal

/-! ### (2)+(3)+(4): `Ω` baseable, `B` as an equalizer, every object baseable

  Under a subobject classifier, `Ω` carries a universal relation targeted at `1`
  (the universal subobject `t : 1 ↣ Ω`), so `Ω` is baseable by (1).  Each object
  `B` is the equalizer of `χ_{·} , ⊤∘! : [B] ⇉ Ω` (the classifying square of the
  singleton mono `{·} : B ↣ [B]`); since `[B]` and `Ω` are baseable, so is `B`. -/

section WithClassifier
variable [Topos 𝒞]

/-- The terminal object as seen by the subobject classifier (the domain of `true`).
    Naming it explicitly sidesteps the `HasTerminal` diamond in `Topos`
    (`Topos.toHasTerminal` vs `…toHasSubobjectClassifier.toHasTerminal`). -/
@[expose] public abbrev oneΩ : 𝒞 := @one 𝒞 _ (HasSubobjectClassifier.toHasTerminal)

/-- The universal relation packaging the universal subobject `t : 1 ↣ Ω`. -/
@[expose] public def trueRel : BinRel 𝒞 HasSubobjectClassifier.omega oneΩ where
  src  := oneΩ
  colA := HasSubobjectClassifier.true
  colB := @term 𝒞 _ HasSubobjectClassifier.toHasTerminal oneΩ
  isMonicPair := by
    intro W u v hA _
    exact HasSubobjectClassifier.true_monic u v hA

/-- `term` into the classifier's terminal (avoids the `HasTerminal` diamond). -/
@[expose] public abbrev termΩ (X : 𝒞) : X ⟶ oneΩ := @term 𝒞 _ HasSubobjectClassifier.toHasTerminal X

public theorem termΩ_uniq {X : 𝒞} (f g : X ⟶ oneΩ) : f = g :=
  @term_uniq 𝒞 _ HasSubobjectClassifier.toHasTerminal X f g

/-- A relation targeted at `1` (the classifier's terminal) has a monic left leg. -/
public theorem relTo1_colA_mono {Z : 𝒞} (R : BinRel 𝒞 Z oneΩ) : Monic R.colA := by
  intro W u v huv
  exact R.isMonicPair u v huv (termΩ_uniq _ _)

/-- **(2-core) `Ω` carries a universal relation targeted at `1`.**  Classifying a
    relation `R : BinRel Z 1` is classifying its monic left leg via `χ`. -/
public theorem trueRel_universal : IsUniversalRel (trueRel (𝒞 := 𝒞)) := by
  constructor
  · -- classify_exists.
    intro Z R
    have hmono : Monic R.colA := relTo1_colA_mono R
    refine ⟨HasSubobjectClassifier.classify R.colA hmono, ?_⟩
    -- relPullback χ trueRel ≅ R.  Both directions from the classifying pullback.
    -- The classifying square: R.colA is the pullback of t along χ; trueRel.colA = t.
    have hpb := HasSubobjectClassifier.classify_pullback R.colA hmono
    -- relPullback χ trueRel : src = pullback of (χ, t), colA = π₁, colB = π₂ ≫ term 1.
    -- The classifying cone (R.src, R.colA, term R.src) IS a pullback of (χ, t).
    constructor
    · -- R ⊂ relPullback χ trueRel:  lift R into the chosen pullback.
      let P := HasPullbacks.has (HasSubobjectClassifier.classify R.colA hmono) trueRel.colA
      have hsq : R.colA ≫ HasSubobjectClassifier.classify R.colA hmono
               = termΩ R.src ≫ trueRel.colA := HasSubobjectClassifier.classify_sq R.colA hmono
      let Rcone : Cone (HasSubobjectClassifier.classify R.colA hmono) trueRel.colA :=
        ⟨R.src, R.colA, termΩ R.src, hsq⟩
      refine ⟨P.lift Rcone, ?_, ?_⟩
      · show P.lift Rcone ≫ P.cone.π₁ = R.colA; exact P.lift_fst Rcone
      · show P.lift Rcone ≫ (P.cone.π₂ ≫ trueRel.colB) = R.colB
        rw [← Cat.assoc, P.lift_snd]; exact termΩ_uniq _ _
    · -- relPullback χ trueRel ⊂ R: the pullback apex maps to R via hpb's universality.
      let P := HasPullbacks.has (HasSubobjectClassifier.classify R.colA hmono) trueRel.colA
      have hPsq : P.cone.π₁ ≫ HasSubobjectClassifier.classify R.colA hmono
                = P.cone.π₂ ≫ trueRel.colA :=
        P.cone.w
      -- hpb gives a unique map from any cone over (χ, t) to R.src; apply to P's cone.
      obtain ⟨u, ⟨hu1, _⟩, _⟩ := hpb ⟨P.cone.pt, P.cone.π₁, P.cone.π₂, hPsq⟩
      refine ⟨u, ?_, ?_⟩
      · show u ≫ R.colA = P.cone.π₁; exact hu1
      · show u ≫ R.colB = P.cone.π₂ ≫ trueRel.colB
        exact termΩ_uniq _ _
  · -- classify_unique: two classifying maps of R agree.  Reduce to classify_unique
    -- of the subobject classifier for the monic leg R.colA.
    intro Z R f g hf hg
    have hmono : Monic R.colA := relTo1_colA_mono R
    -- f classifies R.colA: R.colA is the pullback of t along f.  Use hsc.classify_unique.
    -- Show f = classify R.colA and g = classify R.colA.
    have key : ∀ (h : Z ⟶ HasSubobjectClassifier.omega),
        (RelHom R (relPullback h trueRel) ∧ RelHom (relPullback h trueRel) R) →
        h = HasSubobjectClassifier.classify R.colA hmono := by
      intro h hh
      obtain ⟨⟨w, hwA, hwB⟩, ⟨v, hvA, hvB⟩⟩ := hh
      -- The square (R.src, R.colA, term R.src, h) is a pullback of (h, t).  Then classify_unique.
      have hsq : R.colA ≫ h = termΩ R.src ≫ HasSubobjectClassifier.true := by
        -- R.colA ≫ h : use w : R.src → (relPullback h trueRel).src with w ≫ π₁ = R.colA.
        -- π₁ ≫ h = π₂ ≫ t (pullback square); so R.colA ≫ h = (w≫π₁)≫h = w≫(π₂≫t) = term ≫ t.
        let P := HasPullbacks.has h trueRel.colA
        have hPw : P.cone.π₁ ≫ h = P.cone.π₂ ≫ trueRel.colA := P.cone.w
        have hwA' : w ≫ P.cone.π₁ = R.colA := hwA
        calc R.colA ≫ h = (w ≫ P.cone.π₁) ≫ h := by rw [hwA']
          _ = w ≫ (P.cone.π₁ ≫ h) := Cat.assoc _ _ _
          _ = w ≫ (P.cone.π₂ ≫ trueRel.colA) := by rw [hPw]
          _ = termΩ R.src ≫ HasSubobjectClassifier.true := by
              rw [← Cat.assoc]; exact congrArg (· ≫ HasSubobjectClassifier.true) (termΩ_uniq _ _)
      refine HasSubobjectClassifier.classify_unique R.colA hmono h hsq ?_
      -- The cone (R.src, R.colA, term R.src) is a pullback of (h, t).
      intro d
      -- d : cone over (h, t).  Build a cone over P (chosen pb of (h, trueRel.colA=t)) then push to R via v.
      let P := HasPullbacks.has h trueRel.colA
      -- d.π₁ : d.pt → Z, d.π₂ : d.pt → 1, d.w : d.π₁ ≫ h = d.π₂ ≫ t.
      have hdw : d.π₁ ≫ h = d.π₂ ≫ trueRel.colA := d.w
      let e := P.lift ⟨d.pt, d.π₁, d.π₂, hdw⟩
      -- e ≫ π₁ = d.π₁ ; e ≫ π₂ = d.π₂.  v : (relPullback h trueRel).src → R.src, v ≫ R.colA = π₁.
      refine ⟨e ≫ v, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · -- (e ≫ v) ≫ R.colA = d.π₁.
          rw [Cat.assoc, hvA]; show e ≫ P.cone.π₁ = d.π₁; exact P.lift_fst _
        · exact termΩ_uniq _ _
      · -- uniqueness of the lift.
        intro y hy1 _
        -- y ≫ R.colA = d.π₁.  Both y and e≫v are sections; R.colA monic ⟹ equal.
        apply hmono
        rw [hy1, Cat.assoc, hvA]; show d.π₁ = e ≫ P.cone.π₁; exact (P.lift_fst _).symm
    rw [key f hf, key g hg]

/-- **(2) `Ω` is baseable.** -/
public theorem baseable_omega : Baseable (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  baseable_of_universalRel trueRel trueRel_universal

/-- **(3)+(4) Every object `B` is baseable.**  `B` is the equalizer of
    `χ := χ_{·} , ⊤∘! : [B] ⇉ Ω` (the classifying square of the singleton mono
    `{·} : B ↣ [B]` makes `B` the pullback of `t` along `χ`, i.e. that equalizer).
    `[B]` and `Ω` are baseable by (1),(2), and §1.859 closes the equalizer. -/
public theorem all_baseable (B : 𝒞) : Baseable B := by
  -- χ classifies the singleton mono; t∘! the constant ⊤.
  let m  := singletonMap923 B
  have hm : Monic m := singletonMapMonic923 B
  let χ  := HasSubobjectClassifier.classify m hm
  let c  := termΩ (HasPowerObject.powerObj (C := B)) ≫ HasSubobjectClassifier.true
  -- E := eqObj χ c is baseable by §1.859 (both [B] and Ω baseable).
  have hBE : Baseable (eqObj χ c) :=
    baseable_equalizer_is_baseable (baseable_powerObj B) baseable_omega χ c
  -- Now B ≅ eqObj χ c, and Baseable transports across iso.
  -- Forward e : B → eqObj χ c, via m equalizing χ, c.
  have hmeq : m ≫ χ = m ≫ c := by
    show m ≫ χ = m ≫ (termΩ _ ≫ HasSubobjectClassifier.true)
    rw [HasSubobjectClassifier.classify_sq m hm, ← Cat.assoc]
    exact congrArg (· ≫ HasSubobjectClassifier.true) (termΩ_uniq _ _)
  let e : B ⟶ eqObj χ c := eqLift χ c m hmeq
  -- Backward e' : eqObj χ c → B, via classify_pullback (m is the pullback of t along χ).
  have hpb := HasSubobjectClassifier.classify_pullback m hm
  -- eqMap χ c : eqObj → [B] forms a cone over (χ, t): eqMap ≫ χ = eqMap ≫ c = (eqMap≫term)≫t.
  have heqcone : eqMap χ c ≫ χ = termΩ (eqObj χ c) ≫ HasSubobjectClassifier.true := by
    rw [eqMap_eq χ c]; show eqMap χ c ≫ (termΩ _ ≫ HasSubobjectClassifier.true) = _
    rw [← Cat.assoc]; exact congrArg (· ≫ HasSubobjectClassifier.true) (termΩ_uniq _ _)
  obtain ⟨e', ⟨he'm, _⟩, _⟩ := hpb ⟨eqObj χ c, eqMap χ c, termΩ (eqObj χ c), heqcone⟩
  -- he'm : e' ≫ m = eqMap χ c.
  refine baseable_of_iso e e' ?_ ?_ hBE
  · -- e ≫ e' = id B.  Cancel the monic m: (e≫e')≫m = e≫(e'≫m) = e≫eqMap = m = id≫m.
    apply hm
    rw [Cat.assoc, he'm]; show e ≫ eqMap χ c = Cat.id B ≫ m
    rw [Cat.id_comp]; exact eqLift_fac χ c m hmeq
  · -- e' ≫ e = id (eqObj).  Cancel the monic eqMap: (e'≫e)≫eqMap = e'≫(e≫eqMap) = e'≫m = eqMap.
    have hqmono : Monic (eqMap χ c) := by
      intro W u v huv
      rw [eqLift_uniq χ c (u ≫ eqMap χ c) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) u rfl,
          eqLift_uniq χ c (u ≫ eqMap χ c) (by rw [Cat.assoc, Cat.assoc, eqMap_eq]) v huv.symm]
    apply hqmono
    rw [Cat.assoc]; show e' ≫ (e ≫ eqMap χ c) = Cat.id _ ≫ eqMap χ c
    rw [Cat.id_comp, eqLift_fac χ c m hmeq, he'm]

end WithClassifier

end Baseable923

end Freyd
