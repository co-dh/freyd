/-
  Freyd & Scedrov, *Categories and Allegories* — §2.16(13): AC regular categories
  and their effective reflections.

  "If C is an AC regular category, and Ĉ is its effective reflection, then C is
   equivalent to the full subcategory of projective objects in Ĉ.  Hence if C is
   not effective then Ĉ is not AC.

   BECAUSE: For each B ∈ Ĉ there exists A ∈ C and a cover A ↠ B.  If C ∈ C then it
   is projective in Ĉ: given B ↠ C in Ĉ choose A ↠ B where A ∈ C.  Since C is full
   in Ĉ and C is projective in C there exists C → A ↠ B → C = 1.
   If B is projective in Ĉ then choose A ↠ B where A ∈ C.  There exists
   (B → A → B) = 1 in Ĉ.  B is an equalizer of 1_A and A → B → A, forcing it to be
   isomorphic to a C-object."

  Formalized at the ALLEGORY level: `C = Map 𝒜` for a tabular allegory `𝒜`, and the
  effective reflection `Ĉ` is (the maps of) `Spl(Eq 𝒜) = SplEqObj 𝒜`, the reflexive
  splitting completion (§2.433, S2_433_SplEqInstance2).  Covers are the §2.147
  allegory covers (`Cat.id c ⊑ f° ≫ f`); AC (`CoversSplit`) says every cover splits
  with a map section (§1.57); projectivity (`ProjectiveObj`) is the retract form of
  the repo's `Freyd.Projective` (S1_57): every cover ONTO the object splits.

  Contents:
  •  `embEq` — the full faithful embedding `𝒜 ↪ Spl(Eq 𝒜)` (objects `a ↦ (a, 1_a)`;
     homs are literally `embHom`), with `Map`/order transfer.
  •  Step 1 (`covHom`) — every object `E = (a, e)` of `Spl(Eq 𝒜)` is covered by the
     embedded `embEq a`, via the idempotent `e` itself; the cover is SPLIT at the
     relation level (`covHom° ≫ covHom = 1`), but its section `covHom°` is a map only
     when `e` splits in `𝒜`.
  •  Step 2 (`embEq_projective`) — AC in `𝒜` makes every embedded object projective
     in `Spl(Eq 𝒜)` (the book's fullness argument, no pullbacks needed).
  •  Step 3/4 core (`splitsAsMap_of_section`) — a MAP section of the canonical cover
     forces the equivalence relation `e` to split as a map in `𝒜`: the section's
     underlying `S` satisfies `S ⊑ e`, so `S ≫ S° = e`, and splitting the coreflexive
     `S° ≫ S` (tabularity — the book's "equalizer of 1_A and A → B → A") yields the
     splitting map `f = S ≫ h°`.
  •  Step 4 (`effective_of_coversSplit`, `not_coversSplit_of_not_effective`) — if
     `Spl(Eq 𝒜)` is AC then `𝒜` is effective; contrapositive = the book's "hence".
  •  Step 3 (`projective_isoEmbedded`, headline `projective_iff_isoEmbedded`) — the
     projective objects of `Spl(Eq 𝒜)` are exactly (the isomorphs of) the embedded
     `𝒜`-objects.
  •  Stretch (`contains_map_of_entire`, `embEq_projective_lifts`) — §1.57 choice
     from cover-splitting, and the LIFTING form of projectivity for embedded objects.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/
module

public import Freyd.S2_433_SplEqInstance2
public import Freyd.S2_16b

universe v u

namespace Freyd.Alg

open Cat

/-! ## AC and projectivity at the allegory level (§1.57 / §2.147)

  A map `f : x ⟶ c` is a COVER iff `Cat.id c ⊑ f° ≫ f` (§2.147, equivalently
  `Entire f°`).  AC for the category of maps says every cover splits — §1.57's
  "all objects projective" in the retract form of `Freyd.Projective` (S1_57). -/

section ACDefs
variable {𝒜 : Type u} [Allegory 𝒜]

/-- **§1.57 (allegory form)**: `c` is PROJECTIVE if every §2.147 cover onto it —
    a map `f : x ⟶ c` with `Cat.id c ⊑ f° ≫ f` — splits with a MAP section.
    Mirrors the retract-form `Freyd.Projective` of S1_57 (every cover onto C splits). -/
@[expose] public def ProjectiveObj (c : 𝒜) : Prop :=
  ∀ {x : 𝒜} (f : x ⟶ c), Map f → Cat.id c ⊑ f° ≫ f →
    ∃ s : c ⟶ x, Map s ∧ s ≫ f = Cat.id c

/-- **AC** (§1.57, §2.16(13)): every cover of `Map 𝒜` splits, i.e. every object is
    projective.  This is the "axiom of choice" of an AC regular category, stated for
    its allegory of relations. -/
@[expose] public def CoversSplit (𝒜 : Type u) [Allegory 𝒜] : Prop :=
  ∀ c : 𝒜, ProjectiveObj c

/-- §2.147 covers compose: `(f ≫ g)° ≫ (f ≫ g) = g° ≫ (f° ≫ f) ≫ g ⊒ g° ≫ g ⊒ 1`. -/
theorem covers_compose {a b c : 𝒜} {f : a ⟶ b} {g : b ⟶ c}
    (hf : Cat.id b ⊑ f° ≫ f) (hg : Cat.id c ⊑ g° ≫ g) :
    Cat.id c ⊑ (f ≫ g)° ≫ (f ≫ g) := by
  have heq : (f ≫ g)° ≫ (f ≫ g) = g° ≫ (f° ≫ f) ≫ g := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have h1 : g° ≫ Cat.id b ≫ g ⊑ g° ≫ (f° ≫ f) ≫ g :=
    comp_mono_left g° (comp_mono_right hf g)
  rw [Cat.id_comp] at h1
  rw [heq]
  exact le_trans hg h1

end ACDefs

/-! ## Milestone (a): the embedding `𝒜 ↪ Spl(Eq 𝒜)`

  `SplEqObj 𝒜` restricts `SplObj 𝒜` to the REFLEXIVE symmetric idempotents, and its
  homs are the underlying `SplHom`s.  The identity idempotent is reflexive, so the
  §2.164 embedding `embObj`/`embHom` lands in `Spl(Eq 𝒜)`; fullness, faithfulness and
  preservation of `≫`/`°`/`∩` are inherited verbatim from S2_16. -/

section Embedding
variable {𝒜 : Type u} [Allegory 𝒜]

/-- The embedding `𝒜 → Spl(Eq 𝒜)` on objects: `a ↦ (a, 1_a)` (the identity idempotent
    is reflexive).  On homs it is literally `embHom` (§2.164), since `Spl(Eq)`-homs
    ARE the underlying `SplHom`s. -/
@[expose] public def embEq (a : 𝒜) : SplEqObj 𝒜 := ⟨embObj a, le_refl _⟩

/-- The embedding `𝒜 → Spl(Eq 𝒜)` on homs: `embHom` (§2.164), retyped at the
    embedded `Spl(Eq)`-objects. -/
@[expose] public def embEqHom {a b : 𝒜} (R : a ⟶ b) : (embEq a : SplEqObj 𝒜) ⟶ embEq b := embHom R

@[simp] theorem embEqHom_R {a b : 𝒜} (R : a ⟶ b) : (embEqHom R).R = R := rfl

/-- The embedding preserves identities in `Spl(Eq 𝒜)`. -/
public theorem embEq_id (a : 𝒜) : embEqHom (Cat.id a) = Cat.id (embEq a : SplEqObj 𝒜) :=
  SplHom.ext rfl

/-- The embedding preserves composition in `Spl(Eq 𝒜)`. -/
public theorem embEq_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    embEqHom (R ≫ S) = embEqHom R ≫ embEqHom S :=
  SplHom.ext rfl

/-- The embedding preserves reciprocation in `Spl(Eq 𝒜)`. -/
theorem embEq_recip {a b : 𝒜} (R : a ⟶ b) :
    embEqHom (R°) = (embEqHom R)° :=
  SplHom.ext rfl

/-- The embedding preserves intersection in `Spl(Eq 𝒜)`. -/
theorem embEq_inter {a b : 𝒜} (R S : a ⟶ b) :
    embEqHom (R ∩ S) = embEqHom R ∩ embEqHom S :=
  SplHom.ext rfl

/-- The embedding preserves and reflects MAPS: `embEqHom f` is a map of `Spl(Eq 𝒜)`
    iff `f` is a map of `𝒜` (both `dom` and the simplicity order compute underlying). -/
public theorem embEq_map_iff {a b : 𝒜} (f : a ⟶ b) :
    Map (embEqHom f) ↔ Map f := by
  constructor
  · rintro ⟨hent, hsimp⟩
    exact ⟨congrArg SplHom.R hent, (splEqLe_iff _ _).mp hsimp⟩
  · rintro ⟨hent, hsimp⟩
    exact ⟨SplHom.ext hent, (splEqLe_iff _ _).mpr hsimp⟩

end Embedding

/-! ## Milestone (b) — Step 1: every object of `Spl(Eq 𝒜)` is covered by an
  embedded object

  For `E = (a, e)` the idempotent `e` itself, viewed as a hom `embEq a ⟶ E`
  (it is `splDown e`, §2.164), is a MAP — entire exactly because `e` is REFLEXIVE
  (`1 ⊑ e`, the defining condition of `Spl(Eq)`) — and a SPLIT cover:
  `covHom° ≫ covHom = 1_E` on the nose.  Its section `covHom°` is a map only when
  `e` splits in `𝒜` (its simplicity would force `e ⊑ 1`), which is the whole point
  of §2.16(13). -/

section Covering
variable {𝒜 : Type u} [Allegory 𝒜]

/-- **Step 1 (the canonical cover)**: the §2.164 "down" leg `splDown`, viewed in
    `Spl(Eq 𝒜)`: the hom `embEq a ⟶ (a, e)` with underlying morphism `e`. -/
@[expose] public def covHom (E : SplEqObj 𝒜) : (embEq E.1.carrier : SplEqObj 𝒜) ⟶ E :=
  splDown E.1.idem

@[simp] theorem covHom_R (E : SplEqObj 𝒜) : (covHom E).R = E.1.idem.e := rfl

/-- The canonical cover is SPLIT at the relation level: `covHom° ≫ covHom = 1_E`
    (underlying `e° ≫ e = e`, which is the identity of `(a, e)`). -/
public theorem covHom_recip_comp (E : SplEqObj 𝒜) :
    (covHom E)° ≫ covHom E = Cat.id E := by
  apply SplHom.ext
  show E.1.idem.e° ≫ E.1.idem.e = E.1.idem.e
  rw [E.1.idem.sym, E.1.idem.idem]

/-- The canonical cover is a §2.147 COVER: `1_E ⊑ covHom° ≫ covHom`. -/
public theorem covHom_cover (E : SplEqObj 𝒜) :
    Cat.id E ⊑ (covHom E)° ≫ covHom E := by
  rw [covHom_recip_comp]; exact le_refl _

/-- `covHom ≫ covHom° = embHom e`: the canonical cover splits the embedded
    equivalence relation `e` (compare `spl_equivalence_splits_map`, §2.169). -/
theorem covHom_comp_recip (E : SplEqObj 𝒜) :
    covHom E ≫ (covHom E)° =
      (embHom E.1.idem.e : (embEq E.1.carrier : SplEqObj 𝒜) ⟶ embEq E.1.carrier) := by
  apply SplHom.ext
  show E.1.idem.e ≫ E.1.idem.e° = E.1.idem.e
  rw [E.1.idem.sym, E.1.idem.idem]

/-- **Step 1**: the canonical cover is a MAP of `Spl(Eq 𝒜)`.  Entireness is exactly
    REFLEXIVITY of `e` (`1 ⊑ e`, the `Spl(Eq)` condition `E.2`); simplicity is the
    split equation `covHom° ≫ covHom = 1`. -/
public theorem covHom_map (E : SplEqObj 𝒜) : Map (covHom E) := by
  refine ⟨?_, ?_⟩
  · -- Entire: dom(covHom) = 1.  Underlying: `1_a ∩ e ≫ e° = 1_a`, i.e. `1 ⊑ e`.
    apply SplHom.ext
    show Cat.id E.1.carrier ∩ E.1.idem.e ≫ E.1.idem.e° = Cat.id E.1.carrier
    rw [E.1.idem.sym, E.1.idem.idem]
    exact E.2
  · -- Simple: covHom° ≫ covHom = 1 ⊑ 1.
    show (covHom E)° ≫ covHom E ⊑ Cat.id E
    rw [covHom_recip_comp]; exact le_refl _

end Covering

/-! ## Milestone (d) — Step 2: AC in `𝒜` makes embedded objects projective

  The book's argument: given a cover `Φ : B ↠ embEq a`, choose the canonical cover
  `covHom B : embEq b ↠ B` (step 1); the composite is a cover BETWEEN EMBEDDED
  objects, hence (fullness) a cover of `𝒜`, which AC splits; composing the section
  with `covHom B` splits `Φ`.  No pullbacks are needed. -/

section EmbeddedProjective
variable {𝒜 : Type u} [Allegory 𝒜]

/-- **Step 2 (§2.16(13), "if C ∈ C then it is projective in Ĉ")**: if covers split in
    `Map 𝒜` (AC), then every embedded object `embEq a` is projective in `Spl(Eq 𝒜)`. -/
theorem embEq_projective (hAC : CoversSplit 𝒜) (a : 𝒜) :
    ProjectiveObj (embEq a : SplEqObj 𝒜) := by
  intro B Φ hΦ hcov
  -- The composite `covHom B ≫ Φ : embEq b ⟶ embEq a` is a map-cover between
  -- embedded objects.
  have hcomp_map : Map (covHom B ≫ Φ) := map_comp (covHom_map B) hΦ
  have hcomp_cov : Cat.id (embEq a : SplEqObj 𝒜) ⊑ (covHom B ≫ Φ)° ≫ (covHom B ≫ Φ) :=
    covers_compose (covHom_cover B) hcov
  -- By fullness it is `embHom g` for `g := (covHom B ≫ Φ).R`; transfer map + cover to `𝒜`.
  have hg_map : Map (covHom B ≫ Φ).R :=
    (embEq_map_iff _).mp ((embHom_full (covHom B ≫ Φ)).symm ▸ hcomp_map)
  have hg_cov : Cat.id a ⊑ (covHom B ≫ Φ).R° ≫ (covHom B ≫ Φ).R :=
    (splEqLe_iff _ _).mp hcomp_cov
  -- AC in `𝒜` splits the cover `g`.
  obtain ⟨t, ht_map, ht_sec⟩ := hAC a (covHom B ≫ Φ).R hg_map hg_cov
  -- The section of `Φ` is `embEqHom t ≫ covHom B`.
  refine ⟨embEqHom t ≫ covHom B, map_comp ((embEq_map_iff t).mpr ht_map) (covHom_map B), ?_⟩
  apply SplHom.ext
  show (t ≫ B.1.idem.e) ≫ Φ.R = Cat.id a
  rw [Cat.assoc]
  exact ht_sec

end EmbeddedProjective

/-! ## The step 3/4 core: a MAP section of the canonical cover splits the
  equivalence relation in `𝒜`

  Book: "There exists (B → A → B) = 1 in Ĉ.  B is an equalizer of 1_A and
  A → B → A, forcing it to be isomorphic to a C-object."  Here: a map section
  `s : (a,e) ⟶ embEq a` of `covHom` has underlying `S` with `e ≫ S = S` (typing),
  `S ≫ e = e` (section), `S° ≫ S ⊑ 1` (simple), `e ⊑ S ≫ S°` (entire).  Since `e`
  is reflexive, `S = S ≫ 1 ⊑ S ≫ e = e`, whence `S ≫ S° = e`.  The "equalizer" is
  the splitting of the COREFLEXIVE `S° ≫ S` (tabularity, §2.163): a map `h : d ⟶ a`
  with `h° ≫ h = S° ≫ S`, `h ≫ h° = 1_d`; then `f := S ≫ h°` is a map splitting `e`. -/

/-- **Steps 3/4 core**: a MAP section of the canonical cover of `(a, e)` yields a
    map-splitting of the equivalence relation `e` in `𝒜` (§2.163 effectiveness of
    `e`).  Tabularity of `𝒜` supplies the splitting of the coreflexive `S° ≫ S` —
    the book's "B is an equalizer of 1_A and A → B → A". -/
public theorem splitsAsMap_of_section {𝒜 : Type u} [TabularAllegory 𝒜] (B : SplEqObj 𝒜)
    {s : B ⟶ (embEq B.1.carrier : SplEqObj 𝒜)} (hs : Map s)
    (hsec : s ≫ covHom B = Cat.id B) :
    ∃ (d : 𝒜) (f : B.1.carrier ⟶ d), SplitsAsMap f B.1.idem.e := by
  obtain ⟨hs_ent, hs_simp⟩ := hs
  -- Underlying data in `𝒜`.
  have hsec' : s.R ≫ B.1.idem.e = B.1.idem.e := congrArg SplHom.R hsec
  have hsimple : s.R° ≫ s.R ⊑ Cat.id B.1.carrier := (splEqLe_iff _ _).mp hs_simp
  have hentire : B.1.idem.e ⊑ s.R ≫ s.R° := congrArg SplHom.R hs_ent
  -- `S ⊑ e` from the section equation and reflexivity of `e`.
  have hSle : s.R ⊑ B.1.idem.e := by
    have h1 : s.R ≫ Cat.id B.1.carrier ⊑ s.R ≫ B.1.idem.e := comp_mono_left s.R B.2
    have h2 : s.R ≫ Cat.id B.1.carrier = s.R := Cat.comp_id s.R
    rw [h2, hsec'] at h1
    exact h1
  -- `S ≫ S° = e`.
  have hSS : s.R ≫ s.R° = B.1.idem.e := by
    refine le_antisymm ?_ hentire
    have h1 : s.R ≫ s.R° ⊑ B.1.idem.e ≫ B.1.idem.e° :=
      le_trans (comp_mono_right hSle s.R°) (comp_mono_left B.1.idem.e (recip_mono hSle))
    rwa [B.1.idem.sym, B.1.idem.idem] at h1
  -- Split the coreflexive `S° ≫ S` (tabularity, §2.163).
  obtain ⟨d, h, _hh_map, hh1, hh2⟩ := coreflexive_splits (𝒜 := 𝒜) hsimple
  -- `f := S ≫ h°` splits `e` as a map.
  have hff : (s.R ≫ h°) ≫ (s.R ≫ h°)° = B.1.idem.e := by
    rw [Allegory.recip_comp, Allegory.recip_recip]
    calc (s.R ≫ h°) ≫ h ≫ s.R°
        = s.R ≫ (h° ≫ h) ≫ s.R° := by simp [Cat.assoc]
      _ = s.R ≫ (s.R° ≫ s.R) ≫ s.R° := by rw [hh1]
      _ = (s.R ≫ s.R°) ≫ s.R ≫ s.R° := by simp [Cat.assoc]
      _ = B.1.idem.e ≫ B.1.idem.e := by rw [hSS]
      _ = B.1.idem.e := B.1.idem.idem
  have hff' : (s.R ≫ h°)° ≫ (s.R ≫ h°) = Cat.id d := by
    rw [Allegory.recip_comp, Allegory.recip_recip]
    calc (h ≫ s.R°) ≫ s.R ≫ h°
        = h ≫ (s.R° ≫ s.R) ≫ h° := by simp [Cat.assoc]
      _ = h ≫ (h° ≫ h) ≫ h° := by rw [hh1]
      _ = (h ≫ h°) ≫ h ≫ h° := by simp [Cat.assoc]
      _ = Cat.id d := by rw [hh2, Cat.id_comp]
  refine ⟨d, s.R ≫ h°, ⟨?_, ?_⟩, hff, hff'⟩
  · -- Entire: `dom f = 1 ∩ f ≫ f° = 1 ∩ e = 1` by reflexivity.
    show Cat.id B.1.carrier ∩ (s.R ≫ h°) ≫ (s.R ≫ h°)° = Cat.id B.1.carrier
    rw [hff]; exact B.2
  · -- Simple: `f° ≫ f = 1 ⊑ 1`.
    show (s.R ≫ h°)° ≫ (s.R ≫ h°) ⊑ Cat.id d
    rw [hff']; exact le_refl _

/-! ## Milestone (c) — Step 4: if `Spl(Eq 𝒜)` is AC then `𝒜` is effective

  The book's "hence": the canonical cover of the object `(a, e)` splits by AC in
  the reflection, and its map section transports (via the core lemma) to a
  map-splitting of `e` in `𝒜`. -/

section Effectiveness
variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-- The object of `Spl(Eq 𝒜)` carried by an equivalence relation
    (reflexive symmetric idempotent) `e : a ⟶ a` of `𝒜`. -/
@[expose] public def eqRelObj {a : 𝒜} (e : a ⟶ a) (hrefl : Cat.id a ⊑ e) (hsym : e° = e)
    (hidem : e ≫ e = e) : SplEqObj 𝒜 :=
  ⟨⟨a, e, hsym, hidem⟩, hrefl⟩

/-- **Step 4 (§2.16(13))**: if every cover of `Map (Spl(Eq 𝒜))` splits (the effective
    reflection is AC), then every equivalence relation of `𝒜` splits as a map — `𝒜`
    is EFFECTIVE (§2.169 shape, cf. `EffectiveAllegory.split_symmetric_idempotent`). -/
public theorem effective_of_coversSplit (hAC : CoversSplit (SplEqObj 𝒜))
    {a : 𝒜} (e : a ⟶ a) (hrefl : Cat.id a ⊑ e) (hsym : e° = e) (hidem : e ≫ e = e) :
    ∃ (d : 𝒜) (f : a ⟶ d), SplitsAsMap f e := by
  obtain ⟨s, hs_map, hs_sec⟩ :=
    hAC (eqRelObj e hrefl hsym hidem) (covHom _) (covHom_map _) (covHom_cover _)
  exact splitsAsMap_of_section (eqRelObj e hrefl hsym hidem) hs_map hs_sec

/-- **§2.16(13), "hence if C is not effective then Ĉ is not AC"**: an equivalence
    relation of `𝒜` with no map-splitting witnesses that covers do NOT all split in
    the effective reflection `Spl(Eq 𝒜)`. -/
public theorem not_coversSplit_of_not_effective
    {a : 𝒜} (e : a ⟶ a) (hrefl : Cat.id a ⊑ e) (hsym : e° = e) (hidem : e ≫ e = e)
    (hno : ∀ (d : 𝒜) (f : a ⟶ d), ¬ SplitsAsMap f e) :
    ¬ CoversSplit (SplEqObj 𝒜) := fun hAC =>
  let ⟨d, f, hf⟩ := effective_of_coversSplit hAC e hrefl hsym hidem
  hno d f hf

end Effectiveness

/-! ## Milestone (e) — Step 3: projective objects are (isomorphic to) embedded
  objects — and the §2.16(13) HEADLINE

  Forward: a projective `B` splits its own canonical cover; the core lemma turns
  the map section into a map-splitting `f` of `e` in `𝒜`, and `(f, f°)` is then an
  isomorphism `B ≅ embEq d` of `Spl(Eq 𝒜)` by pure computation.  Backward: an object
  isomorphic to an embedded one inherits its projectivity (step 2, given AC in `𝒜`). -/

section ProjectiveEmbedded

/-- A map-splitting `f` of `e = B.1.idem.e` in `𝒜` makes `B` ISOMORPHIC to the
    embedded object `embEq d` in `Spl(Eq 𝒜)` — the iso legs are `f` and `f°`, both
    maps.  (The book's "forcing it to be isomorphic to a C-object".) -/
theorem isoEmbedded_of_splitsAsMap {𝒜 : Type u} [Allegory 𝒜] (B : SplEqObj 𝒜) {d : 𝒜}
    {f : B.1.carrier ⟶ d} (h : SplitsAsMap f B.1.idem.e) :
    ∃ (i : B ⟶ (embEq d : SplEqObj 𝒜)) (j : (embEq d : SplEqObj 𝒜) ⟶ B),
      Map i ∧ Map j ∧ i ≫ j = Cat.id B ∧ j ≫ i = Cat.id (embEq d) := by
  obtain ⟨_hf_map, hff, hff'⟩ := h
  -- `e ≫ f = f` and `f° ≫ e = f°` (so `f`, `f°` are well-typed `Spl(Eq)`-homs).
  have hef : B.1.idem.e ≫ f = f := by
    calc B.1.idem.e ≫ f = (f ≫ f°) ≫ f := by rw [hff]
      _ = f ≫ f° ≫ f := Cat.assoc f (f°) f
      _ = f ≫ Cat.id d := by rw [hff']
      _ = f := Cat.comp_id f
  have hfe : f° ≫ B.1.idem.e = f° := by
    have h2 : (B.1.idem.e ≫ f)° = f° := congrArg Allegory.recip hef
    rwa [Allegory.recip_comp, B.1.idem.sym] at h2
  let i : B ⟶ (embEq d : SplEqObj 𝒜) :=
    ⟨f, by show B.1.idem.e ≫ f ≫ Cat.id d = f; rw [Cat.comp_id]; exact hef⟩
  let j : (embEq d : SplEqObj 𝒜) ⟶ B :=
    ⟨f°, by show Cat.id d ≫ f° ≫ B.1.idem.e = f°; rw [Cat.id_comp]; exact hfe⟩
  refine ⟨i, j, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Entire i: `e ∩ f ≫ f° = e ∩ e = e`.
    apply SplHom.ext
    show B.1.idem.e ∩ f ≫ f° = B.1.idem.e
    rw [hff]; exact Allegory.inter_idem _
  · -- Simple i: `i° ≫ i = 1 ⊑ 1`.
    have h2 : (i° ≫ i : (embEq d : SplEqObj 𝒜) ⟶ embEq d) = Cat.id (embEq d) := by
      apply SplHom.ext; show f° ≫ f = Cat.id d; exact hff'
    show i° ≫ i ⊑ Cat.id (embEq d)
    rw [h2]; exact le_refl _
  · -- Entire j: `1 ∩ f° ≫ f°° = 1 ∩ 1 = 1`.
    apply SplHom.ext
    show Cat.id d ∩ f° ≫ f°° = Cat.id d
    rw [Allegory.recip_recip, hff']; exact Allegory.inter_idem _
  · -- Simple j: `j° ≫ j = e ⊑ e = 1_B`.
    have h2 : (j° ≫ j : B ⟶ B) = Cat.id B := by
      apply SplHom.ext; show f°° ≫ f° = B.1.idem.e
      rw [Allegory.recip_recip]; exact hff
    show j° ≫ j ⊑ Cat.id B
    rw [h2]; exact le_refl _
  · apply SplHom.ext; show f ≫ f° = B.1.idem.e; exact hff
  · apply SplHom.ext; show f° ≫ f = Cat.id d; exact hff'

/-- **Step 3 (§2.16(13), "if B is projective in Ĉ then … it is isomorphic to a
    C-object")**: a projective object of `Spl(Eq 𝒜)` is isomorphic (by maps) to an
    embedded `𝒜`-object. -/
theorem projective_isoEmbedded {𝒜 : Type u} [TabularAllegory 𝒜] {B : SplEqObj 𝒜}
    (hproj : ProjectiveObj B) :
    ∃ (d : 𝒜) (i : B ⟶ (embEq d : SplEqObj 𝒜)) (j : (embEq d : SplEqObj 𝒜) ⟶ B),
      Map i ∧ Map j ∧ i ≫ j = Cat.id B ∧ j ≫ i = Cat.id (embEq d) := by
  obtain ⟨s, hs_map, hs_sec⟩ := hproj (covHom B) (covHom_map B) (covHom_cover B)
  obtain ⟨d, f, hsplit⟩ := splitsAsMap_of_section B hs_map hs_sec
  exact ⟨d, isoEmbedded_of_splitsAsMap B hsplit⟩

/-- An object of `Spl(Eq 𝒜)` isomorphic (by maps) to an embedded object is
    projective, given AC in `𝒜` — projectivity of `embEq c` (step 2) transfers
    across the isomorphism. -/
theorem projective_of_isoEmbedded {𝒜 : Type u} [Allegory 𝒜] (hAC : CoversSplit 𝒜)
    {B : SplEqObj 𝒜} {c : 𝒜} {i : B ⟶ (embEq c : SplEqObj 𝒜)}
    {j : (embEq c : SplEqObj 𝒜) ⟶ B} (hi : Map i) (hj : Map j)
    (hij : i ≫ j = Cat.id B) (hji : j ≫ i = Cat.id (embEq c)) :
    ProjectiveObj B := by
  intro X Φ hΦ hcov
  -- `Φ ≫ i : X ⟶ embEq c` is a map-cover (`i` is a split cover: `1 = i°(j°j)i ⊑ i°i`).
  have hi_cover : Cat.id (embEq c : SplEqObj 𝒜) ⊑ i° ≫ i := by
    have h0 : Cat.id (embEq c : SplEqObj 𝒜) = (j ≫ i)° ≫ (j ≫ i) := by
      rw [hji, recip_id, Cat.id_comp]
    have heq : (j ≫ i)° ≫ (j ≫ i) = i° ≫ (j° ≫ j) ≫ i := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have h1 : i° ≫ (j° ≫ j) ≫ i ⊑ i° ≫ Cat.id B ≫ i :=
      comp_mono_left i° (comp_mono_right hj.2 i)
    rw [Cat.id_comp] at h1
    rw [h0, heq]
    exact h1
  obtain ⟨t, ht_map, ht_sec⟩ :=
    embEq_projective hAC c (Φ ≫ i) (map_comp hΦ hi) (covers_compose hcov hi_cover)
  refine ⟨i ≫ t, map_comp hi ht_map, ?_⟩
  -- `(i ≫ t) ≫ Φ = ((i ≫ t) ≫ Φ) ≫ (i ≫ j) = (i ≫ (t ≫ (Φ ≫ i))) ≫ j = i ≫ j = 1_B`.
  calc (i ≫ t) ≫ Φ
      = ((i ≫ t) ≫ Φ) ≫ Cat.id B := (Cat.comp_id _).symm
    _ = ((i ≫ t) ≫ Φ) ≫ i ≫ j := by rw [hij]
    _ = (i ≫ (t ≫ (Φ ≫ i))) ≫ j := by simp [Cat.assoc]
    _ = (i ≫ Cat.id (embEq c)) ≫ j := by rw [ht_sec]
    _ = Cat.id B := by rw [Cat.comp_id, hij]

/-- **§2.16(13) HEADLINE**: for a tabular allegory `𝒜` with AC (`Map 𝒜` an AC regular
    category), the PROJECTIVE objects of the effective reflection `Spl(Eq 𝒜)` are
    EXACTLY the objects isomorphic to embedded `𝒜`-objects — "C is equivalent to the
    full subcategory of projective objects in Ĉ" (the embedding is full and faithful,
    `embHom_full`/`embHom_injective`, and this identifies its closure under isomorphism
    with the projectives). -/
theorem projective_iff_isoEmbedded {𝒜 : Type u} [TabularAllegory 𝒜]
    (hAC : CoversSplit 𝒜) (B : SplEqObj 𝒜) :
    ProjectiveObj B ↔
      ∃ (d : 𝒜) (i : B ⟶ (embEq d : SplEqObj 𝒜)) (j : (embEq d : SplEqObj 𝒜) ⟶ B),
        Map i ∧ Map j ∧ i ≫ j = Cat.id B ∧ j ≫ i = Cat.id (embEq d) :=
  ⟨fun hproj => projective_isoEmbedded hproj,
   fun ⟨_, _, _, hi, hj, hij, hji⟩ => projective_of_isoEmbedded hAC hi hj hij hji⟩

end ProjectiveEmbedded

/-! ## Milestone (f) — stretch: §1.57 choice, and the LIFTING form of projectivity

  From cover-splitting and tabularity, every entire relation contains a map (§1.57
  choice ⟸ projectivity, allegory form).  With it, embedded objects satisfy the full
  LIFTING form of projectivity in `Spl(Eq 𝒜)`: any map into the target of a cover
  lifts through the cover.  The relational lift `ψ ≫ Φ°` is entire; pulling it back
  to `𝒜` through the canonical cover and choosing a map inside it gives the lift
  (two maps with `ℓ ≫ Φ ⊑ ψ` are equal, `map_order_discrete`). -/

section Lifting

/-- **§1.57 (choice from AC, allegory form)**: in a tabular allegory with
    cover-splitting, every ENTIRE relation contains a map.  Tabulate `R = u° ≫ v`;
    `u` is a cover (`entire_of_comp_entire`), its section `s` satisfies `s ⊑ u°`,
    so `s ≫ v ⊑ u° ≫ v = R` is the contained map. -/
theorem contains_map_of_entire {𝒜 : Type u} [TabularAllegory 𝒜] (hAC : CoversSplit 𝒜)
    {x y : 𝒜} (R : x ⟶ y) (hR : Entire R) : ∃ m : x ⟶ y, Map m ∧ m ⊑ R := by
  obtain ⟨t, u, v, hu, hv, hR_eq, _htab⟩ := TabularAllegory.tabular R
  -- `u` is a cover: `Entire R = Entire (u° ≫ v)` forces `Entire u°`.
  have hu_cover : Cat.id x ⊑ u° ≫ u := by
    have h1 : Entire (u° ≫ v) := hR_eq ▸ hR
    have h2 : Entire (u°) := entire_of_comp_entire h1
    dsimp [Entire, dom] at h2
    rw [Allegory.recip_recip] at h2
    exact h2
  obtain ⟨s, hs_map, hs_sec⟩ := hAC x u hu hu_cover
  -- `s ⊑ u°`: `s = s ≫ 1 ⊑ s ≫ u ≫ u° = u°`.
  have hsu : s ⊑ u° := by
    have h1 : s ≫ Cat.id t ⊑ s ≫ u ≫ u° := comp_mono_left s (entire_id_le hu.1)
    rw [Cat.comp_id, ← Cat.assoc, hs_sec, Cat.id_comp] at h1
    exact h1
  exact ⟨s ≫ v, map_comp hs_map hv,
    by rw [hR_eq]; exact comp_mono_right hsu v⟩

/-- **Lifting-form projectivity of embedded objects (§2.16(13) stretch)**: given a
    cover `Φ : X ↠ C` in `Spl(Eq 𝒜)` and a map `ψ : embEq a ⟶ C`, there is a map
    lift `ℓ : embEq a ⟶ X` with `ℓ ≫ Φ = ψ`.  Route: the relational lift
    `ψ ≫ Φ° ≫ covHom X°` is an entire relation between embedded objects; §1.57
    choice picks a map `m` inside its underlying relation, and `ℓ := embHom m ≫
    covHom X` works since `ℓ ≫ Φ ⊑ ψ` and both are maps. -/
theorem embEq_projective_lifts {𝒜 : Type u} [TabularAllegory 𝒜] (hAC : CoversSplit 𝒜)
    {a : 𝒜} {X C : SplEqObj 𝒜} (Φ : X ⟶ C) (hΦ : Map Φ)
    (hcov : Cat.id C ⊑ Φ° ≫ Φ) (ψ : (embEq a : SplEqObj 𝒜) ⟶ C) (hψ : Map ψ) :
    ∃ ℓ : (embEq a : SplEqObj 𝒜) ⟶ X, Map ℓ ∧ ℓ ≫ Φ = ψ := by
  -- A map that is a cover satisfies `Φ° ≫ Φ = 1` exactly.
  have hΦΦ : Φ° ≫ Φ = Cat.id C := le_antisymm hΦ.2 hcov
  -- `Φ°` and `covHom X°` are entire, so the relational lift is entire.
  have hΦo_ent : Entire (Φ°) := by
    dsimp [Entire, dom]
    rw [Allegory.recip_recip, hΦΦ]
    exact Allegory.inter_idem _
  have hχo_ent : Entire ((covHom X)°) := by
    dsimp [Entire, dom]
    rw [Allegory.recip_recip, covHom_recip_comp]
    exact Allegory.inter_idem _
  have hR_ent : Entire (ψ ≫ Φ° ≫ (covHom X)°) :=
    entire_comp hψ.1 (entire_comp hΦo_ent hχo_ent)
  -- Pull entireness down to `𝒜` and choose a map inside.
  have hr_ent : Entire ((ψ ≫ Φ° ≫ (covHom X)°).R) := congrArg SplHom.R hR_ent
  obtain ⟨m, hm_map, hm_le⟩ := contains_map_of_entire hAC _ hr_ent
  refine ⟨embEqHom m ≫ covHom X,
    map_comp ((embEq_map_iff m).mpr hm_map) (covHom_map X), ?_⟩
  -- Both sides are maps; it suffices to show `ℓ ≫ Φ ⊑ ψ`.
  apply map_order_discrete
    (map_comp (map_comp ((embEq_map_iff m).mpr hm_map) (covHom_map X)) hΦ) hψ
  rw [splEqLe_iff]
  -- Underlying goal in `𝒜`: `(m ≫ e_X) ≫ Φ.R ⊑ ψ.R`.
  show (m ≫ X.1.idem.e) ≫ Φ.R ⊑ ψ.R
  have hΦΦ' : Φ.R° ≫ Φ.R = C.1.idem.e := congrArg SplHom.R hΦΦ
  -- Upper bound the lift by the relational lift and collapse.
  have h1 : (m ≫ X.1.idem.e) ≫ Φ.R ⊑
      ((ψ.R ≫ Φ.R° ≫ X.1.idem.e°) ≫ X.1.idem.e) ≫ Φ.R :=
    comp_mono_right (comp_mono_right hm_le X.1.idem.e) Φ.R
  have h2 : ((ψ.R ≫ Φ.R° ≫ X.1.idem.e°) ≫ X.1.idem.e) ≫ Φ.R = ψ.R := by
    rw [X.1.idem.sym]
    calc ((ψ.R ≫ Φ.R° ≫ X.1.idem.e) ≫ X.1.idem.e) ≫ Φ.R
        = ψ.R ≫ Φ.R° ≫ X.1.idem.e ≫ X.1.idem.e ≫ Φ.R := by simp [Cat.assoc]
      _ = ψ.R ≫ Φ.R° ≫ Φ.R := by rw [Φ.fixed_left, Φ.fixed_left]
      _ = ψ.R ≫ C.1.idem.e := by rw [hΦΦ']
      _ = ψ.R := ψ.fixed_right
  rw [h2] at h1
  exact h1

end Lifting

end Freyd.Alg
