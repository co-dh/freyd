/-
  Freyd & Scedrov, *Categories and Allegories* — §2.217:

    "As repeatedly promised in chapter 1: A PRE-LOGOS MAY BE FAITHFULLY REPRESENTED IN A
     POSITIVE PRE-LOGOS.  Because: starting with a pre-logos C we may construct its positive
     reflection as the category of maps in the positive reflection of the allegory of
     relations in C."

  The building blocks are already in the repo:
    • `Mat 𝒜` (the positive reflection `𝒜⁺`, §2.216) with its category/Allegory/Distributive/
      Division/Tabular/Unitary/POSITIVE instances — `Freyd/S2_216_MatrixAllegory.lean`;
    • `Map(Mat(Rel C))` a positive pre-logos + the faithful `embed217 : C ↪ Map(Mat(Rel C))`
      (`s217PreLogos`, `embed217_faithful`, `s217_faithful_embed_into_positive`) —
      `Freyd/S2_111_RelCat.lean`.

  WHAT THIS FILE ADDS (the §2.217 pieces that were still missing):

  1. Freyd's PARENTHETICAL CHARACTERIZATIONS of the structural morphisms of `Mat 𝒜`:
       • `mat_entire_iff`   — a matrix `M` is ENTIRE iff for each row `i`,
                              `1 ⊑ ∪_j M i j ≫ (M i j)°`;
       • `mat_simple_iff`   — `M` is SIMPLE iff each entry is simple and
                              `(M i j)° ≫ M i j' = 𝟘` for `j ≠ j'` (same-row cross terms vanish);
       • the RECAST `S° ≫ T = 𝟘 ↔ dom S ∩ dom T = 𝟘` via the book's two displayed chains
         (`dom_inter_dom_le`, `recip_comp_le_through_doms`,
          `recip_comp_eq_zero_iff_dom_disjoint`);
       • `mat_simple_iff_dom_disjoint` — ".. iff each entry is simple and the domains of any
         two entries in the same row are disjoint";
       • `mat_map_iff` — "It is a map iff each entry is simple and domains of the entries on
         any row form a partition of 1" (`mat_entire_iff_dom_partition` supplies the
         join-is-1 half of "partition").

  2. The singleton embedding `α ↦ ⟨α⟩` as a REPRESENTATION of distributive allegories, over a
     BARE `[DistributiveAllegory 𝒜]` (moved here from `S2_21b`, which needed it only in the
     tabular-unitary case): `matEmbed` (an `AllegoryFunctor`: preserves `≫`, `id`, `°`, `∩`),
     `matEmbed_faithful`, and the strengthenings Freyd states — FULL (`matEmbed_full`) and
     order-reflecting (`matEmbed_le_iff`); `matEmbed_unitObj` records that it carries the unit
     to the unit (§2.216 "units are preserved").

  3. `matTabularUnitaryPositive` — `Mat 𝒜` of a tabular unitary DISTRIBUTIVE allegory is a
     tabular unitary POSITIVE allegory, bundled as the hypothesis class that the §2.218
     positive-case pipeline (`tabular_repr_in_power_of_sets`) consumes.

  4. The HEADLINE `prelogos_repr_in_positive_prelogos`: for a pre-logos `C`, the composite
     `C → Map(Mat(Rel C))` is a FUNCTOR (`embed217Functor`, upgrading `embed217` from a raw
     per-hom injection to a functorial representation via `embed217_id`/`embed217_comp`) that
     is faithful, into a positive pre-logos.

  Downstream, `Freyd/S2_21b.lean` composes `matEmbed` with the positive §2.218
  `tabular_repr_in_power_of_sets` to remove positivity from §2.218
  (`tabular_repr_in_power_of_sets_distributive`).
-/
module

public import Freyd.S2_111_RelCat

universe v u

/-! ## §A  The `Dom`-disjointness recast (Freyd §2.217, parenthetical)

  "We may recast the last condition.  `S°T = 0` iff `Dom S` and `Dom T` are disjoint:

      (Dom S) ∩ (Dom T) ⊂ (Dom S)(Dom T) ⊂ SS°TT°,
      S°T ⊂ S°(Dom S)(Dom T)T ⊂ S°[Dom(S) ∩ Dom(T)]T."

  The two displayed containment chains, then the iff.  Pure distributive-allegory facts
  (only `𝟘` and its absorption laws are needed beyond `Allegory`), so they live in
  `Freyd.Alg` beside §2.12. -/

namespace Freyd.Alg

section DomDisjoint

variable {𝒜 : Type u} [DistributiveAllegory.{u, v} 𝒜]

/-- Freyd §2.217, FIRST displayed chain:
    `(Dom S) ∩ (Dom T) ⊂ (Dom S)(Dom T) ⊂ SS°TT°`.  The first link is §2.121
    (`coreflexive_comp_eq_inter`, an equality for coreflexives); the second is
    `dom R ⊑ R ≫ R°` in each factor. -/
public theorem dom_inter_dom_le {a b c : 𝒜} (S : a ⟶ b) (T : a ⟶ c) :
    dom S ∩ dom T ⊑ (S ≫ S°) ≫ (T ≫ T°) := by
  rw [← coreflexive_comp_eq_inter (dom_coreflexive S) (dom_coreflexive T)]
  exact le_trans (comp_mono_right (inter_lb_right _ _) (dom T))
                 (comp_mono_left (S ≫ S°) (inter_lb_right _ _))

/-- Freyd §2.217, SECOND displayed chain:
    `S°T ⊂ S°(Dom S)(Dom T)T ⊂ S°[Dom(S) ∩ Dom(T)]T`.  The first link is
    `R ⊑ dom R ≫ R` (§2.122) on both factors (reciprocated on the left); the second is
    §2.121 collapsing `(Dom S)(Dom T)` to the meet. -/
public theorem recip_comp_le_through_doms {a b c : 𝒜} (S : a ⟶ b) (T : a ⟶ c) :
    S° ≫ T ⊑ S° ≫ (dom S ∩ dom T) ≫ T := by
  -- `S° ⊑ S° ≫ dom S`: reciprocate `S ⊑ dom S ≫ S` and use `(dom S)° = dom S`.
  have hS : S° ⊑ S° ≫ dom S := by
    have h := recip_mono (le_dom_comp S)
    rwa [Allegory.recip_comp, dom_recip] at h
  have hchain : S° ≫ T ⊑ (S° ≫ dom S) ≫ (dom T ≫ T) :=
    le_trans (comp_mono_right hS T) (comp_mono_left (S° ≫ dom S) (le_dom_comp T))
  have hassoc : (S° ≫ dom S) ≫ (dom T ≫ T) = S° ≫ (dom S ≫ dom T) ≫ T := by
    rw [Cat.assoc, ← Cat.assoc (dom S) (dom T) T]
  rw [hassoc, coreflexive_comp_eq_inter (dom_coreflexive S) (dom_coreflexive T)] at hchain
  exact hchain

/-- **Freyd §2.217 (parenthetical recast): `S°T = 0` iff `Dom S` and `Dom T` are disjoint.**
    Forward: chain 1 sandwiches the meet of the domains under `S(S°T)T° = S𝟘T° = 𝟘`.
    Reverse: chain 2 sandwiches `S°T` under `S°𝟘T = 𝟘`. -/
public theorem recip_comp_eq_zero_iff_dom_disjoint {a b c : 𝒜} (S : a ⟶ b) (T : a ⟶ c) :
    S° ≫ T = 𝟘 ↔ dom S ∩ dom T = 𝟘 := by
  constructor
  · intro h
    refine le_antisymm ?_ (zero_le _)
    have hz : (S ≫ S°) ≫ (T ≫ T°) = 𝟘 := by
      rw [Cat.assoc, ← Cat.assoc S° T T°, h, DistributiveAllegory.zero_comp,
          DistributiveAllegory.comp_zero]
    exact hz ▸ dom_inter_dom_le S T
  · intro h
    refine le_antisymm ?_ (zero_le _)
    have hz : S° ≫ (dom S ∩ dom T) ≫ T = 𝟘 := by
      rw [h, DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]
    exact hz ▸ recip_comp_le_through_doms S T

end DomDisjoint

end Freyd.Alg

/-! ## §B  Entire / simple / map matrices (Freyd §2.217, parenthetical)

  "(A matrix R is entire iff for each i, `1 ⊂ ∪_j R_ij R_ij°`.  It is simple iff `R_ij` is
  simple for each i,j and `R_ij° R_ij' = 0` for all i, j, j', j ≠ j'. …  Hence a matrix is
  simple iff each entry is simple and the domains of any two entries in the same row are
  disjoint.  It is a map iff each entry is simple and domains of the entries on any row form
  a partition of 1.)" -/

namespace Freyd.Alg.Mat

section MatCharacterizations

variable {𝒜 : Type u} [DistributiveAllegory.{u, v} 𝒜]

/-- **§2.217: a matrix is ENTIRE iff each row's polarizations join above the identity** —
    "R is entire iff for each i, `1 ⊂ ∪_j R_ij R_ij°`". -/
public theorem mat_entire_iff {X Y : MatObj 𝒜} (M : X ⟶ Y) :
    Entire (𝒜 := MatObj 𝒜) M ↔
      ∀ i : Fin X.n, Cat.id (X.objs i) ⊑ finJoin (fun j => M i j ≫ (M i j)°) := by
  constructor
  · intro h i
    -- entry (i,i) of `dom M = matId X`.
    have he : matInter (matId X) (matComp M (matRecip M)) = matId X := h
    have hi := congrFun (congrFun he i) i
    simp only [matInter, matComp, matRecip, matId, ↓reduceDIte] at hi
    exact hi
  · intro h
    show matInter (matId X) (matComp M (matRecip M)) = matId X
    funext i i'
    by_cases hii : i = i'
    · subst hii
      simp only [matInter, matComp, matRecip, matId, ↓reduceDIte]
      exact h i
    · simp only [matInter, matId, dif_neg hii, zero_inter]

/-- **§2.217: entire = the row domains JOIN TO 1** (the "partition of 1" join half for maps):
    `M` is entire iff on each row the domains of the entries join to the identity.
    (`1 ∩ ∪_j M_ij M_ij° = ∪_j (1 ∩ M_ij M_ij°) = ∪_j dom M_ij` by distributivity.) -/
public theorem mat_entire_iff_dom_partition {X Y : MatObj 𝒜} (M : X ⟶ Y) :
    Entire (𝒜 := MatObj 𝒜) M ↔
      ∀ i : Fin X.n, finJoin (fun j => dom (M i j)) = Cat.id (X.objs i) := by
  rw [mat_entire_iff]
  refine forall_congr' (fun i => ⟨fun h => ?_, fun h => ?_⟩)
  · have h' : Cat.id (X.objs i) ∩ finJoin (fun j => M i j ≫ (M i j)°)
        = Cat.id (X.objs i) := h
    rw [inter_finJoin] at h'
    exact h'
  · have hmono : finJoin (fun j => dom (M i j)) ⊑ finJoin (fun j => M i j ≫ (M i j)°) :=
      finJoin_mono (fun j => inter_lb_right _ _)
    exact h ▸ hmono

/-- **§2.217: a matrix is SIMPLE iff each entry is simple and same-row cross terms vanish** —
    "R is simple iff `R_ij` is simple for each i, j and `R_ij° R_ij' = 0` for j ≠ j'". -/
public theorem mat_simple_iff {X Y : MatObj 𝒜} (M : X ⟶ Y) :
    Simple (𝒜 := MatObj 𝒜) M ↔
      (∀ (i : Fin X.n) (j : Fin Y.n), Simple (M i j)) ∧
      (∀ (i : Fin X.n) (j j' : Fin Y.n), j ≠ j' → (M i j)° ≫ M i j' = 𝟘) := by
  constructor
  · intro h
    have h' := matLe_iff.mp h
    refine ⟨fun i j => ?_, fun i j j' hne => ?_⟩
    · -- diagonal entry (j,j) of `M°≫M ⊑ 1`, restricted to the i-th summand.
      have hij : (M i j)° ≫ M i j ⊑ matId Y j j :=
        le_trans (show (fun i => (M i j)° ≫ M i j) i ⊑ finJoin (fun i => (M i j)° ≫ M i j) from le_listJoinD (List.mem_ofFn.mpr ⟨i, rfl⟩)) (h' j j)
      rwa [matId_diag] at hij
    · -- off-diagonal entry (j,j') forces every summand under `𝟘`.
      have hij : (M i j)° ≫ M i j' ⊑ matId Y j j' :=
        le_trans (show (fun i => (M i j)° ≫ M i j') i ⊑ finJoin (fun i => (M i j)° ≫ M i j') from le_listJoinD (List.mem_ofFn.mpr ⟨i, rfl⟩)) (h' j j')
      rw [matId_off hne] at hij
      exact le_antisymm hij (zero_le _)
  · rintro ⟨hsimp, hdisj⟩
    refine matLe_iff.mpr (fun j j' => ?_)
    by_cases hjj : j = j'
    · subst hjj
      have hle : finJoin (fun i => (M i j)° ≫ M i j) ⊑ Cat.id (Y.objs j) :=
        listJoinD_le (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hsimp i j)
      rwa [← matId_diag (X := Y) j] at hle
    · have hz : finJoin (fun i => (M i j)° ≫ M i j') = (𝟘 : Y.objs j ⟶ Y.objs j') :=
        finJoin_zero_all (fun i => hdisj i j j' hjj)
      have hle : finJoin (fun i => (M i j)° ≫ M i j') ⊑ matId Y j j' := by
        rw [hz]; exact zero_le _
      exact hle

/-- **§2.217: "Hence a matrix is simple iff each entry is simple and the domains of any two
    entries in the same row are disjoint."**  `mat_simple_iff` with the cross-term condition
    recast through `recip_comp_eq_zero_iff_dom_disjoint`. -/
public theorem mat_simple_iff_dom_disjoint {X Y : MatObj 𝒜} (M : X ⟶ Y) :
    Simple (𝒜 := MatObj 𝒜) M ↔
      (∀ (i : Fin X.n) (j : Fin Y.n), Simple (M i j)) ∧
      (∀ (i : Fin X.n) (j j' : Fin Y.n), j ≠ j' → dom (M i j) ∩ dom (M i j') = 𝟘) := by
  rw [mat_simple_iff]
  exact and_congr_right fun _ =>
    forall_congr' fun i => forall_congr' fun j => forall_congr' fun j' =>
      imp_congr_right fun _ => recip_comp_eq_zero_iff_dom_disjoint (M i j) (M i j')

/-- **§2.217: "It is a map iff each entry is simple and domains of the entries on any row
    form a partition of 1."**  ("Partition": the row domains join to `1`
    (`mat_entire_iff_dom_partition`) and are pairwise disjoint
    (`mat_simple_iff_dom_disjoint`).) -/
public theorem mat_map_iff {X Y : MatObj 𝒜} (M : X ⟶ Y) :
    Map (𝒜 := MatObj 𝒜) M ↔
      (∀ (i : Fin X.n) (j : Fin Y.n), Simple (M i j)) ∧
      (∀ i : Fin X.n, finJoin (fun j => dom (M i j)) = Cat.id (X.objs i)) ∧
      (∀ (i : Fin X.n) (j j' : Fin Y.n), j ≠ j' → dom (M i j) ∩ dom (M i j') = 𝟘) := by
  have hmap : Map (𝒜 := MatObj 𝒜) M ↔
      Entire (𝒜 := MatObj 𝒜) M ∧ Simple (𝒜 := MatObj 𝒜) M := Iff.rfl
  rw [hmap, mat_entire_iff_dom_partition, mat_simple_iff_dom_disjoint]
  exact ⟨fun ⟨hpart, hsimp, hdisj⟩ => ⟨hsimp, hpart, hdisj⟩,
         fun ⟨hsimp, hpart, hdisj⟩ => ⟨hpart, hsimp, hdisj⟩⟩

end MatCharacterizations

end Freyd.Alg.Mat

namespace Freyd

open Freyd.Alg Freyd.Alg.Mat

/-! ## §C  The singleton embedding `𝒜 ↪ Mat 𝒜` as a representation (§2.216/§2.217)

  "Define `A → A⁺` by sending α to ⟨α⟩.  It is a FULL AND FAITHFUL representation of
  distributive allegories, and A⁺ is positive."

  Packaged over a BARE `[DistributiveAllegory 𝒜]` (§2.218's `S2_21b` re-exports it in its
  tabular-unitary setting).  Beyond the `AllegoryFunctor` laws (`≫`, `id`, `°`, `∩` — `∪`,
  `𝟘`, `/` are `embed1_union`/`embed1_zero`/`embed1_div`), it is faithful, FULL, and
  order-reflecting, and carries the unit to the unit. -/

section MatEmbedRep

/-- **§2.216 — the singleton embedding `𝒜 ↪ Mat 𝒜` as an allegory functor** (`α ↦ ⟨α⟩`,
    `R ↦ embed1 R`), over a bare `[DistributiveAllegory 𝒜]`.  Hom laws are the `embed1_*`
    homomorphism lemmas (`Cat.id (unitObj a)` is `matId (unitObj a)` definitionally). -/
@[expose] public def matEmbed (𝒜 : Type u) [DistributiveAllegory.{u, v} 𝒜] :
    AllegoryFunctor 𝒜 (MatObj 𝒜) where
  obj := unitObj
  map := embed1
  map_id _ := embed1_id
  map_comp R S := embed1_comp R S
  map_recip R := embed1_recip R
  map_inter R S := embed1_inter R S

/-- `matEmbed` is FAITHFUL — `embed1` is injective (`embed1_injective`). -/
public theorem matEmbed_faithful {𝒜 : Type u} [DistributiveAllegory.{u, v} 𝒜] :
    (matEmbed 𝒜).Faithful :=
  fun _ _ h => embed1_injective h

/-- `matEmbed` is FULL — every `Mat 𝒜`-morphism between singleton objects is the 1×1 matrix
    of its unique entry ("full and faithful representation", §2.216). -/
theorem matEmbed_full {𝒜 : Type u} [DistributiveAllegory.{u, v} 𝒜] {a b : 𝒜}
    (N : (matEmbed 𝒜).obj a ⟶ (matEmbed 𝒜).obj b) :
    ∃ R : a ⟶ b, (matEmbed 𝒜).map R = N := by
  refine ⟨N ⟨0, Nat.zero_lt_one⟩ ⟨0, Nat.zero_lt_one⟩, funext fun i => funext fun j => ?_⟩
  have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero i
  have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero j
  subst hi; subst hj
  rfl

/-- `matEmbed` carries the UNIT of `𝒜` to the unit of `Mat 𝒜` (definitionally:
    `matUnitObj = unitObj λ`). -/
theorem matEmbed_unitObj {𝒜 : Type u} [UnitaryDistributiveAllegory.{u, v} 𝒜] :
    (matEmbed 𝒜).obj (UnitaryAllegory.unit_obj (𝒜 := 𝒜)) = matUnitObj :=
  rfl

/-- **§2.215/§2.216 bundled for the §2.218 pipeline**: `Mat 𝒜` of a tabular unitary
    DISTRIBUTIVE allegory is a tabular unitary POSITIVE allegory — exactly the hypothesis
    class consumed by `tabular_repr_in_power_of_sets` (`Freyd/S2_21b.lean`). -/
@[expose] public noncomputable def matTabularUnitaryPositive (𝒜 : Type u)
    [Alg.TabularUnitaryDistributiveAllegory.{u, u} 𝒜] :
    Alg.TabularUnitaryPositiveAllegory (MatObj 𝒜) :=
  -- the two §2.342 hypothesis classes of the matrix construction (single shared `Allegory`).
  letI : Alg.Mat.TabularDistributiveAllegory 𝒜 :=
    { (inferInstance : Alg.TabularAllegory 𝒜), (inferInstance : Alg.DistributiveAllegory 𝒜) with }
  letI : Alg.Mat.UnitaryDistributiveAllegory 𝒜 :=
    { (inferInstance : Alg.UnitaryAllegory 𝒜), (inferInstance : Alg.DistributiveAllegory 𝒜) with }
  { (instTabularAllegoryMat : Alg.TabularAllegory (MatObj 𝒜)),
    (instUnitaryAllegoryMat : Alg.UnitaryAllegory (MatObj 𝒜)),
    (instPositiveAllegoryMat : Alg.PositiveAllegory (MatObj 𝒜)) with }

end MatEmbedRep

/-! ## §D  Headline: a pre-logos may be faithfully represented in a positive pre-logos

  `S2_111_RelCat` builds the target `D = Map(Mat(Rel C))` with its positive-pre-logos
  structure (`s217PreLogos`) and the per-hom injection `embed217 : C ↪ D`
  (`embed217_faithful`).  Here we upgrade `embed217` to a FUNCTOR (`embed217_id`,
  `embed217_comp`, `embed217Functor`) and package Freyd's headline. -/

section S217Headline

variable {𝒞 : Type u} [Cat.{v} 𝒞] [PreLogos 𝒞]

/-- `embed217` preserves identities: both sides have `val = matId (unitObj ⟨a⟩)` (through
    `embedRel_id` and `embed1_id`), and `Map`-witnesses are proof-irrelevant. -/
public theorem embed217_id (a : 𝒞) :
    embed217 (Cat.id a)
      = @Cat.id (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))
          (embed217Obj a) := by
  apply Subtype.ext
  show embed1' (embedRel (Cat.id a)).val = _
  rw [show (embedRel (Cat.id a)).val
        = (@Cat.id (MapObj (RelObj 𝒞)) (mapCat (𝒜 := RelObj 𝒞)) ⟨a⟩).val
      from congrArg Subtype.val (embedRel_id a)]
  exact embed1_id

/-- `embed217` preserves composition: on `val` this is `embedRel_comp` (graph composition in
    `Map(Rel C)`) followed by `embed1_comp` (1×1 matrix composition). -/
public theorem embed217_comp {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c) :
    embed217 (f ≫ g)
      = @Cat.comp (MapObj (MatObj (RelObj 𝒞))) (mapCat (𝒜 := MatObj (RelObj 𝒞)))
          (embed217Obj a) (embed217Obj b) (embed217Obj c) (embed217 f) (embed217 g) := by
  apply Subtype.ext
  show embed1' (embedRel (f ≫ g)).val = _
  rw [show (embedRel (f ≫ g)).val
        = (embedRel f).val ≫ (embedRel g).val
      from congrArg Subtype.val (embedRel_comp f g)]
  exact embed1_comp (embedRel f).val (embedRel g).val

end S217Headline

section S217HeadlineSmall

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞]

/-- **§2.217 — the representation `C → Map(Mat(Rel C))` as a `Functor`** (small case, the one
    the §2.218 pipeline uses: all hom universes coincide).  Its `map` is `embed217`. -/
@[expose] public noncomputable def embed217Functor :
    @Functor 𝒞 (MapObj (MatObj (RelObj 𝒞))) _ (mapCat (𝒜 := MatObj (RelObj 𝒞))) :=
  -- explicit `@Functor.mk`, not `where`: structure-instance notation re-synthesizes the target
  -- `Cat` argument, and — `MapObj A` being an abbrev for `A` — lands on `instCatMatObj`
  -- instead of `mapCat` (the repo-standard `mapCat`-pinning gotcha).
  @Functor.mk 𝒞 (MapObj (MatObj (RelObj 𝒞))) _ (mapCat (𝒜 := MatObj (RelObj 𝒞))) embed217Obj
    (fun {_ _} f => embed217 f) embed217_id (fun f g => embed217_comp f g)

/-- **§2.217 HEADLINE — "A pre-logos may be faithfully represented in a positive
    pre-logos."**  For any pre-logos `C` (bare `[PreLogos 𝒞]` — `C` need NOT be positive),
    the target `D = Map(Mat(Rel C))` — the category of maps of the positive reflection
    `Mat(Rel C)` of the allegory of relations — is a positive pre-logos (`s217PreLogos`),
    and the graph-of-1×1-matrices FUNCTOR `embed217Functor : C → D` is faithful. -/
public theorem prelogos_repr_in_positive_prelogos :
    Nonempty (@PositivePreLogos (MapObj (MatObj (RelObj 𝒞)))
        (mapCat (𝒜 := MatObj (RelObj 𝒞)))) ∧
    ∀ {a b : 𝒞} {f g : a ⟶ b},
      @Functor.map 𝒞 (MapObj (MatObj (RelObj 𝒞))) _
          (mapCat (𝒜 := MatObj (RelObj 𝒞))) (embed217Functor (𝒞 := 𝒞)) a b f =
        @Functor.map 𝒞 (MapObj (MatObj (RelObj 𝒞))) _
          (mapCat (𝒜 := MatObj (RelObj 𝒞))) (embed217Functor (𝒞 := 𝒞)) a b g → f = g :=
  ⟨⟨s217PreLogos⟩, fun h => embed217_faithful h⟩

end S217HeadlineSmall

end Freyd

