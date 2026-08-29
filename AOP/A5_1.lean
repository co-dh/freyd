/-
  Bird & de Moor, *Algebra of Programming*, §5.1 Relators (book pp. 111–113).

  A RELATOR is a monotonic functor between allegories; between tabular allegories this is
  the same as a converse-preserving functor (Theorem 5.1).  Relators are the datatype-formers
  of the relational calculus: §5.2–§5.5 build relational products, coproducts, the power
  relator, and relational catamorphisms over them.

  Weaker than `AllegoryFunctor` (S2_147), which also preserves `∩`; a relator preserves `∩`
  only on coreflexives (Ex 5.2).

  Contents: `Relator` structure + identity/composition; Lemma 5.1 (relators preserve maps and
  their converses), Theorem 5.1(a) (relator ⟹ converse-preserving, over tabular source),
  Corollary 5.1 (relators agreeing on maps agree), Ex 5.2 (meets of coreflexives), Ex 5.5 (dom).

  Theorem 5.1(b) — the converse direction (converse-preserving, out of a tabular source, ⟹
  monotone) — is DROPPED; see the "Theorem 5.1(b) DROPPED" section near the end of the file
  for the precise blocker (transporting `m`'s simplicity across a not-yet-known-monotone map
  is circular).  Nothing else in this file, or so far outside it, needs that direction.
-/
module

public import Freyd.S2_10
public import AOP.A4_2

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Freyd.Alg

/-- A RELATOR (B&dM §5.1 p. 111): a monotonic functor between allegories. -/
public structure Relator (𝒜 : Type u₁) (ℬ : Type u₂) [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    extends Freyd.Functor 𝒜 ℬ where
  /-- MONOTONICITY — the defining extra over a plain functor. -/
  map_mono : ∀ {a b : 𝒜} {R S : a ⟶ b}, R ⊑ S → map R ⊑ map S

/-- A relator PRESERVES CONVERSE when `F(R°) = (FR)°`.  Automatic over a tabular source
    (Theorem 5.1); carried as a hypothesis where tabularity is not otherwise needed. -/
@[expose] public def Relator.PreservesRecip {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F : Relator 𝒜 ℬ) : Prop :=
  ∀ {a b : 𝒜} (R : a ⟶ b), F.map R° = (F.map R)°

/-- The identity relator. -/
@[expose] public def Relator.idRelator (𝒜 : Type u₁) [Allegory.{v₁} 𝒜] : Relator 𝒜 𝒜 where
  obj := id
  map := id
  map_id _ := rfl
  map_comp _ _ := rfl
  map_mono h := h

/-- Composition of relators (diagram order: first `F`, then `G`). -/
@[expose] public def Relator.comp {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] [Allegory.{v₃} 𝒞]
    (F : Relator 𝒜 ℬ) (G : Relator ℬ 𝒞) : Relator 𝒜 𝒞 where
  obj := G.obj ∘ F.obj
  map R := G.map (F.map R)
  map_id a := by simp [F.map_id, G.map_id]
  map_comp R S := by simp [F.map_comp, G.map_comp]
  map_mono h := G.map_mono (F.map_mono h)

/-- The CONSTANT relator `X ↦ b`, `R ↦ 𝟙 b`.  With `Relator.prod` it expresses `A×−`
    as `Relator.prod (Relator.const A) (Relator.idRelator 𝒜)`. -/
@[expose] public def Relator.const {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (b : ℬ) : Relator 𝒜 ℬ where
  obj _ := b
  map _ := 𝟙 b
  map_id _ := rfl
  map_comp _ _ := (Cat.id_comp (𝟙 b)).symm
  map_mono _ := le_refl _

-- Lives in §5.1, not with §5.7's theorems about it: it mentions nothing but two relators and a
-- family of arrows, and §5.2's `outr` example already needs it.
/-- **B&dM 5.13** (LAX NATURAL TRANSFORMATION, mirrored to diagram order): `φ : G ⟶ F`,
    a family `φ a : G.obj a ⟶ F.obj a`, is LAX NATURAL when `G.map R ≫ φ b ⊑ φ a ≫ F.map R`
    for every `R : a ⟶ b`. -/
@[expose] public def LaxNatural {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F G : Relator 𝒜 ℬ) (φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a) : Prop :=
  ∀ {a b : 𝒜} (R : a ⟶ b), G.map R ≫ φ b ⊑ φ a ≫ F.map R

/-- A relator carries a LAX SQUARE to a lax square: `Ta ≫ X ⊑ X' ≫ Tb` gives
    `F(Ta) ≫ F(X) ⊑ F(X') ≫ F(Tb)`.  Just `map_mono` read through `map_comp` on both sides.
    The two sides carry DIFFERENT arrows `X`, `X'` — at `X' = X` and endo `Ta`, `Tb` this is
    monotonicity of `F(X)`, and at `Ta, Tb := G(R), F(R)`, `X, X' := φ b, φ a` it is a relator
    applied on the OUTSIDE of a lax natural `φ`, one `R` at a time. -/
public theorem Relator.map_slides {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) {a₁ a₂ b₁ b₂ : 𝒜}
    {Ta : a₁ ⟶ a₂} {Tb : b₁ ⟶ b₂} {X : a₂ ⟶ b₂} {X' : a₁ ⟶ b₁} (h : Ta ≫ X ⊑ X' ≫ Tb) :
    F.map Ta ≫ F.map X ⊑ F.map X' ≫ F.map Tb := by
  have := F.map_mono h
  rwa [F.map_comp, F.map_comp] at this

/-! ## Lemma 5.1  Relators preserve maps and their converses (B&dM p. 112)

  A relator need not preserve `°` on a general relation, but it always preserves it — and
  preserves mapness — on the maps of `𝒜`.  Both halves come from one application of
  Prop 4.1 (`recip_of_comp_id`, A4_2) to `R := F.map f`, `S := F.map f°`; the two hypotheses
  of Prop 4.1 are the images, under `F.map_mono`, of `f`'s entireness and simplicity.

  Stated first over raw relator DATA (`obj`, `map`, `map_id`, `map_comp`, `map_mono`) rather
  than a bundled `Relator`, so Corollary 5.1 can reuse it after `cases`-ing a `Relator` into
  its fields (a bundled `F : Relator 𝒜 ℬ` can't be reconstructed once `F.obj` has been
  unified with another relator's object map by `subst`). -/

private theorem relator_map_recip_map_aux {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (obj : 𝒜 → ℬ)
    (map : {a b : 𝒜} → (a ⟶ b) → (obj a ⟶ obj b))
    (map_id : ∀ (a : 𝒜), map (Cat.id a) = Cat.id (obj a))
    (map_comp : ∀ {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c), map (R ≫ S) = map R ≫ map S)
    (map_mono : ∀ {a b : 𝒜} {R S : a ⟶ b}, R ⊑ S → map R ⊑ map S)
    {a b : 𝒜} {f : a ⟶ b} (hf : Map f) :
    map f° = (map f)° ∧ Map (map f) := by
  have h1 : Cat.id (obj a) ⊑ map f ≫ map f° := by
    simpa [map_id, map_comp] using map_mono (entire_id_le hf.1)
  have h2 : map f° ≫ map f ⊑ Cat.id (obj b) := by
    simpa [map_id, map_comp] using map_mono hf.2
  exact recip_of_comp_id h1 h2

/-- **Lemma 5.1**, first half (B&dM p. 112): a relator sends the converse of a map to the
    converse of its image. -/
public theorem Relator.map_recip_map {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) {a b : 𝒜} {f : a ⟶ b} (hf : Map f) :
    F.map f° = (F.map f)° :=
  (relator_map_recip_map_aux F.obj F.map F.map_id F.map_comp F.map_mono hf).1

/-- **Lemma 5.1**, second half (B&dM p. 112): a relator sends a map to a map. -/
public theorem Relator.map_is_map {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) {a b : 𝒜} {f : a ⟶ b} (hf : Map f) :
    Map (F.map f) :=
  (relator_map_recip_map_aux F.obj F.map F.map_id F.map_comp F.map_mono hf).2

/-! ## Theorem 5.1(a)  Over a tabular source, every relator preserves converse (B&dM p. 112)

  Every `R : a ⟶ b` tabulates as `f° ≫ g` for maps `f, g` from a common apex; Lemma 5.1 turns
  `F`'s action on `f, g` into converse-preserving pieces, and reassembling them on both sides
  of `F(R°) = (F R)°` matches term-by-term. -/

theorem Relator.preservesRecip_of_tabular {𝒜 : Type u₁} {ℬ : Type u₂}
    [TabularAllegory 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) : F.PreservesRecip := by
  intro a b R
  obtain ⟨c, f, g, hf_map, hg_map, hR, _⟩ := TabularAllegory.tabular R
  have hRrecip : R° = g° ≫ f := by rw [hR, Allegory.recip_comp, Allegory.recip_recip]
  have hFmapR : F.map R = (F.map f)° ≫ F.map g := by
    rw [hR, F.map_comp, F.map_recip_map hf_map]
  have hFmapRrecip : F.map R° = (F.map g)° ≫ F.map f := by
    rw [hRrecip, F.map_comp, F.map_recip_map hg_map]
  rw [hFmapRrecip, hFmapR, Allegory.recip_comp, Allegory.recip_recip]

/-! ## Corollary 5.1  Relators agreeing on maps agree everywhere (B&dM p. 112)

  Any `R` tabulates as `f°≫g` for maps `f, g`; `Theorem 5.1(a)`'s computation of `F.map R`
  only ever touches `F.map f`, `F.map g`, so two relators that agree on all maps already
  agree on `R`.  Stated with `F.obj = G.obj` (rather than reconstructing a bundled `Relator`
  from raw fields) so that, after destructuring `F` and `subst`, the two hom-maps land in the
  same type `G.obj a ⟶ G.obj b` and the conclusion becomes an ordinary `Eq` wrapped in
  `HEq` (`heq_of_eq`). -/

theorem Relator.map_eq_of_eq_on_maps {𝒜 : Type u₁} {ℬ : Type u₂}
    [TabularAllegory 𝒜] [Allegory.{v₂} ℬ] {F G : Relator 𝒜 ℬ}
    (hobj : ∀ a, F.obj a = G.obj a)
    (hmaps : ∀ {a b : 𝒜} (f : a ⟶ b), Map f → HEq (F.map f) (G.map f))
    {a b : 𝒜} (R : a ⟶ b) : HEq (F.map R) (G.map R) := by
  have hobjeq : F.obj = G.obj := funext hobj
  obtain ⟨c, f, g, hf_map, hg_map, hR, _⟩ := TabularAllegory.tabular R
  obtain ⟨⟨obj, map, map_id, map_comp⟩, map_mono⟩ := F
  dsimp only at hobjeq hmaps ⊢
  subst hobjeq
  apply heq_of_eq
  show map R = G.map R
  have hff : map f = G.map f := eq_of_heq (hmaps f hf_map)
  have hgg : map g = G.map g := eq_of_heq (hmaps g hg_map)
  have hFrecip : map f° = (map f)° :=
    (relator_map_recip_map_aux G.obj map map_id map_comp map_mono hf_map).1
  have hFR : map R = (map f)° ≫ map g := by rw [hR, map_comp, hFrecip]
  have hGR : G.map R = (G.map f)° ≫ G.map g := by
    rw [hR, G.map_comp, Relator.map_recip_map G hf_map]
  rw [hFR, hGR, hff, hgg]

/-! ## Ex 5.2  A relator preserves meets of coreflexives (B&dM p. 113)

  A relator need not preserve `∩` in general — only monotonicity is assumed — but on
  coreflexives `∩` collapses to `≫` (`coreflexive_comp_eq_inter`, S2_1 §2.121), where
  `map_comp` applies directly. -/

/-- The one half of meet-preservation that monotonicity alone buys, for arbitrary `R S`:
    `R ∩ S` is below both, so its image is below both images, hence below their meet.
    The reverse inclusion FAILS in general — the power relator `P` is a counterexample:
    with `R = {(a₁,b₁),(a₂,b₂)}`, `S = {(a₁,b₂),(a₂,b₁)}`, the pair `({a₁,a₂},{b₁,b₂})` is
    in `P R ∩ P S` while `R ∩ S = ∅` makes it absent from `P (R ∩ S)`.  Equality needs
    either coreflexivity (`map_inter_coreflexive` below) or the stronger
    `AllegoryFunctor.map_inter` (S2_147). -/
theorem Relator.map_inter_le {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) {a b : 𝒜} (R S : a ⟶ b) :
    F.map (R ∩ S) ⊑ F.map R ∩ F.map S :=
  le_inter (F.map_mono (inter_lb_left R S)) (F.map_mono (inter_lb_right R S))

theorem Relator.map_inter_coreflexive {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ)
    {a : 𝒜} {X Y : a ⟶ a} (hX : Coreflexive X) (hY : Coreflexive Y) :
    F.map (X ∩ Y) = F.map X ∩ F.map Y := by
  have hFX : Coreflexive (F.map X) := by
    have := F.map_mono hX; rwa [F.map_id] at this
  have hFY : Coreflexive (F.map Y) := by
    have := F.map_mono hY; rwa [F.map_id] at this
  rw [← coreflexive_comp_eq_inter hX hY, F.map_comp, coreflexive_comp_eq_inter hFX hFY]

/-! ## Ex 5.5  A relator commutes with `dom`, given it preserves converse (B&dM p. 113)

  `⊑`: `dom R` is below both `id` and `R≫R°`; take images under `F.map` and combine with
  `le_inter`.  `⊒`: `dom_UP` (A4_2) reduces `dom(F.map R) ⊑ F.map(dom R)` to
  `F.map R ⊑ F.map(dom R)≫F.map R`, which is the image of `R ⊑ dom R≫R` (`le_dom_comp`,
  S2_1) under `F.map`. -/

theorem Relator.map_dom {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) (hc : F.PreservesRecip)
    {a b : 𝒜} (R : a ⟶ b) : F.map (dom R) = dom (F.map R) := by
  have hcoref : Coreflexive (F.map (dom R)) := by
    have := F.map_mono (dom_coreflexive R); rwa [F.map_id] at this
  apply le_antisymm
  · have h2 : F.map (dom R) ⊑ F.map R ≫ (F.map R)° := by
      have := F.map_mono (inter_lb_right (Cat.id a) (R ≫ R°))
      rwa [F.map_comp, hc R] at this
    exact le_inter hcoref h2
  · rw [dom_UP hcoref]
    have := F.map_mono (le_dom_comp R)
    rwa [F.map_comp] at this

/-- Ex 5.5, tabular corollary: over a tabular source, `Theorem 5.1(a)` discharges the
    converse-preservation hypothesis automatically. -/
theorem Relator.map_dom_of_tabular {𝒜 : Type u₁} {ℬ : Type u₂}
    [TabularAllegory 𝒜] [Allegory.{v₂} ℬ] (F : Relator 𝒜 ℬ) {a b : 𝒜} (R : a ⟶ b) :
    F.map (dom R) = dom (F.map R) :=
  Relator.map_dom F (Relator.preservesRecip_of_tabular F) R

/-! ## Theorem 5.1(b)  DROPPED — converse-preserving does not obviously give monotone
    (B&dM p. 112)

  The book's other half of Theorem 5.1: a functor between allegories that preserves `id`,
  `≫` and `°`, out of a *tabular* source, is automatically monotone (hence a relator).
  Attempted and dropped after a real derivation attempt; here is the precise blocker.

  Tabulate `R = h°≫k` (apex `c`) and `S = f°≫g` (apex `d`).  `R ⊑ S` gives `h°≫k ⊑ f°≫g`, so
  `tabulation_UP_forward` (applied to `(f,g)`, with `x := h`, `y := k`) yields a MAP
  `m : c ⟶ d` with `m≫f = h`, `m≫g = k`.  Chasing the two tabulation identities
  (`h≫h°∩k≫k° = id_c`, `f≫f°∩g≫g° = id_d`) gives the EQUATION `m≫m° = id_c` (`⊑` from the
  joint-monic chase, `⊒` from `Entire m`) — this much needs no monotonicity, only equational
  allegory reasoning.

  Now `map R = map(h°≫k) = (map h)°≫map k = (map f)°≫(map m)°≫map m≫map g` (via `hrec` and
  `map_comp`, applied to `h = m≫f` and `k = m≫g` — again purely equational), while
  `map S = (map f)°≫map g`.  So `map R ⊑ map S` reduces to
  `(map m)°≫map m ⊑ Cat.id (obj d)`.

  This is where the argument breaks: `Simple m` (part of `Map m`) gives `m°≫m ⊑ id_d` IN
  `𝒜`, but transporting an INEQUALITY across `map` to get `(map m)°≫map m ⊑ id` in `ℬ` is
  exactly an instance of monotonicity — the very property being proved, so invoking it here
  is circular.  The equational route (`m°≫m = id_d` outright, which WOULD transport for
  free via `map_comp`/`hrec`/`congrArg`, no monotonicity needed) fails because nothing
  forces `m` to be co-entire: `R ⊑ S` can be a strict inequality, in which case `S`'s apex
  `d` is not exactly covered by `m`'s image and `m` is a genuinely proper (non-invertible)
  map.

  No non-circular derivation was found in the time available.  Only Theorem 5.1(a)
  (`Relator.preservesRecip_of_tabular`) is formalized; nothing later in this file, and
  nothing so far outside it, depends on the converse direction. -/

end Freyd.Alg
