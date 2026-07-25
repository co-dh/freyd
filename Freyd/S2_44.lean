import Freyd.S2_40

universe u

/-
  Freyd & Scedrov, *Categories and Allegories*.

  §2.441  The pre-positive / well-joined / straight-join / simple-factor equivalence,
          assembled as a multi-way result from one-directional lemmas.
  §2.416  The EPIC half of the progenitor `∋`-construction: a straight map factor is an
          ISO (the `1 ⊑ h°h` half that needs the progenitor's separating property), and
          the resulting thickness / representation conclusion.

  Everything here lives over a `DivisionAllegory` (the book's forward directions of §2.441
  hold "in any distributive/division allegory", and §2.416's maximality step is pure
  straight/simple calculus), reusing the existing `Straight`, `Simple`, `Map`,
  `rightInvertible_straight`, `straight_of_comp_straight`, `straight_map_monic`,
  `straight_cancel_simple`, `map_comp`, `le_dom_comp` from `Freyd.S2_*`.
-/



namespace Freyd.Alg

variable {𝒜 : Type u}

/-! ## §2.441  The four equivalent conditions (forward directions)

  Freyd states, for power allegories, that the following are equivalent:

    (1) PRE-POSITIVE: every pair `(a,b)` embeds into a common `γ` via monic maps `f`,`g`
        with disjoint images (`ff° = 1`, `gg° = 1`, `fg° = 0`).
    (2) WELL-JOINED: every pair `(a,b)` has a common `γ` of which both are RETRACTS
        (maps `f : a → γ`, `g : b → γ` each with a right inverse — the figure's two
        triangles `a → γ → a = 1`, `b → γ → b = 1`; the free power allegory is well-joined
        "via its singleton maps and their reciprocals", i.e. `f' = f°`).
    (3) STRAIGHT-JOIN: every pair `(a,b)` has a common `γ` reached by STRAIGHT `S₁`, `S₂`.
    (4) CONNECTED and every morphism factors as `S ≫ F` with `S` straight, `F` simple.

  Book proof of the forward arrows:
    (1)⟹(2) trivial (the monic equation `ff° = 1` makes `f°` a right inverse of `f`);
    (2)⟹(3) right-invertibility implies straight [2.355];
    (1)⟹(4) connectivity via `f ≫ g°`, factorization `S = f ∪ R≫g`, `F = g°` [§2.441 (1)⟹(4)].

  The reverse arrows all funnel through (3)⟹(1), which needs the membership/division
  `1/∋` construction (the `ℓ,μ : [γ] → [[γ]]` of §2.441's BECAUSE) — see the blocked-direction
  note on `prePositive_wellJoined_straightJoin_tfae`. -/

/-- (1) PRE-POSITIVE (§2.441): every pair embeds into a common object via monic maps with
    disjoint images. -/
def PrePositiveCond (𝒜 : Type u) [DivisionAllegory 𝒜] : Prop :=
  ∀ (a b : 𝒜), ∃ (γ : 𝒜) (f : a ⟶ γ) (g : b ⟶ γ),
    Map f ∧ Map g ∧
    f ≫ f° = Cat.id a ∧ g ≫ g° = Cat.id b ∧ f ≫ g° = (𝟘 : a ⟶ b)

/-- (2) WELL-JOINED (§2.441, the figure's retract form): every pair of objects are both
    retracts of a common object, i.e. there are maps `f : a → γ`, `g : b → γ` each having a
    right inverse (`f ≫ f' = 1`, `g ≫ g' = 1`). -/
def WellJoinedCond (𝒜 : Type u) [DivisionAllegory 𝒜] : Prop :=
  ∀ (a b : 𝒜), ∃ (γ : 𝒜) (f : a ⟶ γ) (g : b ⟶ γ),
    Map f ∧ Map g ∧
    (∃ f' : γ ⟶ a, f ≫ f' = Cat.id a) ∧ (∃ g' : γ ⟶ b, g ≫ g' = Cat.id b)

/-- (3) STRAIGHT-JOIN (§2.441): every pair has a common target reached by straight morphisms. -/
def StraightJoinCond (𝒜 : Type u) [DivisionAllegory 𝒜] : Prop :=
  ∀ (a b : 𝒜), ∃ (γ : 𝒜) (S₁ : a ⟶ γ) (S₂ : b ⟶ γ), Straight S₁ ∧ Straight S₂

/-- (4) CONNECTED-SIMPLE-FACTOR (§2.441): the allegory is connected (every pair of objects
    has a morphism) and every morphism factors as a straight one followed by a simple one. -/
def ConnectedSimpleFactorCond (𝒜 : Type u) [DivisionAllegory 𝒜] : Prop :=
  (∀ (a b : 𝒜), Nonempty (a ⟶ b)) ∧
  (∀ (a b : 𝒜) (R : a ⟶ b), ∃ (c : 𝒜) (S : a ⟶ c) (F : c ⟶ b),
    Straight S ∧ Simple F ∧ R = S ≫ F)

variable [DivisionAllegory 𝒜]

/-- §2.441 (1)⟹(2): pre-positive implies well-joined.  The monic equation `f ≫ f° = 1`
    exhibits `f°` as a right inverse of `f`, so each object is a retract of the common `γ`. -/
theorem prePositive_to_wellJoined (hPP : PrePositiveCond 𝒜) : WellJoinedCond 𝒜 := by
  intro a b
  obtain ⟨γ, f, g, hf, hg, hff, hgg, _⟩ := hPP a b
  exact ⟨γ, f, g, hf, hg, ⟨f°, hff⟩, ⟨g°, hgg⟩⟩

/-- §2.441 (2)⟹(3): well-joined implies straight-join.  A right-invertible morphism is
    straight [§2.355 `rightInvertible_straight`], so the retraction maps `f`, `g` are straight. -/
theorem wellJoined_to_straightJoin (hWJ : WellJoinedCond 𝒜) : StraightJoinCond 𝒜 := by
  intro a b
  obtain ⟨γ, f, g, _hf, _hg, ⟨f', hf'⟩, ⟨g', hg'⟩⟩ := hWJ a b
  exact ⟨γ, f, g, rightInvertible_straight hf', rightInvertible_straight hg'⟩

/-- §2.441 (1)⟹(3): pre-positive implies straight-join (composing the two arrows above). -/
theorem prePositive_to_straightJoin (hPP : PrePositiveCond 𝒜) : StraightJoinCond 𝒜 :=
  wellJoined_to_straightJoin (prePositive_to_wellJoined hPP)

/-- §2.441 (1)⟹(4): pre-positive implies connected-with-simple-factorization.

    CONNECTED: `f ≫ g° : a → b` is a morphism for every pair.
    FACTORIZATION (Freyd §2.441 (1)⟹(4)): given `R`, take `S = f ∪ R≫g` (straight via the
    right inverse `f°`, using disjointness `g ≫ f° = 0`) and `F = g°` (simple); then
    `S ≫ F = (f ∪ R≫g) ≫ g° = f≫g° ∪ R≫(g≫g°) = 0 ∪ R = R`. -/
theorem prePositive_to_connectedSimpleFactor (hPP : PrePositiveCond 𝒜) :
    ConnectedSimpleFactorCond 𝒜 := by
  refine ⟨fun a b => ?_, fun a b R => ?_⟩
  · obtain ⟨_γ, f, g, _hf, _hg, _, _, _⟩ := hPP a b
    exact ⟨f ≫ g°⟩
  · obtain ⟨γ, f, g, _hf, _hg, hff, hgg, hfg⟩ := hPP a b
    -- Disjointness reciprocated: g ≫ f° = (f ≫ g°)° = 0° = 0.
    have hgf : g ≫ f° = (𝟘 : b ⟶ a) := by
      have : (g ≫ f°) = (f ≫ g°)° := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [this, hfg, recip_zero]
    refine ⟨γ, f ∪ R ≫ g, g°, ?_, ?_, ?_⟩
    · -- Straight via right inverse f°: (f ∪ R≫g) ≫ f° = f≫f° ∪ R≫(g≫f°) = 1 ∪ 0 = 1.
      refine rightInvertible_straight (T := f°) ?_
      rw [union_comp_distrib, Cat.assoc, hgf, DistributiveAllegory.comp_zero, union_zero, hff]
    · -- Simple F = g°: (g°)° ≫ g° = g ≫ g° = 1 ⊑ 1.
      dsimp [Simple]; rw [Allegory.recip_recip, hgg]; exact le_refl _
    · -- S ≫ F = (f ∪ R≫g) ≫ g° = f≫g° ∪ R≫(g≫g°) = 0 ∪ R = R.
      rw [union_comp_distrib, hfg, Cat.assoc, hgg, Cat.comp_id,
        DistributiveAllegory.union_comm, union_zero]

/-- §2.441 multi-way equivalence, assembled.  Given the one book direction that genuinely
    needs the `1/∋` membership construction — `hSJtoPP : (3)⟹(1)` (Freyd §2.441's BECAUSE:
    `Λ(S₁), Λ(S₂)` monic into `[γ]`, then the explicit `ℓ,μ : [γ] → [[γ]]` with
    `ℓℓ° = 1 = μμ°`, `ℓμ° = 0` built from `1/∋` and `Λ(0) ∩ Λ(1) = 0`) — conditions
    (1) PRE-POSITIVE, (2) WELL-JOINED, (3) STRAIGHT-JOIN are pairwise equivalent.

    The forward arrows `(1)⟹(2)⟹(3)` are proven unconditionally above; only the single
    reverse hypothesis `hSJtoPP` is assumed, exactly as Freyd's proof closes the cycle. -/
theorem prePositive_wellJoined_straightJoin_tfae
    (hSJtoPP : StraightJoinCond 𝒜 → PrePositiveCond 𝒜) :
    (PrePositiveCond 𝒜 ↔ WellJoinedCond 𝒜) ∧
    (WellJoinedCond 𝒜 ↔ StraightJoinCond 𝒜) :=
  ⟨⟨prePositive_to_wellJoined,
    fun hWJ => hSJtoPP (wellJoined_to_straightJoin hWJ)⟩,
   ⟨wellJoined_to_straightJoin,
    fun hSJ => prePositive_to_wellJoined (hSJtoPP hSJ)⟩⟩

/-! ## §2.416  The progenitor `∋`-construction: the EPIC half (maximality is an iso)

  Freyd's §2.416 builds `∋` as the straight-and-thick factor `S` of the obvious morphism
  `T : Σ_I γ → α` out of a copower of the progenitor `γ`.  `S` is straight, and "maximal" —
  if `S = h ≫ S'` with `S'` straight and `h` a map then `h` is an ISO.

  The MONIC half `h ≫ h° = 1` is `straight_map_monic` (`h` straight via `S = h≫S'` straight,
  §2.355).  The EPIC half `h° ≫ h = 1` is the progenitor-dependent one: Freyd tests
  `F h° h = F` for every simple `F` out of the progenitor `γ` and invokes `γ`'s separating
  property.  We capture exactly that property as `Separates γ`. -/

/-- A PROGENITOR / separator (§1.966 separating property, as used in §2.416): morphisms with
    the same source and target are equal as soon as they agree after precomposition with every
    simple morphism out of `γ`.  (In `Rel(Set)` with `γ` a singleton-supporting generator this
    is "two relations agree iff they agree on every element".) -/
def Separates (γ : 𝒜) : Prop :=
  ∀ ⦃a b : 𝒜⦄ (R R' : a ⟶ b),
    (∀ (F : γ ⟶ a), Simple F → F ≫ R = F ≫ R') → R = R'

/-- §2.416 maximality (the iso, including the EPIC half).  If `S = h ≫ S'` with `S`, `S'`
    straight, `h` a map, and `S` is THICK from the progenitor (`∀ R : γ → α` there is a map
    `f` with `R = f ≫ S`), then `h` is an isomorphism: `h ≫ h° = 1` and `h° ≫ h = 1`.

    `h ≫ h° = 1`: `h` is straight (§2.355) and a map, so monic (`straight_map_monic`), and
    entire, giving `1 ⊑ h≫h° ⊑ 1`.
    `h° ≫ h = 1` (EPIC, the progenitor half): for every simple `F : γ → Q`, thickness gives a
    map `f` with `F ≫ S' = f ≫ S = (f≫h) ≫ S'`; `f≫h` is a map, so by the straight
    cancellation §2.352 (`straight_cancel_simple`) `dom F ≫ (f≫h) = dom(f≫h) ≫ F = F`; then
    `F ≫ h° ≫ h = dom F ≫ f ≫ (h ≫ h° ≫ h) = dom F ≫ f ≫ h = F` using the allegory identity
    `h ≫ h° ≫ h = h`.  Since `F ≫ (h°≫h) = F = F ≫ 1` for all such `F`, `Separates γ` forces
    `h° ≫ h = 1`. -/
theorem progenitor_straight_factor_iso (γ : 𝒜) (hSep : Separates γ)
    {P Q α : 𝒜} {S : P ⟶ α} {S' : Q ⟶ α} {h : P ⟶ Q}
    (hSstr : Straight S) (hS'str : Straight S') (hh : Map h) (hSeq : S = h ≫ S')
    (hSthick : ∀ (R : γ ⟶ α), ∃ (f : γ ⟶ P), Map f ∧ R = f ≫ S) :
    h ≫ h° = Cat.id P ∧ h° ≫ h = Cat.id Q := by
  -- `h` is straight (§2.355, from `S = h≫S'` straight) and a map.
  have hstr : Straight h := straight_of_comp_straight (S := h) (R := S') (hSeq ▸ hSstr)
  have hmono : h ≫ h° ⊑ Cat.id P := straight_map_monic hh hstr
  -- MONIC half `h ≫ h° = 1` (`hmono` plus entireness of `h`).
  have hHr : h ≫ h° = Cat.id P := by
    refine le_antisymm hmono ?_
    have he : Cat.id P ∩ h ≫ h° = Cat.id P := hh.1   -- Entire h : dom h = 1
    exact he ▸ inter_lb_right (Cat.id P) (h ≫ h°)
  -- The allegory identity `h ≫ h° ≫ h = h`.
  have key : h ≫ (h° ≫ h) = h := by
    have hle : (h ≫ h°) ≫ h ⊑ h := by
      have hh1 := comp_mono_right hmono h; rwa [Cat.id_comp] at hh1
    have hge : h ⊑ (h ≫ h°) ≫ h :=
      le_trans (le_dom_comp h) (comp_mono_right (inter_lb_right (Cat.id P) (h ≫ h°)) h)
    have h0 : (h ≫ h°) ≫ h = h := le_antisymm hle hge
    exact (Cat.assoc h h° h).symm.trans h0
  -- EPIC half `h° ≫ h = 1` via separation by simple morphisms from `γ`.
  have hrH : h° ≫ h = Cat.id Q := by
    refine hSep (h° ≫ h) (Cat.id Q) (fun F hF => ?_)
    -- `F ≫ S'` factors through `S` (thickness): `F ≫ S' = f ≫ S` with `f` a map.
    obtain ⟨f, hf, hfR⟩ := hSthick (F ≫ S')
    have hfh : F ≫ S' = (f ≫ h) ≫ S' := by rw [hfR, hSeq, ← Cat.assoc]
    have hfhmap : Map (f ≫ h) := map_comp hf hh
    -- §2.352 straight cancellation: `dom F ≫ (f≫h) = dom(f≫h) ≫ F`, and `dom(f≫h) = 1`.
    have hcancel := straight_cancel_simple hS'str hF hfhmap.2 hfh
    have hdfh : dom (f ≫ h) = Cat.id γ := hfhmap.1
    rw [hdfh, Cat.id_comp] at hcancel    -- hcancel : dom F ≫ (f ≫ h) = F
    -- `F ≫ (h° ≫ h) = F`.
    have step : F ≫ (h° ≫ h) = F := by
      have e1 : F ≫ (h° ≫ h) = (dom F ≫ (f ≫ h)) ≫ (h° ≫ h) := by rw [hcancel]
      rw [e1, Cat.assoc (dom F) (f ≫ h) (h° ≫ h), Cat.assoc f h (h° ≫ h), key]
      exact hcancel
    exact step.trans (Cat.comp_id F).symm
  exact ⟨hHr, hrH⟩

/-- §2.416 (the representation / thickness conclusion).  Under the progenitor separation
    `Separates γ` and the EFFECTIVE straightening of the cotuple `(S;R)` (Freyd §2.354:
    for each `R : β → α` the cotuple of `S` and `R` straightens, restricting to
    `S = h ≫ S'` and `R = h' ≫ S'` with `h, h'` maps and `S'` straight — this is the
    coproduct/effectiveness content of §2.416), the straight thick `S` is THICK for ALL
    targets: every `R : β → α` factors as a map followed by `S`.

    Proof: `h` is an iso by `progenitor_straight_factor_iso`, so `h°` is a map and
    `h° ≫ S = S'`; then `R = h' ≫ S' = (h' ≫ h°) ≫ S` with `h' ≫ h°` a map. -/
theorem progenitor_straight_thick (γ : 𝒜) (hSep : Separates γ)
    {P α : 𝒜} {S : P ⟶ α} (hSstr : Straight S)
    (hSthick : ∀ (R : γ ⟶ α), ∃ (f : γ ⟶ P), Map f ∧ R = f ≫ S)
    (hCotuple : ∀ {β : 𝒜} (R : β ⟶ α),
      ∃ (Q : 𝒜) (S' : Q ⟶ α) (h : P ⟶ Q) (h' : β ⟶ Q),
        Straight S' ∧ Map h ∧ Map h' ∧ S = h ≫ S' ∧ R = h' ≫ S')
    {β : 𝒜} (R : β ⟶ α) :
    ∃ (m : β ⟶ P), Map m ∧ R = m ≫ S := by
  obtain ⟨Q, S', h, h', hS'str, hh, hh', hSeq, hReq⟩ := hCotuple R
  obtain ⟨hHr, hrH⟩ :=
    progenitor_straight_factor_iso γ hSep hSstr hS'str hh hSeq hSthick
  -- `h°` is a map (since `h` is an iso).
  have hrmap : Map h° := by
    refine ⟨?_, ?_⟩
    · dsimp only [Entire, dom]; rw [Allegory.recip_recip, hrH, Allegory.inter_idem]
    · show (h°)° ≫ h° ⊑ Cat.id P
      rw [Allegory.recip_recip, hHr]; exact le_refl _
  -- `h° ≫ S = S'`, hence `R = (h' ≫ h°) ≫ S`.
  have hrS : h° ≫ S = S' := by rw [hSeq, ← Cat.assoc, hrH, Cat.id_comp]
  exact ⟨h' ≫ h°, map_comp hh' hrmap, by rw [hReq, ← hrS, Cat.assoc]⟩

/-- §2.416: the cotuple hypothesis `hCotuple` of `progenitor_straight_thick` is DISCHARGED in an
    EFFECTIVE division allegory with binary coproducts — exactly Freyd's §2.416 coproduct/
    effectiveness content, now derived rather than assumed.  Given a binary coproduct `Q = P ⊕ β`
    the cotuple `(S;R) : Q → α` is the coproduct mediator (`coproduct_five_eqs_to_universal`);
    straightening it via §2.354 (`straight_factorization`) gives `(S;R) = k ≫ S'` with `k` a map
    and `S'` straight, and restricting `k` to the injections `u₁, u₂` gives `h = u₁ ≫ k`,
    `h' = u₂ ≫ k` with `S = h ≫ S'`, `R = h' ≫ S'`.  (Stated with a fresh carrier `ℬ` so the
    section's ambient `[DivisionAllegory 𝒜]` is not also bound — no instance diamond.) -/
theorem hCotuple_of_coproduct {ℬ : Type u} [EffectiveDivisionAllegory ℬ]
    {P α : ℬ} (S : P ⟶ α) {β : ℬ} (R : β ⟶ α) {Q : ℬ} (cp : Coproduct Q P β) :
    ∃ (Q' : ℬ) (S' : Q' ⟶ α) (h : P ⟶ Q') (h' : β ⟶ Q'),
      Straight S' ∧ Map h ∧ Map h' ∧ S = h ≫ S' ∧ R = h' ≫ S' := by
  -- The cotuple mediator `M = (S;R) : Q → α`.
  obtain ⟨M, hM1, hM2, _⟩ := coproduct_five_eqs_to_universal cp α S R
  -- The injections are maps: entire from `uᵢuᵢ° = 1`, simple from `⋃ uᵢ°uᵢ = 1`.
  have hu1simp : cp.u₁° ≫ cp.u₁ ⊑ Cat.id Q := by
    have h := le_union_left (cp.u₁° ≫ cp.u₁) (cp.u₂° ≫ cp.u₂); rwa [cp.recip_union_eq_id] at h
  have hu2simp : cp.u₂° ≫ cp.u₂ ⊑ Cat.id Q := by
    have h := le_union_right (cp.u₁° ≫ cp.u₁) (cp.u₂° ≫ cp.u₂); rwa [cp.recip_union_eq_id] at h
  have hu1 : Map cp.u₁ :=
    ⟨by show dom cp.u₁ = Cat.id P; dsimp [dom]; rw [cp.u₁_self_comp_recip, Allegory.inter_idem], hu1simp⟩
  have hu2 : Map cp.u₂ :=
    ⟨by show dom cp.u₂ = Cat.id β; dsimp [dom]; rw [cp.u₂_self_comp_recip, Allegory.inter_idem], hu2simp⟩
  -- Straighten `M` (§2.354): `M = k ≫ (k° ≫ M)`, `k` a map, `k° ≫ M` straight.
  obtain ⟨c, k, hk, _, hS'str, hMeq⟩ := straight_factorization M
  refine ⟨c, k° ≫ M, cp.u₁ ≫ k, cp.u₂ ≫ k, hS'str, map_comp hu1 hk, map_comp hu2 hk, ?_, ?_⟩
  · show S = (cp.u₁ ≫ k) ≫ (k° ≫ M); rw [Cat.assoc, ← hMeq, hM1]
  · show R = (cp.u₂ ≫ k) ≫ (k° ≫ M); rw [Cat.assoc, ← hMeq, hM2]

/-- **§2.416 (cotuple hypothesis discharged).**  In an EFFECTIVE division allegory with binary
    coproducts, a straight `S : P → α` that is thick against a progenitor `γ` (`Separates γ`,
    `hSthick`) is THICK for ALL targets — Freyd's §2.416 — with NO `hCotuple` hypothesis: it is
    discharged by `hCotuple_of_coproduct` from the binary coproducts `Q = P ⊕ b`. -/
theorem progenitor_straight_thick_of_coproduct {ℬ : Type u} [EffectiveDivisionAllegory ℬ]
    (γ : ℬ) (hSep : Separates γ) {P α : ℬ} {S : P ⟶ α} (hSstr : Straight S)
    (hSthick : ∀ (R : γ ⟶ α), ∃ (f : γ ⟶ P), Map f ∧ R = f ≫ S)
    (hcoprod : ∀ (b : ℬ), ∃ (Q : ℬ), Nonempty (Coproduct Q P b))
    {β : ℬ} (R : β ⟶ α) :
    ∃ (m : β ⟶ P), Map m ∧ R = m ≫ S := by
  refine progenitor_straight_thick γ hSep hSstr hSthick ?_ R
  intro b R'
  obtain ⟨Q, ⟨cp⟩⟩ := hcoprod b
  exact hCotuple_of_coproduct S R' cp

/-! ## §2.441  The disjointness crux `Λ(0) ∩ Λ(1) = 0`

  Freyd's (3)⟹(1) reduces the disjointness `ℓϰ° = 0` of the two `[γ] → [[γ]]` maps to
  `Λ(0) ∩ Λ(1) = 0`, where `Λ = A` is the §2.41 transpose.  This is the genuine
  mathematical core of that step; we prove it here.  (The remaining ingredients of the
  full (3)⟹(1) — that `Λ(S)` is a SPLIT-MONIC map, `Λ(S)Λ(S)° = 1` — need `Λ(S)` ENTIRE,
  which in the repo's box-guarded power allegory holds only under the §2.41 box condition
  `codBox S = codBox ∋` (`A_is_map`); so the full assembly is box-gated, exactly as §2.537.) -/

section PowerDisjoint
variable {ℬ : Type u} [PowerAllegory ℬ] {a : ℬ}

/-- If `W ⊑ Λ(0)` and `W ⊑ Λ(1)` then `W = 0`.  `WW° ⊑ Λ(0)Λ(1)° ⊑ (0/∋)∋ ⊑ 0`
    (`Λ(0) ⊑ 0/∋`, `Λ(1)° ⊑ ∋/1 = ∋`), so `dom W ⊑ 0` and `W ⊑ (dom W)W ⊑ 0`. -/
theorem le_zero_of_le_A_zero_A_one (W : a ⟶ PowerAllegory.powerObj a)
    (h0 : W ⊑ A (𝟘 : a ⟶ a)) (h1 : W ⊑ A (Cat.id a)) :
    W = (𝟘 : a ⟶ PowerAllegory.powerObj a) := by
  apply le_antisymm _ (zero_le _)
  have hA0 : A (𝟘 : a ⟶ a) ⊑ (𝟘 : a ⟶ a) / PowerAllegory.eps a := inter_lb_left _ _
  have hA1r : (A (Cat.id a))° ⊑ PowerAllegory.eps a := by
    show (symmDiv (Cat.id a) (PowerAllegory.eps a))° ⊑ _
    rw [symmDiv, Allegory.recip_inter, Allegory.recip_recip, div_one]
    exact inter_lb_right _ _
  have hWW : W ≫ W° ⊑ (𝟘 : a ⟶ a) := by
    have h1' : W ≫ W° ⊑ A (𝟘 : a ⟶ a) ≫ (A (Cat.id a))° :=
      le_trans (comp_mono_right h0 (W°)) (comp_mono_left _ (recip_mono h1))
    have h2 : A (𝟘 : a ⟶ a) ≫ (A (Cat.id a))°
        ⊑ ((𝟘 : a ⟶ a) / PowerAllegory.eps a) ≫ PowerAllegory.eps a :=
      le_trans (comp_mono_right hA0 _) (comp_mono_left _ hA1r)
    exact le_trans h1' (le_trans h2 (DivisionAllegory.div_comp_le _ _))
  have hdom : dom W ⊑ (𝟘 : a ⟶ a) := by
    show Cat.id a ∩ W ≫ W° ⊑ (𝟘 : a ⟶ a); exact le_trans (inter_lb_right _ _) hWW
  refine le_trans (le_dom_comp W) (le_trans (comp_mono_right hdom W) ?_)
  rw [DistributiveAllegory.zero_comp]; exact le_refl _

/-- **§2.441 disjointness crux**: `Λ(0) ∩ Λ(1) = 0` (`A 𝟘 ∩ A 1 = 𝟘`).  The empty-transpose
    and the singleton-transpose are disjoint — the heart of (3)⟹(1)'s `ℓϰ° = 0`. -/
theorem A_zero_inter_A_one :
    A (𝟘 : a ⟶ a) ∩ A (Cat.id a) = (𝟘 : a ⟶ PowerAllegory.powerObj a) :=
  le_zero_of_le_A_zero_A_one _ (inter_lb_left _ _) (inter_lb_right _ _)

end PowerDisjoint

end Freyd.Alg
