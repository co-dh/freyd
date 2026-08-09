module

public import Freyd.S2_10
public import Freyd.S2_20
public import Freyd.S2_30
public import Freyd.S2_40

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.422.

  HEADLINE (§2.422, division allegory):
    For any equivalence relation `E`, `E = E / E` (right division of `E` by itself).

  COROLLARY (§2.421 + §2.422, power allegory):
    In a power allegory every equivalence relation has the form `f ≫ f°` for a map `f`
    (already proven upstream as `equivRel_eq_map_comp_recip`); hence if coreflexives split
    then every equivalence relation is *effective* — it splits as `h ≫ h° = E`, `h° ≫ h = 1`.

  Builds on:
    * `le_div_iff`, `div_self_comp_le`, `one_le_div_self`  (S2_3, §2.31/2.314)
    * `EquivalenceRel`, `Reflexive`, `Symmetric`, `Transitive`, `Map`, `Simple`, `Coreflexive`
      (S2_1, §2.12)
    * `equivRel_idem`, `equivRel_eq_map_comp_recip`  (S2_4, §2.422)
-/



namespace Freyd.Alg

/-! ## §2.422  `E = E / E` for an equivalence relation -/

/-- **§2.422**: in any division allegory, every equivalence relation `E` satisfies `E = E / E`
    (right division of `E` by itself).

    * `E ⊑ E/E`: by `le_div_iff` this reduces to `E ≫ E ⊑ E`, i.e. transitivity.
    * `E/E ⊑ E`: `E/E = (E/E) ≫ 1 ⊑ (E/E) ≫ E ⊑ E`, using reflexivity `1 ⊑ E`
      and the division counit `(E/E) ≫ E ⊑ E`. -/
theorem equivRel_eq_div_self {𝒜 : Type u} [DivisionAllegory 𝒜] {a : 𝒜} {E : a ⟶ a}
    (hE : EquivalenceRel E) : E = E / E := by
  apply le_antisymm
  · -- E ⊑ E/E  ⟺  E ≫ E ⊑ E  (Transitive E)
    exact (le_div_iff E E E).mpr hE.2.2
  · -- E/E ⊑ E:  E/E = (E/E) ≫ 1 ⊑ (E/E) ≫ E ⊑ E
    have h1 : E / E ⊑ (E / E) ≫ E := by
      have h := comp_mono_left (E / E) hE.1        -- (E/E) ≫ 1 ⊑ (E/E) ≫ E
      rwa [Cat.comp_id] at h
    exact le_trans h1 (div_self_comp_le E)

/-! ## §2.421 + §2.422  Effectiveness in a power allegory

  In a power allegory, `equivRel_eq_map_comp_recip` already gives `E = f ≫ f°` with `f = A(E)`
  a map.  We upgrade this to *effectiveness* once coreflexives split.

  The coreflexive `f° ≫ f` (which `⊑ 1` because `f` is simple) splits as `g° ≫ g = f° ≫ f`,
  `g ≫ g° = 1`.  Setting `h = f ≫ g°` gives a map with `h ≫ h° = E`, `h° ≫ h = 1`:

      h ≫ h° = f (g° g) f° = f (f° f) f° = (f f°)(f f°) = E·E = E,
      h° ≫ h = g (f° f) g° = g (g° g) g° = (g g°)(g g°) = 1·1 = 1. -/

/-- **§2.421/§2.422 corollary**: in a power allegory in which coreflexives split, every
    equivalence relation `E` is effective — there is a map `h` with `h ≫ h° = E` and
    `h° ≫ h = 1`.  The "coreflexives split" hypothesis is taken in the exact shape produced by
    `coreflexive_splits` (S2_2): a coreflexive `A` splits as `g° ≫ g = A`, `g ≫ g° = 1`. -/
theorem equivRel_effective_of_coreflexives_split {𝒜 : Type u} [PowerAllegory 𝒜] {a : 𝒜}
    (E : a ⟶ a) (hE : EquivalenceRel E) (hbox : codBox E = codBox (∋ a))
    (hsplit : ∀ {x : 𝒜} {A : x ⟶ x}, Coreflexive A →
      ∃ (c : 𝒜) (g : c ⟶ x), Map g ∧ g° ≫ g = A ∧ g ≫ g° = Cat.id c) :
    ∃ (c : 𝒜) (h : a ⟶ c), Map h ∧ h ≫ h° = E ∧ h° ≫ h = Cat.id c := by
  -- §2.421/§2.422: E = f ≫ f° with f = A(E) a map.
  obtain ⟨f, hf, hEeq⟩ := equivRel_eq_map_comp_recip E hE hbox
  have hffE : f ≫ f° = E := hEeq.symm
  -- f° ≫ f is coreflexive (f is simple); split it.
  have hcor : Coreflexive (f° ≫ f) := hf.2
  obtain ⟨d, g, _, hgg, hgg1⟩ := hsplit hcor   -- hgg : g° ≫ g = f° ≫ f,  hgg1 : g ≫ g° = 1_d
  -- The candidate splitting map h = f ≫ g°.
  have hrecip : (f ≫ g°)° = g ≫ f° := by rw [Allegory.recip_comp, Allegory.recip_recip]
  -- h ≫ h° = E
  have hHHr : (f ≫ g°) ≫ (f ≫ g°)° = E := by
    rw [hrecip]
    have hstep : (f ≫ g°) ≫ (g ≫ f°) = (f ≫ f°) ≫ (f ≫ f°) := by
      have a1 : (f ≫ g°) ≫ (g ≫ f°) = f ≫ (g° ≫ g) ≫ f° := by simp only [Cat.assoc]
      have a2 : f ≫ (f° ≫ f) ≫ f° = (f ≫ f°) ≫ (f ≫ f°) := by simp only [Cat.assoc]
      rw [a1, hgg, a2]
    rw [hstep, hffE, equivRel_idem hE]
  -- h° ≫ h = 1_d
  have hHrH : (f ≫ g°)° ≫ (f ≫ g°) = Cat.id d := by
    rw [hrecip]
    have hstep : (g ≫ f°) ≫ (f ≫ g°) = (g ≫ g°) ≫ (g ≫ g°) := by
      have a1 : (g ≫ f°) ≫ (f ≫ g°) = g ≫ (f° ≫ f) ≫ g° := by simp only [Cat.assoc]
      have a2 : g ≫ (g° ≫ g) ≫ g° = (g ≫ g°) ≫ (g ≫ g°) := by simp only [Cat.assoc]
      rw [a1, ← hgg, a2]
    rw [hstep, hgg1, Cat.id_comp]
  refine ⟨d, f ≫ g°, ⟨?_, ?_⟩, hHHr, hHrH⟩
  · -- Entire (f ≫ g°): dom = id_a, i.e. id_a ⊑ (f≫g°)(f≫g°)° = E, by reflexivity.
    show Cat.id a ∩ (f ≫ g°) ≫ (f ≫ g°)° = Cat.id a
    have hle : Cat.id a ⊑ (f ≫ g°) ≫ (f ≫ g°)° := by rw [hHHr]; exact hE.1
    dsimp [le] at hle; exact hle
  · -- Simple (f ≫ g°): (f≫g°)°(f≫g°) = 1_d ⊑ 1_d.
    show (f ≫ g°)° ≫ (f ≫ g°) ⊑ Cat.id d
    rw [hHrH]; exact le_refl _

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.423.

  §2.423  If A is a connected power allegory in which coreflexives split then it has
          a unit.

  BECAUSE (Freyd): given an object α define the maximal endomorphism M = 1_α / 0_α of
  (α,α).  M is reflexive, symmetric and idempotent (an equivalence relation), so in a
  power allegory in which coreflexives split it splits — there is a map f : α → β with
  f f° = M and f° f = 1_β.  Its target β is a PARTIAL UNIT: for every R : β → β,

        R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β

  (the middle step because f R f° ⊑ M is maximal).  Connectivity (which in any allegory
  implies strong connectivity) gives every object a map to α; composing with f gives every
  object a map to β, so β is a UNIT.

  Steps 1 and 2 (`maxEndo_max`, `target_split_partialUnit`) are UNCONDITIONAL pure algebra
  over a `DivisionAllegory`.  Step 3 (`connected_power_coreflexivesSplit_has_unit`) is
  HYPOTHESIS-GATED: it takes strong connectivity (`hconn`) and the splitting of equivalence
  relations (`hsplit`) as named hypotheses.  `hsplit` is exactly Freyd's
  "coreflexives split" combined with §2.422 (in a power allegory every equivalence relation
  is of the form `f f°`); §2.422 is not yet formalised here, so it is left as a hypothesis —
  it coincides with the field `EffectiveAllegory.split_symmetric_idempotent`.
-/



namespace Freyd.Alg

/-! ## §2.423  The maximal endomorphism `M = 1_α / 0_α` -/

section Division
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- §2.423: the MAXIMAL endomorphism `M = 1_α / 0_α` of `(α,α)`. -/
def maxEndo (α : 𝒜) : α ⟶ α := Cat.id α / 𝟘

/-- §2.423: `M = 1_α / 0_α` is maximal in `(α,α)`: every `R : α → α` satisfies `R ⊑ M`.
    `R ⊑ 1/0 ↔ R≫0 ⊑ 1`, and `R≫0 = 0 ⊑ 1` holds always. -/
theorem maxEndo_max {α : 𝒜} (R : α ⟶ α) : R ⊑ maxEndo α := by
  apply (le_div_iff R (Cat.id α) (𝟘 : α ⟶ α)).mpr
  rw [DistributiveAllegory.comp_zero]
  exact zero_le _

/-- §2.423 (the partial-unit step, pure algebra).  If `f : α → β` splits the maximal
    endomorphism `M = 1_α/0_α` — `f f° = M` and `f° f = 1_β` — then its target `β` is a
    PARTIAL UNIT: every `R : β → β` satisfies `R ⊑ 1_β`.

    Book chain: `R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β`, using `f R f° ⊑ M`
    (maximality) for the inequality and `M = f f°`, `f° f = 1_β` for the equalities. -/
theorem target_split_partialUnit {α β : 𝒜} (f : α ⟶ β)
    (hff : f ≫ f° = maxEndo α) (hf'f : f° ≫ f = Cat.id β) :
    PartialUnit β := by
  intro R
  -- f R f° ⊑ M  (every endo of α is below the maximal one)
  have hmax : (f ≫ R ≫ f°) ⊑ maxEndo α := maxEndo_max _
  -- f° (f R f°) f ⊑ f° M f
  have h1 : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ f° ≫ maxEndo α ≫ f :=
    comp_mono_left f° (comp_mono_right hmax f)
  -- f° M f = f° (f f°) f = (f° f)(f° f) = 1_β
  have h2 : f° ≫ maxEndo α ≫ f = Cat.id β := by
    rw [← hff, Cat.assoc, hf'f, Cat.comp_id, hf'f]
  -- f° (f R f°) f = (f° f) R (f° f) = R
  have hXeq : f° ≫ (f ≫ R ≫ f°) ≫ f = R := by
    rw [Cat.assoc f (R ≫ f°) f, ← Cat.assoc f° f ((R ≫ f°) ≫ f), hf'f, Cat.id_comp,
        Cat.assoc R f° f, hf'f, Cat.comp_id]
  have hle : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ Cat.id β := h2 ▸ h1
  rwa [hXeq] at hle

end Division

/-! ## §2.423  Strong connectivity -/

/-- §2.423: an allegory is STRONGLY CONNECTED if every object has a MAP to every object.
    Freyd: connectivity in any allegory implies strong connectivity, so this is the working
    form of "connected". -/
@[expose] public def StronglyConnectedAllegory (𝒜 : Type u) [Allegory 𝒜] : Prop :=
  ∀ (a b : 𝒜), ∃ (g : a ⟶ b), Map g

/-! ## §2.423  A connected power allegory in which coreflexives split has a unit -/

section Power
variable {𝒜 : Type u} [PowerAllegory 𝒜]

/-- **§2.423**: a CONNECTED POWER ALLEGORY in which coreflexives split has a UNIT.

    HYPOTHESIS-GATED on:
    * `hconn` — strong connectivity (Freyd's connectivity implies it);
    * `hsplit` — every equivalence relation splits with an entire leg.  In a power allegory
      this is Freyd's "coreflexives split" together with §2.422 (every equivalence relation
      is `f f°`); it is precisely `EffectiveAllegory.split_symmetric_idempotent`.

    Construction: split the maximal endomorphism `M = 1_α/0_α` (an equivalence relation) to
    get a map `f : α → π` with `f f° = M`, `f° f = 1_π`; then `π` is a partial unit
    (`target_split_partialUnit`) and connectivity gives every object a map to `π`. -/
theorem connected_power_coreflexivesSplit_has_unit
    (hconn : StronglyConnectedAllegory 𝒜)
    (hsplit : ∀ {a : 𝒜} (E : a ⟶ a), Reflexive E → Symmetric E → E ≫ E = E →
       ∃ (b : 𝒜) (g : a ⟶ b), Map g ∧ g ≫ g° = E ∧ g° ≫ g = Cat.id b)
    (α : 𝒜) :
    ∃ (π : 𝒜), IsUnit π := by
  -- M = 1_α/0_α is reflexive, symmetric, idempotent (an equivalence relation).
  have hRefl : Reflexive (maxEndo α) := maxEndo_max (Cat.id α)
  have hSym : Symmetric (maxEndo α) := maxEndo_max ((maxEndo α)°)
  have hIdem : (maxEndo α) ≫ (maxEndo α) = maxEndo α :=
    reflexive_transitive_idempotent hRefl (maxEndo_max _)
  -- Split it: f : α → π with f f° = M, f° f = 1_π.
  obtain ⟨π, f, hf, hff, hf'f⟩ := hsplit (maxEndo α) hRefl hSym hIdem
  -- π is a partial unit, and every object has a map to π (connectivity ≫ f).
  refine ⟨π, target_split_partialUnit f hff hf'f, fun a => ?_⟩
  obtain ⟨g, hg⟩ := hconn a α
  exact ⟨g ≫ f, (map_comp hg hf).1⟩

end Power

end Freyd.Alg
