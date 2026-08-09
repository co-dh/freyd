/-
  Bird & de Moor, *Algebra of Programming* §4.3  Tabular allegories.

  This file adds only the facts B&dM §4.3 states that Freyd's own development
  (Freyd/S2_1.lean §2.14-§2.15) does not already cover: the unit-is-terminal-in-Map
  property and its converse (p.94-95), and the three tabulation-leg exercises
  4.21-4.23 relating simplicity/entirety/mapness of `R` to properties of its
  tabulating legs.

  Out of scope: B&dM p.95's Horn-sentence meta-theorem that unitary tabular
  allegories are exactly the allegories representable as Rel(C) for a regular
  category C.  This is a full representation theorem, not a single lemma; Freyd's
  own version is tracked (unproved) as §2.148/§2.154 in S2_1.lean.
-/

module

public import Freyd.S2_10
public import AOP.A4_2  -- entire_id_le

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## The unit is terminal among maps (B&dM p.94) -/

/-- **B&dM p.94** (generalized to any partial unit, not just the chosen one of a
    `UnitaryAllegory`): two maps into a partial unit `t` are equal — `t` is terminal in
    the subcategory of maps.  `g = 1≫g ⊑ (f f°)≫g = f≫(f°≫g) ⊑ f≫1 = f` [`Entire f`,
    `PartialUnit t`], giving `g ⊑ f`; `map_order_discrete` (§2.133) upgrades `⊑` to `=`. -/
theorem maps_to_partial_unit_unique {a t : 𝒜} (ht : PartialUnit t) {f g : a ⟶ t}
    (hf : Map f) (hg : Map g) : f = g := by
  have hf_ent : Cat.id a ⊑ f ≫ f° := entire_id_le hf.1
  have h1 : f° ≫ g ⊑ Cat.id t := ht (f° ≫ g)
  have hge : g ⊑ f := by
    have step1 : g ⊑ (f ≫ f°) ≫ g := by
      have h := comp_mono_right hf_ent g
      rwa [Cat.id_comp] at h
    have step2 : (f ≫ f°) ≫ g ⊑ f := by
      rw [Cat.assoc]
      have h := comp_mono_left f h1
      rwa [Cat.comp_id] at h
    exact le_trans step1 step2
  exact (map_order_discrete hg hf hge).symm

/-- **B&dM p.94** (Π): reciprocating a cospan of maps into a common apex `t` swaps the
    legs — `(p_a·p_b°)° = p_b·p_a°`. -/
theorem unit_top_recip {a b t : 𝒜} (p_a : a ⟶ t) (p_b : b ⟶ t) :
    (p_a ≫ p_b°)° = p_b ≫ p_a° := by
  rw [Allegory.recip_comp, Allegory.recip_recip]

/-- **B&dM p.94**: naturality of the terminal cone into a partial unit `t` — composing a
    map `f : a → b` with the projection `p_b : b → t` recovers the (unique) projection
    `p_a : a → t`.  Used later for products in `Map(𝒜)`. -/
theorem map_comp_proj {a b t : 𝒜} (ht : PartialUnit t) {f : a ⟶ b} {p_a : a ⟶ t} {p_b : b ⟶ t}
    (hf : Map f) (hp_a : Map p_a) (hp_b : Map p_b) : f ≫ p_b = p_a :=
  maps_to_partial_unit_unique ht (map_comp hf hp_b) hp_a

section UnitTerminal

variable {𝒜 : Type u} [UnitaryAllegory 𝒜]

/-- **B&dM p.94**: the unit is terminal among maps: any two maps into the chosen unit of
    a unitary allegory agree.  Corollary of `maps_to_partial_unit_unique`. -/
theorem maps_to_unit_unique {a : 𝒜} {f g : a ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜)}
    (hf : Map f) (hg : Map g) : f = g :=
  maps_to_partial_unit_unique (UnitaryAllegory.unit_prop (𝒜 := 𝒜)).1 hf hg

end UnitTerminal

/-! ## Converse: a terminal object in Map is a unit (B&dM p.95) -/

section TerminalUnit

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-- **B&dM p.95**: in a tabular allegory, an object `t` that is terminal in the
    subcategory of maps (every object maps to it, and any two maps to it agree) is a
    unit.  Book proof: given `R : t → t`, tabulate it by `(f,g)`; `f,g` are both maps
    `apex → t` so `f = g` by the hypothesis; the tabulation identity then collapses to
    `g≫g° = 1`, and `R = f°≫g = g°≫g ⊑ 1` is exactly `Simple g`. -/
theorem unit_of_terminal_in_maps (t : 𝒜)
    (hex : ∀ a : 𝒜, ∃ f : a ⟶ t, Map f)
    (huniq : ∀ {a : 𝒜} (f g : a ⟶ t), Map f → Map g → f = g) :
    IsUnit t := by
  refine ⟨fun R => ?_, fun a => ?_⟩
  · obtain ⟨c, f, g, hf, hg, hRfg, _⟩ := TabularAllegory.tabular R
    have hfg : f = g := huniq f g hf hg
    rw [hRfg, hfg]; exact hg.2
  · obtain ⟨f, hf⟩ := hex a
    exact ⟨f, hf.1⟩

end TerminalUnit

/-! ## Tabulation-leg exercises (B&dM Ex 4.21-4.23)

  For `Tabulates f g R` with `f : c → a`, `g : c → b`, `R : a → b`. -/

/-- **B&dM Ex 4.21**: if `R` is simple, its `a`-side tabulating leg `f` is monic (in fact
    `f≫f° = 1`, i.e. `f°` splits `f` on the nose).  Chain: `f° ⊑ R≫g°` and `f ⊑ g≫R°`
    (both from `Entire g`); combining and using `Simple R` gives `f≫f° ⊑ g≫g°`; then
    `f≫f° = f≫f°∩g≫g° = 1` by the tabulation identity. -/
theorem tabulates_simple_monic {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (hR : Simple R) : f ≫ f° = Cat.id c := by
  obtain ⟨_, hg, hReq, htab⟩ := ht
  have hg_ent : Cat.id c ⊑ g ≫ g° := entire_id_le hg.1
  have h_fo_le : f° ⊑ R ≫ g° := by
    calc f° = f° ≫ Cat.id c := (Cat.comp_id f°).symm
      _ ⊑ f° ≫ (g ≫ g°) := comp_mono_left f° hg_ent
      _ = R ≫ g° := by rw [← Cat.assoc, ← hReq]
  have h_f_le : f ⊑ g ≫ R° := by
    have hRo : g° ≫ f = R° := by rw [hReq, Allegory.recip_comp, Allegory.recip_recip]
    calc f = Cat.id c ≫ f := (Cat.id_comp f).symm
      _ ⊑ (g ≫ g°) ≫ f := comp_mono_right hg_ent f
      _ = g ≫ (g° ≫ f) := Cat.assoc g g° f
      _ = g ≫ R° := by rw [hRo]
  have h_ff_le : f ≫ f° ⊑ g ≫ g° := by
    have step1 : f ≫ f° ⊑ (g ≫ R°) ≫ (R ≫ g°) :=
      le_trans (comp_mono_right h_f_le f°) (comp_mono_left (g ≫ R°) h_fo_le)
    have step2 : (g ≫ R°) ≫ (R ≫ g°) = g ≫ (R° ≫ R) ≫ g° := by simp [Cat.assoc]
    rw [step2] at step1
    have step3 : g ≫ (R° ≫ R) ≫ g° ⊑ g ≫ Cat.id b ≫ g° :=
      comp_mono_left g (comp_mono_right hR g°)
    have step4 := le_trans step1 step3
    rwa [Cat.id_comp] at step4
  calc f ≫ f° = (f ≫ f°) ∩ (g ≫ g°) := (inter_eq_left h_ff_le).symm
    _ = Cat.id c := htab

/-- **B&dM Ex 4.22**: if `R` is entire, its `a`-side tabulating leg `f` is a cover (in
    fact `f°≫f = 1`).  `⊑` is `Simple f`; `⊒` follows from `Entire R` via the modular law
    applied to `X≫f ∩ 1` with `X := f°≫(g≫g°)` (so `X≫f = R≫R°`). -/
theorem tabulates_entire_cover {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (hR : Entire R) : f° ≫ f = Cat.id a := by
  obtain ⟨hf, _, hReq, _⟩ := ht
  apply le_antisymm hf.2
  have hRRo : R ≫ R° = (f° ≫ (g ≫ g°)) ≫ f := by
    rw [hReq, Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  have h_id_le : Cat.id a ⊑ (f° ≫ (g ≫ g°)) ≫ f := by rw [← hRRo]; exact entire_id_le hR
  have h_mod := modular_le (f° ≫ (g ≫ g°)) f (Cat.id a)
  rw [Cat.id_comp] at h_mod
  have heq : ((f° ≫ (g ≫ g°)) ≫ f) ∩ Cat.id a = Cat.id a := by
    rw [Allegory.inter_comm]; exact h_id_le
  rw [heq] at h_mod
  exact le_trans h_mod (comp_mono_right (inter_lb_right _ _) f)

/-- **B&dM Ex 4.23**: if `R` is a map, its `a`-side tabulating leg `f` is an isomorphism
    (with inverse `f°`).  Immediate from Ex 4.21 (`Simple R`) and Ex 4.22 (`Entire R`). -/
theorem tabulates_map_iso {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (hR : Map R) : Freyd.IsIso f :=
  ⟨f°, tabulates_simple_monic ht hR.2, tabulates_entire_cover ht hR.1⟩

end Freyd.Alg
