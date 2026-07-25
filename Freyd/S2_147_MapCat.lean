/-
  Freyd & Scedrov, *Categories and Allegories* §2.147  The category of maps Map(𝒜).

  §2.14   CATEGORY OF MAPS Map(𝒜): objects of 𝒜; morphisms a ⟶ b = maps of 𝒜.
  §2.147  If 𝒜 is a TABULAR allegory then Map(𝒜) has finite limits.
          Freyd's constructive recipes:
            • pullback of f, g : a → c   = tabulation of f ≫ g°
            • equalizer of f, g : a → b  = tabulation of dom (f ∩ g)
            • image of f : a → b         = tabulation of dom (f°)
            • g is a cover iff 1 ⊑ g° ≫ g (i.e. g° is entire)

  **Proved in this file** (all Sorry-free):
  (A) Cat instance on MapObj 𝒜  (§2.14).
  (B) Helper lemmas: dom R ⊑ dom R ≫ R; dom(f∩g) ≫ f = f ∩ g for Map f.
  (C) Pullback cone equation π₁° ≫ f = π₂° ≫ g  (§2.147).
  (D) Equalizer cone equation e° ≫ f = e° ≫ g  (§2.147).
  (E) Cover characterization: g is a cover iff Entire g°  (§2.147).
  (F) §2.143 mediating map is entire + simple (building blocks for UMP).
  (G) §2.143 forward UMP (in `S2_1.lean`; no `Map(π°)` hypotheses — source-apex).
  (H) Pullback UMP in Map(𝒜)  (§2.147).
  (I) Equalizer UMP in Map(𝒜)  (§2.147).

  **Source-apex convention** (legs FROM the apex: π₁ : p→a, π₂ : p→b, R = π₁°≫π₂):
  the §2.143 forward direction's mediating map needs NO `Map(π°)` hypothesis — the legs
  are already maps the right way, and the old `Map(π₁°)` blocker is gone.  The §2.143
  universal property (`tabulation_UP_forward`/`tabulation_UP_unique`) lives in `S2_1.lean`.

  **§2.148** (Sorry-free):
  (J) `tab_round_trip_rel`: Ψ∘Φ = id — from a tabulation (f,g) of R, f°≫g = R.
  (K) `span_self_tabulates`: a jointly-monic span (f,g) in Map(𝒜) self-tabulates f°≫g.
  (L) `tab_iso_unique_exists`: two tabulations of R are related by a UNIQUE isomorphism
      (now UNCONDITIONAL — §2.144 via `tabulation_unique_iso`; no `Map(f°)` needed).
  The allegory equivalence `RelMap 𝒜 ≅ 𝒜` is packaged below (`relMap_allegoryEquiv`).
-/

import Freyd.S2_01
import Freyd.S2_03
import Freyd.S2_16b
import Freyd.S1_60
import Freyd.S1_62
import Freyd.S1_64

universe v u

open Freyd
open Freyd.Alg

namespace Freyd.Alg

/-! ## §2.14  The category of maps Map(𝒜) -/

/-- Objects of Map(𝒜) coincide with objects of 𝒜.
    An `abbrev` alias (not `def`) so Lean transparently unfolds it when
    constructing the Cat instance; a `def` would cause typeclass look-ups to
    fail when Lean's unifier encounters `MapObj 𝒜` vs `𝒜`. -/
abbrev MapObj (𝒜 : Type u) : Type u := 𝒜

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ### Helper order lemmas -/

/-- dom(f ∩ g) ≫ f = f ∩ g  for any Map f. -/
theorem dom_inter_comp {a b : 𝒜} {f g : a ⟶ b} (hf : Map f) : dom (f ∩ g) ≫ f = f ∩ g := by
  apply le_antisymm
  · have hf_le : dom (f ∩ g) ≫ f ⊑ f := by
      have := comp_mono_right (dom_coreflexive (f ∩ g)) f; rwa [Cat.id_comp] at this
    have hg_le : dom (f ∩ g) ≫ f ⊑ g := by
      rw [dom_inter]
      have h2 : (g ≫ f°) ≫ f ⊑ g := by
        rw [Cat.assoc]; have := comp_mono_left g hf.2; rwa [Cat.comp_id] at this
      exact le_trans (comp_mono_right (inter_lb_right _ _) f) h2
    exact le_inter hf_le hg_le
  · exact le_trans (le_dom_comp (f ∩ g)) (comp_mono_left _ (inter_lb_left f g))

/-- dom(f ∩ g) ≫ g = f ∩ g  for any Map g.  By symmetry. -/
theorem dom_inter_comp_right {a b : 𝒜} {f g : a ⟶ b} (hg : Map g) : dom (f ∩ g) ≫ g = f ∩ g := by
  have h : dom (g ∩ f) ≫ g = g ∩ f := dom_inter_comp hg
  have hdom : dom (f ∩ g) = dom (g ∩ f) := by congr 1; exact Allegory.inter_comm f g
  calc dom (f ∩ g) ≫ g = dom (g ∩ f) ≫ g := by rw [hdom]
    _ = g ∩ f := h
    _ = f ∩ g := Allegory.inter_comm g f

/-! ### Identity and composition in Map(𝒜) -/

/-- **§2.14**: Map(𝒜) is a category. -/
instance (priority := 0) mapCat : Cat.{v} (MapObj 𝒜) where
  Hom   a b := { R : a ⟶ b // Map R }
  id    a   := ⟨Cat.id a, id_is_map_local a⟩
  comp  f g := ⟨f.val ≫ g.val, map_comp f.property g.property⟩
  id_comp f := Subtype.ext (Cat.id_comp f.val)
  comp_id f := Subtype.ext (Cat.comp_id f.val)
  assoc f g h := Subtype.ext (Cat.assoc f.val g.val h.val)

/-! ## §2.147  Finite limits in Map(𝒜) via tabulations

  In the source-apex convention the tabulation legs `f : c→a`, `g : c→b` are maps FROM
  the apex, so the pullback projections of `f g°` ARE maps (no `Map(π°)` hypotheses are
  needed — the old blocker vanishes). -/

section TabularLimits

variable [TabularAllegory 𝒜]

/-- id_c ⊑ g ≫ g° for second tabulation leg (the joint-monic equation). -/
theorem tab_gog {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : Cat.id c ⊑ g ≫ g° :=
  ht.2.2.2 ▸ inter_lb_right _ _

/-- **§2.147 first-leg coreflexive**: for a tabulation `(f,g)` of `R` (source-apex), the
    coreflexive `f° ≫ f` equals `dom R`.  (In Rel(Set): `f°≫f` is the diagonal on the domain
    of `R`.)  Used to compute the coreflexive of a Map(𝒜) pullback/inverse-image projection. -/
theorem tab_leg_dom {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : f° ≫ f = dom R := by
  have hf : Map f := ht.1
  have hR : f° ≫ g = R := ht.2.2.1.symm
  apply le_antisymm
  · -- f°≫f ⊑ dom R = id ∩ R≫R°.  f°≫f ⊑ id (f simple); f°≫f ⊑ R≫R° via id_c ⊑ g≫g°.
    refine le_inter hf.2 ?_
    have hRRo : R ≫ R° = f° ≫ (g ≫ g°) ≫ f := by
      rw [← hR, Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
    rw [hRRo]
    have h1 : f° ≫ f ⊑ f° ≫ (g ≫ g°) ≫ f :=
      comp_mono_left f° (by have := comp_mono_right (tab_gog ht) f; rwa [Cat.id_comp] at this)
    exact h1
  · -- dom R = dom(f°≫g) ⊑ dom(f°) = f°≫f  (`dom_comp_le` + f simple).
    have hdomR : dom R ⊑ dom (f°) := hR ▸ dom_comp_le f° g
    have hdomfo : dom (f°) = f° ≫ f := by
      rw [dom, Allegory.recip_recip, Allegory.inter_comm]
      exact hf.2  -- (f°≫f) ∩ id = f°≫f  since f°≫f ⊑ id (f simple)
    rw [← hdomfo]; exact hdomR

/-! ### §2.147  Pullback cone equation -/

/-- **§2.147 pullback cone**: if (π₁, π₂) tabulate f ≫ g° (source-apex: π₁ : p→a,
    π₂ : p→b, π₁°≫π₂ = f≫g°) then π₁ ≫ f = π₂ ≫ g. -/
theorem tab_pullback_cone {a b c p : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (hfg : π₁° ≫ π₂ = f ≫ g°)
    (hπ₁1 : π₁ ≫ π₁° = Cat.id p) (hπ₂1 : π₂ ≫ π₂° = Cat.id p) :
    π₁ ≫ f = π₂ ≫ g := by
  -- π₂≫g = (π₁π₁°)π₂g = π₁(π₁°π₂)g = π₁(fg°)g = π₁f(g°g) ⊑ π₁f, and symmetrically.
  have hrecip : π₂° ≫ π₁ = g ≫ f° := by
    have h : (π₁° ≫ π₂)° = (f ≫ g°)° := congrArg Allegory.recip hfg
    simpa [Allegory.recip_comp, Allegory.recip_recip] using h
  -- hA : π₁ ≫ f ≫ g° = π₂;  hB : π₂ ≫ g ≫ f° = π₁.
  have hA : π₁ ≫ f ≫ g° = π₂ := by
    rw [← hfg, ← Cat.assoc, hπ₁1, Cat.id_comp]
  have hB : π₂ ≫ g ≫ f° = π₁ := by
    rw [← hrecip, ← Cat.assoc, hπ₂1, Cat.id_comp]
  apply le_antisymm
  · -- π₁f = (π₂ g f°) f = π₂ g (f°f) ⊑ π₂ g.
    calc π₁ ≫ f = (π₂ ≫ g ≫ f°) ≫ f := by rw [hB]
      _ = π₂ ≫ g ≫ (f° ≫ f) := by simp [Cat.assoc]
      _ ⊑ π₂ ≫ g ≫ Cat.id c := comp_mono_left _ (comp_mono_left _ hf.2)
      _ = π₂ ≫ g := by rw [Cat.comp_id]
  · -- π₂g = (π₁ f g°) g = π₁ f (g°g) ⊑ π₁ f.
    calc π₂ ≫ g = (π₁ ≫ f ≫ g°) ≫ g := by rw [hA]
      _ = π₁ ≫ f ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ ⊑ π₁ ≫ f ≫ Cat.id c := comp_mono_left _ (comp_mono_left _ hg.2)
      _ = π₁ ≫ f := by rw [Cat.comp_id]

/-- **§2.147 pullback cone (joint-monic form)**: if (π₁, π₂) tabulate f ≫ g°
    (source-apex: π₁ : p→a, π₂ : p→b, π₁°≫π₂ = f≫g°) with f, g maps, then π₁ ≫ f = π₂ ≫ g.
    This version derives the cone equation directly from the tabulation, using ONLY the
    joint-monic fact via the entirety of π₂≫g / π₁≫f — it does NOT need each leg to be a
    retraction (`π₁≫π₁° = id`). -/
theorem tab_pullback_cone' {a b c p : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
    (hf : Map f) (hg : Map g)
    {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (ht : Tabulates π₁ π₂ (f ≫ g°)) :
    π₁ ≫ f = π₂ ≫ g := by
  have hπ₁ : Map π₁ := ht.1
  have hπ₂ : Map π₂ := ht.2.1
  have hrecip : π₂° ≫ π₁ = g ≫ f° := by
    have h := congrArg Allegory.recip ht.2.2.1
    simp [Allegory.recip_comp, Allegory.recip_recip] at h; exact h.symm
  have hlt1 : (π₂ ≫ g)° ≫ (π₁ ≫ f) ⊑ Cat.id c := by
    have heq : (π₂ ≫ g)° ≫ (π₁ ≫ f) = (g° ≫ g) ≫ (f° ≫ f) := by
      rw [Allegory.recip_comp]; simp only [Cat.assoc]; rw [← Cat.assoc π₂°, hrecip]
      simp [Cat.assoc]
    rw [heq]
    exact le_trans (comp_mono_right hg.2 _) (by rw [Cat.id_comp]; exact hf.2)
  have hle1 : π₁ ≫ f ⊑ π₂ ≫ g := by
    have hent' : Cat.id p ⊑ (π₂ ≫ g) ≫ (π₂ ≫ g)° := by
      have h := entire_comp hπ₂.1 hg.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _
    have h1 : π₁ ≫ f ⊑ ((π₂ ≫ g) ≫ (π₂ ≫ g)°) ≫ (π₁ ≫ f) := by
      have := comp_mono_right hent' (π₁ ≫ f); rwa [Cat.id_comp] at this
    have h2 : ((π₂ ≫ g) ≫ (π₂ ≫ g)°) ≫ (π₁ ≫ f) ⊑ π₂ ≫ g := by
      rw [Cat.assoc]
      exact le_trans (comp_mono_left _ hlt1) (by rw [Cat.comp_id]; exact le_refl _)
    exact le_trans h1 h2
  have hlt2 : (π₁ ≫ f)° ≫ (π₂ ≫ g) ⊑ Cat.id c := by
    have heq : (π₁ ≫ f)° ≫ (π₂ ≫ g) = (f° ≫ f) ≫ (g° ≫ g) := by
      rw [Allegory.recip_comp]; simp only [Cat.assoc]; rw [← Cat.assoc π₁°, ← ht.2.2.1]
      simp [Cat.assoc]
    rw [heq]
    exact le_trans (comp_mono_right hf.2 _) (by rw [Cat.id_comp]; exact hg.2)
  have hle2 : π₂ ≫ g ⊑ π₁ ≫ f := by
    have hent' : Cat.id p ⊑ (π₁ ≫ f) ≫ (π₁ ≫ f)° := by
      have h := entire_comp hπ₁.1 hf.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _
    have h1 : π₂ ≫ g ⊑ ((π₁ ≫ f) ≫ (π₁ ≫ f)°) ≫ (π₂ ≫ g) := by
      have := comp_mono_right hent' (π₂ ≫ g); rwa [Cat.id_comp] at this
    have h2 : ((π₁ ≫ f) ≫ (π₁ ≫ f)°) ≫ (π₂ ≫ g) ⊑ π₁ ≫ f := by
      rw [Cat.assoc]
      exact le_trans (comp_mono_left _ hlt2) (by rw [Cat.comp_id]; exact le_refl _)
    exact le_trans h1 h2
  exact le_antisymm hle1 hle2

/-! ### §2.147  Cover characterization -/

/-- **§2.147**: g : a → b is a cover iff Entire(g°). -/
theorem cover_iff_recip_entire {a b : 𝒜} (g : a ⟶ b) :
    Cat.id b ⊑ g° ≫ g ↔ Entire g° := by
  simp only [Entire, dom, Allegory.recip_recip]
  constructor
  · intro h; exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h)
  · intro h
    calc Cat.id b = Cat.id b ∩ g° ≫ g := h.symm
      _ ⊑ g° ≫ g := inter_lb_right _ _

/-! ### §2.147  Pullback universal property in Map(𝒜)

  The §2.143 universal property of tabulations lives in `S2_1.lean`
  (`tabulation_UP_forward`/`tabulation_UP_unique`) — in the source-apex convention its
  mediating map needs NO `Map(π°)` hypothesis (the old blocker is gone). -/

/-- **§2.147 pullback UMP**: the tabulation of fg° gives the pullback of f and g in Map(𝒜).
    Given maps x : q→a, y : q→b with x≫f = y≫g, there is a unique h : q→p in Map(𝒜)
    with h≫π₁=x and h≫π₂=y. -/
theorem tab_pullback_UMP {a b c p q : 𝒜} {f : a ⟶ c} {g : b ⟶ c}
 (hg : Map g)
    {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (ht : Tabulates π₁ π₂ (f ≫ g°))
    {x : q ⟶ a} {y : q ⟶ b}
    (hx : Map x) (hy : Map y)
    (hcone : x ≫ f = y ≫ g) :
    ∃ (hm : q ⟶ p), Map hm ∧ hm ≫ π₁ = x ∧ hm ≫ π₂ = y ∧
      ∀ hm' : q ⟶ p, Map hm' → hm' ≫ π₁ = x → hm' ≫ π₂ = y → hm' = hm := by
  -- Derive x°y ⊑ fg° from cone equation.
  have hgg : Cat.id b ⊑ g ≫ g° := by
    have := hg.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hxy : x° ≫ y ⊑ f ≫ g° := by
    have s1 : x° ≫ y ⊑ x° ≫ y ≫ g ≫ g° := by
      have h1 := comp_mono_left (x° ≫ y) hgg; rw [Cat.comp_id] at h1
      simp only [Cat.assoc] at h1 ⊢; exact h1
    have s2 : x° ≫ y ≫ g ≫ g° = (x° ≫ x) ≫ f ≫ g° := by
      have hh : x° ≫ (y ≫ g) ≫ g° = x° ≫ (x ≫ f) ≫ g° := by rw [hcone]
      simp only [Cat.assoc] at hh ⊢; exact hh
    have s3 : (x° ≫ x) ≫ f ≫ g° ⊑ f ≫ g° := by
      have h3 := comp_mono_right hx.2 (f ≫ g°)
      rw [Cat.id_comp] at h3; exact h3
    rw [s2] at s1; exact le_trans s1 s3
  obtain ⟨hm, hh_map, hhx, hhy⟩ := tabulation_UP_forward ht hx hy hxy
  refine ⟨hm, hh_map, hhx, hhy, fun hm' hh'_map hhx' hhy' => ?_⟩
  exact tabulation_UP_unique ht hh'_map hh_map (hhx'.trans hhx.symm) (hhy'.trans hhy.symm)

/-! ### §2.147  Equalizer cone + universal property in Map(𝒜)

  The equalizer of f, g : a→b is the splitting e : p→a of dom(f∩g):
  `e° ≫ e = dom(f∩g)`, `e ≫ e° = id_p` (`coreflexive_splits`, source-apex direction).
  The cone is `e ≫ f = e ≫ g`; the UMP factors any map killing the parallel pair. -/

/-- **§2.147 equalizer cone**: if e°≫e = dom(f∩g) and e≫e° = id_p then e ≫ f = e ≫ g. -/
theorem tab_equalizer_cone {a b p : 𝒜} {f g : a ⟶ b} {e : p ⟶ a}
    (hf : Map f) (hg : Map g)
    (hee : e° ≫ e = dom (f ∩ g))
    (he1 : e ≫ e° = Cat.id p) :
    e ≫ f = e ≫ g := by
  -- e≫f = e≫(dom(f∩g))≫? ; instead: e(f∩g) = ef ∩ eg and e°e = dom(f∩g) ⊑ (f∩g)(f∩g)°…
  -- Direct: e ≫ f = (e≫e°)≫e≫f = e≫(e°≫e)≫f = e≫dom(f∩g)≫f = e≫(f∩g) (dom_inter_comp),
  -- and likewise e≫g = e≫(f∩g); so e≫f = e≫g.
  have hef : e ≫ f = e ≫ (f ∩ g) := by
    calc e ≫ f = (e ≫ e°) ≫ e ≫ f := by rw [he1, Cat.id_comp]
      _ = e ≫ (e° ≫ e) ≫ f := by simp [Cat.assoc]
      _ = e ≫ dom (f ∩ g) ≫ f := by rw [hee]
      _ = e ≫ (f ∩ g) := by rw [dom_inter_comp hf]
  have heg : e ≫ g = e ≫ (f ∩ g) := by
    calc e ≫ g = (e ≫ e°) ≫ e ≫ g := by rw [he1, Cat.id_comp]
      _ = e ≫ (e° ≫ e) ≫ g := by simp [Cat.assoc]
      _ = e ≫ dom (f ∩ g) ≫ g := by rw [hee]
      _ = e ≫ (f ∩ g) := by rw [dom_inter_comp_right hg]
  rw [hef, heg]

/-- **§2.147 equalizer UMP**: given the splitting e of dom(f∩g) and a map h with h≫f=h≫g,
    there is a unique map k with k≫e=h. -/
theorem tab_equalizer_UMP {a b p q : 𝒜} {f g : a ⟶ b}
    (hf : Map f)
    {e : p ⟶ a}
    (he : Map e) (hee : e° ≫ e = dom (f ∩ g)) (he1 : e ≫ e° = Cat.id p)
    {h : q ⟶ a} (hh : Map h) (hcone : h ≫ f = h ≫ g) :
    ∃ (k : q ⟶ p), Map k ∧ k ≫ e = h ∧
      ∀ k' : q ⟶ p, Map k' → k' ≫ e = h → k' = k := by
  -- (e, e) tabulates e°≫e (= dom(f∩g)); we apply the §2.143 forward UP with x = y = h.
  have htab_e : Tabulates e e (e° ≫ e) := ⟨he, he, rfl, by rw [Allegory.inter_idem, he1]⟩
  -- h°≫h ⊑ e°≫e = dom(f∩g).
  -- First h≫(f∩g) = h≫f (h simple: h(f∩g) = hf ∩ hg = hf).
  have hfg_eq : h ≫ (f ∩ g) = h ≫ f := by
    have := simple_dist_inter hh.2 f g; rw [this, hcone, Allegory.inter_idem]
  have hmap_hf : Map (h ≫ f) := map_comp hh hf
  have hent : Cat.id q ⊑ (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° := by
    have := (hfg_eq ▸ hmap_hf).1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hdomfg : h° ≫ h ⊑ (f ∩ g) ≫ (f ∩ g)° := by
    have hA := hent
    have hexp : (h ≫ (f ∩ g)) ≫ (h ≫ (f ∩ g))° = h ≫ (f ∩ g) ≫ (f ∩ g)° ≫ h° := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    rw [hexp] at hA
    have step : h° ≫ h ⊑ (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) := by
      have s1 := comp_mono_left h° hA; rw [Cat.comp_id] at s1
      have s2 := comp_mono_right s1 h
      simp only [Cat.assoc] at s2 ⊢; exact s2
    have sb : (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑ (f ∩ g) ≫ (f ∩ g)° := by
      have sr1 : (h° ≫ h) ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑
               Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) := comp_mono_right hh.2 _
      have sr2 : Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ (h° ≫ h) ⊑
               Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ Cat.id a :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hh.2))
      have sr3 : Cat.id a ≫ (f ∩ g) ≫ (f ∩ g)° ≫ Cat.id a = (f ∩ g) ≫ (f ∩ g)° := by
        simp [Cat.id_comp, Cat.comp_id]
      exact sr3 ▸ le_trans sr1 sr2
    exact le_trans step sb
  have hdomfg2 : h° ≫ h ⊑ e° ≫ e := by
    rw [hee]; exact le_inter hh.2 hdomfg
  obtain ⟨k, hk_map, hke, _⟩ := tabulation_UP_forward htab_e hh hh hdomfg2
  exact ⟨k, hk_map, hke,
    fun k' hk'_map hk'e => tabulation_UP_unique htab_e hk'_map hk_map (hk'e.trans hke.symm)
      (hk'e.trans hke.symm)⟩

end TabularLimits

/-! ## §2.148  𝒜 ≅ Rel(Map 𝒜) for tabular 𝒜

  In Freyd's §2.148, a tabular allegory 𝒜 is isomorphic to Rel(Map 𝒜) — the
  allegory of relations in its own category of maps.  The comparison functors are:

    Φ : 𝒜 → Rel(Map 𝒜),  R ↦ [tabulation span of R] = [(f, g) with Tabulates f g R]
    Ψ : Rel(Map 𝒜) → 𝒜,  [(f : c→a, g : c→b)] ↦ f° ≫ g

  In the source-apex convention (f : c→a, g : c→b, R = f°≫g, f≫f° ∩ g≫g° = id_c):

    (i)  Ψ∘Φ = id: from Tabulates f g R one has f° ≫ g = R   [see tab_round_trip_rel]
    (ii) Φ∘Ψ on standard spans: (f,g) with f≫f° ∩ g≫g° = id_c self-tabulates
         f°≫g                                                    [see span_self_tabulates]
    (iii) Any two tabulations of the same R are related by a UNIQUE isomorphism
         (UNCONDITIONAL — §2.144, no `Map(f°)` needed)       [see tab_iso_unique_exists]

  A "jointly-monic span in Map(𝒜)" (an object of Rel(Map 𝒜)(a,b)) is exactly a
  `Tabulates`-triple (f,g,R) — the tabulation condition f≫f° ∩ g≫g° = id_c IS the
  §2.141 jointly-monic condition for the pair (f, g) of maps with common source c. -/

section Rel148

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-- **§2.148 (J) — forward round-trip** (Ψ∘Φ = id): from a tabulation (f,g) of R,
    applying the backward functor Ψ recovers R.  Trivial: Ψ(Φ(R)) = f° ≫ g = R. -/
theorem tab_round_trip_rel {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) : f° ≫ g = R :=
  ht.2.2.1.symm

/-- **§2.148 (K) — backward round-trip** (Φ∘Ψ identifies spans with tabulations):
    a span (f : c→a, g : c→b) of maps satisfying the jointly-monic condition
    f≫f° ∩ g≫g° = id_c is itself a tabulation of f°≫g. -/
theorem span_self_tabulates {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b}
    (hf : Map f) (hg : Map g) (hjoint : f ≫ f° ∩ g ≫ g° = Cat.id c) :
    Tabulates f g (f° ≫ g) :=
  ⟨hf, hg, rfl, hjoint⟩

/-- **§2.148 (L) — unique iso between tabulations** (§2.144, now UNCONDITIONAL): two
    tabulations of the same `R` are related by a unique isomorphism `u` with `f' = uf`,
    `g' = ug`.  No `Map(f°)` hypotheses are needed in the source-apex convention. -/
theorem tab_iso_unique_exists {a b c c' : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {f' : c' ⟶ a} {g' : c' ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (ht' : Tabulates f' g' R) :
    ∃ (u : c' ⟶ c), Map u ∧ Freyd.IsIso u ∧ f' = u ≫ f ∧ g' = u ≫ g :=
  tabulation_unique_iso ht ht'

/-! ## §2.148  RelMap 𝒜 — the allegory Rel(Map(𝒜))

  `RelMap 𝒜` is the allegory whose objects are those of 𝒜 and whose morphisms
  `a ⇸ b` are the TABULAR morphisms `R : a ⟶ b` in 𝒜.  In a `TabularAllegory`
  every morphism is tabular, so `RelMap 𝒜` has the SAME hom-sets as 𝒜 — the subtype
  `{R : a ⟶ b // Tabular R}` is in bijection with `a ⟶ b`.  The allegory operations
  (composition, reciprocation, intersection) on `RelMap 𝒜` are simply those of 𝒜,
  well-defined because tabular morphisms are closed under all three:

    • Closed under recip: if `(f,g)` tabulates `R` then `(g,f)` tabulates `R°`.
    • Closed under comp: if R and S are tabular then R ≫ S is tabular
      (every morphism of 𝒜 is tabular by `TabularAllegory.tabular`).
    • Closed under inter: same reason.

  These closures follow trivially from `TabularAllegory.tabular`, so the subtype
  `{R // Tabular R}` with operations inherited from 𝒜 forms an `Allegory` in a
  uniform way.  We record this and build the comparison functors. -/

/-- Tabularity is closed under reciprocation: if (f,g) tabulates R then (g,f) tabulates R°. -/
theorem tabular_recip {a b : 𝒜} {R : a ⟶ b} (hR : Tabular R) : Tabular R° := by
  obtain ⟨c, f, g, hf, hg, hR_eq, hjoint⟩ := hR
  refine ⟨c, g, f, hg, hf, ?_, by rw [Allegory.inter_comm]; exact hjoint⟩
  -- Goal: R° = g° ≫ f, from R = f° ≫ g.
  calc R° = (f° ≫ g)° := by rw [hR_eq]
    _ = g° ≫ f := by rw [Allegory.recip_comp, Allegory.recip_recip]

/-- Tabularity is closed under composition: both R and S tabular ⟹ R ≫ S tabular.
    In a `TabularAllegory` this is immediate from the axiom. -/
theorem tabular_comp {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c}
    (_hR : Tabular R) (_hS : Tabular S) : Tabular (R ≫ S) :=
  TabularAllegory.tabular _

/-- Tabularity is closed under intersection. -/
theorem tabular_inter {a b : 𝒜} {R S : a ⟶ b}
    (_hR : Tabular R) (_hS : Tabular S) : Tabular (R ∩ S) :=
  TabularAllegory.tabular _

/-! ### Hom-set of RelMap 𝒜 and the bijection with 𝒜 homs

  `RelMap 𝒜` has the same objects as 𝒜 and hom-set `a ⇸ b := {R : a ⟶ b // Tabular R}`.
  In a `TabularAllegory` the bijection `Φ : (a ⟶ b) ≅ {R : a ⟶ b // Tabular R}` is
  trivial: `Φ(R) = ⟨R, tabular⟩`, `Ψ(⟨R,_⟩) = R`.

  We package the `Allegory` axioms directly on the subtype to show it forms an allegory
  isomorphic to 𝒜. The instance avoids `RelMapObj 𝒜 = 𝒜` (which would conflict with the
  existing `TabularAllegory` instance) by wrapping objects in a `WrapObj` newtype.  -/

/-- A wrapper newtype for the objects of `RelMap 𝒜`, avoiding instance collisions
    with the ambient `TabularAllegory 𝒜`. -/
structure RelMapObj (𝒜 : Type u) where
  /-- The underlying object. -/
  obj : 𝒜

/-- **§2.148 allegory instance**: `RelMap 𝒜` is an allegory.
    Objects = `RelMapObj 𝒜` (a wrapper for objects of 𝒜); morphisms from `⟨a⟩` to `⟨b⟩`
    are tabular morphisms `{R : a ⟶ b // Tabular R}`.  Operations pointwise from 𝒜. -/
instance relMapAllegory : Allegory.{v} (RelMapObj 𝒜) where
  Hom A B := { R : A.obj ⟶ B.obj // Tabular R }
  id  A   := ⟨Cat.id A.obj, TabularAllegory.tabular _⟩
  comp f g := ⟨f.val ≫ g.val, tabular_comp f.2 g.2⟩
  id_comp f := Subtype.ext (Cat.id_comp f.val)
  comp_id f := Subtype.ext (Cat.comp_id f.val)
  assoc f g h := Subtype.ext (Cat.assoc f.val g.val h.val)
  recip f := ⟨f.val°, tabular_recip f.2⟩
  inter f g := ⟨f.val ∩ g.val, tabular_inter f.2 g.2⟩
  recip_recip f     := Subtype.ext (Allegory.recip_recip f.val)
  recip_comp  f g   := Subtype.ext (Allegory.recip_comp f.val g.val)
  recip_inter f g   := Subtype.ext (Allegory.recip_inter f.val g.val)
  inter_idem  f     := Subtype.ext (Allegory.inter_idem f.val)
  inter_comm  f g   := Subtype.ext (Allegory.inter_comm f.val g.val)
  inter_assoc f g h := Subtype.ext (Allegory.inter_assoc f.val g.val h.val)
  semidistrib R S T := by exact Subtype.ext (Allegory.semidistrib R.val S.val T.val)
  modular R S T     := by exact Subtype.ext (Allegory.modular R.val S.val T.val)

/-! ### Comparison maps Φ and Ψ

  `Φ(R) = ⟨R, tabular⟩` and `Ψ(⟨R,_⟩) = R` are mutually inverse bijections on hom-sets.
  At the allegory level they preserve all operations. -/

/-- **§2.148 Φ** — sends `R : a ⟶ b` to `⟨R, tabular⟩` in RelMap 𝒜. -/
def relMap_Phi {a b : 𝒜} (R : a ⟶ b) : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩ :=
  ⟨R, TabularAllegory.tabular R⟩

/-- **§2.148 Ψ** — discards the tabularity certificate. -/
def relMap_Psi {a b : 𝒜} (R : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩) : a ⟶ b :=
  R.val

/-- **§2.148 (Ψ∘Φ = id)**. -/
@[simp] theorem relMap_Psi_Phi {a b : 𝒜} (R : a ⟶ b) :
    relMap_Psi (relMap_Phi R) = R := rfl

/-- **§2.148 (Φ∘Ψ = id)**. -/
@[simp] theorem relMap_Phi_Psi {a b : 𝒜} (R : @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩) :
    relMap_Phi (relMap_Psi R) = R := by cases R; rfl

/-- **§2.148 — Φ preserves composition** (val-level). -/
theorem relMap_Phi_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    (relMap_Phi (R ≫ S)).val = (relMap_Phi R).val ≫ (relMap_Phi S).val := rfl

/-- **§2.148 — Φ preserves reciprocation** (val-level). -/
theorem relMap_Phi_recip {a b : 𝒜} (R : a ⟶ b) :
    (relMap_Phi R°).val = (relMap_Phi R).val° := rfl

/-- **§2.148 — Φ preserves intersection** (val-level). -/
theorem relMap_Phi_inter {a b : 𝒜} (R S : a ⟶ b) :
    (relMap_Phi (R ∩ S)).val = (relMap_Phi R).val ∩ (relMap_Phi S).val := rfl

end Rel148

/-! ## §2.148  AllegoryFunctor and AllegoryEquiv

  An allegory functor F : 𝒜 → ℬ is a functor on the underlying categories that also
  preserves reciprocation and intersection.  An allegory equivalence is a pair of
  allegory functors mutually inverse on objects and homs. -/

section AllegoryFunctorDef

/-- A functor between allegories preserving `≫`, `id`, `°`, `∩`. -/
structure AllegoryFunctor (𝒜 : Type u₁) (ℬ : Type u₂) [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] where
  /-- Object map. -/
  obj  : 𝒜 → ℬ
  /-- Hom map. -/
  map  : {a b : 𝒜} → (a ⟶ b) → (obj a ⟶ obj b)
  map_id   : ∀ (a : 𝒜), map (Cat.id a) = Cat.id (obj a)
  map_comp : ∀ {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c), map (R ≫ S) = map R ≫ map S
  map_recip : ∀ {a b : 𝒜} (R : a ⟶ b), map R° = (map R)°
  map_inter : ∀ {a b : 𝒜} (R S : a ⟶ b), map (R ∩ S) = map R ∩ map S

/-- A pair of allegory functors mutually inverse on objects and homs (using `HEq`
    for the hom round-trip conditions, since the hom-types differ by the object round-trip). -/
structure AllegoryEquiv (𝒜 : Type u₁) (ℬ : Type u₂) [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] where
  toFun   : AllegoryFunctor 𝒜 ℬ
  invFun  : AllegoryFunctor ℬ 𝒜
  left_inv_obj  : ∀ (a : 𝒜), invFun.obj (toFun.obj a) = a
  right_inv_obj : ∀ (b : ℬ), toFun.obj (invFun.obj b) = b
  /-- Round-trip on homs: `invFun.map (toFun.map R) ≅ R` (heterogeneously). -/
  left_inv_map  : ∀ {a b : 𝒜} (R : a ⟶ b),
    HEq (invFun.map (toFun.map R)) R
  /-- Round-trip on homs: `toFun.map (invFun.map S) ≅ S` (heterogeneously). -/
  right_inv_map : ∀ {a b : ℬ} (S : a ⟶ b),
    HEq (toFun.map (invFun.map S)) S

/-- Composition of allegory functors: `obj`/`map` compose, every law follows. -/
def AllegoryFunctor.comp {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] [Allegory.{v₃} 𝒞]
    (F : AllegoryFunctor 𝒜 ℬ) (G : AllegoryFunctor ℬ 𝒞) : AllegoryFunctor 𝒜 𝒞 where
  obj a := G.obj (F.obj a)
  map {a b} R := G.map (F.map R)
  map_id a := by rw [F.map_id, G.map_id]
  map_comp R S := by rw [F.map_comp, G.map_comp]
  map_recip R := by rw [F.map_recip, G.map_recip]
  map_inter R S := by rw [F.map_inter, G.map_inter]

/-- An allegory functor is FAITHFUL if it is injective on hom-sets. -/
def AllegoryFunctor.Faithful {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (F : AllegoryFunctor 𝒜 ℬ) : Prop :=
  ∀ {a b : 𝒜} (R S : a ⟶ b), F.map R = F.map S → R = S

/-- Faithfulness composes. -/
theorem AllegoryFunctor.Faithful.comp {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] [Allegory.{v₃} 𝒞]
    {F : AllegoryFunctor 𝒜 ℬ} {G : AllegoryFunctor ℬ 𝒞}
    (hF : F.Faithful) (hG : G.Faithful) : (F.comp G).Faithful :=
  fun R S h => hF R S (hG _ _ h)

/-- The forward leg of an `AllegoryEquiv` is faithful (it has a left inverse on homs). -/
theorem AllegoryEquiv.toFun_faithful {𝒜 : Type u₁} {ℬ : Type u₂}
    [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] (E : AllegoryEquiv 𝒜 ℬ) : E.toFun.Faithful := by
  intro a b R S h
  have hR := E.left_inv_map R
  have hS := E.left_inv_map S
  -- `invFun.map (toFun.map R) ≅ R`, `invFun.map (toFun.map S) ≅ S`, and `toFun.map R = toFun.map S`.
  rw [h] at hR
  exact eq_of_heq (hR.symm.trans hS)

end AllegoryFunctorDef

/-! ## §2.148  The equivalence Rel(Map 𝒜) ≅ 𝒜

  We now package the comparison maps Φ, Ψ as an `AllegoryEquiv (RelMapObj 𝒜) 𝒜`. -/

section RelMapEquiv

variable {𝒜 : Type u} [TabularAllegory 𝒜]

/-! ### Allegory functor Ψ : RelMap 𝒜 → 𝒜 -/

/-- The hom-map of Ψ: forget the tabularity certificate, reindexed by `obj`-projections. -/
private def relMap_Psi_map {A B : RelMapObj 𝒜}
    (R : @Cat.Hom _ relMapAllegory.toCat A B) : A.obj ⟶ B.obj := R.val

/-- **§2.148 — Ψ is an allegory functor** RelMap 𝒜 → 𝒜. -/
def relMap_Psi_functor : AllegoryFunctor (RelMapObj 𝒜) 𝒜 where
  obj   := RelMapObj.obj
  map   := relMap_Psi_map
  map_id   _     := rfl
  map_comp _ _   := rfl
  map_recip _    := rfl
  map_inter _ _  := rfl

/-! ### Allegory functor Φ : 𝒜 → RelMap 𝒜 -/

/-- The hom-map of Φ: wrap with tabularity certificate. -/
private def relMap_Phi_map {a b : 𝒜} (R : a ⟶ b) :
    @Cat.Hom _ relMapAllegory.toCat ⟨a⟩ ⟨b⟩ :=
  ⟨R, TabularAllegory.tabular R⟩

/-- Φ preserves `≫` at the Subtype level. -/
private theorem relMap_Phi_map_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    relMap_Phi_map (R ≫ S) = relMap_Phi_map R ≫ relMap_Phi_map S :=
  Subtype.ext rfl

/-- Φ preserves `°` at the Subtype level. -/
private theorem relMap_Phi_map_recip {a b : 𝒜} (R : a ⟶ b) :
    relMap_Phi_map R° = (relMap_Phi_map R)° :=
  Subtype.ext rfl

/-- Φ preserves `∩` at the Subtype level. -/
private theorem relMap_Phi_map_inter {a b : 𝒜} (R S : a ⟶ b) :
    relMap_Phi_map (R ∩ S) = relMap_Phi_map R ∩ relMap_Phi_map S :=
  Subtype.ext rfl

/-- **§2.148 — Φ is an allegory functor** 𝒜 → RelMap 𝒜. -/
def relMap_Phi_functor : AllegoryFunctor 𝒜 (RelMapObj 𝒜) where
  obj   := fun a => ⟨a⟩
  map   := relMap_Phi_map
  map_id   _     := Subtype.ext rfl
  map_comp R S   := relMap_Phi_map_comp R S
  map_recip R    := relMap_Phi_map_recip R
  map_inter R S  := relMap_Phi_map_inter R S

/-! ### Mutual-inverse conditions -/

-- In the equivalence below: toFun = Ψ (RelMapObj 𝒜 → 𝒜), invFun = Φ (𝒜 → RelMapObj 𝒜).
-- left_inv_obj requires invFun.obj (toFun.obj A) = A, i.e. Φ(Ψ(A)) = A.
-- right_inv_obj requires toFun.obj (invFun.obj a) = a, i.e. Ψ(Φ(a)) = a.

/-- Φ∘Ψ = id on objects: `⟨A.obj⟩ = A`. -/
private theorem relMap_PhiPsi_obj (A : RelMapObj 𝒜) :
    relMap_Phi_functor.obj (relMap_Psi_functor.obj A) = A := by cases A; rfl

/-- Ψ∘Φ = id on objects: `⟨a⟩.obj = a`. -/
private theorem relMap_PsiPhi_obj (a : 𝒜) :
    relMap_Psi_functor.obj (relMap_Phi_functor.obj a) = a := rfl

/-- Φ∘Ψ = id on homs (HEq): `Φ(Ψ(S)) ≅ S`. -/
private theorem relMap_PhiPsi_map {A B : RelMapObj 𝒜}
    (S : @Cat.Hom _ relMapAllegory.toCat A B) :
    HEq (relMap_Phi_functor.map (relMap_Psi_functor.map S)) S := by
  cases A; cases B; cases S; exact HEq.refl _

/-- Ψ∘Φ = id on homs (HEq): `Ψ(Φ(R)) ≅ R`. -/
private theorem relMap_PsiPhi_map {a b : 𝒜} (R : a ⟶ b) :
    HEq (relMap_Psi_functor.map (relMap_Phi_functor.map R)) R :=
  HEq.refl _

/-- **§2.148** — the allegory equivalence `RelMap 𝒜 ≅ 𝒜`.
    Ψ : RelMap 𝒜 → 𝒜 and Φ : 𝒜 → RelMap 𝒜 are mutually inverse allegory functors. -/
def relMap_allegoryEquiv : AllegoryEquiv (RelMapObj 𝒜) 𝒜 where
  toFun         := relMap_Psi_functor
  invFun        := relMap_Phi_functor
  left_inv_obj  := relMap_PhiPsi_obj      -- invFun.obj (toFun.obj A) = A
  right_inv_obj := relMap_PsiPhi_obj      -- toFun.obj (invFun.obj a) = a
  left_inv_map  := relMap_PhiPsi_map      -- HEq (invFun.map (toFun.map S)) S
  right_inv_map := relMap_PsiPhi_map      -- HEq (toFun.map (invFun.map R)) R

end RelMapEquiv


/-! ## §2.212  Map(𝒜) is a pre-logos for tabular unitary distributive 𝒜

    "§2.212: If 𝒜 is a tabular unitary distributive allegory, then Map(𝒜) is a pre-logos."

    PROVED (sorry-free): HasTerminal, HasPullbacks, HasBinaryProducts, HasEqualizers, HasImages,
            PullbacksTransferCovers, RegularCategory, HasSubobjectUnions, PreLogos.
    The `Allegory` diamond is resolved by `TabularUnitaryDistributiveAllegory` (single class
    merging tabular/unitary/distributive parents); `mapPreLogos` assembles the full instance. -/

/-- A TABULAR UNITARY ALLEGORY (§2.212): combines `TabularAllegory` and `UnitaryAllegory`
    in a single class so the `Allegory` diamond is merged.  Having both in scope
    simultaneously creates two `Allegory A` instances (one from each parent), making
    expressions like `f.val ≫ g.val°` fail with "instance not definitionally equal".
    A single `TabularUnitaryAllegory` provides exactly one `Allegory A`. -/
class TabularUnitaryAllegory (𝒜 : Type u) extends TabularAllegory 𝒜, UnitaryAllegory 𝒜

/-- A **TABULAR UNITARY DISTRIBUTIVE ALLEGORY** (§2.212): combines `TabularUnitaryAllegory`
    (= `TabularAllegory` + `UnitaryAllegory`) with `DistributiveAllegory` in a SINGLE class so
    the `Allegory` grandparent is merged into one `toAllegory` field.  This is the standard Lean 4
    diamond-safe structure-inheritance pattern: extending all the parents directly makes Lean
    merge their shared `Allegory` parent, so `≫`/`°`/`∩` (the tabular/unitary side) and `∪`/`𝟘`
    (the distributive side) all live on the SAME `Allegory A` instance — no "synthesized instance
    not definitionally equal" diamond.  (The earlier worry that this "does not help" was mistaken;
    `TabularUnitaryAllegory.toTabularAllegory.toAllegory = DistributiveAllegory.toAllegory` is
    `rfl` here.)  Every lemma needing `[TabularUnitaryAllegory A]`/`[DistributiveAllegory A]` is
    served automatically from this class via the projection instances. -/
class TabularUnitaryDistributiveAllegory (𝒜 : Type u) extends
    TabularUnitaryAllegory 𝒜, DistributiveAllegory 𝒜

/-- A TABULAR UNITARY POSITIVE allegory: a `TabularUnitaryDistributiveAllegory` that is also
    POSITIVE (§2.215, has finite coproducts).  Extending both parents directly merges their
    shared `DistributiveAllegory` (hence `Allegory`) — the same diamond-safe inheritance pattern
    as `TabularUnitaryDistributiveAllegory` — so `≫`/`°`/`∩`/`∪`/`𝟘` and the coproduct injections
    all live on ONE `Allegory 𝒜`.  This is the hypothesis under which `Map(𝒜)` is a POSITIVE
    pre-logos with disjoint binary coproducts (§2.214 dual). -/
class TabularUnitaryPositiveAllegory (𝒜 : Type u) extends
    TabularUnitaryDistributiveAllegory 𝒜, PositiveAllegory 𝒜

/-! ### §2.212  Domain algebra: `dom` distributes over union

  Two pure (distributive-)allegory facts used by the inverse-image preservation laws below:
  `id ∩ R ⊑ dom R` for any `R`, and `dom (P ∪ Q) = dom P ∪ dom Q`. -/

section DomUnion

variable {𝒜 : Type u}

/-- `id ∩ R ⊑ dom R` for any endo `R`.  The coreflexive `C := id ∩ R` is symmetric idempotent
    (`C = C ≫ C°`) and `C ⊑ R`, `C° ⊑ R°`, whence `C = C≫C° ⊑ R≫R°`; with `C ⊑ id` this gives
    `C ⊑ id ∩ R≫R° = dom R`. -/
theorem id_inter_le_dom [Allegory 𝒜] {a : 𝒜} (R : a ⟶ a) :
    Cat.id a ∩ R ⊑ dom R := by
  have hcor : Coreflexive (Cat.id a ∩ R) := inter_lb_left _ _
  have hidem : (Cat.id a ∩ R) ≫ (Cat.id a ∩ R)° = Cat.id a ∩ R := by
    have h := coreflexive_symmetric_idempotent hcor
    rw [symmetric_eq h.1]; exact h.2
  have hle : Cat.id a ∩ R ⊑ R ≫ R° := by
    have hCR : Cat.id a ∩ R ⊑ R := inter_lb_right _ _
    have hCRo : (Cat.id a ∩ R)° ⊑ R° := recip_mono hCR
    calc Cat.id a ∩ R = (Cat.id a ∩ R) ≫ (Cat.id a ∩ R)° := hidem.symm
      _ ⊑ R ≫ R° := le_trans (comp_mono_right hCR _) (comp_mono_left R hCRo)
  exact le_inter (inter_lb_left _ _) hle

/-- `dom (P ∪ Q) = dom P ∪ dom Q` in a distributive allegory.  The `⊒` direction is
    monotonicity; for `⊑`, expand `(P∪Q)(P∪Q)° = PP° ∪ PQ° ∪ QP° ∪ QQ°`, distribute `id ∩ ·`,
    and absorb the cross terms via `id ∩ PQ° ⊑ dom(PQ°) ⊑ dom P` (`id_inter_le_dom` + `dom_comp_le`). -/
theorem dom_union [DistributiveAllegory 𝒜] {a b : 𝒜} (P Q : a ⟶ b) :
    dom (P ∪ Q) = dom P ∪ dom Q := by
  apply le_antisymm
  · -- ⊑ : expand and distribute id ∩ (·) over the four-fold union, absorb cross terms.
    dsimp [dom]
    rw [recip_union, DistributiveAllegory.comp_union_distrib,
        union_comp_distrib, union_comp_distrib,
        DistributiveAllegory.inter_union_distrib, DistributiveAllegory.inter_union_distrib,
        DistributiveAllegory.inter_union_distrib]
    -- Goal: a four-fold union of the meets id∩{PQ°,QQ°,PP°,QP°}  ⊑  (id∩PP°) ∪ (id∩QQ°)
    have hPP : Cat.id a ∩ P ≫ P° ⊑ dom P ∪ dom Q := le_union_left _ _
    have hQQ : Cat.id a ∩ Q ≫ Q° ⊑ dom P ∪ dom Q := le_union_right _ _
    have hPQ : Cat.id a ∩ P ≫ Q° ⊑ dom P ∪ dom Q :=
      le_trans (le_trans (id_inter_le_dom (P ≫ Q°)) (dom_comp_le P Q°)) (le_union_left _ _)
    have hQP : Cat.id a ∩ Q ≫ P° ⊑ dom P ∪ dom Q :=
      le_trans (le_trans (id_inter_le_dom (Q ≫ P°)) (dom_comp_le Q P°)) (le_union_right _ _)
    refine union_lub (union_lub hPQ hQQ) (union_lub hPP hQP)
  · -- ⊒ : dom P, dom Q ⊑ dom(P∪Q) by monotonicity.
    exact union_lub (dom_mono_of_le (le_union_left _ _)) (dom_mono_of_le (le_union_right _ _))

/-- `dom R = dom (R ≫ R°)` for any `R`.  `⊑`: `dom R = id ∩ RR° ⊑ dom(RR°)` (`id_inter_le_dom`);
    `⊒`: `dom(RR°) ⊑ dom R` (`dom_comp_le`). -/
theorem dom_eq_dom_comp_recip [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    dom R = dom (R ≫ R°) :=
  le_antisymm (id_inter_le_dom (R ≫ R°)) (dom_comp_le R R°)

/-- `dom 𝟘 = 𝟘`: `dom 𝟘 = id ∩ 𝟘≫𝟘° = id ∩ 𝟘 = 𝟘`. -/
theorem dom_zero [DistributiveAllegory 𝒜] {a b : 𝒜} : dom (𝟘 : a ⟶ b) = (𝟘 : a ⟶ a) := by
  dsimp [dom]; rw [recip_zero, DistributiveAllegory.comp_zero]
  exact le_antisymm (inter_lb_right _ _) (zero_le _)

end DomUnion

section MapPreLogos

-- §2.154/§2.16: the whole REGULAR-category structure of `Map(𝒜)` (terminal, pullbacks,
-- products, equalizers, images, PullbacksTransferCovers, `mapRegularCategory`) needs only
-- TABULAR + UNITARY, exactly as in the book.  Distributivity enters first at
-- `HasSubobjectUnions` (the pre-logos upgrade), which lives in the next section.
variable {A : Type u} [TabularUnitaryAllegory A]

-- mapCat is at priority 0 by default; do NOT raise it higher than Allegory.toCat (~1000)
-- since that would break the allegory operations (°, ⊑, etc.) which use Allegory.toCat.
-- All mapCat hom usage must be annotated with @Cat.Hom _ (mapCat ..) or @HasPullback.mk etc.

-- Subtype equality helper for mapCat homs
private theorem mapHom_ext {a b : MapObj A}
    {f g : @Cat.Hom _ (mapCat (𝒜 := A)) a b}
    (h : f.val = g.val) : f = g := Subtype.ext h

/-- Any two maps from a to unit_obj agree (allegory-level). -/
private theorem map_to_unit_unique_alg {a : A}
    {f g : a ⟶ UnitaryAllegory.unit_obj (𝒜 := A)}
    (hf : Map f) (hg : Map g) : f = g := by
  apply map_order_discrete hf hg
  obtain ⟨hPU, _⟩ := UnitaryAllegory.unit_prop (𝒜 := A)
  have hEntG : Cat.id a ⊑ g ≫ g° := by
    have := hg.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have h1 : f ⊑ (g ≫ g°) ≫ f := by
    have := comp_mono_right hEntG f; rwa [Cat.id_comp] at this
  have h2 : (g ≫ g°) ≫ f = g ≫ g° ≫ f := Cat.assoc g g° f
  have h3 : g ≫ g° ≫ f ⊑ g ≫ Cat.id (UnitaryAllegory.unit_obj (𝒜 := A)) :=
    comp_mono_left g (hPU (g° ≫ f))
  rw [Cat.comp_id] at h3
  exact le_trans h1 (h2 ▸ h3)

/-- §2.152: The unit object of 𝒜 is terminal in Map(𝒜). -/
noncomputable def mapHasTerminal : @HasTerminal (MapObj A) (mapCat (𝒜 := A)) :=
  @HasTerminal.mk (MapObj A) (mapCat (𝒜 := A))
    UnitaryAllegory.unit_obj
    (fun a =>
      let h := unit_proj_is_map (𝒜 := A) a
      (⟨h.choose, h.choose_spec⟩ :
        @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a (UnitaryAllegory.unit_obj (𝒜 := A))))
    (fun {_} f g =>
      mapHom_ext (map_to_unit_unique_alg f.property g.property))

/-! ### §2.212  HasPullbacks (MapObj A)

  Pullback of f : a → c, g : b → c in Map(𝒜) = tabulation of f ≫ g°.
  By `tab_pullback_UMP` (proved above) this cone has the universal property. -/

-- Helper: Map e ⟹ id_p ⊑ e≫e° (Entire e)
private theorem map_entire_le {A : Type u} [Allegory A] {p b : A} {e : p ⟶ b}
    (he : Map e) : Cat.id p ⊑ e ≫ e° := by
  have := he.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _

/-- A map `u` with a map retraction (`w ≫ u = id`, `w` a map) is RELATIONALLY a split mono:
    `u° ≫ u = id`.  Proof: `w ⊑ u°` (since `u` entire: `w ⊑ w(uu°) = (wu)u° = u°`), so
    `id = wu ⊑ u°u`; combined with `u°u ⊑ id` (`u` simple). -/
theorem map_retr_leg {A : Type u} [Allegory A] {p q : A} {u : p ⟶ q} {w : q ⟶ p}
    (hu : Map u) (hwu : w ≫ u = Cat.id q) : u° ≫ u = Cat.id q := by
  apply le_antisymm hu.2
  -- w ⊑ u°  ⟹  id = w≫u ⊑ u°≫u.
  have hw_le : w ⊑ u° := by
    have h1 : w ⊑ w ≫ (u ≫ u°) := by
      have := comp_mono_left w (map_entire_le hu); rwa [Cat.comp_id] at this
    have h2 : w ≫ (u ≫ u°) = (w ≫ u) ≫ u° := by rw [Cat.assoc]
    rw [h2, hwu, Cat.id_comp] at h1; exact h1
  have := comp_mono_right hw_le u; rw [hwu] at this; exact this

/-- Helper for mapHasPullback: extract the mediating map data via Classical.choice,
    taking cone fields as plain allegory homs to avoid Cat synthesis issues. -/
private noncomputable def mapLiftData {a b c p : A}
    {f : a ⟶ c} {g : b ⟶ c} {π₁ : p ⟶ a} {π₂ : p ⟶ b}
    (_ : Map f) (hg : Map g) (ht : Tabulates π₁ π₂ (f ≫ g°))
    (q : A) (x : q ⟶ a) (y : q ⟶ b)
    (hx : Map x) (hy : Map y) (hw : x ≫ f = y ≫ g) :
    PSigma fun hm : {R : q ⟶ p // Map R} =>
        hm.val ≫ π₁ = x ∧ hm.val ≫ π₂ = y :=
  Classical.choice (by
    obtain ⟨hm, hhm, hh1, hh2, _⟩ := tab_pullback_UMP hg ht hx hy hw
    exact ⟨⟨⟨hm, hhm⟩, hh1, hh2⟩⟩)

/-- Helper for mapHasEqualizer: extract the splitting data via Classical.choice. -/
private noncomputable def mapCorSplit {a : A} {R : a ⟶ a} (hcor : Coreflexive R) :
    PSigma fun c : A => PSigma fun g : c ⟶ a =>
        Map g ∧ g° ≫ g = R ∧ g ≫ g° = Cat.id c :=
  Classical.choice (by
    obtain ⟨c, g, hg, hl, hr⟩ := coreflexive_splits hcor
    exact ⟨⟨c, g, hg, hl, hr⟩⟩)

/-- Helper for mapHasEqualizer: extract the mediating map via Classical.choice. -/
private noncomputable def mapEqLiftData {a b p q : A} {f g : a ⟶ b} {e : p ⟶ a}
    (hf : Map f) (_ : Map g) (he : Map e) (hee : e° ≫ e = dom (f ∩ g)) (he1 : e ≫ e° = Cat.id p)
    (h : q ⟶ a) (hh : Map h) (hcone : h ≫ f = h ≫ g) :
    PSigma fun k : {R : q ⟶ p // Map R} => k.val ≫ e = h :=
  Classical.choice (by
    obtain ⟨k, hk, hke, _⟩ := tab_equalizer_UMP hf he hee he1 hh hcone
    exact ⟨⟨⟨k, hk⟩, hke⟩⟩)

/-- §2.212 pullback: tabulation of f≫g° gives the pullback of f,g in Map(𝒜). -/
noncomputable def mapHasPullback
    {a b c : MapObj A} (f : @Cat.Hom _ (mapCat (𝒜 := A)) a c)
    (g : @Cat.Hom _ (mapCat (𝒜 := A)) b c) :
    @HasPullback (MapObj A) (mapCat (𝒜 := A)) a b c f g := by
  have fgR : @Freyd.Alg.Tabular A TabularAllegory.toAllegory _ _ (f.val ≫ g.val°) :=
    @TabularAllegory.tabular A _ _ _ (f.val ≫ g.val°)
  -- Tabular is a Prop ∃; use PSigma + Classical.choice to extract witnesses into Type-valued goal.
  have fgR_N : Nonempty (PSigma fun p : A =>
      PSigma fun π₁ : p ⟶ _ => PSigma fun π₂ : p ⟶ _ =>
      Tabulates π₁ π₂ (f.val ≫ g.val°)) := by
    obtain ⟨p, π₁, π₂, ht⟩ := fgR; exact ⟨⟨p, π₁, π₂, ht⟩⟩
  obtain ⟨p, π₁, π₂, ht⟩ := Classical.choice fgR_N
  have hπ₁ : Map π₁ := ht.1
  have hπ₂ : Map π₂ := ht.2.1
  -- Derive cone equation π₁≫f = π₂≫g directly from tabulation (not via retraction).
  -- π₂°≫π₁ = g°°≫f° = g≫f° (recip of ht.2.2.1 : f≫g° = π₁°≫π₂).
  have hrecip : π₂° ≫ π₁ = g.val ≫ f.val° := by
    have h := congrArg Allegory.recip ht.2.2.1
    simp [Allegory.recip_comp, Allegory.recip_recip] at h; exact h.symm
  -- Derive cone eq π₁≫f = π₂≫g from tabulation.
  -- Step: (π₂≫g)°≫(π₁≫f) = g°≫(π₂°≫π₁)≫f = g°≫g≫f°≫f ⊑ id (via Simple g, Simple f).
  have hlt1 : (π₂ ≫ g.val)° ≫ (π₁ ≫ f.val) ⊑ Cat.id c := by
    have heq : (π₂ ≫ g.val)° ≫ (π₁ ≫ f.val) = (g.val° ≫ g.val) ≫ (f.val° ≫ f.val) := by
      rw [Allegory.recip_comp]; simp only [Cat.assoc]; rw [← Cat.assoc π₂°, hrecip]
      simp [Cat.assoc]
    rw [heq]
    exact le_trans (comp_mono_right g.property.2 _)
      (by rw [Cat.id_comp]; exact f.property.2)
  have hle1 : π₁ ≫ f.val ⊑ π₂ ≫ g.val := by
    have hent' : Cat.id p ⊑ (π₂ ≫ g.val) ≫ (π₂ ≫ g.val)° := by
      have h := entire_comp hπ₂.1 g.property.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _
    have h1 : π₁ ≫ f.val ⊑ ((π₂ ≫ g.val) ≫ (π₂ ≫ g.val)°) ≫ (π₁ ≫ f.val) := by
      have := comp_mono_right hent' (π₁ ≫ f.val); rwa [Cat.id_comp] at this
    have h2 : ((π₂ ≫ g.val) ≫ (π₂ ≫ g.val)°) ≫ (π₁ ≫ f.val) ⊑ π₂ ≫ g.val := by
      rw [Cat.assoc]
      exact le_trans (comp_mono_left _ hlt1) (by rw [Cat.comp_id]; exact le_refl _)
    exact le_trans h1 h2
  have hlt2 : (π₁ ≫ f.val)° ≫ (π₂ ≫ g.val) ⊑ Cat.id c := by
    have heq : (π₁ ≫ f.val)° ≫ (π₂ ≫ g.val) = (f.val° ≫ f.val) ≫ (g.val° ≫ g.val) := by
      rw [Allegory.recip_comp]; simp only [Cat.assoc]; rw [← Cat.assoc π₁°, ← ht.2.2.1]
      simp [Cat.assoc]
    rw [heq]
    exact le_trans (comp_mono_right f.property.2 _)
      (by rw [Cat.id_comp]; exact g.property.2)
  have hle2 : π₂ ≫ g.val ⊑ π₁ ≫ f.val := by
    have hent' : Cat.id p ⊑ (π₁ ≫ f.val) ≫ (π₁ ≫ f.val)° := by
      have h := entire_comp hπ₁.1 f.property.1; rw [Entire, dom] at h; exact h ▸ inter_lb_right _ _
    have h1 : π₂ ≫ g.val ⊑ ((π₁ ≫ f.val) ≫ (π₁ ≫ f.val)°) ≫ (π₂ ≫ g.val) := by
      have := comp_mono_right hent' (π₂ ≫ g.val); rwa [Cat.id_comp] at this
    have h2 : ((π₁ ≫ f.val) ≫ (π₁ ≫ f.val)°) ≫ (π₂ ≫ g.val) ⊑ π₁ ≫ f.val := by
      rw [Cat.assoc]
      exact le_trans (comp_mono_left _ hlt2) (by rw [Cat.comp_id]; exact le_refl _)
    exact le_trans h1 h2
  have hcone_eq : π₁ ≫ f.val = π₂ ≫ g.val := le_antisymm hle1 hle2
  -- Build the HasPullback. tab_pullback_UMP returns a Prop ∃; use PSigma + Classical.choice.
  -- Access ALL cone fields via @Cone.fieldName with explicit Cat to avoid Lean 4's Cat
  -- re-synthesis in structure projections. Even explicit lambda type annotation doesn't prevent it.
  let cpt  := fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
    @Cone.pt  (MapObj A) (mapCat (𝒜 := A)) a b c f g cone
  let cπ₁ := fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
    @Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone
  let cπ₂ := fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
    @Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone
  let cw   := fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
    congrArg Subtype.val (@Cone.w (MapObj A) (mapCat (𝒜 := A)) a b c f g cone)
  exact @HasPullback.mk (MapObj A) (mapCat (𝒜 := A)) a b c f g
    (@Cone.mk (MapObj A) (mapCat (𝒜 := A)) a b c f g p ⟨π₁, hπ₁⟩ ⟨π₂, hπ₂⟩ (mapHom_ext hcone_eq))
    (fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
       mapLiftData f.property g.property ht (cpt cone) (cπ₁ cone).val (cπ₂ cone).val
         (cπ₁ cone).property (cπ₂ cone).property (cw cone) |>.1)
    (fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
       mapHom_ext (mapLiftData f.property g.property ht (cpt cone) (cπ₁ cone).val (cπ₂ cone).val
         (cπ₁ cone).property (cπ₂ cone).property (cw cone) |>.2.1))
    (fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g) =>
       mapHom_ext (mapLiftData f.property g.property ht (cpt cone) (cπ₁ cone).val (cπ₂ cone).val
         (cπ₁ cone).property (cπ₂ cone).property (cw cone) |>.2.2))
    (fun (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g)
         (u : @Cat.Hom _ (mapCat (𝒜 := A)) (cpt cone) p)
         (hu1 : @Cat.comp _ (mapCat (𝒜 := A)) _ _ _ u ⟨π₁, hπ₁⟩ = cπ₁ cone)
         (hu2 : @Cat.comp _ (mapCat (𝒜 := A)) _ _ _ u ⟨π₂, hπ₂⟩ = cπ₂ cone) =>
       let hU1 := congrArg Subtype.val hu1
       let hU2 := congrArg Subtype.val hu2
       let dLift := mapLiftData f.property g.property ht (cpt cone)
                      (cπ₁ cone).val (cπ₂ cone).val
                      (cπ₁ cone).property (cπ₂ cone).property (cw cone)
       (by obtain ⟨hm, hhm, hh1, hh2, uniq⟩ := tab_pullback_UMP g.property ht
               (cπ₁ cone).property (cπ₂ cone).property (cw cone)
           -- dLift.1.val satisfies the same conditions, so uniq gives dLift.1.val = hm
           have hdL : dLift.1.val = hm := uniq dLift.1.val dLift.1.property dLift.2.1 dLift.2.2
           exact mapHom_ext (hdL ▸ uniq u.val u.property hU1 hU2)))

/-- §2.212: Map(𝒜) has all pullbacks. -/
noncomputable instance mapHasPullbacks :
    @HasPullbacks (MapObj A) (mapCat (𝒜 := A)) :=
  @HasPullbacks.mk (MapObj A) (mapCat (𝒜 := A)) (fun {_ _ _} f g => mapHasPullback f g)

/-- **§2.212 BRIDGE (pullback leg coreflexive)**: for ANY pullback `pb` of maps `f : a→c`,
    `g : b→c` in Map(𝒜), the first-leg coreflexive equals the relational `dom (f g°)`:

        `pb.cone.π₁° ≫ pb.cone.π₁ = dom (f.val ≫ g.val°)`.

    The choice-extracted projection of `mapHasPullback` does not reduce definitionally; we
    bridge it to the canonical tabulation `(π₁,π₂)` of `f g°` via the pullback-UNIQUENESS
    comparison iso `v : pb.pt → p` (`v ≫ π₁ = pb.π₁`, with map inverse `u`), then transport
    `tab_leg_dom` across it using `map_retr_leg` (`v°≫v = id`). -/
theorem mapPullback_leg_corOf {a b c : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a c) (g : @Cat.Hom _ (mapCat (𝒜 := A)) b c)
    (pb : @HasPullback (MapObj A) (mapCat (𝒜 := A)) a b c f g) :
    (@Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g
        (@HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb)).val° ≫
      (@Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g
        (@HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb)).val
      = dom (f.val ≫ g.val°) := by
  -- Cone-field accessors (lambda-wrapped to keep the explicit mapCat instance).
  let C := @HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb
  let cpt : MapObj A := @Cone.pt _ (mapCat (𝒜 := A)) a b c f g C
  let pbπ₁ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt a := @Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g C
  let pbπ₂ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt b := @Cone.π₂ _ (mapCat (𝒜 := A)) a b c f g C
  show pbπ₁.val° ≫ pbπ₁.val = dom (f.val ≫ g.val°)
  -- Canonical tabulation (p, π₁, π₂) of f g°.
  have fgR : @Freyd.Alg.Tabular A TabularAllegory.toAllegory _ _ (f.val ≫ g.val°) :=
    @TabularAllegory.tabular A _ _ _ (f.val ≫ g.val°)
  have fgR_N : Nonempty (PSigma fun p : A =>
      PSigma fun π₁ : p ⟶ _ => PSigma fun π₂ : p ⟶ _ =>
      Tabulates π₁ π₂ (f.val ≫ g.val°)) := by
    obtain ⟨p, π₁, π₂, ht⟩ := fgR; exact ⟨⟨p, π₁, π₂, ht⟩⟩
  obtain ⟨p, π₁, π₂, ht⟩ := Classical.choice fgR_N
  -- v : pb.pt → p from the tabulation UMP, with v.val ≫ π₁ = pbπ₁, v.val ≫ π₂ = pbπ₂.
  have hcw : pbπ₁.val ≫ f.val = pbπ₂.val ≫ g.val :=
    congrArg Subtype.val (@Cone.w _ (mapCat (𝒜 := A)) a b c f g C)
  obtain ⟨hm, hm_map, hm1, hm2, _⟩ :=
    tab_pullback_UMP g.property ht pbπ₁.property pbπ₂.property hcw
  -- Cone over (f,g) with apex p (cone eq from tab_pullback_cone'); u := pb.lift of it.
  let cone0 : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g :=
    @Cone.mk (MapObj A) (mapCat (𝒜 := A)) a b c f g p ⟨π₁, ht.1⟩ ⟨π₂, ht.2.1⟩
      (mapHom_ext (tab_pullback_cone' f.property g.property ht))
  let u : @Cat.Hom _ (mapCat (𝒜 := A)) p cpt :=
    @HasPullback.lift _ (mapCat (𝒜 := A)) a b c f g pb cone0
  have hu1 : u.val ≫ pbπ₁.val = π₁ :=
    congrArg Subtype.val (@HasPullback.lift_fst _ (mapCat (𝒜 := A)) a b c f g pb cone0)
  have hu2 : u.val ≫ pbπ₂.val = π₂ :=
    congrArg Subtype.val (@HasPullback.lift_snd _ (mapCat (𝒜 := A)) a b c f g pb cone0)
  -- u ≫ v = id_p, by tabulation joint-monicity (both u≫v and id agree after π₁, π₂).
  have huv_alg : u.val ≫ hm = Cat.id p := by
    apply tabulation_UP_unique ht (map_comp u.property hm_map) (id_is_map_local p)
    · rw [Cat.assoc, show hm ≫ π₁ = pbπ₁.val from hm1, hu1, Cat.id_comp]
    · rw [Cat.assoc, show hm ≫ π₂ = pbπ₂.val from hm2, hu2, Cat.id_comp]
  -- hm°≫hm = id_p via map_retr_leg (retraction u.val ≫ hm = id_p).
  have hvleg : hm° ≫ hm = Cat.id p := map_retr_leg hm_map huv_alg
  -- pbπ₁.val = hm ≫ π₁ (hm1); transport tab_leg_dom across hm°≫hm = id.
  calc pbπ₁.val° ≫ pbπ₁.val = (hm ≫ π₁)° ≫ (hm ≫ π₁) := by rw [show pbπ₁.val = hm ≫ π₁ from hm1.symm]
    _ = π₁° ≫ (hm° ≫ hm) ≫ π₁ := by rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ = π₁° ≫ Cat.id p ≫ π₁ := by rw [show hm° ≫ hm = Cat.id p from hvleg]
    _ = π₁° ≫ π₁ := by rw [Cat.id_comp]
    _ = dom (f.val ≫ g.val°) := tab_leg_dom ht

/-- **§2.147 BRIDGE (pullback cross-term)**: for ANY pullback `pb` of maps `f : a→c`,
    `g : b→c` in Map(𝒜), the cross composite of the legs equals the relational `f ≫ g°`:

        `pb.cone.π₁° ≫ pb.cone.π₂ = f.val ≫ g.val°`.

    Same comparison-iso transport as `mapPullback_leg_corOf`, but reads off the cross term
    (`π₁°≫π₂ = f g°` is the very tabulation equation) rather than the first-leg coreflexive. -/
theorem mapPullback_cross {a b c : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a c) (g : @Cat.Hom _ (mapCat (𝒜 := A)) b c)
    (pb : @HasPullback (MapObj A) (mapCat (𝒜 := A)) a b c f g) :
    (@Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g
        (@HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb)).val° ≫
      (@Cone.π₂ _ (mapCat (𝒜 := A)) a b c f g
        (@HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb)).val
      = f.val ≫ g.val° := by
  let C := @HasPullback.cone _ (mapCat (𝒜 := A)) a b c f g pb
  let cpt : MapObj A := @Cone.pt _ (mapCat (𝒜 := A)) a b c f g C
  let pbπ₁ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt a := @Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g C
  let pbπ₂ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt b := @Cone.π₂ _ (mapCat (𝒜 := A)) a b c f g C
  show pbπ₁.val° ≫ pbπ₂.val = f.val ≫ g.val°
  have fgR : @Freyd.Alg.Tabular A TabularAllegory.toAllegory _ _ (f.val ≫ g.val°) :=
    @TabularAllegory.tabular A _ _ _ (f.val ≫ g.val°)
  have fgR_N : Nonempty (PSigma fun p : A =>
      PSigma fun π₁ : p ⟶ _ => PSigma fun π₂ : p ⟶ _ =>
      Tabulates π₁ π₂ (f.val ≫ g.val°)) := by
    obtain ⟨p, π₁, π₂, ht⟩ := fgR; exact ⟨⟨p, π₁, π₂, ht⟩⟩
  obtain ⟨p, π₁, π₂, ht⟩ := Classical.choice fgR_N
  have hcw : pbπ₁.val ≫ f.val = pbπ₂.val ≫ g.val :=
    congrArg Subtype.val (@Cone.w _ (mapCat (𝒜 := A)) a b c f g C)
  obtain ⟨hm, hm_map, hm1, hm2, _⟩ :=
    tab_pullback_UMP g.property ht pbπ₁.property pbπ₂.property hcw
  let cone0 : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g :=
    @Cone.mk (MapObj A) (mapCat (𝒜 := A)) a b c f g p ⟨π₁, ht.1⟩ ⟨π₂, ht.2.1⟩
      (mapHom_ext (tab_pullback_cone' f.property g.property ht))
  let u : @Cat.Hom _ (mapCat (𝒜 := A)) p cpt :=
    @HasPullback.lift _ (mapCat (𝒜 := A)) a b c f g pb cone0
  have hu1 : u.val ≫ pbπ₁.val = π₁ :=
    congrArg Subtype.val (@HasPullback.lift_fst _ (mapCat (𝒜 := A)) a b c f g pb cone0)
  have hu2 : u.val ≫ pbπ₂.val = π₂ :=
    congrArg Subtype.val (@HasPullback.lift_snd _ (mapCat (𝒜 := A)) a b c f g pb cone0)
  have huv_alg : u.val ≫ hm = Cat.id p := by
    apply tabulation_UP_unique ht (map_comp u.property hm_map) (id_is_map_local p)
    · rw [Cat.assoc, show hm ≫ π₁ = pbπ₁.val from hm1, hu1, Cat.id_comp]
    · rw [Cat.assoc, show hm ≫ π₂ = pbπ₂.val from hm2, hu2, Cat.id_comp]
  have hvleg : hm° ≫ hm = Cat.id p := map_retr_leg hm_map huv_alg
  calc pbπ₁.val° ≫ pbπ₂.val = (hm ≫ π₁)° ≫ (hm ≫ π₂) := by
        rw [show pbπ₁.val = hm ≫ π₁ from hm1.symm, show pbπ₂.val = hm ≫ π₂ from hm2.symm]
    _ = π₁° ≫ (hm° ≫ hm) ≫ π₂ := by rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ = π₁° ≫ Cat.id p ≫ π₂ := by rw [show hm° ≫ hm = Cat.id p from hvleg]
    _ = π₁° ≫ π₂ := by rw [Cat.id_comp]
    _ = f.val ≫ g.val° := ht.2.2.1.symm

/-! ### §2.212  HasBinaryProducts (MapObj A)

  Product a×b = pullback over the terminal (unit). -/

noncomputable instance mapHasBinaryProducts :
    @HasBinaryProducts (MapObj A) (mapCat (𝒜 := A)) :=
  -- Use term-mode let bindings with fully explicit types to avoid Cat synthesis issues.
  let trm := @HasTerminal.one _ (mapCat (𝒜 := A)) mapHasTerminal
  let t    := fun (a : MapObj A) => @HasTerminal.trm _ (mapCat (𝒜 := A)) mapHasTerminal a
  let getPB := fun (a b : MapObj A) => mapHasPullback (t a) (t b)
  let getC  := fun (a b : MapObj A) =>
    @HasPullback.cone (MapObj A) (mapCat (𝒜 := A)) a b trm (t a) (t b) (getPB a b)
  let getCpt := fun (a b : MapObj A) =>
    @Cone.pt (MapObj A) (mapCat (𝒜 := A)) a b trm (t a) (t b) (getC a b)
  let getCπ₁ := fun (a b : MapObj A) =>
    @Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) a b trm (t a) (t b) (getC a b)
  let getCπ₂ := fun (a b : MapObj A) =>
    @Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a b trm (t a) (t b) (getC a b)
  -- Cone over terminal: f≫t(a) = g≫t(b) holds by terminal uniqueness
  let mkCone := fun (X a b : MapObj A) (f : @Cat.Hom _ (mapCat (𝒜 := A)) X a)
                    (g : @Cat.Hom _ (mapCat (𝒜 := A)) X b) =>
      @Cone.mk (MapObj A) (mapCat (𝒜 := A)) a b trm (t a) (t b) X f g
        (@HasTerminal.uniq _ (mapCat (𝒜 := A)) mapHasTerminal _ _ _)
  @HasBinaryProducts.mk (MapObj A) (mapCat (𝒜 := A))
    (fun a b => getCpt a b)
    (fun {a b} => getCπ₁ a b)
    (fun {a b} => getCπ₂ a b)
    (fun {X a b} f g => @HasPullback.lift _ (mapCat (𝒜 := A)) _ _ _ _ _ (getPB a b) (mkCone X a b f g))
    (fun {X a b} f g => @HasPullback.lift_fst _ (mapCat (𝒜 := A)) _ _ _ _ _ (getPB a b) (mkCone X a b f g))
    (fun {X a b} f g => @HasPullback.lift_snd _ (mapCat (𝒜 := A)) _ _ _ _ _ (getPB a b) (mkCone X a b f g))
    (fun {X a b} f g h hf hg =>
       @HasPullback.lift_uniq _ (mapCat (𝒜 := A)) _ _ _ _ _ (getPB a b) (mkCone X a b f g) h hf hg)

/-! ### §2.212  HasEqualizers (MapObj A)

  Equalizer of f,g : a→b = splitting of dom(f∩g). -/

noncomputable def mapHasEqualizer
    {a b : MapObj A} (f g : @Cat.Hom _ (mapCat (𝒜 := A)) a b) :
    @HasEqualizer (MapObj A) (mapCat (𝒜 := A)) a b f g :=
  -- Extract splitting data using Classical.choice (Prop ∃ → Type data)
  let splt   := mapCorSplit (dom_coreflexive (f.val ∩ g.val))
  let p      := splt.1
  let e      := splt.2.1
  let he_map := splt.2.2.1
  let hee_l  := splt.2.2.2.1
  let hee_r  := splt.2.2.2.2
  let hcone_eq : e ≫ f.val = e ≫ g.val := tab_equalizer_cone f.property g.property hee_l hee_r
  -- Build the equalizer cone in mapCat (explicit Cat everywhere)
  let eqCone : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g :=
    @EqualizerCone.mk (MapObj A) (mapCat (𝒜 := A)) a b f g p ⟨e, he_map⟩ (mapHom_ext hcone_eq)
  -- Helper to extract underlying allegory data from a mapCat EqualizerCone
  let cMap := fun (c : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g) =>
      @EqualizerCone.map (MapObj A) (mapCat (𝒜 := A)) a b f g c
  let cEq  := fun (c : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g) =>
      @EqualizerCone.eq (MapObj A) (mapCat (𝒜 := A)) a b f g c
  -- liftFn: for each cone c, use Classical.choice to pick the mediating map
  let liftFn := fun (c : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g) =>
      mapEqLiftData f.property g.property he_map hee_l hee_r
        (cMap c).val (cMap c).property (congrArg Subtype.val (cEq c)) |>.1
  -- fac: (liftFn c) ≫ eqCone.map = c.map as mapCat hom equation
  let facFn  := fun (c : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g) =>
      mapHom_ext
        (mapEqLiftData f.property g.property he_map hee_l hee_r
          (cMap c).val (cMap c).property (congrArg Subtype.val (cEq c)) |>.2)
  -- uniqFn: m ≫ eqCone.map = c.map → m = liftFn c
  let uniqFn := fun (c : @EqualizerCone (MapObj A) (mapCat (𝒜 := A)) a b f g)
      (m : @Cat.Hom _ (mapCat (𝒜 := A))
             (@EqualizerCone.dom (MapObj A) (mapCat (𝒜 := A)) a b f g c) p)
      (hm : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) _ _ _
              m (@EqualizerCone.map (MapObj A) (mapCat (𝒜 := A)) a b f g eqCone) =
            @EqualizerCone.map (MapObj A) (mapCat (𝒜 := A)) a b f g c) => by
      obtain ⟨_, _, _, uniq⟩ := tab_equalizer_UMP f.property he_map hee_l hee_r
        (cMap c).property (congrArg Subtype.val (cEq c))
      let kd := mapEqLiftData f.property g.property he_map hee_l hee_r
                  (cMap c).val (cMap c).property (congrArg Subtype.val (cEq c))
      have hdL : kd.1.val = _ := uniq kd.1.val kd.1.property kd.2
      exact mapHom_ext (hdL ▸ uniq m.val m.property (congrArg Subtype.val hm))
  @HasEqualizer.mk (MapObj A) (mapCat (𝒜 := A)) a b f g eqCone liftFn facFn uniqFn

/-- §2.212: Map(𝒜) has all equalizers. -/
noncomputable instance mapHasEqualizers :
    @HasEqualizers (MapObj A) (mapCat (𝒜 := A)) :=
  @HasEqualizers.mk (MapObj A) (mapCat (𝒜 := A))
    (fun _ _ f g => mapHasEqualizer f g)

/-! ### §2.212  HasImages (MapObj A)

  image(f : a→b) = splitting of dom(f°) : b→b.
  Splitting e : p→b satisfies e°≫e = dom(f°), e≫e° = id_p.

  Allows: (e,e) tabulates e°≫e. Apply tab UP with x=y=f (Map a→b):
    need f°≫f ⊑ e°≫e = dom(f°). Since Simple f: f°≫f ⊑ id_b, and f°≫f ⊑ f°≫f,
    so f°≫f ⊑ id_b ∩ f°≫f = dom(f°). ✓

  Minimality: if Map m:q→b allows f via Map k:a→q with k≫m=f, then
    f°≫f = m°≫k°≫k≫m ⊑ m°≫m (k Simple), so e°≫e = dom(f°) ⊑ m°≫m.
    Define h := e≫m° : p→q.
    Simple h: m≫e°≫e≫m° ⊑ m≫m°≫m≫m° ⊑ id (Simple m).
    Entire h: id_p = e≫e° ⊑ e≫m°≫m≫e° (via e°≫e ⊑ m°≫m).
    h≫m = e≫m°≫m = e (since e = e≫e°≫e ⊑ e≫m°≫m and e≫m°≫m ⊑ e≫id = e). ✓ -/

-- Monic maps in MapCat are retracts: m≫m° = id.
-- Uses q : A (not MapObj A) to avoid Cat diamond on instance inference.
private theorem map_monic_retract {q : A} {a : MapObj A}
    {m : q ⟶ a} (hm : Map m)
    (hm_monic : @Monic (MapObj A) (mapCat (𝒜 := A)) q a ⟨m, hm⟩)
    (hss : Map (m ≫ m°)) (hloop : m ≫ m° ≫ m = m) : m ≫ m° = Cat.id q :=
  congrArg Subtype.val
    (hm_monic ⟨m ≫ m°, hss⟩ ⟨Cat.id q, id_is_map_local q⟩
      (mapHom_ext (by simp only [mapCat, Cat.id_comp, Cat.assoc]; exact hloop)))

/-- **§2.142 (forward)**: a map `m : C → a` that is MONIC in Map(𝒜) is INJECTIVE as a
    relation: `m ≫ m° ⊑ 1_C`.  Constructive kernel-pair argument: tabulate `m ≫ m°` as a
    span `(s, t)`; by `tab_pullback_cone'` it is the kernel pair of `m` (`s ≫ m = t ≫ m`),
    so mapCat-monicity of `m` forces `s = t`, whence `m ≫ m° = s° ≫ t = s° ≫ s ⊑ 1_C`
    (`s` simple).  No retraction or `Map (m≫m°)` assumption is needed (breaks the old circle). -/
theorem mapMonic_inj {C : A} {a : MapObj A}
    {m : C ⟶ a} (hm : Map m)
    (hm_monic : @Monic (MapObj A) (mapCat (𝒜 := A)) C a ⟨m, hm⟩) :
    m ≫ m° ⊑ Cat.id C := by
  obtain ⟨k, s, t, ht⟩ := TabularAllegory.tabular (𝒜 := A) (m ≫ m°)
  have hs : Map s := ht.1
  have htt : Map t := ht.2.1
  -- s ≫ m = t ≫ m  (kernel pair of m), from the tabulation of m ≫ m°° = m ≫ m°.
  have hcone : s ≫ m = t ≫ m := by
    have h := tab_pullback_cone' (a := C) (b := C) (c := a) hm hm
      (π₁ := s) (π₂ := t) (by simpa using ht)
    simpa using h
  -- monic m in mapCat ⟹ s = t (allegory level).
  have hst : s = t := congrArg Subtype.val
    (hm_monic ⟨s, hs⟩ ⟨t, htt⟩ (mapHom_ext hcone))
  -- m ≫ m° = s° ≫ t = s° ≫ s ⊑ 1_C  (s simple).
  calc m ≫ m° = s° ≫ t := ht.2.2.1
    _ = s° ≫ s := by rw [hst]
    _ ⊑ Cat.id C := hs.2

theorem map_retract_monic {a : MapObj A} {p : A}
    {e : p ⟶ a} (he_map : Map e) (hee_r : e ≫ e° = Cat.id p) :
    @Monic (MapObj A) (mapCat (𝒜 := A)) p a ⟨e, he_map⟩ := by
  intro W u v huv
  apply mapHom_ext
  -- congrArg Subtype.val gives the underlying allegory equation since mapCat comp is pointwise
  have heq : u.val ≫ e = v.val ≫ e := congrArg Subtype.val huv
  calc u.val = u.val ≫ e ≫ e° := by rw [hee_r, Cat.comp_id]
    _ = (u.val ≫ e) ≫ e° := (Cat.assoc _ _ _).symm
    _ = (v.val ≫ e) ≫ e° := by rw [heq]
    _ = v.val := by rw [Cat.assoc, hee_r, Cat.comp_id]

-- Extract the image splitting data via Classical.choice (avoids Prop ∃ in Type goal).
private noncomputable def mapImageData {a b : A} (f : {R : a ⟶ b // Map R}) :
    PSigma fun p : A => PSigma fun e : p ⟶ b =>
        Map e ∧ e° ≫ e = dom (f.val°) ∧ e ≫ e° = Cat.id p :=
  Classical.choice (by
    obtain ⟨p, e, he, hl, hr⟩ := coreflexive_splits (dom_coreflexive (f.val°))
    exact ⟨⟨p, e, he, hl, hr⟩⟩)

-- The image subobject of f in mapCat: splitting of dom(f°) is a monic in Map(𝒜).
private noncomputable def mapImage {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b) : @Subobject (MapObj A) (mapCat (𝒜 := A)) b :=
  let d := mapImageData f
  @Subobject.mk (MapObj A) (mapCat (𝒜 := A)) b d.1 ⟨d.2.1, d.2.2.1⟩
    (map_retract_monic d.2.2.1 d.2.2.2.2)

-- Helper for mapIsImage minimality: given S allows f, produce (mapImage f) ≤ S in allegory-land.
theorem mapIsImage_min_aux {a b : MapObj A} {p : A} {e : p ⟶ b}
    (he_map : Map e) (hee_r : e ≫ e° = Cat.id p)
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b)
    (hee_le_f : e° ≫ e ⊑ f.val° ≫ f.val)  -- e°e ⊑ f°f (image below f)
    (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) b)
    (k_S : @Cat.Hom _ (mapCat (𝒜 := A)) a (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) b S))
    (hk_S_eq : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) _ _ _ k_S
        (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b S) = f) :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) b
      (@Subobject.mk (MapObj A) (mapCat (𝒜 := A)) b p ⟨e, he_map⟩ (map_retract_monic he_map hee_r))
      S := by
  let sarr        := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b S).val
  have sarr_map   : Map sarr := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b S).property
  have sarr_entire : Entire sarr := sarr_map.1
  have sarr_simple : Simple sarr := sarr_map.2
  -- sarr ≫ sarr° = id: from Monic S.arr (in MapCat) + Map sarr.
  -- Take u = sarr≫sarr° and v = Cat.id in MapCat, then u ≫ sarr = sarr (by sarr≫sarr°≫sarr = sarr
  -- via Simple/Entire) = v ≫ sarr, so u = v.
  -- Key: sarr ≫ sarr° = Cat.id S.dom. Proof via S.arr.monic in MapCat.
  -- Step 1: sarr ≫ sarr° ≫ sarr = sarr (via le_dom_comp + Entire/Simple).
  have sarr_eq_loop : sarr ≫ sarr° ≫ sarr = sarr :=
    le_antisymm
      (le_trans (comp_mono_left sarr sarr_simple) (by rw [Cat.comp_id]; exact le_refl _))
      (le_trans (le_dom_comp sarr)
        (le_trans (comp_mono_right (inter_lb_right _ _) sarr)
          (by rw [Cat.assoc]; exact le_refl _)))
  -- Step 2: sarr≫sarr° is a Map (used below for monicity argument).
  have sarr_map_ss : Map (sarr ≫ sarr°) :=
    ⟨by -- Entire (sarr≫sarr°): dom(sarr≫sarr°) = id ∩ (sarr≫sarr°)≫(sarr≫sarr°) = id ∩ sarr≫sarr° = id
        rw [Entire, dom, Allegory.recip_comp, Allegory.recip_recip]
        have heq : (sarr ≫ sarr°) ≫ sarr ≫ sarr° = sarr ≫ sarr° := by
          rw [Cat.assoc, ← Cat.assoc sarr° sarr sarr°, ← Cat.assoc sarr (sarr° ≫ sarr) sarr°,
              sarr_eq_loop]
        rw [heq]; exact sarr_entire,
     by -- Simple (sarr≫sarr°): (sarr≫sarr°)≫(sarr≫sarr°) ⊑ id_S.dom.  Reduces to sarr≫sarr° ⊑ id,
        -- which is `mapMonic_inj` applied to S.arr (monic in MapCat) — NO logical circle.
        rw [Simple, Allegory.recip_comp, Allegory.recip_recip]
        have heq : (sarr ≫ sarr°) ≫ sarr ≫ sarr° = sarr ≫ sarr° := by
          rw [Cat.assoc, ← Cat.assoc sarr° sarr sarr°, ← Cat.assoc sarr (sarr° ≫ sarr) sarr°,
              sarr_eq_loop]
        rw [heq]
        exact mapMonic_inj sarr_map (@Subobject.monic (MapObj A) (mapCat (𝒜 := A)) b S)⟩
  -- Step 3: sarr ≫ sarr° = Cat.id S.dom (sarr is a retract).
  -- Use map_monic_retract: S.dom is a plain A-object in the helper, avoiding Cat diamond.
  -- No type annotation to avoid the Cat diamond in the type signature.
  have sarr_retract :=
    map_monic_retract sarr_map
      (@Subobject.monic (MapObj A) (mapCat (𝒜 := A)) b S)
      sarr_map_ss sarr_eq_loop
  have sarr_eq : k_S.val ≫ sarr = f.val := congrArg Subtype.val hk_S_eq
  have hfle : f.val° ≫ f.val ⊑ sarr° ≫ sarr := by
    have hfact : f.val° ≫ f.val = sarr° ≫ k_S.val° ≫ k_S.val ≫ sarr := by
      have h1 : f.val = k_S.val ≫ sarr := sarr_eq.symm
      rw [h1, Allegory.recip_comp]; simp [Cat.assoc]
    rw [hfact]
    have h1 : k_S.val° ≫ k_S.val ≫ sarr ⊑ Cat.id _ ≫ sarr := by
      rw [← Cat.assoc]; exact comp_mono_right k_S.property.2 sarr
    have h2 : sarr° ≫ k_S.val° ≫ k_S.val ≫ sarr ⊑ sarr° ≫ Cat.id _ ≫ sarr :=
      comp_mono_left sarr° h1
    exact le_trans h2 (by rw [Cat.id_comp]; exact le_refl _)
  have hee_sarr : e° ≫ e ⊑ sarr° ≫ sarr := le_trans hee_le_f hfle
  let h_alg : p ⟶ (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) b S) := e ≫ sarr°
  have hh_simple : Simple h_alg := by
    -- h_alg = e ≫ sarr°; h_alg° = sarr ≫ e°; (h_alg°)≫h_alg = (sarr≫e°)≫(e≫sarr°).
    -- Use Simple e (e°≫e ⊑ id_b) and sarr_retract (sarr≫sarr° = id_S.dom).
    rw [Simple, Allegory.recip_comp, Allegory.recip_recip]
    have hs : (e° ≫ e) ≫ sarr° ⊑ sarr° := by
      have h := comp_mono_right he_map.2 sarr°; rw [Cat.id_comp] at h; exact h
    have hchain : (sarr ≫ e°) ≫ h_alg ⊑ sarr ≫ sarr° :=
      calc (sarr ≫ e°) ≫ h_alg = (sarr ≫ e°) ≫ (e ≫ sarr°) := rfl
        _ = sarr ≫ (e° ≫ e) ≫ sarr° := by rw [Cat.assoc, ← Cat.assoc e° e sarr°]
        _ ⊑ sarr ≫ sarr° := comp_mono_left sarr hs
    rw [sarr_retract] at hchain; exact hchain
  have hh_entire : Entire h_alg := by
    -- h_alg = e ≫ sarr°; dom(h_alg) = id ∩ (e≫sarr°)≫(e≫sarr°)°
    -- (e≫sarr°)≫(e≫sarr°)° = e≫sarr°≫sarr≫e°. Need id_p ⊑ this.
    rw [Entire, dom]; apply le_antisymm (inter_lb_left _ _); apply le_inter (le_refl _)
    rw [Allegory.recip_comp, Allegory.recip_recip]
    -- Goal: Cat.id p ⊑ (e≫sarr°)≫(sarr≫e°) = e≫sarr°≫sarr≫e°
    have hrw : (e ≫ sarr°) ≫ (sarr ≫ e°) = e ≫ sarr° ≫ sarr ≫ e° := by simp [Cat.assoc]
    rw [hrw]
    -- e ≫ sarr° ≫ sarr ≫ e° = e ≫ e° (by sarr°≫sarr = Cat.id b from sarr_retract going right,
    -- but sarr°≫sarr ⊑ id not =. We use: id_p = e≫e° directly from hee_r!)
    -- Actually: e≫(sarr°≫sarr)≫e° ⊇ e≫id_b≫e° = e≫e° = id_p.
    -- Wait we need ⊑, not ⊇. Use: e≫sarr°≫sarr≫e° ⊇ e≫e° = id_p via Entire sarr.
    -- sarr_ent_eq : id_S.dom ⊑ sarr≫sarr°. So e≫e° = id_p (from hee_r).
    -- And (e≫sarr°)≫(sarr≫e°) ⊇ e≫e° iff sarr°≫sarr ⊇ id_b.
    -- sarr_ent_eq says id_S.dom ⊑ sarr≫sarr°, NOT id_b ⊑ sarr°≫sarr.
    -- Correct path: use hee_r directly.
    -- id_p = e≫e° (from hee_r). And e≫sarr°≫sarr≫e° ⊇ e≫id_b≫e° = e≫e° = id_p
    -- via Entire sarr: id_S.dom ⊑ sarr≫sarr°, so ... hmm this is for S.dom not b.
    -- Better: sarr°≫sarr ⊑ id_b (Simple) but we need ≥. We have sarr_ent_eq : id ⊑ sarr≫sarr°.
    -- But id_b ⊑ sarr°≫sarr iff sarr°≫sarr = id_b (since ⊑ id too). Actually use:
    -- sarr_retract : sarr≫sarr° = id_S.dom. So sarr°≫sarr°° = sarr°≫sarr ⊑ id_b (Simple).
    -- And id_S.dom = sarr≫sarr° ⊑ sarr≫sarr°≫sarr≫sarr° from id ⊑ sarr°≫sarr? NO.
    -- KEY: e ≫ e° = id_p (hee_r). So we need id_p ⊑ e≫sarr°≫sarr≫e°.
    -- Use: id_p = e≫e° and id_S.dom ⊑ sarr≫sarr° (sarr_ent_eq).
    -- Then: e≫sarr°≫sarr≫e° = ??? We need sarr°≫sarr ≥ id... NO Simple says ≤.
    -- REAL KEY: sarr_retract says sarr≫sarr° = id_S.dom. Then sarr°≫sarr ≥ ???
    -- Actually sarr is a retraction: sarr≫sarr°=id. So sarr° is a section. sarr°≫sarr ≥ id_b
    -- because: sarr≫(sarr°≫sarr)≫sarr° = (sarr≫sarr°)≫(sarr≫sarr°) = id≫id = id.
    -- But (sarr≫sarr°≫sarr)≫sarr° = sarr≫sarr° = id. And sarr°≫sarr ⊑ id. So we need other.
    -- Actually from sarr_retract: sarr≫sarr° = id_S.dom. Since sarr°≫sarr ⊑ id_b (Simple)
    -- and sarr≫(sarr°≫sarr) = (sarr≫sarr°)≫sarr = id_S.dom≫sarr = sarr (by sarr_retract).
    -- Now: sarr°≫sarr ≥ id_b? Apply: sarr° ≫ (sarr ≫ sarr° ≫ sarr) = sarr°≫sarr (by RHS = sarr).
    -- So sarr°≫(sarr≫sarr°)≫sarr = sarr°≫sarr. And (sarr°≫sarr≫sarr°)≫sarr = sarr°≫sarr.
    -- But also (sarr°≫sarr≫sarr°)≫sarr = sarr°≫id_S.dom≫sarr = sarr°≫sarr.
    -- This just gives sarr°≫sarr=sarr°≫sarr. Not helpful.
    -- CONCLUSION: id_b ⊑ sarr°≫sarr NOT provable in general. But we don't need it!
    -- We need id_p ⊑ e≫sarr°≫sarr≫e°. Use hee_r: id_p = e≫e°.
    -- Then: e≫e° ⊑ e≫sarr°≫sarr≫e° via id_b ⊑ sarr°≫sarr? Not available.
    -- ALTERNATIVE: e≫e° = id_p and we need id_p ⊑ e≫sarr°≫sarr≫e°.
    -- id_p = e≫e° ⊑ e≫sarr°≫sarr≫e° iff e° ⊑ sarr°≫sarr≫e° which means e°(e°)° ⊑ sarr°≫sarr
    -- i.e., e°≫e ⊑ sarr°≫sarr. YES that's hee_sarr!
    -- So: id_p = e≫e° and e° ⊑ sarr°≫sarr≫e° iff e°≫(sarr°≫sarr≫e°)° ... this is Entire of e°.
    -- Let me just compute directly:
    -- id_p ⊑ e≫sarr°≫sarr≫e° ← hee_r gives id_p = e≫e°
    -- Need e≫e° ⊑ e≫sarr°≫sarr≫e°, i.e., e° ⊑ sarr°≫sarr≫e° (comp_mono_left e from left).
    -- Actually comp_mono_left e does: from e° ⊑ sarr°≫sarr≫e°, get e≫e° ⊑ e≫sarr°≫sarr≫e°.
    -- But e° ⊑ sarr°≫sarr≫e°? That's: (e°)≫id ⊑ (sarr°≫sarr)≫e°. i.e., comp_mono_right ? e°.
    -- Need id ⊑ sarr°≫sarr. NOT available from Simple.
    -- Different: e° ≫ e ⊑ sarr° ≫ sarr (hee_sarr). Multiply by e° on right:
    -- (e°≫e)≫e° ⊑ (sarr°≫sarr)≫e°. LHS = e°≫(e≫e°) = e°≫id = e°.
    -- RHS = sarr°≫sarr≫e°. So e° ⊑ sarr°≫sarr≫e°. YES!
    have hstep : e° ⊑ sarr° ≫ sarr ≫ e° := by
      have h1 : (e° ≫ e) ≫ e° ⊑ (sarr° ≫ sarr) ≫ e° := comp_mono_right hee_sarr e°
      simp only [Cat.assoc, hee_r, Cat.comp_id] at h1; exact h1
    rw [← hee_r]; exact comp_mono_left e hstep
  have hh_eq : h_alg ≫ sarr = e := by
    show (e ≫ sarr°) ≫ sarr = e
    exact le_antisymm
      (by calc (e ≫ sarr°) ≫ sarr = e ≫ sarr° ≫ sarr := Cat.assoc e sarr° sarr
               _ ⊑ e ≫ Cat.id b := comp_mono_left e sarr_simple
               _ = e := Cat.comp_id e)
      (by calc e = e ≫ (e° ≫ e) := by rw [← Cat.assoc, hee_r, Cat.id_comp]
               _ ⊑ e ≫ (sarr° ≫ sarr) := comp_mono_left e hee_sarr
               _ = (e ≫ sarr°) ≫ sarr := (Cat.assoc e sarr° sarr).symm)
  exact ⟨⟨h_alg, ⟨hh_entire, hh_simple⟩⟩, mapHom_ext hh_eq⟩

-- The image is an image: f allows through it, and it is minimal.
private theorem mapIsImage {a b : MapObj A} (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b) :
    @IsImage (MapObj A) (mapCat (𝒜 := A)) a b f (mapImage f) := by
  let d      := mapImageData f
  let p      : A := d.1
  let e      : p ⟶ b := d.2.1
  let he_map : Map e                   := d.2.2.1
  let hee_l  : e° ≫ e = dom (f.val°) := d.2.2.2.1
  let hee_r  : e ≫ e° = Cat.id p     := d.2.2.2.2
  have htab_e : Tabulates e e (e° ≫ e) :=
    ⟨he_map, he_map, rfl, by rw [Allegory.inter_idem, hee_r]⟩
  have hff_le : f.val° ≫ f.val ⊑ e° ≫ e := by
    rw [hee_l]; exact le_inter f.property.2 (by rw [Allegory.recip_recip]; exact le_refl _)
  obtain ⟨k, hk, hke, _⟩ := tabulation_UP_forward htab_e f.property f.property hff_le
  -- hee_le_f : e°≫e ⊑ f°≫f needed for mapIsImage_min_aux
  have hee_le_f : e° ≫ e ⊑ f.val° ≫ f.val := by
    simp only [hee_l, dom, Allegory.recip_recip]; exact inter_lb_right _ _
  refine ⟨⟨⟨k, hk⟩, mapHom_ext hke⟩, fun S hS => ?_⟩
  obtain ⟨k_S, hk_S_eq⟩ := hS
  exact mapIsImage_min_aux he_map hee_r f hee_le_f S k_S hk_S_eq

noncomputable instance mapHasImages :
    @HasImages (MapObj A) (mapCat (𝒜 := A)) :=
  @HasImages.mk (MapObj A) (mapCat (𝒜 := A))
    (fun {_ _} f => mapImage f) (fun {_ _} f => mapIsImage f)

/-! ### §2.212  PullbacksTransferCovers

  Key algebraic fact: if f:a→c is a cover (id_c ⊑ f°≫f) and (π₁:p→a, π₂:p→b)
  is the tabulation of f≫g°, then π₂ is a cover (id_b ⊑ π₂°≫π₂).
  Proof: π₂°≫π₁ = g≫f° (recip of π₁°≫π₂=f≫g°). Then:
    π₂°≫π₂ ⊇ π₂°≫id_p≫π₂  (trivially)
             = π₂°≫(π₁≫π₁°)≫π₂  (π₁≫π₁°=id_p from Entire π₁)
             = (π₂°≫π₁)≫(π₁°≫π₂)
             = (g≫f°)≫(f≫g°)
             = g≫(f°≫f)≫g°
             ⊇ g≫id_c≫g°  (using id_c ⊑ f°≫f = cover f)
             = g≫g°
             ⊇ id_b  (Entire g, since g is a Map).
  For an ARBITRARY pullback cone: it is isomorphic to the canonical one via a comparison
  map u. We show u is iso (using the UMP in both directions), then use cover_precomp_iso. -/

-- Extract id_c ⊑ f°≫f from Cover f in Map(𝒜)
theorem mapCover_entire {a c : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a c)
    (hcov : @Cover (MapObj A) (mapCat (𝒜 := A)) a c f) :
    Cat.id c ⊑ f.val° ≫ f.val := by
  haveI : @HasImages (MapObj A) (mapCat (𝒜 := A)) := mapHasImages
  -- image of f = splitting of dom(f°); the cover forces image iso
  obtain ⟨p, e, he_map, hee_l, hee_r⟩ := coreflexive_splits (dom_coreflexive (f.val°))
  have htab_e : Tabulates e e (e° ≫ e) :=
    ⟨he_map, he_map, rfl, by rw [Allegory.inter_idem, hee_r]⟩
  have hff_le : f.val° ≫ f.val ⊑ e° ≫ e := by
    rw [hee_l]; exact le_inter f.property.2 (by rw [Allegory.recip_recip]; exact le_refl _)
  obtain ⟨k_f, hk_f, hk_f_eq, _⟩ := tabulation_UP_forward htab_e f.property f.property hff_le
  -- e monic and f factors through e ⟹ e iso (by Cover)
  have he_iso : @IsIso (MapObj A) (mapCat (𝒜 := A)) p c ⟨e, he_map⟩ :=
    hcov ⟨e, he_map⟩ ⟨k_f, hk_f⟩ (map_retract_monic he_map hee_r) (mapHom_ext hk_f_eq)
  obtain ⟨⟨e', he'_map⟩, hee'sub, he'esub⟩ := he_iso
  have he'e_alg : e' ≫ e = Cat.id c := congrArg Subtype.val he'esub
  -- id_c ⊑ e°≫e: from e'≫e=id_c ⟹ e°≫(e')°=id_c ⟹ id_c=e°≫(e')°≫e'≫e ⊑ e°≫id_c≫e=e°≫e
  have hrecip_inv : e° ≫ e'° = Cat.id c := by
    have := congrArg Allegory.recip he'e_alg
    simp [Allegory.recip_comp, recip_id] at this; exact this
  have hid_le : Cat.id c ⊑ e° ≫ e :=
    calc Cat.id c = e° ≫ e'° := hrecip_inv.symm
      _ = e° ≫ e'° ≫ (e' ≫ e) := by rw [he'e_alg, Cat.comp_id]
      _ = e° ≫ (e'° ≫ e') ≫ e := by simp [Cat.assoc]
      _ ⊑ e° ≫ Cat.id p ≫ e := comp_mono_left e° (comp_mono_right he'_map.2 e)
      _ = e° ≫ e := by rw [Cat.id_comp]
  have hff_inter : dom (f.val°) ⊑ f.val° ≫ f.val := by
    simp only [dom, Allegory.recip_recip]; exact inter_lb_right _ _
  have hid_dom : Cat.id c ⊑ dom (f.val°) := hee_l ▸ hid_le
  exact le_trans hid_dom hff_inter

/-- **§2.147 (cover from allegory-entireness)**: a map `x : a → c` of Map(𝒜) with
    `id_c ⊑ x°≫x` (allegory level — equivalently `Entire x°`, §2.147) is a COVER in the
    category sense.  Reason: any monic factor `m` of `x` (with `k≫m = x`) has
    `id_c ⊑ x°≫x ⊑ m°≫m ⊑ id_c`, so `m°≫m = id_c`; `m` monic+Entire forces `m≫m° = id`,
    making `m` iso with inverse `m°`.  (Reused by `mapPullbacksTransferCovers` and the
    §2.217(2) effectiveness bridge.) -/
theorem mapEntire_cover {a c : MapObj A}
    (x : @Cat.Hom _ (mapCat (𝒜 := A)) a c) (hx : Cat.id c ⊑ x.val° ≫ x.val) :
    @Cover (MapObj A) (mapCat (𝒜 := A)) a c x := by
  intro C m k hm_monic hkm
  obtain ⟨m, hm_map⟩ := m
  obtain ⟨k, hk_map⟩ := k
  have hkm_alg : k ≫ m = x.val := congrArg Subtype.val hkm
  have hm_sim : m° ≫ m ⊑ Cat.id c := hm_map.2
  have hm_ent : Cat.id C ⊑ m ≫ m° := map_entire_le hm_map
  have hid_le_mm : Cat.id c ⊑ m° ≫ m := by
    have heq : x.val° ≫ x.val = m° ≫ k° ≫ k ≫ m := by
      rw [← hkm_alg, Allegory.recip_comp]; simp [Cat.assoc]
    have hkk_le : (k° ≫ k) ≫ m ⊑ m := by
      have h := comp_mono_right hk_map.2 m; rwa [Cat.id_comp] at h
    have hstep : m° ≫ k° ≫ k ≫ m ⊑ m° ≫ m := by
      apply comp_mono_left m°; rw [← Cat.assoc]; exact hkk_le
    exact le_trans (heq ▸ hx) hstep
  have hmm_id : m° ≫ m = Cat.id c := le_antisymm hm_sim hid_le_mm
  have hmm'_id : m ≫ m° = Cat.id C :=
    le_antisymm (mapMonic_inj hm_map hm_monic) hm_ent
  have hmo_map : Map (m°) := by
    refine ⟨?_, ?_⟩
    · rw [Entire, dom, Allegory.recip_recip, hmm_id]; exact (Allegory.inter_idem _)
    · rw [Simple, Allegory.recip_recip]; exact hmm'_id ▸ le_refl _
  exact ⟨⟨m°, hmo_map⟩, mapHom_ext hmm'_id, mapHom_ext hmm_id⟩

/-- §2.212: PullbacksTransferCovers for Map(𝒜). -/
noncomputable instance mapPullbacksTransferCovers :
    @PullbacksTransferCovers (MapObj A) (mapCat (𝒜 := A)) :=
  @PullbacksTransferCovers.mk (MapObj A) (mapCat (𝒜 := A)) (by
    intro a b c f g cone hpb hcov_f
    -- Step 1: extract f is cover in the allegory (id_c ⊑ f°≫f)
    have hf_ent : Cat.id b ⊑ f.val° ≫ f.val := mapCover_entire f hcov_f
    -- Step 2: id_b ⊑ cone.π₂.val°≫cone.π₂.val for the CANONICAL tabulation pullback.
    -- First work with the canonical pullback (tabulation of f≫g°).
    obtain ⟨p, π₁, π₂, ht⟩ := TabularAllegory.tabular (𝒜 := A) (f.val ≫ g.val°)
    have hπ₁ : Map π₁ := ht.1
    have hπ₂ : Map π₂ := ht.2.1
    -- Cone equation for the canonical tabulation, derived directly from the tabulation via the
    -- joint-monic form (NO `π≫π°=id` retraction — that fact is FALSE for a generic leg).
    have hcone_can_eq : π₁ ≫ f.val = π₂ ≫ g.val :=
      tab_pullback_cone' f.property g.property ht
    let canon_cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a c b f g :=
      @Cone.mk (MapObj A) (mapCat (𝒜 := A)) a c b f g p ⟨π₁, hπ₁⟩ ⟨π₂, hπ₂⟩ (mapHom_ext hcone_can_eq)
    -- recip of π₁°≫π₂=f≫g°: π₂°≫π₁ = g≫f°
    have hrecip_eq : π₂° ≫ π₁ = g.val ≫ f.val° := by
      have h := congrArg Allegory.recip ht.2.2.1
      simp [Allegory.recip_comp, Allegory.recip_recip] at h; exact h.symm
    -- id_b ⊑ π₂°≫π₂ (canonical pullback π₂ is a cover).  BOOK §2.147: f is a cover ⟹ f° is
    -- entire ⟹ g≫f° is entire (g a map) ⟹ π₂°≫π₁ (= g≫f°) is entire ⟹ π₂° is entire
    -- (`entire_of_comp_entire`) ⟹ π₂ is a cover.  No retraction is used.
    have hcan_π₂_cover : Cat.id c ⊑ π₂° ≫ π₂ := by
      have hfo_ent : Entire f.val° := (cover_iff_recip_entire f.val).mp hf_ent
      have hgfo_ent : Entire (g.val ≫ f.val°) := entire_comp g.property.1 hfo_ent
      have hπ₂π₁_ent : Entire (π₂° ≫ π₁) := hrecip_eq ▸ hgfo_ent
      have hπ₂o_ent : Entire π₂° := entire_of_comp_entire hπ₂π₁_ent
      exact (cover_iff_recip_entire π₂).mpr hπ₂o_ent
    -- Extract cone.pt as cpt_cone via explicit @Cone.pt to avoid Cat diamond in type annotations.
    -- Access cone fields via explicit @Cone.field to avoid Cat re-synthesis (diamond).
    let cpt_cone := @Cone.pt (MapObj A) (mapCat (𝒜 := A)) a c b f g cone
    let cπ₁c := @Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) a c b f g cone
    let cπ₂c := @Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a c b f g cone
    let cwc  := congrArg Subtype.val (@Cone.w (MapObj A) (mapCat (𝒜 := A)) a c b f g cone)
    -- Step 3: the given cone is related to canon_cone by a comparison iso.
    -- From hpb (given cone IsPullback), apply it to canon_cone to get u: p→cone.pt.
    obtain ⟨u_sub, ⟨hu1, hu2⟩, hu_uniq⟩ := hpb canon_cone
    -- u_sub : p → cpt_cone in MapCat; hu1 : u_sub ≫ cπ₁c = ⟨π₁,_⟩; hu2 : u_sub ≫ cπ₂c = ⟨π₂,_⟩
    -- From tab_pullback_UMP applied to cone as source: v: cpt_cone→p
    obtain ⟨hv, hv_map, hv1, hv2, hv_uniq⟩ := tab_pullback_UMP g.property ht
      cπ₁c.property cπ₂c.property cwc
    -- Name the mapCat morphisms explicitly to avoid Cat diamond in ⟨...⟩ constructor
    let hv_sub : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) cpt_cone p :=
      Subtype.mk hv hv_map
    let hπ₂_sub : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) p c :=
      Subtype.mk π₂ hπ₂
    let u_sub' : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) p cpt_cone :=
      u_sub
    -- u_sub' ≫ hv_sub = id_p in MapCat: by tab_pullback_UMP uniqueness applied at canon.pt
    have huv_mapcat : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) _ _ _ u_sub' hv_sub =
        @Cat.id (MapObj A) (mapCat (𝒜 := A)) p := by
      have heq1 : (u_sub.val ≫ hv) ≫ π₁ = π₁ := by
        rw [Cat.assoc, hv1]; exact congrArg Subtype.val hu1
      have heq2 : (u_sub.val ≫ hv) ≫ π₂ = π₂ := by
        rw [Cat.assoc, hv2]; exact congrArg Subtype.val hu2
      exact mapHom_ext (tabulation_UP_unique ht (map_comp u_sub.property hv_map) (id_is_map_local p)
        (heq1.trans (Cat.id_comp π₁).symm) (heq2.trans (Cat.id_comp π₂).symm))
    -- hv_sub ≫ u_sub = id_{cone.pt} in MapCat: from u_sub having right-inverse hv_sub.
    -- Proof: u_sub.val ≫ hv = Cat.id p (from huv_mapcat) ⟹
    --   u_sub.val ≫ (hv ≫ u_sub.val) = Cat.id p ≫ u_sub.val = u_sub.val = u_sub.val ≫ Cat.id cone.pt.
    --   u_sub.val is monic (has retraction hv with u_sub.val ≫ hv = Cat.id p? NO: that's HUV direction).
    -- Actually: hv has LEFT inverse u_sub.val (u_sub.val ≫ hv = id_p), so hv is monic.
    --   hv ≫ (u_sub.val ≫ hv) = (hv ≫ u_sub.val) ≫ hv = ??? circular.
    -- Use: Monic hv (since u_sub.val ≫ hv = id_p makes hv monic).
    --   hv ≫ (hv ≫ u_sub.val) = (hv ≫ Cat.id p)? NO: u_sub.val ≫ hv = id_p, not hv ≫ u_sub.val.
    -- hv_sub ≫ u_sub' = id_{cpt_cone}: by uniqueness in hpb applied at cone.
    -- Underlying allegory: (hv ≫ u_sub.val) ≫ cone.π₁.val = cone.π₁.val (and π₂).
    -- The unique map cone.pt→cone.pt in hpb cone that satisfies the equations must be id.
    have hvu_mapcat : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) _ _ _ hv_sub u_sub' =
        @Cat.id (MapObj A) (mapCat (𝒜 := A)) cpt_cone := by
      -- Prove via the canonical tabulation uniqueness: in the allegory, both hv≫u_sub.val
      -- and id_{cone.pt} are maps cone.pt→cone.pt that split the tabulation diagrams.
      -- We use the map tabulation UMP uniqueness by comparing both against arbitrary X.
      -- Direct: use hpb uniqueness at mapCat level. We apply hpb with d = the cone formed by:
      -- d.pt = cpt_cone (= cone.pt), d.π₁ = cπ₁c, d.π₂ = cπ₂c.
      -- That d IS cone. hpb cone = IsPullback of cone, gives uniqueness for maps cone.pt→cone.pt.
      -- Extract uniqueness part of hpb cone:
      obtain ⟨w_self, ⟨hw_self_1, hw_self_2⟩, huniq_self⟩ := hpb cone
      -- huniq_self : ∀ v : cone.pt → cone.pt in mapCat, v≫cone.π₁=cone.π₁ → v≫cone.π₂=cone.π₂ → v = w_self
      -- Both hv_sub≫u_sub' and id_{cpt_cone} satisfy this; hence they are equal.
      let prod := @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone p cpt_cone hv_sub u_sub'
      let idpt := @Cat.id (MapObj A) (mapCat (𝒜 := A)) cpt_cone
      have hu1v : u_sub.val ≫ cπ₁c.val = π₁ := congrArg Subtype.val hu1
      have hu2v : u_sub.val ≫ cπ₂c.val = π₂ := congrArg Subtype.val hu2
      have hcomp_π₁ : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone cpt_cone a prod cπ₁c = cπ₁c :=
        mapHom_ext (show (hv ≫ u_sub.val) ≫ cπ₁c.val = cπ₁c.val by
          rw [Cat.assoc, hu1v, hv1])
      have hcomp_π₂ : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone cpt_cone c prod cπ₂c = cπ₂c :=
        mapHom_ext (show (hv ≫ u_sub.val) ≫ cπ₂c.val = cπ₂c.val by
          rw [Cat.assoc, hu2v, hv2])
      have hid_π₁ : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone cpt_cone a idpt cπ₁c = cπ₁c :=
        mapHom_ext (Cat.id_comp cπ₁c.val)
      have hid_π₂ : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone cpt_cone c idpt cπ₂c = cπ₂c :=
        mapHom_ext (Cat.id_comp cπ₂c.val)
      exact (huniq_self _ hcomp_π₁ hcomp_π₂).trans (huniq_self _ hid_π₁ hid_π₂).symm
    -- hv_sub is iso with inverse u_sub'
    have h_hv_iso : @IsIso (MapObj A) (mapCat (𝒜 := A)) cpt_cone p hv_sub :=
      ⟨u_sub', hvu_mapcat, huv_mapcat⟩
    -- cπ₂c = hv_sub ≫ hπ₂_sub (from hv2 : hv ≫ π₂ = cπ₂c.val)
    have hπ₂_eq : cπ₂c = @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone p c hv_sub hπ₂_sub :=
      (mapHom_ext hv2).symm
    -- cover_precomp_iso: ⟨π₂, hπ₂⟩ cover and iso ≫ cover ⟹ cone.π₂ cover
    -- First: ⟨π₂, hπ₂⟩ is a cover in Map(𝒜) (from hcan_π₂_cover via cover_iff_recip_entire)
    -- π₂ : p ⟶ c (second tabulation leg); Cover in mapCat = every monic factor is iso.
    have hπ₂_cover : @Cover (MapObj A) (mapCat (𝒜 := A)) p c hπ₂_sub :=
      -- `hπ₂_sub = ⟨π₂, hπ₂⟩`, so `hπ₂_sub.val°≫hπ₂_sub.val = π₂°≫π₂` (defeq); apply the
      -- extracted allegory-entireness ⟹ cover lemma.
      mapEntire_cover hπ₂_sub hcan_π₂_cover
    -- Step 4: cone.π₂ = hv_sub ≫ hπ₂_sub (hπ₂_eq via cπ₂c=cone.π₂) + h_hv_iso ⟹ Cover cone.π₂
    -- cπ₂c = cone.π₂ by definition; rewrite goal Cover cone.π₂ to Cover (hv_sub ≫ hπ₂_sub)
    have hπ₂_eq' : @Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a c b f g cone =
        @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone p c hv_sub hπ₂_sub :=
      hπ₂_eq
    have hcov : @Cover (MapObj A) (mapCat (𝒜 := A)) cpt_cone c
        (@Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt_cone p c hv_sub hπ₂_sub) :=
      @cover_precomp_iso (MapObj A) (mapCat (𝒜 := A)) cpt_cone p c hv_sub h_hv_iso hπ₂_sub hπ₂_cover
    show @Cover (MapObj A) (mapCat (𝒜 := A)) cpt_cone c
        (@Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a c b f g cone)
    rw [hπ₂_eq']; exact hcov)

/-- §2.212: Map(𝒜) is a RegularCategory. -/
noncomputable instance mapRegularCategory :
    @RegularCategory (MapObj A) (mapCat (𝒜 := A)) :=
  @RegularCategory.mk (MapObj A) (mapCat (𝒜 := A))
    mapHasTerminal mapHasBinaryProducts mapHasPullbacks mapHasImages mapPullbacksTransferCovers

/-! ### §2.217(2)  Effectiveness bridge — allegory side

  Freyd §2.169/§2.217(2): if the allegory `A` is EFFECTIVE then every equivalence relation
  of `Map(A)` is the level (kernel pair) of a cover — i.e. `Map(A)` is an EFFECTIVE regular
  category.  The ALLEGORY side of that bridge is purely about splitting: a reflexive
  symmetric idempotent `R : a → a` of `A` (an allegory-level equivalence relation) splits
  via `EffectiveAllegory.split_symmetric_idempotent` as `R = x≫x°`, `x°≫x = id_Q`, with `x`
  a MAP; that map `x : a → Q` is then a COVER of `Map(A)` (`mapEntire_cover`, since
  `id_Q = x°≫x ⊑ x°≫x`).  This `mapEffectivenessSplit` is the constructive core; the
  remaining §2.217(2) gap (see the marker below) is the BinRel↔allegory translation that
  exhibits `R` as the relation underlying a category-level `EquivalenceRelation` and the
  kernel pair of `x` as that relation. -/

/-- **§2.217(2) (allegory-side core)**: in `Map(A)`, the effective splitting of a reflexive
    symmetric idempotent `R : a → a` of `A` IS a COVER.  Given the split data — a map
    `x : a → Q` of `A` with `x ≫ x° = R` and `x° ≫ x = id_Q` (exactly what
    `EffectiveAllegory.split_symmetric_idempotent` produces for an equivalence relation `R`)
    — `x` is a `Cover` in `Map(A)`.  The split is taken as DATA (not via an
    `[EffectiveAllegory A]` instance) to avoid the `Allegory A` diamond between the effective
    structure and the ambient `TabularUnitaryDistributiveAllegory A` (the repo's standard
    workaround, cf. `SplitsSymmIdem` in S2_22).  This packages the effective splitting of an
    allegory-level equivalence relation into the cover/quotient datum the category-level
    `IsEffective` needs. -/
theorem mapEffectivenessSplit {a Q : A} (x : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a Q)
    (hxxId : x.val° ≫ x.val = Cat.id Q) :
    @Cover (MapObj A) (mapCat (𝒜 := A)) a Q x :=
  -- Cover: `mapEntire_cover` needs `id_Q ⊑ x°≫x`; here `x°≫x = id_Q` exactly.
  mapEntire_cover x (hxxId ▸ le_refl (Cat.id Q))  -- `id_Q ⊑ x°≫x` ⟸ `x°≫x = id_Q`

/-! ### §2.217(2)  The BinRel(Map 𝒜) ↔ allegory dictionary

  The crux of §2.217(2) is the translation between a CATEGORY-level binary relation
  `E : BinRel (MapObj A) A A` (a jointly-monic span of maps `colA, colB : src → A`) and its
  underlying ALLEGORY endo `relOf E := colA° ≫ colB : A → A` of `A`.

  CONVENTION NOTE.  `MapObj A` is an `abbrev` for `A`, so the `Cat (MapObj A)` instance `mapCat`
  is NEVER auto-found (Lean unfolds `MapObj A → A` and picks the allegory's `Allegory.toCat`).
  Every `BinRel (MapObj A)` field projection therefore re-synthesizes the wrong `Cat` instance and
  fails with "synthesized instance not defeq".  The fix used throughout this section is to pass
  `mapCat` EXPLICITLY to each projection — packaged once in the accessors `relColA`/`relColB`
  (the underlying allegory legs) and `relColA_map`/`relColB_map` (their `Map` certificates).

  The dictionary then proves (all over a bare `[TabularAllegory A]`):
    • `relOf_le_of_relLe` : `E ⊂ F`  (Map(A) containment)   ⟹  `relOf E ⊑ relOf F`   (allegory);
    • `relOf_reciprocal`  : `relOf (E°) = (relOf E)°`;
    • `relOf_graph`       : `relOf (graph x) = x.val`;
    • `relOf_reflexive`   : the diagonal of `E` ⟹ `Reflexive (relOf E)`;
    • `relOf_symmetric`   : `E ⊂ E°` ⟹ `Symmetric (relOf E)`.

  This reduces an equivalence relation of `Map(A)` to a reflexive symmetric (idempotent) of `A`,
  which `mapIsEffective_of_split` splits to a cover (`mapEffectivenessSplit`) whose level is `E`.
  The two §2.14 bridges are now CLOSED below: `relOf_compose` (`relOf (R⊚S) = relOf R ≫ relOf S`,
  via `mapPullback_cross` + the image cover), `relOf_tabulates`/`relLe_of_relOf_le` (reverse
  containment, via `monicPair_tab_identity` = the §2.141 converse).  These promote
  `Rel(Map A) ≅ A` to the CATEGORY level and yield `mapIsEffective_of_split`/`mapEffectiveRegular`. -/

/-- Underlying allegory leg `colA.val : E.src → a` of a Map(A) relation (instance pinned). -/
@[reducible] def relColA {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    @Cat.Hom A Allegory.toCat (@BinRel.src (MapObj A) (mapCat (𝒜 := A)) a b E) a :=
  (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a b E).val

/-- Underlying allegory leg `colB.val : E.src → b` of a Map(A) relation (instance pinned). -/
@[reducible] def relColB {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    @Cat.Hom A Allegory.toCat (@BinRel.src (MapObj A) (mapCat (𝒜 := A)) a b E) b :=
  (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a b E).val

/-- `relColA E` is a map of `A`. -/
def relColA_map {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) : Map (relColA E) :=
  (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a b E).property

/-- `relColB E` is a map of `A`. -/
def relColB_map {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) : Map (relColB E) :=
  (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a b E).property

/-- The underlying allegory morphism of a category-level relation `E : BinRel (MapObj A) a b`:
    `relOf E = E.colA° ≫ E.colB : a → b` in the allegory `A`.  (`relOf (graph x) = x`, and
    `relOf (E°) = (relOf E)°`.) -/
def relOf {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    @Cat.Hom A Allegory.toCat a b :=
  Allegory.recip (relColA E) ≫ relColB E

/-- **§2.217(2) dictionary (forward, structural)**: a `Map(A)`-containment `E ⊂ F` descends to
    allegory containment `relOf E ⊑ relOf F`.  The witnessing map `h : E.src → F.src` (with
    `h≫F.colA = E.colA`, `h≫F.colB = E.colB`) gives
    `relOf E = (h F.colA)°(h F.colB) = F.colA°(h°h)F.colB ⊑ F.colA° F.colB = relOf F`
    (`h` simple: `h°≫h ⊑ id`). -/
theorem relOf_le_of_relLe {a b : A} {E F : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b}
    (h : @RelLe (MapObj A) (mapCat (𝒜 := A)) a b E F) : relOf E ⊑ relOf F := by
  obtain ⟨⟨hh, hhA, hhB⟩⟩ := h
  have hhA' : hh.val ≫ relColA F = relColA E := congrArg Subtype.val hhA
  have hhB' : hh.val ≫ relColB F = relColB E := congrArg Subtype.val hhB
  show Allegory.recip (relColA E) ≫ relColB E ⊑ Allegory.recip (relColA F) ≫ relColB F
  have hmid : (Allegory.recip hh.val ≫ hh.val) ≫ relColB F ⊑ relColB F := by
    have := comp_mono_right hh.property.2 (relColB F); rwa [Cat.id_comp] at this
  calc Allegory.recip (relColA E) ≫ relColB E
      = Allegory.recip (hh.val ≫ relColA F) ≫ (hh.val ≫ relColB F) := by rw [hhA', hhB']
    _ = Allegory.recip (relColA F) ≫ ((Allegory.recip hh.val ≫ hh.val) ≫ relColB F) := by
          rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ ⊑ Allegory.recip (relColA F) ≫ relColB F := comp_mono_left _ hmid

/-- `relOf (E°) = (relOf E)°`: the reciprocal swaps the columns. -/
theorem relOf_reciprocal {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    relOf (@reciprocal (MapObj A) (mapCat (𝒜 := A)) a b E) = Allegory.recip (relOf E) := by
  show Allegory.recip (relColB E) ≫ relColA E
      = Allegory.recip (Allegory.recip (relColA E) ≫ relColB E)
  rw [Allegory.recip_comp, Allegory.recip_recip]

/-- `relOf (graph x) = x.val` for a Map(A) endo-map `x : a → a`. -/
theorem relOf_graph {a b : A} (x : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a b) :
    relOf (@graph (MapObj A) (mapCat (𝒜 := A)) a b x) = x.val := by
  show Allegory.recip (Cat.id a) ≫ x.val = x.val
  rw [recip_id, Cat.id_comp]

/-- **§2.217(2) dictionary**: `relOf E` is REFLEXIVE given `E`'s diagonal map (the reflexivity
    component of `EquivalenceRelation`, fed through `relColA`/`relColB`). -/
theorem relOf_reflexive {a : A} {E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a a}
    {d : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a
          (@BinRel.src (MapObj A) (mapCat (𝒜 := A)) a a E)}
    (hdA' : d.val ≫ relColA E = Cat.id a) (hdB' : d.val ≫ relColB E = Cat.id a) :
    Reflexive (relOf E) := by
  show Cat.id a ⊑ Allegory.recip (relColA E) ≫ relColB E
  have hmid : (Allegory.recip d.val ≫ d.val) ≫ relColB E ⊑ relColB E := by
    have := comp_mono_right d.property.2 (relColB E); rwa [Cat.id_comp] at this
  calc Cat.id a
      = Allegory.recip (d.val ≫ relColA E) ≫ (d.val ≫ relColB E) := by
          rw [hdA', hdB', recip_id, Cat.id_comp]
    _ = Allegory.recip (relColA E) ≫ ((Allegory.recip d.val ≫ d.val) ≫ relColB E) := by
          rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ ⊑ Allegory.recip (relColA E) ≫ relColB E := comp_mono_left _ hmid

/-- **§2.217(2) dictionary**: `relOf E` is SYMMETRIC given `E ⊂ E°` (the symmetry component of
    `EquivalenceRelation`).  `relOf E ⊑ (relOf E)°` by the forward dictionary + `relOf_reciprocal`;
    reciprocate. -/
theorem relOf_symmetric {a : A} {E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a a}
    (hsym : @RelLe (MapObj A) (mapCat (𝒜 := A)) a a E
              (@reciprocal (MapObj A) (mapCat (𝒜 := A)) a a E)) :
    Symmetric (relOf E) := by
  have h := relOf_le_of_relLe hsym
  rw [relOf_reciprocal] at h
  have := recip_mono h
  rwa [Allegory.recip_recip] at this

/-- Entirety of a map `f`, in the form `id ⊑ f ≫ f°` (the `dom f = id` rewrite). -/
private theorem map_id_le_ffo {x y : A} {f : x ⟶ y} (hf : Map f) : Cat.id x ⊑ f ≫ f° := by
  have h := hf.1; dsimp [Entire, dom] at h; dsimp [le]; rw [h]

/-- **§2.141 converse (tabular)**: a CATEGORICALLY jointly-monic pair of maps `colA, colB : s → a`
    in `Map(A)` satisfies the ALGEBRAIC tabulation identity `colA≫colA° ∩ colB≫colB° = id_s`.
    `⊒ id` is automatic (both legs entire); for `⊑ id` tabulate the symmetric coreflexive-candidate
    `m := colA≫colA° ∩ colB≫colB°` by maps `(u,v)`; from `m ⊑ colA≫colA°`, `m ⊑ colB≫colB°` and
    simplicity of `colA`, `colB` one gets `u≫colX = v≫colX` (X∈{A,B}), so `u = v` by joint-monicity,
    whence `m = u°≫v = u°≫u ⊑ id`. -/
theorem monicPair_tab_identity {a b s : A} {colA : s ⟶ a} {colB : s ⟶ b}
    (hA : Map colA) (hB : Map colB)
    (hmono : @MonicPair (MapObj A) (mapCat (𝒜 := A)) s a b ⟨colA, hA⟩ ⟨colB, hB⟩) :
    colA ≫ colA° ∩ colB ≫ colB° = Cat.id s := by
  -- abbreviation `m` introduced by a definitional `have`.
  obtain ⟨m, hm⟩ : ∃ m, m = colA ≫ colA° ∩ colB ≫ colB° := ⟨_, rfl⟩
  rw [← hm]
  obtain ⟨t, u, v, hu, hv, hmuv, _⟩ := TabularAllegory.tabular m
  -- m = u°≫v, m symmetric ⟹ also v°≫u = m.
  have hmsym : m° = m := by
    rw [hm, Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
        Allegory.recip_recip, Allegory.recip_recip]
  have hvu : v° ≫ u = m := by
    have := congrArg Allegory.recip hmuv
    rw [Allegory.recip_comp, Allegory.recip_recip, hmsym] at this; exact this.symm
  -- For a leg `col` (X-component): `u≫col = v≫col`.  Uses `m ⊑ col≫col°` + `col` simple.
  have leg_eq : ∀ {tgt : A} {col : s ⟶ tgt}, Map col → m ⊑ col ≫ col° → u ≫ col = v ≫ col := by
    intro tgt col hcol hmle
    -- m≫col ⊑ col≫col°≫col ⊑ col (col simple).
    have hstep : m ≫ col ⊑ col := by
      have h1 : m ≫ col ⊑ (col ≫ col°) ≫ col := comp_mono_right hmle col
      have h2 : (col ≫ col°) ≫ col ⊑ col := by
        rw [Cat.assoc]
        have := comp_mono_left col hcol.2; rwa [Cat.comp_id] at this
      exact le_trans h1 h2
    -- v≫col ⊑ (u≫u°)≫(v≫col) = u≫(m≫col) ⊑ u≫col.
    have hle : v ≫ col ⊑ u ≫ col := by
      have h1 : v ≫ col ⊑ (u ≫ u°) ≫ (v ≫ col) := by
        have := comp_mono_right (map_id_le_ffo hu) (v ≫ col); rwa [Cat.id_comp] at this
      have h2 : (u ≫ u°) ≫ (v ≫ col) = u ≫ (m ≫ col) := by rw [hmuv]; simp [Cat.assoc]
      have h3 : u ≫ (m ≫ col) ⊑ u ≫ col := comp_mono_left u hstep
      exact le_trans h1 (le_trans (h2 ▸ le_refl _) h3)
    -- u≫col ⊑ (v≫v°)≫(u≫col) = v≫(m≫col) ⊑ v≫col  (via v°≫u = m).
    have hge : u ≫ col ⊑ v ≫ col := by
      have h1 : u ≫ col ⊑ (v ≫ v°) ≫ (u ≫ col) := by
        have := comp_mono_right (map_id_le_ffo hv) (u ≫ col); rwa [Cat.id_comp] at this
      have h2 : (v ≫ v°) ≫ (u ≫ col) = v ≫ (m ≫ col) := by rw [← hvu]; simp [Cat.assoc]
      have h3 : v ≫ (m ≫ col) ⊑ v ≫ col := comp_mono_left v hstep
      exact le_trans h1 (le_trans (h2 ▸ le_refl _) h3)
    exact le_antisymm hge hle
  have heA : u ≫ colA = v ≫ colA := leg_eq hA (hm ▸ inter_lb_left _ _)
  have heB : u ≫ colB = v ≫ colB := leg_eq hB (hm ▸ inter_lb_right _ _)
  -- joint-monicity (categorical) on the maps u, v : t → s ⟹ u = v.
  have huv : u = v :=
    congrArg Subtype.val (hmono (W := t) ⟨u, hu⟩ ⟨v, hv⟩ (mapHom_ext heA) (mapHom_ext heB))
  -- m = u°≫v = v°≫v; `m ⊑ id` (v simple) and `id ⊑ m` (m entire: both legs entire) ⟹ m = id.
  have hmle_id : m ⊑ Cat.id s := by rw [hmuv, huv]; exact hv.2
  have hid_le_m : Cat.id s ⊑ m := by
    rw [hm]; exact le_inter (map_id_le_ffo hA) (map_id_le_ffo hB)
  exact le_antisymm hmle_id hid_le_m

/-- **§2.217(2) dictionary (tabulation)**: every category-level relation `E : BinRel (Map A) A A`
    TABULATES its underlying allegory endo `relOf E = E.colA°≫E.colB`.  The tabulation identity
    is the `monicPair_tab_identity` translation of the categorical joint-monicity (`isMonicPair`)
    that every `BinRel` carries; hence in `Map(A)` over a tabular allegory a category-level
    relation is exactly a §2.14 tabulation. -/
theorem relOf_tabulates {a b : A} (E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    Tabulates (relColA E) (relColB E) (relOf E) := by
  refine ⟨relColA_map E, relColB_map E, rfl, ?_⟩
  exact monicPair_tab_identity (relColA_map E) (relColB_map E)
    (@BinRel.isMonicPair (MapObj A) (mapCat (𝒜 := A)) a b E)

/-- **§2.217(2) dictionary (REVERSE containment, bridge D)**: allegory containment of the
    underlying relations descends to `Map(A)`-containment, `relOf E ⊑ relOf F ⟹ E ⊂ F`.
    Since `F` tabulates `relOf F` (`relOf_tabulates`), the §2.143 universal property
    (`tabulation_UP_forward`) factors `E`'s columns through `F`'s — exactly a `RelHom E F`. -/
theorem relLe_of_relOf_le {a b : A} {E F : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b}
    (hle : relOf E ⊑ relOf F) : @RelLe (MapObj A) (mapCat (𝒜 := A)) a b E F := by
  obtain ⟨h, hmap, hA, hB⟩ :=
    tabulation_UP_forward (relOf_tabulates F) (relColA_map E) (relColB_map E) hle
  exact ⟨⟨⟨h, hmap⟩, mapHom_ext hA, mapHom_ext hB⟩⟩

/-- **§2.217(2) dictionary (COMPOSITION, bridge C)**: `relOf (R ⊚ S) = relOf R ≫ relOf S`.
    The category-level composite `R ⊚ S` is the IMAGE (cover `e`) of the span over the pullback
    `(π₁,π₂)` of `R.colB, S.colA`.  Two §2.147 facts collapse the image+pullback to a plain
    allegory product: the pullback CROSS-term `π₁°≫π₂ = R.colB≫S.colA°` (`mapPullback_cross`) and
    the image cover identity `e°≫e = id` (`e` a cover-map).  Then
      `relOf R ≫ relOf S = R.colA°≫(R.colB≫S.colA°)≫S.colB = (π₁≫R.colA)°≫(π₂≫S.colB)`
                        `= (e≫(R⊚S).colA)°≫(e≫(R⊚S).colB) = (R⊚S).colA°≫(e°≫e)≫(R⊚S).colB`
                        `= relOf (R ⊚ S)`. -/
theorem relOf_compose {a b c : A}
    (R : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b)
    (S : @BinRel (MapObj A) (mapCat (𝒜 := A)) b c) :
    relOf (@compose (MapObj A) (mapCat (𝒜 := A))
            mapHasBinaryProducts mapHasPullbacks mapHasImages a b c R S)
      = relOf R ≫ relOf S := by
  -- Abbreviations (mapCat composition `cm`; mapCat reciprocal stays the allegory `°` on `.val`).
  let cm := @Cat.comp (MapObj A) (mapCat (𝒜 := A))
  let cB := @BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a b R
  let cA := @BinRel.colA (MapObj A) (mapCat (𝒜 := A)) b c S
  let pb := @HasPullbacks.has (MapObj A) (mapCat (𝒜 := A)) mapHasPullbacks _ _ _ cB cA
  let π₁ := @Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) _ _ _ cB cA pb.cone
  let π₂ := @Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) _ _ _ cB cA pb.cone
  let qA := cm π₁ (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a b R)
  let qB := cm π₂ (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) b c S)
  let span := @pair (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts _ _ _ qA qB
  let img := @image (MapObj A) (mapCat (𝒜 := A)) mapHasImages _ _ span
  let e := @image.lift (MapObj A) (mapCat (𝒜 := A)) mapHasImages _ _ span
  let RS := @compose (MapObj A) (mapCat (𝒜 := A))
              mapHasBinaryProducts mapHasPullbacks mapHasImages a b c R S
  -- (R⊚S) columns are the image-arrow legs (definitional).
  let pfst := @fst (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a c
  let psnd := @snd (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a c
  let iarr := @Subobject.arr (MapObj A) (mapCat (𝒜 := A))
                (@prod (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a c) img
  have hcolA_def : @BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a c RS
      = cm iarr pfst := rfl
  have hcolB_def : @BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a c RS
      = cm iarr psnd := rfl
  -- Image factorization: e ≫ img.arr = span.
  have hfac : cm e iarr = span :=
    @image.lift_fac (MapObj A) (mapCat (𝒜 := A)) mapHasImages _ _ span
  -- Column factorizations through cover `e` (mapCat homs).
  have heA : cm e (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a c RS)
      = qA :=
    calc cm e (cm iarr pfst)
        = cm (cm e iarr) pfst :=
          (@Cat.assoc (MapObj A) (mapCat (𝒜 := A)) _ _ _ _ e iarr pfst).symm
      _ = cm span pfst := by rw [hfac]
      _ = qA := @fst_pair (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts _ _ _ qA qB
  have heB : cm e (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a c RS)
      = qB :=
    calc cm e (cm iarr psnd)
        = cm (cm e iarr) psnd :=
          (@Cat.assoc (MapObj A) (mapCat (𝒜 := A)) _ _ _ _ e iarr psnd).symm
      _ = cm span psnd := by rw [hfac]
      _ = qB := @snd_pair (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts _ _ _ qA qB
  -- Cover `e` is a map with `e°≫e = id` (cover ⟹ `id ⊑ e°≫e`; map ⟹ `e°≫e ⊑ id`).
  have he_cover : @Cover (MapObj A) (mapCat (𝒜 := A)) _ _ e :=
    @image_lift_cover (MapObj A) (mapCat (𝒜 := A)) _ _ span mapHasImages
  have hee_id : e.val° ≫ e.val = Cat.id _ :=
    le_antisymm e.property.2 (mapCover_entire e he_cover)
  -- Pullback cross-term: π₁°≫π₂ = R.colB ≫ S.colA°.
  have hcross : π₁.val° ≫ π₂.val
      = (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a b R).val ≫
        (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) b c S).val° :=
    mapPullback_cross cB cA pb
  -- `.val` of the factorizations heA/heB.
  have heAv : e.val ≫ (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a c RS).val
      = π₁.val ≫ (@BinRel.colA (MapObj A) (mapCat (𝒜 := A)) a b R).val :=
    congrArg Subtype.val heA
  have heBv : e.val ≫ (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) a c RS).val
      = π₂.val ≫ (@BinRel.colB (MapObj A) (mapCat (𝒜 := A)) b c S).val :=
    congrArg Subtype.val heB
  -- The allegory computation (all on `.val`).
  show relOf RS = relOf R ≫ relOf S
  show (relColA RS)° ≫ relColB RS
      = ((relColA R)° ≫ relColB R) ≫ ((relColA S)° ≫ relColB S)
  -- relColX RS = RS.colX.val, relColX R = R.colX.val, etc.  Rewrite via heAv/heBv & hcross.
  have key : (π₁.val ≫ (relColA R)) ° ≫ (π₂.val ≫ (relColB S))
      = (relColA R)° ≫ (relColB R ≫ (relColA S)°) ≫ (relColB S) := by
    rw [Allegory.recip_comp]
    simp only [Cat.assoc]
    rw [← Cat.assoc π₁.val° π₂.val (relColB S), hcross]
    simp only [Cat.assoc]
  calc (relColA RS)° ≫ relColB RS
      = (e.val ≫ relColA RS)° ≫ (e.val ≫ relColB RS) := by
        rw [Allegory.recip_comp]; simp only [Cat.assoc]
        rw [← Cat.assoc e.val° e.val (relColB RS), hee_id, Cat.id_comp]
    _ = (π₁.val ≫ relColA R)° ≫ (π₂.val ≫ relColB S) := by rw [heAv, heBv]
    _ = (relColA R)° ≫ (relColB R ≫ (relColA S)°) ≫ (relColB S) := key
    _ = ((relColA R)° ≫ relColB R) ≫ ((relColA S)° ≫ relColB S) := by
        simp only [Cat.assoc]

/-- A tabulating pair `(u, v)` of maps (`u≫u° ∩ v≫v° = id`) is a `MonicPair` in `Map(A)`.
    Bridges the `.val`-level §2.141 joint-monicity (`tabulates_monic_pair`) to the subtype
    `MonicPair` that a `BinRel (MapObj A)` carries. -/
theorem mapMonicPair_of_tab {a b s : A} {u : s ⟶ a} {v : s ⟶ b}
    (hu : Map u) (hv : Map v) (htab : u ≫ u° ∩ v ≫ v° = Cat.id s) :
    @MonicPair (MapObj A) (mapCat (𝒜 := A)) s a b ⟨u, hu⟩ ⟨v, hv⟩ := by
  intro W f g hfA hfB
  apply mapHom_ext
  refine tabulates_monic_pair hu hv htab f.val g.val f.property g.property
    (congrArg Subtype.val hfA) (congrArg Subtype.val hfB)

/-- **§2.217(2) dictionary (MEET, bridge for R2)**: `relOf (R ⊓ S) = relOf R ∩ relOf S`.
    The §2.14 fact that tabulation respects meets, here for two `BinRel (Map A)` relations.

    `⊑`: `R ⊓ S ⊂ R` and `R ⊓ S ⊂ S` (`intersect_le_left`/`right`); the forward dictionary
    `relOf_le_of_relLe` lowers these to `relOf (R⊓S) ⊑ relOf R, relOf S`, so the meet UMP
    (`le_inter`) gives `relOf (R⊓S) ⊑ relOf R ∩ relOf S`.

    `⊒`: let `m := relOf R ∩ relOf S`; tabulate it by maps `(u,v)` (tabular allegory).  The pair
    is jointly monic, so it assembles a `BinRel (Map A)` table `M` with `relOf M = u°≫v = m`.
    From `m ⊑ relOf R`, `m ⊑ relOf S` the reverse dictionary `relLe_of_relOf_le` gives
    `M ⊂ R`, `M ⊂ S`, hence `M ⊂ R ⊓ S` (`le_intersect`); the forward dictionary lowers this to
    `m = relOf M ⊑ relOf (R⊓S)`. -/
theorem relOf_inter {a b : A}
    (R S : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b) :
    relOf (@intersect (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts mapHasPullbacks a b R S)
      = relOf R ∩ relOf S := by
  apply le_antisymm
  · -- relOf (R⊓S) ⊑ relOf R ∩ relOf S
    exact le_inter
      (relOf_le_of_relLe
        (@intersect_le_left (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts mapHasPullbacks a b R S))
      (relOf_le_of_relLe
        (@intersect_le_right (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts mapHasPullbacks a b R S))
  · -- relOf R ∩ relOf S ⊑ relOf (R⊓S):  tabulate the meet, descend to a BinRel, intersect.
    obtain ⟨s, u, v, hu, hv, hmuv, htab⟩ :=
      TabularAllegory.tabular (𝒜 := A) (relOf R ∩ relOf S)
    -- M : the BinRel table tabulating the allegory meet m = u°≫v.
    let M : @BinRel (MapObj A) (mapCat (𝒜 := A)) a b :=
      @BinRel.mk (MapObj A) (mapCat (𝒜 := A)) a b s ⟨u, hu⟩ ⟨v, hv⟩
        (mapMonicPair_of_tab hu hv htab)
    have hcolAM : relColA M = u := rfl
    have hcolBM : relColB M = v := rfl
    have hrelM : relOf M = relOf R ∩ relOf S := by
      show Allegory.recip (relColA M) ≫ relColB M = relOf R ∩ relOf S
      rw [hcolAM, hcolBM]; exact hmuv.symm
    -- M ⊂ R and M ⊂ S from m ⊑ relOf R, relOf S (reverse dictionary).
    have hMR : @RelLe (MapObj A) (mapCat (𝒜 := A)) a b M R :=
      relLe_of_relOf_le (hrelM ▸ inter_lb_left _ _)
    have hMS : @RelLe (MapObj A) (mapCat (𝒜 := A)) a b M S :=
      relLe_of_relOf_le (hrelM ▸ inter_lb_right _ _)
    -- M ⊂ R ⊓ S, lowered to m ⊑ relOf (R⊓S).
    have hMRS : @RelLe (MapObj A) (mapCat (𝒜 := A)) a b M
        (@intersect (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts mapHasPullbacks a b R S) :=
      @le_intersect (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts mapHasPullbacks a b M R S hMR hMS
    have := relOf_le_of_relLe hMRS
    rwa [hrelM] at this

/-- **§2.217(2) dictionary (IDEMPOTENCY)**: a TRANSITIVE + REFLEXIVE relation `E` of `Map(A)` has
    an idempotent `relOf E`.  `E⊚E ⊂ E` (transitivity) gives `relOf (E⊚E) ⊑ relOf E`; by the
    composition bridge `relOf (E⊚E) = relOf E ≫ relOf E`, so `relOf E ≫ relOf E ⊑ relOf E`.  And
    reflexivity (`id ⊑ relOf E`) gives `relOf E = id ≫ relOf E ⊑ relOf E ≫ relOf E`. -/
theorem relOf_idempotent {a : A} {E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a a}
    (hrefl : Reflexive (relOf E))
    (htrans : @RelLe (MapObj A) (mapCat (𝒜 := A)) a a
                (@compose (MapObj A) (mapCat (𝒜 := A))
                  mapHasBinaryProducts mapHasPullbacks mapHasImages a a a E E) E) :
    relOf E ≫ relOf E = relOf E := by
  -- ⊑ : relOf E ≫ relOf E = relOf (E⊚E) ⊑ relOf E.
  have hle : relOf E ≫ relOf E ⊑ relOf E := by
    have h := relOf_le_of_relLe htrans
    rwa [relOf_compose] at h
  -- ⊒ : relOf E = id ≫ relOf E ⊑ (relOf E ≫ relOf E).
  have hge : relOf E ⊑ relOf E ≫ relOf E := by
    have := comp_mono_right hrefl (relOf E)
    rwa [Cat.id_comp] at this
  exact le_antisymm hle hge

/-- **§2.217(2) — `Map(A)` is EFFECTIVE (core)**: every category-level equivalence relation `E`
    of `Map(A)` is the level of a cover.  Effectiveness of the allegory `A` is supplied as the
    explicit splitting datum `split` (the `EffectiveAllegory.split_symmetric_idempotent` shape),
    passed as DATA to avoid the `Allegory A` diamond between an `[EffectiveAllegory A]` instance
    and the ambient `[TabularUnitaryDistributiveAllegory A]`.

    `E` equiv ⟹ `relOf E` reflexive (`relOf_reflexive`), symmetric (`relOf_symmetric`), idempotent
    (`relOf_idempotent`) ⟹ `split` gives a map `x` with `x≫x° = relOf E`, `x°≫x = id` ⟹ `x` is a
    COVER (`mapEffectivenessSplit`).  Finally `relOf (graph x ⊚ graph x°) = x≫x° = relOf E` (bridge
    C + `relOf_graph`/`relOf_reciprocal`), so `E ⊂ graph x⊚graph x°` and back by bridge D. -/
theorem mapIsEffective_of_split {a : A}
    (split : ∀ {c : A} (R : c ⟶ c), Reflexive R → Symmetric R → R ≫ R = R →
      ∃ (d : A) (f : c ⟶ d), Map f ∧ f ≫ f° = R ∧ f° ≫ f = Cat.id d)
    {E : @BinRel (MapObj A) (mapCat (𝒜 := A)) a a}
    (hE : @EquivalenceRelation (MapObj A) (mapCat (𝒜 := A))
            mapHasBinaryProducts mapHasPullbacks mapHasImages a E) :
    @IsEffective (MapObj A) (mapCat (𝒜 := A)) a E
      mapHasBinaryProducts mapHasPullbacks mapHasImages := by
  obtain ⟨⟨d, hdA, hdB⟩, ⟨hsymHom⟩, ⟨htransHom⟩⟩ := hE
  -- relOf E reflexive / symmetric / idempotent.
  have hrefl : Reflexive (relOf E) :=
    relOf_reflexive (E := E) (d := d) (congrArg Subtype.val hdA) (congrArg Subtype.val hdB)
  have hsym : Symmetric (relOf E) := relOf_symmetric ⟨hsymHom⟩
  have hidem : relOf E ≫ relOf E = relOf E := relOf_idempotent hrefl ⟨htransHom⟩
  -- Split it as a map x : a → Q (allegory level), then bundle into Map(A).
  obtain ⟨Q, xv, hxMap, hxx, hxxId⟩ := split (relOf E) hrefl hsym hidem
  let x : @Cat.Hom (MapObj A) (mapCat (𝒜 := A)) a Q := ⟨xv, hxMap⟩
  have hxcov : @Cover (MapObj A) (mapCat (𝒜 := A)) a Q x := mapEffectivenessSplit x hxxId
  -- relOf (graph x ⊚ (graph x)°) = x ≫ x° = relOf E.
  have hlevel : relOf (@compose (MapObj A) (mapCat (𝒜 := A))
          mapHasBinaryProducts mapHasPullbacks mapHasImages a Q a
          (@graph (MapObj A) (mapCat (𝒜 := A)) a Q x)
          (@reciprocal (MapObj A) (mapCat (𝒜 := A)) a Q (@graph (MapObj A) (mapCat (𝒜 := A)) a Q x)))
      = relOf E := by
    rw [relOf_compose, relOf_graph, relOf_reciprocal, relOf_graph, hxx]
  refine ⟨⟨⟨d, hdA, hdB⟩, ⟨hsymHom⟩, ⟨htransHom⟩⟩, Q, x, hxcov, ?_, ?_⟩
  · exact relLe_of_relOf_le (hlevel ▸ le_refl _)
  · exact relLe_of_relOf_le (hlevel ▸ le_refl _)

end MapPreLogos

section MapPreLogosUnions

-- The pre-logos upgrade (subobject unions, effectiveness assembly, `mapPreLogos`) genuinely
-- uses `∪`/`𝟘`, hence the distributive class from here on.
variable {A : Type u} [TabularUnitaryDistributiveAllegory A]

/-! ### §2.212  HasSubobjectUnions (MapObj A)

  A subobject `S` of `B` in Map(𝒜) is a monic map `s := S.arr : S.dom → B`; its associated
  COREFLEXIVE on `B` is `corOf S := s° ≫ s` (coreflexive since `s` is simple).  Subobject
  containment `S ≤ T` corresponds EXACTLY to `corOf S ⊑ corOf T`:
    • `S ≤ T` via `h ≫ t = s` gives `s°≫s = t°(h°h)t ⊑ t°≫t`  (`h` simple);
    • conversely `s°≫s ⊑ t°≫t` factors `s` through the splitting `t` by `tabulation_UP_forward`
      (`(t,t)` tabulates `t°≫t` because `t≫t° = 1` via `mapMonic_inj` + Entire).
  In a DISTRIBUTIVE allegory the join of two coreflexives is `corOf S ∪ corOf T` (still
  coreflexive by `union_lub`); SPLITTING it (`coreflexive_splits`, every coreflexive splits
  in a tabular allegory) gives the union subobject, with `union_left`/`union_right`/`union_min`
  read off `le_union_left`/`le_union_right`/`union_lub` through the `corOf` correspondence.

  With the single `[TabularUnitaryDistributiveAllegory A]` instance (diamond merged) every
  mixed `≫`/`°`/`∪` expression lives on ONE `Allegory A`, so the construction goes through. -/

/-- The COREFLEXIVE on `B` associated to a subobject `S` of `B` in Map(𝒜): `s° ≫ s` where
    `s = S.arr.val` is the underlying monic map.  Coreflexive because `s` is simple. -/
private def corOf {B : MapObj A} (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) : B ⟶ B :=
  (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val° ≫
    (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val

/-- The underlying arrow of a subobject is a Map. -/
private theorem subArr_map {B : MapObj A} (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    Map (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val :=
  (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).property

/-- A subobject's arrow is a retraction: `s ≫ s° = id` (monic-in-Map ⟹ injective relation,
    plus entirety). -/
private theorem subArr_retract {B : MapObj A} (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    let s := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val
    s ≫ s° = Cat.id (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B S) := by
  intro s
  exact le_antisymm
    (mapMonic_inj (subArr_map S) (@Subobject.monic (MapObj A) (mapCat (𝒜 := A)) B S))
    (map_entire_le (subArr_map S))

/-- `(s, s)` tabulates `corOf S = s°≫s` (using the retraction `s≫s° = id`). -/
private theorem subArr_tabulates {B : MapObj A}
    (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    let s := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val
    Tabulates s s (corOf S) := by
  intro s
  exact ⟨subArr_map S, subArr_map S, rfl, by rw [Allegory.inter_idem]; exact subArr_retract S⟩

/-- **§2.212 correspondence (⟸)**: if `corOf S ⊑ corOf T` then `S ≤ T` in Map(𝒜).
    The map `s` factors through `t` via `tabulation_UP_forward` against the tabulation `(t,t)`
    of `corOf T`. -/
private theorem le_of_corOf_le {B : MapObj A}
    {S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B}
    (hle : corOf S ⊑ corOf T) :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) B S T := by
  let s := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val
  -- s°≫s ⊑ t°≫t = corOf T, and (t,t) tabulates corOf T; apply forward UP with x = y = s.
  obtain ⟨h, hh, hht, _⟩ :=
    tabulation_UP_forward (subArr_tabulates T) (subArr_map S) (subArr_map S) hle
  -- h : S.dom → T.dom with h ≫ T.arr.val = s, i.e. S ≤ T in mapCat.
  exact ⟨⟨h, hh⟩, mapHom_ext hht⟩

/-- **§2.212 correspondence (⟹)**: if `S ≤ T` in Map(𝒜) then `corOf S ⊑ corOf T`.
    From `h ≫ t = s` one gets `s°≫s = t°(h°h)t ⊑ t°≫t` since `h` is simple. -/
private theorem corOf_le_of_le {B : MapObj A}
    {S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B}
    (hle : @Subobject.le (MapObj A) (mapCat (𝒜 := A)) B S T) :
    corOf S ⊑ corOf T := by
  obtain ⟨h, hh_eq⟩ := hle
  -- h.val ≫ T.arr.val = S.arr.val (allegory level)
  have heq : h.val ≫ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T).val =
      (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val := congrArg Subtype.val hh_eq
  let s := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val
  let t := (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T).val
  -- corOf S = s°≫s = (h≫t)°≫(h≫t) = t°≫(h°≫h)≫t ⊑ t°≫t = corOf T (h simple).
  show s° ≫ s ⊑ t° ≫ t
  calc s° ≫ s = (h.val ≫ t)° ≫ (h.val ≫ t) := by rw [heq]
    _ = t° ≫ (h.val° ≫ h.val) ≫ t := by rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ ⊑ t° ≫ Cat.id _ ≫ t := comp_mono_left t° (comp_mono_right h.property.2 t)
    _ = t° ≫ t := by rw [Cat.id_comp]

/-- `S ≤ T  ↔  corOf S ⊑ corOf T`. -/
private theorem le_iff_corOf_le {B : MapObj A}
    {S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B} :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) B S T ↔ corOf S ⊑ corOf T :=
  ⟨corOf_le_of_le, le_of_corOf_le⟩

/-- Subobjects with the SAME associated coreflexive have isomorphic domains in Map(𝒜):
    `corOf S = corOf T` gives mutual `≤`, whose factoring maps are mutually inverse (each
    monic arrow is mapCat-monic). -/
private theorem corOf_eq_dom_iso {B : MapObj A}
    {S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B} (hcor : corOf S = corOf T) :
    @Isomorphic (MapObj A) (mapCat (𝒜 := A))
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B S)
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B T) := by
  obtain ⟨h, hh⟩ := le_of_corOf_le (S := S) (T := T) (hcor ▸ le_refl _)
  obtain ⟨k, hk⟩ := le_of_corOf_le (S := T) (T := S) (hcor ▸ le_refl _)
  have hhv : h.val ≫ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T).val =
      (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val := congrArg Subtype.val hh
  have hkv : k.val ≫ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val =
      (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T).val := congrArg Subtype.val hk
  -- h≫t = s, k≫s = t.  (h≫k)≫s = h≫t? no: h≫k : S.dom→S.dom; (h≫k)≫s = h≫(k≫s)=h≫t=s=id≫s.
  refine ⟨h, ⟨k, ?_, ?_⟩⟩
  · -- h ≫ k = id_{S.dom}: monic S.arr.  (h≫k)≫s = h≫(k≫s) = h≫t = s = id≫s.
    exact @Subobject.monic (MapObj A) (mapCat (𝒜 := A)) B S _
      (@Cat.comp _ (mapCat (𝒜 := A)) _ _ _ h k)
      (@Cat.id _ (mapCat (𝒜 := A)) _)
      (mapHom_ext (by
        show (h.val ≫ k.val) ≫ _ = Cat.id _ ≫ _
        rw [Cat.assoc, hkv, hhv, Cat.id_comp]))
  · -- k ≫ h = id_{T.dom}: monic T.arr.
    exact @Subobject.monic (MapObj A) (mapCat (𝒜 := A)) B T _
      (@Cat.comp _ (mapCat (𝒜 := A)) _ _ _ k h)
      (@Cat.id _ (mapCat (𝒜 := A)) _)
      (mapHom_ext (by
        show (k.val ≫ h.val) ≫ _ = Cat.id _ ≫ _
        rw [Cat.assoc, hhv, hkv, Cat.id_comp]))

/-- **§2.212 BRIDGE (†)**: the coreflexive of an inverse image is the relational inverse image
    of the subobject's coreflexive:

        `corOf (InverseImage f T) = dom (f.val ≫ corOf T ≫ f.val°)`.

    `InverseImage f T`'s arrow is the first projection of `mapHasPullback f T.arr`, whose leg
    coreflexive is `dom (f.val ≫ T.arr.val°)` (`mapPullback_leg_corOf`).  Writing
    `R := f.val ≫ T.arr.val°`, `f.val ≫ corOf T ≫ f.val° = R ≫ R°` and `dom R = dom (R ≫ R°)`
    (`dom_eq_dom_comp_recip`), giving the stated form. -/
private theorem corOf_invImage {B C : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) B C)
    (T : @Subobject (MapObj A) (mapCat (𝒜 := A)) C) :
    corOf (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f T mapHasPullbacks)
      = dom (f.val ≫ corOf T ≫ f.val°) := by
  -- The InverseImage arrow IS the first leg of mapHasPullback f T.arr.
  let t : @Cat.Hom _ (mapCat (𝒜 := A)) (@Subobject.dom _ (mapCat (𝒜 := A)) C T) C :=
    @Subobject.arr (MapObj A) (mapCat (𝒜 := A)) C T
  have hleg := mapPullback_leg_corOf f t (mapHasPullback f t)
  -- corOf(InverseImage) = leg° ≫ leg = dom (f.val ≫ t.val°).
  have hcor : corOf (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f T mapHasPullbacks)
      = dom (f.val ≫ t.val°) := hleg
  rw [hcor]
  -- dom (f.val ≫ t.val°) = dom (f.val ≫ corOf T ≫ f.val°), via R≫R° rewrite (R = f.val ≫ t.val°).
  have hRR : f.val ≫ corOf T ≫ f.val° = (f.val ≫ t.val°) ≫ (f.val ≫ t.val°)° := by
    show f.val ≫ (t.val° ≫ t.val) ≫ f.val° = (f.val ≫ t.val°) ≫ (f.val ≫ t.val°)°
    rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  rw [hRR, ← dom_eq_dom_comp_recip]

/-- Extract the splitting of a coreflexive as Type-valued data via `Classical.choice`. -/
private noncomputable def corSplitData {B : A} {R : B ⟶ B} (hcor : Coreflexive R) :
    PSigma fun u : A => PSigma fun e : u ⟶ B =>
        Map e ∧ e° ≫ e = R ∧ e ≫ e° = Cat.id u :=
  Classical.choice (by
    obtain ⟨u, e, he, hl, hr⟩ := coreflexive_splits hcor
    exact ⟨⟨u, e, he, hl, hr⟩⟩)

/-- Build a subobject of `B` from a coreflexive `R` on `B` by splitting it: the splitting map
    `e : u → B` is monic in Map(𝒜) (a retraction), and `corOf (splitSub R) = R`. -/
private noncomputable def splitSub {B : MapObj A} {R : B ⟶ B} (hcor : Coreflexive R) :
    @Subobject (MapObj A) (mapCat (𝒜 := A)) B :=
  let d := corSplitData hcor
  @Subobject.mk (MapObj A) (mapCat (𝒜 := A)) B d.1 ⟨d.2.1, d.2.2.1⟩
    (map_retract_monic d.2.2.1 d.2.2.2.2)

/-- The coreflexive recovered from `splitSub` is the original `R`. -/
private theorem corOf_splitSub {B : MapObj A} {R : B ⟶ B} (hcor : Coreflexive R) :
    corOf (splitSub hcor) = R :=
  (corSplitData hcor).2.2.2.1

/-- **§2.212 union of subobjects**: split the coreflexive `corOf S ∪ corOf T`. -/
private noncomputable def mapSubUnion {B : MapObj A}
    (S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    @Subobject (MapObj A) (mapCat (𝒜 := A)) B :=
  splitSub (R := corOf S ∪ corOf T)
    (union_lub (subArr_map S).2 (subArr_map T).2)

private theorem corOf_mapSubUnion {B : MapObj A}
    (S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    corOf (mapSubUnion S T) = corOf S ∪ corOf T :=
  corOf_splitSub _

/-- **§2.212 corOf of an intersection**: `corOf (S ∩ T) = s° ≫ dom(s ≫ t°) ≫ s`, where
    `s = S.arr.val`, `t = T.arr.val`.  The intersection's arrow is `π₁ ≫ s` for the pullback of
    `(s, t)`; its leg coreflexive `π₁° ≫ π₁ = dom(s ≫ t°)` is `mapPullback_leg_corOf`. -/
private theorem corOf_inter {B : MapObj A}
    (S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    corOf (@Subobject.inter (MapObj A) (mapCat (𝒜 := A)) mapHasPullbacks B S T)
      = (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val° ≫
          dom ((@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val ≫
                (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T).val°) ≫
          (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val := by
  -- π₁°≫π₁ = dom(S.arr.val ≫ T.arr.val°) for the pullback used by `Subobject.inter`.
  have hleg := mapPullback_leg_corOf
      (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S)
      (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T)
      (mapHasPullback (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S)
        (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B T))
  -- Operate on the goal (all `≫`/`°` come from `corOf`'s definition — already the allegory Cat,
  -- so no mapCat/allegory `≫` ambiguity from re-typed compositions).
  -- corOf(inter) = (π₁≫S.arr).val° ≫ (π₁≫S.arr).val.  Distribute `.val` (mapCat comp), recip_comp,
  -- reassoc, then apply `hleg : π₁°≫π₁ = dom(S.arr ≫ T.arr°)`.
  simp only [corOf, Subobject.inter, mapCat, Allegory.recip_comp, Cat.assoc]
  rw [← Cat.assoc _ _ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) B S).val, hleg]

/-- **§2.212**: subobjects of Map(𝒜) have binary unions. -/
noncomputable instance mapHasSubobjectUnions :
    @HasSubobjectUnions (MapObj A) (mapCat (𝒜 := A)) mapHasImages :=
  @HasSubobjectUnions.mk (MapObj A) (mapCat (𝒜 := A)) mapHasImages
    (fun {_B} S T => mapSubUnion S T)
    (fun {_B} S T => le_iff_corOf_le.mpr (by
      rw [corOf_mapSubUnion]; exact le_union_left _ _))
    (fun {_B} S T => le_iff_corOf_le.mpr (by
      rw [corOf_mapSubUnion]; exact le_union_right _ _))
    (fun {_B} S T U hSU hTU => le_iff_corOf_le.mpr (by
      rw [corOf_mapSubUnion]
      exact union_lub (le_iff_corOf_le.mp hSU) (le_iff_corOf_le.mp hTU)))

/-! ### §2.212  bottom (empty join) of the Map(𝒜) subobject lattices

  The minimal subobject of `B` is the split of the ZERO coreflexive `𝟘 : B → B`
  (`𝟘 ⊑ 1_B` by `zero_le`).  It is least (`corOf` of anything is `⊒ 𝟘`), and any two of
  these (over different objects) have isomorphic domains via `corOf_eq_dom_iso`. -/

/-- The empty-join (minimal) subobject of `B` in Map(𝒜): the split of `𝟘 : B → B`. -/
private noncomputable def mapBottom (B : MapObj A) :
    @Subobject (MapObj A) (mapCat (𝒜 := A)) B :=
  splitSub (R := (𝟘 : B ⟶ B)) (zero_le _)

/-- `mapBottom B` is the least subobject of `B`. -/
private theorem mapBottom_min {B : MapObj A} (S : @Subobject (MapObj A) (mapCat (𝒜 := A)) B) :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B) S :=
  le_iff_corOf_le.mpr (by
    rw [show corOf (mapBottom B) = (𝟘 : B ⟶ B) from corOf_splitSub _]
    exact zero_le _)

/-- The apex of `mapBottom B` carries `id = 𝟘` at the ALLEGORY level: its splitting arrow `e`
    satisfies `e = e≫(e°≫e) = e≫𝟘 = 𝟘`, whence `id_u = e≫e° = 𝟘≫𝟘 = 𝟘`. -/
private theorem mapBottom_id_zero (B : MapObj A) :
    Cat.id (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B)) =
      (𝟘 : (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B)) ⟶
            (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B))) := by
  let d := corSplitData (R := (𝟘 : B ⟶ B)) (zero_le _)
  -- e°≫e = 𝟘, e≫e° = id_u.  e = e≫(e°≫e) = e≫𝟘 = 𝟘 ⟹ id_u = e≫e° = 𝟘≫𝟘 = 𝟘.
  have he_zero : d.2.1 = (𝟘 : d.1 ⟶ B) := by
    calc d.2.1 = (d.2.1 ≫ d.2.1°) ≫ d.2.1 := by rw [d.2.2.2.2, Cat.id_comp]
      _ = d.2.1 ≫ (d.2.1° ≫ d.2.1) := Cat.assoc _ _ _
      _ = d.2.1 ≫ (𝟘 : B ⟶ B) := by rw [d.2.2.2.1]
      _ = 𝟘 := DistributiveAllegory.comp_zero _
  show Cat.id d.1 = (𝟘 : d.1 ⟶ d.1)
  calc Cat.id d.1 = d.2.1 ≫ d.2.1° := d.2.2.2.2.symm
    _ = (𝟘 : d.1 ⟶ B) ≫ (𝟘 : d.1 ⟶ B)° := by rw [he_zero]
    _ = (𝟘 : d.1 ⟶ B) ≫ (𝟘 : B ⟶ d.1) := by rw [recip_zero]
    _ = (𝟘 : d.1 ⟶ d.1) := DistributiveAllegory.comp_zero _

/-- On the apex `u` of `mapBottom X` (where `id_u = 𝟘`), the zero endo/morphisms are maps:
    Entire since `id_u = 𝟘 ⊑ 𝟘≫𝟘°`, Simple since `𝟘°≫𝟘 = 𝟘 ⊑ id_u`. -/
private theorem zero_is_map_on_bottom {B C : MapObj A}
    (hidB : Cat.id (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B)) =
      (𝟘 : _ ⟶ _)) :
    Map (𝟘 : (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B)) ⟶
              (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) C (mapBottom C))) := by
  refine ⟨?_, ?_⟩
  · -- Entire: id ⊑ 𝟘≫𝟘°.  id = 𝟘 (hidB) and 𝟘≫𝟘° = 𝟘, so id ⊑ 𝟘.
    rw [Entire, dom]; apply le_antisymm (inter_lb_left _ _); apply le_inter (le_refl _)
    rw [recip_zero, DistributiveAllegory.comp_zero, hidB]; exact le_refl _
  · -- Simple: 𝟘°≫𝟘 = 𝟘 ⊑ id.
    rw [Simple, recip_zero, DistributiveAllegory.zero_comp]; exact zero_le _

/-- The minimal subobjects over any two objects have isomorphic domains (both split `𝟘`).
    The apexes have `id = 𝟘` (`mapBottom_id_zero`); the zero map between them is a map
    (`zero_is_map_on_bottom`) and is its own two-sided inverse (`𝟘≫𝟘 = 𝟘 = id`). -/
private theorem mapBottom_dom_iso (B C : MapObj A) :
    @Isomorphic (MapObj A) (mapCat (𝒜 := A))
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B))
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) C (mapBottom C)) := by
  have hidB := mapBottom_id_zero B
  have hidC := mapBottom_id_zero C
  refine ⟨⟨(𝟘 : _ ⟶ _), zero_is_map_on_bottom (B := B) (C := C) hidB⟩,
    ⟨⟨(𝟘 : _ ⟶ _), zero_is_map_on_bottom (B := C) (C := B) hidC⟩, ?_, ?_⟩⟩
  · -- (𝟘:uB→uC) ≫ (𝟘:uC→uB) = id_uB = 𝟘
    exact mapHom_ext (by
      show (𝟘 : _ ⟶ _) ≫ 𝟘 = Cat.id _
      rw [DistributiveAllegory.comp_zero]; exact hidB.symm)
  · -- (𝟘:uC→uB) ≫ (𝟘:uB→uC) = id_uC = 𝟘
    exact mapHom_ext (by
      show (𝟘 : _ ⟶ _) ≫ 𝟘 = Cat.id _
      rw [DistributiveAllegory.comp_zero]; exact hidC.symm)

/-! ### §2.212  Inverse image preserves unions and the bottom (via the bridge (†)) -/

/-- `corOf (f# (S ∪ T)) = corOf (f# S ∪ f# T)`: pure relational computation from (†)
    (`corOf_invImage`), `corOf_mapSubUnion`, `comp_union_distrib`, and `dom_union`. -/
private theorem corOf_invImage_union {B C : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) B C)
    (S T : @Subobject (MapObj A) (mapCat (𝒜 := A)) C) :
    corOf (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f (mapSubUnion S T) mapHasPullbacks)
      = corOf (mapSubUnion
          (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f S mapHasPullbacks)
          (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f T mapHasPullbacks)) := by
  rw [corOf_invImage f (mapSubUnion S T), corOf_mapSubUnion,
      corOf_mapSubUnion, corOf_invImage f S, corOf_invImage f T]
  -- dom(f (corOf S ∪ corOf T) f°) = dom(f corOf S f° ∪ f corOf T f°) = dom(..) ∪ dom(..).
  have hdist : f.val ≫ (corOf S ∪ corOf T) ≫ f.val°
      = (f.val ≫ corOf S ≫ f.val°) ∪ (f.val ≫ corOf T ≫ f.val°) := by
    rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib]
  rw [hdist, dom_union]

/-- **§2.212**: `f#` preserves binary unions in Map(𝒜).  Both inclusions follow from the
    `corOf`-equality `corOf_invImage_union` through `le_iff_corOf_le`. -/
theorem mapInvImage_preserves_union {B C : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) B C) :
    @inverseImage_preserves_unions (MapObj A) (mapCat (𝒜 := A)) mapHasImages
      mapHasSubobjectUnions B C f mapHasPullbacks := by
  intro S T
  have heq := corOf_invImage_union f S T
  exact ⟨le_iff_corOf_le.mpr (heq ▸ le_refl _), le_iff_corOf_le.mpr (heq ▸ le_refl _)⟩

/-- **§2.212**: `f#` preserves the bottom (empty join) in Map(𝒜): `corOf (f# ⊥) = 𝟘 = corOf ⊥`,
    whence isomorphic domains via `corOf_eq_dom_iso`. -/
theorem mapInvImage_preserves_bottom {B C : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) B C) :
    @Isomorphic (MapObj A) (mapCat (𝒜 := A))
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B
        (@InverseImage (MapObj A) (mapCat (𝒜 := A)) B C f (mapBottom C) mapHasPullbacks))
      (@Subobject.dom (MapObj A) (mapCat (𝒜 := A)) B (mapBottom B)) := by
  apply corOf_eq_dom_iso
  -- corOf(f# ⊥) = dom(f ≫ 𝟘 ≫ f°) = dom 𝟘 = 𝟘 = corOf ⊥.
  rw [corOf_invImage f (mapBottom C),
      show corOf (mapBottom C) = (𝟘 : C ⟶ C) from corOf_splitSub _,
      show corOf (mapBottom B) = (𝟘 : B ⟶ B) from corOf_splitSub _]
  rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero, dom_zero]

end MapPreLogosUnions

/-! ### §2.212  PreLogos (MapObj A) — the assembled pre-logos -/

/-- **§2.212**: For a TABULAR UNITARY DISTRIBUTIVE allegory `A`, `Map(A)` is a PRE-LOGOS.
    Assembled from `mapRegularCategory` (regular), `mapHasSubobjectUnions` (subobject joins),
    the bottom apparatus (`mapBottom`/`mapBottom_min`/`mapBottom_dom_iso`), and the
    inverse-image-preservation laws (`mapInvImage_preserves_union`/`_bottom`) built on the
    bridge (†) (`corOf_invImage`). -/
noncomputable instance mapPreLogos {A : Type u} [TabularUnitaryDistributiveAllegory A] :
    @PreLogos (MapObj A) (mapCat (𝒜 := A)) :=
  @PreLogos.mk (MapObj A) (mapCat (𝒜 := A)) mapRegularCategory mapHasSubobjectUnions
    mapBottom (fun {_B} S => mapBottom_min S) mapBottom_dom_iso
    (fun {_B _C} f => mapInvImage_preserves_union f)
    (fun {_B _C} f => mapInvImage_preserves_bottom f)

/-- **§2.217(2) — `Map(A)` is EFFECTIVE REGULAR** (given allegory effectiveness as DATA).
    `mapRegularCategory` supplies the regular structure; the `effective` field is
    `mapIsEffective_of_split` fed the supplied splitting `split`.  Taken as a `def` over the
    SPLIT DATA (not an `[EffectiveAllegory A]` instance) to keep the single `Allegory A` from
    `[TabularUnitaryDistributiveAllegory A]` — the standard diamond dodge, cf. `s217_2_*`. -/
noncomputable def mapEffectiveRegular {A : Type u} [TabularUnitaryDistributiveAllegory A]
    (split : ∀ {c : A} (R : c ⟶ c), Freyd.Alg.Reflexive R → Freyd.Alg.Symmetric R → R ≫ R = R →
      ∃ (d : A) (f : c ⟶ d), Freyd.Alg.Map f ∧ f ≫ f° = R ∧ f° ≫ f = Cat.id d) :
    @EffectiveRegular (MapObj A) (mapCat (𝒜 := A)) :=
  @EffectiveRegular.mk (MapObj A) (mapCat (𝒜 := A)) mapRegularCategory
    (fun {_a} _E hE => mapIsEffective_of_split split hE)

/-! ### §2.212  PreLogos (MapObj A) — DONE (Sorry-free)

  `mapPreLogos` above is a fully PROVED `PreLogos (MapObj A)` instance for a
  `TabularUnitaryDistributiveAllegory A`.  All eight fields are discharged:

    • regular + subobject joins:  `mapRegularCategory`, `mapHasSubobjectUnions`;
    • bottom:  `mapBottom`, `mapBottom_min`, `mapBottom_dom_iso` (cross-object `𝟘`-split iso);
    • inverse-image preservation:  `mapInvImage_preserves_union` / `mapInvImage_preserves_bottom`,
      both built on the BRIDGE LEMMA (†)

          corOf (InverseImage f T)  =  dom (f.val ≫ corOf T ≫ f.val°)        (†)   `corOf_invImage`

      The pullback-leg coreflexive `pb.π₁°≫pb.π₁ = dom(f g°)` (`mapPullback_leg_corOf`) is bridged
      from the choice-extracted projection to the canonical tabulation of `f g°` via the
      pullback-uniqueness comparison map (`map_retr_leg` + `tab_leg_dom`); (†) then follows with
      `dom_eq_dom_comp_recip`.  Union/bottom preservation are mechanical relational algebra from (†)
      (`corOf_mapSubUnion`, `comp_union_distrib`/`union_comp_distrib`, `dom_union`, `dom_zero`),
      read off through the `corOf` correspondence `le_iff_corOf_le` / `corOf_eq_dom_iso`. -/

/-! ### §2.32 backward  `Logos (MapObj A)` for a tabular unitary DIVISION allegory

  The one field beyond `mapPreLogos` is `HasRightAdjointImage`: the right adjoint `f##` to the
  inverse-image `f#`.  Under the bridge `Sub(Map A) X ≅ Cor(X)` (`corOf`/`splitSub`), for a map
  `f : a → b` and coreflexives `A = corOf A'` (on a), `c = corOf B'` (on b), the inverse image
  reads off as `corOf (InverseImage f B') = dom (f c f°) = 1 ∩ f c f°` (`corOf_invImage` +
  `dom_map_coref`, §2.32).  Its right adjoint on `Cor` is `D = f \ (1 → A) / f°`, where `1 → A`
  is the §2.316 Heyting arrow `oneHeyting A` on the FULL hom-poset `(a,a)` (NOT on `Cor(a)`); the
  adjunction `1 ∩ f c f° ⊑ A ↔ c ⊑ D` for coreflexive `c` is `le_leftDiv_iff`/`le_div_iff` chained
  with `oneHeyting_adj`.  We take the coreflexive part `1_b ∩ D` (so it splits to a subobject;
  `c ⊑ 1_b ∩ D ↔ c ⊑ D` as `c ⊑ 1_b`). -/

section MapLogos
variable {A : Type u} [TabularUnitaryDivisionAllegory A]

/-- A `TabularUnitaryDivisionAllegory` is a `TabularUnitaryDistributiveAllegory`
    (forgetting right division).  Same `Allegory` base — no diamond. -/
instance mapTUDA_of_TUDiv : TabularUnitaryDistributiveAllegory A :=
  { (inferInstance : TabularAllegory A), (inferInstance : UnitaryAllegory A),
    (inferInstance : DistributiveAllegory A) with }

/-- The coreflexive right adjoint `1_b ∩ f \ (oneHeyting A) / f°` for a map `f : a → b`
    and a coreflexive `A` on `a`. -/
private noncomputable def rightAdjCor {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b) (A' : a ⟶ a) : b ⟶ b :=
  Cat.id b ∩ (f.val \ (DivisionAllegory.div (oneHeyting A') f.val°))

private theorem rightAdjCor_coref {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b) (A' : a ⟶ a) : Coreflexive (rightAdjCor f A') :=
  inter_lb_left _ _

/-- **§2.32 adjunction (coreflexive form)**: for a map `f : a → b`, coreflexive `A` on `a`
    and coreflexive `c` on `b`,
        `(1 ∩ f c f°) ⊑ A   ↔   c ⊑ rightAdjCor f A`. -/
private theorem rightAdjCor_adj {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b) {A' : a ⟶ a} {c : b ⟶ b}
    (hc : Coreflexive c) :
    (Cat.id a ∩ (f.val ≫ c ≫ f.val°)) ⊑ A' ↔ c ⊑ rightAdjCor f A' := by
  have hf : Map f.val := f.property
  -- c ⊑ 1_b ∩ D  ↔  c ⊑ D   (c ⊑ 1_b)
  have hcc : c ⊑ rightAdjCor f A' ↔ c ⊑ (f.val \ (DivisionAllegory.div (oneHeyting A') f.val°)) := by
    rw [rightAdjCor]
    exact ⟨fun h => le_trans h (inter_lb_right _ _), fun h => le_inter hc h⟩
  rw [hcc, le_leftDiv_iff, le_div_iff]
  -- (f c) f° ⊑ oneHeyting A  ↔  f c f° ⊑ oneHeyting A
  have hassoc : (f.val ≫ c) ≫ f.val° = f.val ≫ c ≫ f.val° := Cat.assoc _ _ _
  rw [hassoc, ← oneHeyting_adj A' (f.val ≫ c ≫ f.val°), Allegory.inter_comm]

/-- **§2.32 backward — `HasRightAdjointImage (MapObj A)`**.  `rightAdj f A' := splitSub (rightAdjCor)`;
    the adjunction is `rightAdjCor_adj` read through the `corOf`/`splitSub` bridge. -/
noncomputable instance mapHasRightAdjointImage :
    @HasRightAdjointImage (MapObj A) (mapCat (𝒜 := A)) :=
  @HasRightAdjointImage.mk (MapObj A) (mapCat (𝒜 := A)) mapHasImages mapHasPullbacks
    (fun {a b} f A' => splitSub (R := rightAdjCor f (corOf A')) (rightAdjCor_coref f (corOf A')))
    (fun {a b} f B' A' => by
      -- LHS: InverseImage f B' ≤ A'  ↔  corOf (InverseImage f B') ⊑ corOf A'
      rw [le_iff_corOf_le, le_iff_corOf_le, corOf_splitSub,
          corOf_invImage f B',
          dom_map_coref f.val f.property (show Coreflexive (corOf B') from (subArr_map B').2)]
      -- goal: (1 ∩ f (corOf B') f°) ⊑ corOf A'  ↔  corOf B' ⊑ rightAdjCor f (corOf A')
      exact rightAdjCor_adj f (subArr_map B').2)

/-- **§2.32 — `Logos (MapObj A)`** for a tabular unitary division allegory `A`.  Combines the
    pre-logos `mapPreLogos` (regular + subobject lattice) with the right adjoint
    `mapHasRightAdjointImage` to `f#`.  This is Freyd §2.32 (backward direction): `Mσn(A)` is a
    logos. -/
noncomputable instance mapLogos : @Logos (MapObj A) (mapCat (𝒜 := A)) :=
  @Logos.mk (MapObj A) (mapCat (𝒜 := A))
    mapRegularCategory mapHasSubobjectUnions
    (@HasRightAdjointImage.rightAdj (MapObj A) (mapCat (𝒜 := A)) mapHasRightAdjointImage)
    (@HasRightAdjointImage.adjunction (MapObj A) (mapCat (𝒜 := A)) mapHasRightAdjointImage)
    mapBottom (fun {_B} S => mapBottom_min S) mapBottom_dom_iso

end MapLogos

/-! ## §2.214 (dual)  `Map(positive allegory)` has disjoint binary coproducts

  Freyd §2.214 characterises the coproduct `a ⊕ b` of a distributive allegory by the five
  equations on its injections `u₁ : a → a⊕b`, `u₂ : b → a⊕b`
  (`Coproduct`, S2_2).  Those injections are MAPS (entire from `u₁u₁°=1`; simple from
  `u₁°u₁ ⊑ u₁°u₁ ∪ u₂°u₂ = 1`), so they are morphisms of `Map(𝒜)`, and the allegory coproduct
  becomes a CATEGORICAL coproduct in `Map(𝒜)` — the reciprocal dual of "Map of a positive
  allegory is a positive pre-logos".

  Copairing: for maps `f : a → x`, `g : b → x` the mediating map is the relation
  `case f g := u₁°f ∪ u₂°g : a⊕b → x`.  It is a map (entire via `u₁u₁° = 1` / `f`,`g` entire;
  simple via the disjointness `u₁u₂° = u₂u₁° = 0` / `f`,`g` simple) and satisfies
  `u₁ ≫ case = f`, `u₂ ≫ case = g` with uniqueness — exactly Freyd's mediator from
  `coproduct_five_eqs_to_universal`. -/

section MapCoproduct

variable {A : Type u} [TabularUnitaryPositiveAllegory A]

/-- The chosen allegory coproduct diagram `(a ⊕ b, u₁, u₂)` for `a, b : MapObj A`. -/
private def mapCoprodDiagram (a b : MapObj A) :
    Coproduct (PositiveAllegory.coprod a b) a b :=
  PositiveAllegory.has_coproduct a b

/-- The left injection `u₁ : a → a⊕b` is a MAP (entire from `u₁u₁°=1`; simple from
    `u₁°u₁ ⊑ u₁°u₁ ∪ u₂°u₂ = 1`). -/
private theorem mapCoprod_u₁_map (a b : MapObj A) : Map (mapCoprodDiagram a b).u₁ := by
  refine ⟨?_, ?_⟩
  · -- Entire: id_a ⊑ u₁ ≫ u₁° (in fact = id_a).
    rw [Entire, dom]
    exact le_antisymm (inter_lb_left _ _)
      (le_inter (le_refl _) ((mapCoprodDiagram a b).u₁_self_comp_recip ▸ le_refl _))
  · -- Simple: u₁°≫u₁ ⊑ u₁°u₁ ∪ u₂°u₂ = id.
    have h := le_union_left ((mapCoprodDiagram a b).u₁° ≫ (mapCoprodDiagram a b).u₁)
                           ((mapCoprodDiagram a b).u₂° ≫ (mapCoprodDiagram a b).u₂)
    rw [(mapCoprodDiagram a b).recip_union_eq_id] at h
    exact h

/-- The right injection `u₂ : b → a⊕b` is a MAP. -/
private theorem mapCoprod_u₂_map (a b : MapObj A) : Map (mapCoprodDiagram a b).u₂ := by
  refine ⟨?_, ?_⟩
  · rw [Entire, dom]
    exact le_antisymm (inter_lb_left _ _)
      (le_inter (le_refl _) ((mapCoprodDiagram a b).u₂_self_comp_recip ▸ le_refl _))
  · have h := le_union_right ((mapCoprodDiagram a b).u₁° ≫ (mapCoprodDiagram a b).u₁)
                            ((mapCoprodDiagram a b).u₂° ≫ (mapCoprodDiagram a b).u₂)
    rw [(mapCoprodDiagram a b).recip_union_eq_id] at h
    exact h

/-- The copairing relation `u₁°f ∪ u₂°g : a⊕b → x` of two maps `f : a → x`, `g : b → x`. -/
private def mapCase {a b x : MapObj A} (f : a ⟶ x) (g : b ⟶ x) :
    PositiveAllegory.coprod a b ⟶ x :=
  (mapCoprodDiagram a b).u₁° ≫ f ∪ (mapCoprodDiagram a b).u₂° ≫ g

/-- The copairing `u₁°f ∪ u₂°g` of two MAPS is a MAP.
    Entire: `id = u₁°u₁ ∪ u₂°u₂ ⊑ u₁°(ff°)u₁ ∪ u₂°(gg°)u₂ ⊑ case ≫ case°`.
    Simple: cross terms vanish by `u₁u₂° = u₂u₁° = 0`, leaving `f°f ∪ g°g ⊑ id`. -/
private theorem mapCase_map {a b x : MapObj A} {f : a ⟶ x} {g : b ⟶ x}
    (hf : Map f) (hg : Map g) : Map (mapCase f g) := by
  -- `cp` is a `let`-alias for `mapCoprodDiagram a b` (the expression `mapCase` unfolds to), so
  -- `hunfold` is `rfl` and after `rw [hunfold]` the goal is in `cp.uᵢ` terms — matching the
  -- structure-projection rewrites `cp.u₁_u₂_recip` etc. syntactically.
  let cp := mapCoprodDiagram a b
  -- Entirety facts: id ⊑ ff°, id ⊑ gg°.
  have hfe : Cat.id a ⊑ f ≫ f° := by
    have := hf.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hge : Cat.id b ⊑ g ≫ g° := by
    have := hg.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hunfold : mapCase f g = cp.u₁° ≫ f ∪ cp.u₂° ≫ g := rfl
  have hcaseo : (mapCase f g)° = f° ≫ cp.u₁ ∪ g° ≫ cp.u₂ := by
    rw [hunfold, recip_union, Allegory.recip_comp, Allegory.recip_comp,
        Allegory.recip_recip, Allegory.recip_recip]
    exact DistributiveAllegory.union_comm _ _
  refine ⟨?_, ?_⟩
  · -- Entire (mapCase): id_{a⊕b} ⊑ case ≫ case°.
    rw [Entire, dom]
    refine le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) ?_)
    show Cat.id (PositiveAllegory.coprod a b) ⊑ mapCase f g ≫ (mapCase f g)°
    rw [hcaseo]
    -- id = u₁°u₁ ∪ u₂°u₂ ⊑ u₁°(ff°)u₁ ∪ u₂°(gg°)u₂ ⊑ case≫case°.
    have hdiag : cp.u₁° ≫ cp.u₁ ∪ cp.u₂° ≫ cp.u₂ ⊑ mapCase f g ≫ (f° ≫ cp.u₁ ∪ g° ≫ cp.u₂) := by
      have hL : cp.u₁° ≫ cp.u₁ ⊑ mapCase f g ≫ (f° ≫ cp.u₁ ∪ g° ≫ cp.u₂) := by
        have h1 : cp.u₁° ≫ cp.u₁ ⊑ cp.u₁° ≫ (f ≫ f°) ≫ cp.u₁ := by
          have := comp_mono_left cp.u₁° (comp_mono_right hfe cp.u₁); rwa [Cat.id_comp] at this
        have h2 : cp.u₁° ≫ (f ≫ f°) ≫ cp.u₁ = (cp.u₁° ≫ f) ≫ (f° ≫ cp.u₁) := by simp [Cat.assoc]
        have h3 : (cp.u₁° ≫ f) ≫ (f° ≫ cp.u₁) ⊑ mapCase f g ≫ (f° ≫ cp.u₁ ∪ g° ≫ cp.u₂) := by
          rw [hunfold]
          exact le_trans (comp_mono_right (le_union_left _ _) _)
                         (comp_mono_left _ (le_union_left _ _))
        exact le_trans h1 (h2 ▸ h3)
      have hR : cp.u₂° ≫ cp.u₂ ⊑ mapCase f g ≫ (f° ≫ cp.u₁ ∪ g° ≫ cp.u₂) := by
        have h1 : cp.u₂° ≫ cp.u₂ ⊑ cp.u₂° ≫ (g ≫ g°) ≫ cp.u₂ := by
          have := comp_mono_left cp.u₂° (comp_mono_right hge cp.u₂); rwa [Cat.id_comp] at this
        have h2 : cp.u₂° ≫ (g ≫ g°) ≫ cp.u₂ = (cp.u₂° ≫ g) ≫ (g° ≫ cp.u₂) := by simp [Cat.assoc]
        have h3 : (cp.u₂° ≫ g) ≫ (g° ≫ cp.u₂) ⊑ mapCase f g ≫ (f° ≫ cp.u₁ ∪ g° ≫ cp.u₂) := by
          rw [hunfold]
          exact le_trans (comp_mono_right (le_union_right _ _) _)
                         (comp_mono_left _ (le_union_right _ _))
        exact le_trans h1 (h2 ▸ h3)
      exact union_lub hL hR
    have hid : cp.u₁° ≫ cp.u₁ ∪ cp.u₂° ≫ cp.u₂ = Cat.id (PositiveAllegory.coprod a b) :=
      cp.recip_union_eq_id
    rw [hid] at hdiag; exact hdiag
  · -- Simple (mapCase): case° ≫ case ⊑ id_x.
    show (mapCase f g)° ≫ mapCase f g ⊑ Cat.id x
    rw [hcaseo, hunfold]
    -- Expand the product of unions into four terms.
    rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib, union_comp_distrib]
    -- Four terms (in goal order after the two `union_comp_distrib`):
    --   (f°u₁)(u₁°f), (g°u₂)(u₁°f), (f°u₁)(u₂°g), (g°u₂)(u₂°g).
    refine union_lub (union_lub ?_ ?_) (union_lub ?_ ?_)
    · -- f°u₁u₁°f = f°(u₁u₁°)f = f°f ⊑ id.
      have he : f° ≫ cp.u₁ ≫ cp.u₁° ≫ f = f° ≫ f := by
        rw [← Cat.assoc cp.u₁ cp.u₁° f, cp.u₁_self_comp_recip, Cat.id_comp]
      simp only [Cat.assoc]; rw [he]; exact hf.2
    · -- g°u₂u₁°f = g°(u₂u₁°)f = 0 ⊑ id.
      have he : g° ≫ cp.u₂ ≫ cp.u₁° ≫ f = (𝟘 : x ⟶ x) := by
        rw [← Cat.assoc cp.u₂ cp.u₁° f, cp.u₂_u₁_recip, DistributiveAllegory.zero_comp,
            DistributiveAllegory.comp_zero]
      simp only [Cat.assoc]; rw [he]; exact zero_le _
    · -- f°u₁u₂°g = f°(u₁u₂°)g = f°·0·g = 0 ⊑ id.
      have he : f° ≫ cp.u₁ ≫ cp.u₂° ≫ g = (𝟘 : x ⟶ x) := by
        rw [← Cat.assoc cp.u₁ cp.u₂° g, cp.u₁_u₂_recip, DistributiveAllegory.zero_comp,
            DistributiveAllegory.comp_zero]
      simp only [Cat.assoc]; rw [he]; exact zero_le _
    · -- g°u₂u₂°g = g°(u₂u₂°)g = g°g ⊑ id.
      have he : g° ≫ cp.u₂ ≫ cp.u₂° ≫ g = g° ≫ g := by
        rw [← Cat.assoc cp.u₂ cp.u₂° g, cp.u₂_self_comp_recip, Cat.id_comp]
      simp only [Cat.assoc]; rw [he]; exact hg.2

/-- `u₁ ≫ case = f` (allegory level): `u₁(u₁°f ∪ u₂°g) = (u₁u₁°)f ∪ (u₁u₂°)g = f ∪ 0 = f`. -/
private theorem mapCase_u₁ {a b x : MapObj A} (f : a ⟶ x) (g : b ⟶ x) :
    (mapCoprodDiagram a b).u₁ ≫ mapCase f g = f := by
  let cp := mapCoprodDiagram a b
  show cp.u₁ ≫ (cp.u₁° ≫ f ∪ cp.u₂° ≫ g) = f
  rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
      cp.u₁_self_comp_recip, cp.u₁_u₂_recip, Cat.id_comp,
      DistributiveAllegory.zero_comp, union_zero]

/-- `u₂ ≫ case = g` (allegory level). -/
private theorem mapCase_u₂ {a b x : MapObj A} (f : a ⟶ x) (g : b ⟶ x) :
    (mapCoprodDiagram a b).u₂ ≫ mapCase f g = g := by
  let cp := mapCoprodDiagram a b
  show cp.u₂ ≫ (cp.u₁° ≫ f ∪ cp.u₂° ≫ g) = g
  rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
      cp.u₂_u₁_recip, cp.u₂_self_comp_recip, Cat.id_comp,
      DistributiveAllegory.zero_comp, DistributiveAllegory.zero_union]

/-- Uniqueness of the copairing (allegory level): any `h` with `u₁≫h = f`, `u₂≫h = g` equals
    `mapCase f g`.  This is Freyd's mediator-uniqueness, `1 = u₁°u₁ ∪ u₂°u₂` applied to `h`. -/
private theorem mapCase_uniq {a b x : MapObj A} (f : a ⟶ x) (g : b ⟶ x)
    (h : PositiveAllegory.coprod a b ⟶ x)
    (h₁ : (mapCoprodDiagram a b).u₁ ≫ h = f) (h₂ : (mapCoprodDiagram a b).u₂ ≫ h = g) :
    h = mapCase f g := by
  let cp := mapCoprodDiagram a b
  show h = cp.u₁° ≫ f ∪ cp.u₂° ≫ g
  calc h = Cat.id (PositiveAllegory.coprod a b) ≫ h := (Cat.id_comp h).symm
    _ = (cp.u₁° ≫ cp.u₁ ∪ cp.u₂° ≫ cp.u₂) ≫ h := by rw [cp.recip_union_eq_id]
    _ = cp.u₁° ≫ (cp.u₁ ≫ h) ∪ cp.u₂° ≫ (cp.u₂ ≫ h) := by
          rw [union_comp_distrib, Cat.assoc, Cat.assoc]
    _ = cp.u₁° ≫ f ∪ cp.u₂° ≫ g := by rw [h₁, h₂]

/-- **§2.214 (dual)**: `Map(𝒜)` has binary coproducts for a positive allegory `𝒜`.
    Object `a ⊕ b`, injections the allegory injections `u₁, u₂` (which are maps),
    copairing `case f g = u₁°f ∪ u₂°g`. -/
noncomputable instance mapHasBinaryCoproducts :
    @HasBinaryCoproducts (MapObj A) (mapCat (𝒜 := A)) :=
  @HasBinaryCoproducts.mk (MapObj A) (mapCat (𝒜 := A))
    (fun a b => PositiveAllegory.coprod a b)
    (fun {a b} => ⟨(mapCoprodDiagram a b).u₁, mapCoprod_u₁_map a b⟩)
    (fun {a b} => ⟨(mapCoprodDiagram a b).u₂, mapCoprod_u₂_map a b⟩)
    (fun {_x _a _b} f g => ⟨mapCase f.val g.val, mapCase_map f.property g.property⟩)
    (fun {_x _a _b} f g => mapHom_ext (mapCase_u₁ f.val g.val))
    (fun {_x _a _b} f g => mapHom_ext (mapCase_u₂ f.val g.val))
    (fun {_x _a _b} f g h h₁ h₂ =>
      mapHom_ext (mapCase_uniq f.val g.val h.val
        (congrArg Subtype.val h₁) (congrArg Subtype.val h₂)))

/-! ### §2.214 (dual)  Positivity / disjointness

  The injections are SUBOBJECT inclusions of `a ⊕ b`: `inl` is monic (it is a retraction
  `u₁u₁° = 1`, hence `map_retract_monic`), and through the `corOf`-correspondence the
  disjointness `inl ∩ inr ≤ 0` and the covering `inl ∪ inr = a⊕b` are EXACTLY the allegory
  equations `u₁u₂° = 0` and `u₁°u₁ ∪ u₂°u₂ = 1`. -/

/-- The coproduct object `a ⊕ b`, named through the `HasBinaryCoproducts` projection so that
    `inlSub`/`Subobject.inter`/`mapBottom` annotations match `inl`/`inr`'s codomain syntactically. -/
private noncomputable abbrev mapCoprodObj (a b : MapObj A) : MapObj A :=
  @HasBinaryCoproducts.coprod (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b

/-- `inl = u₁` is monic in `Map(𝒜)` (retraction `u₁ ≫ u₁° = id`).  `HasBinaryCoproducts.inl`
    is definitionally `⟨u₁, _⟩`; `change` exposes that so `map_retract_monic` applies. -/
private theorem mapInl_monic (a b : MapObj A) :
    @Monic (MapObj A) (mapCat (𝒜 := A)) a (mapCoprodObj a b)
      (@HasBinaryCoproducts.inl (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b) := by
  change @Monic (MapObj A) (mapCat (𝒜 := A)) a _
    (⟨(mapCoprodDiagram a b).u₁, mapCoprod_u₁_map a b⟩ :
      @Cat.Hom _ (mapCat (𝒜 := A)) a (PositiveAllegory.coprod a b))
  exact map_retract_monic (mapCoprod_u₁_map a b) (mapCoprodDiagram a b).u₁_self_comp_recip

/-- `inr = u₂` is monic in `Map(𝒜)`. -/
private theorem mapInr_monic (a b : MapObj A) :
    @Monic (MapObj A) (mapCat (𝒜 := A)) b (mapCoprodObj a b)
      (@HasBinaryCoproducts.inr (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b) := by
  change @Monic (MapObj A) (mapCat (𝒜 := A)) b _
    (⟨(mapCoprodDiagram a b).u₂, mapCoprod_u₂_map a b⟩ :
      @Cat.Hom _ (mapCat (𝒜 := A)) b (PositiveAllegory.coprod a b))
  exact map_retract_monic (mapCoprod_u₂_map a b) (mapCoprodDiagram a b).u₂_self_comp_recip

/-- `corOf (inlSub) = u₁° ≫ u₁` (as an endo on `a⊕b`).  `inlSub.arr.val = inl.val = u₁`. -/
private theorem corOf_inlSub (a b : MapObj A) :
    corOf (@inlSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInl_monic a b))
      = (@HasBinaryCoproducts.inl (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val° ≫
        (@HasBinaryCoproducts.inl (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val :=
  rfl

/-- `corOf (inrSub) = u₂° ≫ u₂`. -/
private theorem corOf_inrSub (a b : MapObj A) :
    corOf (@inrSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInr_monic a b))
      = (@HasBinaryCoproducts.inr (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val° ≫
        (@HasBinaryCoproducts.inr (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val :=
  rfl

/-- `inl.val = u₁` and `inr.val = u₂` (definitional unfolding of the instance fields). -/
private theorem mapInl_val (a b : MapObj A) :
    (@HasBinaryCoproducts.inl (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val
      = (mapCoprodDiagram a b).u₁ := rfl
private theorem mapInr_val (a b : MapObj A) :
    (@HasBinaryCoproducts.inr (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b).val
      = (mapCoprodDiagram a b).u₂ := rfl

/-- **§2.214 (dual) DISJOINTNESS**: `inl ∩ inr ≤ 0`.  By `corOf_inter` the intersection's
    coreflexive is `inl° ≫ dom(inl ≫ inr°) ≫ inl = u₁° ≫ dom(u₁ ≫ u₂°) ≫ u₁ = u₁° ≫ dom 𝟘 ≫ u₁
    = 𝟘` (via `u₁u₂° = 0`), so it is `≤ mapBottom` (whose coreflexive is `𝟘`). -/
private theorem mapInl_inter_inr (a b : MapObj A) :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) (mapCoprodObj a b)
      (@Subobject.inter (MapObj A) (mapCat (𝒜 := A)) mapHasPullbacks (mapCoprodObj a b)
        (@inlSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInl_monic a b))
        (@inrSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInr_monic a b)))
      (mapBottom (mapCoprodObj a b)) := by
  apply le_iff_corOf_le.mpr
  rw [show corOf (mapBottom (mapCoprodObj a b)) = (𝟘 : (mapCoprodObj a b) ⟶ (mapCoprodObj a b))
        from corOf_splitSub _, corOf_inter]
  -- inl° ≫ dom(inl ≫ inr°) ≫ inl = u₁° ≫ dom(u₁ ≫ u₂°) ≫ u₁ = u₁° ≫ dom 𝟘 ≫ u₁ = 𝟘.
  -- `(inlSub).arr.val = inl.val = u₁`, `(inrSub).arr.val = inr.val = u₂` (definitional).
  simp only [inlSub, inrSub, mapInl_val, mapInr_val]
  rw [(mapCoprodDiagram a b).u₁_u₂_recip, dom_zero,
      DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]
  exact le_refl _

/-- **§2.214 (dual) COVERING**: `a⊕b ≤ inl ∪ inr`.  Via the `corOf`-correspondence this is
    `id = corOf(entire) ⊑ corOf(union) = u₁°u₁ ∪ u₂°u₂ = id` (the fifth allegory equation). -/
private theorem mapInl_union_inr (a b : MapObj A) :
    @Subobject.le (MapObj A) (mapCat (𝒜 := A)) (mapCoprodObj a b)
      (@Subobject.entire (MapObj A) (mapCat (𝒜 := A)) (mapCoprodObj a b))
      (@HasSubobjectUnions.union (MapObj A) (mapCat (𝒜 := A)) mapHasImages mapHasSubobjectUnions
        (mapCoprodObj a b)
        (@inlSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInl_monic a b))
        (@inrSub (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryCoproducts a b (mapInr_monic a b))) := by
  apply le_iff_corOf_le.mpr
  -- corOf(union) = corOf(inlSub) ∪ corOf(inrSub) = u₁°u₁ ∪ u₂°u₂ = id.
  rw [show (@HasSubobjectUnions.union (MapObj A) (mapCat (𝒜 := A)) mapHasImages mapHasSubobjectUnions
              (mapCoprodObj a b) _ _)
        = mapSubUnion _ _ from rfl,
      corOf_mapSubUnion, corOf_inlSub, corOf_inrSub, mapInl_val, mapInr_val,
      (mapCoprodDiagram a b).recip_union_eq_id]
  -- corOf(entire) = id° ≫ id = id ⊑ id.  `Subobject.entire.arr.val = (mapCat id).val = Cat.id`.
  show (Cat.id (mapCoprodObj a b))° ≫ Cat.id (mapCoprodObj a b) ⊑ Cat.id (mapCoprodObj a b)
  rw [recip_id, Cat.id_comp]
  exact le_refl _

/-- **§2.214 (dual)**: `Map(𝒜)` is a POSITIVE pre-logos for a positive allegory `𝒜`. -/
noncomputable instance mapPositivePreLogos :
    @PositivePreLogos (MapObj A) (mapCat (𝒜 := A)) :=
  @PositivePreLogos.mk (MapObj A) (mapCat (𝒜 := A)) mapPreLogos mapHasBinaryCoproducts

/-- **§2.214 (dual) — the missing brick for §2.217(1)**: `Map(𝒜)` has DISJOINT binary
    coproducts for a tabular unitary positive allegory `𝒜`.  All four disjointness fields are
    discharged from the five allegory coproduct equations through the `corOf` correspondence. -/
noncomputable instance mapDisjointBinaryCoproduct :
    @DisjointBinaryCoproduct (MapObj A) (mapCat (𝒜 := A)) :=
  @DisjointBinaryCoproduct.mk (MapObj A) (mapCat (𝒜 := A)) mapPositivePreLogos
    (fun {a b} => mapInl_monic a b)
    (fun {a b} => mapInr_monic a b)
    (fun {a b} => mapInl_inter_inr a b)
    (fun {a b} => mapInl_union_inr a b)

end MapCoproduct

end Freyd.Alg
