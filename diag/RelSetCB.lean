/-
  `diag.RelSetCB` — SOUNDNESS: the repo's own `Rel(Set)` is a cartesian bicategory of relations.

  functorialSemanticsForRelationalTheories.pdf p. 18 lists the structure for `Rel`: `Δ` the
  diagonal, `!` the terminal map, and `∇ := Δ°`, `? := !°`.  We take exactly that, with `⊗` the
  carrier product (the existing action `rprodMap`, `AOP/A6_1_RelSet.lean`) and `I := ⟨PUnit⟩`.

  Two decisions worth stating, because everything downstream leans on them:

  * The hom order is the ALLEGORY order `⊑` itself (`Freyd/S2_10.lean`), not a second copy.  So
    `OrderedCat.le` and `⊑` are the same relation by definition, `RelSet.le_iff` turns either into
    relational inclusion, and phase 5's bridge has nothing to reconcile on the order.
  * Every structural isomorphism is a `RelSet.graph`, hence a map (`RelSet.graph_map`).  That is
    what makes the coherence laws cheap: `rprodMap_graph` and `graph_comp` normalise a composite of
    them to a single `graph`, after which Lean's definitional eta for `Prod` and `PUnit` closes the
    goal.  Only the four naturality laws mention an arbitrary relation; those go pointwise.

  Names stay `RelSet`-qualified throughout: `Freyd.graph` (the graph of an ARROW, `S1_77`) and
  `Freyd.Alg.RelSet.graph` (the graph of a FUNCTION) are different things, and `open Freyd` is
  needed here for `Cat`/`≫`/`𝟙`.
-/
import diag.CB_Derived
import AOP.A6_1_RelSet

universe u

namespace Freyd.Diag

open Freyd
open Freyd.Alg
open scoped SymMonCat

instance : OrderedCat RelSet.{u} :=
  { (inferInstance : Cat RelSet.{u}) with
    le := Freyd.Alg.le
    le_refl := Freyd.Alg.le_refl
    le_trans := Freyd.Alg.le_trans
    le_antisymm := Freyd.Alg.le_antisymm
    comp_mono := fun h₁ h₂ => Freyd.Alg.le_trans (comp_mono_right h₁ _) (comp_mono_left _ h₂) }

instance : SymMonCat RelSet.{u} :=
  { (inferInstance : OrderedCat RelSet.{u}) with
    tens := fun a b => ⟨a.carrier × b.carrier⟩
    tunit := ⟨PUnit⟩
    tensHom := fun R S => RelSet.rprodMap R S

    tensHom_id := fun a b => by
      rw [← RelSet.graph_id a, ← RelSet.graph_id b, RelSet.rprodMap_graph]
      exact RelSet.graph_id _
    tensHom_comp := fun R R' S S' => RelSet.hom_ext fun p q =>
      ⟨fun ⟨⟨y, hR, hR'⟩, ⟨z, hS, hS'⟩⟩ => ⟨(y, z), ⟨hR, hS⟩, hR', hS'⟩,
       fun ⟨m, ⟨hR, hS⟩, hR', hS'⟩ => ⟨⟨m.1, hR, hR'⟩, ⟨m.2, hS, hS'⟩⟩⟩
    tensHom_mono := fun h₁ h₂ => RelSet.le_iff.mpr fun p q h =>
      ⟨RelSet.le_iff.mp h₁ _ _ h.1, RelSet.le_iff.mp h₂ _ _ h.2⟩

    tensAssoc := fun a b c =>
      RelSet.graph fun p : (a.carrier × b.carrier) × c.carrier => (p.1.1, (p.1.2, p.2))
    tensAssocInv := fun a b c =>
      RelSet.graph fun p : a.carrier × (b.carrier × c.carrier) => ((p.1, p.2.1), p.2.2)
    tensAssoc_inv := fun a b c => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    inv_tensAssoc := fun a b c => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    tensAssoc_nat := by
      intro a a' b b' c c' R S T
      apply RelSet.hom_ext; intro p q
      constructor
      · rintro ⟨m, ⟨⟨hR, hS⟩, hT⟩, hq⟩
        have hq' : q = (m.1.1, (m.1.2, m.2)) := hq
        subst hq'; exact ⟨_, rfl, hR, hS, hT⟩
      · rintro ⟨n, hn, hR, hS, hT⟩
        have hn' : n = (p.1.1, (p.1.2, p.2)) := hn
        subst hn'; exact ⟨((q.1, q.2.1), q.2.2), ⟨⟨hR, hS⟩, hT⟩, rfl⟩

    lunit := fun a => RelSet.graph fun p : PUnit × a.carrier => p.2
    lunitInv := fun a => RelSet.graph fun x : a.carrier => (PUnit.unit, x)
    lunit_inv := fun a => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    inv_lunit := fun a => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    lunit_nat := by
      intro a b R
      apply RelSet.hom_ext; intro p y
      constructor
      · rintro ⟨m, ⟨_, hR⟩, hy⟩
        have hy' : y = m.2 := hy
        subst hy'; exact ⟨p.2, rfl, hR⟩
      · rintro ⟨x, hx, hR⟩
        have hx' : x = p.2 := hx
        subst hx'; exact ⟨(p.1, y), ⟨rfl, hR⟩, rfl⟩

    runit := fun a => RelSet.graph fun p : a.carrier × PUnit => p.1
    runitInv := fun a => RelSet.graph fun x : a.carrier => (x, PUnit.unit)
    runit_inv := fun a => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    inv_runit := fun a => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    runit_nat := by
      intro a b R
      apply RelSet.hom_ext; intro p y
      constructor
      · rintro ⟨m, ⟨hR, _⟩, hy⟩
        have hy' : y = m.1 := hy
        subst hy'; exact ⟨p.1, rfl, hR⟩
      · rintro ⟨x, hx, hR⟩
        have hx' : x = p.1 := hx
        subst hx'; exact ⟨(y, p.2), ⟨hR, rfl⟩, rfl⟩

    swap := fun a b => RelSet.graph fun p : a.carrier × b.carrier => (p.2, p.1)
    swap_swap := fun a b => by rw [RelSet.graph_comp]; exact RelSet.graph_id _
    swap_nat := by
      intro a a' b b' R S
      apply RelSet.hom_ext; intro p q
      constructor
      · rintro ⟨m, ⟨hR, hS⟩, hq⟩
        have hq' : q = (m.2, m.1) := hq
        subst hq'; exact ⟨(p.2, p.1), rfl, hS, hR⟩
      · rintro ⟨n, hn, hS, hR⟩
        have hn' : n = (p.2, p.1) := hn
        subst hn'; exact ⟨(q.2, q.1), ⟨hR, hS⟩, rfl⟩
    swap_lunit := fun a => by rw [RelSet.graph_comp]

    pentagon := fun a b c d => by
      rw [← RelSet.graph_id d, ← RelSet.graph_id a]
      simp only [RelSet.rprodMap_graph, RelSet.graph_comp]
    triangle := fun a b => by
      rw [← RelSet.graph_id a, ← RelSet.graph_id b]
      simp only [RelSet.rprodMap_graph, RelSet.graph_comp]
    hexagon := fun a b c => by
      rw [← RelSet.graph_id c, ← RelSet.graph_id b]
      simp only [RelSet.rprodMap_graph, RelSet.graph_comp] }

/-! ### The monoidal operations, spelled out

  Each of these is `rfl`.  They exist so `simp only` can turn an abstract composite into a concrete
  relation — the step every proof below, and every agreement theorem, starts from. -/

@[simp] theorem tensHom_eq {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    (R ⊗ₕ S) = RelSet.rprodMap R S := rfl

@[simp] theorem tensAssoc_eq (a b c : RelSet.{u}) :
    SymMonCat.tensAssoc a b c
      = (RelSet.graph fun p : (a.carrier × b.carrier) × c.carrier => (p.1.1, (p.1.2, p.2))
          : ((a ⊗ b) ⊗ c) ⟶ (a ⊗ (b ⊗ c))) := rfl

@[simp] theorem tensAssocInv_eq (a b c : RelSet.{u}) :
    SymMonCat.tensAssocInv a b c
      = (RelSet.graph fun p : a.carrier × (b.carrier × c.carrier) => ((p.1, p.2.1), p.2.2)
          : (a ⊗ (b ⊗ c)) ⟶ ((a ⊗ b) ⊗ c)) := rfl

@[simp] theorem lunit_eq (a : RelSet.{u}) :
    SymMonCat.lunit a
      = (RelSet.graph fun p : PUnit × a.carrier => p.2 : ((𝕀 : RelSet.{u}) ⊗ a) ⟶ a) := rfl

@[simp] theorem lunitInv_eq (a : RelSet.{u}) :
    SymMonCat.lunitInv a
      = (RelSet.graph fun x : a.carrier => (PUnit.unit, x) : a ⟶ ((𝕀 : RelSet.{u}) ⊗ a)) := rfl

@[simp] theorem runit_eq (a : RelSet.{u}) :
    SymMonCat.runit a
      = (RelSet.graph fun p : a.carrier × PUnit => p.1 : (a ⊗ (𝕀 : RelSet.{u})) ⟶ a) := rfl

@[simp] theorem runitInv_eq (a : RelSet.{u}) :
    SymMonCat.runitInv a
      = (RelSet.graph fun x : a.carrier => (x, PUnit.unit) : a ⟶ (a ⊗ (𝕀 : RelSet.{u}))) := rfl

@[simp] theorem swap_eq (a b : RelSet.{u}) :
    SymMonCat.swap a b
      = (RelSet.graph fun p : a.carrier × b.carrier => (p.2, p.1) : (a ⊗ b) ⟶ (b ⊗ a)) := rfl

/-! ### The Frobenius structure

  functorialSemanticsForRelationalTheories.pdf p. 18 for `Rel`: `Δ` is the diagonal, `!` the map to
  the one-point set, and the monoid is their converse — `∇ := Δ°`, `? := !°`. -/

/-- `Δ_n : n ⟶ n ⊗ n`, the diagonal. -/
def ΔRel (n : RelSet.{u}) : n ⟶ (⟨n.carrier × n.carrier⟩ : RelSet.{u}) :=
  RelSet.graph fun x => (x, x)

/-- `!_n : n ⟶ I`, the map to the one-point set. -/
def «!Rel» (n : RelSet.{u}) : n ⟶ (⟨PUnit⟩ : RelSet.{u}) := RelSet.graph fun _ => PUnit.unit

/-- `∇ = Δ°` merges two strands: `(x, y)` reaches `z` exactly when both components are `z`. -/
theorem ΔRel_recip_apply (n : RelSet.{u}) (p : n.carrier × n.carrier) (z : n.carrier) :
    (ΔRel n)° p z ↔ (p.1 = z ∧ p.2 = z) :=
  ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, fun h => Prod.ext_iff.mpr ⟨h.1, h.2⟩⟩

/-- `? = !°` relates the point of `I` to everything: the one-point set has nothing to distinguish. -/
theorem «!Rel_recip_apply» (n : RelSet.{u}) (u : PUnit) (x : n.carrier) :
    («!Rel» n)° u x ↔ True :=
  ⟨fun _ => trivial, fun _ => rfl⟩

instance : CartBicat RelSet.{u} :=
  { (inferInstance : SymMonCat RelSet.{u}) with
    Δ := ΔRel
    «!» := «!Rel»
    «∇» := fun n => (ΔRel n)°
    «?» := fun n => («!Rel» n)°

    Δ_assoc := fun n => by
      simp only [ΔRel, tensHom_eq, tensAssoc_eq, ← RelSet.graph_id n, RelSet.rprodMap_graph,
        RelSet.graph_comp]
    Δ_comm := fun n => by
      simp only [ΔRel, swap_eq, RelSet.graph_comp]
    Δ_counit := fun n => by
      simp only [ΔRel, «!Rel», tensHom_eq, runit_eq, ← RelSet.graph_id n, RelSet.rprodMap_graph,
        RelSet.graph_comp]

    «∇_assoc» := fun n => by
      apply RelSet.hom_ext; intro p w
      constructor
      · rintro ⟨m, ⟨h1, h2⟩, h3⟩
        have h1' : p.1.1 = m.1 ∧ p.1.2 = m.1 := (ΔRel_recip_apply n p.1 m.1).mp h1
        have h2' : p.2 = m.2 := h2
        have h3' : m.1 = w ∧ m.2 = w := (ΔRel_recip_apply n m w).mp h3
        exact ⟨(p.1.1, (p.1.2, p.2)), rfl,
          (w, w), ⟨h1'.1.trans h3'.1, (ΔRel_recip_apply n _ w).mpr
            ⟨h1'.2.trans h3'.1, h2'.trans h3'.2⟩⟩, rfl⟩
      · rintro ⟨r, hr, s, ⟨h1, h2⟩, h3⟩
        have hr' : r = (p.1.1, (p.1.2, p.2)) := hr
        subst hr'
        have h1' : p.1.1 = s.1 := h1
        have h2' : p.1.2 = s.2 ∧ p.2 = s.2 := (ΔRel_recip_apply n _ s.2).mp h2
        have h3' : s.1 = w ∧ s.2 = w := (ΔRel_recip_apply n s w).mp h3
        exact ⟨(w, w), ⟨(ΔRel_recip_apply n p.1 w).mpr
          ⟨h1'.trans h3'.1, h2'.1.trans h3'.2⟩, h2'.2.trans h3'.2⟩, rfl⟩
    «∇_comm» := fun n => by
      apply RelSet.hom_ext; intro p z
      constructor
      · rintro ⟨m, hm, h⟩
        have hm' : m = (p.2, p.1) := hm
        subst hm'
        have h' := (ΔRel_recip_apply n _ z).mp h
        exact (ΔRel_recip_apply n p z).mpr ⟨h'.2, h'.1⟩
      · intro h
        have h' := (ΔRel_recip_apply n p z).mp h
        exact ⟨(p.2, p.1), rfl, (ΔRel_recip_apply n _ z).mpr ⟨h'.2, h'.1⟩⟩
    «∇_unit» := fun n => by
      apply RelSet.hom_ext; intro x w
      constructor
      · rintro ⟨r, hr, s, ⟨h1, _⟩, h2⟩
        have hr' : r = (x, PUnit.unit) := hr
        subst hr'
        exact (h1 : x = s.1).trans ((ΔRel_recip_apply n s w).mp h2).1
      · intro h
        have h' : x = w := h
        exact ⟨(x, PUnit.unit), rfl, (w, w), ⟨h', rfl⟩, rfl⟩

    «∇Δ_le_𝟙» := fun n => RelSet.le_iff.mpr <| by
      rintro p q ⟨z, h1, h2⟩
      have h1' := (ΔRel_recip_apply n p z).mp h1
      have h2' : q = (z, z) := h2
      exact Prod.ext_iff.mpr ⟨h1'.1.trans (congrArg Prod.fst h2').symm,
        h1'.2.trans (congrArg Prod.snd h2').symm⟩
    «𝟙_le_Δ∇» := fun n => RelSet.le_iff.mpr <| by
      intro x y h
      exact ⟨(x, x), rfl, (ΔRel_recip_apply n _ y).mpr ⟨h, h⟩⟩
    «?!_le_𝟙» := fun n => RelSet.le_iff.mpr <| by
      rintro u v _; rfl
    «𝟙_le_!?» := fun n => RelSet.le_iff.mpr <| by
      intro x y _; exact ⟨PUnit.unit, rfl, rfl⟩

    frob_left := fun n => by
      apply RelSet.hom_ext; intro p q
      constructor
      · rintro ⟨⟨r1, r2⟩, ⟨h1, h2⟩, s, hs, h3, h4⟩
        have h1' : p.1 = r1 := h1
        have h2' : r2 = (p.2, p.2) := h2
        subst h2'
        have hs' : s = ((r1, p.2), p.2) := hs
        subst hs'
        have h3' := (ΔRel_recip_apply n (r1, p.2) q.1).mp h3
        have h4' : p.2 = q.2 := h4
        -- The copy on the right strand forces `p.2 = q.1 = q.2`, and the merge `p.1 = q.1`.
        exact ⟨q.1, Prod.ext_iff.mpr ⟨h1'.trans h3'.1, h3'.2⟩,
          Prod.ext_iff.mpr ⟨rfl, h4'.symm.trans h3'.2⟩⟩
      · rintro ⟨z, h1, h2⟩
        have h1' : p = (z, z) := h1
        have h2' : q = (z, z) := h2
        subst h1'; subst h2'
        exact ⟨(z, (z, z)), ⟨rfl, rfl⟩, ((z, z), z), rfl, rfl, rfl⟩
    frob_right := fun n => by
      apply RelSet.hom_ext; intro p q
      constructor
      · rintro ⟨⟨r1, r2⟩, ⟨h1, h2⟩, s, hs, h3, h4⟩
        have h1' : r1 = (p.1, p.1) := h1
        subst h1'
        have h2' : p.2 = r2 := h2
        subst h2'
        have hs' : s = (p.1, (p.1, p.2)) := hs
        subst hs'
        have h3' : p.1 = q.1 := h3
        have h4' := (ΔRel_recip_apply n (p.1, p.2) q.2).mp h4
        -- The copy on the left strand forces `p.1 = q.1 = q.2`, and the merge `p.2 = q.2`.
        have hq2 : q.2 = q.1 := h4'.1.symm.trans h3'
        exact ⟨q.1, Prod.ext_iff.mpr ⟨h3', h4'.2.trans hq2⟩, Prod.ext_iff.mpr ⟨rfl, hq2⟩⟩
      · rintro ⟨z, h1, h2⟩
        have h1' : p = (z, z) := h1
        have h2' : q = (z, z) := h2
        subst h1'; subst h2'
        exact ⟨((z, z), z), ⟨rfl, rfl⟩, (z, (z, z)), rfl, rfl, rfl⟩

    lax_Δ := fun R => RelSet.le_iff.mpr <| by
      rintro x q ⟨y, hR, hq⟩
      have hq' : q = (y, y) := hq
      subst hq'
      exact ⟨(x, x), rfl, hR, hR⟩
    lax_! := fun R => RelSet.le_iff.mpr <| by
      rintro x u ⟨_, _, hu⟩; exact hu }

@[simp] theorem delta_eq (n : RelSet.{u}) : CartBicat.Δ n = ΔRel n := rfl
@[simp] theorem bang_eq (n : RelSet.{u}) : CartBicat.«!» n = «!Rel» n := rfl
@[simp] theorem nabla_eq (n : RelSet.{u}) : CartBicat.«∇» n = (ΔRel n)° := rfl
@[simp] theorem unitR_eq (n : RelSet.{u}) : CartBicat.«?» n = («!Rel» n)° := rfl

/-! ### Agreement — the load-bearing part of this file

  The derived diagram operations are not new operations on `Rel(Set)`: they are the ones the repo
  already had.  Without these, a `CartBicat` theorem would say nothing about the AOP corpus. -/

/-- The meet `Δ;(R ⊗ S);∇` IS the allegory intersection (`Allegory RelSet`,
    `AOP/A6_1_RelSet.lean`): copying the input and merging the two outputs forces the two results
    to coincide. -/
theorem meet_eq_inter {a b : RelSet.{u}} (R S : a ⟶ b) : meet R S = R ∩ S := by
  apply RelSet.hom_ext; intro x y
  constructor
  · rintro ⟨p, hp, m, ⟨hR, hS⟩, hm⟩
    have hp' : p = (x, x) := hp
    subst hp'
    have hm' := (ΔRel_recip_apply b m y).mp hm
    exact ⟨hm'.1 ▸ hR, hm'.2 ▸ hS⟩
  · rintro ⟨hR, hS⟩
    exact ⟨(x, x), rfl, (y, y), ⟨hR, hS⟩, rfl⟩

/-- `⊤ = !;?` relates everything to everything — discard the input, then create any output. -/
theorem top_apply {a b : RelSet.{u}} (x : a.carrier) (y : b.carrier) : top a b x y :=
  ⟨PUnit.unit, rfl, rfl⟩

/-- **The converse built by bending wires is the ordinary relational converse.**  This is the check
    that the phase-3 definition of `conv` is the right one: `conv` is assembled from cups, caps and
    associators with no mention of `°`, and it lands on `Allegory.recip`. -/
theorem conv_eq_recip {a b : RelSet.{u}} (R : a ⟶ b) : CartBicat.conv R = R° := by
  apply RelSet.hom_ext; intro y x
  constructor
  · rintro ⟨w, hw, v, ⟨⟨z, _, hz⟩, hw2⟩, t, ht, s, ⟨hs, m, ⟨hR, hm2⟩, z', hz', _⟩, hx⟩
    have hw' : w = (PUnit.unit, y) := hw
    subst hw'
    have hz2 : v.1 = (z, z) := hz
    have hw2' : y = v.2 := hw2
    have ht' : t = (v.1.1, (v.1.2, v.2)) := ht
    subst ht'
    have hs' : v.1.1 = s.1 := hs
    have hx' : x = s.1 := hx
    have hm2' : v.2 = m.2 := hm2
    have hz'' : m = (z', z') := hz'
    -- `m.1 = z' = m.2 = v.2 = y`, and `x = s.1 = v.1.1 = z = v.1.2`, so `hR : R x y`.
    have hm1 : m.1 = y :=
      (congrArg Prod.fst hz'').trans ((congrArg Prod.snd hz'').symm.trans (hm2'.symm.trans hw2'.symm))
    have hv12 : v.1.2 = x := (congrArg Prod.snd hz2).trans
      ((congrArg Prod.fst hz2).symm.trans (hs'.trans hx'.symm))
    exact hm1 ▸ hv12 ▸ hR
  · intro hR
    have hR' : R x y := hR
    exact ⟨(PUnit.unit, y), rfl, ((x, x), y), ⟨⟨x, rfl, rfl⟩, rfl⟩, (x, (x, y)), rfl,
      (x, PUnit.unit), ⟨rfl, (y, y), ⟨hR', rfl⟩, y, rfl, rfl⟩, rfl⟩

end Freyd.Diag
