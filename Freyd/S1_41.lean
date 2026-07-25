/-
  Freyd & Scedrov, *Categories and Allegories* §1.41 (§1.41–§1.412)
  Monic, MonicPair, MonicFamily, IsIso.
-/

import Freyd.S1_1

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

def Monic {X Y : 𝒞} (m : X ⟶ Y) : Prop :=
  ∀ {W : 𝒞} (g h : W ⟶ X), g ≫ m = h ≫ m → g = h

/-- A MONIC PAIR x: T→A, y: T→B: jointly left-cancellable (§1.41). -/
def MonicPair {T A B : 𝒞} (x : T ⟶ A) (y : T ⟶ B) : Prop :=
  ∀ {W : 𝒞} (f g : W ⟶ T), f ≫ x = g ≫ x → f ≫ y = g ≫ y → f = g

/-- MONIC FAMILY {xᵢ: T→Aᵢ}: jointly left-cancellable (§1.412). -/
def MonicFamily {T : 𝒞} {I : Type} (feet : I → 𝒞) (cols : (i : I) → T ⟶ feet i) : Prop :=
  ∀ {X : 𝒞} (f g : X ⟶ T), (∀ i, f ≫ cols i = g ≫ cols i) → f = g

def IsIso {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y

/-- Isomorphisms are closed under composition; the inverse is `g⁻¹ ≫ f⁻¹`. -/
theorem isIso_comp {X Y Z : 𝒞} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  obtain ⟨f', hf1, hf2⟩ := hf
  obtain ⟨g', hg1, hg2⟩ := hg
  exact ⟨g' ≫ f',
    by rw [Cat.assoc, ← Cat.assoc g, hg1, Cat.id_comp, hf1],
    by rw [Cat.assoc, ← Cat.assoc f', hf2, Cat.id_comp, hg2]⟩

/-- A split mono is monic: a map with a retraction is left-cancellable. -/
theorem mono_of_retraction {X Y : 𝒞} (m : X ⟶ Y) (r : Y ⟶ X)
    (hr : m ≫ r = Cat.id X) : Monic m := by
  intro W g h hgh
  calc g = g ≫ m ≫ r   := by rw [hr, Cat.comp_id]
    _    = (g ≫ m) ≫ r := (Cat.assoc _ _ _).symm
    _    = (h ≫ m) ≫ r := by rw [hgh]
    _    = h ≫ m ≫ r   := Cat.assoc _ _ _
    _    = h           := by rw [hr, Cat.comp_id]

/-! ## §1.413  Containment of tables

  Given tables (T; x₁,…,xₙ) and (T'; x'₁,…,x'ₙ) over the same feet,
  the first is CONTAINED in the second if there exists z : T → T' with
  z ≫ x'ᵢ = xᵢ for all i.  The witness z is unique and monic.
  Containment is a pre-order on tables and a partial order on relations
  (mutual containment ↔ isomorphism of tops).
-/

/-- (T; cols) is CONTAINED in (T'; cols') if ∃ z : T → T' with z ≫ cols' i = cols i. -/
def TableContained {I : Type} {feet : I → 𝒞}
    {T : 𝒞} (cols  : (i : I) → T  ⟶ feet i) (_hm  : MonicFamily feet cols)
    {T' : 𝒞} (cols' : (i : I) → T' ⟶ feet i) (_hm' : MonicFamily feet cols') : Prop :=
  ∃ z : T ⟶ T', ∀ i, z ≫ cols' i = cols i

/-- The containment morphism is unique (cols' is a monic family). -/
theorem tableContained_unique {I : Type} {feet : I → 𝒞}
    {T : 𝒞}  (cols  : (i : I) → T  ⟶ feet i) (_hm  : MonicFamily feet cols)
    {T' : 𝒞} (cols' : (i : I) → T' ⟶ feet i) (hm' : MonicFamily feet cols')
    (z w : T ⟶ T') (hz : ∀ i, z ≫ cols' i = cols i) (hw : ∀ i, w ≫ cols' i = cols i) :
    z = w :=
  hm' z w (fun i => by rw [hz i, hw i])

/-- The containment morphism is monic (the source monic family transfers injectivity). -/
theorem tableContained_mono {I : Type} {feet : I → 𝒞}
    {T : 𝒞}  (cols  : (i : I) → T  ⟶ feet i) (hm  : MonicFamily feet cols)
    {T' : 𝒞} (cols' : (i : I) → T' ⟶ feet i) (_hm' : MonicFamily feet cols')
    (z : T ⟶ T') (hz : ∀ i, z ≫ cols' i = cols i) : Monic z :=
  fun {W} f g hfg => hm f g (fun i => by
    calc f ≫ cols i = f ≫ z ≫ cols' i := by rw [hz i]
      _              = g ≫ z ≫ cols' i := by rw [← Cat.assoc, hfg, Cat.assoc]
      _              = g ≫ cols i      := by rw [hz i])

/-- Containment is reflexive (witness = identity). -/
theorem tableContained_refl {I : Type} {feet : I → 𝒞}
    {T : 𝒞} (cols : (i : I) → T ⟶ feet i) (hm : MonicFamily feet cols) :
    TableContained cols hm cols hm :=
  ⟨Cat.id T, fun i => Cat.id_comp (cols i)⟩

/-- Containment is transitive. -/
theorem tableContained_trans {I : Type} {feet : I → 𝒞}
    {T : 𝒞}   (cols   : (i : I) → T   ⟶ feet i) (hm   : MonicFamily feet cols)
    {T' : 𝒞}  (cols'  : (i : I) → T'  ⟶ feet i) (hm'  : MonicFamily feet cols')
    {T'' : 𝒞} (cols'' : (i : I) → T'' ⟶ feet i) (hm'' : MonicFamily feet cols'')
    (h1 : TableContained cols hm cols' hm') (h2 : TableContained cols' hm' cols'' hm'') :
    TableContained cols hm cols'' hm'' := by
  obtain ⟨z, hz⟩ := h1; obtain ⟨w, hw⟩ := h2
  exact ⟨z ≫ w, fun i => by rw [Cat.assoc, hw i, hz i]⟩

/-- Mutual containment gives an isomorphism of tops (partial order up to iso). -/
theorem tableContained_antisymm {I : Type} {feet : I → 𝒞}
    {T : 𝒞}  (cols  : (i : I) → T  ⟶ feet i) (hm  : MonicFamily feet cols)
    {T' : 𝒞} (cols' : (i : I) → T' ⟶ feet i) (hm' : MonicFamily feet cols')
    (h1 : TableContained cols hm cols' hm') (h2 : TableContained cols' hm' cols hm) :
    ∃ (z : T ⟶ T') (w : T' ⟶ T), (∀ i, z ≫ cols' i = cols i) ∧
        (∀ i, w ≫ cols i = cols' i) ∧ z ≫ w = Cat.id T ∧ w ≫ z = Cat.id T' := by
  obtain ⟨z, hz⟩ := h1; obtain ⟨w, hw⟩ := h2
  refine ⟨z, w, hz, hw, ?_, ?_⟩
  · -- z ≫ w = id T: both make cols agree, use hm
    exact hm (z ≫ w) (Cat.id T) (fun i => by rw [Cat.assoc, hw i, hz i, Cat.id_comp])
  · -- w ≫ z = id T': both make cols' agree, use hm'
    exact hm' (w ≫ z) (Cat.id T') (fun i => by rw [Cat.assoc, hz i, hw i, Cat.id_comp])

/-! ## §1.414  Monic iff subterminator in the slice

  In the slice category A/B, the terminal object is ⟨B, id_B⟩.
  A morphism f : A → B, viewed as an object ⟨A, f⟩ of A/B, is a
  SUBTERMINATOR in A/B iff the terminal map ⟨A, f⟩ → ⟨B, id_B⟩
  (whose underlying map is f itself) is monic in A/B.
  We prove this is equivalent to f being monic in A.

  (We inline the slice-category structure here; S1_26.lean cannot be
  imported in S1_41.lean because it depends on S1_41.)
-/

/-- Monic in the slice A/B: the Over-hom `f` is left-cancellable among
    maps that commute with the projection to B. -/
def MonoInSlice {A B : 𝒞} (f : A ⟶ B) : Prop :=
  ∀ {W : 𝒞} (h : W ⟶ B) (u v : W ⟶ A), u ≫ f = h → v ≫ f = h → u = v

/-- §1.414: f : A → B is monic iff it is a subterminator in the slice A/B. -/
theorem mono_iff_monoInSlice {A B : 𝒞} (f : A ⟶ B) : Monic f ↔ MonoInSlice f := by
  constructor
  · intro hm W h u v hu hv
    exact hm u v (by rw [hu, hv])
  · intro hs W u v huv
    exact hs (u ≫ f) u v rfl (by rw [huv])
