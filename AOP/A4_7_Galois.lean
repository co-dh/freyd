/-
  Port of AoPA `Relations/Galois.agda` into the concrete allegory `Rel(Set)`.

  Galois connection between a pair of functions `f : A → B`, `g : B → A` and a pair of
  relations `≼ : B ⟶ B`, `⊴ : A ⟶ A`, in the two equivalent formulations AoPA gives:

  * pointwise  `galois f g ≼ ⊴  =  ∀ x y, f x ≼ y ⇔ x ⊴ g y`;
  * point-free `galois-○ f g R S =  (fun f)˘ ○ R ≑ S ○ fun g`.

  Translation (aopa → repo): `X ○ Y ↦ Y ≫ X` (composition reverses), `R ˘ ↦ R°`, `fun f ↦ graph f`.
  A relation `P : B ← A` with membership `P b a` becomes `P : a ⟶ b` with `P a b`, so the
  argument order flips: aopa `f x ≼ y` (= `≼ (f x) y`) becomes `R y (f x)`, and aopa `x ⊴ g y`
  becomes `S (g y) x`.  Under this dictionary
      `(fun f)˘ ○ R  ↦  R ≫ (graph f)°`  and  `S ○ fun g  ↦  graph g ≫ S`,
  both of type `b ⟶ a`, and the point-free equation is `R ≫ (graph f)° = graph g ≫ S`.

  Mathlib-free; axioms ⊆ {propext}.
-/
import AOP.A6_1_RelSet
import Freyd.S2_01  -- Reflexive / Transitive on `𝒜`

universe u

namespace Freyd.Alg
namespace RelSet

variable {a b : RelSet.{u}}

/-- Galois connection, pointwise (AoPA `galois`): `∀ x y, f x ≼ y ⇔ x ⊴ g y`. -/
def galois (f : a.carrier → b.carrier) (g : b.carrier → a.carrier)
    (R : b ⟶ b) (S : a ⟶ a) : Prop :=
  ∀ x y, R y (f x) ↔ S (g y) x

/-- Point-free formulation of the Galois connection (AoPA `galois-○`):
    `(fun f)˘ ○ R ≑ S ○ fun g`, i.e. `R ≫ (graph f)° = graph g ≫ S`. -/
def galoisPF (f : a.carrier → b.carrier) (g : b.carrier → a.carrier)
    (R : b ⟶ b) (S : a ⟶ a) : Prop :=
  R ≫ (graph f)° = graph g ≫ S

variable {f : a.carrier → b.carrier} {g : b.carrier → a.carrier} {R : b ⟶ b} {S : a ⟶ a}

/-- Both composites reduce pointwise: `(R ≫ (graph f)°) y x ↔ R y (f x)`. -/
private theorem comp_graphf_recip (y : b.carrier) (x : a.carrier) :
    (R ≫ (graph f)°) y x ↔ R y (f x) :=
  ⟨fun ⟨_, hR, hz⟩ => hz ▸ hR, fun hR => ⟨f x, hR, rfl⟩⟩

/-- `(graph g ≫ S) y x ↔ S (g y) x`. -/
private theorem graphg_comp (y : b.carrier) (x : a.carrier) :
    (graph g ≫ S) y x ↔ S (g y) x :=
  ⟨fun ⟨_, hw, hS⟩ => hw ▸ hS, fun hS => ⟨g y, rfl, hS⟩⟩

/-- AoPA `galois-equiv-⇒`: the pointwise connection implies the point-free one. -/
theorem galois_equiv_mpr (gal : galois f g R S) : galoisPF f g R S :=
  hom_ext fun y x => (comp_graphf_recip y x).trans ((gal x y).trans (graphg_comp y x).symm)

/-- AoPA `galois-equiv-⇐`: the point-free connection implies the pointwise one. -/
theorem galois_equiv_mp (galpf : galoisPF f g R S) : galois f g R S := fun x y => by
  have h : (R ≫ (graph f)°) y x ↔ (graph g ≫ S) y x := by
    rw [galpf]
  exact (comp_graphf_recip y x).symm.trans (h.trans (graphg_comp y x))

/-- The two formulations of the Galois connection agree. -/
theorem galois_iff : galois f g R S ↔ galoisPF f g R S :=
  ⟨galois_equiv_mpr, galois_equiv_mp⟩

/-! ### Monotonicity of the lower adjoint (AoPA `monotonic-lower` / `monotonic-lower-○`) -/

/-- AoPA `monotonic-lower`: for preorders `≼`, `⊴`, the lower adjoint `f` is monotone,
    `x₀ ⊴ x₁ → f x₀ ≼ f x₁`.  (In repo orientation `S x₁ x₀ → R (f x₁) (f x₀)`.) -/
theorem monotonic_lower (hRrefl : Reflexive R) (hStrans : Transitive S)
    (gal : galois f g R S) {x₀ x₁ : a.carrier} (h : S x₁ x₀) : R (f x₁) (f x₀) := by
  -- `x ⊴ g (f x)`, from reflexivity of `≼` through the connection.
  have hunit : ∀ x, S (g (f x)) x := fun x =>
    (gal x (f x)).mp (le_iff.mp hRrefl (f x) (f x) rfl)
  -- `x₀ ⊴ g (f x₁)` by transitivity, then transport across the connection.
  have hmid : S (g (f x₁)) x₀ := le_iff.mp hStrans _ _ ⟨x₁, hunit x₁, h⟩
  exact (gal x₀ (f x₁)).mpr hmid

/-- AoPA `monotonic-lower-○`: the point-free form of monotonicity,
    `⊴ ○ (fun f)˘ ⊑ (fun f)˘ ○ ≼`, i.e. `(graph f)° ≫ S ⊑ R ≫ (graph f)°`. -/
theorem monotonic_lower_pf (hRrefl : Reflexive R) (hStrans : Transitive S)
    (gal : galois f g R S) : (graph f)° ≫ S ⊑ R ≫ (graph f)° := by
  rw [le_iff]
  rintro y x ⟨z, hz, hSzx⟩
  -- `hz : (graph f)° y z` unfolds to `y = f z`; `hSzx : S z x`.
  refine ⟨f x, ?_, rfl⟩
  -- goal `R y (f x)`; rewrite `y = f z`, then apply monotonicity at `x₁ := z`, `x₀ := x`.
  rw [(hz : y = f z)]
  exact monotonic_lower hRrefl hStrans gal (x₀ := x) (x₁ := z) hSzx

/-! ### The "easy" and "hard" halves (AoPA `galois-easy-⇒` / `galois-hard-⇒`)

  These package `graph g` and its converse; ported as point-free calc chains that reuse the
  generic allegory laws (which hold in `Rel(Set)`). -/

/-- AoPA `galois-easy-⇒`: `fun g ⊑ (fun f)˘ ○ R`, i.e. `graph g ⊑ R ≫ (graph f)°`.
    (`≼`-reflexivity is not needed; only the point-free connection.) -/
theorem galois_easy_mpr (gal : galois f g R S) (hSrefl : Reflexive S) :
    graph g ⊑ R ≫ (graph f)° := by
  rw [galois_equiv_mpr gal]  -- `R ≫ (graph f)° = graph g ≫ S`
  -- `graph g ⊑ graph g ≫ S` since `id ⊑ S` and `graph g ≫ id = graph g`.
  calc graph g = graph g ≫ Cat.id a := (Cat.comp_id _).symm
    _ ⊑ graph g ≫ S := comp_mono_left (graph g) hSrefl

/-- AoPA `galois-hard-⇒`: `fun g ○ ((fun f)˘ ○ R)˘ ⊑ S˘`, i.e.
    `(R ≫ (graph f)°)° ≫ graph g ⊑ S°`. -/
theorem galois_hard_mpr (gal : galois f g R S) :
    (R ≫ (graph f)°)° ≫ graph g ⊑ S° := by
  -- From `R ≫ (graph f)° = graph g ≫ S`, take converses.
  have hpf : (R ≫ (graph f)°)° = (graph g ≫ S)° := by rw [galois_equiv_mpr gal]
  rw [hpf, Allegory.recip_comp]  -- `(graph g ≫ S)° = S° ≫ (graph g)°`
  -- `(S° ≫ (graph g)°) ≫ graph g ⊑ S°`, using `(graph g)° ≫ graph g ⊑ id`.
  calc (S° ≫ (graph g)°) ≫ graph g
      = S° ≫ ((graph g)° ≫ graph g) := Cat.assoc _ _ _
    _ ⊑ S° ≫ Cat.id a := comp_mono_left (S°) (graph_simple g)
    _ = S° := Cat.comp_id _

end RelSet
end Freyd.Alg
