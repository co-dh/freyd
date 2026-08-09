/-
  Freyd & Scedrov, *Categories and Allegories* §1.8–§1.81
  Adjoint functors, reflective/coreflective subcategories.

  §1.81  ADJOINT PAIR OF FUNCTORS — hom-set bijection, unit, counit, triangle identities
  §1.813 REFLECTIVE SUBCATEGORY, REFLECTION
  §1.816 COREFLECTIVE INCLUSION
  §1.815 CLOSURE OPERATION (poset case: idempotent, inflationary, order-preserving)
-/

module

public import Freyd.S1_10
public import Freyd.S1_18
public import Freyd.S1_51_Order  -- §1.51 IsClosureOp (poset closure operations, §1.815)


universe v u u₁ u₂

namespace Freyd

variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]

/-! ## §1.81  Adjoint pair of functors

  F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 form an ADJOINT PAIR if there is a
  natural equivalence (F A ⟶ B) ≃ (A ⟶ G B) (§1.81).
  F = LEFT-ADJOINT of G, G = RIGHT-ADJOINT of F. -/

/-- An adjoint pair F ⊣ G: a bijection (F A ⟶ B) ≃ (A ⟶ G B)
    natural in A (contravariant) and B (covariant) (§1.81). -/
public structure Adjunction (F : Functor 𝒞 𝒟) (G : Functor 𝒟 𝒞) where
  φ {A B} (f : F.obj A ⟶ B) : (A ⟶ G.obj B)
  ψ {A B} (f : A ⟶ G.obj B) : (F.obj A ⟶ B)
  φψ {A B} (f : A ⟶ G.obj B) : φ (ψ f) = f
  ψφ {A B} (f : F.obj A ⟶ B) : ψ (φ f) = f
  φ_nat_left {A' A B} (a : A' ⟶ A) (h : F.obj A ⟶ B) : φ (F.map a ≫ h) = a ≫ φ h
  φ_nat_right {A B B'} (h : F.obj A ⟶ B) (b : B ⟶ B') : φ (h ≫ b) = φ h ≫ G.map b

infix:25 " ⊣ " => Adjunction

/-- F is a LEFT-ADJOINT of G. -/
public class LeftAdjoint (F : Functor 𝒞 𝒟) (G : Functor 𝒟 𝒞) where
  adj : F ⊣ G

/-- G is a RIGHT-ADJOINT of F. -/
public class RightAdjoint (G : Functor 𝒟 𝒞) (F : Functor 𝒞 𝒟) where
  adj : F ⊣ G

section AdjunctionProperties
variable {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} (adj : F ⊣ G)

public theorem φ_inj {A B} {f₁ f₂ : F.obj A ⟶ B} (h : adj.φ f₁ = adj.φ f₂) : f₁ = f₂ := by
  calc
    f₁ = adj.ψ (adj.φ f₁) := by rw [adj.ψφ]
    _ = adj.ψ (adj.φ f₂) := by rw [h]
    _ = f₂ := by rw [adj.ψφ]

/-! ### Derived naturality for ψ (= φ⁻¹) -/

public theorem ψ_nat_left {A' A B} (a : A' ⟶ A) (g : A ⟶ G.obj B) :
    adj.ψ (a ≫ g) = F.map a ≫ adj.ψ g :=
  φ_inj adj <| by
    rw [adj.φ_nat_left, adj.φψ, adj.φψ]

public theorem ψ_nat_right {A B B'} (g : A ⟶ G.obj B) (b : B ⟶ B') :
    adj.ψ (g ≫ G.map b) = adj.ψ g ≫ b :=
  φ_inj adj <| by
    rw [adj.φ_nat_right, adj.φψ, adj.φψ]

/-! ### Unit and counit -/

/-- The UNIT η_A : A → G(F A) is the adjoint of id_{F A} (§1.81). -/
@[expose] public def unit (A : 𝒞) : A ⟶ G.obj (F.obj A) := adj.φ (Cat.id (F.obj A))

/-- The COUNIT ε_B : F(G B) → B is the adjoint of id_{G B} (§1.81). -/
@[expose] public def counit (B : 𝒟) : F.obj (G.obj B) ⟶ B := adj.ψ (Cat.id (G.obj B))

/-- Unit naturality: f ≫ η_B = η_A ≫ G(F f). -/
public theorem unit_naturality {A B : 𝒞} (f : A ⟶ B) :
    f ≫ unit adj B = unit adj A ≫ G.map (F.map f) := by
  dsimp [unit]
  calc
    f ≫ adj.φ (Cat.id (F.obj B)) = adj.φ (F.map f ≫ Cat.id (F.obj B)) := by
      rw [adj.φ_nat_left]
    _ = adj.φ (F.map f) := by rw [Cat.comp_id]
    _ = adj.φ (Cat.id (F.obj A) ≫ F.map f) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F.obj A)) ≫ G.map (F.map f) := by rw [adj.φ_nat_right]

/-- Counit naturality: F(G f) ≫ ε_B = ε_A ≫ f. -/
theorem counit_naturality {A B : 𝒟} (f : A ⟶ B) :
    F.map (G.map f) ≫ counit adj B = counit adj A ≫ f := by
  dsimp [counit]
  calc
    F.map (G.map f) ≫ adj.ψ (Cat.id (G.obj B)) =
      adj.ψ (G.map f ≫ Cat.id (G.obj B)) := by
      rw [← ψ_nat_left adj (G.map f) (Cat.id (G.obj B))]
    _ = adj.ψ (G.map f) := by rw [Cat.comp_id]
    _ = adj.ψ (Cat.id (G.obj A) ≫ G.map f) := by rw [Cat.id_comp]
    _ = adj.ψ (Cat.id (G.obj A)) ≫ f := by rw [ψ_nat_right adj (Cat.id (G.obj A)) f]

/-- Triangle identity I: F(η_A) ≫ ε_{F A} = id_{F A}. -/
public theorem triangle_one (A : 𝒞) : F.map (unit adj A) ≫ counit adj (F.obj A) = Cat.id (F.obj A) := by
  dsimp [unit, counit]
  calc
    F.map (adj.φ (Cat.id (F.obj A))) ≫ adj.ψ (Cat.id (G.obj (F.obj A))) =
      adj.ψ (adj.φ (Cat.id (F.obj A)) ≫ Cat.id (G.obj (F.obj A))) := by
      rw [ψ_nat_left adj (adj.φ (Cat.id (F.obj A))) (Cat.id (G.obj (F.obj A)))]
    _ = adj.ψ (adj.φ (Cat.id (F.obj A))) := by rw [Cat.comp_id]
    _ = Cat.id (F.obj A) := by rw [adj.ψφ]

/-- Triangle identity II: η_{G B} ≫ G(ε_B) = id_{G B}. -/
public theorem triangle_two (B : 𝒟) : unit adj (G.obj B) ≫ G.map (counit adj B) = Cat.id (G.obj B) := by
  dsimp [unit, counit]
  calc
    adj.φ (Cat.id (F.obj (G.obj B))) ≫ G.map (adj.ψ (Cat.id (G.obj B))) =
      adj.φ (Cat.id (F.obj (G.obj B)) ≫ adj.ψ (Cat.id (G.obj B))) := by rw [adj.φ_nat_right]
    _ = adj.φ (adj.ψ (Cat.id (G.obj B))) := by rw [Cat.id_comp]
    _ = Cat.id (G.obj B) := by rw [adj.φψ]

/-- φ(h) = η_A ≫ G(h) — reconstruct φ from the unit. -/
public theorem φ_eq (h : F.obj A ⟶ B) : adj.φ h = unit adj A ≫ G.map h := by
  dsimp [unit]
  calc
    adj.φ h = adj.φ (Cat.id (F.obj A) ≫ h) := by rw [Cat.id_comp]
    _ = adj.φ (Cat.id (F.obj A)) ≫ G.map h := by rw [adj.φ_nat_right]

/-- ψ(g) = F(g) ≫ ε_B — reconstruct ψ from the counit. -/
public theorem ψ_eq (g : A ⟶ G.obj B) : adj.ψ g = F.map g ≫ counit adj B := by
  dsimp [counit]
  calc
    adj.ψ g = adj.ψ (g ≫ Cat.id (G.obj B)) := by rw [Cat.comp_id]
    _ = F.map g ≫ adj.ψ (Cat.id (G.obj B)) := by rw [ψ_nat_left adj g (Cat.id (G.obj B))]

end AdjunctionProperties

/-! ## §1.813 Reflective subcategories -/

/-- A subcategory via inclusion I : 𝒜' → 𝒞 is REFLECTIVE
    if I has a left adjoint (§1.813). The left adjoint is the REFLECTION. -/
public class ReflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : Functor 𝒜' 𝒞) where
  reflection : Functor 𝒞 𝒜'
  adj : LeftAdjoint reflection I

/-- §1.816: A subcategory is COREFLECTIVE if the inclusion has a right adjoint. -/
public class CoreflectiveSubcategory {𝒜' : Type u₁} [Cat.{v} 𝒜'] (I : Functor 𝒜' 𝒞) where
  coreflection : Functor 𝒞 𝒜'
  adj : RightAdjoint coreflection I

/-! ## §1.815  Closure operation

  On a poset, a CLOSURE OPERATION is order-preserving, idempotent,
  inflationary (§1.815). For a general category this is an idempotent monad.

  The book states three explicit axioms for the poset case:
    (i)  order-preserving:  x ≤ y → x̄ ≤ ȳ
    (ii) idempotent:        x̄ = x̄̄  (i.e. applying closure twice = once)
    (iii) inflationary:     x ≤ x̄ -/

/-- A CLOSURE OPERATION on a category (§1.815). T is the closure,
    η is the unit (inflationary), idem says Tη is an isomorphism. -/
structure ClosureOperation (𝒞 : Type u) [Cat.{v} 𝒞] where
  T : Functor 𝒞 𝒞
  η : (A : 𝒞) → A ⟶ T.obj A
  η_natural : ∀ {A B} (f : A ⟶ B), f ≫ η B = η A ≫ T.map f
  idem : ∀ (A : 𝒞), IsIso (T.map (η A))

/-! ### §1.815 Poset case: three explicit axioms

  When the ambient category is a poset (hom-sets are propositions),
  the three axioms reduce to the statements the book gives explicitly. -/

/-- Minimal partial-order typeclass used for the poset case of §1.815.
    (The repo avoids mathlib; this bundles LE with the three order axioms.) -/
public class PosetOrder (P : Type u) extends LE P where
  le_refl  : ∀ (x : P), x ≤ x
  le_trans : ∀ {x y z : P}, x ≤ y → y ≤ z → x ≤ z
  le_antisymm : ∀ {x y : P}, x ≤ y → y ≤ x → x = y

/-- A CLOSURE OPERATION on a poset (§1.815, poset case): a map `op` that is a closure operation
    for the poset order, i.e. the generic `Freyd.IsSup`-companion `Freyd.IsClosureOp`
    (Freyd/S1_51_Order) — order-preserving, inflationary, idempotent:

      (i)  x ≤ y  →  op x ≤ op y      (`isClosureOp.monotone`)
      (ii) x ≤ op x                   (`isClosureOp.inflationary`)
      (iii) op (op x) ≤ op x          (`isClosureOp.idempotent`; equivalently `op (op x) = op x`) -/
public structure ClosureOpPoset (P : Type u) [PosetOrder P] where
  /-- The closure operation -/
  op : P → P
  /-- `op` is a closure operation for the poset order `≤` (§1.815). -/
  isClosureOp : IsClosureOp (· ≤ ·) op

/-- The closure is idempotent as an equality: op(op x) = op x (§1.815). -/
theorem ClosureOpPoset.idem_eq {P : Type u} [po : PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : cl.op (cl.op x) = cl.op x :=
  cl.isClosureOp.idem_eq (fun h₁ h₂ => po.le_antisymm h₁ h₂) x

/-- A point x is CLOSED if op x = x (§1.815). -/
def ClosureOpPoset.IsClosed {P : Type u} [PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : Prop := cl.op x = x

/-- Every value of op is closed (§1.815). -/
theorem ClosureOpPoset.value_is_closed {P : Type u} [PosetOrder P]
    (cl : ClosureOpPoset P) (x : P) : cl.IsClosed (cl.op x) := cl.idem_eq x

/-- Universal property of the reflection: x ≤ y ↔ op x ≤ y for closed y (§1.815).
    This shows closed elements form a reflective sub-poset. -/
theorem ClosureOpPoset.reflection_universal {P : Type u} [po : PosetOrder P]
    (cl : ClosureOpPoset P) {x y : P} (hy : cl.IsClosed y) :
    x ≤ y ↔ cl.op x ≤ y := by
  constructor
  · intro h; exact hy ▸ cl.isClosureOp.monotone h
  · intro h; exact po.le_trans (cl.isClosureOp.inflationary x) h

/-! ## §1.817  Representability ⟺ left-adjoint criterion

  §1.817: G : 𝒟 → 𝒞 has a left-adjoint F iff (A, G(-)) is representable for all A.
  The forward direction: F A represents (A, G(-)) via the adjunction bijection.
  The converse: choose representing objects FA and the equivalence (A,G(-)) ≅ (FA,-);
  define Fx as the unique map making the naturality square commute. -/

/-- (A, G(-)) is REPRESENTABLE BY an object R ∈ 𝒟: a bijection
    (A ⟶ G B) ≃ (R ⟶ B), natural in B (§1.817). -/
public structure RepresentedBy {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
    (G : Functor 𝒟 𝒞) (A : 𝒞) (R : 𝒟) where
  φ {B : 𝒟} : (A ⟶ G.obj B) → (R ⟶ B)
  ψ {B : 𝒟} : (R ⟶ B) → (A ⟶ G.obj B)
  φψ {B : 𝒟} (f : R ⟶ B) : φ (ψ f) = f
  ψφ {B : 𝒟} (g : A ⟶ G.obj B) : ψ (φ g) = g
  /-- φ is natural in B: precomposing with G(b) on the right corresponds to
      postcomposing with b on the R side. -/
  φ_nat {B B' : 𝒟} (g : A ⟶ G.obj B) (b : B ⟶ B') :
    φ (g ≫ G.map b) = φ g ≫ b

/-- §1.817 (→): if F ⊣ G then (A, G(-)) is represented by F A. -/
@[expose] public def repr_of_adj {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
    {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞}
    (adj : F ⊣ G) (A : 𝒞) : RepresentedBy G A (F.obj A) where
  φ g  := adj.ψ g
  ψ h  := adj.φ h
  φψ f := adj.ψφ f
  ψφ g := adj.φψ g
  -- naturality: ψ (g ≫ G(b)) = ψ g ≫ b  (ψ_nat_right)
  φ_nat g b := ψ_nat_right adj g b

/-! ### Derived laws for `RepresentedBy` -/

section RepresentedByLaws
variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]
variable {G : Functor 𝒟 𝒞} {A : 𝒞} {R : 𝒟} (r : RepresentedBy G A R)

/-- φ is injective on `(A ⟶ G B)` (it is a bijection). -/
theorem RepresentedBy.φ_inj {B : 𝒟} {g₁ g₂ : A ⟶ G.obj B} (h : r.φ g₁ = r.φ g₂) : g₁ = g₂ := by
  rw [← r.ψφ g₁, ← r.ψφ g₂, h]

/-- ψ is natural in B (the inverse of `φ_nat`): ψ(f ≫ b) = ψ f ≫ G(b). -/
theorem RepresentedBy.ψ_nat {B B' : 𝒟} (f : R ⟶ B) (b : B ⟶ B') :
    r.ψ (f ≫ b) = r.ψ f ≫ G.map b :=
  r.φ_inj <| by rw [r.φ_nat, r.φψ, r.φψ]

end RepresentedByLaws

end Freyd
