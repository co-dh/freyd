module

/-
  Freyd & Scedrov, *Categories and Allegories* §1.51.

  BOOK-FAITHFUL PREORDER-LEVEL ORDER THEORY.  Freyd defines "an adjoint pair of functions
  between posets" ONCE (§1.51) and then reuses it: §1.7 `f# ⊣ f##`, §1.72 `∧ ⊣ →`,
  §1.723 frames, the direct-image / inverse-image adjunction, closure operators (§1.815).
  This module supplies that single definition together with the handful of generic lemmas
  those sites consume, so no carrier re-states adjunction / sup / closure laws by hand.

  Everything is stated over a BARE relation `le : α → α → Prop` — NO antisymmetry — because
  the carriers are genuine PREORDERS of representatives (subobjects up to iso, allegory
  hom-sets).  Reflexivity / transitivity, where a proof needs them, are passed as explicit
  hypotheses, so the module needs no per-carrier order typeclass and stays dependency-free.

  Composition is written in diagram order elsewhere; here the "lower" adjoint `f` is Freyd's
  left adjoint and the "upper" adjoint `g` the right adjoint (`f x ≤ y ↔ x ≤ g y`).
-/

namespace Freyd

universe u v

/-- A GALOIS CONNECTION (Freyd's "adjoint pair of functions between posets", §1.51) between a
    preorder `(α, le₁)` and a preorder `(β, le₂)`: `f` is the LOWER (left) adjoint, `g` the
    UPPER (right) adjoint, characterised by `le₂ (f x) y ↔ le₁ x (g y)`. -/
@[expose] public def GaloisConnection {α : Type u} {β : Type v}
    (le₁ : α → α → Prop) (le₂ : β → β → Prop) (f : α → β) (g : β → α) : Prop :=
  ∀ x y, le₂ (f x) y ↔ le₁ x (g y)

/-- `x` is a SUP (least upper bound) of the family `S` for the relation `le`: an upper bound of
    `S` that lies below every other upper bound. -/
public structure IsSup {α : Type u} (le : α → α → Prop) (S : α → Prop) (x : α) : Prop where
  /-- `x` is an upper bound of `S`. -/
  upper : ∀ y, S y → le y x
  /-- `x` is the least upper bound. -/
  least : ∀ u, (∀ y, S y → le y u) → le x u

/-- `c` is a CLOSURE OPERATION for the relation `le` (§1.815): inflationary, monotone,
    idempotent. -/
public structure IsClosureOp {α : Type u} (le : α → α → Prop) (c : α → α) : Prop where
  /-- (ii) inflationary: `x ≤ c x`. -/
  inflationary : ∀ x, le x (c x)
  /-- (i) order-preserving: `x ≤ y → c x ≤ c y`. -/
  monotone : ∀ {x y}, le x y → le (c x) (c y)
  /-- (iii) idempotent (`≤` half): `c (c x) ≤ c x`. -/
  idempotent : ∀ x, le (c (c x)) (c x)

/-! ### Sup uniqueness -/

/-- The sup is unique when `le` is antisymmetric. -/
public theorem IsSup.unique {α : Type u} {le : α → α → Prop}
    (antisymm : ∀ {a b : α}, le a b → le b a → a = b)
    {S : α → Prop} {x x' : α} (hx : IsSup le S x) (hx' : IsSup le S x') : x = x' :=
  antisymm (hx.least x' hx'.upper) (hx'.least x hx.upper)

/-! ### Galois-connection lemmas -/

namespace GaloisConnection

variable {α : Type u} {β : Type v} {le₁ : α → α → Prop} {le₂ : β → β → Prop}
  {f : α → β} {g : β → α}

/-- The LOWER (left) adjoint is monotone. -/
public theorem monotone_l (h : GaloisConnection le₁ le₂ f g)
    (refl₂ : ∀ b, le₂ b b) (trans₁ : ∀ {a b c : α}, le₁ a b → le₁ b c → le₁ a c)
    {x x' : α} (hx : le₁ x x') : le₂ (f x) (f x') :=
  (h x (f x')).mpr (trans₁ hx ((h x' (f x')).mp (refl₂ _)))

/-- The UPPER (right) adjoint is monotone. -/
public theorem monotone_u (h : GaloisConnection le₁ le₂ f g)
    (refl₁ : ∀ a, le₁ a a) (trans₂ : ∀ {a b c : β}, le₂ a b → le₂ b c → le₂ a c)
    {y y' : β} (hy : le₂ y y') : le₁ (g y) (g y') :=
  (h (g y) y').mp (trans₂ ((h (g y) y).mpr (refl₁ _)) hy)

/-- The LOWER adjoint preserves sups: if `x` is a sup of `S`, then `f x` is a sup of the image
    `f '' S`.  (Freyd Ex 4.39/4.40; a left adjoint preserves all existing joins.) -/
public theorem map_isSup (h : GaloisConnection le₁ le₂ f g)
    (refl₂ : ∀ b, le₂ b b) (trans₁ : ∀ {a b c : α}, le₁ a b → le₁ b c → le₁ a c)
    {S : α → Prop} {x : α} (hx : IsSup le₁ S x) :
    IsSup le₂ (fun y => ∃ z, S z ∧ y = f z) (f x) where
  upper := by
    rintro y ⟨z, hz, rfl⟩
    exact h.monotone_l refl₂ trans₁ (hx.upper z hz)
  least u hu :=
    (h x u).mpr (hx.least (g u) (fun z hz => (h z u).mp (hu (f z) ⟨z, hz, rfl⟩)))

end GaloisConnection

/-! ### Closure-operation lemmas -/

namespace IsClosureOp

variable {α : Type u} {le : α → α → Prop} {c : α → α}

/-- The closure is idempotent as an equality (needs antisymmetry). -/
public theorem idem_eq (antisymm : ∀ {a b : α}, le a b → le b a → a = b)
    (hc : IsClosureOp le c) (x : α) : c (c x) = c x :=
  antisymm (hc.idempotent x) (hc.inflationary (c x))

end IsClosureOp

end Freyd
