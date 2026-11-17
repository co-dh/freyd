/-
  `(μX : φX)` and `(νX : φX)` on a hom-set of relations (B&dM Theorem 6.1), defined for every `φ`: a fixed point
  when `φ` is monotonic. The one copy of the fixed points Rel proper uses; `Gen.mu`, `Gen.nu` compute them.
-/
import LeetQ.Core.Rel

namespace LeetQ.Core.Rel

open LeetQ.Core

variable {α β : Type} {φ ψ : Rel α β → Rel α β} {Y : Rel α β}

/-- A monotonic map on a hom-set ("not necessarily a functor", Theorem 6.1). -/
def Monotonic (φ : Rel α β → Rel α β) : Prop := ∀ X Y : Rel α β, X ⊑ Y → φ X ⊑ φ Y

/-- `(μX : φX)`: the pairs in every prefixed point. -/
def mu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∀ Y : Rel α β, φ Y ⊑ Y → Y a b

/-- `(νX : φX)`: the pairs in some postfixed point. -/
def nu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∃ Y : Rel α β, Y ⊑ φ Y ∧ Y a b

theorem mu_le (h : φ Y ⊑ Y) : mu φ ⊑ Y := le_iff.2 fun _ _ hx => hx Y h

theorem le_nu (h : Y ⊑ φ Y) : Y ⊑ nu φ := le_iff.2 fun _ _ hy => ⟨Y, h, hy⟩

theorem mu_prefixed (hφ : Monotonic φ) : φ (mu φ) ⊑ mu φ :=
  le_iff.2 fun a b hx _ hY => le_iff.1 hY a b (le_iff.1 (hφ _ _ (mu_le hY)) a b hx)

theorem mu_fix (hφ : Monotonic φ) : φ (mu φ) = mu φ :=
  le_antisymm (mu_prefixed hφ) (mu_le (hφ _ _ (mu_prefixed hφ)))

theorem nu_fix (hφ : Monotonic φ) : φ (nu φ) = nu φ := by
  have h1 : nu φ ⊑ φ (nu φ) :=
    le_iff.2 fun a b ⟨Y, hY, hy⟩ => le_iff.1 (hφ _ _ (le_nu hY)) a b (le_iff.1 hY a b hy)
  exact le_antisymm (le_nu (hφ _ _ h1)) h1

/-- `mu` is monotone in its body, pointwise: no monotonicity of either body is needed. -/
theorem mu_mono (h : ∀ X, φ X ⊑ ψ X) : mu φ ⊑ mu ψ :=
  le_iff.2 fun _ _ hx Y hY => hx Y (le_trans (h Y) hY)

theorem nu_mono (h : ∀ X, φ X ⊑ ψ X) : nu φ ⊑ nu ψ :=
  le_iff.2 fun _ _ ⟨Y, hY, hy⟩ => ⟨Y, le_trans hY (h Y), hy⟩

end LeetQ.Core.Rel
