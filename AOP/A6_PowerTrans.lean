/-
  Port of AoPA `Relations/PowerTrans.agda` into `Rel(Set)`.

  Two layers:

  * The existential image on SETS, AoPA `ℰ R : ℙ A → ℙ B`, here `image R s = {y | ∃ x ∈ s, R x y}`
    — with its monotonicity in the set and in the relation, and functoriality.  These carry the
    real computational content of the file.

  * The power transpose `Λ` and its interaction with membership `∈`.  In `Rel(Set)` a set-valued
    function `A → ℙ B` is literally `a.carrier → b.carrier → Prop`, the SAME type as a relation
    `a ⟶ b`, and the transpose `Λ` / membership-composition `∈ ₁∘ _` are the currying iso, hence
    the identity view.  Ordered by pointwise `⊆`, AoPA's `Λ∈-galois-1/2`, `Λ∈/∈Λ-cancelation` and
    `Λ-monotonic` therefore become the (trivial, but faithful) statements that this iso preserves
    the order — matching AoPA's proofs, which are all argument swaps `R⊑S a b h = R⊑S b a h`.

  The genuinely non-trivial power-object facts AoPA proves alongside these already live in the
  repo abstractly (for any `UnguardedPowerAllegory`, hence for `Rel(Set)`):
    * `∈Λ-cancelation`  `Λ R ≫ ∋ = R`      →  `Λ_eps_eq'` (a.k.a. `RelSet.classifier_comp_eps`);
    * `ℰΛ-absorption`   `Λ S ≫ ℰ R = Λ(S≫R)` →  `Λ_absorption`;
    * `ℰ-functor`       `ℰ(S≫R) = ℰ S ≫ ℰ R` →  `existsImage_comp`.

  Mathlib-free; axioms ⊆ {propext} (via `funext`/`propext`/`le_iff`).
-/
module

public import AOP.A6_1_RelSet

universe u

namespace Freyd.Alg
namespace RelSet

variable {A B C : RelSet.{u}}

/-! ### The existential image on sets (AoPA `ℰ` acting on `ℙ`) -/

/-- AoPA `ℰ R` on a subset: `image R s = {y | ∃ x, s x ∧ R x y}`. -/
def image (R : A ⟶ B) (s : A.carrier → Prop) : B.carrier → Prop :=
  fun y => ∃ x, s x ∧ R x y

/-- AoPA `ℰ-monotonic'`: `image` is monotone in the set argument. -/
theorem image_mono_set (R : A ⟶ B) {s t : A.carrier → Prop} (h : ∀ x, s x → t x) :
    ∀ y, image R s y → image R t y :=
  fun _ ⟨x, hs, hR⟩ => ⟨x, h x hs, hR⟩

/-- AoPA `ℰ-monotonic`: `image` is monotone in the relation argument. -/
theorem image_mono_rel {R S : A ⟶ B} (h : R ⊑ S) (s : A.carrier → Prop) :
    ∀ y, image R s y → image S s y :=
  fun y ⟨x, hs, hR⟩ => ⟨x, hs, le_iff.mp h x y hR⟩

/-- AoPA `ℰ-functor`: `image (R ≫ S) s = image S (image R s)` (functoriality on sets). -/
theorem image_comp (R : A ⟶ B) (S : B ⟶ C) (s : A.carrier → Prop) :
    image (R ≫ S) s = image S (image R s) := by
  funext z
  exact propext
    ⟨fun ⟨x, hs, y, hR, hS⟩ => ⟨y, ⟨x, hs, hR⟩, hS⟩,
     fun ⟨y, ⟨x, hs, hR⟩, hS⟩ => ⟨x, hs, y, hR, hS⟩⟩

/-! ### The power transpose `Λ` vs. membership `∈` (the currying iso)

  A set-valued function `A → ℙ B` is `SVF a b`; `Lam` is `Λ`, `memAfter` is `∈ ₁∘ _`.  In
  `Rel(Set)` both are the identity view of `a ⟶ b`; the lemmas record that this iso preserves the
  pointwise-`⊆` order.  (`Lam`, `memAfter` are kept as names so the statements read like AoPA.) -/

/-- A set-valued function `A → ℙ B`; the same underlying type as a relation `a ⟶ b`. -/
abbrev SVF (A B : RelSet.{u}) := A.carrier → B.carrier → Prop

/-- Pointwise `⊆` order on set-valued functions. -/
def SVFLe (r s : SVF A B) : Prop := ∀ x y, r x y → s x y

/-- The power transpose `Λ` of a relation, as a set-valued function (curry). -/
def Lam (S : A ⟶ B) : SVF A B := fun x y => S x y

/-- Membership after a set-valued function, `∈ ₁∘ r`, back as a relation. -/
def memAfter (r : SVF A B) : A ⟶ B := fun x y => r x y

/-- AoPA `Λ∈-galois-1`: `(∈ ₁∘ r) ⊑ S → r ⊑ Λ S`. -/
theorem Lam_mem_galois_1 {r : SVF A B} {S : A ⟶ B} (h : memAfter r ⊑ S) : SVFLe r (Lam S) :=
  fun x y hr => le_iff.mp h x y hr

/-- AoPA `Λ∈-galois-2`: `r ⊑ Λ S → (∈ ₁∘ r) ⊑ S`. -/
theorem Lam_mem_galois_2 {r : SVF A B} {S : A ⟶ B} (h : SVFLe r (Lam S)) : memAfter r ⊑ S :=
  le_iff.mpr h

/-- AoPA `Λ∈-cancelation`: `Λ(∈ ₁∘ r) ⊑ r`. -/
theorem Lam_mem_cancel (r : SVF A B) : SVFLe (Lam (memAfter r)) r :=
  fun _ _ hr => hr

/-- AoPA `∈Λ-cancelation` (set-valued-function form): `(∈ ₁∘ (Λ R)) ⊑ R`.
    (As a morphism equation this is the repo's `classifier_comp_eps`/`Λ_eps_eq'`.) -/
theorem mem_Lam_cancel (R : A ⟶ B) : memAfter (Lam R) ⊑ R :=
  le_iff.mpr fun _ _ hr => hr

/-- AoPA `Λ-monotonic`: `R ⊑ S → Λ R ⊑ Λ S`. -/
theorem Lam_mono {R S : A ⟶ B} (h : R ⊑ S) : SVFLe (Lam R) (Lam S) :=
  fun x y hr => le_iff.mp h x y hr

end RelSet
end Freyd.Alg
