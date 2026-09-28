/-
  Bird & de Moor, *Algebra of Programming* §3.5  Concatenation and currying.

  Theorem 3.1 (p.73), the structural recursion theorem: a recursion `f` with an
  extra parameter is solved by currying `f` and folding over the initial algebra.
  The setting is a cartesian closed category (Freyd §1.85, `HasExponentials`).

  Freyd's product functor puts the parameter on the LEFT (`prodMap B X Y u = 1×u`,
  `eval_exp B A : B × A^B → A`), where B&dM write `f : A ← T×B`, `f·(α×id)`;
  so B&dM's `α × id` is `prodMap B _ _ α`, `apply` is `eval_exp`, `curry` is `curry`.
-/

module

public import Freyd.S1_85

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- An initial `F`-algebra `α : F T → T` of an endofunctor `F`, given by its universal
    property (B&dM §2.6): `x = ⦇k⦈ ≡ α x = F(x) k` (diagram order). -/
public structure InitialAlg (F : Functor 𝒞 𝒞) where
  t : 𝒞
  α : F.obj t ⟶ t
  cata : {A : 𝒞} → (F.obj A ⟶ A) → (t ⟶ A)
  cata_univ : ∀ {A : 𝒞} (k : F.obj A ⟶ A) (x : t ⟶ A), x = cata k ↔ α ≫ x = F.map x ≫ k

variable [HasExponentials 𝒞]

/-- **B&dM Theorem 3.1** (p.73), structural recursion: if `φ` is natural in the sense
    `G(h×id)·φ = φ·(Fh×id)`, then
    `f·(α×id) = h·Gf·φ` iff `f = apply·(⦇curry(h·G apply·φ)⦈ × id)`.
    Diagram order, parameter `B` on the left: `φ X : B×FX → G(B×X)`, and the fold's
    algebra is `curry(φ(A^B) ≫ G(eval) ≫ h) : F(A^B) → A^B`. -/
public theorem structural_recursion {F G : Functor 𝒞 𝒞} (I : InitialAlg F) {A B : 𝒞}
    (φ : ∀ X : 𝒞, prod B (F.obj X) ⟶ G.obj (prod B X))
    (hφ : ∀ {X Y : 𝒞} (u : X ⟶ Y),
      prodMap B _ _ (F.map u) ≫ φ Y = φ X ≫ G.map (prodMap B X Y u))
    (h : G.obj A ⟶ A) (f : prod B I.t ⟶ A) :
    prodMap B _ _ I.α ≫ f = φ I.t ≫ G.map f ≫ h ↔
      f = prodMap B _ _ (I.cata (curry (φ (A ^^ B) ≫ G.map (eval_exp B A) ≫ h))) ≫
        eval_exp B A := by
  -- curry f is the fold iff f satisfies the recursion; B&dM's calculation on p.73.
  have hk : F.map (curry f) ≫ curry (φ (A ^^ B) ≫ G.map (eval_exp B A) ≫ h) =
      curry (φ I.t ≫ G.map f ≫ h) := by
    rw [curry_precomp, ← Cat.assoc, hφ, Cat.assoc, ← Cat.assoc (G.map _), ← G.map_comp,
      curry_eval_eq]
  rw [show _ ↔ _ from ⟨congrArg curry, curry_inj⟩, ← curry_precomp, ← hk, ← I.cata_univ]
  exact ⟨fun hc => by rw [← hc, curry_eval_eq],
    fun hf => (curry_unique_eq hf.symm).symm⟩

end Freyd
