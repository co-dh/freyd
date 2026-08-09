/-
  **Generic membership for a polynomial functor** — a port of AoPA's `Data.Generic.Membership`.

  `epsPoly F : ⟦F⟧ A X ⟶ X` (aopa `ε`) is the membership relation: `epsPoly F t x` iff `x` occurs in
  the second-argument (`arg₂`) positions of the structure `t`.  `Path F x G y` witnesses that the
  sub-structure `y : ⟦G⟧` sits inside `x : ⟦F⟧`, and `path_to_eps` reads a membership fact off a path.
  `ε_wpre_sub`/`ε_wpre_sup` (aopa `ε-⍀-⊆`/`⊇`) relate the weakest-precondition residual of `ε F ≫ S`
  to that of `S` under the predicate lift `fmapP F`.

  This membership relation is the base of the well-foundedness hypothesis `well-found (ε F ≫ g)` that
  drives the FUNCTIONAL generic hylomorphism (`Data.Generic.Hylo`); see `A6_PolyHylo.lean`.
  Composition is diagram order (`X ○ Y ↦ Y ≫ X`).
-/
module

public import AOP.A6_Poly

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Poly

open Freyd Freyd.Alg.RelSet

/-! ## The membership relation (aopa `ε`) -/

/-- aopa `ε`: `epsPoly F t x` iff `x` occurs at an `arg₂` leaf of `t`. -/
def epsPoly : (F : PolyF) → {A X : Type} → (Fo F ⟨A⟩ ⟨X⟩ ⟶ (⟨X⟩ : RelSet.{0}))
  | .zer,        _, _ => fun e _ => e.elim
  | .one,        _, _ => fun _ _ => False
  | .arg₁,       _, _ => fun _ _ => False
  | .arg₂,       _, _ => fun t x => x = t
  | .oplus l r,  _, _ => fun u x => match u with
      | Sum.inl y => epsPoly l y x
      | Sum.inr y => epsPoly r y x
  | .otimes l r, _, _ => fun u x => epsPoly l u.1 x ∨ epsPoly r u.2 x

/-! ## Paths (aopa `Path`) -/

/-- aopa `Path`: a witness that `y : ⟦G⟧ A X` is the sub-structure of `x : ⟦F⟧ A X` reached by the
    recorded sequence of injection/projection descents. -/
inductive Path (F : PolyF) {A X : Type} (x : sem F A X) : (G : PolyF) → sem G A X → Type where
  | root : Path F x F x
  | inj₁ : {G₁ G₂ : PolyF} → {y : sem G₁ A X} →
      Path F x (.oplus G₁ G₂) (Sum.inl y) → Path F x G₁ y
  | inj₂ : {G₁ G₂ : PolyF} → {y : sem G₂ A X} →
      Path F x (.oplus G₁ G₂) (Sum.inr y) → Path F x G₂ y
  | out₁ : {G₁ G₂ : PolyF} → {y₁ : sem G₁ A X} → {y₂ : sem G₂ A X} →
      Path F x (.otimes G₁ G₂) (y₁, y₂) → Path F x G₁ y₁
  | out₂ : {G₁ G₂ : PolyF} → {y₁ : sem G₁ A X} → {y₂ : sem G₂ A X} →
      Path F x (.otimes G₁ G₂) (y₁, y₂) → Path F x G₂ y₂

/-- aopa `path-to-ε'`: a member of a sub-structure is a member of the whole. -/
def path_to_eps' {F : PolyF} {A X : Type} {x : sem F A X} :
    ∀ {G : PolyF} {y : sem G A X}, Path F x G y → ∀ {z : X}, epsPoly G y z → epsPoly F x z
  | _, _, .root,   _, hz => hz
  | _, _, .inj₁ p, _, hz => path_to_eps' p hz
  | _, _, .inj₂ p, _, hz => path_to_eps' p hz
  | _, _, .out₁ p, _, hz => path_to_eps' p (Or.inl hz)
  | _, _, .out₂ p, _, hz => path_to_eps' p (Or.inr hz)

/-- aopa `path-to-ε`: an `arg₂`-leaf reached by a path is a member of the root. -/
def path_to_eps {F : PolyF} {A X : Type} {x : sem F A X} {y : X} (p : Path F x .arg₂ y) :
    epsPoly F x y :=
  path_to_eps' p (rfl : epsPoly .arg₂ y y)

/-! ## The membership / weakest-precondition residual (aopa `ε-⍀`) -/

/-- Predicate inclusion (aopa `_⊆_` on `B → Set`). -/
def subPred {a : RelSet.{0}} (P Q : a.carrier → Prop) : Prop := ∀ x, P x → Q x

/-- The weakest-precondition residual `R ⍀ P` (aopa `_⍀_`): points whose every `R`-image lies in `P`. -/
def wpre {c b : RelSet.{0}} (R : c ⟶ b) (P : b.carrier → Prop) : c.carrier → Prop :=
  fun z => ∀ x, R z x → P x

/-- aopa `ε-⍀-⊆`: `(ε F ≫ S) ⍀ P ⊆ S ⍀ (fmapP F P)`. -/
theorem ε_wpre_sub (F : PolyF) {A B C : Type} (S : (⟨C⟩ : RelSet.{0}) ⟶ Fo F ⟨A⟩ ⟨B⟩)
    (P : B → Prop) : subPred (wpre (S ≫ epsPoly F) P) (wpre S (fmapP F P)) := by
  induction F with
  | zer => intro c hc elt _; exact (elt : Empty).elim
  | one => intro c hc _ _; trivial
  | arg₁ => intro c hc _ _; trivial
  | arg₂ => intro c hc elt hSc; exact hc elt ⟨elt, hSc, rfl⟩
  | oplus l r ihl ihr =>
      intro c hc elt hSc
      cases elt with
      | inl x =>
          refine ihl (S ≫ (graph Sum.inl)°) c ?_ x ⟨Sum.inl x, hSc, rfl⟩
          intro b hb
          obtain ⟨w, ⟨v, hSv, hveq⟩, hew⟩ := hb
          exact hc b ⟨v, hSv, hveq.symm ▸ (hew : epsPoly (.oplus l r) (Sum.inl w) b)⟩
      | inr x =>
          refine ihr (S ≫ (graph Sum.inr)°) c ?_ x ⟨Sum.inr x, hSc, rfl⟩
          intro b hb
          obtain ⟨w, ⟨v, hSv, hveq⟩, hew⟩ := hb
          exact hc b ⟨v, hSv, hveq.symm ▸ (hew : epsPoly (.oplus l r) (Sum.inr w) b)⟩
  | otimes l r ihl ihr =>
      intro c hc elt hSc
      refine ⟨ihl (S ≫ graph Prod.fst) c ?_ elt.1 ⟨elt, hSc, rfl⟩,
              ihr (S ≫ graph Prod.snd) c ?_ elt.2 ⟨elt, hSc, rfl⟩⟩
      · intro b hb
        obtain ⟨w, ⟨v, hSv, hveq⟩, hew⟩ := hb
        exact hc b ⟨v, hSv, Or.inl (hveq ▸ hew)⟩
      · intro b hb
        obtain ⟨w, ⟨v, hSv, hveq⟩, hew⟩ := hb
        exact hc b ⟨v, hSv, Or.inr (hveq ▸ hew)⟩

/-- aopa `ε-⍀-⊇`: `S ⍀ (fmapP F P) ⊆ (ε F ≫ S) ⍀ P`. -/
theorem ε_wpre_sup (F : PolyF) {A B C : Type} (S : (⟨C⟩ : RelSet.{0}) ⟶ Fo F ⟨A⟩ ⟨B⟩)
    (P : B → Prop) : subPred (wpre S (fmapP F P)) (wpre (S ≫ epsPoly F) P) := by
  induction F with
  | zer => intro c hc b hb; obtain ⟨elt, _, _⟩ := hb; exact (elt : Empty).elim
  | one => intro c hc b hb; obtain ⟨_, _, he⟩ := hb; exact he.elim
  | arg₁ => intro c hc b hb; obtain ⟨_, _, he⟩ := hb; exact he.elim
  | arg₂ => intro c hc b hb; obtain ⟨elt, hSc, he⟩ := hb; exact he.symm ▸ hc elt hSc
  | oplus l r ihl ihr =>
      intro c hc b hb; obtain ⟨elt, hSc, he⟩ := hb
      cases elt with
      | inl x =>
          refine ihl (S ≫ (graph Sum.inl)°) c (fun w hw => ?_) b ⟨x, ⟨Sum.inl x, hSc, rfl⟩, he⟩
          obtain ⟨v, hSv, hveq⟩ := hw
          exact hc (Sum.inl w) (hveq ▸ hSv)
      | inr x =>
          refine ihr (S ≫ (graph Sum.inr)°) c (fun w hw => ?_) b ⟨x, ⟨Sum.inr x, hSc, rfl⟩, he⟩
          obtain ⟨v, hSv, hveq⟩ := hw
          exact hc (Sum.inr w) (hveq ▸ hSv)
  | otimes l r ihl ihr =>
      intro c hc b hb; obtain ⟨elt, hSc, he⟩ := hb
      cases he with
      | inl he₁ =>
          refine ihl (S ≫ graph Prod.fst) c (fun w hw => ?_) b ⟨elt.1, ⟨elt, hSc, rfl⟩, he₁⟩
          obtain ⟨v, hSv, hveq⟩ := hw
          exact hveq.symm ▸ (hc v hSv).1
      | inr he₂ =>
          refine ihr (S ≫ graph Prod.snd) c (fun w hw => ?_) b ⟨elt.2, ⟨elt, hSc, rfl⟩, he₂⟩
          obtain ⟨v, hSv, hveq⟩ := hw
          exact hveq.symm ▸ (hc v hSv).2

end Freyd.Alg.RelSet.Poly
