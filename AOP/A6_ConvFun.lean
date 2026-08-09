/-
  Port of AoPA `Data/List/ConvFunThm.agda`: the converse-of-a-function theorem for list folds,
  in `Rel(Set)`.

  The repo already proves B&dM's relational-fold theory via initial algebras (`relCata`, A5_5 /
  A6_*), so AoPA's powerset fold `foldR R e = ∈ ₁∘ foldr₁ (Λ(R ○ (idR ⨉ ∈))) e` and its fusion law
  are NOT reused here.  Instead the relational list fold is written directly and structurally on
  raw `List` (`foldRrel`), and the theorem is proved by list induction — the fusion detour AoPA
  takes point-free collapses to a two-case induction concretely.

  Statement (AoPA `conv-fun-thm`): if `f : β → List α` satisfies the coalgebra step
      `fun f ○ R ⊑ cons ○ (idR ⨉ fun f)`   (`R ≫ graph f ⊑ (id ⨉ graph f) ≫ cons`)
  and maps the base set `e` into `[]` (`fun f · e ⊆ nil`), then the fold refines `f°`:
      `foldR R e ⊑ (fun f)°`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A6_1_RelSet

namespace Freyd.Alg
namespace RelSet

variable {α β : Type}

/-- Object abbreviations at universe 0, where this file's concrete datatypes live. -/
abbrev dEl (τ : Type) : RelSet.{0} := ⟨τ⟩
abbrev dPair (σ τ : Type) : RelSet.{0} := ⟨σ × τ⟩
abbrev dList (τ : Type) : RelSet.{0} := ⟨List τ⟩

/-- The relational list fold (AoPA `foldR R e`), directly and structurally on raw lists:
    `foldRrel R e [] = e`, `foldRrel R e (x::xs) b = ∃ b', foldRrel R e xs b' ∧ R (x,b') b`. -/
def foldRrel (R : dPair α β ⟶ dEl β) (e : β → Prop) : List α → β → Prop
  | [],        b => e b
  | (x :: xs), b => ∃ b', foldRrel R e xs b' ∧ R (x, b') b

/-- The list constructor `cons : A × List A ⟶ List A` (AoPA `cons`), i.e. `graph (uncurry (::))`
    written out (kept as a bare relation to avoid `graph`'s universe inference here). -/
def consR : dPair α (List α) ⟶ dList α := fun p l => l = p.1 :: p.2

/-- AoPA `conv-fun-thm`: a function `f` satisfying the coalgebra step (`hstep`) and the base
    condition (`hbase`) has its fold `foldR R e` refining the converse `f°`. -/
theorem conv_fun_thm (f : β → List α) (R : dPair α β ⟶ dEl β) (e : β → Prop)
    (hstep : R ≫ (graph f : dEl β ⟶ dList α) ⊑
      rprodMap (Cat.id (dEl α)) (graph f : dEl β ⟶ dList α) ≫ consR)
    (hbase : ∀ b, e b → f b = []) :
    (foldRrel R e : dList α ⟶ dEl β) ⊑ ((graph f : dEl β ⟶ dList α)° : dList α ⟶ dEl β) := by
  -- The pointwise content: the fold sends `xs` only to `b` with `f b = xs`.
  have key : ∀ xs (b : β), foldRrel R e xs b → xs = f b := by
    intro xs
    induction xs with
    | nil =>
      intro b hfold
      exact (hbase b hfold).symm
    | cons x xs ih =>
      intro b hfold
      obtain ⟨b', hfold', hR⟩ := hfold
      have hxs : xs = f b' := ih b' hfold'
      -- Feed `R (x,b') b` through the point-free step to read off `f b = x :: f b'`.
      obtain ⟨q, ⟨hq1, hq2⟩, hcons⟩ := le_iff.mp hstep (x, b') (f b) ⟨b, hR, rfl⟩
      -- `hq1 : x = q.1`, `hq2 : q.2 = f b'`, `hcons : consR q (f b)` (`f b = q.1 :: q.2`).
      have hc : f b = q.1 :: q.2 := hcons
      rw [← hq1, hq2, ← hxs] at hc
      exact hc.symm
  rw [le_iff]
  intro xs b hfold
  -- `(graph f)° xs b` is definitionally `xs = f b`.
  show xs = f b
  exact key xs b hfold

end RelSet
end Freyd.Alg
