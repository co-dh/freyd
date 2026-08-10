/-
  **Sanity check: the generic polynomial layer specialized to the list functor.**

  The list bifunctor is the code `LF = one ⊕ (arg₁ ⊗ arg₂)`, so `⟦LF⟧ A X = 1 + A × X` and
  `Mu LF A` is the cons-list of `A` with `nil = In (inl ())`, `cons a xs = In (inr (a, xs))`.  This
  file instantiates the generic machinery at `LF`:

  * `fold_nil`/`fold_cons` — the generic `fold_computation` becomes the cons-list fold recurrence.
  * `list_fold_unique` — the generic universal property (`foldR_universal`, via `foldR_fun`) becomes
    exactly the shape of `A6_GenFold`'s per-datatype `CL.consFold_unique`
    (`graph h = ⦇graph alg⦈` for `h` satisfying the cons recursion), now DERIVED from the
    functor-generic law instead of a bespoke induction.
  * `#eval` cross-checks (`length`, `sumList`) confirm the generic `fold` runs.

  So the repo's existing per-datatype fold laws (`A6_SnocList`/`A6_ConsList`/`A6_TreeBin`/`A6_GenFold`)
  are the `LF`- (and, for trees, `one ⊕ (arg₂ ⊗ arg₁) ⊗ arg₂`-) instances of this generic layer; the
  carriers there are separate inductive types, so the correspondence is a definitional remark plus this
  concrete instance, not a transport of `Mu LF A ≅ ConsList Unit A` (which would need a type iso).
-/
module

public import AOP.A6_PolyFold

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Poly.ListF

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.Poly

/-- The list functor code `one ⊕ (arg₁ ⊗ arg₂)`. -/
@[expose] public def LF : PolyF := .oplus .one (.otimes .arg₁ .arg₂)

/-- `⟦LF⟧ A X = 1 + A × X`. -/
example (A X : Type) : sem LF A X = (PUnit ⊕ A × X) := rfl

/-- Empty list. -/
def nil {A : Type} : Mu LF A := In (Sum.inl PUnit.unit)
/-- Cons. -/
def cons {A : Type} (a : A) (xs : Mu LF A) : Mu LF A := In (Sum.inr (a, xs))

/-- A list algebra `1 + A×C → C`, split into base `g : C` and step `st : A → C → C`. -/
def listFun {A C : Type} (g : C) (st : A → C → C) : sem LF A C → C
  | Sum.inl _      => g
  | Sum.inr (a, c) => st a c

/-- `fold LF (listFun g st)` — the cons-list fold. -/
def foldList {A C : Type} (g : C) (st : A → C → C) : Mu LF A → C := fold LF (listFun g st)

/-- The generic `fold_computation`, specialized: `fold` of a list algebra is `g` on `nil`. -/
theorem fold_nil {A C : Type} (g : C) (st : A → C → C) : foldList g st nil = g := by
  show fold LF (listFun g st) (In (Sum.inl PUnit.unit)) = g
  rw [fold_computation]; rfl

/-- The generic `fold_computation`, specialized: the cons step. -/
theorem fold_cons {A C : Type} (g : C) (st : A → C → C) (a : A) (xs : Mu LF A) :
    foldList g st (cons a xs) = st a (foldList g st xs) := by
  show fold LF (listFun g st) (In (Sum.inr (a, xs))) = st a (fold LF (listFun g st) xs)
  rw [fold_computation]; rfl

/-- The list algebra as a `Rel(Set)` map (a graph), matching `A6_GenFold.CL.consScalarAlg`. -/
def listAlg {A C : Type} (g : C) (st : A → C → C) : Fo LF ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0}) :=
  graph (listFun g st)

/-- **The generic universal property, specialized to lists** = `A6_GenFold.CL.consFold_unique`'s
    statement, here DERIVED from `foldR_fun` + `fold_universal`.  A function `h` obeying the
    cons-list recurrence is the relational catamorphism of `listAlg`. -/
theorem list_fold_unique {A C : Type} (g : C) (st : A → C → C) (h : Mu LF A → C)
    (hnil : h nil = g) (hcons : ∀ a xs, h (cons a xs) = st a (h xs)) :
    (graph h : (⟨Mu LF A⟩ : RelSet.{0}) ⟶ ⟨C⟩) = foldRel LF (listAlg g st) := by
  have hfold : h = fold LF (listFun g st) := by
    refine fold_universal_le LF h (listFun g st) (fun s => ?_)
    cases s with
    | inl u => exact hnil
    | inr p => exact hcons p.1 p.2
  rw [hfold]
  exact foldR_fun LF (listFun g st)

/-! ### Executable cross-checks -/

/-- `List A → Mu LF A`. -/
def ofList {A : Type} : List A → Mu LF A
  | []      => nil
  | a :: as => cons a (ofList as)

def length {A : Type} : Mu LF A → Nat := foldList 0 (fun _ n => n + 1)
def sumList : Mu LF Nat → Nat := foldList 0 (fun a n => a + n)

example : length (ofList [7, 8, 9] : Mu LF Nat) = 3 := by
  show foldList 0 (fun _ n => n + 1) (cons 7 (cons 8 (cons 9 nil))) = 3
  rw [fold_cons, fold_cons, fold_cons, fold_nil]

example : sumList (ofList [1, 2, 3, 4]) = 10 := by
  show foldList 0 (fun a n => a + n) (cons 1 (cons 2 (cons 3 (cons 4 nil)))) = 10
  rw [fold_cons, fold_cons, fold_cons, fold_cons, fold_nil]

end Freyd.Alg.RelSet.Poly.ListF
