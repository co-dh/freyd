/-
  Bird & de Moor, *Algebra of Programming* §6.6  Sorting by selection — the FULLY CONCRETE
  correctness proof (book p.153, "the proof is left as a simple exercise").

  `AOP.A6_6_Sort` proved `sort ⊆ ordered·perm` modulo three hypotheses (perm symmetric, ordered
  coreflexive, and the `select` fusion-proviso `perm·cons·ok ⊇ select°·(id×perm)`).  Here we
  DISCHARGE ALL THREE by constructing `select` concretely (B&dM p.153: `(a,y) = select x` iff `a::y`
  is a permutation of `x` with `a` below every element of `y`) and the ordered algebra `[nil,
  cons·ok]`, using the concrete `perm`/`inlist` of `AOP.A5_6_ListCombinators`.  The result
  (`selection_sort_correct_concrete`) holds for ANY relation `R : A → A → Prop` — no hypotheses.
-/
module

public import AOP.A6_6_Sort
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Sort

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type} (R : A → A → Prop)

/-- Permutation preserves membership: `Perm x x' → (a ∈ x → a ∈ x')`. -/
public theorem perm_mem : ∀ {x x' : ConsList Unit A}, Perm x x' → ∀ {b : A}, inlistP x b → inlistP x' b
  | _, _, Perm.nil, _, h => h
  | _, _, Perm.cons a hp, b, h => by
    cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (perm_mem hp h)
  | _, _, Perm.swap a b' x, b, h => by
    cases h with
    | inl h => exact Or.inr (Or.inl h)
    | inr h => cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inr h)
  | _, _, Perm.trans hp1 hp2, b, h => perm_mem hp2 (perm_mem hp1 h)

/-- `a` is `R`-below every element of `x`. -/
def lb (a : A) (x : ConsList Unit A) : Prop := ∀ b, inlistP x b → R a b

/-- **The concrete selection relation** (B&dM p.153): `select x (a, y)` iff `a::y` is a permutation
    of `x` and `a` is `R`-below every element of `y` (so `a` is an `R`-minimum of `x`, `y` the rest). -/
def selectC : dList A ⟶ (⟨A × ConsList Unit A⟩ : RelSet.{0}) :=
  fun x p => Perm (ConsList.cons p.1 p.2) x ∧ lb R p.1 p.2

/-- **The ordered algebra** `[nil, cons·ok]` (B&dM p.152): `nil ↦ []`, and `(a, y) ↦ a::y` guarded
    by `ok(a,y)` (= `a` below all of `y`).  `cataR oalgC = ordered` (sortedness). -/
def oalgC : Fobj Unit A (dList A) ⟶ dList A :=
  fun u y => match u with
    | Sum.inl _ => y = ConsList.wrap ()
    | Sum.inr p => lb R p.1 p.2 ∧ y = ConsList.cons p.1 p.2

/-- `cataR oalgC` is coreflexive (it is the sortedness relation `ordered ⊑ id`), by induction. -/
theorem oalg_coref : ∀ (x y : ConsList Unit A), cataFold (oalgC R) x y → x = y
  | ConsList.wrap u, y, h => by cases u; exact (h : y = _).symm
  | ConsList.cons a x, y, h => by
    obtain ⟨y', hy', ho⟩ := h
    have hxy' : x = y' := oalg_coref x y' hy'
    obtain ⟨_, hy⟩ := ho
    rw [hxy']; exact hy.symm

/-- The fusion condition B&dM leave "as a simple exercise": `perm·[nil,select°] ⊇ [nil,cons·ok]`,
    mirrored `F(perm) ≫ [nil, select°] ⊑ [nil, cons·ok] ≫ perm`.  Proved from the concrete `select`
    using `perm_mem` (`a` below all of a permuted list is below all of the original). -/
theorem hfus_concrete :
    (F Unit A).map perm ≫ sortAlg (selectC R) ⊑ oalgC R ≫ perm := by
  rw [le_iff]; intro u y h
  obtain ⟨v, hv, hsort⟩ := h
  cases u with
  | inl u' =>
    cases v with
    | inl v' =>
      have hy : y = ConsList.wrap () := hsort
      exact ⟨ConsList.wrap (), rfl, by rw [hy]; exact Perm.nil⟩
    | inr q => exact hv.elim
  | inr p =>
    obtain ⟨a, x⟩ := p
    cases v with
    | inl v' => exact hv.elim
    | inr q =>
      obtain ⟨a', x''⟩ := q
      have haa : a = a' := hv.1
      have hpx : Perm x x'' := hv.2
      obtain ⟨hperm', hlb'⟩ := hsort
      subst haa
      refine ⟨ConsList.cons a x, ⟨?_, rfl⟩, ?_⟩
      · intro b hb; exact hlb' b (perm_mem hpx hb)
      · exact Perm.trans (Perm.cons a hpx) hperm'

/-- **§6.6 fully concrete (B&dM pp.152-153)**: selection sort with the concrete `select`,
    `sort (selectC R) ⊆ ordered · perm` — mirrored `sort ⊑ perm ≫ cataR (oalgC R)`, where
    `cataR (oalgC R)` is sortedness and `perm` is the concrete permutation relation.  Holds for ANY
    `R : A → A → Prop`, with NO hypotheses: `perm` symmetry, `ordered` coreflexivity, and the
    `select` fusion-proviso are all discharged concretely. -/
theorem selection_sort_correct_concrete :
    sort (selectC R) ⊑ perm ≫ cataR (oalgC R) :=
  selection_sort_correct (selectC R) (oalgC R) perm
    (hom_ext fun _ _ => ⟨fun h => Perm.symm h, fun h => Perm.symm h⟩)
    (le_iff.mpr fun x y h => oalg_coref R x y h) (hfus_concrete R)

end Freyd.Alg.RelSet.Sort
