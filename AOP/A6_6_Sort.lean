/-
  Bird & de Moor, *Algebra of Programming* §6.6  Sorting by selection (book pp. 151-153) — a
  worked program in the Set model `Rel(Set)`, over cons-lists `list A = ConsList Unit A`.

  `sort` is specified by `sort ⊆ ordered · perm` (6.6): a sorted permutation of the input, where
  `perm` is the permutation relation and `ordered = ⦇[nil, cons·ok]⦈` the coreflexive testing
  sortedness under a connected preorder.  Selection sort HEADS FOR AN ALGORITHM EXPRESSED AS THE
  CONVERSE OF A CATAMORPHISM: `sort = ⦇[nil, select°]⦈°`, whose recursion is
  `sort x = [] if x=[], [a] ++ sort y where (a,y) = select x` — precisely our `cata_converse_eq`
  at `φ = [nil, select°]`.  Correctness (`sort ⊆ ordered·perm`) is the fusion step: B&dM construct
  `select` (via `base`/`step`, p.153) to satisfy `perm·cons·ok ⊇ select°·(id×perm)`; given that
  fusion condition, sortedness and permutation-symmetry, selection sort refines the spec.
-/
module

public import AOP.A6_ConsList

namespace Freyd.Alg.RelSet.Sort

open Freyd Freyd.Alg.RelSet.CL

variable {A : Type}

/-- `list A = ConsList Unit A` (`nil = wrap ()`). -/
@[expose] public abbrev dList (A : Type) : RelSet.{0} := dCL Unit A

/-- Coreflexives in `Rel(Set)` are symmetric: `R ⊑ id ⟹ R° = R`. -/
public theorem coref_recip {a : RelSet.{0}} {R : a ⟶ a} (h : R ⊑ Cat.id a) : R° = R :=
  symmetric_eq (coreflexive_symmetric_idempotent h).1

variable (select : dList A ⟶ (⟨A × ConsList Unit A⟩ : RelSet.{0}))

/-- The selection-sort algebra `[nil, select°]`: `nil ↦ []`, and `select°` on the cons-summand. -/
@[expose] public def sortAlg : Fobj Unit A (dList A) ⟶ dList A :=
  fun u y => match u with
    | Sum.inl _ => y = ConsList.wrap ()
    | Sum.inr p => select y p

/-- **Selection sort (B&dM p.153)**: `sort = ⦇[nil, select°]⦈°`, the algorithm expressed as the
    CONVERSE OF A CATAMORPHISM. -/
@[expose] public def sort : dList A ⟶ dList A := (cataR (sortAlg select))°

/-- **§6.6 (B&dM p.153)**: the selection-sort recursion — `sort x = [] if x=[]`, else
    `[a] ++ sort y where (a, y) = select x`.  A direct instance of `cata_converse_eq`:
    `sort = (nil° ≫ nil) ∪ (select ≫ (id × sort) ≫ cons)` (mirrored). -/
theorem sort_recursion :
    sort select = (algWrap (sortAlg select))° ≫ wrapR
      ∪ (algCons (sortAlg select))° ≫ rprodMap (Cat.id (dE A)) (sort select) ≫ consR :=
  cata_converse_eq (sortAlg select)

/-- **§6.6 correctness (B&dM p.152-153)**: selection sort refines its specification,
    `sort ⊆ ordered · perm` (mirrored `sort ⊑ perm ≫ ordered`), PROVIDED `select` satisfies the
    fusion condition B&dM construct it for (`hfus`, packaging `perm·cons·ok ⊇ select°·(id×perm)`),
    `perm` is symmetric (`hperm`), and `ordered = ⦇[nil, cons·ok]⦈` is coreflexive (`hord`).  By
    the fusion law (6.4) `relCata_le_comp` and reciprocation. -/
public theorem selection_sort_correct (oalg : Fobj Unit A (dList A) ⟶ dList A)
    (perm : dList A ⟶ dList A) (hperm : perm° = perm) (hord : cataR oalg ⊑ Cat.id (dList A))
    (hfus : (F Unit A).map perm ≫ sortAlg select ⊑ oalg ≫ perm) :
    sort select ⊑ perm ≫ cataR oalg := by
  have hf : relCata (initial Unit A) (sortAlg select) ⊑ relCata (initial Unit A) oalg ≫ perm :=
    relCata_le_comp (initial Unit A) hfus
  rw [← cataR_eq_relCata (sortAlg select), ← cataR_eq_relCata oalg] at hf
  have hrec := recip_mono hf
  rw [Allegory.recip_comp, hperm, coref_recip hord] at hrec
  exact hrec

end Freyd.Alg.RelSet.Sort
