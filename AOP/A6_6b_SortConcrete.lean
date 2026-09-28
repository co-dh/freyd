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

/-! ## The book's point-free argument (B&dM pp.151-153)

Each step of the book's calculation is one declaration, stated in the relations it composes;
only the laws the book cites without proof (`perm°=perm`, the cons-branch of `perm`'s fold,
Ex 6.22) drop to points. -/

/-- B&dM p.152 `ok`: the coreflexive holding at `(a, x)` when `a` is `R`-below every element of `x`. -/
@[expose] public def ok : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ ⟨A × ConsList Unit A⟩ :=
  fun p q => p = q ∧ ∀ b, inlistP p.2 b → R p.1 b

/-- **(6.6)** `ordered = ⦇[nil, ok cons]⦈`: sortedness is the fold that checks `ok` at each `cons`. -/
public theorem ordered_cata :
    (ordered R : dList A ⟶ dList A)
      = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun D r => ?_, fun a x r => ?_⟩)
  · cases D
    exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, trivial⟩⟩
  · constructor
    · rintro ⟨rfl, hlb, hx⟩
      exact ⟨x, ⟨rfl, hx⟩, (a, x), ⟨rfl, hlb⟩, rfl⟩
    · rintro ⟨y, ⟨rfl, hx⟩, q, ⟨rfl, hlb⟩, hr⟩
      subst hr
      exact ⟨rfl, hlb, hx⟩

/-- `perm` is its own converse. -/
public theorem perm_recip : (perm : dList A ⟶ dList A)° = perm :=
  hom_ext fun _ _ => ⟨fun h => Perm.symm h, fun h => Perm.symm h⟩

/-- **p.152, step 1**: `perm ordered = (ordered perm)°`, `perm` and the coreflexive `ordered`
    being their own converses. -/
public theorem selection_step1 :
    (perm : dList A ⟶ dList A) ≫ ordered R = (ordered R ≫ perm)° := by
  rw [Allegory.recip_comp, perm_recip, coref_recip (le_iff.mpr fun _ _ h => h.1)]

/-- **p.152, step 2**: `(ordered perm)° = (⦇[nil, ok cons]⦈ perm)°` — (6.6). -/
public theorem selection_step2 :
    ((ordered R : dList A ⟶ dList A) ≫ perm)°
      = (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ perm)° := by
  rw [ordered_cata]

/-- The cons-branch of `perm = ⦇[nil, cons perm]⦈`: `cons perm = (𝟙×perm) cons perm`. -/
public theorem cons_perm :
    (consR : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A) ≫ perm
      = rprodMap (𝟙 (dE A)) perm ≫ consR ≫ perm :=
  hom_ext fun p r => ⟨fun ⟨w, hw, h⟩ => ⟨p, ⟨rfl, Perm.refl p.2⟩, w, hw, h⟩,
    fun ⟨q, ⟨h1, h2⟩, w, hw, h⟩ => by
      obtain ⟨a, x⟩ := p; obtain ⟨a', y⟩ := q
      obtain rfl : a = a' := h1
      subst hw
      exact ⟨_, rfl, Perm.trans (Perm.cons a h2) h⟩⟩

/-- **Ex 6.22**: `ok (𝟙×perm) = (𝟙×perm) ok` — permuting the tail keeps `a` below all of it. -/
public theorem ok_perm :
    ok R ≫ rprodMap (𝟙 (dE A)) perm = rprodMap (𝟙 (dE A)) perm ≫ ok R :=
  hom_ext fun p r => ⟨fun ⟨q, ⟨hq, hlb⟩, h1, h2⟩ => by
      subst hq
      exact ⟨r, ⟨h1, h2⟩, rfl, fun b hb => h1 ▸ hlb b (perm_mem (Perm.symm h2) hb)⟩,
    fun ⟨q, ⟨h1, h2⟩, hq, hlb⟩ => by
      subst hq
      exact ⟨p, ⟨rfl, fun b hb => h1 ▸ hlb b (perm_mem h2 hb)⟩, h1, h2⟩⟩

/-- **p.153, step 1**: `ok cons perm = ok (𝟙×perm) cons perm` — the cons-branch of `perm`. -/
public theorem select_step1 :
    ok R ≫ consR ≫ (perm : dList A ⟶ dList A)
      = ok R ≫ rprodMap (𝟙 (dE A)) perm ≫ consR ≫ perm :=
  congrArg (ok R ≫ ·) cons_perm

/-- **p.153, step 2**: `ok (𝟙×perm) cons perm = (𝟙×perm) ok cons perm` — Ex 6.22. -/
public theorem select_step2 :
    ok R ≫ rprodMap (𝟙 (dE A)) perm ≫ consR ≫ (perm : dList A ⟶ dList A)
      = rprodMap (𝟙 (dE A)) perm ≫ ok R ≫ consR ≫ perm := by
  rw [← Cat.assoc, ok_perm, Cat.assoc]

variable {R} {select : dList A ⟶ (⟨A × ConsList Unit A⟩ : RelSet.{0})}

/-- **p.153, step 3**: `(𝟙×perm) ok cons perm ⊒ (𝟙×perm) select°`, `select` being specified by
    `select° ⊑ ok cons perm`. -/
public theorem select_step3 (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    rprodMap (𝟙 (dE A)) perm ≫ select° ⊑ rprodMap (𝟙 (dE A)) perm ≫ ok R ≫ consR ≫ perm :=
  comp_mono_left _ hsel

/-- **p.153**: the fusion proviso `ok cons perm ⊒ (𝟙×perm) select°`. -/
public theorem select_proviso (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    rprodMap (𝟙 (dE A)) perm ≫ select° ⊑ ok R ≫ consR ≫ (perm : dList A ⟶ dList A) := by
  rw [select_step1, select_step2]; exact select_step3 hsel

/-- **p.152, step 3**: `(⦇[nil, ok cons]⦈ perm)° ⊒ ⦇[nil, select°]⦈°` — fusion (6.4) under the
    proviso. -/
public theorem selection_step3 (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
          : (F Unit A).obj (dList A) ⟶ dList A)⦈)°
      ⊑ (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ perm)° := by
  have hfus : (F Unit A).map perm ≫ junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
      ⊑ junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR) ≫ perm := by
    rw [Fmap_comp_junc, junc_comp, Cat.assoc]
    exact junc_mono _ (le_iff.mpr fun d r h => ⟨r, h, Perm.refl r⟩) (select_proviso hsel)
  exact recip_mono (relCata_le_comp _ hfus)

/-- **Selection sort (B&dM p.152)**: `perm ordered ⊒ ⦇[nil, select°]⦈°`. -/
public theorem selection_sort (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
          : (F Unit A).obj (dList A) ⟶ dList A)⦈)°
      ⊑ (perm : dList A ⟶ dList A) ≫ ordered R := by
  rw [selection_step1, selection_step2]; exact selection_step3 hsel

/-- The concrete `select` meets the specification `select° ⊑ ok cons perm` (B&dM p.153). -/
theorem selectC_spec : (selectC R)° ⊑ ok R ≫ consR ≫ (perm : dList A ⟶ dList A) :=
  le_iff.mpr fun p _ ⟨hp, hlb⟩ => ⟨p, ⟨rfl, hlb⟩, _, rfl, hp⟩

end Freyd.Alg.RelSet.Sort
