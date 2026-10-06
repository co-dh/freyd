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
import AOP.CalcSteps

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

/-! ## The book's point-free argument (B&dM pp.151-153)

Each step of the book's calculation is one declaration, stated in the relations it composes;
only the laws the book cites without proof (`perm°=perm`, the cons-branch of `perm`'s fold,
Ex 6.22) drop to points. -/

/-- B&dM p.152 `ok`: the coreflexive holding at `(a, xs)` when `a` is `R`-below every element of `xs`. -/
@[expose] public def ok : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ ⟨A × ConsList Unit A⟩ :=
  fun (a, xs) q => (a, xs) = q ∧ ∀ x, inlistP xs x → R a x

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

/-- Relating elementwise and then permuting is permuting and then relating elementwise. -/
theorem perm_listP {B : Type} (Q : dE A ⟶ dE B) : ∀ {y z : ConsList Unit B}, Perm y z →
    ∀ x : ConsList Unit A, listP Q x y → ∃ x', Perm x x' ∧ listP Q x' z
  | _, _, Perm.nil, x, h => ⟨x, Perm.refl x, h⟩
  | _, _, Perm.cons _ hp, ConsList.cons a x, h =>
      let ⟨x', p, l⟩ := perm_listP Q hp x h.2
      ⟨ConsList.cons a x', Perm.cons a p, h.1, l⟩
  | _, _, Perm.swap _ _ _, ConsList.cons a₁ (ConsList.cons a₂ x), h =>
      ⟨_, Perm.swap a₁ a₂ x, h.2.1, h.1, h.2.2⟩
  | _, _, Perm.trans h₁ h₂, x, h =>
      let ⟨x₁, p₁, l₁⟩ := perm_listP Q h₁ x h
      let ⟨x₂, p₂, l₂⟩ := perm_listP Q h₂ x₁ l₁
      ⟨x₂, Perm.trans p₁ p₂, l₂⟩

/-- `perm` is strictly natural, `list(Q) perm = perm list(Q)`: a permutation does not look at the
    elements. -/
public theorem perm_strictNatural :
    StrictNatural (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (fun a => (perm : dList a.carrier ⟶ dList a.carrier)) := by
  intro a b Q
  apply hom_ext; intro x z
  constructor
  · rintro ⟨y, hl, hp⟩
    exact perm_listP Q hp x hl
  · rintro ⟨x', hp, hl⟩
    obtain ⟨z', p, l⟩ := perm_listP Q° (Perm.symm hp) z ((listP_recip Q z x').mpr hl)
    exact ⟨z', (listP_recip Q z' x).mp l, Perm.symm p⟩

/-- `nil` is strictly natural, `nil list(Q) = nil`: the empty list has no element for `Q` to relate. -/
public theorem nil_strictNatural :
    StrictNatural (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.const (dL Unit)) (fun a => (wrapR : dL Unit ⟶ dList a.carrier)) := by
  intro a b Q
  apply hom_ext; intro d z
  cases d
  constructor
  · rintro ⟨u, hu, h⟩
    cases u; subst h
    exact ⟨ConsList.wrap (), rfl, trivial⟩
  · rintro ⟨y, hy, hl⟩
    subst hy
    cases z with
    | wrap u => exact ⟨(), rfl, by cases u; rfl⟩
    | cons b w => exact hl.elim

/-- `ordered` is a coreflexive, so its own converse. -/
public theorem ordered_recip : (ordered R : dList A ⟶ dList A)° = ordered R :=
  coref_recip (le_iff.mpr fun _ _ h => h.1)

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

variable {R} {select : dList A ⟶ (⟨A × ConsList Unit A⟩ : RelSet.{0})}

/-- **p.153**: the fusion proviso `ok cons perm ⊒ (𝟙×perm) select°`: `select° ⊑ ok cons perm`,
    Ex 6.22, then the cons-branch of `perm`. -/
public theorem select_proviso (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    rprodMap (𝟙 (dE A)) perm ≫ select° ⊑ ok R ≫ consR ≫ (perm : dList A ⟶ dList A) :=
  calc rprodMap (𝟙 (dE A)) perm ≫ select° ⊑ rprodMap (𝟙 (dE A)) perm ≫ ok R ≫ consR ≫ perm :=
        comp_mono_left _ hsel
    _ = ok R ≫ rprodMap (𝟙 (dE A)) perm ≫ consR ≫ perm := by rw [← Cat.assoc, ← ok_perm, Cat.assoc]
    _ = ok R ≫ consR ≫ perm := congrArg (ok R ≫ ·) cons_perm.symm

calc_steps select_proviso

/-- **p.152**: `(⦇[nil, ok cons]⦈ perm)° ⊒ ⦇[nil, select°]⦈°` — fusion (6.4) under the
    proviso. -/
public theorem selection_fusion (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
          : (F Unit A).obj (dList A) ⟶ dList A)⦈)°
      ⊑ (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ perm)° := by
  have hfus : (F Unit A).map perm ≫ junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
      ⊑ junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR) ≫ perm := by
    rw [Fmap_comp_junc, junc_comp, Cat.assoc]
    exact junc_mono _ (le_iff.mpr fun d r h => ⟨r, h, Perm.refl r⟩) (select_proviso hsel)
  exact recip_mono (relCata_le_comp _ hfus)

/-- **Selection sort (B&dM p.152)**: `perm ordered ⊒ ⦇[nil, select°]⦈°`, the book's chain from
    the bottom line up. -/
public theorem selection_sort (hsel : select° ⊑ ok R ≫ consR ≫ perm) :
    (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
          : (F Unit A).obj (dList A) ⟶ dList A)⦈)°
      ⊑ (perm : dList A ⟶ dList A) ≫ ordered R :=
  calc (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
          : (F Unit A).obj (dList A) ⟶ dList A)⦈)°
        ⊑ (⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (ok R ≫ consR)
          : (F Unit A).obj (dList A) ⟶ dList A)⦈ ≫ perm)° := selection_fusion hsel
    _ = ((ordered R : dList A ⟶ dList A) ≫ perm)° := by rw [ordered_cata]
    _ = perm° ≫ (ordered R)° := Allegory.recip_comp _ _
    _ = perm ≫ (ordered R)° := by rw [perm_recip]
    _ = perm ≫ ordered R := by rw [ordered_recip]

calc_steps selection_sort

/-- The concrete `select` meets the specification `select° ⊑ ok cons perm` (B&dM p.153). -/
theorem selectC_spec : (selectC R)° ⊑ ok R ≫ consR ≫ (perm : dList A ⟶ dList A) :=
  le_iff.mpr fun p _ ⟨hp, hlb⟩ => ⟨p, ⟨rfl, hlb⟩, _, rfl, hp⟩

variable (select) in
/-- **p.153, the program**: `X = ⦇[nil, select°]⦈°` satisfies `X = nil°nil ∪ select(𝟙×X)cons` —
    the converse of the fold unfolds one `select` at a time. -/
public theorem sort_rec :
    (cataR (junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
        : (F Unit A).obj (dList A) ⟶ dList A))°
      = wrapR° ≫ wrapR
        ∪ select ≫ rprodMap (𝟙 (dE A))
            (cataR (junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
              : (F Unit A).obj (dList A) ⟶ dList A))° ≫ consR := by
  have hw : algWrap (junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
      : (F Unit A).obj (dList A) ⟶ dList A) = wrapR :=
    hom_ext fun d r => junc_sum_inl _ _ d r
  have hc : algCons (junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR select°
      : (F Unit A).obj (dList A) ⟶ dList A) = select° :=
    hom_ext fun p r => junc_sum_inr _ _ p r
  refine (cata_converse_eq _).trans ?_
  rw [hw, hc, Allegory.recip_recip]

end Freyd.Alg.RelSet.Sort

-- printing-only: the preorder is fixed for the whole of §6.6, so `ok` is written without it (p.151).
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Sort.ok] public meta def Freyd.Alg.RelSet.Sort.unexpandOk : Unexpander
  | `($_ $_) => `($(mkIdent `ok))
  | _ => throw ()
