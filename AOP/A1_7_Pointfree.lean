/-
  Bird & de Moor, *Algebra of Programming* §1.7 "Pointwise and point-free" (book pp. 20–22) — the
  calculation `listr outl · filter outr · zip · pair (id, listr p) = filter p`, one theorem per step
  of the book's calculation (`filter_pointfree_step1` … `_step10`), composed into
  `filter_pointfree`.

  Every composite is mirrored to diagram order (`xy` = first `x` then `y`), in the Set model of
  relations on cons-lists (`dList A = ConsList Unit A`, `AOP.A5_6_ListCombinators`), where
  `listr` is the list relator `list`, `pair` is `rpair` and `outl`/`outr` are the projections of
  `relProd`.  The rules (1.5), (1.6), (1.8), (1.9) are the existing `wrap_natural`,
  `concat_natural`, `list_comp`, `list_id`; (1.4), (1.7) and (1.11) are proved here.  Nothing in
  the calculation needs `p` to be a map: every step holds for a relation `p : A ⟶ Bool`.

  Mathlib-free; constructive.
-/
module

public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Pointfree

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A B C : Type}

/-- `zip` on cons-lists: pair two lists position by position, stopping at the shorter. -/
@[expose] public def czip : ConsList Unit A → ConsList Unit B → ConsList Unit (A × B)
  | ConsList.cons a x, ConsList.cons b y => ConsList.cons (a, b) (czip x y)
  | _, _ => ConsList.wrap ()

/-- B&dM's `zip : list A × list B → list (A × B)` (p.20) as a relation. -/
@[expose] public def zip : (⟨ConsList Unit A × ConsList Unit B⟩ : RelSet.{0}) ⟶ dList (A × B) :=
  graph fun q => czip q.1 q.2

/-- B&dM's `nil` as a constant function (p.20, `nil a = []`): whatever comes in, the empty list. -/
@[expose] public def nil {X : RelSet.{0}} : X ⟶ dList A := graph fun _ => ConsList.wrap ()

/-- B&dM's conditional `(q → R, S)` (p.21): `R` where `q` answers `true`, `S` where it answers
    `false`. -/
@[expose] public def conditional {X : Type} {Y : RelSet.{0}} (q : dE X ⟶ dE Bool) (R S : dE X ⟶ Y) :
    dE X ⟶ Y :=
  fun x y => (q x true ∧ R x y) ∨ (q x false ∧ S x y)

/-- B&dM's `filter p = concat · listr (p → wrap, nil)` (§1.7, p.20), in diagram order. -/
@[expose] public def filter (p : dE A ⟶ dE Bool) : dList A ⟶ dList A :=
  list (conditional p (singleR ()) nil : dE A ⟶ dE (ConsList Unit A)) ≫ concatR

/-! ## The rules the calculation uses that `AOP.A5_6_ListCombinators` does not already state -/

/-- **(1.4)** `listr f · nil = nil`, mirrored: `nil list(R) = nil`. -/
public theorem nil_list {X : RelSet.{0}} (R : dE A ⟶ dE B) :
    (nil : X ⟶ dList A) ≫ list R = nil := by
  apply hom_ext; intro x z; rw [comp_apply]
  constructor
  · rintro ⟨_, rfl, hz⟩
    cases z with
    | wrap _ => rfl
    | cons _ _ => exact hz.elim
  · rintro rfl; exact ⟨ConsList.wrap (), rfl, trivial⟩

theorem listP_rpair (R : dE A ⟶ dE B) (S : dE A ⟶ dE C) :
    ∀ (x : ConsList Unit A) (z : ConsList Unit (B × C)),
      listP (rpair R S) x z ↔ ∃ y w, listP R x y ∧ listP S x w ∧ z = czip y w
  | ConsList.wrap _, ConsList.wrap _ =>
      ⟨fun _ => ⟨ConsList.wrap (), ConsList.wrap (), trivial, trivial, rfl⟩, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ =>
      ⟨False.elim, fun ⟨y, w, hy, hw, hz⟩ => by
        cases y with
        | cons _ _ => exact hy.elim
        | wrap _ => cases w with
          | cons _ _ => exact hw.elim
          | wrap _ => exact nomatch hz⟩
  | ConsList.cons _ _, ConsList.wrap _ =>
      ⟨False.elim, fun ⟨y, w, hy, hw, hz⟩ => by
        cases y with
        | wrap _ => exact hy.elim
        | cons _ _ => cases w with
          | wrap _ => exact hw.elim
          | cons _ _ => exact nomatch hz⟩
  | ConsList.cons a x, ConsList.cons q z => by
      constructor
      · rintro ⟨⟨h1, h2⟩, hxz⟩
        obtain ⟨y, w, hy, hw, rfl⟩ := (listP_rpair R S x z).mp hxz
        exact ⟨ConsList.cons q.1 y, ConsList.cons q.2 w, ⟨h1, hy⟩, ⟨h2, hw⟩, rfl⟩
      · rintro ⟨y, w, hy, hw, hz⟩
        cases y with
        | wrap _ => exact hy.elim
        | cons b y => cases w with
          | wrap _ => exact hw.elim
          | cons c w =>
            cases hz
            exact ⟨⟨hy.1, hw.1⟩, (listP_rpair R S x _).mpr ⟨y, w, hy.2, hw.2, rfl⟩⟩

/-- **(1.7)** `zip · pair (listr f, listr g) = listr (pair (f, g))`, mirrored:
    `⟨list(R), list(S)⟩ zip = list(⟨R, S⟩)` — `zip` is natural. -/
public theorem zip_natural (R : dE A ⟶ dE B) (S : dE A ⟶ dE C) :
    rpair (list R) (list S) ≫ zip = list (rpair R S) := by
  apply hom_ext; intro x z; rw [comp_apply]
  constructor
  · rintro ⟨q, ⟨hy, hw⟩, hz⟩
    exact (listP_rpair R S x z).mpr ⟨q.1, q.2, hy, hw, hz⟩
  · intro h
    obtain ⟨y, w, hy, hw, hz⟩ := (listP_rpair R S x z).mp h
    exact ⟨(y, w), ⟨hy, hw⟩, hz⟩

/-- **(1.11)** `h · (p → f, g) = (p → h · f, h · g)`, mirrored: `(q → R, S) H = (q → RH, SH)`. -/
public theorem conditional_comp {X : Type} {Y Z : RelSet.{0}} (q : dE X ⟶ dE Bool)
    (R S : dE X ⟶ Y) (H : Y ⟶ Z) :
    conditional q R S ≫ H = conditional q (R ≫ H) (S ≫ H) := by
  apply hom_ext; intro x z; rw [comp_apply]
  constructor
  · rintro ⟨y, ⟨hq, hR⟩ | ⟨hq, hS⟩, hH⟩
    · exact Or.inl ⟨hq, y, hR, hH⟩
    · exact Or.inr ⟨hq, y, hS, hH⟩
  · rintro (⟨hq, y, hR, hH⟩ | ⟨hq, y, hS, hH⟩)
    · exact ⟨y, Or.inl ⟨hq, hR⟩, hH⟩
    · exact ⟨y, Or.inr ⟨hq, hS⟩, hH⟩

/-- **(1.10) with (1.1) and (1.3)** at `h = pair (id, p)`, mirrored: `⟨𝟙, p⟩ (π₂ → π₁ wrap, nil) =
    (p → 𝟙 wrap, nil)` — the test reads `p`, the kept branch reads the element. -/
public theorem pair_conditional (p : dE A ⟶ dE Bool) :
    rpair (𝟙 (dE A)) p
        ≫ conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil
      = conditional p (𝟙 (dE A) ≫ singleR ()) (nil : dE A ⟶ dList A) := by
  have e1 : (relProd (dE A) (dE Bool)).outl = graph (fun q : A × Bool => q.1) := rfl
  have e2 : (relProd (dE A) (dE Bool)).outr = graph (fun q : A × Bool => q.2) := rfl
  rw [e1, e2]
  apply hom_ext; intro a y; rw [comp_apply]
  constructor
  · rintro ⟨⟨a', b⟩, ⟨ha, hp⟩, ⟨hb, a'', ha'', hy⟩ | ⟨hb, hy⟩⟩
    · have ha : a = a' := (id_apply a a').mp ha
      have hb : true = b := hb
      have ha'' : a'' = a' := ha''
      subst ha hb ha''
      exact Or.inl ⟨hp, _, (id_apply _ _).mpr rfl, hy⟩
    · have ha : a = a' := (id_apply a a').mp ha
      have hb : false = b := hb
      subst ha hb
      exact Or.inr ⟨hp, hy⟩
  · rintro (⟨hp, a', ha', hy⟩ | ⟨hp, hy⟩)
    · have ha' : a = a' := (id_apply a a').mp ha'
      subst ha'
      exact ⟨(a, true), ⟨(id_apply a a).mpr rfl, hp⟩, Or.inl ⟨rfl, a, rfl, hy⟩⟩
    · exact ⟨(a, false), ⟨(id_apply a a).mpr rfl, hp⟩, Or.inr ⟨rfl, hy⟩⟩

/-! ## The beads' naturality: `zip` and the two conditionals are LAX natural (Theorem 5.2's
  `⊑`, not `=`: at an element with no `R`-image the left side is empty and the right side is not) -/

theorem listP_rprodMap_czip {D : Type} (R : dE A ⟶ dE C) (S : dE B ⟶ dE D) :
    ∀ (x : ConsList Unit A) (y : ConsList Unit B) (q : ConsList Unit C × ConsList Unit D),
      listP R x q.1 → listP S y q.2 → listP (rprodMap R S) (czip x y) (czip q.1 q.2)
  | ConsList.cons _ x, ConsList.cons _ y, (ConsList.cons _ u, ConsList.cons _ v), h1, h2 =>
      ⟨⟨h1.1, h2.1⟩, listP_rprodMap_czip R S x y (u, v) h1.2 h2.2⟩
  | ConsList.cons _ _, ConsList.cons _ _, (ConsList.wrap _, _), h1, _ => h1.elim
  | ConsList.cons _ _, ConsList.cons _ _, (ConsList.cons _ _, ConsList.wrap _), _, h2 => h2.elim
  | ConsList.wrap _, _, (ConsList.wrap _, _), _, _ => trivial
  | ConsList.wrap _, _, (ConsList.cons _ _, _), h1, _ => h1.elim
  | ConsList.cons _ _, ConsList.wrap _, (ConsList.wrap _, _), _, _ => trivial
  | ConsList.cons _ _, ConsList.wrap _, (ConsList.cons _ _, ConsList.wrap _), _, _ => trivial
  | ConsList.cons _ _, ConsList.wrap _, (ConsList.cons _ _, ConsList.cons _ _), _, h2 => h2.elim

/-- `zip` is lax natural in its left element type: `(list(R)×𝟙) zip ⊑ zip list(R×𝟙)`. -/
public theorem zip_laxNatural_left :
    LaxNatural
      (Relator.comp (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE B))) listRelator)
      (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
        (Relator.const (dList B)))
      (fun a => (zip : (⟨ConsList Unit a.carrier × ConsList Unit B⟩ : RelSet.{0})
        ⟶ dList (a.carrier × B))) := by
  intro a b R
  show prodMap (relProd _ _) (relProd _ _) (list R) (𝟙 (dList B)) ≫ zip
    ⊑ zip ≫ list (prodMap (relProd _ _) (relProd _ _) R (𝟙 (dE B)))
  rw [prodMap_eq_rprodMap, prodMap_eq_rprodMap, ← list_id]
  exact le_iff.mpr fun p z ⟨q, ⟨h1, h2⟩, hz⟩ =>
    ⟨czip p.1 p.2, rfl, (show z = czip q.1 q.2 from hz) ▸ listP_rprodMap_czip R _ p.1 p.2 q h1 h2⟩

/-- `zip` is lax natural in its right element type: `(𝟙×list(R)) zip ⊑ zip list(𝟙×R)`. -/
public theorem zip_laxNatural_right :
    LaxNatural
      (Relator.comp (Relator.prod (Relator.const (dE A)) (Relator.idRelator RelSet.{0})) listRelator)
      (Relator.prod (Relator.const (dList A))
        (Relator.comp (Relator.idRelator RelSet.{0}) listRelator))
      (fun b => (zip : (⟨ConsList Unit A × ConsList Unit b.carrier⟩ : RelSet.{0})
        ⟶ dList (A × b.carrier))) := by
  intro a b R
  show prodMap (relProd _ _) (relProd _ _) (𝟙 (dList A)) (list R) ≫ zip
    ⊑ zip ≫ list (prodMap (relProd _ _) (relProd _ _) (𝟙 (dE A)) R)
  rw [prodMap_eq_rprodMap, prodMap_eq_rprodMap, ← list_id]
  exact le_iff.mpr fun p z ⟨q, ⟨h1, h2⟩, hz⟩ =>
    ⟨czip p.1 p.2, rfl, (show z = czip q.1 q.2 from hz) ▸ listP_rprodMap_czip _ R p.1 p.2 q h1 h2⟩

/-- `(π₂ → wrap, nil)` is lax natural: `(R×𝟙)(π₂ → wrap, nil) ⊑ (π₂ → wrap, nil) list(R×𝟙)`. -/
public theorem conditional_wrap_laxNatural :
    LaxNatural
      (Relator.comp (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool)))
        listRelator)
      (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool)))
      (fun a => conditional (relProd a (dE Bool)).outr (singleR ()) nil) := by
  intro a b R
  show prodMap (relProd _ _) (relProd _ _) R (𝟙 (dE Bool)) ≫ _
    ⊑ _ ≫ list (prodMap (relProd _ _) (relProd _ _) R (𝟙 (dE Bool)))
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun ⟨x, t⟩ y ⟨⟨x', t'⟩, ⟨hR, ht⟩, hc⟩ => ?_
  have ht : t = t' := (id_apply t t').mp ht
  subst ht
  rcases hc with ⟨hb, hy⟩ | ⟨hb, hy⟩
  · exact ⟨ConsList.cons (x, t) (ConsList.wrap ()), Or.inl ⟨hb, rfl⟩,
      (show y = _ from hy) ▸ ⟨⟨hR, (id_apply t t).mpr rfl⟩, trivial⟩⟩
  · exact ⟨ConsList.wrap (), Or.inr ⟨hb, rfl⟩, (show y = _ from hy) ▸ trivial⟩

/-- `(π₂ → π₁ wrap, nil)` is lax natural: `(R×𝟙)(π₂ → π₁ wrap, nil) ⊑ (π₂ → π₁ wrap, nil) list(R)`. -/
public theorem conditional_outl_wrap_laxNatural :
    LaxNatural (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)
      (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool)))
      (fun a => conditional (relProd a (dE Bool)).outr ((relProd a (dE Bool)).outl ≫ singleR ())
        nil) := by
  intro a b R
  show prodMap (relProd _ _) (relProd _ _) R (𝟙 (dE Bool)) ≫ _ ⊑ _ ≫ list R
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun ⟨x, t⟩ y ⟨⟨x', t'⟩, ⟨hR, ht⟩, hc⟩ => ?_
  have ht : t = t' := (id_apply t t').mp ht
  subst ht
  rcases hc with ⟨hb, x'', hx, hy⟩ | ⟨hb, hy⟩
  · have hx : x'' = x' := hx
    subst hx
    exact ⟨ConsList.cons x (ConsList.wrap ()), Or.inl ⟨hb, x, rfl, rfl⟩,
      (show y = _ from hy) ▸ ⟨hR, trivial⟩⟩
  · exact ⟨ConsList.wrap (), Or.inr ⟨hb, rfl⟩, (show y = _ from hy) ▸ trivial⟩

/-- `filter(π₂)` is lax natural: `list(R×𝟙) filter(π₂) ⊑ filter(π₂) list(R×𝟙)` — the conditional's
    square under `list`, then (1.6). -/
public theorem filter_outr_laxNatural :
    LaxNatural
      (Relator.comp (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool)))
        listRelator)
      (Relator.comp (Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool)))
        listRelator)
      (fun a => filter (relProd a (dE Bool)).outr) := by
  intro a b R
  have hel := conditional_wrap_laxNatural R
  show list ((Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool))).map R)
      ≫ filter _
    ⊑ filter _ ≫ list ((Relator.prod (Relator.idRelator RelSet.{0}) (Relator.const (dE Bool))).map R)
  unfold filter
  rw [← Cat.assoc, ← list_comp, Cat.assoc, ← concat_natural, ← Cat.assoc, ← list_comp]
  exact le_iff.mpr fun x z ⟨y, hy, hz⟩ => ⟨y, le_iff.mp (list_mono hel) _ _ hy, hz⟩

/-! ## The calculation of p.21–22, one theorem per step -/

variable (p : dE A ⟶ dE Bool)

/-- p.21 {definition of filter}. -/
public theorem filter_pointfree_step1 :
    rpair (𝟙 (dList A)) (list p) ≫ zip ≫ filter (relProd (dE A) (dE Bool)).outr
        ≫ list (relProd (dE A) (dE Bool)).outl
      = rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil)
          ≫ concatR ≫ list (relProd (dE A) (dE Bool)).outl := by
  rw [filter, Cat.assoc]

/-- p.21 {equation (1.6)}: `listr f · concat = concat · listr (listr f)`. -/
public theorem filter_pointfree_step2 :
    rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil)
          ≫ concatR ≫ list (relProd (dE A) (dE Bool)).outl
      = rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil)
          ≫ list (list (relProd (dE A) (dE Bool)).outl) ≫ concatR := by
  rw [concat_natural]

/-- p.21 {equation (1.8) (backwards)}: `listr f · listr g = listr (f · g)`. -/
public theorem filter_pointfree_step3 :
    rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil)
          ≫ list (list (relProd (dE A) (dE Bool)).outl) ≫ concatR
      = rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil
            ≫ list (relProd (dE A) (dE Bool)).outl) ≫ concatR := by
  rw [list_comp, Cat.assoc]

/-- p.21 {equations (1.11), (1.5), and (1.4)}. -/
public theorem filter_pointfree_step4 :
    rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr (singleR ()) nil
            ≫ list (relProd (dE A) (dE Bool)).outl) ≫ concatR
      = rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR := by
  rw [conditional_comp, wrap_natural, nil_list]

/-- p.21 {equation (1.9) (backwards)}: `listr id = id`. -/
public theorem filter_pointfree_step5 :
    rpair (𝟙 (dList A)) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR
      = rpair (list (𝟙 (dE A))) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR := by
  rw [list_id]

/-- p.21 {equation (1.7)}: `zip · pair (listr f, listr g) = listr (pair (f, g))`. -/
public theorem filter_pointfree_step6 :
    rpair (list (𝟙 (dE A))) (list p) ≫ zip
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR
      = list (rpair (𝟙 (dE A)) p)
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR := by
  rw [← Cat.assoc, zip_natural]

/-- p.22 {equation (1.8) (backwards)}. -/
public theorem filter_pointfree_step7 :
    list (rpair (𝟙 (dE A)) p)
          ≫ list (conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR
      = list (rpair (𝟙 (dE A)) p
          ≫ conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR := by
  rw [list_comp, Cat.assoc]

/-- p.22 {equations (1.10), (1.1), and (1.3)}. -/
public theorem filter_pointfree_step8 :
    list (rpair (𝟙 (dE A)) p
          ≫ conditional (relProd (dE A) (dE Bool)).outr
            ((relProd (dE A) (dE Bool)).outl ≫ singleR ()) nil) ≫ concatR
      = list (conditional p (𝟙 (dE A) ≫ singleR ()) nil) ≫ concatR := by
  rw [pair_conditional]

/-- p.22 {equation (1.12)}: `f · id = f`. -/
public theorem filter_pointfree_step9 :
    list (conditional p (𝟙 (dE A) ≫ singleR ()) nil) ≫ concatR
      = list (conditional p (singleR ()) nil) ≫ concatR := by
  rw [Cat.id_comp]

/-- p.22 {definition of filter}. -/
public theorem filter_pointfree_step10 :
    list (conditional p (singleR ()) nil) ≫ concatR = filter p := rfl

/-- **§1.7 (B&dM p.20–22)**: `listr outl · filter outr · zip · pair (id, listr p) = filter p`,
    mirrored: `⟨𝟙, list(p)⟩ zip filter(π₂) list(π₁) = filter(p)` — pair each element with its
    answer under `p`, keep the pairs answered `true`, drop the answers. -/
public theorem filter_pointfree :
    rpair (𝟙 (dList A)) (list p) ≫ zip ≫ filter (relProd (dE A) (dE Bool)).outr
        ≫ list (relProd (dE A) (dE Bool)).outl
      = filter p :=
  (filter_pointfree_step1 p).trans <| (filter_pointfree_step2 p).trans <|
    (filter_pointfree_step3 p).trans <| (filter_pointfree_step4 p).trans <|
    (filter_pointfree_step5 p).trans <| (filter_pointfree_step6 p).trans <|
    (filter_pointfree_step7 p).trans <| (filter_pointfree_step8 p).trans <|
    (filter_pointfree_step9 p).trans (filter_pointfree_step10 p)

-- printing-only: the book's names.  `nil` and `zip` take only implicit arguments, so they print as
-- bare constants no `app_unexpander` fires on; a delaborator names them.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.RelSet.Pointfree.nil, delab const.Freyd.Alg.RelSet.Pointfree.nil]
public meta def delabNil : Delab := `($(mkIdent `nil))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.RelSet.Pointfree.zip, delab const.Freyd.Alg.RelSet.Pointfree.zip]
public meta def delabZip : Delab := `($(mkIdent `zip))
open Lean PrettyPrinter in
@[app_unexpander conditional] public meta def unexpandConditional : Unexpander
  | `($_ $q $R $S) => `(($q → $R, $S))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander filter] public meta def unexpandFilter : Unexpander
  | `($_ $q) => `($(mkIdent `filter) $q)
  | _ => throw ()
-- B&dM's `wrap`, the one-element list: `singleR`'s leaf argument is the empty leaf `()`.
open Lean PrettyPrinter in
@[app_unexpander singleR] public meta def unexpandSingleR : Unexpander
  | `($_ $_) => `($(mkIdent `wrap))
  | _ => throw ()

end Freyd.Alg.RelSet.Pointfree
