/-
  Generic BINARY TREE datatype as an initial algebra in `Rel(Set)` — the tree-shaped companion of
  `AOP.A6_SnocList`/`AOP.A6_ConsList`, unlocking the LeetCode Tree block (§104 depth, §226
  invert, §100 same-tree, §98 BST, §124 path sum, …).

  `Tree A` (`A`-labelled internal nodes, empty leaves) is `nil | node (Tree A) A (Tree A)`, the
  initial algebra of the polynomial functor `F X = 1 + (X × A × X)`.  Same construction as
  `A6_SnocList` (SECTION-FOR-SECTION port): build the functor as a `Relator` (with
  `PreservesRecip`), the structural fold `cataTreeFold` defined DIRECTLY from the
  algebra-relation (no choice), and the `InitialAlgebra` package (`cataR`-style relational cata).
  Mathlib-free.
-/
module

public import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.TB

open Freyd

variable {A : Type}

/-- The binary tree datatype: empty leaves `nil`, `A`-labelled internal nodes. -/
public inductive Tree (A : Type) where
  | nil  : Tree A
  | node : Tree A → A → Tree A → Tree A

/-- The object carrying `Tree A`. -/
@[expose] public abbrev dTree (A : Type) : RelSet.{0} := ⟨Tree A⟩
/-- The object carrying the label type `A`. -/
abbrev dA (A : Type) : RelSet.{0} := ⟨A⟩

/-! ## Two elementary `Rel(Set)` facts about maps -/

/-- An entire relation relates every point to something. -/
public theorem entire_total {a b : RelSet.{u}} {R : a ⟶ b} (h : Entire R) (x : a.carrier) :
    ∃ y, R x y := by
  have hd : (dom R) x x := by
    have e : (dom R) x x = (Cat.id a) x x := congrFun (congrFun h x) x
    rw [e]; rfl
  obtain ⟨_, y, hy, _⟩ := hd
  exact ⟨y, hy⟩

/-- A simple relation is single-valued. -/
public theorem simple_uniq {a b : RelSet.{u}} {R : a ⟶ b} (h : Simple R) {x : a.carrier}
    {y y' : b.carrier} (hy : R x y) (hy' : R x y') : y = y' :=
  le_iff.mp h y y' ⟨x, hy, hy'⟩

/-! ## The functor `F X = 1 + (X × A × X)` -/

/-- Carrier of `F X`. -/
@[expose] public def TFobj (A : Type) (c : RelSet.{0}) : RelSet.{0} := ⟨Unit ⊕ (c.carrier × A × c.carrier)⟩

/-- Action of `F` on a relation: identity on the `1` summand, `R × id × R` on `X × A × X`. -/
@[expose] public def Fmap (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') : TFobj A c ⟶ TFobj A c' :=
  fun u v => match u, v with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2.1 = q.2.1 ∧ R p.2.2 q.2.2
    | _, _ => False

@[simp] theorem Fmap_ll (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (x y : Unit) :
    Fmap A R (Sum.inl x) (Sum.inl y) = True := rfl
@[simp] public theorem Fmap_rr (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c')
    (p : c.carrier × A × c.carrier) (q : c'.carrier × A × c'.carrier) :
    Fmap A R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2.1 = q.2.1 ∧ R p.2.2 q.2.2) := rfl
@[simp] theorem Fmap_lr (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (x : Unit)
    (q : c'.carrier × A × c'.carrier) : Fmap A R (Sum.inl x) (Sum.inr q) = False := rfl
@[simp] public theorem Fmap_rl (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c')
    (p : c.carrier × A × c.carrier) (y : Unit) : Fmap A R (Sum.inr p) (Sum.inl y) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (A : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := TFobj A
  map R := Fmap A R
  map_id c := hom_ext fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl, id_apply] <;> grind
  map_comp R S := hom_ext fun u v => by
    cases u with
    | inl x => cases v with
      | inl y =>
        simp only [Fmap_ll, comp_apply]
        exact ⟨fun _ => ⟨Sum.inl x, trivial, trivial⟩, fun _ => trivial⟩
      | inr q =>
        simp only [Fmap_lr, comp_apply]
        exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl z => exact hw2.elim
            | inr q' => exact hw1.elim⟩
    | inr p => cases v with
      | inl y =>
        simp only [Fmap_rl, comp_apply]
        exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl z => exact hw1.elim
            | inr q' => exact hw2.elim⟩
      | inr q =>
        obtain ⟨pl, pa, pr⟩ := p; obtain ⟨ql, qa, qr⟩ := q
        simp only [Fmap_rr, comp_apply]
        constructor
        · rintro ⟨⟨m1, hRm1, hSm1⟩, hpq, ⟨m2, hRm2, hSm2⟩⟩
          exact ⟨Sum.inr (m1, pa, m2), ⟨hRm1, rfl, hRm2⟩, ⟨hSm1, hpq, hSm2⟩⟩
        · rintro ⟨w, hw1, hw2⟩
          cases w with
          | inl z => rw [Fmap_rl] at hw1; exact hw1.elim
          | inr md =>
            obtain ⟨m1, ma, m2⟩ := md
            rw [Fmap_rr] at hw1 hw2
            obtain ⟨hRm1, hpa, hRm2⟩ := hw1
            obtain ⟨hSm1, haq, hSm2⟩ := hw2
            exact ⟨⟨m1, hRm1, hSm1⟩, hpa.trans haq, ⟨m2, hRm2, hSm2⟩⟩
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first
        | exact id
        | exact fun hh => ⟨le_iff.mp h _ _ hh.1, hh.2.1, le_iff.mp h _ _ hh.2.2⟩
        | exact False.elim

/-- `F` preserves converse. -/
public theorem F_preservesRecip (A : Type) : (F A).PreservesRecip := by
  intro c c' R
  apply hom_ext; intro u v
  cases u <;> cases v <;> simp only [F, Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
    first
      | exact ⟨fun h => h.symm, fun h => h.symm⟩
      | exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3⟩⟩
      | exact Iff.rfl

/-! ## `Tree A` is the initial algebra of `F` -/

/-- The constructor map `[nil, node] : F (Tree A) → Tree A`. -/
@[expose] public def con : (TFobj A (dTree A)).carrier → Tree A
  | Sum.inl _ => Tree.nil
  | Sum.inr (l, a, r) => Tree.node l a r

/-- The structural fold, defined DIRECTLY from the algebra-relation `f` (no choice). -/
@[expose] public def cataTreeFold {c : RelSet.{0}} (f : TFobj A c ⟶ c) : Tree A → c.carrier → Prop
  | Tree.nil => fun r => f (Sum.inl ()) r
  | Tree.node l a r => fun res =>
      ∃ rl rr, cataTreeFold f l rl ∧ cataTreeFold f r rr ∧ f (Sum.inr (rl, a, rr)) res

@[simp] public theorem cataTreeFold_nil {c : RelSet.{0}} (f : TFobj A c ⟶ c) (r : c.carrier) :
    cataTreeFold f Tree.nil r = f (Sum.inl ()) r := rfl
@[simp] public theorem cataTreeFold_node {c : RelSet.{0}} (f : TFobj A c ⟶ c) (l r : Tree A) (a : A)
    (res : c.carrier) : cataTreeFold f (Tree.node l a r) res =
      ∃ rl rr, cataTreeFold f l rl ∧ cataTreeFold f r rr ∧ f (Sum.inr (rl, a, rr)) res := rfl

public theorem cataTree_total {c : RelSet.{0}} (f : TFobj A c ⟶ c) (hf : Map f) :
    ∀ t : Tree A, ∃ r, cataTreeFold f t r
  | Tree.nil => entire_total hf.1 (Sum.inl ())
  | Tree.node l a r => by
    obtain ⟨rl, hrl⟩ := cataTree_total f hf l
    obtain ⟨rr, hrr⟩ := cataTree_total f hf r
    obtain ⟨res, hres⟩ := entire_total hf.1 (Sum.inr (rl, a, rr))
    exact ⟨res, rl, rr, hrl, hrr, hres⟩

public theorem cataTree_functional {c : RelSet.{0}} (f : TFobj A c ⟶ c) (hf : Map f) :
    ∀ (t : Tree A) (r r' : c.carrier), cataTreeFold f t r → cataTreeFold f t r' → r = r'
  | Tree.nil, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | Tree.node l a r, res, res', h1, h2 => by
    obtain ⟨rl, rr, hl, hr, hf1⟩ := h1
    obtain ⟨rl', rr', hl', hr', hf2⟩ := h2
    have hll : rl = rl' := cataTree_functional f hf l rl rl' hl hl'
    have hrr' : rr = rr' := cataTree_functional f hf r rr rr' hr hr'
    subst hll; subst hrr'
    exact simple_uniq hf.2 hf1 hf2

public theorem cataTree_map {c : RelSet.{0}} (f : TFobj A c ⟶ c) (hf : Map f) :
    Map (a := dTree A) (b := c) (cataTreeFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataTreeFold f) = Cat.id (dTree A)
    apply hom_ext; intro t t'
    refine ⟨fun h => h.1, fun (h : t = t') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataTree_total f hf t
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨t, h1, h2⟩ := h
    exact cataTree_functional f hf t r r' h1 h2

/-- The initial `F`-algebra structure on `Tree A`. -/
@[expose] public def initial (A : Type) : InitialAlgebra (F A) where
  t := dTree A
  α := graph con
  α_map := graph_map con
  cata f _ := cataTreeFold f
  cata_map f hf := cataTree_map f hf
  cata_comm f hf := by
    apply hom_ext; intro u r
    cases u with
    | inl x =>
      constructor
      · intro h; obtain ⟨t, ht, hfold⟩ := h
        have hteq : t = Tree.nil := ht
        rw [hteq] at hfold
        exact ⟨Sum.inl x, trivial, hfold⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl w => exact ⟨Tree.nil, rfl, hfv⟩
        | inr q => exact hv.elim
    | inr p =>
      obtain ⟨pl, pa, pr⟩ := p
      constructor
      · intro h; obtain ⟨t, ht, hfold⟩ := h
        have hteq : t = Tree.node pl pa pr := ht
        rw [hteq] at hfold
        obtain ⟨rl, rr, hl, hr, hfr⟩ := hfold
        exact ⟨Sum.inr (rl, pa, rr), ⟨hl, rfl, hr⟩, hfr⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl w => exact hv.elim
        | inr q =>
          obtain ⟨ql, qa, qr⟩ := q
          obtain ⟨hq1, hq2, hq3⟩ := hv
          have hpa : pa = qa := hq2
          refine ⟨Tree.node pl pa pr, rfl, ql, qr, hq1, hq3, ?_⟩
          rw [hpa]; exact hfv
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro t
    induction t with
    | nil =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl ())) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl ()) r := ⟨Tree.nil, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl w => exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : ((F A).map h ≫ f) (Sum.inl ()) r := ⟨Sum.inl (), trivial, hc⟩
        rw [← key] at hrhs
        obtain ⟨t, ht, hh⟩ := hrhs
        have hteq : t = Tree.nil := ht
        rw [hteq] at hh; exact hh
    | node l a r ihl ihr =>
      intro res
      have key := congrFun (congrFun hcomm (Sum.inr (l, a, r))) res
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (l, a, r)) res := ⟨Tree.node l a r, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl w => exact hv.elim
        | inr q =>
          obtain ⟨ql, qa, qr⟩ := q
          obtain ⟨hq1, hq2, hq3⟩ := hv
          have haq : a = qa := hq2
          refine ⟨ql, qr, (ihl ql).mp hq1, (ihr qr).mp hq3, ?_⟩
          rw [haq]; exact hfv
      · intro hc
        obtain ⟨rl, rr, hrl, hrr, hfr⟩ := hc
        have hrhs : ((F A).map h ≫ f) (Sum.inr (l, a, r)) res :=
          ⟨Sum.inr (rl, a, rr), ⟨(ihl rl).mpr hrl, rfl, (ihr rr).mpr hrr⟩, hfr⟩
        rw [← key] at hrhs
        obtain ⟨t, ht, hh⟩ := hrhs
        have hteq : t = Tree.node l a r := ht
        rw [hteq] at hh; exact hh

/-- The catamorphism (fold) of `φ` as a genuine morphism `dTree A ⟶ c`. -/
@[expose] public def cataR {c : RelSet.{0}} (φ : TFobj A c ⟶ c) : dTree A ⟶ c := cataTreeFold φ

/-- The book's banana brackets for the catamorphism — one global overload per datatype engine,
    disambiguated by the algebra's type. -/
notation:max "⦇" φ "⦈" => cataR φ

/-- The catamorphism computation rule holds for ANY algebra-relation `φ` (not just maps):
    `α ≫ cataTreeFold φ = F(cataTreeFold φ) ≫ φ`.  This is the `Map`-free form of `initial`'s own
    `cata_comm` field — the structural proof never references `Map φ` — and is the tree analogue of
    `A6_SnocList.cataFold_comm`. -/
public theorem cataTreeFold_comm {c : RelSet.{0}} (φ : TFobj A c ⟶ c) :
    graph con ≫ cataTreeFold φ = (F A).map (cataTreeFold φ) ≫ φ := by
  apply hom_ext; intro u r
  cases u with
  | inl x =>
    constructor
    · intro h; obtain ⟨t, ht, hfold⟩ := h
      have hteq : t = Tree.nil := ht
      rw [hteq] at hfold
      exact ⟨Sum.inl x, trivial, hfold⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl w => exact ⟨Tree.nil, rfl, hfv⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨pl, pa, pr⟩ := p
    constructor
    · intro h; obtain ⟨t, ht, hfold⟩ := h
      have hteq : t = Tree.node pl pa pr := ht
      rw [hteq] at hfold
      obtain ⟨rl, rr, hl, hr, hfr⟩ := hfold
      exact ⟨Sum.inr (rl, pa, rr), ⟨hl, rfl, hr⟩, hfr⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl w => exact hv.elim
      | inr q =>
        obtain ⟨ql, qa, qr⟩ := q
        obtain ⟨hq1, hq2, hq3⟩ := hv
        have hpa : pa = qa := hq2
        refine ⟨Tree.node pl pa pr, rfl, ql, qr, hq1, hq3, ?_⟩
        rw [hpa]; exact hfv

/-- The structural tree fold IS the relational catamorphism `relCata I φ` (Eilenberg–Wright, via
    `cataTreeFold_comm` and the universal property `relCata_UP`).  Lets the abstract catamorphism
    laws (fusion, greedy, …) apply to `cataR` over binary trees.  Tree analogue of
    `A6_SnocList.cataR_eq_relCata`. -/
public theorem cataR_eq_relCata {c : RelSet.{0}} (φ : TFobj A c ⟶ c) :
    cataR φ = relCata (initial A) φ :=
  (relCata_UP (initial A) φ (cataR φ)).mp (cataTreeFold_comm φ)

end Freyd.Alg.RelSet.TB
