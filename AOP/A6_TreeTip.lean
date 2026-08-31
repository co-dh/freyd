/-
  Bird & de Moor's LEAF-LABELLED binary tree `tree A ::= tip A ∣ bin (tree A, tree A)` as an
  initial algebra in `Rel(Set)` — the datatype §9.3's optimal-bracketing problem is stated over.

  `F X = A + X²`, so `F(R) = 𝟙 + R²`: the labels sit at the LEAVES, and a node carries nothing
  but its two subtrees.  That is a different functor from `AOP.A6_TreeBin`'s
  `F X = 1 + (X × A × X)` (labels at the internal nodes, empty leaves), so the two datatypes are
  siblings, not variants of one another.  Section-for-section port of `AOP.A6_TreeBin`: the
  functor as a `Relator` (with `PreservesRecip`), the structural fold defined DIRECTLY from the
  algebra-relation (no choice), the `InitialAlgebra` package, and reflection `⦇[tip,bin]⦈ = 𝟙`.
  Mathlib-free.
-/
module

public import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.TT

open Freyd

variable {A : Type}

/-- **mct-defn**: `tree A::=tip A∣bin (tree A,tree A)`. -/
public inductive Tree (A : Type) where
  | tip : A → Tree A
  | bin : Tree A → Tree A → Tree A

/-- The object carrying `Tree A`. -/
@[expose] public abbrev dTree (A : Type) : RelSet.{0} := ⟨Tree A⟩
/-- The object carrying the label type `A`. -/
@[expose] public abbrev dA (A : Type) : RelSet.{0} := ⟨A⟩

/-! ## The functor `F X = A + X²` -/

/-- Carrier of `F X`. -/
@[expose] public def TFobj (A : Type) (c : RelSet.{0}) : RelSet.{0} :=
  ⟨A ⊕ (c.carrier × c.carrier)⟩

/-- **mct-defn**: `F(R)=𝟙+R²` — the identity on the label summand, `R` in both slots of a node. -/
@[expose] public def Fmap (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') : TFobj A c ⟶ TFobj A c' :=
  fun u v => match u, v with
    | Sum.inl a, Sum.inl a' => a = a'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ R p.2 q.2
    | _, _ => False

@[simp] public theorem Fmap_ll (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (a a' : A) :
    Fmap A R (Sum.inl a) (Sum.inl a') = (a = a') := rfl
@[simp] public theorem Fmap_rr (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c')
    (p : c.carrier × c.carrier) (q : c'.carrier × c'.carrier) :
    Fmap A R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ R p.2 q.2) := rfl
@[simp] public theorem Fmap_lr (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (a : A)
    (q : c'.carrier × c'.carrier) : Fmap A R (Sum.inl a) (Sum.inr q) = False := rfl
@[simp] public theorem Fmap_rl (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c')
    (p : c.carrier × c.carrier) (a : A) : Fmap A R (Sum.inr p) (Sum.inl a) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (A : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := TFobj A
  map R := Fmap A R
  -- constructive (no `grind`): `grind` drags in Classical.choice, which would taint every
  -- catamorphism over `F` (the repo bar is axioms ⊆ {propext, Quot.sound})
  map_id c := hom_ext fun u v => by
    cases u <;> cases v
    · exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    · next a q => exact ⟨False.elim, fun h => nomatch (show Sum.inl a = Sum.inr q from h)⟩
    · next p a => exact ⟨False.elim, fun h => nomatch (show Sum.inr p = Sum.inl a from h)⟩
    · next p q =>
      exact ⟨fun ⟨h1, h2⟩ => congrArg Sum.inr (Prod.ext h1 h2),
        fun h => by cases Sum.inr.inj h; exact ⟨rfl, rfl⟩⟩
  map_comp R S := hom_ext fun u v => by
    cases u with
    | inl a => cases v with
      | inl a' =>
        simp only [Fmap_ll, comp_apply]
        exact ⟨fun h => ⟨Sum.inl a, rfl, h⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl m => exact hw1.trans hw2
            | inr q => exact hw1.elim⟩
      | inr q =>
        simp only [Fmap_lr, comp_apply]
        exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl m => exact hw2.elim
            | inr q' => exact hw1.elim⟩
    | inr p => cases v with
      | inl a' =>
        simp only [Fmap_rl, comp_apply]
        exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl m => exact hw1.elim
            | inr q' => exact hw2.elim⟩
      | inr q =>
        obtain ⟨pl, pr⟩ := p; obtain ⟨ql, qr⟩ := q
        simp only [Fmap_rr, comp_apply]
        constructor
        · rintro ⟨⟨m1, hRm1, hSm1⟩, ⟨m2, hRm2, hSm2⟩⟩
          exact ⟨Sum.inr (m1, m2), ⟨hRm1, hRm2⟩, ⟨hSm1, hSm2⟩⟩
        · rintro ⟨w, hw1, hw2⟩
          cases w with
          | inl m => rw [Fmap_rl] at hw1; exact hw1.elim
          | inr md =>
            obtain ⟨m1, m2⟩ := md
            rw [Fmap_rr] at hw1 hw2
            exact ⟨⟨m1, hw1.1, hw2.1⟩, ⟨m2, hw1.2, hw2.2⟩⟩
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first
        | exact id
        | exact fun hh => ⟨le_iff.mp h _ _ hh.1, le_iff.mp h _ _ hh.2⟩
        | exact False.elim

/-- `F` preserves converse. -/
public theorem F_preservesRecip (A : Type) : (F A).PreservesRecip := by
  intro c c' R
  apply hom_ext; intro u v
  cases u <;> cases v <;> simp only [F, Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
    first
      | exact ⟨fun h => h.symm, fun h => h.symm⟩
      | exact Iff.rfl

/-! ## `Tree A` is the initial algebra of `F` -/

/-- **mct-defn**: the constructor map `h ≜ [tip,bin] : F (tree A) → tree A`. -/
@[expose] public def con : (TFobj A (dTree A)).carrier → Tree A
  | Sum.inl a => Tree.tip a
  | Sum.inr (l, r) => Tree.bin l r

/-- The structural fold, defined DIRECTLY from the algebra-relation `f` (no choice). -/
@[expose] public def cataTreeFold {c : RelSet.{0}} (f : TFobj A c ⟶ c) : Tree A → c.carrier → Prop
  | Tree.tip a => fun r => f (Sum.inl a) r
  | Tree.bin l r => fun res =>
      ∃ rl rr, cataTreeFold f l rl ∧ cataTreeFold f r rr ∧ f (Sum.inr (rl, rr)) res

@[simp] public theorem cataTreeFold_tip {c : RelSet.{0}} (f : TFobj A c ⟶ c) (a : A)
    (r : c.carrier) : cataTreeFold f (Tree.tip a) r = f (Sum.inl a) r := rfl
@[simp] public theorem cataTreeFold_bin {c : RelSet.{0}} (f : TFobj A c ⟶ c) (l r : Tree A)
    (res : c.carrier) : cataTreeFold f (Tree.bin l r) res =
      ∃ rl rr, cataTreeFold f l rl ∧ cataTreeFold f r rr ∧ f (Sum.inr (rl, rr)) res := rfl

public theorem cataTree_total {c : RelSet.{0}} (f : TFobj A c ⟶ c) (hf : Map f) :
    ∀ t : Tree A, ∃ r, cataTreeFold f t r
  | Tree.tip a => entire_total hf.1 (Sum.inl a)
  | Tree.bin l r => by
    obtain ⟨rl, hrl⟩ := cataTree_total f hf l
    obtain ⟨rr, hrr⟩ := cataTree_total f hf r
    obtain ⟨res, hres⟩ := entire_total hf.1 (Sum.inr (rl, rr))
    exact ⟨res, rl, rr, hrl, hrr, hres⟩

public theorem cataTree_functional {c : RelSet.{0}} (f : TFobj A c ⟶ c) (hf : Map f) :
    ∀ (t : Tree A) (r r' : c.carrier), cataTreeFold f t r → cataTreeFold f t r' → r = r'
  | Tree.tip a, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | Tree.bin l r, res, res', h1, h2 => by
    obtain ⟨rl, rr, hl, hr, hf1⟩ := h1
    obtain ⟨rl', rr', hl', hr', hf2⟩ := h2
    obtain rfl : rl = rl' := cataTree_functional f hf l rl rl' hl hl'
    obtain rfl : rr = rr' := cataTree_functional f hf r rr rr' hr hr'
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
@[expose, instance] public def initial (A : Type) : InitialAlgebra (F A) where
  t := dTree A
  α := graph con
  α_map := graph_map con
  cata f _ := cataTreeFold f
  cata_map f hf := cataTree_map f hf
  cata_comm f hf := by
    apply hom_ext; intro u r
    cases u with
    | inl a =>
      constructor
      · intro h; obtain ⟨t, ht, hfold⟩ := h
        obtain rfl : t = Tree.tip a := ht
        exact ⟨Sum.inl a, rfl, hfold⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl a' => obtain rfl : a = a' := hv; exact ⟨Tree.tip a, rfl, hfv⟩
        | inr q => exact hv.elim
    | inr p =>
      obtain ⟨pl, pr⟩ := p
      constructor
      · intro h; obtain ⟨t, ht, hfold⟩ := h
        obtain rfl : t = Tree.bin pl pr := ht
        obtain ⟨rl, rr, hl, hr, hfr⟩ := hfold
        exact ⟨Sum.inr (rl, rr), ⟨hl, hr⟩, hfr⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl a => exact hv.elim
        | inr q =>
          obtain ⟨ql, qr⟩ := q
          exact ⟨Tree.bin pl pr, rfl, ql, qr, hv.1, hv.2, hfv⟩
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro t
    induction t with
    | tip a =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl a)) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl a) r := ⟨Tree.tip a, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl a' => obtain rfl : a = a' := hv; exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : ((F A).map h ≫ f) (Sum.inl a) r := ⟨Sum.inl a, rfl, hc⟩
        rw [← key] at hrhs
        obtain ⟨t, ht, hh⟩ := hrhs
        obtain rfl : t = Tree.tip a := ht
        exact hh
    | bin l r ihl ihr =>
      intro res
      have key := congrFun (congrFun hcomm (Sum.inr (l, r))) res
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (l, r)) res := ⟨Tree.bin l r, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl a => exact hv.elim
        | inr q =>
          obtain ⟨ql, qr⟩ := q
          exact ⟨ql, qr, (ihl ql).mp hv.1, (ihr qr).mp hv.2, hfv⟩
      · intro hc
        obtain ⟨rl, rr, hrl, hrr, hfr⟩ := hc
        have hrhs : ((F A).map h ≫ f) (Sum.inr (l, r)) res :=
          ⟨Sum.inr (rl, rr), ⟨(ihl rl).mpr hrl, (ihr rr).mpr hrr⟩, hfr⟩
        rw [← key] at hrhs
        obtain ⟨t, ht, hh⟩ := hrhs
        obtain rfl : t = Tree.bin l r := ht
        exact hh

/-- The catamorphism (fold) of `φ` as a genuine morphism `dTree A ⟶ c`. -/
@[expose] public def cataR {c : RelSet.{0}} (φ : TFobj A c ⟶ c) : dTree A ⟶ c := cataTreeFold φ

/-- The catamorphism computation rule for ANY algebra-relation `φ` (not just maps). -/
public theorem cataTreeFold_comm {c : RelSet.{0}} (φ : TFobj A c ⟶ c) :
    graph con ≫ cataTreeFold φ = (F A).map (cataTreeFold φ) ≫ φ := by
  apply hom_ext; intro u r
  cases u with
  | inl a =>
    constructor
    · intro h; obtain ⟨t, ht, hfold⟩ := h
      obtain rfl : t = Tree.tip a := ht
      exact ⟨Sum.inl a, rfl, hfold⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl a' => obtain rfl : a = a' := hv; exact ⟨Tree.tip a, rfl, hfv⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨pl, pr⟩ := p
    constructor
    · intro h; obtain ⟨t, ht, hfold⟩ := h
      obtain rfl : t = Tree.bin pl pr := ht
      obtain ⟨rl, rr, hl, hr, hfr⟩ := hfold
      exact ⟨Sum.inr (rl, rr), ⟨hl, hr⟩, hfr⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl a => exact hv.elim
      | inr q =>
        obtain ⟨ql, qr⟩ := q
        exact ⟨Tree.bin pl pr, rfl, ql, qr, hv.1, hv.2, hfv⟩

/-- The structural tree fold IS the relational catamorphism `relCata I φ` (Eilenberg–Wright). -/
public theorem cataR_eq_relCata {c : RelSet.{0}} (φ : (F A).obj c ⟶ c) :
    cataR φ = relCata φ :=
  (relCata_UP (initial A) φ (cataR φ)).mp (cataTreeFold_comm φ)

/-- **Reflection**: `⦇[tip,bin]⦈ = 𝟙` — what collapses `H = ⦇h⦈·⦇T⦈°` to `⦇T⦈°` whenever the
    refolding algebra is the constructor itself. -/
public theorem cataR_con : cataR (graph (con (A := A))) = 𝟙 (dTree A) := by
  apply hom_ext; intro t
  induction t with
  | tip a => exact fun r => ⟨Eq.symm, Eq.symm⟩
  | bin l r ihl ihr =>
    intro res
    constructor
    · rintro ⟨rl, rr, hl, hr, hcon⟩
      obtain rfl : l = rl := (ihl rl).mp hl
      obtain rfl : r = rr := (ihr rr).mp hr
      exact (hcon : res = Tree.bin l r).symm
    · intro (h : Tree.bin l r = res)
      exact ⟨l, r, (ihl l).mpr rfl, (ihr r).mpr rfl, h.symm⟩

end Freyd.Alg.RelSet.TT
