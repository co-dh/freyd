/-
  Generic CONS-LIST datatype as an initial algebra in `Rel(Set)` — the `head`/`tail` companion of
  `AOP.A6_SnocList`, for the Bird & de Moor list programs (§6.6 sorting onward).

  `ConsList L E` (leaf type `L`, element type `E`) is `wrap L | cons E (ConsList L E)`, the initial
  algebra of the polynomial functor `F X = L + (E × X)` (element on the LEFT of the product,
  recursion on the tail).  `list A` of the book is `ConsList Unit A` (`wrap () = nil`,
  `cons a x`).  Same construction as `A6_SnocList`, product swapped so folds run head-first.
-/
module

public import AOP.A6_1_RelSet
-- for `F_eq_sum_prod`: the `+` half of the generic relator combination lives in §5.3.
public import AOP.A5_3

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.CL

open Freyd

variable {L E : Type}

/-- The cons-list datatype: a leaf `wrap l`, extended by `cons`-ing elements on the front. -/
public inductive ConsList (L E : Type) where
  | wrap : L → ConsList L E
  | cons : E → ConsList L E → ConsList L E

/-- Reshape a raw Lean `List E` onto the initial algebra as a `ConsList Unit E`
    (`[] ↦ wrap ()`, `x :: xs ↦ cons x (ofList xs)`).  The book's `list A` is `ConsList Unit A`,
    so this is the canonical bridge for deriving folds over raw input lists; use it instead of
    re-declaring a per-file copy. -/
@[expose] public def ofList : List E → ConsList Unit E
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

@[simp] theorem ofList_nil : (ofList [] : ConsList Unit E) = ConsList.wrap () := rfl
@[simp] public theorem ofList_cons (x : E) (xs : List E) :
    ofList (x :: xs) = ConsList.cons x (ofList xs) := rfl

/-- The object carrying `ConsList L E`. -/
@[expose] public abbrev dCL (L E : Type) : RelSet.{0} := ⟨ConsList L E⟩
/-- The object carrying the leaf type `L`. -/
@[expose] public abbrev dL (L : Type) : RelSet.{0} := ⟨L⟩
/-- The object carrying the element type `E`. -/
@[expose] public abbrev dE (E : Type) : RelSet.{0} := ⟨E⟩

/-! ## The functor `F X = L + (E × X)` -/

/-- Carrier of `F X`. -/
@[expose] public def Fobj (L E : Type) (c : RelSet.{0}) : RelSet.{0} := ⟨L ⊕ (E × c.carrier)⟩

/-- Action of `F` on a relation: identity on the `L` summand, `id × R` on `E × X`. -/
@[expose] public def Fmap (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') : Fobj L E c ⟶ Fobj L E c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => p.1 = q.1 ∧ R p.2 q.2
    | _, _ => False

@[simp] theorem Fmap_ll (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (d d' : L) :
    Fmap L E R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (p : E × c.carrier)
    (q : E × c'.carrier) : Fmap L E R (Sum.inr p) (Sum.inr q) = (p.1 = q.1 ∧ R p.2 q.2) := rfl
@[simp] theorem Fmap_lr (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (d : L) (q : E × c'.carrier) :
    Fmap L E R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (p : E × c.carrier) (d : L) :
    Fmap L E R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (L E : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj L E
  map R := Fmap L E R
  -- constructive (no `grind`): `grind` drags in Classical.choice, which would taint every
  -- catamorphism over `F` (the repo bar is axioms ⊆ {propext, Quot.sound}).
  map_id c := hom_ext fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl, id_apply] <;>
      first
        | exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
        | exact ⟨False.elim, fun h => nomatch h⟩
        | exact ⟨fun h => congrArg Sum.inr (Prod.ext_iff.mpr h),
            fun h => Prod.ext_iff.mp (Sum.inr.inj h)⟩
  map_comp R S := hom_ext fun u v => by
    cases u with
    | inl d => cases v with
      | inl d' => exact ⟨fun h => ⟨Sum.inl d, rfl, h⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.trans hw2
            | inr q => exact hw1.elim⟩
      | inr q => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw2.elim
            | inr q' => exact hw1.elim⟩
    | inr p => cases v with
      | inl d' => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr q' => exact hw2.elim⟩
      | inr q =>
        obtain ⟨pa, pd⟩ := p; obtain ⟨qa, qd⟩ := q
        exact ⟨fun ⟨hpq, m, hRm, hSm⟩ => ⟨Sum.inr (pa, m), ⟨rfl, hRm⟩, ⟨hpq, hSm⟩⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr md =>
              obtain ⟨ma, mtl⟩ := md
              exact ⟨hw1.1.trans hw2.1, mtl, hw1.2, hw2.2⟩⟩
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first | exact id | exact fun hh => ⟨hh.1, le_iff.mp h _ _ hh.2⟩ | exact False.elim

/-- `F` preserves converse. -/
public theorem F_preservesRecip (L E : Type) : (F L E).PreservesRecip := by
  intro c c' R
  apply hom_ext; intro u v
  cases u <;> cases v <;> simp only [F, Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
    first
      | exact ⟨fun h => h.symm, fun h => h.symm⟩
      | exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
      | exact Iff.rfl

/-- `F` IS the generic relator combination `const L + (const E × id)` of §5.2/§5.3, not merely
    isomorphic to it: `Rel(Set)` names its own coproduct (`sumCop`) and its own relational product
    (`HasRelProd`), so the two sides agree on OBJECTS definitionally — which is what makes this
    equation typecheck — and the calculation below settles them on relations. -/
public theorem F_eq_sum_prod (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') :
    (Relator.sum (Relator.const (dL L))
        (Relator.prod (Relator.const (dE E)) (Relator.idRelator RelSet.{0}))).map R
      = (F L E).map R := by
  apply hom_ext; intro u v
  cases u <;> cases v <;>
    simp [F, Fmap, Relator.sum, Relator.prod, Relator.const, Relator.idRelator, sumMap, junc,
      RelProd.pair, prodMap, graph, instPositiveAllegory, instHasRelProd, sumCop] <;> grind

/-! ## `ConsList L E` is the initial algebra of `F` -/

/-- The constructor map `[wrap, cons] : F (ConsList L E) → ConsList L E`. -/
@[expose] public def con : (Fobj L E (dCL L E)).carrier → ConsList L E
  | Sum.inl d => ConsList.wrap d
  | Sum.inr p => ConsList.cons p.1 p.2

/-- The structural fold, defined DIRECTLY from the algebra-relation `f` (no choice). -/
@[expose] public def cataFold {c : RelSet.{0}} (f : Fobj L E c ⟶ c) : ConsList L E → c.carrier → Prop
  | ConsList.wrap d => fun r => f (Sum.inl d) r
  | ConsList.cons dig dec => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (dig, r')) r

@[simp] public theorem cataFold_wrap {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (d : L) (r : c.carrier) :
    cataFold f (ConsList.wrap d) r = f (Sum.inl d) r := rfl
@[simp] public theorem cataFold_cons {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (dig : E) (dec : ConsList L E)
    (r : c.carrier) :
    cataFold f (ConsList.cons dig dec) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (dig, r')) r := rfl

public theorem cataFold_total {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    ∀ dec : ConsList L E, ∃ r, cataFold f dec r
  | ConsList.wrap d => entire_total hf.1 (Sum.inl d)
  | ConsList.cons dig dec => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (dig, r'))
    exact ⟨r, r', hr', hr⟩

public theorem cataFold_functional {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    ∀ (dec : ConsList L E) (r r' : c.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | ConsList.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | ConsList.cons dig dec, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

public theorem cataFold_map {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    Map (a := dCL L E) (b := c) (cataFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataFold f) = Cat.id (dCL L E)
    apply hom_ext; intro dec dec'
    refine ⟨fun h => h.1, fun (h : dec = dec') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataFold_total f hf dec
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨dec, h1, h2⟩ := h
    exact cataFold_functional f hf dec r r' h1 h2

/-- The initial `F`-algebra structure on `ConsList L E`. -/
@[expose, instance] public def initial (L E : Type) : InitialAlgebra (F L E) where
  t := dCL L E
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := by
    apply hom_ext; intro u r
    cases u with
    | inl d =>
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = ConsList.wrap d := hdec; subst hd
        exact ⟨Sum.inl d, rfl, hfold⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨ConsList.wrap d, rfl, hfv⟩
        | inr q => exact hv.elim
    | inr p =>
      obtain ⟨dig, tail⟩ := p
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = ConsList.cons dig tail := hdec; subst hd
        obtain ⟨r', hr', hfr'⟩ := hfold
        exact ⟨Sum.inr (dig, r'), ⟨rfl, hr'⟩, hfr'⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qtl⟩ := q
          obtain ⟨hqa, hcata⟩ := hv
          refine ⟨ConsList.cons dig tail, rfl, qtl, hcata, ?_⟩
          have hd2 : dig = qa := hqa; rw [hd2]; exact hfv
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro dec
    induction dec with
    | wrap d =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl d)) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl d) r := ⟨ConsList.wrap d, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : ((F L E).map h ≫ f) (Sum.inl d) r := ⟨Sum.inl d, rfl, hc⟩
        rw [← key] at hrhs
        obtain ⟨dec, hdec, hh⟩ := hrhs
        have hd : dec = ConsList.wrap d := hdec; subst hd; exact hh
    | cons dig tail ih =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inr (dig, tail))) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (dig, tail)) r := ⟨ConsList.cons dig tail, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qtl⟩ := q
          obtain ⟨hqa, hcata⟩ := hv
          refine ⟨qtl, (ih qtl).mp hcata, ?_⟩
          have hd2 : dig = qa := hqa; rw [hd2]; exact hfv
      · intro hc
        obtain ⟨r', hr', hfr'⟩ := hc
        have hrhs : ((F L E).map h ≫ f) (Sum.inr (dig, tail)) r :=
          ⟨Sum.inr (dig, r'), ⟨rfl, (ih r').mpr hr'⟩, hfr'⟩
        rw [← key] at hrhs
        obtain ⟨d', hd', hh⟩ := hrhs
        have hd : d' = ConsList.cons dig tail := hd'; subst hd; exact hh

/-! ## The recursive equation for the converse of a catamorphism -/

/-- The catamorphism (fold) of `φ` as a genuine morphism `dCL L E ⟶ c`. -/
@[expose] public def cataR {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) : dCL L E ⟶ c := cataFold φ

/-- The catamorphism computation rule holds for ANY algebra-relation `φ` (not just maps):
    `α ≫ cataFold φ = F(cataFold φ) ≫ φ`.  (The structural proof never uses `Map φ`.) -/
public theorem cataFold_comm {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
    graph con ≫ cataFold φ = (F L E).map (cataFold φ) ≫ φ := by
  apply hom_ext; intro u r
  cases u with
  | inl d =>
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = ConsList.wrap d := hdec; subst hd
      exact ⟨Sum.inl d, rfl, hfold⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨ConsList.wrap d, rfl, hfv⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨dig, tail⟩ := p
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = ConsList.cons dig tail := hdec; subst hd
      obtain ⟨r', hr', hfr'⟩ := hfold
      exact ⟨Sum.inr (dig, r'), ⟨rfl, hr'⟩, hfr'⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => exact hv.elim
      | inr q =>
        obtain ⟨qa, qtl⟩ := q
        obtain ⟨hqa, hcata⟩ := hv
        refine ⟨ConsList.cons dig tail, rfl, qtl, hcata, ?_⟩
        have hd2 : dig = qa := hqa; rw [hd2]; exact hfv

/-- The structural fold IS the relational catamorphism `relCata I φ` (Eilenberg–Wright, via
    `cataFold_comm` and the universal property `relCata_UP`).  Lets the abstract catamorphism laws
    (fusion, …) apply to `cataR`. -/
public theorem cataR_eq_relCata {c : RelSet.{0}} (φ : (F L E).obj c ⟶ c) :
    cataR φ = relCata φ :=
  (relCata_UP (initial L E) φ (cataR φ)).mp (cataFold_comm φ)

/-- **Reflection**: the fold of the constructor algebra is the identity, `⦇[wrap,cons]⦈ = 𝟙`.
    What collapses `H = ⦇h⦈·⦇T⦈°` to `⦇T⦈°` whenever the refolding algebra is `α` itself. -/
public theorem cataR_con : cataR (graph (con (L := L) (E := E))) = 𝟙 (dCL L E) := by
  apply hom_ext; intro dec
  induction dec with
  | wrap d => exact fun r => ⟨Eq.symm, Eq.symm⟩
  | cons a x ih =>
    intro r
    constructor
    · rintro ⟨r', hr', hcon⟩
      obtain rfl : x = r' := (ih r').mp hr'
      exact (hcon : r = ConsList.cons a x).symm
    · intro (h : ConsList.cons a x = r)
      exact ⟨x, (ih x).mpr rfl, h.symm⟩

/-- The `wrap`-component of an algebra `φ = [g, h]`. -/
@[expose] public def algWrap {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) : dL L ⟶ c := fun d r => φ (Sum.inl d) r
/-- The `cons`-component of an algebra `φ = [g, h]`. -/
@[expose] public def algCons {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) : (⟨E × c.carrier⟩ : RelSet.{0}) ⟶ c :=
  fun p r => φ (Sum.inr p) r

/-- The constructor `wrap` (`nil`) as a relation. -/
@[expose] public def wrapR : dL L ⟶ dCL L E := graph ConsList.wrap
/-- The constructor `cons` as a relation. -/
@[expose] public def consR : (⟨E × ConsList L E⟩ : RelSet.{0}) ⟶ dCL L E := graph (fun p => ConsList.cons p.1 p.2)

/-- The recursive equation for the converse of a cons-list catamorphism:
    `val° = (wrap·g°) ∪ (cons·(id×val°)·h°)` (mirrored), for any algebra `φ = [g, h]`. -/
public theorem cata_converse_eq {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
    (cataR φ)° = (algWrap φ)° ≫ wrapR
      ∪ (algCons φ)° ≫ rprodMap (Cat.id (dE E)) (cataR φ)° ≫ consR := by
  apply hom_ext; intro r dec
  cases dec with
  | wrap d =>
    constructor
    · intro h
      exact Or.inl ⟨d, h, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        have hd : d = e := ConsList.wrap.inj hde
        rw [hd]; exact he
      | inr h =>
        obtain ⟨p, hp, q, hq, hcons⟩ := h
        obtain ⟨qa, qtl⟩ := q
        have hc : ConsList.wrap d = ConsList.cons qa qtl := hcons
        nomatch hc
  | cons dig tail =>
    constructor
    · intro h
      obtain ⟨r', hr', hφ⟩ := h
      exact Or.inr ⟨(dig, r'), hφ, (dig, tail), ⟨rfl, hr'⟩, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        have hc : ConsList.cons dig tail = ConsList.wrap e := hde
        nomatch hc
      | inr h =>
        obtain ⟨p, hp, q, hq, hcons⟩ := h
        obtain ⟨pa, ptl⟩ := p
        obtain ⟨qa, qtl⟩ := q
        obtain ⟨hpq, hcata⟩ := hq
        obtain ⟨hda, hdd⟩ := ConsList.cons.inj hcons
        refine ⟨ptl, ?_, ?_⟩
        · rw [hdd]; exact hcata
        · have hpa : pa = dig := hpq.trans hda.symm
          rw [hpa] at hp; exact hp

end Freyd.Alg.RelSet.CL
