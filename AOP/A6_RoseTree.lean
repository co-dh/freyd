/-
  ROSE-TREE datatype as an initial algebra in `Rel(Set)` — the carrier of Bird & de Moor §7.3
  (planning a company party, book p.175): `tree A ::= node (A, [tree A])`.

  `Rose A` is the nested inductive `node : A → ConsList Unit (Rose A) → Rose A`, the initial
  algebra of the base functor `F(A, X) = A × [X]` (`Fmap = 𝟙 × list(R)`, built on the list
  relator of `AOP.A5_6_ListCombinators`).  The structural fold is defined MUTUALLY with its
  own list-of-subtrees fold (`cataFoldList`, provably `list(cataFold f)`) so the nested
  recursion stays structural; every proof about it is the same mutual tree/list induction.
  Same construction as `A6_ConsList`, one recursive position per list element.
-/
module

public import AOP.A5_6_ListCombinators

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.RT

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-- The rose-tree datatype `tree A ::= node (A, [tree A])` (B&dM §7.3 p.175): an employee,
    and the list of subtrees under them. -/
public inductive Rose (A : Type) where
  | node : A → ConsList Unit (Rose A) → Rose A

/-- The object carrying `tree A`. -/
@[expose] public abbrev dRose (A : Type) : RelSet.{0} := ⟨Rose A⟩

/-! ## The base functor `F(A, X) = A × [X]` -/

/-- Carrier of `F(A, X) = A × [X]`: an employee beside the recursive positions, one layer deep. -/
@[expose] public def Fobj (A : Type) (c : RelSet.{0}) : RelSet.{0} := ⟨A × ConsList Unit c.carrier⟩

/-- Action of `F` on a relation: `𝟙 × list(R)` — the root untouched, the subtree results
    related elementwise. -/
@[expose] public def Fmap (A : Type) {c c' : RelSet.{0}} (R : c ⟶ c') : Fobj A c ⟶ Fobj A c' :=
  rprodMap (𝟙 (dE A)) (list (A := c.carrier) (B := c'.carrier) R)

/-- `F(A, −)` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (A : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj A
  map := Fmap A
  map_id c := by
    show rprodMap (𝟙 (dE A)) (list (𝟙 (dE c.carrier)))
        = 𝟙 (⟨A × ConsList Unit c.carrier⟩ : RelSet.{0})
    rw [list_id, rprodMap_id]
  map_comp {c c' c''} R S := by
    show rprodMap (𝟙 (dE A)) (list (A := c.carrier) (B := c''.carrier) (R ≫ S))
        = rprodMap (𝟙 (dE A)) (list (A := c.carrier) (B := c'.carrier) R)
          ≫ rprodMap (𝟙 (dE A)) (list (A := c'.carrier) (B := c''.carrier) S)
    rw [rprodMap_comp, Cat.id_comp, list_comp]
  map_mono {c c'} {R S} h :=
    le_iff.mpr fun p q hpq => ⟨hpq.1, listP_mono (le_iff.mp h) _ _ hpq.2⟩

/-- `F` preserves converse: `F(R°) = F(R)°` — componentwise, `𝟙° = 𝟙` and `list(R°) = list(R)°`. -/
public theorem F_preservesRecip (A : Type) : (F A).PreservesRecip := by
  intro c c' R
  show rprodMap (𝟙 (dE A)) (list (A := c'.carrier) (B := c.carrier) R°)
      = (rprodMap (𝟙 (dE A)) (list (A := c.carrier) (B := c'.carrier) R))°
  rw [list_recip, rprodMap_recip, recip_id]

/-! ## `tree A` is the initial algebra of `F` -/

/-- The constructor map `node : F (tree A) → tree A`. -/
@[expose] public def con : (Fobj A (dRose A)).carrier → Rose A := fun p => Rose.node p.1 p.2

mutual
  /-- The structural fold, defined DIRECTLY from the algebra-relation `f` (no choice). -/
  @[expose] public def cataFold {c : RelSet.{0}} (f : Fobj A c ⟶ c) : Rose A → c.carrier → Prop
    | Rose.node a ts => fun r => ∃ rs, cataFoldList f ts rs ∧ f (a, rs) r
  /-- `list(cataFold f)`, unrolled so the nested recursion is structural. -/
  @[expose] public def cataFoldList {c : RelSet.{0}} (f : Fobj A c ⟶ c) :
      ConsList Unit (Rose A) → ConsList Unit c.carrier → Prop
    | ConsList.wrap _ => fun rs => rs = ConsList.wrap ()
    | ConsList.cons t ts => fun rs =>
        ∃ r' rs', cataFold f t r' ∧ cataFoldList f ts rs' ∧ rs = ConsList.cons r' rs'
end

/-- The unrolled list fold IS `list(cataFold f)`. -/
public theorem cataFoldList_eq_listP {c : RelSet.{0}} (f : Fobj A c ⟶ c) :
    ∀ (ts : ConsList Unit (Rose A)) (rs : ConsList Unit c.carrier),
      cataFoldList f ts rs ↔ listP (cataFold f) ts rs
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨(fun h => nomatch h), False.elim⟩
  | ConsList.cons t ts, ConsList.wrap _ =>
      ⟨(fun ⟨_, _, _, _, h⟩ => nomatch h), False.elim⟩
  | ConsList.cons t ts, ConsList.cons r0 rs0 => by
      constructor
      · rintro ⟨r', rs', h1, h2, heq⟩
        obtain ⟨rfl, rfl⟩ : r0 = r' ∧ rs0 = rs' :=
          ⟨(ConsList.cons.inj heq).1, (ConsList.cons.inj heq).2⟩
        exact ⟨h1, (cataFoldList_eq_listP f ts rs0).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨r0, rs0, h1, (cataFoldList_eq_listP f ts rs0).mpr h2, rfl⟩

/-- The fold at a node, with the list fold already spelled `list(cataFold f)`. -/
public theorem cataFold_node {c : RelSet.{0}} (f : Fobj A c ⟶ c) (a : A)
    (ts : ConsList Unit (Rose A)) (r : c.carrier) :
    cataFold f (Rose.node a ts) r ↔ ∃ rs, listP (cataFold f) ts rs ∧ f (a, rs) r := by
  constructor
  · rintro ⟨rs, h1, h2⟩; exact ⟨rs, (cataFoldList_eq_listP f ts rs).mp h1, h2⟩
  · rintro ⟨rs, h1, h2⟩; exact ⟨rs, (cataFoldList_eq_listP f ts rs).mpr h1, h2⟩

mutual
  public theorem cataFold_total {c : RelSet.{0}} (f : Fobj A c ⟶ c) (hf : Map f) :
      ∀ t : Rose A, ∃ r, cataFold f t r
    | Rose.node a ts => by
        obtain ⟨rs, hrs⟩ := cataFoldList_total f hf ts
        obtain ⟨r, hr⟩ := entire_total hf.1 (a, rs)
        exact ⟨r, rs, hrs, hr⟩
  public theorem cataFoldList_total {c : RelSet.{0}} (f : Fobj A c ⟶ c) (hf : Map f) :
      ∀ ts : ConsList Unit (Rose A), ∃ rs, cataFoldList f ts rs
    | ConsList.wrap _ => ⟨ConsList.wrap (), rfl⟩
    | ConsList.cons t ts => by
        obtain ⟨r, hr⟩ := cataFold_total f hf t
        obtain ⟨rs, hrs⟩ := cataFoldList_total f hf ts
        exact ⟨ConsList.cons r rs, r, rs, hr, hrs, rfl⟩
end

mutual
  public theorem cataFold_functional {c : RelSet.{0}} (f : Fobj A c ⟶ c) (hf : Map f) :
      ∀ (t : Rose A) (r r' : c.carrier), cataFold f t r → cataFold f t r' → r = r'
    | Rose.node a ts, r, r', ⟨rs, hrs, hfr⟩, ⟨rs', hrs', hfr'⟩ => by
        obtain rfl : rs = rs' := cataFoldList_functional f hf ts rs rs' hrs hrs'
        exact simple_uniq hf.2 hfr hfr'
  public theorem cataFoldList_functional {c : RelSet.{0}} (f : Fobj A c ⟶ c) (hf : Map f) :
      ∀ (ts : ConsList Unit (Rose A)) (rs rs' : ConsList Unit c.carrier),
        cataFoldList f ts rs → cataFoldList f ts rs' → rs = rs'
    | ConsList.wrap _, _, _, h, h' => h.trans h'.symm
    | ConsList.cons t ts, _, _, ⟨r1, rs1, hr1, hrs1, rfl⟩, ⟨r2, rs2, hr2, hrs2, rfl⟩ => by
        obtain rfl : r1 = r2 := cataFold_functional f hf t r1 r2 hr1 hr2
        obtain rfl : rs1 = rs2 := cataFoldList_functional f hf ts rs1 rs2 hrs1 hrs2
        rfl
end

public theorem cataFold_map {c : RelSet.{0}} (f : Fobj A c ⟶ c) (hf : Map f) :
    Map (a := dRose A) (b := c) (cataFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataFold f) = 𝟙 (dRose A)
    apply hom_ext; intro t t'
    refine ⟨fun h => h.1, fun (h : t = t') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataFold_total f hf t
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨t, h1, h2⟩ := h
    exact cataFold_functional f hf t r r' h1 h2

/-- The catamorphism computation rule holds for ANY algebra-relation `φ` (not just maps):
    `α ≫ cataFold φ = F(cataFold φ) ≫ φ`.  (The structural proof never uses `Map φ`.) -/
public theorem cataFold_comm {c : RelSet.{0}} (φ : Fobj A c ⟶ c) :
    graph con ≫ cataFold φ = Fmap A (cataFold φ) ≫ φ := by
  apply hom_ext; intro u r
  constructor
  · rintro ⟨t, ht, hfold⟩
    have hfold' : cataFold φ (con u) r := (show t = con u from ht) ▸ hfold
    obtain ⟨rs, hrs, hφ⟩ :=
      (show ∃ rs, cataFoldList φ u.2 rs ∧ φ (u.1, rs) r from hfold')
    exact ⟨(u.1, rs), ⟨rfl, (cataFoldList_eq_listP φ u.2 rs).mp hrs⟩, hφ⟩
  · rintro ⟨v, ⟨hv1, hv2⟩, hφ⟩
    exact ⟨con u, rfl, v.2, (cataFoldList_eq_listP φ u.2 v.2).mpr hv2,
      (show u.1 = v.1 from hv1) ▸ hφ⟩

mutual
  public theorem cataFold_unique_tree {c : RelSet.{0}} (f : Fobj A c ⟶ c) (h : dRose A ⟶ c)
      (hcomm : graph con ≫ h = Fmap A h ≫ f) :
      ∀ (t : Rose A) (r : c.carrier), h t r ↔ cataFold f t r
    | Rose.node a ts, r => by
      have key : (graph con ≫ h) (a, ts) r = (Fmap A h ≫ f) (a, ts) r := by rw [hcomm]
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (a, ts) r := ⟨Rose.node a ts, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, ⟨hv1, hv2⟩, hfv⟩ := hlhs
        exact ⟨v.2, (cataFoldList_eq_listP f ts v.2).mpr
          ((cataFold_unique_list f h hcomm ts v.2).mp hv2),
          (show a = v.1 from hv1) ▸ hfv⟩
      · rintro ⟨rs, hrs, hfr⟩
        have hrhs : (Fmap A h ≫ f) (a, ts) r :=
          ⟨(a, rs), ⟨rfl, (cataFold_unique_list f h hcomm ts rs).mpr
            ((cataFoldList_eq_listP f ts rs).mp hrs)⟩, hfr⟩
        rw [← key] at hrhs
        obtain ⟨t', ht', hh⟩ := hrhs
        have hh' : h (con (a, ts)) r := (show t' = con (a, ts) from ht') ▸ hh
        exact hh'
  public theorem cataFold_unique_list {c : RelSet.{0}} (f : Fobj A c ⟶ c) (h : dRose A ⟶ c)
      (hcomm : graph con ≫ h = Fmap A h ≫ f) :
      ∀ (ts : ConsList Unit (Rose A)) (rs : ConsList Unit c.carrier),
        listP h ts rs ↔ listP (cataFold f) ts rs
    | ConsList.wrap _, ConsList.wrap _ => Iff.rfl
    | ConsList.wrap _, ConsList.cons _ _ => Iff.rfl
    | ConsList.cons _ _, ConsList.wrap _ => Iff.rfl
    | ConsList.cons t ts, ConsList.cons r rs => by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(cataFold_unique_tree f h hcomm t r).mp h1,
            (cataFold_unique_list f h hcomm ts rs).mp h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(cataFold_unique_tree f h hcomm t r).mpr h1,
            (cataFold_unique_list f h hcomm ts rs).mpr h2⟩
end

/-- The initial `F`-algebra structure on `tree A`. -/
@[expose, instance] public def initial (A : Type) : InitialAlgebra (F A) where
  t := dRose A
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := cataFold_comm f
  cata_unique f hf h hmap hcomm :=
    hom_ext fun t r => cataFold_unique_tree f h hcomm t r

/-- The catamorphism (fold) of `φ` as a genuine morphism `tree A ⟶ c`. -/
@[expose] public def cataR {c : RelSet.{0}} (φ : Fobj A c ⟶ c) : dRose A ⟶ c := cataFold φ

/-- The structural fold IS the relational catamorphism (Eilenberg–Wright, via `cataFold_comm`
    and the universal property `relCata_UP`).  Lets the abstract catamorphism laws apply to
    `cataR`. -/
public theorem cataR_eq_relCata {c : RelSet.{0}} (φ : (F A).obj c ⟶ c) :
    cataR φ = relCata φ :=
  (relCata_UP (initial A) φ (cataR φ)).mp (cataFold_comm φ)

end Freyd.Alg.RelSet.RT
