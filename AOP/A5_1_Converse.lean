/-
  Bird & de Moor, *Algebra of Programming*, Theorem 5.1 (p. 112), the direction
  "converse-preserving ⟹ relator".

  The book states it for any tabular source and proves it by tabulating `R ⊑ S` as
  `h°k ⊑ f°g`, getting a map `m` with `h = mf`, `k = mg`, and then using that `F(m)` is simple.
  That step is not justified, and the statement is false for tabular sources in general: the
  second half of this file gives a converse-preserving functor out of a tabular allegory that is
  not monotone.

  For the source `Rel` (`RelSet`) the statement holds, and the first half proves it: every
  function `f` has `F(f)` entire (via the relation `𝟙 ∪ (Y×{∗}) : Y → Y+1`) and simple (via the
  gluing of two copies of `A` along the image of `f`), after which the book's tabulation argument
  goes through.
-/
module

public import AOP.A6_1_RelSet

universe u u₂ v₂

namespace Freyd.Alg

open RelSet

/-- An arrow with a right factor of the identity is entire: `𝟙 ⊑ PX ⟹ 𝟙 ⊑ PP°`, by the modular
    law `(P(X)) ∩ 𝟙 ⊑ P(X ∩ P°)`.  It never forms `∩` of images of a functor. -/
public theorem id_le_comp_recip_of_id_le_comp {𝒜 : Type u₂} [Allegory.{v₂} 𝒜] {A B : 𝒜}
    {P : A ⟶ B} {X : B ⟶ A} (h : 𝟙 A ⊑ P ≫ X) : 𝟙 A ⊑ P ≫ P° :=
  calc 𝟙 A ⊑ (P ≫ X) ∩ 𝟙 A := le_inter h (le_refl _)
    _ ⊑ P ≫ (X ∩ P° ≫ 𝟙 A) := modular_le_right P X (𝟙 A)
    _ ⊑ P ≫ P° := comp_mono_left P (by rw [Cat.comp_id]; exact inter_lb_right _ _)

section RelSource

variable {ℬ : Type u₂} [Allegory.{v₂} ℬ] (F : Freyd.Functor RelSet.{u} ℬ)
  (hc : ∀ {A B : RelSet.{u}} (R : A ⟶ B), F.map R° = (F.map R)°)
include hc

/-- A converse-preserving `F` out of `Rel` sends every function `f` to an ENTIRE arrow.
    First for `!_A : A → 1`: `R = 𝟙 ∪ (A×{∗}) : A → A+1` and `S = ι₁°` give `RS = 𝟙` and
    `RR° = !_A!_A°`, so `𝟙 ⊑ F(R)F(S)` makes `F(R)` entire and `F(R)F(R)° = F(!_A)F(!_A)°`.
    Then `f!_B = !_A` makes `𝟙 ⊑ F(f)(F(!_B)F(!_B)°F(f)°)`. -/
public theorem id_le_map_graph {A B : RelSet.{u}} (f : A.carrier → B.carrier) :
    𝟙 (F.obj A) ⊑ F.map (RelSet.graph f) ≫ (F.map (RelSet.graph f))° := by
  have hbang : ∀ A : RelSet.{u}, 𝟙 (F.obj A) ⊑
      F.map (RelSet.graph (B := ⟨PUnit⟩) fun (_ : A.carrier) => PUnit.unit) ≫
        (F.map (RelSet.graph (B := ⟨PUnit⟩) fun (_ : A.carrier) => PUnit.unit))° := by
    intro A
    let O : RelSet.{u} := ⟨Option A.carrier⟩
    let R : A ⟶ O := fun a z => z = some a ∨ z = none
    let S : O ⟶ A := fun z a => z = some a
    have hRS : R ≫ S = 𝟙 A := RelSet.hom_ext fun a b => by
      constructor
      · rintro ⟨z, hR, hS⟩
        subst hS
        rcases hR with h | h
        · exact (Option.some.inj h).symm
        · exact nomatch h
      · intro h; subst h; exact ⟨some a, Or.inl rfl, rfl⟩
    have hRR : R ≫ R° = RelSet.graph (B := ⟨PUnit⟩) (fun (_ : A.carrier) => PUnit.unit) ≫
        (RelSet.graph (B := ⟨PUnit⟩) fun (_ : A.carrier) => PUnit.unit)° :=
      RelSet.hom_ext fun _ _ => ⟨fun _ => ⟨PUnit.unit, rfl, rfl⟩, fun _ => ⟨none, Or.inr rfl, Or.inr rfl⟩⟩
    have h1 : 𝟙 (F.obj A) ⊑ F.map R ≫ F.map S := by
      rw [← F.map_comp, hRS, F.map_id]; exact le_refl _
    have h2 := id_le_comp_recip_of_id_le_comp h1
    rwa [← hc, ← F.map_comp, hRR, F.map_comp, hc] at h2
  have e : RelSet.graph f ≫ RelSet.graph (B := ⟨PUnit⟩) (fun (_ : B.carrier) => PUnit.unit) =
      RelSet.graph (B := ⟨PUnit⟩) fun (_ : A.carrier) => PUnit.unit := RelSet.graph_comp _ _
  have h := hbang A
  rw [← e, F.map_comp, Allegory.recip_comp] at h
  exact id_le_comp_recip_of_id_le_comp (by simpa only [Cat.assoc] using h)

/-- A converse-preserving `F` out of `Rel` sends every function `i : X → A` to a SIMPLE arrow.
    Glue two copies of `A` along the image of `i`: `Y = A × Prop` with `g(a) = (a, True)`,
    `h(a) = (a, a ∈ im i)` and `k = fst`.  Then `gh° = i°i` and `gk = 𝟙 = hk`, so
    `F(i)°F(i) = F(g)F(h)° ⊑ F(g)F(k)F(k)°F(h)° = 𝟙`, using `F(k)` entire. -/
public theorem simple_map_graph {X A : RelSet.{u}} (i : X.carrier → A.carrier) :
    Simple (F.map (RelSet.graph i)) := by
  let Y : RelSet.{u} := ⟨A.carrier × Prop⟩
  let g : A ⟶ Y := RelSet.graph fun a => (a, True)
  let h : A ⟶ Y := RelSet.graph fun a => (a, ∃ x, i x = a)
  let k : Y ⟶ A := RelSet.graph Prod.fst
  have hgk : g ≫ k = 𝟙 A := (RelSet.graph_comp _ _).trans (RelSet.hom_ext fun _ _ => ⟨Eq.symm, Eq.symm⟩)
  have hhk : h ≫ k = 𝟙 A := (RelSet.graph_comp _ _).trans (RelSet.hom_ext fun _ _ => ⟨Eq.symm, Eq.symm⟩)
  have hgh : g ≫ h° = (RelSet.graph i)° ≫ RelSet.graph i := RelSet.hom_ext fun a b => by
    constructor
    · rintro ⟨y, hy, hy'⟩
      have e := Prod.ext_iff.mp (hy.symm.trans hy')
      obtain ⟨x, hx⟩ : ∃ x, i x = b := cast e.2 trivial
      exact ⟨x, e.1.trans hx.symm, hx.symm⟩
    · rintro ⟨x, ha, hb⟩
      subst ha; subst hb
      exact ⟨_, rfl, Prod.ext_iff.mpr ⟨rfl, propext ⟨fun _ => ⟨x, rfl⟩, fun _ => trivial⟩⟩⟩
  show (F.map (RelSet.graph i))° ≫ F.map (RelSet.graph i) ⊑ 𝟙 (F.obj A)
  calc (F.map (RelSet.graph i))° ≫ F.map (RelSet.graph i) = F.map (g ≫ h°) := by
        rw [hgh, F.map_comp, hc]
    _ = F.map g ≫ 𝟙 (F.obj Y) ≫ (F.map h)° := by rw [F.map_comp, hc, Cat.id_comp]
    _ ⊑ F.map g ≫ (F.map k ≫ (F.map k)°) ≫ (F.map h)° :=
        comp_mono_left _ (comp_mono_right (id_le_map_graph F hc Prod.fst) _)
    _ = (F.map g ≫ F.map k) ≫ (F.map h ≫ F.map k)° := by
        rw [Allegory.recip_comp]; simp only [Cat.assoc]
    _ = 𝟙 (F.obj A) := by
        rw [← F.map_comp, ← F.map_comp, hgk, hhk, F.map_id, recip_id, Cat.id_comp]

/-- **Theorem 5.1** (p.112), converse ⟹ relator, for source Rel: a functor out of `Rel` that
    preserves converse is monotone.  Tabulate `S = f°g` over `{(a,b) ∣ S(a,b)}`; `R ⊑ S` makes the
    inclusion `m` of `{(a,b) ∣ R(a,b)}` a function with `R = (mf)°(mg)`, so
    `F(R) = F(f)°F(m)°F(m)F(g) ⊑ F(f)°F(g) = F(S)` since `F(m)` is simple. -/
public theorem map_mono_of_preservesRecip_relSet {A B : RelSet.{u}} {R S : A ⟶ B} (hRS : R ⊑ S) :
    F.map R ⊑ F.map S := by
  have hle := RelSet.le_iff.mp hRS
  let P : RelSet.{u} := ⟨{ p : A.carrier × B.carrier // R p.1 p.2 }⟩
  let Q : RelSet.{u} := ⟨{ p : A.carrier × B.carrier // S p.1 p.2 }⟩
  let f : Q ⟶ A := RelSet.graph fun q => q.1.1
  let g : Q ⟶ B := RelSet.graph fun q => q.1.2
  let m : P.carrier → Q.carrier := fun p => ⟨p.1, hle _ _ p.2⟩
  have hS : S = f° ≫ g := RelSet.hom_ext fun a b =>
    ⟨fun hs => ⟨⟨(a, b), hs⟩, rfl, rfl⟩, fun ⟨q, ha, hb⟩ => by subst ha; subst hb; exact q.2⟩
  have hR : R = (RelSet.graph m ≫ f)° ≫ (RelSet.graph m ≫ g) := by
    rw [RelSet.graph_comp, RelSet.graph_comp]
    exact RelSet.hom_ext fun a b =>
      ⟨fun hr => ⟨⟨(a, b), hr⟩, rfl, rfl⟩, fun ⟨p, ha, hb⟩ => by subst ha; subst hb; exact p.2⟩
  have e1 : F.map R = (F.map f)° ≫ ((F.map (RelSet.graph m))° ≫ F.map (RelSet.graph m)) ≫ F.map g := by
    rw [hR, F.map_comp, hc, F.map_comp, F.map_comp, Allegory.recip_comp]; simp only [Cat.assoc]
  have e2 : F.map S = (F.map f)° ≫ F.map g := by rw [hS, F.map_comp, hc]
  rw [e1, e2]
  calc (F.map f)° ≫ ((F.map (RelSet.graph m))° ≫ F.map (RelSet.graph m)) ≫ F.map g
      ⊑ (F.map f)° ≫ 𝟙 (F.obj Q) ≫ F.map g :=
        comp_mono_left _ (comp_mono_right (simple_map_graph F hc m) _)
    _ = (F.map f)° ≫ F.map g := by rw [Cat.id_comp]

end RelSource

/-! ## Theorem 5.1 fails for tabular sources in general

  `RelTwo` is the full sub-allegory of `Rel` on `∅` and `1`: `𝟙` on `∅`, the empty `u : ∅ → 1`,
  its converse `u°`, and on `1` the two relations `0₁` (`false`) and `𝟙₁` (`true`).  It is
  tabular (`0₁ = u°u`).  Into `Rel` send `∅ ↦ 1`, `1 ↦ 2`, `u ↦ ⊤₁,₂`, `u° ↦ ⊤₂,₁`,
  `0₁ ↦ ⊤₂`, `𝟙₁ ↦ 𝟙₂`: a functor that preserves converse but not `0₁ ⊑ 𝟙₁`. -/

/-- The two objects `∅` and `1` of the counterexample. -/
public inductive RelTwo | empty | one

namespace RelTwo

/-- The relations between `∅` and `1`: a `Bool` on `1 → 1` (`true` = `𝟙₁`, `false` = `0₁`),
    the one empty relation everywhere else. -/
@[expose] public abbrev Hom : RelTwo → RelTwo → Type
  | .one, .one => Bool
  | .empty, .empty => Unit
  | .empty, .one => Unit
  | .one, .empty => Unit

@[expose] public def comp : {X Y Z : RelTwo} → Hom X Y → Hom Y Z → Hom X Z
  | .one, .one, .one, r, s => r && s
  | .one, .empty, .one, _, _ => false
  | .one, .one, .empty, _, _ => ()
  | .one, .empty, .empty, _, _ => ()
  | .empty, .one, .one, _, _ => ()
  | .empty, .empty, .one, _, _ => ()
  | .empty, .one, .empty, _, _ => ()
  | .empty, .empty, .empty, _, _ => ()

@[expose] public def id : (X : RelTwo) → Hom X X
  | .one => true
  | .empty => ()

@[expose] public def recip : {X Y : RelTwo} → Hom X Y → Hom Y X
  | .one, .one, r => r
  | .one, .empty, _ => ()
  | .empty, .one, _ => ()
  | .empty, .empty, _ => ()

@[expose] public def inter : {X Y : RelTwo} → Hom X Y → Hom X Y → Hom X Y
  | .one, .one, r, s => r && s
  | .one, .empty, _, _ => ()
  | .empty, .one, _, _ => ()
  | .empty, .empty, _, _ => ()

@[expose] public instance instCat : Cat RelTwo where
  Hom := Hom
  id := id
  comp := comp
  id_comp := by intro X Y R; cases X <;> cases Y <;> cases R <;> rfl
  comp_id := by intro X Y R; cases X <;> cases Y <;> cases R <;> rfl
  assoc := by
    intro W X Y Z R S T
    cases W <;> cases X <;> cases Y <;> cases Z <;> cases R <;> cases S <;> cases T <;> rfl

@[expose] public instance instAllegory : Allegory RelTwo where
  recip := recip
  inter := inter
  recip_recip := by intro X Y R; cases X <;> cases Y <;> cases R <;> rfl
  recip_comp := by
    intro X Y Z R S; cases X <;> cases Y <;> cases Z <;> cases R <;> cases S <;> rfl
  recip_inter := by intro X Y R S; cases X <;> cases Y <;> cases R <;> cases S <;> rfl
  inter_idem := by intro X Y R; cases X <;> cases Y <;> cases R <;> rfl
  inter_comm := by intro X Y R S; cases X <;> cases Y <;> cases R <;> cases S <;> rfl
  inter_assoc := by
    intro X Y R S T; cases X <;> cases Y <;> cases R <;> cases S <;> cases T <;> rfl
  semidistrib := by
    intro X Y Z R S T
    cases X <;> cases Y <;> cases Z <;> cases R <;> cases S <;> cases T <;> rfl
  modular := by
    intro X Y Z R S T
    cases X <;> cases Y <;> cases Z <;> cases R <;> cases S <;> cases T <;> rfl

/-- `RelTwo` is tabular: `𝟙₁` by `(𝟙₁, 𝟙₁)`, every other relation by `(u, u)`-shaped legs out of
    `∅`. -/
@[expose] public instance : TabularAllegory RelTwo :=
  { (inferInstance : Allegory RelTwo) with
    tabular := by
      intro X Y R
      have idMap : Map (𝟙 RelTwo.one) :=
        ⟨rfl, rfl⟩
      cases X <;> cases Y
      · exact ⟨.empty, (), (), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨.empty, (), (), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨.empty, (), (), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      · cases R
        · exact ⟨.empty, (), (), ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
        · exact ⟨.one, 𝟙 RelTwo.one, 𝟙 RelTwo.one, idMap, idMap, rfl, rfl⟩ }

/-- The functor of the counterexample: `∅ ↦ 1`, `1 ↦ 2`, `0₁ ↦ ⊤₂`, `𝟙₁ ↦ 𝟙₂`, and the full
    relation on every arrow touching `∅`. -/
@[expose] public def toRel : Freyd.Functor RelTwo RelSet.{0} where
  obj
    | .empty => ⟨Unit⟩
    | .one => ⟨Bool⟩
  map {X Y} R := match X, Y, R with
    | .one, .one, true => fun x y => x = y
    | .one, .one, false => fun _ _ => True
    | .empty, .empty, _ => fun x y => x = y
    | .empty, .one, _ => fun _ _ => True
    | .one, .empty, _ => fun _ _ => True
  map_id X := by cases X <;> rfl
  map_comp {X Y Z} R S := by
    cases X <;> cases Y <;> cases Z <;> cases R <;> cases S <;>
      exact RelSet.hom_ext fun x z => by simp [instCat, comp] <;> first | exact ⟨true, trivial⟩ | skip

end RelTwo

open RelTwo in
/-- **Theorem 5.1 fails for tabular sources in general: counterexample.**  `toRel` out of the
    tabular `RelTwo` into the tabular `Rel` preserves converse, yet `0₁ ⊑ 𝟙₁` while
    `F(0₁) = ⊤₂ ⋢ 𝟙₂ = F(𝟙₁)`. -/
public theorem thm5_1_fails_for_tabular :
    ¬ ∀ (𝒜 : Type) (ℬ : Type 1) [TabularAllegory.{0, 0} 𝒜] [TabularAllegory.{1, 0} ℬ]
      (F : Freyd.Functor 𝒜 ℬ), (∀ {A B : 𝒜} (R : A ⟶ B), F.map R° = (F.map R)°) →
      ∀ {A B : 𝒜} {R S : A ⟶ B}, R ⊑ S → F.map R ⊑ F.map S := by
  intro H
  have hc : ∀ {A B : RelTwo} (R : A ⟶ B), toRel.map R° = (toRel.map R)° := by
    intro A B R
    cases A <;> cases B <;> cases R <;> exact RelSet.hom_ext fun x y => by
      first
        | (simp [RelTwo.instAllegory, recip, toRel, eq_comm]; done)
        | (cases x; cases y; simp [RelTwo.instAllegory, recip, toRel])
  have h := H RelTwo RelSet.{0} toRel hc (A := .one) (B := .one) (R := false) (S := true) rfl
  exact nomatch (RelSet.le_iff.mp h true false trivial)

end Freyd.Alg
