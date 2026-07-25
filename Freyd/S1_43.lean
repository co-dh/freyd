/-
  Freyd & Scedrov, *Categories and Allegories* §1.43–§1.437
  Cartesian categories: equalizers, pullbacks, equivalences.

  Constructive proofs (adapted from mathlib).
-/


import Freyd.S1_10
import Freyd.S1_18
import Freyd.S1_28
import Freyd.S1_31
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_45


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## Equalizers -/

structure EqualizerCone {A B : 𝒞} (f g : A ⟶ B) where
  dom : 𝒞
  map : dom ⟶ A
  eq  : map ≫ f = map ≫ g

class HasEqualizer {A B : 𝒞} (f g : A ⟶ B) where
  cone : EqualizerCone f g
  lift : ∀ (c : EqualizerCone f g), c.dom ⟶ cone.dom
  fac  : ∀ (c : EqualizerCone f g), lift c ≫ cone.map = c.map
  uniq : ∀ (c : EqualizerCone f g) (m : c.dom ⟶ cone.dom), m ≫ cone.map = c.map → m = lift c

class HasEqualizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  eq (A B : 𝒞) (f g : A ⟶ B) : HasEqualizer f g

section EqualizerAPI
variable [HasEqualizers 𝒞]

def eqObj {A B : 𝒞} (f g : A ⟶ B) : 𝒞 := (HasEqualizers.eq A B f g).cone.dom
def eqMap {A B : 𝒞} (f g : A ⟶ B) : eqObj f g ⟶ A := (HasEqualizers.eq A B f g).cone.map
theorem eqMap_eq {A B : 𝒞} (f g : A ⟶ B) : eqMap f g ≫ f = eqMap f g ≫ g :=
  (HasEqualizers.eq A B f g).cone.eq

def eqLift {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) : X ⟶ eqObj f g :=
  (HasEqualizers.eq A B f g).lift ⟨X, k, h⟩

theorem eqLift_fac {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g) :
    eqLift f g k h ≫ eqMap f g = k := (HasEqualizers.eq A B f g).fac ⟨X, k, h⟩

theorem eqLift_uniq {A B X : 𝒞} (f g : A ⟶ B) (k : X ⟶ A) (h : k ≫ f = k ≫ g)
    (m : X ⟶ eqObj f g) (hm : m ≫ eqMap f g = k) : m = eqLift f g k h :=
  (HasEqualizers.eq A B f g).uniq ⟨X, k, h⟩ m hm
end EqualizerAPI

/-! ## Cartesian category (§1.43) -/

class CartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasEqualizers 𝒞

/-! ## §1.432 Products + equalizers → pullbacks -/

section PB_from_ProdEq
variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [heq : HasEqualizers 𝒞]

def products_equalizers_implies_pullbacks {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) : HasPullback f g :=
  let pbObj := eqObj (fst ≫ f) (snd ≫ g)
  let pbMap : pbObj ⟶ prod A B := eqMap (fst ≫ f) (snd ≫ g)
  have h_sq : (pbMap ≫ fst) ≫ f = (pbMap ≫ snd) ≫ g :=
    calc
      (pbMap ≫ fst) ≫ f = pbMap ≫ (fst ≫ f) := by rw [Cat.assoc]
      _ = pbMap ≫ (snd ≫ g) := eqMap_eq (fst ≫ f) (snd ≫ g)
      _ = (pbMap ≫ snd) ≫ g := by rw [Cat.assoc]
  let pullCone : Cone f g := { pt := pbObj, π₁ := pbMap ≫ fst, π₂ := pbMap ≫ snd, w := h_sq }
  have mk_h_cond : ∀ (c : Cone f g), pair c.π₁ c.π₂ ≫ (fst ≫ f) = pair c.π₁ c.π₂ ≫ (snd ≫ g) := by
    intro c
    calc
      pair c.π₁ c.π₂ ≫ (fst ≫ f) = (pair c.π₁ c.π₂ ≫ fst) ≫ f := by rw [Cat.assoc]
      _ = c.π₁ ≫ f := by rw [fst_pair]
      _ = c.π₂ ≫ g := by rw [c.w]
      _ = (pair c.π₁ c.π₂ ≫ snd) ≫ g := by rw [snd_pair]
      _ = pair c.π₁ c.π₂ ≫ (snd ≫ g) := by rw [Cat.assoc]
  { cone := pullCone
    lift := λ c => eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c)
    lift_fst := λ c => by
      dsimp [pullCone, pbMap]
      calc
        eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g) ≫ fst
            = (eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g)) ≫ fst := by rw [Cat.assoc]
        _ = pair c.π₁ c.π₂ ≫ fst := by rw [eqLift_fac]
        _ = c.π₁ := fst_pair _ _
    lift_snd := λ c => by
      dsimp [pullCone, pbMap]
      calc
        eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g) ≫ snd
            = (eqLift (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) ≫ eqMap (fst ≫ f) (snd ≫ g)) ≫ snd := by rw [Cat.assoc]
        _ = pair c.π₁ c.π₂ ≫ snd := by rw [eqLift_fac]
        _ = c.π₂ := snd_pair _ _
    lift_uniq := λ c u hu₁ hu₂ => by
      dsimp [pullCone] at hu₁ hu₂ ⊢
      apply eqLift_uniq (fst ≫ f) (snd ≫ g) (pair c.π₁ c.π₂) (mk_h_cond c) u
      apply pair_uniq c.π₁ c.π₂ (u ≫ pbMap)
      · rw [Cat.assoc, hu₁]
      · rw [Cat.assoc, hu₂] }
end PB_from_ProdEq

/-! ## §1.433 Pullbacks + terminator → binary products -/

section Prod_from_PB_Term
variable [ht : HasTerminal 𝒞] [hpull : HasPullbacks 𝒞]

def pullbacks_terminator_implies_products : HasBinaryProducts 𝒞 where
  prod A B := (hpull.has (term A) (term B)).cone.pt
  fst := λ {A B} => (hpull.has (term A) (term B)).cone.π₁
  snd := λ {A B} => (hpull.has (term A) (term B)).cone.π₂
  pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  fst_pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift_fst
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  snd_pair := λ {X A B} f g => (hpull.has (term A) (term B)).lift_snd
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) }
  pair_uniq := λ {X A B} f g h h₁ h₂ => (hpull.has (term A) (term B)).lift_uniq
    { pt := X, π₁ := f, π₂ := g, w := term_uniq (f ≫ term A) (g ≫ term B) } h h₁ h₂
end Prod_from_PB_Term

/-! ## §1.434 Products + pullbacks → equalizers -/

section Eq_from_ProdPB
variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

def products_pullbacks_implies_equalizers : HasEqualizers 𝒞 where
  eq A B f g :=
    let u : A ⟶ prod A B := pair (Cat.id A) f
    let v : A ⟶ prod A B := pair (Cat.id A) g
    let pb := hpull.has u v
    have h_pb_sq : pb.cone.π₁ ≫ u = pb.cone.π₂ ≫ v := pb.cone.w
    have h_fst_eq : pb.cone.π₁ = pb.cone.π₂ := by
      have h1 : pb.cone.π₁ ≫ Cat.id A = pb.cone.π₂ ≫ Cat.id A := by
        calc
          pb.cone.π₁ ≫ Cat.id A = pb.cone.π₁ ≫ (u ≫ fst) := by rw [fst_pair, Cat.comp_id]
          _ = (pb.cone.π₁ ≫ u) ≫ fst := by rw [Cat.assoc]
          _ = (pb.cone.π₂ ≫ v) ≫ fst := by rw [h_pb_sq]
          _ = pb.cone.π₂ ≫ (v ≫ fst) := by rw [Cat.assoc]
          _ = pb.cone.π₂ ≫ Cat.id A := by rw [fst_pair, Cat.comp_id]
      exact (by
        simpa [Cat.comp_id] using h1)
    have h_eq_cond : pb.cone.π₁ ≫ f = pb.cone.π₁ ≫ g := by
      calc
        pb.cone.π₁ ≫ f = pb.cone.π₁ ≫ (u ≫ snd) := by rw [snd_pair]
        _ = (pb.cone.π₁ ≫ u) ≫ snd := by rw [Cat.assoc]
        _ = (pb.cone.π₂ ≫ v) ≫ snd := by rw [h_pb_sq]
        _ = pb.cone.π₂ ≫ (v ≫ snd) := by rw [Cat.assoc]
        _ = pb.cone.π₂ ≫ g := by rw [snd_pair]
        _ = pb.cone.π₁ ≫ g := by rw [h_fst_eq]
    have mk_hcone_w : ∀ (c : EqualizerCone f g), c.map ≫ u = c.map ≫ v := by
      intro c
      calc
        c.map ≫ u = pair c.map (c.map ≫ f) :=
          pair_uniq c.map (c.map ≫ f) (c.map ≫ u)
            (by rw [Cat.assoc, fst_pair, Cat.comp_id])
            (by rw [Cat.assoc, snd_pair])
        _ = pair c.map (c.map ≫ g) := by rw [c.eq]
        _ = c.map ≫ v :=
          (pair_uniq c.map (c.map ≫ g) (c.map ≫ v)
            (by rw [Cat.assoc, fst_pair, Cat.comp_id])
            (by rw [Cat.assoc, snd_pair])).symm
    { cone := { dom := pb.cone.pt, map := pb.cone.π₁, eq := h_eq_cond }
      lift := λ c =>
        pb.lift { pt := c.dom, π₁ := c.map, π₂ := c.map, w := mk_hcone_w c }
      fac := λ c => pb.lift_fst _
      uniq := λ c m hm => by
        have hm₂ : m ≫ pb.cone.π₂ = c.map := by
          calc
            m ≫ pb.cone.π₂ = m ≫ pb.cone.π₁ := by
              dsimp [pb]; rw [h_fst_eq]
            _ = c.map := hm
        exact pb.lift_uniq { pt := c.dom, π₁ := c.map, π₂ := c.map, w := mk_hcone_w c } m hm hm₂ }
end Eq_from_ProdPB

/-! ## §1.435 Pullbacks + terminator → Cartesian -/

section Cartesian_from_PB_Term
variable [ht : HasTerminal 𝒞] [hpull : HasPullbacks 𝒞]

def pullbacks_terminator_implies_cartesian : CartesianCategory 𝒞 :=
  letI hp : HasBinaryProducts 𝒞 := pullbacks_terminator_implies_products
  letI heq : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  { toHasTerminal := ht
    toHasBinaryProducts := hp
    toHasEqualizers := heq }
end Cartesian_from_PB_Term

/-! ## §1.439 Terminal + Pullbacks ↔ Cartesian

  The diagram (Freyd & Scedrov, §1.439):

  ```
              §1.432
  Cartesian -----------> HasPullbacks
     ^                      |
     |                      | §1.433 (pb → prod)
     |                      v
     └── §1.434 ── (HasTerm, HasProd, HasPullbacks)
       (prod+pb → eq)
  ```

  Given a terminal object, binary products + equalizers together are
  equivalent to pullbacks.  Hence `Cartesian` ⇔ `HasTerminal + HasPullbacks`. -/

section S1_439
variable [HasTerminal 𝒞]

/-- **§1.439**: In a category with a terminal object,
    `HasBinaryProducts 𝒞 ∧ HasEqualizers 𝒞 ↔ HasPullbacks 𝒞`.

    → (§1.432): Given products and equalizers, construct the pullback of
      `f` and `g` as the equalizer of `fst≫f` and `snd≫g` on `A×B`.

    ← (§1.433 + §1.434): Given pullbacks, build products as the pullback
      of `A→1` and `B→1`; then build the equalizer of `f,g` as the
      pullback of `⟨id,f⟩` and `⟨id,g⟩` over `A×B`. -/
theorem cartesian_iff_pullbacks :
    (Nonempty (HasBinaryProducts 𝒞) ∧ Nonempty (HasEqualizers 𝒞)) ↔ Nonempty (HasPullbacks 𝒞) := by
  constructor
  · -- (§1.432): Prod + Eq → Pullbacks
    rintro ⟨⟨hp⟩, ⟨heq⟩⟩
    haveI := hp; haveI := heq
    refine ⟨⟨λ {A B C} f g => products_equalizers_implies_pullbacks f g⟩⟩
  · -- (§1.433 + §1.434): Pullbacks → Prod, then Prod + Pullbacks → Eq
    intro ⟨hpull⟩
    haveI := hpull
    have hp : HasBinaryProducts 𝒞 := pullbacks_terminator_implies_products
    have heq : HasEqualizers 𝒞 :=
      haveI := hp
      products_pullbacks_implies_equalizers
    exact ⟨⟨hp⟩, ⟨heq⟩⟩

/-- **§1.439** bundled: `Cartesian 𝒞 ↔ HasPullbacks 𝒞` given a terminator.  Also the §1.825
    record of the same equivalence. -/
theorem cartesianCategory_iff_pullbacks :
    Nonempty (CartesianCategory 𝒞) ↔ Nonempty (HasPullbacks 𝒞) := by
  constructor
  · intro ⟨h⟩
    haveI : HasBinaryProducts 𝒞 := h.toHasBinaryProducts
    haveI : HasEqualizers 𝒞 := h.toHasEqualizers
    have hpb : HasPullbacks 𝒞 :=
      { has := λ f g => products_equalizers_implies_pullbacks f g }
    exact ⟨hpb⟩
  · intro ⟨h⟩
    haveI := h
    exact ⟨pullbacks_terminator_implies_cartesian⟩

end S1_439

/-! ## §1.425 Finite (n-ary) products

  Given an indexed family `{Aᵢ}_{i ∈ Fin n}` of objects, a PRODUCT is an
  object `P` with projections `πᵢ : P → Aᵢ` universal for all cones.  The
  empty product (n = 0) is a terminator.  Non-empty finite products are built
  by iterating binary products (§1.425).
  Note: use `Nat` not `ℕ` since `ℕ` is a single-char auto-implicit under
  `relaxedAutoImplicit = false`. -/

/-- ℬ has all FINITE products (§1.425): every `Fin n`-indexed family has a product.
    The single per-family witness is the §1.42 `HasIndexedProduct`; the former cone-packaged
    copies `FinProdCone`/`HasFinProd` were a redundant repackaging (DRY) and were deleted in
    favour of `HasIndexedProduct` (`Fin n : Type`, so no universe change is needed). -/
class HasFiniteProducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  fin_prod : ∀ {n : Nat} (A : Fin n → 𝒞), HasIndexedProduct A

section FinProdAPI
variable [hfp : HasFiniteProducts 𝒞]

def finProdObj {n : Nat} (A : Fin n → 𝒞) : 𝒞 := (hfp.fin_prod A).prod
def finProdπ   {n : Nat} (A : Fin n → 𝒞) (i : Fin n) : finProdObj A ⟶ A i :=
  (hfp.fin_prod A).proj i

def finProdLift {n : Nat} (A : Fin n → 𝒞) {X : 𝒞} (f : (i : Fin n) → X ⟶ A i) :
    X ⟶ finProdObj A :=
  (hfp.fin_prod A).lift f

theorem finProdLift_uniq {n : Nat} (A : Fin n → 𝒞) {X : 𝒞} (f : (i : Fin n) → X ⟶ A i)
    (m : X ⟶ finProdObj A) (hm : ∀ i, m ≫ finProdπ A i = f i) : m = finProdLift A f :=
  (hfp.fin_prod A).lift_uniq f m hm

end FinProdAPI

section FinProd_equiv

-- Helper: 2-object family from two objects (avoids Matrix/Fin.cons)
private def fin2 (A B : 𝒞) : Fin 2 → 𝒞 := Fin.cases A (Fin.cases B (fun i => i.elim0))

/-- **§1.425** (→): `HasFiniteProducts` gives a terminator (empty product). -/
def finiteProducts_implies_terminal (hfp : HasFiniteProducts 𝒞) : HasTerminal 𝒞 where
  one  := (hfp.fin_prod (n := 0) Fin.elim0).prod
  trm  := fun X => (hfp.fin_prod (n := 0) Fin.elim0).lift (fun i => i.elim0)
  uniq := fun {X} f g => by
    have hf := (hfp.fin_prod (n := 0) Fin.elim0).lift_uniq (fun i => i.elim0) f
                (fun i => i.elim0)
    have hg := (hfp.fin_prod (n := 0) Fin.elim0).lift_uniq (fun i => i.elim0) g
                (fun i => i.elim0)
    rw [hf, hg]

/-- **§1.425** (→): `HasFiniteProducts` gives binary products. -/
def finiteProducts_implies_binary (hfp : HasFiniteProducts 𝒞) : HasBinaryProducts 𝒞 where
  prod  := fun A B => (hfp.fin_prod (n := 2) (fin2 A B)).prod
  fst   := fun {A B} => (hfp.fin_prod (fin2 A B)).proj 0
  snd   := fun {A B} => (hfp.fin_prod (fin2 A B)).proj 1
  pair  := fun {_ A B} f g =>
    (hfp.fin_prod (fin2 A B)).lift (Fin.cases f (Fin.cases g (fun i => i.elim0)))
  fst_pair := fun {_ A B} f g =>
    (hfp.fin_prod (fin2 A B)).lift_π (Fin.cases f (Fin.cases g (fun i => i.elim0))) 0
  snd_pair := fun {_ A B} f g =>
    (hfp.fin_prod (fin2 A B)).lift_π (Fin.cases f (Fin.cases g (fun i => i.elim0))) 1
  pair_uniq := fun {_ A B} f g h h₁ h₂ =>
    (hfp.fin_prod (fin2 A B)).lift_uniq (Fin.cases f (Fin.cases g (fun i => i.elim0))) h
      (fun i => Fin.cases h₁ (fun j => Fin.cases h₂ (fun k => k.elim0) j) i)

/-- **§1.425** (←): Terminal + binary products give all finite products.  Each `Fin n`-family's
    product is the §1.42 `HasIndexedProduct` built directly by `finiteProduct_from_term_binary`
    (no cone-repackaging step — `HasFinProd`/`toHasFinProd` were removed as DRY duplicates). -/
def terminal_binary_implies_finiteProducts [HasTerminal 𝒞] [HasBinaryProducts 𝒞] :
    HasFiniteProducts 𝒞 where
  fin_prod A := finiteProduct_from_term_binary A

/-- **§1.425**: finite products ↔ terminator + binary products. -/
theorem finiteProducts_iff :
    Nonempty (HasFiniteProducts 𝒞) ↔ Nonempty (HasTerminal 𝒞) ∧ Nonempty (HasBinaryProducts 𝒞) := by
  constructor
  · intro ⟨hfp⟩
    exact ⟨⟨finiteProducts_implies_terminal hfp⟩, ⟨finiteProducts_implies_binary hfp⟩⟩
  · intro ⟨⟨ht⟩, ⟨hp⟩⟩
    haveI := ht; haveI := hp
    exact ⟨terminal_binary_implies_finiteProducts⟩

end FinProd_equiv

/-! ## §1.429 Equalizers split idempotents

  If a category has equalizers, then every idempotent `e : A → A` splits:
  the equalizer of `e` and `1_A` gives the splitting.  §1.28/§1.281 live in `S1_28`. -/

section S1_429
variable [HasEqualizers 𝒞]

/-- **§1.429**: In a category with equalizers, every idempotent splits.

  PROOF (Freyd §1.429): Given `e : A → A`, `e² = e`, let `y : B → A` be the
  equalizer of `e` and `id_A`.  Define `x : A → B` as the unique map with
  `x ≫ y = e` (exists since `e ≫ e = e ≫ id_A`).  Then
  `(y ≫ x) ≫ y = y ≫ (x ≫ y) = y ≫ e = y ≫ id_A = y`,
  so `y ≫ x = id_B` by equalizer uniqueness (canceling `y` on the right). -/
theorem equalizers_split_idempotents {A : 𝒞} (e : A ⟶ A) (he : Idempotent e) :
    SplitIdempotent e := by
  -- Equalizer y : B → A of e and id_A
  let B := eqObj e (Cat.id A)
  let y := eqMap e (Cat.id A)
  have hy : y ≫ e = y ≫ Cat.id A := eqMap_eq e (Cat.id A)
  -- x : A → B, the unique lift of e through y (uses e ≫ e = e ≫ id_A)
  have hee : e ≫ e = e ≫ Cat.id A := by rw [Cat.comp_id]; exact he
  let x := eqLift e (Cat.id A) e hee
  have hxy : x ≫ y = e := eqLift_fac e (Cat.id A) e hee
  -- y ≫ x = id_B: both (y≫x) and id_B satisfy `? ≫ y = y`
  have hyx_fac : (y ≫ x) ≫ y = y := by
    rw [Cat.assoc, hxy]; exact hy.trans (Cat.comp_id _)
  have hid_fac : Cat.id B ≫ y = y := Cat.id_comp _
  have hyx : y ≫ x = Cat.id B := by
    have h1 : y ≫ x = eqLift e (Cat.id A) y hy := eqLift_uniq _ _ _ hy _ hyx_fac
    have h2 : Cat.id B = eqLift e (Cat.id A) y hy := eqLift_uniq _ _ _ hy _ hid_fac
    rw [h1, ← h2]
  exact ⟨B, x, y, hxy, hyx⟩

end S1_429

/-! ## §1.437 Representation of Cartesian categories

  A REPRESENTATION OF CARTESIAN CATEGORIES is a functor between Cartesian
  categories that preserves finite products and equalizers (§1.437). -/

section S1_437

/-- A functor `F : 𝒞 → 𝒟` PRESERVES EQUALIZERS if for each equalizer
    `y : E → A` of `f, g : A → B` in `𝒞`, the image `F(y) : F E → F A`
    is an equalizer of `F f, F g` in `𝒟`. -/
def PreservesEqualizers {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟) [HasEqualizers 𝒞] [HasEqualizers 𝒟] : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B),
    -- the canonical comparison map F(eqObj f g) → eqObj (Ff) (Fg) is iso
    IsIso ((HasEqualizers.eq (F.obj A) (F.obj B) (F.map f) (F.map g)).lift
            { dom := F.obj (eqObj f g)
              map := F.map (eqMap f g)
              eq  := by rw [← F.map_comp, ← F.map_comp, eqMap_eq] })

/-- A functor `F : 𝒞 → 𝒟` PRESERVES TERMINAL if `F(1_𝒞)` is terminal in `𝒟`. -/
def PreservesTerminal {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟) [HasTerminal 𝒞] [HasTerminal 𝒟] : Prop :=
  ∀ (X : 𝒟) (f g : X ⟶ F.obj one), f = g

/-- A functor `F : 𝒞 → 𝒟` PRESERVES BINARY PRODUCTS if the canonical map
    `F(A × B) → F A × F B` (given by `⟨F fst, F snd⟩`) is an isomorphism. -/
def PreservesBinaryProducts {𝒞 : Type u₁} {𝒟 : Type u₂} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟) [HasBinaryProducts 𝒞] [HasBinaryProducts 𝒟] : Prop :=
  ∀ {A B : 𝒞},
    IsIso (pair (F.map (fst (A := A) (B := B))) (F.map (snd (A := A) (B := B))) :
             F.obj (prod A B) ⟶ prod (F.obj A) (F.obj B))

/-- **§1.437** A REPRESENTATION OF CARTESIAN CATEGORIES: a functor between
    Cartesian categories preserving finite products (= terminal + binary products)
    and equalizers. -/
structure CartesianFunctor {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    (F : Functor 𝒞 𝒟) : Prop where
  pres_terminal  : PreservesTerminal F
  pres_products  : PreservesBinaryProducts F
  pres_equalizers : PreservesEqualizers F

/-- **§1.437**: A CartesianFunctor preserves pullbacks.

  PROOF: By §1.432 a pullback of `f : A → C`, `g : B → C` is the equalizer
  of `fst ≫ f`, `snd ≫ g` on `A × B`.  Since `F` preserves products and
  equalizers, it preserves this construction. -/
theorem cartesianFunctor_preserves_pullbacks {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    {F : Functor 𝒞 𝒟} (_hcf : CartesianFunctor F) :
    ∀ {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C),
      (products_equalizers_implies_pullbacks f g).cone.IsPullback :=
  fun f g => (products_equalizers_implies_pullbacks f g).cone_isPullback

/-- An `EqualizerCone` is an EQUALIZER if every cone over the same parallel
    pair factors uniquely through it (universal-property form, choice-free). -/
def EqualizerCone.IsEqualizer {A B : 𝒞} {f g : A ⟶ B} (c : EqualizerCone f g) : Prop :=
  ∀ d : EqualizerCone f g, ∃ u : d.dom ⟶ c.dom,
    u ≫ c.map = d.map ∧ ∀ v : d.dom ⟶ c.dom, v ≫ c.map = d.map → v = u

/-- The chosen equalizer of a parallel pair satisfies the universal property. -/
theorem chosenEqualizer_isEqualizer {𝒟 : Type u} [Cat.{v} 𝒟] [HasEqualizers 𝒟]
    {A B : 𝒟} (f g : A ⟶ B) :
    (EqualizerCone.mk (eqObj f g) (eqMap f g) (eqMap_eq f g)).IsEqualizer := by
  intro d
  exact ⟨eqLift f g d.map d.eq, eqLift_fac f g d.map d.eq,
    fun v hv => eqLift_uniq f g d.map d.eq v hv⟩

/-- Two equalizer cones over the same parallel pair: the comparison map (any
    `m` with `m ≫ c.map = d.map`) between their domains is an isomorphism. -/
theorem isIso_of_two_equalizers {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B : 𝒟} {f g : A ⟶ B} {c d : EqualizerCone f g}
    (hc : c.IsEqualizer) (hd : d.IsEqualizer)
    (m : c.dom ⟶ d.dom) (hm : m ≫ d.map = c.map) :
    IsIso m := by
  obtain ⟨n, hn, _⟩ := hc d   -- n : d.dom → c.dom, n ≫ c.map = d.map
  refine ⟨n, ?_, ?_⟩
  · obtain ⟨_, _, huniq⟩ := hc c
    have e1 : (m ≫ n) ≫ c.map = c.map := by rw [Cat.assoc, hn, hm]
    rw [huniq (m ≫ n) e1, huniq (Cat.id c.dom) (Cat.id_comp _)]
  · obtain ⟨_, _, huniq⟩ := hd d
    have e1 : (n ≫ m) ≫ d.map = d.map := by rw [Cat.assoc, hm, hn]
    rw [huniq (n ≫ m) e1, huniq (Cat.id d.dom) (Cat.id_comp _)]

/-- **§1.434 bridge.**  In a category with binary products, a cone
    `(E, m)` equalizing `f, g : A → B` is the equalizer of `f, g` iff the
    square `(E, m, m)` is a pullback of `u := ⟨id, f⟩` and `v := ⟨id, g⟩`
    over `A × B`.  Here we record the two implications as a single equivalence
    at the level of the universal properties. -/
theorem isEqualizer_iff_isPullback {𝒟 : Type u} [Cat.{v} 𝒟] [HasBinaryProducts 𝒟]
    {A B E : 𝒟} {f g : A ⟶ B} (m : E ⟶ A) (hm : m ≫ f = m ≫ g) :
    (EqualizerCone.mk E m hm).IsEqualizer ↔
      (Cone.mk (f := pair (Cat.id A) f) (g := pair (Cat.id A) g) E m m
        (by rw [pair_uniq (m ≫ Cat.id A) (m ≫ f) (m ≫ pair (Cat.id A) f)
                  (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]),
                pair_uniq (m ≫ Cat.id A) (m ≫ g) (m ≫ pair (Cat.id A) g)
                  (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]), hm])).IsPullback := by
  constructor
  · -- equalizer ⟹ pullback
    intro heq d
    -- d is a cone over (u,v): d.π₁ ≫ u = d.π₂ ≫ v.  Comparing first coords gives
    -- d.π₁ = d.π₂; comparing seconds gives d.π₁ ≫ f = d.π₁ ≫ g.
    have hd12 : d.π₁ = d.π₂ := by
      have := d.w
      calc d.π₁ = d.π₁ ≫ Cat.id A := (Cat.comp_id _).symm
        _ = d.π₁ ≫ (pair (Cat.id A) f ≫ fst) := by rw [fst_pair]
        _ = (d.π₁ ≫ pair (Cat.id A) f) ≫ fst := (Cat.assoc _ _ _).symm
        _ = (d.π₂ ≫ pair (Cat.id A) g) ≫ fst := by rw [this]
        _ = d.π₂ ≫ (pair (Cat.id A) g ≫ fst) := Cat.assoc _ _ _
        _ = d.π₂ ≫ Cat.id A := by rw [fst_pair]
        _ = d.π₂ := Cat.comp_id _
    have hdeq : d.π₁ ≫ f = d.π₁ ≫ g := by
      have := d.w
      calc d.π₁ ≫ f = d.π₁ ≫ (pair (Cat.id A) f ≫ snd) := by rw [snd_pair]
        _ = (d.π₁ ≫ pair (Cat.id A) f) ≫ snd := (Cat.assoc _ _ _).symm
        _ = (d.π₂ ≫ pair (Cat.id A) g) ≫ snd := by rw [this]
        _ = d.π₂ ≫ (pair (Cat.id A) g ≫ snd) := Cat.assoc _ _ _
        _ = d.π₂ ≫ g := by rw [snd_pair]
        _ = d.π₁ ≫ g := by rw [hd12]
    obtain ⟨z, hz, huniq⟩ := heq (EqualizerCone.mk d.pt d.π₁ hdeq)
    refine ⟨z, ⟨hz, ?_⟩, ?_⟩
    · show z ≫ m = d.π₂
      exact hz.trans hd12
    · intro w hw₁ _
      exact huniq w hw₁
  · -- pullback ⟹ equalizer
    intro hpb d
    -- d : EqualizerCone f g, i.e. d.map ≫ f = d.map ≫ g.  Build a pullback cone.
    have hwd : d.map ≫ pair (Cat.id A) f = d.map ≫ pair (Cat.id A) g := by
      rw [pair_uniq (d.map ≫ Cat.id A) (d.map ≫ f) (d.map ≫ pair (Cat.id A) f)
            (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]),
          pair_uniq (d.map ≫ Cat.id A) (d.map ≫ g) (d.map ≫ pair (Cat.id A) g)
            (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]), d.eq]
    obtain ⟨z, ⟨hz₁, _⟩, huniq⟩ := hpb (Cone.mk d.dom d.map d.map hwd)
    refine ⟨z, hz₁, ?_⟩
    intro v hv
    exact huniq v hv (by rw [hv])

/-- The equalizer of two EQUAL maps is trivial: `eqMap f g` is an isomorphism
    (its inverse is the lift of the identity). -/
theorem eqMap_iso_of_eq {𝒟 : Type u} [Cat.{v} 𝒟] [HasEqualizers 𝒟]
    {A B : 𝒟} {f g : A ⟶ B} (h : f = g) : IsIso (eqMap f g) := by
  have hcond : Cat.id A ≫ f = Cat.id A ≫ g := by rw [Cat.id_comp, Cat.id_comp, h]
  let eL := eqLift f g (Cat.id A) hcond
  have heL_fac : eL ≫ eqMap f g = Cat.id A := eqLift_fac f g _ hcond
  have hem_eL : eqMap f g ≫ eL = Cat.id _ := by
    have h1 := eqLift_uniq f g (eqMap f g) (eqMap_eq _ _) (eqMap f g ≫ eL)
                  (by rw [Cat.assoc, heL_fac, Cat.comp_id])
    have h2 := eqLift_uniq f g (eqMap f g) (eqMap_eq _ _) (Cat.id _) (Cat.id_comp _)
    rw [h1, ← h2]
  exact ⟨eL, hem_eL, heL_fac⟩

/-- An isomorphism is an equalizer of any parallel pair it equalizes: if
    `m : E ⟶ A` is iso and `m ≫ f = m ≫ g`, then `(E, m)` is the equalizer
    of `f, g`.  (Choice-free: the lift of a cone `d` is `d.map ≫ m⁻¹`.) -/
theorem isEqualizer_of_isIso {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B E : 𝒟} {f g : A ⟶ B} (m : E ⟶ A) (hm : m ≫ f = m ≫ g)
    (hmi : IsIso m) : (EqualizerCone.mk E m hm).IsEqualizer := by
  obtain ⟨n, hmn, hnm⟩ := hmi
  intro d
  refine ⟨d.map ≫ n, ?_, ?_⟩
  · show (d.map ≫ n) ≫ m = d.map
    rw [Cat.assoc, hnm, Cat.comp_id]
  · intro v hv
    -- v = v ≫ (m ≫ n) = (v ≫ m) ≫ n = d.map ≫ n
    calc v = v ≫ Cat.id E := (Cat.comp_id _).symm
      _ = v ≫ (m ≫ n)    := by rw [hmn]
      _ = (v ≫ m) ≫ n    := (Cat.assoc _ _ _).symm
      _ = d.map ≫ n      := by rw [hv]

/-- Conversely, if `(E, m)` is an equalizer of a pair of EQUAL maps `f = g`
    (so the constraint is vacuous and the codomain `A` itself, with `1_A`, is a
    cone), then `m` is an isomorphism.  This is the reflection-of-isos kernel:
    `f` iso ⟺ `(dom f, f)` is an equalizer of `1_B, 1_B`. -/
theorem isIso_of_isEqualizer_id {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B E : 𝒟} {f g : A ⟶ B} {m : E ⟶ A} (hfg : f = g)
    {hm : m ≫ f = m ≫ g} (heq : (EqualizerCone.mk E m hm).IsEqualizer) :
    IsIso m := by
  -- `(A, 1_A)` is a cone over `(f, g)` since `1_A ≫ f = 1_A ≫ g` (as `f = g`).
  have hid : Cat.id A ≫ f = Cat.id A ≫ g := by rw [Cat.id_comp, Cat.id_comp, hfg]
  obtain ⟨n, hn, _⟩ := heq (EqualizerCone.mk A (Cat.id A) hid)
  -- n : A ⟶ E with n ≫ m = 1_A.  Show m ≫ n = 1_E via uniqueness on cone (E, m).
  refine ⟨n, ?_, hn⟩
  obtain ⟨_, _, huniq⟩ := heq (EqualizerCone.mk E m hm)
  have e1 : (m ≫ n) ≫ m = m := by rw [Cat.assoc, hn, Cat.comp_id]
  rw [huniq (m ≫ n) e1, huniq (Cat.id E) (Cat.id_comp _)]

/-- Two pullback cones over the same cospan have a canonical comparison map
    that is an isomorphism (pullbacks are unique up to iso). -/
theorem isIso_of_two_pullbacks {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B C : 𝒟} {f : A ⟶ C} {g : B ⟶ C} {c d : Cone f g}
    (hc : c.IsPullback) (hd : d.IsPullback)
    (u : c.pt ⟶ d.pt) (hu₁ : u ≫ d.π₁ = c.π₁) (hu₂ : u ≫ d.π₂ = c.π₂) :
    IsIso u := by
  obtain ⟨v, ⟨hv₁, hv₂⟩, _⟩ := hc d
  refine ⟨v, ?_, ?_⟩
  · -- u ≫ v = id_c : both equal the self-comparison of c, which is unique = id
    obtain ⟨_, _, huniq⟩ := hc c
    have e1 : (u ≫ v) ≫ c.π₁ = c.π₁ := by rw [Cat.assoc, hv₁, hu₁]
    have e2 : (u ≫ v) ≫ c.π₂ = c.π₂ := by rw [Cat.assoc, hv₂, hu₂]
    rw [huniq (u ≫ v) e1 e2, huniq (Cat.id c.pt) (Cat.id_comp _) (Cat.id_comp _)]
  · -- v ≫ u = id_d
    obtain ⟨_, _, huniq⟩ := hd d
    have e1 : (v ≫ u) ≫ d.π₁ = d.π₁ := by rw [Cat.assoc, hu₁, hv₁]
    have e2 : (v ≫ u) ≫ d.π₂ = d.π₂ := by rw [Cat.assoc, hu₂, hv₂]
    rw [huniq (v ≫ u) e1 e2, huniq (Cat.id d.pt) (Cat.id_comp _) (Cat.id_comp _)]

/-- A `Cone.IsPullback` can be transported along an isomorphism of its apex:
    if `c` is a pullback and `i : p ≅ c.pt` (with inverse `j`), then the cone
    with apex `p` and projections `i ≫ c.π₁`, `i ≫ c.π₂` is a pullback. -/
theorem isPullback_of_iso_apex {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B C : 𝒟} {f : A ⟶ C} {g : B ⟶ C} {c : Cone f g} (hc : c.IsPullback)
    {p : 𝒟} (i : p ⟶ c.pt) (j : c.pt ⟶ p)
    (hij : i ≫ j = Cat.id p) (hji : j ≫ i = Cat.id c.pt)
    (w : (i ≫ c.π₁) ≫ f = (i ≫ c.π₂) ≫ g) :
    (Cone.mk p (i ≫ c.π₁) (i ≫ c.π₂) w).IsPullback := by
  intro d
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc d
  refine ⟨u ≫ j, ⟨?_, ?_⟩, ?_⟩
  · show (u ≫ j) ≫ i ≫ c.π₁ = d.π₁
    rw [← Cat.assoc, Cat.assoc u, hji, Cat.comp_id, hu₁]
  · show (u ≫ j) ≫ i ≫ c.π₂ = d.π₂
    rw [← Cat.assoc, Cat.assoc u, hji, Cat.comp_id, hu₂]
  · intro v hv₁ hv₂
    -- v ≫ i is the unique comparison into c, equal to u; then v = u ≫ j
    have hvi₁ : (v ≫ i) ≫ c.π₁ = d.π₁ := by
      rw [Cat.assoc]; exact hv₁
    have hvi₂ : (v ≫ i) ≫ c.π₂ = d.π₂ := by
      rw [Cat.assoc]; exact hv₂
    have : v ≫ i = u := huniq (v ≫ i) hvi₁ hvi₂
    calc v = v ≫ Cat.id p := (Cat.comp_id _).symm
      _ = v ≫ i ≫ j := by rw [hij]
      _ = (v ≫ i) ≫ j := (Cat.assoc _ _ _).symm
      _ = u ≫ j := by rw [this]

/-- In a category with binary products, the product cone `(A × B, fst, snd)`
    is a pullback of any cospan `(t₁ : A → T, t₂ : B → T)` whose target `T`
    is weakly terminal (`hT : ∀ X (p q : X → T), p = q`).  This subsumes the
    product-as-pullback-over-the-terminal-object fact, and also works for a
    cospan into `F.obj one` when `F` preserves the terminal. -/
theorem prodCone_isPullback {𝒟 : Type u} [Cat.{v} 𝒟] [HasBinaryProducts 𝒟]
    {A B T : 𝒟} (t₁ : A ⟶ T) (t₂ : B ⟶ T) (hT : ∀ (X : 𝒟) (p q : X ⟶ T), p = q) :
    (Cone.mk (prod A B) fst snd (hT _ (fst ≫ t₁) (snd ≫ t₂))).IsPullback := by
  intro d
  refine ⟨pair d.π₁ d.π₂, ⟨fst_pair _ _, snd_pair _ _⟩, ?_⟩
  intro v hv₁ hv₂
  exact pair_uniq d.π₁ d.π₂ v hv₁ hv₂

/-- A `Cone.IsPullback` can be transported along an isomorphism of the cospan
    APEX `C`: if `c` is a pullback of `(f', g' : · → C')` and `φ : C' → C''`
    is iso, then the same apex and projections form a pullback of
    `(f' ≫ φ, g' ≫ φ)` — the cospan maps are post-composed by the iso.
    (Post-composing a cospan by a mono — here an iso — does not change the
    pullback.) -/
theorem isPullback_of_iso_cospan {𝒟 : Type u} [Cat.{v} 𝒟]
    {A B C' C'' : 𝒟} {f' : A ⟶ C'} {g' : B ⟶ C'} {c : Cone f' g'}
    (hc : c.IsPullback) (φ : C' ⟶ C'') (ψ : C'' ⟶ C') (hφψ : φ ≫ ψ = Cat.id C')
    (w : c.π₁ ≫ (f' ≫ φ) = c.π₂ ≫ (g' ≫ φ)) :
    (Cone.mk (f := f' ≫ φ) (g := g' ≫ φ) c.pt c.π₁ c.π₂ w).IsPullback := by
  intro d
  -- d : cone over (f'≫φ, g'≫φ): d.π₁ ≫ (f' ≫ φ) = d.π₂ ≫ (g' ≫ φ).
  -- Post-compose by ψ to cancel φ (it is split-monic) ⇒ cone over (f',g').
  have hdw : d.π₁ ≫ f' = d.π₂ ≫ g' := by
    have hd := d.w
    calc d.π₁ ≫ f' = (d.π₁ ≫ f') ≫ Cat.id C' := (Cat.comp_id _).symm
      _ = (d.π₁ ≫ f') ≫ (φ ≫ ψ) := by rw [hφψ]
      _ = (d.π₁ ≫ (f' ≫ φ)) ≫ ψ := by simp only [Cat.assoc]
      _ = (d.π₂ ≫ (g' ≫ φ)) ≫ ψ := by rw [hd]
      _ = (d.π₂ ≫ g') ≫ (φ ≫ ψ) := by simp only [Cat.assoc]
      _ = (d.π₂ ≫ g') ≫ Cat.id C' := by rw [hφψ]
      _ = d.π₂ ≫ g' := Cat.comp_id _
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc (Cone.mk d.pt d.π₁ d.π₂ hdw)
  exact ⟨u, ⟨hu₁, hu₂⟩, fun v hv₁ hv₂ => huniq v hv₁ hv₂⟩

/-- **§1.437**: A functor preserving pullbacks and the terminator is a
    representation of Cartesian categories.

  PROOF: §1.433 gives binary products (pullback over terminator);
  §1.434 gives equalizers (pullback of ⟨id,f⟩ vs ⟨id,g⟩). -/
theorem pullbacks_terminal_implies_cartesianFunctor {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    {F : Functor 𝒞 𝒟}
    (hpull : ∀ {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C),
      Cone.IsPullback
        { pt := F.obj (products_equalizers_implies_pullbacks f g).cone.pt
          π₁ := F.map (products_equalizers_implies_pullbacks f g).cone.π₁
          π₂ := F.map (products_equalizers_implies_pullbacks f g).cone.π₂
          w  := by rw [← F.map_comp, ← F.map_comp,
                       (products_equalizers_implies_pullbacks f g).cone.w] })
    (hterm : PreservesTerminal F) : CartesianFunctor F := by
  -- `F.obj one` is weakly terminal in 𝒟 (PreservesTerminal: any two maps into it agree).
  have hweakT : ∀ (X : 𝒟) (p q : X ⟶ F.obj one), p = q := hterm
  have hprodPres : PreservesBinaryProducts F := by
    intro A B
    -- The §1.432 pullback of (term A, term B): its apex is the equalizer
    -- of `fst ≫ term A` and `snd ≫ term B`, which are EQUAL (both into `one`),
    -- so the comparison `pbMap := eqMap … : P.pt → A × B` is an iso.
    let P := products_equalizers_implies_pullbacks (term A) (term B)
    have hcospan_eq : (fst (A := A) (B := B)) ≫ term A = snd ≫ term B :=
      term_uniq _ _
    -- pbMap : P.pt → prod A B  (the equalizer map), an iso in 𝒞.
    have hpb_iso : IsIso (eqMap (fst (A := A) (B := B) ≫ term A) (snd ≫ term B)) :=
      eqMap_iso_of_eq hcospan_eq
    obtain ⟨pbInv, hpb1, hpb2⟩ := hpb_iso
    -- The §1.432 cone projections reduce definitionally to `pbMap ≫ fst`, `pbMap ≫ snd`.
    -- `Fc` (apex `F P.pt`, projs `F.map (pbMap≫fst)`, `F.map (pbMap≫snd)`) is a pullback.
    have hFc : (Cone.mk (F.obj P.cone.pt) (F.map P.cone.π₁) (F.map P.cone.π₂)
        (by rw [← F.map_comp, ← F.map_comp, P.cone.w])).IsPullback := hpull (term A) (term B)
    -- Transport to apex `F.obj (prod A B)` via the F-image of the iso `pbMap`.
    -- i : F(prod A B) → F P.pt  is  F.map pbInv ;  j : F P.pt → F(prod A B) is F.map pbMap.
    -- The transported projections equal `F.map fst`, `F.map snd`.
    have hπ₁ : F.map pbInv ≫ F.map P.cone.π₁ = F.map (fst (A := A) (B := B)) := by
      rw [← F.map_comp]; congr 1
      show pbInv ≫ (eqMap _ _ ≫ fst) = fst
      rw [← Cat.assoc, hpb2, Cat.id_comp]
    have hπ₂ : F.map pbInv ≫ F.map P.cone.π₂ = F.map (snd (A := A) (B := B)) := by
      rw [← F.map_comp]; congr 1
      show pbInv ≫ (eqMap _ _ ≫ snd) = snd
      rw [← Cat.assoc, hpb2, Cat.id_comp]
    have hij : F.map pbInv ≫ F.map (eqMap (fst (A := A) (B := B) ≫ term A) (snd ≫ term B))
        = Cat.id (F.obj (prod A B)) := by rw [← F.map_comp, hpb2, F.map_id]
    have hji : F.map (eqMap (fst (A := A) (B := B) ≫ term A) (snd ≫ term B)) ≫ F.map pbInv
        = Cat.id (F.obj P.cone.pt) := by
      rw [← F.map_comp, hpb1]; exact F.map_id _
    have hFpc : (Cone.mk (f := F.map (term A)) (g := F.map (term B)) (F.obj (prod A B))
        (F.map (fst (A := A) (B := B))) (F.map snd)
        (hweakT _ (F.map (fst (A := A) (B := B)) ≫ F.map (term A))
                  (F.map snd ≫ F.map (term B)))).IsPullback := by
      have key := isPullback_of_iso_apex hFc (F.map pbInv)
        (F.map (eqMap (fst (A := A) (B := B) ≫ term A) (snd ≫ term B))) hij hji (hweakT _ _ _)
      -- rewrite the cone of `key` to the desired projections via hπ₁/hπ₂
      intro d
      obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := key d
      refine ⟨u, ⟨?_, ?_⟩, ?_⟩
      · show u ≫ F.map (fst (A := A) (B := B)) = d.π₁
        rw [← hπ₁]; exact hu₁
      · show u ≫ F.map (snd (A := A) (B := B)) = d.π₂
        rw [← hπ₂]; exact hu₂
      · intro v hv₁ hv₂
        refine huniq v ?_ ?_
        · show v ≫ (F.map pbInv ≫ F.map P.cone.π₁) = d.π₁
          rw [hπ₁]; exact hv₁
        · show v ≫ (F.map pbInv ≫ F.map P.cone.π₂) = d.π₂
          rw [hπ₂]; exact hv₂
    -- Now `prod (F.obj A) (F.obj B)` with (fst,snd) is a pullback over the same cospan.
    have hprodC : (Cone.mk (prod (F.obj A) (F.obj B)) fst snd
        (hweakT _ (fst ≫ F.map (term A)) (snd ≫ F.map (term B)))).IsPullback :=
      prodCone_isPullback (F.map (term A)) (F.map (term B)) hweakT
    -- The comparison `pair (F.map fst) (F.map snd)` between the two pullbacks is iso.
    exact isIso_of_two_pullbacks hFpc hprodC
      (pair (F.map (fst (A := A) (B := B))) (F.map snd))
      (fst_pair _ _) (snd_pair _ _)
  refine { pres_terminal := hterm, pres_products := hprodPres, pres_equalizers := ?_ }
  -- PreservesEqualizers
  intro A B f g
  -- Abbreviations for the parallel pair and its §1.434 representation as a pullback.
  -- u = ⟨id,f⟩, v = ⟨id,g⟩ : A → A×B.  The equalizer (eqObj f g, eqMap f g) is the
  -- pullback of (u,v); the §1.432 pullback P of (u,v) is iso to it.
  let u : A ⟶ prod A B := pair (Cat.id A) f
  let v : A ⟶ prod A B := pair (Cat.id A) g
  -- The cone (eqObj f g, eqMap, eqMap) over (u,v).
  have hwEq : eqMap f g ≫ u = eqMap f g ≫ v := by
    show eqMap f g ≫ pair (Cat.id A) f = eqMap f g ≫ pair (Cat.id A) g
    rw [pair_uniq (eqMap f g ≫ Cat.id A) (eqMap f g ≫ f) (eqMap f g ≫ pair (Cat.id A) f)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]),
        pair_uniq (eqMap f g ≫ Cat.id A) (eqMap f g ≫ g) (eqMap f g ≫ pair (Cat.id A) g)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]), eqMap_eq f g]
  let eqCone : Cone u v := Cone.mk (eqObj f g) (eqMap f g) (eqMap f g) hwEq
  -- (eqObj f g, eqMap, eqMap) is a pullback of (u,v) in 𝒞.
  have hEqPB : eqCone.IsPullback :=
    (isEqualizer_iff_isPullback (eqMap f g) (eqMap_eq f g)).mp (chosenEqualizer_isEqualizer f g)
  -- The §1.432 pullback of (u,v); its apex P.pt is iso to eqObj f g.
  let P := products_equalizers_implies_pullbacks u v
  have hPpb : P.cone.IsPullback := P.cone_isPullback
  -- Canonical comparison θ : eqObj f g → P.pt; θ ≫ P.πᵢ = eqMap f g; θ is iso.
  obtain ⟨θ, ⟨hθ₁, hθ₂⟩, _⟩ := hPpb eqCone
  have hθ_iso : IsIso θ := isIso_of_two_pullbacks hEqPB hPpb θ hθ₁ hθ₂
  obtain ⟨θ', hθθ', hθ'θ⟩ := hθ_iso
  -- F preserves P's pullback (over (Fu, Fv)).
  have hFc : (Cone.mk (f := F.map u) (g := F.map v) (F.obj P.cone.pt)
      (F.map P.cone.π₁) (F.map P.cone.π₂)
      (by rw [← F.map_comp, ← F.map_comp, P.cone.w])).IsPullback := hpull u v
  -- Transport to apex F(eqObj f g) via F-image of θ : eqObj f g → P.pt.
  have hθP₁ : F.map θ ≫ F.map P.cone.π₁ = F.map (eqMap f g) := by
    rw [← F.map_comp, hθ₁]
  have hθP₂ : F.map θ ≫ F.map P.cone.π₂ = F.map (eqMap f g) := by
    rw [← F.map_comp, hθ₂]
  have hFij : F.map θ ≫ F.map θ' = Cat.id (F.obj (eqObj f g)) := by
    rw [← F.map_comp, hθθ']; exact F.map_id _
  have hFji : F.map θ' ≫ F.map θ = Cat.id (F.obj P.cone.pt) := by
    rw [← F.map_comp, hθ'θ]; exact F.map_id _
  have hFeqPB_uv : (Cone.mk (f := F.map u) (g := F.map v) (F.obj (eqObj f g))
      (F.map (eqMap f g)) (F.map (eqMap f g))
      (by rw [← F.map_comp, ← F.map_comp, hwEq])).IsPullback := by
    have key := isPullback_of_iso_apex hFc (F.map θ) (F.map θ') hFij hFji
      (by rw [hθP₁, hθP₂, ← F.map_comp, ← F.map_comp, hwEq])
    intro d
    obtain ⟨w, ⟨hw₁, hw₂⟩, huniq⟩ := key d
    refine ⟨w, ⟨?_, ?_⟩, ?_⟩
    · show w ≫ F.map (eqMap f g) = d.π₁
      exact (congrArg (w ≫ ·) hθP₁).symm.trans hw₁
    · show w ≫ F.map (eqMap f g) = d.π₂
      exact (congrArg (w ≫ ·) hθP₂).symm.trans hw₂
    · intro z hz₁ hz₂
      refine huniq z ?_ ?_
      · show z ≫ (F.map θ ≫ F.map P.cone.π₁) = d.π₁
        exact (congrArg (z ≫ ·) hθP₁).trans hz₁
      · show z ≫ (F.map θ ≫ F.map P.cone.π₂) = d.π₂
        exact (congrArg (z ≫ ·) hθP₂).trans hz₂
  -- Product-preservation: φ = ⟨F fst, F snd⟩ : F(A×B) → FA×FB is iso, and
  -- F.map u ≫ φ = ⟨id, Ff⟩,  F.map v ≫ φ = ⟨id, Fg⟩.
  obtain ⟨φ', hφφ', _⟩ := hprodPres (A := A) (B := B)
  have hFu_φ : F.map u ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)
      = pair (Cat.id (F.obj A)) (F.map f) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) f ≫ fst) = Cat.id (F.obj A)
      rw [fst_pair, F.map_id]
    · rw [Cat.assoc, snd_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) f ≫ snd) = F.map f
      rw [snd_pair]
  have hFv_φ : F.map v ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)
      = pair (Cat.id (F.obj A)) (F.map g) := by
    refine pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) g ≫ fst) = Cat.id (F.obj A)
      rw [fst_pair, F.map_id]
    · rw [Cat.assoc, snd_pair, ← F.map_comp]
      show F.map (pair (Cat.id A) g ≫ snd) = F.map g
      rw [snd_pair]
  -- Transport the cospan from (Fu, Fv) to (⟨id,Ff⟩, ⟨id,Fg⟩) via the iso φ.
  have hFeqPB : (Cone.mk (f := pair (Cat.id (F.obj A)) (F.map f))
      (g := pair (Cat.id (F.obj A)) (F.map g)) (F.obj (eqObj f g))
      (F.map (eqMap f g)) (F.map (eqMap f g))
      (by rw [← hFu_φ, ← hFv_φ]; simp only [← Cat.assoc, ← F.map_comp]; rw [hwEq])).IsPullback := by
    have key := isPullback_of_iso_cospan hFeqPB_uv
      (pair (F.map (fst (A := A) (B := B))) (F.map snd)) φ' hφφ'
      (by simp only [← Cat.assoc, ← F.map_comp]; rw [hwEq])
    -- `key` is a pullback of (Fu≫φ, Fv≫φ) = (⟨id,Ff⟩, ⟨id,Fg⟩).  Re-interpret a
    -- cone `d` over (⟨id,Ff⟩,⟨id,Fg⟩) as one over (Fu≫φ,Fv≫φ) and apply `key`.
    intro d
    have hdw' : d.π₁ ≫ (F.map u ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd))
        = d.π₂ ≫ (F.map v ≫ pair (F.map (fst (A := A) (B := B))) (F.map snd)) := by
      rw [hFu_φ, hFv_φ]; exact d.w
    obtain ⟨z, ⟨hz₁, hz₂⟩, huniq⟩ := key (Cone.mk d.pt d.π₁ d.π₂ hdw')
    exact ⟨z, ⟨hz₁, hz₂⟩, fun y hy₁ hy₂ => huniq y hy₁ hy₂⟩
  -- Hence (F(eqObj f g), F.map(eqMap f g)) is the equalizer of (Ff, Fg).
  have hFeqMap_eq : F.map (eqMap f g) ≫ F.map f = F.map (eqMap f g) ≫ F.map g :=
    (F.map_comp (eqMap f g) f).symm.trans
      ((congrArg F.map (eqMap_eq f g)).trans (F.map_comp (eqMap f g) g))
  have hFeq_isEq : (EqualizerCone.mk (F.obj (eqObj f g)) (F.map (eqMap f g)) hFeqMap_eq).IsEqualizer :=
    (isEqualizer_iff_isPullback (F.map (eqMap f g)) hFeqMap_eq).mpr hFeqPB
  -- The comparison k to the chosen equalizer is iso.
  let eqD := HasEqualizers.eq (F.obj A) (F.obj B) (F.map f) (F.map g)
  let hcone : EqualizerCone (F.map f) (F.map g) :=
    { dom := F.obj (eqObj f g), map := F.map (eqMap f g),
      eq := by rw [← F.map_comp, ← F.map_comp, eqMap_eq f g] }
  have hk_fac : eqD.lift hcone ≫ eqMap (F.map f) (F.map g) = F.map (eqMap f g) :=
    eqD.fac hcone
  exact isIso_of_two_equalizers hFeq_isEq (chosenEqualizer_isEqualizer (F.map f) (F.map g))
    (eqD.lift hcone) hk_fac

end S1_437

/-! ## §1.438 Reflects equalizers ⟹ reflects isomorphisms; faithfulness

  A functor reflecting equalizers reflects isomorphisms (§1.438).
  An iso-reflecting equalizer-preserving functor is faithful (§1.438). -/

section S1_438

variable {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
variable (F : Functor 𝒞 𝒟)

/-- The `F`-image of an equalizer cone `c` over `(f, g)`: the cone
    `(F c.dom, F c.map)` over `(Ff, Fg)`.  Its commutation law transports
    `c.eq` through `map_comp`. -/
def FImageEqCone [HasEqualizers 𝒞] [HasEqualizers 𝒟] {A B : 𝒞} {f g : A ⟶ B}
    (c : EqualizerCone f g) : EqualizerCone (F.map f) (F.map g) :=
  { dom := F.obj c.dom, map := F.map c.map
    eq := by rw [← F.map_comp, ← F.map_comp, c.eq] }

/-- A functor REFLECTS EQUALIZERS (general-cone form) if: whenever `F` carries
    an equalizer cone `c` over `(f, g)` to an *equalizer* cone in `𝒟`
    (i.e. `FImageEqCone c` is an equalizer), then `c` was already an equalizer
    cone in `𝒞`.  This is the genuine cone-reflection property — strictly
    stronger than merely making the chosen comparison map iso, and it is what
    §1.438 needs (a single `f : A ⟶ B`, viewed as a cone over `1_B, 1_B`,
    must be reflected, not just the chosen equalizer's comparison). -/
def ReflectsEqualizers [HasEqualizers 𝒞] [HasEqualizers 𝒟] : Prop :=
  ∀ {A B : 𝒞} {f g : A ⟶ B} (c : EqualizerCone f g),
    (FImageEqCone F c).IsEqualizer → c.IsEqualizer

/-- **§1.438**: A functor that reflects equalizers reflects isomorphisms.

  PROOF: `f : A → B` is an isomorphism iff it is the equalizer of `1_B`
  and `1_B` (it equalizes since `f ≫ 1 = f ≫ 1`, and any lift is iso).
  So if `F f` is iso in `𝒟`, then `F f` equalizes in `𝒟`, reflecting back
  to `f` equalizing in `𝒞`, which forces `f` to be iso. -/
theorem reflects_equalizers_reflects_isos [HasEqualizers 𝒞] [HasEqualizers 𝒟]
    (hre : ReflectsEqualizers F) :
    ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (F.map f) → IsIso f := by
  intro A B f hFf
  -- View `f` as a cone over the parallel pair `(1_B, 1_B)`: trivially
  -- `f ≫ 1_B = f ≫ 1_B`.
  have hceq : f ≫ Cat.id B = f ≫ Cat.id B := rfl
  let c : EqualizerCone (Cat.id B) (Cat.id B) := EqualizerCone.mk A f hceq
  -- The F-image cone `(F A, F f)` is an equalizer in `𝒟`: `F f` is iso and
  -- equalizes the (equal) pair `(F 1_B, F 1_B)`.
  have hFimg : (FImageEqCone F c).IsEqualizer :=
    isEqualizer_of_isIso (FImageEqCone F c).map (FImageEqCone F c).eq hFf
  -- Reflect: `c = (A, f)` is an equalizer of `(1_B, 1_B)` in `𝒞`.
  have hc : c.IsEqualizer := hre c hFimg
  -- An equalizer of the equal pair `(1_B, 1_B)` is an iso.
  exact isIso_of_isEqualizer_id (f := Cat.id B) (g := Cat.id B) rfl hc

/-- **§1.438**: A source-category-with-equalizers functor that preserves
    equalizers and reflects isomorphisms is faithful (an embedding).

  PROOF (book §1.438): given `f g : A → B` with `F f = F g`, then `F f`
  equalizes `F h` and `F h` for any `h`, so by preservation `f` equalizes
  `h` and `h`.  The equalizer of `h, h` is `id_A` (any map equalizes equal
  maps), so `f = g`. -/
theorem iso_reflecting_eq_preserving_faithful [HasEqualizers 𝒞] [HasEqualizers 𝒟]
    (hre : ∀ {A B : 𝒞} (f : A ⟶ B), IsIso (F.map f) → IsIso f)
    (hpe : PreservesEqualizers F) :
    Embedding F := by
  intro A B f g hfg
  -- Step 1: eqMap(Ff,Fg) is iso in 𝒟 (since Ff=Fg, the equalizer of equal maps has domain≅codomain)
  have hFfg_eq : F.map f = F.map g := hfg
  let em := eqMap (F.map f) (F.map g)
  have hem_iso : IsIso em := eqMap_iso_of_eq hFfg_eq
  -- Step 2: the canonical comparison map k : F(eqObj f g) → eqObj(Ff,Fg) is iso by hpe
  let eqD := HasEqualizers.eq (F.obj A) (F.obj B) (F.map f) (F.map g)
  let hcone : EqualizerCone (F.map f) (F.map g) :=
    { dom := F.obj (eqObj f g), map := F.map (eqMap f g),
      eq := by rw [← F.map_comp, ← F.map_comp, eqMap_eq f g] }
  let k := eqD.lift hcone
  have hk_fac : k ≫ em = F.map (eqMap f g) := eqD.fac hcone
  have hk_iso : IsIso k := hpe f g
  -- Step 3: F.map(eqMap f g) is iso as k ≫ em with both isos
  have hFem_iso : IsIso (F.map (eqMap f g)) := by
    rw [← hk_fac]; exact isIso_comp hk_iso hem_iso
  -- Step 4: eqMap f g is iso in 𝒞 by hre
  have hem_C_iso : IsIso (eqMap f g) := hre (eqMap f g) hFem_iso
  -- Step 5: eqMap f g is epi (iso ⟹ epi); cancel from eqMap_eq f g to get f = g
  obtain ⟨r, _hr1, hr2⟩ := hem_C_iso
  have heq : eqMap f g ≫ f = eqMap f g ≫ g := eqMap_eq f g
  calc f = Cat.id _ ≫ f       := (Cat.id_comp _).symm
    _ = (r ≫ eqMap f g) ≫ f  := by rw [hr2]
    _ = r ≫ eqMap f g ≫ f    := Cat.assoc _ _ _
    _ = r ≫ eqMap f g ≫ g    := by rw [heq]
    _ = (r ≫ eqMap f g) ≫ g  := (Cat.assoc _ _ _).symm
    _ = Cat.id _ ≫ g          := by rw [hr2]
    _ = g                      := Cat.id_comp _

end S1_438

end Freyd
