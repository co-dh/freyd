/-
  Bird & de Moor, *Algebra of Programming* §5.3  Relational coproducts (+ Ex 5.17 guards).

  Builds on `Freyd.S2_2` (`Coproduct`, the five equations of §2.214), `AOP.A4_5` (the
  Boolean layer: negation `∼`, `BooleanAllegory`), and `AOP.A5_1` (the `Relator` structure).

  We reuse `Freyd.Alg.Coproduct` (§2.214) directly rather than redefining coproducts: for
  `C : Coproduct s a₁ a₂` the injections are `C.u₁ : a₁ ⟶ s`, `C.u₂ : a₂ ⟶ s` (book's `inl`,
  `inr`), and the five equations are `C.u₁_self_comp_recip`, `C.u₁_u₂_recip`, `C.u₂_u₁_recip`,
  `C.u₂_self_comp_recip`, `C.recip_union_eq_id`.

  Statements are in Freyd's diagram-order convention: B&dM's composition `X·Y` (right to left)
  is Freyd's `Y ≫ X` (first Y then X).  In particular B&dM's junc `[R,S] = (R·inl°) ∪ (S·inr°)`
  becomes `(C.u₁° ≫ R) ∪ (C.u₂° ≫ S)`.

  Contents:
  §1  `junc` (B&dM 5.9) and its universal-property lemmas, `junc_recip`.
  §2  (5.11) cancellation `junc_recip_junc`, and `junc_map`.
  §2b `Λ[R,S] = [ΛR,ΛS]` (pp. 117–118).
  §3  `sumMap` (B&dM 5.10) and its functor laws.
  §4  Ex 5.12.
  §5  Guards and conditionals (Ex 5.17).
-/
module

public import Freyd.S2_20
public import AOP.A4_5
public import AOP.A4_6  -- `Λ` (§4.6), for the power transpose of a junction
public import AOP.A5_1

universe v₂ u₂ v u

namespace Freyd.Alg

-- (`union_mono` was hoisted into S2_2 at collection.)

/-! ## §1  `junc` (B&dM 5.9) -/

section Junc

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- **B&dM 5.9**: the junc (case) morphism `[R,S] : s ⟶ c` induced by a coproduct
    `C : Coproduct s a₁ a₂` together with `R : a₁ ⟶ c`, `S : a₂ ⟶ c`, in Freyd's diagram order:
    `[R,S] = (u₁°≫R) ∪ (u₂°≫S)`. -/
@[expose] public def junc {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) : s ⟶ c :=
  (C.u₁° ≫ R) ∪ (C.u₂° ≫ S)

/-- **B&dM 5.9** (UP, first injection): `u₁ ≫ [R,S] = R`. -/
public theorem u₁_junc {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) :
    C.u₁ ≫ junc C R S = R := by
  show C.u₁ ≫ ((C.u₁° ≫ R) ∪ (C.u₂° ≫ S)) = R
  rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
    C.u₁_self_comp_recip, C.u₁_u₂_recip, Cat.id_comp, DistributiveAllegory.zero_comp, union_zero]

/-- **B&dM 5.9** (UP, second injection): `u₂ ≫ [R,S] = S`. -/
public theorem u₂_junc {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) :
    C.u₂ ≫ junc C R S = S := by
  show C.u₂ ≫ ((C.u₁° ≫ R) ∪ (C.u₂° ≫ S)) = S
  rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
    C.u₂_u₁_recip, C.u₂_self_comp_recip, Cat.id_comp, DistributiveAllegory.zero_comp,
    DistributiveAllegory.zero_union]

/-- **B&dM 5.9** (UP, uniqueness), reusing the mediator uniqueness already proved for
    `coproduct_five_eqs_to_universal` (§2.214) rather than re-deriving it. -/
public theorem junc_unique {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) {R : a₁ ⟶ c} {S : a₂ ⟶ c} {T : s ⟶ c}
    (h₁ : C.u₁ ≫ T = R) (h₂ : C.u₂ ≫ T = S) : T = junc C R S := by
  obtain ⟨T', hT'1, hT'2, huniq⟩ := coproduct_five_eqs_to_universal C c R S
  rw [huniq T h₁ h₂, huniq (junc C R S) (u₁_junc C R S) (u₂_junc C R S)]

/-- The injections case-split to the identity: `[u₁,u₂] = 1_s`. -/
theorem junc_injections {s a₁ a₂ : 𝒜} (C : Coproduct s a₁ a₂) :
    junc C C.u₁ C.u₂ = Cat.id s :=
  (junc_unique C (Cat.comp_id C.u₁) (Cat.comp_id C.u₂)).symm

/-- `junc` is monotone in both branches. -/
public theorem junc_mono {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) {R R' : a₁ ⟶ c} {S S' : a₂ ⟶ c}
    (hR : R ⊑ R') (hS : S ⊑ S') : junc C R S ⊑ junc C R' S' :=
  union_mono (comp_mono_left (C.u₁°) hR) (comp_mono_left (C.u₂°) hS)

/-- Fusion: post-composing a junc with any `Z` distributes into the branches, an immediate
    consequence of (5.9) via `comp_union_distrib`.  Used for `sumMap`'s functor laws and the
    guard/conditional laws (Ex 5.17) without re-expanding `junc` by hand each time. -/
public theorem junc_comp {s a₁ a₂ c d : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) (Z : c ⟶ d) :
    junc C R S ≫ Z = junc C (R ≫ Z) (S ≫ Z) := by
  show ((C.u₁° ≫ R) ∪ (C.u₂° ≫ S)) ≫ Z = (C.u₁° ≫ (R ≫ Z)) ∪ (C.u₂° ≫ (S ≫ Z))
  rw [union_comp_distrib, Cat.assoc, Cat.assoc]

/-- `[R,S]° = (R°≫u₁) ∪ (S°≫u₂)`. -/
public theorem junc_recip {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) :
    (junc C R S)° = (R° ≫ C.u₁) ∪ (S° ≫ C.u₂) := by
  show ((C.u₁° ≫ R) ∪ (C.u₂° ≫ S))° = (R° ≫ C.u₁) ∪ (S° ≫ C.u₂)
  rw [recip_union, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip,
    Allegory.recip_recip]
  exact DistributiveAllegory.union_comm _ _

/-- A coproduct in a DISTRIBUTIVE allegory is also a PRODUCT — `+` is a BIPRODUCT — with the
    converses `u₁°`, `u₂°` as projections and `(R≫u₁) ∪ (S≫u₂)` as the pairing.  Cancellation is
    `u₁≫u₁° = 1` against `u₂≫u₁° = 0`; uniqueness is the fifth equation `u₁°u₁ ∪ u₂°u₂ = 1`
    composed on the right of the competitor. -/
public theorem coproduct_is_product {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : c ⟶ a₁)
    (S : c ⟶ a₂) :
    ((R ≫ C.u₁) ∪ (S ≫ C.u₂)) ≫ C.u₁° = R ∧ ((R ≫ C.u₁) ∪ (S ≫ C.u₂)) ≫ C.u₂° = S ∧
      ∀ Z : c ⟶ s, Z ≫ C.u₁° = R → Z ≫ C.u₂° = S → Z = (R ≫ C.u₁) ∪ (S ≫ C.u₂) := by
  refine ⟨?_, ?_, fun Z h₁ h₂ => ?_⟩
  · rw [union_comp_distrib, Cat.assoc, Cat.assoc, C.u₁_self_comp_recip, C.u₂_u₁_recip,
      Cat.comp_id, DistributiveAllegory.comp_zero, union_zero]
  · rw [union_comp_distrib, Cat.assoc, Cat.assoc, C.u₁_u₂_recip, C.u₂_self_comp_recip,
      Cat.comp_id, DistributiveAllegory.comp_zero, DistributiveAllegory.zero_union]
  · calc Z = Z ≫ Cat.id s := (Cat.comp_id Z).symm
      _ = Z ≫ ((C.u₁° ≫ C.u₁) ∪ (C.u₂° ≫ C.u₂)) := by rw [C.recip_union_eq_id]
      _ = (Z ≫ (C.u₁° ≫ C.u₁)) ∪ (Z ≫ (C.u₂° ≫ C.u₂)) :=
          DistributiveAllegory.comp_union_distrib _ _ _
      _ = ((Z ≫ C.u₁°) ≫ C.u₁) ∪ ((Z ≫ C.u₂°) ≫ C.u₂) := by rw [Cat.assoc, Cat.assoc]
      _ = (R ≫ C.u₁) ∪ (S ≫ C.u₂) := by rw [h₁, h₂]

/-! ## §2  (5.11) cancellation -/

/-- **B&dM (5.11)**: `[U,V]° ≫ [R,S] = (U°≫R) ∪ (V°≫S)`. -/
public theorem junc_recip_junc {s a₁ a₂ c d : 𝒜} (C : Coproduct s a₁ a₂)
    {U : a₁ ⟶ d} {V : a₂ ⟶ d} {R : a₁ ⟶ c} {S : a₂ ⟶ c} :
    (junc C U V)° ≫ junc C R S = (U° ≫ R) ∪ (V° ≫ S) := by
  rw [junc_recip, union_comp_distrib, Cat.assoc, Cat.assoc, u₁_junc, u₂_junc]

/-- A junction of MAPS is a map.  Simplicity is (5.11) `[f,g]°[f,g] = (f°f) ∪ (g°g)`, both
    branches below `1`; entirety is the fifth coproduct equation `[u₁,u₂] = 1` pushed through
    `[f,g][f,g]° = [f([f,g]°), g([f,g]°)]`, each branch dominating its injection because
    `1 ⊑ ff°`.  Nothing here asks the branches to share a source or a target. -/
public theorem junc_map {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) {f : a₁ ⟶ c} {g : a₂ ⟶ c}
    (hf : Map f) (hg : Map g) : Map (junc C f g) := by
  refine ⟨(entire_iff_one_le _).mpr ?_, ?_⟩
  · have h₁ : C.u₁ ⊑ f ≫ (junc C f g)° := by
      rw [junc_recip]
      calc C.u₁ = Cat.id a₁ ≫ C.u₁ := (Cat.id_comp _).symm
        _ ⊑ (f ≫ f°) ≫ C.u₁ := comp_mono_right (entire_id_le hf.1) _
        _ = f ≫ (f° ≫ C.u₁) := Cat.assoc _ _ _
        _ ⊑ f ≫ ((f° ≫ C.u₁) ∪ (g° ≫ C.u₂)) := comp_mono_left _ (le_union_left _ _)
    have h₂ : C.u₂ ⊑ g ≫ (junc C f g)° := by
      rw [junc_recip]
      calc C.u₂ = Cat.id a₂ ≫ C.u₂ := (Cat.id_comp _).symm
        _ ⊑ (g ≫ g°) ≫ C.u₂ := comp_mono_right (entire_id_le hg.1) _
        _ = g ≫ (g° ≫ C.u₂) := Cat.assoc _ _ _
        _ ⊑ g ≫ ((f° ≫ C.u₁) ∪ (g° ≫ C.u₂)) := comp_mono_left _ (le_union_right _ _)
    rw [junc_comp, ← junc_injections C]
    exact junc_mono C h₁ h₂
  · show (junc C f g)° ≫ junc C f g ⊑ Cat.id c
    rw [junc_recip_junc]
    exact union_lub hf.2 hg.2

end Junc

/-! ## §2b  The power transpose of a junction (B&dM §5.3, p.118) -/

section ΛJunc

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- **B&dM pp. 117–118**: `Λ[R,S] = [ΛR,ΛS]` — the coproduct of maps applied underneath the
    bijection `·∋ ⊣ Λ`.  `[ΛR,ΛS]` is a map (`junc_map` on `Λ_is_map'`) and `[ΛR,ΛS]∋ =
    [ΛR∋,ΛS∋] = [R,S]`, so the universal property of `Λ` names it `Λ[R,S]`. -/
public theorem Λ_junc {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) :
    Λ (junc C R S) = junc C (Λ R) (Λ S) :=
  (Λ_unique _ _ (junc_map C (Λ_is_map' R) (Λ_is_map' S))
    (by rw [junc_comp, Λ_eps_eq', Λ_eps_eq'])).symm

end ΛJunc

/-! ## §3  `sumMap` (B&dM 5.10) -/

section SumMap

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- **B&dM 5.10**: the sum (coproduct) of two morphisms `R : a₁⟶b₁`, `S : a₂⟶b₂` across
    coproducts `C : Coproduct s a₁ a₂`, `D : Coproduct t b₁ b₂`. -/
@[expose] public def sumMap {s a₁ a₂ t b₁ b₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) : s ⟶ t :=
  junc C (R ≫ D.u₁) (S ≫ D.u₂)

public theorem sumMap_mono {s a₁ a₂ t b₁ b₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    {R R' : a₁ ⟶ b₁} {S S' : a₂ ⟶ b₂} (hR : R ⊑ R') (hS : S ⊑ S') :
    sumMap C D R S ⊑ sumMap C D R' S' :=
  junc_mono C (comp_mono_right hR D.u₁) (comp_mono_right hS D.u₂)

/-- **B&dM 5.10**, functor law: `sumMap` sends identities to identities. -/
public theorem sumMap_id {s a₁ a₂ : 𝒜} (C : Coproduct s a₁ a₂) :
    sumMap C C (Cat.id a₁) (Cat.id a₂) = Cat.id s := by
  show junc C (Cat.id a₁ ≫ C.u₁) (Cat.id a₂ ≫ C.u₂) = Cat.id s
  rw [Cat.id_comp, Cat.id_comp]
  exact junc_injections C

/-- **B&dM 5.10**, functor law: `sumMap` sends composition to composition. -/
public theorem sumMap_comp {s a₁ a₂ t b₁ b₂ w c₁ c₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (E : Coproduct w c₁ c₂) (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) (U : b₁ ⟶ c₁) (V : b₂ ⟶ c₂) :
    sumMap C D R S ≫ sumMap D E U V = sumMap C E (R ≫ U) (S ≫ V) := by
  show junc C (R ≫ D.u₁) (S ≫ D.u₂) ≫ junc D (U ≫ E.u₁) (V ≫ E.u₂)
      = junc C ((R ≫ U) ≫ E.u₁) ((S ≫ V) ≫ E.u₂)
  rw [junc_comp]
  have h1 : (R ≫ D.u₁) ≫ junc D (U ≫ E.u₁) (V ≫ E.u₂) = (R ≫ U) ≫ E.u₁ := by
    rw [Cat.assoc, u₁_junc, Cat.assoc]
  have h2 : (S ≫ D.u₂) ≫ junc D (U ≫ E.u₁) (V ≫ E.u₂) = (S ≫ V) ≫ E.u₂ := by
    rw [Cat.assoc, u₂_junc, Cat.assoc]
  rw [h1, h2]

/-- **B&dM p.42** (coproduct fusion, lifted to relations): `[P,Q] · (R+S) = [P·R, Q·S]`,
    mirrored to `(R+S) ≫ [P,Q] = [R≫P, S≫Q]`. -/
public theorem sumMap_junc {s a₁ a₂ t b₁ b₂ c : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) (P : b₁ ⟶ c) (Q : b₂ ⟶ c) :
    sumMap C D R S ≫ junc D P Q = junc C (R ≫ P) (S ≫ Q) := by
  show junc C (R ≫ D.u₁) (S ≫ D.u₂) ≫ junc D P Q = junc C (R ≫ P) (S ≫ Q)
  rw [junc_comp, Cat.assoc, Cat.assoc, u₁_junc, u₂_junc]

/-- `(R+S) ≫ u₁° = u₁° ≫ R`: post-composing a sum with an injection's CONVERSE selects that
    branch, the other being annihilated by `u₂ ≫ u₁° = 𝟘`.  The converse-side companion of
    `u₁_junc`, and what makes the projection `u₁°` strictly natural. -/
public theorem sumMap_recip_u₁ {s a₁ a₂ t b₁ b₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) : sumMap C D R S ≫ D.u₁° = C.u₁° ≫ R := by
  show junc C (R ≫ D.u₁) (S ≫ D.u₂) ≫ D.u₁° = C.u₁° ≫ R
  rw [junc_comp, Cat.assoc, Cat.assoc, D.u₁_self_comp_recip, D.u₂_u₁_recip, Cat.comp_id,
    DistributiveAllegory.comp_zero]
  show (C.u₁° ≫ R) ∪ (C.u₂° ≫ (𝟘 : a₂ ⟶ b₁)) = C.u₁° ≫ R
  rw [DistributiveAllegory.comp_zero, union_zero]

/-- `(R+S) ≫ u₂° = u₂° ≫ S`, the `u₂` half of `sumMap_recip_u₁`. -/
public theorem sumMap_recip_u₂ {s a₁ a₂ t b₁ b₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) : sumMap C D R S ≫ D.u₂° = C.u₂° ≫ S := by
  show junc C (R ≫ D.u₁) (S ≫ D.u₂) ≫ D.u₂° = C.u₂° ≫ S
  rw [junc_comp, Cat.assoc, Cat.assoc, D.u₁_u₂_recip, D.u₂_self_comp_recip, Cat.comp_id,
    DistributiveAllegory.comp_zero]
  show (C.u₁° ≫ (𝟘 : a₁ ⟶ b₂)) ∪ (C.u₂° ≫ S) = C.u₂° ≫ S
  rw [DistributiveAllegory.comp_zero, DistributiveAllegory.zero_union]

/-- **B&dM 5.10**, functor law: `sumMap` commutes with converse (with the coproducts swapped). -/
public theorem sumMap_recip {s a₁ a₂ t b₁ b₂ : 𝒜} (C : Coproduct s a₁ a₂) (D : Coproduct t b₁ b₂)
    (R : a₁ ⟶ b₁) (S : a₂ ⟶ b₂) : (sumMap C D R S)° = sumMap D C R° S° := by
  show (junc C (R ≫ D.u₁) (S ≫ D.u₂))° = junc D (R° ≫ C.u₁) (S° ≫ C.u₂)
  rw [junc_recip, Allegory.recip_comp, Allegory.recip_comp, Cat.assoc, Cat.assoc]
  rfl

end SumMap

/-! ## Relators are closed under coproduct -/

section SumRelator

-- Needs `PositiveAllegory`, not merely `DistributiveAllegory`: a relator's `obj` must CHOOSE a
-- coproduct object for each `x`, which is exactly `PositiveAllegory.coprod`.
variable {𝒜 : Type u} [PositiveAllegory 𝒜]

/-- Relators are closed under coproduct: `X ↦ F X + G X`, `R ↦ F R + G R`, on the ambient
    `PositiveAllegory`'s chosen coproducts.  Functor laws from `sumMap`'s composed with `F`'s
    and `G`'s. -/
@[expose] public def Relator.sum {𝒮 : Type u₂} [Allegory.{v₂} 𝒮] (F G : Relator 𝒮 𝒜) :
    Relator 𝒮 𝒜 where
  obj x := PositiveAllegory.coprod (F.obj x) (G.obj x)
  map R := sumMap (PositiveAllegory.has_coproduct _ _) (PositiveAllegory.has_coproduct _ _)
    (F.map R) (G.map R)
  map_id x := by
    simp only [F.map_id, G.map_id]; exact sumMap_id (PositiveAllegory.has_coproduct _ _)
  map_comp R S := by
    simp only [F.map_comp, G.map_comp]; exact (sumMap_comp _ _ _ _ _ _ _).symm
  map_mono h := sumMap_mono _ _ (F.map_mono h) (G.map_mono h)

end SumRelator

/-! ## §4  Ex 5.12 -/

section Ex512

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- **Ex 5.12**: `[1,0] = u₁°`.  (`DistributiveAllegory.zero_comp`/`comp_zero` are primitive
    axioms of the class here, not derived facts, so no extra hypotheses are needed.) -/
theorem junc_id_zero {s a₁ a₂ : 𝒜} (C : Coproduct s a₁ a₂) :
    junc C (Cat.id a₁) (𝟘 : a₂ ⟶ a₁) = C.u₁° := by
  show (C.u₁° ≫ Cat.id a₁) ∪ (C.u₂° ≫ (𝟘 : a₂ ⟶ a₁)) = C.u₁°
  rw [Cat.comp_id, DistributiveAllegory.comp_zero, union_zero]

end Ex512

-- Ex 5.14 (`(R+S) ∩ ([U,V]°·[P,Q]) = (R∩(U°·P)) + (S∩(V°·Q))`) is DROPPED: no local copy of
-- the B&dM source text was available in this repo to pin down the exact mirrored form (which
-- meet/junc nests inside which), and the task marked it optional ("DROP freely if messy").

/-! ## §5  Guards and conditionals (Ex 5.17)

  The complement of a coreflexive `X` WITHIN the coreflexives is `corNeg X := ∼X ∩ 1`.  Given a
  self-coproduct `C : Coproduct s a a`, `guard C X : a ⟶ s` is the map sending each point either
  through the first or second injection according to whether `X` or `corNeg X` holds; `cond`
  then dispatches to `R` or `S` accordingly. -/

section Guard

variable {𝒜 : Type u} [BooleanAllegory 𝒜]

/-- The complement of `X` within the coreflexives (Ex 5.17). -/
def corNeg {a : 𝒜} (X : a ⟶ a) : a ⟶ a := (∼X) ∩ Cat.id a

theorem corNeg_coreflexive {a : 𝒜} (X : a ⟶ a) : Coreflexive (corNeg X) :=
  inter_lb_right (∼X) (Cat.id a)

/-- `X ∩ corNeg X = 0` — holds unconditionally (no coreflexivity hypothesis needed). -/
theorem inter_corNeg {a : 𝒜} (X : a ⟶ a) : X ∩ corNeg X = 𝟘 := by
  show X ∩ ((∼X) ∩ Cat.id a) = 𝟘
  rw [Allegory.inter_assoc, inter_neg_zero X]
  exact inter_eq_left (zero_le _)

/-- `X ∪ corNeg X = 1` when `X` is coreflexive (Ex 5.17): `X` and its coreflexive complement
    exhaust the identity. -/
theorem union_corNeg {a : 𝒜} {X : a ⟶ a} (hX : Coreflexive X) : X ∪ corNeg X = Cat.id a := by
  have hsplit : Cat.id a ∩ (X ∪ ∼X) = (Cat.id a ∩ X) ∪ (Cat.id a ∩ (∼X)) :=
    DistributiveAllegory.inter_union_distrib (Cat.id a) X (∼X)
  rw [union_neg_eq_top X, inter_eq_left (show Cat.id a ⊑ topHom a a from LocallyCompleteDistributiveAllegory.le_Sup trivial),
    Allegory.inter_comm (Cat.id a) X, inter_eq_left hX, Allegory.inter_comm (Cat.id a) (∼X)] at hsplit
  exact hsplit.symm

/-- **Ex 5.17**: the guard morphism dispatching to the first branch on `X`, the second on
    `corNeg X`. -/
def guard {s a : 𝒜} (C : Coproduct s a a) (X : a ⟶ a) : a ⟶ s :=
  (junc C X (corNeg X))°

/-- Two coreflexive helper facts (symmetry + idempotence), packaged once for reuse. -/
private theorem coreflexive_facts {a : 𝒜} {X : a ⟶ a} (hX : Coreflexive X) :
    X° = X ∧ X ≫ X = X :=
  ⟨symmetric_eq (coreflexive_symmetric_idempotent hX).1, (coreflexive_symmetric_idempotent hX).2⟩

/-- **Ex 5.17**: `guard C X` is a map (entire and simple) whenever `X` is coreflexive. -/
theorem guard_map {s a : 𝒜} {C : Coproduct s a a} {X : a ⟶ a} (hX : Coreflexive X) :
    Map (guard C X) := by
  have hCX := corNeg_coreflexive X
  obtain ⟨hXsymm, hXidem⟩ := coreflexive_facts hX
  obtain ⟨hCsymm, hCidem⟩ := coreflexive_facts hCX
  have hXC0 : X ≫ corNeg X = 𝟘 := by rw [coreflexive_comp_eq_inter hX hCX, inter_corNeg X]
  have hCX0 : corNeg X ≫ X = 𝟘 := by
    rw [coreflexive_comp_eq_inter hCX hX, Allegory.inter_comm, inter_corNeg X]
  refine ⟨?_, ?_⟩
  · -- Entire: `guard≫guard° = 1`, hence `dom(guard) = 1`.
    show dom (guard C X) = Cat.id a
    have hgg : guard C X ≫ (guard C X)° = Cat.id a := by
      show (junc C X (corNeg X))° ≫ (junc C X (corNeg X))°° = Cat.id a
      rw [Allegory.recip_recip, junc_recip_junc, hXsymm, hCsymm, hXidem, hCidem]
      exact union_corNeg hX
    show Cat.id a ∩ (guard C X ≫ (guard C X)°) = Cat.id a
    rw [hgg, Allegory.inter_idem]
  · -- Simple: `guard°≫guard ⊑ 1_s`.  (`recip_recip` is a propositional `Allegory` axiom, not
    -- a definitional unfolding, so `(guard C X)°` must be turned into `junc C X (corNeg X)` by
    -- an explicit `rw`, not by `show`.)
    have hgr : (guard C X)° = junc C X (corNeg X) := by
      show ((junc C X (corNeg X))°)° = junc C X (corNeg X)
      exact Allegory.recip_recip _
    show (guard C X)° ≫ guard C X ⊑ Cat.id s
    rw [hgr]
    show junc C X (corNeg X) ≫ (junc C X (corNeg X))° ⊑ Cat.id s
    have hJ'exp : (junc C X (corNeg X))° = (X ≫ C.u₁) ∪ (corNeg X ≫ C.u₂) := by
      rw [junc_recip, hXsymm, hCsymm]
    have hX1 : X ≫ (junc C X (corNeg X))° = X ≫ C.u₁ := by
      rw [hJ'exp, DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc, hXidem, hXC0,
        DistributiveAllegory.zero_comp, union_zero]
    have hC2 : corNeg X ≫ (junc C X (corNeg X))° = corNeg X ≫ C.u₂ := by
      rw [hJ'exp, DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc, hCX0, hCidem,
        DistributiveAllegory.zero_comp, DistributiveAllegory.zero_union]
    have hu1 : X ≫ C.u₁ ⊑ C.u₁ := by
      have h := comp_mono_right hX C.u₁; rwa [Cat.id_comp] at h
    have hu2 : corNeg X ≫ C.u₂ ⊑ C.u₂ := by
      have h := comp_mono_right hCX C.u₂; rwa [Cat.id_comp] at h
    have hstep : junc C X (corNeg X) ≫ (junc C X (corNeg X))°
        = junc C (X ≫ C.u₁) (corNeg X ≫ C.u₂) := by
      rw [junc_comp, hX1, hC2]
    rw [hstep, ← junc_injections C]
    exact junc_mono C hu1 hu2

/-- **Ex 5.17**: the conditional `cond C X R S` runs `R` when `X` holds, `S` when `corNeg X`
    holds. -/
def cond {s a b : 𝒜} (C : Coproduct s a a) (X : a ⟶ a) (R S : a ⟶ b) : a ⟶ b :=
  guard C X ≫ junc C R S

/-- `cond` unfolds to the explicit union form `(X≫R) ∪ (corNeg X≫S)`, via the (5.11)
    cancellation law. -/
theorem cond_eq_union {s a b : 𝒜} {C : Coproduct s a a} {X : a ⟶ a} (hX : Coreflexive X)
    (R S : a ⟶ b) : cond C X R S = (X ≫ R) ∪ (corNeg X ≫ S) := by
  obtain ⟨hXsymm, _⟩ := coreflexive_facts hX
  obtain ⟨hCsymm, _⟩ := coreflexive_facts (corNeg_coreflexive X)
  show (junc C X (corNeg X))° ≫ junc C R S = (X ≫ R) ∪ (corNeg X ≫ S)
  rw [junc_recip_junc, hXsymm, hCsymm]

/-- **Ex 5.17**: the universal characterisation of `cond` — `T` refines `cond C X R S` iff its
    `X`-guarded restriction refines `R` and its `corNeg X`-guarded restriction refines `S`. -/
theorem cond_spec {s a b : 𝒜} {C : Coproduct s a a} {X : a ⟶ a} (hX : Coreflexive X)
    (R S : a ⟶ b) (T : a ⟶ b) :
    T ⊑ cond C X R S ↔ (X ≫ T ⊑ R ∧ corNeg X ≫ T ⊑ S) := by
  have hCX := corNeg_coreflexive X
  obtain ⟨_, hXidem⟩ := coreflexive_facts hX
  obtain ⟨_, hCidem⟩ := coreflexive_facts hCX
  have hXC0 : X ≫ corNeg X = 𝟘 := by rw [coreflexive_comp_eq_inter hX hCX, inter_corNeg X]
  have hCX0 : corNeg X ≫ X = 𝟘 := by
    rw [coreflexive_comp_eq_inter hCX hX, Allegory.inter_comm, inter_corNeg X]
  rw [cond_eq_union hX]
  constructor
  · intro hT
    constructor
    · have h1 := comp_mono_left X hT
      rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc, hXidem, hXC0,
        DistributiveAllegory.zero_comp, union_zero] at h1
      have h2 : X ≫ R ⊑ R := by have h := comp_mono_right hX R; rwa [Cat.id_comp] at h
      exact le_trans h1 h2
    · have h1 := comp_mono_left (corNeg X) hT
      rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc, hCX0, hCidem,
        DistributiveAllegory.zero_comp, DistributiveAllegory.zero_union] at h1
      have h2 : corNeg X ≫ S ⊑ S := by have h := comp_mono_right hCX S; rwa [Cat.id_comp] at h
      exact le_trans h1 h2
  · rintro ⟨h1, h2⟩
    have e1 : X ≫ T ⊑ X ≫ R := by
      have h := comp_mono_left X h1; rw [← Cat.assoc, hXidem] at h; exact h
    have e2 : corNeg X ≫ T ⊑ corNeg X ≫ S := by
      have h := comp_mono_left (corNeg X) h2; rw [← Cat.assoc, hCidem] at h; exact h
    have hsplit : T = (X ≫ T) ∪ (corNeg X ≫ T) := by
      calc T = Cat.id a ≫ T := (Cat.id_comp T).symm
        _ = (X ∪ corNeg X) ≫ T := by rw [union_corNeg hX]
        _ = (X ≫ T) ∪ (corNeg X ≫ T) := union_comp_distrib X (corNeg X) T
    rw [hsplit]
    exact union_mono e1 e2

end Guard

-- printing-only unexpander: the book's own spelling of (5.9).  `[R,S]` is the case morphism, and
-- the coproduct it is taken over is the source object's own.  Changes no statement and no
-- `stmt_key`.
open Lean PrettyPrinter in
@[app_unexpander junc] public meta def unexpandJunc : Unexpander
  | `($_ $_ $R $S) => `([$R, $S])
  | _ => throw ()

end Freyd.Alg
