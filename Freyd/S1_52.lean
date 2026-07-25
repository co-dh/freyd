/-
  Freyd & Scedrov, *Categories and Allegories* §1.52  Regular categories,
  well-supported, well-pointed, capital.  §1.52–§1.525.

  RegularCategory: Cartesian + images + pullbacks transfer covers.
  PreRegular: Cartesian + pullbacks transfer covers (images optional).
  WellSupported (§1.522), WellPointed (§1.523), Capital (§1.525).
-/


import Freyd.S1_1
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_43
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_513_CoveringFamily


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.52 Regular and pre-regular categories

  A REGULAR CATEGORY is Cartesian with images where pullbacks transfer
  covers.  A PRE-REGULAR CATEGORY drops the images requirement. -/

/-- Mixin (§1.52): pullbacks transfer covers — the closure condition shared by
    regular and pre-regular categories.  In a pullback square the map opposite
    a cover is a cover; the square must be a pullback, not just commutative
    (in **Set** an empty corner over a commutative square defeats transfer). -/
class PullbacksTransferCovers (𝒞 : Type u) [Cat.{v} 𝒞] where
  pullbacks_transfer_covers : ∀ {A B C : 𝒞} {f : A ⟶ B} {g : C ⟶ B}
    (c : Cone f g), c.IsPullback → Cover f → Cover c.π₂

/-- A regular category: Cartesian, has images, pullbacks transfer covers (§1.52). -/
class RegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞,
    PullbacksTransferCovers 𝒞

/-- A pre-regular category: Cartesian, pullbacks transfer covers (§1.52). -/
class PreRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞,
    PullbacksTransferCovers 𝒞

/-- Every regular category is pre-regular (forget images).  The four shared parents
    (`HasTerminal`/`HasBinaryProducts`/`HasPullbacks`/`PullbacksTransferCovers`) are projected
    directly, so this introduces no new data and merges cleanly with any other `PreRegularCategory`
    instance built from the same parents. -/
instance (priority := 100) RegularCategory.toPreRegularCategory
    {𝒞 : Type u} [Cat.{v} 𝒞] [RegularCategory 𝒞] : PreRegularCategory 𝒞 where
  toHasTerminal := inferInstance
  toHasBinaryProducts := inferInstance
  toHasPullbacks := inferInstance
  toPullbacksTransferCovers := inferInstance

/-- The chosen pullback of a cover along any map is a cover. -/
theorem cover_pullback [hpull : HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]
    {A B C : 𝒞} {f : A ⟶ B} (g : C ⟶ B) (hf : Cover f) :
    Cover (hpull.has f g).cone.π₂ :=
  PullbacksTransferCovers.pullbacks_transfer_covers _ (hpull.has f g).cone_isPullback hf

/-! ## §1.512 Covers are right-cancellable (epic) -/

/-- A cover `f` is **epic** (right-cancellable).  This is the single-morphism
    instance of §1.514's `covering_family_epic`: by `cover_iff_coveringFamily_singleton`,
    `Cover f` is the one-element (`Unit`-indexed) covering family, and a covering
    family is epic through its equalizer subobject.  The equalizers are supplied from
    finite products + pullbacks by `products_pullbacks_implies_equalizers` — given
    locally (it is a `def`, not a global instance, to avoid a `HasEqualizers` diamond
    against `CartesianCategory`). -/
theorem cover_epi [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) {Z : 𝒞} {a b : Y ⟶ Z}
    (hab : f ≫ a = f ≫ b) : a = b :=
  letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  covering_family_epic ((cover_iff_coveringFamily_singleton f).mp hf) a b (fun _ => hab)

variable [HasTerminal 𝒞]

/-- A is WELL-SUPPORTED if A → 1 is a cover (§1.522). -/
def WellSupported (A : 𝒞) : Prop := Cover (term A)

/-- When `B` is well-supported, the projection `fst : C×B → C` is a cover.
    `C×B` with `(snd, fst)` is the pullback of `term B : B → 1` along
    `term C : C → 1` (a product is a pullback over the terminal), and pullbacks
    transfer the cover `term B` to the opposite leg `fst`. -/
theorem prod_fst_cover [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]
    {C B : 𝒞} (hws : WellSupported B) : Cover (fst : prod C B ⟶ C) := by
  have hpb : (⟨prod C B, snd, fst, term_uniq _ _⟩ : Cone (term B) (term C)).IsPullback := by
    intro d
    refine ⟨pair d.π₂ d.π₁, ⟨snd_pair _ _, fst_pair _ _⟩, ?_⟩
    intro v hv₁ hv₂
    exact pair_uniq d.π₂ d.π₁ v hv₂ hv₁
  intro D m g hm hgm
  exact PullbacksTransferCovers.pullbacks_transfer_covers _ hpb hws m g hm hgm

/-- The SUPPORT of A is the image of A → 1 (§1.522, requires HasImages). -/
def Support [HasImages 𝒞] (A : 𝒞) : Subobject 𝒞 one := image (term A)

/-- With images, A is well-supported iff its support is entire. -/
theorem wellSupported_iff_support_entire [HasImages 𝒞] (A : 𝒞) :
    WellSupported A ↔ Subobject.IsEntire (Support A) :=
  cover_iff_image_entire (term A)

/-- A is WELL-POINTED (§1.523): the collection 1 → A jointly covers A.
    Every proper monic into A misses some point 1 → A. -/
def WellPointed (A : 𝒞) : Prop :=
  ∀ {D : 𝒞} (m : D ⟶ A), Monic m → ¬ IsIso m → ∃ (x : one ⟶ A), ¬ ∃ (y : one ⟶ D), y ≫ m = x

/-- Capital (§1.525): every well-supported object is well-pointed. -/
def Capital : Prop := ∀ (A : 𝒞), WellSupported A → WellPointed A

/-! ## Kernel-pair lemmas (requires products and pullbacks too) -/

variable [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

section
variable (S : 𝒞)

private def _pb : HasPullback (term S) (term S) := hpull.has (term S) (term S)

def _kpCone : Cone (term S) (term S) := ⟨_, kp₁ (f:=term S), kp₂ (f:=term S), kp_sq⟩
def _prodCone : Cone (term S) (term S) := ⟨_, fst, snd, term_uniq _ _⟩

/-- kpProdIso : kernelPair(term S) → S×S via product universal property;
    kpProdInv in the other direction via pullback lift. -/
def kpProdIso : kernelPair (term S) ⟶ prod S S :=
  pair (kp₁ (f:=term S)) (kp₂ (f:=term S))

def kpProdInv : prod S S ⟶ kernelPair (term S) := (_pb S).lift (_prodCone S)

@[simp] theorem kpProdInv_fst : kpProdInv S ≫ kp₁ (f:=term S) = fst := (_pb S).lift_fst (_prodCone S)
@[simp] theorem kpProdInv_snd : kpProdInv S ≫ kp₂ (f:=term S) = snd := (_pb S).lift_snd (_prodCone S)

theorem kpProdIso_inv : kpProdIso S ≫ kpProdInv S = Cat.id (kernelPair (term S)) := by
  let u := kpProdIso S ≫ kpProdInv S
  have hu_fst : u ≫ kp₁ (f:=term S) = kp₁ (f:=term S) := by
    dsimp [u]; rw [Cat.assoc, kpProdInv_fst, show kpProdIso S ≫ fst = kp₁ (f:=term S) from fst_pair _ _]
  have hu_snd : u ≫ kp₂ (f:=term S) = kp₂ (f:=term S) := by
    dsimp [u]
    rw [Cat.assoc, kpProdInv_snd, show kpProdIso S ≫ snd = kp₂ (f:=term S) from snd_pair _ _]
  have h_id_lift : (_pb S).lift (_kpCone S) = Cat.id (kernelPair (term S)) :=
    ((_pb S).lift_uniq (_kpCone S) (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm
  calc
    u = (_pb S).lift (_kpCone S) :=
      (_pb S).lift_uniq (_kpCone S) u hu_fst hu_snd
    _ = Cat.id (kernelPair (term S)) := h_id_lift

theorem kpProdInv_iso : kpProdInv S ≫ kpProdIso S = Cat.id (prod S S) := by
  have h := pair_uniq fst snd (kpProdInv S ≫ kpProdIso S)
    (by rw [Cat.assoc, show kpProdIso S ≫ fst = kp₁ (f:=term S) from fst_pair _ _, kpProdInv_fst])
    (by rw [Cat.assoc, show kpProdIso S ≫ snd = kp₂ (f:=term S) from snd_pair _ _, kpProdInv_snd])
  have hid : pair fst snd = Cat.id (prod S S) :=
    (pair_uniq fst snd (Cat.id (prod S S)) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])).symm
  rw [h, hid]

theorem kpProdIso_isIso : IsIso (kpProdIso S) :=
  ⟨kpProdInv S, kpProdIso_inv S, kpProdInv_iso S⟩

theorem kpProdInv_isIso : IsIso (kpProdInv S) :=
  ⟨kpProdIso S, kpProdInv_iso S, kpProdIso_inv S⟩

theorem kp_diag_prod : kp_diag (f:=term S) ≫ kpProdIso S = diag S := by
  let h := kp_diag (f:=term S) ≫ kpProdIso S
  have hfst : h ≫ fst = Cat.id S := by
    dsimp [h]
    rw [Cat.assoc, show kpProdIso S ≫ fst = kp₁ (f:=term S) from fst_pair _ _,
      show kp_diag (f:=term S) ≫ kp₁ (f:=term S) = Cat.id S from
        (HasPullbacks.has (term S) (term S)).lift_fst (diagCone (f := term S))]
  have hsnd : h ≫ snd = Cat.id S := by
    dsimp [h]
    rw [Cat.assoc, show kpProdIso S ≫ snd = kp₂ (f:=term S) from snd_pair _ _,
      show kp_diag (f:=term S) ≫ kp₂ (f:=term S) = Cat.id S from
        (HasPullbacks.has (term S) (term S)).lift_snd (diagCone (f := term S))]
  have h_eq := pair_uniq (Cat.id S) (Cat.id S) h hfst hsnd
  simpa [h, diag] using h_eq

theorem wellSupported_prod_self (S : 𝒞) (hws : WellSupported S) : WellSupported (prod S S) := by
  intro C m g hm hgm
  have h_diag_term : diag S ≫ term (prod S S) = term S := term_uniq _ _
  have h_factor : (diag S ≫ g) ≫ m = term S := by
    rw [Cat.assoc, hgm, h_diag_term]
  exact hws m (diag S ≫ g) hm h_factor

end

/-- §1.525: in a capital category the terminator is projective.
    Every well-supported A has a point 1 → A. -/
theorem capital_implies_one_projective
    (hcap : Capital (𝒞 := 𝒞)) (A : 𝒞) (hws : WellSupported A) :
    Nonempty (one ⟶ A) := by
  -- 1. If A → 1 is iso, use the inverse.
  by_cases hiso : IsIso (term A)
  · obtain ⟨inv, _, _⟩ := hiso
    exact Nonempty.intro inv
  · -- 2. A → 1 is a cover but not iso.  By monic-cover-iso (1.512), it is not monic.
    have h_not_monic : ¬ Monic (term A) := by
      intro hm
      apply hiso
      exact monic_cover_iso (term A) hws hm
    -- 3. Hence kp_diag(term A) is not iso (1.453: monic_iff_kp_diag_iso).
    --    Via kpProdIso, diag A is also not iso — a proper monic.
    have h_not_iso_kp : ¬ IsIso (kp_diag (f:=term A)) :=
      mt ((monic_iff_kp_diag_iso (f:=term A)).mpr) h_not_monic
    have h_not_iso_diag : ¬ IsIso (diag A) := by
      intro hiso_diag; apply h_not_iso_kp
      have hkp : kp_diag (f:=term A) = diag A ≫ kpProdInv A := by
        rw [← kp_diag_prod A, Cat.assoc, kpProdIso_inv A, Cat.comp_id]
      rw [hkp]
      exact isIso_comp hiso_diag (kpProdInv_isIso A)
    have hm_diag : Monic (diag A) := diag_mono A
    -- 4. A×A is well-supported — via the diagonal, no pullbacks needed.
    have hwsAA : WellSupported (prod A A) := wellSupported_prod_self A hws
    -- 5. By capital, A×A is well-pointed.
    have hwpAA : WellPointed (prod A A) := hcap (prod A A) hwsAA
    -- 6. Apply well-pointed to the proper monic Δ : ∃ x:1→A×A.
    obtain ⟨x, _⟩ := hwpAA (diag A) hm_diag h_not_iso_diag
    -- 7. Compose x with π₁ : 1 → A.
    exact Nonempty.intro (x ≫ fst)

/-! ## §1.524 Projective objects

  An object P is PROJECTIVE if the representable functor (P, -) preserves covers:
  every cover f : A ↠ P has a splitting s : P → A with s ≫ f = id_P.
  NOTE: `Projective` is formally defined in §1.57 (Freyd/S1_57.lean) together with
  the Choice–Projective equivalence.  We record the key consequence here. -/

/-- §1.524 + §1.525: in a capital pre-regular category the terminator 1 is projective
    — every cover `e : A ↠ 1` has a section.  Proof: `capital_implies_one_projective`
    gives `1 → A`; the equation holds by `term_uniq` since everything maps to 1 uniquely. -/
theorem capital_one_projective
    [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]
    (hcap : Capital (𝒞 := 𝒞))
    {A : 𝒞} {e : A ⟶ one} (he : Cover e) :
    ∃ (s : one ⟶ A), s ≫ e = Cat.id one := by
  have hterm : e = term A := term_uniq e _
  subst hterm
  obtain ⟨s⟩ := capital_implies_one_projective hcap A he
  exact ⟨s, term_uniq _ _⟩

/-! ### §1.524 (Set illustration)  A left inverse of a cover is unique up to iso over the base

  §1.524 gives a cover targeted at a projective object a left inverse (a section); that section is
  not unique.  In `Set`, however, any two sections of a surjection are related by an automorphism of
  the total space *over the base* — the canonical fibrewise transposition swapping the two chosen
  points in each fibre.  (Special to `Set`: it fails in `Top`, where the Sierpiński cover `S ↠ ∗` has
  two sections related by no homeomorphism.)  A concrete `Type`-level statement, independent of the
  abstract `Cat` development above. -/

/-- The fibrewise transposition over `c` swapping `s p` and `t p` in each fibre. -/
def fibreSwap {C P : Type u} [DecidableEq C] (c : C → P) (s t : P → C) : C → C :=
  fun x => if x = s (c x) then t (c x) else if x = t (c x) then s (c x) else x

/-- Two sections of a surjection in `Set` are related by an automorphism over the base.
    So a left inverse of a cover is unique up to iso over the base. -/
theorem section_unique_up_to_iso_over_base
    {C P : Type u} (c : C → P) (s t : P → C)
    (hs : ∀ p, c (s p) = p) (ht : ∀ p, c (t p) = p) :
    ∃ φ : C → C,
      (Function.Injective φ ∧ Function.Surjective φ) ∧
      (∀ x, c (φ x) = c x) ∧
      (∀ p, φ (s p) = t p) := by
  classical
  have hbase : ∀ x, c (fibreSwap c s t x) = c x := by
    intro x
    simp only [fibreSwap]
    by_cases h1 : x = s (c x)
    · rw [if_pos h1, ht]
    · rw [if_neg h1]
      by_cases h2 : x = t (c x)
      · rw [if_pos h2, hs]
      · rw [if_neg h2]
  have hst : ∀ p, fibreSwap c s t (s p) = t p := by
    intro p
    simp only [fibreSwap, hs p, if_true]
  have hinv : ∀ x, fibreSwap c s t (fibreSwap c s t x) = x := by
    intro x
    by_cases h1 : x = s (c x)
    · by_cases h2 : x = t (c x)
      · simp only [fibreSwap]
        rw [if_pos h1]
        have hctp : c (t (c x)) = c x := ht (c x)
        rw [hctp, ← h1, if_pos h2.symm]
        exact h2.symm
      · simp only [fibreSwap]
        rw [if_pos h1]
        have hctp : c (t (c x)) = c x := ht (c x)
        rw [hctp, ← h1, if_neg (Ne.symm h2), if_pos rfl]
    · by_cases h2 : x = t (c x)
      · simp only [fibreSwap]
        rw [if_neg h1, if_pos h2]
        have hcsp : c (s (c x)) = c x := hs (c x)
        rw [hcsp, if_pos rfl, ← h2]
      · simp only [fibreSwap]
        rw [if_neg h1, if_neg h2]
        rw [if_neg h1, if_neg h2]
  refine ⟨fibreSwap c s t, ⟨?_, ?_⟩, hbase, hst⟩
  · intro a b h
    have h2 := congrArg (fibreSwap c s t) h
    rwa [hinv, hinv] at h2
  · intro y
    exact ⟨fibreSwap c s t y, hinv y⟩

/-! ## §1.52 Representation of pre-regular categories

  A REPRESENTATION OF PRE-REGULAR CATEGORIES is a functor that preserves
  finite products (terminal + binary products), equalizers, and covers (§1.52). -/

/-- A functor `F : 𝒞 → 𝒟` PRESERVES COVERS if it carries every cover to a cover. -/
def PreservesCovers {𝒞 : Type u₁} {𝒟 : Type u₂} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Cover f → Cover (F.map f)

/-- **§1.52 REPRESENTATION OF PRE-REGULAR CATEGORIES**: a functor between
    pre-regular categories preserving finite products, equalizers, and covers.
    (This is the standard notion; a functor preserving these necessarily
    preserves whatever images may exist.) -/
structure RepOfPreReg {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    [CartesianCategory 𝒞] [CartesianCategory 𝒟]
    (F : Functor 𝒞 𝒟) : Prop where
  cartesian  : CartesianFunctor F
  pres_covers : PreservesCovers F

/-! ## §1.526 The points functor is a representation in a capital category

  In a capital pre-regular category the functor `Γ := (1 ⟶ -)` is a representation
  of pre-regular categories (§1.526).  We record its key preservation properties
  here as type-theoretic statements (Γ lands in Type, not back in 𝒞). -/

/-- §1.526 (terminal): `Γ(1) = (1 ⟶ 1)` is a singleton — has exactly one element. -/
theorem pts_terminal_unique [ht : HasTerminal 𝒞]
    (f g : one ⟶ (one : 𝒞)) : f = g :=
  term_uniq f g

/-- §1.526 (products): `Γ(A × B) → Γ(A) × Γ(B)` given by `x ↦ (x ≫ fst, x ≫ snd)` and
    `Γ(A) × Γ(B) → Γ(A × B)` given by `(a, b) ↦ pair a b` are mutually inverse. -/
theorem pts_prod_iso_left [hp : HasBinaryProducts 𝒞] {A B : 𝒞}
    (a : one ⟶ A) (b : one ⟶ B) :
    pair a b ≫ fst = a ∧ pair a b ≫ snd = b :=
  ⟨fst_pair a b, snd_pair a b⟩

theorem pts_prod_iso_right [hp : HasBinaryProducts 𝒞] {A B : 𝒞}
    (x : one ⟶ prod A B) :
    pair (x ≫ fst) (x ≫ snd) = x :=
  (pair_uniq (x ≫ fst) (x ≫ snd) x rfl rfl).symm

/-- §1.526 (covers): in a capital pre-regular category, `Γ = (1 ⟶ -)` preserves
    covers — if `f : X ↠ Y` is a cover then every point `y : 1 → Y` lifts to a
    point `x : 1 → X` with `x ≫ f = y`.  This is precisely that 1 is projective,
    which follows from capital (§1.525). -/
theorem pts_covers_of_capital
    [PullbacksTransferCovers 𝒞]
    (hcap : Capital (𝒞 := 𝒞))
    {X Y : 𝒞} {f : X ⟶ Y} (hf : Cover f) (y : one ⟶ Y) :
    ∃ (x : one ⟶ X), x ≫ f = y := by
  -- Pull f back along y.  The pullback leg π₂ : P → 1 is a cover (pullbacks transfer
  -- covers), and 1 is projective in a capital category, so π₂ splits.
  -- Then s ≫ π₁ : 1 → X is the desired lift.
  have hcov_π₂ : Cover (hpull.has f y).cone.π₂ := cover_pullback y hf
  obtain ⟨s, hs⟩ := capital_one_projective hcap hcov_π₂
  exact ⟨s ≫ (hpull.has f y).cone.π₁,
         by rw [Cat.assoc, (hpull.has f y).cone.w, ← Cat.assoc, hs, Cat.id_comp]⟩

/-! ## §1.521 The functor category 𝒮^A is regular

  For a small category A, the functor category 𝒮^A (presheaves on A, where 𝒮 = Set)
  is regular and the evaluation functors (ev_a : 𝒮^A → 𝒮 for a ∈ A) form a
  collectively faithful family of representations of regular categories.

  NOTE: This requires natural-transformation infrastructure (𝒮^A as a Cat instance,
  limits/colimits pointwise).  The codebase has no NatTrans type yet; this is
  recorded as MISSING in S1_52.md until that infrastructure exists. -/

end Freyd
