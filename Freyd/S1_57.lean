/-
  Freyd & Scedrov, *Categories and Allegories* §1.57
  Choice objects, AC regular categories, projective objects.

  §1.57  CHOICE: every entire relation targeted at C contains a map.
  AC REGULAR CATEGORY: all objects are choice (⇔ all are projective).
  Equivalent: every morphism factors as left-invertible ∘ monic.
-/


import Freyd.S1_1
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! ## §1.57 Choice and projectivity -/

/-- **§1.57**: C is CHOICE if every entire relation R : A → C contains a map f : A → C.
    (The map condition: 1_A ≤ R°R and there is a section.) -/
def Choice (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (R : BinRel 𝒞 A C), Entire R →
    ∃ (f : A ⟶ C), ∃ (h : A ⟶ R.src), h ≫ R.colA = Cat.id A ∧ h ≫ R.colB = f

/-- C is PROJECTIVE if every cover f : A ↠ C splits (∃ s: C→A with s≫f = id). -/
def Projective (C : 𝒞) : Prop :=
  ∀ {A : 𝒞} (f : A ⟶ C), Cover f → ∃ (s : C ⟶ A), s ≫ f = Cat.id C

/-- Every object is choice iff every object is projective (§1.57). -/
theorem choice_iff_projective : (∀ C : 𝒞, Choice C) ↔ (∀ C : 𝒞, Projective C) := by
  constructor
  · intro h C A f hcov
    -- f: A → C is a cover.  (graph f)°: C → A has left leg = f which is a cover,
    -- hence (graph f)° is entire (by tabulated_is_entire_iff_left_cover).  Apply
    -- Choice at A (the target of the reciprocal) to extract the section.
    have hent : Entire ((graph f)°) :=
      ((tabulated_is_entire_iff_left_cover f (Cat.id A) ((graph f)°).isMonicPair).mpr hcov)
    rcases h A ((graph f)°) hent with ⟨s, k, hkA, hkB⟩
    -- hkA: k ≫ f = id_C,  hkB: k ≫ id_A = s  →  k = s  →  s ≫ f = id_C
    dsimp [graph, reciprocal] at hkA hkB
    rw [Cat.comp_id] at hkB
    -- hkB: k = s, so rewrite the goal (s ≫ f = id_C) to k ≫ f = id_C
    refine ⟨s, ?_⟩
    rw [← hkB]
    exact hkA
  · intro h C A R hent
    -- R entire ⇒ R.colA is a cover (§1.564).  Projective at A splits it,
    -- giving a section s: A → R.src; then s ≫ R.colB: A → C is the map we need.
    have hcov : Cover R.colA :=
      ((tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent)
    rcases h A R.colA hcov with ⟨s, hs⟩
    -- hs: s ≫ R.colA = id_A
    -- The map is s ≫ R.colB: A → C, witness h = s
    refine ⟨s ≫ R.colB, s, hs, rfl⟩

/-- AC REGULAR CATEGORY: all objects are choice. -/
class ACRegularCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasPullbacks 𝒞, HasImages 𝒞 where
  all_choice : ∀ C : 𝒞, Choice C

/-- In an AC regular category, every f factors as p≫m where p is a
    split epi (cover with section) and m is monic. -/
theorem ac_factorization [ACRegularCategory 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    ∃ (C : 𝒞) (p : A ⟶ C) (m : C ⟶ B),
      (∃ (s : C ⟶ A), s ≫ p = Cat.id C) ∧ Monic m ∧ p ≫ m = f := by
  -- Resolve instance diamond: the variable line supplies HasImages etc.,
  -- and ACRegularCategory supplies them again.  Use letI to pick one.
  letI : HasBinaryProducts 𝒞 := ACRegularCategory.toHasBinaryProducts
  letI : HasPullbacks 𝒞 := ACRegularCategory.toHasPullbacks
  letI : HasImages 𝒞 := ACRegularCategory.toHasImages
  -- From all_choice, directly prove all objects are projective
  have h_all_proj : ∀ C : 𝒞, Projective C := by
    intro C A' f' hcov
    have hent : Entire ((graph f')°) :=
      ((tabulated_is_entire_iff_left_cover f' (Cat.id A') ((graph f')°).isMonicPair).mpr hcov)
    rcases ACRegularCategory.all_choice A' ((graph f')°) hent with ⟨s, k, hkA, hkB⟩
    dsimp [graph, reciprocal] at hkA hkB
    rw [Cat.comp_id] at hkB
    -- hkB: k = s, hkA: k ≫ f' = id_C.  Provide s and rewrite to k.
    refine ⟨s, ?_⟩
    rw [← hkB]
    exact hkA
  let I := image f
  -- image.lift f is a cover: if it factors through a monic m, image-minimality
  -- forces m to be iso (standard: image factorizations give cover ∘ monic).
  have h_cover : Cover (image.lift f : A ⟶ I.dom) := by
    intro D m g hm hfac
    -- hfac: g ≫ m = image.lift f, so f = g ≫ (m ≫ I.arr)
    -- The subobject S with arr = m ≫ I.arr allows f via g.
    have hmono_comp : Monic (m ≫ I.arr) := by
      intro W u v huv
      have h1 : u ≫ m = v ≫ m := I.monic _ _ (by
        simpa [Cat.assoc] using huv)
      exact hm _ _ h1
    have h_allows : Allows ⟨D, m ≫ I.arr, hmono_comp⟩ f := by
      refine ⟨g, ?_⟩
      calc g ≫ (m ≫ I.arr) = (g ≫ m) ≫ I.arr := (Cat.assoc _ _ _).symm
        _ = (image.lift f) ≫ I.arr := by rw [hfac]
        _ = f := image.lift_fac f
    have h_le : I.le ⟨D, m ≫ I.arr, hmono_comp⟩ := image_min f _ h_allows
    rcases h_le with ⟨h, hh⟩
    -- hh: h ≫ (m ≫ I.arr) = I.arr
    dsimp at hh
    have hhm : h ≫ m = Cat.id I.dom := I.monic (h ≫ m) (Cat.id I.dom) (by
      calc (h ≫ m) ≫ I.arr = h ≫ (m ≫ I.arr) := Cat.assoc _ _ _
        _ = I.arr := hh
        _ = Cat.id I.dom ≫ I.arr := (Cat.id_comp _).symm)
    have hmh : m ≫ h = Cat.id D := hm (m ≫ h) (Cat.id D) (by
      calc (m ≫ h) ≫ m = m ≫ (h ≫ m) := Cat.assoc _ _ _
        _ = m ≫ Cat.id I.dom := by rw [hhm]
        _ = m := Cat.comp_id _
        _ = Cat.id D ≫ m := (Cat.id_comp _).symm)
    -- IsIso m expects: ∃ g, m ≫ g = id_D ∧ g ≫ m = id_I.dom
    exact ⟨h, hmh, hhm⟩
  -- Split the cover via projectivity
  rcases h_all_proj I.dom (image.lift f) h_cover with ⟨s, hs⟩
  -- hs: s ≫ (image.lift f) = id_I
  refine ⟨I.dom, image.lift f, I.arr, ⟨s, hs⟩, I.monic, image.lift_fac f⟩

/-! ## §1.571 AC regular via idempotent splitting

  Suppose `A` is Cartesian and for every `x : A → B` there exists an idempotent
  `e : A → A` (`e² = e`) with `ex = x` and `e` and `x` have the same level
  (kernel pair).  Then the equalizer of `id_A` and `e` splits `e`, yielding a
  factorization `x = p ≫ n` where `p` is left-invertible and `n` is monic.
  Hence the category is AC regular (alternative definition from §1.57).

  §1.571 — decoding Freyd's paragraph "Let C → A be an equalizer of 1, e …"
  (composition in diagram order: `m;e` means first `m` then `e`).  Let
  `m : C → A` be the equalizer of `id_A` and `e`.
    1. `m` = equalizer of `1, e` — the subobject of fixed points of `e`, where
       `id = e`.  Equalizer maps are monic (`eqMap_mono`).        [`m`, `hm_mono`]
    2. `A → C → A = e` splits the idempotent: `e = p;m` with `p : A → C`.  [`hp_fac`]
    3. `A → C` has left-inverse `C → A`, i.e. `m;p = id_C`, so `p` is
       left-invertible (a cover).  Uses `m;e = m` + monicity of `m`.   [`hm_p`]
    4. `x = A → C → A → B`: from `ex = x` and `e = p;m`, `x = e;x = p;(m;x)`;
       set `n := m;x`, giving `x = p;n`.                                [`hx_fac`]
    5. `C → A → B` is monic: `n = m;x` is monic — the ONLY step using "same
       level".  If `u;n = v;n` then `(u;m, v;m) ∈ ker x = ker e`, so `u;m;e =
       v;m;e`; but `m;e = m`, so `u;m = v;m`, and `m` monic gives `u = v`.
       (Uses only `hle2 : ker x ⊂ ker e`; `_hle1` is discarded.)       [`hn_mono`] -/

section S1_571

variable [CartesianCategory 𝒞]

omit [HasPullbacks 𝒞] [HasImages 𝒞] in
/-- Equalizer maps are monic. -/
theorem eqMap_mono {A B : 𝒞} (f g : A ⟶ B) : Monic (eqMap f g) := eqMap_monic f g

omit [HasImages 𝒞] in  -- §1.572 instantiates this to CONSTRUCT images; no images assumed
/-- **§1.571**: In a Cartesian category, if every morphism admits an idempotent
    with the same level (kernel pair) that stabilizes it, then every morphism
    factors as left-invertible followed by monic — so the category is AC regular.

    §1.571 — why "same level" must be assumed (it is NOT derivable from `e² = e`
    and `ex = x`).  Split `ker e = ker x` into its two inclusions:
      • `ker e ⊆ ker x` IS free from `ex = x`: `u;e = v;e ⇒ u;e;x = v;e;x ⇒ u;x = v;x`
        (this is `_hle1`, the inclusion this proof never uses).
      • `ker x ⊆ ker e` is NOT derivable — it says `x` merges no more than `e`, and
        nothing in `e² = e`, `ex = x` bounds how much `x` collapses (this is `hle2`,
        the inclusion the monicity of `n = m;x` actually consumes).
    Counterexample for the missing direction: take `e = id_A`.  It is idempotent and
    `id;x = x` for EVERY `x`, yet `ker(id) =` diagonal, so "same level" would force
    every `x` monic.  Concretely in Set: `x : {0,1} → {∗}` the constant map has
    `ker x = ⊤` but `ker id =` diagonal.  Intuition: `ex = x` only says `e` fixes `x`
    (and `e = id` fixes everything); the hypothesis is exactly the extra constraint
    that `e`'s fixed-point subobject `C ↣ A` is no bigger than the image of `x`, which
    is what makes the second leg `n = m;x` monic.  With `e = id` we get `C = A`,
    `n = x`, and the factorization degenerates to `x = id;x` with `n` non-monic. -/
theorem ac_factorization_via_idempotent
    (h_exists : ∀ {A B : 𝒞} (x : A ⟶ B), ∃ (e : A ⟶ A),
      e ≫ e = e ∧ e ≫ x = x ∧
      (kernelPairRel e) ⊂ (kernelPairRel x) ∧ (kernelPairRel x) ⊂ (kernelPairRel e))
    {A B : 𝒞} (x : A ⟶ B) : ∃ (C : 𝒞) (p : A ⟶ C) (n : C ⟶ B),
      (∃ (s : C ⟶ A), s ≫ p = Cat.id C) ∧ Monic n ∧ p ≫ n = x := by
  -- The outer variable [HasPullbacks 𝒞] (from line 27) provides the pullback
  -- instance; we use it directly for kernelPair, kp₁, etc.
  rcases h_exists x with ⟨e, hee, hex, _hle1, hle2⟩
  -- Equalizer C ↣ A of id_A and e
  let m := eqMap (Cat.id A) e
  -- e ≫ id = e = e ≫ e, so e lifts through the equalizer
  have he_eq : e ≫ Cat.id A = e ≫ e := by rw [Cat.comp_id, hee]
  let p := eqLift (Cat.id A) e e he_eq
  have hp_fac : p ≫ m = e := eqLift_fac (Cat.id A) e e he_eq
  have hm_eq : m ≫ Cat.id A = m ≫ e := eqMap_eq (Cat.id A) e
  have hm_e : m ≫ e = m := by
    simpa [Cat.comp_id] using hm_eq.symm
  -- m is monic (equalizer maps are monic)
  have hm_mono : Monic m := eqMap_mono (Cat.id A) e
  -- p has left inverse m (since m ≫ e = m, split the idempotent e)
  have hm_p : m ≫ p = Cat.id (eqObj (Cat.id A) e) := by
    apply hm_mono
    calc
      (m ≫ p) ≫ m = m ≫ (p ≫ m) := Cat.assoc _ _ _
      _ = m ≫ e := by rw [hp_fac]
      _ = m := hm_e
      _ = Cat.id _ ≫ m := (Cat.id_comp _).symm
  -- Build the factorization: x = e ≫ x = p ≫ m ≫ x
  let C := eqObj (Cat.id A) e
  let n : C ⟶ B := m ≫ x
  have hx_fac : p ≫ n = x := by
    dsimp [n]
    calc
      p ≫ (m ≫ x) = (p ≫ m) ≫ x := (Cat.assoc _ _ _).symm
      _ = e ≫ x := by rw [hp_fac]
      _ = x := hex
  -- n is monic: proof uses level(x) ⊂ level(e) (hle2)
  have hn_mono : Monic n := by
    intro W u v h
    have h_mx_eq : (u ≫ m) ≫ x = (v ≫ m) ≫ x := by
      dsimp [n] at h; simpa [Cat.assoc] using h
    -- w : W → kernelPair x witnesses (u≫m, v≫m) in ker(x)
    let w := (HasPullbacks.has x x).lift ⟨W, u ≫ m, v ≫ m, h_mx_eq⟩
    have hw1 : w ≫ kp₁ (f := x) = u ≫ m := kp_lift_p₁ (u ≫ m) (v ≫ m) h_mx_eq
    have hw2 : w ≫ kp₂ (f := x) = v ≫ m := kp_lift_p₂ (u ≫ m) (v ≫ m) h_mx_eq
    -- From hle2: kernelPairRel x ⊂ kernelPairRel e, extract the RelHom
    obtain ⟨hrel⟩ := hle2
    obtain ⟨h_map, hA, hB⟩ := hrel
    -- Work with kernelPairRel accessors directly (avoid kp₁/kp₂ conversion issues)
    have hleft : (w ≫ h_map) ≫ (kernelPairRel e).colA = u ≫ m := by
      calc
        (w ≫ h_map) ≫ (kernelPairRel e).colA = w ≫ (h_map ≫ (kernelPairRel e).colA) := Cat.assoc _ _ _
        _ = w ≫ (kernelPairRel x).colA := by rw [hA]
        _ = w ≫ kp₁ (f := x) := by simp [kernelPairRel]
        _ = u ≫ m := hw1
    have hright : (w ≫ h_map) ≫ (kernelPairRel e).colB = v ≫ m := by
      calc
        (w ≫ h_map) ≫ (kernelPairRel e).colB = w ≫ (h_map ≫ (kernelPairRel e).colB) := Cat.assoc _ _ _
        _ = w ≫ (kernelPairRel x).colB := by rw [hB]
        _ = w ≫ kp₂ (f := x) := by simp [kernelPairRel]
        _ = v ≫ m := hw2
    -- Now use kp_sq to relate both sides via kernel-pair properties
    have hae_be : (u ≫ m) ≫ e = (v ≫ m) ≫ e := by
      calc
        (u ≫ m) ≫ e = ((w ≫ h_map) ≫ (kernelPairRel e).colA) ≫ e :=
          (congrArg (· ≫ e) hleft).symm
        _ = ((w ≫ h_map) ≫ (kernelPairRel e).colB) ≫ e := by
          simp [kernelPairRel, Cat.assoc, kp_sq (f := e)]
        _ = (v ≫ m) ≫ e := congrArg (· ≫ e) hright
    -- Simplify via m ≫ e = m: (u ≫ m) ≫ e = u ≫ (m ≫ e) = u ≫ m
    have huv : u ≫ m = v ≫ m := by
      simpa [Cat.assoc, hm_e] using hae_be
    exact hm_mono _ _ huv
  exact ⟨C, p, n, ⟨m, hm_p⟩, hn_mono, hx_fac⟩

end S1_571

end Freyd
