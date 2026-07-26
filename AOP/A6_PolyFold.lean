/-
  **Generic relational catamorphism (`foldR`) for polynomial functors** — a port of AoPA's
  `Data.Generic.Fold` into `Rel(Set)`.

  `fold`/`foldRel` are the functional and relational catamorphisms of a `PolyF` code.  The headline
  facts, matching the Agda file line-for-line (aopa name in a comment on each):

  * `fold_computation`, `fold_universal_le/ge`, `fold_fusion` — the functional universal property.
  * `mapFold_bimap` — `mapFoldR F G R = fmapR G (foldR F R)` (aopa `mapFold-bimap`).
  * `foldR_computation`(`'`) — `In ≫ ⦇R⦈ = ⟦F⟧⦇R⦈ ≫ R` (aopa `foldR-computation`).
  * `foldR_universal_le/ge` — the relational universal property (aopa `foldR-universal-⇐`).
  * `foldR_monotonic`, `foldR_fusion` — aopa `foldR-monotonic`, `foldR-fusion`.
  * `idR_foldR` — `𝟙 = ⦇graph In⦈` (aopa `idR-foldR`).

  These specialize, at the list code `oplus one (otimes arg₁ arg₂)`, to the per-datatype
  `A6_GenFold`/`A6_ConsList` fold-uniqueness laws (`consFold_unique` etc.); `A6_Poly_List.lean`
  makes the correspondence formal.  Composition is diagram order (`X ○ Y ↦ Y ≫ X`).
-/
import AOP.A6_Poly

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Poly

open Freyd Freyd.Alg.RelSet

/-! ## Functional catamorphism -/

mutual
/-- aopa `fold`. -/
def fold (F : PolyF) {A B : Type} (f : sem F A B → B) : Mu F A → B
  | .In body => f (mapFoldBody F F f body)
/-- aopa `mapFold` (defined on `Body`, where the recursive occurrence is structural). -/
def mapFoldBody (F G : PolyF) {A B : Type} (f : sem F A B → B) : Body F A G → sem G A B
  | .unit      => PUnit.unit
  | .fst a     => a
  | .snd x     => fold F f x
  | .inl y     => Sum.inl (mapFoldBody F _ f y)
  | .inr y     => Sum.inr (mapFoldBody F _ f y)
  | .pair x y  => (mapFoldBody F _ f x, mapFoldBody F _ f y)
end

/-- `mapFold F G f = bimap G id (fold F f)` (the content aopa folds into `mapFold`'s definition). -/
theorem mapFoldBody_eq (F G : PolyF) {A B : Type} (f : sem F A B → B) :
    ∀ body : Body F A G, mapFoldBody F G f body = bimap G id (fold F f) (toSem G body)
  | .unit      => rfl
  | .fst a     => rfl
  | .snd m     => rfl
  | .inl b     => congrArg Sum.inl (mapFoldBody_eq F _ f b)
  | .inr b     => congrArg Sum.inr (mapFoldBody_eq F _ f b)
  | .pair x y  => Prod.ext (mapFoldBody_eq F _ f x) (mapFoldBody_eq F _ f y)

/-- aopa `fold-computation`: `fold F f (In s) = f (⟦F⟧ id (fold F f) s)`. -/
theorem fold_computation (F : PolyF) {A B : Type} (f : sem F A B → B) (s : sem F A (Mu F A)) :
    fold F f (In s) = f (bimap F id (fold F f) s) := by
  show f (mapFoldBody F F f (ofSem F s)) = f (bimap F id (fold F f) s)
  rw [mapFoldBody_eq, toSem_ofSem]

/-! ## Relational catamorphism (`foldR`) -/

mutual
/-- aopa `foldR`.  `foldRel F R (In s) y` iff some `⟦F⟧`-structure `ys` of child-results folds to
    `y` under the algebra `R` (`R ys y`). -/
def foldRel (F : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩
  | .In body, y => ∃ ys : sem F A B, mapFoldRelBody F F R body ys ∧ R ys y
/-- aopa `mapFoldR`, over `Body` (structural recursive occurrence). -/
def mapFoldRelBody (F G : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    Body F A G → sem G A B → Prop
  | .unit,     _         => True
  | .fst a,    a'        => a = a'
  | .snd m,    y         => foldRel F R m y
  | .inl b,    Sum.inl y => mapFoldRelBody F _ R b y
  | .inr b,    Sum.inr y => mapFoldRelBody F _ R b y
  | .inl _,    Sum.inr _ => False
  | .inr _,    Sum.inl _ => False
  | .pair x y, (u, v)    => mapFoldRelBody F _ R x u ∧ mapFoldRelBody F _ R y v
end

/-- aopa `mapFoldR` presented over `⟦G⟧`, via the `Body ≅ ⟦G⟧` iso. -/
def mapFoldRel (F G : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    Fo G ⟨A⟩ ⟨Mu F A⟩ ⟶ Fo G ⟨A⟩ ⟨B⟩ :=
  fun s y => mapFoldRelBody F G R (ofSem G s) y

/-- aopa `mapFold-bimap`: `mapFoldR F G R = ⟦G⟧ ⦇R⦈`. -/
theorem mapFold_bimap (F G : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    mapFoldRel F G R = fmapR G (foldRel F R) := by
  induction G with
  | zer => apply hom_ext; intro s; exact (s : Empty).elim
  | one => apply hom_ext; intro s y; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | arg₁ => apply hom_ext; intro s y; exact Iff.rfl
  | arg₂ => apply hom_ext; intro s y; exact Iff.rfl
  | oplus l r ihl ihr =>
      apply hom_ext; intro s y
      cases s with
      | inl x => cases y with
        | inl y' => exact iff_of_eq (congrFun (congrFun ihl x) y')
        | inr y' => exact Iff.rfl
      | inr x => cases y with
        | inl y' => exact Iff.rfl
        | inr y' => exact iff_of_eq (congrFun (congrFun ihr x) y')
  | otimes l r ihl ihr =>
      apply hom_ext; intro s y
      have el := iff_of_eq (congrFun (congrFun ihl s.1) y.1)
      have er := iff_of_eq (congrFun (congrFun ihr s.2) y.2)
      exact ⟨fun h => ⟨el.mp h.1, er.mp h.2⟩, fun h => ⟨el.mpr h.1, er.mpr h.2⟩⟩

/-! ### The `In` isomorphism -/

/-- `In` is an isomorphism: `In° ≫ In = 𝟙` on `μ F A`. -/
theorem In_iso (F : PolyF) {A : Type} :
    (inGraph F A)° ≫ inGraph F A = Cat.id (⟨Mu F A⟩ : RelSet.{0}) := by
  apply hom_ext; intro m m'
  constructor
  · rintro ⟨s, hms, hm's⟩
    have hms' : m = In s := hms
    have hm's' : m' = In s := hm's
    exact hms'.trans hm's'.symm
  · intro h
    have hmm : m = m' := h
    refine ⟨out m, (In_out m).symm, ?_⟩
    rw [← hmm]; exact (In_out m).symm

/-! ### Computation rules -/

/-- aopa `foldR-computation`: `In ≫ ⦇R⦈ = ⟦F⟧⦇R⦈ ≫ R`. -/
theorem foldR_computation (F : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    inGraph F A ≫ foldRel F R = fmapR F (foldRel F R) ≫ R := by
  rw [show inGraph F A = graph In from rfl, graph_comp_left]
  apply hom_ext; intro s y
  show foldRel F R (In s) y ↔ (fmapR F (foldRel F R) ≫ R) s y
  have hb := fun ys => iff_of_eq (congrFun (congrFun (mapFold_bimap F F R) s) ys)
  constructor
  · rintro ⟨ys, hmf, hR⟩; exact ⟨ys, (hb ys).mp hmf, hR⟩
  · rintro ⟨ys, hf, hR⟩; exact ⟨ys, (hb ys).mpr hf, hR⟩

theorem foldR_computation_le (F : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    inGraph F A ≫ foldRel F R ⊑ fmapR F (foldRel F R) ≫ R := Freyd.Alg.le_of_eq (foldR_computation F R)

theorem foldR_computation_ge (F : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    fmapR F (foldRel F R) ≫ R ⊑ inGraph F A ≫ foldRel F R := Freyd.Alg.le_of_eq (foldR_computation F R).symm

/-- aopa `foldR-computation'`: `⦇R⦈ = In° ≫ ⟦F⟧⦇R⦈ ≫ R`. -/
theorem foldR_computation' (F : PolyF) {A B : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) :
    foldRel F R = (inGraph F A)° ≫ fmapR F (foldRel F R) ≫ R := by
  rw [← foldR_computation, ← Cat.assoc, In_iso, Cat.id_comp]

/-! ### Relational universal property (aopa `foldR-universal-⇐`) -/

mutual
/-- The `⊑` half of `foldR-universal-⇐`, over `Mu`. -/
theorem foldR_universal_le_go (F : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : inGraph F A ≫ S ⊑ fmapR F S ≫ R) : ∀ (m : Mu F A) (y : B), S m y → foldRel F R m y
  | .In body, y, hSmy => by
      have e1 : In (toSem F body) = Mu.In body := by
        show Mu.In (ofSem F (toSem F body)) = Mu.In body; rw [ofSem_toSem]
      have hin : (inGraph F A ≫ S) (toSem F body) y := ⟨Mu.In body, e1.symm, hSmy⟩
      obtain ⟨ys, hfs, hR⟩ := le_iff.mp hom (toSem F body) y hin
      exact ⟨ys, mapFoldR_univ_le_go F F S R hom body ys hfs, hR⟩
/-- The `⊑` half's `mapFold` helper, over `Body`. -/
theorem mapFoldR_univ_le_go (F G : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : inGraph F A ≫ S ⊑ fmapR F S ≫ R) :
    ∀ (body : Body F A G) (ys : sem G A B), fmapR G S (toSem G body) ys → mapFoldRelBody F G R body ys
  | .unit,     _,         _ => trivial
  | .fst a,    a',        h => h
  | .snd m,    y,         h => foldR_universal_le_go F S R hom m y h
  | .inl b,    Sum.inl y, h => mapFoldR_univ_le_go F _ S R hom b y h
  | .inr b,    Sum.inr y, h => mapFoldR_univ_le_go F _ S R hom b y h
  | .inl _,    Sum.inr _, h => (h : False).elim
  | .inr _,    Sum.inl _, h => (h : False).elim
  | .pair x y, (u, v),    h =>
      ⟨mapFoldR_univ_le_go F _ S R hom x u h.1, mapFoldR_univ_le_go F _ S R hom y v h.2⟩
end

/-- aopa `foldR-universal-⇐-⊑`: `In ≫ S ⊑ ⟦F⟧S ≫ R → S ⊑ ⦇R⦈`. -/
theorem foldR_universal_le (F : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : inGraph F A ≫ S ⊑ fmapR F S ≫ R) : S ⊑ foldRel F R :=
  le_iff.mpr (foldR_universal_le_go F S R hom)

mutual
/-- The `⊒` half of `foldR-universal-⇐`, over `Mu`. -/
theorem foldR_universal_ge_go (F : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : fmapR F S ≫ R ⊑ inGraph F A ≫ S) : ∀ (m : Mu F A) (y : B), foldRel F R m y → S m y
  | .In body, y, hfold => by
      obtain ⟨ys, mF, hR⟩ := hfold
      have hfs : fmapR F S (toSem F body) ys := mapFoldR_univ_ge_go F F S R hom body ys mF
      obtain ⟨m', hm', hSm'⟩ := le_iff.mp hom (toSem F body) y ⟨ys, hfs, hR⟩
      have e1 : In (toSem F body) = Mu.In body := by
        show Mu.In (ofSem F (toSem F body)) = Mu.In body; rw [ofSem_toSem]
      have : m' = Mu.In body := hm'.trans e1
      exact this ▸ hSm'
/-- The `⊒` half's `mapFold` helper, over `Body`. -/
theorem mapFoldR_univ_ge_go (F G : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : fmapR F S ≫ R ⊑ inGraph F A ≫ S) :
    ∀ (body : Body F A G) (ys : sem G A B), mapFoldRelBody F G R body ys → fmapR G S (toSem G body) ys
  | .unit,     _,         _ => trivial
  | .fst a,    a',        h => h
  | .snd m,    y,         h => foldR_universal_ge_go F S R hom m y h
  | .inl b,    Sum.inl y, h => mapFoldR_univ_ge_go F _ S R hom b y h
  | .inr b,    Sum.inr y, h => mapFoldR_univ_ge_go F _ S R hom b y h
  | .inl _,    Sum.inr _, h => (h : False).elim
  | .inr _,    Sum.inl _, h => (h : False).elim
  | .pair x y, (u, v),    h =>
      ⟨mapFoldR_univ_ge_go F _ S R hom x u h.1, mapFoldR_univ_ge_go F _ S R hom y v h.2⟩
end

/-- aopa `foldR-universal-⇐-⊒`: `⟦F⟧S ≫ R ⊑ In ≫ S → ⦇R⦈ ⊑ S`. -/
theorem foldR_universal_ge (F : PolyF) {A B : Type} (S : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (hom : fmapR F S ≫ R ⊑ inGraph F A ≫ S) : foldRel F R ⊑ S :=
  le_iff.mpr (foldR_universal_ge_go F S R hom)

/-- aopa `foldR-monotonic`: `R ⊑ S → ⦇R⦈ ⊑ ⦇S⦈`. -/
theorem foldR_monotonic (F : PolyF) {A B : Type} (R S : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (h : R ⊑ S) : foldRel F R ⊑ foldRel F S :=
  foldR_universal_le F (foldRel F R) S
    (le_trans (foldR_computation_le F R) (comp_mono_left _ h))

/-- The polynomial functor preserves the identity relation: `⟦F⟧ 𝟙 𝟙 = 𝟙`. -/
theorem bimapR_id (F : PolyF) (a b : RelSet.{0}) :
    bimapR F (Cat.id a) (Cat.id b) = Cat.id (Fo F a b) := by
  induction F with
  | zer => apply hom_ext; intro u; exact (u : Empty).elim
  | one => apply hom_ext; intro u v; exact ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩
  | arg₁ => apply hom_ext; intro _ _; exact Iff.rfl
  | arg₂ => apply hom_ext; intro _ _; exact Iff.rfl
  | oplus l r ihl ihr =>
      apply hom_ext; intro u v
      cases u with
      | inl x => cases v with
        | inl y =>
            have hh := iff_of_eq (congrFun (congrFun ihl x) y)
            exact ⟨fun h => congrArg Sum.inl (hh.mp h), fun h => hh.mpr (Sum.inl.inj h)⟩
        | inr y =>
            constructor
            · intro h; exact (h : False).elim
            · intro h; change Sum.inl x = Sum.inr y at h; contradiction
      | inr x => cases v with
        | inl y =>
            constructor
            · intro h; exact (h : False).elim
            · intro h; change Sum.inr x = Sum.inl y at h; contradiction
        | inr y =>
            have hh := iff_of_eq (congrFun (congrFun ihr x) y)
            exact ⟨fun h => congrArg Sum.inr (hh.mp h), fun h => hh.mpr (Sum.inr.inj h)⟩
  | otimes l r ihl ihr =>
      apply hom_ext; intro u v
      have el := iff_of_eq (congrFun (congrFun ihl u.1) v.1)
      have er := iff_of_eq (congrFun (congrFun ihr u.2) v.2)
      constructor
      · intro h; exact Prod.ext (el.mp h.1) (er.mp h.2)
      · intro h
        have hp : u = v := h
        exact ⟨el.mpr (congrArg Prod.fst hp), er.mpr (congrArg Prod.snd hp)⟩

/-- aopa `idR-foldR`: `𝟙 = ⦇graph In⦈`. -/
theorem idR_foldR (F : PolyF) {A : Type} :
    Cat.id (⟨Mu F A⟩ : RelSet.{0}) = foldRel F (inGraph F A) := by
  have hbid : fmapR F (Cat.id (⟨Mu F A⟩ : RelSet.{0})) = Cat.id (Fo F ⟨A⟩ ⟨Mu F A⟩) :=
    bimapR_id F ⟨A⟩ ⟨Mu F A⟩
  have key : inGraph F A ≫ Cat.id (⟨Mu F A⟩ : RelSet.{0})
      = fmapR F (Cat.id (⟨Mu F A⟩ : RelSet.{0})) ≫ inGraph F A := by
    rw [Cat.comp_id, hbid, Cat.id_comp]
  exact le_antisymm
    (foldR_universal_le F (Cat.id _) (inGraph F A) (Freyd.Alg.le_of_eq key))
    (foldR_universal_ge F (Cat.id _) (inGraph F A) (Freyd.Alg.le_of_eq key.symm))

/-! ### Fusion (aopa `foldR-fusion`) -/

/-- aopa `foldR-fusion-⊑`: `S ≫ R ⊑ ⟦F⟧S ≫ T → ⦇R⦈ ≫ S ⊑ ⦇T⦈`. -/
theorem foldR_fusion_le (F : PolyF) {A B C : Type} (S : (⟨B⟩ : RelSet.{0}) ⟶ ⟨C⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) (T : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0}))
    (hyp : R ≫ S ⊑ fmapR F S ≫ T) : foldRel F R ≫ S ⊑ foldRel F T := by
  refine foldR_universal_le F (foldRel F R ≫ S) T ?_
  rw [← Cat.assoc, foldR_computation, Cat.assoc, ← fmapR_functor F ⟨A⟩ (foldRel F R) S, Cat.assoc]
  exact comp_mono_left _ hyp

/-- aopa `foldR-fusion-⊒`: `⟦F⟧S ≫ T ⊑ S ≫ R → ⦇T⦈ ⊑ ⦇R⦈ ≫ S`. -/
theorem foldR_fusion_ge (F : PolyF) {A B C : Type} (S : (⟨B⟩ : RelSet.{0}) ⟶ ⟨C⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) (T : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0}))
    (hyp : fmapR F S ≫ T ⊑ R ≫ S) : foldRel F T ⊑ foldRel F R ≫ S := by
  refine foldR_universal_ge F (foldRel F R ≫ S) T ?_
  rw [← Cat.assoc, foldR_computation, Cat.assoc, ← fmapR_functor F ⟨A⟩ (foldRel F R) S, Cat.assoc]
  exact comp_mono_left _ hyp

/-- aopa `foldR-fusion-≑`: `S ≫ R = ⟦F⟧S ≫ T → ⦇R⦈ ≫ S = ⦇T⦈`. -/
theorem foldR_fusion (F : PolyF) {A B C : Type} (S : (⟨B⟩ : RelSet.{0}) ⟶ ⟨C⟩)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) (T : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0}))
    (hyp : R ≫ S = fmapR F S ≫ T) : foldRel F R ≫ S = foldRel F T :=
  le_antisymm (foldR_fusion_le F S R T (Freyd.Alg.le_of_eq hyp)) (foldR_fusion_ge F S R T (Freyd.Alg.le_of_eq hyp.symm))

/-! ## Functional fold: universal property and fusion (aopa `fold-universal`, `fold-fusion`) -/

mutual
/-- The `⇐` half of `fold-universal`, over `Mu`. -/
theorem fold_univ_le_go (F : PolyF) {A B : Type} (h : Mu F A → B) (f : sem F A B → B)
    (hom : ∀ s, h (In s) = f (bimap F id h s)) : ∀ m, h m = fold F f m
  | .In body => by
      have e1 : In (toSem F body) = Mu.In body := by
        show Mu.In (ofSem F (toSem F body)) = Mu.In body; rw [ofSem_toSem]
      have hh := hom (toSem F body); rw [e1] at hh
      have hb := mapFold_univ_le_go F F h f hom body
      show h (Mu.In body) = f (mapFoldBody F F f body)
      rw [hh, hb]
/-- The `⇐` half's `mapFold` helper, over `Body`. -/
theorem mapFold_univ_le_go (F G : PolyF) {A B : Type} (h : Mu F A → B) (f : sem F A B → B)
    (hom : ∀ s, h (In s) = f (bimap F id h s)) :
    ∀ body : Body F A G, bimap G id h (toSem G body) = mapFoldBody F G f body
  | .unit     => rfl
  | .fst a    => rfl
  | .snd m    => fold_univ_le_go F h f hom m
  | .inl b    => congrArg Sum.inl (mapFold_univ_le_go F _ h f hom b)
  | .inr b    => congrArg Sum.inr (mapFold_univ_le_go F _ h f hom b)
  | .pair x y => Prod.ext (mapFold_univ_le_go F _ h f hom x) (mapFold_univ_le_go F _ h f hom y)
end

/-- aopa `fold-universal-⇐`: `h ∘ In ≐ f ∘ ⟦F⟧id h → h ≐ fold F f`. -/
theorem fold_universal_le (F : PolyF) {A B : Type} (h : Mu F A → B) (f : sem F A B → B)
    (hom : ∀ s, h (In s) = f (bimap F id h s)) : h = fold F f :=
  funext (fold_univ_le_go F h f hom)

/-- aopa `fold-universal-⇒`: `h ≐ fold F f → h ∘ In ≐ f ∘ ⟦F⟧id h`. -/
theorem fold_universal_ge (F : PolyF) {A B : Type} (h : Mu F A → B) (f : sem F A B → B)
    (hh : h = fold F f) (s : sem F A (Mu F A)) : h (In s) = f (bimap F id h s) := by
  rw [hh]; exact fold_computation F f s

/-- aopa `fold-fusion`: `h ∘ f ≐ g ∘ ⟦F⟧id h → h ∘ fold F f ≐ fold F g`. -/
theorem fold_fusion (F : PolyF) {A B C : Type} (h : B → C) (f : sem F A B → B) (g : sem F A C → C)
    (hyp : ∀ x, h (f x) = g (bimap F id h x)) : (fun m => h (fold F f m)) = fold F g := by
  refine fold_universal_le F (fun m => h (fold F f m)) g (fun s => ?_)
  show h (fold F f (In s)) = g (bimap F id (fun m => h (fold F f m)) s)
  rw [fold_computation, hyp]
  congr 1
  exact (bimap_comp F id h id (fold F f) s).symm

/-! ## Fold of a function is the relational fold of its graph -/

/-- aopa `foldR-fun`: `graph (fold F f) = ⦇graph f⦈`.  (aopa leaves this a `postulate`; it is a
    genuine theorem here — a `≐`/`≑` bookkeeping issue only.) -/
theorem foldR_fun (F : PolyF) {A B : Type} (f : sem F A B → B) :
    (graph (fold F f) : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩) = foldRel F (graph f) := by
  have hom_eq : inGraph F A ≫ graph (fold F f) = fmapR F (graph (fold F f)) ≫ graph f := by
    rw [← fmap_fmapR, show inGraph F A = graph In from rfl, graph_comp_left, graph_comp_left]
    apply hom_ext; intro s y
    show (y = fold F f (In s)) ↔ (y = f (fmap F (fold F f) s))
    rw [fold_computation]; exact Iff.rfl
  exact le_antisymm
    (foldR_universal_le F (graph (fold F f)) (graph f) (Freyd.Alg.le_of_eq hom_eq))
    (foldR_universal_ge F (graph (fold F f)) (graph f) (Freyd.Alg.le_of_eq hom_eq.symm))

/-- aopa `foldR-fold`: `graph f ⊑ R → graph (fold F f) ⊑ ⦇R⦈`. -/
theorem foldR_fold (F : PolyF) {A B : Type} (f : sem F A B → B)
    (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (h : (graph f : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0})) ⊑ R) :
    (graph (fold F f) : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨B⟩) ⊑ foldRel F R :=
  le_trans (Freyd.Alg.le_of_eq (foldR_fun F f)) (foldR_monotonic F (graph f) R h)

end Freyd.Alg.RelSet.Poly
