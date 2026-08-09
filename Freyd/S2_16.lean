module

public import Freyd.S2_10
public import Freyd.S2_20
public import Freyd.S2_216_MatrixAllegory

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* — splitting symmetric idempotents.

  This is the allegory-internal "split-idempotent" (Cauchy / systemic) completion
  of an allegory, the construction `𝒮𝓅𝓁` of §2.164–§2.167 (the book writes it
  `𝒮ℳ𝒶𝓅(g)` for a class `g` of symmetric idempotents; here we split *all*
  symmetric idempotents).

  §2.12   A COREFLEXIVE is symmetric idempotent; a SYMMETRIC IDEMPOTENT `e = e° = ee`
          is a "partial equivalence relation".
  §2.162  If `R, S` splits a symmetric idempotent `T` then `S = R°`.
  §2.163  A coreflexive `A` splits iff it is tabular; an equivalence `E` splits iff
          it is effective.
  §2.164  For a class `g` of symmetric idempotents the splitting category
          `𝒮ℳ𝒶𝓅(g)` carries a natural allegory structure with
            (e ⟶_R f)° = (f ⟶_{R°} e),    (e ⟶_R f) ∩ (e ⟶_S f) = (e ⟶_{R∩S} f);
          and the full inclusion `A ↪ 𝒮ℳ𝒶𝓅(g)` is a faithful representation of
          allegories.  In `𝒮ℳ𝒶𝓅(g)` every idempotent in `g` splits.

  We build the completion `Spl 𝒜` (splitting *all* symmetric idempotents of `𝒜`),
  prove it is an `Allegory`, exhibit the faithful full embedding `𝒜 ↪ Spl 𝒜`, and
  prove that the relevant idempotents split in `Spl 𝒜`.

  Conventions follow the repo: diagram-order composition `R ≫ S` (first `R`, then
  `S`), reciprocation `R°`, intersection `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/



namespace Freyd.Alg

open Cat

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## Symmetric idempotents -/

/-- `R` is a SYMMETRIC IDEMPOTENT (§2.12): `R° = R` and `RR = R`.  Such a morphism
    is a "partial equivalence relation".  Both coreflexives and equivalence
    relations are symmetric idempotents (§2.163). -/
public structure SymIdem (a : 𝒜) where
  /-- The underlying endomorphism `e : a ⟶ a`. -/
  e : a ⟶ a
  /-- SYMMETRIC: `e° = e`. -/
  sym : e° = e
  /-- IDEMPOTENT: `e ≫ e = e`. -/
  idem : e ≫ e = e

namespace SymIdem

variable {a : 𝒜}

/-- A symmetric idempotent is symmetric in the sense of §2.12 (`e° ⊑ e`). -/
theorem symmetric (E : SymIdem a) : Symmetric E.e := by
  dsimp [Symmetric]; rw [E.sym]; exact le_refl _

end SymIdem

/-! ## §2.164  The splitting completion `Spl 𝒜`

  Objects are symmetric idempotents `e : a ⟶ a` of `𝒜` (paired with their carrier
  object).  A morphism `e ⟶ f` is a morphism `R : a ⟶ b` of `𝒜` *split-typed* by
  the condition `e ≫ R ≫ f = R` (the book's `eRf = R`).  Composition,
  reciprocation and intersection are inherited from `𝒜`; the identity on `e` is
  `e` itself. -/

/-- An object of the splitting completion: a symmetric idempotent of `𝒜`. -/
public structure SplObj (𝒜 : Type u) [Allegory 𝒜] where
  /-- The carrier object of `𝒜`. -/
  carrier : 𝒜
  /-- The symmetric idempotent that this object *is*. -/
  idem : SymIdem carrier

/-- A morphism `e ⟶ f` of the splitting completion: a morphism `R` of `𝒜` that is
    fixed by pre/post-composition with the two idempotents, `e ≫ R ≫ f = R`. -/
public structure SplHom (E F : SplObj 𝒜) where
  /-- The underlying morphism of `𝒜`. -/
  R : E.carrier ⟶ F.carrier
  /-- The split-typing condition `e ≫ R ≫ f = R` (the book's `eRf = R`). -/
  fixed : E.idem.e ≫ R ≫ F.idem.e = R

namespace SplHom

variable {E F G : SplObj 𝒜}

/-- Two split-homs are equal iff their underlying morphisms are equal. -/
@[ext] public theorem ext {R S : SplHom E F} (h : R.R = S.R) : R = S := by
  cases R; cases S; cases h; rfl

/-- One-sided absorption on the left: `e ≫ R = R`. -/
public theorem fixed_left (R : SplHom E F) : E.idem.e ≫ R.R = R.R := by
  calc E.idem.e ≫ R.R
      = E.idem.e ≫ (E.idem.e ≫ R.R ≫ F.idem.e) := by rw [R.fixed]
    _ = (E.idem.e ≫ E.idem.e) ≫ (R.R ≫ F.idem.e) := by rw [← Cat.assoc]
    _ = E.idem.e ≫ (R.R ≫ F.idem.e) := by rw [E.idem.idem]
    _ = R.R := R.fixed

/-- One-sided absorption on the right: `R ≫ f = R`. -/
public theorem fixed_right (R : SplHom E F) : R.R ≫ F.idem.e = R.R := by
  calc R.R ≫ F.idem.e
      = (E.idem.e ≫ (R.R ≫ F.idem.e)) ≫ F.idem.e := by rw [R.fixed]
    _ = E.idem.e ≫ (R.R ≫ (F.idem.e ≫ F.idem.e)) := by rw [Cat.assoc, Cat.assoc]
    _ = E.idem.e ≫ (R.R ≫ F.idem.e) := by rw [F.idem.idem]
    _ = R.R := R.fixed

end SplHom

/-! ### The category structure -/

/-- Identity split-hom on `e`: the idempotent `e` itself (`e ≫ e ≫ e = e`). -/
@[expose] public def splId (E : SplObj 𝒜) : SplHom E E :=
  ⟨E.idem.e, by rw [E.idem.idem, E.idem.idem]⟩

/-- Composition of split-homs is the underlying `≫`; the fixed condition is
    preserved because `e (RS) g = (eR)(Sg) = RS` (left-absorption of `R`,
    right-absorption of `S`). -/
@[expose] public def splComp {E F G : SplObj 𝒜} (R : SplHom E F) (S : SplHom F G) : SplHom E G :=
  ⟨R.R ≫ S.R, by
    calc E.idem.e ≫ (R.R ≫ S.R) ≫ G.idem.e
        = (E.idem.e ≫ R.R) ≫ (S.R ≫ G.idem.e) := by rw [Cat.assoc, Cat.assoc]
      _ = R.R ≫ S.R := by rw [R.fixed_left, S.fixed_right]⟩

/-- The splitting completion is a category: identity `splId`, composition
    `splComp`; the three category laws hold on underlying morphisms. -/
@[expose] public instance instCatSpl : Cat.{v} (SplObj 𝒜) where
  Hom E F := SplHom E F
  id E := splId E
  comp R S := splComp R S
  id_comp R := by
    apply SplHom.ext; show (splId _).R ≫ R.R = R.R
    exact R.fixed_left
  comp_id R := by
    apply SplHom.ext; show R.R ≫ (splId _).R = R.R
    exact R.fixed_right
  assoc R S T := by
    apply SplHom.ext; show (R.R ≫ S.R) ≫ T.R = R.R ≫ (S.R ≫ T.R)
    exact Cat.assoc _ _ _

/-! ### Reciprocation and intersection -/

/-- Reciprocation of a split-hom: `R° : f ⟶ e`.  The fixed condition transports by
    `f R° e = (e R f)° = R°` using symmetry of `e` and `f`. -/
@[expose] public def splRecip {E F : SplObj 𝒜} (R : SplHom E F) : SplHom F E :=
  ⟨R.R°, by
    calc F.idem.e ≫ R.R° ≫ E.idem.e
        = (E.idem.e ≫ R.R ≫ F.idem.e)° := by
            simp only [Allegory.recip_comp, E.idem.sym, F.idem.sym, Cat.assoc]
      _ = R.R° := by rw [R.fixed]⟩

/-- Intersection of two parallel split-homs: `R ∩ S : e ⟶ f`.  The fixed condition
    is preserved: `e (R∩S) f = (eRf) ∩ (eSf) = R ∩ S`. -/
@[expose] public def splInter {E F : SplObj 𝒜} (R S : SplHom E F) : SplHom E F :=
  ⟨R.R ∩ S.R, by
    -- `e (R∩S) f = R ∩ S`.  We show both `⊑` directions.
    apply le_antisymm
    · -- `e (R∩S) f ⊑ eRf ∩ eSf = R ∩ S`.  The map `X ↦ e X f` is monotone.
      have hmono : ∀ {X Y : E.carrier ⟶ F.carrier}, X ⊑ Y →
          E.idem.e ≫ X ≫ F.idem.e ⊑ E.idem.e ≫ Y ≫ F.idem.e :=
        fun hXY => comp_mono_left _ (comp_mono_right hXY _)
      have hR : E.idem.e ≫ (R.R ∩ S.R) ≫ F.idem.e ⊑ R.R := by
        have := hmono (inter_lb_left R.R S.R); rw [R.fixed] at this; exact this
      have hS : E.idem.e ≫ (R.R ∩ S.R) ≫ F.idem.e ⊑ S.R := by
        have := hmono (inter_lb_right R.R S.R); rw [S.fixed] at this; exact this
      exact le_inter hR hS
    · -- `R ∩ S ⊑ e (R∩S) f`.  Insert `e` on the left and `f` on the right by the
      -- dual modular law, using `M ⊑ R = eRf`.  Write `e = E.e`, `f = F.e`,
      -- `M = R.R ∩ S.R`.
      -- DUAL MODULAR (reciprocal of `modular_le`):  e≫X ∩ T ⊑ e≫(X ∩ e°≫T).
      have dual_modular : ∀ {b : 𝒜} (X : E.carrier ⟶ b) (T : E.carrier ⟶ b),
          (E.idem.e ≫ X) ∩ T ⊑ E.idem.e ≫ (X ∩ E.idem.e° ≫ T) := by
        intro b X T
        have hr := recip_mono (modular_le X° E.idem.e° T°)
        rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip] at hr
        rw [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_comp,
            Allegory.recip_recip, Allegory.recip_recip] at hr
        rw [Allegory.recip_recip] at hr
        exact hr
      have hMR_eq : R.R ∩ (R.R ∩ S.R) = R.R ∩ S.R := by
        rw [Allegory.inter_assoc, Allegory.inter_idem]
      -- M ⊑ e≫M.   Dual modular with X=R, T=M:  R∩M ⊑ e≫(R ∩ e°≫M);  R∩M = M;
      --            RHS ⊑ e≫(e°≫M) = e≫(e≫M) = e≫M.
      have hMleeM : R.R ∩ S.R ⊑ E.idem.e ≫ (R.R ∩ S.R) := by
        have h1 := dual_modular R.R (R.R ∩ S.R)
        rw [R.fixed_left, hMR_eq] at h1
        refine le_trans h1 ?_
        refine le_trans (comp_mono_left _ (inter_lb_right R.R (E.idem.e° ≫ (R.R ∩ S.R)))) ?_
        rw [E.idem.sym, ← Cat.assoc, E.idem.idem]
        exact le_refl _
      -- M ⊑ M≫f.   Right modular (`modular_le`) with X=R, T=M:
      --            (R≫f)∩M ⊑ (R ∩ M≫f°)≫f;  (R≫f)∩M = M;
      --            RHS ⊑ (M≫f°)≫f = M≫(f≫f) = M≫f.
      have hMlefM : R.R ∩ S.R ⊑ (R.R ∩ S.R) ≫ F.idem.e := by
        have h1 := modular_le R.R F.idem.e (R.R ∩ S.R)
        rw [R.fixed_right, hMR_eq] at h1
        refine le_trans h1 ?_
        refine le_trans (comp_mono_right (inter_lb_right R.R ((R.R ∩ S.R) ≫ F.idem.e°)) _) ?_
        rw [Cat.assoc, F.idem.sym, F.idem.idem]
        exact le_refl _
      -- Combine: M ⊑ e≫M ⊑ e≫(M≫f) = e≫M≫f.
      refine le_trans hMleeM ?_
      exact comp_mono_left _ hMlefM⟩

/-! ### `Spl 𝒜` is an allegory -/

@[expose] public instance instAllegorySpl : Allegory.{v} (SplObj 𝒜) where
  recip R := splRecip R
  inter R S := splInter R S
  recip_recip R := by
    apply SplHom.ext; show R.R°° = R.R; exact Allegory.recip_recip _
  recip_comp R S := by
    apply SplHom.ext; show (R.R ≫ S.R)° = S.R° ≫ R.R°; exact Allegory.recip_comp _ _
  recip_inter R S := by
    apply SplHom.ext; show (R.R ∩ S.R)° = R.R° ∩ S.R°; exact Allegory.recip_inter _ _
  inter_idem R := by
    apply SplHom.ext; show R.R ∩ R.R = R.R; exact Allegory.inter_idem _
  inter_comm R S := by
    apply SplHom.ext; show R.R ∩ S.R = S.R ∩ R.R; exact Allegory.inter_comm _ _
  inter_assoc R S T := by
    apply SplHom.ext; show R.R ∩ (S.R ∩ T.R) = (R.R ∩ S.R) ∩ T.R
    exact Allegory.inter_assoc _ _ _
  semidistrib R S T := by
    apply SplHom.ext
    show R.R ≫ (S.R ∩ T.R) = ((R.R ≫ S.R) ∩ (R.R ≫ (S.R ∩ T.R))) ∩ (R.R ≫ T.R)
    exact Allegory.semidistrib _ _ _
  modular R S T := by
    apply SplHom.ext
    show (R.R ≫ S.R) ∩ T.R
        = ((R.R ≫ S.R) ∩ T.R) ∩ ((R.R ∩ (T.R ≫ S.R°)) ≫ S.R)
    exact Allegory.modular _ _ _

/-! ## §2.164  The faithful full embedding `𝒜 ↪ Spl 𝒜`

  On objects, `a ↦ (a, 1_a)` (the identity is a symmetric idempotent).
  On morphisms, `R : a ⟶ b` maps to itself, since `1_a ≫ R ≫ 1_b = R`.  This is a
  representation of allegories: it preserves identities, composition, reciprocation
  and intersection.  It is faithful (injective on hom-sets) and full (every
  split-hom between embedded objects comes from a unique `R`). -/

/-- The identity `1_a` is a symmetric idempotent. -/
@[expose] public def idSymIdem (a : 𝒜) : SymIdem a :=
  ⟨Cat.id a, recip_id, Cat.id_comp _⟩

/-- The embedding on objects: `a ↦ (a, 1_a)`. -/
@[expose] public def embObj (a : 𝒜) : SplObj 𝒜 := ⟨a, idSymIdem a⟩

/-- The embedding on morphisms: `R ↦ R`, with witness `1 ≫ R ≫ 1 = R`. -/
@[expose] public def embHom {a b : 𝒜} (R : a ⟶ b) : SplHom (embObj a) (embObj b) :=
  ⟨R, by show Cat.id a ≫ R ≫ Cat.id b = R; rw [Cat.comp_id, Cat.id_comp]⟩

@[simp] public theorem embHom_R {a b : 𝒜} (R : a ⟶ b) : (embHom R).R = R := rfl

/-- The embedding is FAITHFUL: injective on hom-sets. -/
public theorem embHom_injective {a b : 𝒜} {R S : a ⟶ b} (h : embHom R = embHom S) : R = S :=
  congrArg SplHom.R h

/-- The embedding is FULL: every split-hom between embedded objects is `embHom R`
    for a unique `R` (namely its underlying morphism). -/
public theorem embHom_full {a b : 𝒜} (φ : SplHom (embObj a) (embObj b)) :
    embHom φ.R = φ := by
  apply SplHom.ext; rfl

/-- The embedding preserves identities: `embHom 1_a = 1_{(a,1)}`. -/
public theorem embHom_id (a : 𝒜) : embHom (Cat.id a) = Cat.id (embObj a) := by
  apply SplHom.ext; rfl

/-- The embedding preserves composition. -/
public theorem embHom_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    (embHom (R ≫ S) : embObj a ⟶ embObj c)
      = splComp (embHom R) (embHom S) := by
  apply SplHom.ext; rfl

/-- The embedding preserves reciprocation. -/
public theorem embHom_recip {a b : 𝒜} (R : a ⟶ b) :
    (embHom (R°) : embObj b ⟶ embObj a) = splRecip (embHom R) := by
  apply SplHom.ext; rfl

/-- The embedding preserves intersection. -/
public theorem embHom_inter {a b : 𝒜} (R S : a ⟶ b) :
    (embHom (R ∩ S) : embObj a ⟶ embObj b) = splInter (embHom R) (embHom S) := by
  apply SplHom.ext; rfl

/-! ## §2.164  Idempotents split in the completion

  We follow the book's notion of a splitting (§1.281): `(x, y)` splits an idempotent
  `e : A ⟶ A` if `x ≫ y = e` and `y ≫ x = 1`.  We show every symmetric idempotent
  `E.e` of `𝒜`, embedded as the endomorphism `embHom E.e : (a,1) ⟶ (a,1)`, splits
  in `Spl 𝒜` through the new object `(a, E)`. -/

/-- The "down" leg `(a,1) ⟶ (a,E)` of the splitting: underlying `E.e`. -/
@[expose] public def splDown {a : 𝒜} (E : SymIdem a) : SplHom (embObj a) ⟨a, E⟩ :=
  ⟨E.e, by show Cat.id a ≫ E.e ≫ E.e = E.e; rw [Cat.id_comp, E.idem]⟩

/-- The "up" leg `(a,E) ⟶ (a,1)` of the splitting: underlying `E.e`. -/
@[expose] public def splUp {a : 𝒜} (E : SymIdem a) : SplHom (⟨a, E⟩ : SplObj 𝒜) (embObj a) :=
  ⟨E.e, by show E.e ≫ E.e ≫ Cat.id a = E.e; rw [Cat.comp_id, E.idem]⟩

/-- `(splDown E, splUp E)` SPLITS the embedded idempotent: `down ≫ up = embHom E.e`. -/
public theorem splDown_up {a : 𝒜} (E : SymIdem a) :
    splComp (splDown E) (splUp E) = embHom E.e := by
  apply SplHom.ext; show E.e ≫ E.e = E.e; exact E.idem

/-- `(splDown E, splUp E)` SPLITS: `up ≫ down = 1_{(a,E)}` (the identity on `(a,E)`,
    whose underlying morphism is `E.e`). -/
public theorem splUp_down {a : 𝒜} (E : SymIdem a) :
    splComp (splUp E) (splDown E) = splId (⟨a, E⟩ : SplObj 𝒜) := by
  apply SplHom.ext; show E.e ≫ E.e = E.e; exact E.idem

/-- §2.164: every symmetric idempotent of `𝒜` splits in `Spl 𝒜`.  The embedded
    idempotent `embHom E.e` factors as `down ≫ up` with `up ≫ down = 1`, where
    `splComp` is composition and `splId` the identity of `Spl 𝒜`. -/
theorem embHom_idem_splits {a : 𝒜} (E : SymIdem a) :
    splComp (splDown E) (splUp E) = embHom E.e ∧
    splComp (splUp E) (splDown E) = splId (⟨a, E⟩ : SplObj 𝒜) :=
  ⟨splDown_up E, splUp_down E⟩

/-! ## §2.162  A splitting of a symmetric idempotent is reciprocal: `S = R°`

  If `R ≫ S = T` (symmetric idempotent) and `S ≫ R = 1`, then `S = R°`. -/

/-- §2.162: if `(R, S)` splits a symmetric idempotent `T = R ≫ S` (so `S ≫ R = 1`
    and `(R ≫ S)° = R ≫ S`), then `S = R°`.

    Book proof (§2.162), every step a containment using `SR = 1`, `(RS)° = RS`,
    and the basic identity `X ⊑ X X° X` (`le_comp_codom`/modular):
      `R° = (SR)R° ⊑ SS°(SR)R° ⊑ SS°R° ⊑ S(RS)° ⊑ (SR)S ⊑ S`,
      `S° ⊑ S°(SR) ⊑ S°(SR)(R°R) ⊑ S°R°R ⊑ (RS)°R ⊑ R(SR) ⊑ R`  (so `S ⊑ R°`). -/
theorem splitting_recip {a b : 𝒜} {R : a ⟶ b} {S : b ⟶ a}
    (hSR : S ≫ R = Cat.id b) (hsym : (R ≫ S)° = R ≫ S) : S = R° := by
  -- Basic identity used twice:  `X ⊑ X ≫ X° ≫ X`.
  -- Proof: `X° ⊑ (1 ∩ X°X)≫X°` by modular law (with `R=1, S=X°, T=X°`);
  -- reciprocate and weaken `(1 ∩ X°X) ⊑ X°X`.
  have codom : ∀ {x y : 𝒜} (X : x ⟶ y), X ⊑ X ≫ X° ≫ X := by
    intro x y X
    have hm := modular_le (Cat.id y) (X°) (X°)
    rw [Cat.id_comp, Allegory.inter_idem, Allegory.recip_recip] at hm
    -- hm : X° ⊑ (1 ∩ X°≫X) ≫ X°
    have hr := recip_mono hm
    rw [Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_inter, recip_id,
        Allegory.recip_comp, Allegory.recip_recip] at hr
    -- hr : X ⊑ X ≫ (1 ∩ X°≫X)
    refine le_trans hr ?_
    exact comp_mono_left X (inter_lb_right (Cat.id y) (X° ≫ X))
  -- `1_b ⊑ S S°`:   `1_b = S ≫ R ⊑ (S ≫ S° ≫ S) ≫ R = S ≫ S° ≫ (S ≫ R) = S ≫ S°`.
  have h1_le_SSr : Cat.id b ⊑ S ≫ S° := by
    have h : S ≫ R ⊑ (S ≫ S° ≫ S) ≫ R := comp_mono_right (codom S) R
    rw [hSR] at h
    calc Cat.id b ⊑ (S ≫ S° ≫ S) ≫ R := h
      _ = S ≫ S° ≫ (S ≫ R) := by rw [Cat.assoc, Cat.assoc]
      _ = S ≫ S° := by rw [hSR, Cat.comp_id]
  -- `R° ⊑ S`:   `R° = 1_b ≫ R° ⊑ (S S°) R° = S (S° R°) = S (R S)° = S (R S) = (S R) S = S`.
  have hRrecip_le_S : R° ⊑ S := by
    calc R° = Cat.id b ≫ R° := by rw [Cat.id_comp]
      _ ⊑ (S ≫ S°) ≫ R° := comp_mono_right h1_le_SSr R°
      _ = S ≫ (R ≫ S)° := by rw [Cat.assoc, Allegory.recip_comp]
      _ = S ≫ (R ≫ S) := by rw [hsym]
      _ = (S ≫ R) ≫ S := by rw [Cat.assoc]
      _ = S := by rw [hSR, Cat.id_comp]
  -- `S° ⊑ R`:   `S° = S° (S R) ⊑ S° (S R) (R° R) = S° R° R = (R S)° R = (R S) R = R (S R) = R`.
  have hSrecip_le_R : S° ⊑ R := by
    -- `S R ⊑ (S R)(R° R)`  from  `R ⊑ R R° R`  (post-compose `R° R`, pre-compose `S`).
    have hStep : S ≫ R ⊑ (S ≫ R) ≫ (R° ≫ R) := by
      have h : S ≫ R ⊑ S ≫ (R ≫ R° ≫ R) := comp_mono_left S (codom R)
      calc S ≫ R ⊑ S ≫ (R ≫ R° ≫ R) := h
        _ = (S ≫ R) ≫ (R° ≫ R) := (Cat.assoc S R (R° ≫ R)).symm
    calc S° = S° ≫ (S ≫ R) := by rw [hSR, Cat.comp_id]
      _ ⊑ S° ≫ ((S ≫ R) ≫ (R° ≫ R)) := comp_mono_left S° hStep
      _ = S° ≫ R° ≫ R := by rw [hSR, Cat.id_comp]
      _ = (S° ≫ R°) ≫ R := (Cat.assoc S° R° R).symm
      _ = (R ≫ S)° ≫ R := by rw [Allegory.recip_comp]
      _ = (R ≫ S) ≫ R := by rw [hsym]
      _ = R ≫ (S ≫ R) := by rw [Cat.assoc]
      _ = R := by rw [hSR, Cat.comp_id]
  -- Combine: `S ⊑ R°` (recip of `S° ⊑ R`) and `R° ⊑ S`.
  have hS_le_Rrecip : S ⊑ R° := by
    have := recip_mono hSrecip_le_R; rwa [Allegory.recip_recip] at this
  exact le_antisymm hS_le_Rrecip hRrecip_le_S

/-! ## §2.212  Maps of a tabular unitary distributive allegory form a pre-logos

  "If A is a tabular unitary distributive allegory, then Mon_U(A) is a pre-logos."
  [§2.212, proof: §2.154 gives regular; subobjects = coreflexives; finite unions exist.]

  PROVED in `Freyd/MapCat.lean`: `mapPreLogos` assembles the full `PreLogos (MapObj A)`
  instance for `[TabularUnitaryDistributiveAllegory A]` — all eight fields discharged:
  `mapRegularCategory`, `mapHasSubobjectUnions`, `mapBottom`/`mapBottom_min`/`mapBottom_dom_iso`,
  `mapInvImage_preserves_union`, `mapInvImage_preserves_bottom`.  Sorry-free. -/

-- §2.212: If A is a tabular unitary distributive allegory, then Mon_U(A) is a pre-logos.
-- PROVED: `mapPreLogos` in Freyd/MapCat.lean (TabularUnitaryDistributiveAllegory A).

/-! ## §2.214  Pre-logos positive iff Rel(C) has finite coproducts

  "A pre-logos C is positive iff Rel(C) has finite coproducts."
  [§2.214, uses §2.215 duality coproduct ↔ product via reciprocation.]

  NOTE (§2.212/§2.214 hypothesis-tightening).  Both `DisjointGluing.relDistributiveAllegory`
  (`Rel(C)` is a DISTRIBUTIVE allegory) and the §2.214 REVERSE
  (`relReverse_positive_of_relCoproducts`) now hold over a BARE `[PreLogos C]` — NOT
  `[PositivePreLogos C]`.  This matches Freyd verbatim: §2.212 says "Rel(C) is distributive for
  ANY pre-logos [1.616]", and §2.214's ⟸ ("Rel(C) coproducts ⟹ C positive") assumes only that
  `C` is a pre-logos.  The relaxation comes from re-basing §1.616's relational union `relUnion`
  on the SUBOBJECT-union (`subRel (union (relSub R) (relSub S))`, needs only `[HasSubobjectUnions]`,
  supplied by every pre-logos) instead of the image of a coproduct copairing.

  The ALLEGORY side (§2.215): a POSITIVE ALLEGORY has a zero object and all finite coproducts,
  characterised by five equations for the injections `u₁ : X → X⊕Y` and `u₂ : Y → X⊕Y`:
    u₁u₁° = 1_X,  u₁u₂° = 0,  u₂u₁° = 0,  u₂u₂° = 1_Y,  u₁°u₁ ∪ u₂°u₂ = 1_{X⊕Y}.

  PROVED (§2.215 / §2.216): `MatObj 𝒜` is a positive allegory for any distributive allegory `𝒜`.
  The coproduct `X ⊕ Y` is the concatenated index family `Fin(m+n) → 𝒜`; the injections
  `u₁ = mInl`, `u₂ = mInr` are built from the block-diagonal identity matrix and satisfy all
  five equations.  See `Freyd/MatrixAllegory.lean` §J (`instPositiveAllegoryMat`, `mCoproduct`).

  The Rel(C) functor (Ch1 → Ch2 bridge) is now BUILT in `Freyd/RelCat.lean`
  (`relAllegory`/`relDistributiveAllegory`/`relTabularAllegory`/`relUnitaryAllegory`). -/

-- §2.214: A pre-logos C is positive iff Rel(C) has finite coproducts.
-- §2.215 PROVED: PositiveAllegory (MatObj 𝒜) — see Freyd.MatrixAllegory.instPositiveAllegoryMat.
-- FORWARD (positive ⟹ Rel(C) coproducts) PROVED: Freyd.DisjointGluing.relCoproduct (RelCat.lean),
--   all five §2.2 equations incl eq(5) (relGraph_recip_union_eq_id).
-- BOOK §2.214 REVERSE (Rel(C) coproducts ⟹ C positive): reads the coproduct back through
--   Map(Rel C) ≅ C.  The category iso is now FULLY PACKAGED in RelCat.lean:
--     • identity-on-objects (`⟨·⟩ : C → RelObj C = MapObj (RelObj C)`),
--     • functorial (`RelCat.embedRel_id`, `RelCat.embedRel_comp`),
--     • FAITHFUL (`RelCat.embedRel_faithful`),
--     • FULL (`RelCat.embedRel_full`: every `Map` of `Rel C` is a unique graph — the §2.148 dual,
--       proved from regular-category balance `monic_cover_iso` via `tabulated_is_map_iff_left_iso`
--       / `tabulated_left_iso_eq_graph`), bundled as `RelCat.embedRel_cat_iso`.
--   REVERSE — STATUS (option (b) taken; the TC DIAMOND is DODGED).  `Freyd/RelCat.lean` now states
--   the reverse with the positive-allegory coproduct DATA built ON TOP of the EXISTING `relAllegory`,
--   so there is no competing `Allegory (RelObj C)`/`Cat (RelObj C)` instance.  Concretely
--   (`section ReverseCoproduct`, now `variable [PreLogos C]` — see the §2.212/§2.214 note above;
--    the coproduct DATA `hcop` supplies positivity, so no ambient `[PositivePreLogos C]` is needed):
--     • `relTUPositiveAllegory (zero) (coprodObj) (hcop)` assembles a
--       `TabularUnitaryPositiveAllegory (RelObj C)` from `relTabularUnitaryDistributiveAllegory` plus
--       the supplied coterminal / binary-coproduct-object / per-pair `Alg.Coproduct` DATA over
--       `relAllegory` (hcop : ∀ a b, Coproduct (coprodObj a b) a b) — the marker's option (b).
--   LANDED SORRY-FREE (axioms [propext, Classical.choice, Quot.sound]):
--     • `relReverseHasBinaryCoproducts zero coprodObj hcop : HasBinaryCoproducts C` — the FULL binary
--       coproduct of C: object `= (H.coprod ⟨a⟩ ⟨b⟩).carrier` (id-on-objects), `inl`/`inr`/`case`
--       pulled back from `MapCat.mapHasBinaryCoproducts` by fullness (`embedRel_cat_iso.2`), with the
--       three UMP equations (`case_inl`/`case_inr`/`case_uniq`) transferred by faithfulness +
--       `embedRel_comp`/`embedRel_id` (`H.case_uniq` on the image side).
--     • `embedRel_reflects_monic` (a full+faithful id-on-objects functor reflects monos), and hence
--       `relReverse_inl_monic` / `relReverse_inr_monic` — the injections of that coproduct are MONIC
--       in C (their `embedRel`-images are `Map(Rel C)`'s injections, monic via
--       `MapCat.mapDisjointBinaryCoproduct`, reflected back).
--   PROVED — the two §1.621 disjointness INEQUALITIES, completing the FULL `DisjointBinaryCoproduct C`:
--     • `relReverse_inl_union_inr` : `entire ≤ inl ∪ inr`.  PURELY in C — the union `inlSub ∪ inrSub`
--       is the image of `case inl inr` (`union_is_image`), and `case inl inr = id` by the coproduct
--       UMP (`case_uniq` against the identity), so the union is the image of `id`, which `entire`
--       allows.  No transport needed for this half.
--     • `relReverse_inl_inter_inr` : `inl ∩ inr ≤ 0`.  TRANSPORTED through `embedRel`.  The C-pullback
--       domain `P` of `(inl, inr)`, pushed through the id-on-objects iso (`embedRel inl = inl_Map`,
--       `embedRel inr = inr_Map` via `embedRel_cat_iso`; square by `embedRel_comp` + `pb.cone.w`),
--       is a cone over `Map(Rel C)`'s `(inl_Map, inr_Map)`.  `Map`'s own disjointness
--       (`coprod_inl_inr_disjoint_elt` from `MapCat.mapDisjointBinaryCoproduct`) gives a Map-map
--       `⟨P⟩ → bottom_Map.dom`, so `⟨P⟩` is initial (`dom_initial_of_map_to_bottom`); routed through
--       the Map-coterminator and lifted back by fullness yields a C-map `P → (⊥ _).dom`, closed by
--       the local helper `le_bottom_of_map_to_bottom`.
--   ASSEMBLED: `relReverseDisjointBinaryCoproduct (zero) (coprodObj) (hcop) : DisjointBinaryCoproduct C`
--   bundles `relReverseHasBinaryCoproducts` + the four §1.621 fields (the `PositivePreLogos` it
--   PRODUCES stores the ambient bare `[PreLogos C]` LITERALLY via `PositivePreLogos.mk ‹PreLogos C›`
--   and pins the coproduct to the reverse one, so the field lemmas — applied at the ambient instance —
--   match definitionally, no diamond).  Wrapper:
--   `relReverse_positive_of_relCoproducts : Nonempty (DisjointBinaryCoproduct C)`.
--   Holds over a BARE `[PreLogos C]`; sorry-free; axioms [propext, Classical.choice, Quot.sound].
--   This is the §2.214 REVERSE.

/-- §2.215 positivity of the matrix allegory: every distributive allegory `𝒜` gives a positive
    allegory `MatObj 𝒜`. The coproduct `X ⊕ Y` is the concatenated index family; the injections
    satisfy the five §2.214 equations. -/
example (𝒜 : Type u) [DistributiveAllegory 𝒜] : PositiveAllegory (Mat.MatObj 𝒜) :=
  Mat.instPositiveAllegoryMat

/-! ## §2.217  Faithful representation in a positive pre-logos / pre-topos

  "A pre-logos may be faithfully represented in a positive pre-logos."
  [§2.217, proof: start with pre-logos C, take maps of the positive reflection
  of the allegory of relations.  The two §2.217 propositions:
    (1) every pre-logos embeds faithfully in a positive pre-logos;
    (2) every pre-logos embeds faithfully in a pre-topos.]

  PROVED IN FULL GENERALITY (bare `[PreLogos C]`, Freyd's headline (1)) in `Freyd/RelCat.lean`:
  `s217_faithful_embed_into_positive` — for ANY pre-logos `C`, `C ↪ Map(Mat(Rel C))` is a faithful
  embedding into a positive pre-logos.  Uses `instTabularAllegoryMat`/`instUnitaryAllegoryMat`/
  `instPositiveAllegoryMat` (MatrixAllegory.lean §2.342/§2.215) and `mapPreLogos` (§2.212);
  `relDistributiveAllegory` holds over any pre-logos (§1.616/§2.212 relUnion-subobject-union
  refactor), and `Mat` supplies the target's positivity — so `C` need not be positive.
  (2) faithful representation in a pre-topos remains OPEN. -/

-- §2.217 (1): A pre-logos may be faithfully represented in a positive pre-logos.
-- PROVED IN FULL GENERALITY (bare [PreLogos C], Freyd's headline):
--   `s217_faithful_embed_into_positive` in Freyd/RelCat.lean. C need NOT be positive —
--   relDistributiveAllegory now holds over any pre-logos (relUnion-subobject-union refactor),
--   and Mat supplies the target's positivity.
-- §2.217 (2): A pre-logos may be faithfully represented in a pre-topos.
-- OPEN — needs pre-topos structure on Map(Mat(Rel(C))).

/-! ## §2.218  Faithful representation in a power of the allegory of sets

  "A small pre-tabular or semi-simple unitary distributive allegory may be faithfully
  represented in a power of the allegory of sets." [§2.218, from §2.167, §2.16(10),
  §2.213, §2.217, §1.635 — complex cross-chapter assembly.] -/

-- BOOK §2.218: A small pre-tabular or semi-simple unitary distributive allegory may be
-- faithfully represented in a power of the allegory of sets.
-- STATUS: BRICKS 1,2,2c,3 DONE; R1 (THE WALL) DONE; R2 (CARRIER BRIDGE) DONE; the §2.218 ASSEMBLY
--   is BUILT and faithful.  The headline + assembly live in `Freyd/S2_218.lean`
--   (`Freyd.repr_in_power_of_sets`, axioms [propext,Classical.choice,Quot.sound]).  With R2 now
--   discharged (`Freyd.repr_in_power_of_sets_of_tabular`), only ONE genuine §1.543 structural
--   residual remains (R3), isolated as explicit hypotheses (see below).
--
-- ★ K1 — DONE (STALK REGULAR-FUNCTOR, Freyd/StalkRegular.lean, axioms ⊆ [propext,Classical.choice,
--   Quot.sound]).  The §1.635 stalk functor `T_F̂ : 𝒞 → Set` (the colimit `TF` of S1_62) is a
--   `RelFunctor.RegularFunctor`: `Freyd.PreLogosHorn.Stalk.TF_regularFunctor ℱ hℱ hproj`.
--   This makes CONCRETE the §1.625 "representation of regular categories" content that S1_62 carried
--   only ABSTRACTLY as the parameter `repReg`.  The five fields split into:
--     • UNCONDITIONAL (any pre-filter — "directed colimit commutes with finite limit in Set"):
--         `TF_preserves_binaryProducts`, `TF_preserves_pullbacks`, `TF_preserves_mono`.
--     • CONDITIONAL on `hproj` = "every member of `ℱ` is PROJECTIVE":
--         `TF_preserves_covers_of_projective`, `TF_preserves_images`.
--   The conditionality is NOT a defect of the formalization — it is Freyd's OWN hypothesis.  §1.635
--   p.123 opens *"We may concentrate on a CAPITAL positive pre-logos A [1.63]"* and §1.634 states
--   *"`T_F` preserves finite products and equalizers; IF the elements of `F` are projective then
--   `T_F` preserves covers."*  In a capital pre-logos the complemented subterminators (an
--   ultra-filter's members) are projective (§1.633).  So the prompt-conjectured "filtered colimit of
--   representables preserves covers with NO projectivity" is FALSE: covers/epis are not a
--   finite-limit notion, and filteredness alone never gives them.  The stalk route DOES NOT bypass
--   capitalization for cover-preservation; it relocates R3, it does not remove it.
--
-- ★ K2 — the stalk route to §2.218 (Freyd/S2_218.lean `Freyd.relStalk_faithful`, axiom-FREE).
--   `Rel(T_F̂) : Rel(𝒞) ⟶ Rel(Set)` is a FAITHFUL allegory morphism GIVEN (i) `hproj` (K1 covers =
--   capitalization, the relocated R3) and (ii) `T_F̂` REFLECTS ISOS.  Set-covers split for free
--   (`set_cover_splits`).  Ingredient (ii) — CONSERVATIVITY — is the genuinely IRREDUCIBLE wall:
--   `relAllegoryHom_faithful_of_reflects` needs reflects-isos, and the reduction `monoFactor_reflect`
--   genuinely uses it (a pullback projection becomes a split-mono = iso downstairs and must reflect
--   to an iso upstairs).  Faithful + reflects-MONOS does NOT suffice — a faithful functor reflects
--   monos but never isos.  A SINGLE stalk is never iso-reflecting; iso-reflection is the JOINT
--   CONSERVATIVITY of the stalk FAMILY (`StalkResidual.reflect`, S1_62), which is genuinely
--   §2.217-grade (ZERO-reflection alone already needs well-pointedness — a non-initial object with no
--   global element has every stalk empty).  CONCLUSION: the stalk route does NOT make §2.218
--   unconditional.  R3 (capitalization, for covers) AND conservativity (for faithfulness) both
--   remain; the stalk route's genuine win is making K1's `RegularFunctor` CONCRETE and supplying the
--   colimit-only ZERO-preservation (already recorded).  The §2.217 conservativity wall is REAL, not a
--   wrong-route artifact, and is the true irreducible residual of §2.218.
--
-- ★ K2′ — the WELL-POINTED stalk route, both stalk residuals discharged (Freyd/StalkConservative.lean,
--   axioms ⊆ [propext,Classical.choice,Quot.sound]).  The PRINCIPAL-TOP stalk `T_principalTop` makes
--   BOTH K2 residuals follow from `Ā` being FULLY WELL-POINTED + `Projective one`:
--     • projectivity  — `principalTop`'s members are `≅ 1`, projective once `1` is (`Projective one`,
--       from `Capital` via `capital_one_Projective`, §1.525);
--     • conservativity — `principalStalk_reflects_iso` (`isIso_of_points_bijective`): in a FULLY
--       well-pointed pre-logos a points-bijective map is an iso, so the principal stalk reflects isos.
--   `Freyd.PreLogosHorn.Stalk.relStalk_faithful_of_wellPointed (hwp : ∀ A, WellPointed Ā) (hone :
--   Projective one)` gives `Rel(T_principalTop)` faithful with NO separate `hrefl`.  Wired into the
--   §2.218 assembly as `Freyd.PreLogosHorn.Stalk.repr_in_set_of_tabular_wellPointed` — a FAITHFUL
--   `𝒜 ⟶ Rel(Set)` (a single set, a fortiori a power) from a tabular `𝒜`, given a PreLogos `Ā` that is
--   fully well-pointed + `Projective one` + a faithful `cap : Rel(Map 𝒜) ⟶ Rel(Ā)`.  This is the
--   CLEANER route: it needs only `Projective one` + well-pointedness, NOT all-objects-projective AC
--   (the homRep route's `hproj`).  THE RESIDUAL IT EXPOSES is the genuine §1.543 gap: capitalization
--   delivers `Capital` = (well-supported ⟹ well-pointed), which is STRICTLY weaker than FULL
--   `∀ A, WellPointed Ā` (a non-well-supported object — e.g. one with empty support — is never
--   well-pointed, so full well-pointedness is FALSE in general for the capital `Ā`).  Hence neither
--   route is unconditional at the §1.543 level: homRep needs all-objects-AC, K2′ needs full
--   well-pointedness, and `Capital` supplies neither.  R3 remains the genuine residual.
--
-- ★ R2 — DONE (CARRIER BRIDGE, Freyd/MapCat.lean + Freyd/RelCat.lean, axioms ⊆ [propext,
--   Classical.choice,Quot.sound]):  the MISSING meet-tabulation lemma `relOf (E ⊓ F) = relOf E ∩
--   relOf F` is now built — `Freyd.Alg.relOf_inter` (MapCat): `⊑` by `relOf_le_of_relLe` on the
--   meet projections + `le_inter`; `⊒` by tabulating the allegory meet `m = relOf R ∩ relOf S`
--   (`TabularAllegory.tabular`), assembling it as a `BinRel (Map A)` table `M` (joint-monic via
--   `mapMonicPair_of_tab`/§2.141), then `relLe_of_relOf_le` + `le_intersect` descend `m ⊑
--   relOf (R⊓S)`.  With it the §2.217(2) `relOf` dictionary is COMPLETE (≫,°,id,∩) and assembles
--   the faithful bridge `Freyd.bridgeFunctor : AllegoryFunctor 𝒜 (Rel(Map 𝒜))` (RelCat,
--   span encoding), faithful by `Freyd.bridgeFunctor_faithful` (`relOf (bridge.map R) = R` via
--   `relOf_tabSpan`).  Feeds the headline as `repr_in_power_of_sets_of_tabular`.
--
-- ★ R1 — DONE (THE WALL, Freyd/RelCat.lean, axioms ⊆ [propext,Classical.choice,Quot.sound]):
--     NON-FULL faithfulness of `Rel(F)`.  `RegularFunctor.relMap_faithful_of_reflects` /
--     `relAllegoryHom_faithful_of_reflects`: `Rel(F)` is faithful for a `RegularFunctor F` that
--     reflects isos + has split covers downstairs, WITHOUT fullness.  Mechanism (replacing the
--     fullness leg-lift): a `BinRel` span is jointly monic, so a `RelHom R S` is a factorization of
--     the mono `pair R.colA R.colB` through `pair S.colA S.colB`; `monoFactor_reflect` reflects that
--     factorization by pulling back along the mono and using `F` preserving pullbacks/monos +
--     reflecting isos (the pullback projection becomes a split mono downstairs, hence iso, reflected
--     upstairs).  `map_pair_comp_comparison` bridges `F(pair·) ≫ φ = pair(F·)` (`pres_prod` iso).
--     Assembled: `Freyd/S2_218.lean` `relHomRep_faithful` — `Rel(homRep Ā)` is faithful for a capital
--     (`hproj`) regular `Ā` (R1 + BRICK 2c + `homRep_reflects_iso` + `power_cover_splits`).
--
--   REMAINING RESIDUALS (now explicit hypotheses of `repr_in_power_of_sets`, both genuine):
--
-- ★ BRICK 2c — DONE (the keystone), axiom-clean ([] — no axioms):
--     `Freyd.homRep_regularFunctor` (Freyd/RelCat.lean): when every cover in a regular category `𝒞`
--     SPLITS (`𝒞` capital, the §1.543 case), `homRep 𝒞 : 𝒞 → Set^|𝒞|` is a `RegularFunctor`.
--     Built from five §1.62 `HomRepRegular` lemmas (Freyd/S1_62.lean, namespace `HomRepRegular`):
--       • `homRep_preserves_prod` — representable preserves binary products (the comparison
--         `h ↦ (h≫fst, h≫snd)` has inverse `(p,q) ↦ ⟨p,q⟩`, the product universal property).
--       • `homRep_preserves_pullbacks` — representable preserves pullbacks (fibrewise the pullback
--         universal property glues a compatible pair of arrows out of `i`).
--       • `homRep_preserves_covers` — from `homRep_preserves_cover_pointwise` (§1.55) + capital
--         projectivity + `power_cover_iff` (fibrewise surjective = cover in `Set^I`).
--       • `homRep_preserves_mono` (§1.55) and `homRep_preserves_images` — image = cover∘mono:
--         the image-lift `ℓ` of `f` is a cover (image-comparison iso), `homRep` carries it to a
--         fibrewise-surjective cover onto the pushed image subobject, giving minimality with NO
--         choice of preimage mattering (the equation holds for every preimage).
--     NOTE — universe generalization: this required widening `PreservesBinaryProducts`/
--     `PreservesPullbacks`/`PreservesCovers`/`PreservesImages`/`Subobject.map` (S1_43/45/52/51) and
--     `RelFunctor.RegularFunctor`/`AllegoryFunctor`/`AllegoryEquiv` (RelCat/MapCat) to TWO object
--     universes (`homRep : Type u → Type (u+1)` is cross-universe), with a shared morphism universe.
--     All backward-compatible (full project still builds).  Added: `Freyd.monic_isImage` (a mono is
--     its own image, S1_51), `Freyd.preservesImages_reflectsImages_of_reflectsIso` (cross-universe
--     §1.511 needing only reflects-iso, S1_51), `RegularCategory.toPreRegularCategory` (S1_52),
--     `AllegoryFunctor.comp`/`AllegoryFunctor.Faithful`/`AllegoryEquiv.toFun_faithful` (MapCat).
--
-- ★ BRICK 2 — DONE (Freyd/RelCat.lean, namespace `RelFunctor`), axioms [propext,Classical.choice,
--   Quot.sound]:
--     • `relImageObj_cover` — `image.lift (pair (F colA)(F colB))` is a cover onto the image-relation
--       src whose legs are the F-images of R's legs.  THE bridge that makes `relLe_of_cover_factor`
--       apply to `relImageObj`.
--     • `RegularFunctor` gained a `pres_pullback : PreservesPullbacks F` field (a regular functor
--       preserves the §1.56 compose/meet pullbacks; products alone don't suffice).
--     • `relImageObj_compose_le` / `relImageObj_le_compose` ⟹ `RegularFunctor.relMap_comp`:
--       **`Rel(F)(R ⊚ S) = Rel(F)(R) ⊚ Rel(F)(S)`** (Beck–Chevalley).  Forward: push the upstairs
--       §1.56 pullback through `F`, lift through the downstairs pullback, descend the composite
--       image-span.  Reverse: pull the image-covers `eR`/`eS` back along the downstairs projections
--       (`cover_pullback`), lift to `F pbRS.pt` via `pres_pullback`, push through `F eRS ≫ eRSd`.
--     • `relImageObj_inter_le` / `relImageObj_le_inter` ⟹ `RegularFunctor.relMap_inter`:
--       **`Rel(F)(R ∩ S) = Rel(F)(R) ∩ Rel(F)(S)`**.  Same pattern over the single meet-pullback;
--       `map_prod_jointly_monic` (from `pres_prod`) lifts the column-agreeing legs into `F(prod A B)`.
--     • `RegularFunctor.relMap_id` (image of the diagonal ≡ graph id) and `relMap_recip` (was done).
--     • `RegularFunctor.relAllegoryHom : AllegoryFunctor (RelObj C) (RelObj D)` — the packaged
--       allegory morphism `Rel(C) → Rel(D)` (all four laws).
--     • `RegularFunctor.relMap_faithful` — **`Rel(F)` is faithful** when `F` is full+faithful and
--       covers in `D` split (`relImageObj_reflect_le`: split the image-cover `eS`, lift the leg-map
--       through fullness, descend the equations by faithfulness).
--
--   REMAINING RESIDUAL (the final assembly), now exactly ONE (R1 — the wall — and R2 — the carrier
--   bridge — are DONE):
--     (R2) CARRIER BRIDGE — DONE (see the ★ R2 block above).  The faithful
--          `Freyd.bridgeFunctor : AllegoryFunctor A (RelObj (MapObj A))` is built from the COMPLETE
--          §2.217(2) `relOf` dictionary (the last piece, `relOf_inter`, is now proven), via the
--          tabulation-span encoding (`tabSpan`/`relOf_tabSpan`); faithful by `bridgeFunctor_faithful`.
--     (R3) CAPITAL-TARGET STRUCTURE.  `capitalization_of_capData` (§1.543) delivers a capital
--          PRE-regular `Ā` with a faithful `Map A → Ā`, BUT the §2.218 `Rel(homRep Ā)` path needs
--          TWO facts about `Ā` that the colimit does NOT surface — VERIFIED genuine gaps (R3
--          INVESTIGATED 2026-06, both confirmed against the actual defs, NOT stale):
--          (a) `RegularCategory Ā` (i.e. `HasImages Ā`).  STATUS (2026-06): the colimit `HasImages`
--              MACHINERY now exists and is axiom-clean — `Colim.colimitHasImages` (Freyd/
--              CatColimitRegular.lean) builds `HasImages C.Obj` from per-stage images + transition
--              image-preservation (each colimit map factors at a stage as cover-then-mono;
--              `coverMono_isImage` makes that an image; `Colim.objIncl_preserves_images` is the
--              per-stage statement).  `capitalization_of_capData_regular` (Freyd/Capitalization.lean)
--              ASSEMBLES `RegularCategory Ā` (capital + faithful) from a `CapData` PLUS the three
--              image hypotheses `hi`/`hmono`/`himgpres`.  THREADED (2026-06): the generic regular
--              entry point `Freyd.capitalization_regular_of_cofinalSystem` (Freyd/Capitalization-
--              Transfinite.lean) now delivers `RegularCategory Ā` (capital + faithful) directly from a
--              cofinal `CatSystem` + per-stage `hi : ∀ i, HasImages (C.A i)` + `hcovpres` (covers
--              preserved); it derives transition image-preservation from cover+mono preservation via
--              `capitalization_of_capData_regular_of_covers`/`Colim.transitions_preserve_images`.  So
--              R3(a) is DONE at the generic cofinal-system level (axioms [propext,Classical.choice,
--              Quot.sound]); each concrete tower supplies `hi` from its per-stage `CapStep.stepImages`.
--          (b) `hproj` — EVERY object of `Ā` projective (every cover splits) = `ACRegularCategory`
--              (S1_57 `Projective C := every cover into C splits`; `∀ C, Choice C ↔ ∀ C, Projective C`).
--              `homRep_regularFunctor` requires this for cover/image preservation.  But `Capital`
--              (S1_52 line 167) is `∀ A, WellSupported A → WellPointed A` — WELL-POINTEDNESS, which is
--              STRICTLY WEAKER than all-objects-projective: it gives only the TERMINATOR projective
--              (`capital_one_projective`/§1.525), not arbitrary `Projective C`.  Capitalization
--              delivers well-pointedness, not the AC condition.
--          Both are genuine §1.543-colimit-structure gaps (image-factorization and
--          all-objects-projectivity must be shown to survive the ω-tower colimit; the latter is a
--          STRENGTHENING of `Capital` from well-pointed to AC-projective, not just a colimit-survival
--          statement) — surfaced as the explicit `[RegularCategory Ā]` + `hproj` hypotheses of
--          `repr_in_power_of_sets`.  Closing R3 = (i) build `HasImages`/`RegularCategory` for the
--          colimit (a `colimitRegular` strengthening of `colimitPreRegular`) and (ii) prove the
--          capitalization yields an `ACRegularCategory`, not merely `Capital`.
--   (Historical R1 note — CLOSED.)  Non-full faithfulness of `Rel(homRep)`: see the R1 block above;
--          `RegularFunctor.relMap_faithful_of_reflects` (RelCat) discharges it via `monoFactor_reflect`
--          (pullback + iso-reflection), replacing the fullness leg-lift of the old `relMap_faithful`.
--   THE STRUCTURAL ASSEMBLY IS OTHERWISE COMPLETE: with (R1)–(R3) discharged, the composite
--     A ≅ RelMapObj A ≅ RelObj(Map A) ──Rel(capInc)──▶ RelObj(Ā) ──Rel(homRep)──▶ RelObj(Set^|Ā|)
--   is a faithful `AllegoryFunctor` (compose via `AllegoryFunctor.comp`; faithfulness via
--   `AllegoryFunctor.Faithful.comp` + `AllegoryEquiv.toFun_faithful` + the (R1) variant), and
--   `RelObj (Set^I)` is a power of `Rel(Set)` (BRICK 3 `powerAllegory`, modulo the fibrewise
--   `RelObj(Set^I) ≅ (RelObj Set)^I` identification).
--
-- ASSEMBLY ROUTE.  Pre-tabular/semi-simple ⟹ tabular (§2.16(10) `splObj_tabular_of_semiSimple` /
-- §2.167 `SplCorObj.tabular_of_preTabular`); a tabular allegory A ≅ Rel(Map A) (§2.148
-- `relMap_allegoryEquiv`); Map A is regular (`mapPreLogos`).  We want a FAITHFUL allegory functor
--   A ≅ Rel(Map A)  ──Rel(F)──▶  Rel(Set^I) ≅ Rel(Set)^I .
--
--   ★ BRICK 1 — DONE.  `RegularCategory (Type u)` and `RegularCategory (I → Type u)` are real
--     instances: `Freyd.SetRegular.setRegular` / `Freyd.SetRegular.powerRegular` (Freyd/S1_62.lean),
--     with pointwise finite limits, set-images (`{b // ∃ a, f a = b}`), covers = (fibrewise)
--     surjections (`set_cover_iff_surjective` / `power_cover_iff`).  Axiom-clean; full project builds.
--
--   ★ BRICK 3 — DONE.  `Freyd.PowerAllegory.powerAllegory : Allegory (PowerObj I 𝒜)` for any
--     `[Allegory 𝒜]` (Freyd/RelCat.lean), all ops POINTWISE, every axiom lifted from the fibre by
--     `funext` (`powerCatAlg` + `powerAllegory`; `power_{comp,id,recip,inter}_apply` simp lemmas).
--     `PowerObj I 𝒜 := I → 𝒜` is a type synonym so the new `Cat`/`Allegory` instances do not clash
--     with the bespoke `Cat (I → Type w)` (S1_55 `powerCat`).  The §2.218 target `Rel(Set)^I` is an
--     allegory-power, exactly this carrier.  Axiom-clean [Quot.sound].
--     (The remaining `Rel(Set^I) ≅ Rel(Set)^I` "a relation in Set^I = a fibrewise family of
--      relations" comparison is the only un-built half of BRICK 3 — routine, see below.)
--
--   ◐ BRICK 2 — INFRASTRUCTURE + RECIPROCATION DONE (Freyd/RelCat.lean, namespace `RelFunctor`):
--       • `RegularFunctor F` — a functor between regular categories preserving binary products,
--         covers, monos, images (the data to transport relations).
--       • `relImageObj hreg R : BinRel D (F A) (F B)` — `Rel(F)` on a span: image of
--         `⟨F R.colA, F R.colB⟩` (joint-monic proof discharged).
--       • `relImageObj_mono` — monotone for `RelLe` (images are monotone; `F` preserves the
--         witness), so the hom action descends to `RelLe`-classes.
--       • `RegularFunctor.relMap` — the hom action `BinRelQuot C A B → BinRelQuot D (F A) (F B)`.
--       • `RegularFunctor.relMap_recip` — **`Rel(F)` preserves `°`** (proven via the product-swap
--         iso + image-uniqueness: `Subobject.postIso`/`isImage_postIso`/`swapImage_isImage`).
--     RESIDUAL WALL (the genuine ~300-line analytic core, NOT faked):
--       (2a) `map_comp` + `map_inter`: need the Beck–Chevalley identity "image of (F-applied
--            composite/intersection span) = F-image of (the pullback-image span)", i.e. that `F`
--            preserving pullbacks + covers makes image commute with `F` on the §1.56 compose/meet
--            constructions.  `map_recip`/`map_id` are cheap (done/trivial); these two are not.
--       (2b) FAITHFULNESS of `Rel(F)` from `F` faithful + reflects-monos (uses image reflection).
--       (2c) the capital hom-rep `‾Map A → Set^I` (after §1.543 capitalization) IS a
--            `RegularFunctor` (cover-preservation via `homRep_preserves_cover_pointwise` +
--            `Capital`-projectivity; image-preservation from cover+mono preservation).
--     With (2a)–(2c), the composite  A ≅ Rel(Map A) ↪ Rel(‾Map A) → Rel(Set^I) ≅ Rel(Set)^I
--     (capitalization faithful, BRICK 3 power-comparison) is the §2.218 faithful representation.

/-! ## §2.219  Semi-simplicity criterion for positive allegories

  "A positive allegory is semi-simple iff for every S such that S° = S and Dom(S) ⊆ S
  there exists R such that S = R°R."

  Within the allegory world: `PositiveAllegory`, `SemiSimpleAllegory`, `dom`.
  The book's `Dom(S)` is the *domain* coreflexive, but the §2.219 condition is
  about `Dom S ⊑ S`, i.e. `1 ∩ SS° ⊑ S`, which for a symmetric morphism means
  `S ≫ S ⊑ S` (see §2.219 proof sketch: apply to the matrix (1,T;T°,1)).

  The proof of ⇐ constructs `R = (F ∪ G) ≫ Dom(S)` from a semi-simple factoring
  `S = F°G`; the ⇒ direction uses the matrix argument.  Signature not yet typed
  because `dom` in this repo is `1 ∩ R ≫ R°` but the §2.219 condition needs careful
  alignment with the distributive-allegory zero. -/

section S219

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-! ### §2.219  Forward direction: semi-simple + symmetric + dom-bounded → R°R-form

  The book's proof: given `S = F°≫G` (semi-simple), `S°=S`, `dom S ⊑ S`, take
  `R = (F ∪ G) ≫ dom S`.  Then `R° = dom S ≫ (G° ∪ F°)` and
  `R°R = dom S ≫ (G°∪F°)≫(F∪G)≫dom S`.  Expanding via distributivity gives four
  terms `G°F ∪ G°G ∪ F°F ∪ F°G`.  Using `G°F = S°= S = F°G` and `F°F, G°G ⊑ 1`:
  - **Upper bound:** `(G°∪F°)≫(F∪G) ⊑ S ∪ 1`, and `dom S ≫ (S∪1) ≫ dom S ⊑ S`
    (by coreflexivity of `dom S` plus `dom S ⊑ S`).
  - **Lower bound:** `S ⊑ dom S ≫ S ≫ dom S ⊑ dom S ≫ (G°∪F°)≫(F∪G)≫dom S`
    (using `le_dom_comp` + symmetry of `dom S` + `S ⊑ (G°∪F°)≫(F∪G)`). -/

/-- §2.219 (⇒): If `S` is semi-simple, symmetric (`S°=S`), and `dom S ⊑ S`, then
    `S = R°≫R` for some `R`.  Proof: take `R = (F ∪ G) ≫ dom S` from the semi-simple
    factoring `S = F°≫G`.  See the module doc for the algebra. -/
theorem semiSimple_sym_dom_to_polar {a : 𝒜} (S : a ⟶ a)
    (hS_sym : S° = S) (hdom_le : dom S ⊑ S) (hSS : SemiSimple S) :
    ∃ (c : 𝒜) (R : c ⟶ a), S = R° ≫ R := by
  obtain ⟨c, F, G, hF, hG, hS_eq⟩ := hSS
  refine ⟨c, (F ∪ G) ≫ dom S, ?_⟩
  have hD : dom S ⊑ Cat.id a := dom_coreflexive S
  have hdomSym : (dom S)° = dom S :=
    symmetric_eq (coreflexive_symmetric_idempotent hD).1
  have hGF : G° ≫ F = S := by
    have key : (F° ≫ G)° = G° ≫ F := by rw [Allegory.recip_comp, Allegory.recip_recip]
    rw [← key, ← hS_eq, hS_sym]
  rw [show ((F ∪ G) ≫ dom S)° ≫ ((F ∪ G) ≫ dom S) =
      dom S ≫ (G° ∪ F°) ≫ (F ∪ G) ≫ dom S from by
    rw [Allegory.recip_comp, hdomSym, recip_union, Cat.assoc]]
  -- (G°∪F°)≫(F∪G) = G°F ∪ G°G ∪ F°F ∪ F°G, bounded above by S ∪ 1
  have hExpand_le : (G° ∪ F°) ≫ (F ∪ G) ⊑ S ∪ Cat.id a := by
    rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib,
        DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · apply union_lub; · rw [hGF]; exact le_union_left _ _
      · exact le_trans hG (le_union_right _ _)
    · apply union_lub; · exact le_trans hF (le_union_right _ _)
      · rw [hS_eq]; exact le_union_left _ _
  -- S ⊑ (G°∪F°)≫(F∪G): S = F°G ⊑ the union term
  have hS_le_expand : S ⊑ (G° ∪ F°) ≫ (F ∪ G) := by
    rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib,
        DistributiveAllegory.comp_union_distrib, hS_eq]
    exact le_trans (le_union_right _ _) (le_union_right _ _)
  -- Upper bound: dom S ≫ (G°∪F°)≫(F∪G)≫dom S ⊑ S
  have hUB : dom S ≫ (G° ∪ F°) ≫ (F ∪ G) ≫ dom S ⊑ S := by
    have hstep : dom S ≫ (G° ∪ F°) ≫ (F ∪ G) ≫ dom S ⊑ dom S ≫ (S ∪ Cat.id a) ≫ dom S :=
      comp_mono_left _ (by rw [← Cat.assoc]; exact comp_mono_right hExpand_le _)
    apply le_trans hstep
    rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · have h1 : dom S ≫ (S ≫ dom S) ⊑ Cat.id a ≫ (S ≫ dom S) := comp_mono_right hD _
      rw [Cat.id_comp] at h1
      have h2 : S ≫ dom S ⊑ S := by have h := comp_mono_left S hD; rwa [Cat.comp_id] at h
      exact le_trans h1 h2
    · rw [Cat.id_comp, (coreflexive_symmetric_idempotent hD).2]; exact hdom_le
  -- Lower bound: S ⊑ dom S ≫ (G°∪F°)≫(F∪G)≫dom S
  have hLB : S ⊑ dom S ≫ (G° ∪ F°) ≫ (F ∪ G) ≫ dom S := by
    have h1 : S ⊑ dom S ≫ S := le_dom_comp S
    have h2 : S ⊑ S ≫ dom S := by
      have := recip_mono h1; rw [Allegory.recip_comp, hdomSym, hS_sym] at this; exact this
    have h4 : S ≫ dom S ⊑ (G° ∪ F°) ≫ (F ∪ G) ≫ dom S := by
      have key := comp_mono_right hS_le_expand (dom S); rw [Cat.assoc] at key; exact key
    exact le_trans h1 (le_trans (comp_mono_left _ h2) (comp_mono_left _ h4))
  exact le_antisymm hLB hUB

end S219

/-! ### §2.219  Reverse direction lives in a `PositiveAllegory`-only context.
    A separate section with a single allegory instance avoids the `Cat` diamond that
    would arise from having both `[DistributiveAllegory 𝒜]` (the §2.219⇒ section) and
    `[PositiveAllegory 𝒜]` in scope simultaneously. -/
section S219Positive

variable {𝒜 : Type u} [PositiveAllegory 𝒜]

/-- The `(1, T; T°, 1)` matrix on the coproduct `ab = coprod a b`, written in the single
    hom-set `ab ⟶ ab` via the injections `u₁ = cp.u₁`, `u₂ = cp.u₂` (§2.219 ⇐). -/
private def matrixS {a b : 𝒜}
    (cp : Coproduct (PositiveAllegory.coprod a b) a b) (T : a ⟶ b) :
    (PositiveAllegory.coprod a b) ⟶ (PositiveAllegory.coprod a b) :=
  ((cp.u₁° ≫ cp.u₁) ∪ (cp.u₁° ≫ (T ≫ cp.u₂))) ∪
    ((cp.u₂° ≫ (T° ≫ cp.u₁)) ∪ (cp.u₂° ≫ cp.u₂))

/-- Union AC permutation used to reassemble `S°` into `S` (swaps the two outer ends). -/
private theorem union_four_ac {a b : 𝒜} (w x y z : a ⟶ b) :
    (w ∪ x) ∪ (y ∪ z) = (z ∪ x) ∪ (y ∪ w) := by
  apply le_antisymm
  · exact union_lub
      (union_lub
        (le_trans (le_union_right _ _) (le_union_right _ _))
        (le_trans (le_union_right _ _) (le_union_left _ _)))
      (union_lub
        (le_trans (le_union_left _ _) (le_union_right _ _))
        (le_trans (le_union_left _ _) (le_union_left _ _)))
  · exact union_lub
      (union_lub
        (le_trans (le_union_right _ _) (le_union_right _ _))
        (le_trans (le_union_right _ _) (le_union_left _ _)))
      (union_lub
        (le_trans (le_union_left _ _) (le_union_right _ _))
        (le_trans (le_union_left _ _) (le_union_left _ _)))

/-! ### §2.219  Reverse direction and full iff (the matrix argument)

  Given `T : a ⟶ b`, work in the coproduct `ab = coprod a b` with injections
  `u₁ : a ⟶ ab`, `u₂ : b ⟶ ab`.  Form the symmetric, reflexive
    `S = u₁°u₁ ∪ u₁°Tu₂ ∪ u₂°T°u₁ ∪ u₂°u₂ : ab ⟶ ab`
  (the "matrix" `(1, T; T°, 1)` written in the single hom-set `ab ⟶ ab`).  The polar
  hypothesis gives `S = R°≫R`.  Sandwiching with the injections reads off:
    `u₁≫S≫u₂° = T`,  `u₁≫S≫u₁° = 1`,  `u₂≫S≫u₂° = 1`
  (all cross terms vanish via `u₁u₂° = 0 = u₂u₁°`).  Hence with `F = R≫u₁°`,
  `G = R≫u₂°` we get `T = F°≫G`, `F°F = u₁≫S≫u₁° = 1` (so `Simple F`) and likewise
  `G°G = 1` (so `Simple G`); thus `T` is semi-simple. -/

/-- §2.219: A positive allegory is semi-simple iff for every `S : a ⟶ a` with `S° = S`
    and `dom S ⊑ S` there is `R : c ⟶ a` with `S = R°≫R`.  (`mp` from
    `semiSimple_sym_dom_to_polar`; `mpr` is the matrix argument above.) -/
theorem positive_semiSimple_iff :
    (∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) ↔
    (∀ {a : 𝒜} (S : a ⟶ a), S° = S → dom S ⊑ S → ∃ (c : 𝒜) (R : c ⟶ a), S = R° ≫ R) := by
  constructor
  · intro hSS _ S hSym hDom; exact semiSimple_sym_dom_to_polar S hSym hDom (hSS S)
  · intro hCond a b T
    -- the coproduct ab = a ⊕ b with injections u₁ : a ⟶ ab, u₂ : b ⟶ ab
    let cp := PositiveAllegory.has_coproduct a b
    let u₁ := cp.u₁
    let u₂ := cp.u₂
    -- the matrix S = (1, T; T°, 1)
    let S := matrixS cp T
    have hS : S = ((u₁° ≫ u₁) ∪ (u₁° ≫ (T ≫ u₂))) ∪ ((u₂° ≫ (T° ≫ u₁)) ∪ (u₂° ≫ u₂)) := rfl
    -- the four coproduct equations on the injections
    have e11 : u₁ ≫ u₁° = Cat.id a := cp.u₁_self_comp_recip
    have e12 : u₁ ≫ u₂° = (𝟘 : a ⟶ b) := cp.u₁_u₂_recip
    have e21 : u₂ ≫ u₁° = (𝟘 : b ⟶ a) := cp.u₂_u₁_recip
    have e22 : u₂ ≫ u₂° = Cat.id b := cp.u₂_self_comp_recip
    -- `u_i ≫ X ≫ u_j°` reassociated to `(u_i ≫ left) ≫ (right ≫ u_j°)`-free atoms.
    -- We compute the three sandwiches we need by distributing over the 4-term union.
    -- Sandwich helper rewrites for the four summands under `u_i ≫ · ≫ u_j°`.
    -- S° = S : reciprocate the four terms; term1, term4 are self-symmetric, term2 ↔ term3.
    have hSym : S° = S := by
      -- reciprocals of the four summands (terms 1,4 self-symmetric; 2 ↔ 3 swap)
      have rA : (u₁° ≫ u₁)° = u₁° ≫ u₁ := by
        rw [Allegory.recip_comp, Allegory.recip_recip]
      have rD : (u₂° ≫ u₂)° = u₂° ≫ u₂ := by
        rw [Allegory.recip_comp, Allegory.recip_recip]
      have rB : (u₁° ≫ (T ≫ u₂))° = u₂° ≫ (T° ≫ u₁) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      have rC : (u₂° ≫ (T° ≫ u₁))° = u₁° ≫ (T ≫ u₂) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip,
            Allegory.recip_recip, Cat.assoc]
      rw [hS, recip_union, recip_union, recip_union, rA, rB, rC, rD]
      -- goal: (D ∪ B) ∪ (C ∪ A) = (A ∪ B) ∪ (C ∪ D), pure union AC.
      exact union_four_ac (u₂° ≫ u₂) (u₁° ≫ (T ≫ u₂)) (u₂° ≫ (T° ≫ u₁)) (u₁° ≫ u₁)
    -- id ⊑ S : id = u₁°u₁ ∪ u₂°u₂ ⊑ S (both are among S's summands).
    have hid_le_S : Cat.id (PositiveAllegory.coprod a b) ⊑ S := by
      rw [← cp.recip_union_eq_id, hS]
      exact union_lub
        (le_trans (le_union_left _ _) (le_union_left _ _))
        (le_trans (le_union_right _ _) (le_union_right _ _))
    -- dom S ⊑ S, via dom S ⊑ id ⊑ S
    have hdom_le_S : dom S ⊑ S := le_trans (dom_coreflexive S) hid_le_S
    -- apply the polar hypothesis
    obtain ⟨c, R, hSR⟩ := hCond S hSym hdom_le_S
    -- Read off the three sandwiches of S.  General term-collapse helpers:
    -- u_i ≫ (u₁°≫u₁) ≫ u_j° = (u_i≫u₁°) ≫ (u₁≫u_j°)
    -- Compute u₁ ≫ S ≫ u₂° = T
    have hT : u₁ ≫ S ≫ u₂° = T := by
      rw [hS]
      simp only [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
      -- four sandwich terms; collapse each via assoc + coproduct eqns
      have t1 : u₁ ≫ (u₁° ≫ u₁) ≫ u₂° = (𝟘 : a ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e11, Cat.id_comp, e12]
      have t2 : u₁ ≫ (u₁° ≫ T ≫ u₂) ≫ u₂° = T := by
        rw [← Cat.assoc, ← Cat.assoc, e11, Cat.id_comp, Cat.assoc, e22, Cat.comp_id]
      have t3 : u₁ ≫ (u₂° ≫ T° ≫ u₁) ≫ u₂° = (𝟘 : a ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e12, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      have t4 : u₁ ≫ (u₂° ≫ u₂) ≫ u₂° = (𝟘 : a ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e12, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      rw [t1, t2, t3, t4, union_zero, DistributiveAllegory.zero_union, union_zero]
    -- Compute u₁ ≫ S ≫ u₁° = id_a
    have hF : u₁ ≫ S ≫ u₁° = Cat.id a := by
      rw [hS]
      simp only [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
      have t1 : u₁ ≫ (u₁° ≫ u₁) ≫ u₁° = Cat.id a := by
        rw [← Cat.assoc, ← Cat.assoc, e11, Cat.id_comp, e11]
      have t2 : u₁ ≫ (u₁° ≫ T ≫ u₂) ≫ u₁° = (𝟘 : a ⟶ a) := by
        rw [← Cat.assoc, ← Cat.assoc, e11, Cat.id_comp, Cat.assoc, e21,
            DistributiveAllegory.comp_zero]
      have t3 : u₁ ≫ (u₂° ≫ T° ≫ u₁) ≫ u₁° = (𝟘 : a ⟶ a) := by
        rw [← Cat.assoc, ← Cat.assoc, e12, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      have t4 : u₁ ≫ (u₂° ≫ u₂) ≫ u₁° = (𝟘 : a ⟶ a) := by
        rw [← Cat.assoc, ← Cat.assoc, e12, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      rw [t1, t2, t3, t4, union_zero, union_zero, union_zero]
    -- Compute u₂ ≫ S ≫ u₂° = id_b
    have hG : u₂ ≫ S ≫ u₂° = Cat.id b := by
      rw [hS]
      simp only [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
      have t1 : u₂ ≫ (u₁° ≫ u₁) ≫ u₂° = (𝟘 : b ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e21, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      have t2 : u₂ ≫ (u₁° ≫ T ≫ u₂) ≫ u₂° = (𝟘 : b ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e21, DistributiveAllegory.zero_comp,
            DistributiveAllegory.zero_comp]
      have t3 : u₂ ≫ (u₂° ≫ T° ≫ u₁) ≫ u₂° = (𝟘 : b ⟶ b) := by
        rw [← Cat.assoc, ← Cat.assoc, e22, Cat.id_comp, Cat.assoc, e12,
            DistributiveAllegory.comp_zero]
      have t4 : u₂ ≫ (u₂° ≫ u₂) ≫ u₂° = Cat.id b := by
        rw [← Cat.assoc, ← Cat.assoc, e22, Cat.id_comp, e22]
      rw [t1, t2, t3, t4, DistributiveAllegory.zero_union, DistributiveAllegory.zero_union,
          DistributiveAllegory.zero_union]
    -- Read off T = (R≫u₁°)° ≫ (R≫u₂°), and F°F = 1, G°G = 1.
    refine ⟨c, R ≫ u₁°, R ≫ u₂°, ?_, ?_, ?_⟩
    · -- Simple (R ≫ u₁°) : (R≫u₁°)° ≫ (R≫u₁°) ⊑ id
      have : (R ≫ u₁°)° ≫ (R ≫ u₁°) = Cat.id a := by
        rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, ← Cat.assoc R° R,
            ← hSR]
        -- now: u₁ ≫ (S ≫ u₁°)  -- need u₁ ≫ S ≫ u₁°
        rw [← Cat.assoc] at hF ⊢; exact hF
      rw [Simple, this]; exact le_refl _
    · -- Simple (R ≫ u₂°)
      have : (R ≫ u₂°)° ≫ (R ≫ u₂°) = Cat.id b := by
        rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, ← Cat.assoc R° R,
            ← hSR]
        rw [← Cat.assoc] at hG ⊢; exact hG
      rw [Simple, this]; exact le_refl _
    · -- T = (R≫u₁°)° ≫ (R≫u₂°)
      rw [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc, ← Cat.assoc R° R, ← hSR]
      rw [← Cat.assoc] at hT ⊢; exact hT.symm

end S219Positive

end Freyd.Alg
