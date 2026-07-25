/-
  Freyd & Scedrov, *Categories and Allegories* §1.44  The slice category A/B.

  §1.44  Σ : A/B → A forgetful functor.  A/B has a distinguished terminator
         ⟨B, id_B⟩, carried by Σ to B.  Σ does not preserve terminators unless
         B is a terminator in A (in which case Σ is an isomorphism).

  §1.441 If A has pullbacks then A/B is Cartesian and Σ preserves pullbacks
         and equalizers.  Σ is faithful.
-/

import Freyd.S1_10
import Freyd.S1_18
import Freyd.S1_26
import Freyd.S1_42
import Freyd.S1_45
import Freyd.S1_27
import Freyd.S1_444_Horn
import Freyd.S1_422_FunctorCategory


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.44  The forgetful functor Σ : A/B → A -/

/-- The forgetful functor Σ : A/B → A (§1.44).  Sends ⟨X, h:X→B⟩ to X,
    and a slice morphism to its underlying arrow (`.f`). -/
def SliceForget (B : 𝒞) : Over B → 𝒞 := λ X => X.dom

/-! ### Distinguished terminator in A/B -/

/-- **§1.44**: The identity `id_B : B → B` is the distinguished terminator in A/B.
    For any Over object X = ⟨X, h:X→B⟩, the unique map to ⟨B, id_B⟩ is h itself. -/
def overTerm (B : 𝒞) : Over B := ⟨B, Cat.id B⟩

instance overHasTerminal (B : 𝒞) : HasTerminal (Over B) where
  one := overTerm B
  trm X := ⟨X.hom, by simpa [overTerm] using (Cat.comp_id X.hom)⟩
  uniq {X} f g := OverHom.ext (by
    have hf : f.f = X.hom := by simpa [overTerm, Cat.comp_id] using f.w
    have hg : g.f = X.hom := by simpa [overTerm, Cat.comp_id] using g.w
    rw [hf, hg])

/-- Σ carries the slice terminator to B.  Σ does NOT preserve terminators unless
    B itself is a terminator in A.  (If B ≅ 1_A then Σ is an isomorphism.) -/
theorem sliceForget_term (B : 𝒞) : SliceForget B (overTerm B) = B := rfl

/-! ## §1.441  Pullbacks in A/B; Σ preserves pullbacks -/

variable [hpull : HasPullbacks 𝒞]

section overPullback

variable {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z)

/-- The underlying pullback in A of `m.f` and `n.f`. -/
private def _pb : HasPullback m.f n.f := hpull.has m.f n.f

private theorem _pb_hom_eq :
    (_pb m n).cone.π₂ ≫ Y.hom = (_pb m n).cone.π₁ ≫ X.hom := by
  calc
    (_pb m n).cone.π₂ ≫ Y.hom   = (_pb m n).cone.π₂ ≫ (n.f ≫ Z.hom) := by rw [← n.w]
    _ = ((_pb m n).cone.π₂ ≫ n.f) ≫ Z.hom := by rw [Cat.assoc]
    _ = ((_pb m n).cone.π₁ ≫ m.f) ≫ Z.hom := by rw [(_pb m n).cone.w]
    _ = (_pb m n).cone.π₁ ≫ (m.f ≫ Z.hom) := by rw [← Cat.assoc]
    _ = (_pb m n).cone.π₁ ≫ X.hom         := by rw [m.w]

/-- **§1.441**: The pullback object in A/B.  The point is the pullback point in A,
    with structure map `π₁ ≫ X.hom` (= `π₂ ≫ Y.hom`). -/
def overPullbackPt : Over B :=
  ⟨(_pb m n).cone.pt, (_pb m n).cone.π₁ ≫ X.hom⟩

/-- First projection of the overPullback. -/
def overPullbackπ₁ : OverHom (overPullbackPt m n) X :=
  ⟨(_pb m n).cone.π₁, rfl⟩

/-- Second projection of the overPullback. -/
def overPullbackπ₂ : OverHom (overPullbackPt m n) Y :=
  ⟨(_pb m n).cone.π₂, _pb_hom_eq m n⟩

/-- The pullback square commutes in A/B. -/
theorem overPullback_sq : overPullbackπ₁ m n ⊚ m = overPullbackπ₂ m n ⊚ n :=
  OverHom.ext ((_pb m n).cone.w)

/-- The universal lift for the overPullback.  Given a cone in A/B, the lift
    in A also respects the Over structure. -/
def overPullbackLift {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n) :
    OverHom W (overPullbackPt m n) :=
  let h_base := congrArg OverHom.f h
  let c : Cone m.f n.f := ⟨W.dom, a.f, b.f, h_base⟩
  let u := (_pb m n).lift c
  ⟨u, by
    dsimp [overPullbackPt, u]
    calc u ≫ ((_pb m n).cone.π₁ ≫ X.hom) = (u ≫ (_pb m n).cone.π₁) ≫ X.hom := by rw [Cat.assoc]
      _ = a.f ≫ X.hom := by rw [(_pb m n).lift_fst c]
      _ = W.hom      := a.w⟩

theorem overPullbackLift_uniq {W : Over B} (a : OverHom W X) (b : OverHom W Y) (h : a ⊚ m = b ⊚ n)
    (u : OverHom W (overPullbackPt m n))
    (hu₁ : u ⊚ overPullbackπ₁ m n = a) (hu₂ : u ⊚ overPullbackπ₂ m n = b) :
    u = overPullbackLift m n a b h :=
  OverHom.ext ((_pb m n).lift_uniq ⟨W.dom, a.f, b.f, congrArg OverHom.f h⟩ u.f
    (congrArg OverHom.f hu₁) (congrArg OverHom.f hu₂))

end overPullback

/-! ## Σ preserves pullbacks (§1.441) -/

/-- **§1.441**: Σ preserves pullbacks.  Applying Σ to the pullback in A/B
    recovers the pullback in A. -/
theorem sigma_preserves_pullback_pt {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    SliceForget B (overPullbackPt m n) = (_pb m n).cone.pt := rfl

/-- **§1.441**: Σ preserves pullbacks — first projection. -/
theorem sigma_preserves_pullback_π₁ {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    (overPullbackπ₁ m n).f = (_pb m n).cone.π₁ := rfl

/-- **§1.441**: Σ preserves pullbacks — second projection. -/
theorem sigma_preserves_pullback_π₂ {B : 𝒞} {X Y Z : Over B} (m : OverHom X Z) (n : OverHom Y Z) :
    (overPullbackπ₂ m n).f = (_pb m n).cone.π₂ := rfl

/-! ## Σ is faithful (§1.442) -/

/-- **§1.442**: Σ is faithful.  Two slice morphisms are equal iff their underlying
    A-arrows are equal (this is exactly `OverHom.ext`). -/
theorem sigma_faithful {B : 𝒞} {X Y : Over B} (f g : OverHom X Y)
    (h : f.f = g.f) : f = g := OverHom.ext h

/-! ## §1.44  Universal property of Σ : A/B → A

  Freyd §1.44: Σ is universal among functors T : 𝒞 → A that carry the designated
  terminator of 𝒞 to B.  Given T with T(1) = B, there is a unique T' : 𝒞 → A/B
  with T'(1) = id_B (the slice terminator) and Σ ∘ T' = T.
  Construction: T'(C) = ⟨T.obj C, hB ▸ T.map(term_C)⟩. -/

/-- **§1.44**: The LIFT of T : 𝒞 → A along Σ.  Given T(1) = B, defines
    T'(C) = ⟨T.obj C, T(term_C) : T C → T(1) = B⟩. -/
def sliceLift {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B) :
    𝒞 → Over B :=
  fun C => ⟨T.obj C, hB ▸ T.map (term C)⟩

def sliceLift_isFunctor {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B) :
    Functor 𝒞 (Over B) where
  obj := sliceLift T hB
  map {C D} f := ⟨T.map f, by
    simp only [sliceLift]; cases hB
    rw [← T.map_comp]; congr 1; exact term_uniq _ _⟩
  map_id C := OverHom.ext (T.map_id C)
  map_comp f g := OverHom.ext (T.map_comp f g)

/-- **§1.44 — existence (terminator)**: T' carries the terminator of 𝒞 to the slice
    terminator ⟨B, id_B⟩. -/
theorem sliceLift_term {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B) :
    sliceLift T hB (one (𝒞 := 𝒞)) = overTerm B := by
  simp only [sliceLift, overTerm]
  cases hB
  congr 1
  simp [term_uniq (term (one (𝒞 := 𝒞))) (Cat.id _), T.map_id]

/-- **§1.44 — existence (Σ ∘ T' = T)**: Composing the lift with Σ recovers T. -/
theorem sliceLift_comp_sigma {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B) :
    SliceForget B ∘ sliceLift T hB = T.obj := rfl

/-- **§1.44 — existence (underlying maps)**: The underlying map of T'(f) is T(f). -/
theorem sliceLift_map_eq {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B)
    {C D : 𝒞} (f : C ⟶ D) :
    ((sliceLift_isFunctor T hB).map f).f = T.map f := rfl

/-- HEq congruence for composition across object identifications: if the three
    objects match (`X=X'`, `Y=Y'`, `Z=Z'`) and the arrows match up to HEq, then
    the composites match up to HEq.  Used to transport `OverHom.w` through the
    domain identification in `sliceLift_unique`. -/
private theorem comp_heq_congr {𝒜 : Type u} [Cat.{v} 𝒜] {X Y Z X' Y' Z' : 𝒜}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : f ≍ f') (hg : g ≍ g') : f ≫ g ≍ f' ≫ g' := by
  subst hX hY hZ; rw [eq_of_heq hf, eq_of_heq hg]

/-- A pair of `.symm ▸` object-transports on an arrow is HEq-trivial.  Strips the
    domain identifications produced by `h_map` in `sliceLift_unique`. -/
private theorem eqRec_symm_symm_heq {𝒜 : Type u} [Cat.{v} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    (hX.symm ▸ hY.symm ▸ f : X ⟶ Y) ≍ f := by
  subst hX; subst hY; rfl

/-- **§1.44 — uniqueness**: Any functor T'' : 𝒞 → A/B satisfying
    (1) T''(1_𝒞) = overTerm B  (terminator condition), and
    (2) for each morphism f, the underlying A-map of T''(f) equals T.map(f)
        up to the domain identification (Σ ∘ T'' = T on maps),
    equals the lift T'.

    We express (2) via a cast-free condition: `(T''.map f).f = (h_obj C) ▸ (h_obj D) ▸ T.map f`
    where `h_obj` gives the domain equality.

    Proof: OverHom.w on T''.map(term_C) gives
      (T''.map(term_C)).f ≫ (T''(1)).hom = (T''.obj C).hom.
    With T''(1) = ⟨B, id_B⟩: (T''.map(term_C)).f = (T''.obj C).hom.
    The domain identification + h_map show both equal hB ▸ T.map(term_C).  □ -/
theorem sliceLift_unique {𝒜 : Type u} [Cat.{v} 𝒜] {B : 𝒜}
    [HasTerminal 𝒞] (T : Functor 𝒞 𝒜) (hB : T.obj (one (𝒞 := 𝒞)) = B)
    (T'' : Functor 𝒞 (Over B))
    -- (1) T''(1_𝒞) = overTerm B
    (h_term : T''.obj (one (𝒞 := 𝒞)) = overTerm B)
    -- (2) Domain equality: Σ ∘ T'' = T on objects.
    (h_obj  : ∀ C, (T''.obj C).dom = T.obj C)
    -- (3) Map equality after domain identification: Σ ∘ T'' = T on morphisms.
    --     (T''.map f).f has type (T''.obj C).dom → (T'' D).dom;
    --     after the domain identification it equals T.map f : T C → T D.
    (h_map  : ∀ {C D : 𝒞} (f : C ⟶ D),
        (T''.map f).f = (h_obj C).symm ▸ (h_obj D).symm ▸ T.map f) :
    ∀ C, T''.obj C = sliceLift T hB C := by
  -- Eliminate B by substituting T one = B. After subst, B disappears,
  -- overTerm (T one) = ⟨T one, Cat.id (T one)⟩, sliceLift T rfl C = ⟨T.obj C, T.map(term C)⟩.
  subst hB
  -- Decompose h_term via Over.mk.injEq to get HEq on the hom field, then unfold
  -- overTerm so the resulting equalities mention `T one` / `Cat.id (T one)`.
  rw [Over.mk.injEq] at h_term
  obtain ⟨h_one_dom, h_one_hom⟩ := h_term
  simp only [overTerm] at h_one_dom h_one_hom
  -- h_one_dom : (T'' one).dom = T one
  -- h_one_hom : (T'' one).hom ≍ Cat.id (T one)
  intro C
  -- Goal: T''.obj C = sliceLift T rfl C = ⟨T.obj C, T.map(term C)⟩.
  -- Prove via Over.mk.injEq: dom-equality (h_obj C) + HEq on homs.
  rw [Over.mk.injEq]
  refine ⟨h_obj C, ?_⟩
  -- Goal: (T''.obj C).hom ≍ T.map (term C).
  -- OverHom.w on T''.map(term C): (T''.map (term C)).f ≫ (T'' one).hom = (T''.obj C).hom.
  have hw : (T''.map (term C)).f ≫ (T''.obj (one (𝒞 := 𝒞))).hom = (T''.obj C).hom :=
    (T''.map (term C)).w
  -- The underlying map of T''(term C) agrees with T.map(term C) up to HEq: the two
  -- ▸ transports in h_map are HEq-trivial (eqRec_heq).
  have hf_heq : (T''.map (term C)).f ≍ T.map (term C) := by
    rw [h_map (term C)]; exact eqRec_symm_symm_heq (h_obj C) (h_obj _) _
  -- Rewrite the goal using hw, then absorb the identity on the rhs and apply the
  -- composition HEq-congruence (objects matched by h_obj C, h_one_dom, rfl).
  rw [← hw]
  refine HEq.trans ?_ (heq_of_eq (Cat.comp_id (T.map (term C))))
  exact comp_heq_congr (h_obj C) h_one_dom rfl hf_heq h_one_hom

/-! ## §1.464  Yoneda representation preserves/reflects cartesian predicates

  Freyd §1.464: The covariant embedding H : A → 𝒮^(A°), B ↦ H_B = (-, B),
  is a full embedding (the YONEDA REPRESENTATION).  It preserves and reflects the
  cartesian predicates.

  The individual covariant representable `representable B = Hom(B, -)` is defined
  in S1_47.lean.  Here we instead realise the full contravariant functor-category statement, using
  `setCat : Cat (Type w)` (Horn.lean) and the functor category `𝒮^(A°)` from
  S1_27 / `FunctorCategory.lean`.  The section below shows:
    `yonedaObj`            — `H_B` is a presheaf `(OppCat 𝒞) → Type w`;
    `yonedaMap`            — `H_f` is the induced natural transformation;
    `yoneda_faithful`      — `H` is faithful (`H_f = H_g ⟹ f = g`);
    `yonedaMap_id/_comp`   — `H` is functorial;
    `yoneda_full`          — `H` is FULL (every NT H_B ⟹ H_C is H_f, Yoneda lemma);
    `yoneda_full_unique`   — the preimage `f` is unique;
    `yoneda_full_faithful` — packages full+faithful: Nat(H_B, H_C) ≅ Hom(B,C);
    `yoneda_reflects_mono` — `H` reflects monics;
    `yoneda_preserves_term`— `H` carries the terminator to a terminal presheaf;
    `yonedaProd_*`         — `H` preserves binary products (pointwise iso). -/

/-! We realise the Yoneda representation `H : A → 𝒮^(A°)` concretely.

    Universe note: `Functor 𝒜 𝒟` forces `𝒜` and `𝒟` at the *same* universe.
    For the presheaf category `Functor (OppCat 𝒞) (Type u)` to typecheck we need
    `OppCat 𝒞 : Type (u+1)` and `Type u : Type (u+1)` to agree, i.e. `𝒞 : Type (u+1)`
    with `Cat.{u} 𝒞`.  Hence this section runs in a fresh universe `w` with
    `𝒞 : Type (w+1)`; the hom-type category `setCat : Cat.{w} (Type w)` (Horn.lean)
    supplies the codomain. -/

section Yoneda464

universe w
variable {𝒞 : Type (w+1)} [inst : Cat.{w} 𝒞]

/-- Precomposition action of `H_B`: an `OppCat 𝒞`-hom `f : X ⟶ Y` (i.e. a `𝒞`-hom
    `Y ⟶ X`) sends `h : X ⟶ B` to `f ≫ h : Y ⟶ B`.  Stated with explicit `@`-comp
    in `𝒞` because `OppCat 𝒞` and `𝒞` are the *same* type, so the `≫` notation cannot
    pick the intended instance on its own. -/
def preComp (B : 𝒞) {X Y : OppCat 𝒞} (f : X ⟶ Y) (h : @Cat.Hom 𝒞 inst X B) :
    @Cat.Hom 𝒞 inst Y B :=
  @Cat.comp 𝒞 inst Y X B f h

/-- §1.464: The presheaf `H_B : (OppCat 𝒞) → Type w`, `X ↦ (X ⟶ B)`.
    The contravariant hom-functor `(-, B)`: morphisms act by precomposition. -/
def yonedaObj (B : 𝒞) : Functor (OppCat 𝒞) (Type w) where
  obj X := @Cat.Hom 𝒞 inst X B
  map := fun {X Y} f => preComp B f
  map_id := fun X => by funext h; exact @Cat.id_comp 𝒞 inst X B h
  -- `f ≫_opp g = g ≫_𝒞 f`, so `map (f≫g) h = (g≫f)≫h = g≫(f≫h)` (assoc).
  map_comp := fun {X Y Z} f g => by funext h; exact @Cat.assoc 𝒞 inst Z Y X B g f h

/-- §1.464: The natural transformation `H_f : H_B ⟹ H_C` induced by `f : B ⟶ C`,
    `app X : (X ⟶ B) → (X ⟶ C)`, `h ↦ h ≫ f` (postcomposition). -/
def yonedaMap {B C : 𝒞} (f : B ⟶ C) : FunctorHom (yonedaObj B) (yonedaObj C) where
  app X h := @Cat.comp 𝒞 inst X B C h f
  -- naturality at `g : X ⟶ Y` of `OppCat 𝒞` (= `g : Y ⟶ X` in `𝒞`):
  -- `(g ≫ h) ≫ f = g ≫ (h ≫ f)` by associativity.
  naturality {X Y} g := by funext h; exact @Cat.assoc 𝒞 inst Y X B C g h f

/-- §1.464: `H` is FAITHFUL: `H_f = H_g ⟹ f = g`.  Evaluate the components at `B`
    on `id_B`: `(H_f)_B (id_B) = id_B ≫ f = f`. -/
theorem yoneda_faithful {B C : 𝒞} (f g : B ⟶ C)
    (h : yonedaMap f = yonedaMap g) : f = g := by
  have hc := congrFun (congrFun (congrArg NaturalTransformation.app h) B) (Cat.id B)
  simpa only [yonedaMap, Cat.id_comp] using hc

/-- §1.464: `H` preserves identities: `H_{id_B} = id_{H_B}`. -/
theorem yonedaMap_id (B : 𝒞) :
    yonedaMap (Cat.id B) = natTrans_id (yonedaObj B) :=
  NaturalTransformation.ext' fun _ => funext fun h => Cat.comp_id h

/-- §1.464: `H` preserves composition: `H_{f ≫ g} = H_f ≫ H_g`. -/
theorem yonedaMap_comp {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    yonedaMap (f ≫ g) = natTrans_comp (yonedaMap f) (yonedaMap g) :=
  NaturalTransformation.ext' fun _ => funext fun h => (Cat.assoc h f g).symm

/-- §1.464: `H` REFLECTS MONICS.  If `H_m` is monic in the presheaf category then
    `m` is monic in `𝒞`.  (Together with fullness this gives reflection of the
    cartesian predicates; here we record the morphism-level statement.) -/
theorem yoneda_reflects_mono {B C : 𝒞} (m : B ⟶ C)
    (hm : Monic (𝒞 := Functor (OppCat 𝒞) (Type w)) (yonedaMap m)) : Monic m := by
  intro W f g hfg
  have hNT : natTrans_comp (yonedaMap f) (yonedaMap m)
           = natTrans_comp (yonedaMap g) (yonedaMap m) := by
    rw [← yonedaMap_comp, ← yonedaMap_comp, hfg]
  exact yoneda_faithful f g (hm (yonedaMap f) (yonedaMap g) hNT)

/-- §1.464: `H` PRESERVES TERMINATORS.  When `𝒞` has a terminator `1`, the presheaf
    `H_1 = (-, 1)` is terminal in `𝒮^(A°)`: every hom-set `X ⟶ 1` is a singleton, so
    there is a unique NT into `H_1` (`app X := fun _ => term X`) and any two agree. -/
instance yoneda_preserves_term [hT : HasTerminal 𝒞] :
    HasTerminal (Functor (OppCat 𝒞) (Type w)) where
  one := yonedaObj one
  trm _ :=
    { app := fun X _ => @term 𝒞 inst hT X
      naturality := fun {_ Y} _ => funext fun _ => @term_uniq 𝒞 inst hT Y _ _ }
  uniq {_} _ _ := NaturalTransformation.ext' fun X => funext fun _ => @term_uniq 𝒞 inst hT X _ _

/-! ### §1.464  `H` preserves binary products

  `H_{B×C}(X) ≅ H_B(X) × H_C(X)`, naturally in `X`.  We give the bijection and its
  inverse pointwise (avoiding the triple instance ambiguity that `OppCat 𝒞 = 𝒞`
  induces between products in `𝒞`, in `Type w`, and in the presheaf category). -/

variable [HasBinaryProducts 𝒞]

/-- Forward leg of `H_{B×C}(X) ≅ H_B(X) × H_C(X)`: `h ↦ (h ≫ fst, h ≫ snd)`. -/
def yonedaProdFwd (B C X : 𝒞) (h : X ⟶ prod B C) : (X ⟶ B) × (X ⟶ C) :=
  (h ≫ fst, h ≫ snd)

/-- Backward leg: `(u, v) ↦ ⟨u, v⟩ = pair u v`. -/
def yonedaProdBwd (B C X : 𝒞) (p : (X ⟶ B) × (X ⟶ C)) : X ⟶ prod B C :=
  pair p.1 p.2

/-- §1.464: forward∘backward = id (`fst_pair`/`snd_pair`). -/
theorem yonedaProd_fwd_bwd (B C X : 𝒞) (p : (X ⟶ B) × (X ⟶ C)) :
    yonedaProdFwd B C X (yonedaProdBwd B C X p) = p :=
  Prod.ext (fst_pair _ _) (snd_pair _ _)

/-- §1.464: backward∘forward = id (`pair_uniq`).  Hence `H_{B×C}(X) ≅ H_B(X) × H_C(X)`. -/
theorem yonedaProd_bwd_fwd (B C X : 𝒞) (h : X ⟶ prod B C) :
    yonedaProdBwd B C X (yonedaProdFwd B C X h) = h :=
  (pair_uniq _ _ h rfl rfl).symm

/-- §1.464: the product iso is NATURAL in `X`: precomposition by `g : Y ⟶ X`
    commutes with the bijection. -/
theorem yonedaProd_fwd_nat (B C : 𝒞) {X Y : 𝒞} (g : Y ⟶ X) (h : X ⟶ prod B C) :
    yonedaProdFwd B C Y (g ≫ h)
      = (g ≫ (yonedaProdFwd B C X h).1, g ≫ (yonedaProdFwd B C X h).2) := by
  simp only [yonedaProdFwd]; rw [Cat.assoc, Cat.assoc]

/-! ### §1.464  FULLNESS: the Yoneda embedding H : A → 𝒮^(A°) is FULL

  The YONEDA LEMMA: `Nat(H_B, H_C) ≅ Hom(B, C)`.  The bijection sends
  `α : H_B ⟹ H_C` to `α_B(id_B) : B ⟶ C`; its inverse sends `f : B ⟶ C`
  to `H_f = yonedaMap f`.

  Proof of fullness: given `α : FunctorHom (yonedaObj B) (yonedaObj C)`, set
  `f := α.app B (Cat.id B)`.  For any `X` and `h : X ⟶ B`, naturality of `α`
  at `h` (viewed as an OppCat morphism `B ⟶ X`) evaluated at `id_B` gives:
    α_X(preComp B h id_B) = preComp C h (α_B id_B)
  i.e. α_X(h ≫ id_B) = h ≫ α_B(id_B), i.e. α_X(h) = h ≫ f = (H_f)_X(h).
  So α = yonedaMap f.

  Universe note: the cross-universe gap between `Cat.{w} 𝒞` and `Cat.{w+1}`
  on `Functor (OppCat 𝒞) (Type w)` prevents use of the `Full` typeclass
  (which requires the same Cat level on source and target).  We therefore state
  fullness directly as an existence+uniqueness result. -/

/-- §1.464 (Yoneda lemma, key step): `α_X h = h ≫ α_B(id_B)` for every
    `α : H_B ⟹ H_C` and `h : X ⟶ B`.  Proved by evaluating the naturality
    square at the OppCat morphism `h : B ⟶ X` at `id_B`. -/
private theorem yoneda_app_eq {B C X : 𝒞}
    (α : FunctorHom (yonedaObj B) (yonedaObj C)) (h : @Cat.Hom 𝒞 inst X B) :
    α.app X h = h ≫ α.app B (Cat.id B) := by
  have nat := congrFun (α.naturality (f := (show @Cat.Hom (OppCat 𝒞) _ B X from h))) (Cat.id B)
  simp only [set_comp] at nat
  have key_lhs : (yonedaObj B).map
      (show @Cat.Hom (OppCat 𝒞) _ B X from h) (Cat.id B) = h :=
    @Cat.comp_id 𝒞 inst X B h
  have key_rhs : (yonedaObj C).map
      (show @Cat.Hom (OppCat 𝒞) _ B X from h) (α.app B (Cat.id B)) =
      @Cat.comp 𝒞 inst X B C h (α.app B (Cat.id B)) := rfl
  rw [key_lhs] at nat; rw [key_rhs] at nat; exact nat

/-- §1.464 FULLNESS (Yoneda lemma): every `α : H_B ⟹ H_C` equals `yonedaMap f` where
    `f := α_B(id_B) : B ⟶ C`.  The Yoneda bijection `Nat(H_B, H_C) ≅ Hom(B, C)`. -/
theorem yoneda_full {B C : 𝒞} (α : FunctorHom (yonedaObj B) (yonedaObj C)) :
    yonedaMap (α.app B (Cat.id B)) = α := by
  apply NaturalTransformation.ext'; intro X; funext h
  simp only [yonedaMap]
  exact (yoneda_app_eq α h).symm

/-- §1.464: the preimage `f` in the Yoneda bijection is unique.
    If `yonedaMap f = α` then `f = α_B(id_B)`. -/
theorem yoneda_full_unique {B C : 𝒞} (α : FunctorHom (yonedaObj B) (yonedaObj C))
    (f : B ⟶ C) (hf : yonedaMap f = α) : f = α.app B (Cat.id B) :=
  yoneda_faithful f (α.app B (Cat.id B))
    (hf.trans (yoneda_full α).symm)

/-- §1.464: FULL + FAITHFUL packaging.  The Yoneda embedding `H : A → 𝒮^(A°)`
    is full and faithful: for every `α : H_B ⟹ H_C` there exists a unique
    `f : B ⟶ C` with `yonedaMap f = α`.  This is the Yoneda bijection
    `Nat(H_B, H_C) ≅ Hom(B, C)`.

    Note: `Full` and `Embedding` typeclasses require source and target at the
    same Cat hom-universe, which fails here (Cat.{w} vs Cat.{w+1} on the presheaf
    category).  The result is therefore stated as a direct ∃-∀ proposition. -/
theorem yoneda_full_faithful {B C : 𝒞} (α : FunctorHom (yonedaObj B) (yonedaObj C)) :
    ∃ f : B ⟶ C, yonedaMap f = α ∧ ∀ g : B ⟶ C, yonedaMap g = α → g = f :=
  ⟨α.app B (Cat.id B), yoneda_full α, fun g hg => yoneda_full_unique α g hg⟩

end Yoneda464

/-! ## §1.531  Σ as a `Functor`; preservation / reflection of monos

  `Σ : A/B → A` is genuinely cross-universe (`Over B : Type (max u v)`,
  `A : Type u`), so it uses the `Monic`-specific `PreservesMono`/`ReflectsMono`
  (where `Monic` is applied directly, hence universe-clean) rather than the generic
  single-universe `Preserves`/`Reflects`. -/

/-- Σ : A/B → A is a functor; its action on arrows is the underlying arrow `.f`. -/
def sliceForgetFunctor (B : 𝒞) : Functor (Over B) 𝒞 where
  obj := SliceForget B
  map f := f.f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **§1.531**: Σ preserves monos.  If `m` is mono in A/B then `m.f` (= Σ m) is mono in A.
    This is the non-trivial direction of the Slice Lemma. -/
theorem sigma_preserves_mono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y)
    (hm : OverMono m) : Monic m.f := by
  intro D p q hpq
  have wq : q ≫ Z.hom = p ≫ Z.hom := by
    rw [← m.w, ← Cat.assoc, ← Cat.assoc, hpq]
  let W : Over B := ⟨D, p ≫ Z.hom⟩
  let pp : OverHom W Z := ⟨p, rfl⟩
  let qq : OverHom W Z := ⟨q, wq⟩
  have h_eq : pp ⊚ m = qq ⊚ m := OverHom.ext hpq
  exact congrArg OverHom.f (hm pp qq h_eq)

/-- **§1.531**: Σ reflects monos.  If `m.f` is mono in A then `m` is mono in A/B.
    This direction follows from the definition. -/
theorem sigma_reflects_mono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y)
    (hmMono : Monic m.f) : OverMono m := by
  intro W g h h_eq
  apply OverHom.ext
  apply hmMono
  exact congrArg OverHom.f h_eq

/-- **§1.531** in the preservation vocabulary: Σ preserves monos. -/
theorem slice_preservesMono (B : 𝒞) : PreservesMono (sliceForgetFunctor B) := by
  intro Z Y m hm
  exact sigma_preserves_mono m hm

/-- **§1.531** in the reflection vocabulary: Σ reflects monos. -/
theorem slice_reflectsMono (B : 𝒞) : ReflectsMono (sliceForgetFunctor B) := by
  intro Z Y m hm
  exact sigma_reflects_mono m hm

end Freyd
