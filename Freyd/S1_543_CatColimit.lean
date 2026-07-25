/-
  Directed (filtered) colimit of categories — Milestone 2a (objects only).

  A `CatSystem` is a directed system of categories over `(ι, D)`: a family of
  categories `A i` with transition functors `F hij : A i → A j` respecting
  identity and composition on objects.  Its colimit's OBJECT type is the
  type-level directed colimit (Milestone 1) of the object families.  The
  hom-colimit and the `Cat` instance on the colimit are Milestone 2b.

  Category theory is hand-built on this repo's `Cat`; no mathlib here.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_543_DirectedColimit

open Freyd

namespace Freyd.Colim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- A directed system of categories over `(ι, D)`: each `A i` is a category
    (`catA i`); for `i ≤ j` a functor `F hij : A i → A j` (`functF hij`), with
    `F` respecting identity and composition on objects. -/
structure CatSystem (ι : Type u) (D : Directed ι) where
  A : ι → Type w
  catA : ∀ i, Cat.{w} (A i)
  F : ∀ {i j}, D.le i j → A i → A j
  Fmap : ∀ {i j} (hij : D.le i j) {x y : A i},
    @Cat.Hom (A i) (catA i) x y → @Cat.Hom (A j) (catA j) (F hij x) (F hij y)
  Fmap_id : ∀ {i j} (hij : D.le i j) (x : A i),
    Fmap hij (@Cat.id (A i) (catA i) x) = @Cat.id (A j) (catA j) (F hij x)
  Fmap_comp : ∀ {i j} (hij : D.le i j) {x y z : A i}
    (f : @Cat.Hom (A i) (catA i) x y) (g : @Cat.Hom (A i) (catA i) y z),
    Fmap hij (@Cat.comp (A i) (catA i) x y z f g)
      = @Cat.comp (A j) (catA j) (F hij x) (F hij y) (F hij z) (Fmap hij f) (Fmap hij g)
  F_refl : ∀ {i} (x : A i), F (D.refl i) x = x
  F_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k) (x : A i),
    F (D.trans hij hjk) x = F hjk (F hij x)

attribute [instance] CatSystem.catA

/-- The transition functor `A i → A j` as a bundled `Functor`, assembled from the
    object action `F` and the morphism action `Fmap`.  (The object action `F` stays a
    field of its own because the colimit needs the *strict* object coherences
    `F_refl`/`F_trans`, which a bundled functor does not record.) -/
def CatSystem.functF (C : CatSystem ι D) {i j} (hij : D.le i j) : Functor (C.A i) (C.A j) where
  obj := C.F hij
  map := C.Fmap hij
  map_id := C.Fmap_id hij
  map_comp := C.Fmap_comp hij

/-- Morphism-level coherence of the transition functors: an identity transition
    acts as the identity functor and composite transitions compose, on *morphisms*
    (up to the object-equalities `F_refl`/`F_trans`, hence stated with `HEq`).
    Together with the object coherence this makes `C` a genuine functor
    `(ι, ≤) → Cat`. -/
structure CatSystem.Coherent (C : CatSystem ι D) : Prop where
  refl_map : ∀ {i : ι} {x x' : C.A i} (g : x ⟶ x'),
    HEq (C.Fmap (D.refl i) g) g
  trans_map : ∀ {i j k : ι} (hij : D.le i j) (hjk : D.le j k) {x x' : C.A i} (g : x ⟶ x'),
    HEq (C.Fmap (D.trans hij hjk) g) (C.Fmap hjk (C.Fmap hij g))

/-- The underlying directed system of OBJECT types of a `CatSystem` (forget the
    morphisms): exactly a Milestone-1 `System`. -/
def CatSystem.objSystem (C : CatSystem ι D) : System ι D where
  X := C.A
  tr := C.F
  tr_refl := C.F_refl
  tr_trans := C.F_trans

/-- The OBJECTS of the colimit category: the type-level directed colimit of the
    object families. -/
def CatSystem.Obj (C : CatSystem ι D) : Type _ := Colimit C.objSystem

/-- The canonical inclusion of stage-`i` objects into the colimit's objects. -/
def CatSystem.objIncl (C : CatSystem ι D) (i : ι) (x : C.A i) : C.Obj :=
  incl C.objSystem i x

/-- Inclusions of objects are compatible with the transition functors. -/
theorem CatSystem.objIncl_compat (C : CatSystem ι D) {i j : ι} (hij : D.le i j) (x : C.A i) :
    C.objIncl j (C.F hij x) = C.objIncl i x :=
  incl_compat C.objSystem hij x

/-! ## Milestone 2b — the index of the hom-colimit

  A morphism `[⟨i,x⟩] → [⟨j,y⟩]` in the colimit will be a class in the directed
  colimit, over the common upper bounds `k` of `i` and `j`, of `Hom_{A k}(F x, F y)`.
  The first ingredient is that those upper bounds form a directed set. -/

/-- The common upper bounds of `i` and `j` in a directed preorder. -/
def UpperBound (D : Directed ι) (i j : ι) : Type u := {k : ι // D.le i k ∧ D.le j k}

/-- The common upper bounds of `i, j` are themselves a directed preorder (order
    inherited from `D`); this is the index set of the hom-colimit. -/
def upperDirected (D : Directed ι) (i j : ι) : Directed (UpperBound D i j) where
  le a b := D.le a.1 b.1
  refl a := D.refl a.1
  trans hab hbc := D.trans hab hbc
  bound a b :=
    let ⟨m, ham, hbm⟩ := D.bound a.1 b.1
    ⟨⟨m, D.trans a.2.1 ham, D.trans a.2.2 ham⟩, ham, hbm⟩

/-! ## Milestone 2b — transporting morphisms along object equalities

  The hom-colimit's transition map applies a transition functor and then re-types
  the result along the object equalities of `F_refl`/`F_trans`.  `castHom` is that
  re-typing; `castHom_of_heq` says a `HEq`-equal morphism transports to its partner,
  which is exactly what the colimit laws need to cancel the casts. -/

/-- Transport a morphism `m : X ⟶ Y` to `X' ⟶ Y'` along object equalities. -/
def castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y')
    (m : X ⟶ Y) : X' ⟶ Y' := hX ▸ hY ▸ m

@[simp] theorem castHom_rfl {𝒜 : Type w} [Cat.{w} 𝒜] {X Y : 𝒜} (m : X ⟶ Y) :
    castHom rfl rfl m = m := rfl

/-- A morphism heterogeneously equal to `g` transports (along the matching object
    equalities) exactly to `g`. -/
theorem castHom_of_heq {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') {m : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq m g) :
    castHom hX hY m = g := by
  subst hX; subst hY; simpa [castHom] using h

/-- Transports compose. -/
theorem castHom_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' X'' Y'' : 𝒜}
    (h1X : X = X') (h1Y : Y = Y') (h2X : X' = X'') (h2Y : Y' = Y'') (m : X ⟶ Y) :
    castHom h2X h2Y (castHom h1X h1Y m) = castHom (h1X.trans h2X) (h1Y.trans h2Y) m := by
  subst h1X; subst h1Y; subst h2X; subst h2Y; rfl

/-- Transport distributes over composition. -/
theorem castHom_comp {𝒜 : Type w} [Cat.{w} 𝒜] {X Y Z X' Y' Z' : 𝒜}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (m : X ⟶ Y) (n : Y ⟶ Z) :
    castHom hX hY m ≫ castHom hY hZ n = castHom hX hZ (m ≫ n) := by
  subst hX; subst hY; subst hZ; rfl

/-- Transport preserves identity. -/
theorem castHom_id {𝒜 : Type w} [Cat.{w} 𝒜] {X X' : 𝒜} (hX : X = X') :
    castHom hX hX (Cat.id X) = Cat.id X' := by subst hX; rfl

/-- A functor commutes with transport: mapping a transported morphism equals
    transporting the mapped morphism (along the image object-equalities). -/
theorem map_castHom {𝒜 𝒝 : Type w} [Cat.{w} 𝒜] [Cat.{w} 𝒝] (T : Functor 𝒜 𝒝)
    {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) :
    T.map (castHom hX hY m) = castHom (congrArg T.obj hX) (congrArg T.obj hY) (T.map m) := by
  subst hX; subst hY; rfl

/-- `map_castHom` specialised to a `CatSystem`'s morphism action `Fmap` (whose result
    type is stated directly over the object action `F`, so its images are syntactically
    `F`-shaped — this is what the downstream `rw [F_trans]` casts need). -/
theorem CatSystem.Fmap_castHom (C : CatSystem ι D) {i j} (hij : D.le i j)
    {X Y X' Y' : C.A i} (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) :
    C.Fmap hij (castHom hX hY m)
      = castHom (congrArg (C.F hij) hX) (congrArg (C.F hij) hY) (C.Fmap hij m) := by
  subst hX; subst hY; rfl

/-- A transport is heterogeneously equal to the morphism it transports. -/
theorem heq_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜} (hX : X = X') (hY : Y = Y')
    (m : X ⟶ Y) : HEq (castHom hX hY m) m := by
  subst hX; subst hY; exact HEq.rfl

/-- Two transports of heterogeneously-equal morphisms onto the *same* objects are
    equal.  This is the cancellation the hom-colimit's `tr_trans` needs. -/
theorem castHom_heq_congr {𝒜 : Type w} [Cat.{w} 𝒜] {X1 Y1 X2 Y2 X' Y' : 𝒜}
    (h1X : X1 = X') (h1Y : Y1 = Y') (h2X : X2 = X') (h2Y : Y2 = Y')
    {m1 : X1 ⟶ Y1} {m2 : X2 ⟶ Y2} (h : HEq m1 m2) :
    castHom h1X h1Y m1 = castHom h2X h2Y m2 :=
  castHom_of_heq h1X h1Y (h.trans (heq_castHom h2X h2Y m2).symm)

/-! ## Milestone 2b — the hom-colimit for fixed representatives

  For `x : C.A i`, `y : C.A j`, a morphism in the colimit is a class in the
  directed colimit of `Hom_{A k}(F x, F y)` over common upper bounds `k`.  The
  transition `homTr` applies the transition functor and re-types along `F_trans`;
  its colimit laws hold by coherence (`refl_map`/`trans_map`) modulo the casts. -/

/-- Transition of the hom-colimit: push a morphism `F x ⟶ F y` (at upper bound `a`)
    to upper bound `b` by applying `F hab` and re-typing along `F_trans`. -/
def homTr (C : CatSystem ι D) {i j : ι} (x : C.A i) (y : C.A j) (a b : UpperBound D i j)
    (hab : D.le a.1 b.1) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) : C.F b.2.1 x ⟶ C.F b.2.2 y :=
  castHom (C.F_trans a.2.1 hab x).symm (C.F_trans a.2.2 hab y).symm (C.Fmap hab g)

theorem homTr_refl (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a : UpperBound D i j) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homTr C x y a a (D.refl a.1) g = g := by
  unfold homTr
  exact castHom_of_heq _ _ (hC.refl_map g)

theorem homTr_trans (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a b c : UpperBound D i j) (hab : D.le a.1 b.1) (hbc : D.le b.1 c.1)
    (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homTr C x y a c (D.trans hab hbc) g = homTr C x y b c hbc (homTr C x y a b hab g) := by
  unfold homTr
  rw [C.Fmap_castHom hbc, castHom_castHom]
  exact castHom_heq_congr _ _ _ _ (hC.trans_map hab hbc g)

/-- The hom-colimit system for fixed representatives `x : C.A i`, `y : C.A j`. -/
def homSystem (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j) :
    System (UpperBound D i j) (upperDirected D i j) where
  X a := C.F a.2.1 x ⟶ C.F a.2.2 y
  tr {a b} hab g := homTr C x y a b hab g
  tr_refl {a} g := homTr_refl C hC x y a g
  tr_trans {a b c} hab hbc g := homTr_trans C hC x y a b c hab hbc g

/-- Morphisms `[⟨i,x⟩] → [⟨j,y⟩]` in the colimit category (for these
    representatives): the directed colimit of `Hom_{A k}(F x, F y)` over the common
    upper bounds `k`. -/
def HomColim (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j) : Type _ :=
  Colimit (homSystem C hC x y)

/-- Include a stage-`a` morphism into the hom-colimit. -/
def homIncl (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    (a : UpperBound D i j) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) : HomColim C hC x y :=
  incl (homSystem C hC x y) a g

/-- The identity germ at `x : C.A i`: `id` included at the trivial upper bound. -/
def homClassId (C : CatSystem ι D) (hC : C.Coherent) {i : ι} (x : C.A i) : HomColim C hC x x :=
  homIncl C hC x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (C.F (D.refl i) x))

/-- Including a germ pushed to a higher level equals including it at the lower
    level: the hom-colimit absorbs the transition (`incl_compat` for `homSystem`).
    A building block for composition's well-definedness. -/
theorem homIncl_compat (C : CatSystem ι D) (hC : C.Coherent) {i j : ι} (x : C.A i) (y : C.A j)
    {a b : UpperBound D i j} (hab : D.le a.1 b.1) (g : C.F a.2.1 x ⟶ C.F a.2.2 y) :
    homIncl C hC x y b (homTr C x y a b hab g) = homIncl C hC x y a g :=
  incl_compat (homSystem C hC x y) hab g

/-! ## Milestone 2b — the colimit category's Hom (via chosen representatives)

  We pick a representative of each colimit object with `Quotient.out` and define a
  morphism as the hom-colimit between the chosen representatives.  This uses choice
  (acceptable: the §1.543 iteration is transfinite and uses choice anyway; a
  choice-free two-sided-germ construction is possible but far longer). -/

/-- A chosen representative `⟨i, x⟩` of a colimit object (via `Quotient.exists_rep`
    + choice; core Lean has no `Quotient.out`). -/
noncomputable def colimOut (C : CatSystem ι D) (p : C.Obj) : Σ i, C.A i :=
  Classical.choose (Quotient.exists_rep p)

/-- The chosen representative includes back to the object. -/
theorem colimOut_spec (C : CatSystem ι D) (p : C.Obj) :
    C.objIncl (colimOut C p).1 (colimOut C p).2 = p :=
  Classical.choose_spec (Quotient.exists_rep p)

/-- A morphism of the colimit category: the hom-colimit between the chosen
    representatives of the two objects. -/
noncomputable def colimHom (C : CatSystem ι D) (hC : C.Coherent) (p q : C.Obj) : Type _ :=
  HomColim C hC (colimOut C p).2 (colimOut C q).2

/-- The identity morphism of the colimit category. -/
noncomputable def colimId (C : CatSystem ι D) (hC : C.Coherent) (p : C.Obj) : colimHom C hC p p :=
  homClassId C hC (colimOut C p).2

/-- C.F is proof-irrelevant in the ordering proof: two proofs of `D.le i j` give
    the same object (since `D.le` is a `Prop`). -/
theorem CatSystem.F_proof_irrel (C : CatSystem ι D) {i j : ι} (h h' : D.le i j) (a : C.A i) :
    C.F h a = C.F h' a := by congr 1

/-- Raw composition of germs: push representatives `f` (level `a`) and `g` (level
    `b`) to a common level `c`, compose in `A c`, and include.  The middle objects
    match (both `F·xq` over a proof `iq ≤ c`, identified by proof-irrelevance). -/
noncomputable def homCompRaw (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr) : HomColim C hC xp xr :=
  let c := Classical.choose (D.bound a.1 b.1)
  let hac : D.le a.1 c := (Classical.choose_spec (D.bound a.1 b.1)).1
  let hbc : D.le b.1 c := (Classical.choose_spec (D.bound a.1 b.1)).2
  let aC : UpperBound D ip iq := ⟨c, D.trans a.2.1 hac, D.trans a.2.2 hac⟩
  let bC : UpperBound D iq ir := ⟨c, D.trans b.2.1 hbc, D.trans b.2.2 hbc⟩
  let f' : C.F aC.2.1 xp ⟶ C.F aC.2.2 xq := homTr C xp xq a aC hac f
  let g' : C.F bC.2.1 xq ⟶ C.F bC.2.2 xr := homTr C xq xr b bC hbc g
  -- The two homTr results have different intermediate C.F objects (aC.2.2 vs bC.2.1)
  -- even though they are both D.le iq c.  Align via hF_proof_irrel:
  let f'' : C.F aC.2.1 xp ⟶ C.F bC.2.1 xq :=
    castHom rfl (by rw [Subsingleton.elim aC.2.2 bC.2.1]) f'
  homIncl C hC xp xr ⟨c, D.trans a.2.1 hac, D.trans b.2.2 hbc⟩
    (f'' ≫ g')

/-- Pushing a composite to a higher level = composing the pushed pieces.  The
    transition `F hcd` is a functor (`map_comp`), and transport distributes over
    composition (`castHom_comp`). -/
theorem homTr_comp (C : CatSystem ι D) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir) {c d : ι}
    (hpc : D.le ip c) (hqc : D.le iq c) (hrc : D.le ir c) (hcd : D.le c d)
    (f : C.F hpc xp ⟶ C.F hqc xq) (g : C.F hqc xq ⟶ C.F hrc xr) :
    homTr C xp xr ⟨c, hpc, hrc⟩ ⟨d, D.trans hpc hcd, D.trans hrc hcd⟩ hcd (f ≫ g)
      = homTr C xp xq ⟨c, hpc, hqc⟩ ⟨d, D.trans hpc hcd, D.trans hqc hcd⟩ hcd f
        ≫ homTr C xq xr ⟨c, hqc, hrc⟩ ⟨d, D.trans hqc hcd, D.trans hrc hcd⟩ hcd g := by
  unfold homTr
  dsimp only
  rw [castHom_comp, ← C.Fmap_comp hcd]

/-- Pushing an identity germ up gives an identity (the transition is a functor:
    `map_id`, then `castHom_id`). -/
theorem homTr_id (C : CatSystem ι D) {i : ι} (x : C.A i)
    (a b : UpperBound D i i) (hab : D.le a.1 b.1) :
    homTr C x x a b hab (Cat.id (C.F a.2.1 x)) = Cat.id (C.F b.2.1 x) := by
  unfold homTr
  rw [C.Fmap_id hab]
  exact castHom_id _

/-- Compose germs `f` (level `a`) and `g` (level `b`) at an explicit common bound
    `e`: push both to `e` and compose there.  `homCompRaw` is this at the chosen
    bound. -/
noncomputable def compAt (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) : HomColim C hC xp xr :=
  homIncl C hC xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩
    (homTr C xp xq a ⟨e, D.trans a.2.1 hae, D.trans a.2.2 hae⟩ hae f
     ≫ homTr C xq xr b ⟨e, D.trans b.2.1 hbe, D.trans b.2.2 hbe⟩ hbe g)

/-- Composing at level `e` equals composing at any higher level `d`: push the
    whole composite up (`homTr_comp` + `homTr_trans`), then `homIncl_compat`. -/
theorem compAt_mono (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    {e d : ι} (hae : D.le a.1 e) (hbe : D.le b.1 e) (hed : D.le e d) :
    compAt C hC xp xq xr a f b g e hae hbe
      = compAt C hC xp xq xr a f b g d (D.trans hae hed) (D.trans hbe hed) := by
  have hpe : D.le ip e := D.trans a.2.1 hae
  have hqe : D.le iq e := D.trans a.2.2 hae
  have hre : D.le ir e := D.trans b.2.2 hbe
  symm
  unfold compAt
  rw [homTr_trans C hC xp xq a ⟨e, hpe, hqe⟩
        ⟨d, D.trans a.2.1 (D.trans hae hed), D.trans a.2.2 (D.trans hae hed)⟩ hae hed f,
      homTr_trans C hC xq xr b ⟨e, hqe, hre⟩
        ⟨d, D.trans b.2.1 (D.trans hbe hed), D.trans b.2.2 (D.trans hbe hed)⟩ hbe hed g,
      ← homTr_comp C xp xq xr hpe hqe hre hed
        (homTr C xp xq a ⟨e, hpe, hqe⟩ hae f) (homTr C xq xr b ⟨e, hqe, hre⟩ hbe g),
      homIncl_compat]

/-- Composition is independent of the chosen common bound: any two bounds agree
    (route both through a common upper bound via `compAt_mono`). -/
theorem compAt_indep (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    {e₁ e₂ : ι} (hae₁ : D.le a.1 e₁) (hbe₁ : D.le b.1 e₁)
    (hae₂ : D.le a.1 e₂) (hbe₂ : D.le b.1 e₂) :
    compAt C hC xp xq xr a f b g e₁ hae₁ hbe₁ = compAt C hC xp xq xr a f b g e₂ hae₂ hbe₂ := by
  obtain ⟨d, h1d, h2d⟩ := D.bound e₁ e₂
  rw [compAt_mono C hC xp xq xr a f b g hae₁ hbe₁ h1d,
      compAt_mono C hC xp xq xr a f b g hae₂ hbe₂ h2d]

/-- `homCompRaw` is `compAt` at any common bound (it uses the chosen bound; all
    bounds agree by `compAt_indep`). -/
theorem homCompRaw_eq_compAt (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) :
    homCompRaw C hC xp xq xr a f b g = compAt C hC xp xq xr a f b g e hae hbe := by
  have h : homCompRaw C hC xp xq xr a f b g
      = compAt C hC xp xq xr a f b g (Classical.choose (D.bound a.1 b.1))
          (Classical.choose_spec (D.bound a.1 b.1)).1
          (Classical.choose_spec (D.bound a.1 b.1)).2 := rfl
  rw [h]; exact compAt_indep C hC xp xq xr a f b g _ _ hae hbe

/-- **Composition reduces to a stage equation.**  To prove a colimit-level
    composite `homCompRaw (germ f) (germ g)` equals an included germ `homIncl fOrig`,
    it suffices to push all three germs to one common level `M` and check the
    equation there (`hstage`).  This is the workhorse that turns every colimit
    universal-property law (product/pullback factorizations, uniqueness) into a
    single equation inside one stage category `C.A M`, where ordinary functor
    calculus applies.  The `homTr` target bounds in `hstage` are exactly the ones
    `compAt` produces, so the proof is `homCompRaw_eq_compAt` → `hstage` →
    `homIncl_compat`. -/
theorem homCompRaw_eq_of_stage (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (ub_h : UpperBound D ip iq) (rM : C.F ub_h.2.1 xp ⟶ C.F ub_h.2.2 xq)
    (ub_g : UpperBound D iq ir) (gK : C.F ub_g.2.1 xq ⟶ C.F ub_g.2.2 xr)
    (ub_orig : UpperBound D ip ir) (fOrig : C.F ub_orig.2.1 xp ⟶ C.F ub_orig.2.2 xr)
    (M : ι) (hhM : D.le ub_h.1 M) (hgM : D.le ub_g.1 M) (hoM : D.le ub_orig.1 M)
    (hstage :
      homTr C xp xq ub_h ⟨M, D.trans ub_h.2.1 hhM, D.trans ub_h.2.2 hhM⟩ hhM rM
        ≫ homTr C xq xr ub_g ⟨M, D.trans ub_g.2.1 hgM, D.trans ub_g.2.2 hgM⟩ hgM gK
      = homTr C xp xr ub_orig ⟨M, D.trans ub_h.2.1 hhM, D.trans ub_g.2.2 hgM⟩ hoM fOrig) :
    homCompRaw C hC xp xq xr ub_h rM ub_g gK = homIncl C hC xp xr ub_orig fOrig := by
  rw [homCompRaw_eq_compAt C hC xp xq xr ub_h rM ub_g gK M hhM hgM]
  unfold compAt
  rw [hstage]
  exact homIncl_compat C hC xp xr hoM fOrig

/-- Pushing the left germ's representative up doesn't change the composite. -/
theorem homCompRaw_push_left (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a a₂ : UpperBound D ip iq) (h : D.le a.1 a₂.1) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr) :
    homCompRaw C hC xp xq xr a₂ (homTr C xp xq a a₂ h f) b g
      = homCompRaw C hC xp xq xr a f b g := by
  obtain ⟨M, ha₂M, hbM⟩ := D.bound a₂.1 b.1
  rw [homCompRaw_eq_compAt C hC xp xq xr a₂ (homTr C xp xq a a₂ h f) b g M ha₂M hbM,
      homCompRaw_eq_compAt C hC xp xq xr a f b g M (D.trans h ha₂M) hbM]
  unfold compAt
  rw [homTr_trans C hC xp xq a a₂
        ⟨M, D.trans a.2.1 (D.trans h ha₂M), D.trans a.2.2 (D.trans h ha₂M)⟩ h ha₂M f]

/-- Pushing the right germ's representative up doesn't change the composite. -/
theorem homCompRaw_push_right (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (b b₂ : UpperBound D iq ir) (h : D.le b.1 b₂.1) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr) :
    homCompRaw C hC xp xq xr a f b₂ (homTr C xq xr b b₂ h g)
      = homCompRaw C hC xp xq xr a f b g := by
  obtain ⟨M, haM, hb₂M⟩ := D.bound a.1 b₂.1
  rw [homCompRaw_eq_compAt C hC xp xq xr a f b₂ (homTr C xq xr b b₂ h g) M haM hb₂M,
      homCompRaw_eq_compAt C hC xp xq xr a f b g M haM (D.trans h hb₂M)]
  unfold compAt
  rw [homTr_trans C hC xq xr b b₂
        ⟨M, D.trans b.2.1 (D.trans h hb₂M), D.trans b.2.2 (D.trans h hb₂M)⟩ h hb₂M g]

/-- Raw composition respects the germ equivalence on both arguments: push each
    representative up to its germ-witness level (`push_left`/`push_right`), where
    the representatives agree. -/
theorem homCompRaw_wd (C : CatSystem ι D) (hC : C.Coherent) {ip iq ir : ι}
    (xp : C.A ip) (xq : C.A iq) (xr : C.A ir)
    (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq)
    (a' : UpperBound D ip iq) (f' : C.F a'.2.1 xp ⟶ C.F a'.2.2 xq)
    (hP : Rel (homSystem C hC xp xq) ⟨a, f⟩ ⟨a', f'⟩)
    (b : UpperBound D iq ir) (g : C.F b.2.1 xq ⟶ C.F b.2.2 xr)
    (b' : UpperBound D iq ir) (g' : C.F b'.2.1 xq ⟶ C.F b'.2.2 xr)
    (hQ : Rel (homSystem C hC xq xr) ⟨b, g⟩ ⟨b', g'⟩) :
    homCompRaw C hC xp xq xr a f b g = homCompRaw C hC xp xq xr a' f' b' g' := by
  obtain ⟨k, hak, ha'k, hf⟩ := hP
  obtain ⟨l, hbl, hb'l, hg⟩ := hQ
  have hf' : homTr C xp xq a k hak f = homTr C xp xq a' k ha'k f' := hf
  have hg' : homTr C xq xr b l hbl g = homTr C xq xr b' l hb'l g' := hg
  rw [← homCompRaw_push_left C hC xp xq xr a k hak f b g, hf',
      homCompRaw_push_left C hC xp xq xr a' k ha'k f' b g,
      ← homCompRaw_push_right C hC xp xq xr a' f' b l hbl g, hg',
      homCompRaw_push_right C hC xp xq xr a' f' b' l hb'l g']

/-- Composition in the colimit category: lift `homCompRaw` over the two
    hom-colimit quotients (well-defined by `homCompRaw_wd`). -/
noncomputable def colimComp (C : CatSystem ι D) (hC : C.Coherent) {p q r : C.Obj}
    (m : colimHom C hC p q) (n : colimHom C hC q r) : colimHom C hC p r :=
  Quotient.lift₂
    (fun rm rn => homCompRaw C hC (colimOut C p).2 (colimOut C q).2 (colimOut C r).2
      rm.1 rm.2 rn.1 rn.2)
    (fun _ _ _ _ hP hQ =>
      homCompRaw_wd C hC (colimOut C p).2 (colimOut C q).2 (colimOut C r).2
        _ _ _ _ hP _ _ _ _ hQ)
    m n

/-! ## Milestone 2b — identity laws for composition -/

theorem homCompRaw_id_left (C : CatSystem ι D) (hC : C.Coherent) {ip iq : ι}
    (xp : C.A ip) (xq : C.A iq) (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq) :
    homCompRaw C hC xp xp xq ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (C.F (D.refl ip) xp)) a f
      = homIncl C hC xp xq a f := by
  rw [homCompRaw_eq_compAt C hC xp xp xq ⟨ip, D.refl ip, D.refl ip⟩
        (Cat.id (C.F (D.refl ip) xp)) a f a.1 a.2.1 (D.refl a.1)]
  unfold compAt
  have hid : homTr C xp xp ⟨ip, D.refl ip, D.refl ip⟩
      ⟨a.1, D.trans (D.refl ip) a.2.1, D.trans (D.refl ip) a.2.1⟩ a.2.1
      (Cat.id (C.F (D.refl ip) xp))
    = Cat.id (C.F (D.trans (D.refl ip) a.2.1) xp) :=
    homTr_id C xp ⟨ip, D.refl ip, D.refl ip⟩
      ⟨a.1, D.trans (D.refl ip) a.2.1, D.trans (D.refl ip) a.2.1⟩ a.2.1
  have hf : homTr C xp xq a ⟨a.1, D.trans a.2.1 (D.refl a.1), D.trans a.2.2 (D.refl a.1)⟩ (D.refl a.1) f = f := by
    simpa using homTr_refl C hC xp xq ⟨a.1, D.trans a.2.1 (D.refl a.1), D.trans a.2.2 (D.refl a.1)⟩ f
  rw [hid, hf, Cat.id_comp]
  unfold homIncl
  apply Quotient.sound
  refine ⟨a, D.refl a.1, D.refl a.1, ?_⟩
  dsimp [homSystem]
  rw [homTr_refl C hC xp xq a f]
  unfold homTr
  exact castHom_of_heq _ _ (hC.refl_map f)

theorem homCompRaw_id_right (C : CatSystem ι D) (hC : C.Coherent) {ip iq : ι}
    (xp : C.A ip) (xq : C.A iq) (a : UpperBound D ip iq) (f : C.F a.2.1 xp ⟶ C.F a.2.2 xq) :
    homCompRaw C hC xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩ (Cat.id (C.F (D.refl iq) xq))
      = homIncl C hC xp xq a f := by
  rw [homCompRaw_eq_compAt C hC xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩
        (Cat.id (C.F (D.refl iq) xq)) a.1 (D.refl a.1) a.2.2]
  unfold compAt
  have hf : homTr C xp xq a ⟨a.1, D.trans a.2.1 (D.refl a.1), D.trans a.2.2 (D.refl a.1)⟩ (D.refl a.1) f = f := by
    simpa using homTr_refl C hC xp xq ⟨a.1, D.trans a.2.1 (D.refl a.1), D.trans a.2.2 (D.refl a.1)⟩ f
  have hid : homTr C xq xq ⟨iq, D.refl iq, D.refl iq⟩
      ⟨a.1, D.trans (D.refl iq) a.2.2, D.trans (D.refl iq) a.2.2⟩ a.2.2
      (Cat.id (C.F (D.refl iq) xq))
    = Cat.id (C.F (D.trans (D.refl iq) a.2.2) xq) :=
    homTr_id C xq ⟨iq, D.refl iq, D.refl iq⟩
      ⟨a.1, D.trans (D.refl iq) a.2.2, D.trans (D.refl iq) a.2.2⟩ a.2.2
  rw [hf, hid, Cat.comp_id]
  unfold homIncl
  apply Quotient.sound
  refine ⟨a, D.refl a.1, D.refl a.1, ?_⟩
  dsimp [homSystem]
  rw [homTr_refl C hC xp xq a f]
  unfold homTr
  exact castHom_of_heq _ _ (hC.refl_map f)

theorem colimComp_id_left (C : CatSystem ι D) (hC : C.Coherent) {p q : C.Obj}
    (m : colimHom C hC p q) : colimComp C hC (colimId C hC p) m = m := by
  induction m using Quotient.ind with
  | _ rm =>
    obtain ⟨a, f⟩ := rm
    exact homCompRaw_id_left C hC (colimOut C p).2 (colimOut C q).2 a f

theorem colimComp_id_right (C : CatSystem ι D) (hC : C.Coherent) {p q : C.Obj}
    (m : colimHom C hC p q) : colimComp C hC m (colimId C hC q) = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm
            exact homCompRaw_id_right C hC (colimOut C p).2 (colimOut C q).2 a f

/-! ## Milestone 2b — associativity of composition in the colimit category -/

theorem colimComp_assoc (C : CatSystem ι D) (hC : C.Coherent) {p q r s : C.Obj}
    (m : colimHom C hC p q) (n : colimHom C hC q r) (k : colimHom C hC r s) :
    colimComp C hC (colimComp C hC m n) k = colimComp C hC m (colimComp C hC n k) := by
  refine Quotient.inductionOn m (fun rm => ?_)
  refine Quotient.inductionOn n (fun rn => ?_)
  refine Quotient.inductionOn k (fun rk => ?_)
  obtain ⟨a, f⟩ := rm; obtain ⟨b, g⟩ := rn; obtain ⟨c, h⟩ := rk
  let xp := (colimOut C p).2; let xq := (colimOut C q).2
  let xr := (colimOut C r).2; let xs := (colimOut C s).2
  -- Pick a common bound M of a.1, b.1, c.1
  let ⟨e₁, hae₁, hbe₁⟩ := D.bound a.1 b.1
  let ⟨M, he₁M, hcM⟩ := D.bound e₁ c.1
  have haM : D.le a.1 M := D.trans hae₁ he₁M
  have hbM : D.le b.1 M := D.trans hbe₁ he₁M
  -- Morphisms transported to level M
  let aMpq : UpperBound D (colimOut C p).1 (colimOut C q).1 :=
    ⟨M, D.trans a.2.1 haM, D.trans a.2.2 haM⟩
  let bMqr : UpperBound D (colimOut C q).1 (colimOut C r).1 :=
    ⟨M, D.trans b.2.1 hbM, D.trans b.2.2 hbM⟩
  let cMrs : UpperBound D (colimOut C r).1 (colimOut C s).1 :=
    ⟨M, D.trans c.2.1 hcM, D.trans c.2.2 hcM⟩
  let F_M : C.F aMpq.2.1 xp ⟶ C.F aMpq.2.2 xq := homTr C xp xq a aMpq haM f
  let G_M : C.F bMqr.2.1 xq ⟶ C.F bMqr.2.2 xr := homTr C xq xr b bMqr hbM g
  let H_M : C.F cMrs.2.1 xr ⟶ C.F cMrs.2.2 xs := homTr C xr xs c cMrs hcM h
  -- Upper bounds for homCompRaw
  let ub_pr_M : UpperBound D (colimOut C p).1 (colimOut C r).1 :=
    ⟨M, D.trans a.2.1 haM, D.trans b.2.2 hbM⟩
  let ub_ps_M : UpperBound D (colimOut C p).1 (colimOut C s).1 :=
    ⟨M, D.trans a.2.1 haM, D.trans c.2.2 hcM⟩
  let ub_qs_M : UpperBound D (colimOut C q).1 (colimOut C s).1 :=
    ⟨M, D.trans b.2.1 hbM, D.trans c.2.2 hcM⟩
  -- colimComp on mk terms reduces definitionally to homCompRaw
  have h_innerLR : colimComp C hC (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩) =
      homCompRaw C hC xp xq xr a f b g := rfl
  have h_innerRR : colimComp C hC (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩) =
      homCompRaw C hC xq xr xs b g c h := rfl
  -- Push inner compositions to compAt at M
  have h_innerL : colimComp C hC (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩) =
      compAt C hC xp xq xr a f b g M haM hbM := by
    rw [h_innerLR, homCompRaw_eq_compAt C hC xp xq xr a f b g M haM hbM]
  have h_innerR : colimComp C hC (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩) =
      compAt C hC xq xr xs b g c h M hbM hcM := by
    rw [h_innerRR, homCompRaw_eq_compAt C hC xq xr xs b g c h M hbM hcM]
  -- The compAt yields a homIncl (= Quotient.mk), so the outer colimComp reduces
  have h_outerL : colimComp C hC (compAt C hC xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩) =
      homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h := rfl
  have h_outerR : colimComp C hC (Quotient.mk _ ⟨a, f⟩) (compAt C hC xq xr xs b g c h M hbM hcM) =
      homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) := rfl
  -- Push outer homCompRaw to compAt at M
  have h_compAtL : homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h =
      compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM :=
    homCompRaw_eq_compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM
  have h_compAtR : homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) =
      compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) :=
    homCompRaw_eq_compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M)
  -- Simplify compAt: homTr at D.refl M is identity by homTr_refl (proof irrelevance makes bounds defeq)
  have h_simpL : compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM =
      homIncl C hC xp xs ub_ps_M ((F_M ≫ G_M) ≫ H_M) := by
    unfold compAt
    rw [homTr_refl C hC xp xr ub_pr_M (F_M ≫ G_M)]
  have h_simpR : compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) =
      homIncl C hC xp xs ub_ps_M (F_M ≫ (G_M ≫ H_M)) := by
    unfold compAt
    rw [homTr_refl C hC xq xs ub_qs_M (G_M ≫ H_M)]
  calc
    colimComp C hC (colimComp C hC (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩)) (Quotient.mk _ ⟨c, h⟩)
        = colimComp C hC (compAt C hC xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩) := by rw [h_innerL]
    _ = homCompRaw C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h := h_outerL
    _ = compAt C hC xp xr xs ub_pr_M (F_M ≫ G_M) c h M (D.refl M) hcM := h_compAtL
    _ = homIncl C hC xp xs ub_ps_M ((F_M ≫ G_M) ≫ H_M) := h_simpL
    _ = homIncl C hC xp xs ub_ps_M (F_M ≫ (G_M ≫ H_M)) := by rw [Cat.assoc F_M G_M H_M]
    _ = compAt C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) M haM (D.refl M) := by rw [h_simpR]
    _ = homCompRaw C hC xp xq xs a f ub_qs_M (G_M ≫ H_M) := by rw [h_compAtR]
    _ = colimComp C hC (Quotient.mk _ ⟨a, f⟩) (compAt C hC xq xr xs b g c h M hbM hcM) := by rw [h_outerR]
    _ = colimComp C hC (Quotient.mk _ ⟨a, f⟩) (colimComp C hC (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩)) := by rw [h_innerR]

noncomputable instance colimitCat (C : CatSystem ι D) (hC : C.Coherent) : Cat (C.Obj) where
  Hom p q := colimHom C hC p q
  id p := colimId C hC p
  comp m n := colimComp C hC m n
  id_comp m := colimComp_id_left C hC m
  comp_id m := colimComp_id_right C hC m
  assoc m n k := colimComp_assoc C hC m n k

end Freyd.Colim
