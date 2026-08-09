/-
  §1.63 union condition for the directed colimit of POSITIVE pre-logoi.

  The last `PreLogos` field for `colimitPreLogos` (`Freyd/ColimitPreLogos.lean`): the inverse image of
  a union is covered by the union of the inverse images,

      `f#(S ∪ T) ≤ f#S ∪ f#T`     (`colimit_invImage_union_le`).

  PROOF (germ-transport).  Every finite construction — `f`, `S`, `T` — lives at a finite stage `N`
  (`colimit_subobject_is_germ`).  Three instance-robust transports identify the colimit operations
  with the `objIncl N`-germ of the per-stage operations:

    * inverse image is a pullback, and `objIncl N` preserves pullbacks (`objIncl_preserves_pullbacks`);
    * union is the image of a copairing, and `objIncl N` preserves coproducts
      (`objIncl_preserves_coproducts`) and images (`objIncl_preserves_images`);
    * `objIncl N` (= `stageInclFunctor`) sends a stage `Subobject.le` to a colimit one.

  The diamonds (which `HasPullbacks`/`HasBinaryCoproducts`/`HasSubobjectUnions` instance is in scope)
  are sidestepped by GENERIC uniqueness lemmas: two pullback cones of one cospan give equivalent
  subobjects (`pullback_subobject_le`), and two joins / two images of one datum are equivalent
  (`isImage_equiv`, `union_via_coproduct_image`).  The stage hard direction is the per-stage
  `PreLogos.invImage_preserves_union`.
-/
module

public import Freyd.S1_543_CatColimitRegular
public import Freyd.S1_543_ColimitCoproductGerm
public import Freyd.S1_543_Capitalization
public import Freyd.S1_61
public import Freyd.S1_62
public import Freyd.S1_543_UnionFromCoproduct

open Freyd

namespace Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## Generic subobject lemmas (instance-robust)

  These are pure §1.5 facts; none mentions the colimit.  They let the germ-transport reason about
  `Subobject.le` up to equivalence (mutual `≤`) without pinning a particular limit/colimit choice. -/

theorem Subobject.Equiv.refl {B : 𝒞} (S : Subobject 𝒞 B) : S.Equiv S := ⟨S.le_refl, S.le_refl⟩

public theorem Subobject.Equiv.symm {B : 𝒞} {S T : Subobject 𝒞 B} (h : S.Equiv T) : T.Equiv S := ⟨h.2, h.1⟩

public theorem Subobject.Equiv.trans {B : 𝒞} {S T U : Subobject 𝒞 B}
    (h₁ : S.Equiv T) (h₂ : T.Equiv U) : S.Equiv U :=
  ⟨Subobject.le_trans h₁.1 h₂.1, Subobject.le_trans h₂.2 h₁.2⟩

/-- A mono-preserving functor is monotone on subobjects: `S ≤ T ⟹ T_*S ≤ T_*T`. -/
theorem Subobject.map_le {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (T : Functor 𝒜 ℬ)
    (hpm : PreservesMono T) {B : 𝒜} {S S' : Subobject 𝒜 B} (h : S.le S') :
    (Subobject.map T hpm S).le (Subobject.map T hpm S') := by
  obtain ⟨k, hk⟩ := h
  exact ⟨T.map k, by
    show T.map k ≫ T.map S'.arr = T.map S.arr
    rw [← T.map_comp, hk]⟩

/-- The chosen image of `f` is equivalent to any image of `f`. -/
public theorem image_equiv_isImage [HasImages 𝒞] {A B : 𝒞} {f : A ⟶ B} {I : Subobject 𝒞 B}
    (hI : IsImage f I) : (image f).Equiv I :=
  ⟨(HasImages.isImage f).2 I hI.1, hI.2 (image f) (HasImages.isImage f).1⟩

/-- The image of a monic is equivalent to the monic-as-subobject. -/
theorem image_monic_equiv [HasImages 𝒞] {M B : 𝒞} (m : M ⟶ B) (hm : Monic m) :
    (image m).Equiv (Subobject.mk M m hm) :=
  image_equiv_isImage (monic_isImage m hm)

/-- Precomposing a morphism with an isomorphism does not change its image. -/
public theorem isImage_precomp_iso {X A B : 𝒞} {i : X ⟶ A} {g : A ⟶ B} (hi : IsIso i)
    {I : Subobject 𝒞 B} (hg : IsImage g I) : IsImage (i ≫ g) I := by
  obtain ⟨inv, hinv1, hinv2⟩ := hi
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := hg.1
    exact ⟨i ≫ k, by rw [Cat.assoc, hk]⟩
  · intro S hS
    obtain ⟨p, hp⟩ := hS
    refine hg.2 S ⟨inv ≫ p, ?_⟩
    rw [Cat.assoc, hp, ← Cat.assoc, hinv2, Cat.id_comp]

/-- **Two pullback cones over one cospan give equivalent π₁-subobjects.**  The pullback UMP of `c'`
    on the cone `c` yields a mediator commuting with `π₁`, i.e. the `Subobject.le` factorization. -/
public theorem pullback_subobject_le {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} {c c' : Cone f g}
    (hc' : c'.IsPullback) (h1 : Monic c.π₁) (h1' : Monic c'.π₁) :
    (Subobject.mk c.pt c.π₁ h1).le (Subobject.mk c'.pt c'.π₁ h1') := by
  obtain ⟨u, ⟨hu1, _⟩, _⟩ := hc' c
  exact ⟨u, hu1⟩

/-- Two pullback cones over one cospan give EQUIVALENT π₁-subobjects.  Kept (not inlined): the two
    `IsPullback` arguments pin BOTH cones `{c c'}`, which the two-sided `⟨le, le⟩` needs — inlining
    forces `mk c.pt c.π₁`-inversion that Lean can't solve for an un-pinned source cone. -/
public theorem pullback_subobject_equiv {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} {c c' : Cone f g}
    (hc : c.IsPullback) (hc' : c'.IsPullback) (h1 : Monic c.π₁) (h1' : Monic c'.π₁) :
    (Subobject.mk c.pt c.π₁ h1).Equiv (Subobject.mk c'.pt c'.π₁ h1') :=
  ⟨pullback_subobject_le hc' h1 h1', pullback_subobject_le hc h1' h1⟩

/-- The first projection of a pullback of `(f, g)` is monic when `g` is.  (The InverseImage-monic
    argument, stated for an abstract pullback cone via its UMP.) -/
public theorem Cone.IsPullback.pi1_monic {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} {c : Cone f g}
    (hc : c.IsPullback) (hg : Monic g) : Monic c.π₁ := by
  intro W u v huv
  have hπ₂ : u ≫ c.π₂ = v ≫ c.π₂ := by
    apply hg
    rw [Cat.assoc, ← c.w, ← Cat.assoc, huv, Cat.assoc, c.w, ← Cat.assoc]
  -- both `u` and `v` are the unique mediator of the cone `⟨W, u≫π₁, u≫π₂⟩`.
  obtain ⟨_, _, huniq⟩ := hc ⟨W, u ≫ c.π₁, u ≫ c.π₂, by rw [Cat.assoc, c.w, ← Cat.assoc]⟩
  rw [huniq u rfl rfl, huniq v huv.symm hπ₂.symm]

/-- Two subobjects with equal domains and `HEq` arrows are mutually `≤`.  Domains are passed as
    free variables so the equality can be `subst`-ed (subobject projections cannot). -/
public theorem subobject_le_of_heq_arr {B Sd Gd : 𝒞} (sa : Sd ⟶ B) (ga : Gd ⟶ B)
    (hsm : Monic sa) (hgm : Monic ga) (edom : Gd = Sd) (harr : HEq ga sa) :
    (Subobject.mk Sd sa hsm).le (Subobject.mk Gd ga hgm) := by
  subst edom
  have : ga = sa := eq_of_heq harr
  subst this
  exact ⟨Cat.id _, Cat.id_comp _⟩

/-! ### The image of a copairing is the join (instance-free)

  `image (case S.arr T.arr)` satisfies the join universal property for `(S, T)` directly — no
  `HasSubobjectUnions` needed.  Hence ANY chosen union is equivalent to it (`union_equiv_image_case`),
  which is how the colimit and the per-stage unions are matched without an instance diamond. -/

public theorem image_case_le_left [HasImages 𝒞] [HasBinaryCoproducts 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    S.le (image (HasBinaryCoproducts.case S.arr T.arr)) := by
  refine ⟨HasBinaryCoproducts.inl ≫ image.lift (HasBinaryCoproducts.case S.arr T.arr), ?_⟩
  rw [Cat.assoc, image.lift_fac]
  exact HasBinaryCoproducts.case_inl S.arr T.arr

public theorem image_case_le_right [HasImages 𝒞] [HasBinaryCoproducts 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    T.le (image (HasBinaryCoproducts.case S.arr T.arr)) := by
  refine ⟨HasBinaryCoproducts.inr ≫ image.lift (HasBinaryCoproducts.case S.arr T.arr), ?_⟩
  rw [Cat.assoc, image.lift_fac]
  exact HasBinaryCoproducts.case_inr S.arr T.arr

public theorem image_case_min [HasImages 𝒞] [HasBinaryCoproducts 𝒞] {B : 𝒞} (S T U : Subobject 𝒞 B)
    (hSU : S.le U) (hTU : T.le U) : (image (HasBinaryCoproducts.case S.arr T.arr)).le U := by
  obtain ⟨s, hs⟩ := hSU
  obtain ⟨t, ht⟩ := hTU
  refine image_min (HasBinaryCoproducts.case S.arr T.arr) U ⟨HasBinaryCoproducts.case s t, ?_⟩
  refine HasBinaryCoproducts.case_uniq S.arr T.arr (HasBinaryCoproducts.case s t ≫ U.arr) ?_ ?_
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inl]; exact hs
  · rw [← Cat.assoc, HasBinaryCoproducts.case_inr]; exact ht

/-- Any chosen union equals the image of the copairing (both are the join of `(S, T)`). -/
public theorem union_equiv_image_case [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasBinaryCoproducts 𝒞]
    {B : 𝒞} (S T : Subobject 𝒞 B) :
    (HasSubobjectUnions.union S T).Equiv (image (HasBinaryCoproducts.case S.arr T.arr)) :=
  ⟨HasSubobjectUnions.union_min S T _ (image_case_le_left S T) (image_case_le_right S T),
   image_case_min S T _ (HasSubobjectUnions.union_left S T) (HasSubobjectUnions.union_right S T)⟩

/-- The §1.432 stage pullback subobject of `(f, X.arr)` (inverse image via products+equalizers).
    Instances passed explicitly so callers can pin exactly the §1.432 choice. -/
@[expose] public noncomputable def pbSub (ht : HasTerminal 𝒞) (hp : HasBinaryProducts 𝒞) (he : HasEqualizers 𝒞)
    {A B : 𝒞} (f : A ⟶ B) (X : Subobject 𝒞 B) : Subobject 𝒞 A :=
  letI := ht; letI := hp; letI := he
  Subobject.mk (products_equalizers_implies_pullbacks f X.arr).cone.pt
    (products_equalizers_implies_pullbacks f X.arr).cone.π₁
    ((HasPullback.cone_isPullback (products_equalizers_implies_pullbacks f X.arr)).pi1_monic X.monic)

/-- The image-of-copairing union subobject. -/
@[expose] public noncomputable def unionImg (hi : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    {B : 𝒞} (S T : Subobject 𝒞 B) : Subobject 𝒞 B :=
  letI := hi; letI := hcop
  image (HasBinaryCoproducts.case S.arr T.arr)

public theorem unionImg_le_left (hi : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    {B : 𝒞} (S T : Subobject 𝒞 B) : S.le (unionImg hi hcop S T) := by
  letI := hi; letI := hcop; exact image_case_le_left S T

public theorem unionImg_le_right (hi : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    {B : 𝒞} (S T : Subobject 𝒞 B) : T.le (unionImg hi hcop S T) := by
  letI := hi; letI := hcop; exact image_case_le_right S T

public theorem unionImg_min (hi : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    {B : 𝒞} (S T U : Subobject 𝒞 B) (hSU : S.le U) (hTU : T.le U) :
    (unionImg hi hcop S T).le U := by
  letI := hi; letI := hcop; exact image_case_min S T U hSU hTU

/-- `unionImg` (any `HasImages`) equals the chosen `HasSubobjectUnions.union` (any instance): both are
    the join.  This is the bridge that dissolves the `HasImages` diamond between the colimit image
    bundle and the per-stage `PreLogos` images. -/
public theorem unionImg_equiv_union (hi : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    [HasImages 𝒞] [HasSubobjectUnions 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B) :
    (unionImg hi hcop S T).Equiv (HasSubobjectUnions.union S T) :=
  ⟨unionImg_min hi hcop S T _ (HasSubobjectUnions.union_left S T) (HasSubobjectUnions.union_right S T),
   HasSubobjectUnions.union_min S T _ (unionImg_le_left hi hcop S T) (unionImg_le_right hi hcop S T)⟩

/-- Transfer `Monic` across a heterogeneous equality of morphisms with equal (object) domains and
    codomains. -/
public theorem monic_of_heq {P Q X Y : 𝒞} {m : P ⟶ Q} {g : X ⟶ Y}
    (hP : P = X) (hQ : Q = Y) (h : HEq m g) (hm : Monic m) : Monic g := by
  subst hP; subst hQ; rw [eq_of_heq h] at hm; exact hm

/-- **The stage union condition for `pbSub`/`unionImg`.**  The per-stage `PreLogos` hard direction
    `f#(S∪T) ≤ f#S ∪ f#T`, re-expressed for the §1.432 pullback (`pbSub`) and the copairing-image
    union (`unionImg`).  The bridge to the `PreLogos`'s own pullback/union is by `≈`-uniqueness, so
    the §1.432/`PreLogos` instance diamond never has to be resolved. -/
public theorem stage_invImage_union_le [hPL : PreLogos 𝒞]
    (ht : HasTerminal 𝒞) (hp : HasBinaryProducts 𝒞) (he : HasEqualizers 𝒞)
    (hii : HasImages 𝒞) (hcop : HasBinaryCoproducts 𝒞)
    {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B) :
    (pbSub ht hp he f (unionImg hii hcop S T)).le
      (unionImg hii hcop (pbSub ht hp he f S) (pbSub ht hp he f T)) := by
  -- PIN the `PreLogos` instances, so `InverseImage`/inverse-image-monotonicity/`union` and the hard
  -- direction all use ONE instance (else the global `exactPullbacks` / image diamonds appear).
  letI : HasPullbacks 𝒞 := hPL.toRegularCategory.toHasPullbacks
  letI : HasImages 𝒞 := hPL.toRegularCategory.toHasImages
  letI : HasSubobjectUnions 𝒞 := hPL.toHasSubobjectUnions
  -- `pbSub f X ≈ InverseImage f X` (two pullback cones of `(f, X.arr)`, possibly different instances)
  have hpb : ∀ (X : Subobject 𝒞 B), (pbSub ht hp he f X).Equiv (InverseImage f X) := fun X =>
    have hcX := HasPullback.cone_isPullback (@products_equalizers_implies_pullbacks 𝒞 _ hp he _ _ _ f X.arr)
    have hc'X := HasPullback.cone_isPullback (HasPullbacks.has f X.arr)
    ⟨pullback_subobject_le hc'X (hcX.pi1_monic X.monic) (InverseImage f X).monic,
     pullback_subobject_le hcX (InverseImage f X).monic (hcX.pi1_monic X.monic)⟩
  -- `unionImg P Q ≈ union P Q` (any object, any `HasImages` — join-uniqueness bridge)
  have hun : ∀ {Y : 𝒞} (P Q : Subobject 𝒞 Y),
      (unionImg hii hcop P Q).Equiv (HasSubobjectUnions.union P Q) :=
    fun P Q => unionImg_equiv_union hii hcop P Q
  refine Subobject.le_trans
    ((hpb (unionImg hii hcop S T)).trans
      ⟨inverseImage_mono f (hun S T).1, inverseImage_mono f (hun S T).2⟩).1 ?_
  refine Subobject.le_trans (PreLogos.invImage_preserves_union f S T).1 ?_
  exact (Subobject.Equiv.trans ⟨union_mono (hpb S).symm.1 (hpb T).symm.1,
      union_mono (hpb S).symm.2 (hpb T).symm.2⟩
    (hun (pbSub ht hp he f S) (pbSub ht hp he f T)).symm).1

end Freyd

namespace Freyd.Colim

universe w

variable {ι : Type u} {D : Directed ι}

/-- The transition-mono-preservation bundle (the `objIncl_preserves_images` shape), abbreviated for
    the many hypotheses below. -/
@[expose] public abbrev TransMono (C : CatSystem ι D) : Prop :=
  ∀ {i j : ι} (hij : D.le i j), @PreservesMono _ (C.catA i) _ (C.catA j) (C.functF hij)

/-- The colimit subobject GERM of a stage subobject `X ⊆ y`: `objIncl N X.dom ↣ objIncl N y` via
    `homInclObj X.arr`, monic since transitions preserve `X.arr`'s mono (`hmono`).  This is exactly
    the form produced by `objIncl_preserves_images`. -/
@[expose] public noncomputable def germSub (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    {N : ι} {y : C.A N} (X : Subobject (C.A N) y) :
    letI : Cat C.Obj := colimitCat C hC
    Subobject C.Obj (C.objIncl N y) :=
  letI : Cat C.Obj := colimitCat C hC
  Subobject.mk (C.objIncl N X.dom) (homInclObj C hC X.arr)
    (homInclObj_mono_of_stage C hC X.arr (fun {_j} hij _z u v huv => hmono hij X.monic u v huv))

theorem germSub_dom (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    {N : ι} {y : C.A N} (X : Subobject (C.A N) y) :
    letI : Cat C.Obj := colimitCat C hC
    (germSub C hC hmono X).dom = C.objIncl N X.dom := rfl

theorem germSub_arr (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    {N : ι} {y : C.A N} (X : Subobject (C.A N) y) :
    letI : Cat C.Obj := colimitCat C hC
    (germSub C hC hmono X).arr = homInclObj C hC X.arr := rfl

/-- The germ functor is monotone: a stage `X ≤ Y` gives a colimit `germ X ≤ germ Y`. -/
public theorem germSub_le (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    {N : ι} {y : C.A N} {X Y : Subobject (C.A N) y} (h : X.le Y) :
    letI : Cat C.Obj := colimitCat C hC
    (germSub C hC hmono X).le (germSub C hC hmono Y) := by
  letI : Cat C.Obj := colimitCat C hC
  obtain ⟨k, hk⟩ := h
  refine ⟨homInclObj C hC k, ?_⟩
  show colimComp C hC (homInclObj C hC k) (homInclObj C hC Y.arr) = homInclObj C hC X.arr
  rw [← homInclObj_comp C hC k Y.arr, hk]

theorem germSub_equiv (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    {N : ι} {y : C.A N} {X Y : Subobject (C.A N) y} (h : X.le Y ∧ Y.le X) :
    letI : Cat C.Obj := colimitCat C hC
    (germSub C hC hmono X).Equiv (germSub C hC hmono Y) :=
  ⟨germSub_le C hC hmono h.1, germSub_le C hC hmono h.2⟩

/-- **Monic reflection for `homInclObj`** (faithful functor reflects monos).  If `homInclObj g` is
    monic in the colimit and transitions are faithful, the stage germ `g` is monic. -/
public theorem homInclObj_mono_reflects (C : CatSystem ι D) (hC : C.Coherent)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    {i : ι} {x y : C.A i} (g : x ⟶ y)
    (hmonic : letI : Cat C.Obj := colimitCat C hC
      @Monic C.Obj (colimitCat C hC) (C.objIncl i x) (C.objIncl i y) (homInclObj C hC g)) :
    Monic g := by
  intro W u v huv
  refine homInclObj_injective C hC hfaith u v ?_
  refine hmonic (homInclObj C hC u) (homInclObj C hC v) ?_
  have e : homInclObj C hC (u ≫ g) = homInclObj C hC (v ≫ g) := by rw [huv]
  rw [homInclObj_comp C hC u g, homInclObj_comp C hC v g] at e
  exact e

/-! ### Transport E — inverse image is a germ

  The colimit inverse image of a germ is the germ of the stage inverse image (a pullback).  Stated
  against the explicit §1.432 stage pullback `products_equalizers_implies_pullbacks`, so it lines up
  with `objIncl_preserves_pullbacks`; the choice of stage pullback is irrelevant up to `≈`
  (two pullback cones of one cospan give equivalent subobjects via `pullback_subobject_le` in both
  directions), so this connects to any per-stage `InverseImage` downstream. -/

set_option maxHeartbeats 1000000 in
public theorem invImage_germ_equiv (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (hmono : TransMono C)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    [hpull : @HasPullbacks C.Obj (colimitCat C hC)]
    (N : ι) {xA xB : C.A N} (f_N : xA ⟶ xB) (X_N : Subobject (C.A N) xB) :
    letI : Cat C.Obj := colimitCat C hC
    (InverseImage (homInclObj C hC f_N) (germSub C hC hmono X_N)).Equiv
      (germSub C hC hmono (pbSub (ht N) (hp N) (he N) f_N X_N)) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasTerminal (C.A N) := ht N
  letI : HasBinaryProducts (C.A N) := hp N
  letI : HasEqualizers (C.A N) := he N
  -- objIncl N-image of the stage pullback cone is a pullback of (homInclObj f_N, homInclObj X_N.arr)
  have himgPB := objIncl_preserves_pullbacks C hC ht htpres hp hpres hpres_pair he hepres hepres_lift
    N f_N X_N.arr
  -- the colimit inverse-image cone is the canonical pullback of the same cospan
  have hcanon : (HasPullbacks.has (homInclObj C hC f_N) (germSub C hC hmono X_N).arr).cone.IsPullback :=
    HasPullback.cone_isPullback _
  exact ⟨pullback_subobject_le himgPB
      ((InverseImage (homInclObj C hC f_N) (germSub C hC hmono X_N)).monic)
      (himgPB.pi1_monic (germSub C hC hmono X_N).monic),
    pullback_subobject_le hcanon
      (himgPB.pi1_monic (germSub C hC hmono X_N).monic)
      ((InverseImage (homInclObj C hC f_N) (germSub C hC hmono X_N)).monic)⟩

/-! ### Transport D — union is a germ

  The colimit union of two germs is the germ of the stage union (image of a copairing).  The
  coproduct keystone (`objIncl_preserves_coproducts`) identifies the colimit copairing with the germ
  of the stage copairing; `objIncl_preserves_images` then carries the image across. -/

set_option maxHeartbeats 1000000 in
public theorem union_germ_equiv (C : CatSystem ι D) (hC : C.Coherent) (hmono : TransMono C)
    (hcop : ∀ i, HasBinaryCoproducts (C.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hcop i).coprod a b) ⟶ z),
        (C.functF hij).map (hcop i).inl ≫ u = (C.functF hij).map (hcop i).inl ≫ v →
        (C.functF hij).map (hcop i).inr ≫ u = (C.functF hij).map (hcop i).inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hcop i).coprod a b) ⟶ z,
          (C.functF hij).map (hcop i).inl ≫ r = p ∧ (C.functF hij).map (hcop i).inr ≫ r = q)
    (hi : ∀ i, HasImages (C.A i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {A B : C.A i} (f : A ⟶ B),
        IsImage (C.Fmap hij f)
          (@Subobject.map _ _ (C.catA i) (C.catA j) (C.functF hij) (hmono hij) _
            (@image _ (C.catA i) (hi i) _ _ f)))
    [hpull : @HasPullbacks C.Obj (colimitCat C hC)]
    [hImg : @HasImages C.Obj (colimitCat C hC)]
    [hUn : @HasSubobjectUnions C.Obj (colimitCat C hC) hImg]
    (N : ι) {xB : C.A N} (S_N T_N : Subobject (C.A N) xB) :
    letI : Cat C.Obj := colimitCat C hC
    letI : HasBinaryCoproducts C.Obj := colimitHasBinaryCoproducts C hC hcop hcoppres hcoppres_case
    (HasSubobjectUnions.union (germSub C hC hmono S_N) (germSub C hC hmono T_N)).Equiv
      (germSub C hC hmono (unionImg (hi N) (hcop N) S_N T_N)) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasImages (C.A N) := hi N
  letI : HasBinaryCoproducts (C.A N) := hcop N
  letI hcopC : HasBinaryCoproducts C.Obj := colimitHasBinaryCoproducts C hC hcop hcoppres hcoppres_case
  -- abbreviations (no Mathlib `set`; use `let` + a defeq `rfl` for the keystone iso)
  let cstage : (hcop N).coprod S_N.dom T_N.dom ⟶ xB := HasBinaryCoproducts.case S_N.arr T_N.arr
  -- the keystone comparison iso κ
  have hκ := objIncl_preserves_coproducts C hC hcop hcoppres hcoppres_case N S_N.dom T_N.dom
  let κ : @HasBinaryCoproducts.coprod C.Obj (colimitCat C hC) hcopC (C.objIncl N S_N.dom)
      (C.objIncl N T_N.dom) ⟶ C.objIncl N ((hcop N).coprod S_N.dom T_N.dom) :=
    @HasBinaryCoproducts.case C.Obj (colimitCat C hC) hcopC
      (C.objIncl N ((hcop N).coprod S_N.dom T_N.dom)) (C.objIncl N S_N.dom) (C.objIncl N T_N.dom)
      (homInclObj C hC ((hcop N).inl (A := S_N.dom) (B := T_N.dom)))
      (homInclObj C hC ((hcop N).inr (A := S_N.dom) (B := T_N.dom)))
  -- D2 key: the colimit copairing of the germ arrows factors through κ and the germ of cstage
  have hD2 : HasBinaryCoproducts.case (germSub C hC hmono S_N).arr (germSub C hC hmono T_N).arr
      = κ ≫ homInclObj C hC cstage := by
    show @HasBinaryCoproducts.case C.Obj (colimitCat C hC) hcopC _ _ _
        (homInclObj C hC S_N.arr) (homInclObj C hC T_N.arr) = κ ≫ homInclObj C hC cstage
    refine Eq.symm (HasBinaryCoproducts.case_uniq (homInclObj C hC S_N.arr) (homInclObj C hC T_N.arr)
      (κ ≫ homInclObj C hC cstage) ?_ ?_)
    · show HasBinaryCoproducts.inl ≫ (κ ≫ homInclObj C hC cstage) = homInclObj C hC S_N.arr
      rw [← Cat.assoc, show (HasBinaryCoproducts.inl ≫ κ)
            = homInclObj C hC ((hcop N).inl (A := S_N.dom) (B := T_N.dom))
            from HasBinaryCoproducts.case_inl _ _]
      show colimComp C hC (homInclObj C hC ((hcop N).inl (A := S_N.dom) (B := T_N.dom)))
          (homInclObj C hC cstage) = homInclObj C hC S_N.arr
      rw [← homInclObj_comp C hC ((hcop N).inl (A := S_N.dom) (B := T_N.dom)) cstage,
          show (hcop N).inl ≫ cstage = S_N.arr from HasBinaryCoproducts.case_inl S_N.arr T_N.arr]
    · show HasBinaryCoproducts.inr ≫ (κ ≫ homInclObj C hC cstage) = homInclObj C hC T_N.arr
      rw [← Cat.assoc, show (HasBinaryCoproducts.inr ≫ κ)
            = homInclObj C hC ((hcop N).inr (A := S_N.dom) (B := T_N.dom))
            from HasBinaryCoproducts.case_inr _ _]
      show colimComp C hC (homInclObj C hC ((hcop N).inr (A := S_N.dom) (B := T_N.dom)))
          (homInclObj C hC cstage) = homInclObj C hC T_N.arr
      rw [← homInclObj_comp C hC ((hcop N).inr (A := S_N.dom) (B := T_N.dom)) cstage,
          show (hcop N).inr ≫ cstage = T_N.arr from HasBinaryCoproducts.case_inr S_N.arr T_N.arr]
  -- chain the equivalences
  refine (union_equiv_image_case (germSub C hC hmono S_N) (germSub C hC hmono T_N)).trans ?_
  rw [hD2]
  refine (image_equiv_isImage
    (isImage_precomp_iso hκ (HasImages.isImage (homInclObj C hC cstage)))).trans ?_
  exact image_equiv_isImage (objIncl_preserves_images C hC hi hfaith hmono himgpres N cstage)

/-! ### Alignment — `f, s, t` into `B` all live at one stage with a shared codomain rep

  The three-legged extension of `colimHom_cospan_as_homInclObj`: a fan `f : A → B`, `s : Sd → B`,
  `t : Td → B` is, up to `HEq`, the stage inclusion of a genuine stage fan into ONE shared `xB`. -/
public theorem colimHom_trifan_as_homInclObj (C : CatSystem ι D) (hC : C.Coherent)
    {A Sd Td B : C.Obj}
    (f : HomColim C hC (colimOut C A).2 (colimOut C B).2)
    (s : HomColim C hC (colimOut C Sd).2 (colimOut C B).2)
    (t : HomColim C hC (colimOut C Td).2 (colimOut C B).2) :
    ∃ (N : ι) (xA xB xSdr xTdr : C.A N) (f_N : xA ⟶ xB) (gS : xSdr ⟶ xB) (gT : xTdr ⟶ xB),
      C.objIncl N xA = A ∧ C.objIncl N xB = B ∧ C.objIncl N xSdr = Sd ∧ C.objIncl N xTdr = Td ∧
      HEq (homInclObj C hC f_N) f ∧ HEq (homInclObj C hC gS) s ∧ HEq (homInclObj C hC gT) t := by
  letI : Cat C.Obj := colimitCat C hC
  obtain ⟨Nf, xAf, xBf, fN, eAf, eBf, hf0⟩ := colimHom_as_homInclObj C hC f
  obtain ⟨Ns, xSf, xBs, sN, eSf, eBs, hs0⟩ := colimHom_as_homInclObj C hC s
  obtain ⟨Nt, xTf, xBt, tN, eTf, eBt, ht0⟩ := colimHom_as_homInclObj C hC t
  obtain ⟨N₁, hNf1, hNs1⟩ := D.bound Nf Ns
  obtain ⟨N₀, h1₀, hNt0⟩ := D.bound N₁ Nt
  let hNf : D.le Nf N₀ := D.trans hNf1 h1₀
  let hNs : D.le Ns N₀ := D.trans hNs1 h1₀
  let hNt : D.le Nt N₀ := hNt0
  let fN0 := (C.functF hNf).map fN
  let sN0 := (C.functF hNs).map sN
  let tN0 := (C.functF hNt).map tN
  -- reconcile the three reps of `B`
  have hBfs0 : C.objIncl N₀ (C.F hNf xBf) = C.objIncl N₀ (C.F hNs xBs) := by
    rw [C.objIncl_compat hNf xBf, C.objIncl_compat hNs xBs, eBf, eBs]
  have hBft0 : C.objIncl N₀ (C.F hNf xBf) = C.objIncl N₀ (C.F hNt xBt) := by
    rw [C.objIncl_compat hNf xBf, C.objIncl_compat hNt xBt, eBf, eBt]
  obtain ⟨Ms, h0Ms, hZs⟩ := objIncl_eq_commonStage C (C.F hNf xBf) (C.F hNs xBs) hBfs0
  obtain ⟨Mt, h0Mt, hZt⟩ := objIncl_eq_commonStage C (C.F hNf xBf) (C.F hNt xBt) hBft0
  obtain ⟨N, hMsN, hMtN⟩ := D.bound Ms Mt
  let hN0N : D.le N₀ N := D.trans h0Ms hMsN
  have hZeq_s : C.F hN0N (C.F hNs xBs) = C.F hN0N (C.F hNf xBf) := by
    rw [C.F_trans h0Ms hMsN (C.F hNf xBf), hZs, ← C.F_trans h0Ms hMsN (C.F hNs xBs)]
  have hZeq_t : C.F hN0N (C.F hNt xBt) = C.F hN0N (C.F hNf xBf) := by
    rw [show hN0N = D.trans h0Mt hMtN from Subsingleton.elim _ _,
        C.F_trans h0Mt hMtN (C.F hNf xBf), hZt, ← C.F_trans h0Mt hMtN (C.F hNt xBt)]
  refine ⟨N, C.F hN0N (C.F hNf xAf), C.F hN0N (C.F hNf xBf),
    C.F hN0N (C.F hNs xSf), C.F hN0N (C.F hNt xTf),
    (C.functF hN0N).map fN0,
    castHom rfl hZeq_s ((C.functF hN0N).map sN0),
    castHom rfl hZeq_t ((C.functF hN0N).map tN0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [C.objIncl_compat hN0N (C.F hNf xAf), C.objIncl_compat hNf xAf, eAf]
  · rw [C.objIncl_compat hN0N (C.F hNf xBf), C.objIncl_compat hNf xBf, eBf]
  · rw [C.objIncl_compat hN0N (C.F hNs xSf), C.objIncl_compat hNs xSf, eSf]
  · rw [C.objIncl_compat hN0N (C.F hNt xTf), C.objIncl_compat hNt xTf, eTf]
  · exact (homInclObj_push_heq C hC hN0N fN0).trans
      ((homInclObj_push_heq C hC hNf fN).trans hf0)
  · refine HEq.trans ?_ ((homInclObj_push_heq C hC hN0N sN0).trans
      ((homInclObj_push_heq C hC hNs sN).trans hs0))
    generalize hY : C.F hN0N (C.F hNf xBf) = Y at hZeq_s ⊢
    cases hZeq_s; rfl
  · refine HEq.trans ?_ ((homInclObj_push_heq C hC hN0N tN0).trans
      ((homInclObj_push_heq C hC hNt tN).trans ht0))
    generalize hY : C.F hN0N (C.F hNf xBf) = Y at hZeq_t ⊢
    cases hZeq_t; rfl

/-! ### The colimit union condition (the hard direction)

  `f#(S ∪ T) ≤ f#S ∪ f#T` in the directed colimit.  Align `f, S, T` to a stage `N` (tri-fan), rewrite
  LHS/RHS as germs of the stage `pbSub`/`unionImg` (transports D, E), apply the per-stage hard
  direction (`stage_invImage_union_le`), and transport the resulting `≤` up by `germSub_le`. -/
set_option maxHeartbeats 1000000 in
public theorem colimit_invImage_union_le (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [hne : Nonempty ι]
    (hmono : TransMono C)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcop : ∀ i, HasBinaryCoproducts (C.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hcop i).coprod a b) ⟶ z),
        (C.functF hij).map (hcop i).inl ≫ u = (C.functF hij).map (hcop i).inl ≫ v →
        (C.functF hij).map (hcop i).inr ≫ u = (C.functF hij).map (hcop i).inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hcop i).coprod a b) ⟶ z,
          (C.functF hij).map (hcop i).inl ≫ r = p ∧ (C.functF hij).map (hcop i).inr ≫ r = q)
    (hi : ∀ i, HasImages (C.A i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {A B : C.A i} (f : A ⟶ B),
        IsImage (C.Fmap hij f)
          (@Subobject.map _ _ (C.catA i) (C.catA j) (C.functF hij) (hmono hij) _
            (@image _ (C.catA i) (hi i) _ _ f)))
    (hbot : ∀ i, PreLogos (C.A i))
    [hReg : @RegularCategory C.Obj (colimitCat C hC)]
    [hUn : @HasSubobjectUnions C.Obj (colimitCat C hC) hReg.toHasImages] :
    letI : Cat C.Obj := colimitCat C hC
    ∀ {A B : C.Obj} (f : A ⟶ B) (S T : Subobject C.Obj B),
      (InverseImage f (HasSubobjectUnions.union S T)).le
        (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)) := by
  letI : Cat C.Obj := colimitCat C hC
  intro A B f S T
  -- align `f, S.arr, T.arr` to a common stage `N` with a shared codomain rep `xB`
  obtain ⟨N, xA, xB, xSdr, xTdr, f_N, gS, gT, eA, eB, eSd, eTd, hf, hgS, hgT⟩ :=
    colimHom_trifan_as_homInclObj C hC f S.arr T.arr
  -- stage monics of the aligned germs (reflect the colimit monos of `S.arr, T.arr`)
  have hgSmono : @Monic C.Obj (colimitCat C hC) _ _ (homInclObj C hC gS) :=
    monic_of_heq eSd.symm eB.symm hgS.symm S.monic
  have hgTmono : @Monic C.Obj (colimitCat C hC) _ _ (homInclObj C hC gT) :=
    monic_of_heq eTd.symm eB.symm hgT.symm T.monic
  let S_N : Subobject (C.A N) xB := ⟨xSdr, gS, homInclObj_mono_reflects C hC hfaith gS hgSmono⟩
  let T_N : Subobject (C.A N) xB := ⟨xTdr, gT, homInclObj_mono_reflects C hC hfaith gT hgTmono⟩
  -- identify `A, B` with the stage reps, and `f` with the germ
  subst eB; subst eA
  have hfeq : f = homInclObj C hC f_N := (eq_of_heq hf).symm
  -- `S ≈ germSub S_N`, `T ≈ germSub T_N`
  have hSeq : S.Equiv (germSub C hC hmono S_N) := by
    refine ⟨subobject_le_of_heq_arr S.arr (homInclObj C hC gS) S.monic
       (germSub C hC hmono S_N).monic eSd hgS, ?_⟩
    show (Subobject.mk (C.objIncl N xSdr) (homInclObj C hC gS) (germSub C hC hmono S_N).monic).le S
    exact subobject_le_of_heq_arr (homInclObj C hC gS) S.arr (germSub C hC hmono S_N).monic
      S.monic eSd.symm hgS.symm
  have hTeq : T.Equiv (germSub C hC hmono T_N) := by
    refine ⟨subobject_le_of_heq_arr T.arr (homInclObj C hC gT) T.monic
       (germSub C hC hmono T_N).monic eTd hgT, ?_⟩
    show (Subobject.mk (C.objIncl N xTdr) (homInclObj C hC gT) (germSub C hC hmono T_N).monic).le T
    exact subobject_le_of_heq_arr (homInclObj C hC gT) T.arr (germSub C hC hmono T_N).monic
      T.monic eTd.symm hgT.symm
  -- LHS as a germ
  have hLHS : (InverseImage f (HasSubobjectUnions.union S T)).Equiv
      (germSub C hC hmono (pbSub (ht N) (hp N) (he N) f_N (unionImg (hi N) (hcop N) S_N T_N))) := by
    rw [hfeq]
    have hUeq := Subobject.Equiv.trans ⟨union_mono hSeq.1 hTeq.1, union_mono hSeq.2 hTeq.2⟩
      (union_germ_equiv C hC hmono hcop hcoppres hcoppres_case hi hfaith himgpres N S_N T_N)
    refine Subobject.Equiv.trans
      ⟨inverseImage_mono (homInclObj C hC f_N) hUeq.1,
        inverseImage_mono (homInclObj C hC f_N) hUeq.2⟩
      (invImage_germ_equiv C hC hmono ht htpres hp hpres hpres_pair he hepres hepres_lift
        N f_N (unionImg (hi N) (hcop N) S_N T_N))
  -- RHS as a germ
  have hRHS : (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).Equiv
      (germSub C hC hmono (unionImg (hi N) (hcop N)
        (pbSub (ht N) (hp N) (he N) f_N S_N) (pbSub (ht N) (hp N) (he N) f_N T_N))) := by
    rw [hfeq]
    have hXS := Subobject.Equiv.trans
        ⟨inverseImage_mono (homInclObj C hC f_N) hSeq.1,
          inverseImage_mono (homInclObj C hC f_N) hSeq.2⟩
        (invImage_germ_equiv C hC hmono ht htpres hp hpres hpres_pair he hepres hepres_lift N f_N S_N)
    have hXT := Subobject.Equiv.trans
        ⟨inverseImage_mono (homInclObj C hC f_N) hTeq.1,
          inverseImage_mono (homInclObj C hC f_N) hTeq.2⟩
        (invImage_germ_equiv C hC hmono ht htpres hp hpres hpres_pair he hepres hepres_lift
          N f_N T_N)
    exact Subobject.Equiv.trans ⟨union_mono hXS.1 hXT.1, union_mono hXS.2 hXT.2⟩
      (union_germ_equiv C hC hmono hcop hcoppres hcoppres_case hi hfaith himgpres N
        (pbSub (ht N) (hp N) (he N) f_N S_N) (pbSub (ht N) (hp N) (he N) f_N T_N))
  -- stage hard direction, transported up
  refine Subobject.le_trans hLHS.1 (Subobject.le_trans
    (germSub_le C hC hmono
      (stage_invImage_union_le (hPL := hbot N) (ht N) (hp N) (he N) (hi N) (hcop N) f_N S_N T_N))
    hRHS.symm.1)

end Freyd.Colim
