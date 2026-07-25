/-
  Freyd & Scedrov, *Categories and Allegories* §1.33–§1.333
  Faithful functors, reflects iso, Cayley representations, functors on posets.
-/


import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_41
import Freyd.S1_81


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.33 Faithful functors -/

/-- F is FAITHFUL if it is an embedding and reflects isomorphisms. -/
def Faithful (F : Functor 𝒞 𝒟) : Prop :=
  Embedding F ∧ (∀ {A B : 𝒞} (f : A ⟶ B), IsIso (F.map f) → IsIso f)

/-- Full embeddings are faithful. -/
theorem full_embedding_faithful (F : Functor 𝒞 𝒟)
    (hEmb : Embedding F) (hFull : Full F) : Faithful F := by
  refine ⟨hEmb, ?_⟩
  intro A B f hiso
  rcases hiso with ⟨ginv, h1, h2⟩
  rcases hFull ginv with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · apply hEmb
    calc
      F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp f g
      _ = F.map f ≫ ginv := by rw [hg]
      _ = Cat.id (F.obj A) := h1
      _ = F.map (Cat.id A) := by rw [F.map_id]
  · apply hEmb
    calc
      F.map (g ≫ f) = F.map g ≫ F.map f := F.map_comp g f
      _ = ginv ≫ F.map f := by rw [hg]
      _ = Cat.id (F.obj B) := h2
      _ = F.map (Cat.id B) := by rw [F.map_id]

/-! ## §1.331 Reflects left-invertibility ⇒ reflects isomorphisms -/

/-- If F reflects left-invertibility, it reflects isomorphisms (§1.331).

    Book's proof: if Ff is an isomorphism, it is left-invertible.  Reflecting,
    f has a left inverse g (g ≫ f = id).  Then Fg ≫ Ff = id, so Fg = (Ff)⁻¹
    (unique via right-cancellation using Ff ≫ finv = id), hence Ff ≫ Fg = id.
    So Fg is left-invertible; reflecting, g has left inverse z (z ≫ g = id).
    Then z = z ≫ id_B = z ≫ g ≫ f = (z ≫ g) ≫ f = id_A ≫ f = f,
    so f ≫ g = id_A.  Combined with g ≫ f = id_B, f is an isomorphism. -/
theorem reflects_leftInv_reflects_iso (F : Functor 𝒞 𝒟)
    (reflLI : ∀ {A B : 𝒞} (f : A ⟶ B), HasLeftInv (F.map f) → HasLeftInv f)
    {A B : 𝒞} (f : A ⟶ B) (hiso : IsIso (F.map f)) : IsIso f := by
  obtain ⟨finv, hfinv1, hfinv2⟩ := hiso
  -- hfinv1 : F.map f ≫ finv = Cat.id (F.obj A)
  -- hfinv2 : finv ≫ F.map f = Cat.id (F.obj B)
  -- Step 1: Ff has left inverse finv; reflect to get g : B ⟶ A with g ≫ f = id_B
  obtain ⟨g, hgf⟩ := reflLI f ⟨finv, hfinv2⟩
  -- Step 2: Fg ≫ Ff = F(g ≫ f) = F(id_B) = id_{FB}
  have hFgFf : F.map g ≫ F.map f = Cat.id (F.obj B) := by
    rw [← F.map_comp, hgf, F.map_id]
  -- Step 3: Fg = finv  (right-cancel Ff: both Fg and finv satisfy ? ≫ Ff = id)
  have hFg_eq_finv : F.map g = finv := by
    have cancel : ∀ (u v : F.obj B ⟶ F.obj A), u ≫ F.map f = v ≫ F.map f → u = v := fun u v huv => by
      have := congrArg (· ≫ finv) huv
      simp only [Cat.assoc, hfinv1, Cat.comp_id] at this
      exact this
    exact cancel _ _ (by rw [hFgFf, hfinv2])
  -- Step 4: Ff ≫ Fg = Ff ≫ finv = id_{FA}
  have hFfFg : F.map f ≫ F.map g = Cat.id (F.obj A) := by
    rw [hFg_eq_finv, hfinv1]
  -- Step 5: Fg has left inverse Ff; reflect to get z : A ⟶ B with z ≫ g = id_A
  obtain ⟨z, hzg⟩ := reflLI g ⟨F.map f, hFfFg⟩
  -- Step 6: z = f  via  z = z ≫ (g ≫ f) = (z ≫ g) ≫ f = id_A ≫ f = f
  --   (using g ≫ f = id_B, so z ≫ Cat.id B = z ≫ g ≫ f)
  have hz_eq_f : z = f := by
    calc z = z ≫ Cat.id B          := (Cat.comp_id z).symm
      _ = z ≫ (g ≫ f)             := by rw [← hgf]
      _ = (z ≫ g) ≫ f             := (Cat.assoc z g f).symm
      _ = Cat.id A ≫ f             := by rw [hzg]
      _ = f                        := Cat.id_comp f
  -- Conclusion: g is the two-sided inverse of f
  --   f ≫ g = id_A  (from z = f and z ≫ g = id_A)
  --   g ≫ f = id_B  (hgf)
  exact ⟨g, by rwa [← hz_eq_f], hgf⟩

/-! ## §1.332 Contravariant Cayley representation C° -/

/-- The type of morphisms with source A (§1.332). -/
private def CoHom (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  (B : 𝒞) × (A ⟶ B)

/-- The CONTRAVARIANT CAYLEY representation C° (§1.332).
    C°(A) = {y | □y = A} = morphisms with source A.
    For f : A → B, C°(f) : C°(B) → C°(A) by pre-composition:
      C°(f)(y : B → C) = (f ≫ y : A → C). -/
def contraCayleyObj (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  CoHom 𝒞 A

/-- The action of C° on morphisms: pre-compose with f. -/
private def contraCayleyMap {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    contraCayleyObj 𝒞 B → contraCayleyObj 𝒞 A :=
  fun ⟨C, y⟩ => ⟨C, f ≫ y⟩

/-- C° preserves identity: C°(id_A)(y) = id_A ≫ y = y. -/
private theorem contraCayleyMap_id {𝒞 : Type u} [Cat.{v} 𝒞] (A : 𝒞) :
    contraCayleyMap (Cat.id A) = id := by
  funext ⟨C, y⟩; simp [contraCayleyMap, Cat.id_comp]

/-- C° reverses composition: C°(f ≫ g) = C°(f) ∘ C°(g).
    Because (f ≫ g) ≫ y = f ≫ (g ≫ y). -/
private theorem contraCayleyMap_comp {𝒞 : Type u} [Cat.{v} 𝒞] {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) :
    contraCayleyMap (f ≫ g) = contraCayleyMap f ∘ contraCayleyMap g := by
  funext ⟨D, y⟩; simp [contraCayleyMap, Cat.assoc]

/-- C° is faithful: if C°(f) = C°(g) then f = g (§1.332).
    Witness: (B, id_B) ∈ C°(B); C°(f)(id_B) = f ≫ id_B = f. -/
theorem contraCayley_faithful {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f g : A ⟶ B)
    (h : contraCayleyMap f = contraCayleyMap g) : f = g := by
  have hfg : contraCayleyMap f ⟨B, Cat.id B⟩ = contraCayleyMap g ⟨B, Cat.id B⟩ :=
    congrFun h ⟨B, Cat.id B⟩
  simp [contraCayleyMap, Cat.comp_id] at hfg
  exact eq_of_heq (Sigma.ext_iff.mp hfg).2

/-- C° reflects right-invertibility (§1.332).
    If C°(x) : C°(B) → C°(A) is right-invertible (has a right inverse), then x : A → B
    is right-invertible.
    Proof: apply the right inverse r to ⟨A, id_A⟩ ∈ C°(A).  Then
    C°(x)(r⟨A,id_A⟩) = ⟨A,id_A⟩, which unpacks to x ≫ y = id_A for some y. -/
theorem contraCayley_reflects_rightInv {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (x : A ⟶ B)
    (h : ∃ (r : contraCayleyObj 𝒞 A → contraCayleyObj 𝒞 B),
          contraCayleyMap x ∘ r = id) :
    ∃ y : B ⟶ A, x ≫ y = Cat.id A := by
  obtain ⟨r, hr⟩ := h
  have h0 : contraCayleyMap x (r ⟨A, Cat.id A⟩) = ⟨A, Cat.id A⟩ := congrFun hr ⟨A, Cat.id A⟩
  -- Generalize r ⟨A, id_A⟩ to a fresh variable p so that `obtain` on p
  -- replaces it uniformly in h0, allowing simp to reduce the match.
  revert h0
  generalize r ⟨A, Cat.id A⟩ = p
  intro h0
  obtain ⟨C, z⟩ := p
  simp only [contraCayleyMap] at h0
  -- h0 : ⟨C, x ≫ z⟩ = ⟨A, id_A⟩ in (Z : 𝒞) × (A ⟶ Z)
  have hC : C = A := (Sigma.ext_iff.mp h0).1
  subst hC
  exact ⟨z, eq_of_heq (Sigma.ext_iff.mp h0).2⟩

/-! ## §1.332 Power-set functor -/

/-- P(f) = inverse image along f. -/
def powerSetMap {S T : Type u} (f : S → T) : Sub T → Sub S :=
  fun T' x => T' (f x)

theorem powerSetMap_id (S : Type u) : powerSetMap (id : S → S) = id := rfl

theorem powerSetMap_comp {S T U : Type u} (f : S → T) (g : T → U) :
    powerSetMap (g ∘ f) = powerSetMap f ∘ powerSetMap g := rfl

/-! ## §1.332 Combined covariant functor F = C × P(C°) -/

/-- The covariant Cayley object C(A) = morphisms with TARGET A (§1.332).
    This is the "dual" of C°: C(A) = {y | ◻y = A}. -/
private def CovHom (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  (B : 𝒞) × (B ⟶ A)

/-- The action of C on morphisms: post-compose with f.
    For f : A → B, C(f) : C(A) → C(B) sends (Z, y : Z→A) to (Z, y ≫ f : Z→B). -/
private def covCayleyMap {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    CovHom 𝒞 A → CovHom 𝒞 B :=
  fun ⟨Z, y⟩ => ⟨Z, y ≫ f⟩

/-- The combined object F(A) = C(A) × P(C°(A)) (§1.332).
    C is covariant Cayley (morphisms into A); P(C°(A)) = predicates on morphisms out of A. -/
def combinedCayleyObj (𝒞 : Type u) [Cat.{v} 𝒞] (A : 𝒞) : Type (max u v) :=
  CovHom 𝒞 A × (contraCayleyObj 𝒞 A → Prop)

/-- The action of F on morphisms: for f : A → B,
    first component C(A)→C(B) via post-composition;
    second component P(C°(A))→P(C°(B)) via P(C°(f)) = inverse image along C°(f). -/
def combinedCayleyMap {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    combinedCayleyObj 𝒞 A → combinedCayleyObj 𝒞 B :=
  fun p => ⟨covCayleyMap f p.1, fun z => p.2 (contraCayleyMap f z)⟩

/-- F reflects left-invertibility (§1.332): if `combinedCayleyMap x` has a *function* right
    inverse `r` (`combinedCayleyMap x ∘ r = id`), then `x` has a left inverse `y`,
    `y ≫ x = id_B` (repo `HasLeftInv x`).

    Convention note.  In the repo's Cat-of-Types, a morphism's left inverse `g` satisfies
    `g ≫ f = id`, i.e. (diagram order) `f ∘ g = id` in Lean's `∘` — a *function right
    inverse*.  Functors preserve, faithful representations reflect, this property; here the
    witness comes entirely from the *covariant Cayley* component `C` of `F = C × P(C°)`.

    Proof.  A function right inverse `r` of `F(x)` makes `F(x)` surjective, hence so is its
    first (C) component `covCayleyMap x : C(A) → C(B)`, `⟨Z,w⟩ ↦ ⟨Z, w ≫ x⟩`.  Surjectivity
    onto `⟨B, id_B⟩ ∈ C(B)` produces `⟨W, y⟩ ∈ C(A)` with `⟨W, y ≫ x⟩ = ⟨B, id_B⟩`; the
    first projection forces `W = B`, and the second gives `y ≫ x = id_B`.  (The companion
    `P(C°)` component, dual to `contraCayley_reflects_rightInv`, is what reflects right-
    invertibility; combining the two gives Freyd's "F reflects both".) -/
theorem combined_reflects_leftInv {𝒞 : Type u} [Cat.{v} 𝒞] {A B : 𝒞} (x : A ⟶ B)
    (h : ∃ (r : combinedCayleyObj 𝒞 B → combinedCayleyObj 𝒞 A),
          combinedCayleyMap x ∘ r = id) :
    ∃ y : B ⟶ A, y ≫ x = Cat.id B := by
  obtain ⟨r, hr⟩ := h
  -- Apply the right inverse at the C(B) element ⟨B, id_B⟩; its image under F(x) is itself.
  have h0 : combinedCayleyMap x (r ⟨⟨B, Cat.id B⟩, fun _ => False⟩)
      = ⟨⟨B, Cat.id B⟩, fun _ => False⟩ := congrFun hr _
  -- Generalise the whole preimage element so `obtain` splits it uniformly in h0.
  revert h0
  generalize r ⟨⟨B, Cat.id B⟩, fun _ => False⟩ = p
  intro h0
  obtain ⟨⟨W, y⟩, pred⟩ := p
  -- Read off the first (covariant Cayley) component: ⟨W, y ≫ x⟩ = ⟨B, id_B⟩.
  have h1 := congrArg Prod.fst h0
  simp only [combinedCayleyMap, covCayleyMap] at h1
  -- h1 : ⟨W, y ≫ x⟩ = ⟨B, id_B⟩  in  (Z : 𝒞) × (Z ⟶ B)
  have hW : W = B := (Sigma.ext_iff.mp h1).1
  subst hW
  exact ⟨y, eq_of_heq (Sigma.ext_iff.mp h1).2⟩

/-! ## §1.333 Functors between posets -/

/-- A PREORDER structure (reflexive, transitive relation). -/
class ProsetCat (α : Type u) : Type u where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- Turn a `ProsetCat` into a `Cat` instance.  Hom-sets are proof-irrelevant (thin). -/
instance prosetToCat {α : Type u} [P : ProsetCat α] : Cat.{0} α where
  Hom a b := PLift (P.le a b)
  id a := ⟨P.refl a⟩
  comp h k := ⟨P.trans h.down k.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- In a preorder-category any two parallel hom-set elements are equal (thin category). -/
theorem proset_hom_subsingleton {α : Type u} [ProsetCat α] {a b : α}
    (f g : a ⟶ b) : f = g := by
  obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl

/-- A functor between preorder-categories is always an embedding (§1.333).
    Proof: morphisms are proof-irrelevant, so any two parallel morphisms are equal. -/
theorem proset_functor_embedding {α β : Type u}
    [ProsetCat α] [ProsetCat β] (F : Functor α β) :
    Embedding F := by
  intro A B f g _
  exact proset_hom_subsingleton f g

/-- §1.333: a functor between preorders is monotone (order-preserving). -/
theorem proset_functor_monotone {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β] (F : Functor α β)
    {a b : α} (hab : P.le a b) : Q.le (F.obj a) (F.obj b) :=
  (F.map (⟨hab⟩ : (a ⟶ b))).down

/-- §1.333: a functor between preorders is full iff the ordering on the domain is induced
    by the ordering on the range: P.le a b ↔ Q.le (F a) (F b).

    Forward (full → induced): If F is full and Q.le (Fa)(Fb), fullness gives f : a → b in P,
    so P.le a b.  The other direction follows from monotonicity.

    Backward (induced → full): Given any Q-morphism h : Fa → Fb (i.e. Q.le (Fa)(Fb)),
    the induced-ordering hypothesis gives P.le a b, hence a P-morphism f : a → b with F(f) = h
    (by proof irrelevance in Q). -/
theorem proset_functor_full_iff_induced {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β] (F : Functor α β) :
    Full F ↔
    (∀ a b : α, P.le a b ↔ Q.le (F.obj a) (F.obj b)) := by
  constructor
  · intro hFull a b
    constructor
    · intro hab
      exact (F.map (⟨hab⟩ : (a ⟶ b))).down
    · intro hFab
      obtain ⟨f, _⟩ := hFull (⟨hFab⟩ : (F.obj a ⟶ F.obj b))
      exact f.down
  · intro hInd A B h
    exact ⟨⟨(hInd A B).mpr h.down⟩, proset_hom_subsingleton _ _⟩

/-- §1.333: if F is full and faithful between posets, then F is injective on objects.
    Uses fullness to lift Q-morphisms in both directions to P-morphisms, then antisymP. -/
theorem proset_full_faithful_inj {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β]
    (antisymP : ∀ {a b : α}, P.le a b → P.le b a → a = b)
    (F : Functor α β)
    (hFull : Full F)
    (_ : Faithful F) :
    ∀ a b : α, F.obj a = F.obj b → a = b := fun a b hFab => by
  have h_ab : Q.le (F.obj a) (F.obj b) := hFab ▸ Q.refl (F.obj a)
  have h_ba : Q.le (F.obj b) (F.obj a) := hFab ▸ Q.refl (F.obj b)
  obtain ⟨f, _⟩ := hFull (⟨h_ab⟩ : (F.obj a ⟶ F.obj b))
  obtain ⟨g, _⟩ := hFull (⟨h_ba⟩ : (F.obj b ⟶ F.obj a))
  exact antisymP f.down g.down

/-- §1.333: an injective-on-objects functor between posets is faithful (§1.333 backward).
    Proof: embedding is free (thin cat); reflects-iso uses antisymQ + injectivity to show
    A = B and then any f : A → A is its own inverse. -/
theorem proset_inj_faithful {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β]
    (antisymQ : ∀ {a b : β}, Q.le a b → Q.le b a → a = b)
    (F : Functor α β)
    (hInj : ∀ a b : α, F.obj a = F.obj b → a = b) :
    Faithful F :=
  ⟨proset_functor_embedding F, fun {A B} f hiso => by
    obtain ⟨g, _, _⟩ := hiso
    have hFAFB : F.obj A = F.obj B := antisymQ (F.map f).down g.down
    have hAB : A = B := hInj A B hFAFB
    subst hAB
    exact ⟨f, proset_hom_subsingleton _ _, proset_hom_subsingleton _ _⟩⟩

/-- §1.333: for a FULL functor between posets, faithful iff injective on objects.

    The book (§1.333) states "faithful iff one-to-one on objects".  With our
    diagrammatic `Faithful = Embedding + reflects-iso`, the forward direction
    (Faithful ⟹ injective on objects) is FALSE without fullness: the unique functor
    from the 2-element discrete poset {a,b} to the 1-element poset {x} is an Embedding
    (no non-trivial parallel morphisms) and reflects isos (vacuously, every domain
    morphism is already iso), yet is not injective on objects.  Freyd's posets carry
    the *induced* ordering, i.e. the representations he uses are full; we therefore
    state the iff under the fullness hypothesis, which makes it genuinely true.

    Forward (uses fullness): `proset_full_faithful_inj` — from F a = F b lift
      id_{Fa} : Fa ⟶ Fb and id_{Fb} : Fb ⟶ Fa back to P-morphisms a ⟶ b and b ⟶ a,
      then P-antisymmetry gives a = b.

    Backward: injective on objects ⟹ faithful (`proset_inj_faithful`); fullness unused.
      For reflects-iso: from IsIso (hF.map f), Q-antisymmetry gives Fa = Fb,
      injectivity gives a = b, and then IsIso f is trivial. -/
theorem proset_faithful_iff_injective {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β]
    (antisymP : ∀ {a b : α}, P.le a b → P.le b a → a = b)
    (antisymQ : ∀ {a b : β}, Q.le a b → Q.le b a → a = b)
    (F : Functor α β)
    (hFull : Full F) :
    Faithful F ↔
    (∀ a b : α, F.obj a = F.obj b → a = b) := by
  constructor
  · intro hFaith
    exact proset_full_faithful_inj antisymP F hFull hFaith
  · intro hInj
    exact proset_inj_faithful antisymQ F hInj


/-- §1.333: equivalence functor between posets iff order-isomorphism.

    An order-isomorphism is a surjective monotone functor whose inverse is also monotone,
    equivalently a bijection F with P.le a b ↔ Q.le (F a) (F b). -/
theorem proset_equiv_iff_ord_iso {α β : Type u}
    [P : ProsetCat α] [Q : ProsetCat β]
    (antisymP : ∀ {a b : α}, P.le a b → P.le b a → a = b)
    (antisymQ : ∀ {a b : β}, Q.le a b → Q.le b a → a = b)
    (F : Functor α β) :
    EquivalenceFunctor F ↔
    ((∀ a b : α, F.obj a = F.obj b → a = b) ∧
     (∀ b : β, ∃ a : α, F.obj a = b) ∧
     (∀ a b : α, P.le a b ↔ Q.le (F.obj a) (F.obj b))) := by
  constructor
  · intro ⟨hEmb, hFull, hRep⟩
    refine ⟨?_, ?_, ?_⟩
    · -- Injective on objects: from Fa = Fb, use fullness to get morphisms a→b and b→a,
      -- then antisymP.
      intro a b hFab
      -- Fa = Fb, so id_{Fa} : Fa ⟶ Fb in Q-cat.
      have h_ab : Q.le (F.obj a) (F.obj b) := hFab ▸ Q.refl (F.obj a)
      have h_ba : Q.le (F.obj b) (F.obj a) := hFab ▸ Q.refl (F.obj b)
      obtain ⟨f, _⟩ := hFull (⟨h_ab⟩ : (F.obj a ⟶ F.obj b))
      obtain ⟨g, _⟩ := hFull (⟨h_ba⟩ : (F.obj b ⟶ F.obj a))
      exact antisymP f.down g.down
    · -- Surjective: from HasRepresentativeImage
      intro B
      obtain ⟨A, h, hiso⟩ := hRep B
      obtain ⟨k, _, _⟩ := hiso
      -- h : Q.le (FA) B, k : Q.le B (FA); antisymQ gives FA = B
      exact ⟨A, antisymQ h.down k.down⟩
    · -- Order iff
      intro a b; constructor
      · intro hab
        exact (F.map (⟨hab⟩ : (a ⟶ b))).down
      · intro hFaFb
        obtain ⟨f, _⟩ := hFull (⟨hFaFb⟩ : (F.obj a ⟶ F.obj b))
        exact f.down
  · intro ⟨hInj, hSurj, hOrd⟩
    refine ⟨proset_functor_embedding F, ?_, ?_⟩
    · -- Full
      intro A B h
      exact ⟨⟨(hOrd A B).mpr h.down⟩, proset_hom_subsingleton _ _⟩
    · -- HasRepresentativeImage
      intro B
      obtain ⟨A, hFA⟩ := hSurj B
      exact ⟨A, ⟨hFA ▸ Q.refl (F.obj A)⟩,
        ⟨⟨hFA ▸ Q.refl (F.obj A)⟩,
         proset_hom_subsingleton _ _,
         proset_hom_subsingleton _ _⟩⟩

end Freyd
