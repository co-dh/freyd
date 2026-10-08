module

public import AOP.A5_5
import all AOP.A5_5

section
universe u
namespace Freyd.Alg
variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜] (F : Relator 𝒜 𝒜)
variable {F}

/-- Step 5: fold uniqueness, now that `Λ(F(∋)R)` is a map: the chain's last term is its fold. -/
public theorem relCata_UP_step5 (I : InitialAlgebra F) {A : 𝒜} {R : F.obj A ⟶ A} {X : I.t ⟶ A}
    (h : I.α ≫ X = F.map X ≫ R) :
    I.α° ≫ F.map (Λ X) ≫ Λ (F.map (∋ A) ≫ R) = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) :=
  (relCata_UP_chain I h).symm.trans ((relCata_UP_fold I).mp h)

/-- **B&dM p.121, the map algebra's square**: the fold's defining equation at the MAP algebra
    `Λ(F(∋)R)`, together with the triangle saying what that algebra is — `Λ(F(∋)R)∋ = F(∋)R`.
    Two faces of one picture: the second says the algebra the first folds is the transpose of
    `F(∋)R`, and they share that algebra.  The algebra is NAMED `f` and pinned by `hf`, which is
    how the picture writes a name on that arrow with its value beneath. -/
public theorem relCata_mapAlg_cancel (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A)
    {f} (hf : f = Λ (F.map (∋ A) ≫ R)) (hm : Map f) :
    I.α ≫ I.cata f hm = F.map (I.cata f hm) ≫ f
      ∧ f ≫ ∋ A = F.map (∋ A) ≫ R := by
  subst hf; exact ⟨I.cata_comm _ _, Λ_comp_eps _⟩

/-- **B&dM Ex 2.35, p.49**, verbatim: "Show that `(|f · g|) = f · (|g · F f|)`", with the
    types the book leaves implicit — `f : A ← X` and `g : X ← F A`, so `f·g : A ← F A` is an
    F-algebra on `A` and `g·F f : X ← F X` one on `X`.  Mirrored to diagram order with
    `f : x ⟶ a` and `g : F.obj a ⟶ x` it reads `(|(F f) g|) f = (|g f|)`.

    This is `relCata_fusion` at `R := (F f) g`, `S := f`, `Q := g f`, whose side condition
    `R S = (F S) Q` is nothing but associativity: both sides are the same three-arrow word
    `(F f) g f`, bracketed `((F f) g) f` on the left and `(F f) (g f)` on the right.

    A one-term theorem, kept despite the repo's no-wrapper rule under its stated exception
    for a statement that is itself a required deliverable — this is a book-numbered exercise. -/
public theorem relCata_of_comp (I : InitialAlgebra F) {A x : 𝒜} (f : x ⟶ A) (g : F.obj A ⟶ x) :
    relCata (F.map f ≫ g) ≫ f = relCata (g ≫ f) :=
  relCata_fusion I (Cat.assoc (F.map f) g f)

/-- **THE FOLD IS STRICTLY NATURAL IN ITS ALGEBRA**: `Δᴛ(S) ⦇B⦈ = ⦇A⦈ S` for every homomorphism
    `S : A ⟶ B`, `S` below the fold being `U(S)`, the underlying arrow.  `Δᴛ(S)` is the identity,
    so this is `relCata_fusion` read as one square of a natural transformation — an EQUALITY, in
    `TabularUnitaryUnguardedDivisionPowerAllegory`. -/
public theorem fold_natural [I : InitialAlgebra F] {A B : Algebra F} (S : A ⟶ B) :
    (algDelta (F := F)).map S ≫ fold B = fold A ≫ S.hom := by
  show 𝟙 I.t ≫ relCata B.alg = relCata A.alg ≫ S.hom
  rw [Cat.id_comp, relCata_fusion I S.comm]

/-- **An algebra on a PRODUCT carrier is folded by a fork.**  `⟨f,g⟩` meets the two defining
    equations of `h` and `k` — one per component, each seeing BOTH components through `F(⟨f,g⟩)` —
    exactly when it is `⦇⟨h,k⟩⦈`.  Strictly more general than banana split, where `h` and `k`
    factor as `F(π₁)h` and `F(π₂)k` and so each sees only its own component. -/
public theorem pair_eq_relCata_pair_iff [HasBinaryProducts 𝒜] (I : InitialAlgebra F)
    {A B : 𝒜} (f : I.t ⟶ A) (g : I.t ⟶ B)
    (h : F.obj (prod A B) ⟶ A) (k : F.obj (prod A B) ⟶ B) :
    (I.α ≫ f = F.map (pair f g) ≫ h ∧ I.α ≫ g = F.map (pair f g) ≫ k)
      ↔ pair f g = ⦇pair h k⦈ := by
  -- The fold's universal property at `X := ⟨f,g⟩`, `R := ⟨h,k⟩`, with both sides of its equation
  -- pushed through the fork (`pair_precomp`); `⟨-,-⟩` is then injective by its own two β-laws.
  rw [← relCata_UP I (pair h k) (pair f g), pair_precomp, pair_precomp]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro hEq
    exact ⟨by rw [← fst_pair (I.α ≫ f) (I.α ≫ g), hEq, fst_pair],
           by rw [← snd_pair (I.α ≫ f) (I.α ≫ g), hEq, snd_pair]⟩

end Freyd.Alg
end

section
universe u
namespace Freyd.Alg
variable {𝒜 : Type u} [TabularUnitaryUnguardedDivisionPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}

/-- **BANANA SPLIT (B&dM figure 7b)**: the product's universal property read AT THE TWO FOLDS.
    `⟨⦇h⦈,⦇k⦈⟩` is the one arrow `T⟶A×B` with components `⦇h⦈` and `⦇k⦈`, and these are the two
    triangles the note draws round it — which is why the statement is the pair of β-laws at
    `⦇h⦈`, `⦇k⦈` rather than the β-laws at two arbitrary arrows. -/
public theorem relCata_pair_beta [HasBinaryProducts 𝒜] (I : InitialAlgebra F) {A B : 𝒜}
    (h : F.obj A ⟶ A) (k : F.obj B ⟶ B) :
    pair ⦇h⦈ ⦇k⦈ ≫ fst = ⦇h⦈ ∧ pair ⦇h⦈ ⦇k⦈ ≫ snd = ⦇k⦈ :=
  ⟨fst_pair _ _, snd_pair _ _⟩

/-- **BANANA SPLIT (B&dM Ex 3.6, p. 57)**: `⟨(|h|),(|k|)⟩ = (|⟨F(π₁)·h, F(π₂)·k⟩|)` — a fork of
    two folds is ONE fold, hence one traversal.  It is the special case of the mutual-recursion
    law (`pair_eq_relCata_pair_iff`) where the two algebras factor through the projections, so
    each sees only its own component; the two defining equations then reduce to
    `F(⟨(|h|),(|k|)⟩)·F(π₁) = F((|h|))` and its mirror. -/
public theorem pair_relCata_eq_relCata_pair [HasBinaryProducts 𝒜] (I : InitialAlgebra F)
    {A B : 𝒜} (h : F.obj A ⟶ A) (k : F.obj B ⟶ B) :
    pair ⦇h⦈ ⦇k⦈ = ⦇pair (F.map fst ≫ h) (F.map snd ≫ k)⦈ :=
  (pair_eq_relCata_pair_iff I ⦇h⦈ ⦇k⦈ (F.map fst ≫ h) (F.map snd ≫ k)).mp
    ⟨by rw [relCata_cancel I h, ← Cat.assoc, ← F.map_comp, fst_pair],
     by rw [relCata_cancel I k, ← Cat.assoc, ← F.map_comp, snd_pair]⟩

/-- The fork of two folds is a HOMOMORPHISM from `α` to the product algebra
    `⟨F(π₁)h, F(π₂)k⟩`: the square the banana-split picture draws, `α` on its top edge. -/
public theorem pair_relCata_hom [HasBinaryProducts 𝒜] (I : InitialAlgebra F)
    {A B : 𝒜} (h : F.obj A ⟶ A) (k : F.obj B ⟶ B) :
    I.α ≫ pair ⦇h⦈ ⦇k⦈ = F.map (pair ⦇h⦈ ⦇k⦈) ≫ pair (F.map fst ≫ h) (F.map snd ≫ k) := by
  rw [pair_relCata_eq_relCata_pair]; exact relCata_cancel I _

end Freyd.Alg
end
