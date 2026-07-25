/-
  Freyd & Scedrov, *Categories and Allegories* §1.34–§1.341
  Isomorphic objects, equinumerosity, isomorphism classes.
-/


import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_41


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.34 Isomorphic objects -/

/-- Objects A and B are ISOMORPHIC (A ≅ B) if there exists an iso A → B. -/
def Isomorphic (A B : 𝒞) : Prop := ∃ (f : A ⟶ B), IsIso f

/-- Isomorphic is reflexive. -/
theorem isomorphic_refl (A : 𝒞) : Isomorphic A A :=
  ⟨Cat.id A, ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- Isomorphic is symmetric. -/
theorem isomorphic_symm {A B : 𝒞} (h : Isomorphic A B) : Isomorphic B A := by
  rcases h with ⟨f, g, hfg, hgf⟩
  exact ⟨g, f, hgf, hfg⟩

/-- Isomorphic is transitive. -/
theorem isomorphic_trans {A B C : 𝒞} (hAB : Isomorphic A B) (hBC : Isomorphic B C) : Isomorphic A C := by
  obtain ⟨f, hf⟩ := hAB; obtain ⟨g, hg⟩ := hBC
  exact ⟨f ≫ g, isIso_comp hf hg⟩

/-- Functors preserve isomorphic objects. -/
theorem functor_preserves_iso_obj (F : Functor 𝒞 𝒟) {A B : 𝒞}
    (h : Isomorphic A B) : Isomorphic (F.obj A) (F.obj B) := by
  rcases h with ⟨f, hf_iso⟩
  rcases hf_iso with ⟨g, hfg, hgf⟩
  have h_iso : IsIso (F.map f) := functor_preserves_iso (F := F) f ⟨g, hfg, hgf⟩
  exact ⟨F.map f, h_iso⟩

/-- Full embeddings reflect isomorphism of objects. -/
theorem full_embedding_reflects_iso_obj (F : Functor 𝒞 𝒟)
    (hEmb : Embedding F) (hFull : Full F) {A B : 𝒞} (h : Isomorphic (F.obj A) (F.obj B)) :
    Isomorphic A B := by
  rcases h with ⟨h, ginv, h1, h2⟩
  rcases hFull h with ⟨f, hf⟩
  rcases hFull ginv with ⟨g, hg⟩
  refine ⟨f, g, ?_, ?_⟩
  · apply hEmb
    calc
      F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp _ _
      _ = h ≫ ginv := by rw [hf, hg]
      _ = Cat.id (F.obj A) := h1
      _ = F.map (Cat.id A) := (F.map_id _).symm
  · apply hEmb
    calc
      F.map (g ≫ f) = F.map g ≫ F.map f := F.map_comp _ _
      _ = ginv ≫ h := by rw [hg, hf]
      _ = Cat.id (F.obj B) := h2
      _ = F.map (Cat.id B) := (F.map_id _).symm

/-! ## §1.34 One-to-one correspondence on iso-types -/

/-- An equivalence functor maps isomorphic objects to isomorphic objects
    and non-isomorphic objects to non-isomorphic objects (reflects via full embedding). -/
theorem equiv_functor_isoClass_iff (F : Functor 𝒞 𝒟)
    (hEq : EquivalenceFunctor F) {A B : 𝒞} :
    Isomorphic A B ↔ Isomorphic (F.obj A) (F.obj B) :=
  ⟨functor_preserves_iso_obj F, full_embedding_reflects_iso_obj F hEq.1 hEq.2.1⟩

/-- Every isomorphism class in 𝒟 is hit by F (surjectivity on iso-types). -/
theorem equiv_functor_isoClass_surjective (F : Functor 𝒞 𝒟)
    (hEq : EquivalenceFunctor F) (B : 𝒟) : ∃ A : 𝒞, Isomorphic (F.obj A) B := by
  rcases hEq.2.2 B with ⟨A, h, hiso⟩
  exact ⟨A, h, hiso⟩

/-! ## §1.341 Equinumerosity and axiom of choice -/

/-- The iso-class of A: the collection of objects isomorphic to A. -/
def isoClass (A : 𝒞) : 𝒞 → Prop := fun B => Isomorphic A B

/-- Cross-type equinumerosity: existence of a bijection between two
    predicate-selected subcollections of (possibly different) types. -/
def CrossEquinumerous {α β : Type u} (S : α → Prop) (T : β → Prop) : Prop :=
  ∃ (f : α → β),
    (∀ x, S x → T (f x)) ∧
    (∀ y, T y → ∃ x, S x ∧ f x = y) ∧
    (∀ x x', S x → S x' → f x = f x' → x = x')

/-- An isomorphism of categories: a functor with a strict two-sided inverse on objects. -/
def IsoOfCats (F : Functor 𝒞 𝒟) : Prop :=
  ∃ (G : Functor 𝒟 𝒞),
    (∀ X : 𝒞, G.obj (F.obj X) = X) ∧ (∀ Y : 𝒟, F.obj (G.obj Y) = Y)

/-- §1.341. If F : 𝒞 → 𝒟 is an equivalence functor and for every A the iso-class of A in 𝒞
    is equinumerous with the iso-class of FA in 𝒟, then (by the axiom of choice) F is
    conjugate (NatIso) to an isomorphism of categories. -/
theorem equiv_functor_conjugate_to_iso (F : Functor 𝒞 𝒟)
    (hEq : EquivalenceFunctor F)
    (hEnum : ∀ A : 𝒞, CrossEquinumerous (isoClass A) (@isoClass 𝒟 _ (F.obj A))) :
    ∃ (G : Functor 𝒞 𝒟), Nonempty (NatIso F G) ∧ IsoOfCats G := by
  -- Extract per-iso-class bijection properties.
  -- φ A := Classical.choose (hEnum A) : 𝒞 → 𝒟  is the chosen bijection for isoClass A.
  -- By propext: when A ≅ B, isoClass A = isoClass B and isoClass (F A) = isoClass (F B),
  -- so hEnum A and hEnum B are proofs of the SAME Prop, hence φ A = φ B.
  -- This consistency is what makes G (defined as φ A A) a strict bijection.
  have φ_maps : ∀ A x, isoClass A x → @isoClass 𝒟 _ (F.obj A) (Classical.choose (hEnum A) x) :=
    fun A => (Classical.choose_spec (hEnum A)).1
  have φ_surj : ∀ A y, @isoClass 𝒟 _ (F.obj A) y →
      ∃ x, isoClass A x ∧ Classical.choose (hEnum A) x = y :=
    fun A => (Classical.choose_spec (hEnum A)).2.1
  have φ_inj : ∀ A x x', isoClass A x → isoClass A x' →
      Classical.choose (hEnum A) x = Classical.choose (hEnum A) x' → x = x' :=
    fun A => (Classical.choose_spec (hEnum A)).2.2
  -- G on objects: G A = (chosen bijection for isoClass A) applied to A
  -- Since A ∈ isoClass A (reflexivity), G A ∈ isoClass (F A).
  let G : 𝒞 → 𝒟 := fun A => Classical.choose (hEnum A) A
  -- Key property: G A ∈ isoClass (F A), i.e., F A ≅ G A
  have G_in_class : ∀ A : 𝒞, @isoClass 𝒟 _ (F.obj A) (G A) :=
    fun A => φ_maps A A (isomorphic_refl A)
  -- Key lemma: when A ≅ B, the chosen bijections are equal (by propext).
  have isoClass_eq : ∀ {A B : 𝒞}, Isomorphic A B →
      isoClass A = isoClass B := by
    intro A B hAB
    funext C; simp only [isoClass]
    exact propext ⟨isomorphic_trans (isomorphic_symm hAB), isomorphic_trans hAB⟩
  have isoClass_FA_eq : ∀ {A B : 𝒞}, Isomorphic A B →
      @isoClass 𝒟 _ (F.obj A) = @isoClass 𝒟 _ (F.obj B) := by
    intro A B hAB
    funext D; simp only [isoClass]
    exact propext ⟨isomorphic_trans (isomorphic_symm (functor_preserves_iso_obj F hAB)),
                   isomorphic_trans (functor_preserves_iso_obj F hAB)⟩
  have φ_consistent : ∀ {A B : 𝒞}, Isomorphic A B →
      Classical.choose (hEnum A) = Classical.choose (hEnum B) := by
    intro A B hAB
    congr 1
    rw [isoClass_eq hAB, isoClass_FA_eq hAB]
  -- G is injective: G A = G B implies A = B.
  -- Proof: G A = G B means φ_A A = φ_B B.
  -- Case 1: A ≅ B. Then φ_A = φ_B (by φ_consistent), so φ_A A = φ_A B.
  --         By injectivity of φ_A on isoClass A (and B ∈ isoClass A), A = B.
  -- Case 2: A ≇ B. Then isoClass (F A) ∩ isoClass (F B) = ∅ (F reflects and preserves iso).
  --         But φ_A A ∈ isoClass (F A) and φ_B B ∈ isoClass (F B), contradiction.
  have G_inj : ∀ {A B : 𝒞}, G A = G B → A = B := by
    intro A B hGAB
    -- hGAB : G A = G B, i.e., Classical.choose (hEnum A) A = Classical.choose (hEnum B) B
    -- G A ∈ isoClass (F A) and G B ∈ isoClass (F B)
    have hGA : @isoClass 𝒟 _ (F.obj A) (G A) := G_in_class A
    have hGB : @isoClass 𝒟 _ (F.obj B) (G B) := G_in_class B
    -- G A = G B means isoClass (F A) and isoClass (F B) overlap at G A = G B
    -- Hence F A ≅ F B (since G A ∈ both iso-classes)
    have hFAFB : Isomorphic (F.obj A) (F.obj B) := by
      rw [← hGAB] at hGB
      -- hGA : F A ≅ G A,  hGB (after rw) : F B ≅ G A
      -- F A ≅ G A ≅ F B (via sym hGB)
      exact isomorphic_trans hGA (isomorphic_symm hGB)
    -- F reflects isomorphism (F is full embedding): A ≅ B
    have hAB : Isomorphic A B :=
      full_embedding_reflects_iso_obj F hEq.1 hEq.2.1 hFAFB
    -- Now use φ_consistent: φ_A = φ_B
    have φ_eq : Classical.choose (hEnum A) = Classical.choose (hEnum B) := φ_consistent hAB
    -- B ∈ isoClass A (since A ≅ B)
    have hB_in_A : isoClass A B := hAB
    -- φ_A A = φ_A B (from hGAB and φ_eq)
    have : Classical.choose (hEnum A) A = Classical.choose (hEnum A) B :=
      hGAB.trans (show Classical.choose (hEnum B) B = Classical.choose (hEnum A) B by
        rw [φ_eq])
    -- By injectivity of φ_A on isoClass A:
    exact φ_inj A A B (isomorphic_refl A) hB_in_A this
  -- G is surjective: for every D : 𝒟, ∃ A with G A = D.
  -- Proof: by HasRepresentativeImage, ∃ A with F A ≅ D (D ∈ isoClass (F A)).
  --        By surjectivity of φ_A, ∃ x ∈ isoClass A with φ_A x = D.
  --        Since x ≅ A, φ_consistent gives φ_x = φ_A, so G x = φ_x x = φ_A x = D.
  have G_surj : ∀ D : 𝒟, ∃ A : 𝒞, G A = D := by
    intro D
    -- get A with F A ≅ D
    obtain ⟨A, hD, hiso⟩ := hEq.2.2 D
    -- hiso : IsIso hD where hD : F A ⟶ D
    -- so D ∈ isoClass (F A)
    have hD_in_FA : @isoClass 𝒟 _ (F.obj A) D := ⟨hD, hiso⟩
    -- by surjectivity of φ_A: ∃ x ∈ isoClass A with φ_A x = D
    obtain ⟨x, hx_class, hx_eq⟩ := φ_surj A D hD_in_FA
    -- x ≅ A, so φ_x = φ_A
    have φ_x_eq : Classical.choose (hEnum x) = Classical.choose (hEnum A) :=
      φ_consistent (isomorphic_symm hx_class)
    -- G x = φ_x x = φ_A x = D
    exact ⟨x, by simp only [G]; rw [φ_x_eq]; exact hx_eq⟩
  -- Extract iso morphisms α A : F A → G A and their inverses
  have h_iso : ∀ A : 𝒞, ∃ (h : F.obj A ⟶ G A), IsIso h := fun A => G_in_class A
  let α : ∀ A : 𝒞, F.obj A ⟶ G A := fun A => Classical.choose (h_iso A)
  have α_iso : ∀ A, IsIso (α A) := fun A => Classical.choose_spec (h_iso A)
  have α_inv_def : ∀ A : 𝒞, ∃ (g : G A ⟶ F.obj A),
      α A ≫ g = Cat.id (F.obj A) ∧ g ≫ α A = Cat.id (G A) := fun A => α_iso A
  let α_inv : ∀ A : 𝒞, G A ⟶ F.obj A := fun A => Classical.choose (α_inv_def A)
  have α_inv_spec : ∀ A, α A ≫ α_inv A = Cat.id (F.obj A) ∧ α_inv A ≫ α A = Cat.id (G A) :=
    fun A => Classical.choose_spec (α_inv_def A)
  -- G on morphisms: Gfun.map f = α_inv A ≫ F.map f ≫ α B (conjugation by the iso)
  have G_map_id : ∀ A, α_inv A ≫ F.map (Cat.id A) ≫ α A = Cat.id (G A) := by
    intro A; rw [F.map_id, Cat.id_comp]; exact (α_inv_spec A).2
  have G_map_comp : ∀ {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C),
      α_inv A ≫ F.map (f ≫ g) ≫ α C =
        (α_inv A ≫ F.map f ≫ α B) ≫ (α_inv B ≫ F.map g ≫ α C) := by
    intro A B C f g
    rw [F.map_comp]
    have key : F.map f ≫ F.map g = F.map f ≫ (α B ≫ α_inv B) ≫ F.map g := by
      rw [(α_inv_spec B).1, Cat.id_comp]
    rw [key]; simp [Cat.assoc]
  let Gfun : Functor 𝒞 𝒟 := {
    obj := G
    map := fun {A B} f => α_inv A ≫ F.map f ≫ α B
    map_id := fun A => G_map_id A
    map_comp := fun f g => G_map_comp f g
  }
  -- NatIso F Gfun: α is natural (F.map f ≫ α B = α A ≫ Gfun.map f)
  have nat_α : ∀ {A B : 𝒞} (f : A ⟶ B),
      F.map f ≫ α B = α A ≫ (α_inv A ≫ F.map f ≫ α B) := by
    intro A B f; rw [← Cat.assoc, ← Cat.assoc, (α_inv_spec A).1, Cat.id_comp]
  let natTrans_FG : NaturalTransformation F Gfun := { app := α, naturality := fun f => nat_α f }
  have natIso_FG : NatIso F Gfun := { nat := natTrans_FG, isIso := α_iso }
  -- IsoOfCats Gfun: build strict inverse H using surjectivity of G.
  -- H D := Classical.choose (G_surj D) — the unique A with G A = D.
  let H : 𝒟 → 𝒞 := fun D => Classical.choose (G_surj D)
  have H_spec : ∀ D, G (H D) = D := fun D => Classical.choose_spec (G_surj D)
  -- G is a full functor (since NatIso F Gfun and F is full).
  have hG_full : Full Gfun := full_of_natIso natIso_FG hEq.2.1
  -- G is an embedding (since NatIso F Gfun and F is embedding).
  have hG_emb : Embedding Gfun := embedding_of_natIso natIso_FG hEq.1
  -- H is a functor via G's fullness.
  -- For h : D ⟶ D', lift to f : H D ⟶ H D' by applying G-fullness to
  -- the cast of h : G(H D) ⟶ G(H D') via H_spec transports.
  let cast_hom : ∀ {D D' : 𝒟}, (D ⟶ D') → (G (H D) ⟶ G (H D')) :=
    fun {D D'} h => (H_spec D).symm ▸ (H_spec D').symm ▸ h
  have H_map_def : ∀ {D D' : 𝒟} (h : D ⟶ D'), ∃ (f : H D ⟶ H D'),
      Gfun.map f = cast_hom h :=
    fun h => hG_full (cast_hom h)
  let H_map : ∀ {D D' : 𝒟}, (D ⟶ D') → (H D ⟶ H D') :=
    fun h => Classical.choose (H_map_def h)
  have H_map_spec : ∀ {D D' : 𝒟} (h : D ⟶ D'), Gfun.map (H_map h) = cast_hom h :=
    fun h => Classical.choose_spec (H_map_def h)
  -- cast_hom (Cat.id D) = Cat.id (G (H D)):
  have cast_id : ∀ D : 𝒟, cast_hom (Cat.id D) = Cat.id (G (H D)) := by
    intro D; simp only [cast_hom]
    exact Eq.rec (Eq.rec rfl (H_spec D).symm) (H_spec D).symm
  have cast_comp : ∀ {D D' D'' : 𝒟} (h : D ⟶ D') (k : D' ⟶ D''),
      cast_hom (h ≫ k) = cast_hom h ≫ cast_hom k := by
    intro D D' D'' h k; simp only [cast_hom]
    exact Eq.rec (Eq.rec (Eq.rec rfl (H_spec D'').symm) (H_spec D').symm) (H_spec D).symm
  have H_map_id : ∀ D : 𝒟, H_map (Cat.id D) = Cat.id (H D) := by
    intro D; apply hG_emb; rw [H_map_spec, cast_id, Gfun.map_id]
  have H_map_comp : ∀ {D D' D'' : 𝒟} (h : D ⟶ D') (k : D' ⟶ D''),
      H_map (h ≫ k) = H_map h ≫ H_map k := by
    intro D D' D'' h k; apply hG_emb
    rw [H_map_spec, cast_comp, Gfun.map_comp, H_map_spec, H_map_spec]
  let Hfun : Functor 𝒟 𝒞 := {
    obj := H
    map := fun {D D'} h => H_map h
    map_id := H_map_id
    map_comp := H_map_comp
  }
  -- Assemble IsoOfCats Gfun
  refine ⟨Gfun, ⟨natIso_FG⟩, Hfun, ?_, ?_⟩
  · intro X; apply G_inj; exact H_spec (G X)    -- H (G X) = X
  · exact H_spec                                  -- G (H Y) = Y

end Freyd
