module

public import Freyd.S2_50

universe v₁ v₂ u₁ u₂

/-
  Freyd & Scedrov, *Categories and Allegories* §2.51

  The quotient representation `quotRep : 𝒜 → 𝒜/C` (S2_5_QuotAllegory) preserves
  the "graph-of-a-function" properties:

      "The equivalence class of an ENTIRE (resp. SIMPLE, TABULAR) morphism is
       such (in the quotient allegory).  The equivalence class of a (partial)
       UNIT is a (partial) unit."

  Every one of these is order- and operation-defined, and `quotRep` is an
  `AllegoryFunctor`, so it preserves `≫`, `°`, `∩`, `id` and — derived from
  `map_inter` — the allegory order `⊑` (since `R ⊑ S` means `R ∩ S = R`).
  Therefore the ENTIRE/SIMPLE/MAP/TABULAR facts hold for ANY allegory functor;
  we prove them at that generality (`AllegoryFunctor.preserves_*`) and read off
  the `quotRep` corollaries.

  The (partial) UNIT facts additionally need that `quotRep` is SURJECTIVE on
  homs (every class has a representative) — `PartialUnit T` quantifies over *all*
  endomorphisms of `T` in the quotient, and each is `[R]` for some `R` in `𝒜`.
  That surjectivity is `Quotient.inductionOn`, so these two are proved for
  `quotRep` specifically.
-/



namespace Freyd.Alg

/-! ## §2.51  Any allegory functor preserves order, entire, simple, map, tabular

  These hold for every `AllegoryFunctor` because each property is built from
  `≫`, `°`, `∩`, `id` and the order `⊑`, all of which a functor preserves. -/

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- §2.51  The equivalence class (image under any allegory functor) of an ENTIRE
    morphism is entire.  `Entire R : dom R = 1`, i.e. `1 ∩ R≫R° = 1`; apply `F`
    and push it through `map_inter`/`map_comp`/`map_recip`/`map_id`. -/
public theorem AllegoryFunctor.preserves_entire (F : AllegoryFunctor 𝒜 ℬ) {a b : 𝒜}
    {R : a ⟶ b} (h : Entire R) : Entire (F.map R) := by
  have h' : Cat.id a ∩ R ≫ R° = Cat.id a := h
  show Cat.id (F.obj a) ∩ F.map R ≫ (F.map R)° = Cat.id (F.obj a)
  rw [← F.map_recip, ← F.map_comp, ← F.map_id a, ← F.map_inter, h']

/-- §2.51  The image of a SIMPLE morphism is simple.  `Simple R : R°≫R ⊑ 1`;
    apply `F.mono` and rewrite `map_comp`/`map_recip`/`map_id`. -/
public theorem AllegoryFunctor.preserves_simple (F : AllegoryFunctor 𝒜 ℬ) {a b : 𝒜}
    {R : a ⟶ b} (h : Simple R) : Simple (F.map R) := by
  have hmono := F.mono h
  rwa [F.map_comp, F.map_recip, F.map_id] at hmono

/-- §2.51  The image of a MAP (entire ∧ simple) is a map. -/
public theorem AllegoryFunctor.preserves_map (F : AllegoryFunctor 𝒜 ℬ) {a b : 𝒜}
    {R : a ⟶ b} (h : Map R) : Map (F.map R) :=
  ⟨F.preserves_entire h.1, F.preserves_simple h.2⟩

/-- §2.51  A tabulating pair pushes through `F`: if `(f, g)` tabulates `R` then
    `(F f, F g)` tabulates `F R` — the legs stay maps (`preserves_map`) and the
    two tabulation equations are preserved by `map_comp`/`map_recip`/`map_inter`. -/
public theorem AllegoryFunctor.preserves_tabulates (F : AllegoryFunctor 𝒜 ℬ)
    {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b} (h : Tabulates f g R) :
    Tabulates (F.map f) (F.map g) (F.map R) := by
  obtain ⟨hf, hg, hR, hcanc⟩ := h
  refine ⟨F.preserves_map hf, F.preserves_map hg, ?_, ?_⟩
  · -- F R = (F f)° ≫ F g
    rw [hR, F.map_comp, F.map_recip]
  · -- F f ≫ (F f)° ∩ F g ≫ (F g)° = 1
    have hc := congrArg F.map hcanc
    rwa [F.map_inter, F.map_comp, F.map_comp, F.map_recip, F.map_recip, F.map_id] at hc

/-- §2.51  The image of a TABULAR morphism is tabular. -/
public theorem AllegoryFunctor.preserves_tabular (F : AllegoryFunctor 𝒜 ℬ) {a b : 𝒜}
    {R : a ⟶ b} (h : Tabular R) : Tabular (F.map R) := by
  obtain ⟨c, f, g, ht⟩ := h
  exact ⟨F.obj c, F.map f, F.map g, F.preserves_tabulates ht⟩

/-! ## §2.51  The quotient representation `R ↦ [R]` preserves these

  Corollaries of the generic facts above for `F = quotRep C`. -/

variable {𝒜' : Type u₁} [Allegory.{v₁} 𝒜'] (C : Congruence 𝒜')

/-- §2.51  The equivalence class of an ENTIRE morphism is entire. -/
public theorem quotRep_preserves_entire {a b : 𝒜'} {R : a ⟶ b} (h : Entire R) :
    Entire ((quotRep C).map R) := (quotRep C).preserves_entire h

/-- §2.51  The equivalence class of a SIMPLE morphism is simple. -/
theorem quotRep_preserves_simple {a b : 𝒜'} {R : a ⟶ b} (h : Simple R) :
    Simple ((quotRep C).map R) := (quotRep C).preserves_simple h

/-- §2.51  The equivalence class of a MAP is a map. -/
public theorem quotRep_preserves_map {a b : 𝒜'} {R : a ⟶ b} (h : Map R) :
    Map ((quotRep C).map R) := (quotRep C).preserves_map h

/-- §2.51  The equivalence class of a TABULAR morphism is tabular. -/
public theorem quotRep_preserves_tabular {a b : 𝒜'} {R : a ⟶ b} (h : Tabular R) :
    Tabular ((quotRep C).map R) := (quotRep C).preserves_tabular h

/-! ## §2.51  (Partial) units

  `PartialUnit T` says `1_T` is the maximum endomorphism of `T`.  In the
  quotient every endomorphism of `[T]` is `[R]` (`Quotient.inductionOn`), and
  `R ⊑ 1_T ⟹ [R] ⊑ [1_T] = 1_[T]` by `quotRep_mono` + `map_id`. -/

/-- §2.51  The equivalence class of a PARTIAL UNIT is a partial unit:
    `quotRep` is identity on objects, so we must show every endomorphism `S` of
    `[T] = T` in the quotient lies below `1`; `S = [R]` and `R ⊑ 1_T`. -/
theorem quotRep_preserves_partialUnit {T : 𝒜'} (h : PartialUnit T) :
    PartialUnit ((quotRep C).obj T) := by
  intro S
  refine Quotient.inductionOn S (fun R => ?_)
  have hmono := quotRep_mono C (h R)
  rwa [(quotRep C).map_id] at hmono

/-- §2.51  The equivalence class of a UNIT is a unit: partial-unit part from
    `quotRep_preserves_partialUnit`; every object `a` still receives an entire
    `[R] : a → [T]` because `R : a → T` is entire and `quotRep` preserves entire. -/
theorem quotRep_preserves_unit {T : 𝒜'} (h : IsUnit T) :
    IsUnit ((quotRep C).obj T) := by
  obtain ⟨hPU, hEnt⟩ := h
  refine ⟨quotRep_preserves_partialUnit C hPU, ?_⟩
  intro a
  obtain ⟨R, hR⟩ := hEnt a
  exact ⟨(quotRep C).map R, quotRep_preserves_entire C hR⟩

end Freyd.Alg
