/-
  Bird & de Moor, *Algebra of Programming* §5.7  Lax natural transformations.

  Composition throughout is diagram order (`≫`); B&dM's `FR·φ ⊇ φ·GR` (with `φ : FA ← GA`)
  is mirrored to `G.map R ≫ φ b ⊑ φ a ≫ F.map R`.

  Lemma 5.1 (a relator preserves maps and their converses) comes from `AOP.A5_1`
  (`Relator.map_is_map` / `Relator.map_recip_map`).
-/

module

public import AOP.A5_1
public import AOP.A5_2
public import AOP.A5_3
public import AOP.A5_4

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Freyd.Alg

/-! ## §5.7 example (B&dM p.133): `∈` is lax natural from the power relator to the identity

  `powerRel_eps_lax` (`AOP.A5_4`) is LITERALLY the defining inequality of `LaxNatural` with
  `G` the power relator (object map `PowerAllegory.powerObj`, hom map `powerRel`), `F` the
  identity relator, and `φ := ∋`.  The power relator is not bundled as a `Relator` here — its
  `map_comp` field needs the STRONGER `TabularUnitaryUnguardedPowerAllegory` hypothesis of
  `powerRel_comp`, more than this bare-`UnguardedPowerAllegory` section carries — so the
  example is stated as the raw inequality, with `Relator.idRelator`'s `map` unfolding to `id`
  on the nose.  (Under that stronger class it IS bundled: `powerRelator`, AOP.A5_4.) -/

section EpsExample

variable {𝒜 : Type u₁} [UnguardedPowerAllegory 𝒜]

/-- **B&dM p.133**: membership `∋` is lax natural from the power relator to the identity
    relator. -/
theorem eps_lax_natural {A B : 𝒜} (R : A ⟶ B) :
    powerRel R ≫ ∋ B ⊑ ∋ A ≫ (Relator.idRelator 𝒜).map R :=
  powerRel_eps_lax R

end EpsExample

/-! ## §5.7 Theorem 5.2: lax naturality is equivalent to strict naturality on maps -/

section Theorem52

variable {𝒜 : Type u₁} {ℬ : Type u₂} [TabularAllegory 𝒜] [Allegory.{v₂} ℬ]
  (F G : Relator 𝒜 ℬ) (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A)

/-- **B&dM Theorem 5.2**: `φ` is lax natural from `G` to `F` iff it is STRICTLY natural on
    every map `f`. -/
public theorem laxNatural_iff_strict_on_maps :
    LaxNatural F G φ ↔ ∀ {A B : 𝒜} (f : A ⟶ B), Map f → G.map f ≫ φ B = φ A ≫ F.map f := by
  constructor
  · intro hlax A B f hf
    have hFf : Map (F.map f) := F.map_is_map hf
    have hGf : Map (G.map f) := G.map_is_map hf
    have hFfrecip : F.map f° = (F.map f)° := F.map_recip_map hf
    have hGfrecip : G.map f° = (G.map f)° := G.map_recip_map hf
    have hle1 : G.map f ≫ φ B ⊑ φ A ≫ F.map f := hlax f
    have hle2 : G.map f° ≫ φ A ⊑ φ B ≫ F.map f° := hlax f°
    rw [hGfrecip, hFfrecip] at hle2
    have hle2a : φ A ⊑ G.map f ≫ (φ B ≫ (F.map f)°) := (map_shunt_left hGf _ _).mp hle2
    have hle2b : φ A ⊑ (G.map f ≫ φ B) ≫ (F.map f)° := by rw [Cat.assoc]; exact hle2a
    have hle2' : φ A ≫ F.map f ⊑ G.map f ≫ φ B := (map_shunt_right hFf _ _).mpr hle2b
    exact le_antisymm hle1 hle2'
  · intro hstrict A B R
    obtain ⟨C, h, k, hh, hk, hR, _⟩ := TabularAllegory.tabular (𝒜 := 𝒜) R
    have hFhmap : Map (F.map h) := F.map_is_map hh
    have hGhmap : Map (G.map h) := G.map_is_map hh
    have hFhrecip : F.map h° = (F.map h)° := F.map_recip_map hh
    have hGhrecip : G.map h° = (G.map h)° := G.map_recip_map hh
    have hstep_h : (G.map h)° ≫ φ C ⊑ φ A ≫ (F.map h)° := by
      have he : G.map h ≫ φ A = φ C ≫ F.map h := hstrict h hh
      apply (map_shunt_left hGhmap _ _).mpr
      have hent : Cat.id (F.obj C) ⊑ F.map h ≫ (F.map h)° := entire_id_le hFhmap.1
      calc φ C = φ C ≫ Cat.id (F.obj C) := (Cat.comp_id _).symm
        _ ⊑ φ C ≫ (F.map h ≫ (F.map h)°) := comp_mono_left _ hent
        _ = (φ C ≫ F.map h) ≫ (F.map h)° := (Cat.assoc _ _ _).symm
        _ = (G.map h ≫ φ A) ≫ (F.map h)° := by rw [he]
        _ = G.map h ≫ (φ A ≫ (F.map h)°) := Cat.assoc _ _ _
    have hFcomp : F.map (h° ≫ k) = (F.map h)° ≫ F.map k := by rw [F.map_comp, hFhrecip]
    have p1 : G.map R ≫ φ B = ((G.map h)° ≫ φ C) ≫ F.map k := by
      calc G.map R ≫ φ B
          = G.map (h° ≫ k) ≫ φ B := by rw [hR]
        _ = (G.map h° ≫ G.map k) ≫ φ B := by rw [G.map_comp]
        _ = ((G.map h)° ≫ G.map k) ≫ φ B := by rw [hGhrecip]
        _ = (G.map h)° ≫ (G.map k ≫ φ B) := Cat.assoc _ _ _
        _ = (G.map h)° ≫ (φ C ≫ F.map k) := by rw [hstrict k hk]
        _ = ((G.map h)° ≫ φ C) ≫ F.map k := (Cat.assoc _ _ _).symm
    have p2 : ((G.map h)° ≫ φ C) ≫ F.map k ⊑ φ A ≫ F.map R := by
      calc ((G.map h)° ≫ φ C) ≫ F.map k
          ⊑ (φ A ≫ (F.map h)°) ≫ F.map k := comp_mono_right hstep_h _
        _ = φ A ≫ ((F.map h)° ≫ F.map k) := Cat.assoc _ _ _
        _ = φ A ≫ F.map (h° ≫ k) := by rw [hFcomp]
        _ = φ A ≫ F.map R := by rw [← hR]
    rw [p1]; exact p2

end Theorem52

/-! ## LAX SQUARES and how they paste

  A LAX SQUARE `Ta ≫ X ⊑ X' ≫ Tb` slides the left edge `Ta` across to the right edge `Tb`,
  turning the top arrow `X` into the bottom one `X'`.  The rules below paste squares along `≫`
  (`comp_slides`) and along `∪` (`union_slides`); `Relator.map_slides` (A5_1) pushes one through
  a relator, and `pair_slides` / `junc_slides` further down paste along `⟨,⟩` and `▽`.  B&dM
  §7.2 builds its algebras from these.

  Each rule has TWO readings, differing only in what is substituted for the edges:

  * MONOTONICITY of a relation — `X' = X`, `Ta`, `Tb` endo: `X` slides its source order past
    itself to the target order.
  * LAX NATURALITY of a whole family — `Ta, Tb := G(R), F(R)` and `X, X' := φ b, φ a`, then
    quantified over every `R`.

  So there is one law per operation, not two.  The `∀ R` is the only difference, and it is
  outside the law. -/

section CompSlides

variable {𝒜 : Type u₁} [Allegory.{v₁} 𝒜]

/-- **B&dM §5.7**: lax squares paste along `≫`.  Sharing the edge `Tb`, `Ta ≫ X ⊑ X' ≫ Tb` and
    `Tb ≫ Y ⊑ Y' ≫ Tc` give one square from `Ta` to `Tc` with `X ≫ Y` on top and `X' ≫ Y'`
    below.  Read with `X = X'`, `Y = Y'` it says a composite of monotone relations is monotone;
    read at `Ta, Tb, Tc := H(R), G(R), F(R)` with `X, X' := ψ b, ψ a` and `Y, Y' := φ b, φ a` it
    is the vertical composite of two lax natural transformations, at `R`. -/
public theorem comp_slides {a₁ a₂ b₁ b₂ c₁ c₂ : 𝒜} {Ta : a₁ ⟶ a₂} {Tb : b₁ ⟶ b₂} {Tc : c₁ ⟶ c₂}
    {X : a₂ ⟶ b₂} {X' : a₁ ⟶ b₁} {Y : b₂ ⟶ c₂} {Y' : b₁ ⟶ c₁}
    (hX : Ta ≫ X ⊑ X' ≫ Tb) (hY : Tb ≫ Y ⊑ Y' ≫ Tc) :
    Ta ≫ (X ≫ Y) ⊑ (X' ≫ Y') ≫ Tc :=
  calc Ta ≫ (X ≫ Y) = (Ta ≫ X) ≫ Y := (Cat.assoc _ _ _).symm
    _ ⊑ (X' ≫ Tb) ≫ Y := comp_mono_right hX Y
    _ = X' ≫ (Tb ≫ Y) := Cat.assoc _ _ _
    _ ⊑ X' ≫ (Y' ≫ Tc) := comp_mono_left X' hY
    _ = (X' ≫ Y') ≫ Tc := (Cat.assoc _ _ _).symm

example {A : 𝒜} {T : A ⟶ A} {R S : A ⟶ A} (hR : T ≫ R ⊑ R ≫ T) (hS : T ≫ S ⊑ S ≫ T) :
    T ≫ (R ≫ S) ⊑ (R ≫ S) ≫ T := comp_slides hR hS

end CompSlides

/-! ## Sliding past a union -/

section UnionSlides

-- Needs the distributive layer: `∪` and composition's distribution over it on BOTH sides.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

/-- Lax squares paste along `∪`: two squares with the SAME two edges `Ta`, `Tb` give one with
    `X ∪ Y` on top and `X' ∪ Y'` below.  The INTERSECTION case is FALSE: after
    `Ta ≫ (X ∩ Y) ⊑ (X' ≫ Tb) ∩ (Y' ≫ Tb)` the last step would need
    `(X' ≫ Tb) ∩ (Y' ≫ Tb) ⊑ (X' ∩ Y') ≫ Tb`, the wrong direction of semi-distributivity —
    refuted in both readings, by `inter_not_monotonic` and `laxNatural_inter_false`
    (A6_1_OrdRelSet). -/
public theorem union_slides {a₁ a₂ b₁ b₂ : 𝒜} {Ta : a₁ ⟶ a₂} {Tb : b₁ ⟶ b₂} {X Y : a₂ ⟶ b₂}
    {X' Y' : a₁ ⟶ b₁} (hX : Ta ≫ X ⊑ X' ≫ Tb) (hY : Ta ≫ Y ⊑ Y' ≫ Tb) :
    Ta ≫ (X ∪ Y) ⊑ (X' ∪ Y') ≫ Tb :=
  calc Ta ≫ (X ∪ Y) = (Ta ≫ X) ∪ (Ta ≫ Y) := DistributiveAllegory.comp_union_distrib Ta X Y
    _ ⊑ (X' ≫ Tb) ∪ (Y' ≫ Tb) := union_mono hX hY
    _ = (X' ∪ Y') ≫ Tb := (union_comp_distrib X' Y' Tb).symm

end UnionSlides

/-! ## What is left over for a WHOLE lax natural transformation

  `LaxNatural F G φ` is one lax square per arrow `R`, with the edges `G(R)`, `F(R)` and the two
  arrows `φ b`, `φ a`.  So the closure rules of the previous sections ARE the closure rules of
  lax natural transformations: `fun R => comp_slides (hψ R) (hφ R)` is vertical composition,
  `fun R => union_slides (hφ R) (hψ R)` is union, `fun R => K.map_slides (hφ R)` is a relator
  applied on the outside.  Each is one term, so none of them gets a theorem of its own; they are
  written at the call sites (`laxNaturalCat`, `relatorSum_product`, and the two horizontal
  composites below).

  What DOES need a theorem here is what the pasting rules do not give: reindexing along a relator
  on the INSIDE, the two ways of composing HORIZONTALLY, and the interchange between the two
  kinds of composition. -/

section LaxNaturalClosure

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- A relator on the INSIDE reindexes a lax natural transformation along its object map:
    `φ ∘ K : G ∘ K ⟶ F ∘ K`, with `K` running first.  Free — the new inequation at `R` is
    `φ`'s own at `K.map R`, nothing is composed onto either side. -/
public theorem laxNatural_inside {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (K : Relator 𝒞 𝒜) (h : LaxNatural F G φ) :
    LaxNatural (Relator.comp K F) (Relator.comp K G) (fun C => φ (K.obj C)) :=
  fun {_ _} R => h (K.map R)

/-- A relator on the OUTSIDE carries a lax natural transformation to a lax natural one:
    `K ∘ φ : K ∘ G ⟶ K ∘ F`, with `K` running last.  `map_mono` on `φ`'s own inequation at `R`,
    read through `map_comp` on both sides — `Relator.map_slides` at `Ta, Tb := G.map R, F.map R`
    and `X, X' := φ b, φ a`. -/
public theorem laxNatural_outside {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (K : Relator ℬ 𝒞) (h : LaxNatural F G φ) :
    LaxNatural (Relator.comp F K) (Relator.comp G K) (fun A => K.map (φ A)) :=
  fun {_ _} R => K.map_slides (h R)


/-! ### HORIZONTAL composition is TWO operations, not one

  `φ : G ⟶ F` between `𝒜` and `ℬ` and `χ : L ⟶ K` between `ℬ` and `𝒞` compose to
  `L ∘ G ⟶ K ∘ F` in two ways, according to which of the two 2-cells is crossed FIRST.  Each
  pastes, at every `R`, the reindexed square `laxNatural_inside` supplies with the one
  `Relator.map_slides` supplies — in the two possible orders.  Neither one-sided case is an
  instance of either: the outside one would need `𝟙 ≫ K.map (φ a) = K.map (φ a)` and
  `laxNatural_inside` would need `φ (K.obj c) ≫ F.map (𝟙 _) = φ (K.obj c)`, rewrites, not
  definitional unfoldings. -/

/-- HORIZONTAL composition with the OUTER 2-cell first: `χ` reindexed along `G` on the inside,
    then `K` applied to `φ` on the outside. -/
public theorem laxNatural_hcomp_outer_first {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {K L : Relator ℬ 𝒞} {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} {χ : ∀ B : ℬ, L.obj B ⟶ K.obj B}
    (hχ : LaxNatural K L χ) (hφ : LaxNatural F G φ) :
    LaxNatural (Relator.comp F K) (Relator.comp G L) (fun A => χ (G.obj A) ≫ K.map (φ A)) :=
  fun {_ _} R => comp_slides (laxNatural_inside G hχ R) (K.map_slides (hφ R))

/-- HORIZONTAL composition with the INNER 2-cell first: `L` applied to `φ` on the outside, then
    `χ` reindexed along `F` on the inside.  Same source, same target, same type as
    `laxNatural_hcomp_outer_first` — and a DIFFERENT family, below it by `hχ (φ a)`. -/
public theorem laxNatural_hcomp_inner_first {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {K L : Relator ℬ 𝒞} {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} {χ : ∀ B : ℬ, L.obj B ⟶ K.obj B}
    (hχ : LaxNatural K L χ) (hφ : LaxNatural F G φ) :
    LaxNatural (Relator.comp F K) (Relator.comp G L) (fun A => L.map (φ A) ≫ χ (F.obj A)) :=
  fun {_ _} R => comp_slides (L.map_slides (hφ R)) (laxNatural_inside F hχ R)

-- The two horizontal composites are ORDERED, inner-first below outer-first, and the ordering IS
-- `χ`'s own defining inequation read at the arrow `φ a`: it gets no theorem of its own.
example {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ} {K L : Relator ℬ 𝒞}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} {χ : ∀ B : ℬ, L.obj B ⟶ K.obj B} (hχ : LaxNatural K L χ)
    (A : 𝒜) : L.map (φ A) ≫ χ (F.obj A) ⊑ χ (G.obj A) ≫ K.map (φ A) := hχ (φ A)

/-- STRICTLY natural: the `LaxNatural` inequation as an EQUALITY at EVERY arrow, not only at the
    maps, where Theorem 5.2 gives it for free. -/
@[expose] public def StrictNatural (F G : Relator 𝒜 ℬ) (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A) : Prop :=
  ∀ {A B : 𝒜} (R : A ⟶ B), G.map R ≫ φ B = φ A ≫ F.map R

/-- THE IDENTITY 2-CELL: `𝟙` at every object is strictly natural, `F(R) ≫ 𝟙 = F(R) = 𝟙 ≫ F(R)`.
    The identity of `laxNaturalCat` below, and the factor a compound family carries wherever one
    side of a product is left alone — `φ×𝟙` closes through `strictNatural_prod` only if `𝟙` has a
    square of its own. -/
public theorem strictNatural_id (F : Relator 𝒜 ℬ) : StrictNatural F F (fun A => 𝟙 (F.obj A)) :=
  fun {_ _} R => by rw [Cat.comp_id, Cat.id_comp]

/-- A relator on the INSIDE reindexes a STRICTLY natural family along its object map, the twin of
    `laxNatural_inside`: the new equation at `R` is `φ`'s own at `K.map R`, so it is as free as the
    lax one and needs none of `strictNatural_outside`'s `congrArg`. -/
public theorem strictNatural_inside {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (K : Relator 𝒞 𝒜) (h : StrictNatural F G φ) :
    StrictNatural (Relator.comp K F) (Relator.comp K G) (fun C => φ (K.obj C)) :=
  fun {_ _} R => h (K.map R)

/-- A relator on the OUTSIDE carries a STRICTLY natural family to a strictly natural one, which
    `Relator.map_slides` cannot give: the equality is carried by `congrArg` and then split by
    `map_comp`, where the lax version has only monotonicity.  The twin of `laxNatural_outside`,
    which is stated with the rest of the lax closure above. -/
public theorem strictNatural_outside {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (K : Relator ℬ 𝒞) (h : StrictNatural F G φ) :
    StrictNatural (Relator.comp F K) (Relator.comp G K) (fun A => K.map (φ A)) := by
  intro A B R
  have := congrArg K.map (h R)
  rwa [K.map_comp, K.map_comp] at this

/-- Every strictly natural family is lax natural: the inequation at `R` is its own equality. -/
public theorem laxNatural_of_strictNatural {F G : Relator 𝒜 ℬ}
    {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (h : StrictNatural F G φ) : LaxNatural F G φ :=
  fun {_ _} R => le_of_eq (h R)

/-- THE CONVERSE OF A STRICTLY NATURAL FAMILY IS STRICTLY NATURAL, the other way round — read the
    square at `R°` and take its converse, which needs both relators to preserve `°`.  Lax has no
    such rule: `recip_not_laxNatural` (A6_1_OrdRelSet) refutes it. -/
public theorem strictNatural_recip {F G : Relator 𝒜 ℬ} {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A}
    (hF : F.PreservesRecip) (hG : G.PreservesRecip) (h : StrictNatural F G φ) :
    StrictNatural G F (fun A => (φ A)°) := by
  intro A B R
  have e := congrArg Allegory.recip (h R°)
  rw [Allegory.recip_comp, Allegory.recip_comp, hF, hG, Allegory.recip_recip,
    Allegory.recip_recip] at e
  exact e.symm

/-- Theorem 5.2's right-hand side with the EQUALITY on maps weakened to an INCLUSION: the
    `LaxNatural` inequation at the maps only.  It is strictly weaker than `LaxNatural` —
    `laxOnMaps_not_laxNatural` (A6_1_OrdRelSet) — so Theorem 5.2's equality is forced, not a
    convenience of its proof: shunting the two maps in the step `(G f)° ≫ φ ⊑ φ ≫ (F f)°` that
    tabulation needs turns it into `(G f)° ≫ φ ≫ F f ⊑ φ`, the CONVERSE of what the inclusion
    `G f ≫ φ ⊑ φ ≫ F f` gives. -/
@[expose] public def LaxOnMaps (F G : Relator 𝒜 ℬ) (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A) : Prop :=
  ∀ {A B : 𝒜} (f : A ⟶ B), Map f → G.map f ≫ φ B ⊑ φ A ≫ F.map f

/-- The two horizontal composites COINCIDE when the OUTER 2-cell is strictly natural: their whole
    gap is `χ`'s laxness at the components `φ a`, so removing laxness removes the gap.  Nothing is
    asked of `φ` — it need not even be lax natural. -/
public theorem hcomp_eq_of_strictNatural {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {K L : Relator ℬ 𝒞} (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A) {χ : ∀ B : ℬ, L.obj B ⟶ K.obj B}
    (hχ : StrictNatural K L χ) :
    (fun A => L.map (φ A) ≫ χ (F.obj A)) = (fun A => χ (G.obj A) ≫ K.map (φ A)) :=
  funext fun A => hχ (φ A)

/-! ### INTERCHANGE

  Vertical composition `φ₁` then `φ₂` (`comp_slides`) against horizontal composition, for
  each of the two horizontal composites.  Both hold only as `⊑`, and the two point OPPOSITE ways:
  the gap is `χ₂`'s laxness at `φ₁ a` for the outer-first composite and `χ₁`'s at `φ₂ a` for the
  inner-first one, and in each case it is the OTHER 2-cell's components that must be crossed. -/

/-- INTERCHANGE, outer-first: the vertical composite of the two horizontal composites is BELOW
    the horizontal composite of the two vertical ones. -/
public theorem laxNatural_interchange_outer_first {𝒞 : Type u₃} [Allegory.{v₃} 𝒞]
    {F G H : Relator 𝒜 ℬ} {K L M : Relator ℬ 𝒞} {φ₁ : ∀ A : 𝒜, H.obj A ⟶ G.obj A}
    {φ₂ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} (χ₁ : ∀ B : ℬ, M.obj B ⟶ L.obj B)
    {χ₂ : ∀ B : ℬ, L.obj B ⟶ K.obj B} (hχ₂ : LaxNatural K L χ₂) (A : 𝒜) :
    (χ₁ (H.obj A) ≫ L.map (φ₁ A)) ≫ (χ₂ (G.obj A) ≫ K.map (φ₂ A))
      ⊑ (χ₁ (H.obj A) ≫ χ₂ (H.obj A)) ≫ K.map (φ₁ A ≫ φ₂ A) :=
  calc (χ₁ (H.obj A) ≫ L.map (φ₁ A)) ≫ (χ₂ (G.obj A) ≫ K.map (φ₂ A))
      = χ₁ (H.obj A) ≫ ((L.map (φ₁ A) ≫ χ₂ (G.obj A)) ≫ K.map (φ₂ A)) := by simp [Cat.assoc]
    _ ⊑ χ₁ (H.obj A) ≫ ((χ₂ (H.obj A) ≫ K.map (φ₁ A)) ≫ K.map (φ₂ A)) :=
        comp_mono_left _ (comp_mono_right (hχ₂ (φ₁ A)) _)
    _ = (χ₁ (H.obj A) ≫ χ₂ (H.obj A)) ≫ K.map (φ₁ A ≫ φ₂ A) := by rw [K.map_comp]; simp [Cat.assoc]

/-- INTERCHANGE, inner-first: the horizontal composite of the two vertical ones is BELOW the
    vertical composite of the two horizontal composites — the opposite direction. -/
public theorem laxNatural_interchange_inner_first {𝒞 : Type u₃} [Allegory.{v₃} 𝒞]
    {F G H : Relator 𝒜 ℬ} {K L M : Relator ℬ 𝒞} {φ₁ : ∀ A : 𝒜, H.obj A ⟶ G.obj A}
    {φ₂ : ∀ A : 𝒜, G.obj A ⟶ F.obj A} {χ₁ : ∀ B : ℬ, M.obj B ⟶ L.obj B}
    (χ₂ : ∀ B : ℬ, L.obj B ⟶ K.obj B) (hχ₁ : LaxNatural L M χ₁) (A : 𝒜) :
    M.map (φ₁ A ≫ φ₂ A) ≫ (χ₁ (F.obj A) ≫ χ₂ (F.obj A))
      ⊑ (M.map (φ₁ A) ≫ χ₁ (G.obj A)) ≫ (L.map (φ₂ A) ≫ χ₂ (F.obj A)) :=
  calc M.map (φ₁ A ≫ φ₂ A) ≫ (χ₁ (F.obj A) ≫ χ₂ (F.obj A))
      = M.map (φ₁ A) ≫ ((M.map (φ₂ A) ≫ χ₁ (F.obj A)) ≫ χ₂ (F.obj A)) := by
        rw [M.map_comp]; simp [Cat.assoc]
    _ ⊑ M.map (φ₁ A) ≫ ((χ₁ (G.obj A) ≫ L.map (φ₂ A)) ≫ χ₂ (F.obj A)) :=
        comp_mono_left _ (comp_mono_right (hχ₁ (φ₂ A)) _)
    _ = (M.map (φ₁ A) ≫ χ₁ (G.obj A)) ≫ (L.map (φ₂ A) ≫ χ₂ (F.obj A)) := by simp [Cat.assoc]

end LaxNaturalClosure

/-! ## The sharp condition for the two horizontal composites to agree

  Theorem 5.2 needs the MIDDLE allegory tabular; the closure section above does not, so this one
  theorem sits in its own section. -/

section HcompOnMaps

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃} [Allegory.{v₁} 𝒜] [TabularAllegory ℬ]
  [Allegory.{v₃} 𝒞]

/-- The SHARP condition: the two horizontal composites agree as soon as every COMPONENT `φ a` is
    a MAP, which by Theorem 5.2 is where a lax `χ` is already strict.  Strict naturality of `χ`
    (`hcomp_eq_of_strictNatural`) is sufficient but NOT necessary. -/
public theorem hcomp_eq_of_map_components {F G : Relator 𝒜 ℬ} {K L : Relator ℬ 𝒞}
    (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A) {χ : ∀ B : ℬ, L.obj B ⟶ K.obj B} (hχ : LaxNatural K L χ)
    (hφ : ∀ A : 𝒜, Map (φ A)) :
    (fun A => L.map (φ A) ≫ χ (F.obj A)) = (fun A => χ (G.obj A) ≫ K.map (φ A)) :=
  funext fun A => (laxNatural_iff_strict_on_maps K L χ).mp hχ (φ A) (hφ A)

end HcompOnMaps

/-! ## The closure rules packaged: monotone relations form a category

  `comp_slides` and the two unit laws of `𝟙` are exactly what a category needs, so the
  objects of `𝒜` carrying a chosen endorelation, and the relations that slide past it, form
  one.  Its hom-sets inherit `⊑` and (over a distributive allegory) `∪`. -/

section OrdCat

/-- An object of `𝒜` with a chosen endorelation on it — an "order", though nothing below needs
    reflexivity or transitivity. -/
public structure OrdObj (𝒜 : Type u₁) [Allegory.{v₁} 𝒜] where
  carrier : 𝒜
  ord : carrier ⟶ carrier

variable {𝒜 : Type u₁} [Allegory.{v₁} 𝒜]

/-- A MONOTONE relation `a ⟶ b`: one that the source order slides right past. -/
@[expose] public def MonoHom (a b : OrdObj 𝒜) :=
  { X : a.carrier ⟶ b.carrier // a.ord ≫ X ⊑ X ≫ b.ord }

-- NOT an allegory: `∩` would need `(X ≫ Tb) ∩ (Y ≫ Tb) ⊑ (X ∩ Y) ≫ Tb`, the wrong direction of
-- semi-distributivity (`union_slides`), and `°` slides the order the wrong way (`recip_slides`).
/-- Monotone relations form a CATEGORY: `𝟙` is monotone because `a.ord ≫ 𝟙 = a.ord = 𝟙 ≫ a.ord`,
    and composition is `comp_slides`. -/
@[expose] public instance ordObjCat : Cat.{v₁} (OrdObj 𝒜) where
  Hom A B := MonoHom A B
  id A := ⟨𝟙 A.carrier, by rw [Cat.comp_id, Cat.id_comp]; exact le_refl _⟩
  comp X Y := ⟨X.1 ≫ Y.1, comp_slides X.2 Y.2⟩
  id_comp X := Subtype.ext (Cat.id_comp X.1)
  comp_id X := Subtype.ext (Cat.comp_id X.1)
  assoc X Y Z := Subtype.ext (Cat.assoc X.1 Y.1 Z.1)

/-- The hom-sets are POSETS, ordered pointwise by `⊑` on the underlying relations. -/
@[expose] public def MonoHom.le {A B : OrdObj 𝒜} (X Y : MonoHom A B) : Prop := X.1 ⊑ Y.1

-- Reflexivity gets no theorem: `MonoHom.le X X` unfolds to `X.1 ⊑ X.1`, so it IS `le_refl X.1`.
/-- `calc` support, and transitivity: the underlying `le_trans`. -/
public instance {A B : OrdObj 𝒜} :
    Trans (α := MonoHom A B) MonoHom.le MonoHom.le MonoHom.le where
  trans := Freyd.Alg.le_trans

/-- Antisymmetry, from `le_antisymm` on the underlying relations: two monotone relations ordered
    both ways have equal `.val`, and a `MonoHom` is its `.val` (`Subtype.ext`).  With the
    underlying `le_refl` and `le_trans` this makes each hom-set a POSET, not merely a preorder. -/
public theorem MonoHom.le_antisymm {A B : OrdObj 𝒜} {X Y : MonoHom A B} (hXY : X.le Y)
    (hYX : Y.le X) : X = Y := Subtype.ext (Freyd.Alg.le_antisymm hXY hYX)

/-- Composition is a POSET MAP in both arguments — `comp_mono_right` then `comp_mono_left` on the
    `.val`s.  This and the previous theorem are what "`OrdObj 𝒜` is enriched over posets" asserts:
    hom-sets are posets AND `≫` is monotone. -/
public theorem MonoHom.comp_mono {A B C : OrdObj 𝒜} {X X' : A ⟶ B} {Y Y' : B ⟶ C}
    (hX : MonoHom.le X X') (hY : MonoHom.le Y Y') : MonoHom.le (X ≫ Y) (X' ≫ Y') := by
  show X.1 ≫ Y.1 ⊑ X'.1 ≫ Y'.1
  exact Freyd.Alg.le_trans (comp_mono_right hX Y.1) (comp_mono_left X'.1 hY)

/-- Reciprocating `Ta ≫ X ⊑ X ≫ Tb` gives exactly this, and `°` being an order-isomorphism and
    an involution, this is ALL the hypothesis says about `X°`.  Monotonicity of `X°` for any
    orders `S`, `S'` would read `S ≫ X° ⊑ X° ≫ S'` — the composites sit on the opposite sides of
    `⊑`, and flipping the orders to `Tb°`, `Ta°` does not move them.  So `°` leaves `MonoHom`. -/
public theorem recip_slides {A B : 𝒜} {Ta : A ⟶ A} {Tb : B ⟶ B} {X : A ⟶ B}
    (h : Ta ≫ X ⊑ X ≫ Tb) : X° ≫ Ta° ⊑ Tb° ≫ X° := by
  have hr := recip_mono h
  rwa [Allegory.recip_comp, Allegory.recip_comp] at hr

end OrdCat

section PairSlides

variable {𝒜 : Type u₁} [TabularUnitaryDivisionAllegory 𝒜]

-- Stated over TWO products and non-endo arrows, so that `laxNatural_pair`'s shape — `φ b` on the
-- left, `φ a` on the right, a different product at each end — is an INSTANCE, not a re-proof.
/-- The FORK rule — and the exact contrast with `inter_not_monotonic`.  `⟨X,Y⟩` slides past
    `Ta×Tb` whenever `X` slides past `Ta` and `Y` past `Tb`: the two witnesses land in DIFFERENT
    components, so nothing forces them to agree, which is what the meet of two arrows `a ⟶ b`
    does force.  At `P = Q`, `X' = X`, `Y' = Y` it says `(a,Ta) × (b,Tb) := (P.p, Ta×Tb)` is a
    TENSOR on `OrdObj 𝒜` — not a CATEGORICAL product, since (5.6) makes
    `⟨X,Y⟩ ≫ outl = dom Y ≫ X`, which is `X` only when `Y` is entire. -/
public theorem pair_slides {A B a' b' C c' : 𝒜} (P : RelProd A B) (Q : RelProd a' b')
    {Tc : C ⟶ c'} {Ta : A ⟶ a'} {Tb : B ⟶ b'} {X : C ⟶ A} {Y : C ⟶ B} {X' : c' ⟶ a'}
    {Y' : c' ⟶ b'} (hX : Tc ≫ X' ⊑ X ≫ Ta) (hY : Tc ≫ Y' ⊑ Y ≫ Tb) :
    Tc ≫ Q.pair X' Y' ⊑ P.pair X Y ≫ prodMap P Q Ta Tb := by
  rw [RelProd.pair_prodMap]
  refine RelProd.le_pair_iff.mpr ⟨?_, ?_⟩
  · rw [Cat.assoc, RelProd.pair_outl]
    exact le_trans (comp_mono_left Tc (comp_mono_right (dom_coreflexive Y') X'))
      (by rw [Cat.id_comp]; exact hX)
  · rw [Cat.assoc, RelProd.pair_outr]
    exact le_trans (comp_mono_left Tc (comp_mono_right (dom_coreflexive X') Y'))
      (by rw [Cat.id_comp]; exact hY)

/-- The lax COPY law `R◁ ⊑ ◁(R×R)` is `pair_slides` at `X = Y = 𝟙` — copy IS `⟨𝟙,𝟙⟩` — so it gets
    no theorem of its own.  Its two hypotheses are `T ≫ 𝟙 ⊑ 𝟙 ≫ T`, i.e. `le_refl`. -/
example {A : 𝒜} (P : RelProd A A) {T : A ⟶ A} :
    T ≫ P.pair (𝟙 A) (𝟙 A) ⊑ P.pair (𝟙 A) (𝟙 A) ≫ prodMap P P T T :=
  pair_slides P P (by rw [Cat.comp_id, Cat.id_comp]; exact le_refl T)
    (by rw [Cat.comp_id, Cat.id_comp]; exact le_refl T)

-- With `pair_slides` this makes `×` a BIFUNCTOR on `OrdObj 𝒜` — its TENSOR, not a categorical
-- product, for the (5.6) reason `pair_slides` gives.
/-- `X×Y` slides past `Ta×Tb` whenever `X` slides past `Ta` and `Y` past `Tb`: `prodMap_comp`
    flattens both composites — an EQUALITY, so nothing is dropped — and `prodMap_mono` then
    compares them componentwise.  Stated over FOUR products and non-endo arrows, for the same
    reason `pair_slides` is: `laxNatural_prod`'s square names a different product at each of its
    four corners, and is then an INSTANCE rather than the same calculation written again. -/
public theorem prodMap_slides {A B a' b' C D c' d' : 𝒜} (P : RelProd A B) (Q : RelProd a' b')
    (P' : RelProd C D) (Q' : RelProd c' d') {Ta : A ⟶ a'} {Tb : B ⟶ b'} {Tc : C ⟶ c'}
    {Td : D ⟶ d'} {X : A ⟶ C} {Y : B ⟶ D} {X' : a' ⟶ c'} {Y' : b' ⟶ d'}
    (hX : Ta ≫ X' ⊑ X ≫ Tc) (hY : Tb ≫ Y' ⊑ Y ≫ Td) :
    prodMap P Q Ta Tb ≫ prodMap Q Q' X' Y' ⊑ prodMap P P' X Y ≫ prodMap P' Q' Tc Td := by
  rw [prodMap_comp, prodMap_comp]
  exact prodMap_mono hX hY

/-- The SWAP `a×b ⟶ b×a`: the two projections paired in the other order.  A MAP, being a `pair`
    of two maps (`RelProd.pair_map`), so it is exempt from (5.6)'s `dom` — see `swap_swap`. -/
@[expose] public def RelProd.swap {A B : 𝒜} (P : RelProd A B) (Q : RelProd B A) : P.p ⟶ Q.p :=
  Q.pair P.outr P.outl

/-- The swap is SELF-INVERSE.  Running it twice re-pairs `outl` with `outr` — the `dom`s that
    (5.6)/(5.7) leave behind are identities because the projections are maps — and
    `⟨outl,outr⟩ = 1` is the tabulation's joint-monic equation. -/
public theorem RelProd.swap_swap {A B : 𝒜} (P : RelProd A B) (Q : RelProd B A) :
    P.swap Q ≫ Q.swap P = Cat.id P.p := by
  show Q.pair P.outr P.outl ≫ P.pair Q.outr Q.outl = Cat.id P.p
  rw [RelProd.map_comp_pair (Q.pair_map P.outr_map P.outl_map), RelProd.pair_outl,
    RelProd.pair_outr, P.outl_map.1, P.outr_map.1, Cat.id_comp, Cat.id_comp]
  exact P.joint_id

end PairSlides

section LaxNaturalPair

-- `HasRelProd` on the TARGET only: `Relator.prod` must choose a product object for each `x`.
variable {𝒮 : Type u₁} {𝒜 : Type u₂} [Allegory.{v₁} 𝒮] [TabularUnitaryDivisionAllegory 𝒜]
  [HasRelProd 𝒜]

/-- Lax naturality is closed under FORK: `φ : G ⟶ F` and `ψ : G ⟶ F'` give
    `⟨φ,ψ⟩ : G ⟶ F×F'`.  `pair_slides` at every `R` — stated over the two products `F x × F' x`
    and `F y × F' y`, and over non-endo arrows, precisely so that this is an instance rather
    than the same calculation written out again. -/
public theorem laxNatural_pair {F F' G : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, G.obj x ⟶ F.obj x}
    {ψ : ∀ x : 𝒮, G.obj x ⟶ F'.obj x} (hφ : LaxNatural F G φ) (hψ : LaxNatural F' G ψ) :
    LaxNatural (Relator.prod F F') G
      (fun x => (relProd (F.obj x) (F'.obj x)).pair (φ x) (ψ x)) :=
  fun {_ _} R => pair_slides _ _ (hφ R) (hψ R)

/-- **`Relator.prod` is a TENSOR, not a categorical PRODUCT.**  `laxNatural_pair` supplies the
    mediating arrow, but the first projection does NOT cancel: (5.6) turns `⟨φ,ψ⟩ ≫ outl` into
    `dom (ψ x) ≫ φ x`, below `φ x` and equal to it exactly when `ψ x` is ENTIRE.  The strict
    inclusion is realised in `Rel(Set)` by `prod_not_categorical_product` (A6_1_OrdRelSet), so
    the universal property fails on EXISTENCE, not merely on uniqueness. -/
public theorem laxNatural_pair_outl {F F' G : Relator 𝒮 𝒜} (φ : ∀ x : 𝒮, G.obj x ⟶ F.obj x)
    (ψ : ∀ x : 𝒮, G.obj x ⟶ F'.obj x) (x : 𝒮) :
    ((relProd (F.obj x) (F'.obj x)).pair (φ x) (ψ x) ≫ (relProd (F.obj x) (F'.obj x)).outl
        ⊑ φ x) ∧
      (Entire (ψ x) → (relProd (F.obj x) (F'.obj x)).pair (φ x) (ψ x)
        ≫ (relProd (F.obj x) (F'.obj x)).outl = φ x) := by
  constructor
  · rw [RelProd.pair_outl]
    exact le_trans (comp_mono_right (dom_coreflexive (ψ x)) (φ x)) (le_of_eq (Cat.id_comp (φ x)))
  · intro hent
    rw [RelProd.pair_outl, hent, Cat.id_comp]

/-- The SWAP is lax natural `F×F' ⟶ F'×F` — over any target with chosen products, no tabulation
    of the SOURCE needed.  `RelProd.pair_prodMap` turns the right-hand side into a single `pair`,
    and the two halves of `RelProd.le_pair_iff` are then `prodMap_outr_le` and `prodMap_outl_le`,
    the swap's own `dom`s being identities because the projections are maps. -/
public theorem laxNatural_swap {F F' : Relator 𝒮 𝒜} :
    LaxNatural (Relator.prod F' F) (Relator.prod F F')
      (fun x => (relProd (F.obj x) (F'.obj x)).swap (relProd (F'.obj x) (F.obj x))) :=
  fun {x y} R => by
  show prodMap (relProd (F.obj x) (F'.obj x)) (relProd (F.obj y) (F'.obj y)) (F.map R) (F'.map R)
      ≫ (relProd (F.obj y) (F'.obj y)).swap (relProd (F'.obj y) (F.obj y))
    ⊑ (relProd (F.obj x) (F'.obj x)).swap (relProd (F'.obj x) (F.obj x))
      ≫ prodMap (relProd (F'.obj x) (F.obj x)) (relProd (F'.obj y) (F.obj y)) (F'.map R) (F.map R)
  rw [RelProd.swap, RelProd.swap, RelProd.pair_prodMap]
  refine RelProd.le_pair_iff.mpr ⟨?_, ?_⟩
  · rw [Cat.assoc, RelProd.pair_outl, (relProd (F.obj y) (F'.obj y)).outl_map.1, Cat.id_comp]
    exact prodMap_outr_le _ _ _ _
  · rw [Cat.assoc, RelProd.pair_outr, (relProd (F.obj y) (F'.obj y)).outr_map.1, Cat.id_comp]
    exact prodMap_outl_le _ _ _ _

/-- **`×` CLOSES in LaT**: `φ : G ⟶ F` and `ψ : G' ⟶ F'` lax natural give the PRODUCT MAP
    `φ×ψ : G×G' ⟶ F×F'` lax natural.  Not the fork `laxNatural_pair` — the two families here run
    between four different relators, and the square's four corners are four different products,
    which is what `prodMap_slides` is stated over. -/
public theorem laxNatural_prod {F F' G G' : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, G.obj x ⟶ F.obj x}
    {ψ : ∀ x : 𝒮, G'.obj x ⟶ F'.obj x} (hφ : LaxNatural F G φ) (hψ : LaxNatural F' G' ψ) :
    LaxNatural (Relator.prod F F') (Relator.prod G G')
      (fun x => prodMap (relProd (G.obj x) (G'.obj x)) (relProd (F.obj x) (F'.obj x))
        (φ x) (ψ x)) :=
  fun {_ _} R => prodMap_slides _ _ _ _ (hφ R) (hψ R)

/-- **And `×` closes STRICTLY too** — unlike the fork, whose `outl` already fails to cancel
    (`laxNatural_pair_outl`), the product map creates no slack: `prodMap_comp` flattens each side
    to ONE `prodMap`, and the two components are then the two hypotheses verbatim. -/
public theorem strictNatural_prod {F F' G G' : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, G.obj x ⟶ F.obj x}
    {ψ : ∀ x : 𝒮, G'.obj x ⟶ F'.obj x} (hφ : StrictNatural F G φ) (hψ : StrictNatural F' G' ψ) :
    StrictNatural (Relator.prod F F') (Relator.prod G G')
      (fun x => prodMap (relProd (G.obj x) (G'.obj x)) (relProd (F.obj x) (F'.obj x))
        (φ x) (ψ x)) :=
  fun {x y} R => by
  show prodMap (relProd (G.obj x) (G'.obj x)) (relProd (G.obj y) (G'.obj y)) (G.map R) (G'.map R)
      ≫ prodMap (relProd (G.obj y) (G'.obj y)) (relProd (F.obj y) (F'.obj y)) (φ y) (ψ y)
    = prodMap (relProd (G.obj x) (G'.obj x)) (relProd (F.obj x) (F'.obj x)) (φ x) (ψ x)
      ≫ prodMap (relProd (F.obj x) (F'.obj x)) (relProd (F.obj y) (F'.obj y)) (F.map R) (F'.map R)
  rw [prodMap_comp, prodMap_comp, hφ R, hψ R]

end LaxNaturalPair

section JuncSlides

-- Only `DistributiveAllegory`: unlike the fork, the co-fork needs no tabulation and no `dom`.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

-- Two coproducts and non-endo arrows, for the same reason as `pair_slides`: `laxNatural_junc` is
-- then an instance rather than the same calculation written out again.
/-- The CO-FORK rule, the coproduct's `pair_slides`: `[X,Y]` slides past `Tc` whenever `X` and
    `Y` do.  Where the fork pays for `⟨X,Y⟩ ≫ outl = dom Y ≫ X` — the lax copy law, `dom Y`
    dropped by `dom_coreflexive` — the co-fork's cancellation `sumMap_junc` is an EQUALITY, so
    this proof spends nothing beyond the two hypotheses. -/
public theorem junc_slides {s a₁ a₂ t b₁ b₂ c c' : 𝒜} (C : Coproduct s a₁ a₂)
    (D : Coproduct t b₁ b₂) {Ta : a₁ ⟶ b₁} {Tb : a₂ ⟶ b₂} {Tc : c ⟶ c'} {X : a₁ ⟶ c}
    {Y : a₂ ⟶ c} {X' : b₁ ⟶ c'} {Y' : b₂ ⟶ c'} (hX : Ta ≫ X' ⊑ X ≫ Tc)
    (hY : Tb ≫ Y' ⊑ Y ≫ Tc) :
    sumMap C D Ta Tb ≫ junc D X' Y' ⊑ junc C X Y ≫ Tc := by
  rw [sumMap_junc, junc_comp]
  exact junc_mono C hX hY

-- The injections slide STRICTLY and get no theorem: `(Ta+Tb)` is by definition the junc whose
-- branches are `Ta ≫ u₁`, `Tb ≫ u₂`, so `u₁ ≫ (Ta+Tb) = Ta ≫ u₁` IS `u₁_junc` (resp. `u₂_junc`).

end JuncSlides

section LaxNaturalJunc

-- `PositiveAllegory` on the TARGET only: `Relator.sum` must choose a coproduct object for each `x`.
variable {𝒮 : Type u₁} {𝒜 : Type u₂} [Allegory.{v₁} 𝒮] [PositiveAllegory 𝒜]

/-- Lax naturality is closed under CO-FORK: `φ : F ⟶ G` and `ψ : F' ⟶ G` give
    `[φ,ψ] : F+F' ⟶ G`.  The variance is the fork's mirrored: a `LaxNatural` family runs from the
    SECOND relator to the first, so the two branches go INTO `G` and the coproduct is the source.
    `junc_slides` at every `R`, over the two coproducts `F x + F' x` and `F y + F' y`. -/
public theorem laxNatural_junc {F F' G : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, F.obj x ⟶ G.obj x}
    {ψ : ∀ x : 𝒮, F'.obj x ⟶ G.obj x} (hφ : LaxNatural G F φ) (hψ : LaxNatural G F' ψ) :
    LaxNatural G (Relator.sum F F')
      (fun x => junc (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)) (φ x) (ψ x)) :=
  fun {_ _} R => junc_slides _ _ (hφ R) (hψ R)

/-! ### `Relator.sum` is a BIPRODUCT of relators and lax natural transformations

  Fixing the two allegories, relators `𝒮 ⟶ 𝒜` and lax natural transformations form a category.
  `+` is a biproduct in `𝒜` itself (`coproduct_is_product`), and the whole structure lifts
  POINTWISE: an arrow here is a family, and a family is settled at each `x`. -/

/-- The four structure maps of `Relator.sum` are lax natural — STRICTLY so, at every arrow and
    not only at the maps: the injections by `u₁_junc`/`u₂_junc`, the projections `u₁°`/`u₂°` by
    `sumMap_recip_u₁`/`sumMap_recip_u₂`. -/
public theorem strictNatural_sum_structure {F F' : Relator 𝒮 𝒜} :
    StrictNatural (Relator.sum F F') F
        (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁) ∧
      StrictNatural (Relator.sum F F') F'
        (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂) ∧
      StrictNatural F (Relator.sum F F')
        (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁°) ∧
      StrictNatural F' (Relator.sum F F')
        (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂°) :=
  ⟨fun _ => (u₁_junc _ _ _).symm, fun _ => (u₂_junc _ _ _).symm,
   fun _ => sumMap_recip_u₁ _ _ _ _, fun _ => sumMap_recip_u₂ _ _ _ _⟩

/-- **`Relator.sum F F'` is a COPRODUCT.**  For `φ : F ⟶ G` and `ψ : F' ⟶ G` there is a lax
    natural `θ : F+F' ⟶ G` cancelling against both injections, and it is the ONLY family that
    does — the competitor need not even be lax natural.  Nothing new is proved: existence is
    `laxNatural_junc`, cancellation `u₁_junc`/`u₂_junc`, uniqueness `junc_unique`, each at
    every `x`. -/
public theorem relatorSum_coproduct {F F' G : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, F.obj x ⟶ G.obj x}
    {ψ : ∀ x : 𝒮, F'.obj x ⟶ G.obj x} (hφ : LaxNatural G F φ) (hψ : LaxNatural G F' ψ) :
    ∃ θ : ∀ x : 𝒮, (Relator.sum F F').obj x ⟶ G.obj x, LaxNatural G (Relator.sum F F') θ ∧
      (∀ x, (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁ ≫ θ x = φ x) ∧
      (∀ x, (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂ ≫ θ x = ψ x) ∧
      ∀ θ' : ∀ x : 𝒮, (Relator.sum F F').obj x ⟶ G.obj x,
        (∀ x, (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁ ≫ θ' x = φ x) →
        (∀ x, (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂ ≫ θ' x = ψ x) → θ' = θ :=
  ⟨fun x => junc (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)) (φ x) (ψ x),
   laxNatural_junc hφ hψ, fun _ => u₁_junc _ _ _, fun _ => u₂_junc _ _ _,
   fun _ h₁ h₂ => funext fun x => junc_unique _ (h₁ x) (h₂ x)⟩

/-- **`Relator.sum F F'` is a PRODUCT too** — a BIPRODUCT, as `+` already is in `𝒜`.  The
    pairing `φ≫u₁ ∪ ψ≫u₂` is lax natural by `union_slides` of two `comp_slides` with the
    injections of `strictNatural_sum_structure`, all at every `R`; the three equations are
    `coproduct_is_product` at every `x`. -/
public theorem relatorSum_product {F F' G : Relator 𝒮 𝒜} {φ : ∀ x : 𝒮, G.obj x ⟶ F.obj x}
    {ψ : ∀ x : 𝒮, G.obj x ⟶ F'.obj x} (hφ : LaxNatural F G φ) (hψ : LaxNatural F' G ψ) :
    ∃ θ : ∀ x : 𝒮, G.obj x ⟶ (Relator.sum F F').obj x, LaxNatural (Relator.sum F F') G θ ∧
      (∀ x, θ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁° = φ x) ∧
      (∀ x, θ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂° = ψ x) ∧
      ∀ θ' : ∀ x : 𝒮, G.obj x ⟶ (Relator.sum F F').obj x,
        (∀ x, θ' x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁° = φ x) →
        (∀ x, θ' x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂° = ψ x) → θ' = θ :=
  by
  have hu₁ : LaxNatural (Relator.sum F F') F
      (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁) :=
    fun R => le_of_eq ((strictNatural_sum_structure (F := F) (F' := F')).1 R)
  have hu₂ : LaxNatural (Relator.sum F F') F'
      (fun x => (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂) :=
    fun R => le_of_eq ((strictNatural_sum_structure (F := F) (F' := F')).2.1 R)
  have hφu : LaxNatural (Relator.sum F F') G
      (fun x => φ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁) :=
    fun R => comp_slides (hφ R) (hu₁ R)
  have hψu : LaxNatural (Relator.sum F F') G
      (fun x => ψ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂) :=
    fun R => comp_slides (hψ R) (hu₂ R)
  have hpair : LaxNatural (Relator.sum F F') G
      (fun x => (φ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁) ∪
        (ψ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂)) :=
    fun R => union_slides (hφu R) (hψu R)
  exact ⟨fun x => (φ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₁) ∪
      (ψ x ≫ (PositiveAllegory.has_coproduct (F.obj x) (F'.obj x)).u₂), hpair,
    fun x => (coproduct_is_product _ (φ x) (ψ x)).1,
    fun x => (coproduct_is_product _ (φ x) (ψ x)).2.1,
    fun _ h₁ h₂ => funext fun x => (coproduct_is_product _ (φ x) (ψ x)).2.2 _ (h₁ x) (h₂ x)⟩

end LaxNaturalJunc

section MonoHomUnion

-- Same distributive layer `union_slides` needs; the meet is absent, not merely unproved.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

/-- Binary UNION of monotone relations, well defined by `union_slides`: the hom-sets are
    join-semilattices under `MonoHom.le`. -/
@[expose] public def MonoHom.union {A B : OrdObj 𝒜} (X Y : MonoHom A B) : MonoHom A B :=
  ⟨X.1 ∪ Y.1, union_slides X.2 Y.2⟩

end MonoHomUnion

section ProjLax

variable {𝒜 : Type u₁} [TabularUnitaryDivisionAllegory 𝒜] [HasRelProd 𝒜]

/-- The LEFT projection is lax natural `Δ ⟶ 1` as well — `prodMap_outl_le` where A5_2's
    `outr_lax_natural` (B&dM p.133) uses `prodMap_outr_le`.  The two together are the smallest
    pair of lax natural transformations whose MEET is not one (`laxNatural_inter_false`). -/
public theorem outl_lax_natural :
    LaxNatural (Relator.idRelator 𝒜) (Δ 𝒜) (fun A => (relProd A A).outl) :=
  fun R => prodMap_outl_le _ _ R R

end ProjLax

/-! ## The closure rules packaged: relators and lax natural transformations form a category

  Fixing the two allegories, the relators `𝒜 ⟶ ℬ` are the objects and the lax natural
  transformations the arrows: `comp_slides` at every `R` is composition and the identity
  family is `𝟙`.
  This is NOT an instance of `OrdObj`, nor `OrdObj` of it — `OrdObj` fixes the two orders and
  lets the arrow vary, a `LaxNatural` family fixes the family and quantifies over every `R`. -/

section LaTCat

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- A lax natural transformation `F ⟶ G` bundled with its proof, as `MonoHom` bundles a monotone
    relation with its slide proof.  `LaxNatural G F` reads "`φ` runs from `F` to `G`" — the
    definition of A5_1 names the TARGET first. -/
@[expose] public def LaT (F G : Relator 𝒜 ℬ) :=
  { φ : ∀ A : 𝒜, F.obj A ⟶ G.obj A // LaxNatural G F φ }

-- NOT an allegory, for two independent reasons: `∩` leaves the arrows (`laxNatural_inter_false`)
-- and `°` lands among the OPLAX families (`recip_oplax` below).
/-- Relators and lax natural transformations form a CATEGORY: `𝟙` is lax natural because
    `F(R) ≫ 𝟙 = F(R) = 𝟙 ≫ F(R)`, and composition is `comp_slides` at every `R`. -/
@[expose] public instance laxNaturalCat : Cat.{max u₁ v₂} (Relator 𝒜 ℬ) where
  Hom F G := LaT F G
  id F := ⟨fun A => 𝟙 (F.obj A), laxNatural_of_strictNatural (strictNatural_id F)⟩
  comp φ ψ := ⟨fun A => φ.1 A ≫ ψ.1 A, fun R => comp_slides (φ.2 R) (ψ.2 R)⟩
  id_comp φ := Subtype.ext (funext fun A => Cat.id_comp (φ.1 A))
  comp_id φ := Subtype.ext (funext fun A => Cat.comp_id (φ.1 A))
  assoc φ ψ χ := Subtype.ext (funext fun A => Cat.assoc (φ.1 A) (ψ.1 A) (χ.1 A))

/-- The hom-sets are POSETS, ordered COMPONENTWISE by `⊑` on the underlying relations. -/
@[expose] public def LaT.le {F G : Relator 𝒜 ℬ} (φ ψ : LaT F G) : Prop := ∀ A : 𝒜, φ.1 A ⊑ ψ.1 A

-- Unlike `MonoHom.le`, this does NOT unfold to a single `⊑`: a component has to be supplied
-- first, so reflexivity is `le_refl` under a binder and gets a theorem.
/-- Reflexivity, componentwise. -/
public theorem LaT.le_refl {F G : Relator 𝒜 ℬ} (φ : LaT F G) : φ.le φ :=
  fun A => Freyd.Alg.le_refl (φ.1 A)

/-- `calc` support, and transitivity: the underlying `le_trans` at every component. -/
public instance LaT.le_trans {F G : Relator 𝒜 ℬ} :
    Trans (α := LaT F G) LaT.le LaT.le LaT.le where
  trans h h' := fun A => Freyd.Alg.le_trans (h A) (h' A)

/-- Antisymmetry: two lax natural transformations ordered both ways agree at every component, so
    their families are equal as FUNCTIONS (`funext`) and hence as arrows (`Subtype.ext`).  With
    `LaT.le_refl` and the `Trans` instance this makes each hom-set a POSET. -/
public theorem LaT.le_antisymm {F G : Relator 𝒜 ℬ} {φ ψ : LaT F G} (hφψ : φ.le ψ)
    (hψφ : ψ.le φ) : φ = ψ :=
  Subtype.ext (funext fun A => Freyd.Alg.le_antisymm (hφψ A) (hψφ A))

/-- Composition is a POSET MAP in both arguments — `comp_mono_right` then `comp_mono_left` at
    every component.  This and the previous theorem are what "the LaT category is enriched over
    posets" asserts. -/
public theorem LaT.comp_mono {F G H : Relator 𝒜 ℬ} {φ φ' : F ⟶ G} {ψ ψ' : G ⟶ H}
    (hφ : LaT.le φ φ') (hψ : LaT.le ψ ψ') : LaT.le (φ ≫ ψ) (φ' ≫ ψ') :=
  fun A => Freyd.Alg.le_trans (comp_mono_right (hφ A) (ψ.1 A)) (comp_mono_left (φ'.1 A) (hψ A))

/-- OPLAX: the `LaxNatural` inequation with `⊑` the other way round. -/
@[expose] public def OpLaxNatural (F G : Relator 𝒜 ℬ) (φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A) : Prop :=
  ∀ {A B : 𝒜} (R : A ⟶ B), φ A ≫ F.map R ⊑ G.map R ≫ φ B

/-- **`°` does not act on this category.**  Reciprocating `G(R) ≫ φ b ⊑ φ a ≫ F(R)` at `R°` and
    pushing `°` through both relators turns it into `φ a° ≫ G(R) ⊑ F(R) ≫ φ b°` — the inequation
    of `LaxNatural F G (fun a => (φ a)°)` with `⊑` REVERSED, i.e. `φ°` is OPLAX.  It is not lax:
    `recip_not_laxNatural` (A6_1_OrdRelSet) is a lax `φ` over `Rel(Set)` whose `φ°` is not. -/
public theorem recip_oplax {F G : Relator 𝒜 ℬ} {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A}
    (hF : F.PreservesRecip) (hG : G.PreservesRecip) (h : LaxNatural F G φ) :
    OpLaxNatural G F (fun A => (φ A)°) := fun {A B} R => by
  have hr := recip_mono (h R°)
  rw [Allegory.recip_comp, Allegory.recip_comp, hF, hG, Allegory.recip_recip,
    Allegory.recip_recip] at hr
  exact hr

/-- And back, by the same rewriting: the converse of an OPLAX family is LAX, so `(φ°)°` closes the
    pair and neither condition is a dead end. -/
public theorem recip_lax {F G : Relator 𝒜 ℬ} {φ : ∀ A : 𝒜, G.obj A ⟶ F.obj A}
    (hF : F.PreservesRecip) (hG : G.PreservesRecip) (h : OpLaxNatural F G φ) :
    LaxNatural G F (fun A => (φ A)°) := fun {A B} R => by
  have hr := recip_mono (h R°)
  rw [Allegory.recip_comp, Allegory.recip_comp, hF, hG, Allegory.recip_recip,
    Allegory.recip_recip] at hr
  exact hr

end LaTCat

/-! ## The constant relator at a ZERO OBJECT is a zero object of the LaT category

  Abstract: a zero object of the TARGET allegory is all it takes.  Every relation into or out of
  it is `𝟘`, so both the family and its uniqueness are forced and the lax inequation is between
  two `𝟘`s.  `relSetEmpty_zero` (A6_1_OrdRelSet) is the `Rel(Set)` witness that the hypothesis is
  satisfiable — the empty type — but nothing below reads the set model. -/

section LaTZero

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [DistributiveAllegory ℬ]

/-- `Relator.const z` is TERMINAL: exactly one lax natural transformation `F ⟶ const z`, namely
    `𝟘` at every object.  Every `X : F(a) ⟶ z` is `X ≫ 𝟙 z = X ≫ 𝟘 = 𝟘`. -/
public theorem const_zero_terminal {z : ℬ} (hz : 𝟙 z = (𝟘 : z ⟶ z)) (F : Relator 𝒜 ℬ) :
    ∃ φ : LaT F (Relator.const z), ∀ ψ : LaT F (Relator.const z), ψ = φ := by
  have hone : ∀ {A : 𝒜} (X : F.obj A ⟶ z), X = 𝟘 := by
    intro A X
    have hX : X ≫ 𝟙 z = X := Cat.comp_id X
    rw [hz, DistributiveAllegory.comp_zero] at hX
    exact hX.symm
  exact ⟨⟨fun _ => 𝟘, fun _ => by
      rw [DistributiveAllegory.comp_zero, DistributiveAllegory.zero_comp]; exact le_refl _⟩,
    fun ψ => Subtype.ext (funext fun A => hone (ψ.1 A))⟩

/-- `Relator.const z` is INITIAL as well, so it is a ZERO OBJECT: every `X : z ⟶ F(a)` is
    `𝟙 z ≫ X = 𝟘 ≫ X = 𝟘`.  The two arguments are dual, not one theorem applied twice — `𝟘`'s
    two absorption laws are separate axioms of `DistributiveAllegory`. -/
public theorem const_zero_initial {z : ℬ} (hz : 𝟙 z = (𝟘 : z ⟶ z)) (F : Relator 𝒜 ℬ) :
    ∃ φ : LaT (Relator.const z) F, ∀ ψ : LaT (Relator.const z) F, ψ = φ := by
  have hone : ∀ {A : 𝒜} (X : z ⟶ F.obj A), X = 𝟘 := by
    intro A X
    have hX : 𝟙 z ≫ X = X := Cat.id_comp X
    rw [hz, DistributiveAllegory.zero_comp] at hX
    exact hX.symm
  exact ⟨⟨fun _ => 𝟘, fun _ => by
      rw [DistributiveAllegory.comp_zero, DistributiveAllegory.zero_comp]; exact le_refl _⟩,
    fun ψ => Subtype.ext (funext fun A => hone (ψ.1 A))⟩

end LaTZero

/-! ## The left factor of a product as a lane

  A string diagram draws a product `A×Y` as the ONE lane `A×−` — `Relator.prod (Relator.const A)
  (Relator.idRelator _)` — over the lanes of `Y`, so a bead on that lane is a 2-cell
  `A×− ⟶ A'×−` and its dot is the naturality below. -/

section ConstLane

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- A CONSTANT relator leaves no naturality condition: `(const b).map R` is `𝟙 b` at every `R`, so
    ONE arrow `f : b ⟶ b'` is already a strictly natural family.  Through `strictNatural_prod` and
    `strictNatural_id` this is what makes `Y ↦ f×𝟙 Y` strictly natural from `b×−` to `b'×−`. -/
public theorem strictNatural_const {b b' : ℬ} (f : b ⟶ b') :
    StrictNatural (Relator.const b' : Relator 𝒜 ℬ) (Relator.const b) (fun _ => f) :=
  fun {_ _} _ => by show 𝟙 b ≫ f = f ≫ 𝟙 b'; rw [Cat.id_comp, Cat.comp_id]

end ConstLane

/-! ## `R⊑S` is a special case of a lax transformation

  The lax square at two CONSTANT relators.  `const A` and `const B` send every arrow of the
  source to an identity, so both VERTICALS of the square are identities, and identity verticals
  are what turn a square into a comparison of its two horizontals.  What is left of
  `G(R)φ_Y ⊑ φ_X F(R)` is `φ_Y ⊑ φ_X`: a lax transformation `const A ⇒ const B` is a family of
  arrows `A ⟶ B` that DECREASES along every arrow of the source.  Over a source with one
  non-identity arrow `X ⟶ Y` the entire datum is the pair `φ X, φ Y` with `φ Y ⊑ φ X` — one
  containment `R ⊑ S`, and no naturality left to check. -/

section LaTConst

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- **The collapse**: a lax transformation between two CONSTANT relators is EXACTLY a family
    `φ : 𝒜 → (A ⟶ B)` decreasing along every arrow — `φ Y ⊑ φ X` for every `R : X ⟶ Y`.  Both
    directions are the same rewrite, `𝟙 A ≫ φ Y ⊑ φ X ≫ 𝟙 B` against `φ Y ⊑ φ X`; nothing about
    `R` beyond its existence is used, which is why the collapse is total. -/
public theorem laxNatural_const_iff {A B : ℬ} (φ : ∀ _ : 𝒜, A ⟶ B) :
    LaxNatural (Relator.const B : Relator 𝒜 ℬ) (Relator.const A) φ
      ↔ ∀ {X Y : 𝒜} (_ : X ⟶ Y), φ Y ⊑ φ X := by
  constructor
  · intro hlax X Y R
    have hR : 𝟙 A ≫ φ Y ⊑ φ X ≫ 𝟙 B := hlax R
    rwa [Cat.id_comp, Cat.comp_id] at hR
  · intro hle X Y R
    show 𝟙 A ≫ φ Y ⊑ φ X ≫ 𝟙 B
    rw [Cat.id_comp, Cat.comp_id]
    exact hle R

end LaTConst

end Freyd.Alg
