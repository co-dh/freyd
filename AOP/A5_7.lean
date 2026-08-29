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
  on the nose. -/

section EpsExample

variable {𝒜 : Type u₁} [UnguardedPowerAllegory 𝒜]

/-- **B&dM p.133**: membership `∈` is lax natural from the power relator to the identity
    relator. -/
theorem eps_lax_natural {a b : 𝒜} (R : a ⟶ b) :
    powerRel R ≫ ∋ b ⊑ ∋ a ≫ (Relator.idRelator 𝒜).map R :=
  powerRel_eps_lax R

end EpsExample

/-! ## §5.7 Theorem 5.2: lax naturality is equivalent to strict naturality on maps -/

section Theorem52

variable {𝒜 : Type u₁} {ℬ : Type u₂} [TabularAllegory 𝒜] [Allegory.{v₂} ℬ]
  (F G : Relator 𝒜 ℬ) (φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a)

/-- **B&dM Theorem 5.2**: `φ` is lax natural from `G` to `F` iff it is STRICTLY natural on
    every map `f`. -/
theorem laxNatural_iff_strict_on_maps :
    LaxNatural F G φ ↔ ∀ {a b : 𝒜} (f : a ⟶ b), Map f → G.map f ≫ φ b = φ a ≫ F.map f := by
  constructor
  · intro hlax a b f hf
    have hFf : Map (F.map f) := F.map_is_map hf
    have hGf : Map (G.map f) := G.map_is_map hf
    have hFfrecip : F.map f° = (F.map f)° := F.map_recip_map hf
    have hGfrecip : G.map f° = (G.map f)° := G.map_recip_map hf
    have hle1 : G.map f ≫ φ b ⊑ φ a ≫ F.map f := hlax f
    have hle2 : G.map f° ≫ φ a ⊑ φ b ≫ F.map f° := hlax f°
    rw [hGfrecip, hFfrecip] at hle2
    have hle2a : φ a ⊑ G.map f ≫ (φ b ≫ (F.map f)°) := (map_shunt_left hGf _ _).mp hle2
    have hle2b : φ a ⊑ (G.map f ≫ φ b) ≫ (F.map f)° := by rw [Cat.assoc]; exact hle2a
    have hle2' : φ a ≫ F.map f ⊑ G.map f ≫ φ b := (map_shunt_right hFf _ _).mpr hle2b
    exact le_antisymm hle1 hle2'
  · intro hstrict a b R
    obtain ⟨c, h, k, hh, hk, hR, _⟩ := TabularAllegory.tabular (𝒜 := 𝒜) R
    have hFhmap : Map (F.map h) := F.map_is_map hh
    have hGhmap : Map (G.map h) := G.map_is_map hh
    have hFhrecip : F.map h° = (F.map h)° := F.map_recip_map hh
    have hGhrecip : G.map h° = (G.map h)° := G.map_recip_map hh
    have hstep_h : (G.map h)° ≫ φ c ⊑ φ a ≫ (F.map h)° := by
      have he : G.map h ≫ φ a = φ c ≫ F.map h := hstrict h hh
      apply (map_shunt_left hGhmap _ _).mpr
      have hent : Cat.id (F.obj c) ⊑ F.map h ≫ (F.map h)° := entire_id_le hFhmap.1
      calc φ c = φ c ≫ Cat.id (F.obj c) := (Cat.comp_id _).symm
        _ ⊑ φ c ≫ (F.map h ≫ (F.map h)°) := comp_mono_left _ hent
        _ = (φ c ≫ F.map h) ≫ (F.map h)° := (Cat.assoc _ _ _).symm
        _ = (G.map h ≫ φ a) ≫ (F.map h)° := by rw [he]
        _ = G.map h ≫ (φ a ≫ (F.map h)°) := Cat.assoc _ _ _
    have hFcomp : F.map (h° ≫ k) = (F.map h)° ≫ F.map k := by rw [F.map_comp, hFhrecip]
    have p1 : G.map R ≫ φ b = ((G.map h)° ≫ φ c) ≫ F.map k := by
      calc G.map R ≫ φ b
          = G.map (h° ≫ k) ≫ φ b := by rw [hR]
        _ = (G.map h° ≫ G.map k) ≫ φ b := by rw [G.map_comp]
        _ = ((G.map h)° ≫ G.map k) ≫ φ b := by rw [hGhrecip]
        _ = (G.map h)° ≫ (G.map k ≫ φ b) := Cat.assoc _ _ _
        _ = (G.map h)° ≫ (φ c ≫ F.map k) := by rw [hstrict k hk]
        _ = ((G.map h)° ≫ φ c) ≫ F.map k := (Cat.assoc _ _ _).symm
    have p2 : ((G.map h)° ≫ φ c) ≫ F.map k ⊑ φ a ≫ F.map R := by
      calc ((G.map h)° ≫ φ c) ≫ F.map k
          ⊑ (φ a ≫ (F.map h)°) ≫ F.map k := comp_mono_right hstep_h _
        _ = φ a ≫ ((F.map h)° ≫ F.map k) := Cat.assoc _ _ _
        _ = φ a ≫ F.map (h° ≫ k) := by rw [hFcomp]
        _ = φ a ≫ F.map R := by rw [← hR]
    rw [p1]; exact p2

end Theorem52

/-! ## Sliding a family past a composite -/

section MonotonicComp

variable {𝒜 : Type u₁} [Allegory.{v₁} 𝒜]

/-- **B&dM §5.7**: monotonicity COMPOSES — if `T` slides right past `R` and past `S`, it
    slides past `R ≫ S`.  The endo case `Ta = Tb = Tc` is this theorem instantiated, not a
    separate one. -/
public theorem monotonic_comp {a b c : 𝒜} {Ta : a ⟶ a} {Tb : b ⟶ b} {Tc : c ⟶ c}
    {R : a ⟶ b} {S : b ⟶ c} (hR : Ta ≫ R ⊑ R ≫ Tb) (hS : Tb ≫ S ⊑ S ≫ Tc) :
    Ta ≫ (R ≫ S) ⊑ (R ≫ S) ≫ Tc :=
  calc Ta ≫ (R ≫ S) = (Ta ≫ R) ≫ S := (Cat.assoc _ _ _).symm
    _ ⊑ (R ≫ Tb) ≫ S := comp_mono_right hR S
    _ = R ≫ (Tb ≫ S) := Cat.assoc _ _ _
    _ ⊑ R ≫ (S ≫ Tc) := comp_mono_left R hS
    _ = (R ≫ S) ≫ Tc := (Cat.assoc _ _ _).symm

example {a : 𝒜} {T : a ⟶ a} {R S : a ⟶ a} (hR : T ≫ R ⊑ R ≫ T) (hS : T ≫ S ⊑ S ≫ T) :
    T ≫ (R ≫ S) ⊑ (R ≫ S) ≫ T := monotonic_comp hR hS

end MonotonicComp

/-! ## Sliding a family past a union -/

section MonotonicUnion

-- Needs the distributive layer: `∪` and composition's distribution over it on BOTH sides.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

/-- Monotonicity is closed under UNION — the `∪` member of the family whose `≫` member is
    `monotonic_comp` and whose functor member is `Relator.map_monotonic`; B&dM §7.2 builds its
    algebras from these.  The INTERSECTION case is FALSE: after `Ta ≫ (X ∩ Y) ⊑ (X ≫ Tb) ∩
    (Y ≫ Tb)` the last step would need `(X ≫ Tb) ∩ (Y ≫ Tb) ⊑ (X ∩ Y) ≫ Tb`, the wrong
    direction of semi-distributivity. -/
public theorem monotonic_union {a b : 𝒜} {Ta : a ⟶ a} {Tb : b ⟶ b} {X Y : a ⟶ b}
    (hX : Ta ≫ X ⊑ X ≫ Tb) (hY : Ta ≫ Y ⊑ Y ≫ Tb) :
    Ta ≫ (X ∪ Y) ⊑ (X ∪ Y) ≫ Tb :=
  calc Ta ≫ (X ∪ Y) = (Ta ≫ X) ∪ (Ta ≫ Y) := DistributiveAllegory.comp_union_distrib Ta X Y
    _ ⊑ (X ≫ Tb) ∪ (Y ≫ Tb) := union_mono hX hY
    _ = (X ∪ Y) ≫ Tb := (union_comp_distrib X Y Tb).symm

end MonotonicUnion

/-! ## The same closure rules for a WHOLE lax natural transformation

  `LaxNatural F G φ` is the pointwise inequality quantified over every `R`, so each rule is the
  pointwise argument run at every `R`.  The pointwise theorems themselves do NOT instantiate:
  they slide ONE arrow past `R` — the same `X` on both sides of `⊑` — whereas a lax natural
  transformation slides a FAMILY, `φ b` on the left and `φ a` on the right. -/

section LaxNaturalClosure

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]

/-- Lax naturality composes VERTICALLY: `ψ : H ⟶ G` followed by `φ : G ⟶ F` is lax natural
    `H ⟶ F`.  `monotonic_comp`'s argument at every `R`, with the two ends of the family,
    `ψ b ≫ φ b` and `ψ a ≫ φ a`, where it has one sliding arrow. -/
public theorem laxNatural_comp {F G H : Relator 𝒜 ℬ} {φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a}
    {ψ : ∀ a : 𝒜, H.obj a ⟶ G.obj a} (hψ : LaxNatural G H ψ) (hφ : LaxNatural F G φ) :
    LaxNatural F H (fun a => ψ a ≫ φ a) := fun {a b} R =>
  calc H.map R ≫ (ψ b ≫ φ b) = (H.map R ≫ ψ b) ≫ φ b := (Cat.assoc _ _ _).symm
    _ ⊑ (ψ a ≫ G.map R) ≫ φ b := comp_mono_right (hψ R) _
    _ = ψ a ≫ (G.map R ≫ φ b) := Cat.assoc _ _ _
    _ ⊑ ψ a ≫ (φ a ≫ F.map R) := comp_mono_left _ (hφ R)
    _ = (ψ a ≫ φ a) ≫ F.map R := (Cat.assoc _ _ _).symm

/-- A relator on the OUTSIDE carries a lax natural transformation to one between the
    composites: `K ∘ φ : K ∘ G ⟶ K ∘ F`.  `Relator.map_monotonic`'s argument at every `R`
    (`map_mono` read through `map_comp` on both sides), with `K.map (φ b)` and `K.map (φ a)`
    where it has one sliding arrow. -/
public theorem laxNatural_map {𝒞 : Type u₃} [Allegory.{v₃} 𝒞] {F G : Relator 𝒜 ℬ}
    {φ : ∀ a : 𝒜, G.obj a ⟶ F.obj a} (K : Relator ℬ 𝒞) (h : LaxNatural F G φ) :
    LaxNatural (Relator.comp F K) (Relator.comp G K) (fun a => K.map (φ a)) := fun {_ _} R => by
  have := K.map_mono (h R); rwa [K.map_comp, K.map_comp] at this

end LaxNaturalClosure

section LaxNaturalUnion

-- Needs the distributive layer in the TARGET allegory only: `∪` and its two distribution laws.
variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [DistributiveAllegory ℬ]

/-- Lax naturality is closed under UNION — `monotonic_union`'s argument at every `R`, with
    `φ b ∪ ψ b` and `φ a ∪ ψ a` where it has one sliding arrow.  As there, the INTERSECTION
    case is not available: it would need `(φ a ≫ F.map R) ∩ (ψ a ≫ F.map R) ⊑ (φ a ∩ ψ a) ≫
    F.map R`, the wrong direction of semi-distributivity. -/
public theorem laxNatural_union {F G : Relator 𝒜 ℬ} {φ ψ : ∀ a : 𝒜, G.obj a ⟶ F.obj a}
    (hφ : LaxNatural F G φ) (hψ : LaxNatural F G ψ) :
    LaxNatural F G (fun a => φ a ∪ ψ a) := fun {a b} R =>
  calc G.map R ≫ (φ b ∪ ψ b) = (G.map R ≫ φ b) ∪ (G.map R ≫ ψ b) :=
        DistributiveAllegory.comp_union_distrib _ _ _
    _ ⊑ (φ a ≫ F.map R) ∪ (ψ a ≫ F.map R) := union_mono (hφ R) (hψ R)
    _ = (φ a ∪ ψ a) ≫ F.map R := (union_comp_distrib _ _ _).symm

end LaxNaturalUnion

/-! ## The closure rules packaged: monotone relations form a category

  `monotonic_comp` and the two unit laws of `𝟙` are exactly what a category needs, so the
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
-- semi-distributivity (`monotonic_union`), and `°` slides the order the wrong way (`recip_slides`).
/-- Monotone relations form a CATEGORY: `𝟙` is monotone because `a.ord ≫ 𝟙 = a.ord = 𝟙 ≫ a.ord`,
    and composition is `monotonic_comp`. -/
@[expose] public instance ordObjCat : Cat.{v₁} (OrdObj 𝒜) where
  Hom a b := MonoHom a b
  id a := ⟨𝟙 a.carrier, by rw [Cat.comp_id, Cat.id_comp]; exact le_refl _⟩
  comp X Y := ⟨X.1 ≫ Y.1, monotonic_comp X.2 Y.2⟩
  id_comp X := Subtype.ext (Cat.id_comp X.1)
  comp_id X := Subtype.ext (Cat.comp_id X.1)
  assoc X Y Z := Subtype.ext (Cat.assoc X.1 Y.1 Z.1)

/-- The hom-sets are POSETS, ordered pointwise by `⊑` on the underlying relations. -/
@[expose] public def MonoHom.le {a b : OrdObj 𝒜} (X Y : MonoHom a b) : Prop := X.1 ⊑ Y.1

/-- Reflexivity is the underlying `le_refl`; `MonoHom.le` adds no condition to it. -/
public theorem MonoHom.le_refl {a b : OrdObj 𝒜} (X : MonoHom a b) : X.le X := Freyd.Alg.le_refl X.1

/-- `calc` support, and transitivity: the underlying `le_trans`. -/
public instance {a b : OrdObj 𝒜} :
    Trans (α := MonoHom a b) MonoHom.le MonoHom.le MonoHom.le where
  trans := Freyd.Alg.le_trans

/-- Antisymmetry, from `le_antisymm` on the underlying relations: two monotone relations ordered
    both ways have equal `.val`, and a `MonoHom` is its `.val` (`Subtype.ext`).  With `le_refl`
    and `le_trans` this makes each hom-set a POSET, not merely a preorder. -/
public theorem MonoHom.le_antisymm {a b : OrdObj 𝒜} {X Y : MonoHom a b} (hXY : X.le Y)
    (hYX : Y.le X) : X = Y := Subtype.ext (Freyd.Alg.le_antisymm hXY hYX)

/-- Composition is a POSET MAP in both arguments — `comp_mono_right` then `comp_mono_left` on the
    `.val`s.  This and the previous theorem are what "`OrdObj 𝒜` is enriched over posets" asserts:
    hom-sets are posets AND `≫` is monotone. -/
public theorem MonoHom.comp_mono {a b c : OrdObj 𝒜} {X X' : a ⟶ b} {Y Y' : b ⟶ c}
    (hX : MonoHom.le X X') (hY : MonoHom.le Y Y') : MonoHom.le (X ≫ Y) (X' ≫ Y') := by
  show X.1 ≫ Y.1 ⊑ X'.1 ≫ Y'.1
  exact Freyd.Alg.le_trans (comp_mono_right hX Y.1) (comp_mono_left X'.1 hY)

/-- Reciprocating `Ta ≫ X ⊑ X ≫ Tb` gives exactly this, and `°` being an order-isomorphism and
    an involution, this is ALL the hypothesis says about `X°`.  Monotonicity of `X°` for any
    orders `S`, `S'` would read `S ≫ X° ⊑ X° ≫ S'` — the composites sit on the opposite sides of
    `⊑`, and flipping the orders to `Tb°`, `Ta°` does not move them.  So `°` leaves `MonoHom`. -/
public theorem recip_slides {a b : 𝒜} {Ta : a ⟶ a} {Tb : b ⟶ b} {X : a ⟶ b}
    (h : Ta ≫ X ⊑ X ≫ Tb) : X° ≫ Ta° ⊑ Tb° ≫ X° := by
  have hr := recip_mono h
  rwa [Allegory.recip_comp, Allegory.recip_comp] at hr

end OrdCat

section PairSlides

variable {𝒜 : Type u₁} [TabularUnitaryDivisionAllegory 𝒜]

/-- The FORK rule — and the exact contrast with `inter_not_monotonic`.  `⟨X,Y⟩` slides past
    `Ta×Tb` whenever `X` slides past `Ta` and `Y` past `Tb`: the two witnesses land in DIFFERENT
    components, so nothing forces them to agree, which is what the meet of two arrows `a ⟶ b`
    does force.  So `(a,Ta) × (b,Tb) := (P.p, Ta×Tb)` is a TENSOR on `OrdObj 𝒜` — not a
    CATEGORICAL product, since (5.6) makes `⟨X,Y⟩ ≫ outl = dom Y ≫ X`, which is `X` only when
    `Y` is entire. -/
public theorem pair_slides {a b c : 𝒜} (P : RelProd a b) {Tc : c ⟶ c} {Ta : a ⟶ a} {Tb : b ⟶ b}
    {X : c ⟶ a} {Y : c ⟶ b} (hX : Tc ≫ X ⊑ X ≫ Ta) (hY : Tc ≫ Y ⊑ Y ≫ Tb) :
    Tc ≫ P.pair X Y ⊑ P.pair X Y ≫ prodMap P P Ta Tb := by
  rw [RelProd.pair_prodMap]
  refine RelProd.le_pair_iff.mpr ⟨?_, ?_⟩
  · rw [Cat.assoc, RelProd.pair_outl]
    exact le_trans (comp_mono_left Tc (comp_mono_right (dom_coreflexive Y) X))
      (by rw [Cat.id_comp]; exact hX)
  · rw [Cat.assoc, RelProd.pair_outr]
    exact le_trans (comp_mono_left Tc (comp_mono_right (dom_coreflexive X) Y))
      (by rw [Cat.id_comp]; exact hY)

/-- The lax COPY law `R◁ ⊑ ◁(R×R)` is `pair_slides` at `X = Y = 𝟙` — copy IS `⟨𝟙,𝟙⟩` — so it gets
    no theorem of its own.  Its two hypotheses are `T ≫ 𝟙 ⊑ 𝟙 ≫ T`, i.e. `le_refl`. -/
example {a : 𝒜} (P : RelProd a a) {T : a ⟶ a} :
    T ≫ P.pair (𝟙 a) (𝟙 a) ⊑ P.pair (𝟙 a) (𝟙 a) ≫ prodMap P P T T :=
  pair_slides P (by rw [Cat.comp_id, Cat.id_comp]; exact le_refl T)
    (by rw [Cat.comp_id, Cat.id_comp]; exact le_refl T)

-- With `pair_slides` this makes `×` a BIFUNCTOR on `OrdObj 𝒜` — its TENSOR, not a categorical
-- product, for the (5.6) reason `pair_slides` gives.
/-- `X×Y` slides past `Ta×Tb` whenever `X` slides past `Ta` and `Y` past `Tb`: `prodMap_comp`
    flattens both composites — an EQUALITY, so nothing is dropped — and `prodMap_mono` then
    compares them componentwise. -/
public theorem prodMap_slides {a b a' b' : 𝒜} (P : RelProd a b) (Q : RelProd a' b')
    {Ta : a ⟶ a} {Tb : b ⟶ b} {Tc : a' ⟶ a'} {Td : b' ⟶ b'} {X : a ⟶ a'} {Y : b ⟶ b'}
    (hX : Ta ≫ X ⊑ X ≫ Tc) (hY : Tb ≫ Y ⊑ Y ≫ Td) :
    prodMap P P Ta Tb ≫ prodMap P Q X Y ⊑ prodMap P Q X Y ≫ prodMap Q Q Tc Td := by
  rw [prodMap_comp, prodMap_comp]
  exact prodMap_mono hX hY

end PairSlides

section JuncSlides

-- Only `DistributiveAllegory`: unlike the fork, the co-fork needs no tabulation and no `dom`.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

/-- The CO-FORK rule, the coproduct's `pair_slides`: `[X,Y]` slides past `Tc` whenever `X` and
    `Y` do.  Where the fork pays for `⟨X,Y⟩ ≫ outl = dom Y ≫ X` — the lax copy law, `dom Y`
    dropped by `dom_coreflexive` — the co-fork's cancellation `sumMap_junc` is an EQUALITY, so
    this proof spends nothing beyond the two hypotheses. -/
public theorem junc_slides {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) {Ta : a₁ ⟶ a₁} {Tb : a₂ ⟶ a₂}
    {Tc : c ⟶ c} {X : a₁ ⟶ c} {Y : a₂ ⟶ c} (hX : Ta ≫ X ⊑ X ≫ Tc) (hY : Tb ≫ Y ⊑ Y ≫ Tc) :
    sumMap C C Ta Tb ≫ junc C X Y ⊑ junc C X Y ≫ Tc := by
  rw [sumMap_junc, junc_comp]
  exact junc_mono C hX hY

/-- The first injection is monotone, and STRICTLY so: `u₁ ≫ (Ta+Tb) = Ta ≫ u₁` on the nose,
    since `(Ta+Tb)` is by definition the junc whose first branch is `Ta ≫ u₁`. -/
public theorem u₁_slides {s a₁ a₂ : 𝒜} (C : Coproduct s a₁ a₂) (Ta : a₁ ⟶ a₁) (Tb : a₂ ⟶ a₂) :
    Ta ≫ C.u₁ = C.u₁ ≫ sumMap C C Ta Tb :=
  (u₁_junc C (Ta ≫ C.u₁) (Tb ≫ C.u₂)).symm

/-- The second injection, likewise an equality. -/
public theorem u₂_slides {s a₁ a₂ : 𝒜} (C : Coproduct s a₁ a₂) (Ta : a₁ ⟶ a₁) (Tb : a₂ ⟶ a₂) :
    Tb ≫ C.u₂ = C.u₂ ≫ sumMap C C Ta Tb :=
  (u₂_junc C (Ta ≫ C.u₁) (Tb ≫ C.u₂)).symm

end JuncSlides

section MonoHomUnion

-- Same distributive layer `monotonic_union` needs; the meet is absent, not merely unproved.
variable {𝒜 : Type u₁} [DistributiveAllegory 𝒜]

/-- Binary UNION of monotone relations, well defined by `monotonic_union`: the hom-sets are
    join-semilattices under `MonoHom.le`. -/
@[expose] public def MonoHom.union {a b : OrdObj 𝒜} (X Y : MonoHom a b) : MonoHom a b :=
  ⟨X.1 ∪ Y.1, monotonic_union X.2 Y.2⟩

end MonoHomUnion

end Freyd.Alg
