/-
  Bird & de Moor §5.7 in the set model: what the category of MONOTONE relations is NOT.

  `AOP.A5_7` builds `OrdObj`/`MonoHom`, their slide rules and the closure rules for whole lax
  natural transformations abstractly.  The facts that bound them — the hom-sets have no MEET,
  the tensor has no monotone MERGE, the meet of two lax natural transformations need not be one,
  and the terminal object is the EMPTY one — are refutations and concrete constructions, so they
  need a concrete allegory and live here, after `Rel(Set)`, instead of dragging the §6.1 set
  model into a §5.7 module.
-/
module

public import AOP.A5_7
public import AOP.A6_1_RelSet

namespace Freyd.Alg

-- `reducible` so instance search sees through `ordMerge.carrier.carrier` to `Option Bool`; without
-- it `decide` cannot find `DecidableEq` on the elements below.
/-- The order `{(p,r),(q,r)}` on `{p,q,r}` — spelled `p,q,r = none, some false, some true` — in
    which two DISTINCT elements improve to the SAME one.  Both refutations below turn on that. -/
@[expose, reducible] public def ordMerge : OrdObj RelSet.{0} :=
  ⟨⟨Option Bool⟩, fun x y => x ≠ some true ∧ y = some true⟩

-- `⊑` asserts a WITNESS exists: at `0` both `X` and `Y` have one (`p` for `X`, `q` for `Y`),
-- and being different they are exactly what the meet drops.
/-- **The `∩` case of `union_slides` is FALSE in its MONOTONICITY reading, not merely unproved.**
    Source `A = {0,1}` with `Ta = {(0,1)}` (spelled `0,1 = false,true`), target `ordMerge`,
    `X = {(0,p),(1,r)}`,
    `Y = {(0,q),(1,r)}`.  `X` and `Y` are monotone, but `X ∩ Y = {(1,r)}` is not: `Ta ≫ (X∩Y)`
    relates `0` to `r` while `(X∩Y) ≫ Tb` relates `0` to nothing. -/
public theorem inter_not_monotonic :
    ∃ (a b : OrdObj RelSet.{0}) (X Y : MonoHom a b),
      ¬ (a.ord ≫ (X.val ∩ Y.val) ⊑ (X.val ∩ Y.val) ≫ b.ord) := by
  refine ⟨⟨⟨Bool⟩, fun x y => x = false ∧ y = true⟩, ordMerge,
    ⟨fun x y => y = cond x (some true) none, ?_⟩,
    ⟨fun x y => y = cond x (some true) (some false), ?_⟩, ?_⟩
  · refine RelSet.le_iff.mpr ?_
    rintro x z ⟨y, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨none, rfl, by decide, rfl⟩
  · refine RelSet.le_iff.mpr ?_
    rintro x z ⟨y, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨some false, rfl, by decide, rfl⟩
  · intro h
    obtain ⟨y, ⟨hX, hY⟩, -⟩ := RelSet.le_iff.mp h false (some true) ⟨true, ⟨rfl, rfl⟩, rfl, rfl⟩
    exact absurd (hX.symm.trans hY) (by decide)

-- Two DIFFERENT elements improve to the SAME one, so the merge accepts them after improving and
-- refuses them before; copy has no such freedom, which is why `pair_slides` goes through.
/-- **The MERGE does not slide** — the other half of `inter_not_monotonic`, since `∩` is copy,
    run both, merge.  Over `ordMerge`, with `merge ((x,y),z)` iff `x=y=z`: `((p,q),r)` lies in
    `(T×T) ≫ merge` (take `p→r` and `q→r`, both landing on `r`) but not in `merge ≫ T`, which
    already needs `p=q`.  Contrast `pair_slides` at `𝟙`, the lax copy law, which holds. -/
public theorem merge_not_monotonic :
    ∃ (a : OrdObj RelSet.{0}) (merge : (relProd a.carrier a.carrier).p ⟶ a.carrier),
      ¬ (prodMap (relProd a.carrier a.carrier) (relProd a.carrier a.carrier) a.ord a.ord ≫ merge
          ⊑ merge ≫ a.ord) := by
  refine ⟨ordMerge, fun x z => x.1 = z ∧ x.2 = z, ?_⟩
  intro h
  rw [RelSet.prodMap_eq_rprodMap] at h
  obtain ⟨z, ⟨hp, hq⟩, -⟩ := RelSet.le_iff.mp h (none, some false) (some true)
    ⟨(some true, some true), ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩, rfl, rfl⟩
  exact absurd (hp.trans hq.symm) (by decide)

/-! ## The MEET of two lax natural transformations need not be one

  `inter_not_monotonic` does NOT settle this: it is two monotone relations between two FIXED
  ordered objects, not a family indexed by every object and satisfying the inequation at every
  `R`.  The refutation at that level needs actual relators and actual families, and it cannot be
  found at `F = G = Relator.idRelator`: there the inequation at `R : 1 ⟶ A` reads
  `R ≫ φ A ⊑ φ 1 ≫ R`, so `φ 1 = 𝟘` empties every `φ A`, while `φ 1 = 𝟙` makes every `φ A`
  coreflexive (take `R` a singleton), and then the inequation at `R : A ⟶ 1` forces `𝟙 A ⊑ φ A`.
  Only `𝟘` and `𝟙` are left, and `𝟘 ∩ 𝟙 = 𝟘` is one of them.  `Δ` is the first relator with room
  for a counterexample. -/

/-- `Δ`'s action is the pointwise `R×R` — `prodMap_eq_rprodMap` read at a pair of points. -/
private theorem delta_map_apply {a b : RelSet.{0}} (R : a ⟶ b)
    (p : a.carrier × a.carrier) (q : b.carrier × b.carrier) :
    (Δ RelSet.{0}).map R p q ↔ (R p.1 q.1 ∧ R p.2 q.2) := by
  rw [show (Δ RelSet.{0}).map R = RelSet.rprodMap R R from RelSet.prodMap_eq_rprodMap R R]
  exact Iff.rfl

-- Same shape as `inter_not_monotonic`: two DISTINCT elements improve to the SAME one, and the
-- meet is exactly what forbids the two components from being routed there independently.
/-- **The `∩` case of `union_slides` is FALSE in its LAX NATURALITY reading too.**  The two
    projections `π₁, π₂ : Δ ⟶ 1` are both lax natural (`outl_lax_natural`, `outr_lax_natural`) and
    their meet is the diagonal `{((x,x),x)}`.  At `R = {(false,false),(true,false)}`, which merges
    both elements onto one, `((false,true),false)` lies in `(R×R) ≫ (π₁∩π₂)` — route both components
    to `false`, where the diagonal accepts them — but not in `(π₁∩π₂) ≫ R`, which already needs
    `false = true`.  The step that fails is the last one of `union_slides`'s calculation:
    `(π₁ ≫ R) ∩ (π₂ ≫ R) ⊑ (π₁ ∩ π₂) ≫ R` is semi-distributivity BACKWARDS. -/
public theorem laxNatural_inter_false :
    ∃ (F G : Relator RelSet.{0} RelSet.{0}) (φ ψ : ∀ a, G.obj a ⟶ F.obj a),
      LaxNatural F G φ ∧ LaxNatural F G ψ ∧ ¬ LaxNatural F G (fun a => φ a ∩ ψ a) := by
  refine ⟨Relator.idRelator RelSet.{0}, Δ RelSet.{0}, fun a => (relProd a a).outl,
    fun a => (relProd a a).outr, outl_lax_natural, outr_lax_natural, ?_⟩
  intro h
  let R : (⟨Bool⟩ : RelSet.{0}) ⟶ (⟨Bool⟩ : RelSet.{0}) := fun _ y => y = false
  obtain ⟨y, ⟨hl, hr⟩, -⟩ :=
    RelSet.le_iff.mp (h R) (false, true) false
      ⟨(false, false), (delta_map_apply R _ _).mpr ⟨rfl, rfl⟩, rfl, rfl⟩
  exact absurd (hl.symm.trans hr) (by decide)

/-- **The converse of a lax natural transformation need not be lax natural**, so `recip_oplax`
    (A5_7) is the whole truth about `φ°`.  `φ = π₂ : Δ ⟶ 1` and the same merging
    `R = {(false,false),(true,false)}`: `(true,(true,false))` lies in `R ≫ π₂°` — send `true` to
    `false`, which `π₂°` pairs with any first component — but not in `π₂° ≫ (R×R)`, which must
    fire `R` on the FIRST component too and so can only reach `false` there. -/
public theorem recip_not_laxNatural :
    ∃ (F G : Relator RelSet.{0} RelSet.{0}) (φ : ∀ a, G.obj a ⟶ F.obj a),
      LaxNatural F G φ ∧ ¬ LaxNatural G F (fun a => (φ a)°) := by
  refine ⟨Relator.idRelator RelSet.{0}, Δ RelSet.{0}, fun a => (relProd a a).outr,
    outr_lax_natural, ?_⟩
  intro h
  let R : (⟨Bool⟩ : RelSet.{0}) ⟶ (⟨Bool⟩ : RelSet.{0}) := fun _ y => y = false
  obtain ⟨q, -, hd⟩ := RelSet.le_iff.mp (h R) true (true, false) ⟨false, rfl, rfl⟩
  exact Bool.noConfusion ((delta_map_apply R q (true, false)).mp hd).1

/-- **Theorem 5.2 FAILS with its equality on maps weakened to an inclusion** (`LaxOnMaps`,
    A5_7).  `φ : Δ ⟶ 1` is DISTINCTNESS, `φ a = {((x,y),∗) : x ≠ y}`.  A map cannot separate
    what it received together, which is exactly its simplicity, so `(f×f) ≫ φ ⊑ φ`; a RELATION
    can, and at `R = ⊤ : 1 ⟶ Bool` the pair `((∗,∗),∗)` lies in `(R×R) ≫ φ Bool` — route the two
    components to `false` and to `true` — but not in `φ 1`, where `∗ = ∗`. -/
public theorem laxOnMaps_not_laxNatural :
    ∃ (F G : Relator RelSet.{0} RelSet.{0}) (φ : ∀ a, G.obj a ⟶ F.obj a),
      LaxOnMaps F G φ ∧ ¬ LaxNatural F G φ := by
  refine ⟨Relator.const (⟨Unit⟩ : RelSet.{0}), Δ RelSet.{0}, fun _ p _ => p.1 ≠ p.2, ?_, ?_⟩
  · intro a b f hf
    refine RelSet.le_iff.mpr ?_
    rintro p u ⟨q, hq, hne⟩
    obtain ⟨h1, h2⟩ := (delta_map_apply f p q).mp hq
    refine ⟨u, fun hp => hne (RelSet.le_iff.mp hf.2 q.1 q.2 ⟨p.1, h1, ?_⟩), rfl⟩
    rw [hp]; exact h2
  · intro h
    let R : (⟨Unit⟩ : RelSet.{0}) ⟶ (⟨Bool⟩ : RelSet.{0}) := fun _ _ => True
    obtain ⟨-, hne, -⟩ := RelSet.le_iff.mp (h R) ((), ()) ()
      ⟨(false, true), (delta_map_apply R _ _).mpr ⟨trivial, trivial⟩,
        by intro hEq; exact Bool.noConfusion hEq⟩
    exact hne rfl

/-! ## The two horizontal composites are genuinely DIFFERENT

  `laxNatural_hcomp_inner_first` sits below `laxNatural_hcomp_outer_first`, by the outer 2-cell's
  own inequation at the components `φ a`.  By `hcomp_eq_of_map_components` the gap can only open
  where some `φ a` is NOT a map, so the counterexample takes `φ` a NON-ENTIRE relation, held
  constant by CONSTANT relators — over which `LaxNatural` degenerates to `S ⊑ S` and any single
  arrow is a lax natural transformation. -/

/-- **Horizontal composition is not one operation.**  `F = G = ` the constant relator at `Bool`
    and `φ = S = {(true,true),(true,false)}`, non-entire; `L = Δ`, `K = 1`, `χ = outr`.  At
    `((false,true), true)`: `outr ≫ S` accepts — read the second component, `true`, and `S` fires
    — while `(S×S) ≫ outr` must fire `S` on the FIRST component too, and `S` is empty at
    `false`. -/
public theorem hcomp_inner_first_ne_outer_first :
    ∃ (F G K L : Relator RelSet.{0} RelSet.{0}) (φ : ∀ a, G.obj a ⟶ F.obj a)
      (χ : ∀ b, L.obj b ⟶ K.obj b), LaxNatural F G φ ∧ LaxNatural K L χ ∧
      (fun a => L.map (φ a) ≫ χ (F.obj a)) ≠ (fun a => χ (G.obj a) ≫ K.map (φ a)) := by
  refine ⟨Relator.const (⟨Bool⟩ : RelSet.{0}), Relator.const (⟨Bool⟩ : RelSet.{0}),
    Relator.idRelator RelSet.{0}, Δ RelSet.{0}, fun _ x _ => x = true,
    fun b => (relProd b b).outr,
    fun _ => by show 𝟙 _ ≫ _ ⊑ _ ≫ 𝟙 _; rw [Cat.id_comp, Cat.comp_id]; exact le_refl _,
    outr_lax_natural, ?_⟩
  intro h
  have h' : (Δ RelSet.{0}).map (fun (x _ : Bool) => x = true) ≫
        (relProd (⟨Bool⟩ : RelSet.{0}) ⟨Bool⟩).outr
      = (relProd (⟨Bool⟩ : RelSet.{0}) ⟨Bool⟩).outr ≫ fun (x _ : Bool) => x = true :=
    congrFun h (⟨Bool⟩ : RelSet.{0})
  have hmem : ((relProd (⟨Bool⟩ : RelSet.{0}) ⟨Bool⟩).outr ≫ fun (x _ : Bool) => x = true)
      (false, true) true := ⟨true, rfl, rfl⟩
  rw [← h'] at hmem
  obtain ⟨q, hq, -⟩ := hmem
  exact absurd ((delta_map_apply _ _ q).mp hq).1 (by decide)

/-- **`Relator.prod` is not a categorical PRODUCT.**  The `⊑` of `laxNatural_pair_outl` is
    STRICT: all three relators constant at `Bool`, `φ = 1` and `ψ = {(true,true),(true,false)}`,
    both lax natural, and `⟨φ,ψ⟩ ≫ outl = dom ψ` misses `(false,false)` because `ψ` is empty at
    `false`.  So the failure is of EXISTENCE — no lax natural transformation into `F×F'` has the
    two given components as its projections — not merely of uniqueness. -/
public theorem prod_not_categorical_product :
    ∃ (F F' G : Relator RelSet.{0} RelSet.{0}) (φ : ∀ x, G.obj x ⟶ F.obj x)
      (ψ : ∀ x, G.obj x ⟶ F'.obj x) (x : RelSet.{0}), LaxNatural F G φ ∧ LaxNatural F' G ψ ∧
      (relProd (F.obj x) (F'.obj x)).pair (φ x) (ψ x)
        ≫ (relProd (F.obj x) (F'.obj x)).outl ≠ φ x := by
  refine ⟨Relator.const (⟨Bool⟩ : RelSet.{0}), Relator.const (⟨Bool⟩ : RelSet.{0}),
    Relator.const (⟨Bool⟩ : RelSet.{0}), fun _ => 𝟙 (⟨Bool⟩ : RelSet.{0}), fun _ x _ => x = true,
    ⟨Bool⟩,
    fun _ => by show 𝟙 _ ≫ _ ⊑ _ ≫ 𝟙 _; rw [Cat.id_comp, Cat.comp_id]; exact le_refl _,
    fun _ => by show 𝟙 _ ≫ _ ⊑ _ ≫ 𝟙 _; rw [Cat.id_comp, Cat.comp_id]; exact le_refl _, ?_⟩
  rw [RelProd.pair_outl]
  show dom (fun (x _ : Bool) => x = true) ≫ 𝟙 (⟨Bool⟩ : RelSet.{0}) ≠ 𝟙 (⟨Bool⟩ : RelSet.{0})
  rw [Cat.comp_id]
  intro hEq
  have hd : (dom (fun (x _ : Bool) => x = true) : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩) false false := by
    rw [hEq]; rfl
  obtain ⟨-, _, hz, -⟩ := hd
  exact Bool.noConfusion hz

/-- The EMPTY object, carrying the only relation there is on `Empty`. -/
@[expose] public def ordEmpty : OrdObj RelSet.{0} := ⟨⟨Empty⟩, fun _ y => y.elim⟩

/-- `Rel(Set)`'s ONE-element object is not terminal — an arrow `a ⟶ 1` is a subset of `a`, not a
    single arrow — but the EMPTY object is, here and in `Rel(Set)` itself: any two relations
    `a ⟶ ∅` are equal by `funext`, and the monotonicity side condition is vacuous. -/
public theorem ordEmpty_terminal (a : OrdObj RelSet.{0}) :
    ∃ X : MonoHom a ordEmpty, ∀ Y : MonoHom a ordEmpty, Y = X :=
  ⟨⟨fun _ y => y.elim, RelSet.le_iff.mpr fun _ y => y.elim⟩,
   fun _ => Subtype.ext (funext fun _ => funext fun y => y.elim)⟩

/-! ## No EQUALIZERS, hence not REGULAR

  The counterexample is the note's: `A = {0,1}`, `R = ⊤`, `S = {(0,*)}`, where exactly THREE
  arrows out of the one-point object equalize — `∅ ⊂ {0} ⊂ {0,1}` — and an equalizer `E` would
  put the SUBSETS of `E` in bijection with them, which no power set is.

  Transporting it needs a SOURCE allegory over which a relator is just an object of the target
  and a lax natural transformation just an arrow.  `Relator.const` alone does NOT do that: it is
  faithful but not full, `LaT (const b) (const b')` being a family indexed by every object of the
  source rather than a single arrow.  The one-object one-arrow allegory does. -/

/-- The allegory with ONE object and ONE arrow.  Every relator out of it sends that arrow to an
    identity, so `LaxNatural` reads `X ⊑ X` and the LaT category over it is the target's own
    category of relations. -/
@[expose, reducible] public def UnitAlleg : Type := Unit

@[expose] public instance : Cat.{0} UnitAlleg where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[expose] public instance : Allegory.{0} UnitAlleg where
  recip _ := ()
  inter _ _ := ()
  recip_recip _ := rfl
  recip_comp _ _ := rfl
  recip_inter _ _ := rfl
  inter_idem _ := rfl
  inter_comm _ _ := rfl
  inter_assoc _ _ _ := rfl
  semidistrib _ _ _ := rfl
  modular _ _ _ := rfl

/-- Over `UnitAlleg` EVERY family is lax natural: the one arrow is the identity, both relators
    send it to an identity, and the inequation collapses to `φ ⊑ φ`. -/
public theorem unitAlleg_laxNatural {F G : Relator UnitAlleg RelSet.{0}}
    (φ : ∀ a : UnitAlleg, G.obj a ⟶ F.obj a) : LaxNatural F G φ := by
  intro a b R
  rw [show G.map R = 𝟙 (G.obj a) from G.map_id a, show F.map R = 𝟙 (F.obj a) from F.map_id a,
    Cat.id_comp, Cat.comp_id]
  exact le_refl _

/-- An arrow of `Rel(Set)` read as a lax natural transformation over `UnitAlleg`. -/
@[expose] public def unitLaT {F G : Relator UnitAlleg RelSet.{0}} (X : F.obj () ⟶ G.obj ()) :
    LaT F G := ⟨fun _ => X, unitAlleg_laxNatural (F := G) (G := F) (fun _ => X)⟩

/-- …and it is settled by that one component, `UnitAlleg` having one object. -/
public theorem unitLaT_ext {F G : Relator UnitAlleg RelSet.{0}} {φ ψ : LaT F G}
    (h : φ.1 () = ψ.1 ()) : φ = ψ :=
  Subtype.ext (funext fun _ => h)

/-- `R = ⊤` on `A = {0,1}`. -/
@[expose, reducible] public def boolTop : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun _ _ => True

/-- `S = {(0,*)}`, the relation defined at `0` only — the target is irrelevant, so `B := A`. -/
@[expose, reducible] public def boolFromFalse : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun x _ => x = false

/-- The three arrows `1 ⟶ A` that equalize `boolTop` and `boolFromFalse`: `∅ ⊂ {0} ⊂ {0,1}`. -/
@[expose, reducible] public def ptEmpty : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun _ _ => False

@[expose, reducible] public def ptFalse : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun _ y => y = false

@[expose, reducible] public def ptAll : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun _ _ => True

-- The count is the whole point: 3 is not a power of 2, so no set of subsets can match it.
/-- Those three are ALL of them: `h ≫ ⊤ = h ≫ S` says `h` meets `{0,1}` only if it meets `{0}`,
    which leaves `∅`, `{0}` and `{0,1}`. -/
public theorem equalizing_cases (h : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨Bool⟩)
    (he : h ≫ boolTop = h ≫ boolFromFalse) : h = ptEmpty ∨ h = ptFalse ∨ h = ptAll := by
  have hdown : ∀ z, h () z → h () false := by
    intro z hz
    have hR : (h ≫ boolTop) () true := ⟨z, hz, trivial⟩
    rw [he] at hR
    obtain ⟨w, hw, hwf⟩ := hR
    exact hwf ▸ hw
  by_cases hf : h () false
  · by_cases ht : h () true
    · refine Or.inr (Or.inr (RelSet.hom_ext fun u z => ⟨fun _ => trivial, fun _ => ?_⟩))
      cases z with
      | false => exact hf
      | true => exact ht
    · refine Or.inr (Or.inl (RelSet.hom_ext fun u z => ⟨fun hz => ?_, fun hz => ?_⟩))
      · cases z with
        | false => rfl
        | true => exact absurd hz ht
      · exact hz ▸ hf
  · exact Or.inl (RelSet.hom_ext fun u z => ⟨fun hz => absurd (hdown z hz) hf, False.elim⟩)

/-- **The LaT category has NO EQUALIZERS, so it is not REGULAR.**  With `φ = ⊤` and
    `ψ = {(0,*)}` on `A = {0,1}`, an equalizer `E` would make `x ↦ x ≫ e` a bijection from the
    arrows `1 ⟶ E` — the subsets of `E` — onto the three equalizing arrows `1 ⟶ A`.  The
    mediator `k₂` of `{0,1}` and the whole of `E` then have the same image, so the whole of `E`
    IS `k₂`; and the singleton `{y}` at a point `y` of `k₂` outside the mediator `k₁` of `{0}`
    also has image `{0,1}`, so `{y}` is the whole of `E` too — making `E` the single point `y`,
    which puts the point of `k₁` at `y` and contradicts `y ∉ k₁`. -/
public theorem laT_no_equalizer :
    ∃ (F : Relator UnitAlleg RelSet.{0}) (φ ψ : F ⟶ F),
      ¬ ∃ (E : Relator UnitAlleg RelSet.{0}) (e : E ⟶ F), e ≫ φ = e ≫ ψ ∧
        ∀ (C : Relator UnitAlleg RelSet.{0}) (h : C ⟶ F), h ≫ φ = h ≫ ψ →
          ∃ k : C ⟶ E, k ≫ e = h ∧ ∀ k' : C ⟶ E, k' ≫ e = h → k' = k := by
  refine ⟨Relator.const (⟨Bool⟩ : RelSet.{0}), unitLaT boolTop, unitLaT boolFromFalse, ?_⟩
  rintro ⟨E, e, heq, huniv⟩
  have he : e.1 () ≫ boolTop = e.1 () ≫ boolFromFalse :=
    congrArg (fun t : LaT E (Relator.const (⟨Bool⟩ : RelSet.{0})) => t.1 ()) heq
  -- everything factoring through `e` equalizes, `e` itself does
  have hcomp : ∀ x : (⟨Unit⟩ : RelSet.{0}) ⟶ E.obj (),
      (x ≫ e.1 ()) ≫ boolTop = (x ≫ e.1 ()) ≫ boolFromFalse := by
    intro x; rw [Cat.assoc, Cat.assoc, he]
  -- the universal property, read on the one-point test object
  have hmed : ∀ h : (⟨Unit⟩ : RelSet.{0}) ⟶ ⟨Bool⟩, h ≫ boolTop = h ≫ boolFromFalse →
      ∃ x : (⟨Unit⟩ : RelSet.{0}) ⟶ E.obj (),
        x ≫ e.1 () = h ∧ ∀ x', x' ≫ e.1 () = h → x' = x := by
    intro h hh
    obtain ⟨k, hk, hu⟩ := huniv (Relator.const (⟨Unit⟩ : RelSet.{0})) (unitLaT h) (unitLaT_ext hh)
    refine ⟨k.1 (),
      congrArg (fun t : LaT (Relator.const (⟨Unit⟩ : RelSet.{0}))
        (Relator.const (⟨Bool⟩ : RelSet.{0})) => t.1 ()) hk, fun x' hx' => ?_⟩
    exact congrArg (fun t : LaT (Relator.const (⟨Unit⟩ : RelSet.{0})) E => t.1 ())
      (hu (unitLaT x') (unitLaT_ext hx'))
  obtain ⟨k₁, hk₁, -⟩ := hmed ptFalse
    (RelSet.hom_ext fun u y => ⟨fun _ => ⟨false, rfl, rfl⟩, fun _ => ⟨false, rfl, trivial⟩⟩)
  obtain ⟨k₂, hk₂, hk₂u⟩ := hmed ptAll
    (RelSet.hom_ext fun u y => ⟨fun _ => ⟨false, trivial, rfl⟩, fun _ => ⟨false, trivial, trivial⟩⟩)
  -- the whole of `E` has the same image as `k₂`, hence IS `k₂`
  have htop : ((fun _ _ => True) : (⟨Unit⟩ : RelSet.{0}) ⟶ E.obj ()) ≫ e.1 () = ptAll := by
    refine RelSet.hom_ext fun u b => ⟨fun _ => trivial, fun _ => ?_⟩
    have hb : (k₂ ≫ e.1 ()) u b := by rw [hk₂]; exact trivial
    obtain ⟨z, -, hz⟩ := hb
    exact ⟨z, trivial, hz⟩
  -- a point `y` of `k₂` that `k₁` misses, and a point `x` that `k₁` has
  have hy : (k₂ ≫ e.1 ()) () true := by rw [hk₂]; exact trivial
  obtain ⟨y, -, hey⟩ := hy
  have hx : (k₁ ≫ e.1 ()) () false := by rw [hk₁]
  obtain ⟨x, hx₁, -⟩ := hx
  have hnky : ¬ k₁ () y := by
    intro hky
    have hmem : (k₁ ≫ e.1 ()) () true := ⟨y, hky, hey⟩
    rw [hk₁] at hmem
    exact Bool.noConfusion hmem
  -- the singleton `{y}` also has image `{0,1}`: it meets `{0,1}`, so it is neither `∅` nor `{0}`
  have hsing : ((fun _ z => z = y) : (⟨Unit⟩ : RelSet.{0}) ⟶ E.obj ()) ≫ e.1 () = ptAll := by
    have hmem : (((fun _ z => z = y) : (⟨Unit⟩ : RelSet.{0}) ⟶ E.obj ()) ≫ e.1 ()) () true :=
      ⟨y, rfl, hey⟩
    rcases equalizing_cases _ (hcomp fun _ z => z = y) with hc | hc | hc
    · rw [hc] at hmem; exact hmem.elim
    · rw [hc] at hmem; exact Bool.noConfusion hmem
    · exact hc
  have hxy : x = y := of_eq_true (congrFun (congrFun ((hk₂u _ hsing).trans (hk₂u _ htop).symm) ()) x)
  exact hnky (hxy ▸ hx₁)

/-- The empty type is `Rel(Set)`'s ZERO OBJECT: `𝟙 ∅ = 𝟘`, the hypothesis of
    `const_zero_terminal`/`const_zero_initial`.  So the constant relator at `∅` is a zero object
    of the LaT category over `Rel(Set)` — the abstract theorems need nothing of the set model
    beyond this one equation. -/
public theorem relSetEmpty_zero :
    𝟙 (⟨Empty⟩ : RelSet.{0}) = (𝟘 : (⟨Empty⟩ : RelSet.{0}) ⟶ ⟨Empty⟩) :=
  RelSet.hom_ext fun x _ => x.elim

end Freyd.Alg
