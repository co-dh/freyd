/-
  Bird & de Moor, *Algebra of Programming* §7.3 — is `choose` monotonicity an EQUALITY?

  `A7_3_Party.choose_monotonic` proves `(R×R) ≫ choose ⊑ choose ≫ R` (B&dM p.177,
  "left as a simple exercise").  The `⊑` is STRICT in general: the book's calculation
  (p.177, mirrored) is

      (R×R)choose = (R×R)(π₁∪π₂) = ⟨π₁R,π₂R⟩π₁ ∪ ⟨π₁R,π₂R⟩π₂
                  = Dom(π₂R)·π₁R ∪ Dom(π₁R)·π₂R ⊑ π₁R ∪ π₂R = choose·R

  and its ONE inequality step is `Dom ⊑ 1`, which sharpens to an equality exactly when
  `R` is ENTIRE (`Entire`, `Freyd.S2_10` §2.13).  This file builds the concrete product
  in `Rel(Set)` (`RelSet.prod`), exhibits the strictness witness — `Rel(Set)` on `Bool`
  with the partial relation `R = {(false, false)}`, where `((false, true), false)` lies
  in `choose ≫ R` but not in `(R×R) ≫ choose` — and proves the equality case abstractly
  for entire `R`.
-/
module

public import AOP.A7_3_Party
public import AOP.A6_1_RelSet

universe u

namespace Freyd.Alg

/-! ## 1.  The concrete relational product in `Rel(Set)` (§5.2 instantiated)

  `RelProd` (`AOP.A5_2`) is a tabulation of `topMor a b` by two maps; in `Rel(Set)` the
  legs are the graphs of the two product projections.  The two `Tabulates` conjuncts
  beyond `Map` are proven pointwise first so the structure literal stays flat. -/

public theorem RelSet.graph_fst_snd_topMor (a b : RelSet.{u}) :
    topMor a b = (graph (Prod.fst : a.carrier × b.carrier → a.carrier))° ≫
      (graph (Prod.snd : a.carrier × b.carrier → b.carrier)) := by
  apply hom_ext
  intro x y
  constructor
  · intro h
    exact ⟨(x, y), rfl, rfl⟩
  · intro h
    exact (le_iff.mp (topMor_max (a := a) (b := b) (R := fun _ _ => True))) x y trivial

public theorem RelSet.graph_fst_snd_joint (a b : RelSet.{u}) :
    (graph (Prod.fst : a.carrier × b.carrier → a.carrier)) ≫
        (graph (Prod.fst : a.carrier × b.carrier → a.carrier))°
      ∩ (graph (Prod.snd : a.carrier × b.carrier → b.carrier)) ≫
        (graph (Prod.snd : a.carrier × b.carrier → b.carrier))°
      = Cat.id (RelSet.mk (a.carrier × b.carrier)) := by
  apply hom_ext
  intro p q
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨a', ha1, ha2⟩
    rcases h2 with ⟨b', hb1, hb2⟩
    exact Prod.ext (ha1.symm.trans ha2) (hb1.symm.trans hb2)
  · intro h
    constructor
    · exact ⟨p.1, rfl, congrArg Prod.fst h⟩
    · exact ⟨p.2, rfl, congrArg Prod.snd h⟩

/-- The concrete product of `a` and `b` in `Rel(Set)`: the apex is the Lean product type and the
    legs are the graphs of `Prod.fst`, `Prod.snd`. -/
@[expose] public def RelSet.prod (a b : RelSet.{u}) : RelProd a b :=
  { p := RelSet.mk (a.carrier × b.carrier)
    outl := graph (Prod.fst : a.carrier × b.carrier → a.carrier)
    outr := graph (Prod.snd : a.carrier × b.carrier → b.carrier)
    tab := ⟨graph_map (Prod.fst), graph_map (Prod.snd), graph_fst_snd_topMor a b,
      graph_fst_snd_joint a b⟩ }

theorem RelSet.prod_outl_apply (a b : RelSet.{u}) (p : (a.carrier × b.carrier)) (x : a.carrier) :
    (RelSet.prod a b).outl p x = (x = p.1) := rfl

theorem RelSet.prod_outr_apply (a b : RelSet.{u}) (p : (a.carrier × b.carrier)) (y : b.carrier) :
    (RelSet.prod a b).outr p y = (y = p.2) := rfl

/-- Pointwise computation of `pair` in `Rel(Set)`: `⟨R,S⟩ x p = R x p.1 ∧ S x p.2`. -/
theorem RelSet.prod_pair_apply {a b c : RelSet.{u}} (R : c ⟶ a) (S : c ⟶ b)
    (x : c.carrier) (p : a.carrier × b.carrier) :
    (RelSet.prod a b).pair R S x p = (R x p.1 ∧ S x p.2) := by
  rw [RelProd.pair]
  apply propext
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨y, hy, hy1⟩
    rcases h2 with ⟨z, hz, hz1⟩
    constructor
    · exact hy1 ▸ hy
    · exact hz1 ▸ hz
  · intro h
    constructor
    · exact ⟨p.1, h.1, rfl⟩
    · exact ⟨p.2, h.2, rfl⟩

/-! ## 2.  The counterexample: the inclusion is STRICT -/

/-- The witness relation: `R = {(false, false)}` on `Bool`, undefined at `true`. -/
@[expose] public def chooseWitness : (RelSet.mk Bool) ⟶ (RelSet.mk Bool) :=
  fun x y => x = false ∧ y = false

/-- `chooseWitness` is NOT entire — it is undefined at `true`. -/
public theorem chooseWitness_not_entire : ¬ Entire chooseWitness := by
  intro h
  rcases RelSet.entire_total h true with ⟨y, hy⟩
  simp [chooseWitness] at hy

/-- **The answer**: `choose`'s monotonicity is a STRICT inclusion in general — the `⊑` of
    `choose_monotonic` cannot be strengthened to `=`.  Witness: `Rel(Set)` on `Bool` with the
    partial relation `chooseWitness`. -/
public theorem choose_monotonic_strict :
    prodMap (RelSet.prod _ _) (RelSet.prod _ _) chooseWitness chooseWitness
        ≫ choose (RelSet.prod (RelSet.mk Bool) (RelSet.mk Bool))
      ≠ choose (RelSet.prod (RelSet.mk Bool) (RelSet.mk Bool)) ≫ chooseWitness := by
  let P : RelProd (RelSet.mk Bool) (RelSet.mk Bool) :=
    RelSet.prod (RelSet.mk Bool) (RelSet.mk Bool)
  intro h
  have hR : (choose P ≫ chooseWitness) (false, true) false := by
    rw [choose, RelSet.comp_apply]
    refine ⟨false, ?_, ?_⟩
    · change P.outl (false, true) false ∨ P.outr (false, true) false
      left
      rfl
    · rw [chooseWitness]
      exact ⟨rfl, rfl⟩
  rw [← h] at hR
  rw [prodMap, RelSet.comp_apply] at hR
  rcases hR with ⟨q, hq, _⟩
  rw [RelSet.prod_pair_apply, RelSet.comp_apply, RelSet.comp_apply] at hq
  -- the right leg forces its witness to be both `true` (by `outr`) and `false` (by `chooseWitness`)
  rcases hq.2 with ⟨y, hy, hy0⟩
  have hy1 : y = true := hy
  exact Bool.noConfusion (hy1.symm.trans hy0.1)

/-! ## 3.  The equality case: entire `R` -/

/-- When `R` is entire the `Dom` factors are `𝟙` and `choose_monotonic` becomes an EQUALITY.  The
    `Dom` factors of (5.6)/(5.7) become `𝟙` by `entire_comp` (`S2_10` §2.13): both legs of `P` are
    maps, hence entire, and so is `R`. -/
public theorem choose_monotonic_eq_of_entire {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {a : 𝒜}
    (P : RelProd a a) (R : a ⟶ a) (hR : Entire R) :
    prodMap P P R R ≫ choose P = choose P ≫ R := by
  calc
    prodMap P P R R ≫ choose P
        = (P.pair (P.outl ≫ R) (P.outr ≫ R)) ≫ (P.outl ∪ P.outr) := rfl
    _ = (P.pair (P.outl ≫ R) (P.outr ≫ R) ≫ P.outl) ∪
        (P.pair (P.outl ≫ R) (P.outr ≫ R) ≫ P.outr) := by
          rw [DistributiveAllegory.comp_union_distrib]
    _ = (dom (P.outr ≫ R) ≫ (P.outl ≫ R)) ∪ (dom (P.outl ≫ R) ≫ (P.outr ≫ R)) := by
          rw [RelProd.pair_outl, RelProd.pair_outr]
    _ = (Cat.id P.p ≫ (P.outl ≫ R)) ∪ (Cat.id P.p ≫ (P.outr ≫ R)) := by
          rw [entire_comp P.tab.2.1.1 hR, entire_comp P.tab.1.1 hR]
    _ = (P.outl ≫ R) ∪ (P.outr ≫ R) := by
          rw [Cat.id_comp, Cat.id_comp]
    _ = (P.outl ∪ P.outr) ≫ R := by
          rw [← union_comp_distrib]
    _ = choose P ≫ R := rfl

end Freyd.Alg
