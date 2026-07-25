/-
  Freyd & Scedrov, *Categories and Allegories* §1.54
  Capitalization Lemma.

  §1.541: A framework ℱ of small (pre-)regular categories + faithful representations.
         ℱ = all small (pre-)regular categories satisfies the three conditions:
         (1) equivalence-invariant, (2) slice-closed (proved §1.53),
         (3) directed-union-closed.

  §1.544: For well-supported B ∈ A, A embeds faithfully in A/B.
  §1.545: Relative capitalization definition.
  §1.543: Capitalization Lemma.

  The Henkin-Lubkin representation theorem (§1.55) lives in `S1_55.lean`.
-/


import Freyd.S1_01
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_33
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_44
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_53
import Freyd.S1_543_Capitalization


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

variable [ht : HasTerminal 𝒞] [hp : HasBinaryProducts 𝒞] [hpull : HasPullbacks 𝒞]

/-! ## §1.544: A embeds faithfully in A/B for well-supported B

  The book describes interpreting A as a subcategory of A/B by sending
  A ↦ A × B (the product with B).  When B is well-supported, this
  functor is a faithful embedding. -/

/-- The "product with B" functor `(-)×B : 𝒞 → 𝒞`.  This is the object part of
    the book's embedding `A → A/B`, `C ↦ (C×B → B)`; on morphisms it sends
    `f` to `pair (fst ≫ f) snd`. -/
def prodRight (B : 𝒞) : 𝒞 → 𝒞 := fun C => prod C B

def prodRightFunctor (B : 𝒞) : Functor 𝒞 𝒞 where
  obj := prodRight B
  map {C D} f := pair (fst ≫ f) snd
  map_id C := by
    show pair (fst ≫ Cat.id C) snd = Cat.id (prod C B)
    rw [Cat.comp_id]
    exact (pair_uniq fst snd (Cat.id (prod C B)) (Cat.id_comp fst) (Cat.id_comp snd)).symm
  map_comp {C D E} f g := by
    show pair (fst ≫ f ≫ g) snd = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd
    symm
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
    · rw [Cat.assoc, snd_pair, snd_pair]

/-- **§1.544**: when `B` is well-supported, `(-)×B` SEPARATES MORPHISMS — the
    embedding `A → A/B` is faithful in Freyd's sense ("separates objects and, if
    `B` is well-supported, separates morphisms").  If `f×B = g×B`, projecting
    along `fst` gives `fst ≫ f = fst ≫ g`; and `fst : C×B → C` is a cover
    (`prod_fst_cover`), hence epic (`cover_epi`), so `f = g`. -/
theorem slice_embedding_separates [PullbacksTransferCovers 𝒞] (B : 𝒞) (hws : WellSupported B) :
    Embedding (prodRightFunctor B) := by
  intro C D f g h
  have e1 : (prodRightFunctor B).map f ≫ (fst : prod D B ⟶ D) = (fst : prod C B ⟶ C) ≫ f :=
    fst_pair ((fst : prod C B ⟶ C) ≫ f) snd
  have e2 : (prodRightFunctor B).map g ≫ (fst : prod D B ⟶ D) = (fst : prod C B ⟶ C) ≫ g :=
    fst_pair ((fst : prod C B ⟶ C) ≫ g) snd
  have hfst : (fst : prod C B ⟶ C) ≫ f = (fst : prod C B ⟶ C) ≫ g := by
    rw [← e1, ← e2, h]
  exact cover_epi (prod_fst_cover hws) hfst

/-! ## §1.545 Relative capitalization

  A ⊆ A* is a RELATIVE CAPITALIZATION if for every proper subobject
  B' ↣ B in A with B well-supported, there exists a point x: 1 → B
  in A* that does not factor through B'.  §1.546 constructs it by
  iterating the slice functor A → A/B for each well-supported B. -/

/-- A* is a relative capitalization of A. -/
def IsRelativeCapitalization [HasTerminal 𝒞] [HasImages 𝒞] : Prop :=
  ∀ (B : 𝒞) (B' : Subobject 𝒞 B)
,
    ∃ (x : one ⟶ B), ¬ Allows B' x

/-! ## §1.543 Capitalization Lemma

  If A is a small (pre-)regular category, there exists a capital
  (pre-)regular category Ā and a faithful representation A → Ā.

  Status of the proof in this formalization:
  • §1.544 (one slice step separates morphisms) is PROVED, Sorry-free:
    `slice_embedding_separates` — the keystone facts `cover_epi` (covers are
    right-cancellable) and `prod_fst_cover` (`fst : C×B → C` is a cover when B is
    well-supported) are in `S1_52.lean`.
  • §1.545 relative capitalization is DEFINED (`IsRelativeCapitalization`).

  The construction has been ASSEMBLED in `Freyd/Capitalization.lean` from the
  directed-colimit-of-categories machinery (`CatColimit`/`CatColimitRegular`):

  • The capitalization data is packaged as `CapData A` — a coherent directed system
    of pre-regular categories, faithful in its transitions, whose colimit is capital.
  • `Freyd.capitalization_of_capData` derives the capital pre-regular target `Ā`
    and the faithful representation `A → Ā = objIncl i₀ ∘ base` from a `CapData A`,
    SORRY-FREE, using `colimitPreRegular` (colimit is pre-regular) and the new
    `Freyd.Colim.stageInclFaithful` (the colimit stage-injection is a faithful
    functor — proved via `homInclObj_id` + `homInclObj_comp` + `homInclObj_injective`
    + `homInclObj_isIso_reflects`).
  • `Freyd.capData_exists` is now PROVEN Sorry-free (in `Freyd/CapDataWiring.lean`):
    the cofinal capitalizing tower (`A₀=A`, `A_{α+1}=(A_α)*`, limit stages as
    directed colimits) plus the §1.543 capital-closure.  It wires the §1.547 uniform
    successor (`uniformStep`), the cofinal `hstage`, and the capital fixpoint
    (`tower_capital_of_cofinal`); the §1.546 fibre-density core (`fibreDensity`) it
    consumes is likewise proven Sorry-free.

  Below, `capitalization_lemma` is the small case (object universe = morphism
  universe `u`, as is forced by the `CatSystem` colimit machinery and matches
  Freyd's "small" hypothesis), reduced to `capData_exists`. -/

-- `capitalization_lemma` is RELOCATED to `Freyd.CapDataWiring`:
-- it forwards to `capData_exists`, whose §1.543 discharge wires the §1.547 uniform successor, which
-- transitively imports this file — so it cannot live upstream here.  See
-- `Freyd.CapDataWiring.capitalization_lemma`, now PROVEN Sorry-free (axioms
-- `[propext, Classical.choice, Quot.sound]`).

/-! ## §1.534  Not well-supported ⟹ Δ does not reflect isos (hence not faithful)

  If B is not well-supported, there exists a proper subobject `U ↣ 1` through which
  `term B : B → 1` factors.  The underlying arrow of `Δ(U.arr) : Δ(U) → Δ(1)` in A/B
  is `pair (fst ≫ U.arr) snd : prod U.dom B → prod one B`, and this is iso
  (inverse: `pair (snd ≫ b) snd` where `b : B → U.dom`), while `U.arr` is not iso.
  Hence Δ = `prodRight B` (as endofunctor of 𝒞) does not reflect isos.

  The key step: `U.arr : U.dom ↣ one` monic + `fst ≫ U.arr = term(U.dom×B)` and
  `snd ≫ b ≫ U.arr = snd ≫ term B = term(U.dom×B)` force `fst = snd ≫ b` by monicity,
  which is exactly what makes `pair (snd ≫ b) snd` a right-inverse. -/

/-- **§1.534**: The underlying map `pair (fst ≫ U.arr) snd : prod U.dom B → prod one B`
    is an isomorphism when `b : B → U.dom` factors `term B` through `U.arr`. -/
theorem prodRight_map_subterm_iso {B : 𝒞} (U : Subobject 𝒞 (one (𝒞 := 𝒞)))
    (b : B ⟶ U.dom) (hb : b ≫ U.arr = term B) :
    IsIso ((prodRightFunctor B).map U.arr) := by
  -- `(prodRightFunctor B).map U.arr = pair (fst ≫ U.arr) snd : prod U.dom B → prod one B`
  -- Candidate inverse: `pair (snd ≫ b) snd : prod one B → prod U.dom B`
  -- Key: `fst = snd ≫ b` as maps `prod U.dom B → U.dom`, by monicity of U.arr
  have hkey : (fst : prod U.dom B ⟶ U.dom) = snd ≫ b :=
    U.monic fst (snd ≫ b) (by rw [Cat.assoc, hb]; exact (term_uniq _ _).symm)
  refine ⟨pair (snd ≫ b) snd, ?_, ?_⟩
  · -- f ≫ inv = id(prod U.dom B): `pair (fst ≫ U.arr) snd ≫ pair (snd ≫ b) snd = id`
    show pair (fst ≫ U.arr) snd ≫ pair (snd ≫ b) snd = Cat.id (prod U.dom B)
    have hid : Cat.id (prod U.dom B) = pair fst snd :=
      pair_uniq fst snd (Cat.id _) (Cat.id_comp fst) (Cat.id_comp snd)
    rw [hid, ← pair_uniq fst snd _ _ _]
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, ← hkey]
    · rw [Cat.assoc, snd_pair, snd_pair]
  · -- inv ≫ f = id(prod one B): `pair (snd ≫ b) snd ≫ pair (fst ≫ U.arr) snd = id`
    show pair (snd ≫ b) snd ≫ pair (fst ≫ U.arr) snd = Cat.id (prod one B)
    have hid : Cat.id (prod one B) = pair fst snd :=
      pair_uniq fst snd (Cat.id _) (Cat.id_comp fst) (Cat.id_comp snd)
    rw [hid, ← pair_uniq fst snd _ _ _]
    · -- fst: `(pair(snd≫b) snd ≫ pair(fst≫U.arr) snd) ≫ fst = (snd ≫ b) ≫ U.arr = snd ≫ term B = fst`
      rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc, hb]
      exact term_uniq _ _
    · rw [Cat.assoc, snd_pair, snd_pair]

/-- **§1.534**: `prodRight B` does not reflect isomorphisms when B is not well-supported.
    Concretely: `U.arr : U.dom → 1` is monic-not-iso but `(prodRight B).map U.arr` is iso. -/
theorem prodRight_not_reflects_iso {B : 𝒞} (U : Subobject 𝒞 (one (𝒞 := 𝒞)))
    (b : B ⟶ U.dom) (hb : b ≫ U.arr = term B) (hU : ¬ Subobject.IsEntire U) :
    ∃ (X Y : 𝒞) (f : X ⟶ Y), IsIso ((prodRightFunctor B).map f) ∧ ¬ IsIso f :=
  ⟨U.dom, one, U.arr, prodRight_map_subterm_iso U b hb, hU⟩

end Freyd
