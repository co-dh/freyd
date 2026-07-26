/-
  §1.61 (lax) — the STRICT INITIAL object of a FILTERED lax colimit of pre-logoi.

  Lax port of `Colim.colimitStrictInitial` (`ColimitPreLogos.lean`).  For a `LaxCatSystem` whose
  every stage `L.A i` is a `PreLogos` (§1.6) and whose transitions preserve the chosen stage
  strict-initial object `0_i` on the nose (`hinitpres`), the `objIncl`-image of one stage's strict
  initial `0_{i₀}` is a STRICT COTERMINATOR (strict initial) of the lax colimit `laxColimCat L hL`:
  every lax-colimit map INTO it is an iso.

  KEY SIMPLIFICATION over the strict version.  The lax colimit's objects are the BARE Σ-type
  `Obj L = Σ i, L.A i` — NOT a quotient.  So the codomain `objIncl L i₀ 0_{i₀} = ⟨i₀, 0_{i₀}⟩` is
  literal, and a germ representative `f₀ : L.F a.2.1 xX ⟶ L.F a.2.2 0_{i₀}` of a map into it has its
  codomain `L.F a.2.2 0_{i₀}` EQUAL (on the nose, `hinitpres a.2.2`) to the stage strict-initial
  `0_{a.1}`.  Hence NO push to a common stage `M'` is needed (the strict proof's object-alignment
  `objIncl_eq_commonStage`/`colimHom_as_homInclObj` collapses): cast `f₀` to a map into `0_{a.1}`,
  which is iso by `any_map_to_zero_is_iso` (§1.61); `isIso_of_castHom` strips the cast to `IsIso f₀`,
  whose inverse-and-equations feed `homInclL_isIso_of_rep` (`LaxColimitPreReg.lean`) to lift the
  stage iso to the colimit.

  Mathlib-free; built on `Freyd.LaxColimitPreReg` + the §1.61 strict-initial API.
-/
import Freyd.S1_543_LaxColimitPreReg
import Freyd.S1_61

open Freyd
open Freyd.Colim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- `castHom` reflects isomorphisms (it is a transport along object equalities).  Local copy of
    `Colim.isIso_of_castHom`, duplicated here to avoid importing the heavy §2.218 regular tower
    (`CatColimitRegular`) for a two-line generic utility. -/
private theorem isIso_of_castHom {𝒜 : Type w} [Cat.{w} 𝒜] {X Y X' Y' : 𝒜}
    (hX : X = X') (hY : Y = Y') (m : X ⟶ Y) (h : IsIso (castHom hX hY m)) : IsIso m := by
  subst hX; subst hY; exact h

/-- The chosen strict initial object of stage `i` (the minimal subobject of `1`, §1.61).  Lax
    analogue of `Colim.stageZero`. -/
noncomputable def stageZero (L : LaxCatSystem ι D) (hbot : ∀ i, PreLogos (L.A i)) (i : ι) : L.A i :=
  (minimal_subobject_of_one_is_coterminator (hbot i)).zero

/-- **General lax-colimit strict coterminator.**  If every transition sends a fibre object `Y` to a
    strict coterminator, its image in the lax colimit is a strict coterminator.  A map `g` into
    `objIncl i₀ Y` is a germ `homInclL xX Y a f₀`; its
    codomain `L.F a.2.2 Y` is a strict coterminator (`htrans a.2.2`), so `f₀` (a map into it) is iso,
    lifted to the colimit by `homInclL_isIso_of_rep`. -/
theorem laxColimStrictCot {ι : Type u} {D : Directed ι} (L : LaxCatSystem.{u, w} ι D)
    (hL : Coherent L) {i₀ : ι} (Y : L.A i₀)
    (htrans : ∀ {j : ι} (hij : D.le i₀ j), @StrictCoterminator (L.A j) (L.catA j) (L.F hij Y)) :
    letI : Cat (Obj L) := laxColimCat L hL
    @StrictCoterminator (Obj L) (laxColimCat L hL) (objIncl L i₀ Y) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro X g
  obtain ⟨jX, xX⟩ := X
  refine Quotient.inductionOn g (fun rep => ?_)
  obtain ⟨a, f₀⟩ := rep
  obtain ⟨g₀, h1, h2⟩ := htrans a.2.2 f₀
  exact homInclL_isIso_of_rep L hL xX Y a f₀ g₀ h1 h2
/-- **The lax colimit-zero brick.**  The `objIncl`-image of one stage's strict initial `0_{i₀}` is a
    STRICT COTERMINATOR (strict initial) of `laxColimCat L hL`: every lax-colimit map into it is an
    iso.  Lax port of `Colim.colimitStrictInitial`.

    The transition hypothesis is the UP-TO-ISO form `hinitstrict`: every transition `L.F hij` sends the
    chosen stage strict-initial `0_i` to a STRICT COTERMINATOR of stage `j` (NOT the on-the-nose object
    equality `L.F hij 0_i = 0_j`).  This is the form satisfied by the intended base-change transitions
    (`baseChangeObj`) of the §2.218 capitalization tower: pullback of a strict initial along any map is
    again strict-initial, but only up to iso, never as a chosen-object equality.  The `Eq` form implies
    this one (`strictCoterminator_of_eq` below), so existing callers that DO have an on-the-nose
    equality lose nothing.

    PROOF.  A map `g : X ⟶ objIncl L i₀ 0_{i₀}` is a germ; pick a representative `⟨a, f₀⟩` with
    `f₀ : L.F a.2.1 xX ⟶ L.F a.2.2 0_{i₀}` at an upper bound `a` of `(jX, i₀)`.  Its codomain
    `L.F a.2.2 0_{i₀}` is a STRICT COTERMINATOR of stage `a.1` (`hinitstrict a.2.2`), so `f₀` — a map
    INTO a strict coterminator — is iso directly.  Its inverse-and-equations feed
    `homInclL_isIso_of_rep` to lift the stage iso to the colimit. -/
theorem laxColimStrictInitial (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) [Nonempty ι]
    (hbot : ∀ i, PreLogos (L.A i))
    (hinitstrict : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (L.A j) (L.catA j) (L.F hij (stageZero L hbot i)))
    (i₀ : ι) :
    letI : Cat (Obj L) := laxColimCat L hL
    StrictCoterminator (objIncl L i₀ (stageZero L hbot i₀)) :=
  laxColimStrictCot L hL (stageZero L hbot i₀) (fun hij => hinitstrict hij)

/-- The on-the-nose equality form of `hinitstrict` implies the up-to-iso `StrictCoterminator` form:
    if `L.F hij 0_i = 0_j` then `L.F hij 0_i` is the chosen stage strict-initial `0_j`, which is a
    strict coterminator (`minimal_subobject_of_one_is_coterminator`).  Lets callers with an on-the-nose
    equality use `laxColimStrictInitial` unchanged. -/
theorem strictCoterminator_of_eq (L : LaxCatSystem.{u, w} ι D) (hbot : ∀ i, PreLogos (L.A i))
    {i j : ι} (hij : D.le i j) (e : L.F hij (stageZero L hbot i) = stageZero L hbot j) :
    @StrictCoterminator (L.A j) (L.catA j) (L.F hij (stageZero L hbot i)) := by
  rw [e]
  intro X f
  exact any_map_to_zero_is_iso (hbot j) f

end Freyd.LaxColim
