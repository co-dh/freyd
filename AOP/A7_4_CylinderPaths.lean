/-
  Bird & de Moor, *Algebra of Programming* §7.4 (book pp. 180-184) — the three cylinder beads that
  are natural in the ELEMENT TYPE, which is the index `AOP.A7_4_Cylinder` does not have: it fixes
  one `H` and one `I : InitialAlgebra H`, so `generate`'s tail `N(cp P(α))` is an algebra at the
  single carrier `LA` and no square in the element type can be stated there.  Here `L` is the
  repo's list relator, which has an initial algebra at EVERY object, and the three beads are
  concrete relations, as in `AOP.A7_4_CylinderBeads`:

  - `zip  : F(N(x))⟶N(F(x))` at an ARBITRARY relator `F` — LAX, and lax is all that is proved.
  - `⦇generate⦈ : L(N(x))⟶N(E(L(x)))` — LAX, by induction on the list of columns.
  - `paths ≜ ⦇generate⦈ setify union : L(N(x))⟶E(L(x))` — LAX, the three squares composed.

  `zip` AT AN ARBITRARY `F`.  The book's `zip : F(NA,NB)⟶N(F(A,B))` distributes the tuple out of
  BOTH slots of the base bifunctor, so at one element type it is the unary `F(N(x))⟶N(F(x))` with
  `F(x) ≜ F(x,x)`.  That arrow exists for every relator: `N(F x)` is an `n`-fold product, so the
  `k`-th row can only be `F(π_k)`, and `zip ≜ ⟨F(π₁),…,F(π_n)⟩` is the fork of those.  Its square
  is LAX and no more is claimed: the lax half needs only `N(R)π_k ⊑ π_k R`, which is where the
  equality goes — the tuple relator demands an `R`-image in every OTHER row as well.  Strictness
  does hold at the product summand `F(x,y) = x×y`, which is `zipT` (`AOP.A7_4_CylinderBeads`,
  `zip_natural`); at a general `F` it is not proved here and the note's row does not claim it.

  `L` IS THE REPO'S LIST, so `α = [nil,cons]` where the book has `[wrap,cons]` on non-empty
  lists: the fold's base case is the EMPTY path rather than the one-square path.  On a cylinder
  of one or more columns the two agree — `genFn (cons c nil) k = {[c k]}` either way — and the
  extra empty column costs the naturality squares nothing.

  Composition is diagram order (`≫`) throughout: B&dM `X·Y` = Freyd `Y ≫ X`.
-/
module

public import AOP.A7_4_CylinderBeads
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Tuple

open Freyd CL ListRel

variable {a b : RelSet.{0}} {A B : Type} {n : Nat}

/-! ## `zip` at an arbitrary relator -/

/-- `π_k : N(x)⟶x`, the `k`-th row of a tuple. -/
@[expose] public def tproj (k : Fin n) : dTuple n a ⟶ a := graph fun t => t k

/-- **`N(R)π_k ⊑ π_k R`**, and NOT an equality: the left side demands an `R`-image in every other
    row too, so a `t` whose row `j ≠ k` has no `R`-image is related by the right side only. -/
public theorem tupleP_comp_tproj (R : a ⟶ b) (k : Fin n) :
    tupleP n R ≫ tproj k ⊑ tproj k ≫ R := by
  refine le_iff.mpr fun t y h => ?_
  obtain ⟨t', hR, rfl⟩ := h
  exact ⟨t k, rfl, hR k⟩

/-- Choice over a FINITE index is constructive — the tuple is assembled one row at a time — so the
    `zip` square below rests on no `Classical.choice`. -/
public theorem tuple_of_forall_exists {Z : Type} {m : Nat} {P : Fin m → Z → Prop}
    (h : ∀ k, ∃ z, P k z) : ∃ v : Fin m → Z, ∀ k, P k (v k) := by
  induction m with
  | zero => exact ⟨fun k => k.elim0, fun k => k.elim0⟩
  | succ m ih =>
      obtain ⟨z, hz⟩ := h 0
      obtain ⟨v, hv⟩ := ih (fun k => h k.succ)
      refine ⟨Fin.cases z v, fun k => ?_⟩
      induction k using Fin.cases with
      | zero => exact hz
      | succ i => exact hv i

/-- **`zip ≜ ⟨F(π₁),…,F(π_n)⟩ : F(N(x))⟶N(F(x))`** at an ARBITRARY relator `F`: the `k`-th row of
    the answer is `F` applied to the `k`-th row of the argument, which is the only arrow into an
    `n`-fold product there is. -/
@[expose] public def zipF (F : Relator RelSet.{0} RelSet.{0}) :
    F.obj (dTuple n a) ⟶ dTuple n (F.obj a) :=
  fun w u => ∀ k, F.map (tproj k) w (u k)

/-- **`zip` is lax natural at every relator `F`**: `F(N(R)) zip ⊑ zip N(F(R))`.  Row by row it is
    `F` of `tupleP_comp_tproj`, and the rows are then collected into one tuple by finite choice.
    Only the lax half: the equality already fails one functor down, at `N(R)π_k ⊑ π_k R`. -/
public theorem zipF_lax_natural (F : Relator RelSet.{0} RelSet.{0}) (R : a ⟶ b) :
    F.map (tupleP n R) ≫ zipF (n := n) F ⊑ zipF F ≫ tupleP n (F.map R) := by
  refine le_iff.mpr fun w u h => ?_
  obtain ⟨w', hw', hu⟩ := h
  have key : ∀ k : Fin n, ∃ z, F.map (tproj k) w z ∧ F.map R z (u k) := by
    intro k
    have hslide : F.map (tupleP n R) ≫ F.map (tproj k) ⊑ F.map (tproj k) ≫ F.map R := by
      rw [← F.map_comp, ← F.map_comp]
      exact F.map_mono (tupleP_comp_tproj R k)
    exact le_iff.mp hslide w (u k) ⟨w', hw', hu k⟩
  obtain ⟨v, hv⟩ := tuple_of_forall_exists key
  exact ⟨v, fun k => (hv k).1, fun k => (hv k).2⟩

/-! ## `⦇generate⦈` -/

/-- **`⦇generate⦈` folded** (book p.181), `L(N(x))⟶N(E(L(x)))`: `generate` unfolded at a value is
    `F(𝟙,moves trans N(union)) zip N(cp P(α))` read pointwise — `moves trans N(union)` unions the
    path sets of every row (`moves` is every rotation), `zip` pairs the new column's row `k` with
    that union, and `N(cp P(α))` conses the square onto every path in it. -/
@[expose] public def genFn : ConsList Unit (Fin n → A) → Fin n → ConsList Unit A → Prop
  | ConsList.wrap _, _ => fun p => p = ConsList.wrap ()
  | ConsList.cons c cs, k => fun p => ∃ j q, genFn cs j q ∧ p = ConsList.cons (c k) q

/-- **cyl-defn**: `⦇generate⦈ : L(N(x))⟶N(E(L(x)))`, one path set per row of the cylinder. -/
@[expose] public def cataGenerate :
    dList (Fin n → A) ⟶ dTuple n (PowerAllegory.powerObj (dList A)) :=
  graph fun xs => fun k => genFn xs k

/-- The square at values: `L(N(R))`-related lists of columns fold to path sets that are
    Egli-Milner `L(R)`-related row by row.  The cons step needs both halves at every row `j`,
    because `generate` unions all of them before consing; the union of Egli-Milner related
    families is Egli-Milner related, and `cons` then carries `R` on the square and `L(R)` on the
    tail. -/
public theorem genFn_lax (R : dE A ⟶ dE B) :
    ∀ (xs : ConsList Unit (Fin n → A)) (ys : ConsList Unit (Fin n → B)),
      listP (tupleP n R) xs ys → ∀ k, powerRel (list R) (genFn xs k) (genFn ys k)
  | ConsList.wrap _, ConsList.wrap _, _, _ =>
      (powerRel_apply _ _ _).mpr
        ⟨by rintro p rfl; exact ⟨ConsList.wrap (), trivial, rfl⟩,
         by rintro p rfl; exact ⟨ConsList.wrap (), rfl, trivial⟩⟩
  | ConsList.wrap _, ConsList.cons _ _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h, _ => h.elim
  | ConsList.cons c cs, ConsList.cons d ds, h, k =>
      (powerRel_apply _ _ _).mpr
        ⟨by
          rintro p ⟨j, q, hq, rfl⟩
          obtain ⟨q', hRq, hq'⟩ := ((powerRel_apply _ _ _).mp (genFn_lax R cs ds h.2 j)).1 q hq
          exact ⟨ConsList.cons (d k) q', ⟨h.1 k, hRq⟩, ⟨j, q', hq', rfl⟩⟩,
         by
          rintro p ⟨j, q, hq, rfl⟩
          obtain ⟨q', hq', hRq⟩ := ((powerRel_apply _ _ _).mp (genFn_lax R cs ds h.2 j)).2 q hq
          exact ⟨ConsList.cons (c k) q', ⟨j, q', hq', rfl⟩, ⟨h.1 k, hRq⟩⟩⟩

/-- **`⦇generate⦈` is lax natural**: `L(N(R)) ⦇generate⦈ ⊑ ⦇generate⦈ N(P(L(R)))`.  `⦇generate⦈`
    is the graph of a function, so the square is `genFn_lax` at every row. -/
public theorem cataGenerate_lax_natural (R : dE A ⟶ dE B) :
    list (tupleP n R) ≫ cataGenerate ⊑ cataGenerate ≫ tupleP n (powerRel (list R)) := by
  refine le_iff.mpr fun xs u h => ?_
  obtain ⟨ys, hys, rfl⟩ := h
  exact ⟨fun k => genFn xs k, rfl, fun k => genFn_lax R xs ys hys k⟩

/-! ## `paths` -/

/-- **cyl-defn**: `paths ≜ ⦇generate⦈ setify union : L(N(x))⟶E(L(x))` — every path across the
    cylinder, the row it starts in forgotten. -/
@[expose] public def pathsRel :
    dList (Fin n → A) ⟶ PowerAllegory.powerObj (dList A) :=
  cataGenerate ≫ setify ≫ bigUnion

/-- **`paths` is lax natural**: `L(N(R)) paths ⊑ paths P(L(R))`.  The three squares of its
    definition in order — `⦇generate⦈` lax, `setify` lax at `P(L(R))`, and `union` strictly
    natural (`bigUnion_strict_relSet`), which is the one step that costs nothing. -/
public theorem paths_lax_natural (R : dE A ⟶ dE B) :
    list (tupleP n R) ≫ pathsRel ⊑ pathsRel ≫ powerRel (list R) := by
  calc list (tupleP n R) ≫ pathsRel
      = (list (tupleP n R) ≫ cataGenerate) ≫ setify ≫ bigUnion := by
        rw [pathsRel]; simp only [Cat.assoc]
    _ ⊑ (cataGenerate ≫ tupleP n (powerRel (list R))) ≫ setify ≫ bigUnion :=
        comp_mono_right (cataGenerate_lax_natural R) _
    _ = cataGenerate ≫ (tupleP n (powerRel (list R)) ≫ setify) ≫ bigUnion := by
        simp only [Cat.assoc]
    _ ⊑ cataGenerate ≫ (setify ≫ powerRel (powerRel (list R))) ≫ bigUnion :=
        comp_mono_left _ (comp_mono_right (setify_lax_natural (powerRel (list R))) _)
    _ = cataGenerate ≫ setify ≫ powerRel (powerRel (list R)) ≫ bigUnion := by
        simp only [Cat.assoc]
    _ = cataGenerate ≫ setify ≫ bigUnion ≫ powerRel (list R) := by
        rw [bigUnion_strict_relSet]
    _ = pathsRel ≫ powerRel (list R) := by rw [pathsRel]; simp only [Cat.assoc]

end Freyd.Alg.RelSet.Tuple
