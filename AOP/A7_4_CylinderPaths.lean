/-
  Bird & de Moor, *Algebra of Programming* §7.4 (book pp. 180-184) — the four cylinder beads that
  are natural in the ELEMENT TYPE, which is the index `AOP.A7_4_Cylinder` does not have: it fixes
  one `H` and one `I : InitialAlgebra H`, so `gen`'s tail `N(cp P(α))` is an algebra at the
  single carrier `LA` and no square in the element type can be stated there.  Here `L` is the
  repo's list relator, which has an initial algebra at EVERY object, and the three beads are
  concrete relations, as in `AOP.A7_4_CylinderBeads`:

  - `zip  : F(N(x))⟶N(F(x))` at an ARBITRARY relator `F` — LAX, and lax is all that is proved.
  - `cp   : F(E x)⟶E(F(x))` at the list base functor `F X = L + (E × X)` — STRICT, the one square
    here that is an equality.
  - `⦇gen⦈ : L(N(x))⟶N(E(L(x)))` — LAX, by induction on the list of columns.
  - `paths ≜ ⦇gen⦈ setify union : L(N(x))⟶E(L(x))` — LAX, the three squares composed.

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

/-! ## `cp` -/

/-- **`cp(inl d) = {inl d}`, `cp(e,S) = {(e,s) | s ∈ S}`** (book p.181): `cp ≜ frac(F(𝟙,∋),∋) :
    F(A,E B)⟶E(F(A,B))`, the cross product — the powerset pulled out of the base functor.  It is
    the second half of `gen`'s tail `N(cp P(α))`: `cp` turns a column paired with a SET of
    tails into the SET of pairs, and `P(α)` conses the column onto each of them.  At the repo's
    list functor `F X = L + (E × X)` the `𝟙` slot is the column `e`, so the first component is the
    same in every element of the answer; on the `L` summand there is no set to distribute and `cp`
    is the singleton. -/
@[expose] public def cp (L E : Type) {a : RelSet.{0}} :
    (F L E).obj (PowerAllegory.powerObj a) ⟶ PowerAllegory.powerObj ((F L E).obj a) :=
  graph fun w => match w with
    | Sum.inl d => fun y => y = Sum.inl d
    | Sum.inr p => fun y => ∃ s, p.2 s ∧ y = Sum.inr (p.1, s)

/-- **`cp` is natural, and it is STRICT**: `F(P(R)) cp = cp P(F(R))`.  On the `L` summand both
    sides relate `inl d` to the singleton `{inl d}` and to nothing else — `F(R)` moves no `inl`,
    so Egli-Milner pins the set.  On the product summand the first component is pinned by the
    `𝟙`, so a set the right side names is `{e}×S'` for `S' = {s' | (e,s') ∈ ·}`, and the two
    Egli-Milner halves read off `S` and `S'` are exactly `P(R)`'s.  Compare `zip_natural`
    (`AOP.A7_4_CylinderBeads`), strict for the same reason; the other cylinder beads are lax
    because they duplicate or merge rows, which `cp` never does. -/
public theorem cp_natural (L E : Type) (R : a ⟶ b) :
    (F L E).map (powerRel R) ≫ cp L E (a := b)
      = cp L E (a := a) ≫ powerRel ((F L E).map R) := by
  apply hom_ext
  intro w T
  cases w with
  | inl d =>
      constructor
      · rintro ⟨v, hv, hT⟩
        cases v with
        | inr q => exact hv.elim
        | inl d' =>
            cases hv
            have hTe : T = fun y : (Fobj L E b).carrier => y = Sum.inl d := hT
            subst hTe
            refine ⟨fun y => y = Sum.inl d, rfl, (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩⟩
            · rintro x rfl; exact ⟨Sum.inl d, rfl, rfl⟩
            · rintro y rfl; exact ⟨Sum.inl d, rfl, rfl⟩
      · rintro ⟨U, hU, hEM⟩
        have hUe : U = fun y : (Fobj L E a).carrier => y = Sum.inl d := hU
        subst hUe
        refine ⟨Sum.inl d, rfl, ?_⟩
        have hd : T (Sum.inl d) := by
          obtain ⟨y, hy, hTy⟩ := ((powerRel_apply _ _ _).mp hEM).1 (Sum.inl d) rfl
          cases y with
          | inr q => exact hy.elim
          | inl d' => cases hy; exact hTy
        show T = fun y : (Fobj L E b).carrier => y = Sum.inl d
        funext z
        refine propext ⟨fun hz => ?_, ?_⟩
        · obtain ⟨x, hx, hR⟩ := ((powerRel_apply _ _ _).mp hEM).2 z hz
          subst hx
          cases z with
          | inr q => exact hR.elim
          | inl d' => cases hR; rfl
        · rintro rfl; exact hd
  | inr p =>
      constructor
      · rintro ⟨v, hv, hT⟩
        cases v with
        | inl d => exact hv.elim
        | inr q =>
            obtain ⟨he, hS⟩ := hv
            have hTe : T = fun y : (Fobj L E b).carrier => ∃ s, q.2 s ∧ y = Sum.inr (q.1, s) := hT
            subst hTe
            refine ⟨fun y => ∃ s, p.2 s ∧ y = Sum.inr (p.1, s), rfl,
              (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩⟩
            · rintro x ⟨s, hs, rfl⟩
              obtain ⟨s', hRs, hq⟩ := ((powerRel_apply _ _ _).mp hS).1 s hs
              exact ⟨Sum.inr (q.1, s'), ⟨he, hRs⟩, ⟨s', hq, rfl⟩⟩
            · rintro y ⟨s', hq, rfl⟩
              obtain ⟨s, hs, hRs⟩ := ((powerRel_apply _ _ _).mp hS).2 s' hq
              exact ⟨Sum.inr (p.1, s), ⟨s, hs, rfl⟩, ⟨he, hRs⟩⟩
      · rintro ⟨U, hU, hEM⟩
        have hUe : U = fun y : (Fobj L E a).carrier => ∃ s, p.2 s ∧ y = Sum.inr (p.1, s) := hU
        subst hUe
        refine ⟨Sum.inr (p.1, fun s' => T (Sum.inr (p.1, s'))), ⟨rfl, ?_⟩, ?_⟩
        -- `S'` is read back off `T` one second component at a time; the first is pinned by `𝟙`
        · refine (powerRel_apply _ _ _).mpr ⟨?_, ?_⟩
          · intro s hs
            obtain ⟨y, hy, hTy⟩ :=
              ((powerRel_apply _ _ _).mp hEM).1 (Sum.inr (p.1, s)) ⟨s, hs, rfl⟩
            cases y with
            | inl d => exact hy.elim
            | inr q =>
                obtain ⟨e', s'⟩ := q
                obtain ⟨he, hRs⟩ := hy
                subst he
                exact ⟨s', hRs, hTy⟩
          · intro s' hs'
            obtain ⟨x, hx, hR⟩ :=
              ((powerRel_apply _ _ _).mp hEM).2 (Sum.inr (p.1, s')) hs'
            obtain ⟨s, hs, rfl⟩ := hx
            exact ⟨s, hs, hR.2⟩
        · show T = fun y : (Fobj L E b).carrier =>
            ∃ s, T (Sum.inr (p.1, s)) ∧ y = Sum.inr (p.1, s)
          funext z
          refine propext ⟨fun hz => ?_, ?_⟩
          · obtain ⟨x, hx, hR⟩ := ((powerRel_apply _ _ _).mp hEM).2 z hz
            obtain ⟨s, hs, rfl⟩ := hx
            cases z with
            | inl d => exact hR.elim
            | inr q =>
                obtain ⟨e', s'⟩ := q
                obtain ⟨he, hRs⟩ := hR
                subst he
                exact ⟨s', hz, rfl⟩
          · rintro ⟨s, hTs, rfl⟩
            exact hTs

/-! ## `⦇gen⦈` -/

/-- **`⦇gen⦈` folded** (book p.181), `L(N(x))⟶N(E(L(x)))`: `gen` unfolded at a value is
    `F(𝟙,moves trans N(union)) zip N(cp P(α))` read pointwise — `moves trans N(union)` unions the
    path sets of every row (`moves` is every rotation), `zip` pairs the new column's row `k` with
    that union, and `N(cp P(α))` conses the square onto every path in it. -/
@[expose] public def genFn : ConsList Unit (Fin n → A) → Fin n → ConsList Unit A → Prop
  | ConsList.wrap _, _ => fun p => p = ConsList.wrap ()
  | ConsList.cons c cs, k => fun p => ∃ j q, genFn cs j q ∧ p = ConsList.cons (c k) q

/-- **cyl-defn**: `⦇gen⦈ : L(N(x))⟶N(E(L(x)))`, one path set per row of the cylinder. -/
@[expose] public def cataGen :
    dList (Fin n → A) ⟶ dTuple n (PowerAllegory.powerObj (dList A)) :=
  graph fun xs => fun k => genFn xs k

/-- The square at values: `L(N(R))`-related lists of columns fold to path sets that are
    Egli-Milner `L(R)`-related row by row.  The cons step needs both halves at every row `j`,
    because `gen` unions all of them before consing; the union of Egli-Milner related
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

/-- **`⦇gen⦈` is lax natural**: `L(N(R)) ⦇gen⦈ ⊑ ⦇gen⦈ N(P(L(R)))`.  `⦇gen⦈`
    is the graph of a function, so the square is `genFn_lax` at every row. -/
public theorem cataGen_lax_natural (R : dE A ⟶ dE B) :
    list (tupleP n R) ≫ cataGen ⊑ cataGen ≫ tupleP n (powerRel (list R)) := by
  refine le_iff.mpr fun xs u h => ?_
  obtain ⟨ys, hys, rfl⟩ := h
  exact ⟨fun k => genFn xs k, rfl, fun k => genFn_lax R xs ys hys k⟩

/-! ## `paths` -/

/-- **cyl-defn**: `paths ≜ ⦇gen⦈ setify union : L(N(x))⟶E(L(x))` — every path across the
    cylinder, the row it starts in forgotten. -/
@[expose] public def pathsRel :
    dList (Fin n → A) ⟶ PowerAllegory.powerObj (dList A) :=
  cataGen ≫ setify ≫ bigUnion

/-- **`paths` is lax natural**: `L(N(R)) paths ⊑ paths P(L(R))`.  The three squares of its
    definition in order — `⦇gen⦈` lax, `setify` lax at `P(L(R))`, and `union` strictly
    natural (`bigUnion_strict_relSet`), which is the one step that costs nothing. -/
public theorem paths_lax_natural (R : dE A ⟶ dE B) :
    list (tupleP n R) ≫ pathsRel ⊑ pathsRel ≫ powerRel (list R) := by
  calc list (tupleP n R) ≫ pathsRel
      = (list (tupleP n R) ≫ cataGen) ≫ setify ≫ bigUnion := by
        rw [pathsRel]; simp only [Cat.assoc]
    _ ⊑ (cataGen ≫ tupleP n (powerRel (list R))) ≫ setify ≫ bigUnion :=
        comp_mono_right (cataGen_lax_natural R) _
    _ = cataGen ≫ (tupleP n (powerRel (list R)) ≫ setify) ≫ bigUnion := by
        simp only [Cat.assoc]
    _ ⊑ cataGen ≫ (setify ≫ powerRel (powerRel (list R))) ≫ bigUnion :=
        comp_mono_left _ (comp_mono_right (setify_lax_natural (powerRel (list R))) _)
    _ = cataGen ≫ setify ≫ powerRel (powerRel (list R)) ≫ bigUnion := by
        simp only [Cat.assoc]
    _ = cataGen ≫ setify ≫ bigUnion ≫ powerRel (list R) := by
        rw [bigUnion_strict_relSet]
    _ = pathsRel ≫ powerRel (list R) := by rw [pathsRel]; simp only [Cat.assoc]

end Freyd.Alg.RelSet.Tuple
