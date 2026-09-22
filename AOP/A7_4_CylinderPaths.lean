/-
  Bird & de Moor, *Algebra of Programming* §7.4 (book pp. 180-184) — `Rel(Set)` as THE INSTANCE of
  `AOP.A7_4_Cylinder`'s abstract setting, and the squares that are natural in the ELEMENT TYPE,
  which the abstract section does not have: it fixes one `A` and one `I : InitialAlgebra F(A,−)`,
  so no square in the element type can be stated there.

  WHAT INSTANTIATES WHAT.  `F` is `CL.FB Unit`, the cons-list base bifunctor `F(A,X) = 1+A×X`
  (`AOP.A6_ConsList`), whose partial application IS the list relator `CL.F Unit A` used
  everywhere else (`CL.F_eq_appl`); `I` and `J` are `CL.initial` at the square type `A` and at
  the column type `Aⁿ`; `N` is the tuple relator, and `moves`, `trans`, `zip`, `setify` are
  `AOP.A7_4_CylinderBeads`' concrete relations, whose lax squares discharge the four
  `LaxNatural` hypotheses the setting binds.  `gen`, `Q`, `paths` and `cheapest` are therefore
  the ABSTRACT arrows applied — there is no second definition of any of them here — and the
  pointwise readings `genFun`, `genFn`, `consFn` are what the equalities below connect them to.

  `zip` AT AN ARBITRARY `F`.  The book's `zip : F(NA,NB)⟶N(F(A,B))` distributes the tuple out of
  BOTH slots of the base bifunctor.  `zipCL` is that arrow at the cons-list bifunctor and is what
  the instance supplies.  `zipF` below is the weaker unary reading `F(N(x))⟶N(F(x))` at an
  ARBITRARY relator `F`, which is a different arrow — it holds the first slot at `N(A)` where the
  book's lowers it to `A` — and is kept because it says what every relator admits.

  `L` IS THE REPO'S LIST, so `α = [nil,cons]` where the book has `[wrap,cons]` on non-empty
  lists: the fold's base case is the EMPTY path rather than the one-square path.  On a cylinder
  of one or more columns the two agree — `genFn (cons c nil) k = {[c k]}` either way — and the
  extra empty column costs the naturality squares nothing.

  Composition is diagram order (`≫`) throughout: B&dM `X·Y` = Freyd `Y ≫ X`.
-/
module

public import AOP.A7_4_CylinderBeads
public import AOP.A5_6_ListCombinators
public import AOP.A7_4_Cylinder

namespace Freyd.Alg.RelSet.Tuple

open Freyd CL ListRel

variable {a b : RelSet.{0}} {A B : Type} {n : Nat}

/-! ## The four families the §7.4 setting binds -/

/-- **`moves` is the setting's `moves`**: `AOP.A7_4_CylinderBeads`' square read as the
    `LaxNatural (N∘P) N` the abstract section assumes. -/
public theorem moves_natural :
    LaxNatural (Relator.comp (tupleRelator n) powerRelator) (tupleRelator n)
      (fun x => moves (A := x) (n := n)) :=
  fun {_ _} R => moves_lax_natural R

/-- **`trans` is the setting's `trans`**: `LaxNatural (P∘N) (N∘P)`. -/
public theorem trans_natural :
    LaxNatural (Relator.comp powerRelator (tupleRelator n))
      (Relator.comp (tupleRelator n) powerRelator) (fun x => transT (A := x) (n := n)) :=
  fun {_ _} R => trans_lax_natural R

/-- **`setify` is the setting's `setify`**: `LaxNatural P N`. -/
public theorem setify_natural :
    LaxNatural powerRelator (tupleRelator n) (fun x => setify (A := x) (n := n)) :=
  fun {_ _} R => setify_lax_natural R

/-- **`zip : F(NA,N(x))⟶N(F(A,x))`** (book p.181) at the cons-list base BIFUNCTOR: the `k`-th row
    of the answer takes the `k`-th square of the new column beside the `k`-th tail.  Both slots
    move — the column `NA` drops to one square `A` — which is what the setting's `zip` is and
    what `zipF` cannot do. -/
@[expose] public def zipCL {x : RelSet.{0}} :
    (CL.FB Unit).obj (dTuple n (dE A)) (dTuple n x) ⟶ dTuple n ((CL.FB Unit).obj (dE A) x) :=
  graph fun w => match w with
    | Sum.inl u => fun _ => Sum.inl u
    | Sum.inr p => fun k => Sum.inr (p.1 k, p.2 k)

/-- **`zip` is the setting's `zip`**: `F(𝟙,N(R)) zip ⊑ zip N(F(𝟙,R))`.  Row `k` of either side
    pairs the `k`-th square with an `R`-image of the `k`-th tail, so the two agree row by row and
    the inclusion is in fact an equality; lax is what the setting asks for. -/
public theorem zipCL_natural :
    LaxNatural (Relator.comp ((CL.FB Unit).appl (dE A)) (tupleRelator n))
      (Relator.comp (tupleRelator n) ((CL.FB Unit).appl (dTuple n (dE A))))
      (fun x => zipCL (n := n) (A := A) (x := x)) := by
  intro x y R
  refine le_iff.mpr fun w u h => ?_
  obtain ⟨v, hv, hu⟩ := h
  refine ⟨_, rfl, ?_⟩
  cases w with
  | inl d =>
      cases v with
      | inl d' =>
          have hd : d = d' := hv
          subst hd
          have hue : u = fun _ : Fin n => Sum.inl d := hu
          subst hue
          exact fun _ => rfl
      | inr q => exact hv.elim
  | inr p =>
      obtain ⟨c, T⟩ := p
      cases v with
      | inl d => exact hv.elim
      | inr q =>
          obtain ⟨c', T'⟩ := q
          obtain ⟨hc, hT⟩ := hv
          have hce : c = c' := hc
          subst hce
          have hue : u = fun k => Sum.inr (c k, T' k) := hu
          subst hue
          exact fun k => ⟨rfl, hT k⟩

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

/-- **`cp(inl d) = {inl d}`, `cp(e,S) = {(e,s) | s ∈ S}`** (book p.181) read pointwise: `cp` is
    the abstract `cpMap`, and this is the function whose graph it is (`cpMap_eq_graph`). -/
@[expose] public def cpFn (L E : Type) {a : RelSet.{0}} :
    ((F L E).obj (PowerAllegory.powerObj a)).carrier → Sub ((F L E).obj a).carrier :=
  fun w => match w with
    | Sum.inl d => fun y => y = Sum.inl d
    | Sum.inr p => fun y => ∃ s, p.2 s ∧ y = Sum.inr (p.1, s)

/-- **`cp ≜ frac(F(𝟙,∋),∋) : F(A,E B)⟶E(F(A,B))`**, the cross product — the powerset pulled out
    of the base functor — IS `cpMap` at the list functor, and `cpFn` is what it does.  `cp` is
    the second half of `gen`'s tail `N(cp P(α))`: it turns a column paired with a SET of tails
    into the SET of pairs, and `P(α)` conses the column onto each of them.  At `F X = L+(E×X)`
    the `𝟙` slot is the column `e`, so the first component is the same in every element of the
    answer; on the `L` summand there is no set to distribute and `cp` is the singleton. -/
public theorem cpMap_eq_graph (L E : Type) :
    cpMap (F L E) a = graph (cpFn L E (a := a)) :=
  ((Λ_UP _ (graph_map _)).mpr (by
    apply hom_ext
    intro w y
    constructor
    · rintro ⟨S, hS, hSy⟩
      have hSe : S = cpFn L E w := hS
      subst hSe
      cases w with
      | inl d =>
          have hye : y = Sum.inl d := hSy
          subst hye
          rfl
      | inr p =>
          obtain ⟨s, hs, rfl⟩ := hSy
          exact ⟨rfl, hs⟩
    · intro h
      refine ⟨cpFn L E w, rfl, ?_⟩
      cases w with
      | inl d =>
          cases y with
          | inl d' => exact (h : d = d') ▸ rfl
          | inr q => exact h.elim
      | inr p =>
          cases y with
          | inl d => exact h.elim
          | inr q => exact ⟨q.2, h.2, by rw [h.1]⟩)).symm

/-- **`cp` is natural, and it is STRICT**: `F(P(R)) cp = cp P(F(R))`.  On the `L` summand both
    sides relate `inl d` to the singleton `{inl d}` and to nothing else — `F(R)` moves no `inl`,
    so Egli-Milner pins the set.  On the product summand the first component is pinned by the
    `𝟙`, so a set the right side names is `{e}×S'` for `S' = {s' | (e,s') ∈ ·}`, and the two
    Egli-Milner halves read off `S` and `S'` are exactly `P(R)`'s.  The abstract
    `cpMap_laxNatural` gives only the inclusion; the other cylinder beads are lax because they
    duplicate or merge rows, which `cp` never does. -/
public theorem cpMap_strict_natural (L E : Type) (R : a ⟶ b) :
    (F L E).map (powerRel R) ≫ cpMap (F L E) b = cpMap (F L E) a ≫ powerRel ((F L E).map R) := by
  rw [cpMap_eq_graph, cpMap_eq_graph]
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

/-! ## `gen` -/

/-- **`moves trans N(union)` unions every row into every row** (book p.181): `moves` is every
    rotation, so the transpose holds all `n` rows at each index and `union` collapses them —
    which is why a path may start in any row. -/
public theorem moves_trans_union :
    (moves ≫ transT ≫ tupleP n (bigUnion (a := a))
        : dTuple n (PowerAllegory.powerObj a) ⟶ dTuple n (PowerAllegory.powerObj a))
      = graph (fun T : (dTuple n (PowerAllegory.powerObj a)).carrier =>
          (fun _ => fun q => ∃ i, T i q : (dTuple n (PowerAllegory.powerObj a)).carrier)) := by
  apply hom_ext
  intro T U
  constructor
  · rintro ⟨S, hS, V, hV, hU⟩
    have hSe : S = fun u => ∃ j, rot j T = u := hS
    subst hSe
    have hVe : V = fun k => fun x => ∃ t, (∃ j, rot j T = t) ∧ t k = x := hV
    subst hVe
    show U = _
    funext k
    funext q
    refine propext ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨X, ⟨t, ⟨j, hj⟩, hk⟩, hX⟩ := ((bigUnion_apply _ _).mp (hU k) q).mp hq
      subst hj
      have hkX : T (k + j) = X := hk
      exact ⟨k + j, by rw [hkX]; exact hX⟩
    · obtain ⟨i, hi⟩ := hq
      obtain ⟨j, hj⟩ := exists_rot_index k i
      refine ((bigUnion_apply _ _).mp (hU k) q).mpr ⟨T i, ⟨rot j T, ⟨j, rfl⟩, ?_⟩, hi⟩
      show T (k + j) = T i
      rw [hj]
  · intro hU
    have hUe : U = _ := hU
    subst hUe
    refine ⟨fun u => ∃ j, rot j T = u, rfl,
      fun k => fun x => ∃ t, (∃ j, rot j T = t) ∧ t k = x, rfl, fun k => ?_⟩
    refine (bigUnion_apply _ _).mpr fun q => ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨i, hi⟩ := hq
      obtain ⟨j, hj⟩ := exists_rot_index k i
      refine ⟨T i, ⟨rot j T, ⟨j, rfl⟩, ?_⟩, hi⟩
      show T (k + j) = T i
      rw [hj]
    · obtain ⟨X, ⟨t, ⟨j, hj⟩, hk⟩, hX⟩ := hq
      subst hj
      have hkX : T (k + j) = X := hk
      exact ⟨k + j, by rw [hkX]; exact hX⟩

/-- **`cp P(α)` conses the new square onto every path in the set** (book p.181): `cp` pulls the
    powerset out of the base functor and `P(α)` applies the algebra inside it, so the empty
    summand goes to `{nil}` and a column paired with a set of tails to the set of conses. -/
@[expose] public def consFn :
    ((F Unit A).obj (PowerAllegory.powerObj (dList A))).carrier → Sub (ConsList Unit A) :=
  fun w => match w with
    | Sum.inl u => fun p => p = ConsList.wrap u
    | Sum.inr q => fun p => ∃ s, q.2 s ∧ p = ConsList.cons q.1 s

/-- **`cp P(α) = consFn`** — the tail of `gen`, read as a function. -/
public theorem cpMap_comp_existsImage_alphaR :
    cpMap (F Unit A) (dList A)
        ≫ existsImage (alphaR : (F Unit A).obj (dList A) ⟶ dList A)
      = graph consFn := by
  rw [show cpMap (F Unit A) (dList A) = Λ ((F Unit A).map (∋ (dList A))) from rfl, Λ_absorption]
  refine ((Λ_UP _ (graph_map _)).mpr ?_).symm
  apply hom_ext
  intro w p
  constructor
  · rintro ⟨S, hS, hSp⟩
    have hSe : S = consFn w := hS
    subst hSe
    cases w with
    | inl u =>
        have hpe : p = ConsList.wrap u := hSp
        subst hpe
        exact ⟨Sum.inl u, rfl, rfl⟩
    | inr q =>
        obtain ⟨s, hs, rfl⟩ := hSp
        exact ⟨Sum.inr (q.1, s), ⟨rfl, hs⟩, rfl⟩
  · rintro ⟨v, hv, hp⟩
    refine ⟨consFn w, rfl, ?_⟩
    cases w with
    | inl u =>
        cases v with
        | inr q => exact hv.elim
        | inl u' =>
            have hue : u = u' := hv
            subst hue
            show p = ConsList.wrap u
            exact hp
    | inr q =>
        cases v with
        | inl u => exact hv.elim
        | inr r =>
            obtain ⟨he, hs⟩ := hv
            show ∃ s, q.2 s ∧ p = ConsList.cons q.1 s
            exact ⟨r.2, hs, by rw [he]; exact hp⟩

/-- **cyl-gen** as a FUNCTION: `gen` at a value.  The empty column folds to the one empty path in
    every row; a new column `c` conses `c k` onto every path any row of the tail holds, which is
    `zip` pairing row `k` with `moves trans N(union)`'s union and `N(cp P(α))` prefixing it. -/
@[expose] public def genFun :
    (Fobj Unit (Fin n → A) (dTuple n (PowerAllegory.powerObj (dList A)))).carrier →
      Fin n → ConsList Unit A → Prop
  | Sum.inl _ => fun _ p => p = ConsList.wrap ()
  | Sum.inr (c, T) => fun k p => ∃ j q, T j q ∧ p = ConsList.cons (c k) q

/-- **cyl-gen**: the setting's `gen ≜ F(𝟙,moves trans N(union)) zip N(cp P(α))` at `Rel(Set)`
    IS `genFun` — the three named equalities above composed, summand by summand. -/
public theorem gen_eq_graph :
    Cylinder.gen (N := tupleRelator n) (CL.FB Unit) (CL.initial Unit A)
        (fun x => moves (A := x) (n := n)) (fun x => transT (A := x) (n := n))
        (fun x => zipCL (n := n) (A := A) (x := x))
        moves_natural trans_natural zipCL_natural
      = graph (genFun (n := n) (A := A)) := by
  show (F Unit (Fin n → A)).map
        (moves ≫ transT ≫ tupleP n (bigUnion (a := dList A)))
      ≫ zipCL ≫ tupleP n (cpMap (F Unit A) (dList A)
        ≫ existsImage (alphaR : (F Unit A).obj (dList A) ⟶ dList A))
    = graph (genFun (n := n) (A := A))
  rw [moves_trans_union, cpMap_comp_existsImage_alphaR]
  apply hom_ext
  intro w U
  constructor
  · rintro ⟨v, hv, z, hz, hU⟩
    cases w with
    | inl u =>
        cases v with
        | inr q => exact hv.elim
        | inl u' =>
            have hue : u = u' := hv
            subst hue
            have hze : z = fun _ : Fin n => Sum.inl u := hz
            subst hze
            show U = _
            funext k
            exact hU k
    | inr p =>
        obtain ⟨c, T⟩ := p
        cases v with
        | inl u => exact hv.elim
        | inr r =>
            obtain ⟨c', T'⟩ := r
            obtain ⟨hc, hT⟩ := hv
            have hce : c = c' := hc
            subst hce
            have hTe : T' = fun _ : Fin n => fun q => ∃ i, T i q := hT
            subst hTe
            have hze : z = fun k => Sum.inr (c k, fun q => ∃ i, T i q) := hz
            subst hze
            show U = _
            funext k
            refine (hU k).trans ?_
            funext p
            exact propext ⟨fun ⟨s, ⟨i, hi⟩, hp⟩ => ⟨i, s, hi, hp⟩,
              fun ⟨i, s, hi, hp⟩ => ⟨s, ⟨i, hi⟩, hp⟩⟩
  · intro hU
    have hUe : U = genFun w := hU
    subst hUe
    cases w with
    | inl u =>
        refine ⟨Sum.inl u, rfl, fun _ : Fin n => Sum.inl u, rfl, fun k => ?_⟩
        rfl
    | inr p =>
        obtain ⟨c, T⟩ := p
        refine ⟨Sum.inr (c, fun _ : Fin n => fun q => ∃ i, T i q), ⟨rfl, rfl⟩,
          fun k => Sum.inr (c k, fun q => ∃ i, T i q), rfl, fun k => ?_⟩
        show genFun (Sum.inr (c, T)) k = _
        funext p
        exact propext ⟨fun ⟨i, s, hi, hp⟩ => ⟨s, ⟨i, hi⟩, hp⟩,
          fun ⟨s, ⟨i, hi⟩, hp⟩ => ⟨i, s, hi, hp⟩⟩

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

/-- **`gen` is an `F`-algebra and `⦇gen⦈` its fold** (`<fold-diag>`): `α⦇gen⦈=F(𝟙,⦇gen⦈)gen`.
    `cata_comm` at this algebra, with the two sides the display draws — the fold bead is OUTSIDE
    `F` on the left and INSIDE it on the right, which is all the recursion there is. -/
public theorem cataGen_comm :
    InitialAlgebra.α (F := F Unit (Fin n → A)) ≫ cataGen
      = (F Unit (Fin n → A)).map cataGen ≫ graph (genFun (n := n) (A := A)) := by
  apply hom_ext; intro u T
  cases u with
  | inl d =>
    constructor
    · rintro ⟨xs, hxs, hT⟩
      have hx : xs = ConsList.wrap d := hxs
      subst hx
      exact ⟨Sum.inl d, rfl, hT⟩
    · rintro ⟨v, hv, hT⟩
      cases v with
      | inl d' => exact ⟨ConsList.wrap d, rfl, hT⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨c, cs⟩ := p
    constructor
    · rintro ⟨xs, hxs, hT⟩
      have hx : xs = ConsList.cons c cs := hxs
      subst hx
      exact ⟨Sum.inr (c, fun k => genFn cs k), ⟨rfl, rfl⟩, hT⟩
    · rintro ⟨v, hv, hT⟩
      cases v with
      | inl d => exact hv.elim
      | inr q =>
        obtain ⟨c', S⟩ := q
        obtain ⟨h1, h2⟩ := hv
        have hc : c = c' := h1
        have hS : S = fun k => genFn cs k := h2
        subst hc; subst hS
        exact ⟨ConsList.cons c cs, rfl, hT⟩

/-- **`⦇gen⦈` IS the fold of the setting's `gen`** — the Eilenberg-Wright lemma at `cataGen_comm`,
    which is what makes `pathsRel` below an instance rather than a second definition. -/
public theorem cataGen_eq_relCata :
    (cataGen : dList (Fin n → A) ⟶ dTuple n (PowerAllegory.powerObj (dList A)))
      = relCata (I := CL.initial Unit (Fin n → A))
          (Cylinder.gen (N := tupleRelator n) (CL.FB Unit) (CL.initial Unit A)
            (fun x => moves (A := x) (n := n)) (fun x => transT (A := x) (n := n))
            (fun x => zipCL (n := n) (A := A) (x := x))
            moves_natural trans_natural zipCL_natural) :=
  (relCata_UP (CL.initial Unit (Fin n → A)) _ _).mp (by rw [gen_eq_graph]; exact cataGen_comm)

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
    cylinder, the row it starts in forgotten.  The abstract `Cylinder.paths` at this instance,
    not a second definition of it. -/
@[expose] public noncomputable def pathsRel :
    dList (Fin n → A) ⟶ PowerAllegory.powerObj (dList A) :=
  Cylinder.paths (N := tupleRelator n) (CL.FB Unit) (CL.initial Unit A)
    (CL.initial Unit (Fin n → A))
    (fun x => moves (A := x) (n := n)) (fun x => transT (A := x) (n := n))
    (fun x => zipCL (n := n) (A := A) (x := x)) (fun x => setify (A := x) (n := n))
    moves_natural trans_natural zipCL_natural

/-- `paths` computed: the fold is `cataGen`, so `paths` is the structural fold followed by
    `setify union`. -/
public theorem pathsRel_eq :
    (pathsRel : dList (Fin n → A) ⟶ PowerAllegory.powerObj (dList A))
      = cataGen ≫ setify ≫ bigUnion := by
  rw [pathsRel, Cylinder.paths, ← cataGen_eq_relCata]

/-- **`paths` is lax natural**: `L(N(R)) paths ⊑ paths P(L(R))`.  The three squares of its
    definition in order — `⦇gen⦈` lax, `setify` lax at `P(L(R))`, and `union` strictly
    natural (`bigUnion_strict_relSet`), which is the one step that costs nothing. -/
public theorem paths_lax_natural (R : dE A ⟶ dE B) :
    list (tupleP n R) ≫ pathsRel ⊑ pathsRel ≫ powerRel (list R) := by
  rw [pathsRel_eq, pathsRel_eq]
  calc list (tupleP n R) ≫ cataGen ≫ setify ≫ bigUnion
      = (list (tupleP n R) ≫ cataGen) ≫ setify ≫ bigUnion := by
        simp only [Cat.assoc]
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
    _ = (cataGen ≫ setify ≫ bigUnion) ≫ powerRel (list R) := by simp only [Cat.assoc]

/-! ## The cost of a path, and the specification -/

/-- **cyl-defn**: `R ≜ sum ≤ sum°`, the cost preorder on paths — `xs R ys ⟺ sum(xs) ≤ sum(ys)`.
    Written as the note writes it, `sum` either side of the order on the costs. -/
@[expose] public def costLE : dList Nat ⟶ dList Nat :=
  sumR ≫ (fun m k => m ≤ k : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩) ≫ sumR°

/-- **cyl-defn**: the specification `paths est(R)` — a cheapest path across the cylinder. -/
@[expose] public noncomputable def cheapest : dList (Fin n → Nat) ⟶ dList Nat :=
  pathsRel ≫ est costLE

end Freyd.Alg.RelSet.Tuple
