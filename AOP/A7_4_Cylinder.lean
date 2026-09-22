/-
  Bird & de Moor, *Algebra of Programming* §7.4  Shortest paths on a cylinder
  (book pp. 179-184).

  An `n × m` array of costs is rolled into a cylinder; a path crosses it one column at a time
  and may step up, straight or down, the top row being glued to the bottom.  The cheapest path
  is `paths est(R)` for `R ≜ sum ≤ sum°`, and the fold that computes it is `⦇Q⦈ setify est(R)`.

  §7.4 is NOT a greedy problem: the crux is Theorem 7.1 (`AOP.A7_2`'s
  `distributes_of_monotonicAlg`) at the MAP `α`, which gives (7.13) — the section's only
  numbered equation — and the rest is one catamorphism fusion.

  WHAT IS PROVED HERE (the note's `cyl-fusion`, `cyl-laws`, `cyl-step`):

  - `cyl_7_13`   — (7.13) `F(𝟙,est(R))α ⊑ cp P(α) est(R)`, Theorem 7.1 at `α` with
                   `Λ(F(𝟙,∋)α) = cp P(α)` (`Λ_absorption`).
  - `cyl_fusion` — `gen N(est(R)) ⊒ F(𝟙,N(est(R)))Q`, the fusion condition of the last
                   step of `cyl-laws`, from (7.13) and the lax naturality of `zip`, `trans`
                   and `moves`.
  - `cyl_laws`   — `paths est(R) ⊒ ⦇Q⦈ setify est(R)`, the headline (book p.182).
  - `cyl_step`   — `Q = [N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]` (book p.183), the
                   coproduct of `Q`'s definition opened.

  THE SETTING.  `A7_2`'s `MonotonicAlg`/`Distributes` and `A8_2`'s tabular power merge, with
  `F` the book's base BIFUNCTOR `F(A,X)` of non-empty cons-lists, `A` the type of ONE SQUARE —
  fixed for the whole problem, as the book fixes `Nat` — and `N` the `n`-tuple relator.  Two
  initial algebras of its partial applications stand: `I` of `F(A,−)`, whose carrier `T A` is
  the type of a path, and `J` of `F(NA,−)`, whose carrier `T(NA)` is the type of a cylinder
  read column by column.  One bifunctor and two algebras, as the book has one `F` and the two
  list types `PLA` and `PLNA`.

  ASSUMED, as in the book and as `AOP.A8_5` assumes the sorted-list interface: `moves`,
  `trans`, `zip` and `setify` stay abstract arrows of the types `cyl-defn` gives them, and
  the LAX NATURALITY the book states for them on p.180 and uses on pp.182-183 is carried as a
  hypothesis at the one relation each is used at.  `Cylinder.OneRow` below discharges every
  one of those hypotheses at `n = 1` (`N ≜ 𝟙`, `moves = setify = τ`, `trans = zip = 𝟙`), so
  none of them is vacuous.

  ONE PLACE THE NOTE'S REASON IS NOT LITERALLY THE FACT USED.  `cyl-laws`' third row cites
  "`setify` lax natural" for
  `⦇gen⦈ setify P(est(R)) est(R) ⊒ ⦇gen⦈ N(est(R)) setify est(R)`.  Taken bare,
  `N(est(R)) setify ⊑ setify P(est(R))` is the lax square, and it is exactly what `hsetify`
  below assumes — with `est(R)` on the right of BOTH sides, which is how the row uses it and
  what `OneRow` proves.  `P` here is `AOP.A5_4`'s Egli-Milner power RELATOR `powerRel`, not
  the existential image `existsImage`: the existential image is not monotonic, so no lax
  square through it holds, and (7.11) (`powerRel_est_le_bigUnion`) is stated for `powerRel`
  too.  `P(α)` in `cyl-defn`'s `gen` IS the existential image, `α` being a map
  (`powerRel_map`).

  MIRRORING: diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; B&dM's `min R` is `est R`
  (`AOP.A7_1`), `union` is `bigUnion`, `τ` is `singletonMap`.
-/
module

public import AOP.A8_2
public import AOP.A7_2

universe u

namespace Freyd.Alg.Cylinder

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜]
  {N : Relator 𝒜 𝒜} (F : BiRelator 𝒜) {A : 𝒜}
  (I : InitialAlgebra (F.appl A)) (J : InitialAlgebra (F.appl (N.obj A)))
  (moves : ∀ x : 𝒜, N.obj x ⟶ PowerAllegory.powerObj (N.obj x))
  (trans : ∀ x : 𝒜, PowerAllegory.powerObj (N.obj x) ⟶ N.obj (PowerAllegory.powerObj x))
  (zip : ∀ x : 𝒜, F.obj (N.obj A) (N.obj x) ⟶ N.obj (F.obj A x))
  (setify : ∀ x : 𝒜, N.obj x ⟶ PowerAllegory.powerObj x)
  -- B&dM p.180: "we will need a number of other lax natural transformations".  Lean assumes what
  -- the book assumes, at the family and not at the one relation each square is used at.
  (moves_natural : LaxNatural (Relator.comp N powerRelator) N moves)
  (trans_natural : LaxNatural (Relator.comp powerRelator N) (Relator.comp N powerRelator) trans)
  (zip_natural : LaxNatural (Relator.comp (F.appl A) N) (Relator.comp N (F.appl (N.obj A))) zip)
  (setify_natural : LaxNatural powerRelator N setify)

/-! ## `cyl-defn` -/

/-- **cp-diag**: `cp = 𝟙%∋ E(F(𝟙,∋))` — the cross product at the cylinder's own base functor is
    the power transpose of `F(𝟙,∋)`: pick one path out of each row's set, collect the results. -/
public theorem cyl_cp : cpMap (F.appl A) I.t = Λ ((F.appl A).map (∋ I.t)) := rfl

/-- **cp-diag**, the `A×−` summand of `F(A,−)=A+A×−`: `cp = 𝟙%∋ E(𝟙×∋)` — the new square is
    carried untouched and `∋` picks one path out of the set beside it. -/
public theorem cyl_cp_prod [HasRelProd 𝒜] (A B : 𝒜) :
    cpMap (Relator.prod (Relator.const A) (Relator.idRelator 𝒜)) B
      = Λ (prodMap (relProd A (PowerAllegory.powerObj B)) (relProd A B) (𝟙 A) (∋ B)) := rfl

/-- **cp-diag**, the `A` summand: `cp = 𝟙%∋` — a constant relator has no `E` to distribute, so
    the transpose is the singleton `a↦{a}`. -/
public theorem cyl_cp_const (A B : 𝒜) : cpMap (Relator.const (𝒜 := 𝒜) A) B = Λ (𝟙 A) := rfl

/-- **cyl-defn**: `gen ≜ F(𝟙,moves trans N(union)) zip N(cp P(α))`, of type
    `F(NA,N(E(TA)))⟶N(E(TA))` — one fold step, extending every path of every row by the new
    column.

    THE ASSUMPTION TRAVELS WITH THE DEFINITION.  `gen` is a panel of the note, and its `moves`,
    `trans` and `zip` are beads the book calls lax natural and Lean proves nothing about, so the
    three squares ride in `gen`'s own binders — `include` reaches a theorem's statement but not a
    definition's, so they are written out here. -/
@[expose] public noncomputable def gen
    (moves_natural : LaxNatural (Relator.comp N powerRelator) N moves)
    (trans_natural : LaxNatural (Relator.comp powerRelator N) (Relator.comp N powerRelator) trans)
    (zip_natural : LaxNatural (Relator.comp (F.appl A) N) (Relator.comp N (F.appl (N.obj A))) zip) :
    F.obj (N.obj A) (N.obj (PowerAllegory.powerObj I.t))
      ⟶ N.obj (PowerAllegory.powerObj I.t) :=
  (F.appl (N.obj A)).map (moves (PowerAllegory.powerObj I.t)
      ≫ trans (PowerAllegory.powerObj I.t) ≫ N.map (bigUnion (a := I.t)))
    ≫ zip (PowerAllegory.powerObj I.t) ≫ N.map (cpMap (F.appl A) I.t ≫ existsImage I.α)

/-- **cyl-defn**: `paths ≜ ⦇gen⦈ setify union`, of type `T(NA)⟶E(TA)` — every path
    across the cylinder. -/
@[expose] public noncomputable def paths : J.t ⟶ PowerAllegory.powerObj I.t :=
  ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
    ≫ setify (PowerAllegory.powerObj I.t) ≫ bigUnion

/-- **fold-diag**: `α⦇gen⦈ = F(𝟙,⦇gen⦈)gen` — the fold's computation rule at `gen`: reading the
    whole list is putting the column back on it and then reading it, which is reading the rest
    under `F` and then one `gen`.  `relCata_cancel` at `gen`, the abstract counterpart of
    `Vec.cons_genFold`. -/
public theorem gen_cata_comm :
    J.α ≫ (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
        : J.t ⟶ N.obj (PowerAllegory.powerObj I.t))
      = (F.appl (N.obj A)).map ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ gen F I moves trans zip moves_natural trans_natural zip_natural :=
  relCata_cancel J _

/-- **cyl-defn**: the algebra the derivation's last step folds,
    `Q ≜ F(𝟙,moves trans N(est(R))) zip N(α)`, of type `F(NA,N(TA))⟶N(TA)`.  Its three beads
    carry the setting's naturality for the reason `gen`'s do. -/
@[expose] public noncomputable def Q
    (moves_natural : LaxNatural (Relator.comp N powerRelator) N moves)
    (trans_natural : LaxNatural (Relator.comp powerRelator N) (Relator.comp N powerRelator) trans)
    (zip_natural : LaxNatural (Relator.comp (F.appl A) N) (Relator.comp N (F.appl (N.obj A))) zip)
    (R : I.t ⟶ I.t) : F.obj (N.obj A) (N.obj I.t) ⟶ N.obj I.t :=
  (F.appl (N.obj A)).map (moves I.t ≫ trans I.t ≫ N.map (est R)) ≫ zip I.t ≫ N.map I.α

/-! ## `cyl-fusion` -/

/-- **(7.13)** (book p.182): `F(𝟙,est(R))α ⊑ cp P(α) est(R)` — extending every path in a set
    and then taking a minimum is beaten by extending one minimum.  Theorem 7.1
    (`distributes_of_monotonicAlg`) at the map `α`, with `Λ(F(𝟙,∋)α) = cp P(α)`
    (`Λ_absorption`, `cp = Λ(F(𝟙,∋))`).  The book's "the monotonicity condition is that `α` is
    monotonic on `R` and is easy to verify" is the hypothesis `hmono`. -/
public theorem cyl_7_13 (hGr : (F.appl A).PreservesRecip) (R : I.t ⟶ I.t)
    (hmono : MonotonicAlg I.α R°) :
    (F.appl A).map (est R) ≫ I.α ⊑ cpMap (F.appl A) I.t ≫ existsImage I.α ≫ est R := by
  have hcp : cpMap (F.appl A) I.t ≫ existsImage I.α = Λ ((F.appl A).map (∋ I.t) ≫ I.α) :=
    Λ_absorption _ _
  have hd : Distributes I.α R := distributes_of_monotonicAlg I.α_map hGr hmono
  calc (F.appl A).map (est R) ≫ I.α ⊑ Λ ((F.appl A).map (∋ I.t) ≫ I.α) ≫ est R := hd
    _ = cpMap (F.appl A) I.t ≫ existsImage I.α ≫ est R := by rw [← hcp, Cat.assoc]

/-- **cyl-fusion** (book pp.182-183): `gen N(est(R)) ⊒ F(𝟙,N(est(R)))Q` — the fusion
    condition of `cyl-laws`' last step.  `gen` kills the base functor before the minimum
    is taken inside the tuple; `Q` kills it after, and that swap is the whole step.

    The four hypotheses are the book's own justifications, at the one relation each is used
    at: (7.13) `h713`; `moves`, `trans` and `zip` lax natural (`hmoves`, `htransN`, `hzip`);
    and (7.11) distribution over union, which is `powerRel_est_le_bigUnion` at the transitive
    `R`. -/
public theorem cyl_fusion (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R)
    (h713 : (F.appl A).map (est R) ≫ I.α ⊑ cpMap (F.appl A) I.t ≫ existsImage I.α ≫ est R) :
    (F.appl (N.obj A)).map (N.map (est R))
        ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R
      ⊑ gen F I moves trans zip moves_natural trans_natural zip_natural ≫ N.map (est R) := by
  -- the three squares the book's steps cite, each the setting's own lax naturality at `est(R)`
  have hmoves : N.map (est R) ≫ moves I.t
      ⊑ moves (PowerAllegory.powerObj I.t) ≫ powerRel (N.map (est R)) := moves_natural (est R)
  have htransN : powerRel (N.map (est R)) ≫ trans I.t
      ⊑ trans (PowerAllegory.powerObj I.t) ≫ N.map (powerRel (est R)) := trans_natural (est R)
  have hzip : (F.appl (N.obj A)).map (N.map (est R)) ≫ zip I.t
      ⊑ zip (PowerAllegory.powerObj I.t) ≫ N.map ((F.appl A).map (est R)) := zip_natural (est R)
  -- the tuple-side chain: `N(est R)` slides through `moves`, `trans` and (7.11) to the front
  have hinner : N.map (est R) ≫ moves I.t ≫ trans I.t ≫ N.map (est R)
      ⊑ (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t))) ≫ N.map (est R) := by
    calc N.map (est R) ≫ moves I.t ≫ trans I.t ≫ N.map (est R)
        = (N.map (est R) ≫ moves I.t) ≫ trans I.t ≫ N.map (est R) := by
          simp only [Cat.assoc]
      _ ⊑ (moves (PowerAllegory.powerObj I.t) ≫ powerRel (N.map (est R)))
            ≫ trans I.t ≫ N.map (est R) := comp_mono_right hmoves _
      _ = moves (PowerAllegory.powerObj I.t)
            ≫ (powerRel (N.map (est R)) ≫ trans I.t) ≫ N.map (est R) := by
          simp only [Cat.assoc]
      _ ⊑ moves (PowerAllegory.powerObj I.t)
            ≫ (trans (PowerAllegory.powerObj I.t) ≫ N.map (powerRel (est R)))
            ≫ N.map (est R) := comp_mono_left _ (comp_mono_right htransN _)
      _ = moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
            ≫ N.map (powerRel (est R) ≫ est R) := by
          rw [N.map_comp]; simp only [Cat.assoc]
      _ ⊑ moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
            ≫ N.map (bigUnion (a := I.t) ≫ est R) :=
          comp_mono_left _ (comp_mono_left _ (N.map_mono (powerRel_est_le_bigUnion htrans)))
      _ = (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
            ≫ N.map (bigUnion (a := I.t))) ≫ N.map (est R) := by
          rw [N.map_comp]; simp only [Cat.assoc]
  -- the base-functor side: `zip` lax natural, then (7.13)
  have houter : N.map ((F.appl A).map (est R)) ≫ N.map I.α
      ⊑ N.map (cpMap (F.appl A) I.t ≫ existsImage I.α) ≫ N.map (est R) := by
    calc N.map ((F.appl A).map (est R)) ≫ N.map I.α
        = N.map ((F.appl A).map (est R) ≫ I.α) := by rw [N.map_comp]
      _ ⊑ N.map (cpMap (F.appl A) I.t ≫ existsImage I.α ≫ est R) := N.map_mono h713
      _ = N.map (cpMap (F.appl A) I.t ≫ existsImage I.α) ≫ N.map (est R) := by
          rw [← N.map_comp, Cat.assoc]
  calc (F.appl (N.obj A)).map (N.map (est R))
        ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R
      = (F.appl (N.obj A)).map (N.map (est R) ≫ moves I.t ≫ trans I.t ≫ N.map (est R))
          ≫ zip I.t ≫ N.map I.α := by
        rw [Q, ← Cat.assoc, ← (F.appl (N.obj A)).map_comp]
    _ ⊑ (F.appl (N.obj A)).map ((moves (PowerAllegory.powerObj I.t)
          ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t))) ≫ N.map (est R)) ≫ zip I.t ≫ N.map I.α :=
        comp_mono_right ((F.appl (N.obj A)).map_mono hinner) _
    _ = (F.appl (N.obj A)).map (moves (PowerAllegory.powerObj I.t)
          ≫ trans (PowerAllegory.powerObj I.t) ≫ N.map (bigUnion (a := I.t)))
          ≫ ((F.appl (N.obj A)).map (N.map (est R)) ≫ zip I.t) ≫ N.map I.α := by
        rw [(F.appl (N.obj A)).map_comp]; simp only [Cat.assoc]
    _ ⊑ (F.appl (N.obj A)).map (moves (PowerAllegory.powerObj I.t)
          ≫ trans (PowerAllegory.powerObj I.t) ≫ N.map (bigUnion (a := I.t)))
          ≫ (zip (PowerAllegory.powerObj I.t) ≫ N.map ((F.appl A).map (est R))) ≫ N.map I.α :=
        comp_mono_left _ (comp_mono_right hzip _)
    _ = (F.appl (N.obj A)).map (moves (PowerAllegory.powerObj I.t)
          ≫ trans (PowerAllegory.powerObj I.t) ≫ N.map (bigUnion (a := I.t)))
          ≫ zip (PowerAllegory.powerObj I.t)
          ≫ N.map ((F.appl A).map (est R)) ≫ N.map I.α := by
        simp only [Cat.assoc]
    _ ⊑ (F.appl (N.obj A)).map (moves (PowerAllegory.powerObj I.t)
          ≫ trans (PowerAllegory.powerObj I.t) ≫ N.map (bigUnion (a := I.t)))
          ≫ zip (PowerAllegory.powerObj I.t)
          ≫ N.map (cpMap (F.appl A) I.t ≫ existsImage I.α) ≫ N.map (est R) :=
        comp_mono_left _ (comp_mono_left _ houter)
    _ = gen F I moves trans zip moves_natural trans_natural zip_natural ≫ N.map (est R) := by
        rw [gen]; simp only [Cat.assoc]

/-! ## `cyl-laws` -/

section CylLaws
-- Every step of the chain draws `setify`, so every one of them carries its naturality.
include setify_natural

/-- **cyl-laws** step 1: `⦇Q⦈ setify est(R) ⊑ ⦇gen⦈ N(est(R)) setify est(R)` — fusion, i.e.
    `⦇Q⦈ ⊑ ⦇gen⦈ N(est(R))` by the least-prefixed-point property of `⦇Q⦈`, composed on the
    right.  The `J` ascription is what pins the fold's initial algebra. -/
public theorem cyl_laws_step1 (R : I.t ⟶ I.t)
    (hfusion : (F.appl (N.obj A)).map (N.map (est R))
        ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R
      ⊑ gen F I moves trans zip moves_natural trans_natural zip_natural ≫ N.map (est R)) :
    (⦇Q F I moves trans zip moves_natural trans_natural zip_natural R⦈ : J.t ⟶ N.obj I.t)
        ≫ setify I.t ≫ est R
      ⊑ ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ N.map (est R) ≫ setify I.t ≫ est R := by
  have hcata : (⦇Q F I moves trans zip moves_natural trans_natural zip_natural R⦈
      : J.t ⟶ N.obj I.t)
      ⊑ ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈ ≫ N.map (est R) := by
    apply relCata_le_of_prefixed J
    calc J.α°
            ≫ (F.appl (N.obj A)).map
              (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈ ≫ N.map (est R))
            ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R
        = J.α°
            ≫ (F.appl (N.obj A)).map
              ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
            ≫ (F.appl (N.obj A)).map (N.map (est R))
            ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R := by
          rw [(F.appl (N.obj A)).map_comp]; simp only [Cat.assoc]
      _ ⊑ J.α°
            ≫ (F.appl (N.obj A)).map
              ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
            ≫ gen F I moves trans zip moves_natural trans_natural zip_natural ≫ N.map (est R) :=
          comp_mono_left _ (comp_mono_left _ hfusion)
      _ = J.α°
            ≫ (J.α ≫ ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈)
            ≫ N.map (est R) := by
          rw [relCata_cancel J]; simp only [Cat.assoc]
      _ = ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
            ≫ N.map (est R) := by
          rw [← Cat.assoc, ← Cat.assoc, J.recip_alpha_alpha, Cat.id_comp]
  calc (⦇Q F I moves trans zip moves_natural trans_natural zip_natural R⦈ : J.t ⟶ N.obj I.t)
        ≫ setify I.t ≫ est R
      ⊑ (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ N.map (est R)) ≫ setify I.t ≫ est R :=
        comp_mono_right hcata _
    _ = ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ N.map (est R) ≫ setify I.t ≫ est R := by
        simp only [Cat.assoc]

/-- **cyl-laws** step 2: `⦇gen⦈ N(est(R)) setify est(R) ⊑ ⦇gen⦈ setify P(est(R)) est(R)` —
    `setify`'s lax square, taking the minimum out of the tuple and into the set. -/
public theorem cyl_laws_step2 (R : I.t ⟶ I.t) :
    (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
        : J.t ⟶ N.obj (PowerAllegory.powerObj I.t))
        ≫ N.map (est R) ≫ setify I.t ≫ est R
      ⊑ ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ setify (PowerAllegory.powerObj I.t) ≫ powerRel (est R) ≫ est R := by
  -- the row's own reason: `setify`'s lax square, with `est(R)` standing on the right of both sides
  have hsetify : N.map (est R) ≫ setify I.t ≫ est R
      ⊑ setify (PowerAllegory.powerObj I.t) ≫ powerRel (est R) ≫ est R := by
    rw [← Cat.assoc, ← Cat.assoc]
    exact comp_mono_right (setify_natural (est R)) _
  exact comp_mono_left _ hsetify

/-- **cyl-laws** step 3: `⦇gen⦈ setify P(est(R)) est(R) ⊑ ⦇gen⦈ setify union est(R)` — (7.11)
    at the transitive `R`. -/
public theorem cyl_laws_step3 (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R) :
    (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
        : J.t ⟶ N.obj (PowerAllegory.powerObj I.t))
        ≫ setify (PowerAllegory.powerObj I.t) ≫ powerRel (est R) ≫ est R
      ⊑ ⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
          ≫ setify (PowerAllegory.powerObj I.t) ≫ bigUnion ≫ est R :=
  comp_mono_left _ (comp_mono_left _ (powerRel_est_le_bigUnion htrans))

/-- **cyl-laws** step 4: `⦇gen⦈ setify union est(R) = paths est(R)` — `paths`' definition. -/
public theorem cyl_laws_step4 (R : I.t ⟶ I.t) :
    (⦇gen F I moves trans zip moves_natural trans_natural zip_natural⦈
        : J.t ⟶ N.obj (PowerAllegory.powerObj I.t))
        ≫ setify (PowerAllegory.powerObj I.t) ≫ bigUnion ≫ est R
      = paths F I J moves trans zip setify moves_natural trans_natural zip_natural ≫ est R := by
  rw [paths]; simp only [Cat.assoc]

/-- **cyl-laws** (B&dM §7.4, p.182): `paths est(R) ⊒ ⦇Q⦈ setify est(R)` — a cheapest path
    across the cylinder is one fold over the columns that keeps, for every row, only the
    cheapest path that can start there.

    The chain is the book's: `paths` unfolds to `⦇gen⦈ setify union est(R)`; (7.11)
    replaces `union` by `P(est(R))` (`powerRel_est_le_bigUnion`, `R` transitive); `setify`'s
    lax square moves the minimum inside the tuple (`hsetify`); and fusion at `cyl_fusion`
    (`hfusion`) folds `Q` instead of `gen`. -/
public theorem cyl_laws (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R)
    (hfusion : (F.appl (N.obj A)).map (N.map (est R))
        ≫ Q F I moves trans zip moves_natural trans_natural zip_natural R
      ⊑ gen F I moves trans zip moves_natural trans_natural zip_natural ≫ N.map (est R)) :
    ⦇Q F I moves trans zip moves_natural trans_natural zip_natural R⦈ ≫ setify I.t ≫ est R
      ⊑ paths F I J moves trans zip setify moves_natural trans_natural zip_natural ≫ est R :=
  calc ⦇Q F I moves trans zip moves_natural trans_natural zip_natural R⦈ ≫ setify I.t ≫ est R
      ⊑ _ := cyl_laws_step1 F I J moves trans zip setify moves_natural trans_natural zip_natural
                setify_natural R hfusion
    _ ⊑ _ := cyl_laws_step2 F I J moves trans zip setify moves_natural trans_natural zip_natural
                setify_natural R
    _ ⊑ _ := cyl_laws_step3 F I J moves trans zip setify moves_natural trans_natural zip_natural
                setify_natural R htrans
    _ = _ := cyl_laws_step4 F I J moves trans zip setify moves_natural trans_natural zip_natural
                setify_natural R

end CylLaws

/-! ## `cyl-step` -/

/-- **cyl-step** (book p.183): read as a definition the fusion condition names `Q`, and
    opening the coproduct turns it into the program,
    `Q = [N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]`.

    The coproduct data is what the abstract setting does not carry, so it is given: `C` splits
    `F(NA,N(TA))` as `NA + NA×N(TA)`; `hGmap` is `F(𝟙,X) = 𝟙 + (𝟙×X)` with `pm ≜ 𝟙×X`;
    `hzip` is the book's `zip = 𝟙 + zip'` written with the injections it hides
    (`N(inl)` and `zip' N(inr)`); and `hwrap`, `hcons` are `α = [wrap,cons]`. -/
public theorem cyl_step {p₀ q₀ q : 𝒜} (R : I.t ⟶ I.t)
    (C : Coproduct (F.obj (N.obj A) (N.obj I.t)) (N.obj p₀) q)
    {pm : q ⟶ q} {zip' : q ⟶ N.obj q₀}
    {inlA : p₀ ⟶ F.obj A I.t} {inrA : q₀ ⟶ F.obj A I.t}
    {wrapA : p₀ ⟶ I.t} {consA : q₀ ⟶ I.t}
    (hGmap : (F.appl (N.obj A)).map (moves I.t ≫ trans I.t ≫ N.map (est R))
      = junc C C.u₁ (pm ≫ C.u₂))
    (hzip : zip I.t = junc C (N.map inlA) (zip' ≫ N.map inrA))
    (hwrap : inlA ≫ I.α = wrapA) (hcons : inrA ≫ I.α = consA) :
    Q F I moves trans zip moves_natural trans_natural zip_natural R
      = junc C (N.map wrapA) (pm ≫ zip' ≫ N.map consA) := by
  have hZ : zip I.t ≫ N.map I.α = junc C (N.map wrapA) (zip' ≫ N.map consA) := by
    rw [hzip, junc_comp, ← N.map_comp, hwrap, Cat.assoc, ← N.map_comp, hcons]
  rw [Q, hGmap, hZ, junc_comp, u₁_junc, Cat.assoc, u₂_junc]

/-! ## `Cylinder.OneRow` — the hypotheses at `n = 1`

  A cylinder one row high: `N ≜ 𝟙`, so a tuple is a square, `moves x = {x}` (up and down are
  the identity), `trans = 𝟙` and `zip = 𝟙` (a one-tuple commutes with everything), and
  `setify x = {x}`.  Every lax-naturality hypothesis of `cyl_fusion` and `cyl_laws` holds
  there, so none of them is vacuous. -/

namespace OneRow

/-- `moves = τ` at `N ≜ 𝟙`: the singleton's own lax square. -/
public theorem moves_natural_one :
    LaxNatural (Relator.comp (Relator.idRelator 𝒜) powerRelator) (Relator.idRelator 𝒜)
      (fun _ : 𝒜 => singletonMap) := fun R => singletonMap_powerRel_lax R

/-- `trans = 𝟙` at `N ≜ 𝟙`: a one-tuple commutes with everything, and the square is the unit laws. -/
public theorem trans_natural_one :
    LaxNatural (Relator.comp powerRelator (Relator.idRelator 𝒜))
      (Relator.comp (Relator.idRelator 𝒜) powerRelator)
      (fun x : 𝒜 => 𝟙 (PowerAllegory.powerObj x)) :=
  fun _ => le_of_eq ((Cat.comp_id _).trans (Cat.id_comp _).symm)

/-- `zip = 𝟙` at `N ≜ 𝟙`, at whichever base functor the one row is folded over. -/
public theorem zip_natural_one (K : Relator 𝒜 𝒜) :
    LaxNatural (Relator.comp K (Relator.idRelator 𝒜)) (Relator.comp (Relator.idRelator 𝒜) K)
      (fun x : 𝒜 => 𝟙 (K.obj x)) :=
  fun _ => le_of_eq ((Cat.comp_id _).trans (Cat.id_comp _).symm)

/-- `setify = τ` at `N ≜ 𝟙`: the same singleton square `moves` uses, at the bare power relator. -/
public theorem setify_natural_one :
    LaxNatural powerRelator (Relator.idRelator 𝒜) (fun _ : 𝒜 => singletonMap) :=
  fun R => singletonMap_powerRel_lax R

/-- **The `cyl-laws` headline with nothing assumed but (7.13)**: at `N ≜ 𝟙` — a cylinder one
    row high, where `moves` and `setify` are both `τ` and `trans` and `zip` are identities —
    every lax-naturality hypothesis of `cyl_fusion` and `cyl_laws` is discharged, by
    `singletonMap_powerRel_lax` and by the unit laws.  So those hypotheses are consistent, and
    `cyl_laws` is not vacuous.  At `N ≜ 𝟙` a column IS a square, so the two initial algebras
    are the one algebra `I`. -/
public theorem oneRow_laws {A : 𝒜} (I : InitialAlgebra (F.appl A)) (R : I.t ⟶ I.t)
    (htrans : R ≫ R ⊑ R)
    (h713 : (F.appl A).map (est R) ≫ I.α ⊑ cpMap (F.appl A) I.t ≫ existsImage I.α ≫ est R) :
    (⦇Q (N := Relator.idRelator 𝒜) F I (fun _ => singletonMap)
        (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (F.obj A x))
        moves_natural_one trans_natural_one (zip_natural_one (F.appl A)) R⦈ : I.t ⟶ I.t)
        ≫ singletonMap ≫ est R
      ⊑ paths (N := Relator.idRelator 𝒜) F I I (fun _ => singletonMap)
        (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (F.obj A x))
        (fun _ => singletonMap)
        moves_natural_one trans_natural_one (zip_natural_one (F.appl A)) ≫ est R :=
  cyl_laws (N := Relator.idRelator 𝒜) F I I (fun _ => singletonMap)
    (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (F.obj A x)) (fun _ => singletonMap)
    moves_natural_one trans_natural_one (zip_natural_one (F.appl A)) setify_natural_one
    R htrans
    (cyl_fusion (N := Relator.idRelator 𝒜) F I (fun _ => singletonMap)
      (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (F.obj A x))
      moves_natural_one trans_natural_one (zip_natural_one (F.appl A)) R htrans h713)

end OneRow

end Freyd.Alg.Cylinder
