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
  `H` the base functor `F(A,−)` of non-empty cons-lists (initial algebra `I`, so `I.t = L A`),
  `G` the same functor at the tuple element type, `F(NA,−)` (initial algebra `J`, so
  `J.t = L N A`), and `N` the `n`-tuple relator.

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
  {N G H : Relator 𝒜 𝒜} (I : InitialAlgebra H) (J : InitialAlgebra G)
  (moves : ∀ x : 𝒜, N.obj x ⟶ PowerAllegory.powerObj (N.obj x))
  (trans : ∀ x : 𝒜, PowerAllegory.powerObj (N.obj x) ⟶ N.obj (PowerAllegory.powerObj x))
  (zip : ∀ x : 𝒜, G.obj (N.obj x) ⟶ N.obj (H.obj x))
  (setify : ∀ x : 𝒜, N.obj x ⟶ PowerAllegory.powerObj x)

/-! ## `cyl-defn` -/

/-- **cyl-defn**: `gen ≜ F(𝟙,moves trans N(union)) zip N(cp P(α))`, of type
    `F(NA,N(E(LA)))⟶N(E(LA))` — one fold step, extending every path of every row by the new
    column. -/
@[expose] public noncomputable def gen :
    G.obj (N.obj (PowerAllegory.powerObj I.t)) ⟶ N.obj (PowerAllegory.powerObj I.t) :=
  G.map (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
      ≫ N.map (bigUnion (a := I.t)))
    ≫ zip (PowerAllegory.powerObj I.t) ≫ N.map (cpMap H I.t ≫ existsImage I.α)

/-- **cyl-defn**: `paths ≜ ⦇gen⦈ setify union`, of type `L N Nat⟶E(L Nat)` — every path
    across the cylinder. -/
@[expose] public noncomputable def paths : J.t ⟶ PowerAllegory.powerObj I.t :=
  ⦇gen I moves trans zip⦈ ≫ setify (PowerAllegory.powerObj I.t) ≫ bigUnion

/-- **cyl-defn**: the algebra the derivation's last step folds,
    `Q ≜ F(𝟙,moves trans N(est(R))) zip N(α)`. -/
@[expose] public noncomputable def Q (R : I.t ⟶ I.t) : G.obj (N.obj I.t) ⟶ N.obj I.t :=
  G.map (moves I.t ≫ trans I.t ≫ N.map (est R)) ≫ zip I.t ≫ N.map I.α

/-! ## `cyl-fusion` -/

/-- **(7.13)** (book p.182): `F(𝟙,est(R))α ⊑ cp P(α) est(R)` — extending every path in a set
    and then taking a minimum is beaten by extending one minimum.  Theorem 7.1
    (`distributes_of_monotonicAlg`) at the map `α`, with `Λ(F(𝟙,∋)α) = cp P(α)`
    (`Λ_absorption`, `cp = Λ(F(𝟙,∋))`).  The book's "the monotonicity condition is that `α` is
    monotonic on `R` and is easy to verify" is the hypothesis `hmono`. -/
public theorem cyl_7_13 (hHr : H.PreservesRecip) (R : I.t ⟶ I.t)
    (hmono : MonotonicAlg I.α R°) :
    H.map (est R) ≫ I.α ⊑ cpMap H I.t ≫ existsImage I.α ≫ est R := by
  have hcp : cpMap H I.t ≫ existsImage I.α = Λ (H.map (∋ I.t) ≫ I.α) := Λ_absorption _ _
  have hd : Distributes I.α R := distributes_of_monotonicAlg I.α_map hHr hmono
  calc H.map (est R) ≫ I.α ⊑ Λ (H.map (∋ I.t) ≫ I.α) ≫ est R := hd
    _ = cpMap H I.t ≫ existsImage I.α ≫ est R := by rw [← hcp, Cat.assoc]

/-- **cyl-fusion** (book pp.182-183): `gen N(est(R)) ⊒ F(𝟙,N(est(R)))Q` — the fusion
    condition of `cyl-laws`' last step.  `gen` kills the base functor before the minimum
    is taken inside the tuple; `Q` kills it after, and that swap is the whole step.

    The four hypotheses are the book's own justifications, at the one relation each is used
    at: (7.13) `h713`; `moves`, `trans` and `zip` lax natural (`hmoves`, `htransN`, `hzip`);
    and (7.11) distribution over union, which is `powerRel_est_le_bigUnion` at the transitive
    `R`. -/
public theorem cyl_fusion (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R)
    (h713 : H.map (est R) ≫ I.α ⊑ cpMap H I.t ≫ existsImage I.α ≫ est R)
    (hmoves : N.map (est R) ≫ moves I.t
      ⊑ moves (PowerAllegory.powerObj I.t) ≫ powerRel (N.map (est R)))
    (htransN : powerRel (N.map (est R)) ≫ trans I.t
      ⊑ trans (PowerAllegory.powerObj I.t) ≫ N.map (powerRel (est R)))
    (hzip : G.map (N.map (est R)) ≫ zip I.t
      ⊑ zip (PowerAllegory.powerObj I.t) ≫ N.map (H.map (est R))) :
    G.map (N.map (est R)) ≫ Q I moves trans zip R
      ⊑ gen I moves trans zip ≫ N.map (est R) := by
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
  have houter : N.map (H.map (est R)) ≫ N.map I.α
      ⊑ N.map (cpMap H I.t ≫ existsImage I.α) ≫ N.map (est R) := by
    calc N.map (H.map (est R)) ≫ N.map I.α = N.map (H.map (est R) ≫ I.α) := by rw [N.map_comp]
      _ ⊑ N.map (cpMap H I.t ≫ existsImage I.α ≫ est R) := N.map_mono h713
      _ = N.map (cpMap H I.t ≫ existsImage I.α) ≫ N.map (est R) := by
          rw [← N.map_comp, Cat.assoc]
  calc G.map (N.map (est R)) ≫ Q I moves trans zip R
      = G.map (N.map (est R) ≫ moves I.t ≫ trans I.t ≫ N.map (est R))
          ≫ zip I.t ≫ N.map I.α := by
        rw [Q, ← Cat.assoc, ← G.map_comp]
    _ ⊑ G.map ((moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t))) ≫ N.map (est R)) ≫ zip I.t ≫ N.map I.α :=
        comp_mono_right (G.map_mono hinner) _
    _ = G.map (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t)))
          ≫ (G.map (N.map (est R)) ≫ zip I.t) ≫ N.map I.α := by
        rw [G.map_comp]; simp only [Cat.assoc]
    _ ⊑ G.map (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t)))
          ≫ (zip (PowerAllegory.powerObj I.t) ≫ N.map (H.map (est R))) ≫ N.map I.α :=
        comp_mono_left _ (comp_mono_right hzip _)
    _ = G.map (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t)))
          ≫ zip (PowerAllegory.powerObj I.t) ≫ N.map (H.map (est R)) ≫ N.map I.α := by
        simp only [Cat.assoc]
    _ ⊑ G.map (moves (PowerAllegory.powerObj I.t) ≫ trans (PowerAllegory.powerObj I.t)
          ≫ N.map (bigUnion (a := I.t)))
          ≫ zip (PowerAllegory.powerObj I.t)
          ≫ N.map (cpMap H I.t ≫ existsImage I.α) ≫ N.map (est R) :=
        comp_mono_left _ (comp_mono_left _ houter)
    _ = gen I moves trans zip ≫ N.map (est R) := by
        rw [gen]; simp only [Cat.assoc]

/-! ## `cyl-laws` -/

/-- **cyl-laws** (B&dM §7.4, p.182): `paths est(R) ⊒ ⦇Q⦈ setify est(R)` — a cheapest path
    across the cylinder is one fold over the columns that keeps, for every row, only the
    cheapest path that can start there.

    The chain is the book's: `paths` unfolds to `⦇gen⦈ setify union est(R)`; (7.11)
    replaces `union` by `P(est(R))` (`powerRel_est_le_bigUnion`, `R` transitive); `setify`'s
    lax square moves the minimum inside the tuple (`hsetify`); and fusion at `cyl_fusion`
    (`hfusion`) folds `Q` instead of `gen`. -/
public theorem cyl_laws (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R)
    (hfusion : G.map (N.map (est R)) ≫ Q I moves trans zip R
      ⊑ gen I moves trans zip ≫ N.map (est R))
    (hsetify : N.map (est R) ≫ setify I.t ≫ est R
      ⊑ setify (PowerAllegory.powerObj I.t) ≫ powerRel (est R) ≫ est R) :
    ⦇Q I moves trans zip R⦈ ≫ setify I.t ≫ est R
      ⊑ paths I J moves trans zip setify ≫ est R := by
  -- fusion: `⦇Q⦈ ⊑ ⦇gen⦈ N(est R)`, by the least-prefixed-point property of `⦇Q⦈`
  have hcata : (⦇Q I moves trans zip R⦈ : J.t ⟶ N.obj I.t)
      ⊑ ⦇gen I moves trans zip⦈ ≫ N.map (est R) := by
    apply relCata_le_of_prefixed J
    calc J.α° ≫ G.map (⦇gen I moves trans zip⦈ ≫ N.map (est R))
            ≫ Q I moves trans zip R
        = J.α° ≫ G.map ⦇gen I moves trans zip⦈
            ≫ G.map (N.map (est R)) ≫ Q I moves trans zip R := by
          rw [G.map_comp]; simp only [Cat.assoc]
      _ ⊑ J.α° ≫ G.map ⦇gen I moves trans zip⦈
            ≫ gen I moves trans zip ≫ N.map (est R) :=
          comp_mono_left _ (comp_mono_left _ hfusion)
      _ = J.α° ≫ (J.α ≫ ⦇gen I moves trans zip⦈) ≫ N.map (est R) := by
          rw [relCata_cancel J]; simp only [Cat.assoc]
      _ = ⦇gen I moves trans zip⦈ ≫ N.map (est R) := by
          rw [← Cat.assoc, ← Cat.assoc, J.recip_alpha_alpha, Cat.id_comp]
  calc ⦇Q I moves trans zip R⦈ ≫ setify I.t ≫ est R
      ⊑ (⦇gen I moves trans zip⦈ ≫ N.map (est R)) ≫ setify I.t ≫ est R :=
        comp_mono_right hcata _
    _ = ⦇gen I moves trans zip⦈ ≫ N.map (est R) ≫ setify I.t ≫ est R := by
        simp only [Cat.assoc]
    _ ⊑ ⦇gen I moves trans zip⦈
          ≫ setify (PowerAllegory.powerObj I.t) ≫ powerRel (est R) ≫ est R :=
        comp_mono_left _ hsetify
    _ ⊑ ⦇gen I moves trans zip⦈
          ≫ setify (PowerAllegory.powerObj I.t) ≫ bigUnion ≫ est R :=
        comp_mono_left _ (comp_mono_left _ (powerRel_est_le_bigUnion htrans))
    _ = paths I J moves trans zip setify ≫ est R := by rw [paths]; simp only [Cat.assoc]

/-! ## `cyl-step` -/

/-- **cyl-step** (book p.183): read as a definition the fusion condition names `Q`, and
    opening the coproduct turns it into the program,
    `Q = [N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]`.

    The coproduct data is what the abstract setting does not carry, so it is given: `C` splits
    `F(NA,N(LA))` as `NA + NA×N(LA)`; `hGmap` is `F(𝟙,X) = 𝟙 + (𝟙×X)` with `pm ≜ 𝟙×X`;
    `hzip` is the book's `zip = 𝟙 + zip'` written with the injections it hides
    (`N(inl)` and `zip' N(inr)`); and `hwrap`, `hcons` are `α = [wrap,cons]`. -/
public theorem cyl_step {p₀ q₀ q : 𝒜} (R : I.t ⟶ I.t)
    (C : Coproduct (G.obj (N.obj I.t)) (N.obj p₀) q)
    {pm : q ⟶ q} {zip' : q ⟶ N.obj q₀}
    {inlA : p₀ ⟶ H.obj I.t} {inrA : q₀ ⟶ H.obj I.t}
    {wrapA : p₀ ⟶ I.t} {consA : q₀ ⟶ I.t}
    (hGmap : G.map (moves I.t ≫ trans I.t ≫ N.map (est R)) = junc C C.u₁ (pm ≫ C.u₂))
    (hzip : zip I.t = junc C (N.map inlA) (zip' ≫ N.map inrA))
    (hwrap : inlA ≫ I.α = wrapA) (hcons : inrA ≫ I.α = consA) :
    Q I moves trans zip R = junc C (N.map wrapA) (pm ≫ zip' ≫ N.map consA) := by
  have hZ : zip I.t ≫ N.map I.α = junc C (N.map wrapA) (zip' ≫ N.map consA) := by
    rw [hzip, junc_comp, ← N.map_comp, hwrap, Cat.assoc, ← N.map_comp, hcons]
  rw [Q, hGmap, hZ, junc_comp, u₁_junc, Cat.assoc, u₂_junc]

/-! ## `Cylinder.OneRow` — the hypotheses at `n = 1`

  A cylinder one row high: `N ≜ 𝟙`, so a tuple is a square, `moves x = {x}` (up and down are
  the identity), `trans = 𝟙` and `zip = 𝟙` (a one-tuple commutes with everything), and
  `setify x = {x}`.  Every lax-naturality hypothesis of `cyl_fusion` and `cyl_laws` holds
  there, so none of them is vacuous. -/

namespace OneRow

/-- `τ` is lax natural from `𝟙` to `P`: `S τ ⊑ τ P(S)` — the singleton of an `S`-image is an
    Egli-Milner `S`-image of the singleton.  Shunting across the map `τ` leaves the two halves
    of `powerRel`, each of which `τ ∋ = 𝟙` collapses.  It is `moves` and `setify` at `n = 1`. -/
public theorem comp_singletonMap_le {a b : 𝒜} (S : a ⟶ b) :
    S ≫ singletonMap ⊑ singletonMap ≫ powerRel S := by
  apply (map_shunt_left (Λ_is_map' (𝟙 a)) _ _).mp
  refine le_inter ?_ ?_
  · apply (le_leftDiv_iff _ _ _).mpr
    calc (∋ a)° ≫ singletonMap° ≫ S ≫ singletonMap
        = ((singletonMap ≫ ∋ a)°) ≫ S ≫ singletonMap := by
          rw [Allegory.recip_comp]; simp only [Cat.assoc]
      _ = S ≫ singletonMap := by rw [singletonMap_comp_eps, recip_id, Cat.id_comp]
      _ ⊑ S ≫ (∋ b)° := comp_mono_left _ singletonMap_le_recip_eps
  · apply (le_div_iff _ _ _).mpr
    calc (singletonMap° ≫ S ≫ singletonMap) ≫ ∋ b
        = singletonMap° ≫ S ≫ singletonMap ≫ ∋ b := by simp only [Cat.assoc]
      _ = singletonMap° ≫ S := by rw [singletonMap_comp_eps, Cat.comp_id]
      _ ⊑ ∋ a ≫ S := comp_mono_right singletonMap_recip_le_eps _

/-- **The `cyl-laws` headline with nothing assumed but (7.13)**: at `N ≜ 𝟙` — a cylinder one
    row high, where `moves` and `setify` are both `τ` and `trans` and `zip` are identities —
    every lax-naturality hypothesis of `cyl_fusion` and `cyl_laws` is discharged, by
    `comp_singletonMap_le` and by the unit laws.  So those hypotheses are consistent, and
    `cyl_laws` is not vacuous. -/
public theorem oneRow_laws (I : InitialAlgebra H) (R : I.t ⟶ I.t) (htrans : R ≫ R ⊑ R)
    (h713 : H.map (est R) ≫ I.α ⊑ cpMap H I.t ≫ existsImage I.α ≫ est R) :
    ⦇Q (N := Relator.idRelator 𝒜) (G := H) I (fun _ => singletonMap)
        (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (H.obj x)) R⦈
        ≫ singletonMap ≫ est R
      ⊑ paths (N := Relator.idRelator 𝒜) (G := H) I I (fun _ => singletonMap)
        (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (H.obj x))
        (fun _ => singletonMap) ≫ est R := by
  refine cyl_laws (N := Relator.idRelator 𝒜) (G := H) I I (fun _ => singletonMap)
    (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (H.obj x)) (fun _ => singletonMap)
    R htrans
    (cyl_fusion (N := Relator.idRelator 𝒜) (G := H) I (fun _ => singletonMap)
      (fun x => 𝟙 (PowerAllegory.powerObj x)) (fun x => 𝟙 (H.obj x)) R htrans h713
      (comp_singletonMap_le (est R))
      (le_of_eq ((Cat.comp_id _).trans (Cat.id_comp _).symm))
      (le_of_eq ((Cat.comp_id _).trans (Cat.id_comp _).symm))) ?_
  show est R ≫ singletonMap ≫ est R ⊑ singletonMap ≫ powerRel (est R) ≫ est R
  rw [← Cat.assoc, ← Cat.assoc]
  exact comp_mono_right (comp_singletonMap_le (est R)) _

end OneRow

end Freyd.Alg.Cylinder

