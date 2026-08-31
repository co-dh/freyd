/-
  Bird & de Moor, *Algebra of Programming* §7.3  Planning a company party (book pp. 175-177).

  The party problem (Cormen–Leiserson–Rivest): the company is a tree of employees `tree A =
  node(A, list(tree A))`, each with a conviviality `rating`; choose a guest list maximising total
  rating such that no employee attends with their immediate supervisor.  Formally, maximise
  `max R · Λparty`, where `party = ⦇⟨include, exclude⟩⦈ : list A ← tree A` builds two candidate
  parties (root-in / root-out), `choose = outl ∪ outr` picks one, and `R = (sum·list rating)°·leq·
  (sum·list rating)` orders guest lists by total rating.  The moral (B&dM p.176): this looks like
  dynamic programming but is solved by a GREEDY algorithm.

  Given the two monotonicity claims B&dM leave as exercises — `choose` monotonic on `R`, and
  `⟨include, exclude⟩` monotonic on `R×R` — the greedy theorem (`A7_2.greedy`) yields the
  algorithm.  The first claim is `choose_monotonic` (a general product fact); everything else
  is concrete in `Rel(Set)`: the rose tree is `AOP.A6_RoseTree`, and the `RelSet.Party`
  namespace below builds `cost`/`R`/`include`/`exclude`/`S`/`party` (each certified against its
  point-free `party-defn` row), proves the branch rows and the headline monotonicity
  `(𝟙×list((R×R)°))S ⊑ S(R×R)°` (`party_mono`), and runs the note's `party-laws` derivation
  down to the greedy program (`party_laws`).  Ratings land in `Int` (the book says `Real`;
  Mathlib-free, so the ordered field is out of reach and never needed — only `+`/`≤`).
-/
module

public import AOP.A7_2
public import AOP.A5_2
public import AOP.A6_RoseTree
public import AOP.A7_4_Horner

universe u

namespace Freyd.Alg

/-! ## The `choose` relation and its monotonicity (B&dM p.177, first claim) -/

section Choose

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {a : 𝒜}

/-- **B&dM p.176**: `choose = outl ∪ outr` — pick either component of a pair (either party). -/
@[expose] public def choose (P : RelProd a a) : P.p ⟶ a := P.outl ∪ P.outr

/-- **§7.3 (B&dM p.177), first monotonicity claim** ("left as a simple exercise"): `choose` is
    monotonic on `R`, i.e. `choose·(R×R) ⊆ R·choose` (mirrored `(R×R) ≫ choose ⊑ choose ≫ R`).
    Immediate from the product projection laws `prodMap ≫ outl ⊑ outl ≫ R` (and `outr`) and the
    distributivity of composition over `∪`. -/
public theorem choose_monotonic (P : RelProd a a) (R : a ⟶ a) :
    prodMap P P R R ≫ choose P ⊑ choose P ≫ R := by
  show prodMap P P R R ≫ (P.outl ∪ P.outr) ⊑ (P.outl ∪ P.outr) ≫ R
  rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
  exact union_mono (prodMap_outl_le P P R R) (prodMap_outr_le P P R R)

end Choose

/-! ## Generic `Rel(Set)` est facts the derivation consumes -/

namespace RelSet

open CL ListRel

/-- A map is its own best output for a reflexive order: `f ⊑ Λ(f) est(Q)` when `𝟙 ⊑ Q`. -/
public theorem graph_le_Λ_est {a b : RelSet.{0}} (f : a.carrier → b.carrier) {Q : b ⟶ b}
    (hrefl : 𝟙 b ⊑ Q) : graph f ⊑ Λ (graph f) ≫ est(Q) := by
  apply le_iff.mpr; intro x y hy
  refine ⟨fun z => graph f x z, by rw [Λ_eq_classifier]; rfl, ?_⟩
  refine ⟨hy, fun z hz => ?_⟩
  exact le_iff.mp hrefl y z ((show y = f x from hy).trans (show z = f x from hz).symm)

/-- **Ex 7.15 (B&dM p.169) in `Rel(Set)`**: componentwise bests assemble to a pairwise best,
    `⟨Λ(U) est(Ra°), Λ(V) est(Rb°)⟩ ⊑ Λ(⟨U,V⟩) est((Ra×Rb)°)`. -/
public theorem pair_est_le {c a b : RelSet.{0}} (U : c ⟶ a) (V : c ⟶ b)
    (Ra : a ⟶ a) (Rb : b ⟶ b) :
    rpair (Λ U ≫ est(Ra°)) (Λ V ≫ est(Rb°)) ⊑ Λ (rpair U V) ≫ est((rprodMap Ra Rb)°) := by
  apply le_iff.mpr; intro x p hp
  obtain ⟨⟨Pu, hPu, hest1⟩, ⟨Pv, hPv, hest2⟩⟩ := hp
  have hPu' : Pu = fun y => U x y := by rw [Λ_eq_classifier] at hPu; exact hPu
  have hPv' : Pv = fun y => V x y := by rw [Λ_eq_classifier] at hPv; exact hPv
  subst hPu' hPv'
  obtain ⟨hU1, hUb⟩ := (est_apply _ _ _).mp hest1
  obtain ⟨hV1, hVb⟩ := (est_apply _ _ _).mp hest2
  refine ⟨fun q => rpair U V x q, by rw [Λ_eq_classifier]; rfl, ?_⟩
  exact (est_apply _ _ _).mpr ⟨⟨hU1, hV1⟩, fun q hq => ⟨hUb q.1 hq.1, hVb q.2 hq.2⟩⟩

/-! ## The party itself (the note's `party-defn` table, concretely) -/

namespace Party

open RT (Rose dRose)

variable {A : Type} (rating : A → Int)

/-- `sum : list Real ⟶ Real` at `Real := Int`. -/
@[expose] public def csum : ConsList Unit Int → Int
  | ConsList.wrap _ => 0
  | ConsList.cons n x => n + csum x

/-- **party-defn**: `cost ≜ list(rating) sum` — what a guest list is worth (one recursion;
    `cost_eq` is the point-free form). -/
@[expose] public def costFn : ConsList Unit A → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => rating a + costFn x

/-- `cost = list(rating) sum`, point-free. -/
public theorem cost_eq :
    (graph (costFn rating) : dList A ⟶ (⟨Int⟩ : RelSet.{0}))
      = list (graph rating) ≫ (graph csum : dList Int ⟶ (⟨Int⟩ : RelSet.{0})) := by
  have hcm : ∀ x, csum (cmap rating x) = costFn rating x := by
    intro x
    induction x with
    | wrap u => rfl
    | cons a x ih =>
        show rating a + csum (cmap rating x) = rating a + costFn rating x
        rw [ih]
  apply hom_ext; intro x n
  constructor
  · intro h
    exact ⟨cmap rating x, (listP_graph rating x _).mpr rfl,
      show n = csum (cmap rating x) by rw [hcm, ← (show n = costFn rating x from h)]⟩
  · rintro ⟨ns, hns, hsum⟩
    show n = costFn rating x
    rw [(show n = csum ns from hsum), (listP_graph rating x ns).mp hns, hcm]

/-- The order `≤` on `Int` as a relation. -/
@[expose] public def leq : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun m n => m ≤ n

/-- **party-defn**: `R ≜ cost ≤ cost°` — guest lists by total rating (`x R y` iff
    `cost x ≤ cost y`; `R_eq` is the point-free form). -/
@[expose] public def R : dList A ⟶ dList A := fun x y => costFn rating x ≤ costFn rating y

/-- `R = cost ≤ cost°`, point-free. -/
public theorem R_eq : R rating = graph (costFn rating) ≫ leq ≫ (graph (costFn rating))° := by
  apply hom_ext; intro x y
  constructor
  · intro h; exact ⟨costFn rating x, rfl, costFn rating y, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    show costFn rating x ≤ costFn rating y
    rw [← (show m = costFn rating x from hm), ← (show n = costFn rating y from hn)]
    exact hmn

/-- `R` is reflexive. -/
public theorem R_refl : 𝟙 (dList A) ⊑ R rating :=
  le_iff.mpr fun x y h => by obtain rfl : x = y := h; exact Int.le_refl _

/-- `R` is transitive. -/
public theorem R_trans : R rating ≫ R rating ⊑ R rating :=
  le_iff.mpr fun _ _ ⟨_, h1, h2⟩ => Int.le_trans h1 h2

/-- `(R×R)°` is transitive — what the greedy theorem asks of the pair order. -/
public theorem RR_recip_trans :
    (rprodMap (R rating) (R rating))° ≫ (rprodMap (R rating) (R rating))°
      ⊑ (rprodMap (R rating) (R rating))° :=
  le_iff.mpr fun _ _ ⟨_, h1, h2⟩ =>
    ⟨Int.le_trans h2.1 h1.1, Int.le_trans h2.2 h1.2⟩

/-! ### The two algebras and `S = ⟨include, exclude⟩` -/

/-- **party-defn**: `include ≜ (𝟙×(list(π₂) concat)) cons`, concretely — the party that invites
    the root, which puts every immediate subtree's root out.  A map (`include_eq` is the
    point-free form). -/
@[expose] public def includeFn :
    A × ConsList Unit (ConsList Unit A × ConsList Unit A) → ConsList Unit A :=
  fun u => ConsList.cons u.1 (cconcat (cmap Prod.snd u.2))

/-- `include = (𝟙×(list(π₂) concat)) cons`, point-free. -/
public theorem include_eq :
    (graph includeFn
        : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A)
      = rprodMap (𝟙 (dE A)) (list (graph Prod.snd) ≫ concatR) ≫ consR := by
  apply hom_ext; intro u y
  constructor
  · intro h
    exact ⟨(u.1, cconcat (cmap Prod.snd u.2)),
      ⟨rfl, ⟨cmap Prod.snd u.2, (listP_graph _ _ _).mpr rfl, rfl⟩⟩, h⟩
  · rintro ⟨v, ⟨hv1, zs, hzs, hv2⟩, hy⟩
    show y = includeFn u
    rw [(show y = ConsList.cons v.1 v.2 from hy), ← (show u.1 = v.1 from hv1),
      (show v.2 = cconcat zs from hv2), (listP_graph _ _ _).mp hzs]
    rfl

/-- **party-defn**: `choose ≜ π₁∪π₂`, concretely — takes one of the two parties a subtree
    returns.  `choose_eq` ties it to `choose` at the §5.2 product, whose `tab` is the one
    classically chosen ingredient — kept out of the working statements' closures. -/
@[expose] public def chooseR : (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  graph Prod.fst ∪ graph Prod.snd

/-- `chooseR` IS `choose` at `Rel(Set)`'s own product. -/
public theorem choose_eq : choose (relProd (dList A) (dList A)) = chooseR (A := A) := rfl

/-- **party-defn**: `exclude ≜ (𝟙×(list(choose) concat))π₂`, concretely — the party that leaves
    the root out, so each subtree is free to choose.  Not a map (`exclude_eq` is the
    point-free form). -/
@[expose] public def excludeR :
    (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A :=
  fun u y => ∃ qs, listP chooseR u.2 qs ∧ y = cconcat qs

/-- `exclude = (𝟙×(list(choose) concat))π₂`, point-free. -/
public theorem exclude_eq :
    excludeR = rprodMap (𝟙 (dE A)) (list chooseR ≫ concatR)
      ≫ graph Prod.snd := by
  apply hom_ext; intro u y
  constructor
  · rintro ⟨qs, hqs, hy⟩
    exact ⟨(u.1, cconcat qs), ⟨rfl, qs, hqs, rfl⟩, hy ▸ rfl⟩
  · rintro ⟨v, ⟨hv1, qs, hqs, hv2⟩, hy⟩
    exact ⟨qs, hqs, by
      rw [(show y = v.2 from hy), (show v.2 = cconcat qs from hv2)]⟩

/-- **party-defn**: `S ≜ ⟨include, exclude⟩` — the algebra: one step returns both parties of a
    subtree at once (`pair_eq_rpair` ties `rpair` to the §5.2 `⟨,⟩`). -/
@[expose] public def S :
    (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
      ⟶ (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) :=
  rpair (graph includeFn) excludeR

/-- **party-defn**: `party ≜ ⦇S⦈ choose` — every guest list the president's ruling allows
    (structural fold; `party_eq` is the relational-catamorphism form). -/
@[expose] public def party : dRose A ⟶ dList A :=
  RT.cataR S ≫ chooseR

/-- `party = ⦇S⦈ choose`. -/
public theorem party_eq : party (A := A) = ⦇S⦈ ≫ chooseR := by
  show RT.cataR S ≫ chooseR = _
  rw [RT.cataR_eq_relCata]

/-! ### The two leaves of `party-mono-branch` (B&dM's exercises: `cost` is a sum) -/

/-- `cost` adds over append. -/
theorem costFn_append (x y : ConsList Unit A) :
    costFn rating (cappend x y) = costFn rating x + costFn rating y := by
  induction x with
  | wrap u => show costFn rating y = 0 + costFn rating y; omega
  | cons a x ih =>
      show rating a + costFn rating (cappend x y) = rating a + costFn rating x + costFn rating y
      rw [ih]; omega

/-- A cheaper part makes a cheaper whole: elementwise `R°`-related segment lists have
    `R°`-related concatenations. -/
theorem cost_cconcat_le : ∀ {xss yss : ConsList Unit (ConsList Unit A)},
    listP ((R rating)°) xss yss →
    costFn rating (cconcat yss) ≤ costFn rating (cconcat xss)
  | ConsList.wrap _, ConsList.wrap _, _ => Int.le_refl _
  | ConsList.wrap _, ConsList.cons _ _, h => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h => h.elim
  | ConsList.cons xs xss, ConsList.cons ys yss, ⟨h1, h2⟩ => by
      have ih := cost_cconcat_le h2
      have h1' : costFn rating ys ≤ costFn rating xs := h1
      show costFn rating (cappend ys (cconcat yss)) ≤ costFn rating (cappend xs (cconcat xss))
      rw [costFn_append, costFn_append]; omega

/-- **party-mono-branch `concat` row** (a LEAF, B&dM's exercise): `list(R°) concat ⊑ concat R°`
    — `cost` is a sum, so a cheaper part makes a cheaper whole. -/
public theorem concat_monotonic :
    list ((R rating)°) ≫ concatR ⊑ concatR ≫ (R rating)° := by
  apply le_iff.mpr; intro xss y
  rintro ⟨yss, hl, hy⟩
  refine ⟨cconcat xss, rfl, ?_⟩
  show costFn rating y ≤ costFn rating (cconcat xss)
  rw [(show y = cconcat yss from hy)]
  exact cost_cconcat_le rating hl

/-- **party-mono-branch `h:=cons` row** (a LEAF, B&dM's exercise): `(𝟙×R°) cons ⊑ cons R°`
    — `cost(cons(a,xs)) = rating(a) + cost(xs)`, so a cheaper tail makes a cheaper list. -/
public theorem cons_monotonic :
    rprodMap (𝟙 (dE A)) ((R rating)°) ≫ consR ⊑ consR ≫ (R rating)° := by
  apply le_iff.mpr; intro u y
  rintro ⟨v, ⟨hv1, hv2⟩, hy⟩
  refine ⟨ConsList.cons u.1 u.2, rfl, ?_⟩
  show costFn rating y ≤ costFn rating (ConsList.cons u.1 u.2)
  rw [(show y = ConsList.cons v.1 v.2 from hy), ← (show u.1 = v.1 from hv1)]
  show rating u.1 + costFn rating v.2 ≤ rating u.1 + costFn rating u.2
  have h2 : costFn rating v.2 ≤ costFn rating u.2 := hv2
  omega

/-! ### `party-mono-branch`: one branch `(𝟙×(list(g) concat)) h`, then the two instances -/

/-- **party-mono-branch**: a branch `(𝟙×(list(g) concat)) h` is monotonic on `(R×R)°` given its
    `g` row (`(R×R)°g ⊑ gR°`) and its `h` row (`(𝟙×R°)h ⊑ hR°`); the `concat` leaf and the
    `list` relator laws supply the middle. -/
public theorem branch_monotonic {g : (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A}
    {h : (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dList A}
    (hg : (rprodMap (R rating) (R rating))° ≫ g ⊑ g ≫ (R rating)°)
    (hh : rprodMap (𝟙 (dE A)) ((R rating)°) ≫ h ⊑ h ≫ (R rating)°) :
    rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))°))
        ≫ (rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ h)
      ⊑ (rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ h) ≫ (R rating)° := by
  have e1 : rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))°))
        ≫ (rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ h)
      = rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))° ≫ g) ≫ concatR) ≫ h := by
    rw [← Cat.assoc, rprodMap_comp, Cat.id_comp,
      ← Cat.assoc (list ((rprodMap (R rating) (R rating))°)) (list g) concatR, ← list_comp]
  have s1 : rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))° ≫ g) ≫ concatR) ≫ h
      ⊑ rprodMap (𝟙 (dE A)) (list (g ≫ (R rating)°) ≫ concatR) ≫ h :=
    comp_mono_right (rprodMap_mono (le_refl _) (comp_mono_right (list_mono hg) concatR)) h
  have e2 : rprodMap (𝟙 (dE A)) (list (g ≫ (R rating)°) ≫ concatR) ≫ h
      = rprodMap (𝟙 (dE A)) (list g ≫ (list ((R rating)°) ≫ concatR)) ≫ h := by
    rw [list_comp, Cat.assoc]
  have s2 : rprodMap (𝟙 (dE A)) (list g ≫ (list ((R rating)°) ≫ concatR)) ≫ h
      ⊑ rprodMap (𝟙 (dE A)) (list g ≫ (concatR ≫ (R rating)°)) ≫ h :=
    comp_mono_right (rprodMap_mono (le_refl _) (comp_mono_left _ (concat_monotonic rating))) h
  have e3 : rprodMap (𝟙 (dE A)) (list g ≫ (concatR ≫ (R rating)°)) ≫ h
      = rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ (rprodMap (𝟙 (dE A)) ((R rating)°) ≫ h) := by
    rw [← Cat.assoc (list g) concatR ((R rating)°), ← Cat.assoc, rprodMap_comp, Cat.id_comp]
  have s3 : rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ (rprodMap (𝟙 (dE A)) ((R rating)°) ≫ h)
      ⊑ rprodMap (𝟙 (dE A)) (list g ≫ concatR) ≫ (h ≫ (R rating)°) := comp_mono_left _ hh
  exact le_trans (le_of_eq e1) (le_trans s1 (le_trans (le_of_eq e2) (le_trans s2
    (le_trans (le_of_eq e3) (le_trans s3 (le_of_eq (Cat.assoc _ _ _).symm))))))

/-- **party-mono-branch, `include` row**: `(𝟙×list((R×R)°)) include ⊑ include R°` —
    `g := π₂` (laws 1 and 4 of the product calculus, concretely) and `h := cons`. -/
public theorem include_monotonic :
    rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))°)) ≫ graph includeFn
      ⊑ graph includeFn ≫ (R rating)° := by
  rw [include_eq]
  refine branch_monotonic rating ?_ (cons_monotonic rating)
  -- the `g := π₂` row: `(R×R)°π₂ ⊑ π₂R°`
  apply le_iff.mpr; intro p y
  rintro ⟨q, hq, hy⟩
  exact ⟨p.2, rfl, by
    show costFn rating y ≤ costFn rating p.2
    rw [(show y = q.2 from hy)]
    exact hq.2⟩

/-- **party-mono-branch `g := choose` row / Ex 7.38's hypothesis**: `(R×R)°choose ⊑ choose R°`
    — `choose_monotonic` at `R°` (via `choose_eq` and `(R×R)° = R°×R°`), re-proved on the
    graph-level spelling so its closure stays free of `topMor`'s classical choice. -/
public theorem chooseR_monotonic :
    (rprodMap (R rating) (R rating))° ≫ chooseR ⊑ chooseR ≫ (R rating)° := by
  apply le_iff.mpr; intro p y
  rintro ⟨q, hq, hy⟩
  rcases (show y = q.1 ∨ y = q.2 from hy) with hy1 | hy2
  · exact ⟨p.1, Or.inl rfl, by
      show costFn rating y ≤ costFn rating p.1; rw [hy1]; exact hq.1⟩
  · exact ⟨p.2, Or.inr rfl, by
      show costFn rating y ≤ costFn rating p.2; rw [hy2]; exact hq.2⟩

/-- **party-mono-branch, `exclude` row**: `(𝟙×list((R×R)°)) exclude ⊑ exclude R°` —
    `g := choose` (`chooseR_monotonic`) and `h := π₂` (an equality, `rprodMap_id_snd`). -/
public theorem exclude_monotonic :
    rprodMap (𝟙 (dE A)) (list ((rprodMap (R rating) (R rating))°)) ≫ excludeR
      ⊑ excludeR ≫ (R rating)° := by
  rw [exclude_eq]
  exact branch_monotonic rating (chooseR_monotonic rating) (le_of_eq (rprodMap_id_snd _))

/-! ### The headline: `S` is monotonic on `(R×R)°` (the note's `party-mono`) -/

/-- **§7.3's headline (the note's `party-mono`)**: `(𝟙×list((R×R)°))S ⊑ S(R×R)°` — bettering
    both parties of every subtree before the node's algebra runs gets no further than running
    it first and bettering the two parties it returns.  This is `MonotonicAlg S ((R×R)°)` for
    the rose-tree base relator, so the greedy theorem applies. -/
public theorem party_mono :
    (RT.F A).map ((rprodMap (R rating) (R rating))°) ≫ S
      ⊑ S ≫ (rprodMap (R rating) (R rating))° := by
  apply le_iff.mpr; intro u p
  rintro ⟨v, hv, hi, he⟩
  obtain ⟨z1, hz1, hR1⟩ := le_iff.mp (include_monotonic rating) u p.1 ⟨v, hv, hi⟩
  obtain ⟨z2, hz2, hR2⟩ := le_iff.mp (exclude_monotonic rating) u p.2 ⟨v, hv, he⟩
  exact ⟨(z1, z2), ⟨hz1, hz2⟩, hR1, hR2⟩

/-! ### The derivation (the note's `party-laws` table) -/

/-- Elementwise: what `Λ(choose) est(R°)` keeps dominates whatever `choose` could return. -/
theorem best_dominates :
    ∀ (l : ConsList Unit (ConsList Unit A × ConsList Unit A))
      (ys qs : ConsList Unit (ConsList Unit A)),
      listP (Λ chooseR ≫ est((R rating)°)) l ys →
      listP chooseR l qs →
      listP ((R rating)°) ys qs
  | ConsList.wrap _, ConsList.wrap _, ConsList.wrap _, _, _ => trivial
  | ConsList.wrap _, ConsList.wrap _, ConsList.cons _ _, _, g => g.elim
  | ConsList.wrap _, ConsList.cons _ _, _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.cons _ _, ConsList.wrap _, _, g => g.elim
  | ConsList.cons p l, ConsList.cons yi ys, ConsList.cons qi qs, ⟨h1, h2⟩, ⟨g1, g2⟩ => by
      refine ⟨?_, best_dominates l ys qs h2 g2⟩
      obtain ⟨P0, hP0, hest⟩ := h1
      have hP0' : P0 = fun z => chooseR p z := by
        rw [Λ_eq_classifier] at hP0; exact hP0
      subst hP0'
      exact ((est_apply _ _ _).mp hest).2 qi g1

/-- **party-laws, last row** (`exclude` branch): `est(R°)` pushed into each subtree's choice —
    `π₂ list(Λ(choose) est(R°)) concat ⊑ Λ(exclude) est(R°)`: the best root-out party is the
    concatenation of each subtree's best of its two parties. -/
public theorem exclude_step :
    (graph Prod.snd : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
        ⟶ (⟨ConsList Unit (ConsList Unit A × ConsList Unit A)⟩ : RelSet.{0}))
        ≫ list (Λ chooseR ≫ est((R rating)°)) ≫ concatR
      ⊑ Λ excludeR ≫ est((R rating)°) := by
  apply le_iff.mpr; intro u y
  rintro ⟨m, hm, ys, hys, hy⟩
  obtain rfl : m = u.2 := hm
  have hmem : listP chooseR u.2 ys := by
    refine listP_mono (fun p q hpq => ?_) u.2 ys hys
    obtain ⟨P0, hP0, hest⟩ := hpq
    have hP0' : P0 = fun z => chooseR p z := by
      rw [Λ_eq_classifier] at hP0; exact hP0
    subst hP0'
    exact ((est_apply _ _ _).mp hest).1
  refine ⟨fun z => excludeR u z, by rw [Λ_eq_classifier]; rfl, ?_⟩
  refine (est_apply _ _ _).mpr ⟨⟨ys, hmem, (show y = cconcat ys from hy)⟩, ?_⟩
  rintro z ⟨qs, hqs, hz⟩
  show costFn rating z ≤ costFn rating y
  rw [(show z = cconcat qs from hz), (show y = cconcat ys from hy)]
  exact cost_cconcat_le rating (best_dominates rating u.2 ys qs hys hqs)

/-- **party-laws (the derivation's headline)**: the greedy program refines the specification,
    `⦇⟨include, π₂ list(Λ(choose) est(R°)) concat⟩⦈ Λ(choose) est(R°) ⊑ Λ(party) est(R°)` —
    the best of every guest list the president allows is one pass up the tree, each subtree
    handing up its best party with its boss in and its best with the boss out, and `choose`
    taking the better of the two at the root. -/
public theorem party_laws :
    ⦇(rpair (graph includeFn)
        ((graph Prod.snd : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
            ⟶ (⟨ConsList Unit (ConsList Unit A × ConsList Unit A)⟩ : RelSet.{0}))
          ≫ list (Λ chooseR ≫ est((R rating)°)) ≫ concatR)
      : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
          ⟶ (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}))⦈
        ≫ Λ chooseR ≫ est((R rating)°)
      ⊑ Λ party ≫ est((R rating)°) := by
  -- last row: the program's algebra refines ⟨Λ(include) est(R°), Λ(exclude) est(R°)⟩
  have hRrefl : 𝟙 (dList A) ⊑ (R rating)° := by
    have h := recip_mono (R_refl rating); rwa [recip_id] at h
  have row7 := rpair_mono (graph_le_Λ_est includeFn hRrefl) (exclude_step rating)
  -- Ex 7.15 row: `⟨Λ(include) est(R°), Λ(exclude) est(R°)⟩ ⊑ Λ(S) est((R×R)°)`
  have row6 := pair_est_le (graph includeFn) excludeR (R rating) (R rating)
  have hcata : ⦇(rpair (graph includeFn)
        ((graph Prod.snd : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
            ⟶ (⟨ConsList Unit (ConsList Unit A × ConsList Unit A)⟩ : RelSet.{0}))
          ≫ list (Λ chooseR ≫ est((R rating)°)) ≫ concatR)
      : (RT.F A).obj (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0})
          ⟶ (⟨ConsList Unit A × ConsList Unit A⟩ : RelSet.{0}))⦈
      ⊑ ⦇S%∋ ≫ est((rprodMap (R rating) (R rating))°)⦈ :=
    relCata_mono (RT.initial A) (le_trans row7 row6)
  -- the greedy theorem at `(R×R)°`
  have hgreedy : ⦇S%∋ ≫ est((rprodMap (R rating) (R rating))°)⦈
      ⊑ ⦇S⦈%∋ ≫ est((rprodMap (R rating) (R rating))°) :=
    greedy (RT.F_preservesRecip A) (RT.initial A) (RR_recip_trans rating) (party_mono rating)
  -- Ex 7.38 row, at `Q := (R×R)°`, `T := choose`
  have hRtrans' : (R rating)° ≫ (R rating)° ⊑ (R rating)° := by
    have h := recip_mono (R_trans rating); rwa [Allegory.recip_comp] at h
  have row4 : est((rprodMap (R rating) (R rating))°) ≫ Λ chooseR ≫ est((R rating)°)
      ⊑ existsImage chooseR ≫ est((R rating)°) :=
    est_Λ_est_le (chooseR_monotonic rating) hRtrans'
  -- absorption + `party ≜ ⦇S⦈ choose` close the chain
  have hfin : ⦇S⦈%∋ ≫ (existsImage chooseR ≫ est((R rating)°))
      = Λ party ≫ est((R rating)°) := by
    rw [← Cat.assoc, Λ_absorption, ← party_eq]
  exact le_trans (comp_mono_right hcata _) (le_trans (comp_mono_right hgreedy _)
    (le_trans (le_of_eq (Cat.assoc _ _ _)) (le_trans (comp_mono_left _ row4) (le_of_eq hfin))))

end Party

end RelSet

end Freyd.Alg
