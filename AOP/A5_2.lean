/-
  Bird & de Moor, *Algebra of Programming* §5.2  Relational products (book pp. 113-116).

  The relational product `a Π b` of two objects is a chosen tabulation of the maximal
  arrow `⊤ : a → b` (book p.114: "(outl, outr) tabulates Π").  Pairing `⟨R,S⟩`, the
  binary map-former `R×S`, and their laws (5.1)-(5.9) are built from this single choice.

  Diagram order throughout: `xy` means "first x then y" (`≫`), matching the book's own
  right-to-left composition after mirroring (`X·Y` there = `Y ≫ X` here).  Every
  statement below is already in the mirrored form; do not re-translate.

  Setting: a TABULAR UNITARY DIVISION ALLEGORY (`Freyd.S2_3`), which supplies `topMor`
  (the maximal arrow `⊤ : a → b`, named by division as `𝟘/𝟘`) and full tabulation
  (`TabularAllegory.tabular`).

  Investigated `Freyd.S2_147_MapCat`'s `mapHasBinaryProducts` (binary products of
  `Map(𝒜)`, built as a pullback over the terminal/unit object): conceptually this is
  the SAME universal apex as tabulating `topMor a b` (pulling back the two unit maps
  `p_a, p_b` IS tabulating `p_a ≫ p_b° = topMor a b`), confirming `RelProd` needs no new
  axioms.  Not reused literally: that construction is expressed through the heavy
  `HasPullback`/`Cone`/`MapObj`/`@`-explicit categorical machinery (built for the
  `Map(𝒜)` CATEGORY, with objects packaged as `{f // Map f}` subtypes), whereas `RelProd`
  needs the raw `𝒜`-level legs directly.  Unwinding `Cone.π₁.val` etc. would be strictly
  more code than mirroring `S2_3.topTab`'s direct `TabularAllegory.tabular (topMor a b)`
  pattern, which is what `relProd_nonempty` below does.
-/
module

public import Freyd.S2_30
public import AOP.A4_2
public import AOP.A5_1

universe v v₂ v₃ u₂ u₃ u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜]

/-! ## `topMor` is self-converse under swap (needed for (5.6)/(5.7)) -/

/-- `(⊤ : a → b)° = ⊤ : b → a`.  From maximality alone — each side is above the other's
    converse — so it does not depend on which arrow `topMor` is named by. -/
public theorem recip_topMor (a b : 𝒜) : (topMor a b)° = topMor b a :=
  le_antisymm (topMor_max _) (recip_le_iff.mp (topMor_max _))

/-! ## §5.2  The relational product `RelProd a b` (book p.114)

  A RelProd is a CHOSEN tabulation of `⊤ : a → b`: an apex `p` with legs
  `outl : p ⟶ a`, `outr : p ⟶ b` that are MAPS, tabulating the maximal arrow. -/

/-- A **RELATIONAL PRODUCT** of `a`, `b` (B&dM §5.2, book p.114): a chosen tabulation
    of the maximal arrow `⊤ : a → b` by maps `outl : p → a`, `outr : p → b`. -/
public structure RelProd (a b : 𝒜) where
  /-- The apex (the product object, `a Π b`). -/
  p : 𝒜
  /-- Left projection. -/
  outl : p ⟶ a
  /-- Right projection. -/
  outr : p ⟶ b
  /-- `(outl, outr)` tabulates the maximal arrow `⊤ : a → b`. -/
  tab : Tabulates outl outr (topMor a b)

variable {a b a' b' c : 𝒜}

public theorem RelProd.outl_map (P : RelProd a b) : Map P.outl := P.tab.1

public theorem RelProd.outr_map (P : RelProd a b) : Map P.outr := P.tab.2.1

/-- `outl° ≫ outr = ⊤` (the tabulation equation). -/
public theorem RelProd.eq_topMor (P : RelProd a b) : P.outl° ≫ P.outr = topMor a b := P.tab.2.2.1.symm

/-- The joint-monic identity `outl≫outl° ∩ outr≫outr° = id_p`. -/
public theorem RelProd.joint_id (P : RelProd a b) :
    P.outl ≫ P.outl° ∩ P.outr ≫ P.outr° = Cat.id P.p := P.tab.2.2.2

/-- `outr° ≫ outl = ⊤ : b → a` — the "other" cross term, obtained from `eq_topMor` by
    reciprocation plus `recip_topMor`. -/
public theorem RelProd.outr_recip_outl (P : RelProd a b) : P.outr° ≫ P.outl = topMor b a := by
  have h := congrArg Allegory.recip P.eq_topMor
  rwa [Allegory.recip_comp, Allegory.recip_recip, recip_topMor] at h

/-- A CHOSEN relational product for every pair of objects — the `×` counterpart of
    `PositiveAllegory`'s `coprod`/`has_coproduct` fields.  A class rather than a definition
    because a tabulation of `⊤` fixes the apex only up to isomorphism: with the apex taken from
    `Exists.choose` nothing reduces, so a concrete allegory could never see its own product
    object (`Rel(Set)` names `a.carrier × b.carrier`). -/
public class HasRelProd (𝒜 : Type u) [TabularUnitaryDivisionAllegory 𝒜] where
  /-- The chosen relational product of `x` and `y`. -/
  relProd (x y : 𝒜) : RelProd x y

export HasRelProd (relProd)

-- No fallback `instance` tabulating `⊤` by `Exists.choose`: being an instance it filled itself
-- in wherever a statement forgot to ask, putting `Classical.choice` under the whole §5.2 chain.
/-- Every pair of objects HAS a relational product — tabulate `⊤ : a → b`.  A `Nonempty`, not a
    CHOSEN one: eliminating it into a PROOF costs no choice, which is what keeps (5.3)/(5.8) and
    everything built on them constructive; only `Relator.prod`, which needs an OBJECT, takes
    `HasRelProd`. -/
public theorem relProd_nonempty (x y : 𝒜) : Nonempty (RelProd x y) := by
  obtain ⟨p, f, g, h⟩ := TabularAllegory.tabular (topMor x y)
  exact ⟨⟨p, f, g, h⟩⟩

/-! ## Two generic `topMor`-cancellation facts, used repeatedly below -/

/-- `id_c ∩ (S ≫ ⊤) ⊑ dom S`, for `S : c ⟶ b`.
    (B&dM Ex 4.27-style fact, mirrored; the generic half of (5.6)/(5.7)'s proof.) -/
public theorem id_inter_comp_topMor_le_dom {b c : 𝒜} (S : c ⟶ b) :
    Cat.id c ∩ (S ≫ topMor b c) ⊑ dom S := by
  show Cat.id c ∩ (S ≫ topMor b c) ⊑ Cat.id c ∩ (S ≫ S°)
  apply le_inter (inter_lb_left _ _)
  have hSle : S° ⊑ topMor b c := topMor_max S°
  have hcomm : topMor b c ∩ S° = S° := by rw [Allegory.inter_comm]; exact hSle
  have hmod : (S ≫ topMor b c) ∩ Cat.id c ⊑ S ≫ (topMor b c ∩ S° ≫ Cat.id c) :=
    modular_le_right S (topMor b c) (Cat.id c)
  rw [Cat.comp_id, hcomm] at hmod
  calc Cat.id c ∩ (S ≫ topMor b c) = (S ≫ topMor b c) ∩ Cat.id c := Allegory.inter_comm _ _
    _ ⊑ S ≫ S° := hmod

/-- **Key fact**: `R ∩ (S ≫ ⊤) = dom S ≫ R`, for `R : c ⟶ a`, `S : c ⟶ b`.  The generic
    engine behind (5.6)/(5.7): B&dM Exercise 4.27 mirrored. -/
public theorem inter_comp_topMor_eq_dom_comp {a b c : 𝒜} (R : c ⟶ a) (S : c ⟶ b) :
    R ∩ (S ≫ topMor b a) = dom S ≫ R := by
  apply le_antisymm
  · have h1 : (Cat.id c ≫ R) ∩ (S ≫ topMor b a) ⊑
        (Cat.id c ∩ (S ≫ topMor b a) ≫ R°) ≫ R := modular_le (Cat.id c) R (S ≫ topMor b a)
    rw [Cat.id_comp] at h1
    have h2 : (S ≫ topMor b a) ≫ R° ⊑ S ≫ topMor b c :=
      by rw [Cat.assoc]; exact comp_mono_left S (topMor_max (topMor b a ≫ R°))
    have h3 : Cat.id c ∩ ((S ≫ topMor b a) ≫ R°) ⊑ Cat.id c ∩ (S ≫ topMor b c) :=
      le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h2)
    exact le_trans h1 (comp_mono_right (le_trans h3 (id_inter_comp_topMor_le_dom S)) R)
  · apply le_inter
    · have h := comp_mono_right (dom_coreflexive S) R; rwa [Cat.id_comp] at h
    · have h1 : dom S ≫ R ⊑ (S ≫ S°) ≫ R :=
        comp_mono_right (inter_lb_right (Cat.id c) (S ≫ S°)) R
      have h2 : (S ≫ S°) ≫ R = S ≫ (S° ≫ R) := Cat.assoc S S° R
      have h3 : S ≫ (S° ≫ R) ⊑ S ≫ topMor b a := comp_mono_left S (topMor_max (S° ≫ R))
      rw [h2] at h1; exact le_trans h1 h3

/-! ## (5.1)  Pairing -/

/-- **(5.1)**: `⟨R,S⟩ = (outl°R) ∩ (outr°S)`, mirrored: `pair R S = (R≫outl°) ∩ (S≫outr°)`. -/
@[expose] public def RelProd.pair (P : RelProd a b) (R : c ⟶ a) (S : c ⟶ b) : c ⟶ P.p :=
  (R ≫ P.outl°) ∩ (S ≫ P.outr°)

/-! ## (5.2)  The binary map-former `R×S` -/

/-- **(5.2)**: `R×S = ⟨R·outl, S·outr⟩`, mirrored: `prodMap P Q R S = Q.pair (P.outl≫R) (P.outr≫S)`. -/
@[expose] public def prodMap (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') : P.p ⟶ Q.p :=
  Q.pair (P.outl ≫ R) (P.outr ≫ S)

/-! ## Monotonicity -/

public theorem RelProd.pair_mono {P : RelProd a b} {R R' : c ⟶ a} {S S' : c ⟶ b}
    (hR : R ⊑ R') (hS : S ⊑ S') : P.pair R S ⊑ P.pair R' S' :=
  le_inter (le_trans (inter_lb_left _ _) (comp_mono_right hR _))
    (le_trans (inter_lb_right _ _) (comp_mono_right hS _))

public theorem prodMap_mono {P : RelProd a b} {Q : RelProd a' b'} {R R' : a ⟶ a'} {S S' : b ⟶ b'}
    (hR : R ⊑ R') (hS : S ⊑ S') : prodMap P Q R S ⊑ prodMap P Q R' S' :=
  Q.pair_mono (comp_mono_left P.outl hR) (comp_mono_left P.outr hS)

/-! ## (5.6)/(5.7)  Cancellation of pairing against `outl`/`outr` -/

/-- **(5.6)**: `⟨R,S⟩·outl = dom S · R`, mirrored: `pair R S ≫ outl = dom S ≫ R`. -/
public theorem RelProd.pair_outl {P : RelProd a b} (R : c ⟶ a) (S : c ⟶ b) :
    P.pair R S ≫ P.outl = dom S ≫ R := by
  have step1 : P.pair R S = S ≫ P.outr° ∩ R ≫ P.outl° := by
    show (R ≫ P.outl° ∩ S ≫ P.outr°) = _; rw [Allegory.inter_comm]
  rw [step1, simple_modular_eq P.outl_map.2 (S ≫ P.outr°) R, Cat.assoc, P.outr_recip_outl,
    Allegory.inter_comm]
  exact inter_comp_topMor_eq_dom_comp R S

/-- **(5.7)**: `⟨R,S⟩·outr = dom R · S`, mirrored: `pair R S ≫ outr = dom R ≫ S`. -/
public theorem RelProd.pair_outr {P : RelProd a b} (R : c ⟶ a) (S : c ⟶ b) :
    P.pair R S ≫ P.outr = dom R ≫ S := by
  show (R ≫ P.outl° ∩ S ≫ P.outr°) ≫ P.outr = dom R ≫ S
  rw [simple_modular_eq P.outr_map.2 (R ≫ P.outl°) S, Cat.assoc, P.eq_topMor, Allegory.inter_comm]
  exact inter_comp_topMor_eq_dom_comp S R

/-! ## The pairing Galois connection

  `Z ⊑ pair U V ↔ Z≫outl ⊑ U ∧ Z≫outr ⊑ V`: `pair U V` is the GREATEST morphism whose
  two projections are bounded by `U`, `V`.  The clean characterization behind most of
  the calculations below. -/

public theorem RelProd.le_pair_iff {P : RelProd a b} {Z : c ⟶ P.p} {U : c ⟶ a} {V : c ⟶ b} :
    Z ⊑ P.pair U V ↔ Z ≫ P.outl ⊑ U ∧ Z ≫ P.outr ⊑ V := by
  constructor
  · intro h
    exact ⟨(map_shunt_right P.outl_map Z U).mpr (le_trans h (inter_lb_left _ _)),
      (map_shunt_right P.outr_map Z V).mpr (le_trans h (inter_lb_right _ _))⟩
  · rintro ⟨h1, h2⟩
    exact le_inter ((map_shunt_right P.outl_map Z U).mp h1) ((map_shunt_right P.outr_map Z V).mp h2)

/-! ## `pair` of two maps is a map, and Ex 5.9

  Pairing two MAPS is a map (via the tabulation UP), and pairing commutes with LEFT
  composition by a map (Ex 5.9, via `simple_dist_inter`).  The absorption laws
  (5.3)/(5.4)/(5.5) and the cancellation law (5.8) follow B&dM p.115's staged proof at
  the end of this file: two `outl`/`outr` claims, then the modular-law special cases
  (5.4)/(5.5), then the composite chain. -/

/-- `pair f g` of two MAPS `f, g` is again a MAP: it is literally the mediating witness
    of the tabulation universal property (`tabulation_UP_forward_witness`) applied to
    `f°≫g ⊑ ⊤` (always true, `topMor_max`). -/
public theorem RelProd.pair_map {P : RelProd a b} {f : c ⟶ a} {g : c ⟶ b}
    (hf : Map f) (hg : Map g) : Map (P.pair f g) :=
  (tabulation_UP_forward_witness P.tab hf hg (topMor_max (f° ≫ g))).1

/-- **Ex 5.9**: for a MAP `f : d ⟶ c`, `f ≫ ⟨R,S⟩ = ⟨f≫R, f≫S⟩`, mirrored:
    `f ≫ P.pair R S = P.pair (f≫R) (f≫S)`.  `f` being simple lets composition
    distribute exactly over the defining meet (`simple_dist_inter`). -/
public theorem RelProd.map_comp_pair {P : RelProd a b} {d : 𝒜} {f : d ⟶ c} (hf : Map f)
    (R : c ⟶ a) (S : c ⟶ b) : f ≫ P.pair R S = P.pair (f ≫ R) (f ≫ S) := by
  show f ≫ (R ≫ P.outl° ∩ S ≫ P.outr°) = (f ≫ R) ≫ P.outl° ∩ (f ≫ S) ≫ P.outr°
  rw [simple_dist_inter hf.2, Cat.assoc, Cat.assoc]

/-- For an arbitrary `X` only one half of Ex 5.9 survives: `X·⟨R,S⟩ ⊑ ⟨X·R,X·S⟩`, mirrored
    `X ≫ P.pair R S ⊑ P.pair (X ≫ R) (X ≫ S)` — composition on the left is only lax over the
    defining meet unless `X` is simple. -/
public theorem RelProd.comp_pair_le {P : RelProd a b} {d : 𝒜} (X : d ⟶ c)
    (R : c ⟶ a) (S : c ⟶ b) : X ≫ P.pair R S ⊑ P.pair (X ≫ R) (X ≫ S) := by
  show X ≫ (R ≫ P.outl° ∩ S ≫ P.outr°) ⊑ (X ≫ R) ≫ P.outl° ∩ (X ≫ S) ≫ P.outr°
  refine le_inter ?_ ?_
  · rw [Cat.assoc]; exact comp_mono_left X (inter_lb_left _ _)
  · rw [Cat.assoc]; exact comp_mono_left X (inter_lb_right _ _)

/-! ## Ex 5.6:  functoriality shape of `prodMap` — identity and converse -/

/-- `prodMap` of the two identities is the identity, via the joint-monic identity. -/
public theorem prodMap_id (P : RelProd a b) :
    prodMap P P (Cat.id a) (Cat.id b) = Cat.id P.p := by
  show P.pair (P.outl ≫ Cat.id a) (P.outr ≫ Cat.id b) = Cat.id P.p
  rw [Cat.comp_id, Cat.comp_id]
  show P.outl ≫ P.outl° ∩ P.outr ≫ P.outr° = Cat.id P.p
  exact P.joint_id

/-- `(R×S)° = S°×R°` reading the OTHER way round, mirrored: `(prodMap P Q R S)° =
    prodMap Q P R° S°` — a direct computation from the definitions via `recip_inter`/
    `recip_comp`, no absorption needed. -/
public theorem prodMap_recip {P : RelProd a b} {Q : RelProd a' b'} (R : a ⟶ a') (S : b ⟶ b') :
    (prodMap P Q R S)° = prodMap Q P R° S° := by
  show ((P.outl ≫ R) ≫ Q.outl° ∩ (P.outr ≫ S) ≫ Q.outr°)° =
      (Q.outl ≫ R°) ≫ P.outl° ∩ (Q.outr ≫ S°) ≫ P.outr°
  rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
    Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip,
    Cat.assoc, Cat.assoc]

/-! ## (5.3)/(5.4)/(5.5)  The absorption laws (book pp.114-115)

  B&dM prove the absorption property `(R×S)·⟨X,Y⟩ = ⟨R·X,S·Y⟩` (5.3) in stages: first two
  "claims" (`outl·(R×id) = R·outl` and `outr·(R×S) ⊑ S·outr`), then the special cases
  (5.4)/(5.5) with one identity factor via the modular law, then the composite chain
  through an intermediate relational product.  Everything below is mirrored to diagram
  order: `pair X Y ≫ prodMap P Q R S = pair (X≫R) (Y≫S)`. -/

/-- Book p.115 claim: `outr·(R×S) ⊑ S·outr`, mirrored: `(R×S) ≫ Q.outr ⊑ P.outr ≫ S`.
    From (5.7) and `dom ⊑ id`. -/
public theorem prodMap_outr_le (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') :
    prodMap P Q R S ≫ Q.outr ⊑ P.outr ≫ S := by
  show Q.pair (P.outl ≫ R) (P.outr ≫ S) ≫ Q.outr ⊑ P.outr ≫ S
  rw [RelProd.pair_outr]
  have h := comp_mono_right (dom_coreflexive (P.outl ≫ R)) (P.outr ≫ S)
  rwa [Cat.id_comp] at h

/-- **(5.7) sharpened.**  The `dom` factor (5.7) leaves behind sits on the DISCARDED leg, so it
    is `𝟙` as soon as that leg's relation is ENTIRE: `(R×S) ≫ outr = outr ≫ S`.
    `prodMap_id_outr` is the case `R = 𝟙`; the inclusion is STRICT without the hypothesis
    (`outr_not_strictNatural`, A6_1_OrdRelSet). -/
public theorem prodMap_outr_eq_of_entire (P : RelProd a b) (Q : RelProd a' b') {R : a ⟶ a'}
    (S : b ⟶ b') (hR : Entire R) : prodMap P Q R S ≫ Q.outr = P.outr ≫ S := by
  show Q.pair (P.outl ≫ R) (P.outr ≫ S) ≫ Q.outr = P.outr ≫ S
  rw [RelProd.pair_outr, entire_comp P.outl_map.1 hR, Cat.id_comp]

/-- Mirror of the previous claim on the left leg: `(R×S) ≫ Q.outl ⊑ P.outl ≫ R`. -/
public theorem prodMap_outl_le (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') :
    prodMap P Q R S ≫ Q.outl ⊑ P.outl ≫ R := by
  show Q.pair (P.outl ≫ R) (P.outr ≫ S) ≫ Q.outl ⊑ P.outl ≫ R
  rw [RelProd.pair_outl]
  have h := comp_mono_right (dom_coreflexive (P.outr ≫ S)) (P.outl ≫ R)
  rwa [Cat.id_comp] at h

/-- **(5.6) sharpened**, the mirror of `prodMap_outr_eq_of_entire`: the `dom` factor (5.6) leaves
    behind sits on the DISCARDED leg, so it is `𝟙` as soon as that leg's relation is ENTIRE:
    `(R×S) ≫ outl = outl ≫ R`.  `prodMap_id_outl` is the case `S = 𝟙`. -/
public theorem prodMap_outl_eq_of_entire (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a')
    {S : b ⟶ b'} (hS : Entire S) : prodMap P Q R S ≫ Q.outl = P.outl ≫ R := by
  show Q.pair (P.outl ≫ R) (P.outr ≫ S) ≫ Q.outl = P.outl ≫ R
  rw [RelProd.pair_outl, entire_comp P.outr_map.1 hS, Cat.id_comp]

/-- Book p.115 claim: `outl·(R×id) = R·outl` — with the identity in the second slot the
    `dom` factor of (5.6) is the identity (`outr` is entire), so the bound sharpens to an
    equality.  Mirrored: `(R×id) ≫ Q.outl = P.outl ≫ R`. -/
public theorem prodMap_id_outl (P : RelProd a b) (Q : RelProd a' b) (R : a ⟶ a') :
    prodMap P Q R (Cat.id b) ≫ Q.outl = P.outl ≫ R :=
  prodMap_outl_eq_of_entire P Q R (id_is_map_local b).1

/-- Mirror on the right leg: `(id×S) ≫ Q.outr = P.outr ≫ S`. -/
public theorem prodMap_id_outr (P : RelProd a b) (Q : RelProd a b') (S : b ⟶ b') :
    prodMap P Q (Cat.id a) S ≫ Q.outr = P.outr ≫ S :=
  prodMap_outr_eq_of_entire P Q S (id_is_map_local a).1

/-- Claim 1 reciprocated: `R ≫ Q.outl° = P.outl° ≫ (R×id)` — the rewrite that pushes a
    relation across the products' left legs in (5.4)'s proof. -/
public theorem outl_recip_prodMap (P : RelProd a b) (Q : RelProd a' b) (R : a ⟶ a') :
    R ≫ Q.outl° = P.outl° ≫ prodMap P Q R (Cat.id b) := by
  have h := congrArg Allegory.recip (prodMap_id_outl Q P R°)
  rw [Allegory.recip_comp, Allegory.recip_comp, prodMap_recip, recip_id,
    Allegory.recip_recip] at h
  exact h.symm

/-- Mirror: `S ≫ Q.outr° = P.outr° ≫ (id×S)`. -/
public theorem outr_recip_prodMap (P : RelProd a b) (Q : RelProd a b') (S : b ⟶ b') :
    S ≫ Q.outr° = P.outr° ≫ prodMap P Q (Cat.id a) S := by
  have h := congrArg Allegory.recip (prodMap_id_outr Q P S°)
  rw [Allegory.recip_comp, Allegory.recip_comp, prodMap_recip, recip_id,
    Allegory.recip_recip] at h
  exact h.symm

/-- Claim 2 reciprocated: `P.outr° ≫ (R×S) ⊑ S ≫ Q.outr°`. -/
public theorem recip_outr_prodMap_le (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') :
    P.outr° ≫ prodMap P Q R S ⊑ S ≫ Q.outr° := by
  have h := recip_mono (prodMap_outr_le Q P R° S°)
  rw [Allegory.recip_comp, Allegory.recip_comp, prodMap_recip, Allegory.recip_recip,
    Allegory.recip_recip] at h
  exact h

/-- Mirror: `P.outl° ≫ (R×S) ⊑ R ≫ Q.outl°`. -/
public theorem recip_outl_prodMap_le (P : RelProd a b) (Q : RelProd a' b') (R : a ⟶ a') (S : b ⟶ b') :
    P.outl° ≫ prodMap P Q R S ⊑ R ≫ Q.outl° := by
  have h := recip_mono (prodMap_outl_le Q P R° S°)
  rw [Allegory.recip_comp, Allegory.recip_comp, prodMap_recip, Allegory.recip_recip,
    Allegory.recip_recip] at h
  exact h

/-- **(5.4)**, sharpened to an equality: `⟨R·X, Y⟩ = (R×id)·⟨X,Y⟩`, mirrored:
    `P.pair X Y ≫ (R×id) = Q.pair (X≫R) Y`.  B&dM prove `⊒` by the modular law (the
    tricky half, book p.115); `⊑` is the routine `le_pair_iff` computation. -/
public theorem RelProd.pair_prodMap_fst {P : RelProd a b} {Q : RelProd a' b}
    (X : c ⟶ a) (Y : c ⟶ b) (R : a ⟶ a') :
    P.pair X Y ≫ prodMap P Q R (Cat.id b) = Q.pair (X ≫ R) Y := by
  apply le_antisymm
  · apply RelProd.le_pair_iff.mpr
    constructor
    · rw [Cat.assoc, prodMap_id_outl, ← Cat.assoc, RelProd.pair_outl]
      have h := comp_mono_right (comp_mono_right (dom_coreflexive Y) X) R
      rwa [Cat.id_comp] at h
    · have h1 : prodMap P Q R (Cat.id b) ≫ Q.outr ⊑ P.outr := by
        have h := prodMap_outr_le P Q R (Cat.id b); rwa [Cat.comp_id] at h
      have h2 := comp_mono_left (P.pair X Y) h1
      rw [RelProd.pair_outr] at h2
      have h3 := comp_mono_right (dom_coreflexive X) Y
      rw [Cat.id_comp] at h3
      rw [Cat.assoc]
      exact le_trans h2 h3
  · have hexp : Q.pair (X ≫ R) Y =
        ((X ≫ P.outl°) ≫ prodMap P Q R (Cat.id b)) ∩ (Y ≫ Q.outr°) := by
      show ((X ≫ R) ≫ Q.outl°) ∩ (Y ≫ Q.outr°) = _
      rw [Cat.assoc, outl_recip_prodMap P Q R, ← Cat.assoc]
    have hMr : (Y ≫ Q.outr°) ≫ (prodMap P Q R (Cat.id b))° ⊑ Y ≫ P.outr° := by
      rw [prodMap_recip, recip_id, Cat.assoc]
      apply comp_mono_left Y
      have h := recip_outr_prodMap_le Q P R° (Cat.id b)
      rwa [Cat.id_comp] at h
    have hsub : (X ≫ P.outl°) ∩ ((Y ≫ Q.outr°) ≫ (prodMap P Q R (Cat.id b))°) ⊑ P.pair X Y :=
      le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hMr)
    rw [hexp]
    exact le_trans (modular_le (X ≫ P.outl°) (prodMap P Q R (Cat.id b)) (Y ≫ Q.outr°))
      (comp_mono_right hsub _)

/-- **(5.5)**, sharpened to an equality: `⟨X, S·Y⟩ = (id×S)·⟨X,Y⟩`, mirrored:
    `P.pair X Y ≫ (id×S) = Q.pair X (Y≫S)`.  Symmetric to (5.4). -/
public theorem RelProd.pair_prodMap_snd {P : RelProd a b} {Q : RelProd a b'}
    (X : c ⟶ a) (Y : c ⟶ b) (S : b ⟶ b') :
    P.pair X Y ≫ prodMap P Q (Cat.id a) S = Q.pair X (Y ≫ S) := by
  apply le_antisymm
  · apply RelProd.le_pair_iff.mpr
    constructor
    · have h1 : prodMap P Q (Cat.id a) S ≫ Q.outl ⊑ P.outl := by
        have h := prodMap_outl_le P Q (Cat.id a) S; rwa [Cat.comp_id] at h
      have h2 := comp_mono_left (P.pair X Y) h1
      rw [RelProd.pair_outl] at h2
      have h3 := comp_mono_right (dom_coreflexive Y) X
      rw [Cat.id_comp] at h3
      rw [Cat.assoc]
      exact le_trans h2 h3
    · rw [Cat.assoc, prodMap_id_outr, ← Cat.assoc, RelProd.pair_outr]
      have h := comp_mono_right (comp_mono_right (dom_coreflexive X) Y) S
      rwa [Cat.id_comp] at h
  · have hexp : Q.pair X (Y ≫ S) =
        (X ≫ Q.outl°) ∩ ((Y ≫ P.outr°) ≫ prodMap P Q (Cat.id a) S) := by
      show (X ≫ Q.outl°) ∩ ((Y ≫ S) ≫ Q.outr°) = _
      rw [Cat.assoc, outr_recip_prodMap P Q S, ← Cat.assoc]
    have hMl : (X ≫ Q.outl°) ≫ (prodMap P Q (Cat.id a) S)° ⊑ X ≫ P.outl° := by
      rw [prodMap_recip, recip_id, Cat.assoc]
      apply comp_mono_left X
      have h := recip_outl_prodMap_le Q P (Cat.id a) S°
      rwa [Cat.id_comp] at h
    have hsub : (Y ≫ P.outr°) ∩ ((X ≫ Q.outl°) ≫ (prodMap P Q (Cat.id a) S)°) ⊑ P.pair X Y :=
      le_inter (le_trans (inter_lb_right _ _) hMl) (inter_lb_left _ _)
    rw [hexp, Allegory.inter_comm]
    exact le_trans (modular_le (Y ≫ P.outr°) (prodMap P Q (Cat.id a) S) (X ≫ Q.outl°))
      (comp_mono_right hsub _)

/-- B&dM p.115 "exercise" step, as an equality: `(R×id) ≫ (id×S) = R×S` — immediate from
    (5.5) applied to the pair that DEFINES `R×id`. -/
public theorem prodMap_factor (P : RelProd a b) (M : RelProd a' b) (Q : RelProd a' b')
    (R : a ⟶ a') (S : b ⟶ b') :
    prodMap P M R (Cat.id b) ≫ prodMap M Q (Cat.id a') S = prodMap P Q R S := by
  show M.pair (P.outl ≫ R) (P.outr ≫ Cat.id b) ≫ prodMap M Q (Cat.id a') S = _
  rw [Cat.comp_id, RelProd.pair_prodMap_snd]; rfl

/-- **(5.3)** ABSORPTION (B&dM p.114): `(R×S)·⟨X,Y⟩ = ⟨R·X, S·Y⟩`, mirrored:
    `P.pair X Y ≫ (R×S) = Q.pair (X≫R) (Y≫S)`.  Book chain: factor `R×S` through an
    intermediate relational product of `a'` with `b`, then (5.4) and (5.5). -/
public theorem RelProd.pair_prodMap {P : RelProd a b} {Q : RelProd a' b'}
    (X : c ⟶ a) (Y : c ⟶ b) (R : a ⟶ a') (S : b ⟶ b') :
    P.pair X Y ≫ prodMap P Q R S = Q.pair (X ≫ R) (Y ≫ S) := by
  obtain ⟨M⟩ := relProd_nonempty a' b
  rw [← prodMap_factor P M Q R S, ← Cat.assoc, RelProd.pair_prodMap_fst,
    RelProd.pair_prodMap_snd]

/-- `×` preserves composition (B&dM p.114: the product relator "also preserves
    composition"): `(R×S) ≫ (R'×S') = (R≫R')×(S≫S')`.  From absorption. -/
public theorem prodMap_comp {a'' b'' : 𝒜} (P : RelProd a b) (M : RelProd a' b') (Q : RelProd a'' b'')
    (R : a ⟶ a') (S : b ⟶ b') (R' : a' ⟶ a'') (S' : b' ⟶ b'') :
    prodMap P M R S ≫ prodMap M Q R' S' = prodMap P Q (R ≫ R') (S ≫ S') := by
  show M.pair (P.outl ≫ R) (P.outr ≫ S) ≫ prodMap M Q R' S' = _
  rw [RelProd.pair_prodMap, Cat.assoc, Cat.assoc]; rfl

/-- **(5.8)** CANCELLATION (B&dM p.116): `⟨R,S⟩°·⟨X,Y⟩ = (R°·X) ∩ (S°·Y)`, mirrored:
    `P.pair X Y ≫ (P.pair R S)° = (X≫R°) ∩ (Y≫S°)`.  Book route: write `⟨R,S⟩` as
    `⟨id,id⟩ ≫ (R×S)` (absorption backwards), reciprocate, absorb with (5.3), and
    distribute the SIMPLE map `⟨id,id⟩` over the meet. -/
public theorem RelProd.pair_recip_pair {P : RelProd a b} {d : 𝒜}
    (X : c ⟶ a) (Y : c ⟶ b) (R : d ⟶ a) (S : d ⟶ b) :
    P.pair X Y ≫ (P.pair R S)° = (X ≫ R°) ∩ (Y ≫ S°) := by
  obtain ⟨D⟩ := relProd_nonempty d d
  have hdel : Map (D.pair (Cat.id d) (Cat.id d)) :=
    D.pair_map (id_is_map_local d) (id_is_map_local d)
  have hdom : dom (Cat.id d) = Cat.id d := (id_is_map_local d).1
  have houtl : D.pair (Cat.id d) (Cat.id d) ≫ D.outl = Cat.id d := by
    rw [RelProd.pair_outl, hdom, Cat.id_comp]
  have houtr : D.pair (Cat.id d) (Cat.id d) ≫ D.outr = Cat.id d := by
    rw [RelProd.pair_outr, hdom, Cat.id_comp]
  have hRS : P.pair R S = D.pair (Cat.id d) (Cat.id d) ≫ prodMap D P R S := by
    rw [RelProd.pair_prodMap, Cat.id_comp, Cat.id_comp]
  have hleg1 : ((X ≫ R°) ≫ D.outl°) ≫ (D.pair (Cat.id d) (Cat.id d))° = X ≫ R° := by
    rw [Cat.assoc, ← Allegory.recip_comp, houtl, recip_id, Cat.comp_id]
  have hleg2 : ((Y ≫ S°) ≫ D.outr°) ≫ (D.pair (Cat.id d) (Cat.id d))° = Y ≫ S° := by
    rw [Cat.assoc, ← Allegory.recip_comp, houtr, recip_id, Cat.comp_id]
  rw [hRS, Allegory.recip_comp, prodMap_recip, ← Cat.assoc, RelProd.pair_prodMap]
  show ((X ≫ R°) ≫ D.outl° ∩ (Y ≫ S°) ≫ D.outr°) ≫ (D.pair (Cat.id d) (Cat.id d))° =
    (X ≫ R°) ∩ (Y ≫ S°)
  rw [simple_dist_inter_recip hdel.2, hleg1, hleg2]

/-! ## Relators are closed under product; B&dM p.133's `outr` example of lax naturality -/

section ProdRelator

-- The CHOICE of apex enters only here, where a relator must name an object for each `x`; taking
-- it as a parameter is what lets `Rel(Set)` be recognised on its own `a.carrier × b.carrier`.
variable [HasRelProd 𝒜]

/-- Relators are closed under product: `X ↦ F X × G X`, `R ↦ F R × G R`, on `relProd`'s
    canonical choice.  The functor laws are `prodMap`'s composed with `F`'s and `G`'s. -/
@[expose] public def Relator.prod {𝒮 : Type u₂} [Allegory.{v₂} 𝒮]
    (F G : Relator 𝒮 𝒜) : Relator 𝒮 𝒜 where
  obj x := (relProd (F.obj x) (G.obj x)).p
  map R := prodMap (relProd _ _) (relProd _ _) (F.map R) (G.map R)
  map_id x := by
    simp only [F.map_id, G.map_id]; exact prodMap_id (relProd (F.obj x) (G.obj x))
  map_comp R S := by
    simp only [F.map_comp, G.map_comp]; exact (prodMap_comp _ _ _ _ _ _ _).symm
  map_mono h := prodMap_mono (F.map_mono h) (G.map_mono h)

/-- The PAIRING of two relators into the PRODUCT allegory: `x ↦ (F x, G x)`, `R ↦ (F R, G R)`.
    Its own `𝒜`, not the section's: pairing needs the product ALLEGORY and nothing else, and a
    signature carrying the section's `TabularUnitaryDivisionAllegory` projection instead would not
    typecheck beside a relator whose allegory instance reached `𝒜` by another route. -/
@[expose] public def Relator.pair {𝒜 : Type u} [Allegory.{v} 𝒜] {𝒮 : Type u₂} [Allegory.{v₂} 𝒮]
    (F G : Relator 𝒮 𝒜) : Relator 𝒮 (𝒜 × 𝒜) where
  obj x := (F.obj x, G.obj x)
  map R := (F.map R, G.map R)
  map_id x := Prod.ext (F.map_id x) (G.map_id x)
  map_comp R S := Prod.ext (F.map_comp R S) (G.map_comp R S)
  map_mono h := Prod.ext (F.map_mono h) (G.map_mono h)

/-- The product bifunctor AS A RELATOR `𝒜 × 𝒜 ⟶ 𝒜`, on the same `relProd` apex `Relator.prod`
    takes.  Splitting `F×G` through it is what makes a product TWO NESTED WIRES in a picture —
    the pairing inside the region `𝒜×𝒜`, this one outside it — and not two parallel wires. -/
@[expose] public def timesRel : Relator (𝒜 × 𝒜) 𝒜 where
  obj p := (relProd p.1 p.2).p
  map R := prodMap (relProd _ _) (relProd _ _) R.1 R.2
  map_id p := prodMap_id (relProd p.1 p.2)
  map_comp _ _ := (prodMap_comp _ _ _ _ _ _ _).symm
  map_mono h := prodMap_mono (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- `F×G` IS the pairing followed by the product bifunctor, on the nose.  A SPELLING BRIDGE: a
    picture packs the two arguments (`⟨F,G⟩` then the bifunctor) where the library writes one
    product relator, and the `←` orientation rewrites the picture's spelling into the library's,
    which is the one a closure theorem states its conclusion in. -/
@[diag_bridge ←] public theorem Relator.prod_eq_comp_pair {𝒮 : Type u₂} [Allegory.{v₂} 𝒮] (F G : Relator 𝒮 𝒜) :
    Relator.prod F G = Relator.comp (Relator.pair F G) timesRel := rfl

/-- A relator on the INSIDE distributes over a product: running `K` first and then `F×G` is
    running `K F` and `K G` and taking their product, on the same apex.  A SPELLING BRIDGE: a
    closure theorem reindexed along `K` (`laxNatural_inside`, `strictNatural_inside`) states its
    conclusion with the `K` OUTSIDE the product, where a panel's own lane stack has it
    distributed — one arrow, two spellings, and the search has to see them as one. -/
@[diag_bridge] public theorem Relator.comp_prod {𝒮 : Type u₂} [Allegory.{v₂} 𝒮]
    {𝒯 : Type u₃} [Allegory.{v₃} 𝒯] (K : Relator 𝒯 𝒮) (F G : Relator 𝒮 𝒜) :
    Relator.comp K (Relator.prod F G) = Relator.prod (Relator.comp K F) (Relator.comp K G) := rfl

/-- The identity relator composed on is no relator at all.  A SPELLING BRIDGE for the same
    reason as the last: a lane stack of one wire IS that wire, where a closure theorem
    instantiated at the identity leaves the `comp` standing. -/
@[diag_bridge] public theorem Relator.comp_id {𝒮 : Type u₂} [Allegory.{v₂} 𝒮]
    {𝒯 : Type u₃} [Allegory.{v₃} 𝒯] (K : Relator 𝒯 𝒮) :
    Relator.comp K (Relator.idRelator 𝒮) = K := rfl

/-- The DUPLICATION relator `X ↦ X×X`: the object diagonal `X ↦ (X,X)` followed by the product
    relator, i.e. `Relator.prod` of two identities.  Not the copy relation `◁ : A ⟶ A⊗A`. -/
@[expose] public def Δ (𝒜 : Type u) [TabularUnitaryDivisionAllegory 𝒜] [HasRelProd 𝒜] :
    Relator 𝒜 𝒜 :=
  Relator.prod (Relator.idRelator 𝒜) (Relator.idRelator 𝒜)

/-- **The FREE THEOREM of `π₂`** (B&dM p.133): the right projection is lax natural from `F×G` to
    `G` — `(FR × GR) ≫ outr ⊑ outr ≫ GR` at every `R`, which is `prodMap_outr_le`.  Nothing about
    `outr` beyond its TYPE goes into it: the relators are arbitrary, and the type `F×G ⟶ G` is
    what names the two sides of the square. -/
public theorem outr_laxNatural {𝒮 : Type u₂} [Allegory.{v₂} 𝒮] (F G : Relator 𝒮 𝒜) :
    LaxNatural G (Relator.prod F G) (fun x => (relProd (F.obj x) (G.obj x)).outr) :=
  fun _ => prodMap_outr_le _ _ _ _

/-- **B&dM p.133**: the right projection `outr` is lax natural from the duplication relator to the
    identity relator — `(R×R) ≫ outr ⊑ outr ≫ R`, the `F = G = 1` case of `outr_laxNatural`. -/
public theorem outr_lax_natural :
    LaxNatural (Relator.idRelator 𝒜) (Δ 𝒜) (fun a => (relProd a a).outr) :=
  outr_laxNatural (Relator.idRelator 𝒜) (Relator.idRelator 𝒜)

/-- The free theorem of `π₂` is an EQUALITY when the LEFT relator is ENTIRE at `R` — the
    `Entire (F.map R)` of `prodMap_outr_eq_of_entire`, at every `R` at once.  Without it the
    inclusion is strict: `outr_not_strictNatural` (A6_1_OrdRelSet). -/
public theorem outr_strict_of_entire {𝒮 : Type u₂} [Allegory.{v₂} 𝒮] (F G : Relator 𝒮 𝒜)
    (hF : ∀ {x y : 𝒮} (R : x ⟶ y), Entire (F.map R)) {x y : 𝒮} (R : x ⟶ y) :
    (Relator.prod F G).map R ≫ (relProd (F.obj y) (G.obj y)).outr
      = (relProd (F.obj x) (G.obj x)).outr ≫ G.map R :=
  prodMap_outr_eq_of_entire _ _ _ (hF R)

end ProdRelator

end Freyd.Alg
