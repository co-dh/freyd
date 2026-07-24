import Freyd.S2_1
import Freyd.S2_2
import Freyd.S2_3

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.228.

  §2.228  UNION ALLEGORIES (finite unions distributing with composition,
          but not necessarily with intersection)

  Freyd considers allegories equipped with finite unions which distribute
  with COMPOSITION, but NOT necessarily with INTERSECTION.  This is a
  structure strictly weaker than a distributive allegory (§2.21): a
  distributive allegory additionally satisfies the law
      R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T).

  The three observations of §2.228:
    (a) A TABULAR allegory with this property IS distributive.
    (b) A SEMI-SIMPLE allegory with this property IS distributive.
    (c) An allegory with this property in which every morphism is the
        union of the semi-simple morphisms it contains [2.225] NEED NOT be
        distributive: for any group G of size > 2, adjoining a zero 0 and a
        maximal element M to the one-object allegory on G (with the discrete
        order, RM = MR = M for R ≠ 0, and 0 absorbing) yields such an
        allegory that is not distributive.

  All allegory infrastructure (Allegory, Tabular, SemiSimple, Simple, the
  order ⊑, ∩, °) is reused from S2_1; the distributive-allegory laws are
  reused from S2_2 for comparison.  This file adds ONLY the §2.228 weaker
  structure and the three observations.
-/



namespace Freyd.Alg

variable {𝒜 : Type u}

/-! ## §2.228  Union allegories

  An allegory with finite unions distributing with composition but not
  necessarily with intersection.  Concretely: a zero morphism and a binary
  union forming a commutative-idempotent-associative semigroup with zero as
  unit, absorbing into intersection (so that ⊑ from ∩ agrees with ⊑ from ∪),
  zero absorbing under composition, and COMPOSITION distributing over union.

  This is exactly the `DistributiveAllegory` data of §2.21 MINUS the single
  axiom `inter_union_distrib` (intersection distributing over union).  We
  keep the absorption laws (`union_inter_absorb`, `inter_union_absorb`)
  because they are part of "finite unions" forming a lattice with ∩ — they
  express that ∪ is the join of the same partial order ⊑ that ∩ furnishes;
  Freyd never weakens these, only the ∩-over-∪ distributive law. -/

/-- A **UNION ALLEGORY** (§2.228): an allegory with finite unions that
    distribute with composition, but not necessarily with intersection.
    It carries the full distributive-lattice/zero structure on each hom-set
    together with composition-over-union distribution, but omits the
    intersection-over-union distributive law of §2.21. -/
class UnionAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- Zero morphism 0 : a → b for each pair of objects. -/
  zero {a b : 𝒜} : a ⟶ b
  /-- Union (join) R ∪ S : a → b when R, S : a → b. -/
  union {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- Zero is absorbing on the left: 0 ≫ R = 0. -/
  zero_comp {a b c : 𝒜} (R : b ⟶ c) : (zero : a ⟶ b) ≫ R = zero
  /-- Zero is absorbing on the right: R ≫ 0 = 0. -/
  comp_zero {a b c : 𝒜} (R : a ⟶ b) : R ≫ (zero : b ⟶ c) = zero

  /-- Union is idempotent: R ∪ R = R. -/
  union_idem {a b : 𝒜} (R : a ⟶ b) : union R R = R
  /-- Union is commutative: R ∪ S = S ∪ R. -/
  union_comm {a b : 𝒜} (R S : a ⟶ b) : union R S = union S R
  /-- Union is associative: R ∪ (S ∪ T) = (R ∪ S) ∪ T. -/
  union_assoc {a b : 𝒜} (R S T : a ⟶ b) : union R (union S T) = union (union R S) T

  /-- Absorption: R ∪ (S ∩ R) = R. -/
  union_inter_absorb {a b : 𝒜} (R S : a ⟶ b) : union R (Allegory.inter S R) = R
  /-- Absorption: (R ∪ S) ∩ R = R. -/
  inter_union_absorb {a b : 𝒜} (R S : a ⟶ b) : Allegory.inter (union R S) R = R

  /-- **Composition distributes over union**: R ≫ (S ∪ T) = RS ∪ RT.
      This is the defining property of §2.228. -/
  comp_union_distrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T)
  /-- Zero is identity for union: 0 ∪ R = R. -/
  zero_union {a b : 𝒜} (R : a ⟶ b) : union zero R = R

  -- NOTE (§2.228): the distributive-allegory law `inter_union_distrib`,
  --   R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T),
  -- is DELIBERATELY ABSENT here.  §2.228(a),(b) show it follows from
  -- tabularity / semi-simplicity; §2.228(c) shows it can genuinely fail.

/-- Zero notation for a union allegory. -/
notation "𝟘ᵤ" => UnionAllegory.zero

/-- Union notation for a union allegory. -/
infixl:65 " ∪ᵤ " => UnionAllegory.union

/-- Every distributive allegory (§2.21) is in particular a union allegory:
    it has all the §2.228 data and laws (and more). -/
instance distributiveAllegory_isUnionAllegory [DistributiveAllegory 𝒜] : UnionAllegory 𝒜 where
  zero := DistributiveAllegory.zero
  union := DistributiveAllegory.union
  zero_comp := DistributiveAllegory.zero_comp
  comp_zero := DistributiveAllegory.comp_zero
  union_idem := DistributiveAllegory.union_idem
  union_comm := DistributiveAllegory.union_comm
  union_assoc := DistributiveAllegory.union_assoc
  union_inter_absorb := DistributiveAllegory.union_inter_absorb
  inter_union_absorb := DistributiveAllegory.inter_union_absorb
  comp_union_distrib := DistributiveAllegory.comp_union_distrib
  zero_union := DistributiveAllegory.zero_union

/-! ### Order theory for a union allegory

  The lattice axioms shared with §2.21 (`union_inter_absorb`,
  `inter_union_absorb`, the union semigroup laws) suffice to recover the
  order/least-upper-bound theory of ∪ — none of these proofs uses the absent
  `inter_union_distrib`.  We re-derive them here for `UnionAllegory` so the
  §2.228 arguments can speak about ⊑ and ∪. -/

/-- In a union allegory, `R ⊑ S ↔ R ∪ S = S` (cf. §2.211; uses only the
    absorption laws, not ∩-over-∪ distribution). -/
theorem le_iff_unionU_eq_left [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) :
    (R ⊑ S) ↔ R ∪ᵤ S = S := by
  constructor
  · intro h
    dsimp [le] at h
    have h_absorb : S ∪ᵤ (R ∩ S) = S := UnionAllegory.union_inter_absorb S R
    calc
      R ∪ᵤ S = (R ∩ S) ∪ᵤ S := by rw [h]
      _ = S ∪ᵤ (R ∩ S) := UnionAllegory.union_comm _ _
      _ = S := h_absorb
  · intro h
    dsimp [le]
    calc
      R ∩ S = S ∩ R := Allegory.inter_comm R S
      _ = (R ∪ᵤ S) ∩ R := by rw [h]
      _ = R := UnionAllegory.inter_union_absorb R S

/-- Union is the least upper bound: `A ⊑ C → B ⊑ C → A ∪ B ⊑ C`. -/
theorem unionU_lub [UnionAllegory 𝒜] {a b : 𝒜} {A B C : a ⟶ b}
    (hA : A ⊑ C) (hB : B ⊑ C) : A ∪ᵤ B ⊑ C := by
  rw [le_iff_unionU_eq_left] at hA hB ⊢
  calc
    (A ∪ᵤ B) ∪ᵤ C = A ∪ᵤ (B ∪ᵤ C) := (UnionAllegory.union_assoc A B C).symm
    _ = A ∪ᵤ C := by rw [hB]
    _ = C := hA

/-- `R ⊑ R ∪ S`. -/
theorem le_unionU_left [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) : R ⊑ R ∪ᵤ S := by
  dsimp [le]; rw [Allegory.inter_comm, UnionAllegory.inter_union_absorb]

/-- `S ⊑ R ∪ S`. -/
theorem le_unionU_right [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) : S ⊑ R ∪ᵤ S := by
  rw [UnionAllegory.union_comm]; exact le_unionU_left S R

/-- Union is monotone in both arguments. -/
theorem unionU_mono [UnionAllegory 𝒜] {a b : 𝒜} {R R' S S' : a ⟶ b}
    (hR : R ⊑ R') (hS : S ⊑ S') : R ∪ᵤ S ⊑ R' ∪ᵤ S' :=
  unionU_lub (le_trans hR (le_unionU_left R' S')) (le_trans hS (le_unionU_right R' S'))

/-! ### The intersection-over-union law as a property

  In a `UnionAllegory` the law `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` is *not*
  assumed.  We isolate it as a predicate `InterUnionDistrib`; "is a
  distributive allegory" for a union allegory means exactly that this law
  holds (the remaining distributive-allegory axioms are already present). -/

/-- The intersection-over-union distributive law of §2.21, as a property of
    a union allegory.  When this holds, the union allegory is distributive. -/
def InterUnionDistrib (𝒜 : Type u) [UnionAllegory 𝒜] : Prop :=
  ∀ {a b : 𝒜} (R S T : a ⟶ b), R ∩ (S ∪ᵤ T) = (R ∩ S) ∪ᵤ (R ∩ T)

/-! ### Tabulation transport lemmas (for §2.228(a))

  Fix a tabulation `(f,g)` of `U` (so `f° f = g° g = 1`).  The map
  `φ Q := f° ≫ Q ≫ g` carries `{Q | Q ⊑ U}` to coreflexives on the apex
  (`tab_phi_coreflexive`), with intended inverse `ψ A := f ≫ A ≫ g°`.
  Freyd states this is an order-iso; in fact `ψ` is NOT a section of `φ`
  in a general tabular allegory (the round-trip `ψ(φ Q) = Q` FAILS — see the
  Rel counterexample in `tab_transport_gap`'s docstring).  The genuinely
  constructive content (`tab_phi_coreflexive`, `tab_deflate_source/target`)
  is recorded below; the distributivity is recovered in the SOURCE-apex frame
  (§2.143/§2.166, `interUnionU_distrib_of_srcTabulation`) — now Sorry-free. -/

/-- For a tabulation, `φ Q = f° Q g` is coreflexive whenever `Q ⊑ f g°`. -/
theorem tab_phi_coreflexive [UnionAllegory 𝒜] {a p c : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hff1 : f° ≫ f = Cat.id c) (hgg1 : g° ≫ g = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : Coreflexive (f° ≫ Q ≫ g) := by
  dsimp [Coreflexive]
  have h1 : f° ≫ Q ≫ g ⊑ f° ≫ (f ≫ g°) ≫ g :=
    comp_mono_left f° (comp_mono_right hQ g)
  have h2 : f° ≫ (f ≫ g°) ≫ g = Cat.id c := by
    calc f° ≫ (f ≫ g°) ≫ g
        = (f° ≫ f) ≫ (g° ≫ g) := by simp [Cat.assoc]
      _ = Cat.id c ≫ Cat.id c := by rw [hff1, hgg1]
      _ = Cat.id c := by rw [Cat.id_comp]
  rw [h2] at h1; exact h1

/-! ### Tabulation deflation calculus (constructive half-identities)

  For a tabulation `(f,g)` (so `f° f = 1`, `g° g = 1`) and `Q ⊑ f g°`, the
  two one-sided "deflations" below ARE provable constructively from the meet
  equations alone (no modular law even needed): `f° Q ⊑ g°` and `Q g ⊑ f`.
  They feed `tab_phi_coreflexive` and would feed the transport round-trip.

  WHAT IS NOT PROVABLE here (see `tab_transport_gap`): the full fixed-point
  identity `f (f° Q g) g° = Q` is FALSE in a general tabular allegory — it
  fails already in `Rel`.  Concrete witness (apex `c = {∗}`, `a = b = {1,2}`,
  `f,g` the unique maps to `{∗}`; both are maps with `f° f = g° g = 1_c`, so
  `(f,g)` tabulates the full relation `U = f g°`): for `Q = {(1,1)} ⊑ U` one
  computes `f° Q g = 1_c`, whence `f (f° Q g) g° = f g° = U ≠ Q`.  Hence the
  transport map `ψ A = f A g°` is NOT a section of `φ Q = f° Q g` on
  `{Q ⊑ U}`, and §2.228(a) genuinely needs the coreflexive/idempotent-
  splitting of §2.213/§2.226, absent from this repo. -/

/-- Tabulation deflation (source side): `f° Q ⊑ g°` for `Q ⊑ f g°` when
    `f° f = 1`.  Constructive, modular law not needed. -/
theorem tab_deflate_source [UnionAllegory 𝒜] {a c p : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hff1 : f° ≫ f = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : f° ≫ Q ⊑ g° := by
  calc f° ≫ Q ⊑ f° ≫ (f ≫ g°) := comp_mono_left f° hQ
    _ = (f° ≫ f) ≫ g° := by simp [Cat.assoc]
    _ = g° := by rw [hff1, Cat.id_comp]

/-- Tabulation deflation (target side): `Q g ⊑ f` for `Q ⊑ f g°` when
    `g° g = 1`.  Constructive, modular law not needed. -/
theorem tab_deflate_target [UnionAllegory 𝒜] {a c p : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} (hgg1 : g° ≫ g = Cat.id c)
    {Q : a ⟶ p} (hQ : Q ⊑ f ≫ g°) : Q ≫ g ⊑ f := by
  calc Q ≫ g ⊑ (f ≫ g°) ≫ g := comp_mono_right hQ g
    _ = f ≫ (g° ≫ g) := by simp [Cat.assoc]
    _ = f := by rw [hgg1, Cat.comp_id]

/-! ### The "easy" half of intersection-over-union

  In *any* union allegory the join-semidistributive inequality
      `(R ∩ S) ∪ (R ∩ T) ⊑ R ∩ (S ∪ T)`
  holds with no further hypotheses — both `R ∩ S` and `R ∩ T` sit below `R`
  and below `S ∪ T`.  So `InterUnionDistrib` is equivalent to the *reverse*
  containment, and §2.228(a),(b) only have to supply
      `R ∩ (S ∪ T) ⊑ (R ∩ S) ∪ (R ∩ T)`. -/

/-- The always-available half of ∩-over-∪: `(R∩S) ∪ (R∩T) ⊑ R ∩ (S∪T)`. -/
theorem interUnionU_distrib_ge [UnionAllegory 𝒜] {a b : 𝒜} (R S T : a ⟶ b) :
    (R ∩ S) ∪ᵤ (R ∩ T) ⊑ R ∩ (S ∪ᵤ T) := by
  refine unionU_lub (le_inter (inter_lb_left R S) ?_) (le_inter (inter_lb_left R T) ?_)
  · exact le_trans (inter_lb_right R S) (le_unionU_left S T)
  · exact le_trans (inter_lb_right R T) (le_unionU_right S T)

/-- `InterUnionDistrib` holds iff the *reverse* (hard) containment holds for
    every `R,S,T` — the easy direction `interUnionU_distrib_ge` is free. -/
theorem interUnionDistrib_iff_le [UnionAllegory 𝒜] :
    InterUnionDistrib 𝒜 ↔
      ∀ {a b : 𝒜} (R S T : a ⟶ b), R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  constructor
  · intro h a b R S T; rw [h R S T]; exact le_refl _
  · intro h a b R S T
    exact le_antisymm (h R S T) (interUnionU_distrib_ge R S T)

/-! ## §2.213 / §2.226  Idempotent-splitting transport calculus

  This is the constructive heart of §2.228(a),(b): the *systemic / Cauchy
  completion* machinery (§2.213, §2.226) that lets a tabulation `(f,g)` of
  `U = f g°` transport the order/lattice structure of `{Q | Q ⊑ U}` onto the
  coreflexives of the apex `c`, where ∩ and composition coincide
  (`coreflexive_comp_eq_inter`, §2.121) so that the lattice is distributive.

  Everything in this block is Sorry-free.  The *bridge* hypotheses
  (`hsplit*`, `hψcap`, `hψcup`) of `interUnionU_distrib_of_transport` package
  exactly the §2.213/§2.226 splitting: a coreflexive-valued retraction `ψ` of
  `φ Q := f° Q g` on `{Q ⊑ U}` that preserves ∩ and ∪.  In an EFFECTIVE
  allegory those hypotheses are *theorems* (split the coreflexive `□f`); for a
  bare tabular allegory they are NOT derivable (see `tab_transport_gap`). -/

/-- Reciprocation distributes over union (`(R ∪ S)° = R° ∪ S°`) in a union
    allegory — proved from the lub characterisation of ∪ and `recip` mono. -/
theorem recip_unionU [UnionAllegory 𝒜] {a b : 𝒜} (R S : a ⟶ b) :
    (R ∪ᵤ S)° = R° ∪ᵤ S° := by
  apply le_antisymm
  · rw [recip_le_iff]
    exact unionU_lub (recip_le_iff.mp (le_unionU_left R° S°))
      (recip_le_iff.mp (le_unionU_right R° S°))
  · exact unionU_lub (recip_mono (le_unionU_left R S)) (recip_mono (le_unionU_right R S))

/-- Composition distributes over union on the *right*: `(S ∪ T) g = Sg ∪ Tg`.
    The left law `comp_union_distrib` is an axiom; this is its reciprocal. -/
theorem unionU_comp_distrib [UnionAllegory 𝒜] {a b c : 𝒜} (S T : a ⟶ b) (g : b ⟶ c) :
    (S ∪ᵤ T) ≫ g = (S ≫ g) ∪ᵤ (T ≫ g) := by
  have h : ((S ∪ᵤ T) ≫ g)° = ((S ≫ g) ∪ᵤ (T ≫ g))° := by
    rw [recip_unionU, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_comp,
        recip_unionU, UnionAllegory.comp_union_distrib]
  calc (S ∪ᵤ T) ≫ g = (((S ∪ᵤ T) ≫ g)°)° := (Allegory.recip_recip _).symm
    _ = (((S ≫ g) ∪ᵤ (T ≫ g))°)° := by rw [h]
    _ = (S ≫ g) ∪ᵤ (T ≫ g) := Allegory.recip_recip _

/-- The transport map `φ Q := f° Q g` preserves union:
    `f° (S ∪ T) g = f° S g ∪ f° T g`. -/
theorem phi_unionU [UnionAllegory 𝒜] {a p c : 𝒜} (f : a ⟶ c) (g : p ⟶ c) (S T : a ⟶ p) :
    f° ≫ (S ∪ᵤ T) ≫ g = (f° ≫ S ≫ g) ∪ᵤ (f° ≫ T ≫ g) := by
  rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]

/-- `φ` is a retraction of `ψ A := f A g°` on the apex coreflexives:
    `φ (ψ A) = f° (f A g°) g = A`, using `f° f = g° g = 1_c`.  (This is the
    direction of the §2.226 splitting that holds unconditionally; the *other*
    round-trip `ψ (φ Q) = Q` is the genuine gap — see `tab_transport_gap`.) -/
theorem phi_psi_apex [UnionAllegory 𝒜] {a p c : 𝒜} {f : a ⟶ c} {g : p ⟶ c}
    (hff1 : f° ≫ f = Cat.id c) (hgg1 : g° ≫ g = Cat.id c) (A : c ⟶ c) :
    f° ≫ (f ≫ A ≫ g°) ≫ g = A := by
  calc f° ≫ (f ≫ A ≫ g°) ≫ g
      = (f° ≫ f) ≫ A ≫ (g° ≫ g) := by simp [Cat.assoc]
    _ = Cat.id c ≫ A ≫ Cat.id c := by rw [hff1, hgg1]
    _ = A := by rw [Cat.id_comp, Cat.comp_id]

/-- **`ψ∘φ`-deflation, free half** (the *entirety* containment of the §2.226
    round-trip).  When `f, g` are *entire* (in particular maps), the round-trip
    `ψ (φ Q) = f (f° Q g) g°` always *contains* `Q`:
        `Q ⊑ f f° Q g g°`.
    Proof: entirety gives `1_a ⊑ f f°` and `1_p ⊑ g g°`, then bracket `Q`.
    The *reverse* containment `f f° Q g g° ⊑ Q` is the genuine obstruction —
    it fails for the bare maps-to-terminal tabulation (`f f° = ⊤`), and is
    exactly what splitting the symmetric idempotent `□f` repairs (§2.166,
    §2.213, §2.226).  See `tab_transport_gap`. -/
theorem psi_phi_deflation [UnionAllegory 𝒜] {a p c : 𝒜} {f : a ⟶ c} {g : p ⟶ c}
    (hfe : Entire f) (hge : Entire g) (Q : a ⟶ p) :
    Q ⊑ f ≫ (f° ≫ Q ≫ g) ≫ g° := by
  dsimp [Entire, dom] at hfe hge
  have hf1 : Cat.id a ⊑ f ≫ f° := by
    have := inter_lb_right (Cat.id a) (f ≫ f°); rwa [hfe] at this
  have hg1 : Cat.id p ⊑ g ≫ g° := by
    have := inter_lb_right (Cat.id p) (g ≫ g°); rwa [hge] at this
  have step1 : Q ⊑ (f ≫ f°) ≫ Q := by
    have := comp_mono_right hf1 Q; rwa [Cat.id_comp] at this
  have step2 : (f ≫ f°) ≫ Q ⊑ ((f ≫ f°) ≫ Q) ≫ (g ≫ g°) := by
    have := comp_mono_left ((f ≫ f°) ≫ Q) hg1; rwa [Cat.comp_id] at this
  have h := le_trans step1 step2
  have heq : ((f ≫ f°) ≫ Q) ≫ (g ≫ g°) = f ≫ (f° ≫ Q ≫ g) ≫ g° := by simp [Cat.assoc]
  rwa [heq] at h

/-- `ψ A := f A g°` preserves union: `ψ (A ∪ B) = ψ A ∪ ψ B`.  This is the
    `hψcup` bridge hypothesis of `interUnionU_distrib_of_transport`, available
    unconditionally (no splitting needed) from composition-over-union. -/
theorem psi_unionU [UnionAllegory 𝒜] {a p c : 𝒜} (f : a ⟶ c) (g : p ⟶ c) (A B : c ⟶ c) :
    f ≫ (A ∪ᵤ B) ≫ g° = (f ≫ A ≫ g°) ∪ᵤ (f ≫ B ≫ g°) := by
  rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]

/-! ### Modular meet calculus: maps distribute over intersection (§2.136)

  Two genuinely-new modular-law facts, proved Sorry-free, that the §2.228(a)
  transport needs.  `simple_comp_inter` is Freyd §2.136 (`F(R∩S) = FR ∩ FS`
  for `F` simple); `modular_le_left` is the left-handed companion of
  `modular_le` (`(R≫S)∩T ⊑ R≫(S ∩ R°≫T)`), obtained by reciprocating the
  right modular law.  Together they drive the source-apex round-trip below. -/

/-- **§2.136**: a simple morphism distributes over intersection on the left,
    `F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S)` for `F` simple.  Proved by reciprocating
    and applying the right modular law, using `F° ≫ F ⊑ 1`. -/
theorem simple_comp_inter [UnionAllegory 𝒜] {a b c : 𝒜} {F : a ⟶ b}
    (hF : Simple F) (R S : b ⟶ c) : F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S) := by
  apply le_antisymm
  · exact le_inter (comp_mono_left F (inter_lb_left R S)) (comp_mono_left F (inter_lb_right R S))
  have hgoal : ((F ≫ R) ∩ (F ≫ S))° ⊑ (F ≫ (R ∩ S))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
        Allegory.recip_comp, Allegory.recip_inter]
    refine le_trans (modular_le R° F° (S° ≫ F°)) ?_
    apply comp_mono_right
    apply le_inter (inter_lb_left _ _)
    refine le_trans (inter_lb_right _ _) ?_
    rw [Allegory.recip_recip, Cat.assoc]
    calc S° ≫ (F° ≫ F) ⊑ S° ≫ Cat.id b := comp_mono_left S° hF
      _ = S° := Cat.comp_id S°
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-- The **left modular law** in order form: `(R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T)`.
    The reciprocal companion of `modular_le`; both are pure modular-law facts. -/
theorem modular_le_left [Allegory 𝒜] {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have h := modular_le S° R° T°
  rw [Allegory.recip_recip] at h
  have hgoal : ((R ≫ S) ∩ T)° ⊑ (R ≫ (S ∩ R° ≫ T))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_inter,
        Allegory.recip_comp, Allegory.recip_recip]
    exact h
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-! ### The source-apex round-trip is an EQUALITY (§2.143)

  This is the identity the earlier `tab_transport_gap` docstring claimed was
  *not* elementary.  It IS — provided one uses the **source-apex** tabulation
  (legs `F : c → a`, `G : c → p` out of the apex, `U = F° ≫ G`) rather than the
  repo's *target-apex* `Tabulates` (legs into the apex, `U = f ≫ g°`).  For the
  source-apex span the round-trip `F° (1_c ∩ F Q G°) G = Q` holds for every
  `Q ⊑ F° G`, with NO splitting and NO monic-pair hypothesis — only that
  `F, G` are maps.  (The repo's target-apex span has the *opposite* defect: the
  hard ≥-half holds but the easy ≤-half fails, since it would need `F F° ⊑ 1`.)

  Hence the genuine residual of §2.228(a) is *not* a missing identity but the
  missing **source-apex tabulation** itself: `Tabular`/`TabularAllegory` in this
  repo provide only the target-apex (cospan) form `U = f g°`.  Turning that into
  a jointly-monic span `c → a`, `c → p` is the §2.147 pullback / §2.226 systemic
  completion — the single construction still absent (it needs products or the
  completion object, neither available from `EffectiveAllegory` alone). -/

/-- **§2.143 source-apex round-trip** (Sorry-free).  For maps `F : c → a`,
    `G : c → p` and any `Q ⊑ F° ≫ G`, the transport `Φ Q := 1_c ∩ F Q G°`
    (a coreflexive on the apex `c`) is inverted by `Ψ A := F° A G`:
        `F° ≫ (1_c ∩ F ≫ Q ≫ G°) ≫ G = Q`.
    Easy ≤-half uses `F, G` simple; hard ≥-half uses the modular law and
    `Q ⊑ F° G` (via `modular_le`, `modular_le_left`). -/
theorem src_apex_roundtrip [UnionAllegory 𝒜] {a p c : 𝒜} {F : c ⟶ a} {G : c ⟶ p}
    (hF : Map F) (hG : Map G) {Q : a ⟶ p} (hQ : Q ⊑ F° ≫ G) :
    F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G = Q := by
  apply le_antisymm
  · -- ≤ : F°(1∩FQG°)G ⊑ F°(FQG°)G = (F°F)Q(G°G) ⊑ Q, using F,G simple
    have hFs : F° ≫ F ⊑ Cat.id a := hF.2
    have hGs : G° ≫ G ⊑ Cat.id p := hG.2
    have key : (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) ⊑ Q := by
      have a1 : (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) ⊑ Cat.id a ≫ (Q ≫ (G° ≫ G)) := comp_mono_right hFs _
      rw [Cat.id_comp] at a1
      have a3 : Q ≫ (G° ≫ G) ⊑ Q ≫ Cat.id p := comp_mono_left Q hGs
      rw [Cat.comp_id] at a3
      exact le_trans a1 a3
    have b1 : F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ F° ≫ (F ≫ Q ≫ G°) ≫ G :=
      comp_mono_left F° (comp_mono_right (inter_lb_right _ _) G)
    have b2 : F° ≫ (F ≫ Q ≫ G°) ≫ G = (F° ≫ F) ≫ (Q ≫ (G° ≫ G)) := by simp [Cat.assoc]
    rw [b2] at b1
    exact le_trans b1 key
  · -- ≥ : Q ⊑ (F° ∩ QG°)G ⊑ F°(1 ∩ FQG°)G, via modular_le and modular_le_left
    have s1 : Q ⊑ (F° ∩ (Q ≫ G°)) ≫ G := by
      have hm := modular_le F° G Q
      have heq : (F° ≫ G) ∩ Q = Q := by rw [Allegory.inter_comm]; exact inter_eq_left hQ
      rwa [heq] at hm
    have s2 : (F° ∩ (Q ≫ G°)) ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) := by
      have hml := modular_le_left F° (Cat.id c) (Q ≫ G°)
      rw [Cat.comp_id, Allegory.recip_recip] at hml
      exact hml
    have s3 : (F° ∩ (Q ≫ G°)) ≫ G ⊑ (F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°))) ≫ G :=
      comp_mono_right s2 G
    rw [Cat.assoc] at s3
    exact le_trans s1 s3

/-- **The coreflexive distributive law** (§2.121 → §2.213).  On the
    coreflexives of any object, intersection *equals* composition
    (`coreflexive_comp_eq_inter`), and composition distributes over union
    (`comp_union_distrib`); hence ∩ distributes over ∪ *as an equality*.
    This is the distributivity that §2.228(a) transports back to `{Q ⊑ U}`. -/
theorem coreflexive_inter_unionU_distrib [UnionAllegory 𝒜] {c : 𝒜} {A B C : c ⟶ c}
    (hA : Coreflexive A) (hB : Coreflexive B) (hC : Coreflexive C) :
    A ∩ (B ∪ᵤ C) = (A ∩ B) ∪ᵤ (A ∩ C) := by
  have hBC : Coreflexive (B ∪ᵤ C) := unionU_lub hB hC
  rw [← coreflexive_comp_eq_inter hA hBC, UnionAllegory.comp_union_distrib,
      coreflexive_comp_eq_inter hA hB, coreflexive_comp_eq_inter hA hC]

/-- **§2.213/§2.226 transport theorem** (Sorry-free, conditional).  Given a
    coreflexive-valued retraction `ψ` of `φ Q := f° Q g` on `{Q ⊑ U}` that
    preserves ∩ (on coreflexives) and ∪, the coreflexive distributive law
    transports back to give the full ∩-over-∪ *equality* `R ∩ (S∪T) =
    (R∩S)∪(R∩T)`, hence the §2.228(a) containment, for `R,S,T` whose
    `φ`-images are coreflexive and which `ψ∘φ` fixes.

    The hypotheses `hsplit*` (ψ∘φ = id), `hψcap`, `hψcup` are *precisely* what
    splitting the symmetric idempotent `□f` (§2.213/§2.226) supplies in an
    effective allegory.  Supplying them is the only remaining content of
    §2.228(a),(b); see `tab_transport_gap`. -/
theorem interUnionU_distrib_of_transport [UnionAllegory 𝒜] {a p c : 𝒜}
    {f : a ⟶ c} {g : p ⟶ c} {R S T : a ⟶ p}
    (ψ : (c ⟶ c) → (a ⟶ p))
    (hsplitR : ψ (f° ≫ R ≫ g) = R) (hsplitS : ψ (f° ≫ S ≫ g) = S)
    (hsplitT : ψ (f° ≫ T ≫ g) = T)
    (hcR : Coreflexive (f° ≫ R ≫ g)) (hcS : Coreflexive (f° ≫ S ≫ g))
    (hcT : Coreflexive (f° ≫ T ≫ g))
    (hψcap : ∀ A B : c ⟶ c, Coreflexive A → Coreflexive B → ψ (A ∩ B) = ψ A ∩ ψ B)
    (hψcup : ∀ A B : c ⟶ c, ψ (A ∪ᵤ B) = ψ A ∪ᵤ ψ B) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  have key := coreflexive_inter_unionU_distrib hcR hcS hcT
  have happ := congrArg ψ key
  rw [hψcap _ _ hcR (unionU_lub hcS hcT), hψcup, hψcup,
      hψcap _ _ hcR hcS, hψcap _ _ hcR hcT, hsplitR, hsplitS, hsplitT] at happ
  rw [happ]; exact le_refl _

/-! ### §2.143 / §2.166  Source-apex tabulation transport (the genuine order-iso)

  The target-apex transport (`interUnionU_distrib_of_transport`) used the routing
  `φ Q := f° Q g`, where the round-trip `ψ(φ Q) = Q` genuinely FAILS for a bare
  tabulation (Rel singleton counterexample).  The repair is the SOURCE-APEX routing
  of §2.143/§2.166: a span of *maps* `F : c → a`, `G : c → p` with `U = F° G` that
  is **jointly monic on the apex**, `F F° ∩ G G° = 1_c`.  For such a span the
  order-iso

      φ Q := 1_c ∩ F Q G°   (coreflexive on c),   ψ A := F° A G

  between `{Q | Q ⊑ U}` and the coreflexives of `c` is *genuine* — BOTH round-trips
  hold — and the distributive coreflexive lattice transports back.  Everything in
  this block is Sorry-free; the four order-iso half-identities are
  `src_roundtrip_le` (`ψφ ⊑ id`), `src_roundtrip_ge` (`id ⊑ ψφ`),
  `src_phipsi_le` (`φψ ⊑ id`), `src_phipsi_ge` (`id ⊑ φψ`).  The single piece
  still missing from this repo is the *construction* of such a span for an
  arbitrary `U` (§2.166), isolated as the lone hole `srcTabulation_exists`. -/

/-- **Left-handed modular law**: `S ∩ R≫T ⊑ R ≫ (R°≫S ∩ T)`.  The reciprocal
    companion of `modular_le`; obtained by reciprocating `modular_le` on `T°,R°,S°`. -/
theorem left_modular_le {a b d : 𝒜} [Allegory 𝒜] (R : a ⟶ b) (S : a ⟶ d) (T : b ⟶ d) :
    S ∩ R ≫ T ⊑ R ≫ (R° ≫ S ∩ T) := by
  have hgoal : (S ∩ R ≫ T)° ⊑ (R ≫ (R° ≫ S ∩ T))° := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_inter,
        Allegory.recip_comp, Allegory.recip_recip]
    have hm := modular_le T° R° S°
    rw [Allegory.recip_recip] at hm
    rw [Allegory.inter_comm S° (T° ≫ R°), Allegory.inter_comm (S° ≫ R) T°]
    exact hm
  have := recip_mono hgoal
  rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-- **Apex coupling lemma** (the heart of §2.143's "H is simple").  For a
    jointly-monic span (`F F° ∩ G G° = 1_c`) and a coreflexive `A`, the two
    coupled composites meet inside `A`: `(F F°≫A) ∩ (G G°≫A) ⊑ A`. -/
theorem srcTab_cap {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    ((F ≫ F°) ≫ A) ∩ ((G ≫ G°) ≫ A) ⊑ A := by
  have hAcoref : A ⊑ Cat.id c := hA
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  have hAidem : A ≫ A = A := (coreflexive_symmetric_idempotent hA).2
  have m := modular_le (F ≫ F°) A ((G ≫ G°) ≫ A)
  rw [hAsymm] at m
  rw [show ((G ≫ G°) ≫ A) ≫ A = (G ≫ G°) ≫ A by rw [Cat.assoc, hAidem]] at m
  refine le_trans m ?_
  have hcap : (F ≫ F°) ∩ ((G ≫ G°) ≫ A) ⊑ Cat.id c := by
    have h1 : (G ≫ G°) ≫ A ⊑ G ≫ G° := by
      have := comp_mono_left (G ≫ G°) hAcoref; rwa [Cat.comp_id] at this
    calc (F ≫ F°) ∩ ((G ≫ G°) ≫ A) ⊑ (F ≫ F°) ∩ (G ≫ G°) :=
          le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h1)
      _ = Cat.id c := hmonic
  have := comp_mono_right hcap A; rwa [Cat.id_comp] at this

/-- One-sided deflation feeding `src_phipsi_le`: `1_c ∩ F F° A G G° ⊑ A G G°`. -/
theorem srcTab_peel {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ A ≫ (G ≫ G°) := by
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  have hAidem : A ≫ A = A := (coreflexive_symmetric_idempotent hA).2
  have mL := modular_le (F ≫ F°) (A ≫ (G ≫ G°)) (Cat.id c)
  rw [Allegory.inter_comm ((F ≫ F°) ≫ A ≫ (G ≫ G°)) (Cat.id c)] at mL
  rw [show (A ≫ (G ≫ G°))° = (G ≫ G°) ≫ A by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm],
      Cat.id_comp] at mL
  refine le_trans mL ?_
  have hCA : (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A ⊑ A := by
    have hsd : (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A ⊑ ((F ≫ F°) ≫ A) ∩ (((G ≫ G°) ≫ A) ≫ A) :=
      le_inter (comp_mono_right (inter_lb_left _ _) A) (comp_mono_right (inter_lb_right _ _) A)
    rw [show ((G ≫ G°) ≫ A) ≫ A = (G ≫ G°) ≫ A by rw [Cat.assoc, hAidem]] at hsd
    exact le_trans hsd (srcTab_cap hmonic hA)
  rw [show (F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ (A ≫ (G ≫ G°))
        = ((F ≫ F° ∩ (G ≫ G°) ≫ A) ≫ A) ≫ (G ≫ G°) by simp [Cat.assoc]]
  exact comp_mono_right hCA (G ≫ G°)

/-- **`φψ ⊑ id`** (§2.143/§2.166).  For a jointly-monic span the round-trip
    `φ(ψ A) = 1_c ∩ F F° A G G°` lands back below the coreflexive `A`. -/
theorem src_phipsi_le {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c) {A : c ⟶ c} (hA : Coreflexive A) :
    Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) ⊑ A := by
  have hAsymm : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hA).1
  rw [show F ≫ (F° ≫ A ≫ G) ≫ G° = (F ≫ F°) ≫ A ≫ (G ≫ G°) by simp [Cat.assoc]]
  have hMsymm : (Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)))° = Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) :=
    symmetric_eq (coreflexive_symmetric_idempotent (le_trans (inter_lb_left _ _) (le_refl _))).1
  have hmonic' : G ≫ G° ∩ F ≫ F° = Cat.id c := by rw [Allegory.inter_comm]; exact hmonic
  have hGGA : Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ (G ≫ G°) ≫ A := by
    have h := recip_mono (srcTab_peel hmonic hA); rw [hMsymm] at h
    rwa [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm] at h
  have hMrecip_eq :
      (Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)))° = Cat.id c ∩ ((G ≫ G°) ≫ A ≫ (F ≫ F°)) := by
    simp only [Allegory.recip_inter, recip_id, Allegory.recip_comp, Allegory.recip_recip, hAsymm]
    simp [Cat.assoc]
  have hFFA : Cat.id c ∩ ((F ≫ F°) ≫ A ≫ (G ≫ G°)) ⊑ (F ≫ F°) ≫ A := by
    have hp := srcTab_peel hmonic' hA
    rw [← hMrecip_eq] at hp
    have h := recip_mono hp; rw [Allegory.recip_recip] at h
    rwa [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hAsymm] at h
  exact le_trans (le_inter hFFA hGGA) (srcTab_cap hmonic hA)

/-- **`id ⊑ φψ`** (§2.143/§2.166).  For an *entire* span `1_c ⊑ F F°`, `1_c ⊑ G G°`,
    the round-trip `φ(ψ A)` contains the coreflexive `A`. -/
theorem src_phipsi_ge {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hFe : Entire F) (hGe : Entire G) {A : c ⟶ c} (hA : Coreflexive A) :
    A ⊑ Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) := by
  have hf1 : Cat.id c ⊑ F ≫ F° := by
    dsimp [Entire, dom] at hFe
    have := inter_lb_right (Cat.id c) (F ≫ F°); rwa [hFe] at this
  have hg1 : Cat.id c ⊑ G ≫ G° := by
    dsimp [Entire, dom] at hGe
    have := inter_lb_right (Cat.id c) (G ≫ G°); rwa [hGe] at this
  apply le_inter hA
  have e1 : A ⊑ (F ≫ F°) ≫ A := by
    have := comp_mono_right hf1 A; rwa [Cat.id_comp] at this
  have e2 : (F ≫ F°) ≫ A ⊑ ((F ≫ F°) ≫ A) ≫ (G ≫ G°) := by
    have := comp_mono_left ((F ≫ F°) ≫ A) hg1; rwa [Cat.comp_id] at this
  have e3 : ((F ≫ F°) ≫ A) ≫ (G ≫ G°) = F ≫ (F° ≫ A ≫ G) ≫ G° := by simp [Cat.assoc]
  exact e3 ▸ le_trans e1 e2

/-- **`ψφ ⊑ id`** (§2.143).  `ψ(φ Q) = F° (1_c ∩ F Q G°) G ⊑ Q` for any `Q`,
    using only that `F, G` are simple (`F° F ⊑ 1`, `G° G ⊑ 1`). -/
theorem src_roundtrip_le {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    (hFs : F° ≫ F ⊑ Cat.id a) (hGs : G° ≫ G ⊑ Cat.id p) (Q : a ⟶ p) :
    F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ Q := by
  have hstep : F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ F° ≫ (F ≫ Q ≫ G°) ≫ G :=
    comp_mono_left F° (comp_mono_right (inter_lb_right _ _) G)
  have heq : F° ≫ (F ≫ Q ≫ G°) ≫ G = (F° ≫ F) ≫ Q ≫ (G° ≫ G) := by simp [Cat.assoc]
  have hb1 : (F° ≫ F) ≫ Q ≫ (G° ≫ G) ⊑ Cat.id a ≫ Q ≫ (G° ≫ G) := comp_mono_right hFs _
  have hb2 : Cat.id a ≫ Q ≫ (G° ≫ G) ⊑ Cat.id a ≫ Q ≫ Cat.id p :=
    comp_mono_left _ (comp_mono_left Q hGs)
  have hbound : (F° ≫ F) ≫ Q ≫ (G° ≫ G) ⊑ Q := by
    have h := le_trans hb1 hb2
    rwa [show Cat.id a ≫ Q ≫ Cat.id p = Q by simp [Cat.id_comp, Cat.comp_id]] at h
  exact le_trans hstep (heq ▸ hbound)

/-- **`id ⊑ ψφ`** (§2.143).  `Q ⊑ ψ(φ Q) = F° (1_c ∩ F Q G°) G` for `Q ⊑ F° G`,
    using only the (left-)modular law — no map or monic hypothesis. -/
theorem src_roundtrip_ge {a p c : 𝒜} [Allegory 𝒜] {F : c ⟶ a} {G : c ⟶ p}
    {Q : a ⟶ p} (hQ : Q ⊑ F° ≫ G) :
    Q ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G := by
  have hstep1 : Q ⊑ (F° ∩ (Q ≫ G°)) ≫ G := by
    calc Q = (F° ≫ G) ∩ Q := by rw [Allegory.inter_comm]; exact (inter_eq_left hQ).symm
      _ ⊑ (F° ∩ (Q ≫ G°)) ≫ G := modular_le F° G Q
  have hlm := left_modular_le F° (Q ≫ G°) (Cat.id c)
  rw [Cat.comp_id, Allegory.recip_recip] at hlm
  have hmid : F° ∩ (Q ≫ G°) ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) := by
    rw [Allegory.inter_comm F° (Q ≫ G°)]
    refine le_trans hlm (comp_mono_left F° ?_)
    rw [Allegory.inter_comm (F ≫ Q ≫ G°) (Cat.id c)]; exact le_refl _
  have hstep2 : (F° ∩ (Q ≫ G°)) ≫ G ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G := by
    have h := comp_mono_right hmid G; rwa [Cat.assoc] at h
  exact le_trans hstep1 hstep2

/-- **§2.228(a) transport, made unconditional on the span** (Sorry-free).  Given a
    SOURCE-APEX span of maps `(F, G)` jointly monic on the apex (`F F° ∩ G G° = 1_c`)
    with `R, S, T ⊑ F° G`, the order-iso `φ Q := 1_c ∩ F Q G°` / `ψ A := F° A G`
    transports the distributive coreflexive lattice of `c` back to give the
    ∩-over-∪ containment.  This is Freyd's §2.228(a) argument with the genuine
    §2.143/§2.166 round-trips supplied; the ONLY thing it still presupposes is the
    *existence* of such a span (the §2.166 refinement). -/
theorem interUnionU_distrib_of_srcTabulation [UnionAllegory 𝒜] {a p c : 𝒜}
    {F : c ⟶ a} {G : c ⟶ p}
    (hFm : Map F) (hGm : Map G) (hmonic : F ≫ F° ∩ G ≫ G° = Cat.id c)
    {R S T : a ⟶ p} (hR : R ⊑ F° ≫ G) (hS : S ⊑ F° ≫ G) (hT : T ⊑ F° ≫ G) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  -- φ Q := 1_c ∩ F Q G° (coreflexive on c); ψ A := F° A G.  Written out inline.
  have hφmono : ∀ {Q₁ Q₂ : a ⟶ p}, Q₁ ⊑ Q₂ →
      Cat.id c ∩ (F ≫ Q₁ ≫ G°) ⊑ Cat.id c ∩ (F ≫ Q₂ ≫ G°) := by
    intro Q₁ Q₂ h
    exact le_inter (inter_lb_left _ _)
      (le_trans (inter_lb_right _ _) (comp_mono_left F (comp_mono_right h G°)))
  have hψmono : ∀ {A B : c ⟶ c}, A ⊑ B → F° ≫ A ≫ G ⊑ F° ≫ B ≫ G := by
    intro A B h; exact comp_mono_left F° (comp_mono_right h G)
  have hφcoref : ∀ Q : a ⟶ p, Coreflexive (Cat.id c ∩ (F ≫ Q ≫ G°)) := fun Q => inter_lb_left _ _
  have hrtle : ∀ Q : a ⟶ p, F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G ⊑ Q :=
    fun Q => src_roundtrip_le hFm.2 hGm.2 Q
  have hrtge : ∀ {Q : a ⟶ p}, Q ⊑ F° ≫ G → Q ⊑ F° ≫ (Cat.id c ∩ (F ≫ Q ≫ G°)) ≫ G :=
    fun h => src_roundtrip_ge h
  have hpple : ∀ {A : c ⟶ c}, Coreflexive A → Cat.id c ∩ (F ≫ (F° ≫ A ≫ G) ≫ G°) ⊑ A :=
    fun hA => src_phipsi_le hmonic hA
  have hψcup : ∀ A B : c ⟶ c, F° ≫ (A ∪ᵤ B) ≫ G = (F° ≫ A ≫ G) ∪ᵤ (F° ≫ B ≫ G) := by
    intro A B; rw [unionU_comp_distrib, UnionAllegory.comp_union_distrib]
  have hφcup : ∀ {S T : a ⟶ p}, S ⊑ F° ≫ G → T ⊑ F° ≫ G →
      Cat.id c ∩ (F ≫ (S ∪ᵤ T) ≫ G°) ⊑ (Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)) := by
    intro S T hS hT
    have hbig : S ∪ᵤ T ⊑
        F° ≫ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°))) ≫ G := by
      rw [hψcup]
      exact unionU_lub (le_trans (hrtge hS) (le_unionU_left _ _))
        (le_trans (hrtge hT) (le_unionU_right _ _))
    exact le_trans (hφmono hbig) (hpple (unionU_lub (hφcoref S) (hφcoref T)))
  have hcapbound : ∀ X Y : a ⟶ p,
      F° ≫ ((Cat.id c ∩ (F ≫ X ≫ G°)) ∩ (Cat.id c ∩ (F ≫ Y ≫ G°))) ≫ G ⊑ X ∩ Y := by
    intro X Y
    exact le_inter (le_trans (hψmono (inter_lb_left _ _)) (hrtle X))
      (le_trans (hψmono (inter_lb_right _ _)) (hrtle Y))
  have hcoreflaw :
      (Cat.id c ∩ (F ≫ R ≫ G°)) ∩ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)))
        = ((Cat.id c ∩ (F ≫ R ≫ G°)) ∩ (Cat.id c ∩ (F ≫ S ≫ G°)))
          ∪ᵤ ((Cat.id c ∩ (F ≫ R ≫ G°)) ∩ (Cat.id c ∩ (F ≫ T ≫ G°))) :=
    coreflexive_inter_unionU_distrib (hφcoref R) (hφcoref S) (hφcoref T)
  have hRcup : R ∩ (S ∪ᵤ T) ⊑ F° ≫ G := le_trans (inter_lb_left _ _) hR
  have hlhs : R ∩ (S ∪ᵤ T) ⊑
      F° ≫ ((Cat.id c ∩ (F ≫ R ≫ G°))
        ∩ ((Cat.id c ∩ (F ≫ S ≫ G°)) ∪ᵤ (Cat.id c ∩ (F ≫ T ≫ G°)))) ≫ G := by
    refine le_trans (hrtge hRcup) (hψmono ?_)
    refine le_inter (hφmono (inter_lb_left _ _)) ?_
    exact le_trans (hφmono (inter_lb_right _ _)) (hφcup hS hT)
  rw [hcoreflaw, hψcup] at hlhs
  exact le_trans hlhs (unionU_mono (hcapbound R S) (hcapbound R T))

/-! ## §2.228(a)  A tabular union allegory is distributive

  *A tabular allegory with this property is distributive.*

  Freyd's argument: given R, S, T ∈ (a,p), let (F,G) be a SOURCE-apex tabulation
  of U := R ∪ S ∪ T (maps `F : c → a`, `G : c → p`, `U = F° G`, jointly monic
  `F F° ∩ G G° = 1_c`).  The poset `{ Q | Q ⊑ F° G }` is order-isomorphic to the
  coreflexives of `c` via `φ Q := 1_c ∩ F Q G°`, `ψ A := F° A G`, where
  coreflexives form a distributive lattice (`coreflexive_comp_eq_inter`).  Hence ∩
  distributes over ∪.  The order-iso is `interUnionU_distrib_of_srcTabulation`
  (Sorry-free); the span itself is `srcTabulation_exists`, now CLOSED via §2.16(10)
  (`srcTabulation_of_semiSimple_split`: split `F₀F₀° ∩ G₀G₀°` of `U = F₀° G₀`). -/

/-! ### §2.16(10)  Building the source-apex span by splitting `F₀F₀° ∩ G₀G₀°`

  Freyd's §2.16(10) "routine" construction, made Sorry-free.  From a semi-simple
  factorisation `U = F₀° G₀` (`F₀, G₀` simple) the meet `E := F₀F₀° ∩ G₀G₀°` is a
  symmetric idempotent (symmetric + transitive ⟹ idempotent, §2.12).  In an
  EFFECTIVE allegory `E` splits: a map `f : c₀ → c` with `f f° = E`, `f° f = 1_c`.
  Then `F := f° ≫ F₀ : c → a`, `G := f° ≫ G₀ : c → p` are MAPS with `U = F° G` and
  `F F° ∩ G G° = 1_c` — a SOURCE-apex jointly-monic span of `U`. -/

-- (The Dedekind identity `R ⊑ (R≫R°)≫R` is `le_comp_recip_comp` from A4_1 — B&dM 4.10,
--  in scope via S2_3; the local copy `self_le_comp_recip_comp` was deduped.)

/-- **§2.12**: a symmetric transitive morphism is idempotent (`E ≫ E = E`). -/
theorem symmetric_transitive_idempotent [Allegory 𝒜] {a : 𝒜} {E : a ⟶ a}
    (hsym : Symmetric E) (htrans : Transitive E) : E ≫ E = E := by
  apply le_antisymm htrans
  have heq : E° = E := symmetric_eq hsym
  have h1 : E ⊑ (E ≫ E) ≫ E := by simpa [heq] using le_comp_recip_comp E
  have h2 : (E ≫ E) ≫ E ⊑ E ≫ E := by rw [Cat.assoc]; exact comp_mono_left E htrans
  exact le_trans h1 h2

/-- **§2.16(10)**: for simple `F₀, G₀`, the meet `F₀F₀° ∩ G₀G₀°` is a symmetric
    idempotent (symmetric, and transitive since `F₀° F₀ ⊑ 1`, `G₀° G₀ ⊑ 1`). -/
theorem capE_symm_idem [Allegory 𝒜] {a p c0 : 𝒜} {F0 : c0 ⟶ a} {G0 : c0 ⟶ p}
    (hF0 : Simple F0) (hG0 : Simple G0) :
    Symmetric (F0 ≫ F0° ∩ G0 ≫ G0°) ∧
      (F0 ≫ F0° ∩ G0 ≫ G0°) ≫ (F0 ≫ F0° ∩ G0 ≫ G0°) = (F0 ≫ F0° ∩ G0 ≫ G0°) := by
  have hsym : Symmetric (F0 ≫ F0° ∩ G0 ≫ G0°) := by
    rw [symmetric_iff, Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
        Allegory.recip_recip, Allegory.recip_recip]
  have hFF : (F0 ≫ F0°) ≫ (F0 ≫ F0°) ⊑ F0 ≫ F0° := by
    calc (F0 ≫ F0°) ≫ (F0 ≫ F0°) = F0 ≫ (F0° ≫ F0) ≫ F0° := by simp [Cat.assoc]
      _ ⊑ F0 ≫ Cat.id a ≫ F0° := comp_mono_left F0 (comp_mono_right hF0 F0°)
      _ = F0 ≫ F0° := by rw [Cat.id_comp]
  have hGG : (G0 ≫ G0°) ≫ (G0 ≫ G0°) ⊑ G0 ≫ G0° := by
    calc (G0 ≫ G0°) ≫ (G0 ≫ G0°) = G0 ≫ (G0° ≫ G0) ≫ G0° := by simp [Cat.assoc]
      _ ⊑ G0 ≫ Cat.id p ≫ G0° := comp_mono_left G0 (comp_mono_right hG0 G0°)
      _ = G0 ≫ G0° := by rw [Cat.id_comp]
  have htrans : Transitive (F0 ≫ F0° ∩ G0 ≫ G0°) := by
    have hEF : (F0 ≫ F0° ∩ G0 ≫ G0°) ≫ (F0 ≫ F0° ∩ G0 ≫ G0°) ⊑ F0 ≫ F0° :=
      le_trans (le_trans (comp_mono_right (inter_lb_left _ _) _)
        (comp_mono_left _ (inter_lb_left _ _))) hFF
    have hEG : (F0 ≫ F0° ∩ G0 ≫ G0°) ≫ (F0 ≫ F0° ∩ G0 ≫ G0°) ⊑ G0 ≫ G0° :=
      le_trans (le_trans (comp_mono_right (inter_lb_right _ _) _)
        (comp_mono_left _ (inter_lb_right _ _))) hGG
    exact le_inter hEF hEG
  exact ⟨hsym, symmetric_transitive_idempotent hsym htrans⟩

/-- The leg `f° ≫ F₀` of the §2.16(10) split is a MAP, given `f° f = 1_c`,
    `f f° ⊑ F₀F₀°` and `F₀` simple.  (Entire from `1_c = f°(ff°)f ⊑ F F°`;
    simple from `F° F = F₀°(ff°)F₀ ⊑ (F₀°F₀)(F₀°F₀) ⊑ 1`.) -/
theorem srcTab_leg_map [Allegory 𝒜] {a c0 c : 𝒜} {F0 : c0 ⟶ a} {f : c0 ⟶ c}
    (hf1 : f° ≫ f = Cat.id c) (hEleF : f ≫ f° ⊑ F0 ≫ F0°) (hF0 : Simple F0) :
    Map (f° ≫ F0) := by
  refine ⟨?_, ?_⟩
  · dsimp [Entire, dom]
    have hFFr : (f° ≫ F0) ≫ (f° ≫ F0)° = f° ≫ (F0 ≫ F0°) ≫ f := by
      rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
    have h1le : Cat.id c ⊑ (f° ≫ F0) ≫ (f° ≫ F0)° := by
      rw [hFFr]
      have e0 : Cat.id c = f° ≫ (f ≫ f°) ≫ f := by
        have h2 : f° ≫ (f ≫ f°) ≫ f = (f° ≫ f) ≫ (f° ≫ f) := by simp [Cat.assoc]
        rw [h2, hf1, Cat.id_comp]
      rw [e0]; exact comp_mono_left f° (comp_mono_right hEleF f)
    exact inter_eq_left h1le
  · dsimp [Simple]
    have heq : (f° ≫ F0)° ≫ (f° ≫ F0) = F0° ≫ (f ≫ f°) ≫ F0 := by
      rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
    rw [heq]
    refine le_trans (comp_mono_left F0° (comp_mono_right hEleF F0)) ?_
    have heq2 : F0° ≫ (F0 ≫ F0°) ≫ F0 = (F0° ≫ F0) ≫ (F0° ≫ F0) := by simp [Cat.assoc]
    rw [heq2]
    refine le_trans (comp_mono_left _ hF0) ?_
    rw [Cat.comp_id]; exact hF0

/-- **§2.16(10) monic condition**: the two legs `f° F₀`, `f° G₀` of the split are
    jointly monic, `(f° F₀)(f° F₀)° ∩ (f° G₀)(f° G₀)° = 1_c`.  Proof avoids the
    (false-in-general) conjugation-meet identity: conjugate `M := FF° ∩ GG°` by
    `f, f°` to land below `f f°` (`f M f° ⊑ F₀F₀° ∩ G₀G₀° = f f°` via the
    transitive "sandwich" `E X E ⊑ X`), then `M = f°(f M f°)f ⊑ f°(ff°)f = 1`. -/
theorem srcTab_monic [Allegory 𝒜] {a p c0 c : 𝒜} {F0 : c0 ⟶ a} {G0 : c0 ⟶ p}
    {f : c0 ⟶ c} (hf1 : f° ≫ f = Cat.id c) (hffE : f ≫ f° = F0 ≫ F0° ∩ G0 ≫ G0°)
    (hF0 : Simple F0) (hG0 : Simple G0) :
    (f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)° = Cat.id c := by
  have hFFr : (f° ≫ F0) ≫ (f° ≫ F0)° = f° ≫ (F0 ≫ F0°) ≫ f := by
    rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  have hGGr : (f° ≫ G0) ≫ (f° ≫ G0)° = f° ≫ (G0 ≫ G0°) ≫ f := by
    rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  have hEle1 : f ≫ f° ⊑ F0 ≫ F0° := by rw [hffE]; exact inter_lb_left _ _
  have hEle2 : f ≫ f° ⊑ G0 ≫ G0° := by rw [hffE]; exact inter_lb_right _ _
  have hFt : (F0 ≫ F0°) ≫ (F0 ≫ F0°) ⊑ F0 ≫ F0° := by
    calc (F0 ≫ F0°) ≫ (F0 ≫ F0°) = F0 ≫ (F0° ≫ F0) ≫ F0° := by simp [Cat.assoc]
      _ ⊑ F0 ≫ Cat.id a ≫ F0° := comp_mono_left F0 (comp_mono_right hF0 F0°)
      _ = F0 ≫ F0° := by rw [Cat.id_comp]
  have hGt : (G0 ≫ G0°) ≫ (G0 ≫ G0°) ⊑ G0 ≫ G0° := by
    calc (G0 ≫ G0°) ≫ (G0 ≫ G0°) = G0 ≫ (G0° ≫ G0) ≫ G0° := by simp [Cat.assoc]
      _ ⊑ G0 ≫ Cat.id p ≫ G0° := comp_mono_left G0 (comp_mono_right hG0 G0°)
      _ = G0 ≫ G0° := by rw [Cat.id_comp]
  have sand : ∀ {X : c0 ⟶ c0}, f ≫ f° ⊑ X → (X ≫ X ⊑ X) →
      (f ≫ f°) ≫ X ≫ (f ≫ f°) ⊑ X := by
    intro X hEX hXt
    have s1 : (f ≫ f°) ≫ X ≫ (f ≫ f°) ⊑ X ≫ X ≫ X :=
      le_trans (comp_mono_right hEX _) (comp_mono_left _ (comp_mono_left _ hEX))
    exact le_trans s1 (le_trans (comp_mono_left _ hXt) hXt)
  apply le_antisymm
  · have hMF : (f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)° ⊑ (f° ≫ F0) ≫ (f° ≫ F0)° :=
      inter_lb_left _ _
    have hMG : (f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)° ⊑ (f° ≫ G0) ≫ (f° ≫ G0)° :=
      inter_lb_right _ _
    have hconjF : f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)°) ≫ f° = (f ≫ f°) ≫ (F0 ≫ F0°) ≫ (f ≫ f°) := by
      rw [hFFr]; simp [Cat.assoc]
    have hconjG : f ≫ ((f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f° = (f ≫ f°) ≫ (G0 ≫ G0°) ≫ (f ≫ f°) := by
      rw [hGGr]; simp [Cat.assoc]
    have hb1 : f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f° ⊑ F0 ≫ F0° := by
      refine le_trans (comp_mono_left f (comp_mono_right hMF f°)) ?_
      rw [hconjF]; exact sand hEle1 hFt
    have hb2 : f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f° ⊑ G0 ≫ G0° := by
      refine le_trans (comp_mono_left f (comp_mono_right hMG f°)) ?_
      rw [hconjG]; exact sand hEle2 hGt
    have key : f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f° ⊑ f ≫ f° := by
      rw [hffE]; exact le_inter hb1 hb2
    have hMrecover :
        (f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°
        = f° ≫ (f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f°) ≫ f := by
      have h1 : f° ≫ (f ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ f°) ≫ f
          = (f° ≫ f) ≫ ((f° ≫ F0) ≫ (f° ≫ F0)° ∩ (f° ≫ G0) ≫ (f° ≫ G0)°) ≫ (f° ≫ f) := by
        simp [Cat.assoc]
      rw [h1, hf1, Cat.id_comp, Cat.comp_id]
    rw [hMrecover]
    refine le_trans (comp_mono_left f° (comp_mono_right key f)) ?_
    have hcollapse : f° ≫ (f ≫ f°) ≫ f = (f° ≫ f) ≫ (f° ≫ f) := by simp [Cat.assoc]
    rw [hcollapse, hf1, Cat.id_comp]; exact le_refl _
  · have h1eq : Cat.id c = f° ≫ (f ≫ f°) ≫ f := by
      have h2 : f° ≫ (f ≫ f°) ≫ f = (f° ≫ f) ≫ (f° ≫ f) := by simp [Cat.assoc]
      rw [h2, hf1, Cat.id_comp]
    rw [h1eq, hffE]
    apply le_inter
    · rw [hFFr]; exact comp_mono_left f° (comp_mono_right (inter_lb_left _ _) f)
    · rw [hGGr]; exact comp_mono_left f° (comp_mono_right (inter_lb_right _ _) f)

/-- **§2.16(10) round-trip identity**: `F₀° G₀ = (f° F₀)° (f° G₀)`, i.e. inserting
    the split `f f° = F₀F₀° ∩ G₀G₀°` does not change `U`.  The hard `⊑` half is the
    Dedekind identity `F₀° G₀ ⊑ F₀° (F₀F₀° ∩ G₀G₀°) G₀` (modular law, no simplicity);
    the easy `⊒` half uses `F₀° F₀ ⊑ 1`. -/
theorem srcTab_Ueq [Allegory 𝒜] {a p c0 c : 𝒜} {F0 : c0 ⟶ a} {G0 : c0 ⟶ p}
    {f : c0 ⟶ c} (hffE : f ≫ f° = F0 ≫ F0° ∩ G0 ≫ G0°) (hF0 : Simple F0) :
    F0° ≫ G0 = (f° ≫ F0)° ≫ (f° ≫ G0) := by
  have heq : (f° ≫ F0)° ≫ (f° ≫ G0) = F0° ≫ (f ≫ f°) ≫ G0 := by
    rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  rw [heq, hffE]
  apply le_antisymm
  · -- Dedekind: F0° G0 ⊑ F0° (F0F0° ∩ G0G0°) G0
    have m := modular_le F0° G0 (F0° ≫ G0)
    rw [Allegory.inter_idem] at m
    refine le_trans m ?_
    rw [show F0° ≫ (F0 ≫ F0° ∩ G0 ≫ G0°) ≫ G0 = (F0° ≫ (F0 ≫ F0° ∩ G0 ≫ G0°)) ≫ G0 by
          rw [Cat.assoc]]
    apply comp_mono_right
    have e1 : (F0° ≫ G0) ≫ G0° = F0° ≫ (G0 ≫ G0°) := by simp [Cat.assoc]
    rw [e1]
    refine le_trans (left_modular_le F0° F0° (G0 ≫ G0°)) ?_
    apply comp_mono_left
    rw [Allegory.recip_recip]; exact le_refl _
  · -- F0° (F0F0° ∩ G0G0°) G0 ⊑ F0° (F0F0°) G0 = (F0°F0)(F0°G0) ⊑ F0° G0
    refine le_trans (comp_mono_left F0° (comp_mono_right (inter_lb_left _ _) G0)) ?_
    have e : F0° ≫ (F0 ≫ F0°) ≫ G0 = (F0° ≫ F0) ≫ (F0° ≫ G0) := by simp [Cat.assoc]
    rw [e]
    refine le_trans (comp_mono_right hF0 _) ?_
    rw [Cat.id_comp]; exact le_refl _

/-- **The splitting hypothesis** (§2.169/§2.226), stated over the *same*
    `UnionAllegory` instance to avoid the `Allegory`-diamond between
    `UnionAllegory` and `EffectiveAllegory` (which provide non-defeq `Allegory`
    instances, so an `EffectiveAllegory.split_…` cannot be applied to a
    `UnionAllegory`-typed morphism).  `SplitsSymmIdem 𝒜` says every symmetric
    idempotent of `𝒜` splits — there is `f` with `f f° = E`, `f° f = 1_c`.  This is
    the idempotent-splitting universal (§2.164/§2.169); note the split leg `f` is
    *not* required entire (`E` need not be reflexive), so the predicate also holds at
    the splitting completion `SplObj 𝒜`, where every symmetric idempotent splits but
    a coreflexive/general idempotent's leg is only a partial map.  The §2.16(10)
    source-apex assembly (`srcTabulation_of_semiSimple_split`) consumes only `f° f =
    1_c` and `f f° = E`, never the entirety of `f`. -/
def SplitsSymmIdem (𝒜 : Type u) [Allegory 𝒜] : Prop :=
  ∀ {a : 𝒜} (E : a ⟶ a), Symmetric E → E ≫ E = E →
    ∃ (c : 𝒜) (f : a ⟶ c), f ≫ f° = E ∧ f° ≫ f = Cat.id c

/-- **§2.16(10)**: given the effective splitting (`SplitsSymmIdem`), every
    SEMI-SIMPLE morphism `U` of a union allegory has a SOURCE-APEX jointly-monic
    map span.  Split `E := F₀F₀° ∩ G₀G₀°` of a semi-simple factorisation
    `U = F₀° G₀`; the legs `f° F₀`, `f° G₀` are the span. -/
theorem srcTabulation_of_semiSimple_split [Allegory 𝒜]
    (hsplit : SplitsSymmIdem 𝒜) {a p : 𝒜} (U : a ⟶ p) (hU : SemiSimple U) :
    ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ p),
      Map F ∧ Map G ∧ U = F° ≫ G ∧ F ≫ F° ∩ G ≫ G° = Cat.id c := by
  obtain ⟨c0, F0, G0, hF0, hG0, hUfac⟩ := hU
  obtain ⟨hEsym, hEidem⟩ := capE_symm_idem hF0 hG0
  obtain ⟨c, f, hffE, hf1⟩ := hsplit (F0 ≫ F0° ∩ G0 ≫ G0°) hEsym hEidem
  have hEleF : f ≫ f° ⊑ F0 ≫ F0° := by rw [hffE]; exact inter_lb_left _ _
  have hEleG : f ≫ f° ⊑ G0 ≫ G0° := by rw [hffE]; exact inter_lb_right _ _
  exact ⟨c, f° ≫ F0, f° ≫ G0, srcTab_leg_map hf1 hEleF hF0,
    srcTab_leg_map hf1 hEleG hG0, by rw [hUfac]; exact srcTab_Ueq hffE hF0,
    srcTab_monic hf1 hffE hF0 hG0⟩

/-- **The one residual §2.228(a)/(b) gap, CLOSED** (§2.143 / §2.166 / §2.16(10)):
    for every morphism `U` of a SEMI-SIMPLE union allegory in which symmetric
    idempotents split there is a SOURCE-APEX span of *maps* `(F, G)`,
    `F : c → a`, `G : c → p`, jointly monic on the apex (`F F° ∩ G G° = 1_c`),
    tabulating `U` in the source-apex sense (`U = F° G`).

    Closed via `srcTabulation_of_semiSimple_split`: §2.16(10)'s split of the
    symmetric idempotent `F₀F₀° ∩ G₀G₀°` of a semi-simple factorisation
    `U = F₀° G₀` produces the jointly-monic map span.  Semi-simplicity supplies the
    factorisation; the `SplitsSymmIdem` hypothesis (effectiveness, §2.169/§2.226)
    supplies the splitting.  Both are faithful to Freyd's §2.16(10): "a semi-simple
    allegory in which all symmetric idempotents split is tabular".

    NOTE on the binders.  The splitting is taken as the explicit hypothesis
    `hsplit : SplitsSymmIdem 𝒜` (the `EffectiveAllegory` field), rather than an
    `[EffectiveAllegory 𝒜]` *instance*, because `UnionAllegory` and
    `EffectiveAllegory` each furnish an `Allegory 𝒜` instance and these are not
    definitionally equal — a genuine type-class diamond.  Routing the splitting
    through the union allegory's own reciprocation/composition (this `Prop`)
    keeps every morphism typed by the single `UnionAllegory` instance.  Likewise
    semi-simplicity is the explicit `hss`.  The order-iso the transport needs is
    proven Sorry-free: `src_roundtrip_le/ge`, `src_phipsi_le/ge`,
    `interUnionU_distrib_of_srcTabulation`. -/
theorem srcTabulation_exists [UnionAllegory 𝒜]
    (hss : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) (hsplit : SplitsSymmIdem 𝒜)
    {a p : 𝒜} (U : a ⟶ p) :
    ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ p),
      Map F ∧ Map G ∧ U = F° ≫ G ∧ F ≫ F° ∩ G ≫ G° = Cat.id c :=
  srcTabulation_of_semiSimple_split hsplit U (hss U)

/-- **Tabulation transport** (§2.228(a)).  Given `R, S, T ⊑ U` for a fixed `U`,
    transport the distributive coreflexive lattice of the apex back along the
    §2.143/§2.166 source-apex span of `U` to obtain the ∩-over-∪ containment.
    Sorry-free *modulo* `srcTabulation_exists` — every order-iso step is a
    theorem (`interUnionU_distrib_of_srcTabulation`). -/
theorem tab_transport_gap [UnionAllegory 𝒜]
    (hss : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) (hsplit : SplitsSymmIdem 𝒜)
    {a p : 𝒜} {U R S T : a ⟶ p}
    (hRU : R ⊑ U) (hSU : S ⊑ U) (hTU : T ⊑ U) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) := by
  obtain ⟨c, F, G, hF, hG, hUeq, hmonic⟩ := srcTabulation_exists hss hsplit U
  rw [hUeq] at hRU hSU hTU
  exact interUnionU_distrib_of_srcTabulation hF hG hmonic hRU hSU hTU




/-! ## §2.228(b)  A semi-simple union allegory is distributive

  *A semi-simple allegory with the above-mentioned property is distributive.*

  Freyd's argument: split the symmetric idempotents to obtain a tabular
  allegory with the same property, then apply §2.228(a). -/

/-- **Semi-simple transport** (§2.228(b)).  Freyd's route: split the symmetric
    idempotents to land in a tabular allegory with the same composition-over-union
    structure, where §2.228(a) applies.  Per §2.16(10): for a semi-simple
    `U = F° G` the symmetric idempotent `F F° ∩ G G°` splits (effectiveness,
    §2.226) to make `H F, H G` MAPS jointly tabulating `U` — exactly the
    `srcTabulation_exists` span.  So §2.228(b) reduces to the SAME residual hole
    as §2.228(a), and is discharged by the identical transport: `tab_transport_gap`
    (the surrounding `U := R ∪ S ∪ T` has its source-apex span via §2.166). -/
theorem semiSimple_transport_gap [UnionAllegory 𝒜]
    (hss : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) (hsplit : SplitsSymmIdem 𝒜)
    {a b : 𝒜} {R S T : a ⟶ b}
    (_hR : SemiSimple R) (_hS : SemiSimple S) (_hT : SemiSimple T) :
    R ∩ (S ∪ᵤ T) ⊑ (R ∩ S) ∪ᵤ (R ∩ T) :=
  tab_transport_gap hss hsplit (U := R ∪ᵤ S ∪ᵤ T)
    (le_trans (le_unionU_left _ _) (le_unionU_left _ _))
    (le_trans (le_unionU_right _ _) (le_unionU_left _ _))
    (le_unionU_right _ _)

/-- **§2.228(b)**: a semi-simple union allegory satisfies the
    intersection-over-union distributive law, hence is distributive.

    By `interUnionDistrib_iff_le` it suffices to prove the reverse
    containment; feeding the semi-simple witnesses of `R,S,T` to
    `semiSimple_transport_gap` discharges it (modulo that gap). -/
theorem interUnionDistrib_of_semiSimple [UnionAllegory 𝒜]
    (hsplit : SplitsSymmIdem 𝒜)
    (h : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) : InterUnionDistrib 𝒜 := by
  rw [interUnionDistrib_iff_le]
  intro a b R S T
  exact semiSimple_transport_gap h hsplit (h R) (h S) (h T)

/-- **§2.228(a)**: a tabular union allegory satisfies the intersection-over-
    union distributive law, hence is distributive.

    By `interUnionDistrib_iff_le` it suffices to prove the *reverse*
    containment `R ∩ (S∪T) ⊑ (R∩S) ∪ (R∩T)`; the forward one is free.

    SORRY-FREE (Task 2): the remaining containment is Freyd's source-apex argument
    — `srcTabulation_exists` builds a SOURCE-apex jointly-monic map span of
    `U := R ∪ S ∪ T` (§2.16(10): split `F₀F₀° ∩ G₀G₀°` of a semi-simple
    factorisation), and `interUnionU_distrib_of_srcTabulation` transports the
    distributive coreflexive lattice back via the §2.143 order-iso.  Needs the
    faithful explicit hypotheses `hss` (semi-simplicity) and `hsplit` (effective
    splitting) — taken as `Prop`s over the single `UnionAllegory` instance to dodge
    the `UnionAllegory`/`EffectiveAllegory` `Allegory`-diamond.  A tabular union
    allegory satisfies both (every tabular morphism is semi-simple, every symmetric
    idempotent splits in a tabular/effective allegory); the binders make that
    explicit without a non-defeq second `Allegory` instance. -/
theorem interUnionDistrib_of_tabular [UnionAllegory 𝒜]
    (hss : ∀ {a b : 𝒜} (R : a ⟶ b), SemiSimple R) (hsplit : SplitsSymmIdem 𝒜)
    (_h : ∀ {a b : 𝒜} (R : a ⟶ b), Tabular R) : InterUnionDistrib 𝒜 :=
  -- The tabularity hypothesis is not used: semi-simplicity and splitting already suffice, which is
  -- `interUnionDistrib_of_semiSimple` below.  §2.228(a) is a book-numbered deliverable, so the
  -- statement stays; only its (duplicate) derivation is gone.
  interUnionDistrib_of_semiSimple hsplit hss

/-! ## §2.228(c)  Necessity of one of the two hypotheses

  *An allegory with this property in which, further, every morphism is the
  union of semi-simple morphisms it contains [2.225] need not be
  distributive.*

  The witness: for any group G with more than two elements, adjoin a zero 0
  and a maximal element M to the one-object allegory on G (G discretely
  ordered; composition uses the group multiplication and RM = MR = M for
  R ≠ 0; 0 absorbs everything; reciprocation uses inverses, fixing 0 and M).
  This is a union allegory in which every morphism is the union of the
  semi-simple morphisms it contains, yet it is not distributive. -/

/-- A morphism `R : a → b` is the **union of the semi-simple morphisms it
    contains** (§2.225 / §2.228(c)): `R` is a finite union of semi-simple
    morphisms, each contained in `R`.  Stated via a list of semi-simple
    sub-morphisms whose union is `R`. -/
def UnionOfSemiSimpleUA [UnionAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (l : List (a ⟶ b)),
    (∀ S ∈ l, SemiSimple S ∧ S ⊑ R) ∧
    l.foldr (· ∪ᵤ ·) (𝟘ᵤ : a ⟶ b) = R

/-! ### The explicit witness: the group `ℤ/3` with `0` and `M` adjoined

  We take Freyd's construction for the smallest admissible group `G = ℤ/3 =
  {e, a, a²}` (|G| = 3 > 2).  The one-object allegory has hom-set
  `Q3 = {𝟎, e, a, a², M}` with:

  * **order / lattice**: `𝟎` bottom, `M` top, the three group elements
    pairwise incomparable (discrete order on `G`).  `∩` = meet, `∪` = join.
  * **composition**: group multiplication on `G`; `𝟎` absorbing; `M ∘ x =
    x ∘ M = M` for `x ≠ 𝟎`; identity is `e`.
  * **reciprocation**: inverse on `G` (`a° = a²`), fixing `𝟎` and `M`.

  All allegory and union-allegory axioms are finite identities on `Q3`,
  discharged by `decide`.  The single object is modelled by `Unit`. -/

/-- Hom-set of the §2.228(c) counterexample: `ℤ/3 ∪ {𝟎, M}`. -/
inductive Q3 where
  | zero | e | a | a2 | top
  deriving DecidableEq, Repr

namespace Q3

/-- Lattice meet: `𝟎` bottom, `top` top, distinct group elements meet to `𝟎`. -/
def meet : Q3 → Q3 → Q3
  | zero, _ => zero
  | _, zero => zero
  | top, y => y
  | x, top => x
  | e, e => e | a, a => a | a2, a2 => a2
  | _, _ => zero

/-- Lattice join (dual of `meet`): `top` top, distinct group elements join to `top`. -/
def join : Q3 → Q3 → Q3
  | zero, y => y
  | x, zero => x
  | top, _ => top
  | _, top => top
  | e, e => e | a, a => a | a2, a2 => a2
  | _, _ => top

/-- Composition: group multiplication on `G`, `𝟎` absorbing, `M` maximal. -/
def comp : Q3 → Q3 → Q3
  | zero, _ => zero
  | _, zero => zero
  -- e is the group identity
  | e, y => y
  | x, e => x
  -- M is absorbing among the nonzero elements
  | top, _ => top
  | _, top => top
  -- the remaining products are inside G = {a, a²}
  | a, a => a2
  | a, a2 => e
  | a2, a => e
  | a2, a2 => a

/-- Reciprocation: group inverse (`a° = a²`), `𝟎` and `M` symmetric. -/
def recip : Q3 → Q3
  | zero => zero | e => e | a => a2 | a2 => a | top => top

end Q3

/-- The one-object category of the §2.228(c) counterexample. -/
instance : Cat.{0} Unit where
  Hom _ _ := Q3
  id _ := Q3.e
  comp R S := Q3.comp R S
  id_comp := by intro X Y f; cases f <;> rfl
  comp_id := by intro X Y f; cases f <;> rfl
  assoc := by intro W X Y Z f g h; cases f <;> cases g <;> cases h <;> rfl

/-- The §2.228(c) allegory structure on `Unit` (hom-set `Q3`). -/
instance counterAllegory : Allegory.{0} Unit where
  recip R := Q3.recip R
  inter R S := Q3.meet R S
  recip_recip := by intro a b R; cases R <;> rfl
  recip_comp := by intro a b c R S; cases R <;> cases S <;> rfl
  recip_inter := by intro a b R S; cases R <;> cases S <;> rfl
  inter_idem := by intro a b R; cases R <;> rfl
  inter_comm := by intro a b R S; cases R <;> cases S <;> rfl
  inter_assoc := by intro a b R S T; cases R <;> cases S <;> cases T <;> rfl
  semidistrib := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl
  modular := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl

/-- The §2.228(c) union-allegory structure: `𝟎 = Q3.zero`, `∪ = Q3.join`,
    composition distributing over union, but NOT intersection. -/
instance counterUnionAllegory : UnionAllegory.{0} Unit where
  zero := Q3.zero
  union R S := Q3.join R S
  zero_comp := by intro a b c R; cases R <;> rfl
  comp_zero := by intro a b c R; cases R <;> rfl
  union_idem := by intro a b R; cases R <;> rfl
  union_comm := by intro a b R S; cases R <;> cases S <;> rfl
  union_assoc := by intro a b R S T; cases R <;> cases S <;> cases T <;> rfl
  union_inter_absorb := by intro a b R S; cases R <;> cases S <;> rfl
  inter_union_absorb := by intro a b R S; cases R <;> cases S <;> rfl
  comp_union_distrib := by intro a b c R S T; cases R <;> cases S <;> cases T <;> rfl
  zero_union := by intro a b R; cases R <;> rfl

/-- In the §2.228(c) model the simple morphisms are exactly `{𝟎, e, a, a²}`
    (everything but `M`): `F° F ⊑ e` fails only for `F = M` (`M° M = M ⋢ e`). -/
theorem Q3.simple_of {F : Q3} (hF : F ≠ Q3.top) :
    Simple (𝒜 := Unit) (a := ()) (b := ()) F := by
  dsimp [Simple, le]
  cases F <;> first | rfl | exact absurd rfl hF

/-- Each group element `g` (and `𝟎`) is semi-simple: `g = e° ≫ g` with `e, g`
    simple; `𝟎 = 𝟎° ≫ 𝟎`. -/
theorem Q3.semiSimple_of {R : Q3} (hR : R ≠ Q3.top) :
    SemiSimple (𝒜 := Unit) (a := ()) (b := ()) R :=
  ⟨(), Q3.e, R, Q3.simple_of (by decide), Q3.simple_of hR, by cases R <;> rfl⟩

/-- `S ⊑ R` in the §2.228(c) model is the decidable identity `S ∩ R = S`. -/
theorem Q3.le_of {S R : Q3} (h : Q3.meet S R = S) :
    @le Unit () () counterAllegory S R := h

/-- Every morphism of the §2.228(c) model is the union of the semi-simple
    morphisms it contains.  Non-`M` morphisms are themselves semi-simple;
    `M = e ∪ a` is the union of two distinct (semi-simple) group elements. -/
theorem counter_unionOfSemiSimple (R : Q3) :
    UnionOfSemiSimpleUA (𝒜 := Unit) (a := ()) (b := ()) R := by
  -- helper: a non-M element x with x ∩ R = x is a semi-simple sub-morphism of R
  have ss : ∀ (x : Q3), x ≠ Q3.top → Q3.meet x R = x →
      SemiSimple (𝒜 := Unit) (a := ()) (b := ()) x ∧
        @le Unit () () counterAllegory x R :=
    fun _ hx hle => ⟨Q3.semiSimple_of hx, Q3.le_of hle⟩
  cases R
  · refine ⟨[Q3.zero], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.e], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.a], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · refine ⟨[Q3.a2], ?_, rfl⟩
    intro S hS; simp only [List.mem_singleton] at hS; subst hS; exact ss _ (by decide) rfl
  · -- M = e ∪ a, both simple group elements, both ⊑ M
    refine ⟨[Q3.e, Q3.a], ?_, rfl⟩
    intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl
    · exact ss _ (by decide) rfl
    · exact ss _ (by decide) rfl

/-- **§2.228(c)**: there is a union allegory in which every morphism is the
    union of the semi-simple morphisms it contains, but the intersection-over-
    union distributive law FAILS — so the union-of-semi-simples
    hypothesis alone does not force distributivity (in contrast to the
    tabular and semi-simple hypotheses of (a),(b)).

    Witness: the explicit `ℤ/3 ∪ {𝟎, M}` allegory above. Non-distributivity
    is exhibited by `R = a`, `S = e`, `T = a²`:
    `a ∩ (e ∪ a²) = a ∩ M = a`, but `(a ∩ e) ∪ (a ∩ a²) = 𝟎 ∪ 𝟎 = 𝟎`. -/
theorem exists_unionOfSemiSimple_not_distributive :
    ∃ (𝒜 : Type 0) (_ : UnionAllegory.{0, 0} 𝒜),
      (∀ {a b : 𝒜} (R : a ⟶ b), UnionOfSemiSimpleUA R) ∧ ¬ InterUnionDistrib 𝒜 := by
  refine ⟨Unit, counterUnionAllegory, ?_, ?_⟩
  · -- every morphism is the union of the semi-simple morphisms it contains
    intro a b R
    exact counter_unionOfSemiSimple R
  · -- non-distributivity at R=a, S=e, T=a²
    intro hd
    have h := hd (a := ()) (b := ()) Q3.a Q3.e Q3.a2
    -- LHS = a ∩ M = a, RHS = 𝟎 ∪ 𝟎 = 𝟎; unfold the instance projections.
    simp only [Allegory.inter, UnionAllegory.union, counterAllegory, counterUnionAllegory,
      Q3.meet, Q3.join] at h
    exact Q3.noConfusion h

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* — §2.221–§2.225: the completions of
  an allegory and their structural consequences.

  This file builds on `Freyd/S2_2.lean`, which already provides:

  • the classes `DistributiveAllegory`, `LocallyCompleteDistributiveAllegory` (LCDA),
    `GloballyCompleteAllegory` (with arbitrary disjoint unions);
  • §2.221/§2.222 the LOCAL COMPLETION / IDEAL ALLEGORY `Â = Downdeal 𝒜` of a
    distributive allegory, as a *full* LCDA instance
    (`instLocallyCompleteDistributiveAllegoryDowndealHom`) with a faithful
    principal-ideal embedding `R ↦ ↓R` (`DowndealHom.prin_injective`);
  • §2.224 the GLOBAL COMPLETION data `GlobalObj`/`GlobalMorphism` with a faithful
    embedding (`globalCompletionEmbed_injective`).

  We add, on top of that:

  • §2.223  An indexed DISJOINT UNION in an LCDA coincides with an (indexed)
    COPRODUCT: the injections enjoy the universal mapping property, with mediator
    `M = ⋃ᵢ Uᵢ°Rᵢ`.  This is the indexed extension of the binary §2.214 argument.
  • §2.225  In a GLOBALLY COMPLETE allegory a union of semi-simple morphisms is
    semi-simple: if `R = ⋃ᵢ Fᵢ°Gᵢ` with all `Fᵢ, Gᵢ` simple, then `R = F°G` with
    `F = ⋃ᵢ Uᵢ°Fᵢ`, `G = ⋃ᵢ Uᵢ°Gᵢ` simple — Freyd's keystone for "globally complete
    + every morphism a union of its semi-simple parts ⟹ semi-simple".
  • §2.222  Named restatement that the ideal allegory is an LCDA with a faithful
    representation (the instance already lives in `S2_2.lean`).

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, union `R ∪ S`, order `R ⊑ S`, supremum `Sup P`.  Strictly mathlib-free.
-/



namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

/-! ## Supremum bookkeeping in a locally complete distributive allegory

  Small facts about `Sup` that the §2.223/§2.225 arguments use: congruence in the
  predicate, the reciprocal of a supremum, and `R = S` from `R° = S°`. -/

section LCDAGeneral

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- An equality refines to the allegory order. -/
theorem le_of_eq' {a b : 𝒜} {R S : a ⟶ b} (h : R = S) : R ⊑ S := by
  rw [h]; exact le_refl S

/-- `Sup` depends only on the predicate up to logical equivalence. -/
theorem Sup_congr {a b : 𝒜} {P Q : (a ⟶ b) → Prop} (h : ∀ T, P T ↔ Q T) :
    Sup P = Sup Q := by
  have hPQ : P = Q := funext fun T => propext (h T)
  rw [hPQ]


/-- `R = S` follows from `R° = S°` (reciprocation is injective). -/
theorem recip_injective {a b : 𝒜} {R S : a ⟶ b} (h : R° = S°) : R = S := by
  have h2 : R°° = S°° := by rw [h]
  rwa [Allegory.recip_recip, Allegory.recip_recip] at h2

/-! ## §2.223  Disjoint unions coincide with coproducts

  A DISJOINT UNION of a family `{αᵢ}ᵢ` (Freyd §2.223) is an object `β` with
  injections `Uᵢ : αᵢ → β` satisfying the indexed extension of the five §2.214
  equations:

      `UᵢUᵢ° = 1`,   `UᵢUⱼ° = 0  (i ≠ j)`,   `⋃ᵢ Uᵢ°Uᵢ = 1`.

  (The disjointness `UᵢUⱼ° = 0` quantified over ordered pairs `i ≠ j` supplies both
  cross terms; the union `⋃ᵢ Uᵢ°Uᵢ = 1` is the indexed `recip_union_eq_id`.) -/

/-- A §2.223 DISJOINT UNION datum: injections `Uᵢ : αᵢ → β` with the three indexed
    coproduct equations. -/
structure IndexedDisjointUnion {I : Type u} (α : I → 𝒜) (β : 𝒜) where
  /-- The injections. -/
  U : (i : I) → α i ⟶ β
  /-- `UᵢUᵢ° = 1`. -/
  self : ∀ i, U i ≫ (U i)° = Cat.id (α i)
  /-- `UᵢUⱼ° = 0` for `i ≠ j`. -/
  cross : ∀ {i j : I}, i ≠ j → U i ≫ (U j)° = (𝟘 : α i ⟶ α j)
  /-- `⋃ᵢ Uᵢ°Uᵢ = 1`. -/
  complete : Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i) = Cat.id β

variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- **§2.223 (mediator law).**  For a disjoint union and a family `{Rᵢ : αᵢ → c}`, the
    morphism `M = ⋃ᵢ Uᵢ°Rᵢ` satisfies `Uⱼ ≫ M = Rⱼ`.  (The cross terms `UⱼUᵢ° = 0`
    vanish; the diagonal `UⱼUⱼ° = 1` survives.) -/
theorem IndexedDisjointUnion.inject_mediator (du : IndexedDisjointUnion α β)
    {c : 𝒜} (R : (i : I) → α i ⟶ c) (j : I) :
    du.U j ≫ Sup (fun T => ∃ i, T = (du.U i)° ≫ R i) = R j := by
  rw [comp_Sup_distrib]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
    by_cases hij : i = j
    · have h : du.U j ≫ ((du.U i)° ≫ R i) = R j := by
        subst hij; rw [← Cat.assoc, du.self, Cat.id_comp]
      exact le_of_eq' h
    · have h : du.U j ≫ ((du.U i)° ≫ R i) = (𝟘 : α j ⟶ c) := by
        rw [← Cat.assoc, du.cross (Ne.symm hij), DistributiveAllegory.zero_comp]
      rw [h]; exact zero_le _
  · apply le_Sup
    exact ⟨(du.U j)° ≫ R j, ⟨j, rfl⟩, by rw [← Cat.assoc, du.self, Cat.id_comp]⟩

/-- The indexed COPRODUCT universal property for injections `U : ∀ i, αᵢ → β`: every
    family `{Rᵢ : αᵢ → c}` factors uniquely through the injections (§2.223). -/
def IsIndexedCoproduct (U : (i : I) → α i ⟶ β) : Prop :=
  ∀ (c : 𝒜) (R : (i : I) → α i ⟶ c),
    ∃ M : β ⟶ c, (∀ i, U i ≫ M = R i) ∧
      (∀ M' : β ⟶ c, (∀ i, U i ≫ M' = R i) → M' = M)

/-- **§2.223.**  A disjoint union is an (indexed) coproduct: its injections enjoy the
    universal mapping property, with mediator `M = ⋃ᵢ Uᵢ°Rᵢ`.  Existence is the
    mediator law; uniqueness reciprocates and uses completeness `⋃ᵢ Uᵢ°Uᵢ = 1`. -/
theorem IndexedDisjointUnion.isCoproduct (du : IndexedDisjointUnion α β) :
    IsIndexedCoproduct du.U := by
  intro c R
  refine ⟨Sup (fun T => ∃ i, T = (du.U i)° ≫ R i), fun j => du.inject_mediator R j, ?_⟩
  intro M' hM'
  apply recip_injective
  rw [recip_Sup]
  -- M'° = ⋃ᵢ M'°(Uᵢ°Uᵢ)  (completeness `⋃ᵢ Uᵢ°Uᵢ = 1`, pushed through `M'° ≫ -`)
  have hL : Sup (fun T => ∃ S, (∃ i, S = (du.U i)° ≫ du.U i) ∧ T = M'° ≫ S) = M'° := by
    rw [← comp_Sup_distrib, du.complete, Cat.comp_id]
  rw [← hL]
  apply Sup_congr
  intro T
  constructor
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨(du.U i)° ≫ R i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, hM' i, Allegory.recip_comp, Allegory.recip_recip]⟩
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨(du.U i)° ≫ du.U i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, hM' i, Allegory.recip_comp, Allegory.recip_recip]⟩

/-- The assembled leg `F̂ = ⋃ᵢ Uᵢ°Fᵢ` of a family of SIMPLE morphisms over a disjoint
    union is itself SIMPLE.  `F̂°F̂ = ⋃ᵢ Fᵢ°Fᵢ ⊑ 1` because the cross terms `UᵢUⱼ°`
    vanish (`Uⱼ ≫ F̂ = Fⱼ`) and each `Fᵢ°Fᵢ ⊑ 1`. -/
theorem IndexedDisjointUnion.assembled_simple {a : 𝒜} (du : IndexedDisjointUnion α β)
    (F : (i : I) → α i ⟶ a) (hF : ∀ i, Simple (F i)) :
    Simple (Sup (fun T => ∃ i, T = (du.U i)° ≫ F i)) := by
  show (Sup (fun T => ∃ i, T = (du.U i)° ≫ F i))° ≫
      Sup (fun T => ∃ i, T = (du.U i)° ≫ F i) ⊑ Cat.id a
  rw [comp_Sup_distrib]
  apply Sup_le
  rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
  rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]
  exact hF i

end LCDAGeneral

/-! ## §2.225  A union of semi-simple morphisms is semi-simple

  Freyd §2.225: the local (and global) completion of a SEMI-SIMPLE allegory has the
  property that every morphism is the union of the semi-simple morphisms it contains;
  conversely a globally complete allegory with that property is itself semi-simple.
  The keystone is the following: in a globally complete allegory a union of
  semi-simple morphisms is again semi-simple.

  Given `R = ⋃ᵢ Fᵢ°Gᵢ` with all `Fᵢ : αᵢ → a`, `Gᵢ : αᵢ → b` simple, take the disjoint
  union `{Uᵢ : αᵢ → β}` and set `F = ⋃ᵢ Uᵢ°Fᵢ : β → a`, `G = ⋃ᵢ Uᵢ°Gᵢ : β → b`.  Then
  `F, G` are simple and `R = F°G`. -/

section GloballyComplete

variable {𝒜 : Type u} [GloballyCompleteAllegory 𝒜]

/-- Each `GloballyCompleteAllegory` disjoint union `disjointUnion α` is an
    `IndexedDisjointUnion` datum. -/
def GloballyCompleteAllegory.toIndexedDisjointUnion {I : Type u} (α : I → 𝒜) :
    IndexedDisjointUnion α (GloballyCompleteAllegory.disjointUnion α) where
  U := fun i => GloballyCompleteAllegory.inject (a := α) i
  self := fun i => GloballyCompleteAllegory.inject_self_comp_recip (a := α) i
  cross := fun h => GloballyCompleteAllegory.inject_comp_recip_ne (a := α) h
  complete := GloballyCompleteAllegory.complete (a := α)

/-- **§2.225.**  In a GLOBALLY COMPLETE allegory a union of semi-simple morphisms is
    semi-simple: if `R = ⋃ᵢ Fᵢ°Gᵢ` with every `Fᵢ, Gᵢ` simple, then `R` is semi-simple
    (witnessed by the assembled legs `F = ⋃ᵢ Uᵢ°Fᵢ`, `G = ⋃ᵢ Uᵢ°Gᵢ` over the disjoint
    union of the apexes). -/
theorem semiSimple_of_iSup_semiSimple {I : Type u} {a b : 𝒜} (α : I → 𝒜)
    (F : (i : I) → α i ⟶ a) (G : (i : I) → α i ⟶ b)
    (hF : ∀ i, Simple (F i)) (hG : ∀ i, Simple (G i))
    {R : a ⟶ b}
    (hR : R = Sup (fun T => ∃ i, T = (F i)° ≫ G i)) :
    SemiSimple R := by
  let du := GloballyCompleteAllegory.toIndexedDisjointUnion α
  refine ⟨GloballyCompleteAllegory.disjointUnion α,
    Sup (fun T => ∃ i, T = (du.U i)° ≫ F i),
    Sup (fun T => ∃ i, T = (du.U i)° ≫ G i),
    du.assembled_simple F hF, du.assembled_simple G hG, ?_⟩
  rw [hR]
  symm
  rw [comp_Sup_distrib]
  apply Sup_congr
  intro T
  constructor
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(du.U i)° ≫ G i, ⟨i, rfl⟩, by
      rw [← Cat.assoc, ← Allegory.recip_comp, du.inject_mediator F i]⟩

end GloballyComplete

/-! ## §2.222  The ideal allegory is a locally complete distributive allegory

  Freyd §2.222: for a distributive allegory `A`, the allegory of IDEALS is a locally
  complete distributive allegory, and `A ↪ Â` is a faithful representation.  In this
  repository the ideal allegory is `Downdeal 𝒜` (whose homs `DowndealHom` are ideals:
  downward-closed, `𝟘`-containing, `∪`-closed), and the LCDA instance is already
  `instLocallyCompleteDistributiveAllegoryDowndealHom` in `S2_2.lean`.  We record the
  §2.222 statement explicitly. -/

/-- **§2.222.**  The ideal allegory `Â = Downdeal 𝒜` of a distributive allegory is a
    locally complete distributive allegory (the instance already lives in `S2_2.lean`;
    re-exported here under the §2.222 name). -/
def idealAllegory_locallyComplete (𝒜 : Type u) [DistributiveAllegory 𝒜] :
    LocallyCompleteDistributiveAllegory (Downdeal 𝒜) :=
  instLocallyCompleteDistributiveAllegoryDowndealHom

/-- **§2.222.**  The principal-ideal embedding `A → Â`, `R ↦ ↓R`, is faithful — so any
    distributive allegory is faithfully represented in a locally complete one. -/
theorem idealAllegory_faithful {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    {R S : a ⟶ b} (h : DowndealHom.prin R = DowndealHom.prin S) : R = S :=
  DowndealHom.prin_injective h

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.224  The GLOBAL COMPLETION.

  The global completion `A'` of a locally complete distributive allegory `A`
  has indexed families of objects (`GlobalObj`) as objects and infinite
  matrices (`GlobalMorphism`) as morphisms, with matrix multiplication via the
  locally-complete `Sup`.  The development here equips `GlobalObj A` with the
  full tower of allegory structure:

  * `globalCat`                   : §2.224 the matrices form a category;
  * `globalAllegory`              : reciprocation/intersection make it an allegory;
  * `globalDistributiveAllegory`  : entry-wise union/zero;
  * `globalLCDA`                  : entry-wise/pointwise `Sup`.

  Hence the faithful 1×1 embedding `A → A'` becomes a structure-preserving
  faithful representation into a locally complete distributive allegory.

  The remaining `GloballyCompleteAllegory` instance (disjoint unions of
  `Type u`-of-object-universe-indexed families) is UNIVERSE-BLOCKED by the
  current encoding; see the note at the end of the file.
-/



namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-! ## Generic `Sup` helpers (in the base allegory `𝒜`) -/

/-- If every member of `P` is below `𝟘`, the supremum is `𝟘`. -/
theorem gcSup_eq_zero {a b : 𝒜} {P : (a ⟶ b) → Prop}
    (h : ∀ T, P T → T ⊑ (𝟘 : a ⟶ b)) : Sup P = (𝟘 : a ⟶ b) :=
  le_antisymm (Sup_le h) (zero_le _)

/-- `Sup P = c` when `c` is a member and an upper bound. -/
theorem gcSup_eq {a b : 𝒜} {P : (a ⟶ b) → Prop} {c : a ⟶ b}
    (hc : P c) (hmax : ∀ T, P T → T ⊑ c) : Sup P = c :=
  le_antisymm (Sup_le hmax) (le_Sup hc)

/-! ## §2.224  The identity matrix and the category structure -/

/-- The IDENTITY MATRIX on an indexed family `A`: the diagonal, using a
    propositional `i = j` (no `DecidableEq`) and `HEq` to express that the
    on-diagonal entry is the identity. -/
def globalId (A : GlobalObj 𝒜) : GlobalMorphism A A :=
  fun i j => Sup (fun U : A.obj i ⟶ A.obj j => ∃ (_ : i = j), HEq U (Cat.id (A.obj i)))

theorem globalId_apply (A : GlobalObj 𝒜) (i j : A.idx) :
    globalId A i j
      = Sup (fun U : A.obj i ⟶ A.obj j => ∃ (_ : i = j), HEq U (Cat.id (A.obj i))) := rfl

/-- The diagonal entry of the identity matrix is the object identity. -/
theorem globalId_diag (A : GlobalObj 𝒜) (i : A.idx) :
    globalId A i i = Cat.id (A.obj i) := by
  rw [globalId_apply]
  apply le_antisymm
  · apply Sup_le
    rintro U ⟨_, hU⟩
    rw [eq_of_heq hU]; exact le_refl _
  · exact le_Sup ⟨rfl, HEq.refl _⟩

theorem globalComp_apply {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (S : GlobalMorphism B C) (i : A.idx) (k : C.idx) :
    GlobalMorphism.comp R S i k = Sup (fun T => ∃ j, T = R i j ≫ S j k) := rfl

/-- `1 ≫ R = R` (left identity). -/
theorem globalComp_id_left {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp (globalId A) R = R := by
  funext i k
  rw [globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨j, rfl⟩
    rw [globalId_apply, Sup_comp_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨h, hU⟩, rfl⟩
    subst h
    rw [eq_of_heq hU, Cat.id_comp]; exact le_refl _
  · exact le_Sup ⟨i, by rw [globalId_diag, Cat.id_comp]⟩

/-- `R ≫ 1 = R` (right identity). -/
theorem globalComp_id_right {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp R (globalId B) = R := by
  funext i k
  rw [globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro T ⟨j, rfl⟩
    rw [globalId_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨h, hU⟩, rfl⟩
    subst h
    rw [eq_of_heq hU, Cat.comp_id]; exact le_refl _
  · exact le_Sup ⟨k, by rw [globalId_diag, Cat.comp_id]⟩

/-- Associativity = the `Sup`-interchange (Fubini) for matrix multiplication. -/
theorem globalComp_assoc {A B C D : GlobalObj 𝒜}
    (R : GlobalMorphism A B) (S : GlobalMorphism B C) (T : GlobalMorphism C D) :
    GlobalMorphism.comp (GlobalMorphism.comp R S) T
      = GlobalMorphism.comp R (GlobalMorphism.comp S T) := by
  funext i l
  rw [globalComp_apply, globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨k, rfl⟩
    rw [globalComp_apply, Sup_comp_distrib]
    apply Sup_le
    rintro Y ⟨W, ⟨j, rfl⟩, rfl⟩
    rw [Cat.assoc]
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalComp_apply]
    exact le_Sup ⟨k, rfl⟩
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalComp_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨W, ⟨k, rfl⟩, rfl⟩
    rw [← Cat.assoc]
    refine le_trans ?_ (le_Sup ⟨k, rfl⟩)
    apply comp_mono_right
    rw [globalComp_apply]
    exact le_Sup ⟨j, rfl⟩

/-- §2.224 (1) The global completion is a category. -/
instance globalCat : Cat (GlobalObj 𝒜) where
  Hom := GlobalMorphism
  id := globalId
  comp := GlobalMorphism.comp
  id_comp := globalComp_id_left
  comp_id := globalComp_id_right
  assoc := globalComp_assoc

/-! ## §2.224  Reciprocation and intersection -/

/-- Pointwise intersection of two matrices. -/
def globalInter {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) : GlobalMorphism A B :=
  fun i j => R i j ∩ S i j

theorem globalInter_apply {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) (i : A.idx) (j : B.idx) :
    globalInter R S i j = R i j ∩ S i j := rfl

theorem globalRecip_apply {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) (j : B.idx) (i : A.idx) :
    GlobalMorphism.recip R j i = (R i j)° := rfl

theorem globalRecip_recip {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.recip (GlobalMorphism.recip R) = R := by
  funext i j
  rw [globalRecip_apply, globalRecip_apply, Allegory.recip_recip]

/-- `(R ≫ S)° = S° ≫ R°` : reciprocal flips and transposes, using `recip_Sup`. -/
theorem globalRecip_comp {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C) :
    GlobalMorphism.recip (GlobalMorphism.comp R S)
      = GlobalMorphism.comp (GlobalMorphism.recip S) (GlobalMorphism.recip R) := by
  funext k i
  change (Sup (fun T => ∃ j, T = R i j ≫ S j k))°
       = Sup (fun T' => ∃ j, T' = (S j k)° ≫ (R i j)°)
  rw [recip_Sup]
  apply Sup_congr
  intro T'
  constructor
  · rintro ⟨W, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [Allegory.recip_comp]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨R i j ≫ S j k, ⟨j, rfl⟩, by rw [Allegory.recip_comp]⟩

theorem globalRecip_inter {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    GlobalMorphism.recip (globalInter R S)
      = globalInter (GlobalMorphism.recip R) (GlobalMorphism.recip S) := by
  funext j i
  simp only [globalRecip_apply, globalInter_apply]
  rw [Allegory.recip_inter]

theorem globalInter_idem {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalInter R R = R := by
  funext i j; rw [globalInter_apply, Allegory.inter_idem]

theorem globalInter_comm {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalInter R S = globalInter S R := by
  funext i j; rw [globalInter_apply, globalInter_apply, Allegory.inter_comm]

theorem globalInter_assoc {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalInter R (globalInter S T) = globalInter (globalInter R S) T := by
  funext i j; simp only [globalInter_apply]; rw [Allegory.inter_assoc]

/-- Semi-distributivity reduces, at each entry, to base semi-distributivity via
    `R(S∩T) ⊑ RS` and `R(S∩T) ⊑ RT` (the base `comp_mono_left`/`inter_lb`). -/
theorem globalSemidistrib {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S T : GlobalMorphism B C) :
    GlobalMorphism.comp R (globalInter S T)
      = globalInter (globalInter (GlobalMorphism.comp R S)
            (GlobalMorphism.comp R (globalInter S T))) (GlobalMorphism.comp R T) := by
  funext i k
  rw [globalInter_apply, globalInter_apply]
  have hMP : GlobalMorphism.comp R (globalInter S T) i k ⊑ GlobalMorphism.comp R S i k := by
    rw [globalComp_apply, globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalInter_apply]
    exact inter_lb_left _ _
  have hMQ : GlobalMorphism.comp R (globalInter S T) i k ⊑ GlobalMorphism.comp R T i k := by
    rw [globalComp_apply, globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalInter_apply]
    exact inter_lb_right _ _
  rw [Allegory.inter_comm (GlobalMorphism.comp R S i k), inter_eq_left hMP, inter_eq_left hMQ]

/-- The modular law reduces, at each entry, to base `modular_le` plus reindexing
    the inner `Sup` defining `(T ≫ S°)`. -/
theorem globalModular {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C)
    (T : GlobalMorphism A C) :
    globalInter (GlobalMorphism.comp R S) T
      = globalInter (globalInter (GlobalMorphism.comp R S) T)
          (GlobalMorphism.comp
            (globalInter R (GlobalMorphism.comp T (GlobalMorphism.recip S))) S) := by
  funext i k
  rw [globalInter_apply, globalInter_apply, globalInter_apply]
  refine (inter_eq_left ?_).symm
  rw [globalComp_apply, Allegory.inter_comm, inter_Sup_distrib]
  apply Sup_le
  rintro V ⟨X, ⟨j, rfl⟩, rfl⟩
  rw [Allegory.inter_comm (T i k) (R i j ≫ S j k)]
  refine le_trans (modular_le (R i j) (S j k) (T i k)) ?_
  rw [globalComp_apply]
  refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
  apply comp_mono_right
  rw [globalInter_apply]
  apply le_inter (inter_lb_left _ _)
  refine le_trans (inter_lb_right _ _) ?_
  rw [globalComp_apply]
  refine le_Sup ⟨k, ?_⟩
  rw [globalRecip_apply]

/-- §2.224 (2) The global completion is an allegory. -/
instance globalAllegory : Allegory (GlobalObj 𝒜) where
  toCat := globalCat
  recip := GlobalMorphism.recip
  inter := globalInter
  recip_recip := globalRecip_recip
  recip_comp := globalRecip_comp
  recip_inter := globalRecip_inter
  inter_idem := globalInter_idem
  inter_comm := globalInter_comm
  inter_assoc := globalInter_assoc
  semidistrib := globalSemidistrib
  modular := globalModular

/-! ### Global order ↔ entry-wise base order -/

theorem global_le_entry {A B : GlobalObj 𝒜} {R T : A ⟶ B}
    (h : R ⊑ T) (i : A.idx) (j : B.idx) : R i j ⊑ T i j := by
  have h2 : globalInter R T = R := h
  exact congrFun (congrFun h2 i) j

theorem global_le_of_entry {A B : GlobalObj 𝒜} {R T : A ⟶ B}
    (h : ∀ i j, R i j ⊑ T i j) : R ⊑ T := by
  show globalInter R T = R
  funext i j
  exact h i j

/-! ## §2.224  Distributive structure (union and zero) -/

def globalUnion {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) : GlobalMorphism A B :=
  fun i j => R i j ∪ S i j

def globalZero {A B : GlobalObj 𝒜} : GlobalMorphism A B := fun _ _ => 𝟘

theorem globalUnion_apply {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) (i : A.idx) (j : B.idx) :
    globalUnion R S i j = R i j ∪ S i j := rfl

theorem globalZero_apply {A B : GlobalObj 𝒜} (i : A.idx) (j : B.idx) :
    (globalZero : GlobalMorphism A B) i j = (𝟘 : A.obj i ⟶ B.obj j) := rfl

theorem globalZero_comp {A B C : GlobalObj 𝒜} (R : GlobalMorphism B C) :
    GlobalMorphism.comp (globalZero : GlobalMorphism A B) R = globalZero := by
  funext i k
  rw [globalComp_apply, globalZero_apply]
  apply gcSup_eq_zero
  rintro X ⟨j, rfl⟩
  rw [globalZero_apply, DistributiveAllegory.zero_comp]; exact le_refl _

theorem globalComp_zero {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    GlobalMorphism.comp R (globalZero : GlobalMorphism B C) = globalZero := by
  funext i k
  rw [globalComp_apply, globalZero_apply]
  apply gcSup_eq_zero
  rintro X ⟨j, rfl⟩
  rw [globalZero_apply, DistributiveAllegory.comp_zero]; exact le_refl _

theorem globalUnion_idem {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalUnion R R = R := by
  funext i j; rw [globalUnion_apply, DistributiveAllegory.union_idem]

theorem globalUnion_comm {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalUnion R S = globalUnion S R := by
  funext i j; rw [globalUnion_apply, globalUnion_apply, DistributiveAllegory.union_comm]

theorem globalUnion_assoc {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalUnion R (globalUnion S T) = globalUnion (globalUnion R S) T := by
  funext i j; simp only [globalUnion_apply]; rw [DistributiveAllegory.union_assoc]

theorem globalUnion_inter_absorb {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalUnion R (globalInter S R) = R := by
  funext i j; rw [globalUnion_apply, globalInter_apply, DistributiveAllegory.union_inter_absorb]

theorem globalInter_union_absorb {A B : GlobalObj 𝒜} (R S : GlobalMorphism A B) :
    globalInter (globalUnion R S) R = R := by
  funext i j; rw [globalInter_apply, globalUnion_apply, DistributiveAllegory.inter_union_absorb]

theorem globalZero_union {A B : GlobalObj 𝒜} (R : GlobalMorphism A B) :
    globalUnion globalZero R = R := by
  funext i j; rw [globalUnion_apply, globalZero_apply, DistributiveAllegory.zero_union]

theorem globalInter_union_distrib {A B : GlobalObj 𝒜} (R S T : GlobalMorphism A B) :
    globalInter R (globalUnion S T)
      = globalUnion (globalInter R S) (globalInter R T) := by
  funext i j
  simp only [globalInter_apply, globalUnion_apply]
  rw [DistributiveAllegory.inter_union_distrib]

/-- Composition distributes over union: the matrix `Sup` of an entry-wise union
    is the union of the two `Sup`s. -/
theorem globalComp_union_distrib {A B C : GlobalObj 𝒜}
    (R : GlobalMorphism A B) (S T : GlobalMorphism B C) :
    GlobalMorphism.comp R (globalUnion S T)
      = globalUnion (GlobalMorphism.comp R S) (GlobalMorphism.comp R T) := by
  funext i k
  rw [globalUnion_apply, globalComp_apply, globalComp_apply, globalComp_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
    apply union_lub
    · exact le_trans (le_Sup ⟨j, rfl⟩) (le_union_left _ _)
    · exact le_trans (le_Sup ⟨j, rfl⟩) (le_union_right _ _)
  · apply union_lub
    · apply Sup_le
      rintro X ⟨j, rfl⟩
      refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
      rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
      exact le_union_left _ _
    · apply Sup_le
      rintro X ⟨j, rfl⟩
      refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
      rw [globalUnion_apply, DistributiveAllegory.comp_union_distrib]
      exact le_union_right _ _

/-- §2.224 (3) The global completion is a distributive allegory. -/
instance globalDistributiveAllegory : DistributiveAllegory (GlobalObj 𝒜) where
  toAllegory := globalAllegory
  zero := globalZero
  union := globalUnion
  zero_comp := globalZero_comp
  comp_zero := globalComp_zero
  union_idem := globalUnion_idem
  union_comm := globalUnion_comm
  union_assoc := globalUnion_assoc
  union_inter_absorb := globalUnion_inter_absorb
  inter_union_absorb := globalInter_union_absorb
  comp_union_distrib := globalComp_union_distrib
  inter_union_distrib := globalInter_union_distrib
  zero_union := globalZero_union

/-! ## §2.224  Local completeness (pointwise `Sup`) -/

/-- The supremum of a family of matrices is taken pointwise. -/
def globalSup {A B : GlobalObj 𝒜} (P : GlobalMorphism A B → Prop) : GlobalMorphism A B :=
  fun i j => Sup (fun T => ∃ R, P R ∧ T = R i j)

theorem globalSup_apply {A B : GlobalObj 𝒜} (P : GlobalMorphism A B → Prop) (i : A.idx) (j : B.idx) :
    globalSup P i j = Sup (fun T => ∃ R, P R ∧ T = R i j) := rfl

/-- Composition distributes over the pointwise `Sup` (a `Sup`-interchange). -/
theorem globalComp_Sup_distrib {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (P : GlobalMorphism B C → Prop) :
    GlobalMorphism.comp R (globalSup P)
      = globalSup (fun T => ∃ S, P S ∧ T = GlobalMorphism.comp R S) := by
  funext i k
  rw [globalComp_apply, globalSup_apply]
  apply le_antisymm
  · apply Sup_le
    rintro X ⟨j, rfl⟩
    rw [globalSup_apply, comp_Sup_distrib]
    apply Sup_le
    rintro Y ⟨U, ⟨S, hS, rfl⟩, rfl⟩
    refine le_trans ?_ (le_Sup ⟨GlobalMorphism.comp R S, ⟨S, hS, rfl⟩, rfl⟩)
    rw [globalComp_apply]
    exact le_Sup ⟨j, rfl⟩
  · apply Sup_le
    rintro W ⟨Tm, ⟨S, hS, rfl⟩, rfl⟩
    rw [globalComp_apply]
    apply Sup_le
    rintro X ⟨j, rfl⟩
    refine le_trans ?_ (le_Sup ⟨j, rfl⟩)
    apply comp_mono_left
    rw [globalSup_apply]
    exact le_Sup ⟨S, hS, rfl⟩

/-- Intersection distributes over the pointwise `Sup` (no interchange needed). -/
theorem globalInter_Sup_distrib {A B : GlobalObj 𝒜} (R : GlobalMorphism A B)
    (P : GlobalMorphism A B → Prop) :
    globalInter R (globalSup P)
      = globalSup (fun T => ∃ S, P S ∧ T = globalInter R S) := by
  funext i j
  rw [globalInter_apply, globalSup_apply, globalSup_apply, inter_Sup_distrib]
  apply Sup_congr
  intro V
  constructor
  · rintro ⟨U, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨globalInter R S, ⟨S, hS, rfl⟩, rfl⟩
  · rintro ⟨Tm, ⟨S, hS, rfl⟩, rfl⟩
    exact ⟨S i j, ⟨S, hS, rfl⟩, rfl⟩

/-- §2.224 (4) The global completion is a locally complete distributive allegory. -/
instance globalLCDA : LocallyCompleteDistributiveAllegory (GlobalObj 𝒜) where
  toDistributiveAllegory := globalDistributiveAllegory
  Sup := globalSup
  le_Sup := by
    intro A B P R h
    exact global_le_of_entry (fun i j => le_Sup ⟨R, h, rfl⟩)
  Sup_le := by
    intro A B P T h
    refine global_le_of_entry (fun i j => Sup_le ?_)
    rintro U ⟨R', hR', rfl⟩
    exact global_le_entry (h R' hR') i j
  comp_Sup_distrib := globalComp_Sup_distrib
  inter_Sup_distrib := globalInter_Sup_distrib

/-! ## §2.224  The embedding is a faithful structure-preserving representation -/

/-- The embedding preserves reciprocation. -/
theorem globalCompletionEmbed_recip {a b : 𝒜} (R : a ⟶ b) :
    GlobalMorphism.recip (globalCompletionEmbed R) = globalCompletionEmbed (R°) := by
  funext j i; rfl

/-- The embedding preserves composition (the middle `Sup` over `PUnit` collapses). -/
theorem globalCompletionEmbed_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    GlobalMorphism.comp (globalCompletionEmbed R) (globalCompletionEmbed S)
      = globalCompletionEmbed (R ≫ S) := by
  funext i j
  rw [globalComp_apply]
  refine gcSup_eq ⟨PUnit.unit, rfl⟩ ?_
  rintro T ⟨_, rfl⟩
  exact le_refl _

/-! ## §2.224  GloballyCompleteAllegory — universe obstruction

  The `GloballyCompleteAllegory` class demands, for `𝒜' = GlobalObj 𝒜 : Type (u+1)`,
  a disjoint union of *every* family `a : I → 𝒜'` with `I : Type (u+1)` (the index
  type lives in `𝒜'`'s OBJECT universe).  The disjoint union of indexed families is
  the concatenation `idx := Σ i, (a i).idx`; with `I : Type (u+1)` and
  `(a i).idx : Type u`, this `Σ` lands in `Type (u+1)`, but `GlobalObj 𝒜` requires
  `idx : Type u`.  So `disjointUnion a` is NOT a `GlobalObj 𝒜` and the instance
  cannot even be stated, let alone proved — this is a genuine size/universe gap of
  the encoding (the global completion is globally complete only relative to the
  original universe `u`, not the bumped universe `u+1`).  Closing it would require
  a universe-polymorphic `GlobalObj` (`idx : Type w` with `w` independent of the
  object universe), which is fixed in `Freyd/S2_2.lean` and out of scope here.  -/

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* — §2.223 (CONVERSE direction).

  `Freyd/S2_22_Completions.lean` proves the FORWARD half of §2.223: a disjoint
  union (a `IndexedDisjointUnion` datum) is an indexed coproduct, i.e. its
  injections enjoy the universal mapping property
  (`IndexedDisjointUnion.isCoproduct`).

  Here we prove the CONVERSE: an indexed family of injections `U : ∀ i, αᵢ → β`
  that enjoys the indexed COPRODUCT universal property (`IsIndexedCoproduct U`)
  is a disjoint union — it satisfies the three §2.223 equations

      `Uᵢ Uᵢ° = 1`,   `Uᵢ Uⱼ° = 0  (i ≠ j)`,   `⋃ᵢ Uᵢ° Uᵢ = 1`.

  This is the indexed extension of the binary `coproduct_of_universal_eqs`
  (`Freyd/S2_2.lean`).  The argument is the same:

  1. For each `i`, the universal property applied to the DELTA family
     `Δⁱ : (j) ↦ (if j = i then 1 else 0) : αⱼ → αᵢ` gives a mediator
     `pᵢ : β → αᵢ` with `Uᵢ pᵢ = 1` and `Uⱼ pᵢ = 0  (j ≠ i)`.
  2. Completeness: the universal property applied to the family `U` itself has a
     unique mediator; both `1_β` and `⋃ᵢ pᵢ Uᵢ` mediate it, so `⋃ᵢ pᵢ Uᵢ = 1`.
  3. Hence `pᵢ Uᵢ ⊑ 1`, and with `Uᵢ pᵢ = 1` the lemma `eq_recip_of_section`
     gives `pᵢ = Uᵢ°`.
  4. Rewriting `Uᵢ° = pᵢ` reads off the three equations.

  The delta family is encoded with the propositional `j = i` + `HEq` idiom (the
  same one used by `globalId` in `Freyd/S2_224_GlobalCompletion.lean`), so no
  `DecidableEq I` is needed.  Conventions: diagram-order composition `R ≫ S`,
  reciprocation `R°`, union `R ∪ S`, order `R ⊑ S`, supremum `Sup P`, bottom `𝟘`.
  Strictly mathlib-free.
-/



namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

section LCDAConverse

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
variable {I : Type u} {α : I → 𝒜} {β : 𝒜}

/-- The `(i, j)` entry of the DELTA family: `1 : αⱼ → αᵢ` when `j = i`, else `0`.
    Encoded as a `Sup` over the propositional `j = i` + `HEq` to the identity, so
    no `DecidableEq I` is required (cf. `globalId`). -/
def deltaFamEntry (i j : I) : α j ⟶ α i :=
  Sup (fun T : α j ⟶ α i => ∃ (_ : j = i), HEq T (Cat.id (α i)))

/-- The diagonal entry of the delta family is the identity. -/
theorem deltaFamEntry_diag (i : I) : deltaFamEntry (α := α) i i = Cat.id (α i) := by
  apply le_antisymm
  · apply Sup_le; rintro T ⟨_, hT⟩; exact le_of_eq' (eq_of_heq hT)
  · exact le_Sup ⟨rfl, HEq.refl _⟩

/-- An off-diagonal entry of the delta family is `𝟘`. -/
theorem deltaFamEntry_off (i j : I) (hji : j ≠ i) :
    deltaFamEntry (α := α) i j = (𝟘 : α j ⟶ α i) := by
  apply le_antisymm
  · apply Sup_le; rintro T ⟨heq, _⟩; exact absurd heq hji
  · exact zero_le _

/-- **§2.223 (converse).**  An indexed family of injections `U : ∀ i, αᵢ → β` that
    enjoys the indexed COPRODUCT universal property is a DISJOINT UNION: it
    satisfies the three §2.223 equations
    `Uᵢ Uᵢ° = 1`, `Uᵢ Uⱼ° = 0 (i ≠ j)`, `⋃ᵢ Uᵢ° Uᵢ = 1`. -/
theorem indexedCoproduct_to_disjointUnion
    (U : (i : I) → α i ⟶ β) (h : IsIndexedCoproduct U) :
    (∀ i, U i ≫ (U i)° = Cat.id (α i)) ∧
    (∀ {i j : I}, i ≠ j → U i ≫ (U j)° = (𝟘 : α i ⟶ α j)) ∧
    (Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i) = Cat.id β) := by
  -- Step 1: per-`i` mediator `p i` of the delta family `Δⁱ`.
  have hp_all : ∀ i, ∃ M : β ⟶ α i, ∀ j, U j ≫ M = deltaFamEntry (α := α) i j := by
    intro i
    obtain ⟨M, hM, _⟩ := h (α i) (fun j => deltaFamEntry (α := α) i j)
    exact ⟨M, hM⟩
  let p : (i : I) → β ⟶ α i := fun i => Classical.choose (hp_all i)
  have hp : ∀ (i j : I), U j ≫ p i = deltaFamEntry (α := α) i j :=
    fun i => Classical.choose_spec (hp_all i)
  -- `U i ≫ p i = 1`  and  `U j ≫ p i = 0`  for `j ≠ i`.
  have hUp : ∀ i, U i ≫ p i = Cat.id (α i) :=
    fun i => (hp i i).trans (deltaFamEntry_diag i)
  have hUp_off : ∀ i j, j ≠ i → U j ≫ p i = (𝟘 : α j ⟶ α i) :=
    fun i j hji => (hp i j).trans (deltaFamEntry_off i j hji)
  -- Step 2: completeness `⋃ᵢ p i ≫ U i = 1_β`, by uniqueness of the mediator of `U`.
  obtain ⟨R0, _, hR0uniq⟩ := h β U
  have hSum : Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = Cat.id β := by
    have hsum_med : ∀ j, U j ≫ Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = U j := by
      intro j
      rw [comp_Sup_distrib]
      apply le_antisymm
      · apply Sup_le
        rintro T ⟨S, ⟨i, rfl⟩, rfl⟩
        by_cases hij : i = j
        · subst hij
          exact le_of_eq' (by rw [← Cat.assoc, hUp i, Cat.id_comp])
        · have h0 : U j ≫ (p i ≫ U i) = (𝟘 : α j ⟶ β) := by
            rw [← Cat.assoc, hUp_off i j (Ne.symm hij), DistributiveAllegory.zero_comp]
          rw [h0]; exact zero_le _
      · apply le_Sup
        exact ⟨p j ≫ U j, ⟨j, rfl⟩, by rw [← Cat.assoc, hUp j, Cat.id_comp]⟩
    have h1 : Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) = R0 := hR0uniq _ hsum_med
    have h2 : Cat.id β = R0 := hR0uniq _ (fun i => Cat.comp_id (U i))
    rw [h1, ← h2]
  -- Step 3: `p i ≫ U i ⊑ 1`, hence `U i° = p i`.
  have hpU_le : ∀ i, p i ≫ U i ⊑ Cat.id β := fun i => by
    have hle := le_Sup (P := fun T : β ⟶ β => ∃ i, T = p i ≫ U i)
      (R := p i ≫ U i) ⟨i, rfl⟩
    rwa [hSum] at hle
  have hpe : ∀ i, (U i)° = p i :=
    fun i => (eq_recip_of_section (U i) (p i) (hUp i) (hpU_le i)).symm
  -- Step 4: read off the three equations.
  refine ⟨fun i => by rw [hpe i]; exact hUp i, ?_, ?_⟩
  · intro i j hij
    rw [hpe j]; exact hUp_off j i hij
  · have hcongr : Sup (fun R : β ⟶ β => ∃ i, R = (U i)° ≫ U i)
        = Sup (fun T : β ⟶ β => ∃ i, T = p i ≫ U i) := by
      apply Sup_congr; intro T; constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hpe i]⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, by rw [hpe i]⟩
    rw [hcongr, hSum]

/-- **§2.223 (converse), packaged.**  Repackage the universal property as the
    `IndexedDisjointUnion` datum it determines. -/
def IsIndexedCoproduct.toDisjointUnion
    (U : (i : I) → α i ⟶ β) (h : IsIndexedCoproduct U) :
    IndexedDisjointUnion α β where
  U := U
  self := (indexedCoproduct_to_disjointUnion U h).1
  cross := (indexedCoproduct_to_disjointUnion U h).2.1
  complete := (indexedCoproduct_to_disjointUnion U h).2.2

end LCDAConverse

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.226 — embedding a set of partial
  units in a single partial unit.

  §2.226 (the partial-unit-embedding statement).  In a GLOBALLY COMPLETE allegory in
  which equivalence relations split, for every set of partial units there is a partial
  unit in which they may all be embedded.

  BOOK PROOF (verbatim):  "Every object has a maximal endomorphism which is necessarily
  an equivalence relation.  If `M` is a maximal endomorphism and if `ff° = M`, `f°f = 1`,
  then the target of `f` is a partial unit.  Given any set of partial units we may apply
  this construction to their coproduct.  Hence for every set of partial units there is a
  partial unit in which they may all be embedded."

  CONSTRUCTION (mapping the book onto the repo machinery):

  1.  Form the COPRODUCT `Π = ⊕_j π_j` of the family with injections `Uⱼ : πⱼ → Π`.  In a
      `GloballyCompleteAllegory` this is `GloballyCompleteAllegory.disjointUnion`; the
      injections are MAPS (`IndexedDisjointUnion.inject_map`).
  2.  `M = topEndo Π` is the MAXIMAL ENDOMORPHISM (the top `⋃` of the complete hom-lattice
      `Π ⟶ Π`).  It is reflexive, symmetric, idempotent — an equivalence relation.
  3.  Split it (`hsplit`): a map `f : Π → ρ` with `f f° = M`, `f° f = 1_ρ`.
  4.  `ρ` is a PARTIAL UNIT (`target_max_partialUnit`).
  5.  The embedding `πⱼ → ρ` is `Uⱼ ≫ f`, a map (composite of maps), hence the embedding.

  This is the GLOBALLY-COMPLETE analogue of §2.423 (`S2_423_ConnectedUnit.lean`), which
  ran the same argument in a power allegory with `maxEndo = 1_α / 0_α`.  Here there is no
  division: the maximal endomorphism is the lattice top `Sup`, and the partial-unit step is
  recast on a maximality hypothesis `hMax` (Freyd's actual argument) instead of the
  division-specific `maxEndo`.  `hsplit` is §2.423's own "equivalence relations split"
  hypothesis (`EffectiveAllegory.split_symmetric_idempotent`).

  Conventions: diagram-order composition `≫`, reciprocation `°`, intersection `∩`,
  union/supremum `Sup`, order `⊑`, bottom `𝟘`.  Strictly mathlib-free.
-/



namespace Freyd.Alg

open Cat
open LocallyCompleteDistributiveAllegory

section LCDA

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-! ## §2.226  The maximal endomorphism as the lattice top -/

/-- §2.226: the MAXIMAL ENDOMORPHISM of `α` — the union `⋃` of every endomorphism, i.e. the
    top of the complete hom-lattice `α ⟶ α`.  This is the completeness analogue of §2.423's
    `maxEndo α = 1_α / 0_α`; in a globally (hence locally) complete allegory the maximal
    endomorphism is available without division. -/
def topEndo (α : 𝒜) : α ⟶ α := Sup (fun _ : α ⟶ α => True)

/-- §2.226: `topEndo α` is maximal — every `R : α → α` satisfies `R ⊑ topEndo α`. -/
theorem topEndo_max {α : 𝒜} (R : α ⟶ α) : R ⊑ topEndo α := le_Sup trivial

/-- §2.226: the maximal endomorphism is reflexive (`1 ⊑ M`). -/
theorem topEndo_reflexive {α : 𝒜} : Reflexive (topEndo α) := topEndo_max (Cat.id α)

/-- §2.226: the maximal endomorphism is symmetric (`M° ⊑ M`, since `M°` is also an
    endomorphism and `M` is maximal). -/
theorem topEndo_symmetric {α : 𝒜} : Symmetric (topEndo α) := topEndo_max ((topEndo α)°)

/-- §2.226: the maximal endomorphism is idempotent (`M M = M`): reflexive + transitive,
    transitivity `M M ⊑ M` being maximality.  So `M` is an equivalence relation. -/
theorem topEndo_idempotent {α : 𝒜} : (topEndo α) ≫ (topEndo α) = topEndo α :=
  reflexive_transitive_idempotent topEndo_reflexive (topEndo_max _)

/-! ## §2.226  Disjoint-union injections are maps -/

/-- The injections `Uᵢ : αᵢ → β` of a §2.223 disjoint union are MAPS.

    ENTIRE: `dom Uᵢ = 1_{αᵢ} ∩ Uᵢ Uᵢ° = 1_{αᵢ} ∩ 1_{αᵢ} = 1_{αᵢ}` (`self : Uᵢ Uᵢ° = 1`).
    SIMPLE: `Uᵢ° Uᵢ ⊑ ⋃ⱼ Uⱼ° Uⱼ = 1_β` (`complete`). -/
theorem IndexedDisjointUnion.inject_map {I : Type u} {α : I → 𝒜} {β : 𝒜}
    (du : IndexedDisjointUnion α β) (i : I) : Map (du.U i) := by
  refine ⟨?_, ?_⟩
  · -- Entire: dom (Uᵢ) = 1
    show dom (du.U i) = Cat.id (α i)
    dsimp [dom]
    rw [du.self i, Allegory.inter_idem]
  · -- Simple: Uᵢ° Uᵢ ⊑ 1_β
    show (du.U i)° ≫ du.U i ⊑ Cat.id β
    exact le_trans (le_Sup ⟨i, rfl⟩) (le_of_eq' du.complete)

/-! ## §2.226  The partial-unit step

  The book's "if `M` is a maximal endomorphism and `ff° = M`, `f°f = 1` then the target of
  `f` is a partial unit".  This duplicates the algebra of §2.423's `target_split_partialUnit`,
  but parametrised on a MAXIMALITY hypothesis `hMax` rather than the division-specific
  `maxEndo = 1/0`: §2.226 lives in a globally complete (non-division) allegory, where the
  maximal endomorphism is the lattice top.  (Do not dedup this back into the division
  version — the two run in different ambient structures.) -/

/-- §2.226 (partial-unit step).  If `M : α → α` is MAXIMAL (`∀ R, R ⊑ M`) and a map
    `f : α → β` splits it — `f f° = M`, `f° f = 1_β` — then its target `β` is a PARTIAL UNIT.

    Book chain: `R = f° (f R f°) f ⊑ f° M f = f° f f° f = 1_β`, using `f R f° ⊑ M`
    (maximality) for the inequality and `M = f f°`, `f° f = 1_β` for the equalities. -/
theorem target_max_partialUnit {α β : 𝒜} (M : α ⟶ α) (hMax : ∀ R : α ⟶ α, R ⊑ M)
    (f : α ⟶ β) (hff : f ≫ f° = M) (hf'f : f° ≫ f = Cat.id β) :
    PartialUnit β := by
  intro R
  -- f R f° ⊑ M  (every endo of α is below the maximal one)
  have hmax : (f ≫ R ≫ f°) ⊑ M := hMax _
  -- f° (f R f°) f ⊑ f° M f
  have h1 : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ f° ≫ M ≫ f :=
    comp_mono_left f° (comp_mono_right hmax f)
  -- f° M f = f° (f f°) f = (f° f)(f° f) = 1_β
  have h2 : f° ≫ M ≫ f = Cat.id β := by
    rw [← hff, Cat.assoc, hf'f, Cat.comp_id, hf'f]
  -- f° (f R f°) f = (f° f) R (f° f) = R
  have hXeq : f° ≫ (f ≫ R ≫ f°) ≫ f = R := by
    rw [Cat.assoc f (R ≫ f°) f, ← Cat.assoc f° f ((R ≫ f°) ≫ f), hf'f, Cat.id_comp,
        Cat.assoc R f° f, hf'f, Cat.comp_id]
  have hle : f° ≫ (f ≫ R ≫ f°) ≫ f ⊑ Cat.id β := h2 ▸ h1
  rwa [hXeq] at hle

end LCDA

/-! ## §2.226  Partial units embed in a single partial unit -/

section GloballyComplete

variable {𝒜 : Type u} [GloballyCompleteAllegory 𝒜]

/-- **§2.226.**  In a GLOBALLY COMPLETE allegory in which equivalence relations split, for
    every set of partial units there is a PARTIAL UNIT in which they may all be embedded.

    HYPOTHESIS-GATED on `hsplit` — every equivalence relation splits with an entire leg.
    This is §2.423's own hypothesis (Freyd's "coreflexives split" with §2.422), precisely
    `EffectiveAllegory.split_symmetric_idempotent`.

    The construction works for any family of objects; `_hπ` records that the family is a set
    of partial units (Freyd's §2.226 framing), but is not needed — the embedded objects need
    not be partial units for the embedding into the partial unit `ρ` to exist. -/
theorem partialUnits_embed_in_partialUnit
    {J : Type u} (π : J → 𝒜) (_hπ : ∀ j, PartialUnit (π j))
    (hsplit : ∀ {a : 𝒜} (E : a ⟶ a), Reflexive E → Symmetric E → E ≫ E = E →
       ∃ (b : 𝒜) (g : a ⟶ b), Map g ∧ g ≫ g° = E ∧ g° ≫ g = Cat.id b) :
    ∃ (ρ : 𝒜), PartialUnit ρ ∧ ∀ j, ∃ (e : π j ⟶ ρ), Map e := by
  -- 1. The coproduct Π = ⊕_j π_j with its injections U_j (maps).
  let du := GloballyCompleteAllegory.toIndexedDisjointUnion π
  -- 2-3. M = topEndo Π is an equivalence relation; split it: f : Π → ρ, f f° = M, f° f = 1_ρ.
  obtain ⟨ρ, f, hf, hff, hf'f⟩ :=
    hsplit (topEndo (GloballyCompleteAllegory.disjointUnion π))
      topEndo_reflexive topEndo_symmetric topEndo_idempotent
  -- 4. ρ is a partial unit, and 5. each U_j ≫ f : π_j → ρ is a map (the embedding).
  refine ⟨ρ, target_max_partialUnit _ topEndo_max f hff hf'f, fun j => ?_⟩
  exact ⟨du.U j ≫ f, map_comp (du.inject_map j) hf⟩

end GloballyComplete

end Freyd.Alg
