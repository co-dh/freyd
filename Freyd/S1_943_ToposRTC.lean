/-
  Freyd & Scedrov, *Categories and Allegories* §1.943 / §1.77 — toward the
  reflexive-transitive closure `R*` in a topos as the internal-∀ family-glb
  `⋂{ S : BinRel A A | 1 ⊑ S ∧ R ⊑ S ∧ S⊚S ⊑ S }` over a subobject family of `[A×A]`.

  ## Status (HONEST)

  This file delivers the *reusable bridge* the `bigInter`-over-`prod A A` construction
  needs — the `Subobject (prod A A) → BinRel A A` converter `subToRel`, inverse to
  `relSub` — together with its round-trip laws and the order-correspondence
  `RelLe ↔ Subobject.le` lifted through it.  These were genuinely MISSING (the codebase
  had only `relSub : BinRel → Subobject` one-way, S1_60).

  The full `toposHasReflTransClosure` instance is NOT registered here.  See the
  RESIDUAL note at the bottom for the precise reason: the family-membership predicate
  `χ_F : [A×A] → Ω` must internally test transitivity `S⊚S ⊑ S` of the *variable*
  relation `S`, which needs a fibered internal relational composition (an internal
  existential `∃b. aSb ∧ bSc` over the variable `S`).  That operation is the genuine
  §1.543/§1.54-class residual; it is not yet available in the repo, and faking any
  `TransRefClos` field (or registering a `Sorry`-backed instance to discharge the
  downstream `topos_has_coequalizers`/`topos_is_bicartesian`) would be a false close.
-/

module

public import Freyd.S1_60
public import Freyd.S1_77
public import Freyd.S1_987_LeastClosedTopos
public import Freyd.S1_967_ToposExists

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

section
variable [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **`subToRel` — a subobject of `A×B` as a binary relation `A → B`.**  Inverse to
    `relSub` (S1_60): split the monic `m : S ↣ A×B` into its two projections
    `m≫fst, m≫snd`, jointly monic because `pair (m≫fst) (m≫snd) = m` is monic.

    This is exactly the converter the family-glb RTC construction needs to turn the
    `bigInter : Subobject (prod A A)` back into a `BinRel A A`. -/
@[expose] public noncomputable def subToRel {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B := subRel S

/-- `(subToRel S).arr`-pairing is `S.arr`: `pair (S.arr≫fst) (S.arr≫snd) = S.arr`. -/
public theorem relSub_subToRel_arr {A B : 𝒞} (S : Subobject 𝒞 (prod A B)) :
    pair (subToRel S).colA (subToRel S).colB = S.arr :=
  relSub_subRel_arr S

end

section
variable [PreLogos 𝒞]

/-- **Round-trip `subToRel (relSub R) = R`.**  `relSub R` has arrow `pair R.colA R.colB`,
    whose two projections are `R.colA`, `R.colB` again. -/
public theorem subToRel_relSub {A B : 𝒞} (R : BinRel 𝒞 A B) : subToRel (relSub R) = R := by
  -- `subToRel (relSub R)` is `BinRel.mk R.src (pair R.colA R.colB ≫ fst) (… ≫ snd) …`;
  -- the two cols recover `R.colA`, `R.colB` by the fst/snd β-laws; `src` is `R.src`
  -- definitionally and `isMonicPair` is a `Prop` (proof-irrelevant).  Field-wise congruence.
  simp only [subToRel, subRel, relSub, fst_pair, snd_pair]

/-- **Order correspondence through `subToRel`.**  `RelLe (subToRel S) (subToRel T)`
    is exactly `S.le T` for subobjects `S, T` of `A×B`.  (Via `relLe_iff_subLe` and the
    `relSub_subToRel_arr` η-law: `relSub (subToRel S)` has the same arrow as `S`.) -/
public theorem relLe_subToRel_iff_subLe {A B : 𝒞} (S T : Subobject 𝒞 (prod A B)) :
    RelLe (subToRel S) (subToRel T) ↔ S.le T := by
  rw [relLe_iff_subLe]
  -- `(relSub (subToRel S)).arr = pair (subToRel S).colA (subToRel S).colB = S.arr`
  -- (`relSub_subToRel_arr`); same for T.  Both directions just rewrite the arrows.
  have hS : (relSub (subToRel S)).arr = S.arr := relSub_subToRel_arr S
  have hT : (relSub (subToRel T)).arr = T.arr := relSub_subToRel_arr T
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hT] at hh
    rw [← hS]; exact hh
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    rw [hT, hS]; exact hh

end

/-! ## §1.943  The reflexive-transitive closure `R*` as the internal-∀ family-glb

  The RTC of `R : BinRel A A` is the glb `⋂{ S ⊆ A×A | (1 ⊑ S) ∧ (R ⊑ S) ∧ (S⊚S ⊑ S) }`
  over a subobject family of `[A×A]`.  We name that family by a global element
  `rtcFamily R : 1 → [[A×A]]`, classified by `rtcChar R : [A×A] → Ω`, the 3-way meet of:

  *  `reflChar  : [A×A] → Ω`, `s ↦ ∀a. (a,a)∈s`           (the diagonal `1 ⊑ s`),
  *  `containsRChar R : [A×A] → Ω`, `s ↦ ∀p. p∈R ⇒ p∈s`   (`R ⊑ s`),
  *  `transChar : [A×A] → Ω`, `s ↦ ∀(a,b,c). ((a,b)∈s ∧ (b,c)∈s) ⇒ (a,c)∈s`  (`s⊚s ⊑ s`).

  Each is a fibered-∀ `curry body ≫ forallC` over the quantified domain, *exactly* the
  `tStable`/`predF`/`bigInterChar` recipe of `Freyd/LeastClosedTopos.lean`.  The key point
  the prior RESIDUAL note got wrong: TRANSITIVITY does NOT need an internal existential /
  fibered relational composition.  `s⊚s ⊑ s` is equivalent to the *universally* quantified
  `∀a b c. aSb ∧ bSc ⇒ aSc`, which is built from three membership LOOKUPS (`eval`) of the
  variable `s` — no `∃b` ever appears.  The middle variable `b` is universally bound, not
  existentially eliminated, so `transChar` is a plain fibered-∀ like `tStable`. -/

open HasSubobjectClassifier

section
variable [Topos 𝒞]

/-- Internal membership lookup `(coords) ∈ s` for a generalized point `coords : X → A×A`
    of the relation domain and `s : X → [A×A]`: `⟨coords, s⟩ ≫ eval`. -/
@[expose] public noncomputable abbrev memLk {A X : 𝒞} (coords : X ⟶ prod A A) (s : X ⟶ powObj (prod A A)) :
    X ⟶ omega (𝒞 := 𝒞) :=
  pair coords s ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞))

/-! ### The reflexivity predicate `reflChar : [A×A] → Ω`, `s ↦ ∀a. (a,a)∈s`. -/

/-- The diagonal body `prod A [A×A] → Ω`, `(a,s) ↦ (a,a)∈s`. -/
@[expose] public noncomputable def reflBody {A : 𝒞} : prod A (powObj (prod A A)) ⟶ omega (𝒞 := 𝒞) :=
  pair (pair fst fst) snd ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞))

/-- `reflChar : [A×A] → Ω`, `s ↦ ∀a:A. (a,a)∈s`.  Fibered-∀ over `a : A`. -/
@[expose] public noncomputable def reflChar {A : 𝒞} : powObj (prod A A) ⟶ omega (𝒞 := 𝒞) :=
  curry (reflBody (A := A)) ≫ forallC A

/-! ### The containment predicate `containsRChar R : [A×A] → Ω`, `s ↦ ∀p. p∈R ⇒ p∈s`. -/

/-- The contains-`R` body `prod (A×A) [A×A] → Ω`, `(p,s) ↦ (p∈R) ⇒ (p∈s)`, where
    `p∈R = ⟨fst, term≫rName⟩ ≫ eval` and `p∈s = ⟨fst, snd⟩ ≫ eval`. -/
@[expose] public noncomputable def containsRBody {A : 𝒞} (rName : one ⟶ powObj (prod A A)) :
    prod (prod A A) (powObj (prod A A)) ⟶ omega (𝒞 := 𝒞) :=
  pair
    (pair fst (term (prod (prod A A) (powObj (prod A A))) ≫ rName)
      ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
    (pair fst snd ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
  ≫ impΩ

/-- `containsRChar R : [A×A] → Ω`, `s ↦ ∀p:A×A. (p∈R) ⇒ (p∈s)`.  Fibered-∀ over `p`. -/
@[expose] public noncomputable def containsRChar {A : 𝒞} (rName : one ⟶ powObj (prod A A)) :
    powObj (prod A A) ⟶ omega (𝒞 := 𝒞) :=
  curry (containsRBody rName) ≫ forallC (prod A A)

/-! ### The transitivity predicate `transChar : [A×A] → Ω`,
    `s ↦ ∀(a,b,c). ((a,b)∈s ∧ (b,c)∈s) ⇒ (a,c)∈s`. -/

/-- The transitivity body `prod (A×(A×A)) [A×A] → Ω`.  With `w = fst` the bound triple
    `(a,b,c)` and `s = snd`, it is `((a,b)∈s ∧ (b,c)∈s) ⇒ (a,c)∈s`. -/
@[expose] public noncomputable def transBody {A : 𝒞} :
    prod (prod A (prod A A)) (powObj (prod A A)) ⟶ omega (𝒞 := 𝒞) :=
  pair
    (pair
      (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ fst)) snd)
      (memLk (pair (fst ≫ snd ≫ fst) (fst ≫ snd ≫ snd)) snd)
    ≫ omegaMeet)
    (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ snd)) snd)
  ≫ impΩ

/-- `transChar : [A×A] → Ω`, `s ↦ ∀(a,b,c). ((a,b)∈s ∧ (b,c)∈s) ⇒ (a,c)∈s`.  Fibered-∀
    over the triple `(a,b,c) : A × (A × A)`. -/
@[expose] public noncomputable def transChar {A : 𝒞} : powObj (prod A A) ⟶ omega (𝒞 := 𝒞) :=
  curry (transBody (A := A)) ≫ forallC (prod A (prod A A))

/-! ### The full family predicate and its name. -/

/-- The RTC family predicate `rtcChar R : [A×A] → Ω`, the 3-way meet
    `reflChar ∧ containsRChar R ∧ transChar`. -/
@[expose] public noncomputable def rtcChar {A : 𝒞} (rName : one ⟶ powObj (prod A A)) :
    powObj (prod A A) ⟶ omega (𝒞 := 𝒞) :=
  pair (pair (reflChar (A := A)) (containsRChar rName) ≫ omegaMeet) (transChar (A := A))
    ≫ omegaMeet

/-- The family name `rtcFamily R : 1 → [[A×A]]` of `{ s : [A×A] | rtcChar R }`. -/
@[expose] public noncomputable def rtcFamily {A : 𝒞} (rName : one ⟶ powObj (prod A A)) :
    one ⟶ powObj (powObj (prod A A)) :=
  curry (fst ≫ rtcChar rName)

/-- **KEY — `membershipMap (rtcFamily R) = rtcChar R`.**  Via `membershipMap_curry_fst`. -/
public theorem membershipMap_rtcFamily {A : 𝒞} (rName : one ⟶ powObj (prod A A)) :
    membershipMap (rtcFamily rName) = rtcChar rName := by
  rw [rtcFamily, membershipMap_curry_fst]

/-! ## §1.943  membership-lookup at a constant name -/

/-- **Lookup at a name (generalized point).**  For a subobject `T0 ↣ A×A`, a generalized
    point `coords : X → A×A` and the constant name `g = term X ≫ 'T0'`, the membership
    lookup `memLk coords g = coords ≫ classify T0.arr`.  (`p ∈ T0` as an Ω-test.) -/
public theorem memLk_at_name {A X : 𝒞} (T0 : Subobject 𝒞 (prod A A)) (coords : X ⟶ prod A A) :
    memLk coords (term X ≫ nameOf T0.arr T0.monic)
      = coords ≫ HasSubobjectClassifier.classify T0.arr T0.monic := by
  rw [memLk, ← membershipMap_nameOf T0.arr T0.monic, membershipMap, ← Cat.assoc]
  congr 1
  symm
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, Cat.comp_id]
  · rw [Cat.assoc, snd_pair, ← Cat.assoc]
    congr 1
    exact term_uniq _ _

/-! ## §1.943  generic fibered-∀ at a generalized name -/

/-- **∀-elimination at a generalized point (generic body).**  If `g : X → [A×A]` passes the
    fibered-∀ `curry body ≫ forallC C` (`g ≫ … = ⊤`), then for EVERY generalized point
    `τ : X → C` the body holds at `(τ, g)`: `pair τ g ≫ body = ⊤`.  Mirrors `tStable_gen`. -/
public theorem forallName_elim {A C X : 𝒞} (body : prod C (powObj (prod A A)) ⟶ omega (𝒞 := 𝒞))
    (g : X ⟶ powObj (prod A A))
    (hg : g ≫ (curry body ≫ forallC C) = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (τ : X ⟶ C) :
    pair τ g ≫ body = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [← Cat.assoc] at hg
  have hentire : g ≫ curry body = term X ≫ topName C :=
    (forall_beta C (g ≫ curry body)).mp hg
  have helim := forall_elim (g ≫ curry body) hentire τ
  rwa [eval_curry_point body τ g] at helim

/-- **Introducing the fibered-∀ at a name (generic body).**  To show a constant name
    `g = term X ≫ 'T0'` passes the fibered-∀, it suffices that the body, with its `[A×A]`-slot
    fixed at `'T0'`, is entire over `prod C X`.  Concretely: build `S_F ≤ S_In`-style from
    `prodMap C [A×A] … 'T0'`-fixed body = ⊤.  (Used via the conjunct lemmas below.) -/
public theorem forallName_intro {A C : 𝒞} (body : prod C (powObj (prod A A)) ⟶ omega (𝒞 := 𝒞))
    (T0 : Subobject 𝒞 (prod A A))
    (hbody : pair (Cat.id C) (term C ≫ nameOf T0.arr T0.monic) ≫ body
      = term C ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    nameOf T0.arr T0.monic ≫ (curry body ≫ forallC C)
      = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [← Cat.assoc]
  rw [forall_beta C (nameOf T0.arr T0.monic ≫ curry body)]
  have hinj : ∀ (G H : one ⟶ powObj C), membershipMap G = membershipMap H → G = H :=
    fun G H hGH => by rw [← curry_fst_membershipMap G, ← curry_fst_membershipMap H, hGH]
  apply hinj
  rw [show term one ≫ topName C = topName C by
        rw [term_uniq (term one) (Cat.id one), Cat.id_comp]]
  rw [membershipMap_topName, classify_entire]
  -- membershipMap (nameOf T0 ≫ curry body) = body with slot fixed at 'T0' = ⊤.
  show pair (Cat.id C) (term C ≫ (nameOf T0.arr T0.monic ≫ curry body))
      ≫ eval_exp C (omega (𝒞 := 𝒞)) = _
  rw [show term C ≫ (nameOf T0.arr T0.monic ≫ curry body)
        = (term C ≫ nameOf T0.arr T0.monic) ≫ curry body from (Cat.assoc _ _ _).symm]
  rw [eval_curry_point body (Cat.id C) (term C ≫ nameOf T0.arr T0.monic)]
  exact hbody

/-! ## §1.943  the three conjuncts at a subobject-name -/

/-- The name of `R : BinRel A A` as a subobject of `A×A`. -/
@[expose] public noncomputable def rName {A : 𝒞} (R : BinRel 𝒞 A A) : one ⟶ powObj (prod A A) :=
  nameOf (relSub R).arr (relSub R).monic

/-- **`containsRChar` intro.**  If `R ⊑ T` (subobjects of `A×A`), the name `'T'` passes the
    contains-`R` test: `'T' ≫ containsRChar 'R' = ⊤`. -/
public theorem containsRChar_name_of_le {A : 𝒞} (Rs T : Subobject 𝒞 (prod A A)) (hle : Rs.le T) :
    nameOf T.arr T.monic ≫ containsRChar (nameOf Rs.arr Rs.monic)
      = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [containsRChar]
  apply forallName_intro (containsRBody (nameOf Rs.arr Rs.monic)) T
  -- body fixed at 'T' = ⟨p∈R, p∈T⟩ ≫ impΩ over prod (A×A);  p ranges via id.
  rw [containsRBody, ← Cat.assoc]
  -- compute the two components: p∈R = id ≫ χ_Rs ; p∈T = id ≫ χ_T.
  have hcomp : pair (Cat.id (prod A A)) (term (prod A A) ≫ nameOf T.arr T.monic)
      ≫ pair
          (pair fst (term (prod (prod A A) (powObj (prod A A))) ≫ nameOf Rs.arr Rs.monic)
            ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
          (pair fst snd ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
      = pair (subChar Rs) (subChar T) := by
    apply pair_uniq
    · -- first: p∈R = memLk id ('R') = id ≫ χ_Rs = subChar Rs
      rw [Cat.assoc, fst_pair, ← Cat.assoc]
      have h1 : pair (Cat.id (prod A A)) (term (prod A A) ≫ nameOf T.arr T.monic)
          ≫ pair fst (term (prod (prod A A) (powObj (prod A A))) ≫ nameOf Rs.arr Rs.monic)
          = pair (Cat.id (prod A A)) (term (prod A A) ≫ nameOf Rs.arr Rs.monic) := by
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, fst_pair]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc]
          congr 1
          exact term_uniq _ _
      rw [h1]
      show memLk (Cat.id (prod A A)) (term (prod A A) ≫ nameOf Rs.arr Rs.monic) = subChar Rs
      rw [memLk_at_name Rs (Cat.id (prod A A)), Cat.id_comp]
    · -- second: p∈T = memLk id ('T') = subChar T
      rw [Cat.assoc, snd_pair, ← Cat.assoc]
      have h2 : pair (Cat.id (prod A A)) (term (prod A A) ≫ nameOf T.arr T.monic)
          ≫ pair fst snd
          = pair (Cat.id (prod A A)) (term (prod A A) ≫ nameOf T.arr T.monic) := by
        rw [pair_fst_snd, Cat.comp_id]
      rw [h2]
      show memLk (Cat.id (prod A A)) (term (prod A A) ≫ nameOf T.arr T.monic) = subChar T
      rw [memLk_at_name T (Cat.id (prod A A)), Cat.id_comp]
  rw [hcomp]
  exact impΩ_entire_of_le Rs T hle

/-- **`reflChar` intro.**  If the diagonal subobject `Δ = relSub (graph id)` lies below `T`,
    the name `'T'` passes the reflexivity test: `'T' ≫ reflChar = ⊤`. -/
public theorem reflChar_name_of_diag_le {A : 𝒞} (T : Subobject 𝒞 (prod A A))
    (hdiag : (relSub (graph (Cat.id A))).le T) :
    nameOf T.arr T.monic ≫ reflChar (A := A)
      = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [reflChar]
  apply forallName_intro (reflBody (A := A)) T
  -- body fixed at 'T' over A: pair (pair id id) (term≫'T') ≫ eval = diag ≫ χ_T.
  rw [reflBody, ← Cat.assoc]
  have hdiagP : pair (Cat.id A) (term A ≫ nameOf T.arr T.monic)
      ≫ pair (pair fst fst) snd
      = pair (pair (Cat.id A) (Cat.id A)) (term A ≫ nameOf T.arr T.monic) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  rw [hdiagP]
  show memLk (pair (Cat.id A) (Cat.id A)) (term A ≫ nameOf T.arr T.monic)
      = term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [memLk_at_name T (pair (Cat.id A) (Cat.id A))]
  -- diag A ≫ χ_T = ⊤  ⟺  Allows T (diag), supplied by hdiag through Δ.arr = pair id id.
  apply (allows_iff_classify T (pair (Cat.id A) (Cat.id A))).1
  obtain ⟨h, hh⟩ := hdiag
  refine ⟨h, ?_⟩
  rw [hh]
  -- (relSub (graph id)).arr = pair (graph id).colA (graph id).colB = pair id id.
  show (relSub (graph (Cat.id A))).arr = pair (Cat.id A) (Cat.id A)
  rfl

/-! ## §1.943  internal transitivity elimination -/

/-- **Internal transitivity, ∀-eliminated (generalized point).**  If `g : K → [A×A]` passes the
    transitivity test (`g ≫ transChar = ⊤`) and three points satisfy `(a,b)∈g`, `(b,c)∈g`, then
    `(a,c)∈g`.  ∀-elimination of `transBody` at the triple `(a,b,c)` + modus ponens
    (`impΩ_forward`).  No internal `∃`/composition — `b` is the bound middle variable. -/
public theorem transChar_gen {A K : 𝒞} (g : K ⟶ powObj (prod A A)) (a b c : K ⟶ A)
    (hg : g ≫ transChar (A := A) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hab : memLk (pair a b) g = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hbc : memLk (pair b c) g = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    memLk (pair a c) g = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- ∀-elim transBody at τ = (a,(b,c)) : K → A×(A×A).
  rw [transChar] at hg
  have hbody := forallName_elim (transBody (A := A)) g hg (pair a (pair b c))
  -- transBody = ⟨(ab∈g ∧ bc∈g), ac∈g⟩ ≫ impΩ; compute each lookup at the triple.
  rw [transBody, ← Cat.assoc] at hbody
  -- Direct computation of the three sub-lookups along (τ,g).
  have e_ab : pair (pair a (pair b c)) g
      ≫ memLk (pair (fst ≫ fst) (fst ≫ snd ≫ fst)) snd = memLk (pair a b) g := by
    rw [memLk, memLk, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  have e_bc : pair (pair a (pair b c)) g
      ≫ memLk (pair (fst ≫ snd ≫ fst) (fst ≫ snd ≫ snd)) snd = memLk (pair b c) g := by
    rw [memLk, memLk, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  have e_ac : pair (pair a (pair b c)) g
      ≫ memLk (pair (fst ≫ fst) (fst ≫ snd ≫ snd)) snd = memLk (pair a c) g := by
    rw [memLk, memLk, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, snd_pair]
    · rw [Cat.assoc, snd_pair, snd_pair]
  -- Split the impΩ body along K into ⟨antecedent, consequent⟩ ≫ impΩ.
  have hsplit : pair (pair a (pair b c)) g ≫ pair
        (pair (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ fst)) snd)
              (memLk (pair (fst ≫ snd ≫ fst) (fst ≫ snd ≫ snd)) snd) ≫ omegaMeet)
        (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ snd)) snd)
      = pair
          (pair (memLk (pair a b) g) (memLk (pair b c) g) ≫ omegaMeet)
          (memLk (pair a c) g) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, e_ab]
      · rw [Cat.assoc, snd_pair, e_bc]
    · rw [Cat.assoc, snd_pair, e_ac]
  rw [hsplit] at hbody
  -- modus ponens: antecedent (ab∈g ∧ bc∈g) is ⊤, so consequent ac∈g is ⊤.
  have hant : pair (memLk (pair a b) g) (memLk (pair b c) g) ≫ omegaMeet
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    have := (meet_true_iff_and (memLk (pair a b) g) (memLk (pair b c) g) (Cat.id K)).2
      ⟨by rw [Cat.id_comp]; exact hab, by rw [Cat.id_comp]; exact hbc⟩
    rwa [Cat.id_comp] at this
  have := impΩ_forward _ _ (Cat.id K)
    (by rw [Cat.id_comp]; exact hbody)
    (by rw [Cat.id_comp]; exact hant)
  rwa [Cat.id_comp] at this

/-! ## §1.943  conjunct extraction + generalized eliminations -/

/-- The three conjuncts of `rtcChar` at a generalized member `s : K → [A×A]`. -/
public theorem rtcChar_conjuncts {A K : 𝒞} (rName' : one ⟶ powObj (prod A A)) (s : K ⟶ powObj (prod A A))
    (hs : s ≫ rtcChar rName' = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    s ≫ reflChar (A := A) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
    ∧ s ≫ containsRChar rName' = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
    ∧ s ≫ transChar (A := A) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [rtcChar] at hs
  obtain ⟨h12, h3⟩ := (meet_true_iff_and _ (transChar (A := A)) s).1 hs
  obtain ⟨h1, h2⟩ := (meet_true_iff_and (reflChar (A := A)) (containsRChar rName') s).1 h12
  exact ⟨h1, h2, h3⟩

/-- **`reflChar` ∀-elimination.**  If `s : K → [A×A]` passes `reflChar` (`s ≫ reflChar = ⊤`),
    then every diagonal point lies in `s`: for `a : K → A`, `memLk (pair a a) s = ⊤`. -/
public theorem reflChar_gen {A K : 𝒞} (s : K ⟶ powObj (prod A A)) (a : K ⟶ A)
    (hs : s ≫ reflChar (A := A) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    memLk (pair a a) s = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [reflChar] at hs
  have hbody := forallName_elim (reflBody (A := A)) s hs a
  rw [reflBody] at hbody
  rw [← hbody, memLk, ← Cat.assoc]
  congr 1
  symm
  apply pair_uniq
  · rw [Cat.assoc, fst_pair]
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, fst_pair]
  · rw [Cat.assoc, snd_pair, snd_pair]

/-- **`containsRChar` ∀-elimination.**  If `s : K → [A×A]` passes `containsRChar R`
    (`s ≫ containsRChar 'R' = ⊤`) and a generalized point `p : K → A×A` lies in `R`
    (`memLk p (term K ≫ 'R') = ⊤`), then `p` lies in `s` (`memLk p s = ⊤`). -/
public theorem containsRChar_gen {A K : 𝒞} (Rs : Subobject 𝒞 (prod A A)) (s : K ⟶ powObj (prod A A))
    (p : K ⟶ prod A A)
    (hs : s ≫ containsRChar (nameOf Rs.arr Rs.monic) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hp : memLk p (term K ≫ nameOf Rs.arr Rs.monic) = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    memLk p s = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [containsRChar] at hs
  have hbody := forallName_elim (containsRBody (nameOf Rs.arr Rs.monic)) s hs p
  rw [containsRBody, ← Cat.assoc] at hbody
  -- split body = ⟨p∈R, p∈s⟩ ≫ impΩ along K.
  have hsplit : pair p s ≫ pair
        (pair fst (term (prod (prod A A) (powObj (prod A A))) ≫ nameOf Rs.arr Rs.monic)
          ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
        (pair fst snd ≫ eval_exp (prod A A) (omega (𝒞 := 𝒞)))
      = pair (memLk p (term K ≫ nameOf Rs.arr Rs.monic)) (memLk p s) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, memLk]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc]
        congr 1
        exact term_uniq _ _
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, memLk]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]
  rw [hsplit] at hbody
  have := impΩ_forward _ _ (Cat.id K)
    (by rw [Cat.id_comp]; exact hbody)
    (by rw [Cat.id_comp]; exact hp)
  rwa [Cat.id_comp] at this

/-! ## §1.943  the reflexive-transitive closure and the five `TransRefClos` fields -/

/-- The RTC closure subobject `⋂F_R ↣ A×A` of `R : BinRel A A`. -/
@[expose] public noncomputable def rtcSub {A : 𝒞} (R : BinRel 𝒞 A A) : Subobject 𝒞 (prod A A) :=
  bigInter (rtcFamily (rName R))

/-- The RTC closure relation `R* : BinRel A A`. -/
@[expose] public noncomputable def rtcClos {A : 𝒞} (R : BinRel 𝒞 A A) : BinRel 𝒞 A A :=
  subToRel (rtcSub R)

/-- **`le` field — `R ⊑ R*`.**  Greatest-lower-bound: `R` is below every member of `F_R`
    (each member passes `containsRChar`, i.e. `R ⊑ member`), hence below `⋂F_R`. -/
public theorem rtcClos_le {A : 𝒞} (R : BinRel 𝒞 A A) : RelLe R (rtcClos R) := by
  rw [rtcClos, show R = subToRel (relSub R) from (subToRel_relSub R).symm,
    relLe_subToRel_iff_subLe, subToRel_relSub]
  -- (relSub R).le (⋂F_R)  via  Allows (⋂F_R) (relSub R).arr.
  rw [rtcSub]
  show Allows (bigInter (rtcFamily (rName R))) (relSub R).arr
  apply allows_bigInter_of_carrier (relSub R).arr (rtcFamily (rName R))
  intro K k hk
  -- k≫fst ∈ F_R ⟹ (via containsR conjunct) the R-point (relSub R).arr(k≫snd) ∈ (k≫fst).
  rw [← Cat.assoc, membershipMap_rtcFamily] at hk
  obtain ⟨_, hcR, _⟩ := rtcChar_conjuncts (rName R) (k ≫ fst) hk
  -- the R-point: p := (k≫snd) factors as a point of A×A via (relSub R).arr.
  have hpR : memLk ((k ≫ snd) ≫ (relSub R).arr) (term K ≫ nameOf (relSub R).arr (relSub R).monic)
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    rw [memLk_at_name (relSub R) ((k ≫ snd) ≫ (relSub R).arr)]
    -- (relSub R).arr(k≫snd) ∈ R: factors through relSub R, so χ = ⊤.
    apply (allows_iff_classify (relSub R) ((k ≫ snd) ≫ (relSub R).arr)).1
    exact ⟨k ≫ snd, rfl⟩
  have hmem := containsRChar_gen (relSub R) (k ≫ fst) ((k ≫ snd) ≫ (relSub R).arr) hcR hpR
  -- repackage memLk into the hci goal shape.
  rw [memLk] at hmem
  rw [← hmem, ← Cat.assoc]
  congr 1
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, ← Cat.assoc]
  · rw [Cat.assoc, snd_pair]

/-- **`refl` field — `R*` is reflexive.**  Greatest-lower-bound: the diagonal `Δ` is below
    every member (each passes `reflChar`, i.e. `Δ ⊑ member`), hence below `⋂F_R`. -/
public theorem rtcClos_refl {A : 𝒞} (R : BinRel 𝒞 A A) : IsReflexive (rtcClos R) := by
  rw [IsReflexive, rtcClos]
  rw [show graph (Cat.id A) = subToRel (relSub (graph (Cat.id A))) from
      (subToRel_relSub (graph (Cat.id A))).symm]
  rw [relLe_subToRel_iff_subLe]
  rw [rtcSub]
  show Allows (bigInter (rtcFamily (rName R))) (relSub (graph (Cat.id A))).arr
  apply allows_bigInter_of_carrier (relSub (graph (Cat.id A))).arr (rtcFamily (rName R))
  intro K k hk
  rw [← Cat.assoc, membershipMap_rtcFamily] at hk
  obtain ⟨hrefl, _, _⟩ := rtcChar_conjuncts (rName R) (k ≫ fst) hk
  -- diagonal point: (relSub (graph id)).arr = pair id id, so the lookup is reflChar_gen at k≫snd.
  have hmem := reflChar_gen (k ≫ fst) (k ≫ snd) hrefl
  rw [memLk] at hmem
  rw [← hmem, ← Cat.assoc]
  congr 1
  -- k ≫ pair (snd≫Δ) fst = pair (pair (k≫snd) (k≫snd)) (k≫fst), since Δ.arr = pair id id.
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, ← Cat.assoc]
    show (k ≫ snd) ≫ (relSub (graph (Cat.id A))).arr = pair (k ≫ snd) (k ≫ snd)
    rw [show (relSub (graph (Cat.id A))).arr = pair (Cat.id A) (Cat.id A) from rfl]
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]; exact Cat.comp_id _
    · rw [Cat.assoc, snd_pair]; exact Cat.comp_id _
  · rw [Cat.assoc, snd_pair]

/-! ## §1.943  pointwise composition (the external `⊚` at a generalized point) -/

/-- **Pointwise membership in a composition.**  If, over `K`, `pair a b` and `pair b c` both
    factor through a relation `S : BinRel A A` (as the subobject `relSub S`), then `pair a c`
    factors through the composite `relSub (S ⊚ S)`.  This is the elementary pullback+image
    content of `⊚`: `(u,v)` with matching middle leg `b` lift into the pullback, and the
    span maps onto `pair a c`, whose image is `(S⊚S).src`. -/
public theorem mem_compose_of_legs {A K : 𝒞} (S : BinRel 𝒞 A A) (a b c : K ⟶ A)
    (hab : Allows (relSub S) (pair a b)) (hbc : Allows (relSub S) (pair b c)) :
    Allows (relSub (S ⊚ S)) (pair a c) := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  -- (relSub S).arr = pair S.colA S.colB; extract the four leg equations.
  have huA : u ≫ S.colA = a := by
    have := congrArg (· ≫ fst) hu
    simpa [Cat.assoc, fst_pair, relSub] using this
  have huB : u ≫ S.colB = b := by
    have := congrArg (· ≫ snd) hu
    simpa [Cat.assoc, snd_pair, relSub] using this
  have hvA : v ≫ S.colA = b := by
    have := congrArg (· ≫ fst) hv
    simpa [Cat.assoc, fst_pair, relSub] using this
  have hvB : v ≫ S.colB = c := by
    have := congrArg (· ≫ snd) hv
    simpa [Cat.assoc, snd_pair, relSub] using this
  -- (u,v) is a cone over the pullback of S.colB and S.colA (middle leg b).
  let pb := HasPullbacks.has S.colB S.colA
  have hcone : u ≫ S.colB = v ≫ S.colA := by rw [huB, hvA]
  let cone : Cone S.colB S.colA := ⟨K, u, v, hcone⟩
  let l := pb.lift cone
  have hl₁ : l ≫ pb.cone.π₁ = u := pb.lift_fst cone
  have hl₂ : l ≫ pb.cone.π₂ = v := pb.lift_snd cone
  -- the composition span; l carries it onto pair a c.
  let span : pb.cone.pt ⟶ prod A A := pair (pb.cone.π₁ ≫ S.colA) (pb.cone.π₂ ≫ S.colB)
  have hspan : l ≫ span = pair a c := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, hl₁, huA]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, hl₂, hvB]
  -- (S⊚S).arr = (image span).arr, so pair a c = l ≫ span factors through it.
  refine ⟨l ≫ image.lift span, ?_⟩
  show (l ≫ image.lift span) ≫ pair (S ⊚ S).colA (S ⊚ S).colB = pair a c
  rw [show pair (S ⊚ S).colA (S ⊚ S).colB = (image span).arr from
    (pair_uniq _ _ _ rfl rfl).symm]
  rw [Cat.assoc, image.lift_fac, hspan]

/-- **`transChar` intro.**  If `subToRel T0` is transitive, the name `'T0'` passes the
    transitivity test: `'T0' ≫ transChar = ⊤`.  The reduction is `forallName_intro` over the
    triple domain `W = A×(A×A)`; the body fixed at `'T0'` is the Heyting implication
    `(antecedent ⇒ consequent)`, entire because `antecedent ≤ consequent` POINTWISE — on the
    carrier of the antecedent both `(a,b)∈T0` and `(b,c)∈T0` hold, so `(a,c) ∈ T0⊚T0 ⊑ T0`. -/
public theorem transChar_name_of_transitive {A : 𝒞} (T0 : Subobject 𝒞 (prod A A))
    (htr : IsTransitive (subToRel T0)) :
    nameOf T0.arr T0.monic ≫ transChar (A := A)
      = term one ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [transChar]
  apply forallName_intro (transBody (A := A)) T0
  -- the triple domain and its three coordinate projections.
  let pa : prod A (prod A A) ⟶ A := fst
  let pb : prod A (prod A A) ⟶ A := snd ≫ fst
  let pc : prod A (prod A A) ⟶ A := snd ≫ snd
  rw [transBody, ← Cat.assoc]
  -- generic lookup reduction at the fixed name: ⟨id,term≫'T0'⟩ ≫ memLk (pair (fst≫x) (fst≫y)) snd
  -- = pair x y ≫ χ_T0.
  have lk : ∀ (x y : prod A (prod A A) ⟶ A),
      pair (Cat.id (prod A (prod A A))) (term (prod A (prod A A)) ≫ nameOf T0.arr T0.monic)
        ≫ memLk (pair (fst ≫ x) (fst ≫ y)) snd = pair x y ≫ subChar T0 := by
    intro x y
    rw [memLk, ← Cat.assoc]
    have hpaste : pair (Cat.id (prod A (prod A A)))
          (term (prod A (prod A A)) ≫ nameOf T0.arr T0.monic)
        ≫ pair (pair (fst ≫ x) (fst ≫ y)) snd
        = pair (pair x y) (term (prod A (prod A A)) ≫ nameOf T0.arr T0.monic) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair, Cat.id_comp]
      · rw [Cat.assoc, snd_pair, snd_pair]
    rw [hpaste]
    show memLk (pair x y) (term (prod A (prod A A)) ≫ nameOf T0.arr T0.monic) = pair x y ≫ subChar T0
    rw [memLk_at_name T0 (pair x y)]
  -- assemble the body into ⟨ (pab∧pbc) , pac ⟩ ≫ impΩ.
  have hcomp : pair (Cat.id (prod A (prod A A)))
        (term (prod A (prod A A)) ≫ nameOf T0.arr T0.monic)
      ≫ pair
          (pair
            (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ fst)) snd)
            (memLk (pair (fst ≫ snd ≫ fst) (fst ≫ snd ≫ snd)) snd) ≫ omegaMeet)
          (memLk (pair (fst ≫ fst) (fst ≫ snd ≫ snd)) snd)
      = pair
          (pair (pair pa pb ≫ subChar T0) (pair pb pc ≫ subChar T0) ≫ omegaMeet)
          (pair pa pc ≫ subChar T0) := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]
      congr 1
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]; exact lk pa pb
      · rw [Cat.assoc, snd_pair]; exact lk pb pc
    · rw [Cat.assoc, snd_pair]; exact lk pa pc
  rw [hcomp]
  -- entire via impΩ: antecedent ≤ consequent.  Realize as subobjects of W.
  rw [pair_impΩ]
  obtain ⟨_, mA, hmA, hSA⟩ := classify_surjective
    (pair (pair pa pb ≫ subChar T0) (pair pb pc ≫ subChar T0) ≫ omegaMeet)
  obtain ⟨_, mC, hmC, hSC⟩ := classify_surjective (pair pa pc ≫ subChar T0)
  let S_ant : Subobject 𝒞 (prod A (prod A A)) := ⟨_, mA, hmA⟩
  let S_con : Subobject 𝒞 (prod A (prod A A)) := ⟨_, mC, hmC⟩
  have hcA : subChar S_ant
      = pair (pair pa pb ≫ subChar T0) (pair pb pc ≫ subChar T0) ≫ omegaMeet := hSA
  have hcC : subChar S_con = pair pa pc ≫ subChar T0 := hSC
  rw [show pair (pair (pair pa pb ≫ subChar T0) (pair pb pc ≫ subChar T0) ≫ omegaMeet)
            (pair (pair (pair pa pb ≫ subChar T0) (pair pb pc ≫ subChar T0) ≫ omegaMeet)
              (pair pa pc ≫ subChar T0) ≫ omegaMeet)
          ≫ heytingDoubleArrow
        = subChar (Sub.imp S_ant S_con) by
      rw [classify_imp, impChar, hcA, hcC]]
  have hp : HasPullback S_ant.arr (Subobject.entire (prod A (prod A A))).arr := HasPullbacks.has _ _
  -- pointwise S_ant ≤ S_con: on the carrier, (a,b)∈T0 and (b,c)∈T0, so (a,c)∈T0 by transitivity.
  have hle : S_ant.le S_con := by
    apply (allows_iff_classify S_con S_ant.arr).2
    rw [show HasSubobjectClassifier.classify S_con.arr S_con.monic = subChar S_con from rfl, hcC]
    -- carrier k := S_ant.arr.  Its three coords a=k≫pa, b=k≫pb, c=k≫pc.
    -- k ≫ χ_ant = ⊤  ⟹  k ≫ (pab) = ⊤  and  k ≫ (pbc) = ⊤.
    have hcar : S_ant.arr ≫ subChar S_ant
        = term S_ant.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) :=
      HasSubobjectClassifier.classify_sq S_ant.arr S_ant.monic
    rw [hcA] at hcar
    obtain ⟨hpab, hpbc⟩ := (meet_true_iff_and (pair pa pb ≫ subChar T0)
      (pair pb pc ≫ subChar T0) S_ant.arr).1 hcar
    -- (a,b) ∈ T0 and (b,c) ∈ T0 as factorizations through T0.
    -- rewrite to pair-of-coords form to feed mem_compose_of_legs.
    have eab : S_ant.arr ≫ pair pa pb = pair (S_ant.arr ≫ pa) (S_ant.arr ≫ pb) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair]
    have ebc : S_ant.arr ≫ pair pb pc = pair (S_ant.arr ≫ pb) (S_ant.arr ≫ pc) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair]
    have eac : S_ant.arr ≫ pair pa pc = pair (S_ant.arr ≫ pa) (S_ant.arr ≫ pc) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair]
    have hAab : Allows T0 (pair (S_ant.arr ≫ pa) (S_ant.arr ≫ pb)) := by
      apply (allows_iff_classify T0 _).2
      rw [← eab, Cat.assoc]; exact hpab
    have hAbc : Allows T0 (pair (S_ant.arr ≫ pb) (S_ant.arr ≫ pc)) := by
      apply (allows_iff_classify T0 _).2
      rw [← ebc, Cat.assoc]; exact hpbc
    -- (a,c) ∈ T0⊚T0 (mem_compose_of_legs), and T0⊚T0 ⊑ T0 (htr), so (a,c) ∈ T0.
    have hT0arr : (relSub (subToRel T0)).arr = T0.arr := relSub_subToRel_arr T0
    have hcomp := mem_compose_of_legs (subToRel T0) (S_ant.arr ≫ pa) (S_ant.arr ≫ pb)
      (S_ant.arr ≫ pc)
      (by obtain ⟨g, hg⟩ := hAab; exact ⟨g, by rw [hT0arr]; exact hg⟩)
      (by obtain ⟨g, hg⟩ := hAbc; exact ⟨g, by rw [hT0arr]; exact hg⟩)
    -- transfer along htr : (subToRel T0)⊚(subToRel T0) ⊑ subToRel T0, at the subobject level.
    have hsubLe := subLe_of_relLe htr
    obtain ⟨w, hw⟩ := hcomp
    obtain ⟨z, hz⟩ := hsubLe
    have hAac : Allows T0 (pair (S_ant.arr ≫ pa) (S_ant.arr ≫ pc)) := by
      refine ⟨w ≫ z, ?_⟩
      -- (relSub (subToRel T0)).arr = T0.arr (relSub_subToRel_arr); chain the factorizations.
      rw [show T0.arr = (relSub (subToRel T0)).arr from (relSub_subToRel_arr T0).symm]
      rw [Cat.assoc, hz, hw]
    -- conclude S_ant.arr ≫ (pac ≫ χ_T0) = ⊤.
    rw [← Cat.assoc, eac]
    exact (allows_iff_classify T0 (pair (S_ant.arr ≫ pa) (S_ant.arr ≫ pc))).1 hAac
  have hentireLe : (Subobject.entire (prod A (prod A A))).le (Sub.imp S_ant S_con) := by
    rw [imp_adjunction S_ant S_con (Subobject.entire (prod A (prod A A))) hp]
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_ant (Subobject.entire (prod A (prod A A))) hp
    obtain ⟨h₂, e₂⟩ := hle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  have hcl := (le_iff_classify (Subobject.entire (prod A (prod A A)))
    (Sub.imp S_ant S_con)).mp hentireLe
  show subChar (Sub.imp S_ant S_con)
      = term (prod A (prod A A)) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [show (Subobject.entire (prod A (prod A A))).arr ≫ subChar (Sub.imp S_ant S_con)
        = subChar (Sub.imp S_ant S_con) from Cat.id_comp _] at hcl
  rw [hcl]
  congr 1

/-- **`minimal` field — `R*` is the LEAST reflexive-transitive relation containing `R`.**
    Any reflexive-transitive `T ⊇ R` has its name `'relSub T'` passing all three conjuncts
    of `rtcChar`, so it is a member of `F_R`; `bigInter_le_named` gives `⋂F_R ⊑ T`. -/
public theorem rtcClos_minimal {A : 𝒞} (R : BinRel 𝒞 A A) (T : BinRel 𝒞 A A)
    (hRT : RelLe R T) (hrefl : IsReflexive T) (htr : IsTransitive T) :
    RelLe (rtcClos R) T := by
  rw [rtcClos]
  rw [show T = subToRel (relSub T) from (subToRel_relSub T).symm]
  rw [relLe_subToRel_iff_subLe, rtcSub]
  -- 'relSub T' is a member: passes refl ∧ containsR ∧ trans.
  apply bigInter_le_named (rtcFamily (rName R)) (relSub T)
  rw [membershipMap_rtcFamily, rtcChar]
  apply (meet_true_iff_and _ (transChar (A := A)) (nameOf (relSub T).arr (relSub T).monic)).2
  refine ⟨?_, ?_⟩
  · apply (meet_true_iff_and (reflChar (A := A)) (containsRChar (rName R))
      (nameOf (relSub T).arr (relSub T).monic)).2
    refine ⟨?_, ?_⟩
    · -- reflChar: Δ ⊑ relSub T  from  IsReflexive T.
      apply reflChar_name_of_diag_le (relSub T)
      exact subLe_of_relLe hrefl
    · -- containsR: relSub R ⊑ relSub T  from  RelLe R T.
      exact containsRChar_name_of_le (relSub R) (relSub T) (subLe_of_relLe hRT)
  · -- transChar: IsTransitive (subToRel (relSub T)) = IsTransitive T.
    apply transChar_name_of_transitive (relSub T)
    rw [subToRel_relSub]; exact htr

/-! ## §1.943  the glb of (reflexive-)transitive relations is transitive -/

/-- **A point of `⋂F` lies in any member (membership-map form).**  For `p : K → A×A` in
    `⋂F` (`p ≫ bigInterChar F = ⊤`) and `σ : K → [A×A]` a member (`σ ≫ membershipMap F = ⊤`),
    `memLk p σ = ⊤`.  Adapts `bigInter_point_in_member` (which produces the swapped form). -/
public theorem mem_member_of_mem_bigInter {A K : 𝒞} (Fname : one ⟶ powObj (powObj (prod A A)))
    (p : K ⟶ prod A A) (σ : K ⟶ powObj (prod A A))
    (hp : p ≫ bigInterChar Fname = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
    (hmem : σ ≫ membershipMap Fname = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) :
    memLk p σ = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  have h := bigInter_point_in_member Fname p σ hp hmem
  rw [memLk, ← h, ← Cat.assoc]
  congr 1
  symm
  apply pair_uniq
  · rw [Cat.assoc, fst_pair, snd_pair]
  · rw [Cat.assoc, snd_pair, fst_pair]

/-- **`trans` field — `R*` is transitive.**  The glb `⋂F_R` of (reflexive-)transitive
    relations is transitive.  Via `relLe_of_cover_factor` over the image-cover of the
    composition span: on the pullback `pb` (with explicit middle `b`), the composite point
    `(a,c)` lies in `⋂F_R` because for EVERY member `σ` we have `(a,b),(b,c) ∈ σ`
    (`mem_member_of_mem_bigInter`) and `σ` is transitive (`transChar_gen`), so `(a,c) ∈ σ`. -/
public theorem rtcClos_trans {A : 𝒞} (R : BinRel 𝒞 A A) : IsTransitive (rtcClos R) := by
  rw [IsTransitive]
  -- The composition pullback and span (matching `compose`'s definition).
  let clos := rtcClos R
  let pb := HasPullbacks.has clos.colB clos.colA
  let span : pb.cone.pt ⟶ prod A A := pair (pb.cone.π₁ ≫ clos.colA) (pb.cone.π₂ ≫ clos.colB)
  -- the three explicit points on the pullback carrier.
  let a : pb.cone.pt ⟶ A := pb.cone.π₁ ≫ clos.colA
  let b : pb.cone.pt ⟶ A := pb.cone.π₁ ≫ clos.colB
  let c : pb.cone.pt ⟶ A := pb.cone.π₂ ≫ clos.colB
  have hmid : b = pb.cone.π₂ ≫ clos.colA := pb.cone.w
  -- `(a,c)` lies in `⋂F_R = rtcSub R`: every member contains both legs, and is transitive.
  have hac : Allows (rtcSub R) (pair a c) := by
    rw [rtcSub]
    apply allows_bigInter_of_carrier (pair a c) (rtcFamily (rName R))
    intro K k hk
    -- σ := k≫fst (member), the composite point is f∘(k≫snd) = pair a c ∘ (k≫snd).
    rw [← Cat.assoc, membershipMap_rtcFamily] at hk
    obtain ⟨_, _, htrans⟩ := rtcChar_conjuncts (rName R) (k ≫ fst) hk
    -- the three points along k≫snd.
    let kσ : K ⟶ powObj (prod A A) := k ≫ fst
    let ka : K ⟶ A := (k ≫ snd) ≫ a
    let kb : K ⟶ A := (k ≫ snd) ≫ b
    let kc : K ⟶ A := (k ≫ snd) ≫ c
    -- (a,b) and (b,c) are points of ⋂F (factor through (rtcSub R).arr).
    have hcar := bigInter_carrier_true (rtcFamily (rName R))
    -- (rtcSub R).arr = pair clos.colA clos.colB  (clos = subToRel (rtcSub R)).
    have harr : (rtcSub R).arr = pair clos.colA clos.colB := (relSub_subToRel_arr (rtcSub R)).symm
    have hInAB : memLk (pair ka kb) kσ = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      apply mem_member_of_mem_bigInter (rtcFamily (rName R)) (pair ka kb) kσ ?_ ?_
      · -- pair ka kb = (k≫snd) ≫ pb.π₁ ≫ (rtcSub R).arr ∈ ⋂F.
        have hpt : pair ka kb = ((k ≫ snd) ≫ pb.cone.π₁) ≫ (rtcSub R).arr := by
          rw [harr, Cat.assoc]
          symm
          apply pair_uniq
          · show ((k ≫ snd) ≫ pb.cone.π₁ ≫ pair clos.colA clos.colB) ≫ fst = ka
            show _ = (k ≫ snd) ≫ pb.cone.π₁ ≫ clos.colA
            simp only [Cat.assoc, fst_pair]
          · show ((k ≫ snd) ≫ pb.cone.π₁ ≫ pair clos.colA clos.colB) ≫ snd = kb
            show _ = (k ≫ snd) ≫ pb.cone.π₁ ≫ clos.colB
            simp only [Cat.assoc, snd_pair]
        rw [hpt, Cat.assoc, show (rtcSub R).arr ≫ bigInterChar (rtcFamily (rName R))
              = term (rtcSub R).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) from hcar]
        rw [← Cat.assoc, term_uniq (((k ≫ snd) ≫ pb.cone.π₁) ≫ term (rtcSub R).dom) (term K)]
      · show (k ≫ fst) ≫ membershipMap (rtcFamily (rName R)) = _
        rw [membershipMap_rtcFamily]; exact hk
    have hInBC : memLk (pair kb kc) kσ = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      apply mem_member_of_mem_bigInter (rtcFamily (rName R)) (pair kb kc) kσ ?_ ?_
      · have hpt : pair kb kc = ((k ≫ snd) ≫ pb.cone.π₂) ≫ (rtcSub R).arr := by
          rw [harr, Cat.assoc]
          symm
          apply pair_uniq
          · show ((k ≫ snd) ≫ pb.cone.π₂ ≫ pair clos.colA clos.colB) ≫ fst = kb
            show _ = (k ≫ snd) ≫ b
            rw [hmid]
            simp only [Cat.assoc, fst_pair]
          · show ((k ≫ snd) ≫ pb.cone.π₂ ≫ pair clos.colA clos.colB) ≫ snd = kc
            show _ = (k ≫ snd) ≫ pb.cone.π₂ ≫ clos.colB
            simp only [Cat.assoc, snd_pair]
        rw [hpt, Cat.assoc, show (rtcSub R).arr ≫ bigInterChar (rtcFamily (rName R))
              = term (rtcSub R).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) from hcar]
        rw [← Cat.assoc, term_uniq (((k ≫ snd) ≫ pb.cone.π₂) ≫ term (rtcSub R).dom) (term K)]
      · show (k ≫ fst) ≫ membershipMap (rtcFamily (rName R)) = _
        rw [membershipMap_rtcFamily]; exact hk
    -- σ is transitive: (a,c) ∈ σ.
    have hac := transChar_gen kσ ka kb kc
      (by show (k ≫ fst) ≫ transChar (A := A) = _; exact htrans) hInAB hInBC
    -- repackage into the hci goal shape (pair (snd ≫ f) fst).
    rw [memLk] at hac
    rw [← hac, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc]
      apply pair_uniq
      · show ((k ≫ snd) ≫ pair a c) ≫ fst = ka
        rw [Cat.assoc, fst_pair]
      · show ((k ≫ snd) ≫ pair a c) ≫ snd = kc
        rw [Cat.assoc, snd_pair]
    · rw [Cat.assoc, snd_pair]
  -- assemble the RelHom via the image-cover descent.
  obtain ⟨φ, hφ⟩ := hac
  refine relLe_of_cover_factor (image.lift span) (image_lift_cover span) φ ?_ ?_
  · -- φ ≫ clos.colA = image.lift span ≫ (clos⊚clos).colA = a.
    have hrhs : image.lift span ≫ (clos ⊚ clos).colA = a := by
      show image.lift span ≫ ((image span).arr ≫ fst) = _
      rw [← Cat.assoc, image.lift_fac]; exact fst_pair _ _
    rw [hrhs]
    show φ ≫ clos.colA = a
    have := congrArg (· ≫ fst) hφ
    simpa [Cat.assoc, fst_pair] using this
  · have hrhs : image.lift span ≫ (clos ⊚ clos).colB = c := by
      show image.lift span ≫ ((image span).arr ≫ snd) = _
      rw [← Cat.assoc, image.lift_fac]; exact snd_pair _ _
    rw [hrhs]
    show φ ≫ clos.colB = c
    have := congrArg (· ≫ snd) hφ
    simpa [Cat.assoc, snd_pair] using this

/-- **§1.943 — the reflexive-transitive closure `R*` of `R`**, packaged. -/
@[expose] public noncomputable def rtcTransRefClos {A : 𝒞} (R : BinRel 𝒞 A A) : TransRefClos R where
  clos    := rtcClos R
  le      := rtcClos_le R
  refl    := rtcClos_refl R
  trans   := rtcClos_trans R
  minimal := rtcClos_minimal R

/-- **§1.947 — every topos HAS reflexive-transitive closures.**  For every endo-relation `R`,
    its RTC is the §1.943 internal-∀ family-glb `subToRel (⋂{ s | 1⊑s ∧ R⊑s ∧ s⊚s⊑s })` over a
    subobject family of `[A×A]`, built Sorry-free via `bigInter` (NO §1.54 transfinite
    capitalization).  The transitivity predicate is the fibered-∀ `∀a b c. aSb∧bSc ⇒ aSc`
    (no internal `∃`/relational composition).  This discharges the `HasReflTransClosure 𝒞`
    hypothesis for a bare topos, unblocking `topos_has_coequalizers`/`topos_is_bicartesian`. -/
@[expose] public noncomputable instance toposHasReflTransClosure : HasReflTransClosure 𝒞 where
  transRefClos R := rtcTransRefClos R

end

end Freyd
