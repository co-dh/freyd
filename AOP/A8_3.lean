/-
  Bird & de Moor, *Algebra of Programming* §8.3  Implementing `thin` (book pp. 199-203).

  §8.1's `thin Q` shrinks a SET of partial solutions.  §8.3 keeps the candidates in a
  `P`-sorted LIST instead and replaces `thin Q` by `thinlist Q`, one linear pass over that
  list.  What makes the swap legal is the interface (8.6)-(8.11).  The book ASSUMES
  (8.7)-(8.11) of an implementation and PROVES (8.6) from the two conditions it imposes on
  `thinlist Q` — it only drops elements (`thinlist Q ⊑ subseq`) and it implements `thin Q` on
  the underlying set.  The same split is kept here: (8.6) is a theorem, (8.7)-(8.11) are
  hypotheses, and Lemma 8.1, THEOREM 8.2 and Theorem 8.2's fusion side condition follow.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`):
  - `sort P = ordered P·setify°` is `sortRel setify ordered = setify° ≫ ordered`.
  - `thin Q` is `AOP.A8_1`'s `thinRel Q` (the `°` folded into the argument) and `min R°` is
    `AOP.A7_1`'s `est R`; `E`/`P` are `existsImage`/`powerRel`; `cp(F)` is `AOP.A5_6`'s
    `cpMap F` and `cup` `AOP.A5_6`'s `cup`; `⟨g₁,g₂⟩` is `RelProd.pair g₁ g₂` and
    `sort P×sort P` is `prodMap _ _ sortP sortP` (`AOP.A5_2`).
  - The list object `[A]` is an ABSTRACT object `l`, and every list combinator (`ordered P`,
    `subseq`, `thinlist Q`, `filter p`, `list f`, `listcp(F)`, `merge P`, `minlist R`) an
    abstract arrow constrained only through the laws it is used by — the book's own level of
    generality.  `AOP.A5_6_ListCombinators` is the `Rel`-instance of the same vocabulary.

  ASSUMED BEYOND THE BOOK.  (8.6)'s proof needs "a subsequence of a `P`-ordered list is
  `P`-ordered" in the composable form `ordered P ≫ subseq ⊑ subseq ≫ ordered P`; the book
  prints the weaker-looking `subseq·ordered P ⊑ ordered P`, which is false read literally (it
  would force the subsequence to be the whole list).  Lemma 8.1 is stated with `f : FA ⟶ A`,
  not the note's `f : FA ⟶ B`: `FP ⊑ f·P·f°` compares `F` of `P`-on-`A` with `f·(P-on-B)·f°`,
  so the two orders are the same relation and `A = B`.
-/
module

public import AOP.A8_2
-- (8.5) is the one law of `<thinlist-laws>` that is NOT abstract: it needs `bump Q` and
-- `minlist Q` written out on a concrete list, hence the cons-list algebra and `est`'s
-- pointwise reading.
public import AOP.A6_ConsList
public import AOP.A7_4_Horner

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A l : 𝒜}

/-! ## `sort P` and (8.6) -/

/-- `sort P ≜ ordered P·setify°` (book p.199), mirrored `setify° ≫ ordered P`: read the set
    back as one of its `P`-ordered listings.  `l` is the list object `[A]` and
    `setify : [A] ⟶ EA` the map that forgets the order. -/
@[expose] public def sortRel (setify : l ⟶ PowerAllegory.powerObj A) (ordered : l ⟶ l) :
    PowerAllegory.powerObj A ⟶ l := setify° ≫ ordered

/-! ### The steps of the p.201 argument

  `sort P g = setify° ordered P g ⊑ setify° g ordered P ⊑ T setify° ordered P = T sort P`.  The
  outer two steps are the unfolding of `sort P`; the inner two carry the argument and are stated
  here, ahead of their first use, for any combinator `g` that only drops elements and implements
  `T` on the underlying set.  `sortRel_comp_le` below is their composition, (8.6) and (8.9) its
  instances, so the argument is written once. -/

/-- Step 1: `g` only drops elements (`g ⊑ subseq`) and a subsequence of a `P`-ordered list is
    `P`-ordered, so `g` may run before the order test. -/
public theorem sortRel_comp_le_step1 (setify : l ⟶ PowerAllegory.powerObj A)
    {ordered subseq g : l ⟶ l} (hord : Coreflexive ordered) (hsub : g ⊑ subseq)
    (hos : ordered ≫ subseq ⊑ subseq ≫ ordered) :
    setify° ≫ ordered ≫ g ⊑ setify° ≫ g ≫ ordered := by
  refine comp_mono_left _ ?_
  have h1 : ordered ≫ g ⊑ subseq ≫ ordered := le_trans (comp_mono_left _ hsub) hos
  have h2 : ordered ≫ g ⊑ g := by
    have := comp_mono_right hord g
    rwa [Cat.id_comp] at this
  have h3 := le_inter h1 h2
  rw [coreflexive_comp_inter hord subseq g] at h3
  exact le_trans h3 (comp_mono_right (inter_lb_right _ _) ordered)

/-- Step 2: `·setify ⊣ ·setify°` shunts `g`'s specification `g·setify ⊑ setify·T` across the
    converse. -/
public theorem sortRel_comp_le_step2 {setify : l ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    (ordered : l ⟶ l) {g : l ⟶ l}
    {T : PowerAllegory.powerObj A ⟶ PowerAllegory.powerObj A} (hspec : g ≫ setify ⊑ setify ≫ T) :
    setify° ≫ g ≫ ordered ⊑ T ≫ setify° ≫ ordered := by
  have hshunt : setify° ≫ g ⊑ T ≫ setify° := by
    refine (map_shunt_left hset g _).mpr ?_
    have hent : g ⊑ g ≫ setify ≫ setify° := by
      have := comp_mono_left g (entire_id_le hset.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc g setify (setify°), ← Cat.assoc setify T (setify°)]
    exact comp_mono_right hspec _
  rw [← Cat.assoc (setify°) g ordered, ← Cat.assoc T (setify°) ordered]
  exact comp_mono_right hshunt ordered

/-! ### (8.6)'s chain, spelled with `thinlist Q` and `thin Q`

  Only the ends of the chain and the shunt name the combinator; the step between them is
  `sortRel_comp_le_step1` at `g ≜ thinlist Q`, whose statement it is verbatim. -/

/-- Step 1: `sort P ≜ ordered P·setify°` unfolded. -/
public theorem sortRel_comp_thinlist_le_step1 (setify : l ⟶ PowerAllegory.powerObj A)
    (ordered thinlist : l ⟶ l) :
    sortRel setify ordered ≫ thinlist = setify° ≫ ordered ≫ thinlist := by
  show (setify° ≫ ordered) ≫ thinlist = setify° ≫ ordered ≫ thinlist
  exact Cat.assoc _ _ _

/-- Step 2: `thinlist Q·setify ⊑ setify·thin Q` shunted across `setify°`. -/
public theorem sortRel_comp_thinlist_le_step2 {setify : l ⟶ PowerAllegory.powerObj A}
    (hset : Map setify) (ordered : l ⟶ l) {thinlist : l ⟶ l} {Q : A ⟶ A}
    (hspec : thinlist ≫ setify ⊑ setify ≫ thinRel Q) :
    setify° ≫ thinlist ≫ ordered ⊑ thinRel Q ≫ setify° ≫ ordered :=
  sortRel_comp_le_step2 hset ordered hspec

/-- Step 3: `sort P` folded back. -/
public theorem sortRel_comp_thinlist_le_step3 (setify : l ⟶ PowerAllegory.powerObj A)
    (ordered : l ⟶ l) {Q : A ⟶ A} :
    thinRel Q ≫ setify° ≫ ordered = thinRel Q ≫ sortRel setify ordered := rfl

/-- **(8.6)** (book p.201): a thinning of the sorted list lists a thinning of the set,
    `sort P·thinlist Q ⊑ thin Q·sort P` mirrored to
    `sortRel setify ordered ≫ thinlist ⊑ thinRel Q ≫ sortRel setify ordered`.  The two
    conditions on `thinlist Q` do all the work: `thinlist Q ⊑ subseq` lets the thinning run
    before the order test, and `thinlist Q·setify ⊑ setify·thin Q` shunts across `setify°`. -/
public theorem sortRel_comp_thinlist_le
    {setify : l ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    {ordered subseq thinlist : l ⟶ l} {Q : A ⟶ A}
    (hord : Coreflexive ordered) (hsub : thinlist ⊑ subseq)
    (hos : ordered ≫ subseq ⊑ subseq ≫ ordered)
    (hspec : thinlist ≫ setify ⊑ setify ≫ thinRel Q) :
    sortRel setify ordered ≫ thinlist ⊑ thinRel Q ≫ sortRel setify ordered :=
  le_trans (le_of_eq (sortRel_comp_thinlist_le_step1 setify ordered thinlist))
    (le_trans (le_trans (sortRel_comp_le_step1 setify hord hsub hos)
        (sortRel_comp_thinlist_le_step2 hset ordered hspec))
      (le_of_eq (sortRel_comp_thinlist_le_step3 setify ordered)))

/-! ## Lemma 8.1 (book p.202) -/

variable {F : Relator 𝒜 𝒜}

-- The list object `[F(A)]` that the cartesian product `listcp` lands in.  It is indexed by the
-- section's own `F` and not by a relator argument: §8.4-8.6 instantiate this chapter at one
-- relator each, and an arrow indexed by a relator would make every one of them carry the family.
variable {lF : 𝒜}

/-- **Lemma 8.1** (book p.202): one sorted list built from sorted arguments, instead of a set
    built and then sorted —
    `filter p·list f·listcp(F)·F(sort P) ⊑ sort P·Λ(p·f·F∈)`, mirrored to
    `F(sort P) ≫ listcp ≫ list f ≫ filter p ⊑ Λ (F(∋) ≫ f ≫ p) ≫ sort P`.
    The sort walks inwards: past `filter p` by (8.9), past `list f` by (8.8), under `F` by
    (8.11), with `f` monotonic on `P` (`FP ⊑ f·P·f°`) closing the change of order. -/
public theorem map_sort_comp_listcp_le
    {f : F.obj A ⟶ A} (hf : Map f) {p P : A ⟶ A}
    {sort : (A ⟶ A) → (PowerAllegory.powerObj A ⟶ l)}
    {sortF : (F.obj A ⟶ F.obj A) → (PowerAllegory.powerObj (F.obj A) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf : lF ⟶ l} {filterp : l ⟶ l}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono : MonotonicAlg f P)
    (h88 : sortF (f ≫ P ≫ f°) ≫ listf ⊑ powerRel f ≫ sort P)
    (h89 : sort P ≫ filterp ⊑ existsImage p ≫ sort P)
    (h811 : F.map (sort P) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map P)) :
    F.map (sort P) ≫ listcp ≫ listf ≫ filterp ⊑ Λ (F.map (∋ A) ≫ f ≫ p) ≫ sort P := by
  -- (8.11): the sort goes under `F`
  have s1 : F.map (sort P) ≫ listcp ≫ listf ≫ filterp
      ⊑ cpMap F A ≫ sortF (F.map P) ≫ listf ≫ filterp := by
    rw [← Cat.assoc, ← Cat.assoc (cpMap F A)]
    exact comp_mono_right h811 _
  -- `f` monotonic on `P`, and `sort` grows with its order
  have s2 : cpMap F A ≫ sortF (F.map P) ≫ listf ≫ filterp
      ⊑ cpMap F A ≫ sortF (f ≫ P ≫ f°) ≫ listf ≫ filterp :=
    comp_mono_left _ (comp_mono_right (hsortF ((monotonicAlg_iff_sandwich hf).mp hmono)) _)
  -- (8.8): the sort walks past `list f`
  have s3 : cpMap F A ≫ sortF (f ≫ P ≫ f°) ≫ listf ≫ filterp
      ⊑ cpMap F A ≫ powerRel f ≫ sort P ≫ filterp := by
    refine comp_mono_left _ ?_
    rw [← Cat.assoc, ← Cat.assoc (powerRel f)]
    exact comp_mono_right h88 filterp
  -- (8.9): the sort walks past `filter p`
  have s4 : cpMap F A ≫ powerRel f ≫ sort P ≫ filterp
      ⊑ cpMap F A ≫ powerRel f ≫ existsImage p ≫ sort P :=
    comp_mono_left _ (comp_mono_left _ h89)
  -- `E` is a functor and agrees with `P` on maps; the power transpose of a composition
  have s5 : cpMap F A ≫ powerRel f ≫ existsImage p ≫ sort P
      = Λ (F.map (∋ A) ≫ f ≫ p) ≫ sort P := by
    rw [powerRel_map hf, ← Cat.assoc (existsImage f), ← existsImage_comp, ← Cat.assoc,
        show cpMap F A = Λ (F.map (∋ A)) from rfl, Λ_absorption]
  rw [← s5]
  exact le_trans s1 (le_trans s2 (le_trans s3 s4))

/-! ## THEOREM 8.2 (book p.203) and its fusion side condition

  BINARY THINNING DATA (book p.203): `S = (f₁p₁) ∪ (f₂p₂)` with `p₁`, `p₂` coreflexive; `Q` a
  preorder with `Q ⊑ R` and both `f₁p₁`, `f₂p₂` monotonic on `Q`; `P` a connected preorder
  with both `f₁`, `f₂` monotonic on `P`; `gᵢ = list fᵢ·filter pᵢ`.  Connectedness of `P` and
  coreflexivity of the `pᵢ` enter only through the laws (8.6)-(8.11) they are there to make
  true, so they are not separate hypotheses below. -/

/-- **The fusion side condition of THEOREM 8.2** (book p.203): sorting the candidate set is
    what turns the thinning algebra into an algebra on lists,
    `thin Q·Λ(F∈·S)·sort P ⊒ thinlist Q·merge P·⟨g₁,g₂⟩·listcp(F)·F(sort P)` mirrored to
    `F(sort P) ≫ listcp ≫ ⟨g₁,g₂⟩ ≫ merge P ≫ thinlist Q ⊑ Λ (F(∋) ≫ S) ≫ thin Q ≫ sort P`.
    (8.6) exchanges `thin Q` for `thinlist Q`; `cup` splits `Λ` of the union of the two
    algebras; (8.10) exchanges the union of the two sorted lists for `merge P`; and Lemma 8.1
    at `f₁,p₁` and at `f₂,p₂` puts the sort back inside `F`. -/
public theorem sortedAlg_fusion
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ P Q : A ⟶ A}
    {sort : (A ⟶ A) → (PowerAllegory.powerObj A ⟶ l)}
    {sortF : (F.obj A ⟶ F.obj A) → (PowerAllegory.powerObj (F.obj A) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l}
    {filterp₁ filterp₂ : l ⟶ l} {thinlist : (A ⟶ A) → (l ⟶ l)}
    {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj A) (PowerAllegory.powerObj A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ l)}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : MonotonicAlg f₁ P) (hmono₂ : MonotonicAlg f₂ P)
    (h88₁ : sortF (f₁ ≫ P ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort P)
    (h88₂ : sortF (f₂ ≫ P ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort P)
    (h89₁ : sort P ≫ filterp₁ ⊑ existsImage p₁ ≫ sort P)
    (h89₂ : sort P ≫ filterp₂ ⊑ existsImage p₂ ≫ sort P)
    (h811 : F.map (sort P) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map P))
    (h810 : prodMap Pr' Pr (sort P) (sort P) ≫ merge P ⊑ cup Pr' ≫ sort P)
    (h86 : sort P ≫ thinlist Q ⊑ thinRel Q ≫ sort P) :
    F.map (sort P) ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)
        ≫ merge P ≫ thinlist Q
      ⊑ Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q ≫ sort P := by
  have l1 : (F.map (sort P) ≫ listcp) ≫ (listf₁ ≫ filterp₁)
      ⊑ Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort P := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le hf₁ hsortF hmono₁ h88₁ h89₁ h811
  have l2 : (F.map (sort P) ≫ listcp) ≫ (listf₂ ≫ filterp₂)
      ⊑ Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort P := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le hf₂ hsortF hmono₂ h88₂ h89₂ h811
  -- Lemma 8.1 under the common prefix `F(sort P)·listcp(F)`, at each `fᵢ`, `pᵢ`
  have pre : F.map (sort P) ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)
        ≫ merge P ≫ thinlist Q
      ⊑ Pr.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort P) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort P)
        ≫ merge P ≫ thinlist Q := by
    rw [← Cat.assoc (F.map (sort P)) (listcp)
          (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ merge P ≫ thinlist Q),
        ← Cat.assoc (F.map (sort P) ≫ listcp)
          (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)) (merge P ≫ thinlist Q)]
    exact comp_mono_right
      (le_trans (RelProd.comp_pair_le _ _ _) (RelProd.pair_mono l1 l2)) _
  -- `Λ` of the union is the pair of the two transposes, closed by `cup`
  have hsplit : Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)))
      = Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂)) ≫ cup Pr' := by
    rw [DistributiveAllegory.comp_union_distrib, Λ_union]
  have key : Pr.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort P) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort P)
        ≫ merge P ≫ thinlist Q
      ⊑ Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q ≫ sort P := by
    rw [hsplit, ← RelProd.pair_prodMap (P := Pr') (Q := Pr)
          (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂)) (sort P) (sort P),
        Cat.assoc (Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂)))
          (prodMap Pr' Pr (sort P) (sort P)) (merge P ≫ thinlist Q),
        Cat.assoc (Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂)))
          (cup Pr') (thinRel Q ≫ sort P)]
    refine comp_mono_left _ ?_
    have a1 : prodMap Pr' Pr (sort P) (sort P) ≫ merge P ≫ thinlist Q
        ⊑ (cup Pr' ≫ sort P) ≫ thinlist Q := by
      rw [← Cat.assoc (prodMap Pr' Pr (sort P) (sort P)) (merge P) (thinlist Q)]
      exact comp_mono_right h810 (thinlist Q)
    have a2 : (cup Pr' ≫ sort P) ≫ thinlist Q ⊑ cup Pr' ≫ thinRel Q ≫ sort P := by
      rw [Cat.assoc (cup Pr') (sort P) (thinlist Q)]
      exact comp_mono_left _ h86
    exact le_trans a1 a2
  exact le_trans pre key

/-! ### THEOREM 8.2's three steps

  `⦇−thinlist Q⦈minlist R ⊑ ⦇(F(∋)S)%∋ thin Q⦈sort P minlist R ⊑ ⦇(F(∋)S)%∋ thin Q⦈est R
   ⊑ ⦇S⦈%∋ est R`, at `S ≜ f₁p₁∪f₂p₂`; `thinningList` is their composition. -/

/-- Step 1: `relCata_le_comp` fuses `sort P` into the algebra, its side condition being
    `sortedAlg_fusion` — the fold on sorted lists refines the fold on thinned sets, read sorted. -/
public theorem thinningList_step1 (I : InitialAlgebra F)
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ P Q R : A ⟶ A}
    {sort : (A ⟶ A) → (PowerAllegory.powerObj A ⟶ l)}
    {sortF : (F.obj A ⟶ F.obj A) → (PowerAllegory.powerObj (F.obj A) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf₁ listf₂ g₁ g₂ : lF ⟶ l}
    {filterp₁ filterp₂ : l ⟶ l} {thinlist : (A ⟶ A) → (l ⟶ l)}
    {minlist : (A ⟶ A) → (l ⟶ A)} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj A) (PowerAllegory.powerObj A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ l)}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : MonotonicAlg f₁ P) (hmono₂ : MonotonicAlg f₂ P)
    (h88₁ : sortF (f₁ ≫ P ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort P)
    (h88₂ : sortF (f₂ ≫ P ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort P)
    (h89₁ : sort P ≫ filterp₁ ⊑ existsImage p₁ ≫ sort P)
    (h89₂ : sort P ≫ filterp₂ ⊑ existsImage p₂ ≫ sort P)
    (h811 : F.map (sort P) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map P))
    (h810 : prodMap Pr' Pr (sort P) (sort P) ≫ merge P ⊑ cup Pr' ≫ sort P)
    (h86 : sort P ≫ thinlist Q ⊑ thinRel Q ≫ sort P)
    (hg₁ : g₁ = listf₁ ≫ filterp₁) (hg₂ : g₂ = listf₂ ≫ filterp₂) :
    relCata (listcp ≫ Pr.pair g₁ g₂ ≫ merge P ≫ thinlist Q) ≫ minlist R
      ⊑ (relCata (Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q) ≫ sort P)
        ≫ minlist R := by
  subst hg₁
  subst hg₂
  refine comp_mono_right (relCata_le_comp I ?_) (minlist R)
  rw [Cat.assoc]
  exact sortedAlg_fusion hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811 h810 h86

/-- Step 2: (8.7) `sort P·minlist R ⊑ min R` reads the minimum off the sorted list. -/
public theorem thinningList_step2 (I : InitialAlgebra F) {S : F.obj A ⟶ A}
    {P Q R : A ⟶ A}
    {sort : (A ⟶ A) → (PowerAllegory.powerObj A ⟶ l)} {minlist : (A ⟶ A) → (l ⟶ A)}
    (h87 : sort P ≫ minlist R ⊑ est R) :
    (relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ sort P) ≫ minlist R
      ⊑ relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ est R :=
  le_trans (le_of_eq (Cat.assoc _ _ _)) (comp_mono_left _ h87)

/-- Step 3: Corollary 8.1 (`thinning_est`) at the union algebra — the union of two `Q`-monotonic
    algebras is `Q`-monotonic, which is the only hypothesis of it the union has to earn. -/
public theorem thinningList_step3 (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {f₁ f₂ : F.obj A ⟶ A} {p₁ p₂ Q R : A ⟶ A}
    (hQR : Q ⊑ R) (hreflQ : 𝟙 A ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hm₁ : MonotonicAlg (f₁ ≫ p₁) Q) (hm₂ : MonotonicAlg (f₂ ≫ p₂) Q) :
    relCata (Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q) ≫ est R
      ⊑ Λ (relCata ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ est R := by
  have hmonoS : MonotonicAlg ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) Q := by
    show F.map Q ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ⊑ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ≫ Q
    rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
    exact union_mono hm₁ hm₂
  exact thinning_est hFr I hQR hreflQ htransQ (trans_of_recip_trans htransR) hmonoS

/-- **THEOREM 8.2** (book p.203): a fold on SORTED LISTS of partial solutions, thinned at
    every step, refines the thinning specification —
    `min R·Λ⦇S⦈ ⊒ minlist R·⦇thinlist Q·merge P·⟨g₁,g₂⟩·listcp(F)⦈`, mirrored to
    `relCata (listcp(F) ≫ ⟨g₁,g₂⟩ ≫ merge P ≫ thinlist Q) ≫ minlist R ⊑ Λ ⦇S⦈ ≫ est R`.
    The specification's algebra is BOUND as `S` (`hS : S = f₁p₁ ∪ f₂p₂`), because that is the one
    letter the book and the note both write there and a conclusion spelling the union out reads as
    a different theorem from the one the picture draws.
    Corollary 8.1 (`thinning_est`) puts `thin Q` inside the fold, (8.7) splits the minimum
    into `sort P` followed by `minlist R`, and `relCata_le_comp` fuses `sort P` into the
    algebra — that fusion condition being `sortedAlg_fusion`.  No set is ever built. -/
public theorem thinningList (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ P Q R : A ⟶ A}
    {sort : (A ⟶ A) → (PowerAllegory.powerObj A ⟶ l)}
    {sortF : (F.obj A ⟶ F.obj A) → (PowerAllegory.powerObj (F.obj A) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf₁ listf₂ g₁ g₂ : lF ⟶ l}
    {filterp₁ filterp₂ : l ⟶ l} {thinlist : (A ⟶ A) → (l ⟶ l)}
    {minlist : (A ⟶ A) → (l ⟶ A)} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj A) (PowerAllegory.powerObj A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ l)}
    (hQR : Q ⊑ R) (hreflQ : 𝟙 A ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hm₁ : MonotonicAlg (f₁ ≫ p₁) Q) (hm₂ : MonotonicAlg (f₂ ≫ p₂) Q)
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : MonotonicAlg f₁ P) (hmono₂ : MonotonicAlg f₂ P)
    (h88₁ : sortF (f₁ ≫ P ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort P)
    (h88₂ : sortF (f₂ ≫ P ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort P)
    (h89₁ : sort P ≫ filterp₁ ⊑ existsImage p₁ ≫ sort P)
    (h89₂ : sort P ≫ filterp₂ ⊑ existsImage p₂ ≫ sort P)
    (h811 : F.map (sort P) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map P))
    (h810 : prodMap Pr' Pr (sort P) (sort P) ≫ merge P ⊑ cup Pr' ≫ sort P)
    (h86 : sort P ≫ thinlist Q ⊑ thinRel Q ≫ sort P)
    (h87 : sort P ≫ minlist R ⊑ est R)
    (hg₁ : g₁ = listf₁ ≫ filterp₁) (hg₂ : g₂ = listf₂ ≫ filterp₂) {S : F.obj A ⟶ A}
    (hS : S = (f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) :
    relCata (listcp ≫ Pr.pair g₁ g₂ ≫ merge P ≫ thinlist Q) ≫ minlist R
      ⊑ Λ (relCata S) ≫ est R := by
  subst hS
  exact le_trans
    (thinningList_step1 I hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811 h810 h86 hg₁ hg₂)
    (le_trans (thinningList_step2 I h87)
      (thinningList_step3 hFr I hQR hreflQ htransQ htransR hm₁ hm₂))

/-! ## The note's `thinlist-laws`: (8.7), (8.8) and (8.9) discharged

  `thinningList` above takes (8.5) and (8.7)-(8.11) as hypotheses.  Three of them are not
  interface conditions at all once `sort P` is unfolded to `ordered P·setify°`: they follow, in
  the book's own style for (8.6), from the two DEFINING properties of the combinator each one
  mentions.  Everything below is stated for `sortRel`, so it applies to any `setify`/`ordered`
  pair. -/

section SortLaws

variable {A L LF : 𝒜}

/-- **(8.6) and (8.9) are one law.**  A list combinator `g` that only DROPS elements
    (`g ⊑ subseq`) and that implements a set operation `T` on the underlying set
    (`g·setify ⊑ setify·T`) commutes with the sort: `sort P·g ⊑ T·sort P`.  (8.6) is the case
    `g ≜ thinlist Q`, `T ≜ thin Q` (`sortRel_comp_thinlist_le` above); (8.9) is `g ≜ filter p`,
    `T ≜ E p`.  The proof is the book's p.201 argument verbatim: `g` only drops elements and a
    subsequence of a `P`-ordered list is `P`-ordered, so `g` may run before the order test, and
    `·setify ⊣ ·setify°` shunts its specification across the converse. -/
public theorem sortRel_comp_le
    {setify : L ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    {ordered subseq g : L ⟶ L}
    {T : PowerAllegory.powerObj A ⟶ PowerAllegory.powerObj A}
    (hord : Coreflexive ordered) (hsub : g ⊑ subseq)
    (hos : ordered ≫ subseq ⊑ subseq ≫ ordered)
    (hspec : g ≫ setify ⊑ setify ≫ T) :
    sortRel setify ordered ≫ g ⊑ T ≫ sortRel setify ordered := by
  show (setify° ≫ ordered) ≫ g ⊑ T ≫ (setify° ≫ ordered)
  rw [Cat.assoc]
  exact le_trans (sortRel_comp_le_step1 setify hord hsub hos)
    (sortRel_comp_le_step2 hset ordered hspec)

/-- **(8.9)** (book p.203): `sort P·filter p ⊑ E p·sort P` — filtering a sorted list sorts the
    restricted set.  `filter p` drops elements and, on the underlying set, is `E p`; that is all
    the law says, so it is `sortRel_comp_le` at `T ≜ E p`. -/
public theorem sortRel_comp_filter_le
    {setify : L ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    {ordered subseq filterp : L ⟶ L} {p : A ⟶ A}
    (hord : Coreflexive ordered) (hsub : filterp ⊑ subseq)
    (hos : ordered ≫ subseq ⊑ subseq ≫ ordered)
    (hspec : filterp ≫ setify ⊑ setify ≫ existsImage p) :
    sortRel setify ordered ≫ filterp ⊑ existsImage p ≫ sortRel setify ordered :=
  sortRel_comp_le hset hord hsub hos hspec

/-- **(8.7)** (book p.203): `sort P·minlist R ⊑ min R`, mirrored
    `sortRel setify ordered ≫ minlist ⊑ est R` — a minimum of the sorted list is a minimum of the
    set.  The two defining properties of `minlist R` are what it comes to: the answer is an
    ELEMENT of the list (`minlist ⊑ setify·∋`), and it is `R`-below every element of the list
    (`(setify·∋)°·minlist ⊑ R°`).  `ordered` is dropped by coreflexivity and `setify` by
    simplicity, so the order plays no part. -/
public theorem sortRel_comp_minlist_le
    {setify : L ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    {ordered : L ⟶ L} {minlist : L ⟶ A} {R : A ⟶ A}
    (hord : Coreflexive ordered)
    (hmem : minlist ⊑ setify ≫ ∋ A)
    (hleast : (setify ≫ ∋ A)° ≫ minlist ⊑ R°) :
    sortRel setify ordered ≫ minlist ⊑ est R := by
  have hdrop : setify° ≫ ordered ≫ minlist ⊑ setify° ≫ minlist := by
    refine comp_mono_left _ ?_
    have := comp_mono_right hord minlist
    rwa [Cat.id_comp] at this
  refine le_est_iff.mpr ⟨?_, ?_⟩
  · show (setify° ≫ ordered) ≫ minlist ⊑ ∋ A
    rw [Cat.assoc]
    refine le_trans hdrop ?_
    refine le_trans (comp_mono_left _ hmem) ?_
    rw [← Cat.assoc (setify°) setify (∋ A)]
    have := comp_mono_right hset.2 (∋ A)
    rwa [Cat.id_comp] at this
  · show (∋ A)° ≫ (setify° ≫ ordered) ≫ minlist ⊑ R°
    rw [Cat.assoc]
    refine le_trans (comp_mono_left _ hdrop) ?_
    rw [← Cat.assoc ((∋ A)°) (setify°) minlist, ← Allegory.recip_comp]
    exact hleast

/-- **(8.8)** (book p.203): `sort(fPf°)·list f ⊑ P f·sort P`, mirrored
    `sortRel setifyF orderedFPf ≫ listf ⊑ powerRel f ≫ sortRel setify ordered` — shunt a function
    through a sort.  Again two defining properties: `setify` is natural in the list
    (`list f·setify ⊑ setifyF·E f`, so the shunt across `setifyF°` gives `E f·setify°`), and
    `list f` carries an `fPf°`-ordered list to a `P`-ordered one, which is where `f` monotonic on
    `P` enters. -/
public theorem sortRel_comp_listMap_le
    {setifyF : LF ⟶ PowerAllegory.powerObj A} (hsetF : Map setifyF)
    {B : 𝒜} {setify : L ⟶ PowerAllegory.powerObj B} (hset : Map setify)
    {orderedFPf : LF ⟶ LF} {ordered : L ⟶ L} {listf : LF ⟶ L} {f : A ⟶ B} (hf : Map f)
    (hnat : listf ≫ setify ⊑ setifyF ≫ existsImage f)
    (hordf : orderedFPf ≫ listf ⊑ listf ≫ ordered) :
    sortRel setifyF orderedFPf ≫ listf ⊑ powerRel f ≫ sortRel setify ordered := by
  have hshunt : setifyF° ≫ listf ⊑ existsImage f ≫ setify° := by
    refine (map_shunt_left hsetF listf _).mpr ?_
    have hent : listf ⊑ listf ≫ setify ≫ setify° := by
      have := comp_mono_left listf (entire_id_le hset.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc listf setify (setify°), ← Cat.assoc setifyF (existsImage f) (setify°)]
    exact comp_mono_right hnat _
  show (setifyF° ≫ orderedFPf) ≫ listf ⊑ powerRel f ≫ (setify° ≫ ordered)
  rw [Cat.assoc]
  refine le_trans (comp_mono_left _ hordf) ?_
  rw [← Cat.assoc (setifyF°) listf ordered, powerRel_map hf,
    ← Cat.assoc (existsImage f) (setify°) ordered]
  exact comp_mono_right hshunt ordered

/-- **(8.11)** (book p.203): `F(sort P)·listcp(F) ⊑ cp(F)·sort(FP)`, mirrored
    `F.map (sortRel setify ordered) ≫ listcp ⊑ cpMap F A ≫ sortRel setifyF orderedFP` —
    `listcp(F)` is the list implementation of the cartesian product.  Two defining properties
    again: on the underlying sets `listcp(F)` IS the cartesian product
    (`listcp·setifyF ⊑ F(setify)·cp(F)`), and it carries `F`-many `P`-ordered lists to an
    `FP`-ordered one.  A relator preserves a map and its converse (Lemma 5.1), which is what lets
    the `setify°` of the sort come out from under `F`. -/
public theorem map_sortRel_comp_listcp_le
    {setify : L ⟶ PowerAllegory.powerObj A} (hset : Map setify)
    {setifyF : LF ⟶ PowerAllegory.powerObj (F.obj A)} (hsetF : Map setifyF)
    {ordered : L ⟶ L} {orderedFP : LF ⟶ LF} {listcp : F.obj L ⟶ LF}
    (hnat : listcp ≫ setifyF ⊑ F.map setify ≫ cpMap F A)
    (hordcp : F.map ordered ≫ listcp ⊑ listcp ≫ orderedFP) :
    F.map (sortRel setify ordered) ≫ listcp ⊑ cpMap F A ≫ sortRel setifyF orderedFP := by
  have hshunt : (F.map setify)° ≫ listcp ⊑ cpMap F A ≫ setifyF° := by
    refine (map_shunt_left (F.map_is_map hset) listcp _).mpr ?_
    have hent : listcp ⊑ listcp ≫ setifyF ≫ setifyF° := by
      have := comp_mono_left listcp (entire_id_le hsetF.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc listcp setifyF (setifyF°), ← Cat.assoc (F.map setify) (cpMap F A) (setifyF°)]
    exact comp_mono_right hnat _
  show F.map (setify° ≫ ordered) ≫ listcp ⊑ cpMap F A ≫ (setifyF° ≫ orderedFP)
  rw [F.map_comp, F.map_recip_map hset, Cat.assoc]
  refine le_trans (comp_mono_left _ hordcp) ?_
  rw [← Cat.assoc ((F.map setify)°) listcp orderedFP,
    ← Cat.assoc (cpMap F A) (setifyF°) orderedFP]
  exact comp_mono_right hshunt orderedFP

/-- **(8.10)** (book p.203): `(sort P×sort P)·merge P ⊑ cup·sort P` — merging two sorted lists
    sorts their union.  `merge P`'s two defining properties do it: a listing of `S` and a listing
    of `T` merge to a listing of `S∪T`, and merging two `P`-ordered lists gives a `P`-ordered
    list.  The only step besides those is that `−×−` is a functor, so the pair of sorts splits
    into the pair of listings followed by the pair of order tests. -/
public theorem prodMap_sortRel_comp_merge_le
    {setify : L ⟶ PowerAllegory.powerObj A} {ordered : L ⟶ L}
    {Pr : RelProd L L} {Pr' : RelProd (PowerAllegory.powerObj A) (PowerAllegory.powerObj A)}
    {mergeP : Pr.p ⟶ L}
    (hmset : prodMap Pr' Pr (setify°) (setify°) ≫ mergeP ⊑ cup Pr' ≫ setify°)
    (hmord : prodMap Pr Pr ordered ordered ≫ mergeP ⊑ mergeP ≫ ordered) :
    prodMap Pr' Pr (sortRel setify ordered) (sortRel setify ordered) ≫ mergeP
      ⊑ cup Pr' ≫ sortRel setify ordered := by
  have hfun : prodMap Pr' Pr (setify° ≫ ordered) (setify° ≫ ordered)
      = prodMap Pr' Pr (setify°) (setify°) ≫ prodMap Pr Pr ordered ordered := by
    show Pr.pair (Pr'.outl ≫ setify° ≫ ordered) (Pr'.outr ≫ setify° ≫ ordered)
      = Pr.pair (Pr'.outl ≫ setify°) (Pr'.outr ≫ setify°) ≫ prodMap Pr Pr ordered ordered
    rw [RelProd.pair_prodMap, Cat.assoc, Cat.assoc]
  show prodMap Pr' Pr (setify° ≫ ordered) (setify° ≫ ordered) ≫ mergeP
    ⊑ cup Pr' ≫ (setify° ≫ ordered)
  rw [hfun, Cat.assoc]
  refine le_trans (comp_mono_left _ hmord) ?_
  rw [← Cat.assoc (prodMap Pr' Pr (setify°) (setify°)) mergeP ordered,
    ← Cat.assoc (cup Pr') (setify°) ordered]
  exact comp_mono_right hmset ordered

end SortLaws

end Freyd.Alg

/-! ## (8.5): `thinlist Q` on a concrete cons-list (B&dM p.200)

    The rest of §8.3 keeps `thinlist Q` and `minlist Q` abstract, constrained only by the laws
    that use them.  (8.5) cannot: it says what `thinlist Q` COMPUTES, so the fold `⦇[nil,bump Q]⦈`
    and the least member have to be written out.  `minlist Q` is `setify ≫ est Q` — the same
    `est` (8.7) compares it with — and `bump Q` is the book's

      `bump Q (a,[]) = [a]`,  `bump Q (a,[b]⧺x) = (aQb → [a]⧺x, bQa → [b]⧺x, [a]⧺[b]⧺x)`.

    The note's `<thinlist-defn>` prints those two guards against the OTHER two results; read that
    way (8.5) is false already at `[a,b]` with `b Q a` and `¬ a Q b`, where the note's `bump`
    returns `[a]` and the least member is `b`. -/

namespace Freyd.Alg.RelSet.CL

open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A : Type}

/-- Membership in a cons-list. -/
@[expose] public def clMem (w : A) : ConsList Unit A → Prop
  | ConsList.wrap _ => False
  | ConsList.cons a xs => w = a ∨ clMem w xs

public theorem clMem_wrap {u : Unit} {w : A} : clMem w (ConsList.wrap u) ↔ False := Iff.rfl

public theorem clMem_cons {w c : A} {d : ConsList Unit A} :
    clMem w (ConsList.cons c d) ↔ (w = c ∨ clMem w d) := Iff.rfl

/-- `setify : [A]⟶EA` for cons-lists: a list ↦ the set of its elements. -/
@[expose] public def setifyCL : dCL Unit A ⟶ pow (dE A) := graph (fun xs => fun w => clMem w xs)

/-- `minlist Q : [A]⟶A` — a `Q`-least member of the list, i.e. `setify` then `est Q`. -/
@[expose] public def minlist (Q : dE A ⟶ dE A) : dCL Unit A ⟶ dE A := setifyCL ≫ est Q

/-- Applying an operator takes its own brackets, like `P(R)` and `est(R)`.  The spelling is also
    what keeps the arrow ONE box in a circuit: a constant printed under its own bare name is opened
    and drawn by its body, and `minlist`'s body is the `setify est(Q)` the step exists to replace. -/
notation:max "minlist(" Q ")" => Freyd.Alg.RelSet.CL.minlist Q

public theorem minlist_apply (Q : dE A ⟶ dE A) (xs : ConsList Unit A) (w : A) :
    minlist Q xs w ↔ clMem w xs ∧ ∀ z, clMem z xs → Q w z := by
  constructor
  · rintro ⟨P, hP, hest⟩
    have hP' : P = fun v => clMem v xs := hP
    subst hP'
    exact (RelSet.est_apply Q _ w).mp hest
  · intro h
    exact ⟨fun v => clMem v xs, rfl, (RelSet.est_apply Q _ w).mpr h⟩

/-- `bump Q` (B&dM p.200): insert `a` into an already thinned list, dropping whichever of the
    new element and the old head the other dominates. -/
@[expose] public def bumpRel (Q : dE A ⟶ dE A) :
    (⟨A × ConsList Unit A⟩ : RelSet.{0}) ⟶ dCL Unit A := fun p ys =>
  match p.2 with
  | ConsList.wrap _ => ys = ConsList.cons p.1 (ConsList.wrap ())
  | ConsList.cons b xs =>
      (Q p.1 b ∧ ys = ConsList.cons p.1 xs)
      ∨ (Q b p.1 ∧ ys = ConsList.cons b xs)
      ∨ (¬ Q p.1 b ∧ ¬ Q b p.1 ∧ ys = ConsList.cons p.1 (ConsList.cons b xs))

/-- The algebra `[nil, bump Q]`. -/
@[expose] public def bumpAlg (Q : dE A ⟶ dE A) : Fobj Unit A (dCL Unit A) ⟶ dCL Unit A :=
  fun u ys => match u with
    | Sum.inl _ => ys = ConsList.wrap ()
    | Sum.inr p => bumpRel Q p ys

/-- `thinlist Q ≜ ⦇[nil,bump Q]⦈`. -/
@[expose] public def thinlist (Q : dE A ⟶ dE A) : dCL Unit A ⟶ dCL Unit A := cataR (bumpAlg Q)

public theorem thinlist_wrap (Q : dE A ⟶ dE A) (u : Unit) (r : ConsList Unit A) :
    thinlist Q (ConsList.wrap u) r ↔ r = ConsList.wrap () := Iff.rfl

public theorem thinlist_cons (Q : dE A ⟶ dE A) (c : A) (d r : ConsList Unit A) :
    thinlist Q (ConsList.cons c d) r ↔ ∃ r', thinlist Q d r' ∧ bumpRel Q (c, r') r := Iff.rfl

/-- A non-empty list has a `Q`-least member when `Q` is a connected preorder. -/
public theorem minlist_exists {Q : dE A ⟶ dE A} (hrefl : ∀ a, Q a a)
    (htrans : ∀ a b c, Q a b → Q b c → Q a c) (hconn : ∀ a b, Q a b ∨ Q b a) :
    ∀ (a : A) (xs : ConsList Unit A), ∃ w, minlist Q (ConsList.cons a xs) w := by
  intro a xs
  induction xs generalizing a with
  | wrap u =>
      refine ⟨a, (minlist_apply Q _ a).mpr ⟨clMem_cons.mpr (Or.inl rfl), ?_⟩⟩
      intro z hz
      rcases clMem_cons.mp hz with rfl | hz'
      · exact hrefl _
      · exact hz'.elim
  | cons b zs ih =>
      obtain ⟨m, hm⟩ := ih b
      rw [minlist_apply] at hm
      rcases hconn a m with h | h
      · refine ⟨a, (minlist_apply Q _ a).mpr ⟨clMem_cons.mpr (Or.inl rfl), ?_⟩⟩
        intro z hz
        rcases clMem_cons.mp hz with rfl | hz'
        · exact hrefl _
        · exact htrans a m z h (hm.2 z hz')
      · refine ⟨m, (minlist_apply Q _ m).mpr ⟨clMem_cons.mpr (Or.inr hm.1), ?_⟩⟩
        intro z hz
        rcases clMem_cons.mp hz with rfl | hz'
        · exact h
        · exact hm.2 z hz'

/-- **(8.5)** (B&dM p.200): for a CONNECTED preorder `Q` and a non-empty list,
    `thinlist Q xs = [minlist Q xs]` — thinning comes down to one element. -/
public theorem thinlist_eq_singleton_minlist {Q : dE A ⟶ dE A} (hrefl : ∀ a, Q a a)
    (htrans : ∀ a b c, Q a b → Q b c → Q a c) (hconn : ∀ a b, Q a b ∨ Q b a)
    (a : A) (xs ys : ConsList Unit A) :
    thinlist Q (ConsList.cons a xs) ys
      ↔ ∃ w, minlist Q (ConsList.cons a xs) w ∧ ys = ConsList.cons w (ConsList.wrap ()) := by
  induction xs generalizing a ys with
  | wrap u =>
      rw [thinlist_cons]
      constructor
      · rintro ⟨r', hr', hb⟩
        rw [thinlist_wrap] at hr'
        subst hr'
        refine ⟨a, (minlist_apply Q _ a).mpr ⟨clMem_cons.mpr (Or.inl rfl), ?_⟩, hb⟩
        intro z hz
        rcases clMem_cons.mp hz with rfl | hz'
        · exact hrefl _
        · exact hz'.elim
      · rintro ⟨w, hw, rfl⟩
        rw [minlist_apply] at hw
        rcases clMem_cons.mp hw.1 with rfl | hw'
        · exact ⟨ConsList.wrap (), rfl, rfl⟩
        · exact hw'.elim
  | cons b zs ih =>
      rw [thinlist_cons]
      constructor
      · rintro ⟨r', hr', hb⟩
        obtain ⟨m, hm, rfl⟩ := (ih b r').mp hr'
        rw [minlist_apply] at hm
        rcases hb with ⟨hab, rfl⟩ | ⟨hba, rfl⟩ | ⟨h1, h2, _⟩
        · refine ⟨a, (minlist_apply Q _ a).mpr ⟨clMem_cons.mpr (Or.inl rfl), ?_⟩, rfl⟩
          intro z hz
          rcases clMem_cons.mp hz with rfl | hz'
          · exact hrefl _
          · exact htrans a m z hab (hm.2 z hz')
        · refine ⟨m, (minlist_apply Q _ m).mpr ⟨clMem_cons.mpr (Or.inr hm.1), ?_⟩, rfl⟩
          intro z hz
          rcases clMem_cons.mp hz with rfl | hz'
          · exact hba
          · exact hm.2 z hz'
        · exact ((hconn a m).elim h1 h2).elim
      · rintro ⟨w, hw, rfl⟩
        rw [minlist_apply] at hw
        rcases clMem_cons.mp hw.1 with rfl | hwtail
        · obtain ⟨m, hm⟩ := minlist_exists hrefl htrans hconn b zs
          rw [minlist_apply] at hm
          refine ⟨ConsList.cons m (ConsList.wrap ()),
            (ih b _).mpr ⟨m, (minlist_apply Q _ m).mpr hm, rfl⟩, ?_⟩
          exact Or.inl ⟨hw.2 m (clMem_cons.mpr (Or.inr hm.1)), rfl⟩
        · refine ⟨ConsList.cons w (ConsList.wrap ()),
            (ih b _).mpr ⟨w, (minlist_apply Q _ w).mpr
              ⟨hwtail, fun z hz => hw.2 z (clMem_cons.mpr (Or.inr hz))⟩, rfl⟩, ?_⟩
          exact Or.inr (Or.inl ⟨hw.2 a (clMem_cons.mpr (Or.inl rfl)), rfl⟩)

end Freyd.Alg.RelSet.CL
