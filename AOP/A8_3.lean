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
    `cpMap F A` (the relator AND the object) and `cup` `AOP.A5_6`'s `cup`; `⟨g₁,g₂⟩` is `RelProd.pair g₁ g₂` and
    `sort P×sort P` is `prodMap _ _ sortP sortP` (`AOP.A5_2`).
  - The list object `[A]` is `L A` for a LIST RELATOR `L : Relator 𝒜 𝒜`, and `[FA]` is `L (F A)`:
    p.199 pins `setify : PA ← list A`, so the list object is the list relator APPLIED to the
    element object and cannot be a free object of its own.  Every list combinator (`ordered P`,
    `subseq`, `thinlist Q`, `filter p`, `list f`, `listcp`, `merge P`, `minlist R`) is still an
    abstract arrow constrained only through the laws it is used by.
    `AOP.A5_6_ListCombinators` is the `Rel`-instance of the same vocabulary.

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
-- `minlist Q` is `setify est(Q)`, and every §9 program step pushes a `list g` past it, so the
-- cons-list `setify` must be reconciled with `ListRel`'s and its lax naturality available here.
public import AOP.A5_6_ListCombinators
public import AOP.A5_7_ListBeads
import AOP.CalcSteps

universe u

set_option hygiene false in
/-- The order binder `«≼»`, written `≼` as the note writes it. -/
local notation "≼" => «≼»

namespace Freyd.Alg
open PowerAllegory

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A : 𝒜} (L : Relator 𝒜 𝒜)

/-! ## The order `≼`

  B&dM write the connected preorder §8.3 sorts by as a letter, `sort P`, `ordered P`, `merge P`;
  the note writes it `≼`, and so does every statement below.  `≼` is an ordinary binder, named
  `«≼»`; the notation lets the source write it as the note does.  Every combinator the book
  parameterises by that order (`ordered`, `sort`, `merge`) is a FAMILY applied to it, so a
  statement prints `ordered(≼)`, never a fused name.  The notation is declared at the top of
  the file, so the `Rel` section at its end reads the same. -/

/-! ## `sort(≼)` and (8.6) -/

/-- `sort(≼) ≜ ordered(≼)·setify°` (book p.201, "definition of sort P"), mirrored
    `setify° ordered(≼)`: read the set back as one of its `≼`-ordered listings.  `L A` is the list
    object `[A]`, `setify : L A ⟶ EA` the map that forgets the order, and `ordered` the family of
    order tests, `ordered(≼)` the coreflexive that keeps the `≼`-ordered lists. -/
@[expose] public def sortRel (setify : L.obj A ⟶ P A)
    (ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)) («≼» : A ⟶ A) :
    P A ⟶ L.obj A := setify° ≫ ordered ≼

/-! ### The steps of the p.201 argument

  `sort(≼) g = setify° ordered(≼) g ⊑ setify° g ordered(≼) ⊑ T setify° ordered(≼) = T sort(≼)`.
  The outer two steps are the unfolding of `sort(≼)`; the inner two carry the argument and are
  stated here, ahead of their first use, for any combinator `g` that only drops elements and
  implements `T` on the underlying set.  `sortRel_comp_le` below is their composition, (8.6) and
  (8.9) its instances, so the argument is written once. -/

/-- Step 1: `g` only drops elements (`g ⊑ subseq`) and a subsequence of a `≼`-ordered list is
    `≼`-ordered, so `g` may run before the order test. -/
public theorem sortRel_comp_le_step1 (setify : L.obj A ⟶ P A)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A} {subseq g : L.obj A ⟶ L.obj A}
    (hord : Coreflexive (ordered ≼)) (hsub : g ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼) :
    setify° ≫ ordered ≼ ≫ g ⊑ setify° ≫ g ≫ ordered ≼ := by
  refine comp_mono_left _ ?_
  have h1 : ordered ≼ ≫ g ⊑ subseq ≫ ordered ≼ := le_trans (comp_mono_left _ hsub) hos
  have h2 : ordered ≼ ≫ g ⊑ g := by
    have := comp_mono_right hord g
    rwa [Cat.id_comp] at this
  have h3 := le_inter h1 h2
  rw [coreflexive_comp_inter hord subseq g] at h3
  exact le_trans h3 (comp_mono_right (inter_lb_right _ _) (ordered ≼))

/-- Step 2: `·setify ⊣ ·setify°` shunts `g`'s specification `g·setify ⊑ setify·T` across the
    converse. -/
public theorem sortRel_comp_le_step2 {setify : L.obj A ⟶ P A}
    (hset : Map setify) (ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)) («≼» : A ⟶ A)
    {g : L.obj A ⟶ L.obj A}
    {T : P A ⟶ P A} (hspec : g ≫ setify ⊑ setify ≫ T) :
    setify° ≫ g ≫ ordered ≼ ⊑ T ≫ setify° ≫ ordered ≼ := by
  have hshunt : setify° ≫ g ⊑ T ≫ setify° := by
    refine (map_shunt_left hset g _).mpr ?_
    have hent : g ⊑ g ≫ setify ≫ setify° := by
      have := comp_mono_left g (entire_id_le hset.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc g setify (setify°), ← Cat.assoc setify T (setify°)]
    exact comp_mono_right hspec _
  rw [← Cat.assoc (setify°) g (ordered ≼), ← Cat.assoc T (setify°) (ordered ≼)]
  exact comp_mono_right hshunt (ordered ≼)

/-- **(8.6)** (book p.201): a thinning of the sorted list lists a thinning of the set,
    `sort(≼)·thinlist Q ⊑ thin Q·sort(≼)` mirrored to
    `sortRel setify ordered ≼ ≫ thinlist ⊑ thinRel Q ≫ sortRel setify ordered ≼`.  The two
    conditions on `thinlist Q` do all the work: `thinlist Q ⊑ subseq` lets the thinning run
    before the order test, and `thinlist Q·setify ⊑ setify·thin Q` shunts across `setify°`. -/
public theorem sortRel_comp_thinlist_le
    {setify : L.obj A ⟶ P A} (hset : Map setify)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A}
    {subseq thinlist : L.obj A ⟶ L.obj A} {Q : A ⟶ A}
    (hord : Coreflexive (ordered ≼)) (hsub : thinlist ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼)
    (hspec : thinlist ≫ setify ⊑ setify ≫ thinRel Q) :
    sortRel L setify ordered ≼ ≫ thinlist ⊑ thinRel Q ≫ sortRel L setify ordered ≼ :=
  calc sortRel L setify ordered ≼ ≫ thinlist = setify° ≫ ordered ≼ ≫ thinlist := by
        show (setify° ≫ ordered ≼) ≫ thinlist = _
        exact Cat.assoc _ _ _
    _ ⊑ setify° ≫ thinlist ≫ ordered ≼ := sortRel_comp_le_step1 L setify hord hsub hos
    _ ⊑ thinRel Q ≫ setify° ≫ ordered ≼ := sortRel_comp_le_step2 L hset ordered ≼ hspec
    _ = thinRel Q ≫ sortRel L setify ordered ≼ := rfl

calc_steps sortRel_comp_thinlist_le

/-! ## Lemma 8.1 (book p.202) -/

variable {F : Relator 𝒜 𝒜}

/-- **Lemma 8.1** (book p.202): one sorted list built from sorted arguments, instead of a set
    built and then sorted —
    `filter p·list f·listcp(F)·F(sort ≼) ⊑ sort ≼·Λ(p·f·F∈)`, mirrored to
    `F(sort ≼) ≫ listcp ≫ list f ≫ filter p ⊑ Λ (F(∋) ≫ f ≫ p) ≫ sort ≼`.
    The sort walks inwards one law at a time: under `F` by (8.11), `f` monotonic on `≼`
    (`F(≼) ⊑ f≼f°`), past `list f` by (8.8), past `filter p` by (8.9), then `E(f) = P(f)` and the
    transpose absorbs `E(fp)`. -/
public theorem map_sort_comp_listcp_le
    {f : F.obj A ⟶ A} (hf : Map f) {p «≼» : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {sortF : (F.obj A ⟶ F.obj A) → (P (F.obj A) ⟶ L.obj (F.obj A))}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)} {listf : L.obj (F.obj A) ⟶ L.obj A}
    {filterp : L.obj A ⟶ L.obj A}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono : Freyd.Alg.MonoAlg f ≼)
    (h88 : sortF (f ≫ ≼ ≫ f°) ≫ listf ⊑ powerRel f ≫ sort ≼)
    (h89 : sort ≼ ≫ filterp ⊑ existsImage p ≫ sort ≼)
    (h811 : F.map (sort ≼) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map ≼)) :
    F.map (sort ≼) ≫ listcp ≫ listf ≫ filterp ⊑ Λ (F.map (∋ A) ≫ f ≫ p) ≫ sort ≼ :=
  calc F.map (sort ≼) ≫ listcp ≫ listf ≫ filterp
        ⊑ cpMap F A ≫ sortF (F.map ≼) ≫ listf ≫ filterp := by
        rw [← Cat.assoc, ← Cat.assoc (cpMap F A)]
        exact comp_mono_right h811 _
    _ ⊑ cpMap F A ≫ sortF (f ≫ ≼ ≫ f°) ≫ listf ≫ filterp :=
        comp_mono_left _ (comp_mono_right (hsortF ((Freyd.Alg.monoAlg_iff_sandwich hf).mp hmono)) _)
    _ ⊑ cpMap F A ≫ powerRel f ≫ sort ≼ ≫ filterp := by
        refine comp_mono_left _ ?_
        rw [← Cat.assoc, ← Cat.assoc (powerRel f)]
        exact comp_mono_right h88 filterp
    _ ⊑ cpMap F A ≫ powerRel f ≫ existsImage p ≫ sort ≼ := comp_mono_left _ (comp_mono_left _ h89)
    _ = cpMap F A ≫ existsImage f ≫ existsImage p ≫ sort ≼ := by rw [powerRel_map hf]
    _ = cpMap F A ≫ existsImage (f ≫ p) ≫ sort ≼ := by
        rw [← Cat.assoc (existsImage f), ← existsImage_comp]
    _ = Λ (F.map (∋ A) ≫ f ≫ p) ≫ sort ≼ := by
        rw [← Cat.assoc, show cpMap F A = Λ (F.map (∋ A)) from rfl, Λ_absorption]

calc_steps map_sort_comp_listcp_le

/-! ## THEOREM 8.2 (book p.203) and its fusion side condition

  BINARY THINNING DATA (book p.203): `S = (f₁p₁) ∪ (f₂p₂)` with `p₁`, `p₂` coreflexive; `Q` a
  preorder with `Q ⊑ R` and both `f₁p₁`, `f₂p₂` monotonic on `Q`; `≼` a connected preorder
  with both `f₁`, `f₂` monotonic on `≼`; `gᵢ = list fᵢ·filter pᵢ`.  Connectedness of `≼` and
  coreflexivity of the `pᵢ` enter only through the laws (8.6)-(8.11) they are there to make
  true, so they are not separate hypotheses below. -/

/-! ### The fusion side condition's steps (book p.203)

  `sortedAlg_fusion` below is their composition. -/

/-- Step 1: Lemma 8.1 at `f₁,p₁` and at `f₂,p₂` under the common prefix `F(sort ≼)·listcp(F)`. -/
public theorem sortedAlg_fusion_step1
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ «≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {sortF : (F.obj A ⟶ F.obj A) → (P (F.obj A) ⟶ L.obj (F.obj A))}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)}
    {listf₁ listf₂ : L.obj (F.obj A) ⟶ L.obj A}
    {filterp₁ filterp₂ : L.obj A ⟶ L.obj A} {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {Pr : RelProd (L.obj A) (L.obj A)} {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : Freyd.Alg.MonoAlg f₁ ≼) (hmono₂ : Freyd.Alg.MonoAlg f₂ ≼)
    (h88₁ : sortF (f₁ ≫ ≼ ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort ≼)
    (h88₂ : sortF (f₂ ≫ ≼ ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort ≼)
    (h89₁ : sort ≼ ≫ filterp₁ ⊑ existsImage p₁ ≫ sort ≼)
    (h89₂ : sort ≼ ≫ filterp₂ ⊑ existsImage p₂ ≫ sort ≼)
    (h811 : F.map (sort ≼) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map ≼)) :
    F.map (sort ≼) ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)
        ≫ merge ≼ ≫ thinlist Q
      ⊑ Pr.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort ≼) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort ≼)
        ≫ merge ≼ ≫ thinlist Q := by
  have l1 : (F.map (sort ≼) ≫ listcp) ≫ (listf₁ ≫ filterp₁)
      ⊑ Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort ≼ := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le L hf₁ hsortF hmono₁ h88₁ h89₁ h811
  have l2 : (F.map (sort ≼) ≫ listcp) ≫ (listf₂ ≫ filterp₂)
      ⊑ Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort ≼ := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le L hf₂ hsortF hmono₂ h88₂ h89₂ h811
  rw [← Cat.assoc (F.map (sort ≼)) (listcp)
        (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ merge ≼ ≫ thinlist Q),
      ← Cat.assoc (F.map (sort ≼) ≫ listcp)
        (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)) (merge ≼ ≫ thinlist Q)]
  exact comp_mono_right (le_trans (RelProd.comp_pair_le _ _ _) (RelProd.pair_mono l1 l2)) _

/-- Step 2: `⟨X,Y⟩(sort ≼×sort ≼) = ⟨X sort ≼,Y sort ≼⟩`, read right to left. -/
public theorem sortedAlg_fusion_step2 {f₁ f₂ : F.obj A ⟶ A} {p₁ p₂ «≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)} :
    Pr.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁) ≫ sort ≼) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂) ≫ sort ≼)
        ≫ merge ≼ ≫ thinlist Q
      = Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂))
        ≫ prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ≫ thinlist Q := by
  rw [← RelProd.pair_prodMap (P := Pr') (Q := Pr)
        (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂)) (sort ≼) (sort ≼), Cat.assoc]

/-- Step 3, (8.10): `merge ≼` of the two sorted lists lists their union. -/
public theorem sortedAlg_fusion_step3 {f₁ f₂ : F.obj A ⟶ A} {p₁ p₂ «≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (h810 : prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ⊑ cup Pr' ≫ sort ≼) :
    Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂))
        ≫ prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ≫ thinlist Q
      ⊑ Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂))
        ≫ cup Pr' ≫ sort ≼ ≫ thinlist Q := by
  refine comp_mono_left _ ?_
  rw [← Cat.assoc (prodMap Pr' Pr (sort ≼) (sort ≼)) (merge ≼) (thinlist Q),
      ← Cat.assoc (cup Pr') (sort ≼) (thinlist Q)]
  exact comp_mono_right h810 (thinlist Q)

/-- Step 4: `Λ` of the union is the pair of the two transposes, closed by `cup`. -/
public theorem sortedAlg_fusion_step4 {f₁ f₂ : F.obj A ⟶ A} {p₁ p₂ «≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {Pr' : RelProd (P A) (P A)} :
    Pr'.pair (Λ (F.map (∋ A) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ A) ≫ f₂ ≫ p₂))
        ≫ cup Pr' ≫ sort ≼ ≫ thinlist Q
      = Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ sort ≼ ≫ thinlist Q := by
  rw [DistributiveAllegory.comp_union_distrib, Λ_union, Cat.assoc]

/-- Step 5, (8.6): `sort ≼·thinlist Q ⊑ thin Q·sort ≼`. -/
public theorem sortedAlg_fusion_step5 {S : F.obj A ⟶ A} {«≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    (h86 : sort ≼ ≫ thinlist Q ⊑ thinRel Q ≫ sort ≼) :
    Λ (F.map (∋ A) ≫ S) ≫ sort ≼ ≫ thinlist Q ⊑ Λ (F.map (∋ A) ≫ S) ≫ thinRel Q ≫ sort ≼ :=
  comp_mono_left _ h86

/-- **The fusion side condition of THEOREM 8.2** (book p.203): sorting the candidate set is
    what turns the thinning algebra into an algebra on lists,
    `thin Q·Λ(F∈·S)·sort ≼ ⊒ thinlist Q·merge ≼·⟨g₁,g₂⟩·listcp(F)·F(sort ≼)` mirrored to
    `F(sort ≼) ≫ listcp ≫ ⟨g₁,g₂⟩ ≫ merge ≼ ≫ thinlist Q ⊑ Λ (F(∋) ≫ S) ≫ thin Q ≫ sort ≼`.
    (8.6) exchanges `thin Q` for `thinlist Q`; `cup` splits `Λ` of the union of the two
    algebras; (8.10) exchanges the union of the two sorted lists for `merge ≼`; and Lemma 8.1
    at `f₁,p₁` and at `f₂,p₂` puts the sort back inside `F`. -/
public theorem sortedAlg_fusion
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ «≼» Q : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {sortF : (F.obj A ⟶ F.obj A) → (P (F.obj A) ⟶ L.obj (F.obj A))}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)}
    {listf₁ listf₂ : L.obj (F.obj A) ⟶ L.obj A}
    {filterp₁ filterp₂ : L.obj A ⟶ L.obj A} {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : Freyd.Alg.MonoAlg f₁ ≼) (hmono₂ : Freyd.Alg.MonoAlg f₂ ≼)
    (h88₁ : sortF (f₁ ≫ ≼ ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort ≼)
    (h88₂ : sortF (f₂ ≫ ≼ ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort ≼)
    (h89₁ : sort ≼ ≫ filterp₁ ⊑ existsImage p₁ ≫ sort ≼)
    (h89₂ : sort ≼ ≫ filterp₂ ⊑ existsImage p₂ ≫ sort ≼)
    (h811 : F.map (sort ≼) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map ≼))
    (h810 : prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ⊑ cup Pr' ≫ sort ≼)
    (h86 : sort ≼ ≫ thinlist Q ⊑ thinRel Q ≫ sort ≼) :
    F.map (sort ≼) ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)
        ≫ merge ≼ ≫ thinlist Q
      ⊑ Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q ≫ sort ≼ :=
  le_trans (sortedAlg_fusion_step1 L hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811)
    (le_trans (le_of_eq (sortedAlg_fusion_step2 L (Pr' := Pr')))
      (le_trans (sortedAlg_fusion_step3 L h810)
        (le_trans (le_of_eq (sortedAlg_fusion_step4 L)) (sortedAlg_fusion_step5 L h86))))

/-! ### THEOREM 8.2's three steps

  `⦇−thinlist Q⦈minlist R ⊑ ⦇(F(∋)S)%∋ thin Q⦈sort ≼ minlist R ⊑ ⦇(F(∋)S)%∋ thin Q⦈est R
   ⊑ ⦇S⦈%∋ est R`, at `S ≜ f₁p₁∪f₂p₂`; `thinningList` is their composition. -/

/-- Step 1: `relCata_le_comp` fuses `sort ≼` into the algebra, its side condition being
    `sortedAlg_fusion` — the fold on sorted lists refines the fold on thinned sets, read sorted. -/
public theorem thinningList_step1 (I : InitialAlgebra F)
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ «≼» Q R : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {sortF : (F.obj A ⟶ F.obj A) → (P (F.obj A) ⟶ L.obj (F.obj A))}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)}
    {listf₁ listf₂ g₁ g₂ : L.obj (F.obj A) ⟶ L.obj A}
    {filterp₁ filterp₂ : L.obj A ⟶ L.obj A} {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {minlist : (A ⟶ A) → (L.obj A ⟶ A)} {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : Freyd.Alg.MonoAlg f₁ ≼) (hmono₂ : Freyd.Alg.MonoAlg f₂ ≼)
    (h88₁ : sortF (f₁ ≫ ≼ ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort ≼)
    (h88₂ : sortF (f₂ ≫ ≼ ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort ≼)
    (h89₁ : sort ≼ ≫ filterp₁ ⊑ existsImage p₁ ≫ sort ≼)
    (h89₂ : sort ≼ ≫ filterp₂ ⊑ existsImage p₂ ≫ sort ≼)
    (h811 : F.map (sort ≼) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map ≼))
    (h810 : prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ⊑ cup Pr' ≫ sort ≼)
    (h86 : sort ≼ ≫ thinlist Q ⊑ thinRel Q ≫ sort ≼)
    (hg₁ : g₁ = listf₁ ≫ filterp₁) (hg₂ : g₂ = listf₂ ≫ filterp₂) :
    relCata (listcp ≫ Pr.pair g₁ g₂ ≫ merge ≼ ≫ thinlist Q) ≫ minlist R
      ⊑ (relCata (Λ (F.map (∋ A) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q) ≫ sort ≼)
        ≫ minlist R := by
  subst hg₁
  subst hg₂
  refine comp_mono_right (relCata_le_comp I ?_) (minlist R)
  rw [Cat.assoc]
  exact sortedAlg_fusion L hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811 h810 h86

/-- Step 2: (8.7) `sort ≼·minlist R ⊑ min R` reads the minimum off the sorted list. -/
public theorem thinningList_step2 (I : InitialAlgebra F) {S : F.obj A ⟶ A}
    {«≼» Q R : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {minlist : (A ⟶ A) → (L.obj A ⟶ A)}
    (h87 : sort ≼ ≫ minlist R ⊑ est R) :
    (relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ sort ≼) ≫ minlist R
      ⊑ relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ est R :=
  le_trans (le_of_eq (Cat.assoc _ _ _)) (comp_mono_left _ h87)

/-- Step 3: Corollary 8.1 (`thinning_est`) at the union algebra — the union of two `Q`-monotonic
    algebras is `Q`-monotonic, which is the only hypothesis of it the union has to earn. -/
public theorem thinningList_step3 (I : InitialAlgebra F)
    {f₁ f₂ S : F.obj A ⟶ A} {p₁ p₂ Q R : A ⟶ A}
    (hQR : Q ⊑ R) (hQ : Preorder Q) (hR : Preorder R)
    (hm₁ : Freyd.Alg.MonoAlg (f₁ ≫ p₁) Q) (hm₂ : Freyd.Alg.MonoAlg (f₂ ≫ p₂) Q)
    (hS : S = (f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) :
    relCata (Λ (F.map (∋ A) ≫ S) ≫ thinRel Q) ≫ est R
      ⊑ Λ (relCata S) ≫ est R := by
  subst hS
  have hmonoS : Freyd.Alg.MonoAlg ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) Q := by
    show F.map Q ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ⊑ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ≫ Q
    rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
    exact union_mono hm₁ hm₂
  exact thinning_est I hQR hQ hR hmonoS

/-- **THEOREM 8.2** (book p.203): a fold on SORTED LISTS of partial solutions, thinned at
    every step, refines the thinning specification —
    `min R·Λ⦇S⦈ ⊒ minlist R·⦇thinlist Q·merge ≼·⟨g₁,g₂⟩·listcp(F)⦈`, mirrored to
    `relCata (listcp(F) ≫ ⟨g₁,g₂⟩ ≫ merge ≼ ≫ thinlist Q) ≫ minlist R ⊑ Λ ⦇S⦈ ≫ est R`.
    The specification's algebra is BOUND as `S` (`hS : S = f₁p₁ ∪ f₂p₂`), because that is the one
    letter the book and the note both write there and a conclusion spelling the union out reads as
    a different theorem from the one the picture draws.
    Corollary 8.1 (`thinning_est`) puts `thin Q` inside the fold, (8.7) splits the minimum
    into `sort ≼` followed by `minlist R`, and `relCata_le_comp` fuses `sort ≼` into the
    algebra — that fusion condition being `sortedAlg_fusion`.  No set is ever built. -/
public theorem thinningList (I : InitialAlgebra F)
    {f₁ f₂ : F.obj A ⟶ A} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ «≼» Q R : A ⟶ A}
    {sort : (A ⟶ A) → (P A ⟶ L.obj A)}
    {sortF : (F.obj A ⟶ F.obj A) → (P (F.obj A) ⟶ L.obj (F.obj A))}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)}
    {listf₁ listf₂ g₁ g₂ : L.obj (F.obj A) ⟶ L.obj A}
    {filterp₁ filterp₂ : L.obj A ⟶ L.obj A} {thinlist : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {minlist : (A ⟶ A) → (L.obj A ⟶ A)} {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (hQR : Q ⊑ R) (hQ : Preorder Q) (hR : Preorder R)
    (hm₁ : Freyd.Alg.MonoAlg (f₁ ≫ p₁) Q) (hm₂ : Freyd.Alg.MonoAlg (f₂ ≫ p₂) Q)
    (hsortF : ∀ {X Y : F.obj A ⟶ F.obj A}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : Freyd.Alg.MonoAlg f₁ ≼) (hmono₂ : Freyd.Alg.MonoAlg f₂ ≼)
    (h88₁ : sortF (f₁ ≫ ≼ ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sort ≼)
    (h88₂ : sortF (f₂ ≫ ≼ ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sort ≼)
    (h89₁ : sort ≼ ≫ filterp₁ ⊑ existsImage p₁ ≫ sort ≼)
    (h89₂ : sort ≼ ≫ filterp₂ ⊑ existsImage p₂ ≫ sort ≼)
    (h811 : F.map (sort ≼) ≫ listcp ⊑ cpMap F A ≫ sortF (F.map ≼))
    (h810 : prodMap Pr' Pr (sort ≼) (sort ≼) ≫ merge ≼ ⊑ cup Pr' ≫ sort ≼)
    (h86 : sort ≼ ≫ thinlist Q ⊑ thinRel Q ≫ sort ≼)
    (h87 : sort ≼ ≫ minlist R ⊑ est R)
    (hg₁ : g₁ = listf₁ ≫ filterp₁) (hg₂ : g₂ = listf₂ ≫ filterp₂) {S : F.obj A ⟶ A}
    (hS : S = (f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) :
    relCata (listcp ≫ Pr.pair g₁ g₂ ≫ merge ≼ ≫ thinlist Q) ≫ minlist R
      ⊑ Λ (relCata S) ≫ est R := by
  subst hS
  exact le_trans
    (thinningList_step1 L I hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811 h810 h86
      hg₁ hg₂)
    (le_trans (thinningList_step2 L I h87)
      (thinningList_step3 I hQR hQ hR hm₁ hm₂ rfl))

/-! ## The note's `thinlist-laws`: (8.7), (8.8) and (8.9) discharged

  `thinningList` above takes (8.5) and (8.7)-(8.11) as hypotheses.  Three of them are not
  interface conditions at all once `sort(≼)` is unfolded to `setify° ordered(≼)`: they follow, in
  the book's own style for (8.6), from the two DEFINING properties of the combinator each one
  mentions.  Everything below is stated for `sortRel`, so it applies to any `setify`/`ordered`
  pair; `AOP.A8_3`'s `RelSet` section below discharges `ordered`'s properties from its
  definition. -/

section SortLaws

variable {A : 𝒜} (L : Relator 𝒜 𝒜)

/-- **(8.6) and (8.9) are one law.**  A list combinator `g` that only DROPS elements
    (`g ⊑ subseq`) and that implements a set operation `T` on the underlying set
    (`g·setify ⊑ setify·T`) commutes with the sort: `sort(≼)·g ⊑ T·sort(≼)`.  (8.6) is the case
    `g ≜ thinlist Q`, `T ≜ thin Q` (`sortRel_comp_thinlist_le` above); (8.9) is `g ≜ filter p`,
    `T ≜ E p`.  The proof is the book's p.201 argument verbatim: `g` only drops elements and a
    subsequence of a `≼`-ordered list is `≼`-ordered, so `g` may run before the order test, and
    `·setify ⊣ ·setify°` shunts its specification across the converse. -/
public theorem sortRel_comp_le
    {setify : L.obj A ⟶ P A} (hset : Map setify)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A} {subseq g : L.obj A ⟶ L.obj A}
    {T : P A ⟶ P A}
    (hord : Coreflexive (ordered ≼)) (hsub : g ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼)
    (hspec : g ≫ setify ⊑ setify ≫ T) :
    sortRel L setify ordered ≼ ≫ g ⊑ T ≫ sortRel L setify ordered ≼ := by
  show (setify° ≫ ordered ≼) ≫ g ⊑ T ≫ (setify° ≫ ordered ≼)
  rw [Cat.assoc]
  exact le_trans (sortRel_comp_le_step1 L setify hord hsub hos)
    (sortRel_comp_le_step2 L hset ordered ≼ hspec)

/-- **(8.9)** (book p.203): `sort(≼)·filter p ⊑ E p·sort(≼)` — filtering a sorted list sorts the
    restricted set.  `filter p` drops elements and, on the underlying set, is `E p`; that is all
    the law says, so it is `sortRel_comp_le` at `T ≜ E p`. -/
public theorem sortRel_comp_filter_le
    {setify : L.obj A ⟶ P A} (hset : Map setify)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A}
    {subseq filterp : L.obj A ⟶ L.obj A} {p : A ⟶ A}
    (hord : Coreflexive (ordered ≼)) (hsub : filterp ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼)
    (hspec : filterp ≫ setify ⊑ setify ≫ existsImage p) :
    sortRel L setify ordered ≼ ≫ filterp ⊑ existsImage p ≫ sortRel L setify ordered ≼ :=
  sortRel_comp_le L hset hord hsub hos hspec

/-- **(8.7)** (book p.203): `sort(≼)·minlist R ⊑ min R`, mirrored
    `sortRel setify ordered ≼ ≫ minlist ⊑ est R` — a minimum of the sorted list is a minimum of
    the set.  The two defining properties of `minlist R` are what it comes to: the answer is an
    ELEMENT of the list (`minlist ⊑ setify·∋`), and it is `R`-below every element of the list
    (`(setify·∋)°·minlist ⊑ R°`).  `ordered(≼)` is dropped by coreflexivity and `setify` by
    simplicity, so the order plays no part. -/
public theorem sortRel_comp_minlist_le
    {setify : L.obj A ⟶ P A} (hset : Map setify)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A} {minlist : L.obj A ⟶ A} {R : A ⟶ A}
    (hord : Coreflexive (ordered ≼))
    (hmem : minlist ⊑ setify ≫ ∋ A)
    (hleast : (setify ≫ ∋ A)° ≫ minlist ⊑ R°) :
    sortRel L setify ordered ≼ ≫ minlist ⊑ est R := by
  have hdrop : setify° ≫ ordered ≼ ≫ minlist ⊑ setify° ≫ minlist := by
    refine comp_mono_left _ ?_
    have := comp_mono_right hord minlist
    rwa [Cat.id_comp] at this
  refine le_est_iff.mpr ⟨?_, ?_⟩
  · show (setify° ≫ ordered ≼) ≫ minlist ⊑ ∋ A
    rw [Cat.assoc]
    refine le_trans hdrop ?_
    refine le_trans (comp_mono_left _ hmem) ?_
    rw [← Cat.assoc (setify°) setify (∋ A)]
    have := comp_mono_right hset.2 (∋ A)
    rwa [Cat.id_comp] at this
  · show (∋ A)° ≫ (setify° ≫ ordered ≼) ≫ minlist ⊑ R°
    rw [Cat.assoc]
    refine le_trans (comp_mono_left _ hdrop) ?_
    rw [← Cat.assoc ((∋ A)°) (setify°) minlist, ← Allegory.recip_comp]
    exact hleast

/-- **(8.8)** (book p.203): `sort(f≼f°)·list f ⊑ P f·sort(≼)`, mirrored
    `sortRel setifyF ordered (f≼f°) ≫ listf ⊑ powerRel f ≫ sortRel setify ordered ≼` — shunt a
    function through a sort.  `ordered` is ONE family over every object, as the book's is.  Again
    two defining properties: `setify` is natural in the list (`list f·setify ⊑ setifyF·E f`, so
    the shunt across `setifyF°` gives `E f·setify°`), and `list f` carries an `f≼f°`-ordered list
    to a `≼`-ordered one, which is where `f` monotonic on `≼` enters. -/
public theorem sortRel_comp_listMap_le
    {setifyF : L.obj A ⟶ P A} (hsetF : Map setifyF)
    {B : 𝒜} {setify : L.obj B ⟶ P B} (hset : Map setify)
    {ordered : ∀ {X : 𝒜}, (X ⟶ X) → (L.obj X ⟶ L.obj X)} {«≼» : B ⟶ B}
    {listf : L.obj A ⟶ L.obj B} {f : A ⟶ B} (hf : Map f)
    (hnat : listf ≫ setify ⊑ setifyF ≫ existsImage f)
    (hordf : ordered (f ≫ ≼ ≫ f°) ≫ listf ⊑ listf ≫ ordered ≼) :
    sortRel L setifyF ordered (f ≫ ≼ ≫ f°) ≫ listf ⊑ powerRel f ≫ sortRel L setify ordered ≼ := by
  have hshunt : setifyF° ≫ listf ⊑ existsImage f ≫ setify° := by
    refine (map_shunt_left hsetF listf _).mpr ?_
    have hent : listf ⊑ listf ≫ setify ≫ setify° := by
      have := comp_mono_left listf (entire_id_le hset.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc listf setify (setify°), ← Cat.assoc setifyF (existsImage f) (setify°)]
    exact comp_mono_right hnat _
  show (setifyF° ≫ ordered (f ≫ ≼ ≫ f°)) ≫ listf ⊑ powerRel f ≫ (setify° ≫ ordered ≼)
  rw [Cat.assoc]
  refine le_trans (comp_mono_left _ hordf) ?_
  rw [← Cat.assoc (setifyF°) listf (ordered ≼), powerRel_map hf,
    ← Cat.assoc (existsImage f) (setify°) (ordered ≼)]
  exact comp_mono_right hshunt (ordered ≼)

/-- **(8.11)** (book p.203): `F(sort(≼))·listcp(F) ⊑ cp(F)·sort(F(≼))`, mirrored
    `F.map (sortRel setify ordered ≼) ≫ listcp ⊑ cpMap F A ≫ sortRel setifyF ordered (F(≼))` —
    `listcp(F)` is the list implementation of the cartesian product.  Two defining properties
    again: on the underlying sets `listcp(F)` IS the cartesian product
    (`listcp·setifyF ⊑ F(setify)·cp(F)`), and it carries `F`-many `≼`-ordered lists to an
    `F(≼)`-ordered one.  A relator preserves a map and its converse (Lemma 5.1), which is what
    lets the `setify°` of the sort come out from under `F`. -/
public theorem map_sortRel_comp_listcp_le
    {setify : L.obj A ⟶ P A} (hset : Map setify)
    {setifyF : L.obj (F.obj A) ⟶ P (F.obj A)} (hsetF : Map setifyF)
    {ordered : ∀ {X : 𝒜}, (X ⟶ X) → (L.obj X ⟶ L.obj X)} {«≼» : A ⟶ A}
    {listcp : F.obj (L.obj A) ⟶ L.obj (F.obj A)}
    (hnat : listcp ≫ setifyF ⊑ F.map setify ≫ cpMap F A)
    (hordcp : F.map (ordered ≼) ≫ listcp ⊑ listcp ≫ ordered (F.map ≼)) :
    F.map (sortRel L setify ordered ≼) ≫ listcp
      ⊑ cpMap F A ≫ sortRel L setifyF ordered (F.map ≼) := by
  have hshunt : (F.map setify)° ≫ listcp ⊑ cpMap F A ≫ setifyF° := by
    refine (map_shunt_left (F.map_is_map hset) listcp _).mpr ?_
    have hent : listcp ⊑ listcp ≫ setifyF ≫ setifyF° := by
      have := comp_mono_left listcp (entire_id_le hsetF.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc listcp setifyF (setifyF°), ← Cat.assoc (F.map setify) (cpMap F A) (setifyF°)]
    exact comp_mono_right hnat _
  show F.map (setify° ≫ ordered ≼) ≫ listcp ⊑ cpMap F A ≫ (setifyF° ≫ ordered (F.map ≼))
  rw [F.map_comp, F.map_recip_map hset, Cat.assoc]
  refine le_trans (comp_mono_left _ hordcp) ?_
  rw [← Cat.assoc ((F.map setify)°) listcp (ordered (F.map ≼)),
    ← Cat.assoc (cpMap F A) (setifyF°) (ordered (F.map ≼))]
  exact comp_mono_right hshunt (ordered (F.map ≼))

/-- **(8.10)** (book p.203): `(sort(≼)×sort(≼))·merge(≼) ⊑ cup·sort(≼)` — merging two sorted
    lists sorts their union.  `merge(≼)`'s two defining properties do it: a listing of `S` and a
    listing of `T` merge to a listing of `S∪T`, and merging two `≼`-ordered lists gives a
    `≼`-ordered list.  The only step besides those is that `−×−` is a functor, so the pair of
    sorts splits into the pair of listings followed by the pair of order tests. -/
public theorem prodMap_sortRel_comp_merge_le
    {setify : L.obj A ⟶ P A} {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)}
    {«≼» : A ⟶ A} {Pr : RelProd (L.obj A) (L.obj A)}
    {Pr' : RelProd (P A) (P A)}
    {merge : (A ⟶ A) → (Pr.p ⟶ L.obj A)}
    (hmset : prodMap Pr' Pr (setify°) (setify°) ≫ merge ≼ ⊑ cup Pr' ≫ setify°)
    (hmord : prodMap Pr Pr (ordered ≼) (ordered ≼) ≫ merge ≼ ⊑ merge ≼ ≫ ordered ≼) :
    prodMap Pr' Pr (sortRel L setify ordered ≼) (sortRel L setify ordered ≼) ≫ merge ≼
      ⊑ cup Pr' ≫ sortRel L setify ordered ≼ := by
  have hfun : prodMap Pr' Pr (setify° ≫ ordered ≼) (setify° ≫ ordered ≼)
      = prodMap Pr' Pr (setify°) (setify°) ≫ prodMap Pr Pr (ordered ≼) (ordered ≼) := by
    show Pr.pair (Pr'.outl ≫ setify° ≫ ordered ≼) (Pr'.outr ≫ setify° ≫ ordered ≼)
      = Pr.pair (Pr'.outl ≫ setify°) (Pr'.outr ≫ setify°) ≫ prodMap Pr Pr (ordered ≼) (ordered ≼)
    rw [RelProd.pair_prodMap, Cat.assoc, Cat.assoc]
  show prodMap Pr' Pr (setify° ≫ ordered ≼) (setify° ≫ ordered ≼) ≫ merge ≼
    ⊑ cup Pr' ≫ (setify° ≫ ordered ≼)
  rw [hfun, Cat.assoc]
  refine le_trans (comp_mono_left _ hmord) ?_
  rw [← Cat.assoc (prodMap Pr' Pr (setify°) (setify°)) (merge ≼) (ordered ≼),
    ← Cat.assoc (cup Pr') (setify°) (ordered ≼)]
  exact comp_mono_right hmset (ordered ≼)

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
open PowerAllegory

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

/-- `clMem` and `AOP.A5_6_ListCombinators`' `inlistP` are the same predicate read in the two
    argument orders. -/
public theorem clMem_iff_inlistP (w : A) :
    ∀ xs : ConsList Unit A, clMem w xs ↔ ListRel.inlistP xs w
  | ConsList.wrap _ => Iff.rfl
  | ConsList.cons _ xs => or_congr Iff.rfl (clMem_iff_inlistP w xs)

/-- `setifyCL` and `AOP.A5_6_ListCombinators`' `setify` are the SAME arrow — one is written with
    `clMem`, the other with `inlistP`. -/
public theorem setifyCL_eq_setify : (setifyCL : ListRel.dList A ⟶ _) = ListRel.setify := by
  show graph (fun xs => fun w => clMem w xs) = graph (ListRel.inlistP (A := A))
  exact congrArg graph (funext fun xs => funext fun w => propext (clMem_iff_inlistP w xs))

/-- `minlist Q ≜ setify est(Q)`, in the note's own `setify`. -/
public theorem minlist_eq_setify_comp_est (Q : dE A ⟶ dE A) :
    minlist Q = ListRel.setify ≫ est Q := by
  show setifyCL ≫ est Q = ListRel.setify ≫ est Q
  rw [setifyCL_eq_setify]

/-- The one step every §9 program shares (B&dM pp.232, 242): `list(g)minlist(R) ⊑ setify P(g)est(R)`
    — a list of `g`-images has, as a SET, a `P(g)`-image of the set, which is `setify`'s lax
    naturality, and `est(R)` reads the least member off either. -/
public theorem list_comp_minlist_le {B : Type} (g : dE A ⟶ dE B) (R : dE B ⟶ dE B) :
    ListRel.list g ≫ minlist R ⊑ ListRel.setify ≫ powerRel g ≫ est R := by
  rw [minlist_eq_setify_comp_est, ← Cat.assoc, ← Cat.assoc]
  exact comp_mono_right (ListRel.setify_lax_natural g) _

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

/-! ## `ordered(≼)` in `Rel`: the book's definition discharges `hord` and `hos`

  At the list relator, `ordered(≼)` is B&dM's own `⦇[nil, cons·ok]⦈` (p.152, `ListRel.ordered`,
  `ordered_cata`), `ok(a,x) ≡ ∀b∈x. a≼b`.  From that definition the two order hypotheses of
  (8.6) and (8.9) are theorems: `ordered(≼)` is coreflexive, and a subsequence of a `≼`-ordered
  list is `≼`-ordered — for ANY `≼`, because `ok` compares `a` with every later element, not only
  with the next one.  What is left of (8.6) and (8.9) is what they say about `thinlist Q` and
  `filter p`. -/

namespace Freyd.Alg.RelSet.ListRel
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL

variable {A : Type}

/-- An element of a subsequence is an element of the list. -/
public theorem inlistP_of_subseqP : ∀ {ys x : ConsList Unit A}, subseqP ys x →
    ∀ {b : A}, inlistP ys b → inlistP x b
  | ConsList.wrap _, _, _, _, hb => hb.elim
  | ConsList.cons _ _, ConsList.wrap _, h, _, _ => h.elim
  | ConsList.cons a ys, ConsList.cons c x, h, b, hb => by
    rcases h with ⟨rfl, hyx⟩ | h
    · rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (inlistP_of_subseqP hyx hb)
    · exact Or.inr (inlistP_of_subseqP h hb)

/-- A subsequence of a `≼`-ordered list is `≼`-ordered (B&dM p.201 "since subseq·ordered P ⊑
    ordered P"), for any `≼`. -/
public theorem orderedP_of_subseqP («≼» : A → A → Prop) : ∀ {ys x : ConsList Unit A},
    subseqP ys x → orderedP ≼ x → orderedP ≼ ys
  | ConsList.wrap _, _, _, _ => trivial
  | ConsList.cons _ _, ConsList.wrap _, h, _ => h.elim
  | ConsList.cons a ys, ConsList.cons c x, h, ho => by
    rcases h with ⟨rfl, hyx⟩ | h
    · exact ⟨fun b hb => ho.1 b (inlistP_of_subseqP hyx hb), orderedP_of_subseqP ≼ hyx ho.2⟩
    · exact orderedP_of_subseqP ≼ h ho.2

/-- `hos` of (8.6) and (8.9) from the definition: `ordered(≼) subseq ⊑ subseq ordered(≼)`. -/
public theorem ordered_comp_subseq_le («≼» : A → A → Prop) :
    (ordered ≼ : dList A ⟶ dList A) ≫ subseq ⊑ subseq ≫ ordered ≼ :=
  le_iff.mpr fun x ys h => by
    obtain ⟨y, ⟨rfl, hx⟩, hys⟩ := h
    exact ⟨ys, hys, rfl, orderedP_of_subseqP ≼ hys hx⟩

/-- **(8.6)** in `Rel` (book p.201), `sort(≼)·thinlist Q ⊑ thin Q·sort(≼)` with
    `sort(≼) ≜ setify° ordered(≼)` and `ordered(≼)` the book's: only `thinlist Q`'s two conditions
    remain hypotheses. -/
public theorem sort_comp_thinlist_le {«≼» : dE A ⟶ dE A}
    {thinlist : listRelator.obj (dE A) ⟶ listRelator.obj (dE A)} {Q : dE A ⟶ dE A}
    (hsub : thinlist ⊑ subseq) (hspec : thinlist ≫ setify ⊑ setify ≫ thinRel Q) :
    sortRel listRelator setify ordered ≼ ≫ thinlist ⊑ thinRel Q ≫ sortRel listRelator setify ordered ≼ :=
  Freyd.Alg.sortRel_comp_thinlist_le listRelator (graph_map _) (ordered_coreflexive ≼) hsub
    (ordered_comp_subseq_le ≼) hspec

/-- **(8.9)** in `Rel` (book p.203), `sort(≼)·filter p ⊑ E p·sort(≼)`: only `filter p`'s two
    conditions remain hypotheses. -/
public theorem sort_comp_filter_le {«≼» : dE A ⟶ dE A}
    {filterp : listRelator.obj (dE A) ⟶ listRelator.obj (dE A)} {p : dE A ⟶ dE A}
    (hsub : filterp ⊑ subseq) (hspec : filterp ≫ setify ⊑ setify ≫ existsImage p) :
    sortRel listRelator setify ordered ≼ ≫ filterp ⊑ existsImage p ≫ sortRel listRelator setify ordered ≼ :=
  Freyd.Alg.sortRel_comp_filter_le listRelator (graph_map _) (ordered_coreflexive ≼) hsub
    (ordered_comp_subseq_le ≼) hspec

end Freyd.Alg.RelSet.ListRel

/-! ## `merge(≼)` in `Rel` (B&dM Exercise 6.27, p.156)

  `merge(x,[]) = x`, `merge([],y) = y`, and `merge([a]⧺x,[b]⧺y)` is `[a]⧺merge(x,[b]⧺y)` when
  `a ≼ b`, otherwise `[b]⧺merge([a]⧺x,y)`.  With it, (8.10)'s order condition `hmord` is a
  theorem for `≼` a connected preorder; the set condition `hmset` stays a hypothesis, since it
  needs `cup`'s pointwise reading in `Rel`, which nothing here states yet. -/

namespace Freyd.Alg.RelSet.ListRel
open PowerAllegory

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL

variable {A : Type}

/-- `Merge ≼ x y z`: `z` is `merge(≼)(x,y)`, the book's equations read as rules. -/
public inductive Merge («≼» : A → A → Prop) :
    ConsList Unit A → ConsList Unit A → ConsList Unit A → Prop
  | nilr (x : ConsList Unit A) : Merge ≼ x (ConsList.wrap ()) x
  | nill (y : ConsList Unit A) : Merge ≼ (ConsList.wrap ()) y y
  | consl (a b : A) {x y z : ConsList Unit A} : ≼ a b →
      Merge ≼ x (ConsList.cons b y) z →
      Merge ≼ (ConsList.cons a x) (ConsList.cons b y) (ConsList.cons a z)
  | consr (a b : A) {x y z : ConsList Unit A} : ¬ ≼ a b →
      Merge ≼ (ConsList.cons a x) y z →
      Merge ≼ (ConsList.cons a x) (ConsList.cons b y) (ConsList.cons b z)

/-- `merge(≼) : [A]×[A] ⟶ [A]` (B&dM p.156). -/
@[expose] public def merge («≼» : dE A ⟶ dE A) : (relProd (dList A) (dList A)).p ⟶ dList A :=
  fun p z => Merge ≼ p.1 p.2 z

/-- `merge(⊤)=cat` (B&dM p.212): with every pair in order a merge takes all of the first list
    before the second, so `P≜⊤` needs no sorting. -/
public theorem merge_top :
    (merge (topMor (dE A) (dE A)) : (relProd (dList A) (dList A)).p ⟶ dList A) = catR := by
  have hnil : ∀ x : ConsList Unit A, cappend x (ConsList.wrap ()) = x := by
    intro x; induction x with
    | wrap _ => rfl
    | cons a x ih => exact congrArg (ConsList.cons a) ih
  funext p z
  obtain ⟨x, y⟩ := p
  apply propext
  show Merge _ x y z ↔ z = cappend x y
  constructor
  · intro h
    induction h with
    | nilr x => exact (hnil x).symm
    | nill y => rfl
    | consl a b _ _ ih => exact congrArg (ConsList.cons a) ih
    | consr a b hn _ _ => exact absurd (RelSet.topMor_apply a b) hn
  · rintro rfl
    induction x generalizing y with
    | wrap _ => exact Merge.nill y
    | cons a x ih =>
      cases y with
      | wrap _ => rw [hnil]; exact Merge.nilr _
      | cons b y => exact Merge.consl a b (RelSet.topMor_apply a b) (ih _)

/-- Every element of a merge comes from one of the two lists. -/
public theorem inlistP_of_Merge {«≼» : A → A → Prop} {x y z : ConsList Unit A}
    (h : Merge ≼ x y z) {c : A} (hc : inlistP z c) : inlistP x c ∨ inlistP y c := by
  induction h with
  | nilr x => exact Or.inl hc
  | nill y => exact Or.inr hc
  | consl a b _ _ ih =>
    rcases hc with rfl | hc
    · exact Or.inl (Or.inl rfl)
    · rcases ih hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | consr a b _ _ ih =>
    rcases hc with rfl | hc
    · exact Or.inr (Or.inl rfl)
    · rcases ih hc with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Merging two `≼`-ordered lists gives a `≼`-ordered list, `≼` a connected preorder. -/
public theorem orderedP_of_Merge {«≼» : A → A → Prop} (htrans : ∀ a b c, ≼ a b → ≼ b c → ≼ a c)
    (hconn : ∀ a b, ≼ a b ∨ ≼ b a) {x y z : ConsList Unit A} (h : Merge ≼ x y z) :
    orderedP ≼ x → orderedP ≼ y → orderedP ≼ z := by
  induction h with
  | nilr x => exact fun hx _ => hx
  | nill y => exact fun _ hy => hy
  | consl a b hab hm ih =>
    intro hx hy
    refine ⟨fun c hc => ?_, ih hx.2 hy⟩
    rcases inlistP_of_Merge hm hc with hc | hc
    · exact hx.1 c hc
    · rcases hc with rfl | hc
      · exact hab
      · exact htrans _ _ _ hab (hy.1 c hc)
  | consr a b hab hm ih =>
    intro hx hy
    have hba : ≼ b a := (hconn a b).resolve_left hab
    refine ⟨fun c hc => ?_, ih hx hy.2⟩
    rcases inlistP_of_Merge hm hc with hc | hc
    · rcases hc with rfl | hc
      · exact hba
      · exact htrans _ _ _ hba (hx.1 c hc)
    · exact hy.1 c hc

/-- (8.10)'s `hmord` from the definitions: `(ordered(≼)×ordered(≼)) merge(≼) ⊑ merge(≼) ordered(≼)`. -/
public theorem prodMap_ordered_comp_merge_le {«≼» : dE A ⟶ dE A}
    (htrans : ∀ a b c, ≼ a b → ≼ b c → ≼ a c) (hconn : ∀ a b, ≼ a b ∨ ≼ b a) :
    prodMap (relProd (dList A) (dList A)) (relProd (dList A) (dList A)) (ordered ≼) (ordered ≼)
        ≫ merge ≼ ⊑ merge ≼ ≫ ordered ≼ := by
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun ⟨x, y⟩ z h => ?_
  obtain ⟨⟨x', y'⟩, ⟨⟨rfl, hx⟩, ⟨rfl, hy⟩⟩, hm⟩ := h
  exact ⟨z, hm, rfl, orderedP_of_Merge htrans hconn hm hx hy⟩

/-- **(8.10)** in `Rel` (book p.203), `(sort(≼)×sort(≼))·merge(≼) ⊑ cup·sort(≼)`, with
    `merge(≼)` and `ordered(≼)` the book's and `≼` a connected preorder: only the set condition
    `hmset` remains a hypothesis. -/
public theorem prodMap_sort_comp_merge_le {«≼» : dE A ⟶ dE A}
    {Pr' : RelProd (P (dE A)) (P (dE A))}
    (htrans : ∀ a b c, ≼ a b → ≼ b c → ≼ a c) (hconn : ∀ a b, ≼ a b ∨ ≼ b a)
    (hmset : prodMap Pr' (relProd (dList A) (dList A)) (setify°) (setify°) ≫ merge ≼
      ⊑ cup Pr' ≫ setify°) :
    prodMap Pr' (relProd (dList A) (dList A)) (sortRel listRelator setify ordered ≼)
        (sortRel listRelator setify ordered ≼) ≫ merge ≼
      ⊑ cup Pr' ≫ sortRel listRelator setify ordered ≼ :=
  Freyd.Alg.prodMap_sortRel_comp_merge_le listRelator (merge := merge) hmset
    (prodMap_ordered_comp_merge_le htrans hconn)

end Freyd.Alg.RelSet.ListRel
