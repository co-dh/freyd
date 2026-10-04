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
-- (8.9) and (8.11) in `Rel`: the book's `filter(p)` is §7.7's, `cp(F)` at `L+E×X` is §7.4's.
public import AOP.A7_7_Filter
public import AOP.A7_4_CylinderPaths
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

/-- CONNECTED (B&dM p.153, "a connected preorder"): any two elements are comparable one way or the
    other, `Π ⊑ R ∪ R°`.  §8.3's sort order and (8.5)'s thinning order are connected preorders. -/
@[expose] public def Connected (R : A ⟶ A) : Prop := topMor A A ⊑ R ∪ R°

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

/-- `g` only drops elements (`g ⊑ subseq`) and a subsequence of a `≼`-ordered list is
    `≼`-ordered, so `g` may run before the order test. -/
public theorem ordered_comp_le_of_subseq
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A} {subseq g : L.obj A ⟶ L.obj A}
    (hord : Coreflexive (ordered ≼)) (hsub : g ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼) :
    ordered ≼ ≫ g ⊑ g ≫ ordered ≼ := by
  have h1 : ordered ≼ ≫ g ⊑ subseq ≫ ordered ≼ := le_trans (comp_mono_left _ hsub) hos
  have h2 : ordered ≼ ≫ g ⊑ g := by
    have := comp_mono_right hord g
    rwa [Cat.id_comp] at this
  have h3 := le_inter h1 h2
  rw [coreflexive_comp_inter hord subseq g] at h3
  exact le_trans h3 (comp_mono_right (inter_lb_right _ _) (ordered ≼))

/-- Step 1: `ordered_comp_le_of_subseq` under `setify°`. -/
public theorem sortRel_comp_le_step1 (setify : L.obj A ⟶ P A)
    {ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)} {«≼» : A ⟶ A} {subseq g : L.obj A ⟶ L.obj A}
    (hord : Coreflexive (ordered ≼)) (hsub : g ⊑ subseq)
    (hos : ordered ≼ ≫ subseq ⊑ subseq ≫ ordered ≼) :
    setify° ≫ ordered ≼ ≫ g ⊑ setify° ≫ g ≫ ordered ≼ :=
  comp_mono_left _ (ordered_comp_le_of_subseq L hord hsub hos)

/-- `·setify ⊣ ·setify°` shunts `g`'s specification `g·setify ⊑ setify·T` across the
    converse. -/
public theorem setify_conv_comp_le {setify : L.obj A ⟶ P A} (hset : Map setify)
    {g : L.obj A ⟶ L.obj A} {T : P A ⟶ P A} (hspec : g ≫ setify ⊑ setify ≫ T) :
    setify° ≫ g ⊑ T ≫ setify° := by
  refine (map_shunt_left hset g _).mpr ?_
  have hent : g ⊑ g ≫ setify ≫ setify° := by
    have := comp_mono_left g (entire_id_le hset.1)
    rwa [Cat.comp_id] at this
  refine le_trans hent ?_
  rw [← Cat.assoc g setify (setify°), ← Cat.assoc setify T (setify°)]
  exact comp_mono_right hspec _

/-- Step 2: `setify_conv_comp_le` before the order test. -/
public theorem sortRel_comp_le_step2 {setify : L.obj A ⟶ P A}
    (hset : Map setify) (ordered : (A ⟶ A) → (L.obj A ⟶ L.obj A)) («≼» : A ⟶ A)
    {g : L.obj A ⟶ L.obj A}
    {T : P A ⟶ P A} (hspec : g ≫ setify ⊑ setify ≫ T) :
    setify° ≫ g ≫ ordered ≼ ⊑ T ≫ setify° ≫ ordered ≼ := by
  rw [← Cat.assoc (setify°) g (ordered ≼), ← Cat.assoc T (setify°) (ordered ≼)]
  exact comp_mono_right (setify_conv_comp_le L hset hspec) (ordered ≼)

variable {F : Relator 𝒜 𝒜}

/-- The union of two algebras monotonic on `Q` is monotonic on `Q`. -/
public theorem monoAlg_union {S₁ S₂ : F.obj A ⟶ A} {Q : A ⟶ A}
    (h₁ : Freyd.Alg.MonoAlg S₁ Q) (h₂ : Freyd.Alg.MonoAlg S₂ Q) :
    Freyd.Alg.MonoAlg (S₁ ∪ S₂) Q := by
  show F.map Q ≫ (S₁ ∪ S₂) ⊑ (S₁ ∪ S₂) ≫ Q
  rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
  exact union_mono h₁ h₂

/-! ## The note's `thinlist-laws`: (8.7), (8.8) and (8.9) discharged

  (8.6)-(8.11) are not interface conditions at all once `sort(≼)` is unfolded to `setify° ordered(≼)`: they follow, in
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

    The guards go with these results: swapped, (8.5) is false already at `[a,b]` with `b Q a` and
    `¬ a Q b`, where `bump` would return `[a]` and the least member is `b`.  The note prints
    `bump(Q)` from `bumpRel_wrap`/`bumpRel_cons`, so it cannot drift from this. -/

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

/-- `bump(Q)`, its operator applied in brackets as `minlist(Q)` is: a bare `bump Q` loses the `Q` a
    junction label prints. -/
notation:max "bump(" Q ")" => Freyd.Alg.RelSet.CL.bumpRel Q

/-- `bump(Q)` on an empty list: the new element alone. -/
public theorem bumpRel_wrap (Q : dE A ⟶ dE A) (a : A) (u : Unit) (ys : ConsList Unit A) :
    bumpRel Q (a, ConsList.wrap u) ys ↔ ys = ConsList.cons a (ConsList.wrap ()) := Iff.rfl

/-- `bump(Q)` on `[b]⧺xs`: keep `a` if it beats `b`, keep `b` if it beats `a`, else keep both. -/
public theorem bumpRel_cons (Q : dE A ⟶ dE A) (a b : A) (xs ys : ConsList Unit A) :
    bumpRel Q (a, ConsList.cons b xs) ys ↔
      (Q a b ∧ ys = ConsList.cons a xs) ∨ (Q b a ∧ ys = ConsList.cons b xs)
        ∨ (¬ Q a b ∧ ¬ Q b a ∧ ys = ConsList.cons a (ConsList.cons b xs)) := Iff.rfl

/-- The algebra `[nil, bump Q]`. -/
@[expose] public def bumpAlg (Q : dE A ⟶ dE A) : Fobj Unit A (dCL Unit A) ⟶ dCL Unit A :=
  fun u ys => match u with
    | Sum.inl _ => ys = ConsList.wrap ()
    | Sum.inr p => bumpRel Q p ys

/-- `thinlist Q ≜ ⦇[nil,bump Q]⦈`. -/
@[expose] public def thinlist (Q : dE A ⟶ dE A) : dCL Unit A ⟶ dCL Unit A := cataR (bumpAlg Q)

/-- `thinlist(Q) ≜ ⦇[nil,bump(Q)]⦈`, the junction written out. -/
public theorem thinlist_eq (Q : dE A ⟶ dE A) :
    thinlist Q = ⦇(junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (bumpRel Q)
      : (F Unit A).obj (dCL Unit A) ⟶ dCL Unit A)⦈ := by
  have h : bumpAlg Q = (junc (sumCop (dL Unit) ⟨A × ConsList Unit A⟩) wrapR (bumpRel Q)
      : (F Unit A).obj (dCL Unit A) ⟶ dCL Unit A) := by
    funext u ys
    cases u with
    | inl d =>
      refine propext ⟨fun h => Or.inl ⟨d, rfl, h⟩, fun h => ?_⟩
      rcases h with ⟨_, h1, h2⟩ | ⟨_, h1, _⟩
      · cases h1; exact h2
      · cases h1
    | inr p =>
      refine propext ⟨fun h => Or.inr ⟨p, rfl, h⟩, fun h => ?_⟩
      rcases h with ⟨_, h1, _⟩ | ⟨_, h1, h2⟩
      · cases h1
      · cases h1; exact h2
  unfold thinlist
  rw [h, cataR_eq_relCata]

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

/-- `Preorder(Q)` in `Rel`, pointwise: reflexive and transitive. -/
public theorem preorder_apply {Q : dE A ⟶ dE A} (h : Preorder Q) :
    (∀ a, Q a a) ∧ ∀ a b c, Q a b → Q b c → Q a c :=
  ⟨fun a => le_iff.mp h.1 a a rfl, fun a b c hab hbc => le_iff.mp h.2 a c ⟨b, hab, hbc⟩⟩

/-- `Connected(Q)` in `Rel`, pointwise: any two elements are comparable. -/
public theorem connected_apply {Q : dE A ⟶ dE A} (h : Freyd.Alg.Connected Q) :
    ∀ a b, Q a b ∨ Q b a := fun a b => by
  have := le_iff.mp h a b (topMor_apply a b)
  rwa [union_apply] at this

/-- **(8.5)** (B&dM p.200): for a CONNECTED preorder `Q` and a non-empty list,
    `thinlist Q xs = [minlist Q xs]` — thinning comes down to one element. -/
public theorem thinlist_eq_singleton_minlist {Q : dE A ⟶ dE A} (hQ : Preorder Q)
    (hc : Freyd.Alg.Connected Q) (a : A) (xs ys : ConsList Unit A) :
    thinlist Q (ConsList.cons a xs) ys
      ↔ ∃ w, minlist Q (ConsList.cons a xs) w ∧ ys = ConsList.cons w (ConsList.wrap ()) := by
  obtain ⟨hrefl, htrans⟩ := preorder_apply hQ
  have hconn := connected_apply hc
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

/-- What B&dM p.200 asks of an implementation of `thin(Q)` on lists, and all it asks: it only
    drops elements, and on the underlying set it is a thinning.  Every other premise the abstract
    (8.6) carries is a theorem about `setify` and `ordered(≼)`, so this pair is what is left. -/
public structure IsThinlist (Q : dE A ⟶ dE A) (thinlist : dList A ⟶ dList A) : Prop where
  /-- `thinlist(Q)⊑subseq`: the result is a subsequence of the input. -/
  sub : thinlist ⊑ subseq
  /-- `thinlist(Q) setify⊑setify thin(Q)`: as a set, the result is a thinning of the input's. -/
  spec : thinlist ≫ setify ⊑ setify ≫ thinRel Q

/-- `IsThinlist` unfolded: the two conditions of B&dM p.200. -/
public theorem isThinlist_iff (Q : dE A ⟶ dE A) (thinlist : dList A ⟶ dList A) :
    IsThinlist Q thinlist ↔ thinlist ⊑ subseq ∧ thinlist ≫ setify ⊑ setify ≫ thinRel Q :=
  ⟨fun h => ⟨h.sub, h.spec⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `bump(Q)` keeps a subsequence: the output of `thinlist(Q)` is a subsequence of its input. -/
public theorem subseqP_of_thinlist (Q : dE A ⟶ dE A) :
    ∀ {x ys : ConsList Unit A}, thinlist Q x ys → subseqP ys x
  | ConsList.wrap _, _, h => by rw [thinlist_wrap] at h; subst h; exact subseqP.nil _
  | ConsList.cons c d, ys, h => by
    obtain ⟨r', hr', hb⟩ := (thinlist_cons Q c d ys).mp h
    have ih := subseqP_of_thinlist Q hr'
    cases r' with
    | wrap _ => rw [bumpRel_wrap] at hb; subst hb; exact Or.inl ⟨rfl, subseqP.nil _⟩
    | cons b xs =>
      rcases (bumpRel_cons Q c b xs ys).mp hb with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩
      · exact Or.inl ⟨rfl, subseqP.of_cons ih⟩
      · exact Or.inr ih
      · exact Or.inl ⟨rfl, ih⟩

/-- For a preorder `Q`, every member of the input of `thinlist(Q)` has a `Q`-lower bound in its
    output: reflexivity covers a kept element, transitivity passes on what a bumped head covered. -/
public theorem thinlist_covers {Q : dE A ⟶ dE A} (hQ : Preorder Q) :
    ∀ {x ys : ConsList Unit A}, thinlist Q x ys → ∀ z, inlistP x z → ∃ w, Q w z ∧ inlistP ys w
  | ConsList.wrap _, _, _, _, hz => hz.elim
  | ConsList.cons c d, ys, h, z, hz => by
    have hrefl : ∀ a, Q a a := fun a => le_iff.mp hQ.1 a a rfl
    have htrans : ∀ a b e, Q a b → Q b e → Q a e := fun a b e hab hbe =>
      le_iff.mp hQ.2 a e ⟨b, hab, hbe⟩
    obtain ⟨r', hr', hb⟩ := (thinlist_cons Q c d ys).mp h
    have ih := thinlist_covers hQ hr'
    cases r' with
    | wrap _ =>
      rw [bumpRel_wrap] at hb; subst hb
      rcases hz with rfl | hz
      · exact ⟨z, hrefl z, Or.inl rfl⟩
      · obtain ⟨_, _, hw⟩ := ih z hz; exact hw.elim
    | cons b xs =>
      rcases (bumpRel_cons Q c b xs ys).mp hb with ⟨hcb, rfl⟩ | ⟨hbc, rfl⟩ | ⟨_, _, rfl⟩
      · rcases hz with rfl | hz
        · exact ⟨z, hrefl z, Or.inl rfl⟩
        · obtain ⟨w, hwz, hw⟩ := ih z hz
          rcases hw with rfl | hw
          · exact ⟨c, htrans c w z hcb hwz, Or.inl rfl⟩
          · exact ⟨w, hwz, Or.inr hw⟩
      · rcases hz with rfl | hz
        · exact ⟨b, hbc, Or.inl rfl⟩
        · exact ih z hz
      · rcases hz with rfl | hz
        · exact ⟨z, hrefl z, Or.inl rfl⟩
        · obtain ⟨w, hwz, hw⟩ := ih z hz; exact ⟨w, hwz, Or.inr hw⟩

/-- B&dM's `thinlist(Q) ≜ ⦇[nil, bump(Q)]⦈` (p.200) implements `thin(Q)` when `Q` is a preorder. -/
public theorem isThinlist_thinlist {Q : dE A ⟶ dE A} (hQ : Preorder Q) :
    IsThinlist Q (thinlist Q) where
  sub := le_iff.mpr fun _ _ h => subseqP_of_thinlist Q h
  spec := le_iff.mpr fun x S h => by
    obtain ⟨ys, hys, rfl⟩ := h
    exact ⟨inlistP x, rfl, fun _ hy => inlistP_of_subseqP (subseqP_of_thinlist Q hys) hy,
      thinlist_covers hQ hys⟩

/-- `thinlist(Q)` only drops elements, so it may run before the order test. -/
public theorem ordered_comp_thinlist_le {«≼» Q : dE A ⟶ dE A} (hQ : Preorder Q) :
    ordered ≼ ≫ thinlist Q ⊑ thinlist Q ≫ ordered ≼ :=
  ordered_comp_le_of_subseq listRelator (ordered_coreflexive ≼) (isThinlist_thinlist hQ).sub
    (ordered_comp_subseq_le ≼)

/-- `thinlist(Q)` lists a thinning of the set it lists, read across `setify°`. -/
public theorem setify_conv_comp_thinlist_le {Q : dE A ⟶ dE A} (hQ : Preorder Q) :
    setify° ≫ thinlist Q ⊑ thinRel Q ≫ setify° :=
  setify_conv_comp_le listRelator (graph_map _) (isThinlist_thinlist hQ).spec

/-- **(8.6)** in `Rel` (book p.201) at B&dM's own `thinlist(Q) ≜ ⦇[nil, bump(Q)]⦈`: the one
    hypothesis is the book's, that `Q` is a preorder. -/
public theorem sort_comp_bump_thinlist_le {«≼» Q : dE A ⟶ dE A} (hQ : Preorder Q) :
    sortRel listRelator setify ordered ≼ ≫ thinlist Q ⊑ thinRel Q ≫ sortRel listRelator setify ordered ≼ :=
  calc sortRel listRelator setify ordered ≼ ≫ thinlist Q = setify° ≫ ordered ≼ ≫ thinlist Q := by
        show (setify° ≫ ordered ≼) ≫ thinlist Q = _
        exact Cat.assoc _ _ _
    _ ⊑ setify° ≫ thinlist Q ≫ ordered ≼ := comp_mono_left _ (ordered_comp_thinlist_le hQ)
    _ ⊑ thinRel Q ≫ setify° ≫ ordered ≼ := by
        rw [← Cat.assoc (setify°) (thinlist Q) (ordered ≼), ← Cat.assoc (thinRel Q) (setify°)]
        exact comp_mono_right (setify_conv_comp_thinlist_le hQ) _
    _ = thinRel Q ≫ sortRel listRelator setify ordered ≼ := rfl

calc_steps sort_comp_bump_thinlist_le

/-- **(8.7)** in `Rel` (book p.203), `sort(≼)·minlist R ⊑ min R`, with no hypothesis: `minlist(R)`
    is `setify est(R)`, so `ordered(≼)` drops by coreflexivity and `setify° setify` by `setify`
    being a function. -/
public theorem sort_comp_minlist_le {«≼» : dE A ⟶ dE A} (R : dE A ⟶ dE A) :
    sortRel listRelator setify ordered ≼ ≫ minlist R ⊑ est R := by
  have hset : Map (setify : dList A ⟶ P (dE A)) := graph_map _
  rw [minlist_eq_setify_comp_est]
  show (setify° ≫ ordered ≼) ≫ setify ≫ est R ⊑ est R
  rw [Cat.assoc]
  have hord : ordered ≼ ≫ setify ≫ est R ⊑ setify ≫ est R := by
    have := comp_mono_right (ordered_coreflexive ≼) (setify ≫ est R)
    rwa [Cat.id_comp] at this
  refine le_trans (comp_mono_left _ hord) ?_
  rw [← Cat.assoc]
  have := comp_mono_right hset.2 (est R)
  rwa [Cat.id_comp] at this

/-- `filter(p)` only drops elements. -/
public theorem subseqP_filtCL (p : A → Bool) : ∀ x : ConsList Unit A, subseqP (Filter.filtCL p x) x
  | ConsList.wrap _ => trivial
  | ConsList.cons a x => by
    show subseqP (Filter.fStep p a (Filter.filtCL p x)) (ConsList.cons a x)
    unfold Filter.fStep
    split
    · exact Or.inl ⟨rfl, subseqP_filtCL p x⟩
    · exact subseqP.weaken (subseqP_filtCL p x)

/-- `filter(p)` keeps exactly the elements that pass `p`. -/
public theorem inlistP_filtCL (p : A → Bool) (w : A) : ∀ x : ConsList Unit A,
    inlistP (Filter.filtCL p x) w ↔ inlistP x w ∧ p w = true
  | ConsList.wrap _ => ⟨False.elim, fun h => h.1.elim⟩
  | ConsList.cons a x => by
    show inlistP (Filter.fStep p a (Filter.filtCL p x)) w ↔ (w = a ∨ inlistP x w) ∧ p w = true
    unfold Filter.fStep
    split
    · rename_i h
      show (w = a ∨ inlistP (Filter.filtCL p x) w) ↔ _
      rw [inlistP_filtCL p w x]
      constructor
      · rintro (rfl | ⟨hx, hw⟩)
        · exact ⟨Or.inl rfl, h⟩
        · exact ⟨Or.inr hx, hw⟩
      · rintro ⟨rfl | hx, hw⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hw⟩
    · rename_i h
      rw [inlistP_filtCL p w x]
      constructor
      · rintro ⟨hx, hw⟩
        exact ⟨Or.inr hx, hw⟩
      · rintro ⟨rfl | hx, hw⟩
        · exact Bool.noConfusion (h.symm.trans hw)
        · exact ⟨hx, hw⟩

/-- **(8.9)** in `Rel` (book p.201), `sort(≼)·filter p ⊑ E p·sort(≼)`, with no hypothesis:
    `filter(p)` is the book's (§7.7, `Filter.filter`, a function by `filter_emerges`), and `p` is
    the coreflexive of the test, so `filter(p)` only drops elements and lists `E(p)` of the set. -/
public theorem sort_comp_filter_le {«≼» : dE A ⟶ dE A} (p : A → Bool) :
    sortRel listRelator setify ordered ≼ ≫ Filter.filter p
      ⊑ existsImage (GCTakeWhile.pcor p) ≫ sortRel listRelator setify ordered ≼ := by
  rw [(Filter.filter_eq_cata p).trans (Filter.filter_emerges p).symm]
  refine Freyd.Alg.sortRel_comp_filter_le listRelator (graph_map _) (ordered_coreflexive ≼) ?_
    (ordered_comp_subseq_le ≼) ?_
  · exact le_iff.mpr fun x y h => by
      obtain rfl := (h : y = Filter.filtCL p x)
      exact subseqP_filtCL p x
  · refine le_iff.mpr fun x S h => ?_
    obtain ⟨y, rfl, rfl⟩ := h
    refine ⟨inlistP x, rfl, (existsImage_apply _ _ _).mpr (funext fun w => propext ?_)⟩
    rw [inlistP_filtCL p w x]
    exact ⟨fun ⟨hx, hw⟩ => ⟨w, hx, rfl, hw⟩, fun ⟨_, hx, rfl, hw⟩ => ⟨hx, hw⟩⟩

/-! ## `listcp(F)` and (8.11)

  B&dM p.202 leave `listcp(F) : F[X]⟶[FX]` as an exercise for each linear functor (Exercise 8.19);
  every §8.4-8.6 instance uses `FX = L+E×X`, where it is `wrap+cpr`: a leaf becomes the one-element
  list, a label paired with a list becomes the list of the label paired with each element. -/

/-- `x ∈ list(g)(xs)` iff `x` is `g` of an element of `xs`. -/
public theorem inlistP_cmap {B : Type} (g : A → B) (b : B) : ∀ xs : ConsList Unit A,
    inlistP (cmap g xs) b ↔ ∃ a, inlistP xs a ∧ b = g a
  | ConsList.wrap _ => ⟨False.elim, fun ⟨_, h, _⟩ => h.elim⟩
  | ConsList.cons a xs => by
    show (b = g a ∨ inlistP (cmap g xs) b) ↔ ∃ c, (c = a ∨ inlistP xs c) ∧ b = g c
    rw [inlistP_cmap g b xs]
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨a, Or.inl rfl, rfl⟩
      · exact ⟨c, Or.inr hc, rfl⟩
    · rintro ⟨c, rfl | hc, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨c, hc, rfl⟩

/-- A map monotonic from `≼` to `R` sends a `≼`-ordered list to an `R`-ordered one. -/
public theorem orderedP_cmap {B : Type} (g : A → B) («≼» : A → A → Prop) (R : B → B → Prop)
    (hg : ∀ a c, ≼ a c → R (g a) (g c)) : ∀ xs, orderedP ≼ xs → orderedP R (cmap g xs)
  | ConsList.wrap _, _ => trivial
  | ConsList.cons a xs, ⟨ha, hxs⟩ =>
    ⟨fun b hb => by
      obtain ⟨c, hc, rfl⟩ := (inlistP_cmap g b xs).mp hb
      exact hg a c (ha c hc), orderedP_cmap g ≼ R hg xs hxs⟩

/-- B&dM's `cpr : E×[X] ⟶ [E×X]` (p.126) pointwise, landing in the right summand of `F`. -/
@[expose] public def cprInr {L E X : Type} (s : E × ConsList Unit X) : ConsList Unit (L ⊕ E × X) :=
  cmap (fun x => Sum.inr (s.1, x)) s.2

/-- `listcp ≜ wrap+cpr` pointwise. -/
@[expose] public def listcpFn {L E X : Type} : L ⊕ E × ConsList Unit X → ConsList Unit (L ⊕ E × X)
  | Sum.inl d => ConsList.cons (Sum.inl d) (ConsList.wrap ())
  | Sum.inr s => cprInr s

/-- **`listcp(F) : F[X]⟶[FX]`** at the linear `FX = L+E×X` (B&dM p.201, Exercise 8.19):
    `wrap` on the leaf, `cpr` on the pair. -/
@[expose] public def listcp {L E X : Type} :
    (CL.F L E).obj (listRelator.obj (dE X)) ⟶ listRelator.obj ((CL.F L E).obj (dE X)) :=
  graph listcpFn

/-- **(8.11)** in `Rel` (book p.201), `listcp(F)·F(sort ≼) ⊑ sort(F(≼))·cp(F)`, at
    `FX = L+E×X`, with no hypothesis: `listcp` lists exactly the set `cp(F)` builds, in an order
    `F(≼)` sorts because the label is the same in every element. -/
public theorem Fmap_sort_comp_listcp_le {L E X : Type} {«≼» : dE X ⟶ dE X} :
    (CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp
      ⊑ cpMap (CL.F L E) (dE X) ≫ sortRel listRelator setify ordered ((CL.F L E).map ≼) := by
  rw [Tuple.cpMap_eq_graph]
  refine le_iff.mpr fun u ys h => ?_
  obtain ⟨w, hw, rfl⟩ := h
  refine ⟨Tuple.cpFn L E u, rfl, listcpFn w, ?_⟩
  rcases u with d | ⟨e, S⟩ <;> rcases w with d' | ⟨e', xs⟩
  · obtain rfl := (hw : d = d')
    exact ⟨funext fun y => propext ⟨Or.inl, fun h => h.elim id False.elim⟩, rfl,
      fun _ hb => hb.elim, trivial⟩
  · exact (hw : False).elim
  · exact (hw : False).elim
  · obtain ⟨rfl, z, rfl, rfl, ho⟩ := (hw : e = e' ∧ _)
    exact ⟨funext fun y => propext (inlistP_cmap _ y z).symm, rfl,
      orderedP_cmap _ ≼ _ (fun _ _ h => ⟨rfl, h⟩) z ho⟩

/-- `list(F(R))` on one label's row: `cmap (e,·) xs` is related to `zs` exactly when `zs` is the
    row of `e` over a `list(R)`-image of `xs`. -/
public theorem listP_Fmap_cmap_inr {L E X Y : Type} (R : dE X ⟶ dE Y) (e : E) :
    ∀ (xs : ConsList Unit X) (zs : ConsList Unit (L ⊕ E × Y)),
      listP ((CL.F L E).map R) (cmap (fun x => Sum.inr (e, x)) xs) zs ↔
        ∃ ys, listP R xs ys ∧ zs = cmap (fun y => Sum.inr (e, y)) ys
  | ConsList.wrap _, ConsList.wrap _ => ⟨fun _ => ⟨ConsList.wrap (), trivial, rfl⟩, fun _ => trivial⟩
  | ConsList.wrap _, ConsList.cons _ _ => ⟨False.elim, fun ⟨ys, h, hz⟩ => by
      cases ys with
      | wrap _ => exact nomatch hz
      | cons _ _ => exact h.elim⟩
  | ConsList.cons _ _, ConsList.wrap _ => ⟨False.elim, fun ⟨ys, h, hz⟩ => by
      cases ys with
      | wrap _ => exact h.elim
      | cons _ _ => exact nomatch hz⟩
  | ConsList.cons x xs, ConsList.cons z zs => by
    show (Fmap L E R (Sum.inr (e, x)) z ∧ _) ↔ _
    constructor
    · rintro ⟨hz, h⟩
      obtain ⟨ys, hys, rfl⟩ := (listP_Fmap_cmap_inr R e xs zs).mp h
      rcases z with _ | ⟨e', y⟩
      · exact hz.elim
      · obtain ⟨rfl, hxy⟩ := hz
        exact ⟨ConsList.cons y ys, ⟨hxy, hys⟩, rfl⟩
    · rintro ⟨ys, hys, hz⟩
      cases ys with
      | wrap _ => exact hys.elim
      | cons y ys =>
        obtain ⟨hxy, hys⟩ := hys
        cases hz
        exact ⟨⟨rfl, hxy⟩, (listP_Fmap_cmap_inr R e xs _).mpr ⟨ys, hys, rfl⟩⟩

-- Stated in the relators the bead's two lanes spell (`L+E×𝟙` then `list`, and `L+E×(𝟙 list)`),
-- because that is the statement the diagram exporter asks for the `listcp` bead.
/-- **`listcp` is STRICTLY natural**: `F(list(R)) listcp = listcp list(F(R))`. -/
public theorem listcp_strictNatural {L E : Type} :
    StrictNatural
      (Relator.comp (Relator.sum (Relator.const (dL L))
          (Relator.prod (Relator.const (dE E)) (Relator.idRelator RelSet.{0}))) listRelator)
      (Relator.sum (Relator.const (dL L))
          (Relator.prod (Relator.const (dE E))
            (Relator.comp (Relator.idRelator RelSet.{0}) listRelator)))
      (fun a : RelSet.{0} => listcp (L := L) (E := E) (X := a.carrier)) := by
  intro x y R
  show (Relator.sum (Relator.const (dL L)) (Relator.prod (Relator.const (dE E))
      (Relator.idRelator RelSet.{0}))).map (listRelator.map R) ≫ listcp
    = listcp ≫ listRelator.map ((Relator.sum (Relator.const (dL L)) (Relator.prod
      (Relator.const (dE E)) (Relator.idRelator RelSet.{0}))).map R)
  rw [F_eq_sum_prod, F_eq_sum_prod]
  apply hom_ext
  intro u zs
  rcases u with d | ⟨e, xs⟩
  · constructor
    · rintro ⟨w, hw, rfl⟩
      rcases w with d' | _
      · obtain rfl : d = d' := hw
        exact ⟨_, rfl, rfl, trivial⟩
      · exact (hw : False).elim
    · rintro ⟨v, rfl, hv⟩
      rcases zs with _ | ⟨z, zs⟩
      · exact (hv : False).elim
      · obtain ⟨hz, ht⟩ := hv
        rcases z with d' | _
        · obtain rfl : d = d' := hz
          cases zs with
          | wrap u => exact ⟨Sum.inl d, rfl, rfl⟩
          | cons _ _ => exact ht.elim
        · exact (hz : False).elim
  · constructor
    · rintro ⟨w, hw, rfl⟩
      rcases w with _ | ⟨e', ys⟩
      · exact (hw : False).elim
      · obtain ⟨rfl, hys⟩ := hw
        exact ⟨_, rfl, (listP_Fmap_cmap_inr R e xs _).mpr ⟨ys, hys, rfl⟩⟩
    · rintro ⟨v, rfl, hv⟩
      obtain ⟨ys, hys, rfl⟩ := (listP_Fmap_cmap_inr R e xs zs).mp hv
      exact ⟨Sum.inr (e, ys), ⟨rfl, hys⟩, rfl⟩

/-- **`cp(F)` is STRICTLY natural** at `FX = L+E×X`, in the relators its lanes spell:
    `Tuple.cpMap_strict_natural` read through `F = L+E×𝟙` (`F_eq_sum_prod`). -/
public theorem cpMap_F_strictNatural {L E : Type} :
    StrictNatural
      (Relator.comp (Relator.sum (Relator.const (dL L))
          (Relator.prod (Relator.const (dE E)) (Relator.idRelator RelSet.{0}))) powerRelator)
      (Relator.sum (Relator.const (dL L))
          (Relator.prod (Relator.const (dE E))
            (Relator.comp (Relator.idRelator RelSet.{0}) powerRelator)))
      (fun a : RelSet.{0} => cpMap (CL.F L E) a) := by
  intro a b R
  show (Relator.sum (Relator.const (dL L)) (Relator.prod (Relator.const (dE E))
      (Relator.idRelator RelSet.{0}))).map (powerRel R) ≫ cpMap (CL.F L E) b
    = cpMap (CL.F L E) a ≫ powerRel ((Relator.sum (Relator.const (dL L)) (Relator.prod
      (Relator.const (dE E)) (Relator.idRelator RelSet.{0}))).map R)
  rw [F_eq_sum_prod, F_eq_sum_prod]
  exact Tuple.cpMap_strict_natural L E R

end Freyd.Alg.RelSet.ListRel

/-! ## `merge(≼)` in `Rel` (B&dM Exercise 6.27, p.156)

  `merge(x,[]) = x`, `merge([],y) = y`, and `merge([a]⧺x,[b]⧺y)` is `[a]⧺merge(x,[b]⧺y)` when
  `a ≼ b`, otherwise `[b]⧺merge([a]⧺x,y)`.  With it both of (8.10)'s conditions are theorems:
  the set condition `hmset` for any `≼` (a merge has exactly the elements of its two inputs), the
  order condition `hmord` for `≼` a connected preorder. -/

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

-- The book's `merge`, not Lean's qualified name: another `merge` is in scope.
open Lean PrettyPrinter in
@[app_unexpander merge] public meta def unexpandMerge : Unexpander
  | `($_:ident $a) => `($(mkIdent `merge) $a)
  | `($_:ident) => `($(mkIdent `merge))
  | _ => throw ()

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

/-- Every element of either list is an element of their merge. -/
public theorem inlistP_Merge {«≼» : A → A → Prop} {x y z : ConsList Unit A}
    (h : Merge ≼ x y z) {c : A} (hc : inlistP x c ∨ inlistP y c) : inlistP z c := by
  induction h with
  | nilr x => exact hc.elim id False.elim
  | nill y => exact hc.elim False.elim id
  | consl a b _ _ ih =>
    rcases hc with (rfl | hc) | hc
    · exact Or.inl rfl
    · exact Or.inr (ih (Or.inl hc))
    · exact Or.inr (ih (Or.inr hc))
  | consr a b _ _ ih =>
    rcases hc with hc | (rfl | hc)
    · exact Or.inr (ih (Or.inl hc))
    · exact Or.inl rfl
    · exact Or.inr (ih (Or.inr hc))

/-- (8.10)'s `hmset` from the definitions: a listing of `S` and a listing of `T` merge to a listing
    of `S∪T`, `(setify°×setify°) merge(≼) ⊑ cup setify°`, for any `≼`. -/
public theorem prodMap_setify_recip_comp_merge_le {«≼» : dE A ⟶ dE A} :
    prodMap (relProd (P (dE A)) (P (dE A))) (relProd (dList A) (dList A)) (setify°) (setify°)
        ≫ merge ≼ ⊑ cup (relProd (P (dE A)) (P (dE A))) ≫ setify° := by
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun ⟨S, T⟩ z h => ?_
  obtain ⟨⟨x, y⟩, hxy, hm⟩ := h
  obtain ⟨hx, hy⟩ := hxy
  refine ⟨fun w => S w ∨ T w, ?_, ?_⟩
  · rw [cup, Λ_eq_classifier]
    show _ = _
    funext w
    apply propext
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨S, rfl, h⟩
      · exact Or.inr ⟨T, rfl, h⟩
    · rintro (⟨_, rfl, h⟩ | ⟨_, rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr h
  · show _ = _
    change S = inlistP x at hx
    change T = inlistP y at hy
    subst hx hy
    funext w
    exact propext ⟨fun hw => inlistP_Merge hm hw, fun hw => inlistP_of_Merge hm hw⟩

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
    `merge(≼)` and `ordered(≼)` the book's and `≼` a connected preorder: both conditions on
    `merge(≼)` are theorems, so the order's two properties are all that is left. -/
public theorem prodMap_sort_comp_merge_le {«≼» : dE A ⟶ dE A}
    (h : Preorder ≼) (hc : Freyd.Alg.Connected ≼) :
    prodMap (relProd (P (dE A)) (P (dE A))) (relProd (dList A) (dList A))
        (sortRel listRelator setify ordered ≼) (sortRel listRelator setify ordered ≼) ≫ merge ≼
      ⊑ cup (relProd (P (dE A)) (P (dE A))) ≫ sortRel listRelator setify ordered ≼ :=
  Freyd.Alg.prodMap_sortRel_comp_merge_le listRelator (merge := merge)
    prodMap_setify_recip_comp_merge_le
    (prodMap_ordered_comp_merge_le (preorder_apply h).2 (connected_apply hc))

/-- An element of `list(g)(x)` is `g` of an element of `x`. -/
public theorem inlistP_of_listP_graph {B : Type} (g : A → B) :
    ∀ {x : ConsList Unit A} {y : ConsList Unit B}, listP (graph g : dE A ⟶ dE B) x y →
      ∀ {b' : B}, inlistP y b' → ∃ b, inlistP x b ∧ b' = g b
  | ConsList.wrap _, ConsList.wrap _, _, _, hb => hb.elim
  | ConsList.wrap _, ConsList.cons _ _, h, _, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h, _, _ => h.elim
  | ConsList.cons a x, ConsList.cons c y, ⟨hac, hxy⟩, b', hb => by
    rcases hb with rfl | hb
    · exact ⟨a, Or.inl rfl, hac⟩
    · obtain ⟨b, hbx, rfl⟩ := inlistP_of_listP_graph g hxy hb
      exact ⟨b, Or.inr hbx, rfl⟩

/-- `list(g)` carries a `g≼g°`-ordered list to a `≼`-ordered one. -/
public theorem orderedP_of_listP_graph {B : Type} (g : A → B) («≼» : B → B → Prop) :
    ∀ {x : ConsList Unit A} {y : ConsList Unit B}, listP (graph g : dE A ⟶ dE B) x y →
      orderedP ((graph g : dE A ⟶ dE B) ≫ ≼ ≫ (graph g)°) x → orderedP ≼ y
  | ConsList.wrap _, ConsList.wrap _, _, _ => trivial
  | ConsList.wrap _, ConsList.cons _ _, h, _ => h.elim
  | ConsList.cons _ _, ConsList.wrap _, h, _ => h.elim
  | ConsList.cons a x, ConsList.cons c y, ⟨hac, hxy⟩, ⟨hx1, hx2⟩ => by
    refine ⟨fun b' hb' => ?_, orderedP_of_listP_graph g ≼ hxy hx2⟩
    obtain ⟨b, hb, rfl⟩ := inlistP_of_listP_graph g hxy hb'
    obtain ⟨_, rfl, _, h, rfl⟩ := hx1 b hb
    have hc : c = g a := hac
    subst hc
    exact h

/-- **(8.8)** in `Rel` (book p.203), `sort(g≼g°)·list g ⊑ P g·sort(≼)` for a function `g`, with
    no hypothesis: `setify`'s naturality and the order condition both follow from `list`'s
    definition. -/
public theorem sort_comp_list_le {B : Type} (g : A → B) {«≼» : dE B ⟶ dE B} :
    sortRel listRelator setify ordered ((graph g : dE A ⟶ dE B) ≫ ≼ ≫ (graph g)°)
        ≫ list (graph g) ⊑ powerRel (graph g) ≫ sortRel listRelator setify ordered ≼ := by
  have hnat : list (graph g : dE A ⟶ dE B) ≫ setify ⊑ setify ≫ existsImage (graph g) := by
    have := setify_lax_natural (graph g : dE A ⟶ dE B)
    rwa [powerRel_map (graph_map g)] at this
  have hordf : ordered ((graph g : dE A ⟶ dE B) ≫ ≼ ≫ (graph g)°) ≫ list (graph g)
      ⊑ list (graph g) ≫ ordered ≼ :=
    le_iff.mpr fun x y h => by
      obtain ⟨_, ⟨rfl, hx⟩, hxy⟩ := h
      exact ⟨y, hxy, rfl, orderedP_of_listP_graph g ≼ hxy hx⟩
  exact Freyd.Alg.sortRel_comp_listMap_le listRelator (graph_map _) (graph_map _)
    (ordered := fun R => ordered R) (graph_map g) hnat hordf

/-- A list ordered by `X` is ordered by any larger `Y`. -/
public theorem orderedP_mono {X Y : A → A → Prop} (h : ∀ a b, X a b → Y a b) :
    ∀ x : ConsList Unit A, orderedP X x → orderedP Y x
  | ConsList.wrap _, _ => trivial
  | ConsList.cons a x, ⟨ha, hx⟩ => ⟨fun b hb => h a b (ha b hb), orderedP_mono h x hx⟩

/-- `sort` is monotonic in the order: a larger order admits more listings. -/
public theorem sortRel_mono {X Y : dE A ⟶ dE A} (h : X ⊑ Y) :
    sortRel listRelator setify ordered X ⊑ sortRel listRelator setify ordered Y :=
  comp_mono_left _ (le_iff.mpr fun x _ ⟨hxy, ho⟩ =>
    ⟨hxy, orderedP_mono (fun a b hab => le_iff.mp h a b hab) x ho⟩)

/-- **Lemma 8.1** in `Rel` (book p.202) at `FX = L+E×X`: one sorted list built from sorted
    arguments, instead of a set built and then sorted — the one hypothesis is the book's, `f`
    monotonic on `≼`.  The sort walks inwards one law at a time: under `F` by (8.11), `f`
    monotonic, past `list(f)` by (8.8), past `filter(p)` by (8.9), then `E(f) = P(f)` and the
    transpose absorbs `E(fp)`. -/
public theorem Fmap_sort_comp_listcp_list_filter_le {L E : Type} (f : L ⊕ E × A → A)
    (p : A → Bool) {«≼» : dE A ⟶ dE A} (hmono : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f) ≼) :
    (CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp ≫ list (graph f)
        ≫ Filter.filter p
      ⊑ Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f ≫ GCTakeWhile.pcor p)
        ≫ sortRel listRelator setify ordered ≼ :=
  calc (CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp ≫ list (graph f)
          ≫ Filter.filter p
        ⊑ cpMap (CL.F L E) (dE A) ≫ sortRel listRelator setify ordered ((CL.F L E).map ≼)
          ≫ list (graph f) ≫ Filter.filter p := by
        rw [← Cat.assoc, ← Cat.assoc (cpMap (CL.F L E) (dE A))]
        exact comp_mono_right Fmap_sort_comp_listcp_le _
    _ ⊑ cpMap (CL.F L E) (dE A)
          ≫ sortRel listRelator setify ordered (graph f ≫ ≼ ≫ (graph f)°)
          ≫ list (graph f) ≫ Filter.filter p :=
        comp_mono_left _ (comp_mono_right
          (sortRel_mono ((Freyd.Alg.monoAlg_iff_sandwich (graph_map f)).mp hmono)) _)
    _ ⊑ cpMap (CL.F L E) (dE A) ≫ powerRel (graph f) ≫ sortRel listRelator setify ordered ≼
          ≫ Filter.filter p := by
        refine comp_mono_left _ ?_
        rw [← Cat.assoc, ← Cat.assoc (powerRel (graph f))]
        exact comp_mono_right (sort_comp_list_le f) _
    _ ⊑ cpMap (CL.F L E) (dE A) ≫ powerRel (graph f) ≫ existsImage (GCTakeWhile.pcor p)
          ≫ sortRel listRelator setify ordered ≼ :=
        comp_mono_left _ (comp_mono_left _ (sort_comp_filter_le p))
    _ = cpMap (CL.F L E) (dE A) ≫ existsImage (graph f) ≫ existsImage (GCTakeWhile.pcor p)
          ≫ sortRel listRelator setify ordered ≼ := by rw [powerRel_map (graph_map f)]
    _ = cpMap (CL.F L E) (dE A) ≫ existsImage (graph f ≫ GCTakeWhile.pcor p)
          ≫ sortRel listRelator setify ordered ≼ := by
        rw [← Cat.assoc (existsImage (graph f)), ← existsImage_comp]
    _ = Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f ≫ GCTakeWhile.pcor p)
          ≫ sortRel listRelator setify ordered ≼ := by
        rw [← Cat.assoc, show cpMap (CL.F L E) (dE A) = Λ ((CL.F L E).map (∋ (dE A))) from rfl,
          Λ_absorption]

calc_steps Fmap_sort_comp_listcp_list_filter_le

/-- `filter` by the test every element passes keeps every list. -/
public theorem filter_true : Filter.filter (fun _ : A => true) = 𝟙 (dList A) := by
  have h : ∀ x : ConsList Unit A, Filter.filtCL (fun _ => true) x = x := by
    intro x
    induction x with
    | wrap D => cases D; rfl
    | cons a x ih =>
      show Filter.fStep _ a (Filter.filtCL _ x) = _
      unfold Filter.fStep
      split
      · rw [ih]
      · rename_i hn; exact Bool.noConfusion hn
  rw [(Filter.filter_eq_cata _).trans (Filter.filter_emerges _).symm]
  apply hom_ext; intro x y
  rw [id_apply]
  exact ⟨fun hy => ((hy : y = _).trans (h x)).symm, fun hy => show y = _ from hy ▸ (h x).symm⟩

/-- The coreflexive of the test every element passes is the identity. -/
public theorem pcor_true : GCTakeWhile.pcor (fun _ : A => true) = 𝟙 (dE A) := by
  apply hom_ext; intro x y
  rw [id_apply]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- `⊤` is a preorder: it relates everything. -/
public theorem preorder_topMor : Preorder (topMor (dE A) (dE A)) :=
  ⟨le_iff.mpr fun a b _ => RelSet.topMor_apply a b, le_iff.mpr fun a b _ => RelSet.topMor_apply a b⟩

/-- `⊤` is connected: it relates everything. -/
public theorem connected_topMor : Freyd.Alg.Connected (topMor (dE A) (dE A)) :=
  le_iff.mpr fun a b _ => Or.inl (RelSet.topMor_apply a b)

/-- The fusion side condition of **Theorem 8.2** in `Rel` (book p.203) at `FX = L+E×X`: sorting
    the candidate set turns the thinning algebra into an algebra on sorted lists.  Lemma 8.1 at
    `f₁,p₁` and at `f₂,p₂` puts the sort inside `F`, (8.10) exchanges `merge(≼)` for the union of
    the two sorted sets, `Λ` of the union splits by `cup`, and (8.6) exchanges `thinlist(Q)` for
    `thin(Q)`. -/
public theorem sortedAlg_fusion {L E : Type} (f₁ f₂ : L ⊕ E × A → A) (p₁ p₂ : A → Bool)
    {«≼» Q : dE A ⟶ dE A} (hQ : Preorder Q) (hP : Preorder ≼) (hc : Freyd.Alg.Connected ≼)
    (hmono₁ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₁) ≼)
    (hmono₂ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₂) ≼) :
    (CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp
        ≫ (relProd (dList A) (dList A)).pair (list (graph f₁) ≫ Filter.filter p₁)
          (list (graph f₂) ≫ Filter.filter p₂) ≫ merge ≼ ≫ thinlist Q
      ⊑ Λ ((CL.F L E).map (∋ (dE A))
          ≫ ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂)))
        ≫ thinRel Q ≫ sortRel listRelator setify ordered ≼ :=
  calc (CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp
          ≫ (relProd (dList A) (dList A)).pair (list (graph f₁) ≫ Filter.filter p₁)
            (list (graph f₂) ≫ Filter.filter p₂) ≫ merge ≼ ≫ thinlist Q
        ⊑ (relProd (dList A) (dList A)).pair
            ((CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp
              ≫ list (graph f₁) ≫ Filter.filter p₁)
            ((CL.F L E).map (sortRel listRelator setify ordered ≼) ≫ listcp
              ≫ list (graph f₂) ≫ Filter.filter p₂)
          ≫ merge ≼ ≫ thinlist Q := by
        rw [← Cat.assoc ((CL.F L E).map _) listcp, ← Cat.assoc (_ ≫ listcp)]
        refine comp_mono_right (le_trans (RelProd.comp_pair_le _ _ _) (le_of_eq ?_)) _
        rw [Cat.assoc, Cat.assoc]
    _ ⊑ (relProd (dList A) (dList A)).pair
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₁ ≫ GCTakeWhile.pcor p₁)
              ≫ sortRel listRelator setify ordered ≼)
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₂ ≫ GCTakeWhile.pcor p₂)
              ≫ sortRel listRelator setify ordered ≼)
          ≫ merge ≼ ≫ thinlist Q :=
        comp_mono_right (RelProd.pair_mono (Fmap_sort_comp_listcp_list_filter_le f₁ p₁ hmono₁)
          (Fmap_sort_comp_listcp_list_filter_le f₂ p₂ hmono₂)) _
    _ = (relProd (P (dE A)) (P (dE A))).pair
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₁ ≫ GCTakeWhile.pcor p₁))
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₂ ≫ GCTakeWhile.pcor p₂))
          ≫ prodMap (relProd (P (dE A)) (P (dE A))) (relProd (dList A) (dList A))
            (sortRel listRelator setify ordered ≼) (sortRel listRelator setify ordered ≼)
          ≫ merge ≼ ≫ thinlist Q := by
        rw [← RelProd.pair_prodMap (P := relProd (P (dE A)) (P (dE A)))
          (Q := relProd (dList A) (dList A)), Cat.assoc]
    _ ⊑ (relProd (P (dE A)) (P (dE A))).pair
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₁ ≫ GCTakeWhile.pcor p₁))
            (Λ ((CL.F L E).map (∋ (dE A)) ≫ graph f₂ ≫ GCTakeWhile.pcor p₂))
          ≫ cup (relProd (P (dE A)) (P (dE A))) ≫ sortRel listRelator setify ordered ≼
          ≫ thinlist Q := by
        refine comp_mono_left _ ?_
        rw [← Cat.assoc (prodMap _ _ _ _) (merge ≼), ← Cat.assoc (cup _)]
        exact comp_mono_right (prodMap_sort_comp_merge_le hP hc) _
    _ = Λ (((CL.F L E).map (∋ (dE A)) ≫ graph f₁ ≫ GCTakeWhile.pcor p₁)
          ∪ ((CL.F L E).map (∋ (dE A)) ≫ graph f₂ ≫ GCTakeWhile.pcor p₂))
        ≫ sortRel listRelator setify ordered ≼ ≫ thinlist Q := by
        rw [Λ_union _ _ (relProd (P (dE A)) (P (dE A))), Cat.assoc]
    _ = Λ ((CL.F L E).map (∋ (dE A))
          ≫ ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂)))
        ≫ sortRel listRelator setify ordered ≼ ≫ thinlist Q := by
        rw [DistributiveAllegory.comp_union_distrib]
    _ ⊑ Λ ((CL.F L E).map (∋ (dE A))
          ≫ ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂)))
        ≫ thinRel Q ≫ sortRel listRelator setify ordered ≼ :=
        comp_mono_left _ (sort_comp_bump_thinlist_le hQ)

calc_steps sortedAlg_fusion

/-- `cup` read pointwise in `Rel`: the union of the two sets of the pair. -/
public theorem cup_apply {a : RelSet.{0}} (q : (relProd (P a) (P a)).p.carrier) (Z : (P a).carrier) :
    cup (relProd (P a) (P a)) q Z ↔ Z = fun v => q.1 v ∨ q.2 v := by
  unfold cup
  rw [Λ_eq_classifier]
  have : (fun v => (((relProd (P a) (P a)).outl ≫ ∋ a) ∪ ((relProd (P a) (P a)).outr ≫ ∋ a)) q v)
      = fun v => q.1 v ∨ q.2 v := by
    funext v
    simp only [union_apply, comp_apply]
    apply propext; constructor
    · rintro (⟨y, rfl, hv⟩ | ⟨y, rfl, hv⟩)
      · exact Or.inl hv
      · exact Or.inr hv
    · rintro (h | h)
      · exact Or.inl ⟨_, rfl, h⟩
      · exact Or.inr ⟨_, rfl, h⟩
  exact iff_of_eq (congrArg (fun W => Z = W) this)

/-- **`cup` is LAX NATURAL** in `Rel` (B&dM Ex 5.20): `(P(R)×P(R)) cup ⊑ cup P(R)` — the unions of
    two pairs of sets related by `P(R)` are related by `P(R)`.  Stated in the relators the diagram
    exporter reads off `cup`'s two ends. -/
public theorem cup_laxNatural :
    LaxNatural (Relator.comp (Relator.idRelator RelSet.{0}) powerRelator)
      (Relator.prod (Relator.comp (Relator.idRelator RelSet.{0}) powerRelator)
        (Relator.comp (Relator.idRelator RelSet.{0}) powerRelator))
      (fun a => cup (relProd (P a) (P a))) := by
  intro A B R
  refine le_iff.mpr fun p Y h => ?_
  obtain ⟨X, hX, hc⟩ := h
  have h' : prodMap (relProd _ _) (relProd _ _) (powerRel R) (powerRel R) p X := hX
  rw [prodMap_eq_rprodMap] at h'
  have h2 : powerRel R p.1 X.1 ∧ powerRel R p.2 X.2 := h'
  have hY := (cup_apply X Y).mp hc
  show (cup (relProd (P A) (P A)) ≫ powerRel R) p Y
  refine ⟨fun v => p.1 v ∨ p.2 v, (cup_apply p _).mpr rfl, ?_⟩
  rw [powerRel_reading, powerRel_reading] at h2
  rw [powerRel_reading]
  subst hY
  obtain ⟨⟨r1, s1⟩, r2, s2⟩ := h2
  refine ⟨fun w hw => ?_, fun s hs => ?_⟩
  · rcases hw with hw | hw
    · obtain ⟨s, hs, hR⟩ := r1 w hw; exact ⟨s, Or.inl hs, hR⟩
    · obtain ⟨s, hs, hR⟩ := r2 w hw; exact ⟨s, Or.inr hs, hR⟩
  · rcases hs with hs | hs
    · obtain ⟨w, hw, hR⟩ := s1 s hs; exact ⟨w, Or.inl hw, hR⟩
    · obtain ⟨w, hw, hR⟩ := s2 s hs; exact ⟨w, Or.inr hw, hR⟩

/-- **THEOREM 8.2** in `Rel` (book p.203) at `FX = L+E×X`: a fold on SORTED LISTS of partial
    solutions, thinned at every step, refines the thinning specification —
    `min R·Λ⦇f₁p₁ ∪ f₂p₂⦈ ⊒ minlist R·⦇thinlist Q·merge ≼·⟨g₁,g₂⟩·listcp(F)⦈` with
    `gᵢ = list(fᵢ) filter(pᵢ)`, mirrored.  The hypotheses are the book's three: `Q` a preorder
    with `Q ⊑ R` and both `fᵢpᵢ` monotonic on `Q`, `≼` a connected preorder with both `fᵢ`
    monotonic on it; `R` a preorder for `min R`.  `relCata_le_comp` fuses `sort ≼` into the
    algebra by `sortedAlg_fusion`, (8.7) reads the minimum off the sorted list, and Corollary 8.1
    puts `thin Q` inside the fold.  No set is ever built. -/
public theorem thinningList {L E : Type} (f₁ f₂ : L ⊕ E × A → A) (p₁ p₂ : A → Bool)
    {«≼» Q R : dE A ⟶ dE A} (hQR : Q ⊑ R) (hQ : Preorder Q) (hR : Preorder R)
    (hm₁ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₁ ≫ GCTakeWhile.pcor p₁) Q)
    (hm₂ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₂ ≫ GCTakeWhile.pcor p₂) Q)
    (hP : Preorder ≼) (hc : Freyd.Alg.Connected ≼)
    (hmono₁ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₁) ≼)
    (hmono₂ : Freyd.Alg.MonoAlg (F := CL.F L E) (graph f₂) ≼) :
    relCata (I := CL.initial L E) (listcp ≫ (relProd (dList A) (dList A)).pair
        (list (graph f₁) ≫ Filter.filter p₁) (list (graph f₂) ≫ Filter.filter p₂)
        ≫ merge ≼ ≫ thinlist Q) ≫ minlist R
      ⊑ Λ (relCata (I := CL.initial L E)
          ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂))) ≫ est R :=
  calc _ ⊑ (relCata (I := CL.initial L E) (Λ ((CL.F L E).map (∋ (dE A))
            ≫ ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂)))
            ≫ thinRel Q) ≫ sortRel listRelator setify ordered ≼) ≫ minlist R :=
        comp_mono_right (relCata_le_comp (CL.initial L E) (by
          rw [Cat.assoc]; exact sortedAlg_fusion f₁ f₂ p₁ p₂ hQ hP hc hmono₁ hmono₂)) _
    _ ⊑ relCata (I := CL.initial L E) (Λ ((CL.F L E).map (∋ (dE A))
            ≫ ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂)))
            ≫ thinRel Q) ≫ est R :=
        le_trans (le_of_eq (Cat.assoc _ _ _)) (comp_mono_left _ (sort_comp_minlist_le R))
    _ ⊑ Λ (relCata (I := CL.initial L E)
          ((graph f₁ ≫ GCTakeWhile.pcor p₁) ∪ (graph f₂ ≫ GCTakeWhile.pcor p₂))) ≫ est R :=
        thinning_est (CL.initial L E) hQR hQ hR (Freyd.Alg.monoAlg_union hm₁ hm₂)

calc_steps thinningList

end Freyd.Alg.RelSet.ListRel
