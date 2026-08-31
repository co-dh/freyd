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

public import AOP.A8_1
public import AOP.A5_6

universe u

namespace Freyd.Alg

/-- The §8.3 setting: `AOP.A5_6`'s tabular/unitary + unguarded-power merge (which gives
    `RelProd`, `cup` and `cpMap` alongside `Λ`) TOGETHER with local completeness (which gives
    `relCata`, `thinRel` and `est`).  Both parents already share `Allegory`, so this is the
    same diamond-safe structure merge as `AOP.A6_2`'s `UnguardedPowerLCDA`. -/
public class TabularUnitaryUnguardedPowerLCDA (𝒜 : Type u) extends
    TabularUnitaryUnguardedDivisionPowerAllegory 𝒜, LocallyCompleteDistributiveAllegory 𝒜

/-- The power/local-completeness side of the merge, so `AOP.A8_1`'s thinning calculus fires
    here unchanged. -/
@[expose] public instance (priority := 100) TabularUnitaryUnguardedPowerLCDA.toUnguardedPowerLCDA
    {𝒜 : Type u} [inst : TabularUnitaryUnguardedPowerLCDA 𝒜] : UnguardedPowerLCDA 𝒜 :=
  { inst with }

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {a l lF : 𝒜}

/-! ## `sort P` and (8.6) -/

/-- `sort P ≜ ordered P·setify°` (book p.199), mirrored `setify° ≫ ordered P`: read the set
    back as one of its `P`-ordered listings.  `l` is the list object `[A]` and
    `setify : [A] ⟶ EA` the map that forgets the order. -/
@[expose] public def sortRel (setify : l ⟶ PowerAllegory.powerObj a) (ordered : l ⟶ l) :
    PowerAllegory.powerObj a ⟶ l := setify° ≫ ordered

/-- **(8.6)** (book p.201): a thinning of the sorted list lists a thinning of the set,
    `sort P·thinlist Q ⊑ thin Q·sort P` mirrored to
    `sortRel setify ordered ≫ thinlist ⊑ thinRel Q ≫ sortRel setify ordered`.  The two
    conditions on `thinlist Q` do all the work: `thinlist Q ⊑ subseq` lets the thinning run
    before the order test, and `thinlist Q·setify ⊑ setify·thin Q` shunts across `setify°`. -/
public theorem sortRel_comp_thinlist_le
    {setify : l ⟶ PowerAllegory.powerObj a} (hset : Map setify)
    {ordered subseq thinlist : l ⟶ l} {Q : a ⟶ a}
    (hord : Coreflexive ordered) (hsub : thinlist ⊑ subseq)
    (hos : ordered ≫ subseq ⊑ subseq ≫ ordered)
    (hspec : thinlist ≫ setify ⊑ setify ≫ thinRel Q) :
    sortRel setify ordered ≫ thinlist ⊑ thinRel Q ≫ sortRel setify ordered := by
  -- the claim of p.201: `thinlist Q` only drops elements, and a subsequence of a `P`-ordered
  -- list is `P`-ordered, so the thinning may run before the order test
  have hclaim : ordered ≫ thinlist ⊑ thinlist ≫ ordered := by
    have h1 : ordered ≫ thinlist ⊑ subseq ≫ ordered :=
      le_trans (comp_mono_left _ hsub) hos
    have h2 : ordered ≫ thinlist ⊑ thinlist := by
      have := comp_mono_right hord thinlist
      rwa [Cat.id_comp] at this
    have h3 := le_inter h1 h2
    rw [coreflexive_comp_inter hord subseq thinlist] at h3
    exact le_trans h3 (comp_mono_right (inter_lb_right _ _) ordered)
  -- `·setify ⊣ ·setify°` on the specification of `thinlist Q`
  have hshunt : setify° ≫ thinlist ⊑ thinRel Q ≫ setify° := by
    refine (map_shunt_left hset thinlist _).mpr ?_
    have hent : thinlist ⊑ thinlist ≫ setify ≫ setify° := by
      have := comp_mono_left thinlist (entire_id_le hset.1)
      rwa [Cat.comp_id] at this
    refine le_trans hent ?_
    rw [← Cat.assoc thinlist setify (setify°), ← Cat.assoc setify (thinRel Q) (setify°)]
    exact comp_mono_right hspec _
  show (setify° ≫ ordered) ≫ thinlist ⊑ thinRel Q ≫ (setify° ≫ ordered)
  rw [Cat.assoc]
  refine le_trans (comp_mono_left _ hclaim) ?_
  rw [← Cat.assoc (setify°) thinlist ordered, ← Cat.assoc (thinRel Q) (setify°) ordered]
  exact comp_mono_right hshunt ordered

/-! ## Lemma 8.1 (book p.202) -/

variable {F : Relator 𝒜 𝒜}

/-- **Lemma 8.1** (book p.202): one sorted list built from sorted arguments, instead of a set
    built and then sorted —
    `filter p·list f·listcp(F)·F(sort P) ⊑ sort P·Λ(p·f·F∈)`, mirrored to
    `F(sort P) ≫ listcp ≫ list f ≫ filter p ⊑ Λ (F(∋) ≫ f ≫ p) ≫ sort P`.
    The sort walks inwards: past `filter p` by (8.9), past `list f` by (8.8), under `F` by
    (8.11), with `f` monotonic on `P` (`FP ⊑ f·P·f°`) closing the change of order. -/
public theorem map_sort_comp_listcp_le
    {f : F.obj a ⟶ a} (hf : Map f) {p P : a ⟶ a}
    {sortP : PowerAllegory.powerObj a ⟶ l}
    {sortF : (F.obj a ⟶ F.obj a) → (PowerAllegory.powerObj (F.obj a) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf : lF ⟶ l} {filterp : l ⟶ l}
    (hsortF : ∀ {X Y : F.obj a ⟶ F.obj a}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono : MonotonicAlg f P)
    (h88 : sortF (f ≫ P ≫ f°) ≫ listf ⊑ powerRel f ≫ sortP)
    (h89 : sortP ≫ filterp ⊑ existsImage p ≫ sortP)
    (h811 : F.map sortP ≫ listcp ⊑ cpMap F a ≫ sortF (F.map P)) :
    F.map sortP ≫ listcp ≫ listf ≫ filterp ⊑ Λ (F.map (∋ a) ≫ f ≫ p) ≫ sortP := by
  -- (8.11): the sort goes under `F`
  have s1 : F.map sortP ≫ listcp ≫ listf ≫ filterp
      ⊑ cpMap F a ≫ sortF (F.map P) ≫ listf ≫ filterp := by
    rw [← Cat.assoc, ← Cat.assoc (cpMap F a)]
    exact comp_mono_right h811 _
  -- `f` monotonic on `P`, and `sort` grows with its order
  have s2 : cpMap F a ≫ sortF (F.map P) ≫ listf ≫ filterp
      ⊑ cpMap F a ≫ sortF (f ≫ P ≫ f°) ≫ listf ≫ filterp :=
    comp_mono_left _ (comp_mono_right (hsortF ((monotonicAlg_iff_sandwich hf).mp hmono)) _)
  -- (8.8): the sort walks past `list f`
  have s3 : cpMap F a ≫ sortF (f ≫ P ≫ f°) ≫ listf ≫ filterp
      ⊑ cpMap F a ≫ powerRel f ≫ sortP ≫ filterp := by
    refine comp_mono_left _ ?_
    rw [← Cat.assoc, ← Cat.assoc (powerRel f)]
    exact comp_mono_right h88 filterp
  -- (8.9): the sort walks past `filter p`
  have s4 : cpMap F a ≫ powerRel f ≫ sortP ≫ filterp
      ⊑ cpMap F a ≫ powerRel f ≫ existsImage p ≫ sortP :=
    comp_mono_left _ (comp_mono_left _ h89)
  -- `E` is a functor and agrees with `P` on maps; the power transpose of a composition
  have s5 : cpMap F a ≫ powerRel f ≫ existsImage p ≫ sortP
      = Λ (F.map (∋ a) ≫ f ≫ p) ≫ sortP := by
    rw [powerRel_map hf, ← Cat.assoc (existsImage f), ← existsImage_comp, ← Cat.assoc,
        show cpMap F a = Λ (F.map (∋ a)) from rfl, Λ_absorption]
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
    {f₁ f₂ : F.obj a ⟶ a} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ P Q : a ⟶ a}
    {sortP : PowerAllegory.powerObj a ⟶ l}
    {sortF : (F.obj a ⟶ F.obj a) → (PowerAllegory.powerObj (F.obj a) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l} {filterp₁ filterp₂ thinlist : l ⟶ l}
    {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)} {mergeP : Pr.p ⟶ l}
    (hsortF : ∀ {X Y : F.obj a ⟶ F.obj a}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : MonotonicAlg f₁ P) (hmono₂ : MonotonicAlg f₂ P)
    (h88₁ : sortF (f₁ ≫ P ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sortP)
    (h88₂ : sortF (f₂ ≫ P ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sortP)
    (h89₁ : sortP ≫ filterp₁ ⊑ existsImage p₁ ≫ sortP)
    (h89₂ : sortP ≫ filterp₂ ⊑ existsImage p₂ ≫ sortP)
    (h811 : F.map sortP ≫ listcp ⊑ cpMap F a ≫ sortF (F.map P))
    (h810 : prodMap Pr' Pr sortP sortP ≫ mergeP ⊑ cup Pr' ≫ sortP)
    (h86 : sortP ≫ thinlist ⊑ thinRel Q ≫ sortP) :
    F.map sortP ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ mergeP ≫ thinlist
      ⊑ Λ (F.map (∋ a) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q ≫ sortP := by
  have l1 : (F.map sortP ≫ listcp) ≫ (listf₁ ≫ filterp₁)
      ⊑ Λ (F.map (∋ a) ≫ f₁ ≫ p₁) ≫ sortP := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le hf₁ hsortF hmono₁ h88₁ h89₁ h811
  have l2 : (F.map sortP ≫ listcp) ≫ (listf₂ ≫ filterp₂)
      ⊑ Λ (F.map (∋ a) ≫ f₂ ≫ p₂) ≫ sortP := by
    rw [Cat.assoc]
    exact map_sort_comp_listcp_le hf₂ hsortF hmono₂ h88₂ h89₂ h811
  -- Lemma 8.1 under the common prefix `F(sort P)·listcp(F)`, at each `fᵢ`, `pᵢ`
  have pre : F.map sortP ≫ listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)
        ≫ mergeP ≫ thinlist
      ⊑ Pr.pair (Λ (F.map (∋ a) ≫ f₁ ≫ p₁) ≫ sortP) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂) ≫ sortP)
        ≫ mergeP ≫ thinlist := by
    rw [← Cat.assoc (F.map sortP) listcp
          (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ mergeP ≫ thinlist),
        ← Cat.assoc (F.map sortP ≫ listcp)
          (Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂)) (mergeP ≫ thinlist)]
    exact comp_mono_right
      (le_trans (RelProd.comp_pair_le _ _ _) (RelProd.pair_mono l1 l2)) _
  -- `Λ` of the union is the pair of the two transposes, closed by `cup`
  have hsplit : Λ (F.map (∋ a) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)))
      = Pr'.pair (Λ (F.map (∋ a) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂)) ≫ cup Pr' := by
    rw [DistributiveAllegory.comp_union_distrib, Λ_union]
  have key : Pr.pair (Λ (F.map (∋ a) ≫ f₁ ≫ p₁) ≫ sortP) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂) ≫ sortP)
        ≫ mergeP ≫ thinlist
      ⊑ Λ (F.map (∋ a) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q ≫ sortP := by
    rw [hsplit, ← RelProd.pair_prodMap (P := Pr') (Q := Pr)
          (Λ (F.map (∋ a) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂)) sortP sortP,
        Cat.assoc (Pr'.pair (Λ (F.map (∋ a) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂)))
          (prodMap Pr' Pr sortP sortP) (mergeP ≫ thinlist),
        Cat.assoc (Pr'.pair (Λ (F.map (∋ a) ≫ f₁ ≫ p₁)) (Λ (F.map (∋ a) ≫ f₂ ≫ p₂)))
          (cup Pr') (thinRel Q ≫ sortP)]
    refine comp_mono_left _ ?_
    have a1 : prodMap Pr' Pr sortP sortP ≫ mergeP ≫ thinlist
        ⊑ (cup Pr' ≫ sortP) ≫ thinlist := by
      rw [← Cat.assoc (prodMap Pr' Pr sortP sortP) mergeP thinlist]
      exact comp_mono_right h810 thinlist
    have a2 : (cup Pr' ≫ sortP) ≫ thinlist ⊑ cup Pr' ≫ thinRel Q ≫ sortP := by
      rw [Cat.assoc (cup Pr') sortP thinlist]
      exact comp_mono_left _ h86
    exact le_trans a1 a2
  exact le_trans pre key

/-- **THEOREM 8.2** (book p.203): a fold on SORTED LISTS of partial solutions, thinned at
    every step, refines the thinning specification —
    `min R·Λ⦇S⦈ ⊒ minlist R·⦇thinlist Q·merge P·⟨g₁,g₂⟩·listcp(F)⦈`, mirrored to
    `relCata (listcp(F) ≫ ⟨g₁,g₂⟩ ≫ merge P ≫ thinlist Q) ≫ minlist R ⊑ Λ ⦇S⦈ ≫ est R`.
    Corollary 8.1 (`thinning_est`) puts `thin Q` inside the fold, (8.7) splits the minimum
    into `sort P` followed by `minlist R`, and `relCata_le_comp` fuses `sort P` into the
    algebra — that fusion condition being `sortedAlg_fusion`.  No set is ever built. -/
public theorem thinningList (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {f₁ f₂ : F.obj a ⟶ a} (hf₁ : Map f₁) (hf₂ : Map f₂) {p₁ p₂ P Q R : a ⟶ a}
    {sortP : PowerAllegory.powerObj a ⟶ l}
    {sortF : (F.obj a ⟶ F.obj a) → (PowerAllegory.powerObj (F.obj a) ⟶ lF)}
    {listcp : F.obj l ⟶ lF} {listf₁ listf₂ : lF ⟶ l} {filterp₁ filterp₂ thinlist : l ⟶ l}
    {minlist : l ⟶ a} {Pr : RelProd l l}
    {Pr' : RelProd (PowerAllegory.powerObj a) (PowerAllegory.powerObj a)} {mergeP : Pr.p ⟶ l}
    (hQR : Q ⊑ R) (hreflQ : 𝟙 a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hm₁ : MonotonicAlg (f₁ ≫ p₁) Q) (hm₂ : MonotonicAlg (f₂ ≫ p₂) Q)
    (hsortF : ∀ {X Y : F.obj a ⟶ F.obj a}, X ⊑ Y → sortF X ⊑ sortF Y)
    (hmono₁ : MonotonicAlg f₁ P) (hmono₂ : MonotonicAlg f₂ P)
    (h88₁ : sortF (f₁ ≫ P ≫ f₁°) ≫ listf₁ ⊑ powerRel f₁ ≫ sortP)
    (h88₂ : sortF (f₂ ≫ P ≫ f₂°) ≫ listf₂ ⊑ powerRel f₂ ≫ sortP)
    (h89₁ : sortP ≫ filterp₁ ⊑ existsImage p₁ ≫ sortP)
    (h89₂ : sortP ≫ filterp₂ ⊑ existsImage p₂ ≫ sortP)
    (h811 : F.map sortP ≫ listcp ⊑ cpMap F a ≫ sortF (F.map P))
    (h810 : prodMap Pr' Pr sortP sortP ≫ mergeP ⊑ cup Pr' ≫ sortP)
    (h86 : sortP ≫ thinlist ⊑ thinRel Q ≫ sortP)
    (h87 : sortP ≫ minlist ⊑ est R) :
    relCata (listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ mergeP ≫ thinlist)
        ≫ minlist
      ⊑ Λ (relCata ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ est R := by
  -- the union of two `Q`-monotonic algebras is `Q`-monotonic
  have hmonoS : MonotonicAlg ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) Q := by
    show F.map Q ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ⊑ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂)) ≫ Q
    rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
    exact union_mono hm₁ hm₂
  have hfuse :
      relCata (listcp ≫ Pr.pair (listf₁ ≫ filterp₁) (listf₂ ≫ filterp₂) ≫ mergeP ≫ thinlist)
        ⊑ relCata (Λ (F.map (∋ a) ≫ ((f₁ ≫ p₁) ∪ (f₂ ≫ p₂))) ≫ thinRel Q) ≫ sortP := by
    refine relCata_le_comp I ?_
    rw [Cat.assoc]
    exact sortedAlg_fusion hf₁ hf₂ hsortF hmono₁ hmono₂ h88₁ h88₂ h89₁ h89₂ h811 h810 h86
  refine le_trans (comp_mono_right hfuse minlist) ?_
  rw [Cat.assoc]
  exact le_trans (comp_mono_left _ h87) (thinning_est hFr I hQR hreflQ htransQ htransR hmonoS)

end Freyd.Alg
