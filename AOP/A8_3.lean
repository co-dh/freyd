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
end Freyd.Alg
