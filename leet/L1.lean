/-
  LeetCode 1 — Two Sum, derived from its specification.

  Spec: `twoSum(t) ≜ zipIdx pairs(t) : [Int] ⟶ Nat × Nat` with
  `pairs(t) ≜ ⟨∋,∋⟩ (j<k ∧ a+b=t)? (π₂×π₂)`: index the list, take two members `((a,j),(b,k))`,
  keep those with `j<k` and `a+b=t`, return `(j,k)`.

  Derivation, one law per step (diagram order; `some°` unwraps a `some` answer):
      twoSum(t)
    = zipIdx sorted? pairs(t)                 zipIdx_sorted: `zipIdx sorted? = zipIdx`
    = zipIdx sorted? splits memPre(t)         pairs_split: on a sorted list a pair `j<k` is a split
                                              `pre ++ (b,k) :: post` with `(t-b,j) ∈ pre`
    ⊒ zipIdx sorted? splits hit(t,∅)          hit_memPre: a hit of `toMap(pre)` at `t-b` is in `pre`
    = zipIdx splits hit(t,∅)                  zipIdx_sorted
    ⊒ zipIdx go(t,∅) some°                    go_splits: fold law (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`
                                              over `List`, `X = scanSpec(t)` (`scan_le`), at `m = ∅`
    = prog(t) some°                           prog ≜ zipIdx go(t,∅)
  `toMap(m)(pre)` is the left fold of `insert` over `pre`, which is the map `go` carries.  Both `⊒`
  steps keep the domain (`dom_hit`, `dom_go`), so `dom` of the same chain gives completeness.

  `∋` is core's `Membership.mem : List A → A → Prop`, already a relation `[A] ⟶ A`.

  Mathlib-free.  Axioms: `prog_sound`/`prog_complete` ⊆ {propext, Classical.choice, Quot.sound};
  `Classical.choice` is inherited from core's `Std.HashMap.getElem?_insert`/`getElem?_empty`.
-/
import AOP.A6_GenFold
import AOP.A6_2
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL

/-- Indexed lists, their splits `(pre,(b,k))`, and answers `(j,k)`. -/
abbrev IL : RelSet.{0} := ⟨List (Int × Nat)⟩
abbrev Split : RelSet.{0} := ⟨List (Int × Nat) × (Int × Nat)⟩
abbrev Ans : RelSet.{0} := ⟨Nat × Nat⟩
/-- Scans: answers as a function of the start map. -/
abbrev Scan : RelSet.{0} := ⟨Std.HashMap Int Nat → Option (Nat × Nat)⟩

/-! ## The specification -/

def zipIdxR : (⟨List Int⟩ : RelSet.{0}) ⟶ IL := graph List.zipIdx

/-- `π₂ : (a,j) ↦ j`, the index of an indexed element. -/
def π₂ : (⟨Int × Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩ := graph fun (_, j) => j

/-- `pairs(t) ≜ ⟨∋,∋⟩ (j<k ∧ a+b=t)? (π₂×π₂)`: two members `((a,j),(b,k))` taken independently,
    kept when `j<k` and `a+b=t`, answered by their indices. -/
def pairs (t : Int) : IL ⟶ Ans :=
  rpair (Membership.mem : (⟨List (Int × Nat)⟩ : RelSet.{0}) ⟶ ⟨Int × Nat⟩) Membership.mem ≫ corefl (fun ((a, j), (b, k)) => j < k ∧ a + b = t) ≫ rprodMap π₂ π₂

/-- `twoSum(t) ≜ zipIdx pairs(t)`. -/
def twoSum (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ Ans := zipIdxR ≫ pairs t

/-! ## The program: one hash-map scan over `zipIdx(xs)` -/

/-- The scan's step at `(x,k)`, given the scan `r` of the rest: from map `m`, a hit
    `m[t-x]? = some j` answers `(j,k)`, a miss runs `r` from `m` with `x ↦ k` recorded. -/
def scanStep (t : Int) : Int × Nat → (Std.HashMap Int Nat → Option (Nat × Nat)) →
    Std.HashMap Int Nat → Option (Nat × Nat)
  | (x, k), r, m => match m[t - x]? with
    | some j => some (j, k)
    | none => r (m.insert x k)

/-- `go(t) ≜ ⦇[const none, scanStep(t)]⦈`, the right fold over `List`: its result is a function of
    the start map, so the left-to-right map threads through it and a hit stops the scan. -/
def go (t : Int) : List (Int × Nat) → Std.HashMap Int Nat → Option (Nat × Nat) :=
  List.foldr (scanStep t) fun _ => none

/-- `prog(t)(xs)`: the scan over `zipIdx(xs)` from the empty map. -/
def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := go t xs.zipIdx {}

/-- `some° : Option (Nat × Nat) ⟶ Nat × Nat`, the answer inside a `some`. -/
def unsome : (⟨Option (Nat × Nat)⟩ : RelSet.{0}) ⟶ Ans := (graph some)°

/-! ## The relations the derivation passes through -/

/-- `sorted?`: indices strictly increase along the list. -/
def sortedR : IL ⟶ IL := corefl fun L => L.Pairwise fun (_, j) (_, k) => j < k

/-- `splits : L ↦ (pre,(b,k))` whenever `L = pre ++ (b,k) :: post`. -/
def splits : IL ⟶ Split := fun L (pre, bk) => ∃ post, L = pre ++ bk :: post

/-- `memPre(t) : (pre,(b,k)) ↦ (j,k)` for a member `(t-b,j)` of `pre`. -/
def memPre (t : Int) : Split ⟶ Ans := fun (pre, (b, k)) (j, k') => k' = k ∧ (t - b, j) ∈ pre

/-- `toMap(m)(pre)`: the left fold of `insert` over `pre` from `m` — the map `go` has built. -/
def toMap (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) : Std.HashMap Int Nat :=
  pre.foldl (fun m (x, k) => m.insert x k) m

/-- `hit(t,m) : (pre,(b,k)) ↦ (j,k)` when `toMap(m)(pre)` maps `t-b` to `j`. -/
def hit (t : Int) (m : Std.HashMap Int Nat) : Split ⟶ Ans :=
  fun (pre, (b, k)) (j, k') => k' = k ∧ (toMap m pre)[t - b]? = some j

/-- `go(t)` from `∅` on an indexed list, as a relation. -/
def goR (t : Int) : IL ⟶ ⟨Option (Nat × Nat)⟩ := graph fun L => go t L {}

/-- The scan's specification from every start map `m`: a `some` answer is a split hitting
    `toMap(m)(pre)`, and a list with such a split gets a `some` answer. -/
def scanSpec (t : Int) : IL ⟶ Scan :=
  fun L f => ∀ m,
    (∀ a, f m = some a → (splits ≫ hit t m) L a) ∧ ∀ a, (splits ≫ hit t m) L a → ∃ r, f m = some r

/-! ## The step laws -/

/-- Indices along `zipIdx` strictly increase. -/
theorem zipIdx_sorted (xs : List Int) (n : Nat) :
    (xs.zipIdx n).Pairwise fun (_, j) (_, k) => j < k := by
  induction xs generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.pairwise_cons.mpr ⟨fun ⟨b, i⟩ hb => ?_, ih (n + 1)⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (List.mem_zipIdx hb).1

/-- `zipIdx sorted? = zipIdx`, stated under a following `Y`. -/
theorem zipIdxR_sorted {B : RelSet.{0}} (Y : IL ⟶ B) : zipIdxR ≫ sortedR ≫ Y = zipIdxR ≫ Y :=
  hom_ext fun xs _ => ⟨fun ⟨_, h, _, ⟨h', _⟩, hY⟩ => ⟨_, h, h' ▸ hY⟩,
    fun ⟨_, h, hY⟩ => ⟨_, h, _, ⟨rfl, h ▸ zipIdx_sorted xs 0⟩, hY⟩⟩

/-- On a sorted list a pair of members `(a,j)`, `(b,k)` with `j<k` and `a+b=t` is a split
    `pre ++ (b,k) :: post` with `(t-b,j) ∈ pre`. -/
theorem pair_iff_split {L : List (Int × Nat)} (hL : L.Pairwise (fun (_, j) (_, k) => j < k))
    (t : Int)
    (j k : Nat) : (∃ a b, (a, j) ∈ L ∧ (b, k) ∈ L ∧ j < k ∧ a + b = t) ↔
      ∃ pre b post, L = pre ++ (b, k) :: post ∧ (t - b, j) ∈ pre := by
  constructor
  · rintro ⟨a, b, ha, hb, hjk, hs⟩
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    have hsuf := List.pairwise_cons.mp (List.pairwise_append.mp hL).2.1
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨pre, b, post, rfl, by rwa [show t - b = a by omega]⟩
    · rcases List.mem_cons.mp ha with he | ha
      · cases he; exact absurd hjk (Nat.lt_irrefl _)
      · exact absurd (hsuf.1 _ ha) (Nat.lt_asymm hjk)
  · rintro ⟨pre, b, post, rfl, hj⟩
    exact ⟨t - b, b, List.mem_append_left _ hj, List.mem_append_right _ List.mem_cons_self,
      (List.pairwise_append.mp hL).2.2 _ hj _ List.mem_cons_self, by omega⟩

/-- `sorted? pairs(t) = sorted? splits memPre(t)`. -/
theorem pairs_split (t : Int) : sortedR ≫ pairs t = sortedR ≫ splits ≫ memPre t := by
  refine hom_ext fun L ⟨j, k⟩ => ?_
  simp only [sortedR, pairs, splits, memPre, comp_apply, corefl, rpair, rprodMap]
  constructor
  · rintro ⟨_, ⟨rfl, hL⟩, ⟨⟨a, j'⟩, ⟨b, k'⟩⟩, ⟨ha, hb⟩, _, ⟨rfl, hjk, hs⟩, hj, hk⟩
    subst hj hk
    obtain ⟨pre, b, post, hsplit, hm⟩ := (pair_iff_split hL t j k).mp ⟨a, b, ha, hb, hjk, hs⟩
    exact ⟨L, ⟨rfl, hL⟩, (pre, (b, k)), ⟨post, hsplit⟩, rfl, hm⟩
  · rintro ⟨_, ⟨rfl, hL⟩, ⟨pre, ⟨b, k'⟩⟩, ⟨post, hsplit⟩, hk, hm⟩
    subst hk
    obtain ⟨a, b', ha, hb, hjk, hs⟩ := (pair_iff_split hL t j k).mpr ⟨pre, b, post, hsplit, hm⟩
    exact ⟨L, ⟨rfl, hL⟩, ((a, j), (b', k)), ⟨ha, hb⟩, _, ⟨rfl, hjk, hs⟩, rfl, rfl⟩

/-- A value found in `toMap(m)(pre)` is found in `pre` or already in `m`. -/
theorem toMap_lookup (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) (v : Int) (j : Nat)
    (h : (toMap m pre)[v]? = some j) : (v, j) ∈ pre ∨ m[v]? = some j := by
  induction pre generalizing m with
  | nil => exact Or.inr h
  | cons p pre ih =>
    obtain ⟨x, k⟩ := p
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [Std.HashMap.getElem?_insert] at h
      by_cases hv : x = v
      · simp only [hv, beq_self_eq_true, if_true, Option.some.injEq] at h
        exact Or.inl (h ▸ hv ▸ List.mem_cons_self)
      · simp only [beq_iff_eq, hv, if_false] at h
        exact Or.inr h

/-- A value in `m` or in `pre` has an entry in `toMap(m)(pre)`. -/
theorem toMap_some (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) (v : Int)
    (h : (∃ j, m[v]? = some j) ∨ ∃ j, (v, j) ∈ pre) : ∃ j, (toMap m pre)[v]? = some j := by
  induction pre generalizing m with
  | nil => simpa using h
  | cons p pre ih =>
    obtain ⟨x, k⟩ := p
    refine ih _ ?_
    rw [Std.HashMap.getElem?_insert]
    by_cases hv : x = v
    · exact Or.inl ⟨k, by simp [hv]⟩
    · simp only [beq_iff_eq, hv, if_false]
      rcases h with h | ⟨j, h⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp h with he | h
        · exact absurd (congrArg Prod.fst he).symm hv
        · exact Or.inr ⟨j, h⟩

/-- `hit(t) ⊑ memPre(t)`: the map's index for `t-b` is an index of `t-b` in `pre`. -/
theorem hit_memPre (t : Int) : hit t {} ⊑ memPre t :=
  le_iff.mpr fun ⟨pre, _, _⟩ ⟨_, _⟩ ⟨hk, hj⟩ =>
    ⟨hk, (toMap_lookup {} pre _ _ hj).resolve_right (by simp)⟩

/-- `dom(R) ⊑ dom(S)` from: every source `R` relates, `S` relates too. -/
theorem dom_le_dom {A B : RelSet.{0}} {R S : A ⟶ B} (h : ∀ x y, R x y → ∃ z, S x z) :
    dom R ⊑ dom S :=
  le_iff.mpr fun x _ ⟨hxy, y, hR, _⟩ => hxy ▸ let ⟨z, hS⟩ := h x y hR; ⟨rfl, z, hS, hS⟩

/-- `dom(X R) ⊑ dom(X S)` from `dom(R) ⊑ dom(S)`, by `dom(X R) = dom(X dom(R))`. -/
theorem dom_slide {A B C : RelSet.{0}} (X : A ⟶ B) {R S : B ⟶ C} (h : dom R ⊑ dom S) :
    dom (X ≫ R) ⊑ dom (X ≫ S) := by
  rw [dom_comp_dom X R, dom_comp_dom X S]; exact dom_mono_of_le (comp_mono_left X h)

/-- `dom(memPre(t)) ⊑ dom(hit(t))`: a member `t-b` of `pre` has an entry in `toMap(∅)(pre)`. -/
theorem dom_hit (t : Int) : dom (memPre t) ⊑ dom (hit t {}) :=
  dom_le_dom fun ⟨pre, _, k⟩ ⟨j, _⟩ ⟨_, hj⟩ =>
    let ⟨j', h⟩ := toMap_some {} pre _ (Or.inr ⟨j, hj⟩); ⟨(j', k), rfl, h⟩

/-- **`go(t) ⊑ scanSpec(t)`, by (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`** with `X = scanSpec(t)`: the
    premise is one step of the scan, checked on `[]` and on `(x,k) :: L'` from either map lookup. -/
theorem scan_le (t : Int) : (graph (go t) : IL ⟶ Scan) ⊑ scanSpec t := by
  -- `go(t)` satisfies the fold square of `listInitial`, so it is `⦇[const none, scanStep(t)]⦈`.
  have hgo : graph (go t) = relCata (I := listInitial (Int × Nat))
      (consScalarAlg (fun _ _ => none) (scanStep t)) := (relCata_UP (listInitial _) _ _).mp <| by
    show graph listCon ≫ graph (go t) = _
    rw [graph_comp_left]
    refine hom_ext fun u r => ?_
    rcases u with d | ⟨x, L'⟩
    · exact ⟨fun h => ⟨Sum.inl d, rfl, h⟩, fun ⟨v, hv, h⟩ => by
        cases v with
        | inl _ => exact h
        | inr _ => exact hv.elim⟩
    · exact ⟨fun h => ⟨Sum.inr (x, go t L'), ⟨rfl, rfl⟩, h⟩, fun ⟨v, hv, h⟩ => by
        cases v with
        | inl _ => exact hv.elim
        | inr q =>
          obtain ⟨y, f'⟩ := q
          obtain ⟨hy, hf'⟩ := (hv : x = y ∧ _)
          subst hy; subst hf'; exact h⟩
  rw [hgo]
  refine relCata_le_of_prefixed (listInitial (Int × Nat)) (le_iff.mpr ?_)
  rintro L f ⟨u, hu, v, hv, hf⟩ m
  have hu : L = listCon u := hu
  have hf : f = consScalarFn (fun _ _ => none) (scanStep t) v := hf
  subst hu hf
  rcases u with _ | ⟨⟨x, k⟩, L'⟩ <;> rcases v with _ | ⟨e', f'⟩
  · exact ⟨fun _ h => (nomatch h), fun _ ⟨_, ⟨_, hs⟩, _⟩ => by simp [listCon] at hs⟩
  · exact (hv : False).elim
  · exact (hv : False).elim
  · obtain ⟨rfl, hX⟩ : (x, k) = e' ∧ scanSpec t L' f' := hv
    show (∀ a, scanStep t (x, k) f' m = some a → (splits ≫ hit t m) ((x, k) :: L') a) ∧
      ∀ a, (splits ≫ hit t m) ((x, k) :: L') a → ∃ r, scanStep t (x, k) f' m = some r
    have ih := hX (m.insert x k)
    cases hm : m[t - x]? with
    | some j =>
      simp only [scanStep, hm]
      exact ⟨fun _ h => Option.some.inj h ▸ ⟨([], (x, k)), ⟨L', rfl⟩, rfl, hm⟩, fun _ _ => ⟨_, rfl⟩⟩
    | none =>
      simp only [scanStep, hm]
      refine ⟨fun a h => ?_, fun a ⟨⟨pre, b, k'⟩, ⟨post, hs⟩, hh⟩ => ?_⟩
      · obtain ⟨⟨pre, bk⟩, ⟨post, hs⟩, hh⟩ := ih.1 a h
        exact ⟨((x, k) :: pre, bk), ⟨post, by rw [hs]; rfl⟩, hh⟩
      · cases pre with
        | nil => cases hs; exact nomatch hm.symm.trans hh.2
        | cons p pre => cases hs; exact ih.2 a ⟨(pre, (b, k')), ⟨post, rfl⟩, hh⟩

/-- `go(t,∅) some° ⊑ splits hit(t,∅)`: `scan_le` at the empty map, soundness half. -/
theorem go_splits (t : Int) : goR t ≫ unsome ⊑ splits ≫ hit t {} :=
  le_iff.mpr fun L a ⟨_, ho, hs⟩ => (le_iff.mp (scan_le t) L _ rfl {}).1 a ((show _ = _ from ho).symm.trans hs)

/-- `dom(splits hit(t,∅)) ⊑ dom(go(t,∅) some°)`: `scan_le` at the empty map, completeness half. -/
theorem dom_go (t : Int) : dom (splits ≫ hit t {}) ⊑ dom (goR t ≫ unsome) :=
  dom_le_dom fun L a h =>
    let ⟨r, hr⟩ := (le_iff.mp (scan_le t) L _ rfl {}).2 a h; ⟨r, some r, hr.symm, rfl⟩

/-- `prog(t) = zipIdx go(t,∅)`. -/
theorem prog_eq (t : Int) : graph (prog t) ≫ unsome = zipIdxR ≫ goR t ≫ unsome := by
  rw [← Cat.assoc, zipIdxR, goR, graph_comp]; rfl

/-! ## The derivation -/

/-- **Soundness**: every `some` answer of the program is a `twoSum(t)` pair. -/
theorem prog_sound (t : Int) : graph (prog t) ≫ unsome ⊑ twoSum t :=
  calc graph (prog t) ≫ unsome
      = zipIdxR ≫ goR t ≫ unsome := prog_eq t
    _ ⊑ zipIdxR ≫ splits ≫ hit t {} := comp_mono_left _ (go_splits t)
    _ = zipIdxR ≫ sortedR ≫ splits ≫ hit t {} := (zipIdxR_sorted _).symm
    _ ⊑ zipIdxR ≫ sortedR ≫ splits ≫ memPre t :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ (hit_memPre t)))
    _ = zipIdxR ≫ sortedR ≫ pairs t := by rw [pairs_split]
    _ = twoSum t := zipIdxR_sorted _

/-- **Completeness**: the program answers `some` on the whole domain of `twoSum(t)`. -/
theorem prog_complete (t : Int) : dom (twoSum t) ⊑ dom (graph (prog t) ≫ unsome) :=
  calc dom (twoSum t)
      = dom (zipIdxR ≫ sortedR ≫ pairs t) := by rw [zipIdxR_sorted]; rfl
    _ = dom (zipIdxR ≫ sortedR ≫ splits ≫ memPre t) := by rw [pairs_split]
    _ ⊑ dom (zipIdxR ≫ sortedR ≫ splits ≫ hit t {}) :=
        dom_slide _ (dom_slide _ (dom_slide _ (dom_hit t)))
    _ = dom (zipIdxR ≫ splits ≫ hit t {}) := by rw [zipIdxR_sorted]
    _ ⊑ dom (zipIdxR ≫ goR t ≫ unsome) := dom_slide _ (dom_go t)
    _ = dom (graph (prog t) ≫ unsome) := by rw [prog_eq]

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
