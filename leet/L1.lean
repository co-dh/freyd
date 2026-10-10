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
    ⊒ zipIdx sorted? splits hit(t)            hit_memPre: a hit of `toMap(pre)` at `t-b` is in `pre`
    = zipIdx splits hit(t)                    zipIdx_sorted
    ⊒ zipIdx go(t,∅) some°                    go_splits: the scan answers the first hitting split
    = prog(t) some°                           prog ≜ zipIdx go(t,∅)
  `toMap(m)(pre)` is the left fold of `insert` over `pre`, which is the map `go` carries.  Both `⊒`
  steps keep the domain (`dom_hit`, `dom_go`), so `dom` of the same chain gives completeness.

  Mathlib-free.  Axioms: `prog_sound`/`prog_complete` ⊆ {propext, Classical.choice, Quot.sound};
  `Classical.choice` is inherited from core's `Std.HashMap.getElem?_insert`/`getElem?_empty`.
-/
import AOP.A6_1_RelSet
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd

/-- Indexed lists, their splits `(pre,(b,k))`, and answers `(j,k)`. -/
abbrev IL : RelSet.{0} := ⟨List (Int × Nat)⟩
abbrev Split : RelSet.{0} := ⟨List (Int × Nat) × (Int × Nat)⟩
abbrev Ans : RelSet.{0} := ⟨Nat × Nat⟩

/-! ## The specification -/

/-- Membership `∋ : [A] ⟶ A` on core lists.  `ListRel.inlist` is the same relation on `ConsList`;
    `zipIdx` is core's, so its membership is core's `∈` too. -/
def ni {A : Type} : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨A⟩ := fun xs x => x ∈ xs

def zipIdxR : (⟨List Int⟩ : RelSet.{0}) ⟶ IL := graph List.zipIdx

/-- `pairs(t) ≜ ⟨∋,∋⟩ (j<k ∧ a+b=t)? (π₂×π₂)`: two members `((a,j),(b,k))` taken independently,
    kept when `j<k` and `a+b=t`, answered by their indices. -/
def pairs (t : Int) : IL ⟶ Ans :=
  rpair ni ni ≫ corefl (fun c : (Int × Nat) × (Int × Nat) => c.1.2 < c.2.2 ∧ c.1.1 + c.2.1 = t) ≫
    rprodMap (graph Prod.snd : (⟨Int × Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩) (graph Prod.snd)

/-- `twoSum(t) ≜ zipIdx pairs(t)`. -/
def twoSum (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ Ans := zipIdxR ≫ pairs t

/-! ## The program: one hash-map scan over `zipIdx(xs)` -/

/-- The scan from map `m` over the remaining indexed elements: at `(x,k)` a hit `m[t-x]? = some j`
    answers `(j,k)`, a miss records `x ↦ k` and moves on. -/
def go (t : Int) (m : Std.HashMap Int Nat) : List (Int × Nat) → Option (Nat × Nat)
  | [] => none
  | (x, k) :: ps => match m[t - x]? with
    | some j => some (j, k)
    | none => go t (m.insert x k) ps

/-- `prog(t)(xs)`: the scan over `zipIdx(xs)` from the empty map. -/
def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := go t {} xs.zipIdx

/-- `some° : Option (Nat × Nat) ⟶ Nat × Nat`, the answer inside a `some`. -/
def unsome : (⟨Option (Nat × Nat)⟩ : RelSet.{0}) ⟶ Ans := (graph some)°

/-! ## The relations the derivation passes through -/

/-- `sorted?`: indices strictly increase along the list. -/
def sortedR : IL ⟶ IL := corefl fun L => L.Pairwise (fun a b => a.2 < b.2)

/-- `splits : L ↦ (pre,(b,k))` whenever `L = pre ++ (b,k) :: post`. -/
def splits : IL ⟶ Split := fun L p => ∃ post, L = p.1 ++ p.2 :: post

/-- `memPre(t) : (pre,(b,k)) ↦ (j,k)` for a member `(t-b,j)` of `pre`. -/
def memPre (t : Int) : Split ⟶ Ans := fun p q => q.2 = p.2.2 ∧ (t - p.2.1, q.1) ∈ p.1

/-- `toMap(m)(pre)`: the left fold of `insert` over `pre` from `m` — the map `go` has built. -/
def toMap (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) : Std.HashMap Int Nat :=
  pre.foldl (fun m p => m.insert p.1 p.2) m

/-- `hit(t) : (pre,(b,k)) ↦ (j,k)` when `toMap(∅)(pre)` maps `t-b` to `j`. -/
def hit (t : Int) : Split ⟶ Ans := fun p q => q.2 = p.2.2 ∧ (toMap {} p.1)[t - p.2.1]? = some q.1

/-- `go(t,m)` as a relation. -/
def goR (t : Int) : IL ⟶ ⟨Option (Nat × Nat)⟩ := graph (go t {})

/-! ## The step laws -/

/-- Indices along `zipIdx` strictly increase. -/
theorem zipIdx_sorted (xs : List Int) (n : Nat) : (xs.zipIdx n).Pairwise (fun a b => a.2 < b.2) := by
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
theorem pair_iff_split {L : List (Int × Nat)} (hL : L.Pairwise (fun a b => a.2 < b.2)) (t : Int)
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
  simp only [sortedR, pairs, splits, memPre, comp_apply, corefl, rpair, ni, rprodMap, graph]
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
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [Std.HashMap.getElem?_insert] at h
      by_cases hv : p.1 = v
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
    refine ih _ ?_
    rw [Std.HashMap.getElem?_insert]
    by_cases hv : p.1 = v
    · exact Or.inl ⟨p.2, by simp [hv]⟩
    · simp only [beq_iff_eq, hv, if_false]
      rcases h with h | ⟨j, h⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp h with he | h
        · exact absurd (congrArg Prod.fst he).symm hv
        · exact Or.inr ⟨j, h⟩

/-- `hit(t) ⊑ memPre(t)`: the map's index for `t-b` is an index of `t-b` in `pre`. -/
theorem hit_memPre (t : Int) : hit t ⊑ memPre t :=
  le_iff.mpr fun ⟨pre, _⟩ _ ⟨hk, hj⟩ =>
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
theorem dom_hit (t : Int) : dom (memPre t) ⊑ dom (hit t) :=
  dom_le_dom fun ⟨pre, _, k⟩ ⟨j, _⟩ ⟨_, hj⟩ =>
    let ⟨j', h⟩ := toMap_some {} pre _ (Or.inr ⟨j, hj⟩); ⟨(j', k), rfl, h⟩

/-- A `some` answer of the scan from `m` comes from a split whose prefix, folded into `m`, hits. -/
theorem go_split (t : Int) (m : Std.HashMap Int Nat) (L : List (Int × Nat)) (j k : Nat)
    (h : go t m L = some (j, k)) :
    ∃ pre b post, L = pre ++ (b, k) :: post ∧ (toMap m pre)[t - b]? = some j := by
  induction L generalizing m with
  | nil => nomatch h
  | cons p ps ih =>
    obtain ⟨x, k'⟩ := p
    unfold go at h
    split at h
    · rename_i j' hj
      cases h
      exact ⟨[], x, ps, rfl, hj⟩
    · obtain ⟨pre, b, post, hL, h⟩ := ih _ h
      exact ⟨(x, k') :: pre, b, post, by rw [hL]; rfl, h⟩

/-- The scan from `m` answers `some` on a list with a split whose prefix, folded into `m`, hits. -/
theorem go_hits (t : Int) (m : Std.HashMap Int Nat) (pre post : List (Int × Nat)) (b : Int)
    (k j : Nat) (h : (toMap m pre)[t - b]? = some j) :
    ∃ r, go t m (pre ++ (b, k) :: post) = some r := by
  induction pre generalizing m with
  | nil => exact ⟨(j, k), by simp only [List.nil_append, go]; rw [show m[t - b]? = some j from h]⟩
  | cons p pre ih =>
    obtain ⟨x, k'⟩ := p
    show ∃ r, go t m ((x, k') :: (pre ++ (b, k) :: post)) = some r
    unfold go
    split
    · exact ⟨_, rfl⟩
    · exact ih _ h

/-- `go(t,∅) some° ⊑ splits hit(t)`: the scan's answer is a split that hits. -/
theorem go_splits (t : Int) : goR t ≫ unsome ⊑ splits ≫ hit t :=
  le_iff.mpr fun L ⟨j, k⟩ ⟨_, ho, hs⟩ =>
    let ⟨pre, b, post, hL, h⟩ := go_split t {} L j k (ho ▸ hs)
    ⟨(pre, (b, k)), ⟨post, hL⟩, rfl, h⟩

/-- `dom(splits hit(t)) ⊑ dom(go(t,∅) some°)`: on a list with a hitting split the scan answers. -/
theorem dom_go (t : Int) : dom (splits ≫ hit t) ⊑ dom (goR t ≫ unsome) :=
  dom_le_dom fun L _ ⟨⟨pre, b, k⟩, ⟨post, hL⟩, _, hj⟩ =>
    let ⟨r, hr⟩ := go_hits t {} pre post b k _ hj; ⟨r, some r, by rw [hL]; exact hr.symm, rfl⟩

/-- `prog(t) = zipIdx go(t,∅)`. -/
theorem prog_eq (t : Int) : graph (prog t) ≫ unsome = zipIdxR ≫ goR t ≫ unsome := by
  rw [← Cat.assoc, zipIdxR, goR, graph_comp]; rfl

/-! ## The derivation -/

/-- **Soundness**: every `some` answer of the program is a `twoSum(t)` pair. -/
theorem prog_sound (t : Int) : graph (prog t) ≫ unsome ⊑ twoSum t :=
  calc graph (prog t) ≫ unsome
      = zipIdxR ≫ goR t ≫ unsome := prog_eq t
    _ ⊑ zipIdxR ≫ splits ≫ hit t := comp_mono_left _ (go_splits t)
    _ = zipIdxR ≫ sortedR ≫ splits ≫ hit t := (zipIdxR_sorted _).symm
    _ ⊑ zipIdxR ≫ sortedR ≫ splits ≫ memPre t :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ (hit_memPre t)))
    _ = zipIdxR ≫ sortedR ≫ pairs t := by rw [pairs_split]
    _ = twoSum t := zipIdxR_sorted _

/-- **Completeness**: the program answers `some` on the whole domain of `twoSum(t)`. -/
theorem prog_complete (t : Int) : dom (twoSum t) ⊑ dom (graph (prog t) ≫ unsome) :=
  calc dom (twoSum t)
      = dom (zipIdxR ≫ sortedR ≫ pairs t) := by rw [zipIdxR_sorted]; rfl
    _ = dom (zipIdxR ≫ sortedR ≫ splits ≫ memPre t) := by rw [pairs_split]
    _ ⊑ dom (zipIdxR ≫ sortedR ≫ splits ≫ hit t) :=
        dom_slide _ (dom_slide _ (dom_slide _ (dom_hit t)))
    _ = dom (zipIdxR ≫ splits ≫ hit t) := by rw [zipIdxR_sorted]
    _ ⊑ dom (zipIdxR ≫ goR t ≫ unsome) := dom_slide _ (dom_go t)
    _ = dom (graph (prog t) ≫ unsome) := by rw [prog_eq]

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
