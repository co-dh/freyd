/-
  LeetCode 1 — Two Sum, derived from its specification.

  Spec: `twoSum(t) ≜ zipIdx pairs(t) : [Int] ⟶ Nat × Nat` with
  `pairs(t) ≜ ⟨∋,∋⟩ (j<k)? ans(t)` and `ans(t) ≜ (a+b=t)? (π₂×π₂)`: index the list, take two
  members `((a,j),(b,k))`, keep those with `j<k` and `a+b=t`, return `(j,k)`.

  Derivation, one law per step (diagram order; `some°` unwraps a `some` answer):
      twoSum(t)
    = zipIdx sorted? pairs(t)                 zipIdx_sorted: `zipIdx sorted? = zipIdx`
    = zipIdx sorted? splits memPre(t)         pairs_split: `sorted? ⟨∋,∋⟩ (j<k)? = sorted? splits (∋×𝟙)`
    ⊒ zipIdx sorted? splits hit(t,∅)          hit_memPre: `built(∅) ∋ ⊑ ∋`
    = zipIdx splits hit(t,∅)                  zipIdx_sorted
    ⊒ zipIdx go(t,∅) some°                    go_splits: fold law (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`
                                              at `X = scanSpec(t)` (`scan_le`), then `(R/S) S ⊑ R`
    = prog(t) some°                           prog ≜ zipIdx go(t,∅)
  Both `⊒` steps keep the domain (`dom_hit`, `dom_go`), so `dom` of the same chain gives completeness.

  `∋ : [E] ⟶ E` is core's list membership; `built(m) : pre ↦ toList(toMap(m)(pre))` lists the
  entries of the map `go` has built, so `built(m) ∋` is that map's membership.

  Mathlib-free.  Axioms: `prog_sound`/`prog_complete` ⊆ {propext, Classical.choice, Quot.sound};
  `Classical.choice` is inherited from core's `Std.HashMap` lemmas.
-/
import AOP.A6_GenFold
import AOP.A6_2
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL

/-- Indexed members `(a,j)`, indexed lists, pairs of members, splits `(pre,(b,k))`, answers `(j,k)`,
    hash maps, and scans (answers as a function of the start map). -/
abbrev E : RelSet.{0} := ⟨Int × Nat⟩
abbrev IL : RelSet.{0} := ⟨List (Int × Nat)⟩
abbrev E2 : RelSet.{0} := ⟨(Int × Nat) × (Int × Nat)⟩
abbrev Split : RelSet.{0} := ⟨List (Int × Nat) × (Int × Nat)⟩
abbrev Ans : RelSet.{0} := ⟨Nat × Nat⟩
abbrev HM : RelSet.{0} := ⟨Std.HashMap Int Nat⟩
abbrev Scan : RelSet.{0} := ⟨Std.HashMap Int Nat → Option (Nat × Nat)⟩

/-- `∋ : [E] ⟶ E`, core's list membership (the repo's other `∋` is the power allegory's, on `P(A)`). -/
local notation (priority := high) "∋" => (Membership.mem : IL ⟶ E)

/-! ## The specification -/

def zipIdxR : (⟨List Int⟩ : RelSet.{0}) ⟶ IL := graph List.zipIdx

/-- `(j<k)?`: the first member's index is below the second's. -/
def before : E2 ⟶ E2 := corefl fun p => p.1.2 < p.2.2

/-- `ans(t) ≜ (a+b=t)? (π₂×π₂)`: a pair of members summing to `t`, answered by its indices. -/
def ans (t : Int) : E2 ⟶ Ans := corefl (fun p : E2.carrier => p.1.1 + p.2.1 = t) ≫ graph fun p => (p.1.2, p.2.2)

/-- `pairs(t) ≜ ⟨∋,∋⟩ (j<k)? ans(t)`: two members taken independently, in index order, summing to `t`. -/
def pairs (t : Int) : IL ⟶ Ans := rpair ∋ ∋ ≫ before ≫ ans t

/-- `twoSum(t) ≜ zipIdx pairs(t)`. -/
def twoSum (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ Ans := zipIdxR ≫ pairs t

/-! ## The program: one hash-map scan over `zipIdx(xs)` -/

/-- The scan's step at `(x,k)`, given the scan `r` of the rest: the lookup `m[t-x]? : 1 + Nat` is
    consumed by the copair `[r(insert(x,k)(m)), j ↦ some(j,k)]`. -/
def scanStep (t : Int) (p : Int × Nat) (r : Std.HashMap Int Nat → Option (Nat × Nat))
    (m : Std.HashMap Int Nat) : Option (Nat × Nat) :=
  (m[t - p.1]?).elim (r (m.insert p.1 p.2)) fun j => some (j, p.2)

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
def sortedR : IL ⟶ IL := corefl fun L => L.Pairwise fun p q => p.2 < q.2

/-- `cat : (pre,rest) ↦ pre ++ rest`, `cons : (x,xs) ↦ x :: xs`, `outl : (x,xs) ↦ x` on core lists. -/
def cat : (⟨IL.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ IL := graph fun p => p.1 ++ p.2
def cons : (⟨E.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ IL := graph fun p => p.1 :: p.2
def outl : (⟨E.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ E := graph Prod.fst

/-- `splits ≜ cat° (𝟙×cons°) (𝟙×outl)`: cut `L` into `(pre,rest)`, take `rest` apart as
    `(b,k) :: post`, drop `post`. -/
def splits : IL ⟶ Split := cat° ≫ rprodMap (𝟙 IL) cons° ≫ rprodMap (𝟙 IL) outl

/-- `memPre(t) ≜ (∋×𝟙) ans(t)`: a member `(a,j)` of `pre` with `a+b=t` answers `(j,k)`. -/
def memPre (t : Int) : Split ⟶ Ans := rprodMap ∋ (𝟙 E) ≫ ans t

/-- `toMap(m)(pre)`: the left fold of `insert` over `pre` from `m` — the map `go` has built. -/
def toMap (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) : Std.HashMap Int Nat :=
  pre.foldl (fun m p => m.insert p.1 p.2) m

/-- `built(m) : pre ↦ toList(toMap(m)(pre))`, the entries of the built map. -/
def built (m : Std.HashMap Int Nat) : IL ⟶ IL := graph fun pre => (toMap m pre).toList

/-- `entries : (m,(pre,bk)) ↦ (built(m)(pre), bk)`. -/
def entries : (⟨HM.carrier × Split.carrier⟩ : RelSet.{0}) ⟶ Split :=
  graph fun p => ((toMap p.1 p.2.1).toList, p.2.2)

/-- `hit(t,m) ≜ (m,−) entries memPre(t)`: an entry `(a,j)` of `toMap(m)(pre)` with `a+b=t`. -/
def hit (t : Int) (m : Std.HashMap Int Nat) : Split ⟶ Ans := graph (Prod.mk m) ≫ entries ≫ memPre t

/-- `go(t)` from `∅` on an indexed list, as a relation. -/
def goR (t : Int) : IL ⟶ ⟨Option (Nat × Nat)⟩ := graph fun L => go t L {}

/-- `eval ≜ ⟨𝟙,⊤⟩ apply (𝟙×some°) : f ↦ (m,a)` when `f(m) = some a`. -/
def evalR : Scan ⟶ ⟨HM.carrier × Ans.carrier⟩ :=
  rpair (𝟙 Scan) (relTop Scan HM) ≫ graph (fun p => (p.2, p.1 p.2)) ≫ rprodMap (𝟙 HM) unsome

/-- `spec(t) ≜ ⟨⊤,splits⟩ ⟨outl, entries memPre(t)⟩ : L ↦ (m,a)` when a split hits `toMap(m)`. -/
def specR (t : Int) : IL ⟶ ⟨HM.carrier × Ans.carrier⟩ :=
  rpair (relTop IL HM) splits ≫ rpair (graph Prod.fst) (entries ≫ memPre t)

/-- `scanSpec(t) ≜ spec(t)/eval ∩ (eval(𝟙×⊤)/spec(t))°`: from every start map, an answer is a hit,
    and a hit gets an answer. -/
def scanSpec (t : Int) : IL ⟶ Scan :=
  (specR t / evalR) ∩ ((evalR ≫ rprodMap (𝟙 HM) (relTop Ans Ans)) / specR t)°

/-- `at∅ : (∅,a) ↦ a`, the answer from the empty start map. -/
def atEmpty : (⟨HM.carrier × Ans.carrier⟩ : RelSet.{0}) ⟶ Ans :=
  (graph fun a => (({} : Std.HashMap Int Nat), a))°

/-- `sameKey ≜ outl outl°` on members, `sameK ≜ outr outr°` on answers. -/
def sameKey : E ⟶ E := (graph Prod.fst : E ⟶ ⟨Int⟩) ≫ (graph Prod.fst)°
def sameK : Ans ⟶ Ans := (graph Prod.snd : Ans ⟶ ⟨Nat⟩) ≫ (graph Prod.snd)°

/-! ## Base facts about core `List`, `HashMap` and evaluation (pointwise) -/

/-- `L` splits as `(pre,bk)` iff `L = pre ++ bk :: post`. -/
theorem splits_apply (L pre : List (Int × Nat)) (bk : Int × Nat) :
    splits L (pre, bk) ↔ ∃ post, L = pre ++ bk :: post := by
  constructor
  · rintro ⟨⟨p, q⟩, h1, ⟨p', ⟨x, post⟩⟩, ⟨h2, h3⟩, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5; exact ⟨post, rfl⟩
  · rintro ⟨post, rfl⟩; exact ⟨(pre, bk :: post), rfl, (pre, (bk, post)), ⟨rfl, rfl⟩, rfl, rfl⟩

/-- Indices along `zipIdx` strictly increase. -/
theorem zipIdx_sorted (xs : List Int) (n : Nat) : (xs.zipIdx n).Pairwise fun p q => p.2 < q.2 := by
  induction xs generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.pairwise_cons.mpr ⟨fun ⟨b, i⟩ hb => ?_, ih (n + 1)⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (List.mem_zipIdx hb).1

/-- `zipIdx sorted? = zipIdx`. -/
theorem zipIdx_sorted_eq : zipIdxR ≫ sortedR = zipIdxR :=
  hom_ext fun xs _ => ⟨fun ⟨_, h, h', _⟩ => h' ▸ h, fun h => by subst h; exact ⟨_, rfl, rfl, zipIdx_sorted xs 0⟩⟩

/-- `sorted? ⟨∋,∋⟩ (j<k)? = sorted? splits (∋×𝟙)`: on a sorted list two members in index order
    are a member of `pre` and the split element of `pre ++ (b,k) :: post`. -/
theorem sorted_pairs : sortedR ≫ rpair ∋ ∋ ≫ before = sortedR ≫ splits ≫ rprodMap ∋ (𝟙 E) := by
  refine hom_ext fun L ⟨⟨a, j⟩, ⟨b, k⟩⟩ => ⟨?_, ?_⟩
  · rintro ⟨_, ⟨rfl, hL⟩, _, ⟨ha, hb⟩, rfl, hjk⟩
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    have hsuf := List.pairwise_cons.mp (List.pairwise_append.mp hL).2.1
    refine ⟨_, ⟨rfl, hL⟩, (pre, (b, k)), (splits_apply _ _ _).mpr ⟨post, rfl⟩, ?_, rfl⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact ha
    · rcases List.mem_cons.mp ha with he | ha
      · cases he; exact absurd hjk (Nat.lt_irrefl _)
      · exact absurd (hsuf.1 _ ha) (Nat.lt_asymm hjk)
  · rintro ⟨_, ⟨rfl, hL⟩, ⟨pre, bk⟩, hs, ha, rfl⟩
    obtain ⟨post, rfl⟩ := (splits_apply _ _ _).mp hs
    exact ⟨_, ⟨rfl, hL⟩, _, ⟨List.mem_append_left _ ha, List.mem_append_right _ List.mem_cons_self⟩,
      rfl, (List.pairwise_append.mp hL).2.2 _ ha _ List.mem_cons_self⟩

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

/-- `built(∅) ∋ ⊑ ∋`: an entry of `toMap(∅)(pre)` is a member of `pre`. -/
theorem built_le : built {} ≫ ∋ ⊑ ∋ :=
  le_iff.mpr fun pre ⟨v, j⟩ ⟨_, h, hm⟩ => by
    subst h
    exact (toMap_lookup {} pre v j (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm)).resolve_right (by simp)

/-- `∋ ⊑ built(∅) ∋ sameKey`: a member's key has an entry in `toMap(∅)(pre)`. -/
theorem mem_le_built : ∋ ⊑ built {} ≫ ∋ ≫ sameKey :=
  le_iff.mpr fun pre ⟨v, j⟩ h =>
    let ⟨j', hj⟩ := toMap_some {} pre v (Or.inr ⟨j, h⟩)
    ⟨_, rfl, (v, j'), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hj, v, rfl, rfl⟩

/-- `(sameKey×𝟙) ans(t) ⊑ ans(t) sameK`: the test `a+b=t` reads only the key. -/
theorem sameKey_ans (t : Int) : rprodMap sameKey (𝟙 E) ≫ ans t ⊑ ans t ≫ sameK :=
  le_iff.mpr <| by
    rintro ⟨⟨a, j⟩, b, k⟩ _ ⟨⟨⟨a', j'⟩, w⟩, ⟨⟨c, hc, ha⟩, rfl⟩, _, ⟨rfl, hs⟩, rfl⟩
    have ha : a = a' := Eq.trans (Eq.symm hc) ha
    subst ha
    exact ⟨(j, k), ⟨_, ⟨rfl, hs⟩, rfl⟩, k, rfl, rfl⟩

/-- `hit(t,m) = (built(m) ∋ × 𝟙) ans(t)`. -/
theorem hit_eq (t : Int) (m : Std.HashMap Int Nat) :
    hit t m = rprodMap (built m ≫ ∋) (𝟙 E) ≫ ans t := by
  have h : graph (Prod.mk m) ≫ entries = rprodMap (built m) (𝟙 E) :=
    hom_ext fun ⟨pre, bk⟩ ⟨l, bk'⟩ => ⟨fun ⟨_, rfl, h⟩ => ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2.symm⟩,
      fun ⟨h1, h2⟩ => ⟨_, rfl, by
        have h1 : l = (toMap m pre).toList := h1; have h2 : bk = bk' := h2; subst h1 h2; rfl⟩⟩
  rw [hit, ← Cat.assoc, h, memPre, ← Cat.assoc, rprodMap_comp, Cat.id_comp]

/-- `hit(t,m)` pointwise: `toMap(m)(pre)` maps `t-b` to `j`. -/
theorem hit_apply (t : Int) (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) (b : Int)
    (k j k' : Nat) : hit t m (pre, (b, k)) (j, k') ↔ k' = k ∧ (toMap m pre)[t - b]? = some j := by
  rw [hit_eq]
  constructor
  · rintro ⟨⟨⟨a, i⟩, w⟩, ⟨⟨_, rfl, hm⟩, rfl⟩, _, ⟨rfl, hs⟩, h⟩
    have hs : a + b = t := hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, by rw [show t - b = a by omega]; exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm⟩
  · rintro ⟨rfl, hj⟩
    exact ⟨((t - b, j), (b, k')), ⟨⟨_, rfl, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hj⟩, rfl⟩,
      _, ⟨rfl, show t - b + b = t by omega⟩, rfl⟩

/-- `splits hit(t,m)` pointwise. -/
theorem sh_iff (t : Int) (m : Std.HashMap Int Nat) (L : List (Int × Nat)) (j k' : Nat) :
    (splits ≫ hit t m) L (j, k') ↔
      ∃ pre b k, (∃ post, L = pre ++ (b, k) :: post) ∧ k' = k ∧ (toMap m pre)[t - b]? = some j :=
  ⟨fun ⟨⟨pre, b, k⟩, hs, hh⟩ => let ⟨hk, hj⟩ := (hit_apply t m pre b k j k').mp hh
      ⟨pre, b, k, (splits_apply _ _ _).mp hs, hk, hj⟩,
   fun ⟨pre, b, k, hs, hk, hj⟩ =>
      ⟨(pre, (b, k)), (splits_apply _ _ _).mpr hs, (hit_apply t m pre b k j k').mpr ⟨hk, hj⟩⟩⟩

/-- `eval` pointwise: `f(m) = some a`. -/
theorem evalR_apply (f : Scan.carrier) (m : Std.HashMap Int Nat) (a : Nat × Nat) :
    evalR f (m, a) ↔ f m = some a :=
  ⟨by rintro ⟨_, ⟨rfl, _⟩, _, rfl, rfl, h⟩; exact h, fun h => ⟨(f, m), ⟨rfl, trivial⟩, (m, f m), rfl, rfl, h⟩⟩

/-- `spec(t)` pointwise: `splits hit(t,m)` relates `L` to `a`. -/
theorem specR_apply (t : Int) (L : List (Int × Nat)) (m : Std.HashMap Int Nat) (a : Nat × Nat) :
    specR t L (m, a) ↔ (splits ≫ hit t m) L a :=
  ⟨fun ⟨⟨_, s⟩, ⟨_, hs⟩, rfl, h⟩ => ⟨s, hs, _, rfl, h⟩,
   fun ⟨s, hs, _, rfl, h⟩ => ⟨(m, s), ⟨trivial, hs⟩, rfl, h⟩⟩

/-- `scanSpec(t)` pointwise: the division is a `∀` over start maps and answers. -/
theorem scanSpec_apply (t : Int) (L : List (Int × Nat)) (f : Scan.carrier) :
    scanSpec t L f ↔ ∀ m, (∀ a, f m = some a → (splits ≫ hit t m) L a) ∧
      ∀ a, (splits ≫ hit t m) L a → ∃ r, f m = some r := by
  have hd : ∀ m a, (evalR ≫ rprodMap (𝟙 HM) (relTop Ans Ans)) f (m, a) ↔ ∃ r, f m = some r :=
    fun m _ => ⟨fun ⟨⟨_, r⟩, hz, rfl, _⟩ => ⟨r, (evalR_apply f _ r).mp hz⟩,
      fun ⟨r, h⟩ => ⟨(m, r), (evalR_apply f m r).mpr h, rfl, trivial⟩⟩
  constructor
  · intro ⟨h1, h2⟩ m
    exact ⟨fun a ha => (specR_apply t L m a).mp (h1 (m, a) ((evalR_apply f m a).mpr ha)),
      fun a ha => (hd m a).mp (h2 (m, a) ((specR_apply t L m a).mpr ha))⟩
  · intro h
    exact ⟨fun ⟨m, a⟩ hz => (specR_apply t L m a).mpr ((h m).1 a ((evalR_apply f m a).mp hz)),
      fun ⟨m, a⟩ hz => (hd m a).mpr ((h m).2 a ((specR_apply t L m a).mp hz))⟩

/-- `go(t,∅) some° = go(t) eval at∅`. -/
theorem goR_unsome (t : Int) : goR t ≫ unsome = graph (go t) ≫ evalR ≫ atEmpty :=
  hom_ext fun _ _ => ⟨fun ⟨_, rfl, h⟩ => ⟨_, rfl, _, (evalR_apply _ _ _).mpr h, rfl⟩,
    fun ⟨_, rfl, _, h, rfl⟩ => ⟨_, rfl, (evalR_apply _ _ _).mp h⟩⟩

/-- `spec(t) at∅ = splits hit(t,∅)`. -/
theorem specR_atEmpty (t : Int) : specR t ≫ atEmpty = splits ≫ hit t {} :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, rfl⟩ => (specR_apply _ _ _ _).mp h,
    fun h => ⟨_, (specR_apply _ _ _ _).mpr h, rfl⟩⟩

/-- `(𝟙×⊤) at∅ = at∅ ⊤`: both read only the start map. -/
theorem top_atEmpty : rprodMap (𝟙 HM) (relTop Ans Ans) ≫ atEmpty = atEmpty ≫ relTop Ans Ans :=
  hom_ext fun ⟨m, a⟩ b => ⟨fun ⟨_, ⟨h, _⟩, rfl⟩ => ⟨a, show (m, a) = ({}, a) from congrArg (·, a) h, trivial⟩,
    fun ⟨_, h, _⟩ => ⟨({}, b), ⟨(Prod.mk.inj h).1, trivial⟩, rfl⟩⟩

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
  rintro L f ⟨u, hu, v, hv, hf⟩
  have hu : L = listCon u := hu
  have hf : f = consScalarFn (fun _ _ => none) (scanStep t) v := hf
  subst hu hf
  refine (scanSpec_apply t _ _).mpr fun m => ?_
  rcases u with _ | ⟨⟨x, k⟩, L'⟩ <;> rcases v with _ | ⟨e', f'⟩
  · refine ⟨fun _ h => (nomatch h), fun ⟨j, k'⟩ h => ?_⟩
    obtain ⟨pre, b, k, ⟨post, hs⟩, _⟩ := (sh_iff t m _ j k').mp h
    simp [listCon] at hs
  · exact (hv : False).elim
  · exact (hv : False).elim
  · obtain ⟨rfl, hX⟩ : (x, k) = e' ∧ scanSpec t L' f' := hv
    have ih := (scanSpec_apply t L' f').mp hX (m.insert x k)
    show (∀ a, scanStep t (x, k) f' m = some a → (splits ≫ hit t m) ((x, k) :: L') a) ∧
      ∀ a, (splits ≫ hit t m) ((x, k) :: L') a → ∃ r, scanStep t (x, k) f' m = some r
    cases hm : m[t - x]? with
    | some j =>
      simp only [scanStep, hm, Option.elim]
      exact ⟨fun _ h => Option.some.inj h ▸ (sh_iff t m _ j k).mpr ⟨[], x, k, ⟨L', rfl⟩, rfl, hm⟩,
        fun _ _ => ⟨_, rfl⟩⟩
    | none =>
      simp only [scanStep, hm, Option.elim]
      refine ⟨fun ⟨j, k'⟩ h => ?_, fun ⟨j, k'⟩ h => ?_⟩
      · obtain ⟨pre, b, k'', ⟨post, hs⟩, hk, hh⟩ := (sh_iff t _ _ j k').mp (ih.1 _ h)
        exact (sh_iff t m _ j k').mpr ⟨(x, k) :: pre, b, k'', ⟨post, by rw [hs]; rfl⟩, hk, hh⟩
      · obtain ⟨pre, b, k'', ⟨post, hs⟩, hk, hh⟩ := (sh_iff t m _ j k').mp h
        cases pre with
        | nil => cases hs; exact nomatch hm.symm.trans hh
        | cons p pre =>
          cases hs; exact ih.2 _ ((sh_iff t _ _ j k').mpr ⟨pre, b, k'', ⟨post, rfl⟩, hk, hh⟩)

/-! ## The step laws -/

/-- `zipIdx sorted? = zipIdx`, stated under a following `Y`. -/
theorem zipIdxR_sorted {B : RelSet.{0}} (Y : IL ⟶ B) : zipIdxR ≫ sortedR ≫ Y = zipIdxR ≫ Y := by
  rw [← Cat.assoc, zipIdx_sorted_eq]

/-- `sorted? pairs(t) = sorted? splits memPre(t)`. -/
theorem pairs_split (t : Int) : sortedR ≫ pairs t = sortedR ≫ splits ≫ memPre t :=
  calc sortedR ≫ pairs t
      = (sortedR ≫ rpair ∋ ∋ ≫ before) ≫ ans t := by simp only [pairs, Cat.assoc]
    _ = (sortedR ≫ splits ≫ rprodMap ∋ (𝟙 E)) ≫ ans t := by rw [sorted_pairs]
    _ = sortedR ≫ splits ≫ memPre t := by simp only [memPre, Cat.assoc]

/-- `hit(t,∅) ⊑ memPre(t)`: an entry of the built map is a member of `pre`. -/
theorem hit_memPre (t : Int) : hit t {} ⊑ memPre t :=
  calc hit t {}
      = rprodMap (built {} ≫ ∋) (𝟙 E) ≫ ans t := hit_eq t {}
    _ ⊑ rprodMap ∋ (𝟙 E) ≫ ans t := comp_mono_right (rprodMap_mono built_le (le_refl _)) _

/-- `dom(X R) ⊑ dom(X S)` from `dom(R) ⊑ dom(S)`, by `dom(X R) = dom(X dom(R))`. -/
theorem dom_slide {A B C : RelSet.{0}} (X : A ⟶ B) {R S : B ⟶ C} (h : dom R ⊑ dom S) :
    dom (X ≫ R) ⊑ dom (X ≫ S) := by
  rw [dom_comp_dom X R, dom_comp_dom X S]; exact dom_mono_of_le (comp_mono_left X h)

/-- `dom(memPre(t)) ⊑ dom(hit(t,∅))`: a member's key has an entry, and `ans(t)` reads only the key. -/
theorem dom_hit (t : Int) : dom (memPre t) ⊑ dom (hit t {}) :=
  calc dom (memPre t)
      = dom (rprodMap ∋ (𝟙 E) ≫ ans t) := rfl
    _ ⊑ dom (rprodMap (built {} ≫ ∋ ≫ sameKey) (𝟙 E) ≫ ans t) :=
        dom_mono_of_le (comp_mono_right (rprodMap_mono mem_le_built (le_refl _)) _)
    _ = dom ((rprodMap (built {} ≫ ∋) (𝟙 E) ≫ rprodMap sameKey (𝟙 E)) ≫ ans t) := by
        rw [rprodMap_comp, Cat.id_comp, Cat.assoc]
    _ ⊑ dom (rprodMap (built {} ≫ ∋) (𝟙 E) ≫ ans t ≫ sameK) := by
        rw [Cat.assoc]; exact dom_mono_of_le (comp_mono_left _ (sameKey_ans t))
    _ ⊑ dom (rprodMap (built {} ≫ ∋) (𝟙 E) ≫ ans t) := by
        rw [← Cat.assoc]; exact dom_comp_le _ _
    _ = dom (hit t {}) := by rw [hit_eq]

/-- `go(t,∅) some° ⊑ splits hit(t,∅)`: the soundness half of `scanSpec(t)`, `(R/S) S ⊑ R`. -/
theorem go_splits (t : Int) : goR t ≫ unsome ⊑ splits ≫ hit t {} :=
  calc goR t ≫ unsome
      = graph (go t) ≫ evalR ≫ atEmpty := goR_unsome t
    _ ⊑ scanSpec t ≫ evalR ≫ atEmpty := comp_mono_right (scan_le t) _
    _ ⊑ (specR t / evalR) ≫ evalR ≫ atEmpty := comp_mono_right (inter_lb_left _ _) _
    _ ⊑ specR t ≫ atEmpty := by
        rw [← Cat.assoc]; exact comp_mono_right ((le_div_iff _ _ _).mp (le_refl _)) _
    _ = splits ≫ hit t {} := specR_atEmpty t

/-- `dom(splits hit(t,∅)) ⊑ dom(go(t,∅) some°)`: the completeness half of `scanSpec(t)`. -/
theorem dom_go (t : Int) : dom (splits ≫ hit t {}) ⊑ dom (goR t ≫ unsome) :=
  have hc : (graph (go t))° ≫ specR t ⊑ evalR ≫ rprodMap (𝟙 HM) (relTop Ans Ans) := by
    have h := recip_mono (le_trans (scan_le t) (inter_lb_right _ _))
    rw [Allegory.recip_recip] at h
    exact (le_div_iff _ _ _).mp h
  calc dom (splits ≫ hit t {})
      = dom (specR t ≫ atEmpty) := by rw [specR_atEmpty]
    _ ⊑ dom ((graph (go t) ≫ (graph (go t))°) ≫ specR t ≫ atEmpty) := by
        have h := comp_mono_right (graph_entire (go t) : 𝟙 IL ⊑ _) (specR t ≫ atEmpty)
        rw [Cat.id_comp] at h; exact dom_mono_of_le h
    _ ⊑ dom (graph (go t) ≫ (evalR ≫ rprodMap (𝟙 HM) (relTop Ans Ans)) ≫ atEmpty) := by
        simpa only [Cat.assoc] using
          dom_mono_of_le (comp_mono_left (graph (go t)) (comp_mono_right hc atEmpty))
    _ = dom (graph (go t) ≫ evalR ≫ atEmpty ≫ relTop Ans Ans) := by
        rw [Cat.assoc evalR, top_atEmpty]
    _ ⊑ dom (graph (go t) ≫ evalR ≫ atEmpty) := by
        simpa only [Cat.assoc] using dom_comp_le (graph (go t) ≫ evalR ≫ atEmpty) (relTop Ans Ans)
    _ = dom (goR t ≫ unsome) := by rw [goR_unsome]

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
