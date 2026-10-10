/-
  LeetCode 1 — Two Sum, derived from its specification.

  Spec (entire, B&dM style): `twoSumO(t) ≜ orNone(twoSum(t)) : [Int] ⟶ 1 + Nat×Nat`, where
  `orNone(R) ≜ R some ∪ (¬dom R)? none`: some answer of `R` where it has one, `none` elsewhere.
  `twoSum(t) ≜ zipIdx pairs(t)`, `pairs(t) ≜ ⟨∋,∋⟩ (j<k)? ans(t)`, `ans(t) ≜ (a+b=t)? (π₂×π₂)`.

  The map is the relation `look(m) : Int ⟶ Nat`.  From `m`, a split `(pre,(b,k))` of the rest hits
  through `env(m,pre) ≜ look(m) ∪ ∋(pre)`: `hits(t,m) ≜ splits (env(m)×𝟙) ans(t)`.

  Derivation, one law per step (diagram order):
      graph(prog(t))
    = zipIdx go(t) at∅                      prog ≜ zipIdx go(t,∅)
    ⊑ zipIdx scan(t) at∅                    fold law (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`, `X = scan(t)`
    ⊑ zipIdx orNone(hits(t,∅))              scan(t) ≜ ∀m. orNone(hits(t,m)), taken at `m = ∅`
    = orNone(zipIdx hits(t,∅))              `f orNone(R) = orNone(f R)` for a map `f`
    = orNone(twoSum(t))                     `look(∅) = ⊥`, `zipIdx sorted? = zipIdx`, `sorted_pairs`
  The fold premise: a lookup hit answers `(j,k)` at the head split; a miss defers to
  `insert(x,k)(m)`, whose `env` is below `env(m)` one entry later and has the same keys (`look_insert`).

  Boundary facts (pointwise): `look_empty`, `look_insert` (HashMap); `ent_nil`, `ent_cons` (`∋` as
  the fold `⦇[⊥, (x↦k) ∪ −]⦈`), `splits_apply` (`cat°`), `zipIdx_sorted`, `sorted_pairs` (List).

  Mathlib-free.  Axioms of `prog_le` ⊆ {propext, Classical.choice, Quot.sound}; `Classical.choice`
  enters only through core's `Std.HashMap` lemmas in `look_empty`/`look_insert`.
-/
import AOP.A6_GenFold
import AOP.A6_2
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL

/-- Keys, indices, indexed members `(a,j)`, indexed lists, pairs of members, splits `(pre,(b,k))`,
    answers `(j,k)`, hash maps, and scans (answers as a function of the start map). -/
abbrev Key : RelSet.{0} := ⟨Int⟩
abbrev Idx : RelSet.{0} := ⟨Nat⟩
abbrev E : RelSet.{0} := ⟨Int × Nat⟩
abbrev IL : RelSet.{0} := ⟨List (Int × Nat)⟩
abbrev E2 : RelSet.{0} := ⟨(Int × Nat) × (Int × Nat)⟩
abbrev Split : RelSet.{0} := ⟨List (Int × Nat) × (Int × Nat)⟩
abbrev Ans : RelSet.{0} := ⟨Nat × Nat⟩
abbrev Opt : RelSet.{0} := ⟨Option (Nat × Nat)⟩
abbrev Scan : RelSet.{0} := ⟨Std.HashMap Int Nat → Option (Nat × Nat)⟩

/-- `∋ : [E] ⟶ E`, core's list membership (the repo's other `∋` is the power allegory's, on `P(A)`). -/
local notation (priority := high) "∋" => (Membership.mem : IL ⟶ E)

/-! ## The specification -/

def zipIdxR : (⟨List Int⟩ : RelSet.{0}) ⟶ IL := graph List.zipIdx

/-- `(j<k)?`: the first member's index is below the second's. -/
def before : E2 ⟶ E2 := corefl fun ((_, j), (_, k)) => j < k

/-- `ans(t) ≜ (a+b=t)? (π₂×π₂)`: a pair of members summing to `t`, answered by its indices. -/
def ans (t : Int) : E2 ⟶ Ans := corefl (fun ((a, _), (b, _)) => a + b = t) ≫ graph fun ((_, j), (_, k)) => (j, k)

/-- `pairs(t) ≜ ⟨∋,∋⟩ (j<k)? ans(t)`: two members taken independently, in index order, summing to `t`. -/
def pairs (t : Int) : IL ⟶ Ans := rpair ∋ ∋ ≫ before ≫ ans t

/-- `twoSum(t) ≜ zipIdx pairs(t)`. -/
def twoSum (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ Ans := zipIdxR ≫ pairs t

/-- `(¬dom R)?`: the points where `R` has no value. -/
def undef {A B : RelSet.{0}} (R : A ⟶ B) : A ⟶ A := corefl fun a => ∀ b, ¬ R a b

/-- `orNone(R) ≜ R some ∪ (¬dom R)? none`, the entire relation that totals `R`. -/
def orNone {A B : RelSet.{0}} (R : A ⟶ B) : A ⟶ ⟨Option B.carrier⟩ :=
  R ≫ graph some ∪ undef R ≫ graph fun _ => none

/-- `twoSumO(t) ≜ orNone(twoSum(t))`. -/
def twoSumO (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ Opt := orNone (twoSum t)

/-! ## The program: one hash-map scan over `zipIdx(xs)` -/

/-- The scan's step at `(x,k)`, given the scan `r` of the rest: the lookup `m[t-x]? : 1 + Nat` is
    consumed by the copair `[r(insert(x,k)(m)), j ↦ some(j,k)]`. -/
def scanStep (t : Int) : Int × Nat → (Std.HashMap Int Nat → Option (Nat × Nat)) →
    Std.HashMap Int Nat → Option (Nat × Nat) :=
  fun (x, k) r m => (m[t - x]?).elim (r (m.insert x k)) fun j => some (j, k)

/-- `go(t) ≜ ⦇[const none, scanStep(t)]⦈`, the right fold over `List`: its result is a function of
    the start map, so the left-to-right map threads through it and a hit stops the scan. -/
def go (t : Int) : List (Int × Nat) → Std.HashMap Int Nat → Option (Nat × Nat) :=
  List.foldr (scanStep t) fun _ => none

/-- `prog(t)(xs)`: the scan over `zipIdx(xs)` from the empty map. -/
def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := go t xs.zipIdx {}

/-- `at∅ : f ↦ f(∅)`, a scan run from the empty map. -/
def atEmpty : Scan ⟶ Opt := graph fun f => f {}

/-! ## The map and the list as relations: the boundary facts (pointwise) -/

/-- `look(m) : Int ⟶ Nat`, the finite relation the map denotes. -/
def look (m : Std.HashMap Int Nat) : Key ⟶ Idx := fun a j => m[a]? = some j

/-- `(x↦k) ≜ (=x)? k`, the one-entry relation. -/
def single (x : Int) (k : Nat) : Key ⟶ Idx := corefl (· = x) ≫ graph fun _ => k

theorem look_empty : look {} = 𝟘 :=
  hom_ext fun a j => ⟨fun h => by simp [look] at h, fun h => (h : False).elim⟩

/-- `look(insert(x,k)(m)) = (x↦k) ∪ (≠x)? look(m)`: insertion overrides the key `x`. -/
theorem look_insert (m : Std.HashMap Int Nat) (x : Int) (k : Nat) :
    look (m.insert x k) = single x k ∪ corefl (· ≠ x) ≫ look m :=
  hom_ext fun a j => by
    by_cases h : x = a
    · subst h; simp [look, single, corefl, graph, eq_comm]
    · simp [look, single, corefl, graph, Std.HashMap.getElem?_insert, h, Ne.symm h]

/-- `∋(pre) : Int ⟶ Nat`, core's list membership, curried. -/
def ent (pre : List (Int × Nat)) : Key ⟶ Idx := fun a j => (a, j) ∈ pre

/-- `∋` is the fold `⦇[⊥, (x↦k) ∪ −]⦈`: `[]` has no entry, `(x,k) :: pre` adds `x↦k`. -/
theorem ent_nil : ent [] = 𝟘 := hom_ext fun _ _ => ⟨fun h => (nomatch h), fun h => (h : False).elim⟩

theorem ent_cons (x : Int) (k : Nat) (pre : List (Int × Nat)) :
    ent ((x, k) :: pre) = single x k ∪ ent pre :=
  hom_ext fun a j => by simp [ent, single, corefl, graph, and_comm]

/-- `cat : (pre,rest) ↦ pre ++ rest`, `cons : (x,xs) ↦ x :: xs`, `outl : (x,xs) ↦ x` on core lists. -/
def cat : (⟨IL.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ IL := graph fun (p, q) => p ++ q
def cons : (⟨E.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ IL := graph fun (x, xs) => x :: xs
def outl : (⟨E.carrier × IL.carrier⟩ : RelSet.{0}) ⟶ E := graph Prod.fst

/-- `splits ≜ cat° (𝟙×cons°) (𝟙×outl)`: cut `L` into `(pre,rest)`, take `rest` apart as
    `(b,k) :: post`, drop `post`. -/
def splits : IL ⟶ Split := cat° ≫ rprodMap (𝟙 IL) cons° ≫ rprodMap (𝟙 IL) outl

/-- `cat°`: `L` splits as `(pre,bk)` iff `L = pre ++ bk :: post`. -/
theorem splits_apply (L pre : List (Int × Nat)) (bk : Int × Nat) :
    splits L (pre, bk) ↔ ∃ post, L = pre ++ bk :: post := by
  constructor
  · rintro ⟨⟨p, q⟩, h1, ⟨p', ⟨x, post⟩⟩, ⟨h2, h3⟩, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5; exact ⟨post, rfl⟩
  · rintro ⟨post, rfl⟩; exact ⟨(pre, bk :: post), rfl, (pre, (bk, post)), ⟨rfl, rfl⟩, rfl, rfl⟩

/-- `sorted?`: indices strictly increase along the list. -/
def sortedR : IL ⟶ IL := corefl fun L => L.Pairwise fun (_, j) (_, k) => j < k

/-- Indices along `zipIdx` strictly increase. -/
theorem zipIdx_sorted (xs : List Int) (n : Nat) : (xs.zipIdx n).Pairwise fun (_, j) (_, k) => j < k := by
  induction xs generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.pairwise_cons.mpr ⟨fun ⟨b, i⟩ hb => ?_, ih (n + 1)⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (List.mem_zipIdx hb).1

/-- `sorted? ⟨∋,∋⟩ (j<k)? = sorted? splits (∋×𝟙)`: on a sorted list two members in index order
    are a member of `pre` and the split element of `pre ++ (b,k) :: post`. -/
theorem sorted_pairs : sortedR ≫ rpair ∋ ∋ ≫ before = sortedR ≫ splits ≫ rprodMap ∋ (𝟙 E) := by
  refine hom_ext fun L ⟨⟨a, j⟩, ⟨b, k⟩⟩ => ⟨?_, ?_⟩
  · rintro ⟨_, ⟨rfl, hL⟩, _, ⟨ha, hb⟩, rfl, hjk⟩
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
    have hsuf := List.pairwise_cons.mp (List.pairwise_append.mp hL).2.1
    have hjk : j < k := hjk
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

/-! ## Laws derived from the boundary facts -/

/-- `zipIdx sorted? = zipIdx`, stated under a following `Y`. -/
theorem zipIdxR_sorted {B : RelSet.{0}} (Y : IL ⟶ B) : zipIdxR ≫ sortedR ≫ Y = zipIdxR ≫ Y := by
  have h : zipIdxR ≫ sortedR = zipIdxR :=
    hom_ext fun xs _ => ⟨fun ⟨_, h, h', _⟩ => h' ▸ h, fun h => by subst h; exact ⟨_, rfl, rfl, zipIdx_sorted xs 0⟩⟩
  rw [← Cat.assoc, h]

/-- `memPre(t) ≜ (∋×𝟙) ans(t)`: a member `(a,j)` of `pre` with `a+b=t` answers `(j,k)`. -/
def memPre (t : Int) : Split ⟶ Ans := rprodMap ∋ (𝟙 E) ≫ ans t

/-- `sorted? pairs(t) = sorted? splits memPre(t)`. -/
theorem pairs_split (t : Int) : sortedR ≫ pairs t = sortedR ≫ splits ≫ memPre t :=
  calc sortedR ≫ pairs t
      = (sortedR ≫ rpair ∋ ∋ ≫ before) ≫ ans t := by simp only [pairs, Cat.assoc]
    _ = (sortedR ≫ splits ≫ rprodMap ∋ (𝟙 E)) ≫ ans t := by rw [sorted_pairs]
    _ = sortedR ≫ splits ≫ memPre t := by simp only [memPre, Cat.assoc]

/-- `env(m,pre) ≜ look(m) ∪ ∋(pre)`: what the scan can look up after `pre`, started from `m`. -/
def env (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) : Key ⟶ Idx := look m ∪ ent pre

/-- `env(m) : pre ↦ (a,j)`, the entries of `env(m,pre)`. -/
def envR (m : Std.HashMap Int Nat) : IL ⟶ E := fun pre (a, j) => env m pre a j

/-- `hits(t,m) ≜ splits (env(m)×𝟙) ans(t)`: from `m`, an entry `t-b ↦ j` before `(b,k)` answers `(j,k)`. -/
def hits (t : Int) (m : Std.HashMap Int Nat) : IL ⟶ Ans := splits ≫ rprodMap (envR m) (𝟙 E) ≫ ans t

/-- `env(∅) = ∋`, from `look(∅) = ⊥`. -/
theorem envR_empty : envR {} = ∋ :=
  hom_ext fun pre ⟨a, j⟩ => by
    show env {} pre a j ↔ (a, j) ∈ pre
    rw [env, look_empty, DistributiveAllegory.zero_union]; exact Iff.rfl

/-- `env(insert(x,k)(m),pre) ⊑ env(m,(x,k)::pre)`: the override drops entries, adds `x↦k`. -/
theorem env_insert_le (m : Std.HashMap Int Nat) (x : Int) (k : Nat) (pre : List (Int × Nat)) :
    env (m.insert x k) pre ⊑ env m ((x, k) :: pre) := by
  rw [env, env, look_insert, ent_cons]
  exact le_iff.mpr fun a j => by
    rintro ((h | ⟨_, ⟨rfl, -⟩, h⟩) | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- `env(m,(x,k)::pre) ⊑ env(insert(x,k)(m),pre) ⊤`: the override keeps every key. -/
theorem env_keys (m : Std.HashMap Int Nat) (x : Int) (k : Nat) (pre : List (Int × Nat)) :
    env m ((x, k) :: pre) ⊑ env (m.insert x k) pre ≫ relTop Idx Idx := by
  rw [env, env, look_insert, ent_cons]
  refine le_iff.mpr fun a j => ?_
  rintro (h | h | h)
  · by_cases hx : a = x
    · exact ⟨k, Or.inl (Or.inl ⟨a, ⟨rfl, hx⟩, rfl⟩), trivial⟩
    · exact ⟨j, Or.inl (Or.inr ⟨a, ⟨rfl, hx⟩, h⟩), trivial⟩
  · exact ⟨j, Or.inl (Or.inl h), trivial⟩
  · exact ⟨j, Or.inr h, trivial⟩

/-- `splits (cons(e)×𝟙) ⊑ cons(e) splits`: a split of `L` extends to one of `e :: L`. -/
theorem splits_shift (e : Int × Nat) :
    splits ≫ rprodMap (graph (List.cons e)) (𝟙 E) ⊑ graph (List.cons e) ≫ splits :=
  le_iff.mpr fun L ⟨_, _⟩ ⟨⟨pre, _⟩, hs, hpre, hbk⟩ => by
    obtain ⟨post, rfl⟩ := (splits_apply _ _ _).mp hs
    cases hpre; cases hbk
    exact ⟨_, rfl, (splits_apply _ _ _).mpr ⟨post, rfl⟩⟩

/-- `hits(t,insert(x,k)(m)) ⊑ cons(x,k) hits(t,m)`: a later hit is a hit one entry earlier. -/
theorem hits_insert_le (t : Int) (m : Std.HashMap Int Nat) (x : Int) (k : Nat) :
    hits t (m.insert x k) ⊑ graph (List.cons (x, k)) ≫ hits t m :=
  calc hits t (m.insert x k)
      ⊑ splits ≫ rprodMap (graph (List.cons (x, k)) ≫ envR m) (𝟙 E) ≫ ans t :=
        comp_mono_left _ (comp_mono_right (rprodMap_mono
          (le_iff.mpr fun pre ⟨a, j⟩ h => ⟨_, rfl, le_iff.mp (env_insert_le m x k pre) a j h⟩) (le_refl _)) _)
    _ = (splits ≫ rprodMap (graph (List.cons (x, k))) (𝟙 E)) ≫ rprodMap (envR m) (𝟙 E) ≫ ans t := by
        rw [Cat.assoc, ← Cat.assoc (rprodMap _ _), rprodMap_comp, Cat.id_comp]
    _ ⊑ (graph (List.cons (x, k)) ≫ splits) ≫ rprodMap (envR m) (𝟙 E) ≫ ans t :=
        comp_mono_right (splits_shift _) _
    _ = graph (List.cons (x, k)) ≫ hits t m := Cat.assoc _ _ _

/-- `dom(cons(x,k) hits(t,m)) ⊑ dom(hits(t,insert(x,k)(m)))` when `t-x` misses `m`: the head split
    needs that lookup, a later one keeps its key. -/
theorem hits_cons_dom (t : Int) (m : Std.HashMap Int Nat) (x : Int) (k : Nat)
    (h : ∀ j, ¬ look m (t - x) j) (L : List (Int × Nat)) (r : Nat × Nat)
    (hr : hits t m ((x, k) :: L) r) : ∃ r', hits t (m.insert x k) L r' := by
  obtain ⟨⟨pre, b, k'⟩, hs, ⟨⟨c, j⟩, _⟩, ⟨hc, rfl⟩, _, ⟨rfl, hsum⟩, -⟩ := hr
  have hsum : c + b = t := hsum
  obtain ⟨post, hL⟩ := (splits_apply _ _ _).mp hs
  cases pre with
  | nil =>
    obtain ⟨he, -⟩ := List.cons.inj hL
    cases he
    have hc : env m [] c j := hc
    rw [env, ent_nil, union_zero] at hc
    exact (h j (by rw [show t - x = c by omega]; exact hc)).elim
  | cons p pre =>
    simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, hL⟩ := hL
    obtain ⟨j', hj', -⟩ := le_iff.mp (env_keys m x k pre) c j hc
    exact ⟨(j', k'), (pre, (b, k')), (splits_apply _ _ _).mpr ⟨post, hL⟩, ((c, j'), (b, k')), ⟨hj', rfl⟩,
      _, ⟨rfl, hsum⟩, rfl⟩

/-- `orNone(R')(a') ⊑ orNone(R)(a)` when `R'(a') ⊑ R(a)` and `R(a)` is defined only where `R'(a')` is. -/
theorem orNone_of {A A' B : RelSet.{0}} {R : A ⟶ B} {R' : A' ⟶ B} {a : A.carrier} {a' : A'.carrier}
    {r : Option B.carrier} (h1 : ∀ b, R' a' b → R a b) (h2 : ∀ b, R a b → ∃ b', R' a' b')
    (h : orNone R' a' r) : orNone R a r := by
  rcases h with ⟨b, hb, rfl⟩ | ⟨_, ⟨rfl, hn⟩, rfl⟩
  · exact Or.inl ⟨b, h1 b hb, rfl⟩
  · exact Or.inr ⟨a, ⟨rfl, fun b hb => let ⟨b', h'⟩ := h2 b hb; hn b' h'⟩, rfl⟩

/-- `f orNone(R) = orNone(f R)` for a map `f`: a map neither adds nor drops a point of the domain. -/
theorem graph_orNone {A B C : RelSet.{0}} (f : A.carrier → B.carrier) (R : B ⟶ C) :
    graph f ≫ orNone R = orNone (graph f ≫ R) :=
  hom_ext fun a r => ⟨fun ⟨_, hy, h⟩ => by
      subst hy
      exact orNone_of (fun b hb => ⟨_, rfl, hb⟩) (fun b ⟨_, hy, hb⟩ => ⟨b, hy ▸ hb⟩) h,
    fun h => ⟨_, rfl, orNone_of (fun b ⟨_, hy, hb⟩ => hy ▸ hb) (fun b hb => ⟨b, _, rfl, hb⟩) h⟩⟩

/-! ## The fold -/

/-- `scan(t) : L ↦ f` when from every start map `m`, `f(m)` is `orNone(hits(t,m))` of `L`. -/
def scan (t : Int) : IL ⟶ Scan := fun L f => ∀ m, orNone (hits t m) L (f m)

/-- **`go(t) ⊑ scan(t)`, by (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`**: on `[]` there is no split; on
    `(x,k) :: L'` a lookup hit is the head split's answer, a miss is `hits_insert_le`/`hits_cons_dom`. -/
theorem scan_le (t : Int) : (graph (go t) : IL ⟶ Scan) ⊑ scan t := by
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
  · refine Or.inr ⟨_, ⟨rfl, fun _ ⟨⟨pre, bk⟩, hs, _⟩ => ?_⟩, rfl⟩
    obtain ⟨post, hs⟩ := (splits_apply _ _ _).mp hs
    simp [listCon] at hs
  · exact (hv : False).elim
  · exact (hv : False).elim
  · obtain ⟨rfl, hX⟩ : (x, k) = e' ∧ scan t L' f' := hv
    show orNone (hits t m) ((x, k) :: L') (scanStep t (x, k) f' m)
    cases hm : m[t - x]? with
    | some j =>
      exact Or.inl ⟨(j, k), ⟨([], (x, k)), (splits_apply _ _ _).mpr ⟨L', rfl⟩, ((t - x, j), (x, k)),
        ⟨Or.inl hm, rfl⟩, _, ⟨rfl, Int.sub_add_cancel t x⟩, rfl⟩, by simp only [scanStep, hm, Option.elim]; rfl⟩
    | none =>
      rw [show scanStep t (x, k) f' m = f' (m.insert x k) by simp only [scanStep, hm, Option.elim]]
      exact orNone_of (fun r hr => let ⟨_, he, h⟩ := le_iff.mp (hits_insert_le t m x k) L' r hr; he ▸ h)
        (hits_cons_dom t m x k (fun j (hj : m[t - x]? = some j) => nomatch hm.symm.trans hj) L') (hX _)

/-! ## The derivation -/

/-- `zipIdx hits(t,∅) = twoSum(t)`. -/
theorem hits_empty (t : Int) : zipIdxR ≫ hits t {} = twoSum t :=
  calc zipIdxR ≫ hits t {}
      = zipIdxR ≫ splits ≫ memPre t := by rw [hits, envR_empty]; rfl
    _ = zipIdxR ≫ sortedR ≫ splits ≫ memPre t := (zipIdxR_sorted _).symm
    _ = zipIdxR ≫ sortedR ≫ pairs t := by rw [pairs_split]
    _ = twoSum t := zipIdxR_sorted _

/-- **The program refines the entire spec**: `graph(prog(t)) ⊑ twoSumO(t)`. -/
theorem prog_le (t : Int) : (graph (prog t) : (⟨List Int⟩ : RelSet.{0}) ⟶ Opt) ⊑ twoSumO t :=
  calc graph (prog t)
      = zipIdxR ≫ graph (go t) ≫ atEmpty := by rw [zipIdxR, atEmpty, graph_comp, graph_comp]; rfl
    _ ⊑ zipIdxR ≫ scan t ≫ atEmpty := comp_mono_left _ (comp_mono_right (scan_le t) _)
    _ ⊑ zipIdxR ≫ orNone (hits t {}) := comp_mono_left _ (le_iff.mpr fun L r ⟨f, hX, hr⟩ => hr ▸ hX {})
    _ = orNone (zipIdxR ≫ hits t {}) := graph_orNone _ _
    _ = twoSumO t := by rw [hits_empty]; rfl

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
