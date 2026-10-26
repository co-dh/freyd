/-
  §11.4–§11.5 of the RelRep design: the scans, folds and order verbs as expressions of the relation
  algebra, and the laws `kernel = spec` that tie the qlean kernels of `LeetQ.Rel.Scan` to them.

  - A verb answering a list states its law on the answer read as a point `cst(r) : 1 → list`, so
    `cst(r) = cst(x) ≫ spec` says the spec relates `x` to `r` and to nothing else.
  - The long kernels are proved on the dense long encoding, as their `*_toList` theorems are.
-/
import LeetQ.Rel.Spec
import LeetQ.Rel.Scan
import AOP.A7_2_RelSet

namespace LeetQ.Rel.Verb

open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet
open Freyd.Alg.RelSet.ListRel (dList perm ordered orderedP Perm)

variable {n : Nat}

/-! ## vocabulary -/

section Vocabulary

variable {α : Type}

/-- `cst(b) ≫ h = cst(h(b))` for a map `h`. -/
theorem cst_graph {A B C : RelSet.{0}} (b : B.carrier) (h : B.carrier → C.carrier) :
    (cst b : A ⟶ B) ≫ graph h = cst (h b) :=
  hom_ext fun _ _ => ⟨fun ⟨_, hb, hc⟩ => hc.trans (congrArg h hb), fun hc => ⟨b, rfl, hc⟩⟩

open Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel PowerAllegory in
/-- `foldr(g, e) = ⦇[e, g]⦈`: a right fold on `List` is the fold of the cons-list algebra. -/
theorem foldr_cata {A C : Type} (g : A → C → C) (e : C) :
    (graph fun ys => (CL.toList ys).foldr g e : dList A ⟶ (⟨C⟩ : RelSet.{0}))
      = ⦇(junc (sumCop (dL Unit) ⟨A × C⟩) (graph fun _ => e) (graph fun q : A × C => g q.1 q.2)
            : Alg (F Unit A) (⟨C⟩ : RelSet.{0}))⦈ := by
  refine (relCata_UP (initial Unit A) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun D r => Iff.rfl, fun a x r => ?_⟩)
  show r = g a ((CL.toList x).foldr g e) ↔ ∃ y, y = (CL.toList x).foldr g e ∧ r = g a y
  exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨y, hy, hr⟩ => by rw [hr, hy]⟩

/-- `List.Perm` read on cons-lists. -/
theorem perm_ofList : ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → Perm (CL.ofList l₁) (CL.ofList l₂)
  | _, _, .nil => Perm.nil
  | _, _, .cons x h => by rw [CL.ofList_cons, CL.ofList_cons]; exact Perm.cons x (perm_ofList h)
  | _, _, .swap x y l => by simp only [CL.ofList_cons]; exact Perm.swap y x _
  | _, _, .trans h₁ h₂ => Perm.trans (perm_ofList h₁) (perm_ofList h₂)

/-- A cons-list `Perm` read on `List`. -/
theorem perm_toList : ∀ {x y : CL.ConsList Unit α}, Perm x y → (CL.toList x).Perm (CL.toList y)
  | _, _, .nil => .nil
  | _, _, .cons a h => .cons a (perm_toList h)
  | _, _, .swap a b _ => .swap b a _
  | _, _, .trans h₁ h₂ => (perm_toList h₁).trans (perm_toList h₂)

/-- Two lists sorted under an antisymmetric `r` that are permutations of each other are one list. -/
theorem eq_of_perm_pairwise {r : α → α → Prop} (anti : ∀ a b, r a b → r b a → a = b) :
    ∀ {xs ys : List α}, xs.Perm ys → xs.Pairwise r → ys.Pairwise r → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => absurd h.length_eq (by simp)
  | _ :: _, [], h, _, _ => absurd h.length_eq (by simp)
  | a :: xs, b :: ys, h, hx, hy => by
    rw [List.pairwise_cons] at hx hy
    have hab : a = b := by
      rcases List.mem_cons.1 (h.subset (List.mem_cons_self ..)) with e | m
      · exact e
      rcases List.mem_cons.1 (h.symm.subset (List.mem_cons_self ..)) with e | m'
      · exact e.symm
      exact anti a b (hx.1 b m') (hy.1 a m)
    subst hab
    rw [eq_of_perm_pairwise anti h.cons_inv hx.2 hy.2]

/-- `cst(L) = cst(xs) ≫ sort(r)` when `L` is a permutation of `xs` sorted under the antisymmetric `r`:
    `sort(r)` relates `xs` to `L` and to nothing else. -/
theorem cst_sort (r : α → α → Prop) (anti : ∀ a b, r a b → r b a → a = b) {xs L : List α}
    (hp : L.Perm xs) (ho : L.Pairwise r) :
    (cst (CL.ofList L) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList α) = cst (CL.ofList xs) ≫ sort r :=
  hom_ext fun _ ys => by
    show ys = CL.ofList L ↔ ∃ zs, zs = CL.ofList xs ∧ ∃ ws, Perm zs ws ∧ (ws = ys ∧ orderedP r ws)
    constructor
    · rintro rfl; exact ⟨_, rfl, _, perm_ofList hp.symm, rfl, (orderedP_ofList r L).2 ho⟩
    · rintro ⟨_, rfl, ws, hw, rfl, hord⟩
      rw [← ofList_toList ws] at hord ⊢
      rw [orderedP_ofList] at hord
      have hx := perm_toList hw; rw [CL.toList_ofList] at hx
      exact congrArg CL.ofList (eq_of_perm_pairwise anti (hx.symm.trans hp.symm) hord ho)

/-- `cst(mergeSort(le)(xs)) = cst(xs) ≫ sort(r)` for a total, transitive, antisymmetric `le` deciding `r`. -/
theorem cst_mergeSort (le : α → α → Bool) (r : α → α → Prop) (hle : ∀ a b, le a b = true ↔ r a b)
    (htr : ∀ a b c, le a b → le b c → le a c) (htot : ∀ a b, (le a b || le b a) = true)
    (anti : ∀ a b, r a b → r b a → a = b) (xs : List α) :
    (cst (CL.ofList (xs.mergeSort le)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList α) = cst (CL.ofList xs) ≫ sort r :=
  cst_sort r anti (List.mergeSort_perm xs le) ((List.pairwise_mergeSort htr htot xs).imp (hle _ _).1)

/-- In a strictly ascending list, two members in order form a sublist. -/
theorem pair_sublist : ∀ {L : List Nat}, L.Pairwise (· < ·) → ∀ {a b}, a ∈ L → b ∈ L → a < b → [a, b].Sublist L
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: L, hL, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · exact (List.singleton_sublist.2 hb).cons₂ _
    · rcases List.mem_cons.1 hb with rfl | hb
      · have := hL.1 a ha'; omega
      · exact (pair_sublist hL.2 ha' hb hab).cons _

/-- In a list without repeats, two members do not appear in both orders. -/
theorem not_both_orders : ∀ {M : List α}, M.Nodup → ∀ {a b}, [a, b].Sublist M → [b, a].Sublist M → False
  | [], _, _, _, h, _ => nomatch List.sublist_nil.1 h
  | c :: M, hM, a, b, h₁, h₂ => by
    rw [List.nodup_cons] at hM
    rcases List.sublist_cons_iff.1 h₁ with s₁ | ⟨r₁, e₁, s₁⟩ <;>
      rcases List.sublist_cons_iff.1 h₂ with s₂ | ⟨r₂, e₂, s₂⟩
    · exact not_both_orders hM.2 s₁ s₂
    · cases e₂; exact hM.1 (s₁.subset (by simp))
    · cases e₁; exact hM.1 (s₂.subset (by simp))
    · cases e₁; cases e₂; exact hM.1 (s₁.subset (by simp))

/-- The grade of `v` over `til n` by `le`: positions in `le` order, ties in position order. -/
theorem pairwise_grade {β : Type} (v : Nat → β) (le : β → β → Bool) (htr : ∀ a b c, le a b → le b c → le a c)
    (htot : ∀ a b, (le a b || le b a) = true) (n : Nat) :
    ((List.range n).mergeSort fun i j => le (v i) (v j)).Pairwise
      fun i j => (le (v i) (v j) ∧ le (v j) (v i) = false) ∨ (le (v i) (v j) ∧ le (v j) (v i) ∧ i ≤ j) := by
  have htr' : ∀ a b c, le (v a) (v b) → le (v b) (v c) → le (v a) (v c) := fun a b c => htr (v a) (v b) (v c)
  have htot' : ∀ a b, (le (v a) (v b) || le (v b) (v a)) = true := fun a b => htot (v a) (v b)
  have hp := List.mergeSort_perm (List.range n) fun i j => le (v i) (v j)
  have hnd := hp.nodup_iff.2 List.nodup_range
  refine ((List.pairwise_mergeSort htr' htot' _).and (List.pairwise_iff_forall_sublist.2
    fun h => not_both_orders hnd h)).imp_of_mem fun {i j} hi hj ⟨hij, hns⟩ => ?_
  cases hji : le (v j) (v i)
  · exact .inl ⟨hij, rfl⟩
  · refine .inr ⟨hij, rfl, Nat.le_of_not_lt fun hlt => hns ?_⟩
    have hi' := List.mem_range.1 (hp.subset hi)
    have hj' := List.mem_range.1 (hp.subset hj)
    exact List.sublist_mergeSort htr' htot' (List.pairwise_pair.2 hji)
      (pair_sublist (List.pairwise_lt_range ..) (List.mem_range.2 hj') (List.mem_range.2 hi') hlt)

/-- `⊴ₓ` pointwise on a list `x = ix(L)`. -/
theorem stable_iff {β : Type} (L : List β) (lt : (⟨β⟩ : RelSet.{0}) ⟶ ⟨β⟩) (i j : Nat) :
    stable (ix L) lt i j ↔ ∃ a b, L[i]? = some a ∧ L[j]? = some b ∧ (lt a b ∨ (a = b ∧ i ≤ j)) := by
  show (∃ a, L[i]? = some a ∧ ∃ b, lt a b ∧ L[j]? = some b) ∨ ((∃ a, L[i]? = some a ∧ L[j]? = some a) ∧ i ≤ j) ↔ _
  constructor
  · rintro (⟨a, ha, b, hab, hb⟩ | ⟨⟨a, ha, hb⟩, hij⟩)
    · exact ⟨a, b, ha, hb, .inl hab⟩
    · exact ⟨a, a, ha, hb, .inr ⟨rfl, hij⟩⟩
  · rintro ⟨a, b, ha, hb, hab | ⟨rfl, hij⟩⟩
    · exact .inl ⟨a, ha, b, hab, hb⟩
    · exact .inr ⟨⟨a, ha, hb⟩, hij⟩

/-- `⊴ₓ` is antisymmetric when `lt` is a strict order. -/
theorem stable_anti {β : Type} (L : List β) (lt : (⟨β⟩ : RelSet.{0}) ⟶ ⟨β⟩)
    (hasym : ∀ a b, lt a b → ¬ lt b a) (hirr : ∀ a, ¬ lt a a) (i j : Nat) :
    stable (ix L) lt i j → stable (ix L) lt j i → i = j := by
  rw [stable_iff, stable_iff]
  rintro ⟨a, b, ha, hb, h₁⟩ ⟨b', a', hb', ha', h₂⟩
  rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨e, h₂⟩
  · exact absurd h₂ (hasym _ _ h₁)
  · cases e; exact absurd h₁ (hirr _)
  · exact absurd h₂ (hirr _)
  · omega

/-- `cst(grade) = cst(til n) ≫ sort(⊴ₓ)`: the stable grade of `xs` by `le` is `sort` of the positions under
    `⊴ₓ` at the strict `lt` that `le` decides. -/
theorem cst_grade {β : Type} [Inhabited β] (xs : List β) (le : β → β → Bool) (lt : (⟨β⟩ : RelSet.{0}) ⟶ ⟨β⟩)
    (htr : ∀ a b c, le a b → le b c → le a c) (htot : ∀ a b, (le a b || le b a) = true)
    (hanti : ∀ a b, le a b → le b a → a = b) (hlt : ∀ a b, le a b → le b a = false → lt a b)
    (hasym : ∀ a b, lt a b → ¬ lt b a) (hirr : ∀ a, ¬ lt a a) :
    (cst (CL.ofList ((List.range xs.length).mergeSort fun i j => le xs[i]! xs[j]!)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Nat)
      = cst (CL.ofList (List.range xs.length)) ≫ sort (stable (ix xs) lt) := by
  have hv : ∀ i, i < xs.length → xs[i]? = some xs[i]! := fun i h => by
    rw [getElem!_pos xs i h, List.getElem?_eq_getElem h]
  have hp := List.mergeSort_perm (List.range xs.length) fun i j => le xs[i]! xs[j]!
  refine cst_sort _ (stable_anti xs lt hasym hirr) hp
    ((pairwise_grade (fun i => xs[i]!) le htr htot _).imp_of_mem fun {i j} hi hj h => ?_)
  have hi' := List.mem_range.1 (hp.subset hi)
  have hj' := List.mem_range.1 (hp.subset hj)
  refine (stable_iff xs lt i j).2 ⟨_, _, hv i hi', hv j hj', ?_⟩
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
  · exact .inl (hlt _ _ h₁ h₂)
  · exact .inr ⟨hanti _ _ h₁ h₂, h₃⟩

/-- The grade's positions read back as naturals, below `2⁶³`: the merge sort of `til n`. -/
theorem grade_map (desc : Bool) (xs : List Int64) (h63 : xs.length < 2 ^ 63) :
    (Spec.grade desc xs).map Int64.toNatClampNeg = (List.range xs.length).mergeSort
      fun i j => if desc then decide (xs[j]! ≤ xs[i]!) else decide (xs[i]! ≤ xs[j]!) := by
  rw [Spec.grade, List.map_map]
  refine (List.map_congr_left fun i hi => ?_).trans (List.map_id _)
  have := List.mem_range.1 ((List.mergeSort_perm _ _).subset hi)
  exact Int64.toNatClampNeg_ofNat_of_lt (by omega)

/-- `f/` with q's null skip, head first: `skip(f)(x, a) = a` at a null `x`, else `f(x, a)`. -/
def skipNul (f : Int64 → Int64 → Int64) (x a : Int64) : Int64 := if x == Spec.nul then a else f x a

/-- The left fold `Spec.over` is the right fold of `skipNul` when `f` is associative with unit `e`. -/
theorem over_foldr (f : Int64 → Int64 → Int64) (e : Int64) (hA : ∀ a b c, f (f a b) c = f a (f b c))
    (hl : ∀ a, f e a = a) (hr : ∀ a, f a e = a) (xs : List Int64) :
    Spec.over f e xs = xs.foldr (skipNul f) e := by
  suffices h : ∀ (xs : List Int64) a, xs.foldl (fun a x => if x == Spec.nul then a else f a x) a
      = f a (xs.foldr (skipNul f) e) by rw [Spec.over, h, hl]
  intro xs; induction xs with
  | nil => intro a; exact (hr a).symm
  | cons x xs ih =>
    intro a; rw [List.foldl_cons, List.foldr_cons, ih]
    cases hx : (x == Spec.nul) <;> simp [skipNul, hx, hA]

/-- A list's length, read on its cons-list. -/
theorem clen_ofList : ∀ xs : List α, ListRel.clen (CL.ofList xs) = xs.length
  | [] => rfl
  | a :: xs => by rw [CL.ofList_cons, List.length_cons, ← clen_ofList xs]; rfl

/-- `countP` over `Fin g` of a test on the value is `countP` over `til g`. -/
theorem countP_finRange (q : Nat → Bool) : ∀ g, (List.finRange g).countP (fun r => q r.val) = (List.range g).countP q
  | 0 => rfl
  | g+1 => by
    simp only [List.finRange_succ_last, List.range_succ, List.countP_append, List.countP_map, Function.comp_def,
      Fin.coe_castSucc, countP_finRange q g, List.countP_singleton, Fin.val_last]

/-- A test closed downward on `til G` passes the first `countP` positions: `k ≤ countP` iff `k = 0` or
    position `k−1` passes. -/
theorem le_countP_range (p : Nat → Bool) {G : Nat} (hd : ∀ a b, a ≤ b → b < G → p b = true → p a = true) :
    ∀ g, g ≤ G → ∀ k, k ≤ (List.range g).countP p ↔ k = 0 ∨ (k ≤ g ∧ p (k-1) = true)
  | 0, _, k => by
    simp only [List.range_zero, List.countP_nil]
    exact ⟨fun h => .inl (by omega), fun h => by rcases h with h | ⟨h, _⟩ <;> omega⟩
  | g+1, hg, k => by
    have ih := le_countP_range p hd g (by omega)
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    by_cases hp : p g = true
    · have hc : (List.range g).countP p = g := Nat.le_antisymm (Nat.le_trans List.countP_le_length (by simp))
        ((ih g).2 (by
          rcases Nat.eq_zero_or_pos g with h | h
          · exact .inl h
          · exact .inr ⟨Nat.le_refl _, hd _ _ (by omega) (by omega) hp⟩))
      rw [hc, if_pos hp]
      exact ⟨fun hk => if k0 : k = 0 then .inl k0 else .inr ⟨hk, hd _ _ (by omega) (by omega) hp⟩,
        fun h => by rcases h with h | ⟨h, _⟩ <;> omega⟩
    · rw [if_neg hp, Nat.add_zero, ih]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases h with h | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨by omega, h2⟩
      · rcases h with h | ⟨h1, h2⟩
        · exact .inl h
        · refine .inr ⟨?_, h2⟩
          rcases Nat.lt_or_ge g k with h3 | h3
          · rw [show k - 1 = g by omega] at h2; exact absurd h2 hp
          · exact h3

/-- Under `Cuts`, position `i` lies in group `j < g` exactly when `o[j] ≤ i < o[j+1]`. -/
theorem group_iff {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) {j : Nat} (hj : j < g) (i : Nat) :
    Parted.group o i = j ↔ (o.toList[j]!).toNatClampNeg ≤ i ∧ i < (o.toList[j+1]!).toNatClampNeg := by
  have e : ∀ m (hm : m ≤ g), o.toList[m]! = o.get ⟨m, by omega⟩ := fun m hm => by
    rw [getElem!_pos _ m (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
  let p : Nat → Bool := fun m => decide ((o.toList[m+1]!).toInt ≤ (i : Int))
  have hA : Parted.group o i = (List.range g).countP p := by
    rw [← countP_finRange p g]; unfold Parted.group
    congr 1; funext r; simp only [p]; rw [e (r.val+1) (by omega)]; rfl
  have hd : ∀ a b, a ≤ b → b < g → p b = true → p a = true := fun a b hab hb h => by
    simp only [p, decide_eq_true_eq] at h ⊢
    exact Int.le_trans (cuts_get co (i := a+1) (j := b+1) (by omega) (by omega)).2.1 h
  have L := le_countP_range p hd g (Nat.le_refl g)
  have h0 : (o.toList[0]!).toInt = 0 := by
    rw [e 0 (by omega), show (⟨0, by omega⟩ : Fin (g+1)) = 0 from Fin.ext (by simp), co.2.1]; rfl
  obtain ⟨a0, a1, -⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
  have ca := Ops.toNat_cast a0
  have cb := Ops.toNat_cast (Int.le_trans a0 a1)
  have key : ∀ c : Nat, ∀ P Q : Prop, (j ≤ c ↔ P) → (j+1 ≤ c ↔ Q) → (c = j ↔ P ∧ ¬Q) :=
    fun c P Q h1 h2 => by rw [← h1, ← h2]; omega
  have pj : ∀ m, p m = true ↔ (o.toList[m+1]!).toInt ≤ (i : Int) := fun m => decide_eq_true_iff
  rw [hA, key _ _ _ (L j) (L (j+1)), pj, pj, Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · omega
  · rw [Nat.sub_add_cancel hpos]; omega

/-- `grpL(grp o)` at a group `j < g`: its rows `[o[j], o[j+1])` in position order. -/
theorem grpL_grp {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) {j : Nat} (hj : j < g)
    (ys : CL.ConsList Unit Nat) :
    grpL (grp o) j ys ↔ ys = CL.ofList (List.range' (o.toList[j]!).toNatClampNeg
      ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)) := by
  obtain ⟨a0, a1, -⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
  have ca := Ops.toNat_cast a0
  have cb := Ops.toNat_cast (Int.le_trans a0 a1)
  have mem : ∀ i, i ∈ List.range' (o.toList[j]!).toNatClampNeg
      ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg) ↔ j = Parted.group o i := fun i => by
    rw [List.mem_range'_1, eq_comm, group_iff co hj]; omega
  have pw : (List.range' (o.toList[j]!).toNatClampNeg
      ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)).Pairwise (· < ·) := List.pairwise_lt_range'
  show (Λ (grp o)° ≫ enum) j ys ↔ _
  rw [Λ_eq_classifier]
  show (∃ P, P = (fun i => (grp o)° j i) ∧ enum P ys) ↔ _
  constructor
  · rintro ⟨P, rfl, hP⟩
    obtain ⟨hS, ho⟩ := (enum_iff _ _).1 hP
    rw [← ofList_toList ys, orderedP_ofList] at ho
    rw [← ofList_toList ys]
    refine congrArg CL.ofList (eq_of_pairwise_lt ho pw fun i => ?_)
    (rw [mem, ← inlistP_ofList, ofList_toList, ← hS]) <;> exact Iff.rfl
  · rintro rfl
    exact ⟨_, rfl, (enum_iff _ _).2 ⟨funext fun i => propext ((mem i).symm.trans (inlistP_ofList i _).symm),
      (orderedP_ofList _ _).2 pw⟩⟩

/-- `list(ix xs)` takes the positions `[a, a+k)` to the rows `(xs.drop a).take k`. -/
theorem listP_ix_range' (xs : List α) : ∀ k a, a + k ≤ xs.length → ∀ ys,
    ListRel.listP (ix xs) (CL.ofList (List.range' a k)) ys ↔ ys = CL.ofList ((xs.drop a).take k)
  | 0, a, _, ys => by
    cases ys with
    | wrap u => cases u; exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b y => exact ⟨fun h => h.elim, fun h => nomatch h⟩
  | k+1, a, h, ys => by
    have ha : a < xs.length := by omega
    rw [List.range'_succ, List.drop_eq_getElem_cons ha, List.take_succ_cons, CL.ofList_cons, CL.ofList_cons]
    cases ys with
    | wrap u => exact ⟨fun h => h.elim, fun h => nomatch h⟩
    | cons b y =>
      show (xs[a]? = some b ∧ ListRel.listP (ix xs) (CL.ofList (List.range' (a+1) k)) y) ↔ _
      rw [listP_ix_range' xs k (a+1) (by omega) y, List.getElem?_eq_getElem ha]
      simp only [CL.ConsList.cons.injEq, Option.some.injEq]
      exact and_congr eq_comm Iff.rfl

/-- The rows `[a, b)` of `xs` read by position are its slice `(xs.drop a).take (b−a)`. -/
theorem take_drop_map [Inhabited α] (xs : List α) {a b : Nat} (hb : b ≤ xs.length) :
    (List.range' a (b - a)).map (fun i => xs[i]!) = (xs.drop a).take (b - a) := by
  apply List.ext_getElem (by simp only [List.length_map, List.length_range', List.length_take, List.length_drop]; omega)
  intro k h1 h2
  simp only [List.length_map, List.length_range'] at h1
  simp only [List.getElem_map, List.getElem_range', List.getElem_take, List.getElem_drop, Nat.one_mul]
  exact getElem!_pos xs _ (by omega)

/-- The positions of `til n` in `[a, b)`, `b ≤ n`, are `range'`. -/
theorem filter_range_eq (n a b : Nat) (hb : b ≤ n) :
    (List.range n).filter (fun i => decide (a ≤ i ∧ i < b)) = List.range' a (b - a) :=
  eq_of_pairwise_lt ((List.pairwise_lt_range ..).filter _) List.pairwise_lt_range' fun i => by
    simp only [List.mem_filter, List.mem_range, List.mem_range'_1, decide_eq_true_eq]; omega

/-- `Spec.groups = grpL(grp o) ≫ list(x)` on `til g`, read after a map `f` of each group: group `j < g` of
    the cuts `o` is the rows `grpL(grp o)` gives `j`, through `x`. -/
theorem ix_groups {v : QAtomicType} {β : Type} {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) (x : Arr v n)
    (f : CL.ConsList Unit (El v) → β) :
    ix ((Spec.groups (o.toList.map Int64.toNatClampNeg) x.toList).map fun l => f (CL.ofList l))
      = corefl (· < g) ≫ grpL (grp o) ≫ ListRel.list x.rel ≫ (graph f : dList (El v) ⟶ (⟨β⟩ : RelSet.{0})) :=
  hom_ext fun (j : Nat) c => by
    rw [Spec.groups_range, List.map_map, List.length_map, Arr.length_toList, Nat.add_sub_cancel]
    show ((List.range g).map _)[j]? = some c ↔
      ∃ z, (j = z ∧ j < g) ∧ ∃ zs, grpL (grp o) z zs ∧ ∃ ws, ListRel.listP x.rel zs ws ∧ c = f ws
    by_cases hj : j < g
    · obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
      have ca := Ops.toNat_cast a0
      have cb := Ops.toNat_cast (Int.le_trans a0 a1)
      rw [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq]
      simp only [Function.comp_apply, Ops.map_get! o (show j ≤ g by omega), Ops.map_get! o (show j + 1 ≤ g by omega)]
      have hl : (o.toList[j]!).toNatClampNeg + ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)
          ≤ x.toList.length := by rw [Arr.length_toList]; omega
      constructor
      · intro e
        exact ⟨j, ⟨rfl, hj⟩, _, (grpL_grp co hj _).2 rfl, _, (listP_ix_range' x.toList _ _ hl _).2 rfl, e.symm⟩
      · rintro ⟨_, ⟨rfl, -⟩, zs, hz, ws, hw, rfl⟩
        rw [(grpL_grp co hj zs).1 hz] at hw
        rw [(listP_ix_range' x.toList _ _ hl ws).1 hw]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
      exact ⟨(fun e => nomatch e), by rintro ⟨_, ⟨_, h⟩, -⟩; exact absurd h hj⟩

end Vocabulary

/-! ## The laws -/

open QLean.Kernel in
/-- `f/x = ⦇[e, f]⦈` on a dense long column, `f` associative with unit `e` = the kernel's seed, the
    null skipped (`skipNul`). -/
theorem over_rel {op : Coc.Over} (hb : op.boolCast = false)
    (hA : ∀ a b c, op.step (op.step a b) c = op.step a (op.step b c))
    (hl : ∀ a, op.step (op.denseSeed Ew.i64 Spec.nul) a = a) (hr : ∀ a, op.step a (op.denseSeed Ew.i64 Spec.nul) = a)
    {R : Arr .long n} {b : ByteArray} (hc : R.c.enc = .bytes b) {a : Int64} (h : Ops.over op R = some a) :
    (cst a : (⟨Unit⟩ : RelSet.{0}) ⟶ (⟨Int64⟩ : RelSet.{0}))
      = cst (CL.ofList R.toList) ≫ ⦇(junc (sumCop (CL.dL Unit) ⟨Int64 × Int64⟩)
          (graph fun _ => op.denseSeed Ew.i64 Spec.nul) (graph fun q : Int64 × Int64 => skipNul op.step q.1 q.2)
          : Alg (CL.F Unit Int64) (⟨Int64⟩ : RelSet.{0}))⦈ :=
  calc (cst a : (⟨Unit⟩ : RelSet.{0}) ⟶ (⟨Int64⟩ : RelSet.{0}))
      = cst (Spec.over op.step (op.denseSeed Ew.i64 Spec.nul) R.toList) :=
        congrArg cst (Option.some.inj (h.symm.trans (Ops.over_bytes hb hc)))
    _ = cst (R.toList.foldr (skipNul op.step) (op.denseSeed Ew.i64 Spec.nul)) := by rw [over_foldr _ _ hA hl hr]
    _ = cst (CL.ofList R.toList) ≫ graph fun ys => (CL.toList ys).foldr (skipNul op.step) (op.denseSeed Ew.i64 Spec.nul) := by
        rw [cst_graph, CL.toList_ofList]
    _ = _ := by rw [foldr_cata]

/-- `asc x = sort(≤)(x)` on a dense long column. -/
theorem asc_rel {R S : Arr .long n} {ws : List UInt64} (hx : longWords R.c = some ws) (hn : n < USize.size)
    (h : Ops.sort false R = some S) :
    (cst (CL.ofList S.toList) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Int64) = cst (CL.ofList R.toList) ≫ sort (· ≤ ·) :=
  calc (cst (CL.ofList S.toList) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Int64)
      = cst (CL.ofList (Spec.sort false R.toList)) := by rw [Ops.sort_toList hx hn h]
    _ = cst (CL.ofList R.toList) ≫ sort (· ≤ ·) :=
        cst_mergeSort (fun a b => decide (a ≤ b)) _ (fun _ _ => decide_eq_true_iff)
          (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact Int64.le_trans h₁ h₂)
          (fun a b => by rcases Int64.le_total a b with h | h <;> simp [h])
          (fun _ _ => Int64.le_antisymm) _

/-- `desc x = sort(≥)(x)` on a dense long column. -/
theorem desc_rel {R S : Arr .long n} {ws : List UInt64} (hx : longWords R.c = some ws) (hn : n < USize.size)
    (h : Ops.sort true R = some S) :
    (cst (CL.ofList S.toList) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Int64) = cst (CL.ofList R.toList) ≫ sort (· ≥ ·) :=
  calc (cst (CL.ofList S.toList) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Int64)
      = cst (CL.ofList (Spec.sort true R.toList)) := by rw [Ops.sort_toList hx hn h]
    _ = cst (CL.ofList R.toList) ≫ sort (· ≥ ·) :=
        cst_mergeSort (fun a b => decide (b ≤ a)) _ (fun _ _ => decide_eq_true_iff)
          (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact Int64.le_trans h₂ h₁)
          (fun a b => by rcases Int64.le_total a b with h | h <;> simp [h])
          (fun _ _ h₁ h₂ => Int64.le_antisymm h₂ h₁) _

/-- `<x = sort(⊴ₓ)` of `til n` on a dense long column, positions below `2⁶³`. -/
theorem iasc_rel {R S : Arr .long n} {ws : List UInt64} (hx : longWords R.c = some ws) (hn : n < USize.size)
    (h63 : n < 2 ^ 63) (h : Ops.grade false R = some S) :
    (cst (CL.ofList (S.toList.map Int64.toNatClampNeg)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Nat)
      = cst (CL.ofList (List.range n)) ≫ sort (stable R.rel fun a b : Int64 => a < b) :=
  calc (cst (CL.ofList (S.toList.map Int64.toNatClampNeg)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Nat)
      = cst (CL.ofList ((Spec.grade false R.toList).map Int64.toNatClampNeg)) := by rw [Ops.grade_toList hx hn h]
    _ = cst (CL.ofList (List.range R.toList.length)) ≫ sort (stable R.rel fun a b : Int64 => a < b) := by
        rw [grade_map false _ (by rw [Arr.length_toList]; exact h63)]
        exact cst_grade R.toList (fun a b => decide (a ≤ b)) _
          (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact Int64.le_trans h₁ h₂)
          (fun a b => by rcases Int64.le_total a b with h | h <;> simp [h])
          (fun _ _ h₁ h₂ => Int64.le_antisymm (of_decide_eq_true h₁) (of_decide_eq_true h₂))
          (fun _ _ _ h₂ => Int64.not_le.1 (of_decide_eq_false h₂))
          (fun a b h₁ h₂ => by simp only [Int64.lt_iff_toInt_lt] at h₁ h₂; omega)
          (fun a h => by simp only [Int64.lt_iff_toInt_lt] at h; omega)
    _ = cst (CL.ofList (List.range n)) ≫ sort (stable R.rel fun a b : Int64 => a < b) := by rw [Arr.length_toList]

/-- `>x = sort(⊵ₓ)` of `til n` on a dense long column, positions below `2⁶³`. -/
theorem idesc_rel {R S : Arr .long n} {ws : List UInt64} (hx : longWords R.c = some ws) (hn : n < USize.size)
    (h63 : n < 2 ^ 63) (h : Ops.grade true R = some S) :
    (cst (CL.ofList (S.toList.map Int64.toNatClampNeg)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Nat)
      = cst (CL.ofList (List.range n)) ≫ sort (stable R.rel fun a b : Int64 => a > b) :=
  calc (cst (CL.ofList (S.toList.map Int64.toNatClampNeg)) : (⟨Unit⟩ : RelSet.{0}) ⟶ dList Nat)
      = cst (CL.ofList ((Spec.grade true R.toList).map Int64.toNatClampNeg)) := by rw [Ops.grade_toList hx hn h]
    _ = cst (CL.ofList (List.range R.toList.length)) ≫ sort (stable R.rel fun a b : Int64 => a > b) := by
        rw [grade_map true _ (by rw [Arr.length_toList]; exact h63)]
        exact cst_grade R.toList (fun a b => decide (b ≤ a)) _
          (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact Int64.le_trans h₂ h₁)
          (fun a b => by rcases Int64.le_total a b with h | h <;> simp [h])
          (fun _ _ h₁ h₂ => Int64.le_antisymm (of_decide_eq_true h₂) (of_decide_eq_true h₁))
          (fun _ _ _ h₂ => Int64.not_le.1 (of_decide_eq_false h₂))
          (fun a b h₁ h₂ => by simp only [gt_iff_lt, Int64.lt_iff_toInt_lt] at h₁ h₂; omega)
          (fun a h => by simp only [gt_iff_lt, Int64.lt_iff_toInt_lt] at h; omega)
    _ = cst (CL.ofList (List.range n)) ≫ sort (stable R.rel fun a b : Int64 => a > b) := by rw [Arr.length_toList]

/-- `count each` by the cuts `o`: `corefl(<g) ≫ grpL(grp o) ≫ list(x) ≫ length`, as a long. -/
theorem countBy_rel {v : QAtomicType} {g : Nat} {o : Arr .long (g+1)} {co : Cuts o n} {x : Arr v n}
    {wo : List UInt64} (ho : longWords o.c = some wo) (hg : g + 1 < USize.size) {S : Arr .long g}
    (h : Ops.countBy ⟨g, n, o, co, x⟩ = some S) :
    S.rel = corefl (· < g) ≫ grpL (grp o) ≫ ListRel.list x.rel ≫ ListRel.length
      ≫ (graph Int64.ofNat : (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Int64⟩ : RelSet.{0})) :=
  calc S.rel = ix ((Spec.groups (o.toList.map Int64.toNatClampNeg) x.toList).map fun l =>
          Int64.ofNat (ListRel.clen (CL.ofList l))) := by
        show ix S.toList = _
        rw [Ops.countBy_toList ho hg h, Spec.countBy]; simp only [clen_ofList]
    _ = corefl (· < g) ≫ grpL (grp o) ≫ ListRel.list x.rel
          ≫ (graph fun ys => Int64.ofNat (ListRel.clen ys) : dList (El v) ⟶ (⟨Int64⟩ : RelSet.{0})) :=
        ix_groups co x fun ys => Int64.ofNat (ListRel.clen ys)
    _ = _ := by
        rw [show (ListRel.length : dList (El v) ⟶ (⟨Nat⟩ : RelSet.{0})) ≫ (graph Int64.ofNat : (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Int64⟩ : RelSet.{0}))
          = graph fun ys => Int64.ofNat (ListRel.clen ys) from graph_comp _ _]

/-- `last each` by the cuts `o` on a long column: the greatest row of each group through `x`, `0N` for an
    empty group, `corefl(<g) ≫ miss(Λ(grp(o)°) ≫ est(≥) ≫ x, 0N)`. -/
theorem lastBy_rel {g : Nat} {o : Arr .long (g+1)} {co : Cuts o n} {x : Arr .long n} {wo wx : List UInt64}
    (ho : longWords o.c = some wo) (hx : longWords x.c = some wx) (hg : g + 1 < USize.size) (hn : n < USize.size)
    {S : Arr .long g} (h : Ops.lastBy ⟨g, n, o, co, x⟩ = some S) :
    S.rel = corefl (· < g) ≫ miss (Λ (grp o)° ≫ est (· ≥ ·) ≫ x.rel) Spec.nul :=
  calc S.rel = ix ((Spec.groups (o.toList.map Int64.toNatClampNeg) x.toList).map fun l => l.getLastD Spec.nul) :=
        congrArg ix (Ops.lastBy_toList ho hx hg hn h)
    _ = corefl (· < g) ≫ miss (Λ (grp o)° ≫ est (· ≥ ·) ≫ x.rel) Spec.nul := hom_ext fun (j : Nat) c => by
        rw [Spec.groups_range, List.map_map, List.length_map, Arr.length_toList, Nat.add_sub_cancel]
        show ((List.range g).map _)[j]? = some c ↔ ∃ z, (j = z ∧ j < g) ∧ miss (Λ (grp o)° ≫ est (· ≥ ·) ≫ x.rel) Spec.nul z c
        by_cases hj : j < g
        · obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
          have ca := Ops.toNat_cast a0
          have cb := Ops.toNat_cast (Int.le_trans a0 a1)
          have T : ∀ i : Nat, (grp o)° j i ↔ (o.toList[j]!).toNatClampNeg ≤ i ∧ i < (o.toList[j+1]!).toNatClampNeg :=
            fun i => eq_comm.trans (group_iff co hj i)
          have hM : ∀ c, (Λ (grp o)° ≫ est (· ≥ ·) ≫ x.rel) j c ↔ (o.toList[j]!).toNatClampNeg
              < (o.toList[j+1]!).toNatClampNeg ∧ x.toList[(o.toList[j+1]!).toNatClampNeg - 1]? = some c := fun c => by
            rw [Λ_eq_classifier]
            show (∃ P, P = (fun i => (grp o)° j i) ∧ ∃ w : Nat, (P w ∧ ∀ z : Nat, P z → z ≤ w) ∧ x.toList[w]? = some c) ↔ _
            constructor
            · rintro ⟨_, rfl, w, ⟨hw, hmax⟩, e⟩
              have hw' := (T w).1 hw
              have hb := hmax ((o.toList[j+1]!).toNatClampNeg - 1) ((T _).2 (by omega))
              exact ⟨by omega, by rwa [show (o.toList[j+1]!).toNatClampNeg - 1 = w by omega]⟩
            · rintro ⟨hab, e⟩
              exact ⟨_, rfl, _, ⟨(T _).2 (by omega), fun z hz => by have := (T z).1 hz; omega⟩, e⟩
          have key : miss (Λ (grp o)° ≫ est (· ≥ ·) ≫ x.rel) Spec.nul j c ↔
              ((x.toList.drop (o.toList[j]!).toNatClampNeg).take
                ((o.toList[j+1]!).toNatClampNeg - (o.toList[j]!).toNatClampNeg)).getLastD Spec.nul = c := by
            rw [miss_iff]; simp only [hM]
            rcases Nat.lt_or_ge (o.toList[j]!).toNatClampNeg (o.toList[j+1]!).toNatClampNeg with hab | hab
            · rw [Spec.getLastD_take_drop _ _ hab (by rw [Arr.length_toList]; omega),
                getElem!_pos x.toList _ (by rw [Arr.length_toList]; omega),
                List.getElem?_eq_getElem (l := x.toList) (by rw [Arr.length_toList]; omega)]
              simp only [Option.some.injEq]
              exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd ⟨_, hab, rfl⟩ h.1), fun h => .inl ⟨hab, h⟩⟩
            · rw [Nat.sub_eq_zero_of_le hab, List.take_zero, List.getLastD_nil]
              exact ⟨fun h => h.elim (fun h => absurd h.1 (by omega)) (fun h => h.2.symm),
                fun h => .inr ⟨fun ⟨_, h', _⟩ => absurd h' (by omega), h.symm⟩⟩
          rw [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq]
          simp only [Function.comp_apply, Ops.map_get! o (show j ≤ g by omega),
            Ops.map_get! o (show j + 1 ≤ g by omega)]
          rw [← key]
          exact ⟨fun e => ⟨j, ⟨rfl, hj⟩, e⟩, by rintro ⟨_, ⟨rfl, -⟩, hm⟩; exact hm⟩
        · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
          exact ⟨(fun e => nomatch e), by rintro ⟨_, ⟨_, h⟩, -⟩; exact absurd h hj⟩

open QLean.Kernel in
/-- `select f x by k` on a dense long column, `f` associative with unit `e` = the kernel's seed:
    `corefl(<g) ≫ grpL(grp o) ≫ list(x) ≫ ⦇[e, f]⦈`, the null skipped (`skipNul`). -/
theorem overBy_rel {op : Coc.Over} (hb : op.boolCast = false)
    (hA : ∀ a b c, op.step (op.step a b) c = op.step a (op.step b c))
    (hl : ∀ a, op.step (op.denseSeed Ew.i64 Spec.nul) a = a) (hr : ∀ a, op.step a (op.denseSeed Ew.i64 Spec.nul) = a)
    {g : Nat} {o : Arr .long (g+1)} {co : Cuts o n} {x : Arr .long n} {b ob : ByteArray} {S : Arr .long g}
    (hg : g < USize.size) (h63 : g < 2 ^ 63) (hc : x.c.enc = .bytes b) (ho : o.c.enc = .bytes ob)
    (h : Ops.overBy op ⟨g, n, o, co, x⟩ = some ⟨.long, S⟩) :
    S.rel = corefl (· < g) ≫ grpL (grp o) ≫ ListRel.list x.rel ≫ ⦇(junc (sumCop (CL.dL Unit) ⟨Int64 × Int64⟩)
          (graph fun _ => op.denseSeed Ew.i64 Spec.nul) (graph fun q : Int64 × Int64 => skipNul op.step q.1 q.2)
          : Alg (CL.F Unit Int64) (⟨Int64⟩ : RelSet.{0}))⦈ :=
  calc S.rel = ix ((Spec.groups (o.toList.map Int64.toNatClampNeg) x.toList).map fun l =>
          (CL.toList (CL.ofList l)).foldr (skipNul op.step) (op.denseSeed Ew.i64 Spec.nul)) := by
        show ix S.toList = _
        rw [Ops.overBy_bytes hb hg h63 hc ho h, Spec.groups_range, List.map_map, List.length_map, Arr.length_toList,
          Nat.add_sub_cancel]
        refine congrArg ix (List.map_congr_left fun j hj => ?_)
        have hj := List.mem_range.1 hj
        obtain ⟨a0, a1, a2⟩ := cuts_get co (i := j) (j := j + 1) (by omega) (by omega)
        have cb := Ops.toNat_cast (Int.le_trans a0 a1)
        simp only [Function.comp_apply, CL.toList_ofList, Ops.map_get! o (show j ≤ g by omega),
          Ops.map_get! o (show j + 1 ≤ g by omega)]
        rw [filter_range_eq n _ _ (by omega), take_drop_map _ (by rw [Arr.length_toList]; omega),
          over_foldr _ _ hA hl hr]
    _ = corefl (· < g) ≫ grpL (grp o) ≫ ListRel.list x.rel ≫ (graph fun ys =>
          (CL.toList ys).foldr (skipNul op.step) (op.denseSeed Ew.i64 Spec.nul) : dList Int64 ⟶ (⟨Int64⟩ : RelSet.{0})) :=
        ix_groups co x fun ys => (CL.toList ys).foldr (skipNul op.step) (op.denseSeed Ew.i64 Spec.nul)
    _ = _ := by rw [foldr_cata]

#print axioms countBy_rel
#print axioms lastBy_rel
#print axioms overBy_rel
#print axioms over_rel
#print axioms asc_rel
#print axioms desc_rel
#print axioms iasc_rel
#print axioms idesc_rel

end LeetQ.Rel.Verb
