/-
  §11 of the RelRep design, its foundation: the k verbs as expressions of the relation algebra of
  `Rel(Set)` (AOP's `RelSet`), and the laws `kernel = spec` that tie the qlean kernels to them.

  - A list `x : Arr t n` reads as `x.rel = ix(x.toList) : Idx ⟶ El t`, position to value: partial,
    defined exactly on `til n`. A `Rel k v` reads as `Holds`, its tabulation `key° ≫ val` (`mk_rel`).
  - Positions are `Nat`; a long index column reaches them through `pos`, the partial map `Int64 → Nat`.
  - Each law composes the kernel's `*_toList` with the List spec read as the expression (`ix_*`).
-/
import LeetQ.Rel.Struct
import AOP.A5_6_ListCombinators
import AOP.A6_FinRel

namespace LeetQ.Rel.Verb

open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet
open Freyd.Alg.RelSet.ListRel (dList setify perm ordered orderedP inlistP Perm)

variable {t : QAtomicType} {n : Nat}

/-! ## The relational reading -/

/-- `x` as the relation from its positions to its values, `ix(x.toList)`. -/
def _root_.LeetQ.Rel.Arr.rel (x : Arr t n) : Idx ⟶ (⟨El t⟩ : RelSet.{0}) := ix x.toList

theorem rel_iff (x : Arr t n) (j : Nat) (a : El t) : x.rel j a ↔ ∃ h : j < n, x.get ⟨j, h⟩ = a := by
  show x.toList[j]? = some a ↔ _
  constructor
  · intro e
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.1 e
    exact ⟨by rwa [Arr.length_toList] at h, by rw [← e, Arr.getElem_toList]⟩
  · rintro ⟨h, e⟩
    exact List.getElem?_eq_some_iff.2 ⟨by rw [Arr.length_toList]; exact h, by rw [Arr.getElem_toList]; exact e⟩

/-! ## Position maps, each a partial map on `Nat` positions -/

/-- `take(k)` of `n` positions: `j ↦ (takeFrom k n + j) mod n` on `j < |k|`; a negative `k` starts from the end. -/
def take (k : Int) (n : Nat) : Idx ⟶ Idx := corefl (· < k.natAbs) ≫ graph fun j => (Kernel.takeFrom k n + j) % n

/-- `drop(k)` of `n` positions: `j ↦ j+k` (`k ≥ 0`), the first `n−|k|` kept (`k < 0`). -/
def drop (k : Int) (n : Nat) : Idx ⟶ Idx := corefl (· < n - k.natAbs) ≫ graph (· + k.toNat)

/-- `rot(k)` of `n` positions: `j ↦ (j + k mod n) mod n`. -/
def rot (k : Int) (n : Nat) : Idx ⟶ Idx := corefl (· < n) ≫ graph fun j => (j + (k.emod n).toNat) % n

/-- `rev` of `n` positions: `j ↦ n−1−j`. -/
def rev (n : Nat) : Idx ⟶ Idx := corefl (· < n) ≫ graph fun j => n - 1 - j

/-- `shift`: `j ↦ j−1` on `j ≥ 1`, the previous position. -/
def shift : Idx ⟶ Idx := corefl (1 ≤ ·) ≫ graph (· - 1)

/-- `split : til(n+m) → til n + til m`. -/
def split (n m : Nat) : Idx ⟶ (⟨Nat ⊕ Nat⟩ : RelSet.{0}) :=
  corefl (· < n + m) ≫ graph fun i => if i < n then .inl i else .inr (i - n)

/-- `grp(o)`: position `i` to the group holding it under the offsets `o`, `o bin i` (`Parted.group`). -/
def grp {g : Nat} (o : Arr .long (g+1)) : Idx ⟶ Idx := graph (Parted.group o)

/-- `pos`: a long index as a position, defined on `i ≥ 0`. -/
def pos : (⟨Int64⟩ : RelSet.{0}) ⟶ Idx := corefl (0 ≤ ·) ≫ graph fun i => i.toInt.toNat

/-! ## Derived forms, each defined once -/

section Derived

variable {A B : RelSet.{0}}

/-- `dom R = 𝟙 ∩ (R ≫ R°)`. -/
def dom (R : A ⟶ B) : A ⟶ A := 𝟙 A ∩ (R ≫ R°)

/-- `ran R = dom(R°)`. -/
def ran (R : A ⟶ B) : B ⟶ B := dom R°

/-- `corNeg(C) = 𝟙 ∩ (C \ 𝟘)`: the coreflexive on what `C` misses. AOP's `corNeg` needs a
    `BooleanAllegory`, which the constructive `RelSet` is not; this is its division form. -/
def corNeg (C : A ⟶ A) : A ⟶ A := 𝟙 A ∩ (C \ (𝟘 : A ⟶ A))

/-- `!b = ! ≫ b`: the constant map at `b`. -/
def cst (b : B.carrier) : A ⟶ B := graph fun _ => b

/-- `χ(C) = (C ≫ !1b) ∪ (corNeg(C) ≫ !0b)`: the boolean list of a coreflexive. -/
def χ (C : A ⟶ A) : A ⟶ (⟨Bool⟩ : RelSet.{0}) := (C ≫ cst true) ∪ (corNeg C ≫ cst false)

/-- `miss(R, e) = R ∪ (corNeg(dom R) ≫ !e)`: `R` filled with `e` where it is undefined. -/
def miss (R : A ⟶ B) (e : B.carrier) : A ⟶ B := R ∪ (corNeg (dom R) ≫ cst e)

/-- `⊴ₓ = (x ≫ (<) ≫ x°) ∪ ((x ≫ x°) ∩ (≤))`: positions by `x` under `lt`, ties by position; `⊵ₓ` is
    this at `>`. -/
def stable (x : Idx ⟶ B) (lt : B ⟶ B) : Idx ⟶ Idx := (x ≫ lt ≫ x°) ∪ ((x ≫ x°) ∩ fun i j => i ≤ j)

end Derived

/-- `sort(⊴) = perm ≫ ordered(⊴)` (B&dM 6.6). -/
def sort {A : Type} (R : A → A → Prop) : dList A ⟶ dList A := perm ≫ ordered R

/-- `enum = setify° ≫ sort(<)`, a primitive: a set of positions as the list in position order. The order is
    the strict `<`, because `setify°` takes a set to lists with repeats too, which `≤` would keep. -/
def enum := (setify (A := Nat))° ≫ sort (· < ·)

/-! ## `enum` -/

theorem inlistP_ofList {A : Type} (a : A) : ∀ xs : List A, inlistP (CL.ofList xs) a ↔ a ∈ xs
  | [] => by simp [CL.ofList, inlistP]
  | b :: xs => by rw [CL.ofList_cons, List.mem_cons, ← inlistP_ofList a xs]; rfl

theorem orderedP_ofList {A : Type} (R : A → A → Prop) : ∀ xs : List A, orderedP R (CL.ofList xs) ↔ xs.Pairwise R
  | [] => by simp [CL.ofList, orderedP]
  | b :: xs => by
    rw [CL.ofList_cons, List.pairwise_cons, ← orderedP_ofList R xs]
    show ((∀ x, inlistP (CL.ofList xs) x → R b x) ∧ _) ↔ _
    simp only [inlistP_ofList]

theorem ofList_toList {A : Type} : ∀ ys : CL.ConsList Unit A, CL.ofList (CL.toList ys) = ys
  | .wrap () => rfl
  | .cons a ys => by rw [show CL.toList (.cons a ys) = a :: CL.toList ys from rfl, CL.ofList_cons, ofList_toList ys]

theorem perm_inlistP {A : Type} {x y : CL.ConsList Unit A} (h : Perm x y) (a : A) : inlistP x a ↔ inlistP y a := by
  induction h with
  | nil => exact Iff.rfl
  | cons b _ ih => exact or_congr Iff.rfl ih
  | swap b c z => show (a = b ∨ a = c ∨ _) ↔ (a = c ∨ a = b ∨ _); exact ⟨fun | .inl h => .inr (.inl h) | .inr (.inl h) => .inl h | .inr (.inr h) => .inr (.inr h), fun | .inl h => .inr (.inl h) | .inr (.inl h) => .inl h | .inr (.inr h) => .inr (.inr h)⟩
  | trans _ _ i1 i2 => exact i1.trans i2

/-- Two strictly ascending lists with the same members are one list. -/
theorem eq_of_pairwise_lt : ∀ {xs ys : List Nat}, xs.Pairwise (· < ·) → ys.Pairwise (· < ·) →
    (∀ a, a ∈ xs ↔ a ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) List.not_mem_nil
  | a :: xs, b :: ys, hx, hy, h => by
    rw [List.pairwise_cons] at hx hy
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | m
      · exact e
      rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | m'
      · exact e.symm
      have := hy.1 a m; have := hx.1 b m'; omega
    subst hab
    rw [eq_of_pairwise_lt hx.2 hy.2 fun c => ⟨fun m => ?_, fun m => ?_⟩]
    · have := hx.1 c m; rcases List.mem_cons.1 ((h c).1 (List.mem_cons_of_mem _ m)) with e | m'
      · omega
      · exact m'
    · have := hy.1 c m; rcases List.mem_cons.1 ((h c).2 (List.mem_cons_of_mem _ m)) with e | m'
      · omega
      · exact m'

/-- `enum` relates a set to exactly the strictly ascending lists of its members. -/
theorem enum_iff (S) (ys : CL.ConsList Unit Nat) :
    enum S ys ↔ S = inlistP ys ∧ orderedP (· < ·) ys := by
  constructor
  · rintro ⟨xs, (hS : S = inlistP xs), zs, hp, rfl, ho⟩
    exact ⟨hS.trans (funext fun a => propext (perm_inlistP hp a)), ho⟩
  · rintro ⟨hS, ho⟩
    exact ⟨ys, hS, ys, Perm.refl ys, rfl, ho⟩

/-- `enum` executed: the coreflexive given as a bit column `x` (its set `{i ∣ x.rel i 1b}`) enumerates as
    `Find.where x`, the `whereBits` positions, read as naturals. -/
theorem enum_where {nx m : Nat} {x : Arr .boolean nx} {r : Arr .long m} (hn : nx < USize.size)
    (h : Find.where x = .ok ⟨m, r⟩) :
    ∃ L : List Nat, r.toList = L.map Int64.ofNat ∧ ∀ ys, enum (fun i => x.rel i true) ys ↔ ys = CL.ofList L := by
  let L := (List.range x.toList.length).filter fun j => x.toList.getD j false
  have mem : ∀ i, i ∈ L ↔ x.rel i true := fun i => by
    show _ ↔ x.toList[i]? = some true
    simp only [L, List.mem_filter, List.mem_range, List.getD_eq_getElem?_getD]
    constructor
    · rintro ⟨hi, e⟩; rw [List.getElem?_eq_getElem hi] at e ⊢; simpa using e
    · intro e; have hi : i < x.toList.length := (List.getElem?_eq_some_iff.1 e).1; exact ⟨hi, by rw [e]; rfl⟩
  have pw : L.Pairwise (· < ·) := (List.pairwise_lt_range ..).filter _
  refine ⟨L, Find.where_toList hn h, fun ys => ?_⟩
  rw [enum_iff]
  constructor
  · rintro ⟨hS, ho⟩
    rw [← ofList_toList ys, orderedP_ofList] at ho
    rw [← ofList_toList ys]
    refine congrArg CL.ofList (eq_of_pairwise_lt ho pw fun a => ?_)
    rw [mem, ← inlistP_ofList, ofList_toList, ← hS]
  · rintro rfl
    exact ⟨funext fun i => propext ((mem i).symm.trans (inlistP_ofList i L).symm), (orderedP_ofList _ L).2 pw⟩

/-! ## The List specs read as expressions -/

section Lists

variable {α : Type}

theorem ix_map {β : Type} (f : α → β) (xs : List α) : ix (xs.map f) = ix xs ≫ graph f :=
  hom_ext fun j b => by
    show (xs.map f)[j]? = some b ↔ ∃ a, xs[j]? = some a ∧ b = f a
    rw [List.getElem?_map]; cases xs[j]? <;> simp [eq_comm]

theorem ix_takeSpec [Inhabited α] (k : Int) (xs : List α) (h : 0 < xs.length) :
    ix (Struct.takeSpec k xs) = take k xs.length ≫ ix xs :=
  hom_ext fun j a => by
    show (Struct.takeSpec k xs)[j]? = some a ↔ ∃ i, (∃ z, (j = z ∧ j < k.natAbs) ∧ i = (Kernel.takeFrom k xs.length + z) % xs.length) ∧ xs[i]? = some a
    have hm : (Kernel.takeFrom k xs.length + j) % xs.length < xs.length := Nat.mod_lt _ h
    simp only [Struct.takeSpec, List.getElem?_map, List.getElem?_range]
    by_cases hj : j < k.natAbs
    · simp [hj, getElem!_pos, hm, List.getElem?_eq_getElem hm]
    · simp [hj]

theorem ix_dropSpec (k : Int) (xs : List α) : ix (Struct.dropSpec k xs) = drop k xs.length ≫ ix xs :=
  hom_ext fun j a => by
    show (Struct.dropSpec k xs)[j]? = some a ↔ ∃ i, (∃ z, (j = z ∧ j < xs.length - k.natAbs) ∧ i = z + k.toNat) ∧ xs[i]? = some a
    simp only [Struct.dropSpec]
    split
    · rw [List.getElem?_drop]
      constructor
      · intro e; have := (List.getElem?_eq_some_iff.1 e).1
        exact ⟨j + k.toNat, ⟨j, ⟨rfl, by omega⟩, rfl⟩, by rw [show j + k.toNat = k.toNat + j by omega]; exact e⟩
      · rintro ⟨_, ⟨_, ⟨rfl, _⟩, rfl⟩, e⟩; rw [show k.toNat + j = j + k.toNat by omega]; exact e
    · rw [List.getElem?_take]
      constructor
      · intro e; split at e
        · exact ⟨j, ⟨j, ⟨rfl, by omega⟩, by omega⟩, e⟩
        · cases e
      · rintro ⟨_, ⟨_, ⟨rfl, hj⟩, rfl⟩, e⟩; rw [if_pos hj]; rwa [show j + k.toNat = j by omega] at e

theorem ix_reverse (xs : List α) : ix xs.reverse = rev xs.length ≫ ix xs :=
  hom_ext fun j a => by
    show xs.reverse[j]? = some a ↔ ∃ i, (∃ z, (j = z ∧ j < xs.length) ∧ i = xs.length - 1 - z) ∧ xs[i]? = some a
    by_cases hj : j < xs.length
    · rw [List.getElem?_reverse hj]; exact ⟨fun e => ⟨_, ⟨j, ⟨rfl, hj⟩, rfl⟩, e⟩, fun ⟨_, ⟨_, ⟨rfl, _⟩, rfl⟩, e⟩ => e⟩
    · have hl : xs.reverse.length ≤ j := by rw [List.length_reverse]; omega
      rw [List.getElem?_eq_none hl]
      exact ⟨fun e => by cases e, fun ⟨_, ⟨_, ⟨_, h⟩, _⟩, _⟩ => absurd h hj⟩

/-- Element `j` of `xs` rotated left by `s < |xs|` is element `(j+s) mod |xs|`. -/
theorem getElem?_rotateLeft (xs : List α) {s j : Nat} (hs : s < xs.length) (hj : j < xs.length) :
    (xs.rotateLeft s)[j]? = xs[(j + s) % xs.length]? := by
  simp only [List.rotateLeft]
  split
  · have h1 : xs.length = 1 := by omega
    rw [h1, Nat.mod_one, show j = 0 by omega]
  · rw [Nat.mod_eq_of_lt hs]
    have hd : (xs.drop s).length = xs.length - s := List.length_drop ..
    by_cases h2 : j < xs.length - s
    · have h3 : j < (xs.drop s).length := by omega
      rw [List.getElem?_append_left h3, List.getElem?_drop, Nat.mod_eq_of_lt (show j + s < xs.length by omega), Nat.add_comm]
    · have h3 : (xs.drop s).length ≤ j := by omega
      have h4 : j - (xs.drop s).length < s := by omega
      have h5 : (j + s) % xs.length = j + s - xs.length := by
        rw [Nat.mod_eq_sub_mod (show xs.length ≤ j + s by omega), Nat.mod_eq_of_lt (show j + s - xs.length < xs.length by omega)]
      rw [List.getElem?_append_right h3, List.getElem?_take, if_pos h4, hd, h5]
      congr 1; omega

theorem ix_rotateSpec (k : Int) (xs : List α) : ix (Struct.rotateSpec k xs) = rot k xs.length ≫ ix xs :=
  hom_ext fun j a => by
    show (Struct.rotateSpec k xs)[j]? = some a ↔ ∃ i, (∃ z, (j = z ∧ j < xs.length) ∧ i = (z +(k.emod xs.length).toNat) % xs.length) ∧ xs[i]? = some a
    simp only [Struct.rotateSpec]
    split
    · rename_i he; simp at he; subst he; simp
    · rename_i he
      have h0 : 0 < xs.length := by cases xs <;> simp_all
      have e1 : k.emod xs.length < xs.length := Int.emod_lt_of_pos k (by omega)
      have e2 : 0 ≤ k.emod xs.length := Int.emod_nonneg k (by omega)
      have hs : (k.emod xs.length).toNat < xs.length := by omega
      by_cases hj : j < xs.length
      · rw [getElem?_rotateLeft xs hs hj]
        exact ⟨fun e => ⟨_, ⟨j, ⟨rfl, hj⟩, rfl⟩, e⟩, fun ⟨_, ⟨_, ⟨rfl, _⟩, rfl⟩, e⟩ => e⟩
      · have hl : (xs.rotateLeft (k.emod xs.length).toNat).length ≤ j := by rw [List.length_rotateLeft]; omega
        rw [List.getElem?_eq_none hl]
        exact ⟨fun e => by cases e, fun ⟨_, ⟨_, ⟨_, h⟩, _⟩, _⟩ => absurd h hj⟩

/-- `miss` pointwise: `R`, or `e` where `R` holds nothing. -/
theorem miss_iff {A B : RelSet.{0}} (R : A ⟶ B) (e : B.carrier) (i : A.carrier) (b : B.carrier) :
    miss R e i b ↔ R i b ∨ ((¬ ∃ c, R i c) ∧ b = e) := by
  show R i b ∨ (∃ w, (i = w ∧ ∀ v, (v = i ∧ ∃ c, R v c ∧ R i c) → False) ∧ b = e) ↔ _
  exact or_congr Iff.rfl ⟨fun ⟨_, ⟨_, hn⟩, he⟩ => ⟨fun ⟨c, hc⟩ => hn i ⟨rfl, c, hc, hc⟩, he⟩,
    fun ⟨hn, he⟩ => ⟨i, ⟨rfl, fun _ ⟨_, c, _, hc⟩ => hn ⟨c, hc⟩⟩, he⟩⟩

theorem ix_indexSpec (d : α) (xs : List α) (is : List Int64) :
    ix (Struct.indexSpec d xs is) = ix is ≫ miss (pos ≫ ix xs) d :=
  hom_ext fun j a => by
    show (Struct.indexSpec d xs is)[j]? = some a ↔ ∃ i, is[j]? = some i ∧ miss (pos ≫ ix xs) d i a
    simp only [Struct.indexSpec, List.getElem?_map, miss_iff]
    have hp : ∀ (i : Int64) c, (pos ≫ ix xs) i c ↔ 0 ≤ i ∧ xs[i.toInt.toNat]? = some c := fun i c =>
      ⟨fun ⟨_, ⟨_, ⟨rfl, h⟩, rfl⟩, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨_, ⟨i, ⟨rfl, h⟩, rfl⟩, e⟩⟩
    cases is[j]? with
    | none => simp
    | some i =>
      simp only [hp, Option.map_some, Option.some.injEq, exists_eq_left']
      by_cases h0 : 0 ≤ i
      · simp only [h0, if_true, true_and, List.getD_eq_getElem?_getD]
        cases xs[i.toInt.toNat]? <;> simp [eq_comm]
      · simp [h0, eq_comm]

end Lists

/-! ## The first batch of laws: the 8 verbs whose List spec already is the expression -/

/-- `~x = x ≫ not`. -/
theorem not_rel {x r : Arr .boolean n} (hn : n < USize.size) (h : Ew.not x = .ok r) :
    r.rel = x.rel ≫ graph (fun b => !b) :=
  calc r.rel = ix (x.toList.map fun b => !b) := congrArg ix (Ew.not_spec hn h)
    _ = x.rel ≫ graph (fun b => !b) := ix_map ..

/-- `n#x = take(n) ≫ x`. -/
theorem take_rel {k : Int} {x : Arr .long n} {r : Arr .long k.natAbs} (hw : Struct.Words x.c) (h0 : 0 < n)
    (h : Struct.take k x = .ok r) : r.rel = take k n ≫ x.rel :=
  calc r.rel = ix (Struct.takeSpec k x.toList) := congrArg ix (Struct.take_toList hw h0 h)
    _ = take k x.toList.length ≫ x.rel := ix_takeSpec k _ (by rw [Arr.length_toList]; exact h0)
    _ = take k n ≫ x.rel := by rw [Arr.length_toList]

/-- `n_x = drop(n) ≫ x`. -/
theorem drop_rel {k : Int} {x : Arr .long n} {r : Arr .long (n - k.natAbs)} {b : ByteArray} (hc : x.c.enc = .bytes b)
    (h : Struct.drop k x = .ok r) : r.rel = drop k n ≫ x.rel :=
  calc r.rel = ix (Struct.dropSpec k x.toList) := congrArg ix (Struct.drop_toList hc h)
    _ = drop k x.toList.length ≫ x.rel := ix_dropSpec ..
    _ = drop k n ≫ x.rel := by rw [Arr.length_toList]

/-- `n rotate x = rot(n) ≫ x`. -/
theorem rotate_rel {k : Int} {x r : Arr .long n} (hw : Struct.Words x.c) (h : Struct.rotate k x = .ok r) :
    r.rel = rot k n ≫ x.rel :=
  calc r.rel = ix (Struct.rotateSpec k x.toList) := congrArg ix (Struct.rotate_toList hw h)
    _ = rot k x.toList.length ≫ x.rel := ix_rotateSpec ..
    _ = rot k n ≫ x.rel := by rw [Arr.length_toList]

/-- `|x = rev ≫ x`. -/
theorem reverse_rel {x r : Arr .long n} {b : ByteArray} (hc : x.c.enc = .bytes b) (h : Struct.reverse x = .ok r) :
    r.rel = rev n ≫ x.rel :=
  calc r.rel = ix x.toList.reverse := congrArg ix (Struct.reverse_toList hc h)
    _ = rev x.toList.length ≫ x.rel := ix_reverse _
    _ = rev n ≫ x.rel := by rw [Arr.length_toList]

/-- `x@y = y ≫ miss(pos ≫ x, 0N)`. -/
theorem index_rel {nx ny : Nat} {x : Arr .long nx} {y r : Arr .long ny} {xs ws : List UInt64}
    (hx : longWords x.c = some xs) (hy : longWords y.c = some ws) (hnx : nx < USize.size) (hny : ny < USize.size)
    (h63 : nx < 2 ^ 63) (h : Struct.index x y = .ok r) : r.rel = y.rel ≫ miss (pos ≫ x.rel) Int64.minValue :=
  calc r.rel = ix (Struct.indexSpec Int64.minValue x.toList y.toList) :=
        congrArg ix (Struct.index_toList hx hy hnx hny h63 h)
    _ = y.rel ≫ miss (pos ≫ x.rel) Int64.minValue := ix_indexSpec ..

/-- `x!y = x° ≫ y`: a dict's `Holds` is the tabulation of its two columns. -/
theorem mk_rel {k v : QAtomicType} (x : Arr k n) (y : Arr v n) :
    ((⟨n, x, y⟩ : Rel k v).Holds : (⟨El k⟩ : RelSet.{0}) ⟶ ⟨El v⟩) = x.rel° ≫ y.rel :=
  hom_ext fun a b => by
    show (∃ i, x.get i = a ∧ y.get i = b) ↔ ∃ j, x.rel j a ∧ y.rel j b
    simp only [rel_iff]
    exact ⟨fun ⟨i, ha, hb⟩ => ⟨i, ⟨i.2, ha⟩, ⟨i.2, hb⟩⟩, fun ⟨j, ⟨h, ha⟩, ⟨_, hb⟩⟩ => ⟨⟨j, h⟩, ha, hb⟩⟩

/-- `#x = length(x)`, the fold `⦇0, succ⦈` (`ListRel.length_cata`): by the type, nothing runs. -/
theorem count_rel (x : Arr t n) : (ListRel.length : dList (El t) ⟶ (⟨Nat⟩ : RelSet.{0})) (CL.ofList x.toList) n := by
  show n = ListRel.clen (CL.ofList x.toList)
  suffices ∀ xs : List (El t), ListRel.clen (CL.ofList xs) = xs.length by rw [this, Arr.length_toList]
  intro xs; induction xs with
  | nil => rfl
  | cons a xs ih => rw [CL.ofList_cons, List.length_cons, ← ih]; rfl

#print axioms enum_where
#print axioms not_rel
#print axioms take_rel
#print axioms drop_rel
#print axioms rotate_rel
#print axioms reverse_rel
#print axioms index_rel
#print axioms mk_rel
#print axioms count_rel

end LeetQ.Rel.Verb
