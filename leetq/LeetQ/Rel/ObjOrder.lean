/-
  q's `asc` order on every side `A : Obj`: the order qlean's sort kernels implement (`c/sort.c`,
  `QLean/Kernel/Sort.lean`), lifted from atoms to products, arrays and sums.
-/
import LeetQ.Run.Core

namespace LeetQ.Rel

open QLean QLean.Dep QLean.Kernel

/-- The key of an element, a list of naturals compared lexicographically (`Obj.lt`). At an atom it is
    the key qlean's grade sorts by (`Order.rank` of the raw bits, `QLean/Kernel/Sort.lean`): a number by
    its value with every null and NaN lowest and equal, `±0.0` equal; `byte`/`char` unsigned; a symbol by
    its unsigned bytes, a prefix before what extends it; a guid by its sixteen bytes. Each key is
    self-delimiting (`Obj.key_prefix`), so a pair's key is its components' keys side by side and orders
    them lexicographically; an array's elements each follow a `1` and the array ends in `0`, so a proper
    prefix sorts first; a sum's tag leads, `inl` before `inr`. A general atom has no kernel order
    (`orderKind .general = none`) and keys as `[]`: all general atoms tie. -/
def Obj.key : (A : Obj) → A.El → List Nat
  | .atom .boolean, x => [if (x : Bool) then 1 else 0]
  | .atom .byte, x | .atom .char, x => [(x : UInt8).toNat]
  | .atom .short, x => [(Order.rank .i16 (x : Int16).toUInt16.toUInt64).toNat]
  | .atom .int, x | .atom .month, x | .atom .date, x | .atom .minute, x | .atom .second, x
  | .atom .time, x => [(Order.rank .i32 (x : Int32).toUInt32.toUInt64).toNat]
  | .atom .long, x | .atom .timestamp, x | .atom .timespan, x =>
    [(Order.rank .i64 (x : Int64).toUInt64).toNat]
  | .atom .real, x => [(Order.rank .f32 (x : UInt32).toUInt64).toNat]
  | .atom .float, x | .atom .datetime, x => [(Order.rank .f64 (x : UInt64)).toNat]
  | .atom .symbol, x => (x : String).toUTF8.data.toList.map (·.toNat + 1) ++ [0]
  | .atom .guid, x => (x : Guid).toList.map (·.toNat)
  | .atom .general, _ => []
  | .prod a b, (x, y) => a.key x ++ b.key y
  | .arr b, xs => (xs : List b.El).foldr (fun x k => 1 :: b.key x ++ k) [0]
  | .sum a _, .inl x => 0 :: a.key x
  | .sum _ b, .inr y => 1 :: b.key y

/-- q's `asc` order on `A`: `x` before `y`, the lexicographic order of their keys (`Obj.key`). -/
def Obj.lt (A : Obj) (x y : A.El) : Prop := A.key x < A.key y

instance (A : Obj) (x y : A.El) : Decidable (A.lt x y) := inferInstanceAs (Decidable (A.key x < A.key y))

theorem Obj.lt_irrefl (A : Obj) (x : A.El) : ¬ A.lt x x := List.lt_irrefl _

theorem Obj.lt_trans (A : Obj) {x y z : A.El} : A.lt x y → A.lt y z → A.lt x z := List.lt_trans

theorem Obj.lt_asymm (A : Obj) {x y : A.El} : A.lt x y → ¬ A.lt y x := List.lt_asymm

/-- **Trichotomy**: two elements are ordered one way, the other, or have one key — q's `~`, which merges
    every NaN and both zeros of a float. -/
theorem Obj.lt_trichotomy (A : Obj) (x y : A.El) : A.lt x y ∨ A.key x = A.key y ∨ A.lt y x := by
  unfold Obj.lt
  generalize A.key x = a; generalize A.key y = b
  induction a generalizing b with
  | nil => cases b with
    | nil => exact .inr (.inl rfl)
    | cons v b => exact .inl (List.nil_lt_cons v b)
  | cons u a ih => cases b with
    | nil => exact .inr (.inr (List.nil_lt_cons u a))
    | cons v b =>
      simp only [List.cons_lt_cons_iff, List.cons.injEq]
      rcases Nat.lt_trichotomy u v with h | rfl | h
      · exact .inl (.inl h)
      · rcases ih b with h | h | h
        · exact .inl (.inr ⟨rfl, h⟩)
        · exact .inr (.inl ⟨rfl, h⟩)
        · exact .inr (.inr (.inr ⟨rfl, h⟩))
      · exact .inr (.inr (.inl h))

/-- Two lists of no `0` each, ended by `0`: one key extending the other is the same key. -/
theorem key_term {l m r s : List Nat} (hl : ∀ a ∈ l, a ≠ 0) (hm : ∀ a ∈ m, a ≠ 0)
    (h : l ++ [0] ++ r = m ++ [0] ++ s) : l = m := by
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons b m => simp at h; exact absurd h.1.symm (hm b (by simp))
  | cons a l ih => cases m with
    | nil => simp at h; exact absurd h.1 (hl a (by simp))
    | cons b m =>
      simp only [List.cons_append, List.cons.injEq] at h
      rw [h.1, ih (fun x hx => hl x (by simp [hx])) (fun x hx => hm x (by simp [hx])) h.2]

/-- **Keys are self-delimiting**: a key that a key extends is that key. -/
theorem Obj.key_prefix : (A : Obj) → (x y : A.El) → (r s : List Nat) →
    A.key x ++ r = A.key y ++ s → A.key x = A.key y
  | .atom t, x, y, r, s, h => by
    cases t
    case symbol =>
      simp only [Obj.key, List.append_assoc] at h ⊢
      have := key_term (l := (x : String).toUTF8.data.toList.map (·.toNat + 1))
        (m := (y : String).toUTF8.data.toList.map (·.toNat + 1)) (by simp) (by simp)
        (by simpa only [List.append_assoc] using h)
      rw [this]
    case guid => exact (List.append_inj h (by simp [Obj.key])).1
    all_goals exact (List.append_inj h (by simp [Obj.key])).1
  | .prod a b, (x, y), (x', y'), r, s, h => by
    simp only [Obj.key, List.append_assoc] at h ⊢
    have e := Obj.key_prefix a x x' _ _ h
    rw [e, List.append_cancel_left_eq] at h
    rw [e, Obj.key_prefix b y y' _ _ h]
  | .arr b, xs, ys, r, s, h => by
    induction (xs : List b.El) generalizing ys with
    | nil => cases (ys : List b.El) with
      | nil => rfl
      | cons y ys => simp [Obj.key] at h
    | cons x xs ih => cases (ys : List b.El) with
      | nil => simp [Obj.key] at h
      | cons y ys =>
        simp only [Obj.key, List.foldr_cons, List.cons_append, List.cons.injEq, true_and,
          List.append_assoc] at h ⊢
        have e := Obj.key_prefix b x y _ _ h
        rw [e, List.append_cancel_left_eq] at h
        rw [e]; exact congrArg (b.key y ++ ·) (ih ys h)
  | .sum a b, .inl x, .inl y, r, s, h => by
    simp only [Obj.key, List.cons_append, List.cons.injEq, true_and] at h ⊢; exact Obj.key_prefix a x y _ _ h
  | .sum a b, .inr x, .inr y, r, s, h => by
    simp only [Obj.key, List.cons_append, List.cons.injEq, true_and] at h ⊢; exact Obj.key_prefix b x y _ _ h
  | .sum _ _, .inl _, .inr _, _, _, h => by simp [Obj.key] at h
  | .sum _ _, .inr _, .inl _, _, _, h => by simp [Obj.key] at h

/-- A common prefix does not change the order. -/
theorem lt_append_left_iff (l : List Nat) {a b : List Nat} : l ++ a < l ++ b ↔ a < b := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, List.cons_lt_cons_iff, Nat.lt_irrefl, false_or, true_and, ih]

/-- Two different keys of `A`, each extended: ordered as the keys are. -/
theorem Obj.lt_append_iff (A : Obj) {x y : A.El} (ne : A.key x ≠ A.key y) (r s : List Nat) :
    A.key x ++ r < A.key y ++ s ↔ A.lt x y := by
  have hp := Obj.key_prefix A x y
  unfold Obj.lt
  generalize A.key x = a at ne hp; generalize A.key y = b at ne hp
  induction a generalizing b with
  | nil => exact absurd (hp b [] (by simp)) ne
  | cons u a ih => cases b with
    | nil => exact absurd (hp [] (u :: a) (by simp)) ne
    | cons v b =>
      simp only [List.cons_append, List.cons_lt_cons_iff]
      by_cases e : u = v
      · subst e
        have ne' : a ≠ b := fun h => ne (by rw [h])
        have hp' : ∀ r s, a ++ r = b ++ s → a = b := fun r s h => by
          have := hp r s (by simp [h]); simpa using this
        simp only [Nat.lt_irrefl, true_and, false_or, ih b ne' hp']
      · simp [e]

/-- **A pair**: by its first component, then on a tie of keys by its second. -/
theorem Obj.lt_prod (a b : Obj) (x x' : a.El) (y y' : b.El) :
    (Obj.prod a b).lt (x, y) (x', y') ↔ a.lt x x' ∨ a.key x = a.key x' ∧ b.lt y y' := by
  show a.key x ++ b.key y < a.key x' ++ b.key y' ↔ _
  by_cases e : a.key x = a.key x'
  · rw [e, lt_append_left_iff]
    exact ⟨fun h => .inr ⟨rfl, h⟩, fun h => h.elim (fun h => by rw [Obj.lt, e] at h; exact absurd h (List.lt_irrefl _)) (·.2)⟩
  · rw [a.lt_append_iff e]; exact ⟨.inl, fun h => h.elim id fun h => absurd h.1 e⟩

/-- **A sum**: `inl` before `inr`, each side by its own order. -/
theorem Obj.lt_inl_inr (a b : Obj) (x : a.El) (y : b.El) : (Obj.sum a b).lt (.inl x) (.inr y) :=
  List.cons_lt_cons_iff.2 (.inl Nat.zero_lt_one)

theorem Obj.not_lt_inr_inl (a b : Obj) (x : a.El) (y : b.El) : ¬ (Obj.sum a b).lt (.inr y) (.inl x) := by
  show ¬ (1 :: b.key y < 0 :: a.key x); simp [List.cons_lt_cons_iff]

theorem Obj.lt_inl (a b : Obj) (x y : a.El) : (Obj.sum a b).lt (.inl x) (.inl y) ↔ a.lt x y := by
  show 0 :: a.key x < 0 :: a.key y ↔ _; simp [Obj.lt]

theorem Obj.lt_inr (a b : Obj) (x y : b.El) : (Obj.sum a b).lt (.inr x) (.inr y) ↔ b.lt x y := by
  show 1 :: b.key x < 1 :: b.key y ↔ _; simp [Obj.lt]

/-- **An array**, lexicographically: the empty array first, a proper prefix before what extends it. -/
theorem Obj.lt_nil_cons (b : Obj) (y : b.El) (ys : List b.El) : (Obj.arr b).lt ([] : List b.El) (y :: ys) :=
  List.cons_lt_cons_iff.2 (.inl Nat.zero_lt_one)

theorem Obj.not_lt_nil (b : Obj) (xs : List b.El) : ¬ (Obj.arr b).lt xs ([] : List b.El) := by
  show ¬ (xs.foldr (fun x k => 1 :: b.key x ++ k) [0] < [0])
  cases xs <;> simp [List.cons_lt_cons_iff]

theorem Obj.lt_cons (b : Obj) (x y : b.El) (xs ys : List b.El) :
    (Obj.arr b).lt (x :: xs) (y :: ys) ↔ b.lt x y ∨ b.key x = b.key y ∧ (Obj.arr b).lt xs ys := by
  show 1 :: (b.key x ++ _) < 1 :: (b.key y ++ _) ↔ _
  simp only [List.cons_lt_cons_iff, Nat.lt_irrefl, false_or, true_and]
  by_cases e : b.key x = b.key y
  · rw [e, lt_append_left_iff]
    exact ⟨fun h => .inr ⟨rfl, h⟩, fun h => h.elim (fun h => by rw [Obj.lt, e] at h; exact absurd h (List.lt_irrefl _)) (·.2)⟩
  · rw [b.lt_append_iff e]; exact ⟨.inl, fun h => h.elim id fun h => absurd h.1 e⟩

#guard (Obj.arr .long).key ([] : List Int64) < (Obj.arr .long).key ([1] : List Int64)
#guard (Obj.arr .long).key ([1] : List Int64) < (Obj.arr .long).key ([1, 0] : List Int64)
#guard (Obj.atom .long).key (-1 : Int64) < (Obj.atom .long).key (0 : Int64)
#guard (Obj.atom .symbol).key "a" < (Obj.atom .symbol).key "aa"
#guard (Obj.atom .symbol).key "aa" < (Obj.atom .symbol).key "ab"

#print axioms Obj.lt_trichotomy
#print axioms Obj.lt_prod
#print axioms Obj.lt_cons

end LeetQ.Rel
