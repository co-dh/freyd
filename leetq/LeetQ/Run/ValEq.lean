/-
  Equality of general-list elements as Rel reads it: `=` on `QValue`, decided structurally. `QValue` has no
  `DecidableEq`: an attribute (`vector`, `slices`) and a keyed table hold an `IndexCell`, an opaque type with
  no equality. `valEq` compares everything but those cells; it is reflexive everywhere and is `=` on a value
  that holds no cell (`cellFree`).
-/
import QLean.Value

namespace LeetQ.Rel

open QLean

deriving instance DecidableEq for QAtom

mutual

/-- `a = b` but for the index cells, which no equality reads: the attribute's code is compared, its cell not. -/
def valEq : QValue → QValue → Bool
  | .atom a, .atom b => decide (a = b)
  | .vector t n e a, .vector t' n' e' a' =>
    decide (t = t') && decide (n = n') && encEq e e' && decide (a.map (·.1) = a'.map (·.1))
  | .dict k v s, .dict k' v' s' => valEq k k' && valEq v v' && decide (s = s')
  | .table x, .table y => tabEq x y
  | .keyed k v s, .keyed k' v' s' => tabEq k k' && tabEq v v' && decide (s = s')
  | .slices t n e a o, .slices t' n' e' a' o' =>
    decide (t = t') && decide (n = n') && encEq e e' && decide (a.map (·.1) = a'.map (·.1)) && decide (o = o')
  | .func i ⟨xs⟩, .func j ⟨ys⟩ => decide (i = j) && listEq xs ys
  | .err s, .err s' => decide (s = s')
  | .enum s v, .enum s' v' => decide (s = s') && valEq v v'
  | _, _ => false

/-- `valEq` element by element, of one length. -/
def listEq : List QValue → List QValue → Bool
  | [], [] => true
  | x :: xs, y :: ys => valEq x y && listEq xs ys
  | _, _ => false

/-- `valEq` on tables: names, columns, attribute byte. -/
def tabEq : QTable → QTable → Bool
  | .mk c ⟨v⟩ a, .mk c' ⟨v'⟩ a' => decide (c = c') && listEq v v' && decide (a = a')

/-- `valEq` on payloads: one constructor, equal fields. -/
def encEq : Enc → Enc → Bool
  | .bytes b, .bytes b' | .bits b, .bits b' => decide (b = b')
  | .syms b o, .syms b' o' => decide (b = b') && decide (o = o')
  | .foR m p, .foR m' p' => decide (m = m') && decide (p = p')
  | .alp m p x, .alp m' p' x' => decide (m = m') && decide (p = p') && decide (x = x')
  | .enum d o i, .enum d' o' i' => decide (d = d') && decide (o = o') && decide (i = i')
  | .gen ⟨xs⟩, .gen ⟨ys⟩ => listEq xs ys
  | _, _ => false

end

mutual

/-- No `IndexCell` anywhere in the value: no attribute, no keyed table. -/
def cellFree : QValue → Bool
  | .atom _ | .err _ => true
  | .vector _ _ e a | .slices _ _ e a _ => a.isNone && encCellFree e
  | .dict k v _ => cellFree k && cellFree v
  | .table x => tabCellFree x
  | .keyed .. => false
  | .func _ ⟨xs⟩ => listCellFree xs
  | .enum _ v => cellFree v

def listCellFree : List QValue → Bool
  | [] => true
  | x :: xs => cellFree x && listCellFree xs

def tabCellFree : QTable → Bool
  | .mk _ ⟨v⟩ _ => listCellFree v

def encCellFree : Enc → Bool
  | .gen ⟨xs⟩ => listCellFree xs
  | _ => true

end

mutual

theorem valEq_refl : (a : QValue) → valEq a a = true
  | .atom _ | .err _ => by simp [valEq]
  | .vector _ _ e _ => by simp [valEq, encEq_refl e]
  | .slices _ _ e _ _ => by simp [valEq, encEq_refl e]
  | .dict k v _ => by simp [valEq, valEq_refl k, valEq_refl v]
  | .table x => by simp [valEq, tabEq_refl x]
  | .keyed k v _ => by simp [valEq, tabEq_refl k, tabEq_refl v]
  | .func _ ⟨xs⟩ => by simp [valEq, listEq_refl xs]
  | .enum _ v => by simp [valEq, valEq_refl v]

theorem listEq_refl : (l : List QValue) → listEq l l = true
  | [] => by simp [listEq]
  | x :: xs => by simp [listEq, valEq_refl x, listEq_refl xs]

theorem tabEq_refl : (x : QTable) → tabEq x x = true
  | .mk _ ⟨v⟩ _ => by simp [tabEq, listEq_refl v]

theorem encEq_refl : (e : Enc) → encEq e e = true
  | .bytes _ | .bits _ | .syms .. | .foR .. | .alp .. | .enum .. => by simp [encEq]
  | .gen ⟨xs⟩ => by simp [encEq, listEq_refl xs]

end

mutual

theorem valEq_sound : (a b : QValue) → cellFree a = true → valEq a b = true → a = b
  | .atom _, b, _, h | .err _, b, _, h => by cases b <;> simp_all [valEq]
  | .vector _ _ e a, b, hc, h => by
    cases b <;> simp only [valEq, Bool.false_eq_true] at h
    simp only [cellFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, he⟩, ha⟩ := h
    obtain ⟨rfl, hce⟩ := hc
    rw [encEq_sound e _ hce he, (Option.map_eq_none_iff.1 ha.symm)]
  | .slices _ _ e a _, b, hc, h => by
    cases b <;> simp only [valEq, Bool.false_eq_true] at h
    simp only [cellFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, he⟩, ha⟩, rfl⟩ := h
    obtain ⟨rfl, hce⟩ := hc
    rw [encEq_sound e _ hce he, (Option.map_eq_none_iff.1 ha.symm)]
  | .dict k v _, b, hc, h => by
    cases b <;> simp only [valEq, Bool.false_eq_true] at h
    simp only [cellFree, Bool.and_eq_true] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, hv⟩, rfl⟩ := h
    rw [valEq_sound k _ hc.1 hk, valEq_sound v _ hc.2 hv]
  | .table x, b, hc, h => by
    cases b <;> simp only [valEq, Bool.false_eq_true] at h
    simp only [cellFree] at hc
    rw [tabEq_sound x _ hc h]
  | .keyed .., _, hc, _ => by simp [cellFree] at hc
  | .func _ ⟨xs⟩, b, hc, h => by
    cases b with
    | func j ys =>
      obtain ⟨ys⟩ := ys
      simp only [valEq, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [cellFree] at hc
      obtain ⟨rfl, hl⟩ := h
      rw [listEq_sound xs ys hc hl]
    | _ => simp [valEq] at h
  | .enum _ v, b, hc, h => by
    cases b <;> simp only [valEq, Bool.false_eq_true] at h
    simp only [cellFree] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hv⟩ := h
    rw [valEq_sound v _ hc hv]

theorem listEq_sound : (l m : List QValue) → listCellFree l = true → listEq l m = true → l = m
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [listEq] at h
  | _ :: _, [], _, h => by simp [listEq] at h
  | x :: xs, y :: ys, hc, h => by
    simp only [listCellFree, Bool.and_eq_true] at hc
    simp only [listEq, Bool.and_eq_true] at h
    rw [valEq_sound x y hc.1 h.1, listEq_sound xs ys hc.2 h.2]

theorem tabEq_sound : (x y : QTable) → tabCellFree x = true → tabEq x y = true → x = y
  | .mk c ⟨v⟩ a, .mk c' ⟨v'⟩ a', hc, h => by
    simp only [tabCellFree] at hc
    simp only [tabEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hl⟩, rfl⟩ := h
    rw [listEq_sound v v' hc hl]

theorem encEq_sound : (e f : Enc) → encCellFree e = true → encEq e f = true → e = f
  | .gen ⟨xs⟩, f, hc, h => by
    cases f with
    | gen ys =>
      obtain ⟨ys⟩ := ys
      simp only [encEq] at h
      simp only [encCellFree] at hc
      rw [listEq_sound xs ys hc h]
    | _ => simp [encEq] at h
  | .bytes _, f, _, h | .bits _, f, _, h | .syms .., f, _, h | .foR .., f, _, h | .alp .., f, _, h
  | .enum .., f, _, h => by cases f <;> simp_all [encEq]

end

/-- **`valEq` is `=` on a cell-free value**: reflexive everywhere, and equal values where one holds no cell. -/
theorem valEq_iff {a b : QValue} (hc : cellFree a = true) : valEq a b = true ↔ a = b :=
  ⟨valEq_sound a b hc, fun h => h ▸ valEq_refl a⟩

#print axioms valEq_iff

end LeetQ.Rel
