/-
  What `Obj.raze` of two parts READS: row `k` of the razed side is row `k` of the first part below its count, and
  row `k - n` of the second past it — at every shape of side, one lemma per constructor of `Obj`, each taking the
  read-back of its components as a hypothesis, so a side's read-back is these lemmas composed along its shape.
  An atom's read-back is `razeTo`'s list (`razeTo_toList_bytes`, `_boolean`, `_general`); the encodings those do
  not cover stay as the atom lemma's one hypothesis `hA`.
-/
import LeetQ.Rel.RepOps

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A side moved along a count equation keeps its rows. -/
theorem row_castN {A : Obj} {a b : Nat} (e : a = b) (v : Vals A a.toUSize) (i : Fin b.toUSize.toNat) :
    Vals.row (e ▸ v : Vals A b.toUSize) i = Vals.row v ⟨i.1, by subst e; exact i.2⟩ := by subst e; rfl

/-- `Obj.raze` of equal part arrays reads equal rows. -/
theorem raze_row_congr {A : Obj} {cs cs' : Array (Part A)} (e : cs = cs')
    (h : (cs.toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (h' : (cs'.toList.map fun c : Part A => c.1.toNat).sum < USize.size) (k : Nat)
    (hk : k < (cs.toList.map fun c : Part A => c.1.toNat).sum.toUSize.toNat)
    (hk' : k < (cs'.toList.map fun c : Part A => c.1.toNat).sum.toUSize.toNat) :
    Vals.row (A.raze cs h) ⟨k, hk⟩ = Vals.row (A.raze cs' h') ⟨k, hk'⟩ := by subst e; rfl

/-- **Row read-back of `raze` at an atom**: the razed column's element `k` is the first part's below its count,
    the second's past it. `hA`: `razeTo`'s list is the parts' lists one after another (`razeTo2_bytes`,
    `_boolean`, `_general` discharge it). -/
theorem raze_row_atom {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hA : (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.atom t).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row (A := .atom t) x ⟨k, h⟩
      else Vals.row (A := .atom t) y ⟨k - n.toNat, by have := raze2_cnt (X := .atom t) x y hN; omega⟩ := by
  have hc := raze2_cnt (X := .atom t) x y hN
  have hl : k < (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList.length := by
    rw [hA, List.length_append, Arr.length_toList, Arr.length_toList]; omega
  show Arr.get (razeTo t _ rfl hN) ⟨k, hk⟩ = _
  rw [← Arr.getElem_toList _ k hl]
  simp only [hA, List.getElem_append, Arr.length_toList, Vals.row_atom, Arr.getElem_toList]

/-- Two parts' `razeTo` list, from the `flatMap` the `razeTo_toList_*` lemmas conclude. -/
theorem razeTo2_toList {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (h : (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList =
      (#[⟨n, x⟩, ⟨m, y⟩] : Array ((k : USize) × Arr t k)).toList.flatMap (·.2.toList)) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  rw [h]; simp

/-- `raze_row_atom`'s `hA` at two dense parts (`razeTo_toList_bytes`). -/
theorem razeTo2_bytes {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hx : ∃ b, x.enc = .bytes b) (hy : ∃ b, y.enc = .bytes b) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_bytes _ rfl hN fun c hc => by
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hx
    · exact hy)

/-- `raze_row_atom`'s `hA` at `boolean` (`razeTo_toList_boolean`). -/
theorem razeTo2_boolean {n m : USize} (x : Arr .boolean n) (y : Arr .boolean m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom .boolean))).toList.map
      fun c : Part (.atom .boolean) => c.1.toNat).sum < USize.size) :
    (razeTo .boolean #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_boolean _ rfl hN)

/-- `raze_row_atom`'s `hA` at `general` (`razeTo_toList_general`). -/
theorem razeTo2_general {n m : USize} (x : Arr .general n) (y : Arr .general m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom .general))).toList.map
      fun c : Part (.atom .general) => c.1.toNat).sum < USize.size) :
    (razeTo .general #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_general _ rfl hN)

/-- **Row read-back of `raze` at a product**: each component razed on its own (`iha`, `ihb`). -/
theorem raze_row_prod {a b : Obj} {n m : USize} (x : Vals (.prod a b) n) (y : Vals (.prod a b) m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.prod a b))).toList.map fun c : Part (.prod a b) => c.1.toNat).sum <
      USize.size)
    (iha : ∀ hN' k hk, Vals.row (a.raze #[⟨n, x.1⟩, ⟨m, y.1⟩] hN') ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x.1 ⟨k, h⟩
      else Vals.row y.1 ⟨k - n.toNat, by have := raze2_cnt x.1 y.1 hN'; omega⟩)
    (ihb : ∀ hN' k hk, Vals.row (b.raze #[⟨n, x.2⟩, ⟨m, y.2⟩] hN') ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x.2 ⟨k, h⟩
      else Vals.row y.2 ⟨k - n.toNat, by have := raze2_cnt x.2 y.2 hN'; omega⟩) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.prod a b))).toList.map
      fun c : Part (.prod a b) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.prod a b).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ := by
  have hc := raze2_cnt x y hN
  have ha : ((#[⟨n, x.1⟩, ⟨m, y.1⟩] : Array (Part a)).toList.map fun c : Part a => c.1.toNat).sum < USize.size := by
    simpa using hN
  have hb : ((#[⟨n, x.2⟩, ⟨m, y.2⟩] : Array (Part b)).toList.map fun c : Part b => c.1.toNat).sum < USize.size := by
    simpa using hN
  have hka : k < ((#[⟨n, x.1⟩, ⟨m, y.1⟩] : Array (Part a)).toList.map fun c : Part a => c.1.toNat).sum.toUSize.toNat := by
    rw [raze2_cnt x.1 y.1 ha]; omega
  have hkb : k < ((#[⟨n, x.2⟩, ⟨m, y.2⟩] : Array (Part b)).toList.map fun c : Part b => c.1.toNat).sum.toUSize.toNat := by
    rw [raze2_cnt x.2 y.2 hb]; omega
  rw [Obj.raze.eq_2, Vals.row.eq_2]
  dsimp only
  rw [row_castN, row_castN, raze_row_congr (by simp) _ ha k _ hka, raze_row_congr (by simp) _ hb k _ hkb,
    iha ha k hka, ihb hb k hkb]
  by_cases h : k < n.toNat
  · simp only [dif_pos h]; rfl
  · simp only [dif_neg h]; rfl

end LeetQ.Rel.KernelWF
