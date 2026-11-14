/-
  The joint codes of a small integral or float side of several parts, the parts and their `raze` in any
  encoding: part `k`'s code at `i` is the razed column's at `O_k + i`, and that row is part `k`'s row `i`
  (`raze_get`, every answer of `razeColumn`). Above `RazeFoR`, which reads every raze back.
-/
import LeetQ.Rel.KernelWF.RazeFoR
import LeetQ.Rel.KernelWF.CodesFloatParts

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A float side: its codes are faithful jointly across the parts** — equal codes exactly at rows of equal
    bits; the parts and their `raze` in any encoding, the parts' summed count a `USize`, 32 bits where an ALP
    join offsets it (`hA`). -/
theorem codes_float_parts_faithful {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  obtain ⟨q, hq, hc⟩ := codes_float_cut ht cs (by omega)
  obtain ⟨κ, -, g, hκ, -, hq1, hq2, -⟩ := float_groups ht (raze t cs.toArray).2 hq
  obtain ⟨-, hW, -, hBo, -, -⟩ := float_facts ht hκ
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := ofIds_groupOf_wf g (raze t cs.toArray).1 hq1 hq2
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [hc]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    ofIds_float_faithful ht _ hq (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    raze_get hW hBo cs hN hA hk hi, raze_get hW hBo cs hN hA hl hj]

/-- **A side at a small integral or float kind: its codes are faithful jointly across the parts, each well
    formed, all on one lane** — the parts and their `raze` in any encoding; the int sides through
    `codes_small_int_parts_faithful`/`_wf`, the float sides grouped by their bits
    (`codes_float_parts_faithful`/`_wf`); the parts' summed count a `USize`, 32 bits where an ALP join offsets
    it (`hA`). -/
theorem codes_dense_faithful_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32) :
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
          Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
        Vals.row (A := .atom t) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := .atom t) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes (.atom t) cs)[k]'hk
        laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p),
        ((Obj.codes (.atom t) cs)[k]'hk).w = ((Obj.codes (.atom t) cs)[l]'hl).w := by
  rcases hk₀ with hk₀ | hk₀ | hk₀ | hk₀ | hk₀
  -- a float side groups by its bits (`bitsType`)
  all_goals try
    have hf : t = .real ∨ t = .float ∨ t = .datetime := by
      clear hA hN; cases t <;> simp [orderKind] at ht <;> simp_all
    exact ⟨⟨fun hk hl _ _ hi hj => codes_float_parts_faithful hf cs hN hA hk hl hi hj,
      fun hk => (codes_float_parts_wf hf cs hN hk).1⟩, fun hk hl => (codes_float_parts_wf hf cs hN hk).2 hl⟩
  all_goals
    have hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 := by clear hA hN; simp_all
    refine ⟨⟨fun hk hl _ _ hi hj => codes_small_int_parts_faithful ht hk₀ cs hN hk hl hi hj,
      fun hk => codes_small_int_parts_wf ht hk₀ cs hN hk⟩, fun hk hl => ?_⟩
    rw [codes_small_int_cut ht hk₀ cs (by omega)]; unfold Code.cut; split <;> simp

#print axioms codes_float_parts_faithful
#print axioms codes_dense_faithful_wf

end LeetQ.Rel.Alg
