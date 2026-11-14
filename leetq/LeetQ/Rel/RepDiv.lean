/-
  The divisions of `Rel`, read back. `leftDiv R S Ub Uc` joins `R.nub` and `S.nub` on the shared key into rows
  `(y, z)` (the `y` part, as `≫` joins), keeps the first row of each pair whose count equals the count of `y`
  among `R.nub`'s values (`leftDiv_keep`), and adds `⊤` on the values of `Ub` that are no value of `R` and `Uc`.
-/
import LeetQ.Rel.RepComp
import LeetQ.Rel.KernelWF.DivSpec
import LeetQ.Rel.KernelWF.CountSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

-- the pairs `(i, j)` `join l r` answers, as `join_rows` lists them: row `i` of `l`, row `j` of `r`, equal codes
set_option quotPrecheck false in
local notation "jp(" l ", " r ")" => ((List.range (Code.n l).toNat).flatMap fun i =>
  ((List.range (Code.n r).toNat).filter fun j =>
    Column.idAt (Code.b r) (Code.w r) j == Column.idAt (Code.b l) (Code.w l) i).map (i, ·))

/-- **`leftDiv`'s joined rows, read back**: one row per pair `(i, j)` of `join l r`, in its order, `x`'s row `i`
    beside `z`'s row `j`. Stated over any two codes, not `leftDiv`'s, so the statement holds no `Obj.codes`.
    Hypotheses: `join_rows`', and each side picks back at its rows of the pairs. -/
theorem div_y_rows {n₁ n₂ : USize} (l r : Code) (x : Vals B n₁) (z : Vals C n₂) (hln : l.n = n₁) (hrn' : r.n = n₂)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hrn : r.n.toNat < 2 ^ 63)
    (hM : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < 2 ^ 63)
    (hMU : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < USize.size)
    (hB : Vals.PickFits B x ((jp(l, r)).map Prod.fst)) (hC : Vals.PickFits C z ((jp(l, r)).map Prod.snd))
    (m : USize) (hmJ : len (join l r).2 = m.toNat) (hle : m.toNat ≤ len (join l r).1) :
    m.toNat = (jp(l, r)).length ∧
      ∀ (q : Nat) (hq : q < m.toNat), ∃ (hJ : q < (jp(l, r)).length)
        (hi : ((jp(l, r))[q]'hJ).1 < n₁.toNat) (hj : ((jp(l, r))[q]'hJ).2 < n₂.toNat),
        (Vals.pickN B x (join l r).1 m hle).row ⟨q, hq⟩ = x.row ⟨_, hi⟩ ∧
        (Vals.pick C z (join l r).2 m hmJ).row ⟨q, hq⟩ = z.row ⟨_, hj⟩ := by
  subst hln hrn'
  obtain ⟨-, hZ⟩ := join_rows l r hlw hls hrw hrs hrc hrn hM hMU
  have e := hZ m hmJ
  have hfB : Vals.PickFits B x
      ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat) =
      (jp(l, r)).map Prod.fst by rw [e, List.map_map]; rfl]; exact hB
  have hfC : Vals.PickFits C z ((List.range m.toNat).map fun q => (Column.bitsAt (join l r).2 (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (join l r).2 (q * 8) 8).toNat) =
      (jp(l, r)).map Prod.snd by rw [e, List.map_map]; rfl]; exact hC
  have hlen : m.toNat = (jp(l, r)).length := by rw [e, List.length_map, List.length_range]
  refine ⟨hlen, fun q hq => ?_⟩
  have hJ : q < (jp(l, r)).length := by rw [← hlen]; exact hq
  have hq' : (jp(l, r))[q]'hJ = ((Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat,
      (Column.bitsAt (join l r).2 (q * 8) 8).toNat) := by
    rw [List.getElem_of_eq e hJ]; simp only [List.getElem_map, List.getElem_range]
  have hmem := List.getElem_mem hJ
  rw [hq'] at hmem
  obtain ⟨hi, hj, -⟩ := (mem_joinPairs l r _ _).1 hmem
  refine ⟨hJ, by rw [hq']; exact hi, by rw [hq']; exact hj, ?_, ?_⟩
  · unfold Vals.pickN
    rw [pick_row B x _ m _ hfB ⟨q, hq⟩, dif_pos hi]
    exact congrArg x.row (Fin.ext (congrArg Prod.fst hq').symm)
  · rw [pick_row C z _ m hmJ hfC ⟨q, hq⟩, dif_pos hj]
    exact congrArg z.row (Fin.ext (congrArg Prod.snd hq').symm)

#print axioms div_y_rows

end LeetQ.Rel.Rep
