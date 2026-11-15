/-
  `Obj.raze` of any number of parts read back at every shape of side: row `j` of part `l` is the razed row at the
  counts before `l` plus `j` (`raze_rowN`), under `razeC`'s bit. The constructor cases are `RazeRow`'s and
  `RazeRowRec`'s with the second part's offset generalised to the counts before part `l`.
-/
import LeetQ.Rel.KernelWF.RazeFoR

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

theorem foldl_add_sum' : ∀ (L : List Nat) (s : Nat), L.foldl (· + ·) s = s + L.sum
  | [], s => by simp
  | x :: L, s => by rw [List.foldl_cons, foldl_add_sum' L, List.sum_cons]; omega

/-- The running count `raze` moves part `l` by: the counts before `l`. -/
theorem extract_foldl (xs : Array Nat) (l : Nat) : (xs.extract 0 l).foldl (· + ·) 0 = (xs.toList.take l).sum := by
  rw [← Array.foldl_toList, foldl_add_sum', Nat.zero_add, Array.toList_extract, List.extract_eq_drop_take,
    List.drop_zero, Nat.sub_zero]

/-- Parts mapped keeping their counts keep the counts before each part. -/
theorem off_map {α β : USize → Type} (cs : Array ((n : USize) × α n)) (f : ((n : USize) × α n) → (n : USize) × β n)
    (h : ∀ c, (f c).1 = c.1) (l : Nat) :
    (((cs.map f).toList.take l).map (·.1.toNat)).sum = ((cs.toList.take l).map (·.1.toNat)).sum := by
  congr 1; apply List.ext_getElem (by simp); intro i _ _; simp [h]

theorem off_mapIdx {α β : USize → Type} (cs : Array ((n : USize) × α n))
    (f : Nat → ((n : USize) × α n) → (n : USize) × β n) (h : ∀ k c, (f k c).1 = c.1) (l : Nat) :
    (((cs.mapIdx f).toList.take l).map (·.1.toNat)).sum = ((cs.toList.take l).map (·.1.toNat)).sum := by
  congr 1; apply List.ext_getElem (by simp); intro i _ _; simp [h]

theorem row_congr {A : Obj} : ∀ {x y : Part A}, x = y → ∀ i hx hy, x.2.row ⟨i, hx⟩ = y.2.row ⟨i, hy⟩
  | _, _, rfl, _, _, _ => rfl

theorem get_congr {t : QAtomicType} : ∀ {x y : (n : USize) × Arr t n}, x = y → ∀ i hx hy, x.2.get ⟨i, hx⟩ = y.2.get ⟨i, hy⟩
  | _, _, rfl, _, _, _ => rfl

/-- Parts razed, `hT` its list the parts' lists one after another: element `(counts before l) + j` is part `l`'s
    element `j`. -/
theorem razeTo_getN {t : QAtomicType} {C : Array ((k : USize) × Arr t k)} {S : Nat}
    (hs : (C.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size)
    (hT : (razeTo t C hs hS).toList = C.toList.flatMap (·.2.toList)) {l : Nat} (hl : l < C.size) {j : Nat}
    (hj : j < C[l].1.toNat) (q : Nat) (hq : q < S.toUSize.toNat) (e : q = ((C.toList.take l).map (·.1.toNat)).sum + j) :
    (razeTo t C hs hS).get ⟨q, hq⟩ = C[l].2.get ⟨j, hj⟩ := by
  have ho := flatMap_offset (fun c : (k : USize) × Arr t k => c.2.toList) (·.1.toNat) (fun c => Arr.length_toList _)
    C.toList (k := l) (by simpa using hl) (i := j) (by simpa using hj)
  rw [← e, ← hT, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hq), Arr.getElem_toList] at ho
  simp only [Array.getElem_toList] at ho
  rw [List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hj), Arr.getElem_toList] at ho
  exact Option.some.inj ho

/-- `razeTo_toList_bytes` at parts each a dense column `g k d` of the part `d` at its index `k`. -/
theorem razeTo_toList_mapIdx {t : QAtomicType} {α : USize → Type} (D : Array ((n : USize) × α n))
    (g : Nat → (d : (n : USize) × α n) → Arr t d.1) {S : Nat}
    (hs : ((D.mapIdx fun k d => (⟨d.1, g k d⟩ : (n : USize) × Arr t n)).toList.map (·.1.toNat)).sum = S)
    (hS : S < USize.size) (hg : ∀ k d, ∃ b, (g k d).enc = .bytes b) :
    (razeTo t (D.mapIdx fun k d => ⟨d.1, g k d⟩) hs hS).toList =
      (D.mapIdx fun k d => (⟨d.1, g k d⟩ : (n : USize) × Arr t n)).toList.flatMap (·.2.toList) :=
  razeTo_toList_bytes _ hs hS fun c hc => by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
    rw [Array.getElem_mapIdx]; exact hg _ _

/-- **An atom's razed list under `razeC`'s bit**: the parts' lists one after another, at every type. -/
theorem razeTo_toList_bit {t : QAtomicType} (cs : Array (Part (.atom t)))
    (hN : (cs.toList.map fun c : Part (.atom t) => c.1.toNat).sum < USize.size) (hb : ((Obj.atom t).razeC cs hN).2 = true) :
    (razeTo t cs rfl hN).toList = cs.toList.flatMap (·.2.toList) := by
  simp only [Obj.razeC, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hb
  by_cases hB : t = .boolean
  · subst hB; exact razeTo_toList_boolean cs rfl hN
  by_cases hG : t = .general
  · subst hG; exact razeTo_toList_general cs rfl hN
  by_cases hY : t = .symbol
  · subst hY; exact razeTo_toList_symbol cs rfl hN hb.1
  by_cases hU : t = .guid
  · subst hU; exact razeTo_toList_bytes cs rfl hN fun c _ => guid_bytes c.2
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> simp_all [QAtomicType.width]
  exact razeTo_toList_all hw hB cs rfl hN fun _ ha => by
    rcases hb.2 with h | h
    · rw [ha] at h; cases h
    · exact h

/-- A razed side `W` read at `I` clamped, where `I` is part `w`'s position `J` clamped into it, moved past `d`, the
    values before it: `w` read at `J` clamped. -/
theorem side_read_at {c : Obj} {L l1 : USize} (W : Vals c L) (w : Vals c l1) {d : Nat} (hd : d + l1.toNat ≤ L.toNat)
    (hW : ∀ i (hi : i < l1.toNat), Vals.row W ⟨d + i, by omega⟩ = Vals.row w ⟨i, hi⟩)
    {I J : Int64} (hI : I.toInt = ((min (max J.toInt 0).toNat (l1.toNat - 1) + d : Nat) : Int)) (h1 : 0 < l1.toNat) :
    (if h : 0 < L.toNat then Vals.row W (clampFin I L.toNat h) else c.dflt) =
      if h : 0 < l1.toNat then Vals.row w (clampFin J l1.toNat h) else c.dflt := by
  rw [dif_pos (by omega), dif_pos h1,
    show clampFin I L.toNat (by omega) = ⟨d + min (max J.toInt 0).toNat (l1.toNat - 1), by omega⟩ from
      Fin.ext (by simp only [clampFin, hI]; omega), hW _ (by omega)]
  exact congrArg _ (Fin.ext (by simp only [clampFin] <;> omega))

/-- **Row read-back of `raze` of any number of parts**: under `razeC`'s bit, the razed row at the counts before
    part `l` plus `j` is row `j` of part `l` — an atom by its razed list (`razeTo_toList_bit`), a product
    componentwise, an array by its moved offsets (`shiftArr_get`), a sum by its tags and moved positions
    (`place_off_get`) on the `held` parts. -/
theorem raze_rowN : ∀ (A : Obj) (ps : Array (Part A))
    (hN : (ps.toList.map fun c : Part A => c.1.toNat).sum < USize.size), (A.razeC ps hN).2 = true →
    ∀ {l : Nat} (hl : l < ps.size) {j : Nat} (hj : j < ps[l].1.toNat) (q : Nat)
      (hq : q < (ps.toList.map fun c : Part A => c.1.toNat).sum.toUSize.toNat),
      q = ((ps.toList.take l).map (·.1.toNat)).sum + j → (A.raze ps hN).row ⟨q, hq⟩ = ps[l].2.row ⟨j, hj⟩
  | .atom t, ps, hN, hb, l, hl, j, hj, q, hq, e => by
    rw [Obj.raze.eq_1, Vals.row_atom, Vals.row_atom]
    exact razeTo_getN rfl hN (razeTo_toList_bit ps hN hb) hl hj q hq e
  | .prod a b, ps, hN, hb, l, hl, j, hj, q, hq, e => by
    simp only [Obj.razeC, Bool.and_eq_true] at hb
    have s1 := sum_map_fst ps (fun c => (⟨c.1, c.2.1⟩ : Part a)) (fun _ => rfl)
    have s2 := sum_map_fst ps (fun c => (⟨c.1, c.2.2⟩ : Part b)) (fun _ => rfl)
    have h1 : ((ps.map fun c => (⟨c.1, c.2.1⟩ : Part a)).toList.map fun c : Part a => c.1.toNat).sum < USize.size := by
      rw [s1]; exact hN
    have h2 : ((ps.map fun c => (⟨c.1, c.2.2⟩ : Part b)).toList.map fun c : Part b => c.1.toNat).sum < USize.size := by
      rw [s2]; exact hN
    rw [Obj.raze.eq_2, Vals.row.eq_2, Vals.row.eq_2]
    refine Prod.ext ?_ ?_ <;> dsimp only
    · refine (row_heq _ (a.raze _ h1) ⟨q, hq⟩ ⟨q, by rw [s1]; exact hq⟩ (by rw [s1]) ?_ rfl).trans
        ((raze_rowN a _ h1 hb.1 (l := l) (by simpa using hl) (by simpa using hj) q _
          (by rw [off_map] <;> first | exact e | intro; rfl)).trans (row_congr (Array.getElem_map ..) j _ _))
      first
        | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq (by simp) _ _)
        | exact HEq.trans (eqRec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq (by simp) _ _)
        | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq rfl _ _)
    · refine (row_heq _ (b.raze _ h2) ⟨q, hq⟩ ⟨q, by rw [s2]; exact hq⟩ (by rw [s2]) ?_ rfl).trans
        ((raze_rowN b _ h2 hb.2 (l := l) (by simpa using hl) (by simpa using hj) q _
          (by rw [off_map] <;> first | exact e | intro; rfl)).trans (row_congr (Array.getElem_map ..) j _ _))
      first
        | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq (by simp) _ _)
        | exact HEq.trans (eqRec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq (by simp) _ _)
        | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq rfl _ _)
  | .arr b, ps, hN, hb, l, hl, j, hj, q, hq, e => by
    simp only [Obj.razeC] at hb
    split at hb
    rotate_left
    · cases hb
    rename_i hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have hS : (ps.toList.map fun c : Part (.arr b) => c.1.toNat).sum.toUSize.toNat =
        (ps.toList.map fun c : Part (.arr b) => c.1.toNat).sum := USize.toNat_ofNat_of_lt' hN
    have hlF : l < (ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).size := by simpa using hl
    -- the payloads before part `l` and part `l`'s own fit below the payload count
    have hle : (((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.take l).map (·.1.toNat)).sum +
        ps[l].2.1.toNat ≤ ((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map fun c : Part b => c.1.toNat).sum := by
      have := take_sum_le ((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map (·.1.toNat)) (k := l)
        (by simpa using hl)
      simpa using this
    have h63 : ((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map fun c : Part b => c.1.toNat).sum < 2 ^ 63 :=
      hb.1
    generalize hD : (((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.take l).map (·.1.toNat)).sum = d at hle
    have hd : (ps.map (·.2.1.toNat) |>.extract 0 l).foldl (· + ·) 0 = d := by
      rw [extract_foldl, ← hD]; congr 1; apply List.ext_getElem (by simp); intro i _ _; simp
    generalize hR : (Obj.arr b).raze ps hN = R
    have hR1 : R.1 = ((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map
        fun c : Part b => c.1.toNat).sum.toUSize := by
      subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf]
    have hRn : R.1.toNat = ((ps.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map
        fun c : Part b => c.1.toNat).sum := by rw [hR1]; exact USize.toNat_ofNat_of_lt' hf
    have hF : HEq R.2.2.2 (b.raze _ hf) := by
      subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf]
    have hrow : ∀ i (hi : i < ps[l].2.1.toNat) (hd' : d + i < R.1.toNat),
        Vals.row R.2.2.2 ⟨d + i, hd'⟩ = Vals.row ps[l].2.2.2.2 ⟨i, hi⟩ := fun i hi hd' =>
      (row_heq _ _ ⟨_, hd'⟩ ⟨d + i, by rw [← hR1]; exact hd'⟩ hR1 hF rfl).trans
        ((raze_rowN b _ hf hb.2 hlF (j := i) (by simpa using hi) _ _ (by rw [hD])).trans
          (row_congr (Array.getElem_map ..) i _ _))
    have hq' : q < (ps.toList.map fun c : Part (.arr b) => c.1.toNat).sum.toUSize.toNat := hq
    -- row `q`'s offsets: part `l`'s at `j`, clamped into its payload, moved past the payloads before it
    have hO : (R.2.1.get ⟨q, hq⟩).toInt = ((min (max (ps[l].2.2.1.get ⟨j, hj⟩).toInt 0).toNat ps[l].2.1.toNat + d : Nat) : Int) ∧
        (R.2.2.1.get ⟨q, hq⟩).toInt = ((min (max (ps[l].2.2.2.1.get ⟨j, hj⟩).toInt 0).toNat ps[l].2.1.toNat + d : Nat) : Int) := by
      subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf]; dsimp only
      refine ⟨?_, ?_⟩ <;>
        rw [razeTo_getN _ _ (razeTo_toList_mapIdx _ _ _ _ fun _ _ => ⟨_, rfl⟩) (by simpa using hl) (j := j)
          (by simpa using hj) q hq' (by rw [off_mapIdx] <;> first | exact e | intros; rfl),
          get_congr (Array.getElem_mapIdx ..) j _ hj] <;> dsimp only <;> rw [shiftArr_get, hd] <;> omega
    obtain ⟨eL, eH⟩ := hO
    rw [arr_row R, arr_row ps[l].2]
    have hcl : min (max (ps[l].2.2.1.get ⟨j, hj⟩).toInt 0).toNat ps[l].2.1.toNat ≤ ps[l].2.1.toNat := Nat.min_le_right ..
    have hch : min (max (ps[l].2.2.2.1.get ⟨j, hj⟩).toInt 0).toNat ps[l].2.1.toNat ≤ ps[l].2.1.toNat := Nat.min_le_right ..
    have kL : (max (R.2.1.get ⟨q, hq⟩).toInt 0).toNat = d + min (max (ps[l].2.2.1.get ⟨j, hj⟩).toInt 0).toNat
        ps[l].2.1.toNat := by rw [eL]; omega
    have kH : (max (R.2.2.1.get ⟨q, hq⟩).toInt 0).toNat = d + min (max (ps[l].2.2.2.1.get ⟨j, hj⟩).toInt 0).toNat
        ps[l].2.1.toNat := by rw [eH]; omega
    have mL : min (max (R.2.1.get ⟨q, hq⟩).toInt 0).toNat R.1.toNat = d + min (max (ps[l].2.2.1.get ⟨j, hj⟩).toInt
        0).toNat ps[l].2.1.toNat := by rw [kL]; exact Nat.min_eq_left (by rw [hRn]; omega)
    have mH : min (max (R.2.2.1.get ⟨q, hq⟩).toInt 0).toNat R.1.toNat = d + min (max (ps[l].2.2.2.1.get ⟨j, hj⟩).toInt
        0).toNat ps[l].2.1.toNat := by rw [kH]; exact Nat.min_eq_left (by rw [hRn]; omega)
    rw [mL, mH, Nat.add_sub_add_left]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hx : min (max (ps[l].2.2.1.get ⟨j, hj⟩).toInt 0).toNat ps[l].2.1.toNat + i < ps[l].2.1.toNat := by omega
    rw [dif_pos (by omega), dif_pos hx, ← hrow _ hx (by omega)]
    exact congrArg _ (Fin.ext (by dsimp only; omega))
  | .sum a b, ps, hN, hb, l, hl, j, hj, q, hq, e => by
    sorry

end LeetQ.Rel.KernelWF
