/-
  `join l r` read back, from the content lemmas of `JoinContent`: the class ids `Code.groupIds` answers are
  `groupOf` of the codes, the count column `expand` reads is the number of right rows matching each left
  row, and the pairs are every matching `(i, j)` once, by `i` then `j`.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.MemberSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- **`Code.groupIds`' class ids are `groupOf` of the codes**, read at the width of the class count: row
    `i`'s class is the position of its code's first row among the first rows (`groupIds_firsts`), and the
    payload holds all `n` of them. Hypotheses as `groupIds_firsts`. -/
theorem groupIds_groupOf (c : Code)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    Column.idsCap c.groupIds.1 (Column.idWidthOf (len c.groupIds.2)) c.n.toNat = c.n.toNat ∧
      ∀ i < c.n.toNat, Column.idAt c.groupIds.1 (Column.idWidthOf (len c.groupIds.2)) i =
        Verify.groupOf (Column.idAt c.b c.w) c.n.toNat i := by
  rw [len_eq_ids, groupIds_firsts c hw hs hcard]
  have hW := laneWidth_cases (Column.widthFor ((firstsOf (Column.idAt c.b c.w) c.n.toNat).length - 1))
  simp only [show ∀ x, Column.laneWidth (Column.widthFor (x - 1)) = Column.idWidthOf x from fun _ => rfl] at hW
  have hL : (firstsOf (Column.idAt c.b c.w) c.n.toNat).length ≤ 2 ^ 64 := by
    have := List.length_filter_le (fun i => (List.range i).all fun j =>
      !decide (Column.idAt c.b c.w j = Column.idAt c.b c.w i)) (List.range c.n.toNat)
    rw [List.length_range] at this
    exact Nat.le_trans this (Nat.le_of_lt (usize_lt c.n))
  -- a payload `packIds` of `groupOf g n`, `g` grouping as the codes do, is the claim
  have hP : ∀ {α : Type} [DecidableEq α] (g : Nat → α) (G : ByteArray),
      (∀ i < c.n.toNat, ∀ j < c.n.toNat, (g i = g j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) →
      G = Column.packIds (Column.idWidthOf (firstsOf g c.n.toNat).length) c.n.toNat (Verify.groupOf g c.n.toNat) →
      Column.idsCap G (Column.idWidthOf (firstsOf (Column.idAt c.b c.w) c.n.toNat).length) c.n.toNat = c.n.toNat ∧
        ∀ i < c.n.toNat, Column.idAt G (Column.idWidthOf (firstsOf (Column.idAt c.b c.w) c.n.toNat).length) i =
          Verify.groupOf (Column.idAt c.b c.w) c.n.toNat i := by
    intro α _ g G hg hG
    obtain ⟨hf, -, hgo⟩ := groups_congr g c.n.toNat hg
    rw [hG, hf]
    refine ⟨idsCap_packIds _ _ hW, fun i hi => ?_⟩
    rw [idAt_packIds hW hi (by rw [hgo i hi]; exact lt_two_pow_idWidthOf hL (groupOf_lt hi))]; exact hgo i hi
  unfold Code.groupIds Code.kind
  split
  · rename_i k hk
    rcases laneKind_some hk with ⟨rfl, e⟩ | ⟨-, e, hq, hki⟩
    · have hm : min c.n.toNat (Scan.Kind.avail .bit c.b) = c.n.toNat := by
        simp only [Scan.Kind.avail, hs, e]; omega
      refine hP _ _ (fun i _ j _ => ?_) (by rw [(groupIds_spec .bit c.n c.b).1, hm])
      simp only [Order.keyAt, Order.rank, Scan.Kind.bitsAt, e, idAt_one]
      cases Column.bitAt c.b i <;> cases Column.bitAt c.b j <;> decide
    · have hk0 : 0 < k.width := by rcases hki with rfl | rfl | rfl | rfl | rfl <;> decide
      have hk8 : k.width ≤ 8 := by omega
      have hav : Scan.Kind.avail k c.b = c.b.size / k.width := by
        rcases hki with rfl | rfl | rfl | rfl | rfl <;> rfl
      have hm : min c.n.toNat (Scan.Kind.avail k c.b) = c.n.toNat := by
        rw [hav, hs, e, show c.n.toNat * (8 * k.width) + 7 = 8 * (c.n.toNat * k.width) + 7 by
          rw [Nat.mul_left_comm], show (8 * (c.n.toNat * k.width) + 7) / 8 = c.n.toNat * k.width by omega,
          Nat.mul_div_cancel _ hk0, Nat.min_self]
      refine hP _ _ (fun i _ j _ => ?_) (by rw [(groupIds_spec k c.n c.b).1, hm])
      rw [keyAt_eq_iff hki, e, idAt_lane _ hk8, idAt_lane _ hk8]
      exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.1 h⟩
  · rename_i hk
    have h24 := laneKind_none hk hw
    obtain ⟨hcU, hlt⟩ := hcard (by omega)
    have hd : c.card.toUSize.toNat = c.card := USize.toNat_ofNat_of_lt' hcU
    have hwn : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    have hb : ∀ a e : Nat, (a == e) = decide (a = e) := fun a e => Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff])
    have hF : Order.idFirsts c.card.toUSize.toNat c.n.toNat c.w.toUSize.toNat c.b =
        firstsOf (Order.idKey c.card.toUSize.toNat c.b c.w.toUSize.toNat) c.n.toNat := by
      simp only [Order.idFirsts, firstsOf, bne, hb]
    refine hP _ _ (fun i hi j hj => ?_) (by simp only [Order.idGroups, hF, hb]; rfl)
    simp only [Order.idKey, hd, hwn, Nat.min_eq_left (Nat.le_of_lt (hlt i hi)),
      Nat.min_eq_left (Nat.le_of_lt (hlt j hj))]

/-- `Code.groupIds`' first-row count is the number of distinct codes, at most `n`. Hypotheses as
    `groupIds_firsts`. -/
theorem groupIds_len (c : Code)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    len c.groupIds.2 = (firstsOf (Column.idAt c.b c.w) c.n.toNat).length ∧
      (firstsOf (Column.idAt c.b c.w) c.n.toNat).length ≤ c.n.toNat := by
  refine ⟨by rw [len_eq_ids, groupIds_firsts c hw hs hcard], ?_⟩
  have := List.length_filter_le (fun i => (List.range i).all fun j =>
    !decide (Column.idAt c.b c.w j = Column.idAt c.b c.w i)) (List.range c.n.toNat)
  rw [List.length_range] at this; exact this

/-- **The class `idxOf` names**: where the value `v` is some first row's, the rows of that class are the
    rows holding `v`; where it is none, no row holds `v`. -/
theorem idxOf_class {α : Type} [DecidableEq α] (g : Nat → α) (n : Nat) (v : α) :
    (((firstsOf g n).map g).idxOf v < (firstsOf g n).length → ∀ j < n,
      (Verify.groupOf g n j = ((firstsOf g n).map g).idxOf v ↔ g j = v)) ∧
    ((firstsOf g n).length ≤ ((firstsOf g n).map g).idxOf v → ∀ j < n, g j ≠ v) := by
  refine ⟨fun hcF j hj => ?_, fun hcF j hj e => ?_⟩
  · have hlt : ((firstsOf g n).map g).idxOf v < ((firstsOf g n).map g).length := by
      rw [List.length_map]; exact hcF
    have e := beq_iff_eq.1 (List.findIdx_getElem (p := fun x => x == v) (w := hlt))
    have hfc : g ((firstsOf g n)[((firstsOf g n).map g).idxOf v]) = v := by
      simp only [List.getElem_map] at e; exact e
    rw [groupOf_eq_iff hj hcF, hfc]
  · have hm : v ∈ (firstsOf g n).map g :=
      List.mem_map.2 ⟨_, List.getElem_mem (groupOf_lt hj), by rw [groupOf_get (g := g) hj, e]⟩
    have := List.idxOf_lt_length_iff.2 hm
    rw [List.length_map] at this; omega

/-- A code payload of exactly `⌈n·w/8⌉` bytes at a lane holds its `n` codes, exactly at a byte lane: the size
    hypotheses `find_spec` and `gather_spec` take. -/
theorem code_size {w n s : Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hs : s = (n * w + 7) / 8) : w * n ≤ 8 * s ∧ (8 ≤ w → 8 * s = w * n) := by
  subst hs; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **`join`'s hit column, read back**: one long per row of `l`, its code's position among the codes of
    `r`'s first rows (`find` in `r`'s distinct codes), the count of those where it is none. Hypotheses as
    `join_count`. -/
theorem join_hit (l r : Code)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8) :
    len ((r.gather r.groupIds.2).find l) = l.n.toNat ∧ ∀ i < l.n.toNat,
      (Column.bitsAt ((r.gather r.groupIds.2).find l) (i * 8) 8).toNat =
        ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).idxOf (Column.idAt l.b l.w i) := by
  have hF := groupIds_firsts r hrw hrs hrc
  obtain ⟨hK, hFn⟩ := groupIds_len r hrw hrs hrc
  have hKU : len r.groupIds.2 < USize.size := by rw [hK]; exact Nat.lt_of_le_of_lt hFn r.n.toNat_lt_size
  have hFi : ∀ j (hj : j < len r.groupIds.2), (Column.bitsAt r.groupIds.2 (j * 8) 8).toNat =
      (firstsOf (Column.idAt r.b r.w) r.n.toNat)[j]'(by rw [← hK]; exact hj) := fun j hj => ids_get hF _
  obtain ⟨hgw, hgn, -, hgc⟩ := gather_spec r r.groupIds.2 hKU hrw (code_size hrw hrs).2
    fun j hj => by rw [hFi j hj]; exact firsts_lt _ _ (List.getElem_mem _)
  have hGs := gather_size r r.groupIds.2 hKU hrw
  obtain ⟨hfl, hfv⟩ := find_spec (r.gather r.groupIds.2) l (by rw [hgw]; exact hrw) hlw
    (by rw [hgw, hgn]; exact (code_size hrw hGs).1) (code_size hlw hls).1
    (by rw [hgw, hgn]; exact (code_size hrw hGs).2) (code_size hlw hls).2
  have hlist : (List.range (r.gather r.groupIds.2).n.toNat).map
      (Column.idAt (r.gather r.groupIds.2).b (r.gather r.groupIds.2).w) =
      (firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w) := by
    rw [hgn, hgw]
    apply List.ext_getElem (by simp [hK])
    intro j h1 _
    simp only [List.getElem_map, List.getElem_range]
    rw [List.length_map, List.length_range] at h1
    rw [hgc j h1, hFi j h1]
  exact ⟨hfl, fun i hi => by rw [hfv i hi, hlist]⟩

/-- **`join`'s count column, read back**: row `i` of `l` is counted once for every row of `r` holding its
    code — `classSizes` of the class `find` names in `r`'s first rows, `0` where `find` misses. Hypotheses:
    both codes at a lane, payloads of exactly their codes, `r`'s codes below its `card` (a `USize`) at
    `2`/`4` bits. -/
theorem join_count (l r : Code)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8) {i : Nat} (hi : i < l.n.toNat) :
    (Column.bitsAt (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l)) (i * 8) 8).toNat =
      ((List.range r.n.toNat).filter fun j => Column.idAt r.b r.w j == Column.idAt l.b l.w i).length := by
  obtain ⟨hK, hFn⟩ := groupIds_len r hrw hrs hrc
  obtain ⟨hcap, hγ⟩ := groupIds_groupOf r hrw hrs hrc
  have hKU : len r.groupIds.2 < USize.size := by rw [hK]; exact Nat.lt_of_le_of_lt hFn r.n.toNat_lt_size
  obtain ⟨hfl, hfv⟩ := join_hit l r hrw hrs hrc hlw hls
  have hv := hfv i hi
  have hcl := idxOf_class (Column.idAt r.b r.w) r.n.toNat (Column.idAt l.b l.w i)
  generalize hc : ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).idxOf
    (Column.idAt l.b l.w i) = c at hv hcl
  have hS := classSizes_ids r.n r.groupIds hKU
  have hsz : len (classSizes r.n r.groupIds) = len r.groupIds.2 := by rw [len_eq_ids, hS]; simp
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have hgb := (gatherBytes_spec (Nat.toUSize 8) (by rw [h8]; decide) 0 (classSizes r.n r.groupIds)
    ((r.gather r.groupIds.2).find l)).2 i (by have := hfl; simp only [len] at this; omega)
  rw [h8] at hgb
  unfold gather; rw [hgb, hv]
  by_cases hcF : c < (firstsOf (Column.idAt r.b r.w) r.n.toNat).length
  · -- a hit: the rows of class `c`, whose first row holds `l`'s code
    rw [if_pos (show c < (classSizes r.n r.groupIds).size / 8 by rw [show (classSizes r.n r.groupIds).size / 8 = len (classSizes r.n r.groupIds) from rfl, hsz, hK]; exact hcF),
      ids_get hS (by simp [hK, hcF])]
    simp only [List.getElem_map, List.getElem_range, idsW, hcap, List.countP_eq_length_filter, List.filter_map,
      List.length_map]
    congr 1
    refine List.filter_congr fun j hj => ?_
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_def, hγ j hj']
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact hcl.1 hcF j hj'
  · -- a miss: no row of `r` holds `l`'s code
    rw [if_neg (show ¬ c < (classSizes r.n r.groupIds).size / 8 by rw [show (classSizes r.n r.groupIds).size / 8 = len (classSizes r.n r.groupIds) from rfl, hsz, hK]; exact hcF)]
    rw [List.length_eq_zero_iff.2 (List.filter_eq_nil_iff.2 fun j hj => by
      simpa using hcl.2 (Nat.le_of_not_lt hcF) j (List.mem_range.1 hj))]
    simp

/-- `flatMap` over `range m` reads its function below `m` only. -/
theorem flatMap_range_congr {β : Type} {g g' : Nat → List β} {m : Nat} (h : ∀ t < m, g t = g' t) :
    (List.range m).flatMap g = (List.range m).flatMap g' := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih fun t ht => h t (by omega)]
    simp [h m (by omega)]

/-- **The classes below `K` count the rows of class below `K`**: summing, over `c < K`, the rows of `L`
    whose class `κ` is `c`. -/
theorem sum_filter_classes (κ : Nat → Nat) (L : List Nat) (K : Nat) :
    ((List.range K).map fun c => (L.filter fun i => κ i == c).length).sum =
      (L.filter fun i => decide (κ i < K)).length := by
  induction K with
  | zero => simp; exact (List.length_eq_zero_iff.2 (List.filter_eq_nil_iff.2 (by simp))).symm
  | succ K ih =>
    rw [sum_range_succ', ih]
    clear ih
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.filter_cons]
      by_cases h1 : κ x < K
      · have h2 : κ x < K + 1 := by omega
        have h3 : κ x ≠ K := by omega
        simp [h1, h2, h3]; omega
      · by_cases h3 : κ x = K
        · simp [h3]; omega
        · have h2 : ¬ κ x < K + 1 := by omega
          simp [h1, h2, h3]; omega

/-- **Each row `t` paired with its list `f t`, in turn, is the runs of `t` zipped with the lists end to
    end**: `A` is row `t` repeated `|f t|` times and `B` holds entry `q` of `f t` at `Σ_{s<t} |f s| + q`. -/
theorem zip_runs {β : Type} (f : Nat → List β) (m : Nat) {A : List Nat} {B : List β}
    (hA : A = (List.range m).flatMap fun t => List.replicate (f t).length t) (hB : B.length = A.length)
    (hb : ∀ t < m, ∀ q < (f t).length, B[((List.range t).map fun s => (f s).length).sum + q]? = (f t)[q]?) :
    A.zip B = (List.range m).flatMap fun t => (f t).map (t, ·) := by
  subst hA
  apply List.ext_getElem
  · rw [List.length_zip, hB, Nat.min_self]; simp [List.length_flatMap]
  · intro p h1 h2
    have hp : p < ((List.range m).map fun t => (List.replicate (f t).length t).length).sum := by
      rw [List.length_zip, hB, Nat.min_self, List.length_flatMap] at h1; exact h1
    obtain ⟨t, ht, s1, s2, s3⟩ := flatMap_get (fun t => List.replicate (f t).length t) m p hp
    simp only [List.length_replicate] at s1 s2 s3
    rw [List.getElem?_replicate, if_pos (by omega)] at s3
    obtain ⟨q, rfl⟩ : ∃ q, p = ((List.range t).map fun s => (f s).length).sum + q := ⟨_, (Nat.add_sub_cancel' s1).symm⟩
    have hq : q < (f t).length := by omega
    have r1 := flatMap_get_at (fun t => (f t).map (t, ·)) ht (by rw [List.length_map]; exact hq)
    simp only [List.length_map] at r1
    have eA := (List.getElem?_eq_some_iff.1 s3).2
    have eB := (List.getElem?_eq_some_iff.1 ((hb t ht q hq).trans (List.getElem?_eq_getElem hq))).2
    have eR := (List.getElem?_eq_some_iff.1 (r1.trans
      (show ((f t).map (t, ·))[q]? = some (t, (f t)[q]) by simp [hq]))).2
    rw [List.getElem_zip, eA, eB, eR]

/-- **`join l r`, read back**: the two index columns, zipped, are every left row `i` with each right row
    `j` holding its code, by `i` then `j`. Hypotheses: both codes at a lane with payloads of exactly their
    codes, `r`'s codes below its `card` (a `USize`) at `2`/`4` bits; `r`'s rows below `2^63` and the match
    count below `2^63` and a `USize`, so no long sum wraps and the pairs fit. -/
theorem join_spec (l r : Code)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hrn : r.n.toNat < 2 ^ 63)
    (hM : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < 2 ^ 63)
    (hMU : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < USize.size) :
    (ids (join l r).1).zip (ids (join l r).2) =
      (List.range l.n.toNat).flatMap fun i => ((List.range r.n.toNat).filter fun j =>
        Column.idAt r.b r.w j == Column.idAt l.b l.w i).map (i, ·) := by
  -- `f i`: the right rows matching left row `i`; `C c`: the right rows of class `c`
  obtain ⟨f, hf⟩ : ∃ f : Nat → List Nat, f = fun i => (List.range r.n.toNat).filter fun j =>
    Column.idAt r.b r.w j == Column.idAt l.b l.w i := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Nat → List Nat, C = fun c => (List.range r.n.toNat).filter fun j =>
    Verify.groupOf (Column.idAt r.b r.w) r.n.toNat j == c := ⟨_, rfl⟩
  have hM' : ((List.range l.n.toNat).map fun i => (f i).length).sum < 2 ^ 63 := by rw [hf]; exact hM
  have hMU' : ((List.range l.n.toNat).map fun i => (f i).length).sum < USize.size := by rw [hf]; exact hMU
  have hMr : ∀ i, (f i).length ≤ r.n.toNat := fun i => by
    rw [hf]; dsimp only; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact Nat.le_refl _)
  obtain ⟨hK, hFn⟩ := groupIds_len r hrw hrs hrc
  obtain ⟨hcap, hγ⟩ := groupIds_groupOf r hrw hrs hrc
  have hKn : len r.groupIds.2 ≤ r.n.toNat := hK ▸ hFn
  have hKU : len r.groupIds.2 < USize.size := Nat.lt_of_le_of_lt hKn r.n.toNat_lt_size
  have hκ : ∀ j < r.n.toNat, Verify.groupOf (Column.idAt r.b r.w) r.n.toNat j < len r.groupIds.2 :=
    fun j hj => hK ▸ groupOf_lt hj
  -- the class sizes
  have hids := classSizes_ids r.n r.groupIds hKU
  have hsl : len (classSizes r.n r.groupIds) = len r.groupIds.2 := by rw [len_eq_ids, hids]; simp
  have hS : ∀ c < len r.groupIds.2, (Column.bitsAt (classSizes r.n r.groupIds) (c * 8) 8).toNat = (C c).length :=
    fun c hc => by
      rw [ids_get hids (by simpa using hc), hC]
      simp only [List.getElem_map, List.getElem_range, idsW, hcap, List.countP_eq_length_filter, List.filter_map,
        List.length_map]
      congr 1
      exact List.filter_congr fun j hj => by simp only [Function.comp_def, hγ j (List.mem_range.1 hj)]
  have hSc : ∀ m ≤ len r.groupIds.2, ((List.range m).map fun c =>
      (Column.bitsAt (classSizes r.n r.groupIds) (c * 8) 8).toNat).sum = ((List.range m).map fun c => (C c).length).sum :=
    fun m hm => congrArg List.sum (List.map_congr_left fun c hc => hS c (by have := List.mem_range.1 hc; omega))
  have hCn : ((List.range (len r.groupIds.2)).map fun c => (C c).length).sum = r.n.toNat := by
    rw [hC]; dsimp only
    rw [sum_filter_classes, List.filter_eq_self.2 fun j hj => by simpa using hκ j (List.mem_range.1 hj),
      List.length_range]
  -- the grade of the class ids: the classes in turn
  have hsW : Column.idWidthOf (len r.groupIds.2) * r.n.toNat ≤ 8 * r.groupIds.1.size := by
    have h := hcap; unfold Column.idsCap at h
    by_cases h0 : Column.idWidthOf (len r.groupIds.2) = 0
    · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
    · rw [if_neg h0] at h
      have := Nat.min_le_right r.n.toNat (r.groupIds.1.size * 8 / Column.idWidthOf (len r.groupIds.2))
      rw [h] at this
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero h0)).1 this
      rw [Nat.mul_comm]; omega
  have hG : ids (Code.ofIds (len r.groupIds.2) r.n r.groupIds.1).grade = (List.range (len r.groupIds.2)).flatMap C := by
    rw [grade_ofIds _ _ _ (by omega) hsW (fun i hi => by rw [hγ i hi]; exact hκ i hi), hC]
    exact flatMap_range_congr fun c _ => List.filter_congr fun j hj => by rw [hγ j (List.mem_range.1 hj)]
  -- the hit and count columns
  obtain ⟨hfl, hv⟩ := join_hit l r hrw hrs hrc hlw hls
  have hcl : len (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l)) = l.n.toNat := by
    rw [gather_len, hfl]
  have hc : ∀ t < l.n.toNat, (Column.bitsAt (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l))
      (t * 8) 8).toNat = (f t).length := fun t ht => by rw [join_count l r hrw hrs hrc hlw hls ht, hf]
  have hcs : ∀ m ≤ l.n.toNat, ((List.range m).map fun t => (Column.bitsAt (gather 8 (classSizes r.n r.groupIds)
      ((r.gather r.groupIds.2).find l)) (t * 8) 8).toNat).sum = ((List.range m).map fun t => (f t).length).sum :=
    fun m hm => congrArg List.sum (List.map_congr_left fun t ht => hc t (by have := List.mem_range.1 ht; omega))
  -- the left column: row `t` repeated `|f t|` times
  have hA : ids (expandBytes 8 0 (tilLongs l.n) (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l))) =
      (List.range l.n.toNat).flatMap fun t => List.replicate (f t).length t := by
    rw [expand_idx (Nat.le_of_eq hcl) (fun t ht => by
      rw [hcl] at ht; rw [hc t ht]; exact Nat.lt_of_le_of_lt (hMr t) hrn), hcl]
    exact flatMap_range_congr fun t ht => by rw [hc t ht]
  have hLl : len (expandBytes 8 0 (tilLongs l.n) (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l))) =
      ((List.range l.n.toNat).map fun i => (f i).length).sum := by
    rw [len_eq_ids, hA, List.length_flatMap]; simp only [List.length_replicate]
  unfold join expand longCount; dsimp only; simp only [need]
  split
  next hli =>
    split
    next hns =>
      dsimp only
      have hm : (len (expandBytes 8 0 (tilLongs l.n) (gather 8 (classSizes r.n r.groupIds)
          ((r.gather r.groupIds.2).find l)))).toUSize.toNat = len (expandBytes 8 0 (tilLongs l.n)
          (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l))) := USize.toNat_ofNat_of_lt' hli
      have hn : (len (classSizes r.n r.groupIds)).toUSize.toNat = len r.groupIds.2 := by
        rw [USize.toNat_ofNat_of_lt' hns, hsl]
      generalize hlb : expandBytes 8 0 (tilLongs l.n) (gather 8 (classSizes r.n r.groupIds)
        ((r.gather r.groupIds.2).find l)) = li at hli hm hA hLl ⊢
      have hrk := fun {p : Nat} (hp : p < len (expandBytes 8 0 (tilLongs l.n) (gather 8 (classSizes r.n r.groupIds)
          ((r.gather r.groupIds.2).find l)))) =>
        expand_rank (Nat.le_of_eq hcl) (by rw [hcl, hcs _ (Nat.le_refl _)]; exact hM')
          (by rw [hlb, hLl]; exact hMU') hp
      rw [hlb] at hrk
      generalize hsz : classSizes r.n r.groupIds = sizes at hsl hS hSc hn hrk hcs ⊢
      generalize hht : (r.gather r.groupIds.2).find l = hit at hfl hv hrk hcs ⊢
      generalize hgr : (Code.ofIds (len r.groupIds.2) r.n r.groupIds.1).grade = G at hG ⊢
      refine (zip_runs f l.n.toNat hA ?_ ?_).trans (by rw [hf])
      · rw [← len_eq_ids, ← len_eq_ids, gather_len, add, len_val, hm]
      · intro t ht q hq
        have hst := sum_range_le (fun s => (f s).length) (show t + 1 ≤ l.n.toNat by omega)
        rw [sum_range_succ'] at hst
        generalize hSt : ((List.range t).map fun s => (f s).length).sum = St at hst ⊢
        have hpl : St + q < len li := by rw [hLl]; omega
        -- row `t` at position `St + q` of the left column, rank `q`
        have hli' : (Column.bitsAt li ((St + q) * 8) 8).toNat = t := by
          have e1 := flatMap_get_at (fun t => List.replicate (f t).length t) ht (by rw [List.length_replicate]; exact hq)
          simp only [List.length_replicate, hSt] at e1
          rw [List.getElem?_replicate, if_pos hq] at e1
          have hpA : St + q < ((List.range l.n.toNat).flatMap fun t => List.replicate (f t).length t).length := by
            rw [← hA, ← len_eq_ids]; exact hpl
          rw [ids_get hA hpA]; exact Option.some.inj ((List.getElem?_eq_getElem hpA).symm.trans e1)
        have hrq := hrk hpl
        rw [hli', hcs t (by omega), hSt, Nat.add_sub_cancel_left] at hrq
        -- the class `c` of row `t`'s code: a hit, since `f t` is not empty
        have hv' := hv t ht
        have hcls := idxOf_class (Column.idAt r.b r.w) r.n.toNat (Column.idAt l.b l.w t)
        generalize hcd : ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).idxOf
          (Column.idAt l.b l.w t) = c at hv' hcls
        have hcK : c < len r.groupIds.2 := by
          rw [hK]
          refine Nat.lt_of_not_le fun h => ?_
          have h0 : f t = [] := by
            rw [hf]; exact List.filter_eq_nil_iff.2 fun j hj => by simpa using hcls.2 h j (List.mem_range.1 hj)
          rw [h0] at hq; exact Nat.not_lt_zero _ hq
        have hCf : C c = f t := by
          rw [hC, hf]
          exact List.filter_congr fun j hj => by
            rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact hcls.1 (hK ▸ hcK) j (List.mem_range.1 hj)
        -- `starts[c]`: the rows of the classes before `c`
        have hqC : q < (C c).length := by rw [hCf]; exact hq
        have hsc := hSc (c + 1) (by omega)
        rw [sum_range_succ', sum_range_succ'] at hsc
        have hSc1 := hS c hcK
        have hSc0 := hSc c (by omega)
        have hcC := sum_range_le (fun c => (C c).length) (show c + 1 ≤ len r.groupIds.2 by omega)
        rw [sum_range_succ', hCn] at hcC
        have hsg := sums_get (n := (len sizes).toUSize) (b := sizes) (j := c) (by rw [hn]; exact hcK)
          (by rw [hsl]; exact hcK) (by rw [sum_range_succ']; omega)
        rw [sum_range_succ'] at hsg
        have hsub := sub_get (n := (len sizes).toUSize) (a := sums (len sizes).toUSize sizes) (b := sizes) (i := c)
          (by rw [hn]; exact hcK) (by rw [hsg]; omega) (by rw [hsg]; omega)
        rw [hsg, Nat.add_sub_cancel, hSc0] at hsub
        -- position `St + q` of the right index column: `starts[c] + q` into the grade
        have hh := gather8_get (src := hit) (idx := li) (j := St + q) hpl (by rw [hli', hfl]; exact ht)
        have hh' : (Column.bitsAt (gather 8 hit li) ((St + q) * 8) 8).toNat = c := by rw [hh, hli', hv']
        have hAp := gather8_get (src := sub (len sizes).toUSize (sums (len sizes).toUSize sizes) sizes)
          (idx := gather 8 hit li) (j := St + q) (by rw [gather_len]; exact hpl) (by rw [hh', sub, len_val, hn]; exact hcK)
        rw [hh'] at hAp
        have hadd := add_get (n := (len li).toUSize) (a := gather 8 (sub (len sizes).toUSize
          (sums (len sizes).toUSize sizes) sizes) (gather 8 hit li))
          (b := sub (len li).toUSize (tilLongs (len li).toUSize) (gather 8 (sub l.n (sums l.n
            (gather 8 sizes hit)) (gather 8 sizes hit)) li)) (i := St + q) (by rw [hm]; exact hpl)
          (by rw [hAp, hsub, hrq]; omega)
        rw [hAp, hsub, hrq] at hadd
        have hGl : len G = ((List.range (len r.groupIds.2)).map fun c => (C c).length).sum := by
          rw [len_eq_ids, hG, List.length_flatMap]
        have hidx : ((List.range c).map fun c => (C c).length).sum + q < (ids G).length := by
          rw [← len_eq_ids, hGl]; rw [← hCf] at hq; omega
        have hX := gather8_get (src := G) (idx := add (len li).toUSize (gather 8 (sub (len sizes).toUSize
          (sums (len sizes).toUSize sizes) sizes) (gather 8 hit li)) (sub (len li).toUSize (tilLongs (len li).toUSize)
            (gather 8 (sub l.n (sums l.n (gather 8 sizes hit)) (gather 8 sizes hit)) li))) (j := St + q)
          (by rw [add, len_val, hm]; exact hpl) (by rw [hadd, len_eq_ids]; exact hidx)
        rw [hadd] at hX
        have e2 := flatMap_get_at C hcK (show q < (C c).length by rw [hCf]; exact hq)
        have hpX : St + q < (gather 8 G (add (len li).toUSize (gather 8 (sub (len sizes).toUSize
            (sums (len sizes).toUSize sizes) sizes) (gather 8 hit li)) (sub (len li).toUSize (tilLongs (len li).toUSize)
            (gather 8 (sub l.n (sums l.n (gather 8 sizes hit)) (gather 8 sizes hit)) li)))).size / 8 := by
          show St + q < len _; rw [gather_len, add, len_val, hm]; exact hpl
        simp only [ids, List.getElem?_map, List.getElem?_range hpX, Option.map_some]
        rw [hX, ids_get hG (by rw [← hG]; exact hidx), ← hCf, ← e2, List.getElem?_eq_getElem]
    next hns => exact absurd (by rw [hsl]; exact hKU) hns
  next hli => exact absurd (by rw [hLl]; exact hMU') hli

#print axioms join_spec
#print axioms join_count
#print axioms join_hit
#print axioms idxOf_class
#print axioms groupIds_groupOf
#print axioms zip_runs
#print axioms sum_filter_classes

/-- **Every pair `join` answers is a row of each side**: a pair `(i, j)` of the list `join_spec` reads
    `join l r` back as has `i < a`, `j < b`, whatever the matching test `P`. -/
theorem join_pairs_lt {a b : Nat} {P : Nat → Nat → Bool} {p : Nat × Nat}
    (hp : p ∈ (List.range a).flatMap fun i => ((List.range b).filter (P i)).map (i, ·)) : p.1 < a ∧ p.2 < b := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range] at hp
  obtain ⟨i, hi, j, ⟨hj, -⟩, rfl⟩ := hp
  exact ⟨hi, hj⟩

#print axioms join_pairs_lt

end LeetQ.Rel.Alg
