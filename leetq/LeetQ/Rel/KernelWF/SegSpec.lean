/-
  `segments c`, read back: the permutation lists the rows class by class (the classes of `Code.groupIds`, in
  first-occurrence order, each ascending), the offsets are the running totals of the class sizes, and the
  firsts are `groupIds`' first rows. The offsets come from `code_runs` on the class ids read along the
  permutation; `runs_prefix` says that runs of a column cut into consecutive nonempty classes are those classes.
-/
import LeetQ.Rel.KernelWF.RunSpec
import LeetQ.Rel.KernelWF.JoinAssembly

open LaneN

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.KernelWF
open QLean.Verify (ids)

/-- Running totals `P` of nonempty classes ascend strictly. -/
theorem prefix_lt {K : Nat} {P : Nat → Nat} (hPs : ∀ t < K, P t < P (t + 1)) :
    ∀ a b, a < b → b ≤ K → P a < P b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hab) with h | rfl
    · exact Nat.lt_trans (ih h (by omega)) (hPs b (by omega))
    · exact hPs a (by omega)

/-- A column `κ` that is class `t` exactly on `[P t, P (t+1))` keeps equal values together. -/
theorem prefix_cont {n K : Nat} {P κ : Nat → Nat} (hPs : ∀ t < K, P t < P (t + 1))
    (hloc : ∀ s < n, ∃ t < K, κ s = t ∧ P t ≤ s ∧ s < P (t + 1)) :
    ∀ s t u, s ≤ t → t ≤ u → u < n → κ s = κ u → κ t = κ s := by
  have hle : ∀ a b, a ≤ b → b ≤ K → P a ≤ P b := fun a b hab hb => by
    rcases Nat.lt_or_eq_of_le hab with h | rfl
    · exact Nat.le_of_lt (prefix_lt hPs a b h hb)
    · exact Nat.le_refl _
  intro s t u hst htu hu e
  obtain ⟨a, ha, ea, a1, a2⟩ := hloc s (by omega)
  obtain ⟨b, hb, eb, b1, b2⟩ := hloc t (by omega)
  obtain ⟨c, hc, ec, c1, c2⟩ := hloc u hu
  rw [ea, eb]; rw [ea, ec] at e; subst e
  rcases Nat.lt_trichotomy b a with h | h | h
  · have := hle (b + 1) a (by omega) (by omega); omega
  · exact h
  · have := hle (a + 1) b (by omega) (by omega); omega

/-- **The runs of a column cut into consecutive nonempty classes are the classes**: where `κ` is class `t`
    exactly on `[P t, P (t+1))` (`P 0 = 0`, `P K = n`, each class nonempty), the run starts `o` that
    `code_runs` describes are `P 0, …, P K`, `K` runs. -/
theorem runs_prefix {n K m : Nat} {P κ o : Nat → Nat} (hP0 : P 0 = 0) (hPs : ∀ t < K, P t < P (t + 1))
    (hPK : P K = n) (hloc : ∀ s < n, ∃ t < K, κ s = t ∧ P t ≤ s ∧ s < P (t + 1))
    (hlast : o m = n) (hasc : ∀ i j, i < j → j ≤ m → o i < o j)
    (hrun : ∀ s j, s < n → j < m → (κ s = κ (o j) ↔ o j ≤ s ∧ s < o (j + 1)))
    (hcov : ∀ s, s < n → ∃ j, j < m ∧ o j ≤ s ∧ s < o (j + 1)) :
    m = K ∧ ∀ j ≤ K, o j = P j := by
  have hmono := prefix_lt hPs
  have hle : ∀ a b, a ≤ b → b ≤ K → P a ≤ P b := fun a b hab hb => by
    rcases Nat.lt_or_eq_of_le hab with h | rfl
    · exact Nat.le_of_lt (hmono a b h hb)
    · exact Nat.le_refl _
  have hinj : ∀ a b, a ≤ K → b ≤ K → P a = P b → a = b := fun a b ha hb e => by
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := hmono a b h hb; omega
    · exact h
    · have := hmono b a h ha; omega
  -- a run is a class: its ends are the class's
  have hend : ∀ j < m, κ (o j) < K ∧ o j = P (κ (o j)) ∧ o (j + 1) = P (κ (o j) + 1) := by
    intro j hj
    have hoj : o j < n := by have := hasc j m hj (Nat.le_refl _); omega
    have hoj1 : o (j + 1) ≤ n := by
      rcases Nat.lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
      · have := hasc _ m h (Nat.le_refl _); omega
      · rw [h, hlast]; exact Nat.le_refl _
    have hj1 : o j < o (j + 1) := hasc j (j + 1) (by omega) (by omega)
    obtain ⟨t, ht, et, -, -⟩ := hloc (o j) hoj
    have ht1 : P (t + 1) ≤ n := hPK ▸ hle (t + 1) K (by omega) (Nat.le_refl _)
    have hpt : P t < P (t + 1) := hPs t ht
    have hiff : ∀ s < n, (P t ≤ s ∧ s < P (t + 1)) ↔ (o j ≤ s ∧ s < o (j + 1)) := fun s hs => by
      rw [← hrun s j hs hj, et]
      obtain ⟨t', ht', et', h1, h2⟩ := hloc s hs
      rw [et']
      constructor
      · intro ⟨a, b⟩
        rcases Nat.lt_trichotomy t' t with h | h | h
        · have := hle (t' + 1) t (by omega) (by omega); omega
        · exact h
        · have := hle (t + 1) t' (by omega) (by omega); omega
      · intro h; rw [← h]; exact ⟨h1, h2⟩
    have a1 := (hiff (o j) hoj).2 ⟨Nat.le_refl _, hj1⟩
    have a2 := (hiff (P t) (by omega)).1 ⟨Nat.le_refl _, hpt⟩
    have a3 := (hiff (o (j + 1) - 1) (by omega)).2 ⟨by omega, by omega⟩
    have a4 := (hiff (P (t + 1) - 1) (by omega)).1 ⟨by omega, by omega⟩
    rw [et]
    exact ⟨ht, by omega, by omega⟩
  have hid : ∀ j < m, κ (o j) = j := by
    intro j
    induction j with
    | zero =>
      intro hm
      obtain ⟨-, e0, -⟩ := hend 0 hm
      have hn : 0 < n := by have := hasc 0 m hm (Nat.le_refl _); omega
      obtain ⟨j', hj', h1, -⟩ := hcov 0 hn
      have ho : o 0 = 0 := by
        rcases Nat.eq_zero_or_pos j' with rfl | h
        · omega
        · have := hasc 0 j' h (by omega); omega
      rcases Nat.eq_zero_or_pos (κ (o 0)) with h | h
      · exact h
      · have := hmono 0 _ h (by have := (hend 0 hm).1; omega); omega
    | succ j ih =>
      intro hm
      have e1 := ih (by omega)
      have hjK : j < K := by have := (hend j (by omega)).1; omega
      obtain ⟨-, -, e2⟩ := hend j (by omega)
      obtain ⟨ht, e3, -⟩ := hend (j + 1) hm
      rw [e1] at e2
      exact hinj _ _ (by omega) (by omega) (e3.symm.trans e2)
  have hmK : m = K := by
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · rcases Nat.eq_zero_or_pos K with hK | hK
      · omega
      · have := hmono 0 K hK (Nat.le_refl _)
        obtain ⟨j, hj, -⟩ := hcov 0 (by omega)
        omega
    · obtain ⟨-, -, e⟩ := hend (m - 1) (by omega)
      have h1 := hid (m - 1) (by omega)
      have h2 := (hend (m - 1) (by omega)).1
      rw [h1, show m - 1 + 1 = m by omega, hlast] at e
      exact hinj m K (by omega) (Nat.le_refl _) (e.symm.trans hPK.symm)
  refine ⟨hmK, fun j hj => ?_⟩
  rcases Nat.lt_or_eq_of_le hj with h | h
  · obtain ⟨-, e, -⟩ := hend j (by omega)
    rw [e, hid j (by omega)]
  · rw [h, ← hmK, hlast, hmK, hPK]

/-- **`Code.groupIds`' class ids are packed**: `groupOf` of the codes, at the width of the class count — the
    grouping pass at each layout (`groupIds_spec`) and `idGroups` at `2`/`4` bits. Hypotheses as
    `groupIds_firsts`. -/
theorem groupIds_packed (c : Code)
    (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    c.groupIds.1 = Column.packIds (Column.idWidthOf (Verify.firstsOf (Column.idAt c.b c.w) c.n.toNat).length)
      c.n.toNat (Verify.groupOf (Column.idAt c.b c.w) c.n.toNat) := by
  -- a key that agrees exactly where the codes do groups alike
  have hcg : ∀ {β : Type} [DecidableEq β] (key : Nat → β),
      (∀ i < c.n.toNat, ∀ j < c.n.toNat, (key i = key j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) →
      Column.packIds (Column.idWidthOf (Verify.firstsOf key c.n.toNat).length) c.n.toNat
          (Verify.groupOf key c.n.toNat) =
        Column.packIds (Column.idWidthOf (Verify.firstsOf (Column.idAt c.b c.w) c.n.toNat).length) c.n.toNat
          (Verify.groupOf (Column.idAt c.b c.w) c.n.toNat) := fun key h => by
    obtain ⟨h1, -, h3⟩ := Verify.groups_congr key c.n.toNat h
    rw [h1]; exact Verify.packIds_congr _ _ h3
  unfold Code.groupIds Code.kind
  split
  · rename_i k hk
    rw [(Verify.groupIds_spec k c.n c.b).1]
    rcases laneKind_some hk with ⟨rfl, e⟩ | ⟨-, e, hq, hki⟩
    · have hm : min c.n.toNat (Scan.Kind.avail .bit c.b) = c.n.toNat := by
        simp only [Scan.Kind.avail, hs, e]; omega
      rw [hm]
      refine hcg _ fun i _ j _ => ?_
      rw [e]
      simp only [Order.keyAt, Order.rank, Scan.Kind.bitsAt, Verify.idAt_one]
      cases Column.bitAt c.b i <;> cases Column.bitAt c.b j <;> decide
    · have hk0 : 0 < k.width := by rcases hki with rfl | rfl | rfl | rfl | rfl <;> decide
      have hk8 : k.width ≤ 8 := by omega
      have hav : Scan.Kind.avail k c.b = c.b.size / k.width := by
        rcases hki with rfl | rfl | rfl | rfl | rfl <;> rfl
      have hm : min c.n.toNat (Scan.Kind.avail k c.b) = c.n.toNat := by
        rw [hav, hs, e, show c.n.toNat * (8 * k.width) + 7 = 8 * (c.n.toNat * k.width) + 7 by
          rw [Nat.mul_left_comm], show (8 * (c.n.toNat * k.width) + 7) / 8 = c.n.toNat * k.width by omega,
          Nat.mul_div_cancel _ hk0, Nat.min_self]
      rw [hm]
      refine hcg _ fun i _ j _ => ?_
      rw [e, Verify.keyAt_eq_iff hki, idAt_lane _ hk8, idAt_lane _ hk8]
      exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.1 h⟩
  · rename_i hk
    have h24 := laneKind_none hk hw
    obtain ⟨hcU, hlt⟩ := hcard (by omega)
    have hd : c.card.toUSize.toNat = c.card := USize.toNat_ofNat_of_lt' hcU
    have hwn : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    have hb : ∀ a e : Nat, (a != e) = !decide (a = e) := fun a e => by
      cases h : decide (a = e) <;> simp_all
    have hF : Order.idFirsts c.card c.n.toNat c.w c.b = Verify.firstsOf (Order.idKey c.card c.b c.w) c.n.toNat := by
      simp only [Order.idFirsts, Verify.firstsOf, hb]
    simp only [Order.idGroups, hd, hwn, hF]
    refine (Verify.packIds_congr _ _ fun i _ => ?_).trans (hcg (Order.idKey c.card c.b c.w) fun i hi j hj => ?_)
    · simp only [Verify.groupOf]; congr 1
    · simp only [Order.idKey, Nat.min_eq_left (Nat.le_of_lt (hlt i hi)), Nat.min_eq_left (Nat.le_of_lt (hlt j hj))]

/-! `segments`' classes, one home: `open SegN` in every file that reads `segments` back. -/
namespace SegN
-- the first rows of `c`'s classes, by first occurrence
set_option hygiene false in
scoped notation "F(" c ")" => Verify.firstsOf (Column.idAt (Code.b c) (Code.w c)) (USize.toNat (Code.n c))
-- the rows of class `t` of `c`, ascending
set_option hygiene false in
scoped notation "cls(" c ", " t ")" => (List.range (USize.toNat (Code.n c))).filter fun i =>
  Verify.groupOf (Column.idAt (Code.b c) (Code.w c)) (USize.toNat (Code.n c)) i == t
-- the number of rows in the classes before `j`
set_option hygiene false in
scoped notation "pre(" c ", " j ")" => List.sum (List.map (fun t => List.length (cls(c, t))) (List.range j))
end SegN
open SegN

/-- **`segments c`, read back**: its firsts are `groupIds`' first rows; its permutation lists the rows class
    by class, classes in first-occurrence order, each ascending; its offsets are `K + 1` longs, offset `j` the
    number of rows in the classes before `j` (so the last is `n`). Hypotheses: `c` well formed, as
    `groupIds_firsts`; `n ≤ 2^63` (`grade_ofIds`). -/
theorem segments_spec (c : Code)
    (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)
    (h63 : c.n.toNat ≤ 2 ^ 63) :
    ids (segments c).2.2 = F(c) ∧
      ids (segments c).1 = (List.range (F(c)).length).flatMap (fun t => cls(c, t)) ∧
      (segments c).2.1.size = 8 * ((F(c)).length + 1) ∧
      ∀ j ≤ (F(c)).length, (Column.bitsAt (segments c).2.1 (j * 8) 8).toNat = pre(c, j) := by
  obtain ⟨hK, hKn⟩ := groupIds_len c hw hs hcard
  obtain ⟨hcap, hγ⟩ := groupIds_groupOf c hw hs hcard
  have hF := groupIds_firsts c hw hs hcard
  have hκ : ∀ j < c.n.toNat, Verify.groupOf (Column.idAt c.b c.w) c.n.toNat j < (F(c)).length :=
    fun j hj => Verify.groupOf_lt hj
  obtain ⟨g, hg⟩ : ∃ g, g = Code.ofIds (len c.groupIds.2) c.n c.groupIds.1 := ⟨_, rfl⟩
  have hseg : segments c = (g.grade, (g.gather g.grade).runStarts, c.groupIds.2) := by subst hg; rfl
  rw [hseg]; dsimp only
  -- the grade of the class ids: the classes in turn
  have hsW : Column.idWidthOf (len c.groupIds.2) * c.n.toNat ≤ 8 * c.groupIds.1.size := by
    have h := hcap; unfold Column.idsCap at h
    by_cases h0 : Column.idWidthOf (len c.groupIds.2) = 0
    · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
    · rw [if_neg h0] at h
      have := Nat.min_le_right c.n.toNat (c.groupIds.1.size * 8 / Column.idWidthOf (len c.groupIds.2))
      rw [h] at this
      have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero h0)).1 this
      rw [Nat.mul_comm]; omega
  have hP : ids g.grade = (List.range (F(c)).length).flatMap fun t => cls(c, t) := by
    rw [hg, grade_ofIds _ _ _ (by omega) hsW (fun i hi => by rw [hγ i hi, hK]; exact hκ i hi), hK]
    rw [hK] at hγ
    exact flatMap_range_congr fun t _ => List.filter_congr fun j hj => by rw [hγ j (List.mem_range.1 hj)]
  -- the class ids as a code: well formed, reading `groupOf`
  have hwf := ofIds_packIds c.n hKn (Verify.groupOf (Column.idAt c.b c.w) c.n.toNat)
    (fun i hi => Verify.groupOf_lt hi) hK
  dsimp only at hwf
  rw [← groupIds_packed c hw hs hcard, ← hg] at hwf
  obtain ⟨⟨gw, gn, gs, -⟩, gread⟩ := hwf
  have hperm : (ids g.grade).Perm (List.range c.n.toNat) := by
    have := (grade_code g gw gs).1; rwa [gn] at this
  have hlen : len g.grade = c.n.toNat := by rw [len_eq_ids, hperm.length_eq, List.length_range]
  have hl : len g.grade < USize.size := by rw [hlen]; exact c.n.toNat_lt_size
  have hpl : ∀ j < len g.grade, (Column.bitsAt g.grade (j * 8) 8).toNat < g.n.toNat := fun j hj => by
    have hj' : j < (ids g.grade).length := by rw [← len_eq_ids]; exact hj
    rw [← ids_getElem hj', gn]; exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hj'))
  have hcb : 8 ≤ g.w → 8 * g.b.size = g.w * g.n.toNat := fun h8 => by
    rcases gw with h | h | h | h | h | h | h <;> rw [h] at gs ⊢ <;> omega
  obtain ⟨Gw, Gn, -, Gid⟩ := gather_spec g g.grade hl gw hcb hpl
  have Gs := gather_size g g.grade hl gw
  generalize hG : g.gather g.grade = G at Gw Gn Gid Gs ⊢
  -- the class at each position of the permutation
  have hsum : ((List.range (F(c)).length).map fun t => (cls(c, t)).length).sum = c.n.toNat := by
    rw [sum_filter_classes, List.filter_eq_self.2 fun j hj => by simpa using hκ j (List.mem_range.1 hj),
      List.length_range]
  have hne : ∀ t < (F(c)).length, 0 < (cls(c, t)).length := fun t ht => by
    have hf := Verify.firsts_lt _ _ (List.getElem_mem ht)
    refine List.length_pos_of_mem (a := (F(c))[t]) ?_
    simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨hf, (Verify.groupOf_eq_iff hf ht).2 rfl⟩
  have hloc : ∀ s < c.n.toNat, ∃ t < (F(c)).length,
      Column.idAt G.b G.w s = t ∧ pre(c, t) ≤ s ∧ s < pre(c, t + 1) := by
    intro s hs'
    obtain ⟨t, ht, h1, h2, h3⟩ := flatMap_get (fun t => cls(c, t)) (F(c)).length s (by rw [hsum]; exact hs')
    have hsl : s < (ids g.grade).length := by rw [hperm.length_eq, List.length_range]; exact hs'
    rw [← hP, List.getElem?_eq_getElem hsl, ids_getElem hsl] at h3
    have hm := List.mem_of_getElem? h3.symm
    simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hm
    refine ⟨t, ht, ?_, h1, by rw [sum_range_succ']; exact h2⟩
    rw [Gw, Gid s (by rw [hlen]; exact hs'), gread _ hm.1]
    exact hm.2
  have hPs : ∀ t < (F(c)).length, pre(c, t) < pre(c, t + 1) := fun t ht => by
    rw [sum_range_succ']; have := hne t ht; omega
  have hR := code_runs G (by rw [Gw]; exact gw) (by rw [Gs, Gn, Gw])
    (by rw [Gn, hlen]; exact prefix_cont hPs hloc)
  rw [Gn, hlen] at hR
  obtain ⟨m, hsz, hlast, hasc, -, hrun, hcov⟩ := hR
  obtain ⟨hmK, ho⟩ := runs_prefix (P := fun j => pre(c, j)) (κ := fun s => Column.idAt G.b G.w s)
    (o := fun j => (Column.bitsAt G.runStarts (j * 8) 8).toNat) (by simp) hPs hsum hloc hlast hasc hrun hcov
  refine ⟨hF, hP, ?_, ho⟩
  rw [hsz, hmK]

#print axioms prefix_lt
#print axioms prefix_cont
#print axioms runs_prefix
#print axioms groupIds_packed
#print axioms segments_spec

end LeetQ.Rel.Alg
