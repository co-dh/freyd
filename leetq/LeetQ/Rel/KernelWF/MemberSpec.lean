/-
  What the membership kernels' answers CONTAIN, read off their Lean bodies: `Code.member` (bit `i` set
  exactly when code `i` of the needle is some code of the haystack), `whereBits` (the ascending set
  positions), `anti` (the positions whose code is absent), and `Code.groupIds` (one first row per distinct
  code, every class hit). A code is read as `Column.idAt c.b c.w i` at every lane: the bit at `1`
  (`idAt_one`), the packed id at `2`/`4`, the little-endian field at `8`…`64` (`resAt_lane`).
  A well-formed code is the hypothesis pair `w` a lane and `b` exactly `⌈n·w/8⌉` bytes.
-/
import LeetQ.Rel.KernelWF.Lane
import QLean.Verify.Where
import QLean.Verify.FindMember
import QLean.Verify.Elementwise
import QLean.Verify.Encoding
import QLean.Verify.Search
import QLean.Verify.Group

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel LeetQ.Rel
open QLean.Verify (firstsOf ids)

/-! ## Lanes -/

/-- A lane with no sort layout, among the lanes, is `2` or `4` bits. -/
theorem laneKind_none {w : Nat} (h : laneKind w = none)
    (hw : laneOK(w)) : w = 2 ∨ w = 4 := by
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [laneKind]

/-! ## `member` -/

/-- `memberIdsVec` of two well-formed codes: bit `i` of the needle set exactly when some haystack id is its id. -/
theorem memberIds_bit (x c : Code)
    (hxw : laneOK(x.w))
    (hcw : laneOK(c.w))
    (hxs : x.b.size = (x.n.toNat * x.w + 7) / 8) (hcs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    {i : Nat} (hi : i < x.n.toNat) :
    Column.bitAt (memberIdsVec x.w.toUSize x.b x.n c.w.toUSize c.b c.n) i = true ↔
      ∃ j < c.n.toNat, Column.idAt c.b c.w j = Column.idAt x.b x.w i := by
  have ex : x.w.toUSize.toNat = x.w := lane_toNat (by omega)
  have ec : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
  have fx : Column.idsCap x.b x.w x.n.toNat = x.n.toNat := idsCap_full (by omega) (by rw [Nat.mul_comm]; omega)
  have fc : Column.idsCap c.b c.w c.n.toNat = c.n.toNat := idsCap_full (by omega) (by rw [Nat.mul_comm]; omega)
  obtain ⟨-, hg⟩ := Verify.memberIdsVec_mem x.w.toUSize c.w.toUSize x.n c.n x.b c.b (by omega) (by omega)
  rw [ex, ec, fx, fc] at hg
  rw [hg i (by omega)]
  simp [hi, List.mem_map, List.mem_range]

/-- **`Code.member`'s bit `i`** (`i` below the needle count): set exactly when the needle's code `i` is some
    code of the haystack, both codes well formed. Every branch: `memberBits`, `memberVec`, `memberIdsVec`. -/
theorem member_bit (x c : Code)
    (hxw : laneOK(x.w))
    (hcw : laneOK(c.w))
    (hxs : x.b.size = (x.n.toNat * x.w + 7) / 8) (hcs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    {i : Nat} (hi : i < x.n.toNat) :
    Column.bitAt (x.member c) i = true ↔ ∃ j < c.n.toNat, Column.idAt c.b c.w j = Column.idAt x.b x.w i := by
  unfold Code.member Code.kind
  split
  · rename_i h1 h2
    have e1 : x.w = 1 := ((laneKind_some h1).resolve_right (by simp [Scan.Kind.width])).2
    have e2 : c.w = 1 := ((laneKind_some h2).resolve_right (by simp [Scan.Kind.width])).2
    obtain ⟨-, hg⟩ := Verify.memberBits_mem x.n c.n x.b c.b
    rw [hg i (by omega), e1, e2]
    simp only [hi, decide_true, Bool.true_and, decide_eq_true_eq, List.mem_map, List.mem_range, Verify.idAt_one]
    constructor
    · rintro ⟨j, hj, e⟩; exact ⟨j, hj, by rw [e]⟩
    · rintro ⟨j, hj, e⟩
      refine ⟨j, hj, ?_⟩
      revert e; cases Column.bitAt c.b j <;> cases Column.bitAt x.b i <;> simp
  · rename_i k k' hn hx hc
    split
    · rename_i hkk
      have hk : k = k' := by simpa using hkk
      subst hk
      rcases laneKind_some hx with ⟨rfl, -⟩ | ⟨-, e1, hq, hki⟩
      · exact (hn rfl rfl).elim
      have hk8 : k.width ≤ 8 := by omega
      have e2 : c.w = 8 * k.width := by
        rcases laneKind_some hc with ⟨rfl, -⟩ | ⟨-, e2, -⟩
        · exact (hn rfl rfl).elim
        · exact e2
      have hk0 : 0 < k.width := by rcases hki with rfl | rfl | rfl | rfl | rfl <;> decide
      have hwk := KernelWF.toNat_small k.width (by omega)
      have hxn : x.b.size / k.width = x.n.toNat := by
        rw [hxs, e1, show x.n.toNat * (8 * k.width) + 7 = 8 * (x.n.toNat * k.width) + 7 by
          rw [Nat.mul_left_comm]]
        rw [show (8 * (x.n.toNat * k.width) + 7) / 8 = x.n.toNat * k.width by omega]
        exact Nat.mul_div_cancel _ hk0
      have hcn : c.b.size / k.width = c.n.toNat := by
        rw [hcs, e2, show c.n.toNat * (8 * k.width) + 7 = 8 * (c.n.toNat * k.width) + 7 by
          rw [Nat.mul_left_comm]]
        rw [show (8 * (c.n.toNat * k.width) + 7) / 8 = c.n.toNat * k.width by omega]
        exact Nat.mul_div_cancel _ hk0
      obtain ⟨-, hg⟩ := Verify.memberVec_mem k.width.toUSize false x.b c.b
        (by rw [hwk, hcn]; exact c.n.toNat_lt_size)
      rw [hwk, hxn] at hg
      rw [hg i (by omega), if_pos hk8, e1, e2]
      simp only [idAt_lane _ hk8, hi, decide_true, Bool.true_and, decide_eq_true_eq, Verify.elemsW, hcn, List.map_map,
        List.mem_map, List.mem_range, Function.comp_def, Kernel.normalise, Bool.not_false, if_true]
      constructor
      · rintro ⟨j, hj, e⟩; exact ⟨j, hj, by rw [e]⟩
      · rintro ⟨j, hj, e⟩; exact ⟨j, hj, UInt64.toNat_inj.1 e⟩
    · exact memberIds_bit x c hxw hcw hxs hcs hi
  · exact memberIds_bit x c hxw hcw hxs hcs hi

/-! ## `whereBits` and `anti` -/

/-- **`whereBits n b`, read back**: the ascending list of the positions below `n` whose bit is set. -/
theorem whereBits_ids (n : USize) (b : ByteArray) :
    ids (whereBits n b) = (List.range n.toNat).filter (Column.bitAt b) ∧
      ((List.range n.toNat).filter (Column.bitAt b)).Pairwise (· < ·) ∧
      ∀ i, i ∈ (List.range n.toNat).filter (Column.bitAt b) ↔ i < n.toNat ∧ Column.bitAt b i = true := by
  obtain ⟨hs, hg⟩ := Verify.whereBits_spec n b
  obtain ⟨hp, hm⟩ := Verify.whereBits_indices n.toNat b
  refine ⟨List.ext_getElem (by simp [ids, hs]) fun j _ h2 => ?_, hp, hm⟩
  simp only [ids, List.getElem_map, List.getElem_range]
  exact hg j h2

/-- `Ew.notBits` flips each of the first `m` bits. -/
theorem notBits_bitAt (m : USize) (b : ByteArray) {i : Nat} (hi : i < m.toNat) :
    Column.bitAt (Ew.notBits m b) i = !Column.bitAt b i := by
  obtain ⟨-, hg⟩ := Verify.Ew.bit_bitAt (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m
  simp only [Ew.notBits]
  rw [hg i (by omega)]
  simp only [hi, decide_true, Bool.true_and, Ew.shapeIdx]
  have h1 : Column.bitAt ⟨#[1]⟩ 0 = true := by decide
  simp only [show (Ew.av == Ew.vv) = false by decide, show (Ew.av == Ew.va) = false by decide,
    Bool.false_eq_true, ite_false, h1]
  generalize Column.bitAt b i = y
  cases y <;> decide

/-- **`anti x y`, read back**: the ascending positions of `x` whose code is no code of `y`, both well formed. -/
theorem anti_ids (x y : Code)
    (hxw : laneOK(x.w))
    (hyw : laneOK(y.w))
    (hxs : x.b.size = (x.n.toNat * x.w + 7) / 8) (hys : y.b.size = (y.n.toNat * y.w + 7) / 8) :
    ids (anti x y) = (List.range x.n.toNat).filter (fun i => !Column.bitAt (x.member y) i) ∧
      ((List.range x.n.toNat).filter (fun i => !Column.bitAt (x.member y) i)).Pairwise (· < ·) ∧
      ∀ i, i ∈ ids (anti x y) ↔
        i < x.n.toNat ∧ ¬ ∃ j < y.n.toNat, Column.idAt y.b y.w j = Column.idAt x.b x.w i := by
  obtain ⟨he, hp, hm⟩ := whereBits_ids x.n (Ew.notBits x.n (x.member y))
  have hf : (List.range x.n.toNat).filter (Column.bitAt (Ew.notBits x.n (x.member y))) =
      (List.range x.n.toNat).filter (fun i => !Column.bitAt (x.member y) i) :=
    List.filter_congr fun i hi => notBits_bitAt _ _ (List.mem_range.1 hi)
  have ha : ids (anti x y) = (List.range x.n.toNat).filter (fun i => !Column.bitAt (x.member y) i) := by
    simp only [anti]; rw [he, hf]
  refine ⟨ha, hf ▸ hp, fun i => ?_⟩
  rw [ha, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun hx => ?_⟩
    rw [(member_bit x y hxw hyw hxs hys hi).2 hx] at h; exact Bool.false_ne_true h
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    cases hb : Column.bitAt (x.member y) i
    · rfl
    · exact absurd ((member_bit x y hxw hyw hxs hys hi).1 hb) h

/-! ## `groupIds` -/

/-- **`Code.groupIds`' second component, read back**: the first row of each distinct code, ascending, the
    code read at its lane. At `2`/`4` bits `idGroups` reads `card` as a table size, so there every code is
    below `card` and `card` fits a `USize`. -/
theorem groupIds_firsts (c : Code)
    (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    ids c.groupIds.2 = firstsOf (Column.idAt c.b c.w) c.n.toNat := by
  unfold Code.groupIds Code.kind
  split
  · rename_i k hk
    rw [(Verify.groupIds_spec k c.n c.b).2]
    rcases laneKind_some hk with ⟨rfl, e⟩ | ⟨-, e, hq, hki⟩
    · have hm : min c.n.toNat (Scan.Kind.avail .bit c.b) = c.n.toNat := by
        simp only [Scan.Kind.avail, hs, e]; omega
      rw [hm, e]
      refine (Verify.groups_congr _ _ fun i _ j _ => ?_).1
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
      rw [hm, e]
      refine (Verify.groups_congr _ _ fun i _ j _ => ?_).1
      rw [Verify.keyAt_eq_iff hki, idAt_lane _ hk8, idAt_lane _ hk8]
      exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.1 h⟩
  · rename_i hk
    have h24 := laneKind_none hk hw
    obtain ⟨hcU, hlt⟩ := hcard (by omega)
    have hd : c.card.toUSize.toNat = c.card := USize.toNat_ofNat_of_lt' hcU
    have hwn : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    simp only [Order.idGroups]
    rw [Verify.ids_indices _ fun i hi => by
      have : i < c.n.toNat := List.mem_range.1 (List.mem_filter.1 hi).1
      exact Nat.lt_trans this (Verify.usize_lt c.n), hd, hwn]
    have hb : ∀ a e : Nat, (a != e) = !decide (a = e) := fun a e => by
      cases h : decide (a = e) <;> simp_all
    have hF : Order.idFirsts c.card c.n.toNat c.w c.b = firstsOf (Order.idKey c.card c.b c.w) c.n.toNat := by
      simp only [Order.idFirsts, firstsOf, hb]
    rw [hF]
    refine (Verify.groups_congr _ _ fun i hi j hj => ?_).1
    simp only [Order.idKey, Nat.min_eq_left (Nat.le_of_lt (hlt i hi)), Nat.min_eq_left (Nat.le_of_lt (hlt j hj))]

/-- **`Code.groupIds` names one row per class**: every first row is a row, no two first rows hold one code,
    and every row's code is held by a first row (`groupIds_firsts`). -/
theorem groupIds_classes (c : Code)
    (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    (∀ f ∈ ids c.groupIds.2, f < c.n.toNat) ∧ ((ids c.groupIds.2).map (Column.idAt c.b c.w)).Nodup ∧
      ∀ i < c.n.toNat, ∃ f ∈ ids c.groupIds.2, Column.idAt c.b c.w f = Column.idAt c.b c.w i := by
  rw [groupIds_firsts c hw hs hcard]
  exact ⟨fun f hf => Verify.firsts_lt _ _ hf, Verify.nodup_firsts _ _, fun i hi => Verify.exists_first hi⟩

/-- info: 'LeetQ.Rel.Alg.member_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms member_bit
/-- info: 'LeetQ.Rel.Alg.whereBits_ids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms whereBits_ids
/-- info: 'LeetQ.Rel.Alg.anti_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms anti_ids
/-- info: 'LeetQ.Rel.Alg.groupIds_classes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms groupIds_classes

end LeetQ.Rel.Alg
