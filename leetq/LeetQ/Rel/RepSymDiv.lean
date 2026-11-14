/-
  The symmetric division of `Rel`, read back. `symDiv R S Ua Ub` cuts `R`'s rows and `S`'s rows into key classes
  (`segments`), numbers the classes by their sets of value codes in one `setIds` call, joins `R`'s class ids with
  `S`'s, and reads each matching pair's keys at the classes' first rows (`hit`); then adds `⊤` on the elements of
  `Ua` that are no key of `R` and the elements of `Ub` that are no key of `S`.
-/
import LeetQ.Rel.RepDiv
import LeetQ.Rel.KernelWF.SetIdsSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

/-- Long `k` of a byte extract is long `lo/8 + k` of the whole, where the extract holds it. -/
theorem bitsAt_extract (b : ByteArray) {lo hi k : Nat} (h : lo + k * 8 + 8 ≤ hi) (hb : hi ≤ b.size) :
    Column.bitsAt (b.extract lo hi) (k * 8) 8 = Column.bitsAt b (lo + k * 8) 8 :=
  bitsAt_shift _ _ _ _ _ fun j hj => by
    show (b.extract lo hi).data[k * 8 + j]? = b.data[lo + k * 8 + j]?
    rw [ByteArray.data_extract, Array.getElem?_extract, ByteArray.size_data, if_pos (by omega), Nat.add_assoc]

/-- **`concatBytes #[a, b]` read back**: `a`'s `m` longs, then `b`'s. -/
theorem concat_two (a b : ByteArray) {m : Nat} (ha : a.size = 8 * m) :
    (concatBytes #[a, b]).size = a.size + b.size ∧
      (∀ j < m, Column.bitsAt (concatBytes #[a, b]) (j * 8) 8 = Column.bitsAt a (j * 8) 8) ∧
      ∀ t, t * 8 + 8 ≤ b.size → Column.bitsAt (concatBytes #[a, b]) ((m + t) * 8) 8 = Column.bitsAt b (t * 8) 8 := by
  have e : concatBytes #[a, b] = (ByteArray.empty ++ a) ++ b := rfl
  have hX : (ByteArray.empty ++ a).size = 8 * m := by rw [ByteArray.size_append]; simp [ha]
  rw [e]
  refine ⟨by rw [ByteArray.size_append, hX, ha], fun j hj => bitsAt_shift _ _ _ _ _ fun k hk => ?_,
    fun t ht => bitsAt_shift _ _ _ _ _ fun k hk => ?_⟩
  · rw [ba_append_left _ _ _ (by rw [hX]; omega), ba_append_right' _ _ _ (by simp)]; simp
  · rw [show (m + t) * 8 + k = (ByteArray.empty ++ a).size + (t * 8 + k) by rw [hX]; omega, ba_append_right]

-- the number of entries of the lists `g s`, `s < t`
set_option quotPrecheck false in
local notation "pg(" g ", " t ")" => ((List.range t).map fun s => (List.length (g s))).sum

/-- **A block of a column laid out class by class**: where positions `o + x` of `G` read `φ` at entry `x` of the
    classes `g 0, g 1, …` end to end, the positions of class `t` read exactly `φ` of class `t`'s entries. -/
theorem block_slice (g : Nat → List Nat) {K t : Nat} (ht : t < K) (G φ : Nat → Nat) (o : Nat)
    (hG : ∀ x < pg(g, K), G (o + x) = φ ((((List.range K).flatMap g)[x]?).getD 0)) (u : Nat) :
    (∃ i, o + pg(g, t) ≤ i ∧ i < o + pg(g, t + 1) ∧ G i = u) ↔ ∃ a ∈ g t, φ a = u := by
  have hle := sum_range_le (fun s => (g s).length) (show t + 1 ≤ K by omega)
  rw [sum_range_succ'] at hle ⊢
  constructor
  · rintro ⟨i, h1, h2, rfl⟩
    obtain ⟨q, rfl⟩ : ∃ q, i = o + (pg(g, t) + q) := ⟨i - o - pg(g, t), by omega⟩
    have hq : q < (g t).length := by omega
    rw [hG _ (by omega), flatMap_get_at g ht hq, List.getElem?_eq_getElem hq, Option.getD_some]
    exact ⟨_, List.getElem_mem hq, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem ha
    refine ⟨o + (pg(g, t) + q), by omega, by omega, ?_⟩
    rw [hG _ (by omega), flatMap_get_at g ht hq, List.getElem?_eq_getElem hq, Option.getD_some]

-- `segments_spec`'s `F`, `cls`, `pre`, and `setIds_spec`'s `T`
open Alg.SegN

/-- **`segments c` as `symDiv` reads it**: `segments_spec`, plus the classes cover the `n` rows, and class `t`
    is the rows whose code is that of its first row. Hypotheses: `segments_spec`'s. -/
theorem seg_facts (c : Code) (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)
    (h63 : c.n.toNat ≤ 2 ^ 63) {p o f : ByteArray} (he : segments c = (p, o, f)) :
    ids f = F(c) ∧ ids p = (List.range (F(c)).length).flatMap (fun t => cls(c, t)) ∧
      o.size = 8 * ((F(c)).length + 1) ∧ (∀ j ≤ (F(c)).length, (Column.bitsAt o (j * 8) 8).toNat = pre(c, j)) ∧
      pre(c, (F(c)).length) = c.n.toNat ∧
      ∀ t < (F(c)).length, ∀ a, a ∈ cls(c, t) ↔
        a < c.n.toNat ∧ Column.idAt c.b c.w a = Column.idAt c.b c.w ((F(c)).getD t 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := segments_spec c hw hs hcard h63
  rw [he] at h1 h2 h3 h4
  refine ⟨h1, h2, h3, h4, ?_, fun t ht a => ?_⟩
  · rw [sum_filter_classes, List.filter_eq_self.2 fun j hj => by
      simpa using Verify.groupOf_lt (g := Column.idAt c.b c.w) (List.mem_range.1 hj), List.length_range]
  · simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact ⟨fun ⟨ha, e⟩ => ⟨ha, (Verify.groupOf_eq_iff ha ht).1 e⟩, fun ⟨ha, e⟩ => ⟨ha, (Verify.groupOf_eq_iff ha ht).2 e⟩⟩

-- the class counts of `rk`, `sk`, and the start `j` of `s` (`setIds_spec`'s)
set_option hygiene false in
local notation "KR" => List.length (F(rk))
set_option hygiene false in
local notation "KS" => List.length (F(sk))

/-- **`symDiv`'s set ids, read back**: over the key codes `rk`, `sk` and the joint value codes `v0`, `v1` of `R`
    and `S`, `symDiv`'s `ids` holds one long per key class of `rk`, then one per key class of `sk`; a class `i` of
    `rk` and a class `j` of `sk` get one id exactly when they hold one set of value codes. Stated over any codes,
    so the statement holds no `Obj.codes`. Hypotheses: the codes well formed, on one value lane, the value codes
    counting `rk`'s and `sk`'s rows; `nR` is `rk`'s count; the counts fit; `segments`, `ss`, `sid` by their
    defining equations. -/
theorem sym_ids (rk sk v0 v1 : Code)
    (rkw : laneOK(rk.w))
    (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (rkc : rk.w < 8 → rk.card < USize.size ∧ ∀ i < rk.n.toNat, Column.idAt rk.b rk.w i < rk.card)
    (skw : laneOK(sk.w))
    (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (skc : sk.w < 8 → sk.card < USize.size ∧ ∀ i < sk.n.toNat, Column.idAt sk.b sk.w i < sk.card)
    (v0w : laneOK(v0.w))
    (v0s : v0.b.size = (v0.n.toNat * v0.w + 7) / 8)
    (v0c : v0.w < 8 → v0.card < USize.size ∧ ∀ i < v0.n.toNat, Column.idAt v0.b v0.w i < v0.card)
    (v1s : v1.b.size = (v1.n.toNat * v1.w + 7) / 8)
    (v1c : v1.w < 8 → v1.card < USize.size ∧ ∀ i < v1.n.toNat, Column.idAt v1.b v1.w i < v1.card)
    (hvw : v1.w = v0.w) (v0n : v0.n = rk.n) (v1n : v1.n = sk.n)
    (hNU : rk.n.toNat + sk.n.toNat < USize.size) (hN63 : rk.n.toNat + sk.n.toNat + 1 < 2 ^ 63)
    (nR : Nat) (hnR : rk.n.toNat = nR)
    (pr orr fr ps os fs : ByteArray) (hR : segments rk = (pr, orr, fr)) (hS : segments sk = (ps, os, fs))
    (ss : ByteArray) (hss : ss = os.extract 0 (os.size - 8)) (sid : ByteArray)
    (hsid : sid = longCount "/ₛ" ss fun c _ => setIds (Code.cat #[v0.gather pr, v1.gather ps])
      (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss nR])) :
    sid.size = 8 * (KR + KS) ∧ ∀ k < KR, ∀ l < KS,
      (Column.bitsAt sid (8 * k) 8 = Column.bitsAt sid (8 * (KR + l)) 8 ↔
        ∀ u, (∃ a ∈ cls(rk, k), Column.idAt v0.b v0.w a = u) ↔ ∃ b ∈ cls(sk, l), Column.idAt v1.b v1.w b = u) := by
  classical
  have h8 : Kernel.Ew.width Ew.i64 = 8 := by decide
  obtain ⟨-, pR, oR, tR, sR, -⟩ := seg_facts rk rkw rks rkc (by omega) hR
  obtain ⟨-, pS, oS, tS, sS, -⟩ := seg_facts sk skw sks skc (by omega) hS
  have hKR : KR ≤ rk.n.toNat := firstsOf_length_le _ _
  have hKS : KS ≤ sk.n.toNat := firstsOf_length_le _ _
  have mR : ∀ a b, a ≤ b → pre(rk, a) ≤ pre(rk, b) := fun a b h => sum_range_le _ h
  have mS : ∀ a b, a ≤ b → pre(sk, a) ≤ pre(sk, b) := fun a b h => sum_range_le _ h
  have zR : pre(rk, 0) = 0 := rfl
  have zS : pre(sk, 0) = 0 := rfl
  -- the starts: `R`'s class offsets, then `S`'s shifted by `nR`
  have hssz : ss.size = 8 * KS := by rw [hss, ByteArray.size_extract]; omega
  have hlss : len ss = KS := by unfold len; omega
  have hssb : ∀ t < KS, (Column.bitsAt ss (t * 8) 8).toNat = pre(sk, t) := fun t ht => by
    rw [hss, bitsAt_extract os (by omega) (by omega), Nat.zero_add]; exact tS t (by omega)
  have hlssU : len ss < USize.size := by rw [hlss]; exact Nat.lt_of_le_of_lt hKS sk.n.toNat_lt_size
  subst hsid
  unfold longCount need
  rw [dif_pos hlssU]
  dsimp only
  have hc : ((len ss).toUSize).toNat = KS := by rw [USize.toNat_ofNat_of_lt' hlssU, hlss]
  generalize (len ss).toUSize = c at hc ⊢
  have had : ∀ t < KS, (Column.bitsAt (addc c ss nR) (t * 8) 8).toNat = nR + pre(sk, t) := fun t ht => by
    have hpt := mS t KS (by omega)
    have hx : (Column.bitsAt ss (t * 8) 8).toNat < 2 ^ 63 := by rw [hssb t ht]; omega
    have hy : (nR.toUInt64).toNat = nR :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show nR < 2 ^ 63 by omega) (by decide))
    unfold addc
    rw [val_va_get _ _ _ _ (by omega), bitsAt_one, (valStep_add_sub hx (by rw [hy]; omega)).1 (by rw [hy, hssb t ht]; omega),
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show (Column.bitsAt ss (t * 8) 8).toNat + (nR.toUInt64).toNat < 2 ^ 63
        by rw [hy, hssb t ht]; omega) (by decide)), hy, hssb t ht, Nat.add_comm]
  have horr : (orr.extract 0 (orr.size - 8)).size = 8 * KR := by rw [ByteArray.size_extract]; omega
  have hadd : (addc c ss nR).size = 8 * KS := by unfold addc; rw [KernelWF.Ew.val_size, h8, hc]; omega
  obtain ⟨stsz, st0, st1⟩ := concat_two (orr.extract 0 (orr.size - 8)) (addc c ss nR) horr
  generalize concatBytes #[orr.extract 0 (orr.size - 8), addc c ss nR] = s at stsz st0 st1 ⊢
  have hT : ∀ j < KR + KS, T(j) = if j < KR then pre(rk, j) else nR + pre(sk, j - KR) := by
    intro j hj
    by_cases h : j < KR
    · rw [if_pos h, st0 j h, bitsAt_extract orr (by omega) (by omega), Nat.zero_add]; exact tR j (by omega)
    · rw [if_neg h]
      obtain ⟨t, rfl⟩ : ∃ t, j = KR + t := ⟨j - KR, by omega⟩
      rw [st1 t (by omega), had t (by omega), Nat.add_sub_cancel_left]
  -- the codes end to end: `v0` along `R`'s classes, then `v1` along `S`'s
  have hpv : ∀ v ∈ ids pr, v < rk.n.toNat := fun v hv => by
    rw [pR] at hv; obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 hv; exact List.mem_range.1 (List.mem_filter.1 ht).1
  have hsv : ∀ v ∈ ids ps, v < sk.n.toNat := fun v hv => by
    rw [pS] at hv; obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 hv; exact List.mem_range.1 (List.mem_filter.1 ht).1
  have hlpr : len pr = rk.n.toNat := by rw [len_eq_ids, pR, List.length_flatMap]; exact sR
  have hlps : len ps = sk.n.toNat := by rw [len_eq_ids, pS, List.length_flatMap]; exact sS
  have v1w : laneOK(v1.w) := by rw [hvw]; exact v0w
  have hcb0 : 8 ≤ v0.w → 8 * v0.b.size = v0.w * v0.n.toNat := fun _ => by
    rcases v0w with h | h | h | h | h | h | h <;> rw [h] at v0s ⊢ <;> omega
  have hcb1 : 8 ≤ v1.w → 8 * v1.b.size = v1.w * v1.n.toNat := fun _ => by
    rcases v1w with h | h | h | h | h | h | h <;> rw [h] at v1s ⊢ <;> omega
  have hlprU : len pr < USize.size := by rw [hlpr]; exact rk.n.toNat_lt_size
  have hlpsU : len ps < USize.size := by rw [hlps]; exact sk.n.toNat_lt_size
  obtain ⟨g0w, g0n, g0c, g0r⟩ := gather_get v0 pr hlprU v0w hcb0
  have g0s := gather_size v0 pr hlprU v0w
  obtain ⟨g1w, g1n, g1c, g1r⟩ := gather_get v1 ps hlpsU v1w hcb1
  have g1s := gather_size v1 ps hlpsU v1w
  generalize Code.gather v0 pr = g0 at g0w g0n g0c g0r g0s ⊢
  generalize Code.gather v1 ps = g1 at g1w g1n g1c g1r g1s ⊢
  have hmem : ∀ x ∈ (#[g0, g1] : Array Code), x = g0 ∨ x = g1 := fun x hx => by simpa using hx
  have hsum : ((#[g0, g1] : Array Code).toList.map (·.n.toNat)).sum = rk.n.toNat + sk.n.toNat := by
    simp [g0n, g1n, hlpr, hlps]
  have hNc : ((#[g0, g1] : Array Code).toList.map (·.n.toNat)).sum < USize.size := by rw [hsum]; exact hNU
  have hcw : ∀ x ∈ (#[g0, g1] : Array Code), x.w = v0.w := fun x hx => by
    rcases hmem x hx with rfl | rfl
    · exact g0w
    · exact g1w.trans hvw
  have hcs : ∀ x ∈ (#[g0, g1] : Array Code), x.b.size = (x.n.toNat * v0.w + 7) / 8 := fun x hx => by
    rcases hmem x hx with rfl | rfl
    · rw [g0s, g0n]
    · rw [g1s, g1n, hvw]
  have hid : v0.w < 8 → ∀ x ∈ (#[g0, g1] : Array Code), ∀ i < x.n.toNat, Column.idAt x.b v0.w i < max x.card 1 :=
    fun hw x hx i hi => by
    rcases hmem x hx with rfl | rfl
    · rw [g0n] at hi; rw [g0r i hi, g0c]; split
      · exact Nat.lt_of_lt_of_le ((v0c hw).2 _ ‹_›) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
    · rw [g1n] at hi; rw [← hvw, g1r i hi, g1c]; split
      · exact Nat.lt_of_lt_of_le ((v1c (by rw [hvw]; exact hw)).2 _ ‹_›) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  obtain ⟨ccw, ccn, ccr⟩ := cat_get #[g0, g1] v0w (by simp) hcw hcs hid hNc
  obtain ⟨ccs, -⟩ := cat_wf #[g0, g1] v0w (by simp) hcw hcs hid hNc
  have hr0 : ∀ x < rk.n.toNat, Column.idAt (Code.cat #[g0, g1]).b v0.w (0 + x) =
      Column.idAt v0.b v0.w (((ids pr)[x]?).getD 0) := fun x hx => by
    have e : Column.idAt (Code.cat #[g0, g1]).b v0.w (0 + x) = Column.idAt g0.b v0.w x :=
      ccr 0 (by simp) x (by show x < g0.n.toNat; rw [g0n, hlpr]; exact hx)
    have hxl : x < (ids pr).length := by rw [← len_eq_ids, hlpr]; exact hx
    rw [e, g0r x (by rw [hlpr]; exact hx), ← ids_getElem hxl,
      if_pos (by rw [v0n]; exact hpv _ (List.getElem_mem hxl)), List.getElem?_eq_getElem hxl, Option.getD_some]
  have hr1 : ∀ x < sk.n.toNat, Column.idAt (Code.cat #[g0, g1]).b v0.w (rk.n.toNat + x) =
      Column.idAt v1.b v1.w (((ids ps)[x]?).getD 0) := fun x hx => by
    have e : Column.idAt (Code.cat #[g0, g1]).b v0.w (g0.n.toNat + x) = Column.idAt g1.b v0.w x :=
      ccr 1 (by simp) x (by show x < g1.n.toNat; rw [g1n, hlps]; exact hx)
    have hxl : x < (ids ps).length := by rw [← len_eq_ids, hlps]; exact hx
    rw [g0n, hlpr] at e
    rw [e, ← hvw, g1r x (by rw [hlps]; exact hx), ← ids_getElem hxl,
      if_pos (by rw [v1n]; exact hsv _ (List.getElem_mem hxl)), List.getElem?_eq_getElem hxl, Option.getD_some]
  generalize Code.cat #[g0, g1] = cc at ccw ccn ccr ccs hr0 hr1 ⊢
  rw [hsum] at ccn
  -- the slices `setIds` compares, as intervals of `cc`
  have hP : ∀ j < KR + KS, ∀ Lo Hi : Nat, T(j) = Lo →
      (if j + 1 < KR + KS then T(j + 1) else cc.n.toNat) = Hi → Hi ≤ cc.n.toNat → ∀ u,
      ((∃ i < cc.n.toNat, T(j) ≤ i ∧ (j + 1 < KR + KS → i < T(j + 1)) ∧ Column.idAt cc.b cc.w i = u) ↔
        ∃ i, Lo ≤ i ∧ i < Hi ∧ Column.idAt cc.b v0.w i = u) := by
    intro j _ Lo Hi hLo hHi hHN u
    rw [ccw]
    constructor
    · rintro ⟨i, hiN, h1, h2, h3⟩
      refine ⟨i, hLo ▸ h1, ?_, h3⟩
      by_cases h : j + 1 < KR + KS
      · rw [if_pos h] at hHi; rw [← hHi]; exact h2 h
      · rw [if_neg h] at hHi; rw [← hHi]; exact hiN
    · rintro ⟨i, h1, h2, h3⟩
      refine ⟨i, by omega, by rw [hLo]; exact h1, fun h => ?_, h3⟩
      rw [if_pos h] at hHi; rw [hHi]; exact h2
  have hKR0 : KR = 0 → rk.n.toNat = 0 := fun h => by rw [← sR, h]; rfl
  have hKS0 : KS = 0 → sk.n.toNat = 0 := fun h => by rw [← sS, h]; rfl
  have hRside : ∀ k < KR, ∀ u,
      ((∃ x < cc.n.toNat, T(k) ≤ x ∧ (k + 1 < KR + KS → x < T(k + 1)) ∧ Column.idAt cc.b cc.w x = u) ↔
        ∃ a ∈ cls(rk, k), Column.idAt v0.b v0.w a = u) := by
    intro k hk u
    have hpk := mR (k + 1) KR (by omega)
    refine (hP k (by omega) _ (pre(rk, k + 1)) ((hT k (by omega)).trans (if_pos hk)) ?_ (by omega) u).trans ?_
    · by_cases h : k + 1 < KR + KS
      · rw [if_pos h, hT (k + 1) h]
        by_cases h' : k + 1 < KR
        · rw [if_pos h']
        · rw [if_neg h', show k + 1 - KR = 0 by omega, zS, show k + 1 = KR by omega]; omega
      · rw [if_neg h, ccn, hKS0 (by omega), show k + 1 = KR by omega]; omega
    · have := block_slice (fun t => cls(rk, t)) hk (Column.idAt cc.b v0.w) (Column.idAt v0.b v0.w) 0
        (fun x hx => by rw [hr0 x (by rw [← sR]; exact hx), pR]) u
      simpa only [Nat.zero_add] using this
  have hSside : ∀ j < KS, ∀ u,
      ((∃ x < cc.n.toNat, T(KR + j) ≤ x ∧ (KR + j + 1 < KR + KS → x < T(KR + j + 1)) ∧
          Column.idAt cc.b cc.w x = u) ↔ ∃ b ∈ cls(sk, j), Column.idAt v1.b v1.w b = u) := by
    intro j hj u
    have hpj := mS (j + 1) KS (by omega)
    refine (hP (KR + j) (by omega) (nR + pre(sk, j)) (nR + pre(sk, j + 1))
      ((hT _ (by omega)).trans (by rw [if_neg (by omega), Nat.add_sub_cancel_left])) ?_ (by omega) u).trans ?_
    · by_cases h : KR + j + 1 < KR + KS
      · rw [if_pos h, hT _ h, if_neg (by omega), show KR + j + 1 - KR = j + 1 by omega]
      · rw [if_neg h, ccn, show j + 1 = KS by omega]; omega
    · rw [← hnR]
      exact block_slice (fun t => cls(sk, t)) hj (Column.idAt cc.b v0.w) (Column.idAt v1.b v1.w) rk.n.toNat
        (fun x hx => by rw [hr1 x (by rw [← sS]; exact hx), pS]) u
  -- `setIds_spec` at a class of each side
  have hsz : s.size = 8 * (KR + KS) := by rw [stsz, horr, hadd]; omega
  have hw' : laneOK(cc.w) := by rw [ccw]; exact v0w
  have hs' : cc.b.size = (cc.n.toNat * cc.w + 7) / 8 := by rw [ccw]; exact ccs
  have hasc : ∀ j, j + 1 < KR + KS → T(j) ≤ T(j + 1) := fun j hj => by
    rw [hT j (by omega), hT (j + 1) hj]
    by_cases h1 : j + 1 < KR
    · rw [if_pos (by omega), if_pos h1]; exact mR _ _ (by omega)
    · by_cases h0 : j < KR
      · rw [if_pos h0, if_neg h1]; have := mR j KR (by omega); omega
      · rw [if_neg h0, if_neg h1]; have := mS (j - KR) (j + 1 - KR) (by omega); omega
  have hle : ∀ j < KR + KS, T(j) ≤ cc.n.toNat := fun j hj => by
    rw [hT j hj, ccn]
    by_cases h0 : j < KR
    · rw [if_pos h0]; have := mR j KR (by omega); omega
    · rw [if_neg h0]; have := mS (j - KR) KS (by omega); omega
  have h0 : 0 < KR + KS → T(0) = 0 := fun hm => by
    rw [hT 0 hm]
    by_cases h : 0 < KR
    · rw [if_pos h]; rfl
    · rw [if_neg h, Nat.zero_sub, zS]; have := hKR0 (by omega); omega
  refine ⟨by rw [setIds_size]; unfold len; omega, fun k hk l hl => ?_⟩
  have e := (setIds_spec cc s hw' hs' hsz (by rw [ccn]; omega) (by omega) h0 hasc hle (j := k) (j' := KR + l)
    (by omega) (by omega)).1
  refine e.trans (forall_congr' fun u => ?_)
  rw [hRside k hk u, hSside l hl u]

-- `jp(l, r)`: the pairs `(i, j)` `join l r` answers (`RepDiv`'s)
open DivN

/-- **`symDiv`'s joined classes**: `lc`, `rc`, the two halves of `sym_ids`'s `sid` as long codes, are well formed
    with one row per key class of `rk`, `sk`; `join lc rc` pairs a class `k` of `rk` with a class `l` of `sk`
    exactly when they hold one set of value codes. Hypotheses: those of `sym_ids`, and `lc`, `rc` by their
    defining equations. -/
theorem sym_pairs (rk sk v0 v1 : Code)
    (rkw : laneOK(rk.w))
    (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (rkc : rk.w < 8 → rk.card < USize.size ∧ ∀ i < rk.n.toNat, Column.idAt rk.b rk.w i < rk.card)
    (skw : laneOK(sk.w))
    (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (skc : sk.w < 8 → sk.card < USize.size ∧ ∀ i < sk.n.toNat, Column.idAt sk.b sk.w i < sk.card)
    (v0w : laneOK(v0.w))
    (v0s : v0.b.size = (v0.n.toNat * v0.w + 7) / 8)
    (v0c : v0.w < 8 → v0.card < USize.size ∧ ∀ i < v0.n.toNat, Column.idAt v0.b v0.w i < v0.card)
    (v1s : v1.b.size = (v1.n.toNat * v1.w + 7) / 8)
    (v1c : v1.w < 8 → v1.card < USize.size ∧ ∀ i < v1.n.toNat, Column.idAt v1.b v1.w i < v1.card)
    (hvw : v1.w = v0.w) (v0n : v0.n = rk.n) (v1n : v1.n = sk.n)
    (hNU : rk.n.toNat + sk.n.toNat < USize.size) (hN63 : rk.n.toNat + sk.n.toNat + 1 < 2 ^ 63)
    (nR : Nat) (hnR : rk.n.toNat = nR)
    (pr orr fr ps os fs : ByteArray) (hR : segments rk = (pr, orr, fr)) (hS : segments sk = (ps, os, fs))
    (ss : ByteArray) (hss : ss = os.extract 0 (os.size - 8)) (sid : ByteArray)
    (hsid : sid = longCount "/ₛ" ss fun c _ => setIds (Code.cat #[v0.gather pr, v1.gather ps])
      (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss nR]))
    (lc rc : Code) (hlc : lc = Code.ofLongs (sid.extract 0 (8 * len fr)))
    (hrc : rc = Code.ofLongs (sid.extract (8 * len fr) sid.size)) :
    lc.w = 64 ∧ lc.n.toNat = KR ∧ lc.b.size = (lc.n.toNat * lc.w + 7) / 8 ∧
    rc.w = 64 ∧ rc.n.toNat = KS ∧ rc.b.size = (rc.n.toNat * rc.w + 7) / 8 ∧
    ∀ k l, (k, l) ∈ jp(lc, rc) ↔ k < KR ∧ l < KS ∧
      ∀ u, (∃ a ∈ cls(rk, k), Column.idAt v0.b v0.w a = u) ↔ ∃ b ∈ cls(sk, l), Column.idAt v1.b v1.w b = u := by
  obtain ⟨hsz, hid⟩ := sym_ids rk sk v0 v1 rkw rks rkc skw sks skc v0w v0s v0c v1s v1c hvw v0n v1n hNU hN63 nR hnR
    pr orr fr ps os fs hR hS ss hss sid hsid
  obtain ⟨hfr, -⟩ := seg_facts rk rkw rks rkc (by omega) hR
  have hlfr : len fr = KR := by rw [len_eq_ids, hfr]
  have hKR : KR ≤ rk.n.toNat := firstsOf_length_le _ _
  have hKS : KS ≤ sk.n.toNat := firstsOf_length_le _ _
  have e1 : (sid.extract 0 (8 * len fr)).size = 8 * KR := by rw [ByteArray.size_extract, hlfr]; omega
  have e2 : (sid.extract (8 * len fr) sid.size).size = 8 * KS := by rw [ByteArray.size_extract, hlfr]; omega
  have j1 : len (sid.extract 0 (8 * len fr)) = KR := by
    show (sid.extract 0 (8 * len fr)).size / 8 = _; rw [e1]; omega
  have j2 : len (sid.extract (8 * len fr) sid.size) = KS := by
    show (sid.extract (8 * len fr) sid.size).size / 8 = _; rw [e2]; omega
  have l1 : len (sid.extract 0 (8 * len fr)) < USize.size := by rw [j1]; omega
  have l2 : len (sid.extract (8 * len fr) sid.size) < USize.size := by rw [j2]; omega
  have hL : lc.w = 64 ∧ lc.n.toNat = len (sid.extract 0 (8 * len fr)) ∧ lc.b = sid.extract 0 (8 * len fr) := by
    subst hlc; unfold Code.ofLongs longCount; simp only [need, dif_pos l1]
    exact ⟨trivial, USize.toNat_ofNat_of_lt' l1, trivial⟩
  have hM : rc.w = 64 ∧ rc.n.toNat = len (sid.extract (8 * len fr) sid.size) ∧
      rc.b = sid.extract (8 * len fr) sid.size := by
    subst hrc; unfold Code.ofLongs longCount; simp only [need, dif_pos l2]
    exact ⟨trivial, USize.toNat_ofNat_of_lt' l2, trivial⟩
  have n1 : lc.n.toNat = KR := by rw [hL.2.1, j1]
  have n2 : rc.n.toNat = KS := by rw [hM.2.1, j2]
  have i1 : ∀ k < KR, Column.idAt lc.b lc.w k = (Column.bitsAt sid (8 * k) 8).toNat := fun k hk => by
    rw [hL.1, hL.2.2]
    refine (idAt_lane _ (c := 8) (by decide) k).trans ?_
    rw [bitsAt_extract sid (by omega) (by omega), Nat.zero_add, Nat.mul_comm]
  have i2 : ∀ l < KS, Column.idAt rc.b rc.w l = (Column.bitsAt sid (8 * (KR + l)) 8).toNat := fun l hl => by
    rw [hM.1, hM.2.2]
    refine (idAt_lane _ (c := 8) (by decide) l).trans ?_
    rw [bitsAt_extract sid (by omega) (by omega), hlfr, show 8 * KR + l * 8 = 8 * (KR + l) by omega]
  refine ⟨hL.1, n1, by rw [hL.2.2, e1, n1, hL.1]; omega, hM.1, n2, by rw [hM.2.2, e2, n2, hM.1]; omega,
    fun k l => ?_⟩
  rw [mem_joinPairs, n1, n2]
  constructor
  · rintro ⟨hk, hl, he⟩
    refine ⟨hk, hl, (hid k hk l hl).1 ?_⟩
    rw [i1 k hk, i2 l hl] at he; exact (UInt64.toNat_inj.1 he).symm
  · rintro ⟨hk, hl, he⟩
    refine ⟨hk, hl, ?_⟩
    rw [i1 k hk, i2 l hl, (hid k hk l hl).2 he]

/-- **`Vals.pickPart` read back row by row**: its count is `len I`, and its row `q` is `x`'s row at `I`'s `q`-th
    position. Hypotheses: `pickPart_rows`'. -/
theorem pickPart_row {n : USize} (x : Vals B n) (I : ByteArray) (hL : len I < USize.size)
    (hlt : ∀ t ∈ ids I, t < n.toNat) (hP : Vals.PickFits B x (ids I)) :
    (Vals.pickPart B x I).1.toNat = len I ∧ ∀ q (hq : q < (Vals.pickPart B x I).1.toNat),
      ∃ (hq' : q < (ids I).length) (ht : (ids I)[q]'hq' < n.toNat),
        (Vals.pickPart B x I).2.row ⟨q, hq⟩ = x.row ⟨_, ht⟩ := by
  have hpd : Vals.pickPart B x I = ⟨(len I).toUSize, Vals.pick B x I _ (USize.toNat_ofNat_of_lt' hL).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hL]
  have hLn : ((len I).toUSize).toNat = len I := USize.toNat_ofNat_of_lt' hL
  rw [hpd]; dsimp only
  have hfit : Vals.PickFits B x
      ((List.range ((len I).toUSize).toNat).map fun q => (Column.bitsAt I (q * 8) 8).toNat) := by
    rw [hLn]; exact hP
  refine ⟨hLn, fun q hq => ?_⟩
  have hq' : q < (ids I).length := by rw [← len_eq_ids, ← hLn]; exact hq
  have ht := hlt _ (List.getElem_mem hq')
  refine ⟨hq', ht, ?_⟩
  rw [pick_row B x I _ _ hfit ⟨q, hq⟩, dif_pos (by rw [← ids_getElem hq']; exact ht)]
  exact congrArg x.row (Fin.ext (ids_getElem hq').symm)

/-- **`symDiv`'s joined part, read back**: `hit`, the pairs of `join lc rc` (`sym_pairs`) read at the first rows
    of the key classes, holds `(x, y)` exactly when `R` takes `x` somewhere and `R`'s fibre at `x` is `S`'s at
    `y`. Hypotheses: `sym_pairs`'; `rk`, `sk` code `R.key`, `S.key` faithfully, `v0`, `v1` code `R.val`, `S.val`
    jointly faithfully; `rf`, `sf`, `hit` by their defining equations, the sides pick back, the join's counts fit. -/
theorem sym_hit_holds (R : Rel A C) (S : Rel B C) (rk sk v0 v1 : Code)
    (rkw : laneOK(rk.w))
    (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (rkc : rk.w < 8 → rk.card < USize.size ∧ ∀ i < rk.n.toNat, Column.idAt rk.b rk.w i < rk.card)
    (skw : laneOK(sk.w))
    (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (skc : sk.w < 8 → sk.card < USize.size ∧ ∀ i < sk.n.toNat, Column.idAt sk.b sk.w i < sk.card)
    (v0w : laneOK(v0.w))
    (v0s : v0.b.size = (v0.n.toNat * v0.w + 7) / 8)
    (v0c : v0.w < 8 → v0.card < USize.size ∧ ∀ i < v0.n.toNat, Column.idAt v0.b v0.w i < v0.card)
    (v1s : v1.b.size = (v1.n.toNat * v1.w + 7) / 8)
    (v1c : v1.w < 8 → v1.card < USize.size ∧ ∀ i < v1.n.toNat, Column.idAt v1.b v1.w i < v1.card)
    (hvw : v1.w = v0.w) (v0n : v0.n = rk.n) (v1n : v1.n = sk.n)
    (hNU : rk.n.toNat + sk.n.toNat < USize.size) (hN63 : rk.n.toNat + sk.n.toNat + 1 < 2 ^ 63)
    (nR : Nat) (hnR : rk.n.toNat = nR)
    (pr orr fr ps os fs : ByteArray) (hR : segments rk = (pr, orr, fr)) (hS : segments sk = (ps, os, fs))
    (ss : ByteArray) (hss : ss = os.extract 0 (os.size - 8)) (sid : ByteArray)
    (hsid : sid = longCount "/ₛ" ss fun c _ => setIds (Code.cat #[v0.gather pr, v1.gather ps])
      (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss nR]))
    (lc rc : Code) (hlc : lc = Code.ofLongs (sid.extract 0 (8 * len fr)))
    (hrc : rc = Code.ofLongs (sid.extract (8 * len fr) sid.size))
    (rkn : rk.n = R.n) (skn : sk.n = S.n)
    (hrk : ∀ {a a' : Nat} (ha : a < R.n.toNat) (ha' : a' < R.n.toNat),
      Column.idAt rk.b rk.w a = Column.idAt rk.b rk.w a' ↔ R.key.row ⟨a, ha⟩ = R.key.row ⟨a', ha'⟩)
    (hsk : ∀ {b b' : Nat} (hb : b < S.n.toNat) (hb' : b' < S.n.toNat),
      Column.idAt sk.b sk.w b = Column.idAt sk.b sk.w b' ↔ S.key.row ⟨b, hb⟩ = S.key.row ⟨b', hb'⟩)
    (hv : ∀ {a b : Nat} (ha : a < R.n.toNat) (hb : b < S.n.toNat),
      Column.idAt v0.b v0.w a = Column.idAt v1.b v1.w b ↔ R.val.row ⟨a, ha⟩ = S.val.row ⟨b, hb⟩)
    (rf : Part A) (hrf : rf = Vals.pickPart A R.key fr) (sf : Part B) (hsf : sf = Vals.pickPart B S.key fs)
    (hRf : Vals.PickFits A R.key (ids fr)) (hSf : Vals.PickFits B S.key (ids fs))
    (hM : lc.n.toNat * rc.n.toNat < min (2 ^ 63) USize.size)
    (hB : Vals.PickFits A rf.2 ((jp(lc, rc)).map Prod.fst)) (hC : Vals.PickFits B sf.2 ((jp(lc, rc)).map Prod.snd))
    (hit : Rel A B)
    (hhit : hit = longCount "/ₛ" (join lc rc).2 fun m h => (⟨m, Vals.pickN A rf.2 (join lc rc).1 m
      (Nat.le_trans (Nat.le_of_eq h.symm) (join_len lc rc)), Vals.pick B sf.2 (join lc rc).2 m h⟩ : Rel A B))
    (x : A.El) (y : B.El) :
    hit.Holds x y ↔ (∃ c, R.Holds x c) ∧ ∀ c, R.Holds x c ↔ S.Holds y c := by
  classical
  obtain ⟨lw, ln, ls, rw', rn, rs, hjp⟩ := sym_pairs rk sk v0 v1 rkw rks rkc skw sks skc v0w v0s v0c v1s v1c hvw
    v0n v1n hNU hN63 nR hnR pr orr fr ps os fs hR hS ss hss sid hsid lc rc hlc hrc
  obtain ⟨hfr, -, -, -, -, mR⟩ := seg_facts rk rkw rks rkc (by omega) hR
  obtain ⟨hfs, -, -, -, -, mS⟩ := seg_facts sk skw sks skc (by omega) hS
  have hKR : KR ≤ rk.n.toNat := firstsOf_length_le _ _
  have hKS : KS ≤ sk.n.toNat := firstsOf_length_le _ _
  have hlfr : len fr = KR := by rw [len_eq_ids, hfr]
  have hlfs : len fs = KS := by rw [len_eq_ids, hfs]
  -- the picked first rows
  obtain ⟨rf1, rfr⟩ := pickPart_row R.key fr (by rw [hlfr]; exact Nat.lt_of_le_of_lt hKR rk.n.toNat_lt_size)
    (fun t ht => by rw [hfr] at ht; rw [← rkn]; exact firsts_lt _ _ ht) hRf
  obtain ⟨sf1, sfr⟩ := pickPart_row S.key fs (by rw [hlfs]; exact Nat.lt_of_le_of_lt hKS sk.n.toNat_lt_size)
    (fun t ht => by rw [hfs] at ht; rw [← skn]; exact firsts_lt _ _ ht) hSf
  rw [← hrf] at rf1 rfr
  rw [← hsf] at sf1 sfr
  have fRlt : ∀ k < KR, (F(rk)).getD k 0 < R.n.toNat := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, ← rkn]
    exact firsts_lt _ _ (List.getElem_mem hk)
  have fSlt : ∀ l < KS, (F(sk)).getD l 0 < S.n.toNat := fun l hl => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some, ← skn]
    exact firsts_lt _ _ (List.getElem_mem hl)
  have rowR : ∀ k (hk : k < rf.1.toNat), ∃ h : (F(rk)).getD k 0 < R.n.toNat,
      rf.2.row ⟨k, hk⟩ = R.key.row ⟨_, h⟩ := fun k hk => by
    obtain ⟨hq', ht, e⟩ := rfr k hk
    have e2 : (ids fr)[k] = (F(rk)).getD k 0 := by
      rw [List.getD_eq_getElem?_getD, ← hfr, List.getElem?_eq_getElem hq', Option.getD_some]
    exact ⟨e2 ▸ ht, e.trans (congrArg R.key.row (Fin.ext e2))⟩
  have rowS : ∀ l (hl : l < sf.1.toNat), ∃ h : (F(sk)).getD l 0 < S.n.toNat,
      sf.2.row ⟨l, hl⟩ = S.key.row ⟨_, h⟩ := fun l hl => by
    obtain ⟨hq', ht, e⟩ := sfr l hl
    have e2 : (ids fs)[l] = (F(sk)).getD l 0 := by
      rw [List.getD_eq_getElem?_getD, ← hfs, List.getElem?_eq_getElem hq', Option.getD_some]
    exact ⟨e2 ▸ ht, e.trans (congrArg S.key.row (Fin.ext e2))⟩
  -- a key class is the rows of one key
  have cR : ∀ k < KR, ∀ a (ha : a < R.n.toNat) (hf : (F(rk)).getD k 0 < R.n.toNat),
      a ∈ cls(rk, k) ↔ R.key.row ⟨a, ha⟩ = R.key.row ⟨_, hf⟩ := fun k hk a ha hf => by
    rw [mR k hk a]
    exact ⟨fun h => (hrk ha hf).1 h.2, fun h => ⟨by rw [rkn]; exact ha, (hrk ha hf).2 h⟩⟩
  have cS : ∀ l < KS, ∀ b (hb : b < S.n.toNat) (hf : (F(sk)).getD l 0 < S.n.toNat),
      b ∈ cls(sk, l) ↔ S.key.row ⟨b, hb⟩ = S.key.row ⟨_, hf⟩ := fun l hl b hb hf => by
    rw [mS l hl b]
    exact ⟨fun h => (hsk hb hf).1 h.2, fun h => ⟨by rw [skn]; exact hb, (hsk hb hf).2 h⟩⟩
  have gR : ∀ a (ha : a < R.n.toNat), ∃ k < KR, a ∈ cls(rk, k) := fun a ha => by
    have ha' : a < rk.n.toNat := by rw [rkn]; exact ha
    exact ⟨_, Verify.groupOf_lt (g := Column.idAt rk.b rk.w) ha',
      List.mem_filter.2 ⟨List.mem_range.2 ha', beq_self_eq_true _⟩⟩
  have gS : ∀ b (hb : b < S.n.toNat), ∃ l < KS, b ∈ cls(sk, l) := fun b hb => by
    have hb' : b < sk.n.toNat := by rw [skn]; exact hb
    exact ⟨_, Verify.groupOf_lt (g := Column.idAt sk.b sk.w) hb',
      List.mem_filter.2 ⟨List.mem_range.2 hb', beq_self_eq_true _⟩⟩
  -- the rows of `hit`: `join lc rc`'s pairs, read at the first rows
  have hln : lc.n = rf.1 := USize.toNat_inj.1 (by rw [ln, rf1, hlfr])
  have hrn' : rc.n = sf.1 := USize.toNat_inj.1 (by rw [rn, sf1, hlfs])
  have hlw : laneOK(lc.w) := by rw [lw]; decide
  have hrw : laneOK(rc.w) := by rw [rw']; decide
  have hrc' : rc.w < 8 → rc.card < USize.size ∧ ∀ i < rc.n.toNat, Column.idAt rc.b rc.w i < rc.card :=
    fun h => absurd h (by rw [rw']; decide)
  have hrn63 : rc.n.toNat < 2 ^ 63 := by rw [rn]; omega
  obtain ⟨hlt, -⟩ := join_rows lc rc hlw ls hrw rs hrc' hrn63 hM
  have hH : hit.Holds x y ↔ ∃ k l, (k, l) ∈ jp(lc, rc) ∧ ∃ (hk : k < rf.1.toNat) (hl : l < sf.1.toNat),
      rf.2.row ⟨k, hk⟩ = x ∧ sf.2.row ⟨l, hl⟩ = y := by
    subst hhit
    unfold longCount need
    rw [dif_pos hlt]
    dsimp only
    have hm : len (join lc rc).2 = ((len (join lc rc).2).toUSize).toNat := (USize.toNat_ofNat_of_lt' hlt).symm
    obtain ⟨hlen, hrow⟩ := div_y_rows lc rc rf.2 sf.2 hln hrn' hlw ls hrw rs hrc' hrn63 hM hB hC _ hm
      (Nat.le_trans (Nat.le_of_eq hm.symm) (join_len lc rc))
    unfold Rel.Holds
    dsimp only
    constructor
    · rintro ⟨⟨q, hq⟩, ex, ey⟩
      obtain ⟨hJ, hi, hj, e1, e2⟩ := hrow q hq
      exact ⟨_, _, List.getElem_mem hJ, hi, hj, e1.symm.trans ex, e2.symm.trans ey⟩
    · rintro ⟨k, l, hkl, hk, hl, ex, ey⟩
      obtain ⟨q, hJ, hq⟩ := List.getElem_of_mem hkl
      have hq' : q < ((len (join lc rc).2).toUSize).toNat := by rw [hlen]; exact hJ
      obtain ⟨hJ', hi, hj, e1, e2⟩ := hrow q hq'
      refine ⟨⟨q, hq'⟩, ?_, ?_⟩
      · rw [e1, ← ex]; congr 2; rw [hq]
      · rw [e2, ← ey]; congr 2; rw [hq]
  rw [hH]
  constructor
  · rintro ⟨k, l, hkl, hk, hl, ex, ey⟩
    obtain ⟨hk', hl', hV⟩ := (hjp k l).1 hkl
    obtain ⟨hfk, ek⟩ := rowR k hk
    obtain ⟨hfl, el⟩ := rowS l hl
    rw [ek] at ex; rw [el] at ey
    subst ex ey
    refine ⟨⟨_, ⟨_, hfk⟩, rfl, rfl⟩, fun c => ⟨?_, ?_⟩⟩
    · rintro ⟨⟨a, ha⟩, hax, rfl⟩
      obtain ⟨b, hb, e⟩ := (hV _).1 ⟨a, (cR k hk' a ha hfk).2 hax, rfl⟩
      have hbS : b < S.n.toNat := by rw [← skn]; exact ((mS l hl' b).1 hb).1
      exact ⟨⟨b, hbS⟩, (cS l hl' b hbS hfl).1 hb, ((hv ha hbS).1 e.symm).symm⟩
    · rintro ⟨⟨b, hb⟩, hby, rfl⟩
      obtain ⟨a, ha, e⟩ := (hV _).2 ⟨b, (cS l hl' b hb hfl).2 hby, rfl⟩
      have haR : a < R.n.toNat := by rw [← rkn]; exact ((mR k hk' a).1 ha).1
      exact ⟨⟨a, haR⟩, (cR k hk' a haR hfk).1 ha, (hv haR hb).1 e⟩
  · rintro ⟨⟨_, ⟨a, ha⟩, hax, rfl⟩, hiff⟩
    obtain ⟨k, hk, hak⟩ := gR a ha
    obtain ⟨⟨b, hb⟩, hby, hbc⟩ := (hiff _).1 ⟨⟨a, ha⟩, hax, rfl⟩
    obtain ⟨l, hl, hbl⟩ := gS b hb
    have hfk := fRlt k hk
    have hfl := fSlt l hl
    have ka := (cR k hk a ha hfk).1 hak
    have lb := (cS l hl b hb hfl).1 hbl
    have hV : ∀ u, (∃ a ∈ cls(rk, k), Column.idAt v0.b v0.w a = u) ↔
        ∃ b ∈ cls(sk, l), Column.idAt v1.b v1.w b = u := fun u => by
      constructor
      · rintro ⟨a', ha', rfl⟩
        have h' : a' < R.n.toNat := by rw [← rkn]; exact ((mR k hk a').1 ha').1
        obtain ⟨⟨b', hb'⟩, hb'y, hb'c⟩ :=
          (hiff _).1 ⟨⟨a', h'⟩, ((cR k hk a' h' hfk).1 ha').trans (ka.symm.trans hax), rfl⟩
        exact ⟨b', (cS l hl b' hb' hfl).2 (hb'y.trans (hby.symm.trans lb)), ((hv h' hb').2 hb'c.symm).symm⟩
      · rintro ⟨b', hb', rfl⟩
        have h' : b' < S.n.toNat := by rw [← skn]; exact ((mS l hl b').1 hb').1
        obtain ⟨⟨a', ha'⟩, ha'x, ha'c⟩ :=
          (hiff _).2 ⟨⟨b', h'⟩, ((cS l hl b' h' hfl).1 hb').trans (lb.symm.trans hby), rfl⟩
        exact ⟨a', (cR k hk a' ha' hfk).2 (ha'x.trans (hax.symm.trans ka)), (hv ha' h').2 ha'c⟩
    have hkr : k < rf.1.toNat := by rw [rf1, hlfr]; exact hk
    have hls : l < sf.1.toNat := by rw [sf1, hlfs]; exact hl
    obtain ⟨hfk', ek⟩ := rowR k hkr
    obtain ⟨hfl', el⟩ := rowS l hls
    exact ⟨k, l, (hjp k l).2 ⟨hk, hl, hV⟩, hkr, hls, ek.trans (ka.symm.trans hax), el.trans (lb.symm.trans hby)⟩

/-- **The elements of `U` coded as no row of `V`, read back**: `U` picked at `anti uc vc` holds `u` exactly when
    `u` is an element of `U` and no row of `V`. Hypotheses: `uc`, `vc` code `U`, `V` jointly and well formed
    (`anti_ids`); `U` picks back at the kept positions. -/
theorem anti_pick_rows {mu mv : USize} (U : Vals B mu) (V : Vals B mv) (uc vc : Code)
    (hxw : laneOK(uc.w))
    (hyw : laneOK(vc.w))
    (hxs : uc.b.size = (uc.n.toNat * uc.w + 7) / 8) (hys : vc.b.size = (vc.n.toNat * vc.w + 7) / 8)
    (hun : uc.n = mu) (hvn : vc.n = mv)
    (hj : ∀ {j p : Nat} (hj : j < mv.toNat) (hp : p < mu.toNat),
      Column.idAt vc.b vc.w j = Column.idAt uc.b uc.w p ↔ V.row ⟨j, hj⟩ = U.row ⟨p, hp⟩)
    (hP : Vals.PickFits B U (List.range mu.toNat)) (u : B.El) :
    (∃ i, (Vals.pickPart B U (anti uc vc)).2.row i = u) ↔ (∃ p, U.row p = u) ∧ ¬∃ j, V.row j = u := by
  have hm := anti_ids uc vc hxw hyw hxs hys
  have hL : len (anti uc vc) < USize.size := by
    rw [len_eq_ids, hm.1]
    exact Nat.lt_of_le_of_lt (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..)))
      uc.n.toNat_lt_size
  have hlt : ∀ t ∈ ids (anti uc vc), t < mu.toNat := fun t ht => by rw [← hun]; exact ((hm.2.2 t).1 ht).1
  rw [pickPart_rows U _ hL hlt (pickFits_sublist (hun ▸ anti_sublist uc vc) hP) u]
  constructor
  · rintro ⟨t, hti, ht, e⟩
    obtain ⟨-, hno⟩ := (hm.2.2 t).1 hti
    refine ⟨⟨⟨t, ht⟩, e⟩, ?_⟩
    rintro ⟨j, hju⟩
    exact hno ⟨j.1, by rw [hvn]; exact j.2, (hj j.2 ht).2 (hju.trans e.symm)⟩
  · rintro ⟨⟨⟨p, hp⟩, e⟩, hno⟩
    refine ⟨p, (hm.2.2 p).2 ⟨by rw [hun]; exact hp, ?_⟩, hp, e⟩
    rintro ⟨j, hjn, hje⟩
    rw [hvn] at hjn
    exact hno ⟨⟨j, hjn⟩, ((hj hjn hp).1 hje).trans e⟩

-- `symDiv`'s vacuous sides: the elements of `Ua`, `Ub` coded as no key of `R`, `S`
set_option hygiene false in
local notation "vacA" => Vals.pickPart A Ua (anti uac rk)
set_option hygiene false in
local notation "vacB" => Vals.pickPart B Ub (anti ubc sk)

/-- **`symDiv`'s vacuous part, read back**: `⊤` on the elements of `Ua` that are no key of `R` and the elements
    of `Ub` that are no key of `S`. Hypotheses: `anti_pick_rows`' on each side, `rep_top`'s. -/
theorem sym_vac_holds (R : Rel A C) (S : Rel B C) {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb)
    (uac rk ubc sk : Code)
    (uaw : laneOK(uac.w))
    (rkw : laneOK(rk.w))
    (uas : uac.b.size = (uac.n.toNat * uac.w + 7) / 8) (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (ubw : laneOK(ubc.w))
    (skw : laneOK(sk.w))
    (ubs : ubc.b.size = (ubc.n.toNat * ubc.w + 7) / 8) (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (uan : uac.n = ma) (rkn : rk.n = R.n) (ubn : ubc.n = mb) (skn : sk.n = S.n)
    (ha : ∀ {j p : Nat} (hj : j < R.n.toNat) (hp : p < ma.toNat),
      Column.idAt rk.b rk.w j = Column.idAt uac.b uac.w p ↔ R.key.row ⟨j, hj⟩ = Ua.row ⟨p, hp⟩)
    (hb : ∀ {j p : Nat} (hj : j < S.n.toNat) (hp : p < mb.toNat),
      Column.idAt sk.b sk.w j = Column.idAt ubc.b ubc.w p ↔ S.key.row ⟨j, hj⟩ = Ub.row ⟨p, hp⟩)
    (hPa : Vals.PickFits A Ua (List.range ma.toNat)) (hPb : Vals.PickFits B Ub (List.range mb.toNat))
    (hN : (vacA).1.toNat * (vacB).1.toNat < USize.size) (h63 : (vacA).1.toNat * (vacB).1.toNat < 2 ^ 63)
    (hA : Vals.PickFits A (vacA).2 ((List.range ((vacA).1.toNat * (vacB).1.toNat)).map (· / (vacB).1.toNat)))
    (hB : Vals.PickFits B (vacB).2 ((List.range ((vacA).1.toNat * (vacB).1.toNat)).map (· % (vacB).1.toNat)))
    (x : A.El) (y : B.El) :
    (top (vacA).2 (vacB).2).Holds x y ↔
      ((∃ p, Ua.row p = x) ∧ ¬∃ c, R.Holds x c) ∧ ((∃ j, Ub.row j = y) ∧ ¬∃ c, S.Holds y c) := by
  have nR : (¬∃ j, R.key.row j = x) ↔ ¬∃ c, R.Holds x c :=
    not_congr ⟨fun ⟨j, e⟩ => ⟨_, j, e, rfl⟩, fun ⟨_, j, e, _⟩ => ⟨j, e⟩⟩
  have nS : (¬∃ j, S.key.row j = y) ↔ ¬∃ c, S.Holds y c :=
    not_congr ⟨fun ⟨j, e⟩ => ⟨_, j, e, rfl⟩, fun ⟨_, j, e, _⟩ => ⟨j, e⟩⟩
  have eA := (anti_pick_rows Ua R.key uac rk uaw rkw uas rks uan rkn ha hPa x).trans (and_congr Iff.rfl nR)
  have eB := (anti_pick_rows Ub S.key ubc sk ubw skw ubs sks ubn skn hb hPb y).trans (and_congr Iff.rfl nS)
  have h := congrFun (congrFun (rep_top _ _ hN h63 hA hB) x) y
  refine (Iff.of_eq h).trans ?_
  show (∃ a', (x = a' ∧ ∃ i, (vacA).2.row i = x) ∧ ∃ b', True ∧ (b' = y ∧ ∃ j, (vacB).2.row j = b')) ↔ _
  constructor
  · rintro ⟨_, ⟨-, hx⟩, _, -, rfl, hy⟩
    exact ⟨eA.1 hx, eB.1 hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, ⟨rfl, eA.2 hx⟩, y, trivial, rfl, eB.2 hy⟩

-- the one-part code, `nub`'s first rows and `∪`'s razed relation of `P` and `Q` are `RepOps2`'s
open OpsN

/-- **`rep (R /ₛ S)`**: `x` to `y` exactly when `R`'s fibre at `x` is `S`'s at `y`, and either `R` takes `x`
    somewhere, or `x` and `y` are elements of the universes `Ua`, `Ub`. `symDiv`'s intermediate values are bound
    to variables by their defining equations. Hypotheses: `Obj.CodesFit` of every coded part; the counts fit;
    `Vals.PickFits` where a part is picked; `Vals.RazeFits` of `∪`'s raze. -/
theorem rep_symDiv {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb)
    (vc : Vector Code 2) (hvc : vc = C.codes #v[⟨R.n, R.val⟩, ⟨S.n, S.val⟩])
    (hfv : C.CodesFit #v[⟨R.n, R.val⟩, ⟨S.n, S.val⟩])
    (ac : Vector Code 2) (hac : ac = A.codes #v[⟨R.n, R.key⟩, ⟨ma, Ua⟩]) (hfa : A.CodesFit #v[⟨R.n, R.key⟩, ⟨ma, Ua⟩])
    (bc : Vector Code 2) (hbc : bc = B.codes #v[⟨S.n, S.key⟩, ⟨mb, Ub⟩]) (hfb : B.CodesFit #v[⟨S.n, S.key⟩, ⟨mb, Ub⟩])
    (v0 v1 rk uac sk ubc : Code) (ev0 : v0 = vc[0]'Nat.zero_lt_two) (ev1 : v1 = vc[1]'Nat.one_lt_two)
    (erk : rk = ac[0]'Nat.zero_lt_two) (euac : uac = ac[1]'Nat.one_lt_two)
    (esk : sk = bc[0]'Nat.zero_lt_two) (eubc : ubc = bc[1]'Nat.one_lt_two)
    (hNU : R.n.toNat + S.n.toNat < USize.size) (hN63 : R.n.toNat + S.n.toNat + 1 < 2 ^ 63)
    (pr orr fr ps os fs : ByteArray) (epr : pr = (segments rk).1) (eorr : orr = (segments rk).2.1)
    (efr : fr = (segments rk).2.2) (eps : ps = (segments sk).1) (eos : os = (segments sk).2.1)
    (efs : fs = (segments sk).2.2)
    (ss : ByteArray) (hss : ss = os.extract 0 (os.size - 8)) (sid : ByteArray)
    (hsid : sid = longCount "/ₛ" ss fun c _ => setIds (Code.cat #[v0.gather pr, v1.gather ps])
      (concatBytes #[orr.extract 0 (orr.size - 8), addc c ss R.n.toNat]))
    (lc rc : Code) (hlc : lc = Code.ofLongs (sid.extract 0 (8 * len fr)))
    (hrc : rc = Code.ofLongs (sid.extract (8 * len fr) sid.size))
    (rf : Part A) (hrf : rf = Vals.pickPart A R.key fr) (sf : Part B) (hsf : sf = Vals.pickPart B S.key fs)
    (hRf : Vals.PickFits A R.key (ids fr)) (hSf : Vals.PickFits B S.key (ids fs))
    (hM : lc.n.toNat * rc.n.toNat < min (2 ^ 63) USize.size)
    (hB : Vals.PickFits A rf.2 ((jp(lc, rc)).map Prod.fst)) (hC : Vals.PickFits B sf.2 ((jp(lc, rc)).map Prod.snd))
    (hPa : Vals.PickFits A Ua (List.range ma.toNat)) (hPb : Vals.PickFits B Ub (List.range mb.toNat))
    (hN : (vacA).1.toNat * (vacB).1.toNat < USize.size) (h63 : (vacA).1.toNat * (vacB).1.toNat < 2 ^ 63)
    (hA : Vals.PickFits A (vacA).2 ((List.range ((vacA).1.toNat * (vacB).1.toNat)).map (· / (vacB).1.toNat)))
    (hBv : Vals.PickFits B (vacB).2 ((List.range ((vacA).1.toNat * (vacB).1.toNat)).map (· % (vacB).1.toNat)))
    (P Q : Rel A B)
    (hPe : P = longCount "/ₛ" (join lc rc).2 fun m h => (⟨m, Vals.pickN A rf.2 (join lc rc).1 m
      (Nat.le_trans (Nat.le_of_eq h.symm) (join_len lc rc)), Vals.pick B sf.2 (join lc rc).2 m h⟩ : Rel A B))
    (hQe : Q = top (vacA).2 (vacB).2)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hFk : Vals.RazeFits A P.key Q.key) (hFv : Vals.RazeFits B P.val Q.val)
    (hUK : A.CodesFit (#v[⟨(PQ(A, B)).n, (PQ(A, B)).key⟩] : Vector (Part A) 1))
    (hUV : B.CodesFit (#v[⟨(PQ(A, B)).n, (PQ(A, B)).val⟩] : Vector (Part B) 1))
    (hUk : Vals.PickFits A (PQ(A, B)).key (List.range (PQ(A, B)).n.toNat))
    (hUv : Vals.PickFits B (PQ(A, B)).val (List.range (PQ(A, B)).n.toNat)) (x : A.El) (y : B.El) :
    rep (symDiv R S Ua Ub) x y ↔
      (∀ c, rep R x c ↔ rep S y c) ∧ ((∃ c, rep R x c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  classical
  have e : symDiv R S Ua Ub = P ∪ Q := by
    subst hPe hQe hrf hsf hlc hrc hsid hss epr eorr efr eps eos efs ev0 ev1 erk euac esk eubc hvc hac hbc; rfl
  rw [e, rep_union_full P Q hU hFk hFv (one_ok _ hUK) (one_ok _ hUV) hUk hUv]
  show P.Holds x y ∨ Q.Holds x y ↔
    (∀ c, R.Holds x c ↔ S.Holds y c) ∧ ((∃ c, R.Holds x c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y))
  -- the codes, faithful and well formed
  have hV' := codes_faithful_wf C _ hfv; rw [← hvc] at hV'
  obtain ⟨⟨vF, vW⟩, vL⟩ := hV'
  have hA' := codes_faithful_wf A _ hfa; rw [← hac] at hA'
  obtain ⟨⟨aF, aW⟩, -⟩ := hA'
  have hB' := codes_faithful_wf B _ hfb; rw [← hbc] at hB'
  obtain ⟨⟨bF, bW⟩, -⟩ := hB'
  subst ev0 ev1 erk euac esk eubc
  obtain ⟨v0w, v0n, v0s, v0c⟩ := vW (k := 0) (by decide)
  obtain ⟨v1w, v1n, v1s, v1c⟩ := vW (k := 1) (by decide)
  obtain ⟨rkw, rkn, rks, rkc⟩ := aW (k := 0) (by decide)
  obtain ⟨uaw, uan, uas, -⟩ := aW (k := 1) (by decide)
  obtain ⟨skw, skn, sks, skc⟩ := bW (k := 0) (by decide)
  obtain ⟨ubw, ubn, ubs, -⟩ := bW (k := 1) (by decide)
  have v0n' : (vc[0]'Nat.zero_lt_two).n = R.n := v0n
  have v1n' : (vc[1]'Nat.one_lt_two).n = S.n := v1n
  have rkn' : (ac[0]'Nat.zero_lt_two).n = R.n := rkn
  have skn' : (bc[0]'Nat.zero_lt_two).n = S.n := skn
  have hP := sym_hit_holds R S _ _ _ _ rkw rks rkc skw sks skc v0w v0s v0c v1s v1c
    (vL (k := 1) (l := 0) (by decide) (by decide)) (v0n'.trans rkn'.symm) (v1n'.trans skn'.symm)
    (by rw [rkn', skn']; exact hNU) (by rw [rkn', skn']; exact hN63) R.n.toNat (by rw [rkn'])
    pr orr fr ps os fs (by subst epr eorr efr; rfl) (by subst eps eos efs; rfl) ss hss sid hsid lc rc hlc hrc
    rkn' skn' (fun ha ha' => aF (k := 0) (l := 0) (by decide) (by decide) ha ha')
    (fun hb hb' => bF (k := 0) (l := 0) (by decide) (by decide) hb hb')
    (fun ha hb => vF (k := 0) (l := 1) (by decide) (by decide) ha hb)
    rf hrf sf hsf hRf hSf hM hB hC P hPe x y
  have hQ := sym_vac_holds R S Ua Ub _ _ _ _ uaw rkw uas rks ubw skw ubs sks uan rkn' ubn skn'
    (fun hj hp => aF (k := 0) (l := 1) (by decide) (by decide) hj hp)
    (fun hj hp => bF (k := 0) (l := 1) (by decide) (by decide) hj hp) hPa hPb hN h63 hA hBv x y
  subst hQe
  refine (or_congr hP hQ).trans ?_
  constructor
  · rintro (⟨hx, h⟩ | ⟨⟨hx, hnx⟩, hy, hny⟩)
    · exact ⟨h, Or.inl hx⟩
    · exact ⟨fun c => ⟨fun h => absurd ⟨c, h⟩ hnx, fun h => absurd ⟨c, h⟩ hny⟩, Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨h, hx | ⟨hx, hy⟩⟩
    · exact Or.inl ⟨hx, h⟩
    · by_cases hc : ∃ c, R.Holds x c
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨⟨hx, hc⟩, hy, fun ⟨c, hs⟩ => hc ⟨c, (h c).2 hs⟩⟩

#print axioms rep_symDiv
#print axioms sym_vac_holds
#print axioms anti_pick_rows
#print axioms sym_hit_holds
#print axioms pickPart_row
#print axioms sym_pairs
#print axioms sym_ids
#print axioms bitsAt_extract
#print axioms concat_two
#print axioms block_slice
#print axioms seg_facts

end LeetQ.Rel.Rep
