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

-- the first rows of `c`'s classes, the rows of class `t`, and the rows before class `j` (`segments_spec`'s)
set_option hygiene false in
local notation "F(" c ")" => Verify.firstsOf (Column.idAt (Code.b c) (Code.w c)) (USize.toNat (Code.n c))
set_option hygiene false in
local notation "cls(" c ", " t ")" => (List.range (USize.toNat (Code.n c))).filter fun i =>
  Verify.groupOf (Column.idAt (Code.b c) (Code.w c)) (USize.toNat (Code.n c)) i == t
set_option hygiene false in
local notation "pre(" c ", " j ")" => List.sum (List.map (fun t => List.length (cls(c, t))) (List.range j))

/-- **`segments c` as `symDiv` reads it**: `segments_spec`, plus the classes cover the `n` rows, and class `t`
    is the rows whose code is that of its first row. Hypotheses: `segments_spec`'s. -/
theorem seg_facts (c : Code) (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
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
set_option hygiene false in
local notation "T(" j ")" => UInt64.toNat (Column.bitsAt s (j * 8) 8)

set_option maxHeartbeats 800000 in
/-- **`symDiv`'s set ids, read back**: over the key codes `rk`, `sk` and the joint value codes `v0`, `v1` of `R`
    and `S`, `symDiv`'s `ids` holds one long per key class of `rk`, then one per key class of `sk`; a class `i` of
    `rk` and a class `j` of `sk` get one id exactly when they hold one set of value codes. Stated over any codes,
    so the statement holds no `Obj.codes`. Hypotheses: the codes well formed, on one value lane, the value codes
    counting `rk`'s and `sk`'s rows; `nR` is `rk`'s count; the counts fit; `segments`, `ss`, `sid` by their
    defining equations. -/
theorem sym_ids (rk sk v0 v1 : Code)
    (rkw : rk.w = 1 ∨ rk.w = 2 ∨ rk.w = 4 ∨ rk.w = 8 ∨ rk.w = 16 ∨ rk.w = 32 ∨ rk.w = 64)
    (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (rkc : rk.w < 8 → rk.card < USize.size ∧ ∀ i < rk.n.toNat, Column.idAt rk.b rk.w i < rk.card)
    (skw : sk.w = 1 ∨ sk.w = 2 ∨ sk.w = 4 ∨ sk.w = 8 ∨ sk.w = 16 ∨ sk.w = 32 ∨ sk.w = 64)
    (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (skc : sk.w < 8 → sk.card < USize.size ∧ ∀ i < sk.n.toNat, Column.idAt sk.b sk.w i < sk.card)
    (v0w : v0.w = 1 ∨ v0.w = 2 ∨ v0.w = 4 ∨ v0.w = 8 ∨ v0.w = 16 ∨ v0.w = 32 ∨ v0.w = 64)
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
  have v1w : v1.w = 1 ∨ v1.w = 2 ∨ v1.w = 4 ∨ v1.w = 8 ∨ v1.w = 16 ∨ v1.w = 32 ∨ v1.w = 64 := by rw [hvw]; exact v0w
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
  have hw' : cc.w = 1 ∨ cc.w = 2 ∨ cc.w = 4 ∨ cc.w = 8 ∨ cc.w = 16 ∨ cc.w = 32 ∨ cc.w = 64 := by rw [ccw]; exact v0w
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

-- the pairs `(i, j)` `join l r` answers, as `join_rows` lists them: row `i` of `l`, row `j` of `r`, equal codes
set_option quotPrecheck false in
local notation "jp(" l ", " r ")" => ((List.range (Code.n l).toNat).flatMap fun i =>
  ((List.range (Code.n r).toNat).filter fun j =>
    Column.idAt (Code.b r) (Code.w r) j == Column.idAt (Code.b l) (Code.w l) i).map (i, ·))

/-- **`symDiv`'s joined classes**: `lc`, `rc`, the two halves of `sym_ids`'s `sid` as long codes, are well formed
    with one row per key class of `rk`, `sk`; `join lc rc` pairs a class `k` of `rk` with a class `l` of `sk`
    exactly when they hold one set of value codes. Hypotheses: those of `sym_ids`, and `lc`, `rc` by their
    defining equations. -/
theorem sym_pairs (rk sk v0 v1 : Code)
    (rkw : rk.w = 1 ∨ rk.w = 2 ∨ rk.w = 4 ∨ rk.w = 8 ∨ rk.w = 16 ∨ rk.w = 32 ∨ rk.w = 64)
    (rks : rk.b.size = (rk.n.toNat * rk.w + 7) / 8)
    (rkc : rk.w < 8 → rk.card < USize.size ∧ ∀ i < rk.n.toNat, Column.idAt rk.b rk.w i < rk.card)
    (skw : sk.w = 1 ∨ sk.w = 2 ∨ sk.w = 4 ∨ sk.w = 8 ∨ sk.w = 16 ∨ sk.w = 32 ∨ sk.w = 64)
    (sks : sk.b.size = (sk.n.toNat * sk.w + 7) / 8)
    (skc : sk.w < 8 → sk.card < USize.size ∧ ∀ i < sk.n.toNat, Column.idAt sk.b sk.w i < sk.card)
    (v0w : v0.w = 1 ∨ v0.w = 2 ∨ v0.w = 4 ∨ v0.w = 8 ∨ v0.w = 16 ∨ v0.w = 32 ∨ v0.w = 64)
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

#print axioms sym_pairs
#print axioms sym_ids
#print axioms bitsAt_extract
#print axioms concat_two
#print axioms block_slice
#print axioms seg_facts

end LeetQ.Rel.Rep
