/-
  `Obj.sortBy` and `Code.grade`, read back: every grade kernel sorts `til m`, so a grade is a permutation of
  the rows it reads, and `sortBy`'s answer holds the rows it was handed, each once.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CodesAll
import LeetQ.Run.KernelWF.Reduce
import LeetQ.Rel.KernelWF.MemberSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- Element `j` of `ids b` is the long `j` of `b`. -/
theorem ids_getElem {b : ByteArray} {j : Nat} (hj : j < (ids b).length) :
    (ids b)[j] = (Column.bitsAt b (j * 8) 8).toNat := (ids_get rfl hj).symm

/-- A sort of `til m` written as longs reads back as a permutation of `til m`. -/
theorem ids_sort_range (m : Nat) (le : Nat → Nat → Bool) (hm : m < 2 ^ 64) :
    (ids (Order.indices ((List.range m).mergeSort le))).Perm (List.range m) := by
  have hp := List.mergeSort_perm (List.range m) le
  rw [ids_indices _ fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) hm]
  exact hp

/-- **`gather 8 src idx`, read back** at in-range indices: `src`'s long at each index of `idx`. -/
theorem ids_gather8 {src idx : ByteArray} (h : ∀ t ∈ ids idx, t < len src) :
    ids (gather 8 src idx) = (ids idx).map fun t => (ids src).getD t 0 := by
  apply List.ext_getElem
  · simp only [List.length_map, ← len_eq_ids, gather_len]
  · intro j h1 h2
    have h2' : j < (ids idx).length := by simpa using h2
    have hj : j < len idx := by rw [len_eq_ids]; exact h2'
    have hm : (Column.bitsAt idx (j * 8) 8).toNat < len src := by
      rw [← ids_getElem h2']; exact h _ (List.getElem_mem h2')
    have hm' : (ids idx)[j] < (ids src).length := by rw [← len_eq_ids, ids_getElem h2']; exact hm
    rw [ids_getElem h1, List.getElem_map, gather8_get hj hm, ← ids_getElem h2', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hm', Option.getD_some, ids_getElem hm']

/-- **`gather 8 p g` at a permutation `g` of `p`'s positions holds `p`'s longs, each once.** -/
theorem gather_perm {p g : ByteArray} (hg : (ids g).Perm (List.range (len p))) :
    (ids (gather 8 p g)).Perm (ids p) := by
  rw [ids_gather8 fun t ht => List.mem_range.1 (hg.mem_iff.1 ht)]
  refine (hg.map _).trans (List.Perm.of_eq ?_)
  apply List.ext_getElem
  · simp [← len_eq_ids]
  · intro j _ h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]

/-- **`Code.grade` of a well-formed code is a stable sort of its rows**: a permutation of `til n`, ascending in
    a key `κ` that agrees exactly where the codes do, ties in row order — `grade` at the lane's layout,
    `gradeLane` at `2`/`4` bits and past an `i16`/`i32` sign bit. Hypotheses: the lane is one a `Code` takes and
    the payload holds exactly its `n` codes. -/
theorem grade_code (c : Code) (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8) :
    (ids c.grade).Perm (List.range c.n.toNat) ∧ ∃ κ : Nat → Nat,
      (∀ i j, i < c.n.toNat → j < c.n.toNat → (κ i = κ j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) ∧
      (ids c.grade).Pairwise fun i j => κ i ≤ κ j ∧ (κ j ≤ κ i → i < j) := by
  have h0 : 0 < c.w := by omega
  have h64 : c.w ≤ 64 := by omega
  have hl : (ids (Order.gradeLane false c.n c.w.toUSize c.b)).Perm (List.range c.n.toNat) ∧ ∃ κ : Nat → Nat,
      (∀ i j, i < c.n.toNat → j < c.n.toNat → (κ i = κ j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) ∧
      (ids (Order.gradeLane false c.n c.w.toUSize c.b)).Pairwise fun i j => κ i ≤ κ j ∧ (κ j ≤ κ i → i < j) := by
    obtain ⟨hp, hsrt⟩ := gradeLane_spec false c.n c.w.toUSize c.b
    have hcap : c.w * c.n.toNat ≤ 8 * c.b.size := by rw [hs, Nat.mul_comm]; omega
    rw [lane_toNat h64, idsCap_full h0 hcap] at hp
    rw [lane_toNat h64] at hsrt
    exact ⟨hp, fun i => Column.idAt c.b c.w i, fun _ _ _ _ => Iff.rfl,
      hsrt.imp fun ⟨h1, h2⟩ => ⟨by simpa using h1, fun h => h2 (by simpa using h)⟩⟩
  unfold Code.grade Code.kind
  split
  next k hk =>
    split
    next => exact hl
    next =>
      obtain ⟨hp, hsrt⟩ := grade_spec k false c.n c.b
      rw [Nat.min_eq_left (avail_lane hk hs)] at hp
      refine ⟨hp, fun i => (Order.keyAt k c.b i).toNat, fun i j _ _ => ?_,
        hsrt.imp fun ⟨h1, h2⟩ => ⟨?_, fun h => h2 ?_⟩⟩
      · show (Order.keyAt k c.b i).toNat = (Order.keyAt k c.b j).toNat ↔ _
        rw [← keyAt_iff_idAt hk]; exact ⟨fun e => UInt64.toNat_inj.1 e, fun e => by rw [e]⟩
      · simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1; exact UInt64.le_iff_toNat_le.1 h1
      · simp only [keyOrd, Bool.false_eq_true, ↓reduceIte]; exact UInt64.le_iff_toNat_le.2 h
  next => exact hl

/-- **Every grade `gradeColumn` answers ascending is a sort of `til m`** (`indices` of a `mergeSort`): `grade`,
    `gradeFoR`, `gradeSyms`, `gradeIds`, `gradeGuid` alike. -/
theorem gradeColumn_sort {t : QAtomicType} {n : USize} {e v : Enc} (h : gradeColumn t false n e = some v) :
    ∃ m le, v = .bytes (Order.indices ((List.range m).mergeSort le)) := by
  unfold gradeColumn at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  all_goals first
    | (cases h; exact ⟨_, _, rfl⟩)
    | (obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨_, _, rfl⟩)
    | (split at h
       · cases h
       split at h
       · cases h
       split at h
       · cases h; exact ⟨_, _, rfl⟩
       · split at h
         · split at h
           · cases h
           · cases h; exact ⟨_, _, rfl⟩
         · cases h)

/-- **The grade of `kc`'s codes gathered at `vp` is a permutation of `vp`'s positions.** Hypotheses: `kc` well
    formed, every long of `vp` one of its rows. -/
theorem grade_gather_perm (kc : Code) (hw : laneOK(kc.w)) (hs : kc.b.size = (kc.n.toNat * kc.w + 7) / 8)
    (vp : ByteArray) (hl : len vp < USize.size) (hvp : ∀ t ∈ ids vp, t < kc.n.toNat) :
    (ids (kc.gather vp).grade).Perm (List.range (len vp)) := by
  have hvl : ∀ j < len vp, (Column.bitsAt vp (j * 8) 8).toNat < kc.n.toNat := fun j hj => by
    have hj' : j < (ids vp).length := by rw [← len_eq_ids]; exact hj
    rw [← ids_getElem hj']; exact hvp _ (List.getElem_mem hj')
  have hcb : 8 ≤ kc.w → 8 * kc.b.size = kc.w * kc.n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  obtain ⟨hGw, hGn, -, -⟩ := gather_spec kc vp hl hw hcb hvl
  have hGs := gather_size kc vp hl hw
  generalize kc.gather vp = G at hGw hGn hGs
  rw [← hGw] at hw
  rw [← hGn, ← hGw] at hGs
  rw [← hGn]; exact (grade_code G hw hGs).1

/-- A gathered long payload holds whole longs. -/
theorem gather_size8 (s i : ByteArray) : (gather 8 s i).size = len (gather 8 s i) * 8 := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  simp only [len, gather, KernelWF.gatherBytes_size, h8]; omega

/-- **Two long payloads end to end, read back**: long `d` is the first's below its count, the second's past
    it, the first holding exactly its longs. -/
theorem concat2_get {a c : ByteArray} (ha : a.size = len a * 8) (d : Nat) :
    Column.bitsAt (concatBytes #[a, c]) (d * 8) 8 =
      if d < len a then Column.bitsAt a (d * 8) 8 else Column.bitsAt c ((d - len a) * 8) 8 := by
  have e : concatBytes #[a, c] = a ++ c := by simp [concatBytes]
  rw [e]
  split
  · exact KernelWF.bitsAt_congr fun j hj => by
      rw [ByteArray.data_append, Array.getElem?_append_left (by rw [ByteArray.size_data]; omega)]
  · exact KernelWF.bitsAt_congr fun j hj => by
      rw [ByteArray.data_append, Array.getElem?_append_right (by rw [ByteArray.size_data]; omega),
        ByteArray.size_data]
      exact congrArg (c.data[·]?) (by omega)

/-- Two long payloads end to end, read back as one list. -/
theorem ids_concat2 {a c : ByteArray} (ha : a.size = len a * 8) : ids (concatBytes #[a, c]) = ids a ++ ids c := by
  have hs : len (concatBytes #[a, c]) = len a + len c := by
    simp only [len, KernelWF.concatBytes_size, List.map, Array.toList, List.sum_cons, List.sum_nil] at ha ⊢
    omega
  apply List.ext_getElem
  · rw [List.length_append, ← len_eq_ids, ← len_eq_ids, ← len_eq_ids, hs]
  · intro d h1 h2
    rw [ids_getElem h1, concat2_get ha]
    by_cases hd : d < len a
    · have hd' : d < (ids a).length := by rw [← len_eq_ids]; exact hd
      rw [if_pos hd, List.getElem_append_left hd', ids_getElem hd']
    · have hd' : (ids a).length ≤ d := by rw [← len_eq_ids]; omega
      have hc : d - (ids a).length < (ids c).length := by rw [List.length_append] at h2; omega
      rw [if_neg hd, List.getElem_append_right hd', ids_getElem hc, len_eq_ids]

/-- `til |l|` read through `l` is `l`. -/
theorem map_range_getD (l : List Nat) : (List.range l.length).map (fun t => l.getD t 0) = l :=
  List.ext_getElem (by simp) fun j _ h2 => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2)]

/-- **`q` split by a bitmap `g` of its positions, the unmarked rows first, holds `q`'s longs, each once.** -/
theorem split_perm (q g : ByteArray) (hq : len q < USize.size) :
    (ids (gather 8 q (whereBits (len q).toUSize (Ew.notBits (len q).toUSize g))) ++
      ids (gather 8 q (whereBits (len q).toUSize g))).Perm (ids q) := by
  have hm : ((len q).toUSize).toNat = len q := USize.toNat_ofNat_of_lt' hq
  have hin : ∀ b, ∀ t ∈ ids (whereBits (len q).toUSize b), t < len q := fun b t ht => by
    rw [(whereBits_ids _ b).1, List.mem_filter, List.mem_range, hm] at ht; exact ht.1
  rw [ids_gather8 (hin _), ids_gather8 (hin _), (whereBits_ids _ _).1, (whereBits_ids _ _).1,
    List.filter_congr (p := Column.bitAt (Ew.notBits _ g)) (q := fun i => !Column.bitAt g i)
      (fun i hi => notBits_bitAt _ g (List.mem_range.1 hi)), hm]
  refine List.perm_append_comm.trans ?_
  rw [← List.map_append]
  refine ((List.filter_append_perm _ _).map _).trans ?_
  rw [len_eq_ids, map_range_getD]

/-- `til k` as longs, read back. -/
theorem ids_tilLongs (k : USize) : ids (tilLongs k) = List.range k.toNat :=
  List.ext_getElem (by rw [← len_eq_ids, len_tilLongs, List.length_range]) fun j h1 h2 => by
    rw [ids_getElem h1, List.getElem_range, tilLongs_get (by simpa using h2)]

/-- **`sortSide` permutes the rows it is handed**, given that its sort does. -/
theorem sortSide_perm {B : Obj} {s : USize} (x : Vals B s) (srt : {k : USize} → Vals B k → ByteArray → ByteArray)
    (hs : ∀ {k : USize} (v : Vals B k) (r : ByteArray), len r < USize.size → (ids (srt v r)).Perm (ids r))
    (ps q : ByteArray) : (ids (sortSide x srt ps q)).Perm (ids q) := by
  unfold sortSide
  split
  next h =>
    have hm : ((len q).toUSize).toNat = len q := USize.toNat_ofNat_of_lt' h.2
    refine gather_perm ?_
    have := hs (Vals.pickShared B x (gather 8 ps q) (len q).toUSize (by rw [gather_len]; exact hm.symm))
      (tilLongs (len q).toUSize) (by rw [len_tilLongs, hm]; exact h.2)
    rw [ids_tilLongs] at this; exact this.trans (List.Perm.of_eq (by rw [hm]))
  next => exact List.Perm.refl _

theorem sortSide_size8 {B : Obj} {s : USize} (x : Vals B s) (srt : {k : USize} → Vals B k → ByteArray → ByteArray)
    (ps q : ByteArray) (hq : q.size = len q * 8) : (sortSide x srt ps q).size = len (sortSide x srt ps q) * 8 := by
  unfold sortSide; split
  · exact gather_size8 _ _
  · exact hq

/-- **`Obj.sortBy` permutes the rows it is handed**: its answer holds the longs of `p`, each once, at every
    side, wherever `len p` fits a `USize`. -/
theorem sortBy_permutes (A : Obj) {n : USize} (c : Vals A n) (p : ByteArray) (hl : len p < USize.size) :
    (ids (A.sortBy c p)).Perm (ids p) := by
  induction A generalizing n p with
  | atom t =>
    have hx := pick_len t ⟨_, c⟩ p hl
    have hc : (ids (Code.grade (codes t #v[pick t ⟨_, c⟩ p])[0])).Perm (List.range (len p)) := by
      obtain ⟨hw, hn, hs, -⟩ := codes_atom_wf t (pick t ⟨_, c⟩ p)
      have := (grade_code _ hw hs).1
      rw [show ((Obj.codes (.atom t) #v[pick t ⟨_, c⟩ p])[0]).n = _ from hn, hx] at this
      exact this
    simp only [Obj.sortBy, Obj.sortByC]
    split
    next g hg =>
      obtain ⟨m, le, hv⟩ := gradeColumn_sort hg
      cases hv
      have hwf := gradeColumn_wf (pick t ⟨_, c⟩ p).2.wf hg
      simp only [Enc.WF, QAtomicType.width] at hwf
      rw [indices_size, List.length_mergeSort, List.length_range, hx] at hwf
      have hm : m = len p := by omega
      subst hm
      exact gather_perm (ids_sort_range _ le (Nat.lt_of_lt_of_le hl (by have := USize.size_le; omega)))
    next => exact gather_perm hc
  | prod a b iha ihb =>
    have h2 := ihb c.2 p hl
    have hl2 : len (b.sortBy c.2 p) < USize.size := by rw [len_eq_ids, h2.length_eq, ← len_eq_ids]; exact hl
    exact (iha c.1 _ hl2).trans h2
  | arr b ih =>
    simp only [Obj.sortBy, Obj.sortByC]
    generalize List.range _ = ts
    induction ts with
    | nil => exact List.Perm.refl _
    | cons t ts iht =>
      simp only [List.foldr_cons]
      generalize List.foldr _ p ts = q at iht ⊢
      split
      next hq =>
        rw [ids_concat2 (gather_size8 _ _)]
        exact (((List.Perm.refl _).append (sortSide_perm _ _ (fun v r hr => ih v r hr) _ _)).trans
          (split_perm q _ hq)).trans iht
      next => exact iht
  | sum a b iha ihb =>
    simp only [Obj.sortBy, Obj.sortByC]
    split
    next h =>
      rw [ids_concat2 (sortSide_size8 _ _ _ _ (gather_size8 _ _))]
      exact ((sortSide_perm _ _ (fun v r hr => iha v r hr) _ _).append
        (sortSide_perm _ _ (fun v r hr => ihb v r hr) _ _)).trans (split_perm p _ h)
    next h => exact absurd hl h

/-- **`Obj.sortBy` permutes the rows it is handed** (`sortBy_permutes`); the fit and the range of `p` are
    not needed. -/
theorem sortBy_perm (A : Obj) {n : USize} (c : Vals A n) (_hf : A.CodesFit (#v[⟨n, c⟩] : Vector (Part A) 1))
    (p : ByteArray) (hl : len p < USize.size) (_hp : ∀ t ∈ ids p, t < n.toNat) :
    (ids (A.sortBy c p)).Perm (ids p) := sortBy_permutes A c p hl

/-- **`Obj.sortByC`'s permutation holds the rows it is handed under its bit**: `sortBy_perm`, the bit the codes'
    (`sortByC_snd`), so a fit (`codesC_fits`). -/
theorem sortByC_perm (A : Obj) {n : USize} (c : Vals A n) (p : ByteArray) (hb : (A.sortByC c p).2 = true)
    (hl : len p < USize.size) (hp : ∀ t ∈ ids p, t < n.toNat) : (ids (A.sortByC c p).1).Perm (ids p) :=
  sortBy_perm A c (Obj.codesC_fits A _ (Obj.sortByC_snd A c p ▸ hb)) p hl hp

/-- **`transpose`'s row order groups the keys**: `kc`'s codes at `vp`, graded stably and read back through `vp`
    (`p = vp@grade(kc@vp)`), hold every row once, and equal codes stand together along `p`; the grade holds
    `vp`'s positions, each once, two of one code in `vp`'s order. Hypotheses: `kc` well formed, `vp` a
    permutation of its rows (`sortBy_perm` at `til n`). -/
theorem grade_gather_group (kc : Code)
    (hw : laneOK(kc.w))
    (hs : kc.b.size = (kc.n.toNat * kc.w + 7) / 8) (vp : ByteArray) (hvp : (ids vp).Perm (List.range kc.n.toNat)) :
    (ids (gather 8 vp (kc.gather vp).grade)).Perm (List.range kc.n.toNat) ∧
      (∀ s t u, s ≤ t → t ≤ u → u < kc.n.toNat →
        Column.idAt kc.b kc.w (Column.bitsAt (gather 8 vp (kc.gather vp).grade) (s * 8) 8).toNat =
          Column.idAt kc.b kc.w (Column.bitsAt (gather 8 vp (kc.gather vp).grade) (u * 8) 8).toNat →
        Column.idAt kc.b kc.w (Column.bitsAt (gather 8 vp (kc.gather vp).grade) (t * 8) 8).toNat =
          Column.idAt kc.b kc.w (Column.bitsAt (gather 8 vp (kc.gather vp).grade) (s * 8) 8).toNat) ∧
      (ids (kc.gather vp).grade).Perm (List.range kc.n.toNat) ∧
      (ids (kc.gather vp).grade).Pairwise fun i j =>
        Column.idAt kc.b kc.w (Column.bitsAt vp (i * 8) 8).toNat =
          Column.idAt kc.b kc.w (Column.bitsAt vp (j * 8) 8).toNat → i < j := by
  have hN : len vp = kc.n.toNat := by rw [len_eq_ids, hvp.length_eq, List.length_range]
  have hl : len vp < USize.size := by rw [hN]; exact kc.n.toNat_lt_size
  have hvl : ∀ j < len vp, (Column.bitsAt vp (j * 8) 8).toNat < kc.n.toNat := fun j hj => by
    have hj' : j < (ids vp).length := by rw [← len_eq_ids]; exact hj
    rw [← ids_getElem hj']; exact List.mem_range.1 (hvp.mem_iff.1 (List.getElem_mem hj'))
  have hcb : 8 ≤ kc.w → 8 * kc.b.size = kc.w * kc.n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  obtain ⟨hGw, hGn, -, hGid⟩ := gather_spec kc vp hl hw hcb hvl
  have hGs := gather_size kc vp hl hw
  generalize hG : kc.gather vp = G at hGw hGn hGid hGs
  rw [← hGw] at hw
  rw [← hGn, ← hGw] at hGs
  obtain ⟨hgp, κ, hκ, hsrt⟩ := grade_code G hw hGs
  rw [hGn, hN] at hgp hκ
  rw [hGw] at hκ
  have hgl : (ids G.grade).length = kc.n.toNat := by rw [hgp.length_eq, List.length_range]
  -- `g[s]`, the grade's row `s`, below the count; `p`'s long `s` is `vp`'s long `g[s]`
  have hg : ∀ s < kc.n.toNat, (Column.bitsAt G.grade (s * 8) 8).toNat < kc.n.toNat := fun s hs' => by
    have h : s < (ids G.grade).length := by rw [hgl]; exact hs'
    rw [← ids_getElem h]; exact List.mem_range.1 (hgp.mem_iff.1 (List.getElem_mem h))
  have hp : ∀ s < kc.n.toNat, Column.idAt kc.b kc.w (Column.bitsAt (gather 8 vp G.grade) (s * 8) 8).toNat =
      Column.idAt G.b kc.w (Column.bitsAt G.grade (s * 8) 8).toNat := fun s hs' => by
    rw [gather8_get (by rw [len_eq_ids, hgl]; exact hs') (by rw [hN]; exact hg s hs'),
      hGid _ (by rw [hN]; exact hg s hs')]
  have hmono : ∀ s t, s ≤ t → t < kc.n.toNat →
      κ (Column.bitsAt G.grade (s * 8) 8).toNat ≤ κ (Column.bitsAt G.grade (t * 8) 8).toNat := fun s t hst ht => by
    rcases Nat.lt_or_eq_of_le hst with h | rfl
    · have := (List.pairwise_iff_getElem.1 hsrt s t (by rw [hgl]; omega) (by rw [hgl]; exact ht) h).1
      rwa [ids_getElem, ids_getElem] at this
    · exact Nat.le_refl _
  -- two grade positions of one code: `grade`'s ties keep row order
  have hstab : (ids G.grade).Pairwise fun i j =>
      Column.idAt kc.b kc.w (Column.bitsAt vp (i * 8) 8).toNat =
        Column.idAt kc.b kc.w (Column.bitsAt vp (j * 8) 8).toNat → i < j :=
    hsrt.imp_of_mem fun {i j} hi hj h e => by
      have hi' := List.mem_range.1 (hgp.mem_iff.1 hi); have hj' := List.mem_range.1 (hgp.mem_iff.1 hj)
      rw [← hGid i (by rw [hN]; exact hi'), ← hGid j (by rw [hN]; exact hj')] at e
      exact h.2 (Nat.le_of_eq ((hκ _ _ hi' hj').2 e).symm)
  subst hG
  refine ⟨(gather_perm (by rw [hN]; exact hgp)).trans hvp, fun s t u hst htu hu e => ?_, hgp, hstab⟩
  rw [hp s (by omega), hp u hu] at e
  rw [hp t (by omega), hp s (by omega)]
  have e' := (hκ _ _ (hg s (by omega)) (hg u hu)).2 e
  have a := hmono s t hst (by omega); have b := hmono t u htu hu
  exact (hκ _ _ (hg t (by omega)) (hg s (by omega))).1 (by omega)

#print axioms grade_gather_group
#print axioms grade_gather_perm
#print axioms ids_gather8
#print axioms gather_perm
#print axioms grade_code
#print axioms sortBy_perm

end LeetQ.Rel.Alg
