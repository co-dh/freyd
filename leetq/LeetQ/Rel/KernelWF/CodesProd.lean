/-
  What `Code.cat` and `Code.cut` CONTAIN: code `i` of a concatenation is code `i` of the part it falls in,
  moved past the counts before that part, and `cut` reads that back. Then the joint codes of a side of
  several parts, read through `raze`, `groupIdsColumn`, `Code.ofIds` and `cut`.
-/
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.RazeSpec
import LeetQ.Rel.KernelWF.Lane
import QLean.Verify.Codes
import QLean.Verify.SymFind

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## Offsets -/

/-- A `USize` sum whose `Nat` sum fits a `USize` is that `Nat` sum. -/
theorem usize_foldl_add : ∀ (l : List USize) (a : USize), a.toNat + (l.map (·.toNat)).sum < USize.size →
    (l.foldl (· + ·) a).toNat = a.toNat + (l.map (·.toNat)).sum
  | [], a, _ => by simp
  | x :: l, a, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at h ⊢
    have hx : (a + x).toNat = a.toNat + x.toNat := by rw [USize.toNat_add, Nat.mod_eq_of_lt (show a.toNat + x.toNat < USize.size by omega)]
    rw [usize_foldl_add l (a + x) (by rw [hx]; omega), hx, Nat.add_assoc]

/-- The counts before part `k` and part `k`'s own lie within the whole. -/
theorem take_sum_le : ∀ (l : List Nat) {k : Nat} (hk : k < l.length), (l.take k).sum + l[k] ≤ l.sum
  | [], _, hk => absurd hk (by simp)
  | x :: l, 0, _ => by simp
  | x :: l, k + 1, hk => by
    have := take_sum_le l (k := k) (by simpa using hk)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-! ## `Code.cut` -/

/-- **Part `k` of `c.cut ns` reads `c` past the counts before it**, the counts summing to `c.n`: a byte
    extract at a byte lane, `cycleBits` at a bit, `cycleIds` at `2`/`4` bits. -/
theorem cut_get {p : Nat} (c : Code) (ns : Vector USize p)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : (ns.toList.map (·.toNat)).sum = c.n.toNat) {k : Nat} (hk : k < p) :
    (c.cut ns)[k].w = c.w ∧ (c.cut ns)[k].n = ns[k] ∧ (c.cut ns)[k].card = c.card ∧
      ∀ i < ns[k].toNat, Column.idAt (c.cut ns)[k].b c.w i =
        Column.idAt c.b c.w (((ns.toList.take k).map (·.toNat)).sum + i) := by
  have hle := take_sum_le (ns.toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  unfold Code.cut
  by_cases hp : p = 1
  · subst hp
    have hk0 : k = 0 := by omega
    subst hk0
    rw [if_pos rfl]
    simp only [Vector.getElem_replicate, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
    have hn : ns.toList = [ns[0]] := by
      apply List.ext_getElem (by simp) fun j h1 _ => ?_
      simp at h1; subst h1; simp
    rw [hn] at hs
    exact ⟨by simp, USize.toNat_inj.1 (by simpa using hs.symm), by simp, fun _ _ => by simp⟩
  rw [if_neg hp]
  simp only [Vector.getElem_mapIdx]
  refine ⟨by simp, by simp, by simp, fun i hi => ?_⟩
  have ho : ((ns.toArray.extract 0 k).foldl (· + ·) 0).toNat = ((ns.toList.take k).map (·.toNat)).sum := by
    rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero,
      usize_foldl_add _ _ (by simp only [USize.toNat_zero, Nat.zero_add]; exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ ns[k].toNat) hle) c.n.toNat_lt_size)]
    rw [USize.toNat_zero, Nat.zero_add]; rfl
  generalize (ns.toArray.extract 0 k).foldl (· + ·) 0 = o at ho
  rw [← ho]
  have hn : o.toNat + ns[k].toNat ≤ c.n.toNat := by rw [ho]; exact hle
  rw [if_neg (by simp only [beq_iff_eq]; intro h; rw [h] at hi; simp at hi)]
  by_cases h8 : c.w % 8 = 0
  · rw [if_pos (by simpa using h8)]
    obtain ⟨q, hq, hq8⟩ : ∃ q, c.w = 8 * q ∧ q ≤ 8 := ⟨c.w / 8, by omega, by omega⟩
    rw [hq, idAt_lane _ hq8, idAt_lane _ hq8, show 8 * q / 8 = q by omega, bitsAt_extract]
    · congr 2; rw [Nat.add_mul, Nat.mul_comm q]
    · have : (i + 1) * q ≤ ns[k].toNat * q := Nat.mul_le_mul_right q hi
      rw [Nat.add_mul, Nat.one_mul] at this; rw [Nat.mul_add, Nat.mul_comm q ns[k].toNat]; omega
  rw [if_neg (by simpa using h8)]
  by_cases h1 : c.w = 1
  · rw [if_pos (by simpa using h1), h1, idAt_one, idAt_one]
    unfold cycleBits
    rw [bitAt_packOf _ _ _ hi, Nat.mod_eq_of_lt (by omega)]
  rw [if_neg (by simpa using h1)]
  have hw64 : c.w ≤ 64 := by omega
  unfold cycleIds
  rw [lane_toNat hw64, idAt_packIds (f := fun j => Column.idAt c.b c.w ((o.toNat + j) % c.n.toNat)) (by omega) hi
    (idAt_lt _ _ _ hw64), Nat.mod_eq_of_lt (by omega)]

/-- **Part `k` of `c.cut ns` is `⌈ns[k]·w/8⌉` bytes**, `c` itself `⌈c.n·w/8⌉`. -/
theorem cut_size {p : Nat} (c : Code) (ns : Vector USize p)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : (ns.toList.map (·.toNat)).sum = c.n.toNat) (hsz : c.b.size = (c.n.toNat * c.w + 7) / 8)
    {k : Nat} (hk : k < p) : (c.cut ns)[k].b.size = (ns[k].toNat * c.w + 7) / 8 := by
  have hle := take_sum_le (ns.toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  obtain ⟨-, hn, -, -⟩ := cut_get c ns hw hs hk
  unfold Code.cut at hn ⊢
  by_cases hp : p = 1
  · subst hp; rw [if_pos rfl] at hn ⊢; simp only [Vector.getElem_replicate] at hn ⊢; rw [← hn, hsz]
  rw [if_neg hp]
  simp only [Vector.getElem_mapIdx]
  have ho : ((ns.toArray.extract 0 k).foldl (· + ·) 0).toNat ≤ ((ns.toList.take k).map (·.toNat)).sum := by
    rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero,
      usize_foldl_add _ _ (by simp only [USize.toNat_zero, Nat.zero_add]; exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ ns[k].toNat) hle) c.n.toNat_lt_size)]
    rw [USize.toNat_zero, Nat.zero_add]; exact Nat.le_refl _
  generalize (ns.toArray.extract 0 k).foldl (· + ·) 0 = o at ho
  by_cases h0 : ns[k] = 0
  · rw [if_pos (by simpa using h0), h0]; simp only [USize.toNat_zero, Nat.zero_mul, Nat.zero_add]; rfl
  rw [if_neg (by simpa using h0)]
  by_cases h8 : c.w % 8 = 0
  · rw [if_pos (by simpa using h8), ByteArray.size_extract, hsz]
    obtain ⟨q, hq⟩ : ∃ q, c.w = 8 * q := ⟨c.w / 8, by omega⟩
    rw [hq, show 8 * q / 8 = q by omega]
    have h1 : q * (o.toNat + ns[k].toNat) ≤ c.n.toNat * q := by
      rw [Nat.mul_comm c.n.toNat]; exact Nat.mul_le_mul_left q (by omega)
    rw [show (c.n.toNat * (8 * q) + 7) / 8 = c.n.toNat * q by rw [Nat.mul_comm 8 q, ← Nat.mul_assoc]; omega,
      show (ns[k].toNat * (8 * q) + 7) / 8 = ns[k].toNat * q by rw [Nat.mul_comm 8 q, ← Nat.mul_assoc]; omega,
      Nat.min_eq_left h1, Nat.mul_add, Nat.mul_comm q ns[k].toNat]; omega
  rw [if_neg (by simpa using h8)]
  by_cases h1 : c.w = 1
  · rw [if_pos (by simpa using h1), h1]; unfold cycleBits; rw [KernelWF.packOf_size]; simp
  rw [if_neg (by simpa using h1)]
  unfold cycleIds
  rw [lane_toNat (by omega), packIds_size (by omega)]

/-! ## `Code.cat` -/

/-- A running sum is the list's sum. -/
theorem foldl_add_sum {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat), l.foldl (fun s c => s + f c) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_sum f l]; omega

/-- Element `(lengths before part k) + i` of the parts laid end to end is part `k`'s element `i`. -/
theorem flatMap_offset {α β : Type} (f : α → List β) (len : α → Nat) (hl : ∀ c, (f c).length = len c) :
    ∀ (l : List α) {k : Nat} (hk : k < l.length) {i : Nat}, i < len l[k] →
      (l.flatMap f)[((l.take k).map len).sum + i]? = (f l[k])[i]?
  | [], _, hk, _, _ => absurd hk (by simp)
  | x :: l, 0, _, i, hi => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons]
    exact List.getElem?_append_left (by rw [hl]; exact hi)
  | x :: l, k + 1, hk, i, hi => by
    have ih := flatMap_offset f len hl l (k := k) (by simpa using hk) (i := i) hi
    simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [Nat.add_assoc, List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left, ih]

/-- Appending on the right keeps the bytes already there. -/
theorem foldl_append_prefix : ∀ (l : List ByteArray) (acc : ByteArray) {x : Nat}, x < acc.size →
    (l.foldl (· ++ ·) acc).data[x]? = acc.data[x]?
  | [], _, _, _ => rfl
  | b :: l, acc, x, hx => by
    rw [List.foldl_cons, foldl_append_prefix l _ (by rw [ByteArray.size_append]; omega), ByteArray.data_append,
      Array.getElem?_append_left (by rw [ByteArray.size_data]; exact hx)]

/-- Byte `j` of part `k` lies past `acc` and the parts before it. -/
theorem foldl_append_get : ∀ (l : List ByteArray) (acc : ByteArray) {k : Nat} (hk : k < l.length) {j : Nat},
    j < l[k].size → (l.foldl (· ++ ·) acc).data[acc.size + ((l.take k).map (·.size)).sum + j]? = l[k].data[j]?
  | [], _, _, hk, _, _ => absurd hk (by simp)
  | b :: l, acc, 0, _, j, hj => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.foldl_cons]
    rw [foldl_append_prefix l _ (by rw [ByteArray.size_append]; exact Nat.add_lt_add_left hj _), ByteArray.data_append,
      Array.getElem?_append_right (by rw [ByteArray.size_data]; omega), ByteArray.size_data, Nat.add_sub_cancel_left]
    rfl
  | b :: l, acc, k + 1, hk, j, hj => by
    have ih := foldl_append_get l (acc ++ b) (k := k) (by simpa using hk) (j := j) hj
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.foldl_cons, List.getElem_cons_succ]
    rw [ByteArray.size_append] at ih
    rw [← Nat.add_assoc acc.size, ih]

/-- Parts of `q` bytes a code hold `q` bytes per code in all. -/
theorem sum_size_mul (q : Nat) :
    ∀ l : List Code, (∀ c ∈ l, c.b.size = c.n.toNat * q) → (l.map (·.b.size)).sum = (l.map (·.n.toNat)).sum * q
  | [], _ => by simp
  | c :: l, h => by
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    rw [h c (by simp), sum_size_mul q l fun d hd => h d (by simp [hd])]

/-- **Code `i` of part `k` is code `(counts before k) + i` of `Code.cat`**, every part on one lane `w`,
    `⌈n·w/8⌉` bytes, its codes below its `card` at `2`/`4` bits, and the summed count a `USize`:
    `concatBits` at a bit, `concatBytes` at a byte lane, `concatIds` through each part's identity map. -/
theorem cat_get (cs : Array Code) {w : Nat}
    (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (h0 : 0 < cs.size)
    (hcw : ∀ c ∈ cs, c.w = w) (hsz : ∀ c ∈ cs, c.b.size = (c.n.toNat * w + 7) / 8)
    (hid : w = 2 ∨ w = 4 → ∀ c ∈ cs, ∀ i < c.n.toNat, Column.idAt c.b w i < c.card)
    (hN : (cs.toList.map (·.n.toNat)).sum < USize.size) :
    (Code.cat cs).w = w ∧ (Code.cat cs).n.toNat = (cs.toList.map (·.n.toNat)).sum ∧
      ∀ k (hk : k < cs.size), ∀ i < cs[k].n.toNat,
        Column.idAt (Code.cat cs).b w (((cs.toList.take k).map (·.n.toNat)).sum + i) = Column.idAt cs[k].b w i := by
  have hS : cs.foldl (fun s c => s + c.n.toNat) 0 = (cs.toList.map (·.n.toNat)).sum := by
    rw [← Array.foldl_toList, foldl_add_sum (fun c : Code => c.n.toNat), Nat.zero_add]
  have hw0 : cs[0].w = w := hcw _ (Array.getElem_mem h0)
  have hmem : ∀ k (hk : k < cs.size), cs[k] ∈ cs := fun k hk => Array.getElem_mem hk
  have hkl : ∀ k, k < cs.size → k < cs.toList.length := fun k hk => by simpa using hk
  unfold Code.cat
  simp only [dif_pos h0, hw0, need, hS, hN, ↓reduceDIte]
  refine ⟨by simp, by simp [USize.toNat_ofNat_of_lt' hN], fun k hk i hi => ?_⟩
  have hmin : min ((countBytes (cs.map (·.n))).size / 8) (cs.map (·.b)).size = cs.size := by
    rw [countBytes_size]; simp
  have hcnt : ∀ k (hk : k < cs.size), (Column.bitsAt (countBytes (cs.map (·.n))) (8 * k) 8).toNat = cs[k].n.toNat :=
    fun k hk => by rw [KernelWF.countBytes_get _ k (by simpa using hk)]; simp
  by_cases hb : w = 1
  · subst hb
    simp only [laneKind]
    rw [idAt_one, idAt_one]
    unfold concatBits
    rw [hmin]
    generalize hB : Array.flatMap _ (Array.range cs.size) = B
    have hBl : B.toList = cs.toList.flatMap fun c => (List.range c.n.toNat).map (Column.bitAt c.b) := by
      rw [← hB]
      simp only [Array.toList_flatMap, Array.toList_range, Array.toList_map]
      refine KernelWF.flatMap_range cs _ _ fun k hk => ?_
      rw [hcnt k hk, getElem!_pos _ k (by simpa using hk)]; simp
    have ho := flatMap_offset (fun c : Code => (List.range c.n.toNat).map (Column.bitAt c.b)) (·.n.toNat)
      (fun c => by simp) cs.toList (hkl k hk) (i := i) (by simpa using hi)
    rw [← hBl, Array.getElem?_toList] at ho
    simp only [Array.getElem_toList, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at ho
    rw [bitAt_packOf _ _ _ (Array.getElem?_eq_some_iff.1 ho).1, ho]; rfl
  by_cases hi8 : w = 2 ∨ w = 4
  · have hl : laneKind w = none := by rcases hi8 with rfl | rfl <;> rfl
    simp only [hl]
    have hw64 : w ≤ 64 := by omega
    unfold concatIds
    rw [hmin, lane_toNat hw64]
    generalize hB : Array.flatMap _ (Array.range cs.size) = B
    have hBl : B.toList = cs.toList.flatMap fun c => (List.range c.n.toNat).map fun i =>
        Column.idAt (Column.packIds w c.card id) w (Column.idAt c.b w i) := by
      rw [← hB]
      simp only [Array.toList_flatMap, Array.toList_range, Array.toList_map]
      refine KernelWF.flatMap_range cs _ _ fun k hk => ?_
      rw [hcnt k hk, getElem!_pos _ k (by simpa using hk), getElem!_pos _ k (by simpa using hk),
        getElem!_pos _ k (by simpa using hk)]
      simp [hcw _ (hmem k hk)]
    have ho := flatMap_offset (fun c : Code => (List.range c.n.toNat).map fun i =>
        Column.idAt (Column.packIds w c.card id) w (Column.idAt c.b w i)) (·.n.toNat)
      (fun c => by simp) cs.toList (hkl k hk) (i := i) (by simpa using hi)
    rw [← hBl, Array.getElem?_toList] at ho
    simp only [Array.getElem_toList, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at ho
    have hlt := (Array.getElem?_eq_some_iff.1 ho).1
    have hv : B[((cs.toList.take k).map (·.n.toNat)).sum + i]! =
        Column.idAt (Column.packIds w cs[k].card id) w (Column.idAt cs[k].b w i) := by
      rw [getElem!_pos B _ hlt]; exact Option.some_inj.1 ((Array.getElem?_eq_getElem hlt).symm.trans ho)
    have hx := hid hi8 _ (hmem k hk) i hi
    rw [idAt_packIds (f := fun j => B[j]!) (by omega) hlt (by show B[_]! < 2 ^ w; rw [hv]; exact idAt_lt _ _ _ hw64), hv,
      idAt_packIds (f := id) (by omega) hx (idAt_lt _ _ _ hw64)]; rfl
  obtain ⟨q, hq, hq8, hlk⟩ : ∃ q, w = 8 * q ∧ q ≤ 8 ∧ ∃ kd, laneKind w = some kd ∧ kd ≠ .bit := by
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all <;> first
      | exact ⟨1, rfl, by decide, .u8, rfl, by decide⟩ | exact ⟨2, rfl, by decide, .i16, rfl, by decide⟩
      | exact ⟨4, rfl, by decide, .i32, rfl, by decide⟩ | exact ⟨8, rfl, by decide, .i64, rfl, by decide⟩
  obtain ⟨kd, hkd, hkb⟩ := hlk
  simp only [hkd]
  rw [hq, idAt_lane _ hq8, idAt_lane _ hq8]
  congr 1
  refine KernelWF.bitsAt_congr fun j hj => ?_
  have hsq : ∀ c ∈ cs, c.b.size = c.n.toNat * q := fun c hc => by
    rw [hsz c hc, hq, Nat.mul_comm 8 q, ← Nat.mul_assoc]; omega
  have hjk : i * q + j < cs[k].b.size := by
    rw [hsq _ (hmem k hk)]
    have : (i + 1) * q ≤ cs[k].n.toNat * q := Nat.mul_le_mul_right q hi
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hg := foldl_append_get (cs.toList.map fun c : Code => c.b) ByteArray.empty (k := k) (by simpa using hk)
    (j := i * q + j) (by simpa using hjk)
  have hsum : (((cs.toList.map fun c : Code => c.b).take k).map (·.size)).sum =
      ((cs.toList.take k).map (·.n.toNat)).sum * q := by
    rw [← List.map_take, List.map_map]
    exact sum_size_mul q _ fun c hc => hsq c (by simpa using List.mem_of_mem_take hc)
  rw [hsum] at hg
  simp only [List.getElem_map, Array.getElem_toList] at hg
  unfold concatBytes
  rw [← Array.foldl_toList, Array.toList_map]
  rw [show (((cs.toList.take k).map (·.n.toNat)).sum + i) * q + j =
    ByteArray.empty.size + ((cs.toList.take k).map (·.n.toNat)).sum * q + (i * q + j) by simp [Nat.add_mul]; omega]
  exact hg

/-! ## Several parts of one atom type: one grouping pass over the `raze`, then `cut` -/

/-- **Past the bitmap and `rangeOffsets` branches, a side's codes are the codes of its `raze` cut back
    into its parts**: `codes` groups the razed column once (`groupIdsColumn`, `Code.ofIds`) and cuts that
    code at the parts' counts, the razed column being neither a `syms` nor an `enum` payload. -/
theorem codes_raze_cut {t : QAtomicType} (hg : t ≠ .general) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hp : 0 < p) (hb : ∀ k (hk : k < p), ∀ b, cs[k].2.enc ≠ .bits b)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    (hne : ∀ d o ids, Column.intern (raze t cs.toArray).2.enc ≠ .enum d o ids) :
    ∃ q, groupIdsColumn t (raze t cs.toArray).1 (raze t cs.toArray).2.enc = some q ∧
      Obj.codes (.atom t) cs = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).cut (cs.map (·.1)) := by
  have hsome := KernelWF.groupIdsColumn_isSome hg (raze t cs.toArray).2.wf fun d o ids he => (hne d o ids he).elim
  refine ⟨_, (Option.some_get hsome).symm, ?_⟩
  show Alg.codes t cs = _
  unfold Alg.codes
  rw [dif_neg hg]
  split
  · next bs h =>
    have h0 := vec_mapM_some h hp
    exfalso
    revert h0
    cases he : cs[0].2.enc <;> simp
    exact (hb 0 hp _ he).elim
  simp only [hro]
  split
  · next he => exact absurd he (hne _ _ _)
  all_goals rfl

/-- A small integral part is not a bitmap, and `rangeOffsets` declines a small integral side. -/
theorem small_int_branches {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) :
    (∀ {n : USize} (x : Arr t n) b, x.enc ≠ .bits b) ∧
      ∀ {p : Nat} (es : Vector (USize × Enc) p) total, rangeOffsets t es total = none := by
  refine ⟨fun x b he => ?_, fun es total => ?_⟩
  · rcases small_int_enc ht hk x with ⟨b', he'⟩ | ⟨md, pk, he'⟩ <;> rw [he'] at he <;> cases he
  · unfold rangeOffsets
    rw [if_pos (by rcases hk with rfl | rfl | rfl <;> simp [ht])]

/-- **A small integral side of several dense parts: its codes are those of its `raze`, cut back.** -/
theorem codes_small_int_cut {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) {p : Nat} (cs : Vector (Part (.atom t)) p) (hp : 0 < p) :
    Obj.codes (.atom t) cs = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)) := by
  have hg := (small_int_width ht hk).2.2.1
  have hne : ∀ d o ids, Column.intern (raze t cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    rcases small_int_enc ht hk (raze t cs.toArray).2 with ⟨b, hb⟩ | ⟨md, pk, hb⟩ <;> simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut hg cs hp (fun k _ => (small_int_branches ht hk).1 _)
    ((small_int_branches ht hk).2 _ _) hne
  obtain ⟨q', hq', hc'⟩ := codes_small_int ht hk (raze t cs.toArray)
  rw [hc, hc', show q' = q from Option.some_inj.1 (hq'.symm.trans hq)]

/-- The razed column of dense parts reads part `k`'s element `i` past the counts before `k`. -/
theorem raze_get_bytes {t : QAtomicType} {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hd : ∀ k (hk : k < p), ∃ b, cs[k].2.enc = .bytes b) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k : Nat} (hk : k < p) {i : Nat} (hi : i < cs[k].1.toNat)
    (hO : ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat) :
    (raze t cs.toArray).2.get ⟨_, hO⟩ = cs[k].2.get ⟨i, hi⟩ := by
  have hl := KernelWF.razeTo_toList_bytes cs.toArray rfl hN fun c hc => by
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hc
    exact hd j (by simpa using hj)
  unfold razeTo at hl
  rw [KernelWF.cast_toList] at hl
  have ho := flatMap_offset (fun c : Part (.atom t) => c.2.toList) (·.1.toNat) (fun c => Arr.length_toList _)
    cs.toList (k := k) (by simpa using hk) (i := i) (by simpa using hi)
  simp only [Vector.toList_toArray] at hl
  rw [← hl, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hO), Arr.getElem_toList,
    List.getElem?_eq_getElem (by rw [Arr.length_toList]; simpa using hi)] at ho
  have := Option.some_inj.1 ho
  rw [this, Arr.getElem_toList]; rfl

/-- **A small integral side of dense parts: its codes are faithful jointly across the parts.** Part `k`'s
    code at `i` and part `l`'s at `j` agree exactly when the rows do; the parts' summed count a `USize`. -/
theorem codes_small_int_parts_faithful {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hd : ∀ k (hk : k < p), ∃ b, cs[k].2.enc = .bytes b) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom t) cs)[k].b (Obj.codes (.atom t) cs)[k].w i =
        Column.idAt (Obj.codes (.atom t) cs)[l].b (Obj.codes (.atom t) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_small_int_wf ht hk₀ (raze t cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < cs[k].1.toNat, ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat :=
    fun k hk i hi => by
      have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
      simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
      rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_small_int_cut ht hk₀ cs (by omega)]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_small_int_faithful ht hk₀ _ (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom, Vals.row_atom,
    Vals.row_atom, raze_get_bytes cs hd hN hk hi, raze_get_bytes cs hd hN hl hj]

/-- **A small integral side of several parts: each part's code is well formed**, the parts' summed count a
    `USize`. -/
theorem codes_small_int_parts_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = cs[k].1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, hsz, hid⟩ := codes_small_int_wf ht hk₀ (raze t cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)))[k] := by
    show (Obj.codes (.atom t) cs)[k] = _; rw [codes_small_int_cut ht hk₀ cs (by omega)]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

/-! ## `pairCode` where it groups: one numbering pass over the pair -/

/-- **`Code.ofIds` over ids `G` below `L ≤ n`, packed at `L`'s width, reads `G` and is well formed**, the
    lane of no bits included (`Code.ofLane`'s bitmap of zeros). -/
theorem ofIds_packIds (n : USize) {L : Nat} (hL : L ≤ n.toNat) (G : Nat → Nat) (hG : ∀ i < n.toNat, G i < L)
    {fs : ByteArray} (hfs : len fs = L) :
    let c := Code.ofIds (len fs) n (Column.packIds (Column.idWidthOf L) n.toNat G)
    ((c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = n ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ i < n.toNat, Column.idAt c.b c.w i = G i := by
  intro c
  have hL64 : L ≤ 2 ^ 64 := Nat.le_trans hL (Nat.le_of_lt (Verify.usize_lt n))
  have hcard : c.card = L := by
    show (Code.ofIds (len fs) n _).card = _; unfold Code.ofIds Code.ofLane; rw [hfs]; split <;> rfl
  have hn : c.n = n := by show (Code.ofIds (len fs) n _).n = _; unfold Code.ofIds Code.ofLane; split <;> rfl
  have hread : ∀ i < n.toNat, Column.idAt c.b c.w i = G i := fun i hi => by
    have hb := Verify.lt_idWidthOf (hG i hi) hL64
    show Column.idAt (Code.ofIds (len fs) n _).b (Code.ofIds (len fs) n _).w i = _
    unfold Code.ofIds Code.ofLane
    rw [hfs]
    split
    · next h0 =>
      rw [show Column.idWidthOf L = 0 by simpa using h0] at hb
      rw [show G i = 0 by omega]
      simp only [idAt_one]
      simp [Column.bitAt, KernelWF.ba_get?, Array.getElem?_replicate] <;> split <;> simp
    · exact Verify.idAt_packIds_idWidthOf hL64 hi (hG i hi)
  have hsh : ∀ d : Code, d = Code.ofIds (len fs) n (Column.packIds (Column.idWidthOf L) n.toNat G) →
      (d.w = 1 ∨ d.w = 2 ∨ d.w = 4 ∨ d.w = 8 ∨ d.w = 16 ∨ d.w = 32 ∨ d.w = 64) ∧
      d.b.size = (d.n.toNat * d.w + 7) / 8 := by
    intro d hd; subst hd
    unfold Code.ofIds Code.ofLane
    rw [hfs]
    by_cases h0 : (Column.idWidthOf L == 0) = true
    · rw [if_pos h0]; exact ⟨.inl rfl, by simp [ByteArray.size]⟩
    · rw [if_neg h0]
      have hw0 : Column.idWidthOf L ≠ 0 := by simpa using h0
      have hlane := Verify.laneWidth_cases (Column.widthFor (L - 1))
      have hw : Column.idWidthOf L = 1 ∨ Column.idWidthOf L = 2 ∨ Column.idWidthOf L = 4 ∨
          Column.idWidthOf L = 8 ∨ Column.idWidthOf L = 16 ∨ Column.idWidthOf L = 32 ∨ Column.idWidthOf L = 64 := by
        unfold Column.idWidthOf at hw0 ⊢; omega
      exact ⟨hw, packIds_size hw _ _⟩
  exact ⟨⟨(hsh c rfl).1, hn, (hsh c rfl).2, fun _ => ⟨by rw [hcard]; exact Nat.lt_of_le_of_lt hL n.toNat_lt_size,
    fun i hi => by rw [hn] at hi; rw [hread i hi, hcard]; exact hG i hi⟩⟩, hread⟩

/-- **`Code.ofIds` over `idsBy n key` is well formed, and two of its codes agree exactly when the keys do.** -/
theorem ofIds_idsBy {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (key : Nat → α) (n : USize) :
    let c := Code.ofIds (len (Order.idsBy n.toNat key).2) n (Order.idsBy n.toNat key).1
    ((c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = n ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ i < n.toNat, ∀ j < n.toNat, (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ key i = key j) := by
  obtain ⟨h1, h2⟩ := Verify.idsBy_spec n.toNat key
  have hfs : len (Order.idsBy n.toNat key).2 = (Verify.firstsOf key n.toNat).length := by
    unfold len; rw [h2]; omega
  have hL : (Verify.firstsOf key n.toNat).length ≤ n.toNat := by
    simpa [Verify.firstsOf] using List.length_filter_le _ (List.range n.toNat)
  obtain ⟨hwf, hread⟩ := ofIds_packIds n hL (Verify.groupOf key n.toNat) (fun i hi => Verify.groupOf_lt hi) hfs
  intro c
  have hc : c = Code.ofIds (len (Order.idsBy n.toNat key).2) n
      (Column.packIds (Column.idWidthOf (Verify.firstsOf key n.toNat).length) n.toNat (Verify.groupOf key n.toNat)) := by
    show Code.ofIds _ n _ = _; rw [h1]
  rw [hc]
  exact ⟨hwf, fun i hi j hj => by rw [hread i hi, hread j hj]; exact Verify.groupOf_iff hi hj⟩

/-- At a lane `laneKind` names, two keys agree exactly when the codes do. -/
theorem keyAt_iff_idAt {w : Nat} {k : Scan.Kind} (h : laneKind w = some k) (b : ByteArray) (i j : Nat) :
    Order.keyAt k b i = Order.keyAt k b j ↔ Column.idAt b w i = Column.idAt b w j := by
  rcases laneKind_some h with ⟨rfl, rfl⟩ | ⟨-, rfl, hc, hk⟩
  · rw [idAt_one, idAt_one]
    unfold Order.keyAt Scan.Kind.bitsAt
    cases Column.bitAt b i <;> cases Column.bitAt b j <;> first | decide | simp [Order.rank]
  · rw [Verify.keyAt_eq_iff hk, idAt_lane _ (by omega), idAt_lane _ (by omega), UInt64.toNat_inj]

/-- A payload of `⌈n·w/8⌉` bytes at a lane `laneKind` names holds all `n` elements. -/
theorem avail_lane {w : Nat} {k : Scan.Kind} (h : laneKind w = some k) {b : ByteArray} {n : Nat}
    (hs : b.size = (n * w + 7) / 8) : n ≤ k.avail b := by
  rcases laneKind_some h with ⟨rfl, rfl⟩ | ⟨-, rfl, -, hk⟩
  · simp only [Scan.Kind.avail]; omega
  · rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp only [Scan.Kind.avail, Scan.Kind.width] at hs ⊢ <;> omega

/-- `rank .i64` of a `Nat` below `2⁶⁴` keeps it apart from every other. -/
theorem rank_ofNat_iff {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Order.rank .i64 (UInt64.ofNat (x.toUInt64.toNat % 2 ^ 64)) = Order.rank .i64 (UInt64.ofNat (y.toUInt64.toNat % 2 ^ 64)) ↔
      x = y := by
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have t : ∀ a, (UInt64.ofNat a).toNat = a % 2 ^ 64 := fun a => BitVec.toNat_ofNat _ _
  have e := congrArg UInt64.toNat (UInt64.xor_left_inj _ |>.1 e)
  simp only [t, Nat.toUInt64_eq] at e
  simp only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
  exact e

/-- An id payload at a lane `w` of `⌈n·w/8⌉` bytes, repacked as longs by `idsOperand`: `n` longs, long `i` a
    bijection of id `i`. -/
theorem idsOperand_lane {w : Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    {b : ByteArray} {n : USize} (hs : b.size = (n.toNat * w + 7) / 8) :
    Scan.Kind.i64.avail (idsOperand 8 w.toUSize b n) = n.toNat ∧ ∀ i < n.toNat,
      Order.keyAt .i64 (idsOperand 8 w.toUSize b n) i =
        Order.rank .i64 (UInt64.ofNat ((Column.idAt b w i).toUInt64.toNat % 2 ^ 64)) := by
  have e8 : 8 * (8 : USize).toNat = 64 := by
    rw [show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
  have hcap : Column.idsCap b w n.toNat = n.toNat := idsCap_full (by omega) (by rw [hs, Nat.mul_comm]; omega)
  unfold idsOperand
  rw [e8, lane_toNat (by omega), hcap]
  exact keyAt_packIds64 n.toNat (Column.idAt b w)

/-- **`pairCode` where it groups the pair** — its classes answered, `groupIdsPair` at two layouts,
    `groupIdsPairIds` otherwise: the code is well formed, and two of its codes agree exactly when both
    columns' codes do; `a`, `b` lanes of `n` codes in `⌈n·w/8⌉` bytes. -/
theorem pairCode_grouped (cl : Bool) (a b : Code) (hn : b.n = a.n)
    (ha : (a.w = 1 ∨ a.w = 2 ∨ a.w = 4 ∨ a.w = 8 ∨ a.w = 16 ∨ a.w = 32 ∨ a.w = 64) ∧
      a.b.size = (a.n.toNat * a.w + 7) / 8)
    (hb : (b.w = 1 ∨ b.w = 2 ∨ b.w = 4 ∨ b.w = 8 ∨ b.w = 16 ∨ b.w = 32 ∨ b.w = 64) ∧
      b.b.size = (b.n.toNat * b.w + 7) / 8)
    {r : ByteArray × ByteArray} (hr : (pairCode cl a b).2 = some r) :
    let c := (pairCode cl a b).1
    ((c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = a.n ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ i < a.n.toNat, ∀ j < a.n.toNat, (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔
        Column.idAt a.b a.w i = Column.idAt a.b a.w j ∧ Column.idAt b.b b.w i = Column.idAt b.b b.w j) := by
  rw [hn] at hb
  obtain ⟨key, hkey, hc⟩ : ∃ key : Nat → UInt64 × UInt64, (∀ i < a.n.toNat, ∀ j < a.n.toNat, (key i = key j ↔
      Column.idAt a.b a.w i = Column.idAt a.b a.w j ∧ Column.idAt b.b b.w i = Column.idAt b.b b.w j)) ∧
      (pairCode cl a b).1 = Code.ofIds (len (Order.idsBy a.n.toNat key).2) a.n (Order.idsBy a.n.toNat key).1 := by
    revert hr
    unfold pairCode
    dsimp only
    split
    · intro h; simp at h
    intro _
    split
    · next _ _ ka kb hka hkb =>
      have hm : min a.n.toNat (min (ka.avail a.b) (kb.avail b.b)) = a.n.toNat := by
        have := avail_lane hka ha.2; have := avail_lane hkb hb.2; omega
      refine ⟨fun i => (Order.keyAt ka a.b i, Order.keyAt kb b.b i), fun i _ j _ => ?_, ?_⟩
      · rw [Prod.mk.injEq, keyAt_iff_idAt hka, keyAt_iff_idAt hkb]
      · show Code.ofIds _ a.n (Order.groupIdsPair ka kb a.n a.b b.b).1 = _
        unfold Order.groupIdsPair; rw [hm]
    · obtain ⟨hav, hka⟩ := idsOperand_lane ha.1 ha.2
      obtain ⟨hbv, hkb⟩ := idsOperand_lane hb.1 hb.2
      refine ⟨fun i => (Order.keyAt .i64 (idsOperand 8 a.w.toUSize a.b a.n) i,
        Order.keyAt .i64 (idsOperand 8 b.w.toUSize b.b a.n) i), fun i hi j hj => ?_, ?_⟩
      · have haw : a.w ≤ 64 := by rcases ha.1 with h | h | h | h | h | h | h <;> omega
        have hbw : b.w ≤ 64 := by rcases hb.1 with h | h | h | h | h | h | h <;> omega
        have l64 : ∀ (x : ByteArray) w k, w ≤ 64 → Column.idAt x w k < 2 ^ 64 := fun x w k h =>
          Nat.lt_of_lt_of_le (idAt_lt x w k h) (Nat.pow_le_pow_right (by decide) h)
        rw [Prod.mk.injEq, hka i hi, hka j hj, hkb i hi, hkb j hj,
          rank_ofNat_iff (l64 a.b a.w i haw) (l64 a.b a.w j haw), rank_ofNat_iff (l64 b.b b.w i hbw) (l64 b.b b.w j hbw)]
      · show Code.ofIds _ a.n (Order.groupIdsPairIds a.w.toUSize b.w.toUSize a.n a.b b.b).1 = _
        unfold Order.groupIdsPairIds Order.groupIdsPair; rw [hav, hbv, Nat.min_self, Nat.min_self]
  intro c
  rw [show c = _ from hc]
  obtain ⟨hwf, hiff⟩ := ofIds_idsBy key a.n
  exact ⟨hwf, fun i hi j hj => (hiff i hi j hj).trans (hkey i hi j hj)⟩

/-! ## Products: `pairCode` of the two columns' codes laid end to end, cut back -/

/-- A product side's codes are `pairCode` of its columns' codes laid end to end, cut at the parts' counts. -/
theorem codes_prod_eq {a b : Obj} {p : Nat} (cs : Vector (Part (.prod a b)) p) :
    Obj.codes (.prod a b) cs =
      (pairCode false (Code.cat (Obj.codes a (cs.map fun c => (⟨c.1, c.2.1⟩ : Part a))).toArray)
        (Code.cat (Obj.codes b (cs.map fun c => (⟨c.1, c.2.2⟩ : Part b))).toArray)).1.cut
        ((Obj.codes a (cs.map fun c => (⟨c.1, c.2.1⟩ : Part a))).map (·.n)) := by
  rw [Obj.codes]; simp [tuples, tuples.tupleCode]

/-- Equal parts read equal rows. -/
theorem row_part_congr {A : Obj} {x y : Part A} (h : x = y) {i : Nat} (hx : i < x.1.toNat) (hy : i < y.1.toNat) :
    Vals.row x.2 ⟨i, hx⟩ = Vals.row y.2 ⟨i, hy⟩ := by subst h; rfl

/-- Codes of parts on one lane, each `⌈n·w/8⌉` bytes with its codes below its `card` under a byte, laid
    end to end by `Code.cat`: code `(counts before k) + i` is part `k`'s code `i`, at the parts' lane. -/
theorem cat_parts {p : Nat} (cx : Vector Code p) (hp : 0 < p)
    (hl : ∀ {k l : Nat} (hk : k < p) (hl : l < p), cx[k].w = cx[l].w)
    (hwf : ∀ {k : Nat} (hk : k < p),
      (cx[k].w = 1 ∨ cx[k].w = 2 ∨ cx[k].w = 4 ∨ cx[k].w = 8 ∨ cx[k].w = 16 ∨ cx[k].w = 32 ∨ cx[k].w = 64) ∧
      cx[k].b.size = (cx[k].n.toNat * cx[k].w + 7) / 8 ∧
      (cx[k].w < 8 → ∀ i < cx[k].n.toNat, Column.idAt cx[k].b cx[k].w i < cx[k].card))
    (hN : (cx.toList.map (·.n.toNat)).sum < USize.size) :
    (Code.cat cx.toArray).n.toNat = (cx.toList.map (·.n.toNat)).sum ∧
      ∀ k (hk : k < p), ∀ i < cx[k].n.toNat, Column.idAt (Code.cat cx.toArray).b (Code.cat cx.toArray).w
        (((cx.toList.take k).map (·.n.toNat)).sum + i) = Column.idAt cx[k].b cx[k].w i := by
  have hmem : ∀ c ∈ cx.toArray, ∃ k, ∃ hk : k < p, c = cx[k] := fun c hc => by
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
    exact ⟨k, by simpa using hk, by simp⟩
  obtain ⟨hw, hn, hg⟩ := cat_get cx.toArray (w := cx[0].w) (hwf hp).1 (by simpa using hp)
    (fun c hc => by obtain ⟨k, hk, rfl⟩ := hmem c hc; exact hl hk hp)
    (fun c hc => by obtain ⟨k, hk, rfl⟩ := hmem c hc; rw [← hl hk hp]; exact (hwf hk).2.1)
    (fun h24 c hc i hi => by
      obtain ⟨k, hk, rfl⟩ := hmem c hc; rw [← hl hk hp]
      exact (hwf hk).2.2 (by rw [hl hk hp]; omega) i hi)
    (by simpa using hN)
  refine ⟨by simpa using hn, fun k hk i hi => ?_⟩
  have := hg k (by simpa using hk) i (by simpa using hi)
  simp only [Vector.getElem_toArray, Vector.toList_toArray] at this
  rw [hw, hl hk hp]; exact this

end LeetQ.Rel.Alg
