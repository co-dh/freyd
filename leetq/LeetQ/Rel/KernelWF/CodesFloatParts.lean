/-
  `Obj.codes` at a float atom (`real`, `float`, `datetime`) over dense parts: `codes` groups the `raze` at
  `bitsType`, the integral type of the float's width, so a code is one cell's bits — two NaNs of different
  payloads, and `-0.0` against `0.0`, get different codes, as `Vals.row` tells them apart.
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- A float type's facts: `bitsType` sorts it at an integral kind `k` of its width, its dense payload holds
    `k.width` bytes an element. -/
theorem float_facts {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {k : Scan.Kind}
    (hk : orderKind (KernelWF.bitsType t) = some k) :
    (k = .i32 ∨ k = .i64) ∧ t.width = some k.width ∧ t ≠ .general ∧ t ≠ .boolean ∧
      (∀ n b, Enc.WF t n (.bytes b) → b.size = n.toNat * k.width) ∧
      ∀ n b, groupIdsColumn (KernelWF.bitsType t) n (.bytes b) = some (Order.groupIds k n b) := by
  rcases ht with rfl | rfl | rfl <;> simp [KernelWF.bitsType, orderKind] at hk <;> subst hk <;>
    exact ⟨by decide, rfl, by decide, by decide, fun n b h => by simpa [Enc.WF, QAtomicType.width] using h,
      fun n b => by simp [KernelWF.bitsType, groupIdsColumn, orderKind, Enc.bytesOf]⟩

/-- **A dense float column's two rows are one cell exactly when their bits agree** — the cell is its bits
    (`Carrier`), no NaN or zero folded. -/
theorem float_row_eq {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {k : Scan.Kind}
    (hk : orderKind (KernelWF.bitsType t) = some k) {n : USize} (x : Arr t n) {b : ByteArray}
    (he : x.enc = .bytes b) {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat) :
    x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ ↔ Column.bitsAt b (i * k.width) k.width = Column.bitsAt b (j * k.width) k.width := by
  have hg := (float_facts ht hk).2.2.1
  rw [Arr.get_ne x _ hg, Arr.get_ne x _ hg, he]
  have h32 : ∀ a c : UInt64, a.toNat < 2 ^ 32 → c.toNat < 2 ^ 32 → (a.toUInt32 = c.toUInt32 ↔ a = c) :=
    fun a c ha hc => ⟨fun h => UInt64.toNat_inj.1 (by have := congrArg UInt32.toNat h; simp at this; omega),
      fun h => h ▸ rfl⟩
  rcases ht with rfl | rfl | rfl <;> simp [KernelWF.bitsType, orderKind] at hk <;> subst hk <;>
    simp [Enc.get, hi, hj, QAtomicType.width, Column.atomOfBits, Carrier.of?, Scan.Kind.width]
  exact h32 _ _ (Verify.bitsAt_lt _ _ _ (by decide)) (Verify.bitsAt_lt _ _ _ (by decide))

/-- **The `raze` of dense parts of a fixed-width type is dense.** -/
theorem raze_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hg : t ≠ .general) (hbo : t ≠ .boolean)
    (cs : Array ((n : USize) × Arr t n)) (hcs : ∀ c ∈ cs, ∃ b, c.2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) (h0 : cs.size ≠ 0) :
    ∃ B, (raze t cs).2.enc = .bytes B := by
  rcases cs with ⟨l⟩
  simp only [List.mem_toArray] at hcs
  have hl0 : l ≠ [] := by rintro rfl; exact h0 rfl
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1
    obtain ⟨b, hb⟩ := hcs c (by simp)
    have hr : raze t #[c] = c := by unfold raze; simp [hg]
    exact ⟨b, by rw [hr, hb]⟩
  unfold raze
  rw [dif_neg (by simpa using hl0), dif_neg hg, dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr t n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk]; simpa using hN
  unfold need; rw [dif_pos hf]
  have hps : ∀ c ∈ (List.toArray l).map (·.2.part), ∃ b, c.2 = .bytes b := by
    intro c hc; obtain ⟨d, hd, rfl⟩ := Array.mem_map.1 hc; exact hcs d (by simpa using hd)
  have hv : ∀ h, (razeColumn t ((List.toArray l).map (·.2.part))).get h =
      .vector t (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
        (.bytes (concatBytes (((List.toArray l).map (·.2.part)).map
          fun c => (Enc.bytesOf t c.1 c.2).getD .empty))) none :=
    fun h => KernelWF.razeColumn_bytes hw hbo hps (Option.some_get h).symm
  exact ⟨concatBytes (((List.toArray l).map (·.2.part)).map fun c => (Enc.bytesOf t c.1 c.2).getD .empty),
    by simp only [Arr.enc, hv]⟩

/-- **A float side of dense parts: its codes are its `raze` grouped by bits (`bitsType`'s kind `k`), cut
    back into the parts**, the parts' summed count a `USize`. -/
theorem codes_float_cut {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hp : 0 < p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) :
    ∃ k B, orderKind (KernelWF.bitsType t) = some k ∧ (raze t cs.toArray).2.enc = .bytes B ∧
      Obj.codes (.atom t) cs = (Code.ofIds (len (Order.groupIds k (raze t cs.toArray).1 B).2) (raze t cs.toArray).1
        (Order.groupIds k (raze t cs.toArray).1 B).1).cut (cs.map (·.1)) := by
  obtain ⟨k, hk⟩ : ∃ k, orderKind (KernelWF.bitsType t) = some k := by
    rcases ht with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨-, hw, hg, hbo, -, hgc⟩ := float_facts ht hk
  obtain ⟨B, hB⟩ := raze_dense hw hg hbo cs.toArray (fun c hc => by
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hc; simpa using hd j (by simpa using hj))
    (by simpa using hN) (by simp; omega)
  obtain ⟨q, hq, hc⟩ := codes_raze_cut hg cs hp
    (fun j hj b he => by obtain ⟨b', hb'⟩ := hd j hj; rw [hb'] at he; cases he)
    (by unfold rangeOffsets; rcases ht with rfl | rfl | rfl <;> simp [orderKind])
    (fun d o ids he => by rw [hB] at he; simp [Column.intern] at he)
  rw [hB, hgc, Option.some_inj] at hq
  subst hq
  exact ⟨k, B, hk, hB, hc⟩

/-- **A float side of dense parts: its codes are faithful jointly across the parts** — equal codes exactly at
    rows of equal bits; the parts' summed count a `USize`. -/
theorem codes_float_parts_faithful {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  obtain ⟨κ, B, hκ, hB, hc⟩ := codes_float_cut ht cs (by omega) hd hN
  obtain ⟨hκ2, -, -, -, hsz, -⟩ := float_facts ht hκ
  have hX := raze_len t cs.toArray hN
  have hBs := hsz _ _ (hB ▸ (raze t cs.toArray).2.wf)
  have hav : min (raze t cs.toArray).1.toNat (κ.avail B) = (raze t cs.toArray).1.toNat := by
    rcases hκ2 with rfl | rfl <;> simp [Scan.Kind.avail, Scan.Kind.width, hBs]
  have hspec := Verify.groupIds_spec κ (raze t cs.toArray).1 B
  rw [hav] at hspec
  obtain ⟨hw, hn, -, -⟩ := ofIds_groupOf_wf (Order.keyAt κ B) (raze t cs.toArray).1 hspec.1
    (by rw [len_eq_ids, hspec.2])
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum =
      (Code.ofIds (len (Order.groupIds κ (raze t cs.toArray).1 B).2) (raze t cs.toArray).1
        (Order.groupIds κ (raze t cs.toArray).1 B).1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  have hn64 := Verify.usize_lt (raze t cs.toArray).1
  rw [hc]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    ofIds_groupOf (Order.keyAt κ B) _ hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) (hlt k hk i hi),
    ofIds_groupOf (Order.keyAt κ B) _ hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) (hlt l hl j hj),
    groupOf_eq_groupOf (hlt k hk i hi) (hlt l hl j hj),
    Verify.keyAt_eq_iff (by rcases hκ2 with rfl | rfl <;> simp) B,
    ← float_row_eq ht hκ (raze t cs.toArray).2 hB (hlt k hk i hi) (hlt l hl j hj),
    Vals.row_atom, Vals.row_atom, raze_get_bytes cs hd hN hk hi, raze_get_bytes cs hd hN hl hj]

/-- **A float side of dense parts: each part's code is well formed, and all on one lane**, the parts' summed
    count a `USize`. -/
theorem codes_float_parts_wf {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    (let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
    ∀ {l : Nat} (hl : l < p), ((Obj.codes (.atom t) cs)[k]'hk).w = ((Obj.codes (.atom t) cs)[l]'hl).w := by
  obtain ⟨κ, B, hκ, hB, hc⟩ := codes_float_cut ht cs (by omega) hd hN
  obtain ⟨hκ2, -, -, -, hsz, -⟩ := float_facts ht hκ
  have hX := raze_len t cs.toArray hN
  have hBs := hsz _ _ (hB ▸ (raze t cs.toArray).2.wf)
  have hav : min (raze t cs.toArray).1.toNat (κ.avail B) = (raze t cs.toArray).1.toNat := by
    rcases hκ2 with rfl | rfl <;> simp [Scan.Kind.avail, Scan.Kind.width, hBs]
  have hspec := Verify.groupIds_spec κ (raze t cs.toArray).1 B
  rw [hav] at hspec
  obtain ⟨hw, hn, hsz', hid⟩ := ofIds_groupOf_wf (Order.keyAt κ B) (raze t cs.toArray).1 hspec.1
    (by rw [len_eq_ids, hspec.2])
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum =
      (Code.ofIds (len (Order.groupIds κ (raze t cs.toArray).1 B).2) (raze t cs.toArray).1
        (Order.groupIds κ (raze t cs.toArray).1 B).1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  refine ⟨?_, fun hl => by rw [hc]; unfold Code.cut; split <;> simp⟩
  show let c := (Obj.codes (.atom t) cs)[k]'hk; _
  rw [hc]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz' hk
  dsimp only
  rw [hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

/-- **A side of dense parts at a small integral or float kind: its codes are faithful jointly across the parts,
    each well formed, all on one lane** — the int sides through `codes_small_int_parts_faithful`/`_wf`, the float
    sides grouped by their bits (`codes_float_parts_faithful`/`_wf`); the parts' summed count a `USize`. -/
theorem codes_dense_faithful_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) :
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
    have hf : t = .real ∨ t = .float ∨ t = .datetime := by cases t <;> simp [orderKind] at ht <;> simp_all
    exact ⟨⟨fun hk hl _ _ hi hj => codes_float_parts_faithful hf cs hd hN hk hl hi hj,
      fun hk => (codes_float_parts_wf hf cs hd hN hk).1⟩, fun hk hl => (codes_float_parts_wf hf cs hd hN hk).2 hl⟩
  all_goals
    have hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 := by simp_all
    refine ⟨⟨fun hk hl _ _ hi hj => codes_small_int_parts_faithful ht hk₀ cs hd hN hk hl hi hj,
      fun hk => codes_small_int_parts_wf ht hk₀ cs hN hk⟩, fun hk hl => ?_⟩
    rw [codes_small_int_cut ht hk₀ cs (by omega)]; unfold Code.cut; split <;> simp

/-- **One part of a small integral side, in any encoding, or of a dense float side: its codes are faithful and
    well formed** (`codes_small_int_faithful`/`_wf`; a float through `codes_dense_faithful_wf` at one part). -/
theorem codes_num_one_faithful_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (x : Part (.atom t)) (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ ((k₀ = .f32 ∨ k₀ = .f64) ∧ ∃ b, x.2.enc = .bytes b)) :
    (∀ {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat),
      Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w i =
          Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w j ↔
        Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩) ∧
    (let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧ c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) := by
  rcases hk₀ with hk | hk | hk | ⟨hf, hd⟩
  all_goals try exact ⟨fun hi hj => codes_small_int_faithful ht (by simp [hk]) x hi hj,
    codes_small_int_wf ht (by simp [hk]) x⟩
  have h := codes_dense_faithful_wf ht (by rcases hf with h | h <;> simp [h]) #v[x]
    (fun k hk => by match k, hk with | 0, _ => exact hd) (by simpa using x.1.toNat_lt_size)
  exact ⟨fun hi hj => h.1.1 (k := 0) (l := 0) (by decide) (by decide) hi hj, h.1.2 (k := 0) (by decide)⟩

#print axioms codes_float_parts_faithful
#print axioms codes_float_parts_wf
#print axioms codes_dense_faithful_wf
#print axioms codes_num_one_faithful_wf

end LeetQ.Rel.Alg
