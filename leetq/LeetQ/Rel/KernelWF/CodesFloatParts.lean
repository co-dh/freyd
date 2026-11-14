/-
  `Obj.codes` at a float atom (`real`, `float`, `datetime`) over parts in any encoding, their `raze` in any
  encoding (dense, FoR, ALP): `codes` groups the `raze` at `bitsType`, the integral type of the float's width,
  so a code is one cell's bits — two NaNs of different payloads, and `-0.0` against `0.0`, get different codes,
  as `Vals.row` tells them apart.
-/
import LeetQ.Rel.KernelWF.RazeFoR

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

/-- **A float column's two rows are one cell exactly when the bits of its dense decode agree** — the cell is
    its bits (`Carrier`), no NaN or zero folded; the column in any encoding (`get_bytesOf`). -/
theorem float_row_eq {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {k : Scan.Kind}
    (hk : orderKind (KernelWF.bitsType t) = some k) {n : USize} (x : Arr t n) {b : ByteArray}
    (he : Enc.bytesOf t n x.enc = some b) {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat) :
    x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ ↔ Column.bitsAt b (i * k.width) k.width = Column.bitsAt b (j * k.width) k.width := by
  obtain ⟨-, hw, hg, hbo, -, -⟩ := float_facts ht hk
  rw [Arr.get_ne x _ hg, Arr.get_ne x _ hg, ← KernelWF.get_bytesOf hw hbo x.wf he hi,
    ← KernelWF.get_bytesOf hw hbo x.wf he hj]
  have h32 : ∀ a c : UInt64, a.toNat < 2 ^ 32 → c.toNat < 2 ^ 32 → (a.toUInt32 = c.toUInt32 ↔ a = c) :=
    fun a c ha hc => ⟨fun h => UInt64.toNat_inj.1 (by have := congrArg UInt32.toNat h; simp at this; omega),
      fun h => h ▸ rfl⟩
  rcases ht with rfl | rfl | rfl <;> simp [KernelWF.bitsType, orderKind] at hk <;> subst hk <;>
    simp [Enc.get, hi, hj, QAtomicType.width, Column.atomOfBits, Carrier.of?, Scan.Kind.width]
  exact h32 _ _ (Verify.bitsAt_lt _ _ _ (by decide)) (Verify.bitsAt_lt _ _ _ (by decide))

/-- **A float column in any encoding is grouped by the keys of its dense decode `B`**: `groupIdsColumn` at
    `bitsType` packs `Verify.groupOf g` for a `g` that is `keyAt k B` below the count — a dense or ALP payload
    grouped over `B` itself, a FoR one over its encoded form, whose keys are the decode's (`decode_keyAt`). -/
theorem float_groups {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {n : USize} (x : Arr t n)
    {q : ByteArray × ByteArray} (hq : groupIdsColumn (KernelWF.bitsType t) n x.enc = some q) :
    ∃ k B, ∃ g : Nat → UInt64, orderKind (KernelWF.bitsType t) = some k ∧ Enc.bytesOf t n x.enc = some B ∧
      q.1 = Column.packIds (Column.idWidthOf (Verify.firstsOf g n.toNat).length) n.toNat (Verify.groupOf g n.toNat) ∧
      len q.2 = (Verify.firstsOf g n.toNat).length ∧ ∀ i < n.toNat, g i = Order.keyAt k B i := by
  obtain ⟨k, hk⟩ : ∃ k, orderKind (KernelWF.bitsType t) = some k := by
    rcases ht with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨hk2, hw, -, hbo, -, hgc⟩ := float_facts ht hk
  obtain ⟨B, hB, hBs⟩ := KernelWF.bytesOf_size hbo hw x.wf
  have hav : min n.toNat (k.avail B) = n.toNat := by
    rcases hk2 with rfl | rfl <;> simp [Scan.Kind.avail, Scan.Kind.width, hBs]
  have hk0 : k ≠ .bit := by rcases hk2 with rfl | rfl <;> decide
  have hspec := Verify.groupIds_spec k n B
  rw [hav] at hspec
  refine ⟨k, B, ?_⟩
  have hwf := x.wf
  generalize x.enc = e at hq hB hwf ⊢
  cases e
  case bytes b =>
    have hb : b = B := by simpa [Enc.bytesOf] using hB
    subst hb
    rw [hgc, Option.some_inj] at hq; subst hq
    exact ⟨_, hk, hB, hspec.1, by rw [len_eq_ids, hspec.2], fun _ _ => rfl⟩
  case alp md pk a =>
    have hf : groupIdsColumn (KernelWF.bitsType t) n (.alp md pk a) = some (Order.groupIds k n B) := by
      rcases ht with rfl | rfl | rfl <;> simp [KernelWF.bitsType, orderKind] at hk <;> subst hk <;>
        simp [Enc.bytesOf, QAtomicType.width] at hB <;>
        simp [KernelWF.bitsType, groupIdsColumn, orderKind, Enc.bytesOf, QAtomicType.width, hB]
    rw [hf, Option.some_inj] at hq; subst hq
    exact ⟨_, hk, hB, hspec.1, by rw [len_eq_ids, hspec.2], fun _ _ => rfl⟩
  case foR md pk =>
    have hf : groupIdsColumn (KernelWF.bitsType t) n (.foR md pk) = some (Order.groupIdsFoR k n md pk) := by
      rcases ht with rfl | rfl | rfl <;> simp [KernelWF.bitsType, orderKind] at hk <;> subst hk <;>
        simp [KernelWF.bitsType, groupIdsColumn, orderKind]
    rw [hf, Option.some_inj] at hq; subst hq
    have hdec : Coc.decode k.width.toUSize md pk n = B := by simpa [Enc.bytesOf, hw] using hB
    have hs := Verify.groupIdsFoR_spec k hk0 n md pk
    exact ⟨foRKey k md pk, hk, hB, hs.1, by rw [len_eq_ids, hs.2],
      fun i hi => by rw [← (Verify.decode_keyAt k hk0 n md pk).2 i hi, hdec]⟩
  all_goals rcases ht with rfl | rfl | rfl <;> simp [Enc.WF] at hwf

/-- **The grouping code of one float column, in any encoding, is faithful**: `Code.ofIds` of the ids
    `groupIdsColumn` answers at `bitsType` is equal exactly where the cells are. -/
theorem ofIds_float_faithful {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {n : USize}
    (x : Arr t n) {q : ByteArray × ByteArray} (hq : groupIdsColumn (KernelWF.bitsType t) n x.enc = some q)
    {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat) :
    Column.idAt (Code.ofIds (len q.2) n q.1).b (Code.ofIds (len q.2) n q.1).w i =
        Column.idAt (Code.ofIds (len q.2) n q.1).b (Code.ofIds (len q.2) n q.1).w j ↔
      x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ := by
  obtain ⟨k, B, g, hk, hB, hq1, hq2, hg⟩ := float_groups ht x hq
  have hk2 := (float_facts ht hk).1
  have hn64 := Verify.usize_lt n
  rw [ofIds_groupOf g n hn64 hq1 hq2 hi, ofIds_groupOf g n hn64 hq1 hq2 hj, groupOf_eq_groupOf hi hj, hg i hi,
    hg j hj, Verify.keyAt_eq_iff (by rcases hk2 with rfl | rfl <;> simp) B, float_row_eq ht hk x hB hi hj]

/-- **A float side's codes are its `raze` grouped at `bitsType`, cut back into the parts** — the parts and the
    `raze` in any encoding. -/
theorem codes_float_cut {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hp : 0 < p) :
    ∃ q, groupIdsColumn (KernelWF.bitsType t) (raze t cs.toArray).1 (raze t cs.toArray).2.enc = some q ∧
      Obj.codes (.atom t) cs = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).cut (cs.map (·.1)) :=
  codes_raze_cut (by rcases ht with rfl | rfl | rfl <;> decide) cs hp
    (fun j hj b he => by
      have hwf := (cs[j]'hj).2.wf; rw [he] at hwf; rcases ht with rfl | rfl | rfl <;> simp [Enc.WF] at hwf)
    (by unfold rangeOffsets; rcases ht with rfl | rfl | rfl <;> simp [orderKind])
    (fun d o ids he => by
      have hwf := (raze t cs.toArray).2.wf
      generalize (raze t cs.toArray).2.enc = e at hwf he
      cases e <;> rcases ht with rfl | rfl | rfl <;> simp_all [Column.intern, Enc.WF])

/-- **A float side: its codes are faithful jointly across the parts** — equal codes exactly at rows of equal
    bits; the parts and their `raze` in any encoding, the parts' summed count a `USize`, 32 bits where an ALP
    join offsets it (`hA`). -/
theorem codes_float_parts_faithful {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  obtain ⟨q, hq, hc⟩ := codes_float_cut ht cs (by omega)
  obtain ⟨κ, -, g, hκ, -, hq1, hq2, -⟩ := float_groups ht (raze t cs.toArray).2 hq
  obtain ⟨-, hW, -, hBo, -, -⟩ := float_facts ht hκ
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := ofIds_groupOf_wf g (raze t cs.toArray).1 hq1 hq2
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [hc]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    ofIds_float_faithful ht _ hq (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    raze_get hW hBo cs hN hA hk hi, raze_get hW hBo cs hN hA hl hj]

/-- **A float side: each part's code is well formed, and all on one lane** — the parts and their `raze` in any
    encoding, the parts' summed count a `USize`. -/
theorem codes_float_parts_wf {t : QAtomicType} (ht : t = .real ∨ t = .float ∨ t = .datetime) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    (let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
    ∀ {l : Nat} (hl : l < p), ((Obj.codes (.atom t) cs)[k]'hk).w = ((Obj.codes (.atom t) cs)[l]'hl).w := by
  obtain ⟨q, hq, hc⟩ := codes_float_cut ht cs (by omega)
  obtain ⟨-, -, g, -, -, hq1, hq2, -⟩ := float_groups ht (raze t cs.toArray).2 hq
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, hsz', hid⟩ := ofIds_groupOf_wf g (raze t cs.toArray).1 hq1 hq2
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).n.toNat := by
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

/-- **A side at a small integral or float kind: its codes are faithful jointly across the parts, each well
    formed, all on one lane** — the parts and their `raze` in any encoding; the int sides through
    `codes_small_int_parts_faithful`/`_wf`, the float sides grouped by their bits
    (`codes_float_parts_faithful`/`_wf`); the parts' summed count a `USize`, 32 bits where an ALP join offsets
    it (`hA`). -/
theorem codes_dense_faithful_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32) :
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
    have hf : t = .real ∨ t = .float ∨ t = .datetime := by
      clear hA hN; cases t <;> simp [orderKind] at ht <;> simp_all
    exact ⟨⟨fun hk hl _ _ hi hj => codes_float_parts_faithful hf cs hN hA hk hl hi hj,
      fun hk => (codes_float_parts_wf hf cs hN hk).1⟩, fun hk hl => (codes_float_parts_wf hf cs hN hk).2 hl⟩
  all_goals
    have hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 := by clear hA hN; simp_all
    refine ⟨⟨fun hk hl _ _ hi hj => codes_small_int_parts_faithful ht hk₀ cs hN hk hl hi hj,
      fun hk => codes_small_int_parts_wf ht hk₀ cs hN hk⟩, fun hk hl => ?_⟩
    rw [codes_small_int_cut ht hk₀ cs (by omega)]; unfold Code.cut; split <;> simp

/-- **One part of a small integral or float side, in any encoding: its codes are faithful and well formed**
    (`codes_small_int_faithful`/`_wf`; a float through `codes_dense_faithful_wf` at one part, no join to bound). -/
theorem codes_num_one_faithful_wf {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (x : Part (.atom t)) (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) :
    (∀ {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat),
      Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w i =
          Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w j ↔
        Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩) ∧
    (let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧ c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) := by
  have h := codes_dense_faithful_wf ht hk₀ #v[x] (by simpa using x.1.toNat_lt_size) (fun h => absurd h (by decide))
  exact ⟨fun hi hj => h.1.1 (k := 0) (l := 0) (by decide) (by decide) hi hj, h.1.2 (k := 0) (by decide)⟩

#print axioms float_groups
#print axioms codes_float_parts_faithful
#print axioms codes_float_parts_wf
#print axioms codes_dense_faithful_wf
#print axioms codes_num_one_faithful_wf

end LeetQ.Rel.Alg
