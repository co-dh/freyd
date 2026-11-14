/-
  What `raze` CONTAINS where every part is a dense payload: the razed column lists its parts' elements one
  part after another. `razeColumn` lays the parts' bytes end to end (`concatBytes`), and an element of a
  dense payload is read off its own `w` bytes only.
-/
import LeetQ.Rel.KernelWF.PickSpec
import QLean.Verify.Raw
import QLean.Verify.AlpConcat

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg

/-- A byte read as `bitsAt` reads it, zero past the end. -/
theorem dite_byte (b : ByteArray) (j : Nat) : (if h : j < b.size then b[j] else 0) = (b.data[j]?).getD 0 := by
  split
  · rename_i h; rw [Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; exact h)]; rfl
  · rename_i h; rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]; rfl

/-- `bitsAt` reads only its own `w` bytes. -/
theorem bitsAt_congr {b b' : ByteArray} {o o' : Nat} : ∀ {w : Nat}, (∀ j < w, b.data[o + j]? = b'.data[o' + j]?) →
    Column.bitsAt b o w = Column.bitsAt b' o' w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [Column.bitsAt]
    rw [bitsAt_congr (fun j hj => h j (by omega)), dite_byte b, dite_byte b', h w (by omega)]

/-- Element `i` of a dense payload at a type of width `w` is read off its own `w` bytes only, whatever the
    count it is read at. -/
theorem get_bytes_congr {t : QAtomicType} {w : Nat} (hw : t.width = some w) {m m' : USize} {b b' : ByteArray}
    {i i' : Nat} (hi : i < m.toNat) (hi' : i' < m'.toNat) (h : ∀ j < w, b.data[i * w + j]? = b'.data[i' * w + j]?) :
    Enc.get t m (.bytes b) i = Enc.get t m' (.bytes b') i' := by
  have hB := bitsAt_congr h
  have hG : ∀ j < w, b[i * w + j]? = b'[i' * w + j]? := fun j hj => by rw [ba_get?, ba_get?]; exact h j hj
  cases t <;> simp only [QAtomicType.width] at hw <;> cases hw <;>
    simp only [Enc.get, hi, hi', ↓reduceIte, QAtomicType.width, hB]
  apply congrArg; apply congrArg; apply Vector.ext; intro k hk
  simp only [Vector.getElem_ofFn]; rw [hG k hk]

/-- An `Arr` moved along a count equation keeps its list. -/
theorem cast_toList {t : QAtomicType} {a b : USize} (e : a = b) (x : Arr t a) :
    (e ▸ x : Arr t b).toList = x.toList := by subst e; rfl

/-- A dense column's list is its elements read off its payload. -/
theorem toList_bytes {t : QAtomicType} {n : USize} (x : Arr t n) {b : ByteArray} (hx : x.enc = .bytes b)
    (hg : t ≠ .general) :
    x.toList = ((List.range n.toNat).map fun i => Enc.get t n (.bytes b) i).map
      fun o => (o.bind fun a => Carrier.of? t (.atom a)).getD default := by
  apply List.ext_getElem (by simp [Arr.length_toList])
  intro j h1 h2
  rw [Arr.getElem_toList, Arr.get_ne _ _ hg, hx]; simp

/-- Dense parts laid end to end after `acc` of `A` elements read, element by element, as `acc`'s elements and
    then each part's, each at its own count. -/
theorem foldl_bytes_get {t : QAtomicType} {w : Nat} (hw : t.width = some w) (S : USize)
    (g : ((n : USize) × Arr t n) → ByteArray) :
    ∀ (l : List ((n : USize) × Arr t n)) (acc : ByteArray) (A : Nat), acc.size = A * w →
      (∀ c ∈ l, (g c).size = c.1.toNat * w) → A + (l.map (·.1.toNat)).sum ≤ S.toNat →
      (List.range (A + (l.map (·.1.toNat)).sum)).map (fun i => Enc.get t S (.bytes (l.foldl (fun a c => a ++ g c) acc)) i) =
        (List.range A).map (fun i => Enc.get t S (.bytes acc) i) ++
          l.flatMap fun c => (List.range c.1.toNat).map fun i => Enc.get t c.1 (.bytes (g c)) i
  | [], acc, A, _, _, _ => by simp
  | c :: l, acc, A, ha, hl, hS => by
    have hc := hl c (by simp)
    have ih := foldl_bytes_get hw S g l (acc ++ g c) (A + c.1.toNat)
      (by rw [ByteArray.size_append, ha, hc, Nat.add_mul]) (fun d hd => hl d (by simp [hd]))
      (by simp only [List.map_cons, List.sum_cons] at hS; omega)
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, List.flatMap_cons, ← Nat.add_assoc]
    rw [ih, List.range_add, List.map_append, List.map_map, List.append_assoc]
    simp only [List.map_cons, List.sum_cons] at hS
    congr 1
    · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
      refine get_bytes_congr hw (by omega) (by omega) fun j hj => ?_
      have : i * w + j < A * w := by
        have := Nat.mul_le_mul_right w (show i + 1 ≤ A by omega); rw [Nat.succ_mul] at this; omega
      rw [ByteArray.data_append, Array.getElem?_append_left (by rw [ByteArray.size_data]; omega)]
    congr 1
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    simp only [Function.comp]
    refine get_bytes_congr hw (by omega) hi fun j hj => ?_
    rw [ByteArray.data_append, Nat.add_mul, ← ha, Nat.add_assoc,
      Array.getElem?_append_right (by rw [ByteArray.size_data]; omega), ByteArray.size_data, Nat.add_sub_cancel_left]

/-- Where every part is dense, no part is in a form `encodedParts` joins, so `razeColumn` answers dense. -/
theorem encodedParts_bytes {t : QAtomicType} {cs : Array (USize × Enc)} (hcs : ∀ c ∈ cs, ∃ b, c.2 = .bytes b) :
    encodedParts t cs = none := by
  have hany : ∀ p : USize × Enc → Bool, (∀ c ∈ cs, ∀ b, c.2 = .bytes b → p c = false) → cs.any p = false :=
    fun p hp => Bool.eq_false_iff.2 fun h => by
      obtain ⟨i, hi, h⟩ := Array.any_eq_true.1 h
      obtain ⟨b, hb⟩ := hcs cs[i] (Array.getElem_mem hi)
      rw [hp _ (Array.getElem_mem hi) b hb] at h; cases h
  unfold encodedParts; dsimp only
  rw [hany _ (fun c _ b hb => by simp [hb])]
  simp

/-- A type with a width other than `guid` is at most eight bytes wide. -/
theorem width_le8 {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hg : t ≠ .guid) : w ≤ 8 := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hg | decide

/-- A width up to eight survives `toUSize`. -/
theorem toUSize_toNat_le8 {w : Nat} (hw8 : w ≤ 8) : w.toUSize.toNat = w :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))

/-- A dense element at a type of width `w`, other than `boolean` and `guid`, is its `w` bytes' atom. -/
theorem get_bytes_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (b : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.bytes b) i =
      some (Column.atomOfBits t (Column.bitsAt b (i * w) w) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- A Frame-of-Reference element is its `foRBits` atom. -/
theorem get_foR_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (md pk : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.foR md pk) i =
      some (Column.atomOfBits t (Column.foRBits md pk #[] i) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- An ALP element is its `alpBits` atom. -/
theorem get_alp_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (md pk a : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.alp md pk a) i =
      some (Column.atomOfBits t (Column.alpBits md pk a #[] i) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- `alpBits` with no hoisted table reads the start `blockStarts` holds (`foRBits_starts`). -/
theorem alpBits_starts (md pk a : ByteArray) (i : Nat) :
    Column.alpBits md pk a #[] i = Column.alpBits md pk a (Column.blockStarts md) i := by
  unfold Column.alpBits; rw [foRBits_starts]

/-- **An element of a payload's dense decode is the payload's element**, at every well-formed payload of a type
    with a width other than `boolean`: `.bytes` is itself, `.foR` decodes to `foRBits`' low `8w` bits
    (`decodeW`), all `atomOfBits` reads (`atomOfBits_mod`), `.alp` to `alpBits` (`elemsW_alpDecode_alpBits`). -/
theorem get_bytesOf {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n : USize}
    {e : Enc} (hwf : Enc.WF t n e) {b : ByteArray} (he : Enc.bytesOf t n e = some b) {i : Nat}
    (hi : i < n.toNat) : Enc.get t n (.bytes b) i = Enc.get t n e i := by
  obtain ⟨b', hb', hs⟩ := bytesOf_size hb hw hwf
  rw [he, Option.some.injEq] at hb'; subst hb'
  cases e
  case bytes b' => simp only [Enc.bytesOf, Option.some.injEq] at he; subst he; rfl
  case foR md pk =>
    have hg : t ≠ .guid := by rintro rfl; simp [Enc.WF] at hwf
    have hwu := toUSize_toNat_le8 (width_le8 hw hg)
    simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at he; subst he
    have hd := (Verify.decodeW w.toUSize (by rw [hwu]; exact width_le8 hw hg) md pk n).2 i hi
    rw [hwu] at hd
    rw [get_bytes_eq hw hb hg _ hi, get_foR_eq hw hb hg _ _ hi, hd, foRBits_starts, Verify.atomOfBits_mod hw hb hg]
  case alp md pk a =>
    have hg : t ≠ .guid := by rintro rfl; simp [Enc.WF] at hwf
    have hwu := toUSize_toNat_le8 (width_le8 hw hg)
    have hw0 : 0 < w := by
      cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;> decide
    have hesz : Column.alpEsz a = w := by
      cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
        simp_all [Enc.WF, Column.alpEsz, QAtomicType.width]
    simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at he; subst he
    have hel := Verify.elemsW_alpDecode_alpBits md pk a n w.toUSize (by rw [hwu, hesz])
    rw [hwu] at hel
    have h1 : i < (Verify.elemsW w (Coc.alpDecode w.toUSize md pk a n)).length := by
      simp only [Verify.elemsW, List.length_map, List.length_range, hs, Nat.mul_div_cancel _ hw0]; exact hi
    have hx := List.getElem_of_eq hel h1
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range] at hx
    rw [get_bytes_eq hw hb hg _ hi, get_alp_eq hw hb hg _ _ _ hi, hx, alpBits_starts]
  all_goals simp [Enc.bytesOf] at he

/-- A column's list is its elements read off its dense decode `Enc.bytesOf`, at every encoding. -/
theorem toList_bytesOf {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n : USize}
    (x : Arr t n) {b : ByteArray} (hx : Enc.bytesOf t n x.enc = some b) :
    x.toList = ((List.range n.toNat).map fun i => Enc.get t n (.bytes b) i).map
      fun o => (o.bind fun a => Carrier.of? t (.atom a)).getD default := by
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  apply List.ext_getElem (by simp [Arr.length_toList])
  intro j h1 h2
  have hj : j < n.toNat := by simpa [Arr.length_toList] using h1
  rw [Arr.getElem_toList, Arr.get_ne _ _ hg]
  simp only [List.getElem_map, List.getElem_range]
  rw [get_bytesOf hw hb x.wf hx hj]

/-- `razeColumn` where it answers dense — no part is encoded to meet (`encodedParts = none`), or the encoded
    join is the dearer (`denseCheaper`) — at a type with a width other than `boolean`: the parts' decodes end
    to end. -/
theorem razeColumn_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    {cs : Array (USize × Enc)} (hwf : ∀ c ∈ cs, Enc.WF t c.1 c.2)
    (hD : ∀ r, encodedParts t cs = some r → denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w)
      (straddles (r.2.2.1.map (·.toNat))) = true)
    {v : QValue} (hv : razeColumn t cs = some v) :
    v = .vector t (cs.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
      (.bytes (concatBytes (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty))) none := by
  have hm : cs.mapM (fun (c : USize × Enc) => Enc.bytesOf t c.1 c.2) =
      some (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) :=
    mapM_some _ fun c hc => by obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (hwf c hc); simp [hb']
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases hE : encodedParts t cs with
  | none =>
    cases t
    case boolean => exact absurd rfl hb
    case symbol => simp [QAtomicType.width] at hw
    case general => simp [QAtomicType.width] at hw
    all_goals
      simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
      simp only [QAtomicType.width, hE, hm] at hv
      obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
      cases hv; rfl
  | some r =>
    have hC := hD r hE
    obtain ⟨alp, N, ns, ms, ps, as⟩ := r
    dsimp only at hC
    cases t
    case boolean => exact absurd rfl hb
    case symbol => simp [QAtomicType.width] at hw
    case general => simp [QAtomicType.width] at hw
    all_goals
      simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
      simp only [QAtomicType.width, hE, hC, ↓reduceIte, hm] at hv
      obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
      cases hv; rfl

/-- **`razeTo` where `razeColumn` answers dense**: the razed column lists its parts' elements one part after
    another, whatever each part's encoding. -/
theorem razeTo_toList_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (cs : Array ((k : USize) × Arr t k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size)
    (hD : ∀ r, encodedParts t (cs.map (·.2.part)) = some r → denseCheaper (if r.1 then 8 else 5) r.2.1
      (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr t k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  rw [dif_neg (by simpa using h0), dif_neg hg]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr t n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hsum : (l.map (·.1.toNat)).sum = S := by simpa using hs
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk, hsum]; exact hS
  unfold need; rw [dif_pos hf]
  have hpw : ∀ c ∈ (List.toArray l).map (·.2.part), Enc.WF t c.1 c.2 := by
    intro c hc; obtain ⟨d, -, rfl⟩ := Array.mem_map.1 hc; exact d.2.wf
  let gb : ((n : USize) × Arr t n) → ByteArray := fun c => (Enc.bytesOf t c.1 c.2.enc).getD .empty
  have hB : concatBytes (((List.toArray l).map (·.2.part)).map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) =
      l.foldl (fun a c => a ++ gb c) .empty := by
    simp only [concatBytes, Array.foldl_map, List.foldl_toArray', Arr.part, gb]
  have hv : ∀ h, ((razeColumn t ((List.toArray l).map (·.2.part))).get h) =
      .vector t (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
        (.bytes (l.foldl (fun a c => a ++ gb c) .empty)) none := fun h => by
    rw [← hB]; exact razeColumn_dense hw hb hpw hD (Option.some_get h).symm
  have hgb : ∀ c ∈ l, Enc.bytesOf t c.1 c.2.enc = some (gb c) := fun c _ => by
    obtain ⟨b, hb', -⟩ := bytesOf_size hb hw c.2.wf; simp [gb, hb']
  have hsz : ∀ c ∈ l, (gb c).size = c.1.toNat * w := fun c _ => by
    obtain ⟨b, hb', hs⟩ := bytesOf_size hb hw c.2.wf
    simp only [gb, hb', Option.getD_some]; exact hs
  have hN : (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize.toNat =
      (l.map (·.1.toNat)).sum := by rw [USize.toNat_ofNat_of_lt' hf, hk]
  refine (toList_bytes _ (b := l.foldl (fun a c => a ++ gb c) .empty) (by simp only [Arr.enc, hv]) hg).trans ?_
  have hF := foldl_bytes_get hw
    (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize gb l .empty 0
    (by rw [Nat.zero_mul]; rfl) hsz (by rw [hN]; omega)
  rw [Nat.zero_add, List.range_zero, List.map_nil, List.nil_append] at hF
  rw [hN, hF, List.map_flatMap]
  unfold List.flatMap; congr 1
  apply List.map_congr_left; intro c hc
  rw [toList_bytesOf hw hb c.2 (hgb c hc)]

/-- **`razeTo` over dense parts**: the razed column lists its parts' elements one part after another. -/
theorem razeTo_toList_bytes {t : QAtomicType} (cs : Array ((k : USize) × Arr t k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) (hcs : ∀ c ∈ cs, ∃ b, c.2.enc = .bytes b) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  rcases cs with ⟨l⟩
  simp only [List.mem_toArray] at hcs
  by_cases h0 : l = []
  · subst h0
    unfold razeTo; rw [cast_toList]; unfold raze
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr t k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil l h0
  obtain ⟨b₀, hb₀⟩ := hcs c₀ hc₀
  have hwf := c₀.2.wf; rw [hb₀] at hwf
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by
    revert hwf; cases t <;> simp [Enc.WF, QAtomicType.width]
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  have hbo : t ≠ .boolean := by rintro rfl; simp [Enc.WF] at hwf
  exact razeTo_toList_dense hw hbo _ hs hS fun r hr => by
    rw [encodedParts_bytes fun c hc => by
      obtain ⟨d, hd, rfl⟩ := Array.mem_map.1 hc; exact hcs d (by simpa using hd)] at hr
    cases hr

/-- A general list's list is its `gen` payload's. -/
theorem toList_gen {n : USize} (x : Arr .general n) {xs : Array QValue} (he : x.enc = .gen xs) :
    x.toList = xs.toList := by
  apply List.ext_getElem (by rw [Arr.length_toList, Array.length_toList, Arr.gen_size x he])
  intro j h1 h2; rw [Arr.getElem_toList, get_general _ he]; simp

/-- A general list's list is its boxed elements. -/
theorem toList_general {n : USize} (x : Arr .general n) : x.toList = (gens x).toList := by
  obtain ⟨xs, he, -⟩ := general_cases x.wf
  have hgx : gens x = xs := Option.some_inj.1 ((Option.some_get _).trans (by simp [he]))
  rw [toList_gen x he, hgx]

/-- `genCol` of an array whose size fits a `USize` lists it. -/
theorem genCol_toList {xs : Array QValue} (h : xs.size < USize.size) : (genCol xs).2.toList = xs.toList := by
  unfold genCol need; rw [dif_pos h]; exact toList_gen _ rfl

/-- **`razeTo` at `general`**: the razed list lists its parts' elements one part after another. -/
theorem razeTo_toList_general (cs : Array ((k : USize) × Arr .general k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) :
    (razeTo .general cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr .general k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  rw [dif_neg (by simpa using h0), dif_pos rfl]
  have key : ∀ (acc : Array QValue) (l : List ((n : USize) × Arr .general n)),
      (l.foldl (fun xs c => xs ++ gens c.2) acc).toList = acc.toList ++ l.flatMap fun c => (gens c.2).toList := by
    intro acc l; induction l generalizing acc <;> simp_all [List.append_assoc]
  have hf : ((List.toArray l).foldl (fun xs c => xs ++ gens c.2) #[]).size < USize.size := by
    rw [← Array.length_toList]; simp only [List.foldl_toArray']; rw [key]
    have h3 : ∀ c ∈ l, (gens c.2).toList.length = c.1.toNat := fun c _ => by
      rw [← toList_general, Arr.length_toList]
    have h2 : (l.map (·.1.toNat)).sum = S := by simpa using hs
    simp only [List.length_append, List.length_flatMap, List.map_congr_left h3]
    simpa [h2] using hS
  refine (genCol_toList hf).trans ?_
  simp only [List.foldl_toArray']; rw [key]
  unfold List.flatMap; simp only [List.nil_append]; congr 1
  apply List.map_congr_left; intro c _; rw [toList_general]

/-- A `range`-indexed `flatMap` that reads the array `xs` at its index is the `flatMap` over `xs`. -/
theorem flatMap_range {α β : Type} (xs : Array α) (f : Nat → List β) (G : α → List β)
    (h : ∀ k (hk : k < xs.size), f k = G xs[k]) : (List.range xs.size).flatMap f = xs.toList.flatMap G := by
  have e : (List.range xs.size).map f = xs.toList.map G :=
    List.ext_getElem (by simp) fun k h1 h2 => by
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList]
      exact h k (by simpa using h1)
  unfold List.flatMap; rw [e]

/-- A boolean column's payload is its bitmap `tagBits`. -/
theorem enc_tagBits {n : USize} (x : Arr .boolean n) : x.enc = .bits (tagBits x) := by
  obtain ⟨b, hb⟩ : ∃ b, x.enc = .bits b := by have hw := x.wf; revert hw; cases x.enc <;> simp [Enc.WF]
  rw [hb]; simp [tagBits, hb]

/-- A boolean column's list is its bitmap's first `n` bits. -/
theorem toList_bits {n : USize} (x : Arr .boolean n) {b : ByteArray} (hx : x.enc = .bits b) :
    x.toList = (List.range n.toNat).map (Column.bitAt b) := by
  apply List.ext_getElem (by rw [Arr.length_toList, List.length_map, List.length_range])
  intro j h1 h2; rw [Arr.getElem_toList, Arr.get_bool_bits x hx]; simp

/-- **`razeTo` at `boolean`**: the razed bitmap lists its parts' bits one part after another
    (`concatBits`). -/
theorem razeTo_toList_boolean (cs : Array ((k : USize) × Arr .boolean k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) :
    (razeTo .boolean cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr .boolean k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  rw [dif_neg (by simpa using h0), dif_neg (by decide)]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr .boolean n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hsum : (l.map (·.1.toNat)).sum = S := by simpa using hs
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk, hsum]; exact hS
  unfold need; rw [dif_pos hf]
  let ps : Array (USize × ByteArray) := (List.toArray l).map fun c => (c.1, tagBits c.2)
  have hm : ((List.toArray l).map (·.2.part)).mapM
      (fun | ((n : USize), Enc.bits b) => some (n, b) | _ => none) = some ps := by
    rw [Array.mapM_map]
    exact mapM_some _ fun c _ => by simp only [Function.comp, Arr.part, enc_tagBits c.2]
  have hps : ps.foldl (fun s (p : USize × ByteArray) => s + p.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    have e : ∀ (a : Nat) (l : List ((n : USize) × Arr .boolean n)),
        (l.map fun c => (c.1, tagBits c.2)).foldl (fun s (p : USize × ByteArray) => s + p.1.toNat) a =
          a + (l.map (·.1.toNat)).sum := by
      intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
    simpa [ps] using e 0 l
  have hv : ∀ h, (razeColumn .boolean ((List.toArray l).map (·.2.part))).get h =
      .vector .boolean (ps.foldl (fun s (p : USize × ByteArray) => s + p.1.toNat) 0).toUSize
        (.bits (concatBits (countBytes (ps.map (·.1))) (ps.map (·.2)))) none := fun h => by
    apply Option.some_inj.1; rw [Option.some_get]
    unfold razeColumn
    rw [if_neg (by simpa using h0)]
    dsimp only
    split
    next ps' heq =>
      obtain rfl : ps' = ps := Option.some_inj.1 (heq.symm.trans hm)
      simp only [needSize, need]; rw [dif_pos (by rw [hps, hsum]; exact hS)]
    next heq => cases heq.symm.trans hm
  refine (toList_bits _ (b := concatBits (countBytes (ps.map (·.1))) (ps.map (·.2)))
    (by simp only [Arr.enc, hv])).trans ?_
  have hN : (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize.toNat =
      (l.map (·.1.toNat)).sum := by rw [USize.toNat_ofNat_of_lt' hf, hk]
  rw [hN]
  simp only [concatBits]
  have hK : min ((countBytes (ps.map (·.1))).size / 8) (ps.map (·.2)).size = ps.size := by
    rw [countBytes_size]; simp
  rw [hK]
  generalize hb : Array.flatMap _ (Array.range ps.size) = bs
  have hbs : bs.toList = l.flatMap (·.2.toList) := by
    rw [← hb]
    simp only [Array.toList_flatMap, Array.toList_range, Array.toList_map]
    refine (flatMap_range ps _ (fun c => (List.range c.1.toNat).map (Column.bitAt c.2)) fun k hk => ?_).trans ?_
    · have hk' : k < (ps.map (·.1)).size := by simpa using hk
      rw [countBytes_get _ k hk', getElem!_pos _ k (by simpa using hk)]
      simp [USize.toNat_toUInt64]
    · simp only [ps, Array.toList_map, List.flatMap_map]
      unfold List.flatMap; congr 1
      apply List.map_congr_left; intro c _; rw [toList_bits c.2 (enc_tagBits c.2)]
  have hlen : bs.size = (l.map (·.1.toNat)).sum := by
    rw [← Array.length_toList, hbs, List.length_flatMap]; congr 1
    apply List.map_congr_left; intro c _; exact Arr.length_toList c.2
  rw [← hbs]
  apply List.ext_getElem (by simp [hlen])
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, Verify.bitAt_packOf _ _ _ (by simpa [hlen] using h1),
    Array.getElem_toList, Array.getElem?_eq_getElem (by simpa [hlen] using h1), Option.getD_some]

end LeetQ.Rel.KernelWF
