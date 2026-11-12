/-
  What `raze` CONTAINS where every part is a dense payload: the razed column lists its parts' elements one
  part after another. `razeColumn` lays the parts' bytes end to end (`concatBytes`), and an element of a
  dense payload is read off its own `w` bytes only.
-/
import LeetQ.Rel.KernelWF.PickSpec

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

/-- `razeColumn` over dense parts at a type with a width other than `boolean` is the parts' bytes end to end. -/
theorem razeColumn_bytes {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    {cs : Array (USize × Enc)} (hcs : ∀ c ∈ cs, ∃ b, c.2 = .bytes b) {v : QValue} (hv : razeColumn t cs = some v) :
    v = .vector t (cs.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
      (.bytes (concatBytes (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty))) none := by
  have hm : cs.mapM (fun (c : USize × Enc) => Enc.bytesOf t c.1 c.2) =
      some (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) :=
    mapM_some _ fun c hc => by obtain ⟨b, hb⟩ := hcs c hc; simp [hb, Enc.bytesOf]
  have hany : ∀ p : USize × Enc → Bool, (∀ c ∈ cs, ∀ b, c.2 = .bytes b → p c = false) → cs.any p = false :=
    fun p hp => Bool.eq_false_iff.2 fun h => by
      obtain ⟨i, hi, h⟩ := Array.any_eq_true.1 h
      obtain ⟨b, hb⟩ := hcs cs[i] (Array.getElem_mem hi)
      rw [hp _ (Array.getElem_mem hi) b hb] at h; cases h
  have hE : encodedParts t cs = none := by
    unfold encodedParts; dsimp only
    rw [hany _ (fun c _ b hb => by simp [hb])]
    simp
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  case boolean => exact absurd rfl hb
  case symbol => simp [QAtomicType.width] at hw
  case general => simp [QAtomicType.width] at hw
  all_goals
    simp only [hE, QAtomicType.width] at hv
    simp only [hm] at hv
    obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
    cases hv; rfl

/-- **`razeTo` over dense parts**: the razed column lists its parts' elements one part after another. -/
theorem razeTo_toList_bytes {t : QAtomicType} (cs : Array ((k : USize) × Arr t k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) (hcs : ∀ c ∈ cs, ∃ b, c.2.enc = .bytes b) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  simp only [List.mem_toArray] at hcs
  unfold raze
  by_cases h0 : l = []
  · subst h0
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
  have hps : ∀ c ∈ (List.toArray l).map (·.2.part), ∃ b, c.2 = .bytes b := by
    intro c hc; obtain ⟨d, hd, rfl⟩ := Array.mem_map.1 hc; exact hcs d (by simpa using hd)
  let gb : ((n : USize) × Arr t n) → ByteArray := fun c => (Enc.bytesOf t c.1 c.2.enc).getD .empty
  have hB : concatBytes (((List.toArray l).map (·.2.part)).map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) =
      l.foldl (fun a c => a ++ gb c) .empty := by
    simp only [concatBytes, Array.foldl_map, List.foldl_toArray', Arr.part, gb]
  have hv : ∀ h, ((razeColumn t ((List.toArray l).map (·.2.part))).get h) =
      .vector t (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
        (.bytes (l.foldl (fun a c => a ++ gb c) .empty)) none := fun h => by
    rw [← hB]; exact razeColumn_bytes hw hbo hps (Option.some_get h).symm
  have hgb : ∀ c ∈ l, c.2.enc = .bytes (gb c) := fun c hc => by
    obtain ⟨b, hb⟩ := hcs c hc; simp [gb, hb, Enc.bytesOf]
  have hsz : ∀ c ∈ l, (gb c).size = c.1.toNat * w := fun c hc => by
    obtain ⟨b, hb, hs⟩ := bytesOf_size hbo hw c.2.wf
    simp only [gb, hb, Option.getD_some]; exact hs
  have hN : (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize.toNat = (l.map (·.1.toNat)).sum :=
    by rw [USize.toNat_ofNat_of_lt' hf, hk]
  refine (toList_bytes _ (b := l.foldl (fun a c => a ++ gb c) .empty) (by simp only [Arr.enc, hv]) hg).trans ?_
  have hF := foldl_bytes_get hw (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize gb l .empty 0
    (by rw [Nat.zero_mul]; rfl) hsz (by rw [hN]; omega)
  rw [Nat.zero_add, List.range_zero, List.map_nil, List.nil_append] at hF
  rw [hN, hF, List.map_flatMap]
  unfold List.flatMap; congr 1
  apply List.map_congr_left; intro c hc
  rw [toList_bytes c.2 (hgb c hc) hg]

end LeetQ.Rel.KernelWF
