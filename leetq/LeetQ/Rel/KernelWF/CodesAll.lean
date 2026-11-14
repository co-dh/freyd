/-
  `Obj.codes` faithful and well formed at every side built from the covered atoms by `.prod`, `.arr` and
  `.sum`: one recursion on `Obj` over the node theorems (`codes_prod_faithful_wf`, `codes_arr_faithful_wf`,
  `codes_sum_faithful_wf`) and the atoms' several-part theorems.
-/
import LeetQ.Rel.KernelWF.CodesArr
import LeetQ.Rel.KernelWF.CodesSymParts
import LeetQ.Rel.KernelWF.CodesLongParts
import LeetQ.Rel.KernelWF.CodesNumParts
import LeetQ.Rel.KernelWF.CodesGuidParts
import LeetQ.Rel.KernelWF.CodesGeneral

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- The bounds `Obj.codes` needs at every node of `A`, on the parts it hands that node: each node theorem's
    size bounds and `Vals.PickFits`; at an atom, the kinds a several-part theorem covers — boolean, a small
    integral or a float side, its parts and their raze in any encoding, the parts' count 32 bits where an ALP
    join offsets them, an `.i64` side, its parts and their raze in any encoding,
    a symbol side whose dictionaries summed fit a `USize`, a guid side, a general side whose elements hold no
    `IndexCell` (`cellFree`, where `valEq` is `=`). -/
def _root_.LeetQ.Rel.Obj.CodesFit : (A : Obj) → {p : Nat} → Vector (Part A) p → Prop
  | .atom t, p, cs => (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    (t = .boolean ∨
      (∃ k₀, orderKind t = some k₀ ∧ (k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) ∧
        (2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32)) ∨
      orderKind t = some .i64 ∨
      (t = .symbol ∧
        (cs.toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum < USize.size) ∨
      t = .guid ∨
      (t = .general ∧ ∀ k (hk : k < p) xs, (cs[k]'hk).2.enc = .gen xs → ∀ x ∈ xs, cellFree x = true))
  | .prod a b, _, cs => (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    Obj.CodesFit a (cs.map fun c => (⟨c.1, c.2.1⟩ : Part a)) ∧ Obj.CodesFit b (cs.map fun c => (⟨c.1, c.2.2⟩ : Part b))
  | .arr b, p, cs => (∀ k (hk : k < p), Vals.PickFits (.arr b) (cs[k]'hk).2 (List.range (cs[k]'hk).1.toNat)) ∧
    (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < 2 ^ 63 ∧
    (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < USize.size ∧
    Obj.CodesFit b (cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b))
  | .sum a b, p, cs₀ =>
    (cs₀.toList.map (·.1.toNat)).sum < USize.size ∧
    (∀ k (hk : k < p), Vals.PickFits (.sum a b) (cs₀[k]'hk).2 (List.range (cs₀[k]'hk).1.toNat)) ∧
    (∀ k (hk : k < p), (cs₀[k]'hk).2.held.1.toNat < 2 ^ 61) ∧ (∀ k (hk : k < p), (cs₀[k]'hk).2.held.2.1.toNat < 2 ^ 61) ∧
    Obj.CodesFit a ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
      fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)) ∧
    Obj.CodesFit b ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
      fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b))

/-- Every part `cut` answers is on the cut code's lane. -/
theorem cut_lane {p : Nat} (c : Code) (ns : Vector USize p) {k l : Nat} (hk : k < p) (hl : l < p) :
    ((c.cut ns)[k]'hk).w = ((c.cut ns)[l]'hl).w := by
  unfold Code.cut; split <;> simp

/-- **`rangeOffsets`' codes share one lane**: every part is `packed` at the one `w` of the joint span. -/
theorem rangeOffsets_lane {a : QAtomicType} {p : Nat} {cs : Vector (USize × Enc) p} {total : Nat}
    {os : Vector Code p} (h : rangeOffsets a cs total = some os) {k l : Nat} (hk : k < p) (hl : l < p) :
    (os[k]'hk).w = (os[l]'hl).w := by
  unfold rangeOffsets at h
  split at h
  · exact absurd h (by simp)
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  -- `base` (`0` or the least element) is split first; the lane `w` does not read it
  split at h
  all_goals
    split at h
    · exact absurd h (by simp)
    have hk' := vec_mapM_some h hk
    have hl' := vec_mapM_some h hl
    generalize os[k]'hk = ok at hk' ⊢
    generalize os[l]'hl = ol at hl' ⊢
    generalize cs[k]'hk = ck at hk'
    generalize cs[l]'hl = cl at hl'
    obtain ⟨n, e⟩ := ck
    obtain ⟨n', e'⟩ := cl
    -- each part's code is `packed`, the struct literal at the joint `w`
    cases e <;> simp at hk'
    all_goals first
      | obtain ⟨-, rfl⟩ := hk'
      | (obtain ⟨_, -, hk'⟩ := Option.bind_eq_some_iff.1 hk'; split at hk' <;> cases hk')
    all_goals (cases e' <;> simp at hl')
    all_goals first
      | obtain ⟨-, rfl⟩ := hl'
      | (obtain ⟨_, -, hl'⟩ := Option.bind_eq_some_iff.1 hl'; split at hl' <;> cases hl')
    all_goals rfl

/-- **`Obj.codes` is faithful and well formed, on one lane, at every side the recursion covers**: equal codes
    exactly at equal rows, jointly across the parts; each code a lane of `1 … 64` bits, `⌈n·w/8⌉` bytes, ids below
    `card` under a byte; one lane across the parts. `Obj.CodesFit` holds the bounds node by node. -/
theorem codes_faithful_wf (A : Obj) : ∀ {p : Nat} (cs : Vector (Part A) p), A.CodesFit cs →
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes A cs)[k]'hk).b ((Obj.codes A cs)[k]'hk).w i =
          Column.idAt ((Obj.codes A cs)[l]'hl).b ((Obj.codes A cs)[l]'hl).w j ↔
        Vals.row (A := A) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := A) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes A cs)[k]'hk
        laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p), ((Obj.codes A cs)[k]'hk).w = ((Obj.codes A cs)[l]'hl).w := by
  induction A with
  | atom t =>
    intro p cs ⟨hN, ht⟩
    rcases ht with rfl | ⟨k₀, ht, hk₀, hA⟩ | ht | ⟨rfl, hD⟩ | rfl | ⟨rfl, hC⟩
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_boolean_faithful cs hk hl hi hj, fun hk => ?_⟩, fun hk hl => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := codes_boolean_wf cs hk
        exact ⟨Or.inl h2, h1, h3, h4⟩
      · rw [(codes_boolean_wf cs hk).2.1, (codes_boolean_wf cs hl).2.1]
    · exact codes_dense_faithful_wf ht hk₀ cs hN hA
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_long_dense_faithful ht cs hN hk hl hi hj,
        fun hk => codes_long_dense_wf ht cs hN hk⟩, fun hk hl => ?_⟩
      cases hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) with
      | none => obtain ⟨q, -, hc⟩ := codes_long_cut ht cs (by omega) hro; rw [hc]; exact cut_lane _ _ hk hl
      | some os => rw [codes_long_eq ht cs (by omega) hro]; exact rangeOffsets_lane hro hk hl
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_symbol_parts_faithful cs hN hD hk hl hi hj,
        fun hk => codes_symbol_parts_wf cs hN hk⟩, fun hk hl => ?_⟩
      rw [codes_symbol_cut cs (by omega)]; exact cut_lane _ _ hk hl
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_guid_parts_faithful cs hN hk hl hi hj,
        fun hk => codes_guid_parts_wf cs hN hk⟩, fun hk hl => ?_⟩
      rw [codes_guid_cut cs (by omega)]; exact cut_lane _ _ hk hl
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_general_faithful cs hN hC hk hl hi hj,
        fun hk => codes_general_wf cs hN hk⟩, fun hk hl => ?_⟩
      rw [codes_general cs]; exact cut_lane _ _ hk hl
  | prod a b iha ihb =>
    intro p cs ⟨hN, ha, hb⟩
    exact codes_prod_faithful_wf cs rfl rfl rfl rfl (iha _ ha).1 (iha _ ha).2 (ihb _ hb).1 (ihb _ hb).2 hN
  | arr b ih =>
    intro p cs ⟨hfit, hN, hC, hCU, hb⟩
    exact codes_arr_faithful_wf cs rfl rfl (ih _ hb).1 (ih _ hb).2 (fun hk => hfit _ hk) hN hC hCU
  | sum a b iha ihb =>
    intro p cs₀ ⟨hN, hfit, hLa, hLb, ha, hb⟩
    exact codes_sum_faithful_wf cs₀ rfl rfl rfl rfl rfl (iha _ ha).1 (iha _ ha).2 (ihb _ hb).1 (ihb _ hb).2
      (fun hk => by simpa using hLa _ hk) (fun hk => by simpa using hLb _ hk) hN (fun hk => hfit _ hk)

#print axioms codes_faithful_wf

/-- **A one-part atom side fits outright** at every kind whose clause bounds only what one part already
    bounds: a kind with an order layout (boolean, the dense kinds, whose ALP clause reads two parts or more, the
    64-bit kinds) or a guid. A symbol's dictionaries and a general column's cells are not bounded by a count. -/
theorem codesFit_atom_one {t : QAtomicType} (x : Part (.atom t)) (ht : orderKind t ≠ none ∨ t = .guid) :
    Obj.CodesFit (.atom t) #v[x] := by
  unfold Obj.CodesFit
  refine ⟨by simp [x.1.toNat_lt_size], ?_⟩
  rcases ht with h | rfl
  · cases t <;> simp [orderKind] at h ⊢
  · exact .inr (.inr (.inr (.inr (.inl rfl))))

/-- **A several-part atom side fits on its summed count alone** at a kind whose clause bounds nothing else: a
    boolean, an `.i64` or a guid side. -/
theorem codesFit_atom_count {t : QAtomicType} {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) (ht : t = .boolean ∨ orderKind t = some .i64 ∨ t = .guid) :
    Obj.CodesFit (.atom t) cs := by
  unfold Obj.CodesFit
  refine ⟨hN, ?_⟩
  rcases ht with h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inr (.inl h))))

/-- **An atom side's one-part code is well formed and counts its part, with no premise**: a lane of `1 … 64`
    bits, `⌈n·w/8⌉` bytes, ids below `card` under a byte. One part's count is a `USize`, so the several-part
    theorems' summed-count bound holds by itself; `.arr` and `.sum` are not here, their codes need bounds. -/
theorem codes_atom_wf (t : QAtomicType) (x : Part (.atom t)) :
    let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧ c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  have hN : (#v[x].toList.map (·.1.toNat)).sum < USize.size := by simp [x.1.toNat_lt_size]
  cases t
  case boolean =>
    obtain ⟨h1, h2, h3, h4⟩ := codes_boolean_wf #v[x] Nat.zero_lt_one
    exact ⟨Or.inl h2, h1, h3, h4⟩
  all_goals first
    | exact codes_general_wf #v[x] hN Nat.zero_lt_one
    | exact codes_guid_wf x
    | exact codes_symbol_wf x
    | exact codes_long_one_wf rfl x
    -- the kind disjunctions as terms, not `by`: a deferred tactic fails after `first` has committed
    | exact codes_small_int_wf rfl (Or.inl rfl) x
    | exact codes_small_int_wf rfl (Or.inr (Or.inl rfl)) x
    | exact codes_small_int_wf rfl (Or.inr (Or.inr rfl)) x
    | exact (codes_float_parts_wf (Or.inl rfl) #v[x] hN Nat.zero_lt_one).1
    | exact (codes_float_parts_wf (Or.inr (Or.inl rfl)) #v[x] hN Nat.zero_lt_one).1
    | exact (codes_float_parts_wf (Or.inr (Or.inr rfl)) #v[x] hN Nat.zero_lt_one).1

#print axioms codes_atom_wf

/-- **An array part's copies are its values**: where its payload count is below `2^63`, `expand` of its clamped
    counts copies as many positions as its rows hold values (`len_expand_slices`, `arr_row`), and its windows
    at all its rows are as many. -/
theorem arr_copies {b : Obj} {n : USize} (x : Vals (.arr b) n) (hp : x.1.toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) (slicesOf x).2) = ((List.range n.toNat).map fun r =>
      if h : r < n.toNat then (Vals.row (A := .arr b) x ⟨r, h⟩).length else 0).sum ∧
    ((List.range n.toNat).flatMap fun k => if h : k < n.toNat then
      List.range' (min (max (x.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
        (min (max (x.2.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat - min (max (x.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
      else []).length = ((List.range n.toNat).map fun r =>
      if h : r < n.toNat then (Vals.row (A := .arr b) x ⟨r, h⟩).length else 0).sum := by
  have hr : ∀ r (h : r < n.toNat), (Vals.row (A := .arr b) x ⟨r, h⟩).length =
      min (max (x.2.2.1.get ⟨r, h⟩).toInt 0).toNat x.1.toNat - min (max (x.2.1.get ⟨r, h⟩).toInt 0).toNat x.1.toNat :=
    fun r h => by rw [arr_row]; simp
  constructor
  · unfold slicesOf; rw [len_expand_slices hp]; congr 1; apply List.map_congr_left; intro r hr'
    have h := List.mem_range.1 hr'
    rw [dif_pos h, hr r h, longsOf_get _ h, longsOf_get _ h, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64]
  · rw [List.length_flatMap]; congr 1; apply List.map_congr_left; intro r hr'
    have h := List.mem_range.1 hr'
    rw [dif_pos h, dif_pos h, hr r h, List.length_range']

/-- **An array part's conjunct of `Obj.codesC`'s bit**: the copies `expand` counts are the values `W` its rows
    hold (`arr_copies`), below `2^63` and a `USize`, and the part picks in range at all its rows. -/
theorem codesC_arr_part {b : Obj} (c : Part (.arr b)) (W : Nat)
    (hW : W = ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum)
    (hb : (match expand c.1 (slicesOf c.2).2 (fun _ => (none : Option Nat)) (fun k _ _ _ _ => some k.toNat) with
      | some k => decide (c.2.1.toNat < 2 ^ 63) && decide (k < 2 ^ 63) && Vals.fitsN b c.2.2.2.2 k
      | none => false) = true) :
    (expand c.1 (slicesOf c.2).2 (fun _ => (none : Option Nat)) fun k _ _ _ _ => some k.toNat).getD 0 = W ∧
    W < 2 ^ 63 ∧ W < USize.size ∧ Vals.PickFits (.arr b) c.2 (List.range c.1.toNat) := by
  obtain ⟨n, ⟨p, lo, hi, f⟩⟩ := c
  dsimp only at hW hb ⊢
  simp only [expand, need] at hb ⊢
  by_cases hE : len (expandBytes 8 0 (tilLongs n) (slicesOf (⟨p, lo, hi, f⟩ : Vals (.arr b) n)).2) < USize.size
  · simp only [dif_pos hE, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    obtain ⟨⟨hp, hk⟩, hf⟩ := hb
    simp only [USize.toNat_ofNat_of_lt' hE] at hk hf ⊢
    obtain ⟨h1, h2⟩ := arr_copies (⟨p, lo, hi, f⟩ : Vals (.arr b) n) hp
    dsimp only at h1 h2
    refine ⟨by omega, by omega, by omega, ?_⟩
    unfold Vals.PickFits; dsimp only
    exact ⟨hp, by omega, by omega, pickFits_of_fitsN b f _ hf _ (by omega)⟩
  · simp [dif_neg hE, stop] at hb

/-- **`Obj.codesC`'s bit is a fit**: it decides each clause of `Obj.CodesFit` from the counts the pass computes —
    an array's copies by `codesC_arr_part`, a pick by `pickFits_of_fitsN`. -/
theorem _root_.LeetQ.Rel.Obj.codesC_fits : (A : Obj) → {p : Nat} → (cs : Vector (Part A) p) →
    (Obj.codesC A cs).2 = true → A.CodesFit cs
  | .atom t, p, cs, hb => by
    simp only [Obj.codesC, Obj.codesC.atomFit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hN, hb⟩ := hb
    unfold Obj.CodesFit
    refine ⟨hN, ?_⟩
    rcases hb with ((((hb | hb) | hb) | ⟨hs, hd⟩) | hb) | ⟨hg, hc⟩
    · exact Or.inl hb
    · refine Or.inr (Or.inl ?_)
      split at hb
      · rename_i k₀ hk
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hb
        refine ⟨k₀, hk, hb.1, fun h2 ha => ?_⟩
        rcases hb.2 with (h | h) | h
        · omega
        · rw [ha] at h; cases h
        · exact h
      · cases hb
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hd⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hg, fun k hk xs he x hx => ?_⟩))))
      have h : (match (cs[k]'hk).2.enc with | .gen xs => xs.all cellFree | _ => true) = true :=
        Array.all_eq_true.1 hc k (by simpa using hk)
      simp only [he] at h
      exact Array.all_eq_true_iff_forall_mem.1 h x hx
  | .prod a b, p, cs, hb => by
    simp only [Obj.codesC, Bool.and_eq_true, decide_eq_true_eq] at hb
    unfold Obj.CodesFit
    exact ⟨hb.1.1, Obj.codesC_fits a _ hb.1.2, Obj.codesC_fits b _ hb.2⟩
  | .sum a b, p, cs₀, hb => by
    simp only [Obj.codesC, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hN, hp⟩, hh⟩, ha⟩, hb⟩ := hb
    unfold Obj.CodesFit
    have h61 : ∀ k (hk : k < p), (cs₀[k]'hk).2.held.1.toNat < 2 ^ 61 ∧ (cs₀[k]'hk).2.held.2.1.toNat < 2 ^ 61 :=
      fun k hk => by
        have h : (decide (((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b)))[k]'hk).2.1.toNat < 2 ^ 61) &&
            decide (((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b)))[k]'hk).2.2.1.toNat < 2 ^ 61)) = true :=
          Array.all_eq_true.1 hh k (by simpa using hk)
        rw [Vector.getElem_map] at h
        simpa using h
    refine ⟨hN, fun k hk => ?_, fun k hk => (h61 k hk).1, fun k hk => (h61 k hk).2, Obj.codesC_fits a _ ha,
      Obj.codesC_fits b _ hb⟩
    have h := Array.all_eq_true.1 hp k (by simpa using hk)
    exact pickFits_of_fitsN _ _ _ h _ (by simp)
  | .arr b, p, cs, hb => by
    simp only [Obj.codesC, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hec, hN⟩, h63⟩, hU⟩, hall⟩ := hb
    generalize hgs : cs.map (fun c => expand c.1 (slicesOf c.2).2 (fun _ => (none : Option Nat))
      fun k _ _ _ _ => some k.toNat) = gs at h63 hU hall
    have part : ∀ k (hk : k < p), (gs[k].getD 0) =((List.range (cs[k]).1.toNat).map fun r =>
          if h : r < (cs[k]).1.toNat then (Vals.row (A := .arr b) (cs[k]).2 ⟨r, h⟩).length else 0).sum ∧
        ((List.range (cs[k]).1.toNat).map fun r =>
          if h : r < (cs[k]).1.toNat then (Vals.row (A := .arr b) (cs[k]).2 ⟨r, h⟩).length else 0).sum < 2 ^ 63 ∧
        ((List.range (cs[k]).1.toNat).map fun r =>
          if h : r < (cs[k]).1.toNat then (Vals.row (A := .arr b) (cs[k]).2 ⟨r, h⟩).length else 0).sum <
          USize.size ∧
        Vals.PickFits (.arr b) (cs[k]).2 (List.range (cs[k]).1.toNat) := by
      intro k hk
      have h := Array.all_eq_true.1 hall k (by simpa using hk)
      subst hgs
      simp only [Vector.getElem_toArray, Vector.getElem_zipWith, Vector.getElem_map, id] at h ⊢
      exact codesC_arr_part _ _ rfl h
    have hRL : (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
          if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum =
        (gs.toList.map fun g => g.getD 0).sum := by
      congr 1; apply List.ext_getElem (by simp); intro k h1 h2
      simp only [List.getElem_map, Vector.getElem_toList]
      exact ((part k (by simpa using h2)).1).symm
    unfold Obj.CodesFit
    exact ⟨fun k hk => (part k hk).2.2.2, hN, by rw [hRL]; exact h63, by rw [hRL]; exact hU,
      Obj.codesC_fits b _ hec⟩

#print axioms Obj.codesC_fits
#print axioms Obj.razeC_fits
#print axioms Vals.pickC_fits

end LeetQ.Rel.Alg
