/-
  `Obj.codes` on one part of a symbol side: `Column.intern` leaves an `enum` part as it is and interns a
  `syms` part (`Order.internSyms`); the code is the dictionary id at its lane (`Code.ofLane`). Two rows share
  an id exactly when they share a symbol, because the dictionary has no entry twice and every entry is
  valid UTF-8, where `String.fromUTF8?` answers and is injective.
-/
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.Raze

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## Lanes -/

/-- The largest id below `nd` fits a lane `idWidthOf nd` under a byte: a lane of no bits leaves room for the
    id `0` only. (At `64` bits it need not: `nd` is not bounded.) -/
theorem pred_lt_idWidthOf {nd : Nat} (h8 : Column.idWidthOf nd < 8) : nd - 1 < 2 ^ Column.idWidthOf nd := by
  have h := lt_widthFor (nd - 1)
  unfold Column.idWidthOf at h8 ⊢
  generalize Column.widthFor (nd - 1) = w at h h8 ⊢
  have hl : w ≤ Column.laneWidth w := by
    unfold Column.laneWidth at h8 ⊢
    repeat' split
    all_goals (repeat' split at h8)
    all_goals omega
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hl)

/-- `Code.ofLane` reads back the ids it was given; at a lane of no bits, where every id is `0`, its bitmap of
    zeros reads `0`. -/
theorem ofLane_idAt {w : Nat} {n : USize} {card : Nat} {ids : ByteArray} {i : Nat}
    (h0 : w = 0 → Column.idAt ids w i = 0) :
    Column.idAt (Code.ofLane w n card ids).b (Code.ofLane w n card ids).w i = Column.idAt ids w i := by
  unfold Code.ofLane
  split
  · next h =>
    rw [h0 (by simpa using h)]
    simp only [idAt_one]
    simp [Column.bitAt, KernelWF.ba_get?, Array.getElem?_replicate] <;> split <;> simp
  · rfl

/-- **`Code.ofLane` is a well-formed code** for ids below `card` packed at a lane `w` that holds `card - 1`,
    in exactly `⌈n·w/8⌉` bytes where the lane has bits. -/
theorem ofLane_wf {w : Nat} {n : USize} {card : Nat} {ids : ByteArray}
    (hw : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hsz : w ≠ 0 → ids.size = (n.toNat * w + 7) / 8) (hcard : w < 8 → card - 1 < 2 ^ w)
    (hid : ∀ i < n.toNat, Column.idAt ids w i < card) :
    let c := Code.ofLane w n card ids
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = n ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  dsimp only
  have hcd : (Code.ofLane w n card ids).card = card := by unfold Code.ofLane; split <;> rfl
  have hn : (Code.ofLane w n card ids).n = n := by unfold Code.ofLane; split <;> rfl
  have hz : w = 0 → ∀ i < n.toNat, Column.idAt ids w i = 0 := fun h i hi => by
    have := hid i hi; have hc := hcard (by omega); subst h; rw [Nat.pow_zero] at hc; omega
  have hsh : ((Code.ofLane w n card ids).w = 1 ∨ (Code.ofLane w n card ids).w = 2 ∨
      (Code.ofLane w n card ids).w = 4 ∨ (Code.ofLane w n card ids).w = 8 ∨ (Code.ofLane w n card ids).w = 16 ∨
      (Code.ofLane w n card ids).w = 32 ∨ (Code.ofLane w n card ids).w = 64) ∧
      (Code.ofLane w n card ids).b.size = (n.toNat * (Code.ofLane w n card ids).w + 7) / 8 ∧
      ((Code.ofLane w n card ids).w < 8 → w < 8) := by
    unfold Code.ofLane; split
    · next h =>
      have : w = 0 := by simpa using h
      exact ⟨.inl rfl, by simp [ByteArray.size], fun _ => by omega⟩
    · next h =>
      have : w ≠ 0 := by simpa using h
      exact ⟨hw.resolve_left this, hsz this, id⟩
  refine ⟨hsh.1, hn, by rw [hn]; exact hsh.2.1, fun h8 => ⟨?_, fun i hi => ?_⟩⟩
  · rw [hcd]
    have hw8 := hsh.2.2 h8
    have hcard := hcard hw8
    have h7 : 2 ^ w ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have := USize.le_size
    rw [show (2 : Nat) ^ 7 = 128 from rfl] at h7
    omega
  · rw [hn] at hi
    rw [hcd, ofLane_idAt (fun h => hz h i hi)]
    exact hid i hi

/-! ## Rows of a symbol column -/

/-- Two strings are equal when their UTF-8 bytes are. -/
theorem str_eq_of_bytes {s t : String} (h : s.toUTF8.data.toList = t.toUTF8.data.toList) : s = t := by
  have e : s.toUTF8 = t.toUTF8 := ByteArray.ext (Array.toList_inj.1 h)
  obtain ⟨bs, hs⟩ := s
  obtain ⟨bt, ht⟩ := t
  obtain rfl : bs = bt := e
  rfl

/-- An interned row's bytes are its dictionary entry, which is valid UTF-8. -/
theorem enum_row {n : USize} (x : Arr .symbol n) {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (he : x.enc = .enum d o ids) (hu : ∀ k < o.size - 1, (Column.symKey d o k).IsValidUTF8)
    (hlt : ∀ i < n.toNat, Column.idAt ids (Column.idWidth o) i < o.size - 1) (i : Fin n.toNat) :
    (Vals.row (A := .atom .symbol) x i).toUTF8.data.toList = symAt d o (Column.idAt ids (Column.idWidth o) i) := by
  rw [Vals.row_atom, Arr.get_ne x i (by decide), he,
    show Enc.get .symbol n (.enum d o ids) i = some (.symbol ((String.fromUTF8?
      (Column.symKey d o (Column.idAt ids (Column.idWidth o) i))).getD "")) by simp only [Enc.get, if_pos i.2]; rfl]
  simp only [Option.bind_some, Carrier.of?, Option.getD_some]
  exact str_bytes ⟨⟨_, hu _ (hlt i i.2)⟩, rfl⟩

/-- A blob row's bytes are its own symbol, which is valid UTF-8. -/
theorem syms_row {n : USize} (x : Arr .symbol n) {b : ByteArray} {o : Array Nat}
    (he : x.enc = .syms b o) (hu : ∀ k < n.toNat, (Column.symKey b o k).IsValidUTF8) (i : Fin n.toNat) :
    (Vals.row (A := .atom .symbol) x i).toUTF8.data.toList = symAt b o i := by
  rw [Vals.row_atom, Arr.get_ne x i (by decide), he,
    show Enc.get .symbol n (.syms b o) i = some (.symbol ((String.fromUTF8? (Column.symKey b o i)).getD ""))
      by simp only [Enc.get, if_pos i.2]; rfl]
  simp only [Option.bind_some, Carrier.of?, Option.getD_some]
  exact str_bytes ⟨⟨_, hu _ i.2⟩, rfl⟩

/-! ## The code of one part -/

/-- `Column.intern` of a `syms` payload, by its components. -/
theorem intern_syms (b : ByteArray) (o : Array Nat) :
    Column.intern (.syms b o) =
      .enum (Order.internSyms b o).1 (Order.internSyms b o).2.1 (Order.internSyms b o).2.2 := rfl

/-- **One part of a symbol side is coded by its interned ids** at their lane, `Code.ofLane`. -/
theorem codes_symbol (x : Part (.atom .symbol)) :
    ∃ d o ids, Column.intern x.2.enc = .enum d o ids ∧
      (Obj.codes (.atom .symbol) #v[x])[0] = Code.ofLane (Column.idWidth o) x.1 (o.size - 1) ids := by
  obtain ⟨n, v, hv⟩ := x
  cases v <;> try exact hv.elim
  rename_i t' n' e a
  obtain ⟨h1, h2, hwf⟩ := hv
  subst h1 h2
  cases e <;> simp [Enc.WF, QAtomicType.width] at hwf <;>
    simp [Obj.codes, Alg.codes, rangeOffsets, orderKind, raze, intern_syms, Column.intern, Code.cut, vmapM_one,
      Column.encodes, Arr.enc] <;>
    exact ⟨_, _, _, ⟨rfl, rfl, rfl⟩, rfl⟩

/-- A code read at `Code.ofLane` of ids below a dictionary of no entry twice: equal codes are equal rows,
    where each row's bytes are its entry. -/
theorem lane_faithful {n : USize} (x : Arr .symbol n) {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (hlt : ∀ i < n.toNat, Column.idAt ids (Column.idWidth o) i < o.size - 1)
    (hD : ((List.range (o.size - 1)).map (symAt d o)).Nodup)
    (hr : ∀ i : Fin n.toNat,
      (Vals.row (A := .atom .symbol) x i).toUTF8.data.toList = symAt d o (Column.idAt ids (Column.idWidth o) i))
    {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat) :
    Column.idAt (Code.ofLane (Column.idWidth o) n (o.size - 1) ids).b
          (Code.ofLane (Column.idWidth o) n (o.size - 1) ids).w i =
        Column.idAt (Code.ofLane (Column.idWidth o) n (o.size - 1) ids).b
          (Code.ofLane (Column.idWidth o) n (o.size - 1) ids).w j ↔
      Vals.row (A := .atom .symbol) x ⟨i, hi⟩ = Vals.row (A := .atom .symbol) x ⟨j, hj⟩ := by
  have hz : ∀ k < n.toNat, Column.idWidth o = 0 → Column.idAt ids (Column.idWidth o) k = 0 := fun k hk h => by
    have h1 := hlt k hk
    have h2 := pred_lt_idWidthOf (nd := o.size - 1) (by change Column.idWidth o < 8; omega)
    change o.size - 1 - 1 < 2 ^ Column.idWidth o at h2
    rw [h, Nat.pow_zero] at h2
    omega
  rw [ofLane_idAt (hz i hi), ofLane_idAt (hz j hj)]
  constructor
  · intro h
    apply str_eq_of_bytes
    rw [hr ⟨i, hi⟩, hr ⟨j, hj⟩]
    exact congrArg (symAt d o) h
  · intro h
    exact map_range_inj hD (hlt i hi) (hlt j hj) (by rw [← hr ⟨i, hi⟩, ← hr ⟨j, hj⟩, h])

/-- The lane of a dictionary holds its largest id: `idWidth o` is a lane, and `o.size - 2 < 2 ^ idWidth o`. -/
theorem idWidth_facts (o : Array Nat) :
    (Column.idWidth o = 0 ∨ Column.idWidth o = 1 ∨ Column.idWidth o = 2 ∨ Column.idWidth o = 4 ∨
      Column.idWidth o = 8 ∨ Column.idWidth o = 16 ∨ Column.idWidth o = 32 ∨ Column.idWidth o = 64) ∧
    (Column.idWidth o < 8 → o.size - 1 - 1 < 2 ^ Column.idWidth o) :=
  ⟨laneWidth_cases _, fun h => pred_lt_idWidthOf h⟩

/-! ### An `enum` part -/

/-- **One `enum` part of a symbol side: its codes are faithful**, under the part's `Enc.WF` alone. -/
theorem codes_symbol_enum_faithful (x : Part (.atom .symbol)) {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (he : x.2.enc = .enum d o ids) {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  obtain ⟨d', o', ids', hi', hc⟩ := codes_symbol x
  rw [he] at hi'
  simp only [Column.intern, Enc.enum.injEq] at hi'
  obtain ⟨rfl, rfl, rfl⟩ := hi'
  have hwf := x.2.wf
  rw [he] at hwf
  obtain ⟨-, -, hlt, hD, hu⟩ := hwf
  rw [hc]
  exact lane_faithful x.2 hlt hD (enum_row x.2 he hu hlt) hi hj

/-- **One `enum` part of a symbol side: its code is well formed**, under the part's `Enc.WF` alone. -/
theorem codes_symbol_enum_wf (x : Part (.atom .symbol)) {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (he : x.2.enc = .enum d o ids) :
    let c := (Obj.codes (.atom .symbol) #v[x])[0]
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨d', o', ids', hi', hc⟩ := codes_symbol x
  rw [he] at hi'
  simp only [Column.intern, Enc.enum.injEq] at hi'
  obtain ⟨rfl, rfl, rfl⟩ := hi'
  have hwf := x.2.wf
  rw [he] at hwf
  obtain ⟨hsz, -, hlt, -, -⟩ := hwf
  dsimp only
  rw [hc]
  exact ofLane_wf (idWidth_facts o).1 (fun _ => hsz) (idWidth_facts o).2 hlt

/-! ### A `syms` part -/

/-- What `internSyms` of a well-formed `syms` part of `n` symbols answers: ids below the dictionary's count,
    a dictionary of no entry twice, each element's bytes its entry, packed in `⌈n·w/8⌉` bytes. -/
theorem internSyms_facts {n : USize} (x : Arr .symbol n) {b : ByteArray} {o : Array Nat}
    (he : x.enc = .syms b o) :
    (∀ i < n.toNat, Column.idAt (Order.internSyms b o).2.2 (Column.idWidth (Order.internSyms b o).2.1) i <
      (Order.internSyms b o).2.1.size - 1) ∧
    ((List.range ((Order.internSyms b o).2.1.size - 1)).map
      (symAt (Order.internSyms b o).1 (Order.internSyms b o).2.1)).Nodup ∧
    (∀ i : Fin n.toNat, (Vals.row (A := .atom .symbol) x i).toUTF8.data.toList =
      symAt (Order.internSyms b o).1 (Order.internSyms b o).2.1
        (Column.idAt (Order.internSyms b o).2.2 (Column.idWidth (Order.internSyms b o).2.1) i)) ∧
    (Column.idWidth (Order.internSyms b o).2.1 ≠ 0 →
      (Order.internSyms b o).2.2.size = (n.toNat * Column.idWidth (Order.internSyms b o).2.1 + 7) / 8) := by
  have hwf := x.wf
  rw [he] at hwf
  obtain ⟨hos, -, hu⟩ := hwf
  have hn : o.size - 1 = n.toNat := by omega
  have hU : o.size - 1 < USize.size := by have := n.toNat_lt_size; omega
  have e : Order.internSyms b o = ((Order.distinctSyms b o).1, (Order.distinctSyms b o).2,
      Column.packIds (Column.idWidth (Order.distinctSyms b o).2) (o.size - 1) fun j =>
        (findSymScalar (Order.distinctSyms b o).1 (Order.distinctSyms b o).2
          (Column.symKey b o j)).toNat) := rfl
  refine ⟨fun i hi => (internSyms_symAt b o hU (by omega)).1, ?_, fun i => ?_, fun h0 => ?_⟩
  · have hD := distinctSyms_eraseDups b o
    dsimp only [symsOf] at hD
    simp only [← firstsOf_eraseDups] at hD
    rw [e]; dsimp only
    rw [hD]; exact nodup_firsts (symAt b o) (o.size - 1)
  · rw [syms_row x he hu i, (internSyms_symAt b o hU (by omega)).2]
  · rw [e] at h0 ⊢; dsimp only at h0 ⊢
    rw [hn]
    exact packIds_size ((laneWidth_cases _).resolve_left h0) _ _

/-- **One `syms` part of a symbol side: its codes are faithful**, under the part's `Enc.WF` alone. -/
theorem codes_symbol_syms_faithful (x : Part (.atom .symbol)) {b : ByteArray} {o : Array Nat}
    (he : x.2.enc = .syms b o) {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  obtain ⟨d', o', ids', hi', hc⟩ := codes_symbol x
  rw [he, intern_syms, Enc.enum.injEq] at hi'
  obtain ⟨rfl, rfl, rfl⟩ := hi'
  obtain ⟨hlt, hD, hr, -⟩ := internSyms_facts x.2 he
  rw [hc]
  exact lane_faithful x.2 hlt hD hr hi hj

/-- **One `syms` part of a symbol side: its code is well formed**, under the part's `Enc.WF` alone. -/
theorem codes_symbol_syms_wf (x : Part (.atom .symbol)) {b : ByteArray} {o : Array Nat}
    (he : x.2.enc = .syms b o) :
    let c := (Obj.codes (.atom .symbol) #v[x])[0]
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨d', o', ids', hi', hc⟩ := codes_symbol x
  rw [he, intern_syms, Enc.enum.injEq] at hi'
  obtain ⟨rfl, rfl, rfl⟩ := hi'
  obtain ⟨hlt, -, -, hsz⟩ := internSyms_facts x.2 he
  dsimp only
  rw [hc]
  exact ofLane_wf (idWidth_facts _).1 hsz (idWidth_facts _).2 hlt

/-! ### Either encoding -/

/-- A symbol payload is a blob or interned (`Enc.WF`). -/
theorem symbol_enc {n : USize} {e : Enc} (hwf : Enc.WF .symbol n e) :
    (∃ b o, e = .syms b o) ∨ ∃ d o ids, e = .enum d o ids := by
  cases e <;> simp [Enc.WF, QAtomicType.width] at hwf ⊢

/-- **One part of a symbol side: its codes are faithful**, blob or interned, under its `Enc.WF` alone. -/
theorem codes_symbol_faithful (x : Part (.atom .symbol)) {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom .symbol) #v[x])[0].b (Obj.codes (.atom .symbol) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  rcases symbol_enc x.2.wf with ⟨b, o, he⟩ | ⟨d, o, ids, he⟩
  · exact codes_symbol_syms_faithful x he hi hj
  · exact codes_symbol_enum_faithful x he hi hj

/-- **One part of a symbol side: its code is well formed**, blob or interned, under its `Enc.WF` alone. -/
theorem codes_symbol_wf (x : Part (.atom .symbol)) :
    let c := (Obj.codes (.atom .symbol) #v[x])[0]
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  rcases symbol_enc x.2.wf with ⟨b, o, he⟩ | ⟨d, o, ids, he⟩
  · exact codes_symbol_syms_wf x he
  · exact codes_symbol_enum_wf x he

#print axioms codes_symbol_enum_faithful
#print axioms codes_symbol_enum_wf
#print axioms codes_symbol_syms_faithful
#print axioms codes_symbol_syms_wf
#print axioms codes_symbol_faithful
#print axioms codes_symbol_wf

end LeetQ.Rel.Alg
