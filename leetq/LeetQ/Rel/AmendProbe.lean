import LeetQ.Rel.SpecStruct

namespace LeetQ.Rel.Verb
open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A fixed-width array's dense payload: `w` bytes an element, never a bitmap. -/
theorem bytesOf_fixed {t : QAtomicType} {w m : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) (z : Arr t m) (hm : m < USize.size) :
    ∃ D, Column.bytesOf z.c = some D ∧ D.size = w * m ∧ ∀ b, z.c.enc ≠ .bits b := by
  have hw8 : 1 < w ∧ w ≤ 8 := he.elim (width_fixed hw) (fun ha => by have := alp_width hw ha; omega)
  have parts : (∃ B, z.c.enc = .bytes B ∧ B.size = w * m) ∨ (∃ md pk, z.c.enc = .foR md pk) ∨
      ∃ md pk a, z.c.enc = .alp md pk a :=
    he.elim (fun he => (fixed_parts hw he z).elim .inl (.inr ∘ .inl)) (alp_parts hw · z)
  rcases parts with ⟨B, hc, hB⟩ | ⟨md, pk, hc⟩ | ⟨md, pk, a, hc⟩
  · exact ⟨B, by rw [Arr.c_eq z hc]; rfl, hB, fun b e => by rw [hc] at e; cases e⟩
  · exact ⟨Kernel.Coc.decode w.toUSize md pk m.toUSize, by rw [Arr.c_eq z hc]; simp [Column.bytesOf, hw],
      (decode_words ⟨by omega, hw8.2⟩ md pk hm).1, fun b e => by rw [hc] at e; cases e⟩
  · exact ⟨Kernel.Coc.alpDecode w.toUSize md pk a m.toUSize, by rw [Arr.c_eq z hc]; simp [Column.bytesOf, hw],
      (alpDecode_words ⟨by omega, hw8.2⟩ md pk a hm).1, fun b e => by rw [hc] at e; cases e⟩

/-- What `scatter` writes from and into: the dense payload at `8 w` bits an element. -/
theorem packed_fixed {t : QAtomicType} {w : Nat} (hw : t.width = some w) (verb : String) (c : Column)
    {D : ByteArray} (hD : Column.bytesOf c = some D) (hb : ∀ b, c.enc ≠ .bits b) :
    Struct.packed verb t c = pure (D, 8 * w) := by
  unfold Struct.packed; split
  · next b e => exact absurd e (hb b)
  · simp [hw, Find.dense, hD] <;> rfl

/-- A dense payload of `n` elements of a fixed-width type is a well-formed column. -/
theorem wf_bytes {t : QAtomicType} {w n : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) (B : ByteArray) (h : B.size = n * w) :
    Column.WF ⟨t, n, .bytes B, none⟩ := by
  cases t <;> simp_all [Column.WF, QAtomicType.width, Column.encodes, Column.alpEncodes]

/-- Of positions whose index names are distinct, at most one names `j`. -/
theorem filter_le_one (p : Nat → Nat) (m j : Nat) (hinj : ∀ k < m, ∀ k' < m, p k = p k' → k = k') :
    (List.range m).filter (fun k => p k = j) = [] ∨
      ∃ k < m, p k = j ∧ (List.range m).filter (fun k => p k = j) = [k] := by
  have hmem : ∀ k ∈ (List.range m).filter (fun k => p k = j), k < m ∧ p k = j := fun k hk => by
    rw [List.mem_filter, List.mem_range] at hk; exact ⟨hk.1, of_decide_eq_true hk.2⟩
  have hpw := (List.pairwise_lt_range (n := m)).filter (fun k => decide (p k = j))
  generalize (List.range m).filter (fun k => p k = j) = l at hmem hpw ⊢
  match l, hmem, hpw with
  | [], _, _ => exact .inl rfl
  | [k], hm, _ => exact .inr ⟨k, (hm k List.mem_cons_self).1, (hm k List.mem_cons_self).2, rfl⟩
  | a :: b :: _, hm, hp =>
    have ha := hm a List.mem_cons_self
    have hb := hm b (List.mem_cons_of_mem _ List.mem_cons_self)
    have hab := List.rel_of_pairwise_cons hp List.mem_cons_self
    exact absurd (hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm)) (Nat.ne_of_lt hab)

/-- `z` read at the long positions `ix` (`gatherColumn`, through `vec`): the dense gather of its payload. -/
theorem vec_gather {t : QAtomicType} {w m : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) (verb : String) (z : Arr t m)
    (hA : ∀ M P a, z.c.enc = .alp M P a → Column.alpF32 a = (w == 4)) (ix : ByteArray) {c : Column}
    (hc : Find.vec verb t (Kernel.gatherColumn t z.c (LeetQ.Rel.Alg.longs ix)) = .ok c) :
    ∃ src, Column.bytesOf z.c = some src ∧
      c = ⟨t, ix.size / 8, .bytes (Kernel.gatherBytes w.toUSize ((Kernel.nullBits t).getD 0) src ix), none⟩ := by
  have hdw : Kernel.denseWidth t = some w := by
    cases t <;> first | exact hw | simp [Column.encodes, Column.alpEncodes] at he
  have hg : Kernel.gatherColumn t z.c (LeetQ.Rel.Alg.longs ix) = some (.vector c) := by
    unfold Find.vec at hc
    split at hc
    · next c' e => split at hc <;> cases hc; exact e
    all_goals cases hc
  obtain ⟨src, ixb, hsrc, hixb, rfl⟩ :=
    Verify.gatherColumn_fixed_shape hdw z.c (LeetQ.Rel.Alg.longs ix) c z.wf.1 rfl
      (by simp [Verify.countFits, LeetQ.Rel.Alg.longs]) hA hg
  have e : ix = ixb := Option.some.inj
    ((show Column.bytesOf (LeetQ.Rel.Alg.longs ix) = some ix by simp [LeetQ.Rel.Alg.longs, Column.bytesOf]).symm.trans hixb)
  subst e
  exact ⟨src, hsrc, rfl⟩

/-- Positions listed in order, filtered and read through the list: the list filtered, then read. -/
theorem filter_reindex {β : Type} (P : List Nat) (g : Nat → Nat) (h : Nat → β) (j : Nat) :
    ((List.range P.length).filter (fun p => g P[p]! = j)).map (fun p => h P[p]!) = (P.filter (g · = j)).map h := by
  have e : (List.range P.length).map (P[·]!) = P :=
    List.ext_getElem (by simp) fun i h1 h2 => by simp [List.getElem?_eq_getElem h2]
  conv => rhs; rw [← e]
  rw [List.filter_map, List.map_map]; rfl

/-- Of the positions naming one index, a later one has a higher rank (`amendRank_lt`). -/
theorem rank_pairwise (ib : ByteArray) (N j : Nat) :
    ((List.range N).filter fun k => (Column.bitsAt ib (k * 8) 8).toNat = j).Pairwise
      (fun a b => Verify.amendRank ib a < Verify.amendRank ib b) :=
  ((List.pairwise_lt_range (n := N)).filter _).imp_of_mem fun ha hb hab => by
    rw [List.mem_filter] at ha hb
    exact Verify.amendRank_lt ib _ _ hab
      (UInt64.toNat_inj.1 ((of_decide_eq_true ha.2).trans (of_decide_eq_true hb.2).symm))

/-- **One round of `@[x;i;f;y]` at a verb**: `acc` read at the round's positions, `f` with the round's values
    (`Ew.dyad`), written back (`scatter`). Its positions name distinct indices, so each position of the answer
    is `f` of its old element and the value naming it, its old element where none does. -/
theorem amend_round {t : QAtomicType} {w nx : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) {v : Prim.Dyadic}
    {f : Carrier t → Carrier t → Carrier t}
    (hdy : ∀ {m} (cur yv R : Arr t m), (∃ B, cur.c.enc = .bytes B) → m < 2 ^ 32 →
      Ew.dyad v Kernel.Ew.vv t t t cur.c yv.c m = .ok R → R.toList = List.zipWith f cur.toList yv.toList)
    (dec : UInt64 → Carrier t)
    (htl : ∀ {m} (z : Arr t m) {D}, Column.bytesOf z.c = some D → m < USize.size → z.toList = (Verify.elemsW w D).map dec)
    (hnx : nx < 2 ^ 32) (verb : String) (acc : Arr t nx)
    (hA : ∀ M P a, acc.c.enc = .alp M P a → Column.alpF32 a = (w == 4))
    (ix : ByteArray) (hm : ix.size / 8 < 2 ^ 32)
    (hinj : ∀ k < ix.size / 8, ∀ k' < ix.size / 8,
      (Column.bitsAt ix (k * 8) 8).toNat = (Column.bitsAt ix (k' * 8) 8).toNat → k = k')
    {m : Nat} (yv : Arr t m) (hmx : ix.size / 8 = m) {c : Column} {R : Arr t (ix.size / 8)} {out : Column}
    (hc : Find.vec verb t (Kernel.gatherColumn t acc.c (LeetQ.Rel.Alg.longs ix)) = .ok c)
    (hR : Ew.dyad v Kernel.Ew.vv t t t c yv.c (ix.size / 8) = .ok R)
    (hs : Struct.scatter verb t nx acc.c R.c ix = .ok out) :
    ∃ acc' : Arr t nx, acc'.c = out ∧ (∃ B, out.enc = .bytes B) ∧ ∀ j, acc'.toList[j]? =
      acc.toList[j]?.map fun a => (((List.range (ix.size / 8)).filter fun k =>
        (Column.bitsAt ix (k * 8) 8).toNat = j).map (yv.toList[·]!)).foldl f a := by
  have hw8 : 1 < w ∧ w ≤ 8 := he.elim (width_fixed hw) (fun ha => by have := alp_width hw ha; omega)
  have hU : nx < USize.size := Nat.lt_of_lt_of_le hnx USize.le_size
  have hmU : ix.size / 8 < USize.size := Nat.lt_of_lt_of_le hm USize.le_size
  subst hmx
  obtain ⟨src, hsrc, hss, hsb⟩ := bytesOf_fixed hw he acc hU
  obtain ⟨src', hsrc', rfl⟩ := vec_gather hw he verb acc hA ix hc
  have e : src = src' := Option.some.inj (hsrc.symm.trans hsrc'); subst e
  have hw' : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have gs := Verify.gatherBytes_spec w.toUSize (by rw [hw']; exact hw8.2) ((Kernel.nullBits t).getD 0) src ix
  rw [hw'] at gs
  let cur : Arr t (ix.size / 8) :=
    ⟨⟨t, ix.size / 8, .bytes (Kernel.gatherBytes w.toUSize ((Kernel.nullBits t).getD 0) src ix), none⟩,
      rfl, rfl, wf_bytes hw he _ (by rw [gs.1, Nat.mul_comm])⟩
  have hRl := hdy cur yv R ⟨_, rfl⟩ hm hR
  obtain ⟨E, hE, hEs, hEb⟩ := bytesOf_fixed hw he R hmU
  have hts : t ≠ .symbol := by rintro rfl; simp [Column.encodes, Column.alpEncodes] at he
  have hout : out = ⟨t, nx, .bytes (Kernel.scatterPacked (8 * w).toUSize src ix E 0 false), none⟩ := by
    unfold Struct.scatter at hs; split at hs
    · exact absurd rfl hts
    · rw [packed_fixed hw verb acc.c hsrc hsb, packed_fixed hw verb R.c hE hEb] at hs
      simp [show 8 * w ≠ 1 by omega] at hs
      cases hs; simp
  have hwb : (8 * w).toUSize.toNat = 8 * w := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have spec := Verify.scatterPacked_spec w (by omega) (8 * w).toUSize hwb src ix E 0 false
    (by simp only [Bool.false_eq_true, if_false, USize.toNat_zero, Nat.zero_add]
        exact Nat.le_of_eq (by rw [hEs, Nat.mul_comm]))
  subst hout
  refine ⟨⟨_, rfl, rfl, wf_bytes hw he _ (by rw [spec.1, hss, Nat.mul_comm])⟩, rfl, ⟨_, rfl⟩, fun j => ?_⟩
  have hxk : src.size / w = nx := by rw [hss, Nat.mul_div_cancel_left _ (by omega)]
  rw [htl _ (D := Kernel.scatterPacked (8 * w).toUSize src ix E 0 false) rfl hU, htl acc hsrc hU]
  by_cases hj : j < nx
  · rw [List.getElem?_map, List.getElem?_map, Verify.elemsW, Verify.elemsW, List.getElem?_map, List.getElem?_map,
      List.getElem?_range (by rw [spec.1, hxk]; exact hj), List.getElem?_range (by rw [hxk]; exact hj)]
    simp only [Option.map_some, Option.some.injEq]
    rw [spec.2 j (by rw [hxk]; exact hj)]
    have hFL : ((List.range (ix.size / 8)).filter fun k => (Column.bitsAt ix (k * 8) 8).toNat == j) =
        (List.range (ix.size / 8)).filter fun k => (Column.bitsAt ix (k * 8) 8).toNat = j :=
      List.filter_congr fun k _ => Bool.eq_iff_iff.2 (by simp)
    rw [hFL]
    rcases filter_le_one (fun k => (Column.bitsAt ix (k * 8) 8).toNat) (ix.size / 8) j hinj with h | ⟨k, hk, hpk, h⟩
    · rw [h]; rfl
    · rw [h]
      have hRk : R.toList[k]? = some (dec (Column.bitsAt E (k * w) w)) := by
        rw [htl R hE hmU, List.getElem?_map, Verify.elemsW, List.getElem?_map,
          List.getElem?_range (by rw [hEs, Nat.mul_div_cancel_left _ (by omega)]; exact hk)]
        rfl
      have hck : cur.toList[k]? = some (dec (Column.bitsAt src (j * w) w)) := by
        rw [htl cur (D := Kernel.gatherBytes w.toUSize ((Kernel.nullBits t).getD 0) src ix) rfl hmU,
          List.getElem?_map, Verify.elemsW, List.getElem?_map,
          List.getElem?_range (by rw [gs.1, Nat.mul_div_cancel_left _ (by omega)]; exact hk)]
        simp only [Option.map_some, Option.some.injEq]
        rw [gs.2 k hk, if_pos (by rw [hxk]; exact hpk ▸ hj)]
        rw [hpk]
      have hyk : yv.toList[k]? = some yv.toList[k]! := by
        rw [getElem!_pos yv.toList k (by rw [Arr.length_toList]; exact hk)]; exact List.getElem?_eq_getElem _
      rw [hRl] at hRk
      rw [List.getElem?_zipWith, hck, hyk] at hRk; have hz : f _ _ = _ := Option.some.inj hRk
      simp only [List.getLast?_singleton, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        USize.toNat_zero, Nat.zero_add, Bool.false_eq_true, ↓reduceIte]
      exact hz.symm
  · rw [List.getElem?_eq_none (by rw [List.length_map, Verify.elemsW, List.length_map, List.length_range, spec.1, hxk]; omega),
      List.getElem?_eq_none (by rw [List.length_map, Verify.elemsW, List.length_map, List.length_range, hxk]; omega)]
    rfl

/-- `Nat.foldM` in `Except`: a property every step carries from `i` to `i + 1` holds of the answer at `n`. -/
theorem foldM_inv {α ε : Type} (n : Nat) (f : (i : Nat) → i < n → α → Except ε α) (P : Nat → α → Prop)
    (init : α) (h0 : P 0 init) (hs : ∀ i (hi : i < n) a b, P i a → f i hi a = .ok b → P (i + 1) b) {r : α}
    (h : Nat.foldM n f init = .ok r) : P n r := by
  -- `Nat.foldM`'s `loop` is hygienic: argue for any `L` with its two equations, which hold by `rfl`
  have key : ∀ (L : (i : Nat) → i ≤ n → α → Except ε α), (∀ h a, L 0 h a = pure a) →
      (∀ i (h : i + 1 ≤ n) a, L (i + 1) h a = f (n - i - 1) (by omega) a >>= L i (Nat.le_of_succ_le h)) →
      ∀ i (hi : i ≤ n) a, P (n - i) a → L i hi a = .ok r → P n r := by
    intro L hL0 hLs i
    induction i with
    | zero => intro hi a ha e; rw [hL0] at e; cases e; simpa using ha
    | succ i ih =>
      intro hi a ha e
      rw [hLs] at e
      cases hf : f (n - i - 1) (by omega) a with
      | error _ => rw [hf] at e; cases e
      | ok b =>
        rw [hf] at e
        refine ih _ b ?_ e
        have := hs _ (by omega) a b (by rw [show n - i - 1 = n - (i + 1) by omega]; exact ha) hf
        rwa [show n - i - 1 + 1 = n - i by omega] at this
  unfold Nat.foldM at h
  refine key _ ?_ ?_ n _ init (by rw [Nat.sub_self]; exact h0) h
  · intro _ _; rfl
  · intro _ _ _; rfl

/-- Along a list on which `g` strictly rises, the elements below `r + 1` are those below `r`, then the one at `r`. -/
theorem filter_lt_succ (g : Nat → Nat) (r : Nat) : ∀ {l : List Nat}, l.Pairwise (fun a b => g a < g b) →
    l.filter (fun a => g a < r + 1) = l.filter (fun a => g a < r) ++ l.filter (fun a => g a = r)
  | [], _ => rfl
  | a :: l, hp => by
    rw [List.pairwise_cons] at hp
    have ih := filter_lt_succ g r hp.2
    by_cases h1 : g a < r
    · rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_pos (by simpa using h1),
        List.filter_cons_of_neg (by simp; omega), ih]; rfl
    · by_cases h2 : g a = r
      · have hn : ∀ b ∈ l, r < g b := fun b hb => h2 ▸ hp.1 b hb
        rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_neg (by simpa using h1),
          List.filter_cons_of_pos (by simpa using h2),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega)]
        rfl
      · have hn : ∀ b ∈ l, r < g b := fun b hb => by have := hp.1 b hb; omega
        rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simpa using h1),
          List.filter_cons_of_neg (by simpa using h2),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega),
          List.filter_eq_nil_iff.2 (fun b hb => by have := hn b hb; simp; omega)]
        rfl

end LeetQ.Rel.Verb
