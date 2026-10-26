import LeetQ.Rel.SpecStruct

namespace LeetQ.Rel.Verb
open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet

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
    ∃ acc' : Arr t nx, acc'.c = out ∧ (∃ B, out = ⟨t, nx, .bytes B, none⟩) ∧ ∀ j, acc'.toList[j]? =
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

/-- **Round `rr`'s positions**, as `Struct.amend` cuts them out of `amendRounds`' grouped words between the
    counts `lo` and `hi` of ranks below `rr` and below `rr + 1`: the positions of rank `rr`, ascending. -/
theorem round_positions (n : USize) (ib : ByteArray)
    (hn : ¬ ∃ k < ib.size / 8, n.toUInt64 ≤ Column.bitsAt ib (k * 8) 8)
    (h1 : 1 < Verify.amendRoundCount true ib) {rr : Nat} (hrr : rr < Verify.amendRoundCount true ib) {lo hi : Nat}
    (hlo : lo = (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k < rr)))
    (hhi : hi = (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k < rr + 1))) :
    Verify.elemsW 8 ((Kernel.amendRounds n 8 true ib).extract ((2 + Verify.amendRoundCount true ib + lo) * 8)
      ((2 + Verify.amendRoundCount true ib + hi) * 8)) =
      ((List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = rr).map Nat.toUInt64 := by
  -- block `q`: the positions of rank `q`; `c q` its size
  have hl : ∀ q, ((List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = q).length =
      (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k = q)) :=
    fun q => (List.countP_eq_length_filter ..).symm
  have hf : List.find? (fun x => decide (n.toUInt64 ≤ x))
      ((List.range (ib.size / 8)).map fun k => Column.bitsAt ib (k * 8) 8) = none :=
    List.find?_eq_none.2 fun x hx hd => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact hn ⟨k, List.mem_range.1 hk, of_decide_eq_true hd⟩
  generalize hGd : ((List.range (Verify.amendRoundCount true ib)).flatMap fun q =>
    (List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = q) = G
  generalize hCn : (List.range (Verify.amendRoundCount true ib)).map (fun r =>
    (((List.range (ib.size / 8)).map (Verify.amendRank ib)).filter (· ≤ r)).length.toUInt64) = Cn
  have hr : Kernel.amendRounds n 8 true ib =
      ((Verify.amendRoundCount true ib).toUInt64 :: 0 :: (Cn ++ G.map fun k : Nat => k.toUInt64)).foldl
        (fun b v => Column.pushBits b v 8) .empty := by
    (rw [Verify.amendRounds_eq, hf]; dsimp only; rw [if_neg (Nat.not_le.2 h1), hCn, ← hGd]) <;> rfl
  generalize hL : (Verify.amendRoundCount true ib).toUInt64 :: 0 :: (Cn ++ G.map fun k : Nat => k.toUInt64) = L at hr
  obtain ⟨hsz, -, -⟩ := Verify.foldl_pushBits (fun v : UInt64 => v) 8 (Nat.le_refl 8) L ByteArray.empty
  have hW : Verify.elemsW 8 (Kernel.amendRounds n 8 true ib) = L := by
    rw [hr]
    apply List.ext_getElem (by simp only [Verify.elemsW, List.length_map, List.length_range, hsz]; simp)
    intro j _ h2
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [Verify.words_get L (j * 8) j rfl h2, List.getElem?_eq_getElem h2]; rfl
  have hlo' : lo = ((List.range rr).map fun q =>
      (List.range (ib.size / 8)).countP fun k => decide (Verify.amendRank ib k = q)).sum :=
    hlo.trans (countP_lt_sum _ _ rr)
  have hhi' : hi = lo + (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k = rr)) := by
    rw [hhi, countP_lt_sum _ _ (rr + 1), sum_range_succ, hlo']
  have hGl : G.length = ((List.range (Verify.amendRoundCount true ib)).map fun q =>
      (List.range (ib.size / 8)).countP fun k => decide (Verify.amendRank ib k = q)).sum := by
    rw [← hGd, List.length_flatMap]; congr 1; exact List.map_congr_left fun q _ => hl q
  have hle : hi ≤ G.length := by
    rw [hhi', hGl, hlo', ← sum_range_succ]; exact sum_range_mono _ hrr
  have hCl : Cn.length = Verify.amendRoundCount true ib := by rw [← hCn, List.length_map, List.length_range]
  have hLl : L.length = 2 + Verify.amendRoundCount true ib + G.length := by
    rw [← hL]; simp only [List.length_cons, List.length_append, List.length_map, hCl]; omega
  have hsz8 : (Kernel.amendRounds n 8 true ib).size / 8 = L.length := by
    have := congrArg List.length hW; simpa [Verify.elemsW] using this
  rw [Struct.elemsW_extract 8 (by decide) _ (by rw [hsz8, hLl]; omega), hW, ← hL,
    show 2 + Verify.amendRoundCount true ib + lo = (Cn.length + lo) + 1 + 1 by omega, List.drop_succ_cons,
    List.drop_succ_cons, List.drop_append, List.drop_eq_nil_of_le (by omega : Cn.length ≤ Cn.length + lo),
    List.nil_append, Nat.add_sub_cancel_left, ← List.map_drop, ← List.map_take,
    show 2 + Verify.amendRoundCount true ib + hi - (Cn.length + lo + 1 + 1) =
      (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k = rr)) by omega,
    take_drop_eq G lo _ (by omega)]
  congr 1
  apply List.ext_getElem (by rw [List.length_map, List.length_range, hl])
  intro q h1q h2q
  rw [List.getElem_map, List.getElem_range]
  have hq : q < (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k = rr)) := by
    rw [← hl]; exact h2q
  have hb := blocks_get (fun q => (List.range (ib.size / 8)).countP fun k => decide (Verify.amendRank ib k = q))
    (fun q => (List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = q) hl _ hrr hq
  rw [hGd, ← hlo'] at hb
  rw [getElem!_pos G _ (by omega)]
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (hb.trans (List.getElem?_eq_getElem h2q)))

/-- Positions read off per index: a list whose position `j` folds `f` over the values naming `j`, from `xs`'s
    element, is `amendSpec` (`foldl_set_getElem?`). -/
theorem amendSpec_of_positions {α : Type} [Inhabited α] (f : α → α → α) (xs ys : List α) (is : List Int64)
    (hl : is.length = ys.length) (hin : ∀ i ∈ is, i.toInt.toNat < xs.length) (L : List α)
    (hL : ∀ j, L[j]? = xs[j]?.map fun a =>
      (((List.range is.length).filter fun k => is[k]!.toInt.toNat = j).map (ys[·]!)).foldl f a) :
    L = Struct.amendSpec f xs is ys := by
  have hz : is.zip ys = (List.range is.length).map fun k => (is[k]!, ys[k]!) := by
    apply List.ext_getElem (by simp [hl])
    intro k h1 h2
    have hk : k < is.length := by simpa using h2
    rw [List.getElem_zip, List.getElem_map, List.getElem_range, getElem!_pos is k hk, getElem!_pos ys k (hl ▸ hk)]
  apply List.ext_getElem?; intro j
  unfold Struct.amendSpec
  rw [foldl_set_getElem? f j _ xs (fun p hp => hin p.1 (List.of_mem_zip hp).1), hL, hz, List.filter_map,
    List.map_map]
  rfl

/-- A left fold of `max` stays below any bound on its start and its elements. -/
theorem foldl_max_le (l : List Nat) (a c : Nat) (ha : a ≤ c) (h : ∀ y ∈ l, y ≤ c) : l.foldl max a ≤ c := by
  induction l generalizing a with
  | nil => exact ha
  | cons e l ih =>
    exact ih _ (Nat.max_le.2 ⟨ha, h e List.mem_cons_self⟩) fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **Round `rr` of `@[x;i;v;y]`**: the positions `KS` of rank `rr` (`round_positions`), their indices gathered
    out of `ib` and their values out of `y`, one `amend_round`. Before it each position folds `f` over the values
    of rank below `rr` naming it; after it, below `rr + 1`. -/
theorem amend_round_ranked {t : QAtomicType} {w nx : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) {v : Prim.Dyadic}
    {f : Carrier t → Carrier t → Carrier t}
    (hdy : ∀ {m} (cur yv R : Arr t m), (∃ B, cur.c.enc = .bytes B) → m < 2 ^ 32 →
      Ew.dyad v Kernel.Ew.vv t t t cur.c yv.c m = .ok R → R.toList = List.zipWith f cur.toList yv.toList)
    (dec : UInt64 → Carrier t)
    (htl : ∀ {m} (z : Arr t m) {D}, Column.bytesOf z.c = some D → m < USize.size → z.toList = (Verify.elemsW w D).map dec)
    (hnx : nx < 2 ^ 32) (verb : String) (ib : ByteArray) (hN : ib.size / 8 < 2 ^ 32) (rr : Nat)
    (y : Arr t (ib.size / 8)) (hyA : ∀ M P a, y.c.enc = .alp M P a → Column.alpF32 a = (w == 4))
    (x a : Arr t nx) (hA : ∀ M P al, a.c.enc = .alp M P al → Column.alpF32 al = (w == 4))
    (hpos : ∀ j, a.toList[j]? = x.toList[j]?.map fun a0 => ((((List.range (ib.size / 8)).filter fun k =>
      (Column.bitsAt ib (k * 8) 8).toNat = j).filter fun k => Verify.amendRank ib k < rr).map (y.toList[·]!)).foldl f a0)
    (KS : ByteArray)
    (hKS : Verify.elemsW 8 KS = ((List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = rr).map Nat.toUInt64)
    {yc cur : Column} {Rd : Arr t ((Kernel.gatherBytes 8 0 ib KS).size / 8)} {out : Column}
    (hyc : Find.vec verb t (Kernel.gatherColumn t y.c (LeetQ.Rel.Alg.longs KS)) = .ok yc)
    (hcur : Find.vec verb t (Kernel.gatherColumn t a.c (LeetQ.Rel.Alg.longs (Kernel.gatherBytes 8 0 ib KS))) = .ok cur)
    (hRd : Ew.dyad v Kernel.Ew.vv t t t cur yc ((Kernel.gatherBytes 8 0 ib KS).size / 8) = .ok Rd)
    (hsc : Struct.scatter verb t nx a.c Rd.c (Kernel.gatherBytes 8 0 ib KS) = .ok out) :
    ∃ a' : Arr t nx, a'.c = out ∧ (∃ B, out = ⟨t, nx, .bytes B, none⟩) ∧ ∀ j, a'.toList[j]? =
      x.toList[j]?.map fun a0 => ((((List.range (ib.size / 8)).filter fun k =>
        (Column.bitsAt ib (k * 8) 8).toNat = j).filter fun k => Verify.amendRank ib k < rr + 1).map
          (y.toList[·]!)).foldl f a0 := by
  have hw8 : 1 < w ∧ w ≤ 8 := he.elim (width_fixed hw) (fun ha => by have := alp_width hw ha; omega)
  have hUi : ib.size / 8 < USize.size := Nat.lt_of_lt_of_le hN USize.le_size
  obtain ⟨P, hP⟩ : ∃ P, P = (List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = rr := ⟨_, rfl⟩
  rw [← hP] at hKS
  have hPN : P.length ≤ ib.size / 8 := by rw [hP]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hPlt : ∀ k < P.length, P[k]! < ib.size / 8 ∧ Verify.amendRank ib P[k]! = rr := fun k hk => by
    have hm : P[k] ∈ (List.range (ib.size / 8)).filter fun k => Verify.amendRank ib k = rr := by
      rw [← hP]; exact List.getElem_mem hk
    rw [List.mem_filter, List.mem_range] at hm
    rw [getElem!_pos P k hk]
    exact ⟨hm.1, of_decide_eq_true hm.2⟩
  have hPs : P.Pairwise (· < ·) := hP ▸ List.pairwise_lt_range.filter _
  have hKl : KS.size / 8 = P.length := by
    have := congrArg List.length hKS; simpa [Verify.elemsW] using this
  have hKw : ∀ k < P.length, (Column.bitsAt KS (k * 8) 8).toNat = P[k]! := fun k hk => by
    have e : (Verify.elemsW 8 KS)[k]? = some (Column.bitsAt KS (k * 8) 8) := by simp [Verify.elemsW, hKl, hk]
    rw [hKS, List.getElem?_map, List.getElem?_eq_getElem hk] at e
    have e2 := Option.some.inj e
    have hb := (hPlt k hk).1
    rw [getElem!_pos P k hk] at hb ⊢
    rw [← e2]; simp; omega
  have e8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have gs := Verify.gatherBytes_spec 8 (Nat.le_of_eq e8) 0 ib KS
  rw [e8] at gs
  have hixs : (Kernel.gatherBytes 8 0 ib KS).size / 8 = P.length := by rw [gs.1, hKl]; omega
  have hixw : ∀ k < P.length, (Column.bitsAt (Kernel.gatherBytes 8 0 ib KS) (k * 8) 8).toNat =
      (Column.bitsAt ib (P[k]! * 8) 8).toNat := fun k hk => by
    rw [gs.2 k (by rw [hKl]; exact hk), hKw k hk, if_pos (hPlt k hk).1]
  -- `y` at the round's positions
  obtain ⟨ysrc, hysrc, rfl⟩ := vec_gather hw he verb y hyA KS hyc
  obtain ⟨yb, hyb, hys, -⟩ := bytesOf_fixed hw he y hUi
  have e : ysrc = yb := Option.some.inj (hysrc.symm.trans hyb); subst e
  have hw' : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have gw := Verify.gatherBytes_spec w.toUSize (by rw [hw']; exact hw8.2) ((Kernel.nullBits t).getD 0) ysrc KS
  rw [hw'] at gw
  let yA : Arr t (KS.size / 8) :=
    ⟨⟨t, KS.size / 8, .bytes (Kernel.gatherBytes w.toUSize ((Kernel.nullBits t).getD 0) ysrc KS), none⟩,
      rfl, rfl, wf_bytes hw he _ (by rw [gw.1, Nat.mul_comm])⟩
  have hKU : KS.size / 8 < USize.size := by rw [hKl]; omega
  have hyx : ysrc.size / w = ib.size / 8 := by rw [hys, Nat.mul_div_cancel_left _ (by omega)]
  have hyel : ∀ k < P.length, yA.toList[k]! = y.toList[P[k]!]! := fun k hk => by
    have hb := (hPlt k hk).1
    rw [htl yA (D := Kernel.gatherBytes w.toUSize ((Kernel.nullBits t).getD 0) ysrc KS) rfl hKU, htl y hysrc hUi,
      getElem!_pos _ k (by simp [Verify.elemsW, gw.1, Nat.mul_div_cancel_left _ (show 0 < w by omega), hKl, hk]),
      getElem!_pos _ P[k]! (by simp only [Verify.elemsW, List.length_map, List.length_range, hyx]; exact hb)]
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [gw.2 k (by rw [hKl]; exact hk), hKw k hk, if_pos (by rw [hyx]; exact hb)]
  -- the round's indices name distinct positions: equal indices have distinct ranks
  have hinj : ∀ k < (Kernel.gatherBytes 8 0 ib KS).size / 8, ∀ k' < (Kernel.gatherBytes 8 0 ib KS).size / 8,
      (Column.bitsAt (Kernel.gatherBytes 8 0 ib KS) (k * 8) 8).toNat =
        (Column.bitsAt (Kernel.gatherBytes 8 0 ib KS) (k' * 8) 8).toNat → k = k' := by
    intro k hk k' hk' e
    rw [hixs] at hk hk'
    rw [hixw k hk, hixw k' hk'] at e
    have one : ∀ k k', k < P.length → k' < P.length → k < k' →
        (Column.bitsAt ib (P[k]! * 8) 8).toNat = (Column.bitsAt ib (P[k']! * 8) 8).toNat → False :=
      fun k k' hk hk' hl e => by
        have hs := List.pairwise_iff_getElem.1 hPs k k' hk hk' hl
        rw [← getElem!_pos P k hk, ← getElem!_pos P k' hk'] at hs
        have := Verify.amendRank_lt ib _ _ hs (UInt64.toNat_inj.1 e)
        rw [(hPlt k hk).2, (hPlt k' hk').2] at this
        exact Nat.lt_irrefl _ this
    rcases Nat.lt_trichotomy k k' with hl | hl | hl
    · exact (one k k' hk hk' hl e).elim
    · exact hl
    · exact (one k' k hk' hk hl e.symm).elim
  obtain ⟨a', ha', hBo, hp⟩ := amend_round hw he hdy dec htl hnx verb a hA (Kernel.gatherBytes 8 0 ib KS)
    (by rw [hixs]; omega) hinj yA (by rw [hixs, hKl]) hcur hRd hsc
  refine ⟨a', ha', hBo, fun j => ?_⟩
  rw [hp j, hpos j, Option.map_map]
  congr 1; funext a0
  simp only [Function.comp]
  have e1 : (List.range ((Kernel.gatherBytes 8 0 ib KS).size / 8)).filter (fun k =>
      decide ((Column.bitsAt (Kernel.gatherBytes 8 0 ib KS) (k * 8) 8).toNat = j)) =
      (List.range P.length).filter (fun k => decide ((Column.bitsAt ib (P[k]! * 8) 8).toNat = j)) := by
    rw [hixs]; exact List.filter_congr fun k hk => by rw [hixw k (List.mem_range.1 hk)]
  have e2 : ((List.range P.length).filter (fun k => decide ((Column.bitsAt ib (P[k]! * 8) 8).toNat = j))).map
      (yA.toList[·]!) = ((List.range P.length).filter (fun k =>
        decide ((Column.bitsAt ib (P[k]! * 8) 8).toNat = j))).map (fun k => y.toList[P[k]!]!) :=
    List.map_congr_left fun k hk => hyel k (List.mem_range.1 (List.mem_filter.1 hk).1)
  have e3 : P.filter (fun k => decide ((Column.bitsAt ib (k * 8) 8).toNat = j)) =
      ((List.range (ib.size / 8)).filter fun k => (Column.bitsAt ib (k * 8) 8).toNat = j).filter
        fun k => Verify.amendRank ib k = rr := by
    rw [hP, List.filter_filter, List.filter_filter]
    exact List.filter_congr fun k _ => Bool.and_comm _ _
  rw [e1, e2, filter_reindex P (fun k => (Column.bitsAt ib (k * 8) 8).toNat) (y.toList[·]!) j, e3,
    filter_lt_succ (Verify.amendRank ib) rr (rank_pairwise ib _ j), List.map_append, List.foldl_append]

/-- **`@[x;i;v;y]`, the kernel at a verb `v`, is `amendSpec f`**, `f` the verb's element law (`hdy`), at every
    type with a fixed-width encoding, any indices, repeats included: the kernel answers only when every index is
    in `0..nx` and as many as the values, and then folds `f` at each position over the values naming it, in order. -/
theorem amend_verb_toList {t : QAtomicType} {w nx ni ny : Nat} (hw : t.width = some w)
    (he : Column.encodes t = true ∨ Column.alpEncodes t = true) {v : Prim.Dyadic}
    {f : Carrier t → Carrier t → Carrier t}
    (hdy : ∀ {m} (cur yv R : Arr t m), (∃ B, cur.c.enc = .bytes B) → m < 2 ^ 32 →
      Ew.dyad v Kernel.Ew.vv t t t cur.c yv.c m = .ok R → R.toList = List.zipWith f cur.toList yv.toList)
    {x : Arr t nx} {i : Arr .long ni} {y : Arr t ny} {R : Arr t nx}
    (hxA : ∀ M P a, x.c.enc = .alp M P a → Column.alpF32 a = (w == 4))
    (hyA : ∀ M P a, y.c.enc = .alp M P a → Column.alpF32 a = (w == 4))
    (hnx : nx < 2 ^ 32) (hni : ni < 2 ^ 32) (h : Struct.amend x i (some v) y = .ok R) :
    ni = ny ∧ (∀ v ∈ i.toList, 0 ≤ v ∧ v.toInt.toNat < nx) ∧
      R.toList = Struct.amendSpec f x.toList i.toList y.toList := by
  have hU : nx < USize.size := Nat.lt_of_lt_of_le hnx USize.le_size
  have hUi : ni < USize.size := Nat.lt_of_lt_of_le hni USize.le_size
  let dec : UInt64 → Carrier t := fun u =>
    (Carrier.of? t (.atom (Column.atomOfBits t u (QAtomicType.ne_general_of_width hw)))).getD default
  have htl : ∀ {m} (z : Arr t m) {D}, Column.bytesOf z.c = some D → m < USize.size →
      z.toList = (Verify.elemsW w D).map dec := fun {_} z {_} hD hm => toList_fixed hw he z hD hm
  have hsm : ∀ n : Nat, n < 2 ^ 64 → n.toUInt64.toNat = n := fun n hn => by simp; omega
  obtain ⟨hny, ib, hd, hibn, hil, hmiss, hbit, hix, hin⟩ := amend_indices hnx hni h
  subst hny
  subst hibn
  have hw0 := Verify.amendRounds_word0 nx.toUSize true ib
  rw [if_neg hmiss] at hw0
  refine ⟨rfl, hin, ?_⟩
  -- the rounds: one per rank
  have hRN : Verify.amendRoundCount true ib ≤ ib.size / 8 := by
    unfold Verify.amendRoundCount
    by_cases hz : ib.size / 8 = 0
    · simp [hz]
    · rw [if_neg (by simpa using hz), if_pos rfl]
      have := foldl_max_le ((List.range (ib.size / 8)).map (Verify.amendRank ib)) 0 (ib.size / 8 - 1) (Nat.zero_le _)
        (fun y hy => by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
          have := List.mem_range.1 hk
          have : Verify.amendRank ib k ≤ k := by
            unfold Verify.amendRank; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
          omega)
      omega
  have hrank : ∀ k < ib.size / 8, Verify.amendRank ib k < Verify.amendRoundCount true ib := fun k hk => by
    unfold Verify.amendRoundCount
    rw [if_neg (fun h => by rw [beq_iff_eq] at h; omega), if_pos rfl]
    exact Nat.lt_succ_of_le ((Verify.le_foldl_max _ _).2 _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
  have hround : (Column.bitsAt (Kernel.amendRounds nx.toUSize 8 true ib) 0 8).toNat =
      Verify.amendRoundCount true ib := by
    have hb := hRN
    rw [hw0]; unfold Verify.amendRoundCount at hb ⊢
    by_cases hz : ib.size / 8 = 0 <;> simp [hz] at hb ⊢ <;> omega
  have hne : (Column.bitsAt (Kernel.amendRounds nx.toUSize 8 true ib) 0 8 == ~~~0) = false := by
    apply beq_false_of_ne; intro e
    have e2 := congrArg UInt64.toNat e
    rw [hround] at e2
    have : (~~~0 : UInt64).toNat = 18446744073709551615 := by decide
    omega
  simp only [Struct.amend, hd, pure_bind, Option.isSome_some, Nat.zero_mul, hne, hround, ne_eq, not_true_eq_false, if_false,
    Bool.false_eq_true, ↓reduceIte] at h
  -- `simp` cannot reach the round count under `Nat.foldM`'s dependent binder; `rw` abstracts every occurrence
  rw [show (Column.bitsAt (Kernel.amendRounds nx.toUSize 8 true ib) (0 * 8) 8).toNat =
    Verify.amendRoundCount true ib by rw [Nat.zero_mul]; exact hround] at h
  have key : ∃ out, Find.onKey nx t out.answer "@[x;i;f;y]" = .ok R ∧ ∃ acc' : Arr t nx, acc'.c = out ∧
      (∃ B, out = ⟨t, nx, .bytes B, none⟩) ∧ ∀ j, acc'.toList[j]? =
      x.toList[j]?.map fun a => (((List.range (ib.size / 8)).filter fun k =>
        (Column.bitsAt ib (k * 8) 8).toNat = j).map (y.toList[·]!)).foldl f a := by
    by_cases h1 : Verify.amendRoundCount true ib ≤ 1
    · -- one round: every rank is 0, so the indices name distinct positions
      rw [if_pos h1] at h
      obtain ⟨out, hout, hok⟩ := bind_ok h
      refine ⟨out, hok, ?_⟩
      obtain ⟨cur, hcur, h2⟩ := bind_ok hout
      obtain ⟨Rd, hRd, hsc⟩ := bind_ok h2
      refine amend_round hw he hdy dec htl hnx _ x hxA ib hni ?_ y rfl hcur hRd hsc
      intro k hk k' hk' e
      rcases Nat.lt_trichotomy k k' with hl | hl | hl
      · have := Verify.amendRank_lt ib k k' hl (UInt64.toNat_inj.1 e); have := hrank k' hk'; omega
      · exact hl
      · have := Verify.amendRank_lt ib k' k hl (UInt64.toNat_inj.1 e.symm); have := hrank k hk; omega
    · -- several rounds: round `rr` adds the values of rank `rr`
      rw [if_neg h1] at h
      obtain ⟨out, hout, hok⟩ := bind_ok h
      refine ⟨out, hok, ?_⟩
      have h1' : 1 < Verify.amendRoundCount true ib := by omega
      have grp := Verify.amendRounds_grouped nx.toUSize ib hmiss h1'
      have hcnt : ∀ r < Verify.amendRoundCount true ib,
          (Column.bitsAt (Kernel.amendRounds nx.toUSize 8 true ib) ((2 + r) * 8) 8).toNat =
            (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k < r + 1)) := fun r hr => by
        rw [grp.1 r hr, ← List.countP_eq_length_filter, List.countP_map,
          hsm _ (Nat.lt_of_le_of_lt (List.countP_le_length ..) (by simp; omega))]
        exact List.countP_congr fun k _ => by simp [Nat.lt_succ_iff]
      let P := fun (rr : Nat) (acc : Column) => ∃ a : Arr t nx, a.c = acc ∧
        ((rr = 0 ∧ acc = x.c) ∨ ∃ B, acc = ⟨t, nx, .bytes B, none⟩) ∧ ∀ j, a.toList[j]? =
          x.toList[j]?.map fun a0 => ((((List.range (ib.size / 8)).filter fun k =>
            (Column.bitsAt ib (k * 8) 8).toNat = j).filter fun k => Verify.amendRank ib k < rr).map
              (y.toList[·]!)).foldl f a0
      refine (fun fin : P (Verify.amendRoundCount true ib) out => ?_) (foldM_inv _ _ P x.c ?_ ?_ hout)
      · obtain ⟨a, hac, hform, hpos⟩ := fin
        refine ⟨a, hac, ?_, fun j => ?_⟩
        · rcases hform with ⟨e, -⟩ | hB
          · omega
          · exact hB
        · have e : ((List.range (ib.size / 8)).filter fun k => (Column.bitsAt ib (k * 8) 8).toNat = j).filter
              (fun k => Verify.amendRank ib k < Verify.amendRoundCount true ib) =
              (List.range (ib.size / 8)).filter fun k => (Column.bitsAt ib (k * 8) 8).toNat = j :=
            List.filter_eq_self.2 fun k hk => by
              simp only [decide_eq_true_eq]; exact hrank k (List.mem_range.1 (List.mem_filter.1 hk).1)
          rw [hpos j, e]
      · exact ⟨x, rfl, .inl ⟨rfl, rfl⟩, fun j => by
          rw [(List.filter_eq_nil_iff (p := fun k => decide (Verify.amendRank ib k < 0))).2 fun k _ => by simp]
          simp⟩
      · intro rr hrr acc b hPa hb
        obtain ⟨a, hac, hform, hpos⟩ := hPa
        subst hac
        have hA : ∀ M Q al, a.c.enc = .alp M Q al → Column.alpF32 al = (w == 4) := by
          rcases hform with ⟨-, e⟩ | ⟨B, e⟩
          · rw [e]; exact hxA
          · intro M Q al h'; rw [e] at h'; cases h'
        obtain ⟨yc, hyc, hst⟩ := bind_ok hb
        obtain ⟨cur, hcur, h2⟩ := bind_ok hst
        obtain ⟨Rd, hRd, hsc⟩ := bind_ok h2
        have hlo : (if rr == 0 then 0 else
            (Column.bitsAt (Kernel.amendRounds nx.toUSize 8 true ib) ((1 + rr) * 8) 8).toNat) =
            (List.range (ib.size / 8)).countP (fun k => decide (Verify.amendRank ib k < rr)) := by
          cases rr with
          | zero => simp
          | succ q => rw [if_neg (by simp), show 1 + (q + 1) = 2 + q by omega, hcnt q (by omega)]
        obtain ⟨a', ha', hBo, hp⟩ := amend_round_ranked hw he hdy dec htl hnx _ ib hni rr y hyA x a hA hpos _
          (round_positions nx.toUSize ib hmiss h1' hrr hlo (hcnt rr hrr)) hyc hcur hRd hsc
        exact ⟨a', ha', .inr hBo, hp⟩
  -- the answer read back is the last accumulator, and position by position it is `amendSpec`
  obtain ⟨out, hok, a, hac, ⟨B, hBo⟩, hpos⟩ := key
  have hRc := Find.onKey_c hok
  obtain ⟨D0, hD0, hD0s, -⟩ := bytesOf_fixed hw he a hU
  rw [hac, hBo] at hD0
  have e : B = D0 := Option.some.inj hD0
  subst e
  obtain ⟨D, hD, hDw⟩ := bytesOf_answer_bytes hw he B hD0s hnx
  rw [hBo] at hRc
  have hRl : R.toList = a.toList := by
    rw [htl R (by rw [hRc]; exact hD) hU, hDw, ← htl a (by rw [hac, hBo]; rfl) hU]
  rw [hRl]
  have hik : ∀ k < ib.size / 8, i.toList[k]!.toInt.toNat = (Column.bitsAt ib (k * 8) 8).toNat := fun k hk => by
    rw [← hix k hk, hil, getElem!_pos _ k (by simp [Verify.elemsW, hk])]
    simp [Verify.elemsW]
  refine amendSpec_of_positions f x.toList y.toList i.toList (by rw [Arr.length_toList, Arr.length_toList])
    (fun v hv => by rw [Arr.length_toList]; exact (hin v hv).2) a.toList fun j => ?_
  have hf : (List.range (ib.size / 8)).filter (fun k => decide (i.toList[k]!.toInt.toNat = j)) =
      (List.range (ib.size / 8)).filter (fun k => decide ((Column.bitsAt ib (k * 8) 8).toNat = j)) :=
    List.filter_congr fun k hk => by rw [hik k (List.mem_range.1 hk)]
  rw [hpos j, Arr.length_toList, hf]

/-- An element law that always answers, mapped over a zip: `zipWith` of the law. -/
theorem mapM_ok_zipWith {α β γ ε : Type} (g : α → β → γ) : ∀ (l₁ : List α) (l₂ : List β),
    (l₁.zip l₂).mapM (fun p => (Except.ok (g p.1 p.2) : Except ε γ)) = .ok (List.zipWith g l₁ l₂)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l₁, b :: l₂ => by
    simp only [List.zip_cons_cons, List.mapM_cons, List.zipWith_cons_cons, mapM_ok_zipWith g l₁ l₂]; rfl

/-- **`@[x;i;v;y]` on longs, `v` an arithmetic verb (`valOp`), is `amendSpec` of `v`'s step**
    (`intStep`, nulls by q's rule): `amend_verb_toList` with the element law of `val_spec_long` /
    `val_spec_long_bF` (a gathered `x` is dense, `y` dense or `foR`). -/
theorem amend_verb_toList_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hv : Eval.ewType v .long .long = some .long) {nx ni ny : Nat} {x : Arr .long nx} {i : Arr .long ni}
    {y : Arr .long ny} {R : Arr .long nx} (hnx : nx < 2 ^ 32) (hni : ni < 2 ^ 32)
    (h : Struct.amend x i (some v) y = .ok R) :
    ni = ny ∧ (∀ v ∈ i.toList, 0 ≤ v ∧ v.toInt.toNat < nx) ∧
      -- the generic lemmas state `amendSpec` with `Carrier`'s `Inhabited`; instance search would pick `Int64`'s
      R.toList = @Struct.amendSpec (El .long) instInhabitedCarrier (Kernel.Ew.intStep op Int64.minValue)
        x.toList i.toList y.toList := by
  have noAlp : ∀ {m} (z : Arr .long m) (M P a : ByteArray), z.c.enc = .alp M P a → Column.alpF32 a = (8 == 4) :=
    fun z M P a e => by rcases fixed_parts (w := 8) rfl rfl z with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩ <;> rw [hb] at e <;> cases e
  refine amend_verb_toList (f := Kernel.Ew.intStep op Int64.minValue) rfl (.inl rfl) ?_ (noAlp x) (noAlp y) hnx hni h
  intro m cur yv R ⟨B, hB⟩ hm hR
  have hmU : m < USize.size := Nat.lt_of_lt_of_le hm USize.le_size
  have hs : Ew.ValSpec v hv cur yv R := by
    rcases fixed_parts (w := 8) rfl rfl yv with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩
    · exact val_spec_long hop hv hB hb hmU hR
    · exact val_spec_long_bF hop hv hB hb hmU hR
  unfold Ew.ValSpec at hs
  simp only [Ew.elem_long_val hop hv] at hs
  rw [mapM_ok_zipWith (Kernel.Ew.intStep op Int64.minValue)] at hs
  exact (Except.ok.inj hs).symm

/-- **`@[x;i;v;y]` on longs as a relation**, `v` an arithmetic verb, distinct indices: positions no index
    names keep `x`; a named position pairs its `x` with the `y` its index carries and applies `v`'s step. -/
theorem amend_rel_long {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (hv : Eval.ewType v .long .long = some .long) {nx ni ny : Nat} {x : Arr .long nx} {i : Arr .long ni}
    {y : Arr .long ny} {R : Arr .long nx} (hnx : nx < 2 ^ 32) (hni : ni < 2 ^ 32)
    (h : Struct.amend x i (some v) y = .ok R) (hnd : (i.toList.map fun v => v.toInt.toNat).Nodup) :
    R.rel = corNeg (ran (i.rel ≫ pos)) ≫ x.rel ∪
      ran (i.rel ≫ pos) ≫ ⟪x.rel, (i.rel ≫ pos)° ≫ y.rel⟫ ≫
        RelSet.graph fun p => Kernel.Ew.intStep op Int64.minValue p.1 p.2 :=
  amend_rel (amend_verb_toList_long hop hv hnx hni h) hnd

#print axioms amend_round
#print axioms amend_round_ranked
#print axioms amend_verb_toList
#print axioms amend_verb_toList_long
#print axioms amend_rel_long

end LeetQ.Rel.Verb
