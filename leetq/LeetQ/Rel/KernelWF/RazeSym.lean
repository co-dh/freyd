/-
  What `raze` CONTAINS at `symbol`: the razed column lists its parts' symbols one part after another, whether
  every part is a blob (`concatSyms`) or some part is interned (`concatEnum`: `fewSyms`, then `internConcat`
  over `concatIds`). Each step is read back entry by entry: entry `O_k + i` of the answer has the bytes of
  entry `i` of part `k`, `O_k` the counts of the parts before `k`.
-/
import LeetQ.Rel.KernelWF.CodesProd
import LeetQ.Rel.KernelWF.CodesSym

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg

/-! ## Positions of a concatenation -/

/-- The parts before `k`, and part `k`, sum to at most the whole. -/
theorem take_sum_add_le {α : Type} (f : α → Nat) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length), ((l.take k).map f).sum + f (l[k]'hk) ≤ (l.map f).sum
  | [], _, hk => absurd hk (by simp)
  | x :: l, 0, _ => by simp
  | x :: l, k + 1, hk => by
    have := take_sum_add_le f l k (by simpa using hk)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-- Every position below the summed lengths falls in one part: past the lengths before it, inside its own. -/
theorem offset_cover {α : Type} (len : α → Nat) :
    ∀ (l : List α) (j : Nat), j < (l.map len).sum →
      ∃ k, ∃ hk : k < l.length, ∃ i, i < len (l[k]'hk) ∧ j = ((l.take k).map len).sum + i
  | [], j, hj => by simp at hj
  | x :: l, j, hj => by
    by_cases h : j < len x
    · exact ⟨0, by simp, j, by simpa using h, by simp⟩
    · obtain ⟨k, hk, i, hi, e⟩ := offset_cover len l (j - len x)
        (by simp only [List.map_cons, List.sum_cons] at hj; omega)
      exact ⟨k + 1, by simpa using hk, i, by simpa using hi,
        by simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega⟩

/-- A list of the summed length that reads part `k`'s element `i` past the lengths before `k` is the parts one
    after another. -/
theorem eq_flatMap_of_offset {α β : Type} (f : α → List β) (L : List β) (l : List α)
    (hL : L.length = (l.map fun c => (f c).length).sum)
    (h : ∀ k (hk : k < l.length) i, i < (f (l[k]'hk)).length →
      L[((l.take k).map fun c => (f c).length).sum + i]? = (f (l[k]'hk))[i]?) :
    L = l.flatMap f := by
  apply List.ext_getElem?
  intro j
  have hF : (l.flatMap f).length = (l.map fun c => (f c).length).sum := by simp [List.length_flatMap]
  by_cases hj : j < (l.map fun c => (f c).length).sum
  · obtain ⟨k, hk, i, hi, rfl⟩ := offset_cover (fun c => (f c).length) l j hj
    rw [h k hk i hi, flatMap_offset f (fun c => (f c).length) (fun _ => rfl) l hk hi]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Sums over the first `k` of two lists agree where the lists agree term by term. -/
theorem take_sum_congr {α β : Type} (f : α → Nat) (g : β → Nat) (xs : List α) (ys : List β)
    (hl : xs.length = ys.length) (h : ∀ j (h1 : j < xs.length) (h2 : j < ys.length), f (xs[j]'h1) = g (ys[j]'h2))
    (k : Nat) : ((xs.take k).map f).sum = ((ys.take k).map g).sum := by
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_take]
  exact h j _ _

/-- An `Option` pass that answers `some` answers at every index: the image of that index. -/
theorem mapM_getElem {α β : Type} {f : α → Option β} {cs : Array α} {qs : Array β} (h : cs.mapM f = some qs) :
    ∃ hs : qs.size = cs.size, ∀ k (hk : k < cs.size), f (cs[k]'hk) = some (qs[k]'(hs ▸ hk)) := by
  have key : ∀ (l : List α) (ql : List β), l.mapM f = some ql →
      ∃ hs : ql.length = l.length, ∀ k (hk : k < l.length), f (l[k]'hk) = some (ql[k]'(hs ▸ hk)) := by
    intro l; induction l with
    | nil => intro ql h; simp at h; subst h; exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
    | cons a l ih =>
      intro ql h
      rw [List.mapM_cons] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some x =>
        cases hl : l.mapM f with
        | none => simp [ha, hl] at h
        | some xs =>
          simp [ha, hl] at h; subst h
          obtain ⟨hs, hx⟩ := ih xs hl
          refine ⟨by simp [hs], fun k hk => ?_⟩
          cases k with
          | zero => simpa using ha
          | succ k => simpa using hx k (by simpa using hk)
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList] at h
  cases hq : l.mapM f with
  | none => simp [hq] at h
  | some ql =>
    simp [hq] at h; subst h
    obtain ⟨hs, hx⟩ := key l ql hq
    exact ⟨by simpa using hs, fun k hk => by simpa using hx k (by simpa using hk)⟩

/-! ## `concatSyms` read back -/

/-- **`concatSyms` read back**: entry `O_p + k` of the joined blob, `O_p` the entries of the parts before `p`,
    is entry `k` of part `p`. -/
theorem concatSyms_symAt {parts : Array (ByteArray × Array Nat)} (hw : ∀ x ∈ parts, SymsWF x.1 x.2)
    {t n a} {b : ByteArray} {o : Array Nat} (h : concatSyms parts = .vector t n (.syms b o) a)
    (p : Nat) (hp : p < parts.size) (k : Nat) (hk : k < (parts[p]'hp).2.size - 1) :
    ((parts.toList.take p).map fun x => x.2.size - 1).sum + k < o.size - 1 ∧
    Verify.symAt b o (((parts.toList.take p).map fun x => x.2.size - 1).sum + k) =
      Verify.symAt (parts[p]'hp).1 (parts[p]'hp).2 k := by
  obtain ⟨hS, hn, hB⟩ := Verify.symBytes_concatSyms hw h
  have hx := hw _ (Array.getElem_mem hp)
  have hle := take_sum_add_le (fun x : ByteArray × Array Nat => x.2.size - 1) parts.toList p (by simpa using hp)
  simp only [Array.getElem_toList] at hle
  have hlt : ((parts.toList.take p).map fun x => x.2.size - 1).sum + k < o.size - 1 := by omega
  refine ⟨hlt, ?_⟩
  rw [Verify.symAt_eq_dropLast _ _ _ (hS.le _ (by omega)), Verify.symAt_eq_dropLast _ _ _ (hx.le _ (by omega)),
    hB p hp k hk]

/-! ## `concatIds` and `internConcat` read back -/

/-- An id width is a lane. -/
theorem idWidth_lane (o : Array Nat) : Column.idWidth o = 0 ∨ Column.idWidth o = 1 ∨ Column.idWidth o = 2 ∨
    Column.idWidth o = 4 ∨ Column.idWidth o = 8 ∨ Column.idWidth o = 16 ∨ Column.idWidth o = 32 ∨
    Column.idWidth o = 64 := Verify.laneWidth_cases _

/-- **`concatIds` read back**: id `O_k + i` of the answer, `O_k` the counts before part `k`, is part `k`'s id `i`
    read through its map. -/
theorem concatIds_idAt {w : Nat} (hw : w = 0 ∨ laneOK(w))
    (cs : Array USize) (ws : Array Nat) (maps parts : Array ByteArray) (hm : cs.size ≤ parts.size)
    (k : Nat) (hk : k < cs.size) (i : Nat) (hi : i < (cs[k]'hk).toNat) :
    Column.idAt (concatIds w.toUSize (countBytes cs) ws maps parts) w (((cs.toList.take k).map USize.toNat).sum + i) =
      Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i) := by
  have hw64 : w ≤ 64 := by omega
  have hwn : w.toUSize.toNat = w :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show w < 2 ^ 32 by omega) USize.le_size)
  have hc : (countBytes cs).size / 8 = cs.size := by rw [countBytes_size, Nat.mul_div_cancel_left _ (by decide)]
  simp only [concatIds, hwn]
  generalize hids : (Array.range (min ((countBytes cs).size / 8) parts.size)).flatMap (fun k =>
    (Array.range (Column.bitsAt (countBytes cs) (8 * k) 8).toNat).map fun i =>
      Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i)) = ids
  have hl : ids.toList = (List.range cs.size).flatMap fun k =>
      (List.range (cs[k]!).toNat).map fun i => Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i) := by
    rw [← hids, Array.toList_flatMap, Array.toList_range, hc, Nat.min_eq_left hm]
    unfold List.flatMap; congr 1
    apply List.map_congr_left; intro j hj
    rw [List.mem_range] at hj
    rw [Array.toList_map, Array.toList_range, countBytes_get cs j hj, USize.toNat_toUInt64, getElem!_pos cs j hj]
  have hO : ((List.range cs.size).take k).map (fun j => (cs[j]!).toNat) = (cs.toList.take k).map USize.toNat :=
    List.ext_getElem (by simp) fun j h1 h2 => by
      simp only [List.length_map, List.length_take, List.length_range] at h1
      simp [getElem!_pos cs j (by omega)]
  have hi' : i < (cs[k]!).toNat := by rw [getElem!_pos cs k hk]; exact hi
  have hoff := flatMap_offset (fun k => (List.range (cs[k]!).toNat).map fun i =>
      Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i))
    (fun k => (cs[k]!).toNat) (fun c => by simp) (List.range cs.size) (k := k) (by simpa using hk) (i := i)
    (by simpa using hi')
  simp only [List.getElem_range, hO, ← hl, List.getElem?_map, List.getElem?_range hi', Option.map_some] at hoff
  obtain ⟨hj, hv⟩ := List.getElem?_eq_some_iff.1 hoff
  have hj' : ((cs.toList.take k).map USize.toNat).sum + i < ids.size := by simpa using hj
  have hv' : ids[((cs.toList.take k).map USize.toNat).sum + i]! =
      Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i) := by
    rw [getElem!_pos ids _ hj', ← Array.getElem_toList]; exact hv
  rw [Verify.idAt_packIds hw hj' (by rw [hv']; exact Verify.idAt_lt _ _ _ hw64), hv']

/-- A fold that pushes the last entry plus the next part's count keeps every entry it was handed. -/
theorem bases_keep' (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1)) (l : List (ByteArray × Array Nat)) :
    ∀ (acc : Array Nat) (i : Nat), i < acc.size → (l.foldl g acc)[i]! = acc[i]! := by
  induction l with
  | nil => intro acc i _; rfl
  | cons a l ih =>
    intro acc i hi
    simp only [List.foldl]
    rw [ih _ i (by rw [hg, Array.size_push]; omega), hg, getElem!_pos _ i (by rw [Array.size_push]; omega),
      getElem!_pos acc i hi, Array.getElem_push_lt hi]

/-- `internConcat`'s bases: part `k` starts past the entries of the parts before it. -/
theorem bases_get (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1)) (l : List (ByteArray × Array Nat))
    (hl : ∀ x ∈ l, 0 < x.2.size) :
    ∀ (acc : Array Nat), 0 < acc.size → ∀ k, k ≤ l.length →
      (l.foldl g acc)[acc.size - 1 + k]! = acc[acc.size - 1]! + ((l.take k).map (·.2.size - 1)).sum := by
  induction l with
  | nil => intro acc _ k hk; simp at hk; subst hk; simp
  | cons a l ih =>
    intro acc hacc k hk
    have ha := hl a (List.mem_cons_self ..)
    have hs : (g acc a).size = acc.size + 1 := by rw [hg, Array.size_push]
    have hpush : (g acc a)[acc.size]! = acc[acc.size - 1]! + (a.2.size - 1) := by
      rw [hg, getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]; omega
    simp only [List.foldl]
    cases k with
    | zero =>
      rw [Nat.add_zero, bases_keep' g hg l _ _ (by omega), hg, getElem!_pos _ _ (by rw [Array.size_push]; omega),
        Array.getElem_push_lt (by omega), ← getElem!_pos acc _ (by omega)]
      simp
    | succ k =>
      have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (g acc a) (by omega) k (by simpa using hk)
      rw [hs, Nat.add_sub_cancel, hpush] at this
      rw [show acc.size - 1 + (k + 1) = acc.size + k by omega, this]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

/-- `internConcat`'s bases from `#[0]`: part `k` starts past the entries of the parts before it. -/
theorem bases_zero (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1)) (l : List (ByteArray × Array Nat))
    (hl : ∀ x ∈ l, 0 < x.2.size) (k : Nat) (hk : k ≤ l.length) :
    (l.foldl g #[0])[k]! = ((l.take k).map (·.2.size - 1)).sum := by
  have := bases_get g hg l hl #[0] (by decide) k hk
  rw [show (#[0] : Array Nat)[(#[0] : Array Nat).size - 1]! = 0 from rfl,
    show (#[0] : Array Nat).size - 1 + k = k by simp] at this
  simpa using this

/-- **`internConcat` read back**: the entry the answer's id `O_k + i` names, `O_k` the counts of the parts
    before `k`, has the bytes of the entry part `k`'s id `i` names. The parts' dictionaries, summed, fit a
    `USize`, the count `internSyms` numbers its entries in. -/
theorem internConcat_symAt (qs : Array (USize × ByteArray × Array Nat × ByteArray))
    (hq : ∀ p ∈ qs, SymsWF p.2.1 p.2.2.1 ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1)
    (hD : (qs.toList.map fun p => p.2.2.1.size - 1).sum < USize.size)
    (k : Nat) (hk : k < qs.size) (i : Nat) (hi : i < (qs[k]'hk).1.toNat) :
    Verify.symAt (internConcat qs).1 (internConcat qs).2.1
        (Column.idAt (internConcat qs).2.2 (Column.idWidth (internConcat qs).2.1)
          (((qs.toList.take k).map (·.1.toNat)).sum + i)) =
      Verify.symAt (qs[k]'hk).2.1 (qs[k]'hk).2.2.1
        (Column.idAt (qs[k]'hk).2.2.2 (Column.idWidth (qs[k]'hk).2.2.1) i) := by
  obtain ⟨-, hid⟩ := hq _ (Array.getElem_mem hk)
  have he := hid i hi
  generalize hE : Column.idAt (qs[k]'hk).2.2.2 (Column.idWidth (qs[k]'hk).2.2.1) i = e at he ⊢
  unfold internConcat
  -- the kernel's pattern-matching lambdas, renamed to projections
  generalize hds : (Array.map _ qs : Array (ByteArray × Array Nat)) = ds
  obtain rfl : ds = qs.map fun p => (p.2.1, p.2.2.1) := by
    rw [← hds]
  obtain ⟨n', cb, co, hC⟩ : ∃ n' cb co,
      concatSyms (qs.map fun p => (p.2.1, p.2.2.1)) = .vector .symbol n' (.syms cb co) none :=
    ⟨_, _, _, rfl⟩
  simp only [hC]
  generalize hws : (Array.map _ (qs.map fun p => (p.2.1, p.2.2.1)) : Array Nat) = ws
  obtain rfl : ws = (qs.map fun p => (p.2.1, p.2.2.1)).map fun x => Column.idWidth x.2 := by
    rw [← hws]
  generalize hns : (Array.map _ qs : Array USize) = ns
  obtain rfl : ns = qs.map (·.1) := by
    rw [← hns]
  generalize hps : (Array.map _ qs : Array ByteArray) = ps
  obtain rfl : ps = qs.map (·.2.2.2) := by
    rw [← hps]
  generalize hB : (Array.foldl _ #[0] (qs.map fun p => (p.2.1, p.2.2.1)) : Array Nat) = B
  have hcs := hC
  have hdw : ∀ x ∈ qs.map (fun p => (p.2.1, p.2.2.1)), SymsWF x.1 x.2 := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := Array.mem_map.1 hx; exact (hq p hp).1
  have hk' : k < (qs.map fun p => (p.2.1, p.2.2.1)).size := by simpa using hk
  obtain ⟨hlt, hsym⟩ := concatSyms_symAt hdw hcs k hk' e (by simpa using he)
  obtain ⟨-, hn, -⟩ := Verify.symBytes_concatSyms hdw hcs
  have hco : co.size - 1 < USize.size := by
    rw [hn, Array.toList_map, List.map_map]; exact hD
  have hsI := (Verify.internSyms_symAt cb co hco hlt).2
  -- part `k`'s entries start at its base
  have hBk : B[k]! = ((((qs.map fun p => (p.2.1, p.2.2.1)).toList).take k).map fun x => x.2.size - 1).sum := by
    rw [← hB, ← Array.foldl_toList]
    refine bases_zero _ ?_ _ (fun x hx => (hdw x (Array.mem_def.2 hx)).pos) k (by simp; omega)
    intro acc x; obtain ⟨_, _⟩ := x; rfl
  have hOk : ((qs.toList.take k).map (·.1.toNat)).sum = (((qs.map (·.1)).toList.take k).map USize.toNat).sum := by
    rw [Array.toList_map, ← List.map_take, List.map_map]; rfl
  rw [hOk, concatIds_idAt (idWidth_lane _) _ _ _ _ (by simp) k (by simpa using hk) i (by simpa using hi)]
  simp (disch := simp [hk]) only [getElem!_pos, Array.getElem_map, Array.getElem_range]
  rw [hE, Verify.idAt_packIds (f := fun j => Column.idAt (Order.internSyms cb co).2.2
      (Column.idWidth (Order.internSyms cb co).2.1) (B[k]! + j)) (idWidth_lane _) (by simpa using he)
    (Verify.idAt_lt _ _ _ (by rcases idWidth_lane (Order.internSyms cb co).2.1 with h | h | h | h | h | h | h | h <;> omega)),
    hBk, hsI]
  simpa using hsym

/-! ## `fewSyms` read back -/

/-- `fewSyms`' fold, step by step: entry `t` of the blob it builds is the dictionary's entry `e t`, NUL
    included. -/
theorem fewSyms_fold (d : ByteArray) (dof : Array Nat) (e : Nat → Nat) :
    ∀ (N : Nat) (f : (i : Nat) → i < N → ByteArray × Array Nat → ByteArray × Array Nat),
      (∀ i h p, f i h p = (d.copySlice dof[e i]! p.1 p.1.size (dof[e i + 1]! - dof[e i]!),
        p.2.push (d.copySlice dof[e i]! p.1 p.1.size (dof[e i + 1]! - dof[e i]!)).size)) →
      ∀ {q : ByteArray × Array Nat}, Nat.fold N f (ByteArray.empty, #[0]) = q →
      q.2.size = N + 1 ∧ q.2[N]! = q.1.size ∧ (∀ t ≤ N, q.2[t]! ≤ q.1.size) ∧
        ∀ t < N, Verify.symBytes q.1 q.2 t = Verify.symBytes d dof (e t)
  | 0, f, _, q, hq => by
    subst hq
    refine ⟨rfl, rfl, fun t ht => ?_, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    rw [show t = 0 by omega]; exact Nat.le_refl _
  | N + 1, f, hf, q, hq => by
    subst hq
    have ih := fewSyms_fold d dof e N (fun i h => f i (by omega)) (fun i h p => hf i _ p) rfl
    rw [Nat.fold_succ, hf]
    generalize Nat.fold N (fun i h => f i (by omega)) (ByteArray.empty, #[0]) = q at ih ⊢
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨g1, g2, g3, g4, g5⟩ := Verify.symBytes_push q.1
      (d.copySlice dof[e N]! q.1 q.1.size (dof[e N + 1]! - dof[e N]!)) q.2 N
      (Verify.symBytes d dof (e N)) h1 h2 h3 (Verify.copySlice_end _ _ _ _)
    refine ⟨g1, g2, g3, fun t ht => ?_⟩
    rcases Nat.lt_or_ge t N with h | h
    · rw [g5 t h, h4 t h]
    · rw [show t = N by omega, g4]

/-- **`fewSyms` read back**: its entry `i` has the bytes of the dictionary entry element `i`'s id names. -/
theorem fewSyms_symAt {n : USize} {d : ByteArray} {dof : Array Nat} {ids b : ByteArray} {bo : Array Nat}
    (hd : SymsWF d dof) (hi : ∀ i < n.toNat, Column.idAt ids (Column.idWidth dof) i < dof.size - 1)
    (h : fewSyms n (.enum d dof ids) = some (b, bo)) (i : Nat) (hin : i < n.toNat) :
    Verify.symAt b bo i = Verify.symAt d dof (Column.idAt ids (Column.idWidth dof) i) := by
  unfold fewSyms at h
  dsimp only at h
  split at h
  · rw [Option.some.injEq] at h
    obtain ⟨-, -, h3, h4⟩ := fewSyms_fold d dof (fun i => Column.idAt ids (Column.idWidth dof) i) n.toNat _
      (fun i _ p => by obtain ⟨b, o⟩ := p; rfl) h
    dsimp only at h3 h4
    have he := hi i hin
    rw [Verify.symAt_eq_dropLast _ _ _ (h3 _ (by omega)), h4 i hin,
      Verify.symAt_eq_dropLast _ _ _ (hd.le _ (by omega))]
  · cases h

/-- `fewSyms` answers only where the element count is below an eighth of the dictionary's. -/
theorem fewSyms_lt {n : USize} {d : ByteArray} {dof : Array Nat} {ids b : ByteArray} {bo : Array Nat}
    (h : fewSyms n (.enum d dof ids) = some (b, bo)) : 8 * n.toNat < dof.size - 1 := by
  unfold fewSyms at h
  dsimp only at h
  split at h
  · assumption
  · cases h

/-- `internSyms` answers no more entries than its source has. -/
theorem internSyms_card_le (b : ByteArray) (o : Array Nat) :
    (Order.internSyms b o).2.1.size - 1 ≤ o.size - 1 := by
  have hD := Verify.distinctSyms_eraseDups b o
  simp only [Verify.symsOf, ← Verify.firstsOf_eraseDups] at hD
  have := congrArg List.length hD
  simp only [List.length_map, List.length_range] at this
  show (Order.distinctSyms b o).2.size - 1 ≤ o.size - 1
  rw [this, Verify.firstsOf]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-! ## The answer's rows, part by part -/

/-- A symbol column whose row `j` has the bytes `G j` lists the parts' rows in turn, when `G` at part `k`'s
    offset `O_k + i` gives the bytes of that part's row `i`. -/
theorem symbol_toList_eq {N : USize} (X : Arr .symbol N) (G : Nat → List UInt8)
    (hX : ∀ j (hj : j < N.toNat), (X.get ⟨j, hj⟩).toUTF8.data.toList = G j)
    (l : List ((k : USize) × Arr .symbol k)) (hN : N.toNat = (l.map (·.1.toNat)).sum)
    (h : ∀ k (hk : k < l.length) i (hi : i < (l[k]'hk).1.toNat),
      G (((l.take k).map (·.1.toNat)).sum + i) = ((l[k]'hk).2.get ⟨i, hi⟩).toUTF8.data.toList) :
    X.toList = l.flatMap (·.2.toList) := by
  have hlen : (fun c : (k : USize) × Arr .symbol k => c.2.toList.length) = (·.1.toNat) :=
    funext fun c => Arr.length_toList c.2
  apply eq_flatMap_of_offset
  · rw [hlen, Arr.length_toList, hN]
  · intro k hk i hi
    rw [hlen]; rw [Arr.length_toList] at hi
    have hj : ((l.take k).map (·.1.toNat)).sum + i < N.toNat := by
      have := take_sum_add_le (·.1.toNat) l k hk; omega
    rw [List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hj),
      List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hi), Arr.getElem_toList, Arr.getElem_toList]
    congr 1; apply str_eq_of_bytes; rw [hX _ hj]; exact h k hk i hi

/-! ## A part's encoding, read as bytes -/

/-- A blob column's row `j` has the bytes of entry `j`. -/
theorem syms_get {n : USize} (x : Arr .symbol n) {b : ByteArray} {o : Array Nat} (he : x.enc = .syms b o)
    (j : Nat) (hj : j < n.toNat) : (x.get ⟨j, hj⟩).toUTF8.data.toList = Verify.symAt b o j := by
  have hwf := x.wf; rw [he] at hwf
  obtain ⟨-, -, hu⟩ := hwf
  rw [← Vals.row_atom]; exact syms_row x he hu ⟨j, hj⟩

/-- An interned column's row `j` has the bytes of the entry its id `j` names. -/
theorem enum_get {n : USize} (x : Arr .symbol n) {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (he : x.enc = .enum d o ids) (j : Nat) (hj : j < n.toNat) :
    (x.get ⟨j, hj⟩).toUTF8.data.toList = Verify.symAt d o (Column.idAt ids (Column.idWidth o) j) := by
  have hwf := x.wf; rw [he] at hwf
  obtain ⟨-, -, hlt, -, hu⟩ := hwf
  rw [← Vals.row_atom]; exact enum_row x he hu hlt ⟨j, hj⟩

/-- **A part through `Column.intern`**: its count, a dictionary laid out as `SymsWF` says and of valid UTF-8, ids
    below the dictionary's count, row `i`'s bytes the entry id `i` names, and a dictionary no larger than the
    part's own (its count, for a blob). -/
theorem intern_part (c : (k : USize) × Arr .symbol k) {q : USize × ByteArray × Array Nat × ByteArray}
    (h : (match Column.intern c.2.enc with | .enum d o ids => some (c.1, d, o, ids) | _ => none) = some q) :
    q.1 = c.1 ∧ SymsWF q.2.1 q.2.2.1 ∧ (∀ j < q.2.2.1.size - 1, (Column.symKey q.2.1 q.2.2.1 j).IsValidUTF8) ∧
    (∀ i < c.1.toNat, Column.idAt q.2.2.2 (Column.idWidth q.2.2.1) i < q.2.2.1.size - 1) ∧
    (∀ i (hi : i < c.1.toNat), Verify.symAt q.2.1 q.2.2.1 (Column.idAt q.2.2.2 (Column.idWidth q.2.2.1) i) =
      (c.2.get ⟨i, hi⟩).toUTF8.data.toList) ∧
    q.2.2.1.size - 1 ≤ (match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat) := by
  have hwf := c.2.wf
  revert h hwf
  cases he : c.2.enc with
  | syms b o =>
    intro h hwf
    simp only [intern_syms, Option.some.injEq] at h
    subst h
    obtain ⟨hos, -, hu⟩ := hwf
    have hn : o.size - 1 = c.1.toNat := by omega
    obtain ⟨hlt, -, hrow, -⟩ := internSyms_facts c.2 he
    refine ⟨rfl, Verify.symsWF_internSyms b o, utf8_distinctSyms b o (fun i hi => hu i (by omega)), hlt,
      fun i hi => by rw [← Vals.row_atom]; exact (hrow ⟨i, hi⟩).symm, ?_⟩
    have := internSyms_card_le b o
    dsimp only; omega
  | enum d o ids =>
    intro h hwf
    simp only [Column.intern, Option.some.injEq] at h
    subst h
    obtain ⟨-, hsw, hlt, -, hu⟩ := hwf
    exact ⟨rfl, hsw, hu, hlt, fun i hi => (enum_get c.2 he i hi).symm, Nat.le_refl _⟩
  | _ => intro _ hwf; simp [Enc.WF, QAtomicType.width] at hwf

/-- **A part through `fewSyms`** keeps what `intern_part` says of it: the blob of its own symbols, its ids
    counting them. -/
theorem few_part (c : (k : USize) × Arr .symbol k) {q : USize × ByteArray × Array Nat × ByteArray}
    (hq : q.1 = c.1 ∧ SymsWF q.2.1 q.2.2.1 ∧
      (∀ j < q.2.2.1.size - 1, (Column.symKey q.2.1 q.2.2.1 j).IsValidUTF8) ∧
      (∀ i < c.1.toNat, Column.idAt q.2.2.2 (Column.idWidth q.2.2.1) i < q.2.2.1.size - 1) ∧
      (∀ i (hi : i < c.1.toNat), Verify.symAt q.2.1 q.2.2.1 (Column.idAt q.2.2.2 (Column.idWidth q.2.2.1) i) =
        (c.2.get ⟨i, hi⟩).toUTF8.data.toList) ∧
      q.2.2.1.size - 1 ≤ (match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat))
    {b : ByteArray} {bo : Array Nat} (hf : fewSyms q.1 (.enum q.2.1 q.2.2.1 q.2.2.2) = some (b, bo)) :
    let r : USize × ByteArray × Array Nat × ByteArray :=
      (q.1, b, bo, Column.packIds (Column.idWidth bo) q.1.toNat fun j => j)
    r.1 = c.1 ∧ SymsWF r.2.1 r.2.2.1 ∧ (∀ j < r.2.2.1.size - 1, (Column.symKey r.2.1 r.2.2.1 j).IsValidUTF8) ∧
    (∀ i < c.1.toNat, Column.idAt r.2.2.2 (Column.idWidth r.2.2.1) i < r.2.2.1.size - 1) ∧
    (∀ i (hi : i < c.1.toNat), Verify.symAt r.2.1 r.2.2.1 (Column.idAt r.2.2.2 (Column.idWidth r.2.2.1) i) =
      (c.2.get ⟨i, hi⟩).toUTF8.data.toList) ∧
    r.2.2.1.size - 1 ≤ (match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat) := by
  obtain ⟨n, d, o, ids⟩ := q
  obtain ⟨h1, hw, hu, hlt, hrow, hcnt⟩ := hq
  dsimp only at h1 hw hu hlt hrow hcnt hf ⊢
  subst h1
  have hs := fewSyms_size hf
  have h8 := fewSyms_lt hf
  obtain ⟨hw', hu'⟩ := fewSyms_utf8 hw hlt hu hf
  have hid : ∀ i < c.1.toNat, Column.idAt (Column.packIds (Column.idWidth bo) c.1.toNat fun j => j)
      (Column.idWidth bo) i = i := fun i hi =>
    Verify.idAt_packIds (idWidth_lane _) hi
      (lt_idWidthOf_64 (n := bo.size - 1) (by omega) (Nat.lt_trans hi (Verify.usize_lt c.1)))
  refine ⟨rfl, hw', hu', fun i hi => by rw [hid i hi]; omega,
    fun i hi => by rw [hid i hi, fewSyms_symAt hw hlt hf i hi, hrow i hi], by omega⟩

/-- Sums of two lists agree term by term in order: the first at most the second. -/
theorem sum_le_of_getElem {α β : Type} (f : α → Nat) (g : β → Nat) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ j (h1 : j < xs.length) (h2 : j < ys.length), f (xs[j]'h1) ≤ g (ys[j]'h2)) →
      (xs.map f).sum ≤ (ys.map g).sum
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hle => by
    have ih := sum_le_of_getElem f g xs ys (by simpa using h)
      fun j h1 h2 => hle (j + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2)
    have h0 := hle 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    simp only [List.map_cons, List.sum_cons]; omega

-- dup of Raze.hashConcat_ok (private there)
theorem hashConcat_ok' {qs : Array (USize × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .ok r) : r = internConcat qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

-- dup of Raze.hashConcat_error (private there)
theorem hashConcat_error' {qs : Array (USize × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .error r) : r = qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

/-! ## `razeColumn` at `symbol` -/

/-- **`razeColumn` at `symbol` lists its parts' rows in turn**, whether every part is a blob (`concatSyms`) or
    some part is interned (`concatEnum`); the parts' dictionaries, a blob counting its rows, fit a `USize`. -/
theorem razeColumn_symbol_toList (l : List ((k : USize) × Arr .symbol k)) {N : USize} (X : Arr .symbol N)
    (hN : N.toNat = (l.map (·.1.toNat)).sum)
    (hD : (l.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum < USize.size)
    (hl : l ≠ []) (hV : razeColumn .symbol (l.toArray.map (·.2.part)) = some X.1) :
    X.toList = l.flatMap (·.2.toList) := by
  unfold razeColumn at hV
  rw [if_neg (by simpa using hl)] at hV
  dsimp only at hV
  split at hV
  · -- every part a blob: `concatSyms`
    rename_i ps heq
    obtain ⟨hsz, hf⟩ := mapM_getElem heq
    simp only [Array.size_map, List.size_toArray] at hsz
    have hpk : ∀ k (hk : k < l.length),
        (l[k]'hk).2.enc = .syms (ps[k]'(by omega)).1 (ps[k]'(by omega)).2 := by
      intro k hk
      have := hf k (by simpa using hk)
      simp only [Array.getElem_map, List.getElem_toArray, Arr.part] at this
      cases he : (l[k]'hk).2.enc <;> simp [he] at this
      rw [← this]
    have hcnt : ∀ k (hk : k < l.length), (ps[k]'(by omega)).2.size - 1 = (l[k]'hk).1.toNat := by
      intro k hk
      have hwf := (l[k]'hk).2.wf
      rw [hpk k hk] at hwf
      have := hwf.1; omega
    have hw : ∀ x ∈ ps, SymsWF x.1 x.2 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
      have hwf := (l[k]'(by omega)).2.wf
      rw [hpk k (by omega)] at hwf
      exact hwf.2.1
    obtain ⟨n', b, o, hC⟩ : ∃ n' b o, concatSyms ps = .vector .symbol n' (.syms b o) none := ⟨_, _, _, rfl⟩
    have he : X.enc = .syms b o := by
      rw [hC, Option.some.injEq] at hV
      rw [Arr.enc, ← hV]
    refine symbol_toList_eq X (Verify.symAt b o) (fun j hj => syms_get X he j hj) l hN ?_
    intro k hk i hi
    obtain ⟨-, hsym⟩ := concatSyms_symAt hw hC k (by omega) i (by rw [hcnt k hk]; exact hi)
    have hO : ((ps.toList.take k).map fun x => x.2.size - 1).sum = ((l.take k).map (·.1.toNat)).sum :=
      take_sum_congr _ _ ps.toList l (by simp; omega) (fun j h1 h2 => by simpa using hcnt j h2) k
    rw [← hO, hsym, syms_get (l[k]'hk).2 (hpk k hk) i hi]
  split at hV
  · -- some part interned: `concatEnum`
    rename_i qs0 heq
    obtain ⟨hsz, hf⟩ := mapM_getElem heq
    simp only [Array.size_map, List.size_toArray] at hsz
    have hP0 : ∀ k (hk : k < l.length),
        (qs0[k]'(by omega)).1 = (l[k]'hk).1 ∧ SymsWF (qs0[k]'(by omega)).2.1 (qs0[k]'(by omega)).2.2.1 ∧
        (∀ j < (qs0[k]'(by omega)).2.2.1.size - 1,
          (Column.symKey (qs0[k]'(by omega)).2.1 (qs0[k]'(by omega)).2.2.1 j).IsValidUTF8) ∧
        (∀ i < (l[k]'hk).1.toNat, Column.idAt (qs0[k]'(by omega)).2.2.2
          (Column.idWidth (qs0[k]'(by omega)).2.2.1) i < (qs0[k]'(by omega)).2.2.1.size - 1) ∧
        (∀ i (hi : i < (l[k]'hk).1.toNat), Verify.symAt (qs0[k]'(by omega)).2.1 (qs0[k]'(by omega)).2.2.1
          (Column.idAt (qs0[k]'(by omega)).2.2.2 (Column.idWidth (qs0[k]'(by omega)).2.2.1) i) =
          ((l[k]'hk).2.get ⟨i, hi⟩).toUTF8.data.toList) ∧
        (qs0[k]'(by omega)).2.2.1.size - 1 ≤
          (match (l[k]'hk).2.enc with | .enum _ o _ => o.size - 1 | _ => (l[k]'hk).1.toNat) := by
      intro k hk
      have := hf k (by simpa using hk)
      simp only [Array.getElem_map, List.getElem_toArray, Arr.part] at this
      exact intern_part (l[k]'hk) this
    unfold concatEnum at hV
    dsimp only at hV
    generalize hq : Array.mapIdx _ qs0 = qs at hV
    have hqs : qs.size = l.length := by rw [← hq, Array.size_mapIdx]; omega
    have hP : ∀ k (hk : k < l.length),
        (qs[k]'(by omega)).1 = (l[k]'hk).1 ∧ SymsWF (qs[k]'(by omega)).2.1 (qs[k]'(by omega)).2.2.1 ∧
        (∀ j < (qs[k]'(by omega)).2.2.1.size - 1,
          (Column.symKey (qs[k]'(by omega)).2.1 (qs[k]'(by omega)).2.2.1 j).IsValidUTF8) ∧
        (∀ i < (l[k]'hk).1.toNat, Column.idAt (qs[k]'(by omega)).2.2.2
          (Column.idWidth (qs[k]'(by omega)).2.2.1) i < (qs[k]'(by omega)).2.2.1.size - 1) ∧
        (∀ i (hi : i < (l[k]'hk).1.toNat), Verify.symAt (qs[k]'(by omega)).2.1 (qs[k]'(by omega)).2.2.1
          (Column.idAt (qs[k]'(by omega)).2.2.2 (Column.idWidth (qs[k]'(by omega)).2.2.1) i) =
          ((l[k]'hk).2.get ⟨i, hi⟩).toUTF8.data.toList) ∧
        (qs[k]'(by omega)).2.2.1.size - 1 ≤
          (match (l[k]'hk).2.enc with | .enum _ o _ => o.size - 1 | _ => (l[k]'hk).1.toNat) := by
      intro k hk
      have h0 := hP0 k hk
      simp only [← hq, Array.getElem_mapIdx]
      rcases hqk : qs0[k]'(by omega) with ⟨n, d, o, ids⟩
      simp only [hqk] at h0 ⊢
      by_cases hk0 : (k == 0) = true
      · simp only [hk0, if_true]; exact h0
      · simp only [hk0, if_false, Bool.false_eq_true]
        cases hfs : fewSyms n (.enum d o ids) with
        | none => exact h0
        | some r =>
          obtain ⟨b, bo⟩ := r
          exact few_part (l[k]'hk) (q := (n, d, o, ids)) h0 hfs
    have he : X.enc = .enum (internConcat qs).1 (internConcat qs).2.1 (internConcat qs).2.2 := by
      rw [Option.some.injEq] at hV
      rw [Arr.enc, ← hV]
      dsimp only
      cases hh : hashConcat qs with
      | ok r => obtain rfl := hashConcat_ok' hh; rfl
      | error r => obtain rfl := hashConcat_error' hh; rfl
    have hq' : ∀ p ∈ qs, SymsWF p.2.1 p.2.2.1 ∧
        ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1 := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hp
      obtain ⟨h1, hw, -, hlt, -⟩ := hP k (by omega)
      exact ⟨hw, by rw [h1]; exact hlt⟩
    have hD' : (qs.toList.map fun p => p.2.2.1.size - 1).sum < USize.size := by
      refine Nat.lt_of_le_of_lt ?_ hD
      apply sum_le_of_getElem _ _ qs.toList l (by simpa using hqs)
      intro j h1 h2
      simpa using (hP j h2).2.2.2.2.2
    refine symbol_toList_eq X (fun j => Verify.symAt (internConcat qs).1 (internConcat qs).2.1
      (Column.idAt (internConcat qs).2.2 (Column.idWidth (internConcat qs).2.1) j))
      (fun j hj => enum_get X he j hj) l hN ?_
    intro k hk i hi
    obtain ⟨h1, -, -, -, hrow, -⟩ := hP k hk
    have hO : ((qs.toList.take k).map (·.1.toNat)).sum = ((l.take k).map (·.1.toNat)).sum :=
      take_sum_congr _ _ qs.toList l (by simpa using hqs)
        (fun j h1 h2 => by simpa using congrArg USize.toNat (hP j h2).1) k
    dsimp only
    rw [← hO, internConcat_symAt qs hq' hD' k (by omega) i (by rw [h1]; exact hi), hrow i hi]
  · -- no answer: not what `hV` says
    cases hV

/-- **`razeTo` at `symbol`**: the razed column lists its parts' symbols one part after another, whether every
    part is a blob or some part is interned. The parts' dictionaries, a blob counting its rows, fit a `USize`:
    the joined dictionary is counted in one. -/
theorem razeTo_toList_symbol (cs : Array ((k : USize) × Arr .symbol k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size)
    (hD : (cs.toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum <
      USize.size) :
    (razeTo .symbol cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr .symbol k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  rw [dif_neg (by simpa using h0), dif_neg (by decide)]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr .symbol n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hsum : (l.map (·.1.toNat)).sum = S := by simpa using hs
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk, hsum]; exact hS
  unfold need; rw [dif_pos hf]
  exact razeColumn_symbol_toList l _ (by rw [USize.toNat_ofNat_of_lt' hf, hk]) hD h0 (Option.some_get _).symm

/-- The razed symbol column reads part `k`'s element `i` past the counts before `k`. -/
theorem raze_get_symbol {p : Nat} (cs : Vector (Part (.atom .symbol)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hD : (cs.toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum <
      USize.size)
    {k : Nat} (hk : k < p) {i : Nat} (hi : i < cs[k].1.toNat)
    (hO : ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze .symbol cs.toArray).1.toNat) :
    (raze .symbol cs.toArray).2.get ⟨_, hO⟩ = cs[k].2.get ⟨i, hi⟩ := by
  have hl := razeTo_toList_symbol cs.toArray rfl hN hD
  unfold razeTo at hl
  rw [KernelWF.cast_toList] at hl
  have ho := flatMap_offset (fun c : Part (.atom .symbol) => c.2.toList) (·.1.toNat) (fun c => Arr.length_toList _)
    cs.toList (k := k) (by simpa using hk) (i := i) (by simpa using hi)
  simp only [Vector.toList_toArray] at hl
  rw [← hl, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hO), Arr.getElem_toList,
    List.getElem?_eq_getElem (by rw [Arr.length_toList]; simpa using hi)] at ho
  have := Option.some_inj.1 ho
  rw [this, Arr.getElem_toList]; rfl

end LeetQ.Rel.KernelWF
