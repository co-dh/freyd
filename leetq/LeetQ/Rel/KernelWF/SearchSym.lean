/-
  `x bin y` at symbol columns: the answer is one long per needle, which closes the symbol case
  `binColumn_wf` leaves out.
-/
import LeetQ.Rel.KernelWF.Search

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-! ## Loops that keep an invariant -/

/-- A `for` loop over a list in `Id` keeps any property every step keeps, whether it yields or stops. -/
theorem list_forIn_inv {α σ : Type} (P : σ → Prop) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a s, P s → ∀ s', (f a s = .yield s' ∨ f a s = .done s') → P s') :
    ∀ (l : List α) (s : σ), P s → P (forIn l s f).run
  | [], s, hs => hs
  | a :: l, s, hs => by
    rw [List.forIn_cons]
    cases h : f a s with
    | done s' => exact hf a s hs s' (.inr h)
    | yield s' => exact list_forIn_inv P f hf l s' (hf a s hs s' (.inl h))

/-- The same over a range `[:n]`. -/
theorem range_forIn_inv {σ : Type} (P : σ → Prop) (n : Nat) (f : Nat → σ → Id (ForInStep σ))
    (hf : ∀ a s, P s → ∀ s', (f a s = .yield s' ∨ f a s = .done s') → P s') (s : σ) (hs : P s) :
    P (forIn (m := Id) [:n] s f).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact list_forIn_inv P f hf _ s hs

/-! ## Sizes in `binSymColumn` -/

/-- Packing a word array writes eight bytes a word. -/
theorem packLongs_size (a : Array UInt64) :
    (a.foldl (fun acc v => Column.pushBits acc v 8) ByteArray.empty).size = a.size * 8 := by
  rw [← Array.foldl_toList, foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

/-- The needle's ranks are one long per entry of its dictionary. -/
theorem symRanks_snd_size (hb : ByteArray) (ho : Array Nat) (nb : ByteArray) (no : Array Nat) :
    (symRanks hb ho nb no).2.size = (no.size - 1) * 8 := by
  unfold symRanks
  simp only [Id.run]
  show (Array.foldl (fun acc v => Column.pushBits acc v 8) ByteArray.empty (MProd.fst (MProd.snd _))).size = _
  rw [packLongs_size]
  refine congrArg (· * 8) (range_forIn_inv (fun (s : MProd (Array UInt64) (MProd (Array UInt64) UInt64)) => s.snd.fst.size = no.size - 1) _ _ ?_ _ (by simp))
  intro a s hs s' h
  rcases h with h | h <;> (repeat' split at h) <;>
    first | (injection h with h; subst h; simp [hs]) | injection h

/-- `binSymColumn` answers one long per needle: the needle's ranks read straight, or spread through its ids. -/
theorem binSymColumn_size {r : Bool} {xn n : Nat} {xe ne : Enc} {out : ByteArray} (hy : Enc.WF .symbol n ne)
    (hn : n < USize.size) (h : binSymColumn r xn xe n ne = some out) : out.size = n * 8 := by
  have h8 : (8 : USize).toNat = 8 := toNat_small 8 (by decide)
  unfold binSymColumn at h
  rcases symbol_cases hy with ⟨nb, no, rfl⟩ | ⟨d, o, i, rfl⟩
  · simp only [Enc.WF] at hy
    cases xe <;> simp [symKeys] at h <;> subst h <;> simp [binIds, binBytes_size, symRanks_snd_size, h8, hy]
  · cases xe <;> simp [symKeys] at h <;> subst h <;> rw [longsByIds_size, USize.toNat_ofNat_of_lt' hn]

/-! ## `bin` at symbols -/

/-- **`x bin y` answers one long per needle at symbol columns**, blob or interned on either side. -/
theorem binColumn_wf_symbol {r : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)} {v : QValue}
    (_hx : Enc.WF .symbol nx ex) (hy : Enc.WF .symbol ny ey) (hn : ny < USize.size)
    (h : binColumn .symbol r nx ex (.vector .symbol ny ey a) = some v) :
    ∃ e', v = .vector .long ny e' none ∧ Enc.WF .long ny e' := by
  have hc : binColumn .symbol r nx ex (.vector .symbol ny ey a) =
      (binSymColumn r nx ex ny ey).map fun out => .vector .long (out.size / 8) (.bytes out) none := rfl
  rw [hc] at h
  obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.1 h
  exact long_answer (binSymColumn_size hy hn ho)

/-- **`x bin y` answers one long per needle** at every type. -/
theorem binColumn_wf' {t : QAtomicType} {r : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    {v : QValue} (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hn : ny < USize.size)
    (h : binColumn t r nx ex (.vector t ny ey a) = some v) :
    ∃ e', v = .vector .long ny e' none ∧ Enc.WF .long ny e' := by
  by_cases ht : t = .symbol
  · subst ht; exact binColumn_wf_symbol hx hy hn h
  · exact binColumn_wf hx hy ht hn h

end LeetQ.Rel.KernelWF
