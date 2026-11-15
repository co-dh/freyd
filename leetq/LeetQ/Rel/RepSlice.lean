/-
  The slice forms of the class-S list ops (doc/rel-avoid-cons.md §3): each runs as slices of its source's payload,
  `lo`/`hi` index arithmetic with no round and no `cons`, and is read back against the cons-list fold B&dM write it
  as. `prefix`/`suffix` are `inits ∋`/`tails ∋` (`nestMemC`), read back from `rep_initsC`/`rep_tailsC`, `rep_memC`
  and `rep_compC`.
-/
import LeetQ.Rel.CRelList
import LeetQ.Run.CRelListDef

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **`N ∋` under `nestMemC`'s bit**: an array `xs` of `X` goes to each array of the list its nest `N` gives it,
    when `N` gives each array `xs` of `X` exactly the list `g(xs)(k)`, `k = 0 … |xs|`. -/
theorem rep_nestMemC {B : Obj} {n : USize} (N : Vals (.arr B) n → Rel (.arr B) (.arr (.arr B)) × Bool)
    (X : Vals (.arr B) n) (g : List B.El → Nat → List B.El)
    (hN : (N X).2 = true → ∀ xs yss, rep (N X).1 xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map (g xs))
    (hb : (nestMemC N X).2 = true) :
    ∀ xs ys, rep (nestMemC N X).1 xs ys ↔ (∃ j, X.row j = xs) ∧
      ys ∈ (List.range (xs.length + 1)).map (g xs) := by
  simp only [nestMemC, Bool.and_eq_true] at hb ⊢
  obtain ⟨⟨hi, hm⟩, hc⟩ := hb
  have hN := hN hi
  intro xs ys
  rw [rep_compC _ _ hc, comp_apply]
  constructor
  · rintro ⟨yss, h1, h2⟩
    obtain ⟨hx, rfl⟩ := (hN xs yss).1 h1
    exact ⟨hx, ((rep_memC _ hm _ _).1 h2).2⟩
  · rintro ⟨hx, hy⟩
    have h1 := (hN xs _).2 ⟨hx, rfl⟩
    refine ⟨_, h1, (rep_memC _ hm _ _).2 ⟨?_, hy⟩⟩
    rw [rep_apply] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact ⟨i, hi⟩

/-- **`prefix` under `prefixC`'s bit**: an array `xs` of `X` goes to exactly its prefixes, B&dM's
    `prefix = ⦇[nil, nil ∪ cons]⦈` (p.126). -/
theorem rep_prefixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (prefixC X).2 = true) :
    ∀ xs ys, rep (prefixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <+: xs := by
  intro xs ys
  rw [prefixC, rep_nestMemC initsC X (fun xs k => xs.take k) (rep_initsC X) hb]
  refine and_congr_right fun _ => ?_
  simp only [List.mem_map, List.mem_range]
  exact ⟨fun ⟨k, _, e⟩ => e ▸ List.take_prefix k xs,
    fun h => ⟨ys.length, Nat.lt_succ_of_le h.length_le, (List.prefix_iff_eq_take.1 h).symm⟩⟩

/-- **`suffix` under `suffixC`'s bit**: an array `xs` of `X` goes to exactly its suffixes (B&dM p.127). -/
theorem rep_suffixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (suffixC X).2 = true) :
    ∀ xs ys, rep (suffixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
  intro xs ys
  rw [suffixC, rep_nestMemC tailsC X (fun xs k => xs.drop k) (rep_tailsC X) hb]
  refine and_congr_right fun _ => ?_
  simp only [List.mem_map, List.mem_range]
  exact ⟨fun ⟨k, _, e⟩ => e ▸ List.drop_suffix k xs, fun h =>
    ⟨xs.length - ys.length, by omega, (List.suffix_iff_eq_drop.1 h).symm⟩⟩

#print axioms rep_prefixC
#print axioms rep_suffixC

end Rep

namespace CRel

open Rep

variable {B : Obj}

theorem rep_prefix {n : USize} (X : Vals (.arr B) n) (hb : («prefix» X).ok = true) :
    ∀ xs ys, rep («prefix» X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <+: xs :=
  rep_prefixC X hb

theorem rep_suffix {n : USize} (X : Vals (.arr B) n) (hb : (suffix X).ok = true) :
    ∀ xs ys, rep (suffix X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  rep_suffixC X hb

end CRel

end LeetQ.Rel
