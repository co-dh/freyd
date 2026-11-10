/-
  What `monColumn` answers, read off by `Option.get`: the type it claims is `monResultType`'s, never a
  general list.
-/
import LeetQ.Rel.KernelWF.Dyad

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel

/-- No monadic map answers a general list from an operand that is not one (`negType` keeps `general`). -/
theorem monResultType_ne_general {name : String} {t rt : QAtomicType} (h : monResultType name t = some rt)
    (hg : t ≠ .general) : rt ≠ .general := by
  rintro rfl
  unfold monResultType at h
  split at h <;> cases t <;> simp_all [negType, kernelFloorType, Prim.nonNumeric, Option.bind_eq_bind]

/-- The answer `monColumn` claims is at the type `monResultType` names. -/
theorem monColumn_get {name : String} {t rt : QAtomicType} {n : Nat} {e : Enc}
    (hrt : monResultType name t = some rt) (hs : (monColumn name t n e).isSome) :
    monColumn name t n e = some (rt, ((monColumn name t n e).get hs).2) := by
  obtain ⟨⟨r1, r2⟩, h⟩ := Option.isSome_iff_exists.1 hs
  have h1 := monColumn_type h
  rw [hrt, Option.some.injEq] at h1
  subst h1
  simp only [h, Option.get_some]

end LeetQ.Rel.KernelWF
