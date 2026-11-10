/-
`Parted`'s boundary with q's nested list: `box` (the flat form as one vector per group) and `ofBoxes`
(the parser back, where q data is loaded). Apart from `Core` because `box` reads `sliceColumn`'s
answer from `KernelWF`, which imports `Core`.
-/
import LeetQ.Rel.KernelWF.Shape

namespace LeetQ.Rel

open QLean QLean.Dep

namespace Parted

variable {v : QAtomicType}

/-- Group `r`'s values `val[o[r] … o[r+1]-1]` as a q value: `sliceColumn` at an atom type, which answers
    on every well-formed payload whose count fits a `USize`; the general list's elements otherwise. -/
def slice (P : Parted v) (r : Fin P.g) : QValue :=
  let lo := (P.o.get r.castSucc).toNatClampNeg; let hi := (P.o.get r.succ).toNatClampNeg
  if hg : v = .general then by
    subst hg; exact .general (Array.ofFn fun i : Fin (min hi P.n - lo) => P.val.get ⟨lo + i, by have := i.2; omega⟩)
  else if hc : P.n < USize.size then
    .vector v (hi - lo) ((Kernel.sliceColumn v P.n P.val.enc lo (hi - lo)).get
      (KernelWF.sliceColumn_isSome P.val.wf hg (KernelWF.countFits_of_lt hc) lo (hi - lo))) none
  else
    -- a count past `USize` is no input a process holds, and `sliceColumn`'s `USize` arithmetic would wrap
    -- there; the same slice is read through the atoms and rebuilt by `Enc.ofAtoms`
    let as := (Enc.atoms v P.n P.val.enc).extract lo hi
    .vector v as.size ((Enc.ofAtoms v as hg).get (Column.ofAtoms_isSome hg fun a h => by
      obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 h
      exact Column.atoms_type _ _ _ _ (Array.getElem_mem _))) none

/-- q's nested list: one vector per group, each its own slice. -/
def box (P : Parted v) : Arr .general P.g := Arr.mk (.gen (Array.ofFn P.slice)) (by simp [Enc.WF])

/-- The parts of a nested list as each part's count and one flat vector: `raze` of the vectors at an
    atom type, the concatenated lists at `.general`; a part of another shape is declined. -/
def razeParts : QAtomicType → Array QValue → Except String (Array Nat × QValue)
  | .general, xs => do
    let ls ← xs.mapM fun | .general ys _ => pure ys | _ => throw "razeParts: a general part that is not a list"
    pure (ls.map (·.size), .general (ls.foldl (· ++ ·) #[]))
  | t, xs => do
    let cs ← xs.mapM fun | .vector t' n e _ => if t' == t then pure (n, e) else throw "razeParts: a part of another type"
                          | _ => throw "razeParts: a part that is not a vector"
    -- no parts is `t`'s empty vector, which `razeColumn` declines for want of a part to read `t` from
    let some c := (if cs.isEmpty then
        (if h : t = .general then none else (Enc.ofAtoms t #[] h).map (.vector t 0 · none))
      else Kernel.razeColumn t cs)
      | throw "razeParts: razeColumn declines the parts"
    pure (cs.map (·.1), c)

/-- The flat form of a nested list of `g` parts at `v`: `razeParts`, the offsets their running counts. -/
def ofBoxes (v : QAtomicType) {g : Nat} (b : Arr .general g) : Except String (Parted v) := do
  let .gen xs := b.enc | throw "ofBoxes: a nested list's payload is not .gen"
  let (cnt, c) ← razeParts v xs
  let os := cnt.foldl (fun (s, b) m => (s + m, Column.pushBits b (Int64.ofNat (s + m)).toUInt64 8)) (0, Column.pushBits .empty 0 8)
  let o ← Arr.of .long (g+1) (.vector .long (g+1) (.bytes os.2) none) "ofBoxes"
  let val ← Arr.of v os.1 c "ofBoxes"
  let some P := of? o val | throw "ofBoxes: the running counts are not cuts"
  pure P

end Parted

section Checks

open QLean.Column

-- groups `[0,1) [1,1) [1,3)` of `10 20 30`: the empty middle group owns no position
private def o3 : Arr .long 4 := Arr.mk (.bytes <| packLongs [0, 1, 1, 3]) (by decide)
private def v3 : Arr .long 3 := Arr.mk (.bytes <| packLongs [10, 20, 30]) (by decide)
-- `box` then `ofBoxes` is the identity on the flat form, and each box is q's vector of its slice
#guard match Parted.of? o3 v3 with
  | some P => (match (P.box.toList[1]? : Option QValue) with | some (.vector t n _ _) => t == .long && n == 0 | _ => false) &&
      match Parted.ofBoxes .long P.box with | .ok Q => Q.toList == P.toList | .error _ => false
  | none => false

end Checks

end LeetQ.Rel
