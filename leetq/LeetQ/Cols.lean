/-
  qlean's other column constructors as freyd relations. A dense integer column of any width is a
  `QSortedRel` already (`QRel.lean`'s `atW`, `narrow`); here are runs of it at `short` and `int`. A
  boolean `bits` column and its `where` kernel are in `Group.lean`. A `syms` column is `RelRep.enum` from a symbol to the indices
  holding it, and the `?` kernel answers its least one. An `alp` float column is a value reader of a
  `QSortedRel Float`, so `lookup_rep` holds of it as of every other.
-/
import LeetQ.QRel

namespace LeetQ.Cols

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ

/-! ## `short` and `int` keys and values

`QSortedRel.ofList` lays both columns out at their narrowest width. A needle outside the key width is
answered without a search (`Keys.bin`), which `bin_spec` covers. -/

/-- Keys and values that fit `short`. -/
def shortL : List (Int64 × Int64) := [(300, 1), (-7, 2), (300, 3), (12, 4)]

/-- Keys that fit `int` and no narrower, values that fit `short`. -/
def intL : List (Int64 × Int64) := [(100000, 5), (-100000, 6), (100000, 7)]

theorem sortShort : shortL.mergeSort QSortedRel.keyLE = [(-7, 2), (12, 4), (300, 1), (300, 3)] := by
  simp [shortL, List.mergeSort, QSortedRel.keyLE]
theorem sortInt : intL.mergeSort QSortedRel.keyLE = [(-100000, 6), (100000, 5), (100000, 7)] := by
  simp [intL, List.mergeSort, QSortedRel.keyLE]

/-- The key width `ofList` chose. -/
def keyWidth : Keys → Nat
  | .dense w _ => w
  | .foR _ _ _ => 8

example : keyWidth (QSortedRel.ofList shortL dense).keys = 2 := by
  simp only [QSortedRel.ofList, Keys.ofList, sortShort, Bool.false_eq_true, false_and, ↓reduceIte]; decide +kernel
example : keyWidth (QSortedRel.ofList intL dense).keys = 4 := by
  simp only [QSortedRel.ofList, Keys.ofList, sortInt, Bool.false_eq_true, false_and, ↓reduceIte]; decide +kernel
example : (QSortedRel.ofList shortL dense).lookup 300 = [1, 3] := by
  simp only [QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, QSortedRel.ofList, QSortedRel.count,
    Keys.ofList, Keys.bin, Keys.count, Bool.false_eq_true, false_and, ↓reduceIte, sortShort]
  decide +kernel
-- 70000 fits no `short`: answered above every key, without a search.
example : (QSortedRel.ofList shortL dense).lookup 70000 = [] := by
  simp only [QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, QSortedRel.ofList, QSortedRel.count,
    Keys.ofList, Keys.bin, Keys.count, Bool.false_eq_true, false_and, ↓reduceIte, sortShort]
  decide +kernel
example : (QSortedRel.ofList intL dense).lookup 100000 = [5, 7] := by
  simp only [QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, QSortedRel.ofList, QSortedRel.count,
    Keys.ofList, Keys.bin, Keys.count, Bool.false_eq_true, false_and, ↓reduceIte, sortInt]
  decide +kernel

-- The compiled run: `binBytes` is the C `bin` at widths 2 and 4.
#guard keyWidth (QSortedRel.ofList shortL dense).keys == 2
#guard keyWidth (QSortedRel.ofList intL dense).keys == 4
#guard (QSortedRel.ofList shortL dense).lookup 300 == [1, 3]
#guard (QSortedRel.ofList shortL dense).lookup 70000 == []
#guard (QSortedRel.ofList shortL dense).lookup (-70000) == []
#guard (QSortedRel.ofList shortL dense).lookup (-7) == [2]
#guard (QSortedRel.ofList intL dense).lookup 100000 == [5, 7]
#guard (QSortedRel.ofList intL dense).lookup 99999 == []

/-! ## A `syms` column: symbol ↦ its indices -/

/-- The indices whose symbol's bytes are `s`'s UTF-8. Bytes are compared, never decoded, so
`String.fromUTF8?`, which `Column.atoms` reads symbols through, is not reached. -/
def symFib (blob : ByteArray) (offs : Array Nat) (s : String) : List Nat :=
  (List.range (offs.size - 1)).filter fun i => (symKey blob offs i).data == s.toUTF8.data

/-- A symbol column as `RelRep.enum`: each symbol's fibre is the indices holding it. -/
def symRel (blob : ByteArray) (offs : Array Nat) : RelRep String Nat := .enum (symFib blob offs)

/-- **`s` relates to `i` exactly when symbol `i` is `s`.** -/
theorem rel_symRel (blob : ByteArray) (offs : Array Nat) (s : String) (i : Nat) :
    (symRel blob offs).rel s i ↔ i < offs.size - 1 ∧ symKey blob offs i = s.toUTF8 := by
  show i ∈ symFib blob offs s ↔ _
  simp only [symFib, List.mem_filter, List.mem_range, beq_iff_eq]
  exact and_congr_right fun _ => ⟨ByteArray.ext, fun h => h ▸ rfl⟩

/-- **The `?` kernel answers the least index of `s`'s fibre**, and the count when it is empty. -/
theorem findSymScalar_spec (blob : ByteArray) (offs : Array Nat) (s : String) (hn : offs.size - 1 < 2 ^ 32) :
    (findSymScalar blob offs s.toUTF8).toNat = ((symFib blob offs s).head?).getD (offs.size - 1) := by
  rw [symFib, List.head?_filter, findSymScalar]
  apply toNat_toUSize
  cases h : (List.range (offs.size - 1)).find? fun i => (symKey blob offs i).data == s.toUTF8.data with
  | none => exact hn
  | some i => have := List.mem_range.1 (List.mem_of_find?_eq_some h); simp only [Option.getD_some]; omega

/-- A symbol list as the column `Column.symsOf` writes. -/
def symCol (ss : List String) : ByteArray × Array Nat :=
  match Column.symsOf (ss.map QAtom.symbol).toArray with
  | .syms blob offs => (blob, offs)
  | _ => (ByteArray.empty, #[0])

def abcab : ByteArray × Array Nat := symCol ["a", "bc", "", "a", "bc"]

#guard symFib abcab.1 abcab.2 "a" == [0, 3]
#guard symFib abcab.1 abcab.2 "bc" == [1, 4]
#guard symFib abcab.1 abcab.2 "" == [2]
#guard symFib abcab.1 abcab.2 "b" == []
#guard (findSymScalar abcab.1 abcab.2 "bc".toUTF8).toNat == 1
#guard (findSymScalar abcab.1 abcab.2 "zz".toUTF8).toNat == 5
#guard (symRel abcab.1 abcab.2).mem "bc" 4

/-! ## An `alp` float column as the values -/

/-- Element `i` of an ALP column, `Column.alpBits`, as the `Float` it denotes. -/
def alpVal (md pk a : ByteArray) (i : Nat) : Float := Float.ofBits (alpBits md pk a (blockStarts md) i)

/-- A list of floats as an ALP value column: their bits laid out dense, then `Coc.alpEncode64`, the
Lean body of `qlean_alp_encode_f64`. -/
def alpCol (vs : List Float) : Nat → Float :=
  let e := Coc.alpEncode64 (enc 8 (vs.map fun x => x.toBits.toInt64))
  alpVal e.1 e.2.1 e.2.2

/-- Prices by id. -/
def prices : List (Int64 × Float) := [(3, 1.25), (1, 0.5), (3, 2.75), (2, 10.0)]

-- `Float` is opaque to the kernel, so this runs compiled only.
#guard (QSortedRel.ofList prices alpCol).lookup 3 == [1.25, 2.75]
#guard (QSortedRel.ofList prices alpCol).lookup 2 == [10.0]
#guard (QSortedRel.ofList prices alpCol).lookup 4 == []
#guard (QSortedRel.ofList prices alpCol true).lookup 3 == [1.25, 2.75]

/-! ## Axioms -/

#print axioms LeetQ.Keys.bin_spec
#print axioms LeetQ.QSortedRel.rep_ofList
#print axioms LeetQ.QSortedRel.lookup_rep
#print axioms LeetQ.dense_get
#print axioms rel_symRel
#print axioms findSymScalar_spec
#print axioms alpCol

end LeetQ.Cols
