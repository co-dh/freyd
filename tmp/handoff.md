Done: leetq/LeetQ/QRel.lean generalised (dense keys/values at any width 1..8 via `atW`, `narrow`; `QSortedRel V`
with a value reader `val : Nat → V`; `ofList l col foR`, `rep_ofList l col hcol foR`); it compiles alone.
Left: L1.lean adapt (`QSortedRel Int64`, `ofList (ixL xs) dense foR`, `rep_ofList _ _ dense_get`, drop its
`lt_usize`/`toNat_toUSize` now in QRel, kernel-run simp sets: `at8` -> `atW`, plus `narrow`); new Cols.lean
(bits as RelRep.test, syms as RelRep.enum, alp float values as `QSortedRel Float`); lake build; commit.
