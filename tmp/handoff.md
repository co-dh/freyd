# raze-row handoff (checkpoint at 40 calls)

Done (builds, `lake build LeetQ.Rel.KernelWF.RazeRowN` exit 0):
- leetq/LeetQ/Rel/KernelWF/RazeRowN.lean: helpers extract_foldl, off_map, off_mapIdx, row_congr, get_congr,
  razeTo_getN, razeTo_toList_mapIdx, razeTo_toList_bit, side_read_at; `raze_rowN` atom/prod/arr cases.

Left:
1. `raze_rowN` `.sum` case (currently `sorry`): bit gives hf (ls/rs sums < USize), 2^63 bounds, `cs₀.all fitsN`
   (-> pickFits_of_fitsN -> held_row), IH on ls/rs. Use razeTo_getN for tags (razeTo_toList_boolean) and
   positions (razeTo_toList_mapIdx, place output is bytes by rfl), place_off_get, row_sum_eq, held_side,
   side_read_at. Watch omega atom spelling: `(·.1.toNat)` vs `fun c : Part b => c.1.toNat` differ.
2. Bits.lean codeAll: guard `(Vals.pickC A all firsts _ _).2` (pickPart = pickC .1 in need form); PickOf/Inv
   record it; pickC_fits gives PickFits.
3. pickOf_row discharged -> corollary `codeAll ... → row = uOf`.
4. Merge master (b25990c), update BitsSpecRun.lean:220 destructuring `⟨-, hany, hcol, -⟩` if Inv grows.
5. Sudoku: before = 1.03 s wall (lean --setup run).
