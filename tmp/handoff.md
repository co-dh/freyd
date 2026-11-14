rel-74d handoff (checkpoint at call 40)

Done: AppendFoR.append_reads generalised to any tail D (`hTm : D.size / 8 = n1`, else-branch `bitsAt D ((i-n0)*8) 8`).
RazeFoR.concatFoR_reads still uses the old form (broken until the 2-part FoR section is replaced).

Plan: new module KernelWF/RazeParts.lean (imports AppendFoR): range_map_flatten, foldl_arr_*, moveFoR_list,
move_list, append_list, reencode_list, concatFoR_list; then RazeFoR: razeTo_toList_all (n parts, any encoding,
hyp `2 ≤ cs.size → alpEncodes t → S < 2^32`), hat_all from it, delete 2-part FoR chain; then CodesFloatParts:
raze_get (general), float codes via bytesOf, CodesFit numeric clause drops h1/hD.
