rel-74h handoff (checkpoint at call 40)

Done (uncommitted-then-WIP-committed, NOT built):
- merged rel-74d (clean). RazeFoR builds at merge.
- RazeFoR: `hA` weakened to `2 ≤ cs.size → alpEncodes t → S < 2^32` in razeTo_toList_all, hat_all caller,
  raze_get (`2 ≤ p → …`), codes_small_int_parts_faithful.
- CodesGuidParts/CodesLongParts: raze_get_bytes → raze_get, hD dropped; import RazeFoR.
- CodesFloatParts rewritten: float_groups (any encoding: bytes/alp via bytesOf, foR via decode_keyAt),
  ofIds_float_faithful, codes_float_cut/_parts_faithful/_parts_wf without h1/hD, codes_dense_faithful_wf
  (hN, hA), codes_num_one_faithful_wf (f32/f64 without the bytes requirement).

Blocker: import cycle. RazeRow imports RepOps → RepComp (imports CodesFloatParts, CodesGuidParts) and
NubSpec (imports CodesFloatParts); RazeFoR is above RazeRow. So anything using raze_get must sit above.
Plan: CodesFloatParts stays low (import CodesProd; one-part codes_float_one + codes_num_one without
raze_get); new module CodesNumParts (imports RazeFoR) gets codes_float_parts_faithful,
codes_dense_faithful_wf; rep_comp_dense and RepComp's guid theorem move to a new module above
(RepCompParts) so RepComp drops CodesFloatParts/CodesGuidParts imports. Then CodesAll (step 6).
