# Read-back coverage of `Alg` ops on `Rel`

Source: `leetq/LeetQ/Rel/Alg.lean` (namespace `LeetQ.Rel.Alg`, all Rel-returning defs), theorems in
`leetq/LeetQ/Rel/Rep*.lean` plus `KernelWF/` (where `rep_union*`, `rep_nub*`, `rep_junc_full` live).
Hypothesis classes: "none" = only size/universe bounds; "witness" = the kernel's intermediate relations and
`PickFits`/`cOK`/`codesOK` facts are passed in as hypotheses (`hX : X = …`); "list" = list-order (not set) read-back.
Hypothesis text for rows 70+ of the theorem list was classified from the signature head, not read in full.

| op (Alg.lean line)          | rep theorems (file:line)                                              | extra hypotheses |
|-----------------------------|-----------------------------------------------------------------------|------------------|
| zero (29)                   | rep_zero (Rep:29)                                                     | none |
| top (42)                    | rep_top (RepOps:355)                           | encoding witness |
| idU (47)                    | rep_idU (Rep:34)                                                      | none |
| convArr / conv (55, 63)     | rep_conv (Rep:25)                                                     | none |
| union ∪ (36, private)       | rep_union (KernelWF/RazeRow:165), rep_union_full (KernelWF/RazeFoR:334) | size/raze-fit hyps; `_full` no encoding hyp |
| inter / diff (24, 89)       | rep_inter (RepOps:570); rep_diff (585) | encoding witness |
| le (19)                     | rep_le (RepOps:634); rep_eq (650) | witness |
| comp (66)                   | rep_comp (RepComp:45) | join-code witness |
| distinctCorefl (73)         | rep_distinctCorefl (RepOps:180)        | witness |
| dom / ran (78, 81)          | rep_dom (238), rep_ran (246), _corefl (252, 258) | witness; corefl variants |
| antiJoin (84)               | rep_antiJoin (RepOps2:56)               | codesOK/PickFits |
| leftDiv (123)               | rep_leftDiv (RepDiv:308)                                              | witness (CodesFit, PickFits) |
| rightDiv (139)              | rep_rightDiv (RepDiv:411)                                             | witness |
| symDiv (146)                | rep_symDiv (RepSymDiv:636)                                            | witness |
| transpose Λ (166)           | rep_transpose (RepLambda:375), rep_transpose_list (457)               | key-code witness; list variant |
| mem (181)                   | rep_mem (RepMem:24)                              | PickFits |
| pair (197)                  | rep_pair (RepOps:712)                                                 | witness |
| outl / outr (205, 207)      | rep_outl (Rep:40), rep_outr (46)                                      | none |
| num (211)                   | rep_num (RepMem:116)                            | `k + n < 2^63`; PickFits |
| prod (225)                  | rep_prod (RepOps:390)                          | witness |
| inl / inr (256, 259)        | rep_inl (91), rep_inr (105)                        | `n ≤ 2^63` |
| junc (264)                  | rep_junc (RepOps:869), rep_junc_full (KernelWF/RazeFoR:346) | witness; `_full` none on encoding |
| sum R+S (273)               | rep_sum (RepOps:27)                           | `n < 2^63` |
| pairsIn (295)               | rep_pairsIn (RepEst:128)                                              | cmpOK on D |
| swapIn (299)                | rep_swapIn (RepEst:148)                                               | witness |
| thinOn / thin (307, 331)    | rep_thinOn (RepEst:263), rep_thin (303)                               | witness chain |
| estOn / est (315, 326)      | rep_estOn (RepEst:173), rep_est (237)                                 | witness chain |
| uncons (336)                | rep_uncons (RepList:30)                                               | `X.1 < 2^63`, witness |
| cons (350)                  | rep_cons (RepList:168), rep_cons_ok (RepPerm:153)                     | size bounds, witness |
| foldBy (390)                | rep_foldBy (RepFold:716), rep_foldBy_keep (606)                       | witness (T, PickFits, rounds) |
| foldOn (403)                | CRel.rep_foldOn (CRelFold:505)                                        | witness |
| fold (409)                  | rep_fold (RepFold:803)                                                | witness |
| map (417)                   | rep_map (RepList:1066)                                                | witness |
| lt (426), leq (436)         | rep_lt (RepOrd:139), rep_leq (164)                                    | needs `t ≠ .general`; witness |
| succ (442)                  | rep_succ (RepArith:280)                                               | `hs`/`hcs` codes witness |
| arith (455)                 | rep_arith (RepArith:174)                                              | none beyond result spec (`exactA`) |
| plus/minus/times/div/mod    | rep_plus (214), rep_minus (221), rep_times (230), rep_div (239), rep_mod (247) | none |
| τ (489)                     | rep_tau (RepPower:43), rep_tau_list (263)                             | witness; list variant |
| nil (493)                   | rep_nil (RepPrim:18)                                                  | none |
| **alpha (497)**             | **MISSING**                                                           | defined as `junc (nil I) (cons (idU P))`; no `rep_alpha`; derivable from rep_junc, rep_nil, rep_cons, rep_idU |
| lamOn (503)                 | rep_lamOn (RepPower:93), rep_lamOn_list (308)                         | witness; list variant |
| E (508)                     | rep_E (RepE:38), rep_E_list (106), rep_memComp (16)                   | witness at `M`; list variant |
| P (514)                     | rep_P (RepEst:436)                                                    | witness |
| tail (518)                  | rep_tail (RepEst:110)                                                 | `X.1 < 2^63`, witness |
| length (522)                | rep_length (RepArith:707)                                             | `X.1+1 < 2^63`, witness |
| suffix (531)                | rep_suffix (RepPerm:519)                                              | witness |
| inits / tails (553, 559)    | rep_inits (RepUncat:164), rep_tails (214)                             | witness |
| cat (567)                   | rep_cat (RepList:929), rep_cat_ok (RepPerm:161)                       | size bounds, witness |
| zip (590)                   | rep_zip (RepPrim:234)                                                 | witness |
| unsnoc (606)                | rep_unsnoc (RepPrim:106)                                              | witness |
| atPos (619)                 | rep_atPos (RepPrim:31)                                                | witness |
| snoc (627)                  | rep_snoc (RepPerm:655)                                                | witness |
| uncat (633)                 | rep_uncat (RepUncat:278), rep_uncat_ok (RepPerm:171)                  | witness |
| perm (642)                  | rep_perm (RepPerm:417)                                                | witness |
| setify (650)                | rep_setify (RepPower:205), rep_setify_list (372)                      | witness; list variant |
| bagify (657)                | rep_bagify (RepOrd:347)                                               | witness |
| orderedOn / ordered (671, 680) | rep_orderedOn (RepSort:50), rep_ordered (180)                      | witness |
| sortSet (685)               | rep_sortSet (RepSort:209)                                             | witness |
| subseq (690)                | rep_subseq (RepSubseq:133)                                            | witness |
| thinL (696)                 | rep_thinL (RepSort:500), rep_thinL_sets (258), rep_thinL_sublist (429) | witness; set/sublist variants |
| thinLOn (708)               | rep_thinLOn (RepThin:448), rep_thinLOn_bump (518)                     | witness |
| mergeOn / merge (727, 747)  | CRel.rep_mergeOn (CRelLoop:324), rep_merge (RepMerge)                 | `le` agrees with `rep Q`, fuel/witness |
| loopOn / loop (755, 767)    | CRel.rep_loopOn (CRelLoop:297), rep_loop (RepLoop)                    | step-function witness `hf` |
| tic (772)                   | rep_tic (RepPerm:190)                                                 | witness |
| Arr.union (782)             | rep_arrUnion (RepEst:23)                                              | witness at `M` (rep_E) |
| Arr.sum (787)               | Arr.rep_sum (RepArith:566)                                            | witness; only for `Obj.long` arrays, no overflow of any prefix sum, no `nul` elements |
| foldRows (372), demandStep (397) | none standalone; read back through CRel.rep_foldOn / rep_foldBy_keep (RepFold 185, 259, 606) | internal helpers, not user ops |
| nest (540, private)         | none standalone; used inside inits/tails                              | internal |

Non-Rel (Bool) ops with read-back: entire (rep_entire RepOps2:125), surjective (135),
simple (216), injective (234), isMap (245). Not Rel-returning: hylo, iter, tags, sumVals, bitsOf, nilVal.

Count: 62 user-facing Rel ops (incl. both-arity groups) checked: 1 MISSING (`alpha`); 0 of the rest have no theorem.
Read-back only under type-specific or "witness" hypotheses everywhere except zero, idU, conv, outl, outr, arith family, nil.
Atom-type-restricted variants exist for comp, antiJoin, dom/ran, distinctCorefl, inl/inr, sum, top, prod, inter, union, num, mem.
