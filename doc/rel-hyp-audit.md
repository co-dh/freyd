# rep_* hypotheses that stand in for conclusions

Audit of every `theorem rep_*` signature in `leetq/LeetQ/Rel/Rep*.lean` and `KernelWF/*.lean`, after rows 82-95 of
`doc/rel-done-tasks.md`. Unit: one hypothesis binder, or one bundle reference (`h : consOK`, `hR : roundAt`) counted
once at the theorem that carries it; so a bundle's inner conjuncts are not expanded and the totals are lower bounds.
Excluded: defining equations (`hX : x = ...`), parameters' meaning (`hS`, `hf`, `hE`, `hle`), and class I.

- I = input fact: fit of an input at `List.range n`, bound on input counts, sums, products. Not listed.
- K = kept output-size precondition with a `--` reason comment in the source (cited in the last column).
- O = open: a claim about a kernel's intermediate or output, with no `--` reason comment. Most O rows have a reason
  in a `doc/rel-done-tasks.md` row (cited as "row N"); the source carries none, so the cheapest cut is a comment.

Legend: E3 = E, E_list, arrUnion; E7 = E3, lamOn, lamOn_list, setify, setify_list; S2 = setify, setify_list;
F4 = foldBy_keep, foldBy, foldOn, fold; FR = F4, map, perm, subseq, thinLOn, thinLOn_bump;
RT = thinLOn (2 each), loopOn, loop, mergeOn, merge, suffix, orderedOn, ordered, sortSet (hR only).
Theorem names drop the `rep_` prefix. The mem row counts arrUnion's second hypothesis `hk2` (E3 has 4 there).

| hypothesis shape                   | class | count | theorems                        | reason / derivation          |
|------------------------------------|-------|-------|---------------------------------|------------------------------|
| symDiv output size: hB hC hA hBv.. | K     | 11    | symDiv                          | `-- output size` :682-699    |
| ht63: D.n * 1 < 2^63               | K     | 7     | E7                              | `-- bounded only by` RepE:55 |
| hV hVi hVt: overlapping windows    | K     | 4     | inits, tails, uncat             | `-- kept` RepUncat:173..     |
| nub key codes hF hw hn hs hW h63   | O     | 66    | E7, tau (2), transp (2)         | sublist of R's key codes     |
| union chain hN hFk hFv huK..huv    | O     | 54    | E7 (7 each), leq (5)            | generic razes; arr/sum fit   |
| hK hV hk hv at M = mem X >> R      | O     | 20    | E3, S2                          | M a join output              |
| hc: codesOK at [idU U, dom R]      | O     | 10    | E7, entire, surj, isMap         | dom R keys: sublist of R's   |
| mem positions hk hmk hXk hYk       | O     | 10    | mem, memComp, E3, S2, P         | row 91, 94 "rows repeat"     |
| mS(X) >> R join hcc hcM hcA hcC    | O     | 16    | memComp, E3 (4 each)            | atom: join_pairs_lt          |
| join picks hA hC / hA hB hC        | O     | 5     | comp, pair                      | row 87: atom only            |
| cross picks hA hB / hA..hD         | O     | 6     | top, prod                       | row 94 "top repeats rows"    |
| div joins, vac, razes (20 each)    | O     | 40    | leftDiv, rightDiv               | as symDiv row; no comment    |
| round bundles hR hC hS hran..      | O     | 27    | F4, FR, length, RT              | rows 85, 88, 89              |
| fold result hjO hjn hjM hjA (hjC)  | O     | 49    | FR (5 each), length (4)         | F is the fold output         |
| hB: generic seed fit at cross      | O     | 5     | F4, length                      | row 91: generic seed         |
| initOK: initial merge state        | O     | 2     | mergeOn, merge                  | built by the kernel          |
| bundle binder h: consOK catOK..    | O     | 4     | cons_ok, cat_ok, uncat_ok, snoc | repeats the base O           |
| nil, cons counts; raze fit; consOK | O     | 4     | alpha                           | counts of kernel outputs     |
| consOK cmpOK initsOK uncOK at C    | O     | 5     | tic                             | C = cons P computed          |
| ordering bundles h, hq, hc         | O     | 6     | orderedOn, ordered, sortSet     | suffix pieces                |
| thin sets hSv hSk hcQ..hiG         | O     | 9     | thinL_sets                      | at computed St = setify      |
| subOK thinOK setOK hWf             | O     | 6     | thinL_sublist, thinL            | subseq/setify pieces         |
| est/thin/swap h hsw hq.. hi        | O     | 17    | pairsIn..thin, P                | cmpOK/diffOK at ran G        |
| whereBits positions hKf hVf        | O     | 4     | uncons, tail, elR (2)           | row 95: hKf kept             |
| razed cells hRf hFf                | O     | 4     | cons, cat                       | rows 93, 95: generic B       |
| codesL of computed valCol          | O     | 2     | succ, length                    | s = valCol Add U 1           |
| oneOK at the nub hS                | O     | 3     | simple, injective, isMap        | codes of nub keys            |
| pairsOK, fits at computed L        | O     | 6     | lt, leq                         | count-built L                |
| raze rows hA hB hC hF, union fits  | O     | 14    | union, union_full, junc (2)     | _full keeps RazeFits         |
| uncat hk* hS' hU' hj* hv hk        | O     | 15    | uncat                           | inits/tails/zip joins        |

Theorems with no non-input hypothesis: arith (arith, plus, minus, times, div, mod), apply, conv, zero, idU, outl, outr,
nil, num, atPos, unsnoc, zip, nub, antiJoin, dom, ran, dom_corefl, ran_corefl, sum, inl, inr, distinctCorefl, inter,
diff, le, eq, bagify.

measured: 22 kept, 409 open, 431 total non-input total; open share 94.9%
