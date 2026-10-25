# leetq -> flat QAtomicType + Column header (stage 1) — handoff

qlean: /data/tmp/flat/qlean at 8f68875 (master, flat QAtomicType). Build (outside sandbox):
`./scripts/cap lake -R -d leetq -K qlean=/data/tmp/flat/qlean build bench LeetQ.QRel LeetQ.Compressed
LeetQ.Rel.Core LeetQ.Rel.Find LeetQ.Rel.Scan LeetQ.Rel.Ew LeetQ.Rel.Struct LeetQ.Rel.Algebra`.
`QLean.Kernel.SortTest` needs `CAP_MEM_MB=28000` (OOM at 12 GB); it is built now.

Done
- LeetQ/Rel/Core.lean ported and builds: `El` (leetq's own, `.general => QValue`, else `Carrier t`;
  qlean deleted its `El`), `El.ofCarrier`, `Arr.wf : c.ty = t ∧ c.n = n ∧ c.WF`, `Column.admits` deleted,
  `Arr.get_ne`, `Arr.gen_size`; hypotheses `x.c = .bytes b` are now `x.c.enc = .bytes b` (`.foR md pk`,
  `.bits b`, `.enum d o ids`, no count field); `longWords_answer`/`toList_answer_int` state the header
  `⟨t, b.size / w, .bytes b⟩`; `get_sym_bytes` takes `ht : c.ty = .symbol` `hw : c.WF` `hi : i < c.n`.
- sed over all leetq: QVecType -> QAtomicType, `(.atom .x)` -> `.x`, `X (.atom v)` -> `X v` for
  Arr/Parted/Rel/El/..., `QValue.list` -> `QValue.general`, `.wf.2` -> `.wf.2.1` (count is now wf.2.1).

BLOCKER (stopped here): with qlean's current `Carrier .general := Empty`, leetq's `El` cannot be
`Carrier`, and `El t` does not reduce to `Carrier t` for a variable `t`. Every spec stated over a variable
atom type then fails, e.g. LeetQ/Rel/Ew.lean:208 `Ew.ValSpec` — `p.fst has type El t but is expected to
have type Carrier t` (also `Ew.MapSpec`, and the same in Find/Scan). Old `El (.atom t)` was `Carrier t` by
definition. Once qlean has `Carrier .general := QValue` (the user's choice), set `abbrev El := Carrier`
in Core.lean (drop `El.ofCarrier`/the `dite` in `Arr.get`: `get` reads `.gen` at `.general` by matching
`t`), and the specs port unchanged.
Ew.lean is partly ported (atom-only calls take a defaulted `ht : t ≠ .general` last; header columns in
the checks).

Left (error-driven): Ew, Find, Scan (~100 errors each), then Struct, Algebra, Compressed, QRel, Bench.
Recurring fixes: `Column.count t c` -> `c.n`; old `Column` ctors -> `Enc` under `c.enc`, building a column
is `⟨t, n, .bytes b⟩`; `QValue.vector t c` -> `QValue.vector c` (check `c.ty`); `Column.bytesOf t c` ->
`Column.bytesOf c`; `Column.answer t c` -> `Column.answer c`; `Column.get t c i` -> `Column.get c i`;
`Kernel.nullColumn t` needs `t ≠ .general`. Then the bench result comparison against /data/tmp/ck/bench-4238.
