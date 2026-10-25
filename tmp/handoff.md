# leetq -> flat QAtomicType, stage 2 handoff

qlean: /data/tmp/flat2/qlean at ca67f3f (built). Build (outside sandbox, from worktree root):
`CAP_MEM_MB=28000 ./scripts/cap lake -R -d leetq -K qlean=/data/tmp/flat2/qlean build LeetQ.Rel.Find ...`

Done
- Core: `abbrev El := Carrier`; `El.ofCarrier` gone; `Arr.get` matches `t` (general reads `.gen`, else
  `(Column.get x.c i).bind (fun a => Carrier.of? t (.atom a))).getD default`); `get_ne` restated with
  `default`. New `Arr.c_eq (x : Arr t n) (h : x.c.enc = e) : x.c = ⟨t, n, e⟩` — use it wherever a kernel
  matches `⟨_, n, .bits b⟩`. Imports `QLean.Dep.Monadic` for `Inhabited (Carrier t)`.
- Ew builds (`elem` now splits `a = .general` first: `rw [dif_neg (by decide), dif_neg (by decide)]`).
- Find: definitions ported (`list` uses `c.n`, `vec` checks `c.ty`, answers built as `⟨ty, n, .bytes b⟩`),
  `where_toList` ported.

Left
- Find proofs (~100 errors): `Readable` must match `c.enc`; every `cases hc : x.c with | bytes b` becomes
  `cases he : x.c.enc with | bytes b` + `x.c_eq he`; column-level lemmas (`bytesOf_long`, `findSorted_long`,
  `memberSorted_long`, `findColumn_long`, `memberColumn_long`, `binColumn_long`, `longWords_foR`,
  `direct_some`) need the header (`c.ty = .long`) or a `⟨.long, n, enc⟩` column; `.vector .long (.bytes b)`
  becomes `.vector ⟨.long, b.size / 8, .bytes b⟩`; checks section `{ c := .bits 5 … }` becomes `⟨.boolean, 5, .bits …⟩`.
- Then Scan, Struct, Algebra, Compressed, QRel, Bench; bench comparison vs /data/tmp/ck/bench-4238.
