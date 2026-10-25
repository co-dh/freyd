# leetq -> flat QAtomicType, stage 3 handoff

qlean: /data/tmp/flat2/qlean at ca67f3f (built). Build (outside sandbox, from worktree root):
`CAP_MEM_MB=28000 ./scripts/cap lake -R -d leetq -K qlean=/data/tmp/flat2/qlean build LeetQ.Rel.Scan ...`

Done (Core, Ew, Find build; axioms within {propext, Classical.choice, Quot.sound})
- Core: `abbrev El := Carrier`; `El.ofCarrier` gone; `Arr.get` matches `t`; `get_ne` restated with `default`.
  New: `Arr.c_eq (x : Arr t n) (h : x.c.enc = e) : x.c = ⟨t, n, e⟩` (use wherever a kernel matches
  `⟨_, n, .bits b⟩`), `packLongs_size`, `foRLongs_wf xs` (the WF proof of a check's `foR` column, since
  `decide` cannot evaluate `Coc.encode`: `wf := ⟨rfl, rfl, foRLongs_wf [5, 3, 9]⟩`). Imports
  `QLean.Dep.Monadic`, `QLean.Verify.Alp`.
- Ew: `elem` splits `a = .general` first: `rw [dif_neg (by decide), dif_neg (by decide)]`.
- Find: all definitions, laws and checks ported. Patterns that worked:
  - `cases he : x.c.enc with | bytes b => ... x.c_eq he`;
  - `Column.count .long x.c` -> `x.c.n`; `Column.bytesOf .long c` -> `Column.bytesOf c`;
  - kernel answers `.vector .long (.bytes o)` -> `.vector ⟨.long, o.size / 8, .bytes o⟩`;
    in a `change`, write `⟨.long, _, .bytes (...)⟩`;
  - needles `.vector .long y.c` -> `.vector y.c`;
  - `vec` now checks `c.ty == a`: add `beq_self_eq_true, ↓reduceIte` to the `simp only`;
  - a `rfl` that a kernel's `⟨.symbol, _, _⟩` pattern blocks: `by rw [y.c_eq rfl]; rfl`;
  - check columns `{ c := ⟨.long, 3, .bytes (packLongs [..])⟩, wf := by decide }`.

Restated laws so far
- `Arr.get_ne` (RHS `getD default`); `findColumn_long`, `memberColumn_long`, `binColumn_long`,
  `bytesOf_long`, `findSorted_long`, `memberSorted_long` take `c.ty = .long`; `direct_some` gives
  `c.enc = .foR md pk ∧ c.n = k`; `longWords_foR` over `⟨.long, n, .foR md pk⟩`; `readable_bits` gives
  `∃ b, c.enc = .bits b`; `Arr.toList_bits`, `find_bits`, `in_bits`, `distinct_bits` take `x.c.enc = .bits b`
  (the count argument is gone: the header carries it); `Readable` reads `c.enc`.

Left
- Scan: 101 errors in /data/tmp/flat2/s1.log. Definitions first: `offs` (line 52, `Column.bytesOf o.c`),
  `countBy`/`lastBy`/`overBy` (64-81: `(.bytes s)` -> `⟨.long, s.size / 8, .bytes s⟩`, `overColumn .lesser
  .long ⟨...⟩`), `avg` (43: `Carrier.of? .float` now takes a `QValue`: `fun a => Carrier.of? .float a`
  or the atom form, check the signature); then `Column.admits`/`Column.count` (Arr.of's check is now
  `c.ty = t ∧ c.n = n ∧ c.WF`) at 317-318, 419, 438, 479, 678; checks 812-816.
- Then Struct (also has `Column.admits`/`Column.count` at 1136 and old foR checks at 1143), Algebra,
  Compressed, QRel, Bench.
- Scan: DONE, builds, all `#guard`s pass, axioms within the set. Patterns:
  - `Carrier.of? .float` takes a `QValue`: `fun a => Carrier.of? .float (.atom a)`;
  - an `Arr.of` branch: `rw [Arr.of] at h; split at h` then `· rename_i hw …` / `· rename_i hw; cases h`
    (no need to write the 3-part condition). Where `simp` left an outer `match` on `.toOption`
    (sort, overBy): `split at h; · cases h; rename_i A hA; rw [show A = S by cases h; rfl] at hA; split at hA`;
  - a kernel answer whose header is `m.toNat` or `min n cn`: state it as `∃ k, … ⟨.long, k, .bytes P⟩`,
    proved by `exact ⟨_, rfl⟩` (grade, gather);
  - mwin answers carry `n`, not `size / w`, in the header, while `longWords_answer`/`toList_answer_int`
    want `size / w`: rewrite the header with `foldl_push_size` (Scan; any `List.range m` fold of
    `pushBits … ow` is `m * ow` bytes, from `Verify.foldl_pushBits`) after unfolding `Scan.mwinExt`/
    `Scan.mwinSum`; `sizes_size` does the same for `Ew.val … vv` (unfold `Ew.val`, `rfl`);
  - a hand-built `Arr` needs `WF` = `size = n * w` now: `wf := ⟨rfl, rfl, hsize⟩`;
  - a `let Z : Arr … := { c := …,` NEWLINE `wf := … }` fails to parse in a tactic block: keep it on one line.
  Restated in Scan: `hc`/`ho` hypotheses `x.c = .bytes b` -> `x.c.enc = .bytes b` (`denseElems_long`,
  `over_bytes`, `offs_get`, `overBy_bytes`); `toList_answer_long` takes `Column.answer ⟨.long, b.size/8,
  .bytes b⟩`; `mwin_long`/`mwin_answer` answer `Column.answer ⟨rt, n, .bytes (mwinBits …)⟩`.
- Bench results-identical check vs /data/tmp/ck/bench-4238 at n=100000, then timings.
