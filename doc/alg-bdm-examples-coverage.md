# The B&dM note's example programs against `Alg`

Audit only. `Alg` read on `master` at `2382c21` (`leetq/LeetQ/Rel/Algebra.lean`, which has `bagify` at :1399). The
note (`diag/aop/06-recursive.typ` … `10-greedy.typ`) prints each program as `#leanf("<decl>")`, so the formula is
the Lean statement of that declaration; the table names it with the note's line, and "Formulas" below gives the
statement verbatim. File names are shortened to their number: `07:1616` is `diag/aop/07-optimisation.typ:1616`.

"Supported" means one relation term over `Alg` ops. Every `°` of a `fold` and every `Λ` is evaluated on a finite
universe of rows (`perm X` for selection sort, the strings of a run for detab), as all of `Alg` is. `cp (a term)`:
`Alg` has no `cp`, but it is a term — on sets `Λ(⟨outl, outr ≫ ∋⟩)`, on lists in order a `loop` that `snoc`s
`(a, x)`. `const`: a constant, `top U (col [k])`. "deleted module?" asks whether the missing piece exists in a module
step 2 deletes (`Find`, `Ew`, `Scan`, `Parted`, `QSort`, the eight `KernelWF` modules).

The table is wider than 120 columns because a table row cannot wrap.

| ch. | example                  | note's formula (file:line)                 | `Alg` ops it uses                                         | missing from `Alg`           | deleted module? |
|-----|--------------------------|--------------------------------------------|-----------------------------------------------------------|------------------------------|-----------------|
| 6   | digits of a number       | `val_converse_eq` 06:23                    | `fold` `°` `∪` `junc` `snoc` `plus` `times`               | —                            | no              |
| 6   | fast exponentiation      | `exp_program` 06:165, `mod_program` 06:177 | `fold` `°` `plus` `times` `minus` `leq` const            | —                            | no              |
| 6   | selection sort           | `selection_sort` 06:316                    | `fold` `°` `perm` `uncons` `leq` `est`                    | — written: `leetq/programs/selsort.rel`; differs from the note: `[nil, select°]` is the seed `ran(e)` and step `ok cons perm` (`select°` of a demand term is refused), `ok` is `𝟙 − dom(⟨π₁,π₂∋⟩(π₁∼R ∩ π₂))` (`R/∋` is refused), the fold runs on `C`, the rearrangements of the inputs | no              |
| 6   | quicksort                | `quicksort` 06:350                         | `perm` `ordered` (the spec only)                          | trees (declined)             | no              |
| 6   | closure                  | `star_eq_mu'` 06:486                       | `𝟙` `∪` `≫`                                               | `μ`                          | no              |
| 7   | takewhile                | `takewhile_eq_cata` 07:428                 | `takewhile` `fold` `prefix` `est` `length` `leq`          | —                            | no              |
| 7   | mss                      | `mss_eq_scan` 07:688                       | `inits` `tails` `concat` `Arr.sum` `plus` `est` `leq`     | —                            | no              |
| 7   | filter                   | `filter_eq_cata` 07:886                    | `filter` `subseq` `fold` `est` `length` `leq`             | —                            | no              |
| 7   | company party            | `party_laws` 07:1398                       | `Λ` `est` `Arr.sum` `leq` `map` `concat`                  | trees (declined)             | no              |
| 7   | shortest paths, cylinder | `cyl_laws` 07:1616                         | `fold` `zip` `concat` `uncons` `snoc` `Λ` `est` `Arr.sum` | `cp` (a term)                | no              |
| 7   | security van             | `van_laws` 07:2042                         | `fold` `cons` `prefix` `Arr.sum` `est` `leq` `Λ` `minus`  | —                            | no              |
| 8   | layered network          | `thinning_paths` 08:350                    | `fold` `Λ` `P` `est` `∋` `plus` `leq`                     | —                            | no              |
| 8   | knapsack                 | `knap_laws` 08:702                         | `fold` `subseq` `merge` `thinL` `est` `Arr.sum` `leq`     | `cp` (a term)                | no              |
| 8   | paragraph                | `para_laws` 08:873                         | `fold` `cat` `thinL` `est` `Arr.sum` `length` `leq`       | —                            | no              |
| 8   | bitonic tours            | `tour_laws` 08:1067                        | `fold` `cat` `thinL` `est` `plus` `Arr.sum` `leq`         | `cp` (a term)                | no              |
| 9   | string edit              | `edit_X` 09:485; `column_cons` 09:603      | `thin` `Λ` `P` `est` `length` `leq`; `fold` `zip` `tails` | `μ` (not in tabulation)      | no              |
| 9   | optimal bracketing       | `mct_laws` 09:749; `array_cons` 09:951     | `tic` `loop` `zip` `inits` `tails` `est`                  | trees (declined)             | no              |
| 9   | data compression         | `code_laws` 09:1060                        | `thin` `Λ` `P` `est` `prefix` `cat` `snoc` `Arr.sum`      | `μ`                          | no              |
| 10  | detab-entab              | `entab_laws` 10:148; `entab_triple` 10:259 | `fold` `loop` `snoc` `cat` `length` `idU` `mod` `minus`   | —                            | no              |
| 10  | minimum tardiness        | `tardy_laws` 10:463                        | `bagify` `Λ` `est` `snoc` `Arr.sum` `plus` `leq`          | `μ`                          | no              |
| 10  | TeX                      | `tex_laws` 10:607; `f_cons` (Lean)         | `Λ` `est` `cons` `length` `lt` const                      | `μ`                          | no              |

Notes on single rows:

- Fast exponentiation: the note's `μX : …` has the base functor of a list of bits, so it is
  `⦇[zero,shift]⦈° ⦇[one,op(a)]⦈` on bit arrays, a `fold` after the converse of a `fold`; no `μ` is needed.
  `shift°` (halve, keep the bit) is the `°` of `shift = 2n+d`, so no `div`/`mod` either. Digits likewise: `op°` is
  the `°` of `op(n,d) = 10n+d`.
- String edit: the recursive form `edit_X` needs `μ`; the tabulation (09:596-603, `column(xs) = ⦇[fstcol,nextcol]⦈`,
  `nextcol` a fold over `zip(xs, zip(init(us), tail(us)))`) is `fold`, `zip`, `tails`, `init`, `tail`, `est` on
  `length`; `nextcol(xs)(b, …)` depends on `b`, which a `loop` carries in its state.
- Detab-entab: `entab_laws` is a `μ`, but the note's final program `entab_triple` is `triple ⦇…⦈` (`triple_fold`)
  then `assocl π₁ (𝟙×blanks) cat`: a fold. `fill` pads `n − col mod n` blanks (`AOP/A10_2_Detab.lean:64`).
- Minimum tardiness: `bagify` is on `master`. The greedy `μ` recurses on the bag; no fold form is in the note.
- TeX: the Lean program (`AOP/A10_4_Tex.lean`, `Prog.f_cons`) is on integers: an interval `(p,q)` scaled by
  `w = 2¹⁷`, the digit `10q/w`, the next interval `(10p − w·d, 10q − w·d)`. So no rational object is needed, but it
  is an unfold with no list input: `μ`.
- Trees, declined. Quicksort: the formula unfolds into a binary tree and flattens it; the base functor is a tree's, so
  there is no array spelling of it; its spec `perm ordered` is `sort`, a term. Company party: the formula folds a
  rose tree `node(A,[tree A])`; on arrays only by a different formula (e.g. a post-order array folded by `loop` with a
  stack), which is not the note's. Optimal bracketing: the tabulation (`array_cons`, `tic`, `loop`, `zip`) is on
  arrays, but `mix ≜ zip bin′ minL(R)` builds `bin` nodes; a cost-only table of numbers is an array formula and still
  needs `times` (the run at 09:985 costs `rows·shared·columns`).

## Formulas

The statements the note prints (Lean, from `.lake/build/refactor-index.db`, namespaces dropped):

```
val_converse_eq  : val° = embed° ≫ wrap ∪ op° ≫ timesDigit.map val° ≫ snoc
exp_program      : mu (fun X => (zero° ≫ one) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ Exp.op a)) ⊑ exp a
mod_program      : mu (fun X => (zero° ≫ zero) ∪ (shift° ≫ rprodMap X (𝟙 (dE Bit)) ≫ Modulus.op b)) ⊑ mod b
selection_sort   : (⦇junc … τ select°⦈)° ⊑ perm ≫ ordered R
quicksort        : (⦇junc … τ split° : Alg (TB.F A) (dList A)⦈)° ≫ flatten ⊑ perm ≫ ordered R
star_eq_mu'      : star R = mu (fun X => Cat.id A ∪ (X ≫ R))
takewhile_eq_cata: takewhile p = cataR (consScalarAlg (fun _ => ConsList.wrap ()) (twStep p))
mss_eq_scan      : mss = ⦇k⦈ ≫ graph (fun p => p.2) ≫ est(geq)
filter_eq_cata   : filter p = cataR (consScalarAlg (fun _ => ConsList.wrap ()) (fStep p))
party_laws       : ⦇rpair (graph «include») (graph Prod.snd ≫ list (Λ choose ≫ est((R rating)°)) ≫ concatR)
                     : Alg (RT.F A) _⦈ ≫ Λ choose ≫ est((R rating)°) ⊑ Λ party ≫ est((R rating)°)
cyl_laws         : Qfold costLE m ≫ est (costLE (m + 1)) ⊑ graph paths ≫ est (costLE (m + 1))
van_laws         : ⦇progAlg⦈ ⊑ Λ (partition ≫ list secure) ≫ est R
thinning_paths   : relCata (Λ (F.map ∋ 𝟙) ≫ powerRel (Λ (F.map 𝟙 ∋ ≫ alphaR) ≫ est R)) ≫ est R
                     ⊑ Λ (relCata (F.map ∋ 𝟙 ≫ alphaR)) ≫ est R
knap_laws        : ⦇cpL ≫ pair g₁ g₂ ≫ merge (R val) ≫ thinL (Q val wt)⦈ ≫ minL (R val)
                     ⊑ Λ (subseq ≫ corefl (within w)) ≫ est (R val)
para_laws        : ⦇cpL ≫ pair g₁ g₂ ≫ merge ⊤ ≫ thinL (Q w)⦈ ≫ minL R ⊑ Λ (partition ≫ fits w) ≫ est R
tour_laws        : ⦇cpL ≫ pair g₁ g₂ ≫ cat ≫ thinL Q⦈ ≫ minL R ⊑ Λ tour ≫ est R
edit_X           : mu (fun X => (empty ≫ base° ≫ τ) ∪ (ran step ≫ Λ (step°) ≫ thinRel (rprodMap ⊤ V)
                     ≫ powerRel (rprodMap 𝟙 X ≫ consR) ≫ est R)) ⊑ Λ ((graph edit)°) ≫ est R
mct_laws         : mu (fun X => Λ ((graph wrapCatFn)°) ≫ powerRel ((TT.F A).map X ≫ graph con) ≫ est R)
                     ⊑ Λ ((graph flatten)°) ≫ est R
code_laws        : mu (fun X => Λ ((junc nil extend)°) ≫ thinRel Q ≫ powerRel ((F Unit Code).map X
                     ≫ junc nil snoc) ≫ est R) ⊑ Λ (decode°) ≫ est R
entab_laws       : mu (fun X => Λ ((junc nil expand)°) ≫ est Q ≫ (F Unit Char).map X ≫ junc nil snoc)
                     ⊑ Λ (detab°) ≫ est R
entab_triple     : entab = triple ≫ assocl ≫ π₁ ≫ rprodMap 𝟙 blanks ≫ cat
tardy_laws       : mu (fun X => Λ (bagAlg°) ≫ est Q ≫ (F Unit Job).map X ≫ graph con) ⊑ Λ (bagify°) ≫ est R
tex_laws         : interval ≫ mu (fun X => Λ ((junc cop arb step)°) ≫ est Q ≫ (F Unit Digit).map X ≫ alphaR)
                     ⊑ Λ (intern°) ≫ est R
```

## Missing primitives

Done on branch `alg-arith`: `arith op W : Rel (long × long) long` (`Algebra.lean`, before `plus`) is one
`QLean.Kernel.Ew.val op Ew.i64 Ew.vv` over the pairs `W`, and `plus`, `times`, `minus`, `div`, `mod` are its
`Ew.add`, `mul`, `sub`, `idiv`, `imod` instances. It is partial, never a default: no row where the kernel answers
q's null (a null operand, a zero divisor) and no row where the answer wrapped (a `+`/`-` whose order against `u`
disagrees with `v`'s sign, a `*` that `idiv u` does not take back to `v`). `div`/`mod` floor as q's do: `mod` has
the divisor's sign. Guards in `section Checks` hold all five against `Int` on `-7 … 7` squared and on the edges of
`long`, `minus` against the converse reading of `plus`, and `u = v·div + mod` with its bounds. The deleted
wrapper of all of them is leetq's `Ew.val` (`Ew.lean:45`), which answers `Except String (Arr rt n)`: not total, so the Rules forbid `Alg` from
calling it, and nothing is lost by deleting it.

| primitive              | examples                                                                 | qlean kernel                           | wrapper in a deleted module, total?                          |
|------------------------|--------------------------------------------------------------------------|----------------------------------------|--------------------------------------------------------------|
| `times` (done)         | digits, fast exp, paragraph (`sqr`), bracketing (`cb`), tardiness, TeX   | `Ew.mul`: `arith Ew.mul`               | `Ew.val .mul` (Ew.lean:45): `Except`, no                     |
| `minus` (done)         | fast exp (`mod`), van, paragraph, detab, tardiness, TeX                  | `Ew.sub`: `arith Ew.sub`               | `Ew.val .sub`: `Except`, no                                  |
| `div`, `mod` (done)    | detab (`col mod n`), TeX (`10q/w`)                                       | `Ew.idiv`, `Ew.imod`: `arith`          | `Ew.val`: `Except`, no                                       |
| `max`/`min` (done)     | van (`bmax`), tardiness (`bmax`)                                         | none: the term, guarded                | `Ew.val`, `Scan.mwin` (Scan.lean:120): `Except`/`Option`, no |
| `≤`/`<` from a cost    | every optimisation example: `cost ≫ leq U ≫ cost°`                       | `gradeColumn` via `Ops.rank`           | `Ops.rank` (Scan.lean:151): step 2 moves it to `Core`, kept  |
| constants              | `0`, `N`, `w`, `n`, `c`, `p`, `10`, `2¹⁷`                                | none                                   | none                                                         |
| `exp`                  | only the fast-exp spec `exp(a)(b) = a^b`; the program needs `times` only | `Ew.pow`                               | `Ew.val`: `Except`, no                                       |
| prefix sums            | mss, van (`prefix sum`)                                                  | `Scan.scan .sums` (Algebra.lean:55)    | leetq `Scan.scan` (Scan.lean:38): `Option`, no               |

- Present, no new op: `≤`/`<` from a cost, constants, prefix sums (`prefix ≫ Arr.sum`), and `min`/`max` as
  `est (leq U) (outl ∪ outr)` and `est (leq U)° (outl ∪ outr)` (guarded against `min`/`max` on `-7 … 7`).
- `minus`, `div`, `mod` were derivable as terms costing a universe (`°` of `plus`, of `⟨π₁ times(k), π₂⟩ plus`);
  `times` was not. All four are `arith` instances now.
- Not numeric, and in no deleted module: `μX : φ(X)` as a term (closure, data compression, tardiness, TeX, and the
  recursive form of string edit); `Alg` has `iter`/`hylo` as Lean loops only, and `doc/rel-lang-design.md:144`
  lists `μ` and `R*` as not in the language yet. `cp` is a term (above). Trees are declined.
- What else the deleted modules hold that is total: `Find.bin`, `Find.find`, `Find.distinct` (search), and
  `Scan.grade`/`sort`/`permute` (order). No example needs them beyond what `sort`, `setify`, `Obj.sortBy` and the
  `codes` dispatch already give.

## Verdict

No. Step 2 deletes nothing the examples need that would be costly to rebuild. Every missing numeric primitive
(`times`, `minus`, `div`/`mod`, `max`/`min`) is one total `QLean.Kernel.Ew.val` call with another opcode, which
`Algebra.lean` already makes for `plus`, `mulc`, `sub`; the deleted wrappers (`Ew.val`, `Scan.scan`/`over`/`mwin`,
`Parted`) answer `Except`/`Option` and could not be used under the Rules. The one thing kept that the examples
need, `Ops.rank` behind `lt`/`leq`, is moved to `Core` by step 2, not deleted.

Count: 14 of 21 examples are supported (selection sort, takewhile, mss, filter, shortest paths on a cylinder,
paths in a layered network, knapsack, bitonic tours, string edit through its tabulation, and, with `arith`, digits,
fast exponentiation, security van, paragraph, detab-entab); four need `μ` (closure, data compression, minimum
tardiness, TeX, whose numeric ops are now met); three need trees (quicksort, company party, optimal bracketing).
