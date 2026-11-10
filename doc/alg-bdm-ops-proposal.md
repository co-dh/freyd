# Proposal: the B&dM operators that need a new representation in `Alg`

Not implemented: each needs a new `Obj` constructor or a new representation, which needs approval
(`doc/rel-lang-design.md` §h). Everything else in the architecture table's B&dM rows fits `Obj.arr`/`prod`/`sum`.

## 1. Trees `tip`/`bin` (ch. 5 `⦇R⦈`, `F(R)`; ch. 9 `array`, `row`, `col`)

**Declined by the user**: no `Obj.tree`.

The Lean layer's tree is `Tree A = tip A | bin (Tree A) (Tree A)` (`Freyd.Alg.RelSet.TT.Tree`,
AOP/A6_TreeTip.lean; `binFn`, AOP/A9_3_Bracket.lean:1015). `Obj` has no recursive side: `arr` is the only one
whose rows have unbounded size, and its cells are flat.

- **Type.** `Obj.tree (b : Obj)`, `Vals (.tree b) n` =
  `(m : Nat) × Arr .long n × Arr .boolean m × Arr .long m × Arr .long m × Vals b m`:
  a root per row (`Arr .long n`, a node id) into one node table of `m` nodes, each node a tag (`false` tip,
  `true` bin), a left and a right child id (read at a `bin`), and its leaf value (read at a `tip`; a `bin`'s cell
  unused). Nodes are stored children before parents, so a fold is one pass in node order.
- **`Obj.El`.** `.tree b` ↦ an inductive `Tree b.El` in proofs only; `Vals.row` reads a root by recursion on
  the node order (well-founded: a child's id is below its parent's).
- **Ops.** `tip : B ⟶ tree B`, `bin : tree B × tree B ⟶ tree B` (each appends nodes), `⦇[f, g]⦈` (one
  `foldBy`-like pass over the node table, `f` at tips and `g` on the pairs of child results at bins), `F(R)`
  (the tree functor, as `map`), `Vals.pick`/`Obj.codes`/`Obj.raze` cases (a tree's code is the code of its node
  tuple, by the same `slicesRef` scheme `arr` uses).
- **Example.** `size ≜ ⦇[1, plus]⦈ : tree A ⟶ long` on the trees `bin (tip 3) (bin (tip 1) (tip 2))` and
  `tip 5`: node table `[tip 3, tip 1, tip 2, bin 1 2, bin 0 3, tip 5]`, roots `[4, 5]`, answer `[(·, 3), (·, 1)]`.

With it, `row ≜ tails F(mct)`, `col ≜ inits F(mct)` and `array ≜ inits F(row)` are terms in `inits`, `tails`,
`map` (they are definitions of the bracketing program, not operators, so out of scope until the program is).

## 2. Bags `bagify` (ch. 6, ch. 10)

**Done**, variant "representation, no new constructor" (a sorted `arr`): `Alg.bagify`, the order `Obj.sortBy`'s
(value order, code order at `arr`/`sum` cells). `Obj.bag` was declined.

The Lean layer's bag is a list up to permutation (`Bag Job := Quotient perm`, AOP/A10_3_Tardy.lean:193),
`bagify : list ⟶ bag` the quotient map.

- **Representation, no new constructor.** A bag of `B` as the `arr B` holding its elements in the order of
  `Obj.codes` (sorted by code, repeats kept): the canonical member of its `perm` class. Then `bagify` is
  `Vals.pick` of each row's cells at the `grade` of their codes within the row (a `rankSlices`-style kernel),
  and two bags are equal iff their arrays are, so `≫`, `∩`, `nub` need nothing new.
- **What needs approval.** It is a new representation invariant on an existing side: a bag is an `arr` that is
  sorted by code, which no type records. The alternative, `Obj.bag b` as a tagged copy of `arr b`, makes the
  invariant a type but adds a constructor.
- **Example.** `bagify [3, 1, 3] = bagify [1, 3, 3] = [1, 3, 3]`; `bagify° bagify = perm`.
