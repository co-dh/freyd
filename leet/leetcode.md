# LeetCode in the Allegory — the Blind 75 as Bird–de Moor programs

Goal: solve the **Blind 75** LeetCode problems as *allegory programs* in `Rel(Set)`
(`AOP/A6_1_RelSet.lean`), reusing the Algebra-of-Programming toolkit (`A6…A10`), each proved correct,
mathlib-free. `leet/L121.lean` is the seed example. This file is the running skills log + tracker;
update the **Skills** section after every solve.

## What "solving in allegory" means — the 4-step recipe

From `L121.lean`:

1. **Data = initial algebra.** A list is `SnocList L E` (`A6_SnocList.lean`), the initial algebra of
   `F X = L ⊕ X×E` (`wrap` a leaf, `snoc` an element). A left-to-right scan *is* a catamorphism.
2. **Program = catamorphism (a `Map`).** Write the fold `solveFn` by structural recursion, package it
   as `solve := graph solveFn : Data ⟶ Answer` in `Rel(Set)`, and prove it equals the relational cata
   `cataR alg ≫ …` (`solve_eq_cata`). Carry auxiliary state in the fold's result tuple (e.g.
   `(minSoFar, best)`), project out the answer.
3. **Spec = a relation.** `spec : Data ⟶ Answer` relates an input to *every* valid/achievable answer
   (e.g. `profit xs v ↔ v = 0 ∨ ∃ b before s, v = s−b`). LeetCode's "the best" is then `max(≤)·Λ spec`
   (or `min`) — the extremum of that relation.
4. **Correctness = `solve = extremum(≤)·Λ spec`.** Two halves:
   - **refinement** `solve ⊑ spec` — every answer the program returns is valid (`solve_profit`);
   - **domination** `∀ v, spec xs v → v ≤ solveFn xs` (or `≥` for `min`) — it beats every valid answer.

   This is exactly the shape of B&dM's **greedy theorem 7.2** (`A7_2`), **DP theorem 9.1** (`A9_1`), and
   **thinning theorem 8.1** (`A8_1`) — an abstract allegory program with this proof already done once.
   The per-problem job is to instantiate the algebra + monotonicity/optimality condition.

## The reusable toolkit

| piece                    | where                         | what                                                        |
|--------------------------|-------------------------------|-------------------------------------------------------------|
| `RelSet`, `⟶`, `⊑`, `≫`  | `A6_1_RelSet`                 | Freyd's `Rel(Set)` allegory (objects = sets, homs = relns)  |
| `graph f`, `Map`         | `A6_1_RelSet`                 | graph of a function; `Map` = entire+simple (a function)     |
| `SnocList L E`, `dSL`    | `A6_SnocList`                 | non-empty list as initial algebra of `F X = L ⊕ X×E`        |
| `Tree A`, `dTree`        | `A6_TreeBin`                  | binary tree as initial algebra of `F X = 1 + X×A×X` (cata, `cataR`) |
| `cataFold`, `cataR`      | `A6_SnocList`                 | the fold / relational catamorphism                          |
| `imin`, `imax` (+ omega) | `L121`                        | mathlib-free `Int` min/max with rewrite lemmas — copy these |
| `est`, `Λ`               | `A7_1`, `A6_3`                | relational extremum and power-transpose (the `est(≤)·Λ`)    |
| greedy / DP / thinning   | `A7_2` / `A9_1` / `A8_1`      | the abstract optimality theorems to instantiate             |

Axiom budget target: `⊆ {propext, Quot.sound}` (fully constructive; no `Classical.choice`), like L121.

## Fit classification

Allegory programming shines on **folds / scans / DP / greedy / tree recursion**. Ratings below:
`★★★` natural catamorphism (do first — the AOP theorems apply directly); `★★` expressible with effort;
`★` awkward for the fold style (graph/matrix/hash/two-pointer) — reach via a relational spec + a fold
over an encoded structure, or defer. Trees are initial algebras too, so a `TreeCata` engine (analogous
to `SnocList`) unlocks the whole Tree block — **built: `A6_TreeBin` (see S12)**, reuse across ~14 problems.

## Blind 75 — tracker

Status: `·` todo, `▷` in progress, `✓` done (file). Do `★★★` first.

### Array
| #    | problem                                | fit | status         |
|------|----------------------------------------|-----|----------------|
| 121  | Best Time to Buy and Sell Stock        | ★★★ | ✓ `L121.lean`  |
| 53   | Maximum Subarray (Kadane)              | ★★★ | ✓ `L53.lean`   |
| 152  | Maximum Product Subarray               | ★★★ | ✓ `L152.lean`  |
| 217  | Contains Duplicate                     | ★★★ | ✓ `L217.lean`  |
| 238  | Product of Array Except Self           | ★★  | ✓ `L238.lean`  |
| 1    | Two Sum                                | ★★  | ✓ `L1.lean`    |
| 15   | 3Sum                                   | ★★  | ·              |
| 11   | Container With Most Water              | ★★  | ✓ `L11.lean`   |
| 153  | Find Minimum in Rotated Sorted Array   | ★   | ·              |
| 33   | Search in Rotated Sorted Array         | ★   | ·              |

### Binary
| #    | problem                | fit | status |
|------|------------------------|-----|--------|
| 191  | Number of 1 Bits       | ★★★ | ✓ `L191.lean` |
| 338  | Counting Bits          | ★★  | ✓ `L338.lean` |
| 268  | Missing Number         | ★★  | ✓ `L268.lean` |
| 190  | Reverse Bits           | ★★  | ✓ `L190.lean` |
| 371  | Sum of Two Integers    | ★   | ·      |

### Dynamic Programming
| #    | problem                          | fit | status |
|------|----------------------------------|-----|--------|
| 70   | Climbing Stairs (Fibonacci fold) | ★★★ | ✓ `L70.lean`  |
| 198  | House Robber                     | ★★★ | ✓ `L198.lean` |
| 213  | House Robber II                  | ★★  | ✓ `L213.lean` |
| 91   | Decode Ways                      | ★★★ | ✓ `L91.lean`  |
| 62   | Unique Paths                     | ★★★ | ✓ `L62.lean`  |
| 55   | Jump Game (greedy 7.2)           | ★★★ | ✓ `L55.lean`  |
| 322  | Coin Change (DP 9.1)             | ★★★ | ✓ `L322.lean` |
| 300  | Longest Increasing Subseq (thin) | ★★★ | ✓ `L300.lean` |
| 1143 | Longest Common Subsequence       | ★★★ | ✓ `L1143.lean` |
| 139  | Word Break                       | ★★  | ✓ `L139.lean` |
| 39   | Combination Sum                  | ★★  | ·      |

### Interval
| #    | problem                        | fit | status |
|------|--------------------------------|-----|--------|
| 56   | Merge Intervals (sort + fold)  | ★★★ | ✓ `L56.lean`  |
| 435  | Non-overlapping (greedy 7.2)   | ★★★ | ✓ `L435.lean` |
| 57   | Insert Interval                | ★★  | ✓ `L57.lean`  |
| 252  | Meeting Rooms                  | ★★  | ✓ `L252.lean` |
| 253  | Meeting Rooms II               | ★★  | ✓ `L253.lean` |

### Linked List
| #    | problem                        | fit | status |
|------|--------------------------------|-----|--------|
| 206  | Reverse Linked List (cata)     | ★★★ | ✓ `L206.lean` |
| 21   | Merge Two Sorted Lists         | ★★★ | ✓ `L21.lean`  |
| 23   | Merge k Sorted Lists           | ★★  | ✓ `L23.lean`  |
| 19   | Remove Nth Node From End       | ★★  | ✓ `L19.lean`  |
| 141  | Linked List Cycle              | ★   | ·      |
| 143  | Reorder List                   | ★   | ·      |

### String
| #    | problem                                     | fit | status |
|------|---------------------------------------------|-----|--------|
| 3    | Longest Substring Without Repeating (scan)  | ★★★ | ✓ `L3.lean`  |
| 20   | Valid Parentheses (stack fold)              | ★★★ | ✓ `L20.lean` |
| 242  | Valid Anagram (fold to multiset)            | ★★★ | ✓ `L242.lean` |
| 125  | Valid Palindrome                            | ★★★ | ✓ `L125.lean` |
| 49   | Group Anagrams                              | ★★  | ✓ `L49.lean` |
| 424  | Longest Repeating Character Replacement     | ★★  | ·      |
| 76   | Minimum Window Substring                    | ★★  | ·      |
| 5    | Longest Palindromic Substring               | ★★  | ✓ `L5.lean`  |
| 647  | Palindromic Substrings                      | ★★  | ·      |
| 271  | Encode and Decode Strings                   | ★★  | ✓ `L271.lean` |

### Tree  (build a `TreeCata` engine first → unlocks the block)
| #    | problem                                        | fit | status |
|------|------------------------------------------------|-----|--------|
| 104  | Maximum Depth of Binary Tree (cata)            | ★★★ | ✓ `L104.lean` |
| 226  | Invert/Flip Binary Tree (cata)                 | ★★★ | ✓ `L226.lean` |
| 100  | Same Tree                                      | ★★★ | ✓ `L100.lean` |
| 98   | Validate Binary Search Tree                    | ★★★ | ✓ `L98.lean`  |
| 124  | Binary Tree Maximum Path Sum (tupling cata)    | ★★★ | ✓ `L124.lean` |
| 102  | Binary Tree Level Order Traversal              | ★★  | ✓ `L102.lean` |
| 572  | Subtree of Another Tree                        | ★★  | ✓ `L572.lean` |
| 105  | Construct Binary Tree from Preorder + Inorder  | ★★  | ·      |
| 230  | Kth Smallest Element in a BST                  | ★★  | ✓ `L230.lean` |
| 235  | Lowest Common Ancestor of a BST                | ★★  | ·      |
| 297  | Serialize and Deserialize Binary Tree          | ★★  | ✓ `L297.lean` |
| 208  | Implement Trie                                 | ★   | ·      |
| 211  | Add and Search Word                            | ★   | ·      |
| 212  | Word Search II                                 | ★   | ·      |

### Graph / Matrix / Heap  (mostly `★`, defer — reach via relational spec)
| #    | problem                             | fit | status |
|------|-------------------------------------|-----|--------|
| 128  | Longest Consecutive Sequence        | ★★  | ✓ `L128.lean` |
| 207  | Course Schedule (topo sort)         | ★★  | ·      |
| 347  | Top K Frequent Elements             | ★★  | ·      |
| 200  | Number of Islands                   | ★   | ·      |
| 133  | Clone Graph                         | ★   | ·      |
| 417  | Pacific Atlantic Water Flow         | ★   | ·      |
| 269  | Alien Dictionary                    | ★   | ·      |
| 261  | Graph Valid Tree                    | ★   | ·      |
| 323  | Number of Connected Components      | ★   | ·      |
| 73   | Set Matrix Zeroes                   | ★   | ·      |
| 54   | Spiral Matrix                       | ★   | ·      |
| 48   | Rotate Image                        | ★   | ·      |
| 79   | Word Search                         | ★   | ·      |
| 295  | Find Median from Data Stream        | ★   | ·      |

### Beyond Blind 75 (extra solves, same recipe)
| #    | problem                          | fit | status |
|------|----------------------------------|-----|--------|
| 136  | Single Number (xor fold)         | ★★★ | ✓ `L136.lean` |
| 110  | Balanced Binary Tree (cata)      | ★★★ | ✓ `L110.lean` |
| 543  | Diameter of Binary Tree (cata)   | ★★★ | ✓ `L543.lean` |
| 746  | Min Cost Climbing Stairs (DP)    | ★★★ | ✓ `L746.lean` |
| 763  | Partition Labels (greedy scan)   | ★★★ | ✓ `L763.lean` |
| 45   | Jump Game II (greedy)            | ★★★ | ✓ `L45.lean`  |
| 112  | Path Sum (tree decision)         | ★★  | ✓ `L112.lean` |
| 617  | Merge Two Binary Trees (cata)    | ★★  | ✓ `L617.lean` |
| 111  | Minimum Depth (tree, one-child)  | ★★  | ✓ `L111.lean` |
| 14   | Longest Common Prefix (fold-meet)| ★★  | ✓ `L14.lean`  |
| 1137 | N-th Tribonacci (triple tupling) | ★★★ | ✓ `L1137.lean`|
| 2    | Add Two Numbers (carry fold)     | ★★  | ✓ `L2.lean`   |
| 9    | Palindrome Number (digit reflect)| ★★  | ✓ `L9.lean`   |
| 26   | Remove Duplicates Sorted (dedup) | ★★  | ✓ `L26.lean`  |
| 234  | Palindrome Linked List (reverse) | ★★  | ✓ `L234.lean` |
| 283  | Move Zeroes (stable partition)   | ★★  | ✓ `L283.lean` |
| 383  | Ransom Note (multiset contain)   | ★★  | ✓ `L383.lean` |
| 977  | Squares of Sorted Array (sort)   | ★★  | ✓ `L977.lean` |
| 66   | Plus One (digit carry)           | ★★  | ✓ `L66.lean`  |
| 169  | Majority Element (Boyer–Moore)   | ★★  | ✓ `L169.lean` |
| 303  | Range Sum Query (prefix sums)    | ★★  | ✓ `L303.lean` |
| 35   | Search Insert Position (sorted)  | ★★  | ✓ `L35.lean`  |
| 67   | Add Binary (base-2 carry)        | ★★  | ✓ `L67.lean`  |
| 118  | Pascal's Triangle (row fold)     | ★★  | ✓ `L118.lean` |
| 101  | Symmetric Tree (crosswise)       | ★★  | ✓ `L101.lean` |
| 404  | Sum of Left Leaves (flag down)   | ★★  | ✓ `L404.lean` |
| 171  | Excel Column Number (base-26)    | ★★  | ✓ `L171.lean` |
| 13   | Roman to Integer (lookahead)     | ★★  | ✓ `L13.lean`  |
| 724  | Find Pivot Index (prefix bal)    | ★★  | ✓ `L724.lean` |
| 387  | First Unique Character (count)   | ★★  | ✓ `L387.lean` |
| 392  | Is Subsequence (core Sublist)    | ★★  | ✓ `L392.lean` |
| 205  | Isomorphic Strings (eq-pattern)  | ★★  | ✓ `L205.lean` |
| 231  | Power of Two (fuel exponent)     | ★★  | ✓ `L231.lean` |
| 367  | Valid Perfect Square (fuel srch) | ★★  | ✓ `L367.lean` |

## Skills (running log — append after each solve)

### S0 — the L121 template (seed)
- **State-in-the-tuple fold.** When the answer needs auxiliary running data, fold to a tuple and project
  (`solveFn = (foldFn …).2`). Prove `foldFn`'s components equal named invariants (`foldFn_fst =
  minPrice`) so the optimality proof can reason about them.
- **Correctness = refinement + domination**, each a straight `induction xs`. Refinement: the returned
  value is achievable (build the `∃ before …` witness). Domination: `∀ v, spec v → v ≤ solveFn`, using
  the invariant lemmas + `omega`.
- **Mathlib-free `min`/`max`:** copy `imin`/`imax` and their 6 `omega`-backed lemmas from `L121`; never
  reach for `Nat.max`/`Int.instMax` — you want to control the rewrite set.
- **Executable check:** end with `#eval`-style `example : solveFn (ofList …) = k := by decide` sanity
  cases — catches spec/impl mismatches instantly.
- **Axioms:** `graph`/`Map` route keeps it at `{propext, Quot.sound}`; check with `#print axioms`.

### S1 — L53 (Maximum Subarray / the Kadane family)
- **Two-layer spec, no `mutual`.** For subarray/substring answers, define the "ending at the last
  element" relation first (`suffixSum`), then the "anywhere" relation on top of it (`subSum`'s `snoc`
  case `= subSum xs v ∨ suffixSum (snoc xs p) v`) — a plain function calling an already-defined one, not
  a `mutual` block. This is the reusable template for L152, L3, L5, L647.
- **Invoke the fst-invariant at the *current* list.** In the domination proof's suffix case, don't
  re-induct on `suffixSum` — instantiate the already-proved `foldFn_fst_dominates` at `snoc xs p` (the
  list being processed). Turns a nested induction into one lemma application whenever a spec case reads
  "≤ the fold's first component".
- **Nested `imax_eq_or` for `max`-of-`max` state.** When the state is `best = max(prev, e)` with
  `e = max(p, prevEnd+p)`, the refinement witness needs `imax_eq_or` twice (outer: `best` stayed vs took
  `e`; inner: `e` is bare `p` vs `prevEnd+p`). This two-level split is the shape for any Kadane-family
  fold whose state is a `max`-of-`max`.
- **No empty/`0` floor when the empty selection is forbidden.** Unlike L121 (spec has a free `v=0` "do
  nothing"), a non-empty-subarray spec carries no floor — the negative answer on an all-negative input
  falls out for free, no side condition. Do NOT add a `0` disjunct for "must pick ≥1 element" problems.

### S2 — L152 (Maximum Product Subarray) — sandwich invariant + mathlib-free nonlinearity
- **Two-sided sandwich for non-monotone ops.** Addition is monotone (L53 tracked only `maxEnd`);
  multiplication is not, so the fold carries BOTH `minEnd` and `maxEnd`, and the domination invariant is
  two-sided: `minEnd ≤ v ≤ maxEnd` for every suffix product. A fold over a non-monotone binary op needs
  the running min AND max of the "ending here" quantity.
- **Sign-split lemma reusing core monotonicity.** `m ≤ v ≤ M ⟹ imin(mp,Mp) ≤ vp ≤ imax(mp,Mp)` is
  nonlinear (`omega` can't). `rcases Int.le_total 0 p` and chain via `Int.le_trans` with Lean core's
  `Int.mul_le_mul_of_nonneg_right` / `Int.mul_le_mul_of_nonpos_right` (both in `Init/Data/Int/Order`) —
  no hand-rolled monotonicity; never case-split on which side `imin`/`imax` equals.

### S3 — axiom-hygiene & Lean-craft traps (general; watch on every solve)
- **`omega` on a CONJUNCTION goal can pull in `Classical.choice`** even when each conjunct alone is
  omega-clean. If `lean_verify` shows `Classical.choice`, suspect an `omega` closing an `∧`; split it or
  give a constructive term. (Caught in L152.) ALWAYS `lean_verify` the headline theorem.
- **`subst h` on `h : v = x` with `x` a match/`induction`-bound pattern variable deletes `x`** ("unknown
  identifier" later). Use `rw [h]`.
- **A `/-- doc -/` comment cannot precede a `mutual` block** ("unexpected token 'mutual'"). Use `/- -/`.
- **Prefer one `∀ xs, P xs ∧ Q xs` induction over mutually-recursive *theorems*.** Mutual `def`s are fine;
  mutual `theorem`s are fragile. Interdependent invariants → one conjunction, split with `refine ⟨_,_⟩`
  before any `omega`.
- **`nomatch h` is comma-greedy** — `⟨fun h => nomatch h, g⟩` swallows `g`; write `(nomatch h)`.
- **`if (b : Bool) then …` elaborates to `ite (b = true) …`** — reduce on a concrete `true`/`false` with
  `decide`/full `simp`, not `simp only`. Bool programs: `Bool.or_eq_true`/`Bool.and_eq_true`/
  `decide_eq_true_eq`, not `omega`.
- **`ih.mp` vs `ih.mpr`** are trivially transposed in `iff` inductions — if one won't close, try the other.

### S4 — L198 (House Robber) — subset DP
- **Flag-indexed spec via a genuine `mutual`.** `robF`/`robT` (last house excluded/included) reference
  each other in their `snoc` cases on the strictly-smaller `xs` — a real `mutual def` (stays
  definitionally reducible). Extends L53's *sequential* two-layer spec to a *mutual* one.
- **Paired invariant + recycling.** Fold state `(best, prevBest)`; prove `best ⊇ robSpec` and
  `prevBest ⊇ robF` in one conjunction-induction. Load-bearing: `prevBest(snoc xs p) = best(xs)` closes
  the `robF` goals arithmetic-free — reuse for any DP where one state slot recycles another's prev value.

### S5 — L217 (Contains Duplicate) — the DECISION shape
- **Reflection bridge.** Program = Bool fold (`hasDup`, calling a Bool membership sub-fold `memB`); spec =
  Prop relations (`dupP`/`memP`) of the same shape. Prove `memB xs p = true ↔ memP xs p` by induction;
  then `rw` transports Bool↔Prop. Correctness is a one-level `iff` — no refinement+domination, no
  `max(≤)·Λ` extremum.
- **`solve = spec` without `Decidable`.** `spec xs b := (b = true ↔ dupP xs)` + `bool_eq_of_iff_true`
  (`cases b <;> cases c`) — sidesteps a `Decidable dupP` instance that `decide` would demand.

### S6 — L70 (Climbing Stairs) — tupling / linearization
- **Equality refinement by carrying a pair.** When the naive recurrence is already exact but exponential,
  fold `(f n, f(n+1))` for O(1) steps; one induction `fibPair n = (climb n, climb (n+1))` gives
  `solve = spec` (an *equality*, unlike the `⊑` of the optimization scans).
- **Use the problem's own initial algebra.** Object is plain `ℕ` (initial algebra of `1+X`), not a
  `SnocList` — not every allegory program needs the snoc-scan engine.

### S7 — L20 (Valid Parentheses) — stack/depth scan (decision)
- **Depth scan = `(Int depth, Bool ok)` fold**, `ok` short-circuiting once broken; correctness
  (`valid ↔ balancedP`) matches a **prefix-condition spec** (`neverNeg ∧ net = 0`) via two invariants.
  Template for Dyck / balanced-structure decisions.
- **Condition the invariant on the flag.** Once `ok = false` the numeric slot is a *don't-care* dummy, so
  `depth = depthP` holds only *given `ok = true`* (`&&` short-circuit never consults the dummy). When a
  fold's aux state stops meaning anything after failure, condition its invariant on the still-valid flag.

### S8 — L191 (Number of 1 Bits) — count catamorphism
- **State-is-answer cata.** `Nat`-count fold over a `Bool`-element `SnocList` (new element type); the
  state *is* the answer, so `solve = cataR alg` with **no** trailing projection (contrast L121's `≫ snd`).
- **Give a bare count real content.** Prove `count ≤ size`, `count = size ↔ allTrue`, `count = 0 ↔
  allFalse` (from `b2n_eq_one_iff`/`b2n_eq_zero_iff`) instead of a tautological spec.

### S9 — L91 (Decode Ways) — counting DP, not optimisation: took the `decode = climb` route
- **Counting problems are NOT the `L121`/`L198` recipe.** Those refine an ⊑-achievability spec into
  a `≤`-extremum (refinement + domination on a totally ordered type). A COUNT has no order to refine
  into — the honest spec is "the exact number of valid segmentations", and the only content is
  showing an O(n) fold computes that number. Reach for the enumeration-Prop-plus-cardinality route
  (build an inductive family of segmentation witnesses, prove the fold's value is its cardinality)
  ONLY if you actually need it: it requires bijections between witness sets at each recursive step
  (partitioning "segmentations of `snoc xs d`" into "ends in a 1-digit group" ∪ "ends in a 2-digit
  group", each in bijection with a smaller witness set) — real work, with no `Fintype`/`Nat.card`
  infra in this repo to lean on.
- **Route taken: `L70`'s tupling recipe, not the Prop/cardinality one.** Wrote `decode`/`decodePrev`
  as the mutually-recursive TEXTBOOK recurrence directly on `Nat` (no witness type) — the "last group
  is a single digit" / "last group is a valid pair" case split IS the standard decode-ways
  recurrence, accepted as *the* definition of the count exactly as `L70`'s naive `climb` is accepted
  as *the* definition of "ways to climb `n` stairs", with zero enumeration proof beyond that
  definition. It is exponential (each step recurses into two smaller lists, and those overlap), so
  the O(n) `foldFn` — which carries `(ways, prevWays, lastDigit)` — is proved equal to it by one
  induction (`foldFn_eq`), the `L70` linearisation move generalised from a pair to a TRIPLE.
- **A validity guard splits state into "current" vs "one-back".** The 2-digit-window check needs BOTH
  the last digit (`ld`, to form `ld*10+d`) and the count with the last digit removed (`prevWays`, the
  double-branch's contribution) — carry both, don't recompute either. `prevWays` after processing `d`
  is exactly the OLD `ways` (before `d`), the same "recycle the previous slot" trick as `L198`'s
  `prevBest`.
- **Trap: a `-` inside prose inside a `/- … -/` block comment can close it early.** `1-/2-digit` in a
  block comment silently ends the comment at the `-/` substring, cascading into "Function expected"/
  "Unknown identifier" errors dozens of lines later that look unrelated to the real cause. Grep any
  new block comment for a literal `-/` before debugging downstream errors.
- **Trap: `rw` across a `mutual`-def equation often leaves one `rfl` short.** After `rw` substitutes
  the IH equalities, the goal usually becomes definitionally the unfolded `mutual` equation but `rw`'s
  built-in `try rfl` doesn't always fire on it — append an explicit `rfl` after the `rw` (confirmed via
  `lean_multi_attempt`: `rw [...]` alone left "unsolved goals", `rw [...]; rfl` closed it).

### S10 — L62 (Unique Paths) — 2-D DP as a row-carrying fold, and a well-founded-recursion trap
- **2-D equality refinement = `L70`'s tupling, one dimension up.** The naive 2-argument recurrence
  `paths` is already the exact answer (an EQUALITY correctness proof, like `L70`, not `L121`'s
  refinement+domination `⊑`); the efficient program carries an entire DP ROW (`SnocList Nat Nat`, all
  `1`s initially) down the grid's rows instead of a scalar/pair, each new row the INCLUSIVE PREFIX SUM
  of the previous row. The crux proof strengthens "the fold equals the spec" from a single value to a
  WHOLE ROW (`rowAt m n = pathsRow m n`, `pathsRow` an explicit snoc-built list of `paths`-values),
  then a NESTED induction (outer on the row index `m`, inner on the column count `n` inside the crux
  lemma `scanStep_pathsRow`) reduces the row-step to exactly the book's 2-D recurrence at one column.
- **Trap: a genuine 2-argument recurrence (each recursive call decreasing a DIFFERENT argument) compiles
  to WELL-FOUNDED recursion, not structural — its equations are only propositionally true.** `paths (M+1)
  (N+1) = paths M (N+1) + paths (M+1) N` (and even the base cases like `paths (n+1) 0 = 0`) do **not**
  hold by `rfl`/`show … ; rfl`/`decide` (kernel reduction gets stuck on the `WellFounded.fix`/`Acc.rec`
  wrapper) — every unfolding step needs `simp [paths]` (which DOES use the auto-generated `paths.eq_def`
  equation lemmas). Contrast `L70`'s `climb`/`fibPair`, both simple *single*-argument structural
  recursions, where bare `rfl` sufficed throughout — that pattern silently breaks the moment a second
  argument becomes independently recursive. Diagnostic: `rfl`/`show`-then-`rfl` failing with "Type
  mismatch: rfl has type ?m = ?m" on a plain-looking recurrence unfold is the signature of this trap.
- **`simp [paths, Nat.add_comm]` can over-rewrite; isolate the commute instead.** Letting `simp` use
  `Nat.add_comm` alongside the recursive unfold reshuffled unrelated subterms (`m+2` became `1+(m+1)`)
  and left a mismatched goal. Fix: prove the *oriented* recurrence via `simp [paths]` alone first
  (`hbase`), then flip it with one targeted `rw [hbase, Nat.add_comm]` into the order the fold actually
  produces (`scanStep`'s `acc + p`, not the book's `p + acc`) — don't hand `Nat.add_comm` to a broader
  `simp` call.

### S11 — L300 (Longest Increasing Subsequence) — records-list DP + thinning connection
- **Two-layer spec with FLIPPED dependency.** `isSubseqInc = anyEnd = prefix ∨ lastEnd`; but unlike
  L53/L198 (whose "ending here" layer needs only a *suffix*), subsequences skip, so `lastEnd` needs the
  whole prefix's `anyEnd`. When the object can skip elements, the "ending-at-last" layer references the
  *broad* prefix relation, not a narrow suffix.
- **Growing-witness-list invariant pair.** The O(n²) fold carries a `List (Int × Nat)` of records; its
  correctness is a PAIR of invariants (`records_sound` + `records_complete`) — the L53-`foldFn_fst`
  analogue for any DP whose state is an accumulating witness list, not a scalar.
- **Thinning (`A8_1`) is the O(n log n) upgrade, not needed here.** Dropping a record `(v,l)` dominated by
  `(v',l')` (`v'≤v ∧ l'≥l`) is exactly `thinRel`; but `A8_1`'s abstract `thinning` lives in
  `UnguardedPowerLCDA` over power objects, so using it needs recasting the concrete list as a power-object
  frontier + proving the step `MonotonicAlg` — a real reindexing, deferred. Concrete-list route closes
  full O(n²) correctness.

### S12 — L104 + the `A6_TreeBin` engine — trees are initial algebras too
- **New reusable engine `AOP/A6_TreeBin.lean`.** `Tree A = nil | node (Tree A) A (Tree A)` = initial
  algebra of `F X = 1 + X×A×X`; a section-for-section port of `A6_SnocList` (`cataTreeFold`,
  `InitialAlgebra`, `cataR`). **Unlocks the Tree block** (#226/#100/#98/#124…) as folds over it.
- **Two tree-port traps:** (1) the payload-free `nil` summand must map to `True`, not `x = y` (else
  `rfl`-vs-`trivial` term mismatches once `simp` collapses `Unit` equalities); (2) `node`'s TWO recursive
  fields — after `obtain ⟨l,a,r⟩`, a hyp `hv.2.1 : (l,a,r).snd.fst = …` is *defeq* to `a = a'` but not
  *syntactically*, so `rw` fails; first `have haq : a = a' := hv.2.1`, then `rw [haq]`.
- **Tree depth = `max(≤)·Λ pathLen`** (achievable root-to-`nil` path length) — the L121 extremum shape,
  walking the `imax`-larger child instead of scanning a list. State-is-answer, so `solve = cataR alg`.

### S13 — L322 (Coin Change) — ∞-lattice DP over an index axis + the fuel trick
- **`Option Nat` as the ∞-extended lattice.** `omin`/`osucc` (`none` = ∞) states achievability +
  minimality + impossibility as ONE `Option`-valued spec (`coinSpec`) — cleaner than a sentinel `Nat` or
  three separate theorems.
- **Recurse on the INDEX axis (amount), not the input list** — a new shape vs every linear scan so far.
  The descent `amount − c < amount` looks well-founded; **tame it with a fuel parameter**: `dpFuel : fuel
  → amount → Option Nat` recurses on `fuel` (ordinary `Nat.rec`), staying kernel-reducible so `decide`
  works (a `termination_by`/`WellFounded.fix` version is opaque to `decide` — cf. L62/S10's WF trap).
  Prove correctness by induction on `fuel` via a generic per-level `coinFold` lemma. **Reusable for any DP
  over a shrinking index** (LCS #1143 will need it).
- **Gotcha:** `rcases h : e with pat` *generalizes `e` in the goal*, so an existing witness `hs : … = some
  mv` can go useless (the goal's existential becomes `some mv = some mv₁`, closed by `rfl`). Inspect with
  `lean_goal`, don't guess from the error text.

## Tree block (wave 3, over the `A6_TreeBin` engine)

### S14 — L98 (Validate BST) — bounds accumulator threaded DOWN
- Opposite flow to every prior fold (depth/stack flow UP from leaves): `within lo hi t` carries `Option
  Int` sentinels (`none` = unconstrained), TIGHTENED at each node (`l` gets `hi := some a`, `r` gets
  `lo := some a`), so each node is checked against ancestor-inherited bounds — rules out the non-local BST
  bug by construction. Proof: keep `lo hi` GENERALIZED (structural recursion on `t`, not `induction t`
  with bounds fixed) so the two recursive calls instantiate at the tightened bounds. Template for any
  inherited-constraint tree decision (AVL / red-black invariants, range queries).

### S15 — L226 (Invert Tree) — structural OUTPUT (a `Rel(Set)` endomorphism)
- Answer object is `dTree A` again: `solve : dTree A ⟶ dTree A` is a genuine endomorphism, `cataR` fed
  `c := dTree A` (contrast L104's `c := ℕ`). No order to refine into — the spec is a structural relation
  `IsMirror` (simultaneous recursion on both trees, crosswise child swap in `node`). A structural-output
  program carries a natural extra law: **involutivity** `invert(invert t) = t` (the same-object analogue
  of a scalar fold's idempotence/monotonicity).
- **`Tree A` has no `DecidableEq`** (engine stays `Rel(Set)`-only) — add `deriving instance DecidableEq
  for Tree` locally for `decide` checks; and a `/-- doc -/` can't precede `deriving instance` (same family
  as the `mutual` trap — use `--`).

### S16 — L100 (Same Tree) — reflection bridge on a BINARY relation
- Generalize L217's bridge to two inputs: `induction t` while `t'` stays universally quantified (Lean
  threads it as `∀ t'` in each IH); a `cases t'` per case gives the 4 shape-combos, the `nil`/`node` cross
  cases close by `simp [sameFn, SameP]` (both literal `false`/`False`), and the real work is one
  `node/node` case reducing to a conjunction of two independent single-tree IHs.
- Mathlib-free: **`tauto` is unavailable** — use `and_assoc`/`or_assoc` for reassociations. Lambda params
  need explicit type ascription (`fun p : Tree Int × Tree Int => …`) before `.1`/`.2` project through the
  `Cat.Hom` unfold.

### S17 — L572 (Subtree) — nested-relation composition
- The outer `subFn` fold calls a SECOND fold (`sameFn`) at every node: `sameFn (node…) t || subFn l t ||
  subFn r t`. Each sub-fold gets its own reflection bridge (`same_correct`) before the outer
  `solve_correct` (induction on `s` only) composes them with `Bool.or_eq_true`. Wrinkle: `||`/`&&` are
  left-assoc but `∨`/`∧` right-assoc — the final `rw` needs one `or_assoc` to line up (silent "unsolved
  goals", not an error).

### S18 — L124 (Max Path Sum) — tupled tree extremum + `Option`-∞ + the nil-witness trap
- **Tupled tree cata `(best, gain)`**: `gain` = best non-bending downward path from this root (folds only
  children's `gain`); `best` = max over both children's `best` and the through-root bend value. Prove
  `gain`'s achieve/dominate FIRST, then reuse it as a lemma in `best`'s through-root case — don't re-derive
  the descent twice.
- **`Option`-∞ for the empty tree's "no path"** via a whole-value `omax_eq_or : omax x y = x ∨ omax x y =
  y` (4-way `cases` + `imax_eq_or`), NOT `none`/`some` decomposition at each use — turns a 3-way max into
  two chained applications.
- **The nil-child witness trap:** `imax`'s tie-break can credit `imax 0 (gain l)` to the child branch even
  when `l = nil` (`gain nil = 0`), where `downPath nil _` is `False`. Fix: prove `gain_achieves` as
  `l = nil ∨ downPath l (gain l)` and route through the "just the root" witness (`v = a`, since `a+0=a`)
  when the nil case fires.

### S19 — L213 (House Robber II) — circular DP = max over two linear passes
- **Break the ring at each end, take the best.** A circle forbids taking BOTH the first and last
  house; any legal selection therefore misses the last house (so it lies inside `dropLast`, an
  ordinary LINE) or misses the first (lies inside `tail`) — the two cases are exhaustive and each
  is exactly L198's problem with no wraparound. Answer = `imax (robLine dropLast) (robLine tail)`,
  where `robLine` is L198's `foldFn`/`solveFn` fold PORTED VERBATIM from `SnocList` to `List Int`
  (base case `[]` ↦ `0`, since a broken-ring sub-row can be empty). Reusing the linear fold means
  the whole circular-correctness proof reduces to ONE generic two-list lemma
  (`imax_disj_correct l1 l2`: `imax` of two rows' `robLine` achieves/dominates the disjunction of
  their `robSpec`s) — no bespoke "circular gluing" argument needed once the spec is DEFINED as
  that disjunction (`circSpec = robSpec dropLast ∨ robSpec tail`), rather than as an independent
  index-based "subset of a circular list" predicate.
- **A single house breaks the reduction — carve it out first.** For `n=1`, both `dropLast` and
  `tail` come out empty, silently discarding the option of robbing the only house; the standard
  fix (and LeetCode's own edge case) is a separate `[x] => imax x 0` clause before the general
  `dropLast`/`tail` case, both in the program AND in the spec (`v = x ∨ v = 0`).
- **Porting a fold from `SnocList` to `List` swaps which end recurses, harmlessly.** `SnocList`
  peels its LAST element (`snoc xs p → xs`); plain `List` pattern-matching naturally peels its
  FIRST (`x :: xs → xs`). Max-non-adjacent-sum is symmetric under reading the row backwards, so
  the ported fold is still correct — but the mirrored `robF`/`robT` mutual spec must swap roles too
  (`robF`/`robT` now split on "is the FIRST house taken", not the last) to stay a literal
  induction-shape copy of L198's `foldFn_dominates`/`foldFn_is_rob` proofs.
- **`omega` needs an explicit bridge past `def`-level Props and `match`-branch functions.**
  `cases h` on `h : robF [] v` (defeq to `v = 0`, but not syntactically `v = 0`) leaves `omega`
  unable to use it — `have hv : v = 0 := h` first (coercing through defeq once) fixes it. Same
  trap on the `solveFn`-side of a `match`-defined function (`circAnswer [x]` is defeq to
  `imax x 0` but opaque to `omega`): `show v ≤ imax x 0` before invoking `omega`/`have h1 := ...`
  bridges it. General rule (reinforcing S3): every `omega` call needs its hypotheses/goal already
  in a form `omega` can SEE, not just one `rfl`/defeq step away.

### S20 — genuinely APPLYING the AoP greedy/DP theorems (when it works, when it doesn't)
- **Two-component "running-best" scans (L53 Kadane, L121 best-trade) DO fit the GREEDY THEOREM** —
  via the reusable law `AOP/A7_4_Horner.lean`: `greedy_of_refinement_mono` (`A7_2.greedy_of_refinement`
  with monotonicity on `R` rather than `R°`) + `horner_correct` (Rel(Set) packaging over `A6_SnocList`). Route: the
  deterministic pair algebra `alg` is monotone on a PRODUCT/Pareto order `R` and refines the greedy
  choice `A S ≫ est R` of a nondeterministic generator `S`, so `greedy` lands `cataR alg`
  inside the Pareto frontier `A(relCata I S) ≫ est R`; the scalar answer is the frontier's SECOND
  component. BOTH achievability and domination are read off the single greedy conclusion (membership +
  Pareto-maximality); only "generator = spec" (`gen_spec`/`spec_gen`) stays hand-proved — that is
  program-equivalence, NOT the optimisation. This is the repo's first concrete greedy instantiation on
  a real datatype (`L55`/`A7_3_Party`'s "greedy" was only nominal).
- **Key semantic fact (Rel(Set), verified `Iff.rfl`):** `est R P w = w∈P ∧ ∀z∈P, R w z`, so
  `est(≥)` is numeric MAX; feed `R` as the "≥-dominance"/Pareto order (L53: both coords
  `≤`-dominance; L121: first coord by `≥`, since a smaller running-min is better).
- **Prerequisite bridge:** `A6_SnocList.cataR_eq_relCata` (+ `cataFold_comm`) — the missing SnocList
  counterpart of ConsList's — was added so any SnocList greedy/DP instantiation can reach the abstract
  theorems.
- **Cost — it does NOT shrink the file, and it is not axiom-free.** Axioms move
  `{propext,Quot.sound}` → `{propext,Classical.choice,Quot.sound}` (inherited from `relCata`'s
  universal property via the bridge — the same price `A6_6_Sort` pays). L53 217→314, L121 247→331
  lines: the Pareto plumbing + generator characterisation exceed the hand induction they replace. Use
  the AoP theorem when you want the OPTIMISATION proved by the theory, not to save lines.
- **L322 Coin Change does NOT fit the DP theorem (Thm 9.1) — provable, not missing infra** (full
  writeup in `leet/L322.md`). The DP body's Egli–Milner `powerRel` demands EVERY unfolded branch be
  productive; coin change needs only ONE good branch (coins `{2,3}`, amount 3 solvable but sub-amount 1
  dead ⇒ `μ(body) 3 = ∅`). Thm 9.1 fits structural recursion over INPUT data (edit distance,
  bracketing, compression); NOT value-recursion searches with dead ends — for those a direct induction
  is the FAITHFUL proof, and a nominal theorem call would be gerrymandering.

### S21 — L21 (Merge Two Sorted Lists) — two-input recursion with EXACT fuel, one-line head-bound helper
- **Two-input recursion → fuel (S13), but the accounting is EXACT, not slack.** Merge peels the smaller
  head off ONE of two lists, leaving the other untouched — naive pattern matching compiles to
  well-founded recursion, so wrap it in a fuel parameter as usual (`mergeFn xs ys := mergeFuel
  (xs.length+ys.length) xs ys`). But unlike LCS (`L1143`, whose fuel is merely *sufficient*), merge's
  base cases (either list empty) return the other list verbatim at ZERO fuel cost, and each cons/cons
  step hands each recursive call EXACTLY its own minimal requirement. So the defining recurrence
  (`mergeFn_cons_eq`) is recovered by ONE `List.length_cons` + arithmetic rewrite per branch — no
  general "any-sufficient-fuel-agrees" induction (contrast `L1143`'s nested double induction).
- **`LeHead b l := (l = [] ∨ b ≤ l.head)` makes sortedness one line per branch.** `Sorted (b::l) ↔
  LeHead b l ∧ Sorted l` holds BY DEFINITION (no transitivity lemma), and "`mergeFn` preserves a head
  lower bound" is a one-line case split on `mergeFn_cons_eq`'s if-branch, since `LeHead` only inspects
  the first element and the merged head is always exactly one of the two input heads.
- **Honest spec = sorted + exact multiset.** `Sorted (mergeFn xs ys) ∧ ∀ v, count v (mergeFn xs ys) =
  count v xs + count v ys`, both hypotheses `Sorted xs`/`Sorted ys` required. Axioms `[propext,
  Quot.sound]` — fully constructive.
- **Gotcha:** `simp only [List.length_cons]` sometimes closes a length goal by itself (defeq `n+0=n`)
  and sometimes leaves an associativity residual; a trailing bare `omega` then errors "no goals" in the
  first case. Use `simp only [List.length_cons] <;> omega` so it's a no-op when already closed.

### S22 — L56 (Merge Intervals) — sort-then-fold with FULL (not partial) correctness
- **`GapSorted` (all-pairs strict gap), not adjacent-only, is the right disjointness invariant to carry
  through a run-merging induction.** Phrasing "no two outputs overlap/touch" as `∀ jv ∈ rest, iv.2 <
  jv.1` at every head (rather than only between consecutive pairs) costs nothing extra — it is exactly
  what the induction produces, and it composes for free with the "fst-lower-bound" fact already needed
  for coverage. So full disjointness was NOT a hard residual to defer. General lesson: before declaring
  a structural output-invariant "too hard, defer it", check whether the ALL-LATER-ELEMENTS form (used
  already for `Sorted` in `L242`) makes it a byproduct of the same induction.
- **One 4-way conjunction, one induction, one generalized fold-state variable** (`mergeRun_inv`,
  generalizing the running interval `cur` over the sorted tail) is the template for any scan that emits
  a growing OUTPUT LIST, not just a scalar — S3's "one conjunction over mutual theorems" extends past
  scalar DP folds to list-valued folds.
- **Reused `L242`'s concrete `linsert`/`isort`/`Sorted` (ported `Int → Int × Int` by `.1`) instead of
  the abstract `A6_6_Sort`.** That machinery's `sort` is the CONVERSE of a relational cata over
  `ConsList` and is a `Map` (hence executable/`decide`-able) only when the order is a STRICT total
  order; a plain `≤` comparator with ties is not, so it cannot feed a concrete merge fold without extra
  determinism work. Concrete insertion sort is the route whenever the downstream fold must actually RUN.
- **Trap: `exacts [...]` is a repo-custom tactic (`Freyd/Exacts.lean`), not Lean core** — using it
  without that import gives a PARSE-level "unknown tactic" with a confusing, misattributed goal dump.
  Same for `tauto` (still unavailable, reconfirming S16). Watch for the "unknown tactic" error shape.
- **`rw [h]` with `h : jv = cur` does NOT auto-close a leftover `cur.1 ≤ cur.1`** — unlike an `Eq`
  goal, `rw`'s trailing `rfl` doesn't discharge reflexivity-of-`≤`; append `omega`/`exact le_refl _`.
- **Bridge defeq-but-not-syntactic (`mergeRun cur [] ≡ [cur]`) via `have h' : jv ∈ ([cur] : List _) :=
  hjv`, not `rw`** — `rw [List.mem_singleton] at hjv` fails since `hjv`'s displayed type is `jv ∈
  mergeRun cur []`; a fresh `have` against the explicit target type coerces through defeq once (S19).
- **Honest spec + axioms.** `IsMerge ivs out := (∀ x, covers out x ↔ covers ivs x) ∧ Sorted out ∧
  GapSorted out ∧ Valid out` — coverage-preservation, sortedness, disjointness, validity all delivered.
  Axioms `[propext, Quot.sound]`, fully constructive.

### S23 — L238 (Product Except Self) — suffix scan on the RETURN side; reuse core's `zipWith` lemma
- **A suffix scan needs no reversal and no fuel if the accumulator lives in the RETURN value, not an
  argument.** `sufScan (x::xs) = (tot :: sl, tot*x)` where `(sl,tot) := sufScan xs` is plain
  single-argument structural recursion — the running total only exists AFTER the recursive call
  returns, so there is no second independently-decreasing argument (contrast S10/S13's fuel traps).
  Carrying "suffix total" in a bare second component is the same "real content in a bare accumulator"
  move as S8's bit-count.
- **`Init.Data.List.Zip`'s `getElem?_zipWith_eq_some` replaces hand-rolled `zipWith` reasoning** —
  search core BEFORE writing a local lemma (DRY). Phrasing the value spec via `List.getElem?`
  (`out[i]? = some v`) rather than dependent `getElem _ h` sidesteps all proof-term bookkeeping and
  slots directly into that lemma's shape.
- **Two independent per-index lemmas, not one fused induction.** `preScan_get?` (prefix, acc threaded
  DOWN) and `sufScan_get?` (suffix, total threaded UP) are proved SEPARATELY, each closing with one
  `Int.mul_assoc`/`Int.mul_comm`/`Int.one_mul` (Lean core — no `ring`; each step is a single
  associativity/commutativity rewrite, never a multi-term normal form). Combining them via the core zip
  lemma at the end beat one lockstep induction over both scans. No division ⇒ zeros handled for free.

### S24 — L435 (Non-overlapping Intervals) — greedy-by-end exchange argument, Lean-core Sublist/Perm/Pairwise
- **Use Lean CORE `List.Sublist` (`<+`)/`List.Perm` (`~`)/`List.Pairwise`, not hand-rolled `⊆`.** For
  "subset of a list" problems needing MULTIPLICITY, `⊆` is a faithfulness BUG (it silently allows extra
  copies — `[(0,1),(0,1)] ⊆ [(0,1)]` is vacuously true). `Sublist`/`Perm`/`Pairwise` are all in `Init`
  (need `open List` for the scoped `<+`/`~` notation — a bare parse error without it, NOT a
  missing-import error). `List.exists_perm_sublist : l₁<+l₂ → l₂~l₂' → ∃ l₁', l₁'~l₁ ∧ l₁'<+l₂'` is the
  KEY bridge: it converts "an arbitrary sub-selection of the UNSORTED input" into "a same-length
  sub-selection of a SORTED copy" for free — no hand-rolled "sublist survives a stable sort" lemma
  (real, fiddly work). `Perm.pairwise_iff` transports the pairwise invariant across that permutation.
- **Sort ONCE, bridge unsorted↔sorted exactly ONCE, at the END** (contrast L56's merge, which stays
  sorted throughout): prove everything (achievability, the mono/step arithmetic, the exchange-argument
  domination `keptList_dom`) purely on the SORTED list, then bridge to the original input as the last
  step via `exists_perm_sublist`. Don't thread the sort correspondence through the whole proof.
- **The delicate arithmetic: threshold mono + step, proved TOGETHER.** The domination induction needs
  "raising the greedy's start threshold `t→t'` costs at most one kept element" (step), whose proof needs
  "raising the threshold never increases the count" (mono), and vice versa — prove them as ONE combined
  induction returning a conjunction (S3's "one conjunction over mutual theorems", extended to two
  mutually-recursive arithmetic facts).
- **Trap (extends S3): `omega` on a NEGATED-CONJUNCTION HYPOTHESIS silently pulls in `Classical.choice`**
  even for decidable `Int` comparisons. `have h : ¬(P ∧ Q); omega` triggers it. Fix: `by_cases` on `P`
  and `Q` separately (decidable, axiom-free), `exact absurd ⟨_,_⟩ h` where both hold, `omega` elsewhere.
  Prefer bare constructive terms for symmetric-relation lemmas over `unfold; omega`.
- **Check the REAL LeetCode constraint, not the recipe's generic phrasing.** #435's constraint is strict
  `starti < endi`, not the generic `lo ≤ hi`; with degenerate point intervals the greedy exchange step
  has a genuine counterexample. `Valid` uses strict `<`, documented — load-bearing, not cosmetic.
- **Spec + axioms.** `(∃ sub, sub <+ ivs ∧ NonOverlap sub ∧ sub.length = ivs.length - solveFn ivs) ∧
  (∀ sub, sub <+ ivs → NonOverlap sub → sub.length ≤ ivs.length - solveFn ivs)` — achievability +
  optimality of "min removals = n − max non-overlapping subset". Axioms `[propext, Quot.sound]`.

### S25 — L139 (Word Break) — fuel over a WORD-length step, and `rcases h : e` regeneralizes the goal
- **Fuel-by-word-count, not fuel-by-element.** Every prior fuel proof decremented by ONE (`L1143`/`L21`
  peel one cons) or by a value (`L322` by a coin); Word Break consumes a whole dict WORD per level. Fuel
  `s.length` is still exactly sufficient — the load-bearing fact is only `w ≠ [] → 1 ≤ w.length` (so
  `suf.length < s.length`), proved once by `cases w` on `hne`. What transfers from S13 is "some positive
  amount per step", not the literal "1 per step".
- **Hand `splitPrefix : List α → List α → Option (List α)` (returns the leftover suffix), not core
  `List.isPrefixOf`** — the DP step must pattern-match the actual suffix to recurse, not just a `Bool`/∃.
  Bridge `splitPrefix_eq_some : splitPrefix w s = some suf ↔ w ++ suf = s`, structural induction on `w`.
- **Trap (extends S13, hit TWICE): `rcases h : e with pat` REGENERALIZES `e` in the goal** — a
  reflexive `rw [h]` copied from the L322 template then fails "did not find an occurrence" (the `match`
  on `e` was already rewritten by the `rcases`). Delete the stray `rw`. Signature: "did not find an
  occurrence" immediately after `rcases h : e`.
- **Order-sensitive `rintro` against a hand `∃`/`∧` chain type-mismatches DOWNSTREAM, not at the
  pattern.** Swapping two binders (`⟨w,hw,hne,suf,…⟩` vs `⟨w,hw,suf,hne,…⟩`) errored several lines later
  at the first USE of the misbound var — check a multi-binder pattern's field order against the actual
  nesting, not just arity. Spec = honest inductive `Seg` (`nil`; `cons : w∈dict → w≠[] → Seg suf →
  Seg (w++suf)`), reuse allowed; `wordBreak_correct : wordBreakFn dict s = true ↔ Seg dict s`, Bool↔Prop
  reflection (S5). Axioms `[propext, Quot.sound]`.

### S26 — L57 (Insert Interval) — DRY corollary of L56, `covers_cons` massaging
- **Insert = merge `new :: ivs`.** Since L56's `mergeFn` sorts-then-merges an ARBITRARY list, insertion
  needs zero new machinery: `insertFn ivs new := L56.mergeFn (new :: ivs)`. Trades LeetCode's O(n) pass
  for O(n log n), but the campaign proves correctness, not complexity. `import leet.L56`; reuse
  `covers`/`Sorted`/`GapSorted`/`Valid`/`merge_correct` verbatim (DRY, per project rule).
- **The only real content is the coverage clause**, via `L56.covers_cons`: `covers (new::ivs) x ↔
  (new.1 ≤ x ∧ x ≤ new.2) ∨ covers ivs x`, then a manual `∨`-swap (`constructor`/`rintro`, no
  `or_comm`/`tauto`) to match the spec's disjunct order. Validity of `new::ivs` is immediate from
  `hnew`+`hival`.
- **Wrapper judgment: NOT a forbidden one-liner.** `insertFn` is the *program* LeetCode #57 asks for; the
  theorem `insert_correct : IsInsert ivs new (insertFn ivs new)` is a genuine re-derivation under insert
  semantics (new hypothesis `hnew`, translated coverage), not a renamed call to `merge_correct`. Axioms
  `[propext, Quot.sound]` (inherited from L56).

### S27 — L252 (Meeting Rooms) — sort-invariance of Pairwise + sorted⟹adjacent≡all-pairs
- **`Perm.pairwise_iff` transports the all-pairs disjointness across the sort in one line.** Program =
  `canAttendFn ivs := noAdj (L56.isort ivs)` (sort by start, then check consecutive pairs); spec =
  `NonOverlap := List.Pairwise NoOverlap` (Lean-core, all-pairs, `NoOverlap a b := a.2 ≤ b.1 ∨ b.2 ≤ a.1`,
  touching allowed). Sort-invariance: `Perm.pairwise_iff` needs `NoOverlap` SYMMETRIC (a disjunction
  swap) + `isort` a `Perm` — **L56 exposes only `isort_mem`, not `Perm`, so prove `isort_perm : l ~
  isort l` locally** (line-for-line port of L435's `ivs_perm_isortH`, `.1` comparator).
- **Sorted⟹adjacent≡all-pairs splits into TWO asymmetric lemmas.** Forward (adjacent-passing ⟹
  all-pairs) needs ONLY `.1`-sortedness — one adjacent bound `lastHi ≤ head.1` transitively lower-bounds
  every later start. Reverse (all-pairs ⟹ adjacent) genuinely needs **STRICT `Valid` (`lo < hi`)**: given
  `a.1 ≤ b.1` and `b.1 < b.2`, `NoOverlap a b` can hold ONLY via `a.2 ≤ b.1` (the other disjunct
  `b.2 ≤ a.1` chains to `b.2 ≤ a.1 ≤ b.1 < b.2`, absurd). Counterexample confirming strictness is
  load-bearing (S24 recurring): non-strict `≤` lets a zero-length `(1,1)` be `NonOverlap` with `(1,5)`
  via the second disjunct while the adjacent check `5 ≤ 1` fails. `canAttend_correct : canAttendFn ivs =
  true ↔ NonOverlap ivs`, axioms `[propext, Quot.sound]` (no Classical.choice — every `omega` on plain
  conjunctions, `by_cases` on decidable Int `≤`).

### S28 — L230 (Kth Smallest in a BST) — inorder→sorted, FULL rank spec, core `Pairwise`
- **Honesty FULL.** `kthSmallestFn t k := (inorder t)[k-1]?` (plain structural `inorder (node l a r) =
  inorder l ++ a :: inorder r`, no fuel). Headline `kthSmallest_correct (hbst : IsBST t)
  (hk : kthSmallestFn t k = some v) : memT t v ∧ ((inorder t).filter (·< v)).length = k-1` — proves `v`
  is a real tree label AND the exact rank (exactly `k-1` labels are `< v`), not an index restatement.
  Plus `kthSmallest_exists` (totality for `1 ≤ k ≤ length`). Reuses `L98.IsBST`/`BSTwithin`.
- **Reuse Lean-core `List.Pairwise`, don't hand-roll `Sorted`.** `pairwise_append`'s third clause
  (`∀ a∈l1, ∀ b∈l2, R a b`) IS the `Sorted (xs++a::ys)` helper for free; only added one `Int.lt_trans`
  for the cross-subtree `x<a<y` case. The `IsBST ⟹ Sorted inorder` proof generalizes the bounds (S14) and
  proves sortedness AND per-node bound facts as ONE conjunction-induction (S3/S18); phrase bounds as
  `∀ l0, lo = some l0 → l0 < x` (not a `match lo with …` predicate) to dodge defeq-matching when the same
  lemma fires at `lo` and `some a`.
- **Trap: `rw [List.filter_cons_of_pos/neg hcond]` mis-unifies `p`/`a`** when `hcond`'s type is
  beta-reduced (`rw` matches `p a` against `decide`'s internal application → bogus `p := @decide (b<v)`).
  Pass `p`/`a`/`l` EXPLICITLY.
- **Trap (axiom hygiene, S3-family): core `List.filter_eq_nil_iff` pulls in `Classical.choice`.** It
  silently infected every downstream theorem; replaced with a constructive `filter_lt_eq_nil_of_forall_lt`
  (structural recursion + `filter_cons_of_neg`). **`#print axioms` the CORE lemmas you lean on, not only
  your own proofs.** Axioms `[propext, Quot.sound]`.

### S29 — L128 (Longest Consecutive Sequence) — sort + scan, LOCAL-maximality invariant
- **Program** `longestConsecFn nums := scanFn (L242.isort nums)` (isort reused verbatim), a
  `(prev, runLen, best)` scan with dedup-skip / +1-extend / reset branches (`nmax` = L121 `imax` ported to
  `Nat`). Headline `longestConsec_correct : (∃ s, ∀ i < longestConsecFn nums, s+i ∈ nums) ∧
  (∀ s L, (∀ i < L, s+i ∈ nums) → L ≤ longestConsecFn nums)` — achievability + domination (S0). Axioms
  `[propext, Quot.sound]`.
- **The crux invariant needs LOCAL exactness, not just a global lower bound.** A "`best` dominates every
  run with top ≤ prev" invariant is NOT inductively self-sufficient; the extend step needs the current run
  ending at `prev` to be MAXIMAL among runs ending exactly at `prev` (`RunOK`'s 2nd conjunct). Then the
  domination dichotomy closes: any candidate run with top ≤ new watermark `c` either is dominated by old
  `best` (top ≤ old prev) or ends exactly at `c` — nothing lands strictly between `prev` and `c`
  (`dichot_of_cover`, combining the `Cover` invariant with "suffix elements ≥ c" from sortedness). This IS
  the Lean-native "sorted ⟹ a present value-block sits as a literally adjacent stretch", no separate
  dedup/adjacency lemma.
- **The gap-reset case AND the whole-list first element are ONE lemma** `run_singleton (hcl : c∈l)
  (hgap : c-1∉l) : RunOK l c 1` — base case gets `c-1∉l` from sortedness (c is the min), interior gap case
  from `Cover`+contradiction.
- **Trap: a nested `(by omega)` passed as a bare application argument fails "no usable constraints"** when
  the enclosing lemma's implicits aren't pinned yet — hoist to `have hle : … := by omega` FIRST, then pass
  the named term (sharper S3: elaboration ORDER, not just hypothesis form). **Trap: `omega` intermittently
  drops a `have`-bound fact in an antisymmetry goal ("no usable constraints" despite relevant hyps) — fall
  back to `Nat.le_antisymm h1 h2`.** **Trap (S3-family): `rcases h : e with rfl | …` on `mem_cons.mp`
  deletes the induction-bound `c`; name the eq + `omega` instead of `subst`.**

### S30 — L297 (Serialize/Deserialize Tree) — the SECTION–RETRACTION case
- **The cleanest allegory framing of the batch.** `serialize : Tree Int → List Tok` (`Tok := Option Int`,
  preorder with null markers, a plain cata); `deserializeFn` a fuel parser; headline
  `round_trip : deserializeFn (serialize t) = some t`, restated categorically as
  `section_retraction : solveSer ≫ solveDes = graph (some ·)` (a `Rel(Set)` retraction identity — a real
  two-line `hom_ext`, not a delegating one-liner). Axioms `[propext, Quot.sound]`.
- **Fuel bound chosen to make the round-trip a structural induction on the TREE, not the fuel.** `parseFuel`
  peels one unit/node; BOTH of the `node` case's recursive parses reuse the SAME predecessor fuel `fuel'`,
  because the generalized lemma `parseFuel_serialize : ∀ t rest fuel, (serialize t).length ≤ fuel →
  parseFuel fuel (serialize t ++ rest) = some (t, rest)` lets `omega` derive each child's sufficiency from
  one combined `1 + len l + len r ≤ fuel'+1`. `deserializeFn` fuels by `ts.length` (bound is `≤`; at
  `rest=[]` it's met exactly).
- **The `node`-case IH chaining: feed the LEFT parse the trailing tokens `serialize r ++ rest`, then the
  RIGHT parse the original `rest`** — since `serialize (node l a r) ++ rest = some a :: (serialize l ++
  (serialize r ++ rest))` (one `cons_append`+`append_assoc`), the left parse's returned leftover is exactly
  the right parse's input. This is "parse inverts print with ANY trailing tokens".
- **Trap (S9 recurring): after `rw [heq]` regroups the append, closing the nested `match parseFuel …`
  needs `simp only [parseFuel, parseFuel_serialize l …, parseFuel_serialize r …]` in one call — bare `rw`
  won't iota-reduce a matcher application.** Same defeq-not-syntactic gap needs a trailing `rfl` on the
  final `Option.map Prod.fst (some (t,[])) = some t`.

### S31 — L23 (Merge k Sorted Lists) — pure fold-of-fold, the cleanest DRY win
- **The fold IS the induction — no bridging lemma.** `mergeKFn lists := lists.foldr LC21.mergeFn []`, so
  `mergeKFn (l::rest) = LC21.mergeFn l (mergeKFn rest)` holds by definitional unfold (`show`+defeq); the
  correctness `induction lists` needs NO separate "fold commutes with recursion" lemma (contrast the fuel
  proofs L21/L1143). Headline `merge_k_correct : (∀ l ∈ lists, LC21.Sorted l) → LC21.Sorted (mergeKFn
  lists) ∧ ∀ v, LC21.count v (mergeKFn lists) = totalCount v lists`, `totalCount v lists :=
  (lists.map (LC21.count v)).foldr (·+·) 0`. Entire correctness burden = ONE `LC21.merge_correct` call per
  step. Reuse `import leet.L21` verbatim; zero new sortedness/multiplicity machinery. Axioms
  `[propext, Quot.sound]`.
- **Trap: `rw`'s trailing `rfl` does NOT close a definitional unfold of `List.map`/`foldr`.** After
  `rw [hCmerge, hCrest]` the goal `count v l + totalCount v rest = totalCount v (l::rest)` is defeq-true but
  stayed open — add an explicit trailing `rfl`.

### S32 — L253 (Meeting Rooms II) — max-over-instants reduces to max-over-STARTS, no sort
- **The event-sweep-killing reduction.** min rooms = max concurrent meetings; and the max overlap over ALL
  instants is always attained AT SOME meeting start, so `roomsFn ivs := max over each start `iv.1` of
  `countCover ivs iv.1` (a `filter (iv.1 ≤ t ∧ t < iv.2)` length, `Nat.max`-folded). Headline
  `rooms_correct : (∃ t, countCover ivs t = roomsFn ivs) ∧ (∀ t, countCover ivs t ≤ roomsFn ivs)` — genuine
  max over all `Int` instants, NOT a program restatement. **No `Valid`/sortedness hypothesis** — purely
  combinatorial, holds for arbitrary/degenerate intervals (unlike L56/L252/L435/L57).
- **Constructive max-by-key, quantified as `hd :: l` not `l ≠ []`.** `exists_max_start hd l : ∃ m ∈ hd::l,
  ∀ iv ∈ hd::l, iv.1 ≤ m.1` by structural induction — stating over `hd::l` sidesteps the "motive not type
  correct" trap of inducting under a `l ≠ []` hyp that mentions the scrutinee. Domination: reusable
  `filter_length_le_of_imp : (∀ x∈l, p x → q x) → (l.filter p).length ≤ (l.filter q).length` (structural,
  the S28 `filter_cons_of_pos/neg` pattern); every meeting covering `t` also covers the latest start `m.1`
  (`m.1 ≤ t < iv.2` ⟹ `m.1 < iv.2`). Achievability: `foldMax_mem_or_nil`.
- **Trap: `cases h : e with …` REGENERALIZES `e` in the goal in EVERY branch** (confirmed for `cases`, not
  just S25's `rcases h : e`) — a leftover `rw [h]` fails "did not find an occurrence"; `rw [← h]` at branch
  entry routes back. **Trap (extends S19): `rcases h with rfl | h'` on `x ∈ hd::tl` may `subst` the WRONG
  side (deletes `hd`, not `x`)** — name the eq + `rw`, don't `rfl`. Axioms `[propext, Quot.sound]` (no
  `filter_eq_nil_iff`; `of_decide_eq_true` bridges Bool↔Prop).

### S33 — L5 (Longest Palindromic Substring) — expand-center index-free, FULL both halves
- **Full honesty.** `isPalin xs := xs = xs.reverse` (literal), `IsPalinSubstr s len := ∃ i, i+len ≤
  s.length ∧ isPalin (sub s i len)`; headline `longest_palin_correct : IsPalinSubstr s (longestPalinFn s) ∧
  ∀ len, IsPalinSubstr s len → len ≤ longestPalinFn s` (achievability + domination). Axioms
  `[propext, Quot.sound]`.
- **Index-free expand-around-center.** `commonPrefixLen : List Int → List Int → Nat` (structural, no fuel)
  matches a reversed-consumed left prefix against the right remainder; `bestFrom left right` walks `right`
  checking odd/even radii; `longestPalinFn s := bestFrom [] s`. Achievability routed through
  `IsPalinSplit s len := ∃ pre mid post, s = pre++mid++post ∧ mid.length = len ∧ isPalin mid` (bridged to
  `IsPalinSubstr` once at each end) so the recursion never touches `Nat` subtraction. The **peel/wrap
  engine is ONE lemma** `palinSplit_of_commonPrefix` parameterized by a self-reverse `extra`, instantiated
  at `[x]` (odd) and `[]` (even) — odd/even share the proof. Core lemmas that are load-bearing:
  `List.append_inj`, `List.take_left`/`drop_left` (all Lean core, don't hand-roll).
- **BIG axiom-hygiene rule (generalizes S3/S24): `omega`/`simp` closing a NON-arithmetic goal (e.g. an `∃`)
  from a contradictory `Nat` hypothesis silently pulls in `Classical.choice`** — even though the SAME fact
  into a `False` goal is clean. Verified by minimal repro: `(h : 0 = m+1) : False := by omega` is
  `[propext, Quot.sound]`; `(h : 0 = m+1) : ∃ c tl, ([]:List Int) = c::tl := by omega` is
  `[…, Classical.choice, …]`. **Fix: always `exfalso` (or `have _ : False := by omega`) BEFORE the
  arithmetic-closing tactic; never let `omega`/`simp` discharge a non-`False`/non-arithmetic goal from a
  numeric contradiction.** (Bit three `nil`-branch impossibility proofs here.)
- **Trap: `conv`/`set` are NOT in this repo's Lean core** (no Mathlib) — for one-sided rewrites build a
  standalone `have step : <LHS> = <target> := …` via `congrArg`/`.trans`; never `rw` a bare variable that
  also occurs inside the rewrite's own RHS (`rw` substitutes ALL syntactic occurrences in one pass).

### S34 — L1 (Two Sum) — witness search, soundness + completeness, and why NOT `solve = spec`
- **Full honesty via witness soundness AND completeness** (no LeetCode "exactly one solution" crutch).
  `twoSumFn nums target := go [] target nums` scans carrying a `(value,index)` seen-list (next index =
  `seen.length`); `TwoSum nums target i j := i < j ∧ ∃ vi vj, nums[i]? = some vi ∧ nums[j]? = some vj ∧
  vi+vj = target` (getElem?-phrased, S23: `i < length` is a CONSEQUENCE of `= some _`, not a separate hyp).
  Headline `twoSum_correct : (∀ i j, twoSumFn = some (i,j) → TwoSum …) ∧ (twoSumFn = none → ∀ i j, ¬ TwoSum
  …)`, both halves one generalized `go_gen` induction (S3). Axioms `[propext, Quot.sound]`.
- **Deliberately NO `solve = spec`.** A Two-Sum input can have several valid pairs and the program returns
  one, so `spec` (relate input to EVERY valid pair) is entire-but-NOT-simple ⇒ `solve = spec` is FALSE
  (contrast L217's Bool decision with a unique answer). Package `solve := graph …` + `Map solve` for the
  `Rel(Set)` framing, but state correctness at the function level only. **A decision/search that returns one
  of many valid answers cannot use the `solve = spec` shape — use soundness+completeness instead.**
- **`go_gen` needs THREE threaded invariants:** `seen.length = done.length` (running index),
  `SeenIff done seen` (seen captures the processed prefix, both directions), AND `∀ i j, ¬ TwoSum done …`
  ("no pair missed so far") — without the third, the `none`-completeness can't rule out pairs sitting
  entirely inside an already-scanned prefix. **Traps:** an untyped `∀ v i, done[i]? = some v` leaves
  `GetElem?` stuck ("?m depends on v") — annotate `∀ (v:Int) (i:Nat)`. `rintro (heq|hmem)` on raw
  `List.Mem` substitutes head-case vars away — go through `List.mem_cons.mp` first. `injection` gives the
  eq in the rewritten direction (`x=v` not `v=x`) — take what it gives, `.symm` downstream.

### S35 — L102 (Level Order Traversal) — level-merging cata, one unconditional row equation
- **`levels (node l a r) = [a] :: mergeLevels (levels l) (levels r)`** (mergeLevels concatenates two
  level-lists depth-by-depth). Headline `solve_correct : (∀ d, rowAt (levels t) d = atDepth t d) ∧
  (levels t).length = height t`. **Define `rowAt` with the SAME out-of-range ↦ `[]` convention as
  `atDepth`, then prove the row equation UNCONDITIONALLY for all `d`** — both sides collapse to `[]` past the
  height, so one equation delivers "every in-range row right" + "atDepth vanishes past length" with NO
  `d<length`/`d≥length` split and NO `getElem?`/`Option` juggling (the flagged Classical.choice risk spot).
  Axioms `[propext, Quot.sound]`.
- **Crux `mergeLevels_row : rowAt (mergeLevels A B) d = rowAt A d ++ rowAt B d`** proved as a recursive
  theorem mirroring `mergeLevels`'s three clauses (termination structural on the FIRST list even though the
  pattern also splits `d`). Length law needs `imax_succ (m n) : imax (m+1) (n+1) = imax m n + 1`
  (`unfold imax; split <;> split <;> omega` — double-split, two `ite`s). Kept every def plain structural
  (no fuel / no WF) by never recursing on two shrinking args at once ⇒ all unfolds `rfl`-transparent,
  `decide` runs.

### S36 — L49 (Group Anagrams) — `isort`-key partition, Pairwise (positional) separation invariant
- **Anagram key = `LC242.isort` (reused).** `IsAnagram s t := key s = key t` IS `isort_eq_iff_countL_eq`'s
  LHS = same multiset — no delegating wrapper (documented in a comment). `groupFn := strs.foldr insertInto
  []`. Headline `group_correct` = full 4-part partition: membership `x∈strs ↔ ∃ g∈groups, x∈g`,
  non-emptiness, within-group homogeneity, across-group separation. Axioms `[propext, Quot.sound]`
  (omega-free — pure list/Pairwise/Perm).
- **The "one key per group" invariant MUST be `List.Pairwise NoCross groups` (POSITIONAL), not
  membership-based.** A membership `(∃ related)→g1=g2` invariant can't survive `insertInto` because the
  merged group's VALUE changes (`r::rest → s::r::rest`) and membership can't tell "same value new position"
  from a duplicate. `Pairwise`'s head/tail structure is inherently positional; crux `noCross_insertInto`
  carries it, `groupsWF_separation` derives the membership-quantified statement (needs `noCross_symm`).
  Membership preservation is cleanest via `List.Perm`: `insertInto_flatten_perm : (insertInto s groups
  ).flatten ~ s :: groups.flatten` + `mem_flatten`/`Perm.mem_iff`.
- **Traps:** `insertInto`'s `if` does NOT reduce via bare `show`/defeq after `by_cases hk` — expose named
  equation lemmas (`insertInto_merge`/`_skip` via `rw [if_pos/if_neg hk]`) and `rw` at call sites (S9/L242
  pattern; not a forbidden wrapper — it exposes the function's own equations). **Dot notation `.symm`/
  `.trans` FAILS on an `IsAnagram`-typed hyp** (a plain `def`, not `abbrev`, so field-resolution won't
  unfold it to find `Eq.symm`) — use explicit `isAnagram_symm := Eq.symm h` helpers (they typecheck since
  argument-elaboration defeq DOES unfold the `def`).

### S37 — L271 (Encode/Decode Strings) — the L297 `rest`-generalization is FALSE for non-self-delimiting codes
- **KEY LESSON: a round-trip lemma generalized "with any trailing tokens `rest`" (L297/S30) only holds when
  the encoding is SELF-DELIMITING.** L297's preorder-with-null-markers ends each subtree unambiguously
  mid-stream, so `parseFuel fuel (serialize t ++ rest) = some (t, rest)`. A FLAT length-prefixed list of
  strings has NO end marker — a fuelled-and-slack decoder greedily reinterprets trailing garbage as more
  strings: `decodeFuel 1 (encode [] ++ [0]) = some [[]]`, NOT `some ([], [0])` (verified by `#eval` BEFORE
  writing any proof). Fix: prove the plain, NON-`rest`-generalized `decode_encode : ∀ strs fuel,
  (encode strs).length ≤ fuel → decodeFuel fuel (encode strs) = some strs` by induction on `strs` — the
  inductive step's recursive call is always exactly `encode rest'` with nothing appended, so no trailing
  thread is needed. **Check the generalization holds by `#eval` before transplanting a template.**
- `encode1 s := (s.length : Int) :: s`, `encode := List.flatMap encode1`; `decodeFuel` an S13 fuel parser
  (`List.drop` of a computed length isn't structural). `round_trip : decodeFn (encode strs) = some strs`,
  `section_retraction : solveEnc ≫ solveDec = graph (some ·)` (Rel(Set)). No escaping/delimiter needed —
  positional decode is unambiguous (head is ALWAYS a length). Axioms `[propext, Quot.sound]`.
- **Traps:** `Int.toNat_natCast : (↑n).toNat = n` (length token is a literal `Nat`-cast, no
  `toNat_of_nonneg` side-goal). `encode (s::rest') = s.length :: (s ++ encode rest')` via `List.flatMap_cons`
  + `cons_append` (bare `rw` won't unfold `flatMap`'s matcher — S30 class). **`strs=[]` base needs
  `cases fuel <;> rfl`** (opaque `fuel` blocks iota-reduction of `decodeFuel _ []` despite the wildcard
  fuel pattern). `fuel=0` contradiction in `cons` via `exfalso; omega` (S33).

### S38 — L11 (Container With Most Water) — two-pointer window-invariant, nonneg is load-bearing
- **Full both-halves optimization.** `twoPtrFuel : List Int → Nat → Nat → Nat → Int` (fuel `= h.length`,
  structural on fuel); moves the pointer at the SHORTER line inward. `Area h i j := imin h[i]! h[j]! *
  ((j:Int)-(i:Int))`. Headline `maxArea_correct (hnn : Nonneg h) (hlen : 2 ≤ h.length) : IsPairArea h
  (maxAreaFn h) ∧ ∀ a, IsPairArea h a → a ≤ maxAreaFn h` (max over ALL pairs `i<j`). Axioms
  `[propext, Quot.sound]`.
- **Crux `twoPtrFuel_correct`: over window `[lo,hi]` the sweep returns the max `Area` over all pairs inside
  it** (induction on fuel). Step lemmas `discard_lo`/`discard_hi`: if `h[lo] ≤ h[hi]`, every `(lo,j)` with
  `j<hi` has `Area h lo j ≤ Area h lo hi` (both `imin ≤ h[lo]` AND width `j-lo < hi-lo`), so moving `lo`
  inward loses nothing better than the recorded `Area h lo hi`. Nonlinear `*` via ONE core
  `Int.mul_le_mul hac hbd nn_b nn_c : a*b ≤ c*d` (cleaner than L152/S2's two-step chain).
- **`Nonneg h` (LeetCode's `heights[i] ≥ 0`) is LOAD-BEARING, not decorative** — the empty-window tie-break
  `imax a 0 = 0` (last candidate discarded to nothing) needs `Area ≥ 0` to force `a = 0`; without
  nonnegativity the two-pointer is not correct. **Traps:** `subst` on `i = lo` deletes `lo` — `rw [hieq] at
  hij ⊢` (rewrite the HYP too, the discard lemma needs it). `imax_eq_or`'s `exacts` needs
  `import Freyd.Exacts` (S22). Vacuous cases `exfalso; omega` prophylactically (S33).

### S39 — L19 (Remove Nth From End) — take/drop splice, `min` is omega-transparent
- **`removeNthFn xs n := xs.take (xs.length-n) ++ xs.drop (xs.length-n+1)`** — no recursion, no fuel.
  Headline `removeNth_correct (1 ≤ n) (n ≤ xs.length) : (out).length = xs.length-1 ∧ (∀ i, i<k → out[i]? =
  xs[i]?) ∧ (∀ i, k ≤ i → out[i]? = xs[i+1]?)` with `k := xs.length-n` (getElem?-phrased, S23). Axioms
  `[propext, Quot.sound]`.
- **`min` from `List.length_take` is fully `omega`-transparent** — no manual case split on
  `min (len-n) len`; `rw [List.length_take]` then `omega`/`if_pos (by omega)`/`if_neg (by omega)` closes
  every `min`/truncated-`Nat.sub` interaction across `getElem?_append`/`getElem?_take`/`getElem?_drop`
  (`congr 1; omega` for the final index eq). **Bonus `removeNth_splice` (axiom-free, `[]`)**: splicing
  `xs[k]'h` back recovers `xs`, proving the deleted element IS the n-th-from-end — dodge dependent-`getElem`
  proof-irrelevance fights by UNIVERSALLY quantifying over the bound proof `h` and using the SAME `h` on
  both sides of `rw [← List.drop_eq_getElem_cons h, List.take_append_drop]`.

### S40–S43 — wave 6 (clean tree/string; beyond Blind-75)
- **S40 L112 Path Sum.** `path_sum_correct : hasPathSumFn t target = true ↔ PathSum t target`, axioms
  `[propext]`. **Leaf vs one-child encoded structurally:** 5-way pattern match on `(l,r)` shape (nil/leaf/
  left-only/right-only/both) → each arm a literal `rfl` equation, and the correctness proof is a recursive
  theorem mirroring the same 5 arms (the `within_correct`/L98 idiom) — no `DecidableEq (Tree)`, no Bool
  guard. `PathSum`'s `left`/`right` carry `child ≠ nil` (via `node_ne_nil := fun h => nomatch h`) so a
  one-child node can't match `leaf`. `cases h` on a `PathSum` hyp auto-prunes shape-impossible constructors.
- **S41 L617 Merge Two Binary Trees.** `merge_correct : ∀ p, getPath (mergeT t1 t2) p = combine (getPath
  t1 p) (getPath t2 p)`, **axioms `[]` (fully constructive)**. **No fuel:** `mergeT`'s node/node case shrinks
  BOTH trees in the SAME direction (`zipWith` shape) → structural recursion on `t1` alone (`t2` along for the
  ride); contrast L21/L1143 where each call shrinks a DIFFERENT argument (⟹ WF+fuel). Clause order: `nil,t↦t`
  already catches `nil,nil`, so `t,nil↦t` only fires on `node,nil`. `getPath`/`combine` reference `mergeT`
  nowhere ⟹ honest overlay spec, not a restatement; bases close by `cases (getPath …) <;> rfl`.
- **S42 L111 Minimum Depth.** `minDepth_correct (t ≠ nil) : IsRLDepth t (minDepthFn t) ∧ ∀ n, IsRLDepth t n
  → minDepthFn t ≤ n`, axioms `[propext, Quot.sound]`. **One-child gotcha structural** (5-way `(l,r)` match,
  no `if l=nil`, no `DecidableEq`); `IsRLDepth.left/right` carry `child ≠ nil`. **Domination MUST be a
  top-level pattern-match theorem with an explicit recursive self-call (NOT `intro; induction h`)** — the
  constructor index `d+1` isn't a bare var, so `induction h` cascades spurious `Int.ofNat`/`negSucc` cases;
  use `cases h` (which also substitutes `n`, so `show … ≤ _` not `≤ n`) inside each concrete `t`-branch.
  `node_ne_nil` via `intro h; cases h` (not `Tree.noConfusion`, which needs an explicit motive vs `False`).
- **S43 L14 Longest Common Prefix.** `lcp_correct (strs ≠ []) : (∀ s∈strs, lcpFn strs <+: s) ∧ (∀ p, (∀ s∈
  strs, p<+:s) → p<+: lcpFn strs)`, axioms `[propext, Quot.sound]`; uses Lean-core `List.IsPrefix` (`<+:`)
  directly. `commonPrefix2` is a MEET: `commonPrefix2_prefix` + `commonPrefix2_greatest`, joint induction
  closed by core `cons_prefix_cons`/`nil_prefix`/`prefix_nil`/`prefix_rfl` (no hand-rolled prefix lemmas).
  **ERRATUM caught: maximality at `strs=[]` is NOT vacuous** — the hyp `∀ s∈[], p<+:s` holds for any `p` but
  the conclusion `p <+: [] ` forces `p=[]`, so `strs≠[]` is REQUIRED (matches LC's `1 ≤ length`). General
  rule: "hypothesis vacuous" ≠ "theorem vacuous" — check whether the CONCLUSION still needs proving.

### S44–S47 — wave 7 (DP tupling / carry arithmetic / dedup)
- **S44 L1137 Tribonacci.** `solve_correct : solveFn n = trib n` (axioms `[]`; `solve_eq_spec`
  `[propext,Quot.sound]`). L70's pair-tupling one dimension up: `tribTriple n = (T n, T(n+1), T(n+2))`,
  `(n+1) ↦ let (a,b,c) := …; (b,c,a+b+c)`. Successor case needs `Nat.add_assoc`/`add_comm` (fold builds
  `a+b+c`, recurrence unfolds to `T(n+2)+T(n+1)+T n`) + trailing `rfl` (S9 "rw leaves one rfl short").
- **S45 L2 Add Two Numbers.** `add_correct : value (addFn xs ys) = value xs + value ys` (`value (d::ds) =
  d + 10*value ds`), axioms `[propext,Quot.sound]`. Carry-ripple two-input fold, fuel `xs.length+ys.length
  +1` — the `+1` slack is GENUINE (sum can be one digit longer, `99+1=100`), unlike L21's exact fuel. **State
  the crux lemma CARRY-GENERAL** (`addFuel_value : … → value (addFuel fuel c xs ys) = c + value xs + value
  ys`, `c` free through the induction) — the `c:=0` specialization is `add_correct`. **Trap: the IH's carry
  arg must be `s/10` (what `addFuel` passes), not the pre-division `c+y`** — a mismatched-IH `omega` fails
  citing disconnected atoms. Use `Int.mul_ediv_add_emod` (`Int.ediv_add_emod` is DEPRECATED this toolchain).
  `graph`/`graph_map` need the lambda param explicitly typed (`fun p : List Int × List Int => …`) or `.1`/
  `.2` fail "Invalid projection" (S16 reconfirmed).
- **S46 L9 Palindrome Number.** `palin_correct : isPalinNumFn n = true ↔ (0 ≤ n ∧ toDigits n.toNat =
  (toDigits n.toNat).reverse)`, axioms `[propext,Quot.sound]`. Scalar input ⟹ no SnocList/Tree engine, just
  `A6_1_RelSet` + the digit list built INSIDE the program. Fuel digit-peel (`toDigitsFuel (n+1) n`, recurse
  on fuel not `n` — dividing by 10 is a 2nd shrinking arg, S10 trap); LSB-first is fine (reversal-symmetric).
  Sign guard: `n<0` branch `absurd h0 (by omega)` (arithmetic goal, no Classical.choice, S33).
- **S47 L26 Remove Duplicates Sorted.** `dedup_correct (Sorted xs) : (∀ v, v∈dedupFn xs ↔ v∈xs) ∧ Sorted
  (dedupFn xs) ∧ (dedupFn xs).Nodup`, axioms `[propext,Quot.sound]`; reuses `LC242.Sorted` with NO porting
  (domain already `List Int`). **`List.Nodup` IS `Pairwise (·≠·)` by `Iff.rfl`** (core `nodup_iff_pairwise_
  ne`) — prove the Pairwise, slot into the `.Nodup` headline by defeq (a separate `dedup_nodup := …2.2`
  would be a BANNED one-liner wrapper). Nodup-from-adjacent-dedup needs a `LtHead x l := ∀ v∈l, x<v` strict
  invariant threaded as a 4th conjunct in ONE recursive-theorem induction (S3 extended to recursive
  conjunction). **Trap: `nomatch h` is comma-greedy even across a nested bracket** (`⟨fun v hv => nomatch
  hv, trivial⟩` collapses the outer pair) — write `(nomatch hv)`.

### S48–S51 — wave 8 (reflection / partition / multiset). Two NEW mathlib-free traps.
- **NEW core-tactic trap: `by_contra` is NOT in Lean core** (mathlib-only; core has only `false_or_by_contra`).
  Build contrapositives by hand: `fun hpos => hc (hmem.mpr hpos) : ¬(0 < …)` then `omega`. (Found in L383.)
- **NEW axiom trap (extends S28/S30's `filter_eq_nil_iff` note): core `List.filter_eq_nil_iff` is
  `@[simp]`-TAGGED** — a bare `simp` closing ANY `l.filter p = []` goal auto-reaches for it and silently
  pulls `Classical.choice`. Fix: `simp only [List.filter_cons, hcond, Bool.not_false/not_true]` (explicit
  whitelist, no default set). **`#print axioms` EACH helper lemma individually, not just the headline, to
  bisect a `Classical.choice` leak fast.** (Found in L283.)
- **S48 L234 Palindrome Linked List.** `palin_correct : isPalinFn xs = true ↔ xs = xs.reverse`, axioms
  `[propext]`; `isPalinFn xs := decide (xs = LC206.revFn xs)` (reuse L206 reverse; defeq to `xs.reverse`).
  Extra `palin_reversal_invariant`. **Never `rw`/`congrArg` THROUGH `decide`** (the `Decidable` instance arg
  is fragile) — lift to the Prop reflection lemma, rewrite there (`List.reverse_reverse`), push back via
  `bool_eq_of_iff_true`.
- **S49 L283 Move Zeroes.** `move_correct` = 4 clauses (non-zeros-in-order via `filter nzPred`, length,
  multiset `countL`, `∃k, = filter nzPred ++ replicate k 0`), axioms `[propext,Quot.sound]`. **One crux:**
  core `List.eq_replicate_iff` proves `xs.filter zPred = replicate _ 0`, so `moveZeroesFn = filter nzPred ++
  filter zPred` — textbook stable partition; all clauses reduce to 3 predicate-generic partition laws. For
  `f (List.filter p (a::t))` goals, `rw [List.filter_cons]` BEFORE `cases hb : p a`.
- **S50 L383 Ransom Note.** `canBuild_correct : canBuildFn r m = true ↔ ∀ c, countL r c ≤ countL m c`, axioms
  `[propext,Quot.sound]`. **Check-only-appearing-letters:** ∀-over-Int isn't decidable, so program is
  `r.all (fun c => decide (countL r c ≤ countL m c))`; absent letters `countL r c = 0 ≤ _` free via
  `mem_iff_countL_pos` contrapositive. Bridge `List.all_eq_true` + `decide_eq_true_eq`.
- **S51 L977 Squares of Sorted Array.** `squares_correct : Sorted (sortedSquaresFn xs) ∧ ∀ v, countL
  (sortedSquaresFn xs) v = countL (xs.map (·*·)) v`, axioms `[propext,Quot.sound]`. `sortedSquaresFn xs :=
  LC242.isort (xs.map (·*·))` (square-then-sort; NO `Sorted xs` hyp — correct for any input). **`countL_isort`
  is the ENTIRE honest-multiset proof** (`isort_sorted` alone says nothing about which elements survive);
  `List.map` slots into `countL` for free. Trap: `open X Y (a b)` mixing bare + restricted open on one line
  is a parse error — two separate `open` lines.

### S52–S55 — wave 9 (digit carry / voting / prefix sums / sorted search)
- **S52 L66 Plus One.** `plusOne_correct : value (plusOneFn xs) = value xs + 1` (big-endian `value :=
  foldl (acc*10+d)`), axioms `[propext,Quot.sound]`, NO digit-range hyp. **Big-endian↔little-endian value
  bridge powers-free:** `List.foldl_eq_foldr_reverse` flips the left fold to a right fold over `xs.reverse`,
  then one induction identifies it with little-endian `valueLE`'s front-consing — sidesteps all `append`/
  `10^n` algebra. Trap: `plusOneRev (d::ds)`'s `if` doesn't reduce by `show`/`rfl` for symbolic `d` — use
  `simp only [plusOneRev, if_pos hd, valueLE]`.
- **S53 L169 Majority Element (Boyer–Moore).** `majority_correct (IsMajority nums v) : majorityFn nums = v`
  (`IsMajority nums v := 2*countL nums v > nums.length`), axioms `[propext,Quot.sound]`. **Invariant
  `BMInv xs c k : ∀ w, (w=c → 2*countL xs w ≤ len+k) ∧ (w≠c → 2*countL xs w+k ≤ len)` — phrase BOTH halves
  with `+k` on the LARGER side (never `len-k`)** to dodge Nat-subtraction; the only real `cnt-1` is taken
  with `k≠0` in scope so `omega` closes it. `step_inv` (3 cases) → `bmInv_gen` (induction, `List.foldl_cons`,
  no fuel) → `noncand_le_half` → top-level `by_cases` (+ hand contrapositive, no `by_contra`).
- **S54 L303 Range Sum Query.** `sumRange_correct (i ≤ j+1) (j < len) : sumRangeFn nums i j = rangeSum nums
  i j` (`rangeSum := ((drop i).take (j+1-i)).sum`), axioms `[propext,Quot.sound]`. **Core lacks generic
  `sum_append` (only `sum_append_nat`) and offset `take`-split** — hand-prove `sum_append_int` and
  `take k = take i ++ (drop i).take (k-i)` (induction, `take_succ_cons`/`drop_succ_cons` + one `omega`).
  Prefix-sum-at-index = S10/S23 accumulator threading generalized over `a`: `scanlAdd_get? … = some (a +
  (take k).sum)`. Use `[k]?.getD 0` + `Option.getD_some` (avoids `[k]!`/`Inhabited`).
- **S55 L35 Search Insert Position.** `insertPos_correct (Sorted xs) : i ≤ len ∧ (∀ k v, k<i → xs[k]?=some
  v → v<target) ∧ (∀ v, xs[i]?=some v → target≤v)`, axioms `[propext,Quot.sound]`. **The split headline does
  NOT need `Sorted`** (first-index-≥-target holds for any list; `Sorted`'s head-bound is bound `_hhead`,
  unused) — it bites only in the closed form `insertPosFn xs t = (xs.filter (·<t)).length`. Trap: `1 + i` is
  NOT defeq `i + 1` (`Nat.add` recurses on 2nd arg) — `rw [show 1+i = i+1 from by omega, getElem?_cons_succ]`.
  `injection h` on `some x = some v` gives `x = v` (its order) — state the `have` that way, `omega` finishes.

### S56–S59 — wave 10 (base-2 carry / Pascal / tree symmetry / left-leaf sum)
- **S56 L67 Add Binary.** `addBinary_correct : value (addBinaryFn xs ys) = value xs + value ys` (base-2
  Horner), axioms `[propext,Quot.sound]`. **Pure superposition of S45 (L2 carry-fuel) + S52 (L66 BE↔LE
  bridge), `10→2` everywhere** — `addBitsRev` = L2's `addFuel` with base 2, wrapped in `.reverse` both ends.
  No new trap; just `List.length_reverse` for the fuel bound.
- **S57 L118 Pascal's Triangle.** `pascal_correct : ∀ i<n, ∀ k, (pascalFn n)[i]?.bind (·[k]?) = if k≤i then
  some (binom i k) else none`, axioms `[propext,Quot.sound]`. **`nextRow r := zipWith (·+·) (0::r) (r++[0])`
  makes both boundary 1s automatic**; crux `nextRow (rowOf i) = rowOf (i+1)` via `List.ext_getElem?` +
  core `getElem?_zipWith`/`getElem?_append` REALIZES the binom recurrence. **Trap: a structural-on-first-arg
  recursion still traps `rfl` at a deceptive WILDCARD clause** — `binom i 0` for ABSTRACT `i` is stuck under
  `rfl` (recursor routes through arg 1 first); prove `binom_col0 : ∀ n, binom n 0 = 1` (`|0=>rfl |_+1=>rfl`)
  and rewrite. `rw [hj]` not `subst hj` when the case-split names the free theorem param backwards.
- **S58 L101 Symmetric Tree.** `symmetric_correct : isSymmetricFn t = true ↔ IsSymmetric t`, axioms
  `[propext]`. `mirrorFn` = L226's swap read as a BINARY CROSSWISE compare (`l1 vs r2`, `r1 vs l2`); honest
  inductive `Mirror` (`mnil`/`mnode`), L100/S16 double-induction reflection. **Trap: for a nil/node vacuous
  cross case, `by decide` FAILS "must not contain free variables"** (`l2 a2 r2` free) even though reduction
  ignores them — use `simp [mirrorFn] at h` (→ `false=true`, auto-closes). Forward `&&`→`∧` chain needs a
  trailing `and_assoc` (left-nested); reverse direction doesn't.
- **S59 L404 Sum of Left Leaves.** `sum_left_leaves_correct : sumLeftLeavesFn t = (leftLeafValues t
  false).sum`, axioms `[propext]`. Flag "am-I-a-left-child" threaded DOWN, set fresh from the PARENT each
  descent (`sumLL l true + sumLL r false`, ignoring incoming flag); root starts `false`. **Trap: a 3-clause
  leaf/non-leaf match generates a SIDE-CONDITIONED equation lemma** (`sumLL.eq_3` carries `(l=nil→r=nil→
  False)`; the naive unconditional `node l a r ↦ sumLL l true + sumLL r false` is FALSE at `l=r=nil` unless
  `a=0`) — use L112's full 5-way concrete-shape enumeration so every equation is a bare `rfl`. Honesty =
  two layers: `leftLeafValues` (list-valued, different-looking) summed + inductive `IsLeftLeaf` characterizing
  its membership exactly. `sum_append_int` hand-rolled (core `sum_append` is `List Nat`-only, S54).

### S60–S63 — wave 11 (base-26 / roman / pivot / first-unique)
- **S60 L171 Excel Column Number.** `colNumber_correct : colNumberFn xs = value xs` (base-26 Horner =
  `valueLE xs.reverse`), axioms `[propext,Quot.sound]`. Pure `10→26` reuse of L66/S52's BE↔LE bridge; no
  `if` branch ⟹ even simpler than L66 (`rw [ih]; simp only [valueLE]; omega`).
- **S61 L13 Roman to Integer.** `roman_correct : romanFn xs = xs.sum - 2 * subtractedPart xs` (honest
  closed-form re-characterization: sum all, strip twice each subtractive symbol), axioms `[propext,
  Quot.sound]`. Two-element lookahead recursion `x::y::rest ↦ (if x<y then -x else x) + romanFn (y::rest)`
  is structural on the tail (no fuel). **Trap: `have ih := roman_correct (y::rest)` then `simp only
  [List.sum_cons]` on the GOAL leaves `ih` holding the un-normalized `(y::rest).sum` atom → `omega` sees
  two disjoint atoms and fails** — `simp only [List.sum_cons] at ih` FIRST. (General: normalize a captured
  recursive-call hyp to the goal's normal form before omega/linarith.)
- **S62 L724 Find Pivot Index.** `pivot_correct` = soundness + leftmost + none-completeness, axioms
  `[propext,Quot.sound]`. Per-index iff via `List.take_left`/`drop_left'` alone (NO telescoping — the
  scanned prefix IS carried explicitly; `sum_append_int` used only ONCE to grow the prefix). **Leftmost/none
  invariant generalizes over `pre.length ≤ j`, specialized at `pre=[]`** — the reusable shape for any
  first-match scan (generalize "no earlier match" over the PROCESSED prefix's length). Trap: `unfold
  pivotScan; rw [if_pos]` unfolds BOTH occurrences incl. the RHS recursive call — state the unfold as a
  bare TERM `have hshow : … := if_pos hc` instead.
- **S63 L387 First Unique Character.** `firstUniq_correct` = soundness (`IsFirstUniq`: `countL s c = 1` at
  `i`, all earlier `≥ 2`) + none-completeness, axioms `[propext,Quot.sound]`. **Recount against the FIXED
  full string, not the shrinking suffix** — `scanFrom full l i` closes over `full` while recursing on `l`
  with offset `i`; the spec's honesty lives in this one naming choice. `some`/`none` unified into ONE
  `match`-conclusion invariant lemma. **NEW traps: `split_ifs` is NOT in core** (mathlib-only; plain
  `split` grabs the wrong/outer match) — `by_cases h : P` + `rw [if_pos/if_neg h]`. A `∀ i c, s[i]? = some
  c → …` binder with no anchor leaves `GetElem?` stuck ("type argument is a metavariable") — annotate
  `∀ (i : Nat) (c : Int)`.

### S64–S67 — wave 12 (subsequence / isomorphic / power-of-two / perfect-square)
- **BIG NEW axiom trap (sharpens S33): `omega` closing a NON-arithmetic OR EXISTENTIAL goal from a
  contradictory hypothesis pulls `Classical.choice`** — even the fuel-peel `∃ fuel', fuel = fuel'+1` from an
  impossible `fuel=0`. `omega` proving `False` itself is clean; `omega` proving an arbitrary goal FROM false
  hyps is not. **Rule: when `omega` only derives a contradiction, route through `False.elim (by omega :
  False)`, never let it target the surrounding (existential/non-arith) goal.** (Found in L231.)
- **S64 L392 Is Subsequence.** `subseq_correct : isSubseqFn s t = true ↔ s <+ t` (Lean-core `List.Sublist`,
  NOT `⊆`/S24 bug), axioms `[propext]`. Two-input greedy `a::s',b::t' ↦ if a=b then rec s' t' else rec
  (a::s') t'` stays STRUCTURAL (Lean picks the always-shrinking `t`; the rare two-input recursion needing NO
  fuel). `induction t generalizing s`; branches close by core `cons_sublist_cons`/`sublist_cons_iff`.
- **S65 L205 Isomorphic Strings.** `iso_correct : isIsoFn s t = true ↔ IsIso s t`, `IsIso s t := s.length =
  t.length ∧ ∀ i j, s[i]?=s[j]? ↔ t[i]?=t[j]?` (EQUALITY-PATTERN — no ∃ over functions), axioms
  `[propext,Quot.sound]`. Doubled L1-style `SeenIff` loop invariant for BOTH forward+backward maps (one
  `SeenIff_step`, `m'=m ∨ m'=(x,y)::m`). Bounded "no clash yet" invariant → unbounded spec via `noClash_ext`
  once lengths equal (out-of-range = `none` both sides). **Trap: `by rw […]` passed to a lemma with unpinned
  implicit indices unifies BOTH metavars to the SAME witness** — materialize `hP`/`hQ` as `have`s with the
  index pinned first.
- **S66 L231 Power of Two.** `pow2_correct : isPow2Fn n = true ↔ (0 < n ∧ ∃ k:Nat, n = (2:Int)^k)`, axioms
  `[propext,Quot.sound]`. Fuel recurses on fuel only; `m`-branching via `if`-chain (NOT literal `Nat`
  patterns on `m` — those make equation-compiler side-conditions). `Nat.lt_two_pow_self` (`k<2^k`) supplies
  fuel≥k; `Nat.pow_succ` treats `2^k` as an atom for `omega`. Trap: after `rw [Int.natCast_pow]` the defeq
  `(↑2)^k = (2:Int)^k` needs an explicit trailing `rfl` (reducible-transparency `rw`-rfl won't close it).
- **S67 L367 Valid Perfect Square.** `perfectSquare_correct : isPerfectSquareFn n = true ↔ ∃ k:Nat, k*k =
  n`, axioms `[propext,Quot.sound]`. **Start the upward search at `k=0` so `0=0*0` falls out — no `n=0`
  special-case** (CLAUDE.md "normalize outliers, don't special-case"). Completeness invariant generalizes
  over the search's CURRENT `j` (`j ≤ k0 ≤ j+fuel → k0*k0=n → sqFuel fuel j n = true`); `Nat.mul_le_mul`
  monotonicity rules out overshoot; `Nat.le_mul_of_pos_right` bounds fuel sufficiency.
