# The string edit tabulation (B&dM §9.2) in the Rel language

Result: the book's tabulation runs in the existing language, with no grammar change and no new builtin. The
recorded obstacle (a fold seed depending on `(b,us)`) is not an obstacle: inside a definition applied to families
(§e of `doc/rel-lang-design.md`) the fold `X⦇e,S⦈` is the keyed fold, and its seed `e` is a family over the same
key as `X`. `nextcol(x,b,us)` with three parameters is exactly that. `loop(F)` is not needed and was not tested.

Three things do stand in the way of a letter-for-letter transcription; each has a workaround that was run:

| limit                                                      | workaround                                         |
|------------------------------------------------------------|----------------------------------------------------|
| a definition applied to families cannot be applied again   | one top-level line `nextcol'` that uncurries       |
| inside a lifted body to families of another index          | `nextcol`; `column` composes it as a closed term   |
| a `where` item `xus` beside a parameter `x` is read as     | `xus(x,us)` as a top-level definition              |
| `x` then `us`                                              |                                                    |
| the book reuses `base`, `step` for the specification and   | `base'`, `step'`, as `edit.rel.md` already does    |
| for the tabulation; a name is defined once                 |                                                    |

Scratch files: `/data/tmp/edit-tab/t1.rel.md` … `t9.rel.md`. Binary: `leetq/.lake/build/bin/rel`, run as
`env REL_MEM_MB=4096 timeout 120 rel FILE`.

## 1. The book's tabulation

`scripts/book page algprog N` (run from the repo root). Printed pages; the book composes right to left and
writes `([e, f])` for the fold.

| page | the book                                                                                         |
|------|--------------------------------------------------------------------------------------------------|
| 227  | `column x y = [mle (u, y) ∣ u ← tails x]`                                                        |
| 228  | `column x = ([fstcol x, nextcol x])`                                                             |
| 228  | `fstcol = tails · list del`                                                                      |
| 228  | `column x ([b] ⧺ y) = nextcol x (b, column x y)`                                                 |
| 228  | `nextcol x (b, us) = ([base (b, last us), step b]) xus`                                          |
| 229  | `xus = zip (x, zip (init us, tail us))`                                                          |
| 229  | `base (b, u) = [[ins b] ⧺ u]`                                                                    |
| 229  | `step b ((a, (u, v)), ws) = [[cpy a] ⧺ v] ⧺ ws` if `a = b`                                       |
| 229  | `step b ((a, (u, v)), ws) = [bmin R ([del a] ⧺ w, [ins b] ⧺ u)] ⧺ ws` otherwise, `w = head ws`   |
| 229  | Gofer: `mle (x,y) = outl (head (column x y))`, `column x = catalist (fstcol x, nextcol x)`       |
| 267  | Gofer prelude: `bmin r = cond r (outl, outr)`, `head`, `tail`, `last`, `init`, `zip`             |

- `R = length° · leq · length` (p.225), so `bmin R (p, q)` is `p` when `p` is shorter than or equal to `q`.
  The recursion displayed on p.228 says `del` "if `m < n`"; the two differ only on a tie, where both are shortest.
- The Gofer program (p.229) pairs each sequence with its length, `(v, length v)`, "for efficiency"; this is the
  only difference from the displayed definitions and is not transcribed here.
- No misprint was found: `init us` has the entries for `[a] ⧺ u`, `tail us` those for `u`, both as long as `x`.

## 2. Each definition in the Rel language

All of these were RUN (`t1.rel.md` for `fstcol`, `base'`, `xus`, `nextcol`; `t2.rel.md` for the rest).

    last : [α] ⟶ α ≜ snoc° π₂
    ne : A×A ⟶ A×A ≜ 𝟙 − dom(π₁ ∩ π₂)
    fstcol(x : 1 ⟶ [A]) : 1 ⟶ [[A+(A+A)]] ≜ x F(del) tails
    base'(b : 1 ⟶ A, u : 1 ⟶ [Op]) : 1 ⟶ [[A+(A+A)]] ≜ ⟨b ins,u⟩cons τ
    bmin : [α]×[α] ⟶ [α] ≜ q π₁ ∪ (π₂ − (q π₂)) where q ≜ dom(⟨π₁length,π₂length⟩(𝟙(N×N) ∩ (π₁ ≤ π₂°)))
    step'(b : 1 ⟶ A) : (A×([Op]×[Op]))×[[Op]] ⟶ [[Op]] ≜ dom(π₁π₁ ∩ (⊤b))⟨⟨π₁π₁cpy,π₁π₂π₂⟩cons,π₂⟩cons ∪ (dom(⟨π₁π₁,⊤b⟩ne)⟨⟨⟨π₁π₁del,π₂head⟩cons,⟨⊤b ins,π₁π₂π₁⟩cons⟩bmin,π₂⟩cons)
    xus(x : 1 ⟶ [A], us : 1 ⟶ [[Op]]) : 1 ⟶ [A×([Op]×[Op])] ≜ ⟨x,⟨us init,us tail⟩zip⟩zip
    nextcol(x : 1 ⟶ [A], b : 1 ⟶ A, us : 1 ⟶ [[Op]]) : 1 ⟶ [[Op]] ≜ xus(x,us)⦇ran(base'(b,us last)), step'(b)⦈
    nextcol' : [A]×(A×[[Op]]) ⟶ [[Op]] ≜ nextcol(⟨⊤,π₁⟩,⟨⊤,π₂π₁⟩,⟨⊤,π₂π₂⟩)π₂
    column(x : 1 ⟶ [A], y : 1 ⟶ [A]) : 1 ⟶ [[Op]] ≜ y⦇ran(fstcol(x)), ⟨⊤x,⟨π₁,π₂⟩⟩nextcol'⦈
    mle : [A]×[A] ⟶ [Op] ≜ column(⟨⊤,π₁⟩,⟨⊤,π₂⟩)π₂ head

| book                    | here                         | note                                                         |
|-------------------------|------------------------------|--------------------------------------------------------------|
| `last` (p.267)          | `last`                       | not in the prelude; `snoc° π₂` beside the prelude's `init`   |
| `fstcol`                | `fstcol(x)`                  | unchanged from `edit.rel.md`                                 |
| `base (b,u)`            | `base'(b,u)`                 | unchanged; prime because `base` is the specification's       |
| `bmin R`                | `bmin`                       | unchanged; `R` is fixed inside (`length ≤ length°`)          |
| `step b`                | `step'(b)`                   | the two cases as two coreflexives: `a = b`, and `ne` on `(a,b)` |
| `xus`                   | `xus(x,us)`                  | top level, not a `where` item (the limit below)              |
| `nextcol x (b,us)`      | `nextcol(x,b,us)`            | the book's fold, seed `base'(b,us last)` a family            |
| —                       | `nextcol'`                   | `nextcol` uncurried: `(x,(b,us)) ↦ nextcol x (b,us)`         |
| `column x`              | `column(x,y)`                | the book's fold over `y`, seed `fstcol(x)`                   |
| `mle (x,y)`             | `mle`                        | `head (column x y)`                                          |

- `ne` is the test "otherwise" of `step`; the book has no name for it. It is a closed coreflexive on `A×A`
  because `𝟙 − …` on `(A×([Op]×[Op]))×[[Op]]`, an object with no universe, was not tried.
- In `step'`, `π₁π₁` is `a`, `π₁π₂π₁` is `u`, `π₁π₂π₂` is `v`, `π₂` is `ws`, `⊤b` is `b`.

Output of `t1.rel.md` (`x₀ = a b`, `b₀ = b`; `inl` is `cpy`, `inr inl` is `del`, `inr inr` is `ins`):

    fstcol(x₀) = {(∗, [inr inl a inr inl b] [inr inl b] [])}
    base'(b₀, fstcol(x₀) last) = {(∗, [[inr inr b]])}
    xus(x₀, fstcol(x₀)) = {(∗, (a, (inr inl a inr inl b, [inr inl b])) (b, ([inr inl b], [])))}
    nextcol(x₀, b₀, fstcol(x₀)) = {(∗, [inr inl a inl b] [inl b] [inr inr b])}

## 3. The complete program and the check

`/data/tmp/edit-tab/t2.rel.md` is `edit.rel.md` down to `spec`, then the block of section 2, then:

    x₀ : 1 ⟶ [A] ≜ {(∗,a b)}
    y₀ : 1 ⟶ [A] ≜ {(∗,b a)}
    print column(x₀,y₀)
    print D mle
    check D mle ⊑ spec
    check D mle length 𝟙(N) = (spec length 𝟙(N))

Observed: exit 0, both checks pass, 0.17 s wall.

    column(x₀, y₀) = {(∗, [inr inl a inl b inr inr a] [inl b inr inr a] [inr inr b inr inr a])}

- `D mle` has one sequence for each of the 49 pairs of strings of length ≤ 2 over `{a,b}`.
- `check D mle ⊑ spec`: each is a shortest edit sequence. `check D mle length 𝟙(N) = (spec length 𝟙(N))`: every
  pair of `D` has one, of the specification's length.
- `check D mle = spec` fails, as it must (`t3.rel.md`, exit 1): `spec` holds every shortest sequence, `mle` one
  (`([a],[b])` has `del a ins b` and `ins b del a`; `mle` gives the first). This run also shows a `check` is
  evaluated.

Timing of the tabulation alone (no `spec`):

| run                                              | file         | pairs | wall                         |
|--------------------------------------------------|--------------|-------|------------------------------|
| all pairs of strings of length ≤ 2               | `t4.rel.md`  | 49    | 0.11 s                       |
| length ≤ 3                                       | `t7.rel.md`  | 225   | 0.61 s                       |
| length ≤ 4                                       | `t8.rel.md`  | 961   | 12.4 s (50 s CPU)            |
| length ≤ 5                                       | `t6.rel.md`  | 3969  | stopped at 4126 MB, 34 s     |
| one pair of strings of length 8, `x₀` closed     | `t9.rel.md`  | 1     | 0.55 s                       |

One pair is cheap; many keys at once is not, and grows faster than the number of pairs. The cause was not
diagnosed (the keyed fold of `column` holds every key's column each round, and `nextcol'` is a second lifted fold
under it). `t9.rel.md` writes the fold in place with a closed `x₀`:
`y₀⦇ran(fstcol(x₀)), ⟨⊤x₀,⟨π₁,π₂⟩⟩nextcol'⦈head`.

## 4. The limits met, with the interpreter's messages

**A lifted definition applied inside a lifted body to families of another index.** The book's
`column x = ([fstcol x, nextcol x])` puts `nextcol x (b,us)` in the step of a fold whose own key is `x`. Written
directly (`t2.rel.md`, first version):

    column(x : 1 ⟶ [A], y : 1 ⟶ [A]) : 1 ⟶ [[Op]] ≜ y⦇ran(fstcol(x)), nextcol(⟨⊤,⊤x⟩,⟨⊤,π₁⟩,⟨⊤,π₂⟩)π₂⦈

    line 31, col 71: 'x : 1 ⟶ [A]' given a family of fibre A×[[A+(A+A)]] ⟶ 1×[A]

and with the uncurrying written in place, `⟨⊤x,⟨π₁,π₂⟩⟩(nextcol(⟨⊤,π₁⟩,⟨⊤,π₂π₁⟩,⟨⊤,π₂π₂⟩)π₂)`:

    line 31, col 84: the index of a family: found [A]×(A×[[A+(A+A)]]), expected [A]×[A]

- Inside a lifted body a family argument is matched by its fibre (§e), so a family over the step's pairs `(b,us)`
  is not accepted there, and an application to closed families of index `J` is taken for one of the body's index
  `I`.
- The class it blocks: a curried book function `f x (b,us)` whose body is a fold with a seed depending on
  `(b,us)`, used as the step of another fold that is itself keyed by `x`. Every column-by-column tabulation has
  this shape.
- The workaround is general and stays in the language: name the uncurried form at top level, where its arguments
  are closed (`nextcol'`), and compose it in the outer step. It costs one definition whose name the book does not
  have.
- The smallest addition that would remove `nextcol'`: inside a lifted body of index `I`, an application whose
  arguments are all closed families of one index `J` elaborates as it does at top level (a closed term), instead
  of unifying `J` with `I`. That is the second message above turned into the closed row; it needs no nested
  lifting. Not required for this program.

**A `where` item whose name starts with a parameter's name** (`t5.rel.md`):

    nextcol(x : 1 ⟶ [A], b : 1 ⟶ A, us : 1 ⟶ [[Op]]) : 1 ⟶ [[Op]] ≜ xus⦇ran(base'(b,us last)), step'(b)⦈ where xus ≜ ⟨x,⟨us init,us tail⟩zip⟩zip

    line 17, col 70: the source of the right factor of a composition: found 1, expected [A]

`xus` in the body is read as `x` then `us`: the `where` item is not in scope when the run of letters is split
(§c says the longest prefix in scope). With `xus` a top-level definition the same line runs. This is a defect of
the splitting, not of the language's design; the fix is to split with the `where` names in scope.

**Not a limit: the seed.** `xus(x,us)⦇ran(base'(b,us last)), step'(b)⦈` in `nextcol` is the row `X⦇e,S⦈` of §e
with `X`, `e`, `S` all families of the index of `(x,b,us)`. The comment in `edit.rel.md` ("a seed here is closed
or a family of the keys of the fold's own left") is true and is satisfied: the fold's left `xus(x,us)` has the
same key as `base'(b,us last)`.

## Recommendation

- Paste the block of section 2 and the two `check`s of section 3 into `leetq/programs/edit.rel.md`, replacing
  the paragraph that says `nextcol` and `column` are not written and the fenced pseudo-code after it.
- Decide whether `nextcol'` may stay; if not, make the addition of section 4.
- Fix the `where` split so `xus` can be the `where` item the book writes.
- The cost over many keys (section 3) is a separate question for the keyed fold.
