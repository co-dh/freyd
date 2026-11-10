# Rel — a closed text language on `Alg`

A program is a text file of object declarations and relation definitions, parsed and run by an interpreter over
leetq's `Alg` (`Rel k v` on qlean columns). Nothing of Lean is reachable from it: no `let`, lambda, tuple of
relations, loop or host call. Iteration is the book's: a fold `⦇e,S⦈` where one fits, `μX : φ(X)` and `R*`
otherwise. Every operator the B&dM companion note writes is in scope. The design is checked by
`leetq/LeetQ/Rel/BlocksRel.lean`, a line-by-line Lean transcription of the program in §g.

## a. Objects and universes

| declaration / form    | `Core` object      | universe                                                            |
|-----------------------|--------------------|---------------------------------------------------------------------|
| `obj X = {A,B,C}`     | `atom long`        | the named elements, coded `0 … k-1`                                 |
| `obj N = 0…n`         | `atom long`        | the numbers `0 … n`; `succ` is partial at `n`                       |
| `A×B`                 | `prod a b`         | `cross` of the two universes, when both have one                    |
| `A+B`                 | `sum a b`          | `inl` of `A`'s, `inr` of `B`'s, when both have one                  |
| `𝒫A`, `[A]`           | `arr a`            | none: `2^|A|` sets, unboundedly many lists                          |
| `obj St = 𝒫(X×X)`     | (alias)            | a name for a derived object; adds no universe                       |

- The universe of every object with one is computed once, when the program is loaded. An object built from an
  `arr` (`𝒫A`, `𝒫A×B`, …) has none.
- `𝟙`, `⊤`, `∼`, `∋`, `π₁`, `π₂`, `dom` on an object WITHOUT a universe run on DEMAND: in `Q e`, the term `e`
  runs on the keys `ran(Q)` composes into it (`𝟙` ↦ `ran(Q)`, `∋` ↦ `ran(Q)∋`, `⊤` ↦ `ran(Q)⊤`). This is exact
  for the operators whose value at a key depends only on that key (column "local" in §b). A term that needs
  such a universe with no left context, or through a non-local operator (`°`, division, `frac`), is a
  front-end error: "`⊤ : 𝒫(X×X) ⟶ N` has no universe; compose a set of states before it".
- An `arr` object as a TARGET has no demand: `⊤ : A ⟶ 𝒫B`, `∈`, `R/S` into `𝒫B`, `P(R)` are errors there; the
  program names the arrays it means (a coreflexive) and composes them.
- Object names live in the front end only. `X` and `N` are both `atom long` in `Core`, so `class Univ` (one
  universe per `Obj`) cannot hold both: the interpreter passes universes explicitly (`idU U`, `top U V`,
  `leq U`, `succ U`), which every `Alg` op already takes.
- Inference: each constant (`𝟙 ⊤ 𝟘 ∋ π₁ π₂ ≤ <`) gets fresh object variables, unified along the term.
  An unresolved one is an error asking for the explicit form `⊤(A,B)`, `𝟙(A)`.

## b. Operators

"sign" is the polarity of each argument (§d); `0` = the bound variable of a `μ` may not occur there. Every
operator is LOCAL — its value at a key depends only on that key, so it may run on demand (§a) — except `°`,
`ran`, the three divisions, `×`, `[R,S]`, `R+S`, `∈` and `P(R)`.

| symbol                         | meaning                                   | `Alg`                          | sign  |
|--------------------------------|-------------------------------------------|--------------------------------|-------|
| `RS`                           | composition, first `R` then `S`           | `≫`                            | `+ +` |
| `R°`                           | converse; a named one by its name (`∈`)   | `°`                            | `+`   |
| `R ∩ S`, `R ∪ S`               | meet, join                                | `∩`, `∪`                       | `+ +` |
| `R − S`                        | set difference                            | `\`                            | `+ −` |
| `∼R`                           | complement, `⊤ − R`                       | `∼`                            | `−`   |
| `R ⇒ S`                        | `∼R ∪ S`                                  | `∼`, `∪`                       | `− +` |
| `𝟘`, `⊤`, `𝟙`                  | empty, every pair, identity               | `zero`, `top`, `idU`           | —     |
| `dom(R)`, `ran(R)`             | coreflexives on keys, on values           | `dom`, `ran`                   | `+`   |
| `R\S`                          | `y (R\S) z ⟺ ∀x. xRy → xSz`               | `leftDiv`                      | `− +` |
| `R/S`                          | right division                            | `rightDiv`                     | `+ −` |
| `frac(R,S)`                    | symmetric division                        | `symDiv`                       | `0 0` |
| `⟨R,S⟩`, `π₁`, `π₂`            | pair, projections                         | `pair`, `outl`, `outr`         | `+ +` |
| `R×S`                          | product                                   | `prod`                         | `+ +` |
| `[R,S]`, `inl`, `inr`, `R+S`   | case, injections, sum                     | `junc`, `inl`, `inr`, `sum`    | `+ +` |
| `Λ(R)`                         | power transpose                           | `transpose`                    | `0`   |
| `∋`, `∈`                       | membership, its converse                  | `mem`, `°`                     | —     |
| `E(R)`                         | existential image                         | `E`                            | `0`   |
| `P(R)`                         | power relator                             | `P`                            | `+`   |
| `union τ nil α cons°`          | the note's set and list maps              | `Arr.union τ nil alpha uncons` | —     |
| `⦇e,S⦈`                        | fold of lists, `S` on the pairs it meets  | `foldBy` (§h)                  | `+ +` |
| `F(R)`                         | the list functor                          | `map`                          | `+`   |
| `est(R)`                       | `∋ ∩ (∈\R°)`, the least                   | `est`                          | `+`   |
| `thin(Q)`                      | the minimal ones                          | `thin`                         | `0`   |
| `filter(p)`, `takewhile(p)`    | the note's list functions                 | `filter`, `takewhile`          | `0`   |
| `length sum head tail`         | the note's list functions                 | `length Arr.sum head tail`     | —     |
| `prefix`, `suffix`             | the note's list functions                 | `«prefix»`, `suffix`           | —     |
| `succ`, `plus`, `≤`, `<`       | on a declared number universe             | `succ plus leq lt`             | —     |
| `μX : φ(X)`, `R*`              | least fixed point, `μX : 𝟙 ∪ RX`          | `iter` in the interpreter      | `+`   |
| `{(a,b),…}`                    | a literal relation                        | `ofPairs`                      | —     |

- `Λ(G) est(Q)` runs as `est Q G` (B&dM's `Λ(S) min R`): both are the `Q`-least value of each key of `G`.
- `−` replaces the earlier design's `\` for difference, because the note writes `\` for left division.
- Not in the language yet (`no` in the architecture table): `⦇R⦈`, `F(R)` on datatypes other than lists;
  `perm`, `bagify`, `setify`, `ordered(≼)`, `sort(≼)`; `inits`, `tails`, `concat`, `zip`, `snoc`, `init`;
  `merge`, sorting sets, binary thinning; tabulation (`array`, `row`, `col`, `tic`, `loop`).

## c. Grammar and precedence

Kept from the earlier design: one level, left to right — `a op₁ b op₂ c = (a op₁ b) op₂ c` for every binary
operator, composition (juxtaposition) included, so the right operand of every operator is one primary and a
composite on the right takes parentheses (`Sπ₁⊤ − (R(S)π₂(π₁° ∪ π₂°))`). Changed: `−` and `⇒` join the
binary operators; `*` is postfix beside `°`; `μ` reaches to the end of its parentheses.

```
program  := line*
line     := 'obj' Word '=' ( '{' Word (',' Word)* '}' | Num '…' Num | object )
          | Name ('(' Name (',' Name)* ')')? '≜' expr
          | 'print' expr | 'check' expr ('⊑' | '=') expr
expr     := primary ( op? primary )*                 -- flat left fold; no op = composition
          | 'μ' Name ':' expr
op       := '∩' | '∪' | '−' | '⇒' | '/' | '\'
primary  := atom ( '°' | '*' )*
atom     := Name | Name '(' expr (',' expr)* ')'     -- a defined operator, or E( ) P( ) Λ( ) est( ) …
          | '⟨' expr ',' expr '⟩' | '[' expr ',' expr ']' | '⦇' expr ',' expr '⦈'
          | const ( '(' object (',' object)? ')' )?   -- 𝟙 𝟘 ⊤ ∋ π₁ π₂ ≤ < succ, objects optional
          | '{' '(' Word ',' Word ')' (',' '(' Word ',' Word ')')* '}' | '(' expr ')'
object   := Word | object '×' object | object '+' object | '𝒫' object | '[' object ']'
Name     := Letter ( '\'' | Digit | SubscriptDigit )*   -- never U u n T o; a Greek letter is a letter
```

## d. Iteration: fold first, `μ` and `*` where a fold cannot

Fold: `R⦇e,S⦈` folds each array `R` reaches, from the values of `e` (a coreflexive), by `S : E×V ⟶ V`, which
runs on the pairs each round meets — so `S` may run on demand (§a). Bounded iteration is a fold over the array
`0…n` of a number universe: `n+1` rounds, each `S` once.

`μX : φ(X)` is accepted when `X` occurs in `φ` only positively: the product of the polarities on the path from
the root of `φ` to each occurrence of `X` (§b column) is `+`, and no occurrence is under a `0` argument. A
parameter of a defined operator carries the polarity its body gives it. Inside a `μ` body no array may grow
without bound (`cons`, `α`, `F(R)`, `⦇e,S⦈` over a list built in the body are refused): the hom-set is then
finite, `φ` monotone, and the iteration from `𝟘` reaches the least fixed point (AOP/A6_2.lean:53 `mu`, the
`Inf` of the prefixed points; the chain `iterZ`, :276) in at most `|⊤|` rounds; the interpreter stops when a
round changes nothing (`Alg.iter` with `==`). `R*` is `μX : 𝟙 ∪ RX` (AOP/A6_7.lean:44); `S R*` runs as
`μY : S ∪ YR` (`comp_star_eq_mu`, AOP/A6_7.lean:264), so `𝟙` needs no universe.

Both stay in the language although Blocks needs neither (table below): the note writes `μX : φ(X)` and the
closure `R*` in chapter 6.

| iteration in Blocks                 | written as                    | why not a fold                               |
|-------------------------------------|-------------------------------|----------------------------------------------|
| `Q`, the reachable states           | fold over `0…6`, step `T`     | —                                            |
| `C`, walk lengths to a goal state   | fold over `0…6`, step `(QT)°` | —                                            |
| `Z`, the chosen path                | fold over `0…6`, step `ν`     | —                                            |
| an unfold then a fold               | not used                      | a fold over `0…n` already bounds each loop   |

The bound is the declared `N`: a shortest plan moves each block at most twice (to the table, then to its
place), so every distance is at most `2|X| = 6`. The `μ` forms of the same three (`ran(s₀T*)`,
`μY : H⊤{(0,0)} ∪ (QTY succ)`, `μY : (s₀⊤{(0,0)})° ∪ (succ°Yν)`) give the same relations (`BlocksRel.Mu`,
guarded) and need no bound: they stop at the depth of the search, where the fold runs all `|N|` rounds.

Cost found by the check: `∪` razes the flat payloads of both parts of an `arr` side and keeps every element,
so a state carried through a round is copied, not shared. `L(s₀,𝟙)` over 7 rounds holds 7 states of 3 pairs on
a payload of 2295 pairs; with `N = 0…27` the fold runs out of memory within 13 rounds. The language is not
the cause; the fix is in `Alg` (§h).

## e. Definitions

- `N ≜ expr` binds a relation. `N(P₁,…,Pₖ) ≜ expr` defines an operator over relations, applied as
  `N(e₁,…,eₖ)`; an argument is substituted, so a demand-run term (`T`) may be an argument.
- A body names only earlier definitions: no recursion except through `μ`. `≜` puts the defined name on the left.

## f. Not in the language

Lean `let`, lambdas, tuples of relations, `iter`, `Except`, `do`, a loop, recursion, first-class operators,
arithmetic beyond `succ`/`plus`/`≤`/`<` on a declared number universe, row order (`num`, `enum`), and every
operator in the "not yet" list of §b. The only failures are the front end's: unknown name, object mismatch,
no universe for a term (§a), a non-positive `μ` (§d), each with its line.

## g. The blocks world and its search

States are the arrays `Λ` gives the pairs of a map `X ⟶ X`; a family of states is `S : I ⟶ X×X`, one state
per key, and the note's formulas read per key. The search is three folds over `0…6`: the reachable states
from `s₀`, each state's walk lengths to a goal state (`est(≤)` gives the distance), and the path that takes in
each state the least move (`est(≼)`) dropping the distance by one.

```
obj X = {A,B,C}                               -- the blocks
obj N = 0…6                                   -- counts: a shortest plan moves each block at most twice
obj St = 𝒫(X×X)                               -- a state: the set of its pairs
S₀ ≜ {(C,A),(A,A),(B,B)}                      -- C on A, A and B on the table
G ≜ {(A,B),(B,C)}                             -- A on B, B on C

R(S) ≜ S ran⟨𝟙,∼𝟙⟩                            -- per key: S ∩ ∼𝟙, b rests on another block
M(S) ≜ Sπ₁⊤ − (R(S)π₂(π₁° ∪ π₂°))             -- per key: ∼(R°⊤ ∪ ⊤R), the moves allowed
S'(S,p) ≜ S − (pπ₁π₁°) ∪ p                    -- per key: (S ∩ ∼(p⊤)) ∪ p, the state after p

c ≜ ⟨𝟙,M(∋)⟩                                  -- St ⟶ St×(X×X): a state, each move it allows
F ≜ S'(π₁∋,π₂)                                -- St×(X×X) ⟶ X×X: the pairs it leads to
T ≜ cΛ(F)                                     -- St ⟶ St: one move
s₀ ≜ ran(Λ(⊤⟨𝟙,S₀⟩))                          -- the start state
r ≜ Λ(s₀⊤(St,N))                              -- the array 0…6, one fold round each
L(D,B) ≜ ran(r⦇ran⟨D,D⊤{(0,0)}⟩, π₂ ∪ (π₂⟨π₁B,π₂ succ⟩)⦈)   -- (s,k): s is k steps of B from D
Q ≜ ran(L(s₀,T)π₁)                            -- the reachable states
g ≜ ran⟨𝟙,G⟩                                  -- the goal's pairs
H ≜ Q − dom(Q⊤g − (Q∋))                       -- the reachable states holding G
C ≜ L(H,(QT)°)                                -- each state with each walk length to H
W ≜ (Cπ₁)°(Cπ₂)                               -- St ⟶ N
δ ≜ Λ(W)est(≤)                                -- the distance to the goal
K ≜ Qc dom(Λ(F)δ succ ∩ (π₁δ))                -- the moves that take the distance down by one
≼ ≜ π₁ < π₁° ∪ (π₁π₁° ∩ (π₂ ≤ π₂°))           -- moves in lexicographic order
σ ≜ Λ(Kπ₂)est(≼)                              -- the move chosen in each state
ν ≜ ⟨dom(σ),σ⟩Λ(F)                            -- the state it leads to
Z ≜ L(s₀,ν)                                   -- the chosen path, with each state's step
ζ ≜ (Zπ₂)°(Zπ₁)                               -- N ⟶ St: the k-th state
plan ≜ ζσ                                     -- N ⟶ X×X: the k-th move
```

`plan` is `{(0,(C,C)),(1,(B,C)),(2,(A,B))}`; from all blocks on the table it is `{(0,(B,C)),(1,(A,B))}`; for
the goal `{(A,B),(B,A)}` no state is in `H`, `δ` is empty, so `σ` is, and `plan` is `𝟘`. `BlocksRel.lean`
guards these (as sets of pairs: `σ` holds each chosen move in 3 rows, because `≫`, `pair` and `est` keep row
multiplicity), the 13 reachable states, the per-key formulas against `Blocks.R`, `M`, `move` on one state,
agreement with `Blocks.plan` and `Blocks.solve`, and the fold forms against the `μ` forms. The whole module,
search included, checks in 13 s.

Transcription rules the Lean check follows (they are what the interpreter does):

| language                        | `Alg`                                                    |
|---------------------------------|----------------------------------------------------------|
| `e` with a source on demand     | a function of the coreflexive `D` composed into it       |
| `𝟙`, `∋`, `⊤` on `D`            | `D`, `D ≫ mem D.val`, `D ≫ top D.val U`                  |
| `Rπ₁`, `Rπ₂`                    | `outl R`, `outr R`                                       |
| `Λ(G)est(Q)`                    | `est Q G`                                                |
| `R⦇e,S⦈`                        | `R ≫ foldOn e.val S (ran R).val`, `S` on the pairs met   |
| `succ` on `N = 0…n`             | `succ U ≫ idU U`: `Alg.succ` maps `n` to `n+1`           |

## h. New types, constructors, approval

Front end (parser data, no semantics): tokens `≜ ∩ ∪ − ⇒ ° * ⟨ ⟩ ⦇ ⦈ μ : 𝟙 𝟘 ⊤ ∋ ∈ Λ ⊑ …` and subscript
digits; `Decl` = `obj` (elements, number range, or object alias) | `def name params body` | `print` | `check`;
`Expr` = the grammar of §c; an object-name table (name ↦ `Obj` and universe), since `Obj` has no names.
Interpreter environment: name ↦ evaluated relation, or ↦ demand-form term for the definitions whose source
has no universe (`c F T`, the operator `L`).

Needs approval (not added; `BlocksRel.lean` defines each locally from `Alg` ops):

| item                                   | why                                                                    |
|----------------------------------------|------------------------------------------------------------------------|
| `foldOn e S X`: `⦇e,S⦈` with `S` run   | `Alg.fold` takes `S : E×V ⟶ V` as a relation, which needs a universe   |
| on the pairs each round meets          | of `E×V`; `V = 𝒫(X×X)` has none. `foldBy` (public) already runs so     |
| `mu bound φ`, `star`                   | `μ`, `*` in the interpreter: `iter` until a round changes nothing      |
| `succ` partial at the top of `N`       | `Alg.succ U` maps the top of `U` out of it; fix: `succ U ≫ idU U`      |
| universes by object name               | `Univ` is keyed by `Obj`, and `X`, `N` are both `atom long` (§a)       |
| `∪` keeps only the payload its rows    | `Obj.raze` concatenates both payloads; a fold whose step has `∪` grows |
| read (`Obj.raze`, `Rel.nub`)           | its `arr` payload by a factor per round and runs out of memory (§d)    |
