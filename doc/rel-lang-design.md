# Rel — a closed text language on `Alg`

A program is a text file of object declarations and relation definitions, parsed and run by an interpreter over
leetq's `Alg` (`Rel k v` on qlean columns). Nothing of Lean is reachable from it: no `let`, lambda, tuple of
relations, loop or host call. Iteration is a fold `⦇e,S⦈`. A relation formula written for one state runs on a
family of states unchanged: the front end lifts it (§e). Every operator the B&dM companion note writes is in
scope. The design is checked by `leetq/LeetQ/Rel/BlocksRel.lean`, a line-by-line Lean transcription of the lifting
rows (§e) and of the program in §g.

## a. Objects and universes

| declaration / form    | `Core` object      | universe                                                            |
|-----------------------|--------------------|---------------------------------------------------------------------|
| `obj X = {A,B,C}`     | `atom long`        | the named elements, coded `0 … k-1`                                 |
| `obj N = 0…n`         | `atom long`        | the numbers `0 … n`; `succ` is partial at `n`                       |
| `A×B`                 | `prod a b`         | `cross` of the two universes, when both have one                    |
| `A+B`                 | `sum a b`          | `inl` of `A`'s, `inr` of `B`'s, when both have one                  |
| `𝒫A`, `[A]`           | `arr a`            | none: `2^|A|` sets, unboundedly many lists                          |
| `obj St = 𝒫(X×X)`     | (alias)            | a name for a derived object; adds no universe                       |

- A universe belongs to the declared object NAME, not to the `Obj` type: `X` and `N` are both `atom long` and have
  different universes. The interpreter keeps a table name ↦ universe and passes it explicitly (`idU U`, `top U V`,
  `leq U`, `succ U`), which every `Alg` op already takes; `class Univ` (one universe per `Obj`) is not used.
- `succ` is partial at the top of its universe: on `N = 0…n` it maps `n` to nothing. The interpreter runs it as
  `succ U ≫ idU U` while `Alg.succ U` maps `n` to `n+1`.
- The universe of every object with one is computed once, when the program is loaded. An object built from an
  `arr` (`𝒫A`, `𝒫A×B`, …) has none.
- `𝟙`, `⊤`, `∼`, `∋`, `π₁`, `π₂`, `dom` on an object WITHOUT a universe run on DEMAND: in `Q e`, the term `e`
  runs on the keys `ran(Q)` composes into it (`𝟙` ↦ `ran(Q)`, `∋` ↦ `ran(Q)∋`, `⊤` ↦ `ran(Q)⊤`). This is exact
  for the operators whose value at a key depends only on that key (column "local" in §b). A term that needs
  such a universe with no left context, or through a non-local operator (`°`, division, `frac`), is a
  front-end error: "`⊤ : 𝒫(X×X) ⟶ N` has no universe; compose a set of states before it".
- An `arr` object as a TARGET has no demand: `⊤ : A ⟶ 𝒫B`, `∈`, `R/S` into `𝒫B`, `P(R)` are errors there; the
  program names the arrays it means (a coreflexive) and composes them.
- Inference: each constant (`𝟙 ⊤ 𝟘 ∋ π₁ π₂ ≤ <`) gets fresh object variables, unified along the term.
  An unresolved one is an error asking for the explicit form `⊤(A,B)`, `𝟙(A)`.

## b. Operators

Every operator is LOCAL — its value at a key depends only on that key, so it may run on demand (§a) — except `°`,
`ran`, the three divisions, `×`, `[R,S]`, `R+S`, `∈` and `P(R)`.

| symbol                         | meaning                                   | `Alg`                          |
|--------------------------------|-------------------------------------------|--------------------------------|
| `RS`                           | composition, first `R` then `S`           | `≫`                            |
| `R°`                           | converse; a named one by its name (`∈`)   | `°`                            |
| `R ∩ S`, `R ∪ S`               | meet, join                                | `∩`, `∪`                       |
| `R − S`                        | set difference                            | `\`                            |
| `∼R`                           | complement, `⊤ − R`                       | `∼`                            |
| `R ⇒ S`                        | `∼R ∪ S`                                  | `∼`, `∪`                       |
| `𝟘`, `⊤`, `𝟙`                  | empty, every pair, identity               | `zero`, `top`, `idU`           |
| `dom(R)`, `ran(R)`             | coreflexives on keys, on values           | `dom`, `ran`                   |
| `R\S`                          | `y (R\S) z ⟺ ∀x. xRy → xSz`               | `leftDiv`                      |
| `R/S`                          | right division                            | `rightDiv`                     |
| `frac(R,S)`                    | symmetric division                        | `symDiv`                       |
| `⟨R,S⟩`, `π₁`, `π₂`            | pair, projections                         | `pair`, `outl`, `outr`         |
| `R×S`                          | product                                   | `prod`                         |
| `[R,S]`, `inl`, `inr`, `R+S`   | case, injections, sum                     | `junc`, `inl`, `inr`, `sum`    |
| `Λ(R)`                         | power transpose                           | `transpose`                    |
| `∋`, `∈`                       | membership, its converse                  | `mem`, `°`                     |
| `E(R)`                         | existential image, `Λ(∋R)`                | `E`                            |
| `P(R)`                         | power relator                             | `P`                            |
| `union τ nil α cons°`          | the note's set and list maps              | `Arr.union τ nil alpha uncons` |
| `⦇e,S⦈`                        | fold of lists, `S` on the pairs it meets  | `foldBy` (§h)                  |
| `F(R)`                         | the list functor                          | `map`                          |
| `est(R)`                       | `∋ ∩ (∈\R°)`, the least                   | `est`                          |
| `thin(Q)`                      | the minimal ones                          | `thin`                         |
| `filter(p)`, `takewhile(p)`    | the note's list functions                 | `filter`, `takewhile`          |
| `length sum head tail`         | the note's list functions                 | `length Arr.sum head tail`     |
| `prefix`, `suffix`             | the note's list functions                 | `«prefix»`, `suffix`           |
| `succ`, `plus`, `≤`, `<`       | on a declared number universe             | `succ plus leq lt`             |
| `{(a,b),…}`                    | a literal relation                        | `ofPairs`                      |
| `R ⊑ S`                        | inclusion: in `check`, and as a test (§e) | `⊑`                            |

- `Λ(G) est(Q)` runs as `est Q G` (B&dM's `Λ(S) min R`): both are the `Q`-least value of each key of `G`.
- `−` replaces the earlier design's `\` for difference, because the note writes `\` for left division.
- Not in the language yet (`no` in the architecture table): `⦇R⦈`, `F(R)` on datatypes other than lists;
  `perm`, `bagify`, `setify`, `ordered(≼)`, `sort(≼)`; `inits`, `tails`, `concat`, `zip`, `snoc`, `init`;
  `merge`, sorting sets, binary thinning; tabulation (`array`, `row`, `col`, `tic`, `loop`); `μX : φ(X)` and
  `R*` (§d).

## c. Grammar and precedence

Kept from the earlier design: one level, left to right — `a op₁ b op₂ c = (a op₁ b) op₂ c` for every binary
operator, composition (juxtaposition) included, so the right operand of every operator is one primary and a
composite on the right takes parentheses (`π₁ < π₁° ∪ (π₁π₁° ∩ (π₂ ≤ π₂°))`). Changed: `−` and `⇒` join the
binary operators; a parameter may declare its type (§e); a body may be a test `expr ⊑ expr` (§e).

```
program  := line*
line     := 'obj' Word '=' ( '{' Word (',' Word)* '}' | Num '…' Num | object )
          | Name ('(' param (',' param)* ')')? '≜' ( expr | expr '⊑' expr )
          | 'print' expr | 'check' expr ('⊑' | '=') expr
param    := Name ( ':' object '⟶' object )?             -- typed: lifted when given a family (§e)
expr     := primary ( op? primary )*                 -- flat left fold; no op = composition
op       := '∩' | '∪' | '−' | '⇒' | '/' | '\'
primary  := atom '°'*
atom     := Name | Name '(' expr (',' expr)* ')'     -- a defined operator, or E( ) P( ) Λ( ) est( ) …
          | '⟨' expr ',' expr '⟩' | '[' expr ',' expr ']' | '⦇' expr ',' expr '⦈'
          | const ( '(' object (',' object)? ')' )?   -- 𝟙 𝟘 ⊤ ∋ π₁ π₂ ≤ < succ, objects optional
          | '{' '(' Word ',' Word ')' (',' '(' Word ',' Word ')')* '}' | '(' expr ')'
object   := Word | object '×' object | object '+' object | '𝒫' object | '[' object ']'
Name     := Letter ( '\'' | Digit | SubscriptDigit )*   -- never U u n T o; a Greek letter is a letter
```

## d. Iteration: a fold

`R⦇e,S⦈` folds each array `R` reaches, from the values of `e` (a coreflexive), by `S : E×V ⟶ V`, which runs on
the pairs each round meets — so `S` may run on demand (§a). Bounded iteration is a fold over the array `0…n` of a
number universe: `n+1` rounds, each `S` once.

| iteration in Blocks                 | written as                    |
|-------------------------------------|-------------------------------|
| `Q`, the reachable states           | fold over `0…6`, step `t`     |
| `C`, walk lengths to a goal state   | fold over `0…6`, step `(Qt)°` |
| `Z`, the chosen path                | fold over `0…6`, step `ν`     |

The bound is the declared `N`: a shortest plan moves each block at most twice (to the table, then to its
place), so every distance is at most `2|X| = 6`.

Not in the language yet: `μX : φ(X)` and `R* ≜ μX : 𝟙 ∪ RX`. They would need a polarity check — `X` only under
arguments of polarity `+` (both of `RS ∩ ∪ ⟨,⟩ × [,] + ⦇,⦈`, the first of `− /`, the second of `⇒ \`, the one of
`° dom ran P F est`), never under `frac Λ E thin filter takewhile` — and no array growing inside the body; then
`iter` from `𝟘` until a round changes nothing reaches the least fixed point (AOP/A6_2.lean:53 `mu`).

Cost found by the check: `∪` razes the flat payloads of both parts of an `arr` side and keeps every element,
so a state carried through a round is copied, not shared. `L(s₀,𝟙)` over 7 rounds holds 7 states of 3 pairs on
a payload of 2295 pairs; with `N = 0…27` the fold runs out of memory within 13 rounds. The language is not
the cause; the fix is in `Alg` (§h).

## e. Definitions, and lifting a formula to a family

- `N ≜ expr` binds a relation. `N(P₁,…,Pₖ) ≜ expr` defines an operator over relations, applied as
  `N(e₁,…,eₖ)`; an argument is substituted, so a demand-run term (`t`) may be an argument.
- A body names only earlier definitions: no recursion. `≜` puts the defined name on the left.

A FAMILY is a relation `F : I ⟶ A×B`; its FIBRE at a key `i` is the relation `A ⟶ B` of the pairs `i` reaches,
`(ran(iF)π₁)°(ran(iF)π₂)` with `i` the coreflexive on that key. `∋ : 𝒫(X×X) ⟶ X×X` is the family of all states
under consideration, each state the fibre at itself.

**Typing.** A parameter declared `S : A ⟶ B` takes either kind of argument; the argument's type decides:

| argument type     | reading                                                                             |
|-------------------|-------------------------------------------------------------------------------------|
| `A ⟶ B`           | one relation: substituted, the body runs as written                                 |
| `I ⟶ A×B`         | a family of index `I`: the body runs LIFTED, each operator by its row below         |
| anything else     | front-end error: "`S : X ⟶ X` given `St ⟶ X`"                                       |

The two readings never collide (`I ⟶ A×B` is never `A ⟶ B`: `B` is not `A×B`). The declaration is needed
because the body's types alone do not decide: an undeclared `S` gets its type from the body, and a body like
`∼(S°⊤ ∪ ⊤S)` types plainly with `S : St ⟶ X×X` — as a relation on `X×X`, a different meaning from "per state".
The declaration is the smallest marker: no new operator, only the parameter's type, and an undeclared
parameter keeps the plain reading.

**Lifted rows.** `R : I ⟶ A×B`; `S` of the type the row names; `D` the keys in demand (a coreflexive on `I`,
by §a from the left context, or `𝟙` of `I` when `I` has a universe); `π₁`, `π₂` and `𝟙` in the right column run
on demand, and the right column is plain, `⟨R,S⟩` there the plain pair of two relations out of `I`. For a row
needing the key and the source together, `Rᴵ ≜ (ρ⟨π₁,π₂π₁⟩)°(ρπ₂π₂) : I×A ⟶ B` with `ρ ≜ ran⟨𝟙,R⟩` the rows of
`R`. The law of every row: at every key `i` in demand, the fibre of the lifted term is the operator applied to
the fibres at `i` (`BlocksRel.lean` guards it for each row marked ✓ on three states and an empty key).

| operator                        | lifted, `I ⟶ …`                            | why the fibre at `i` is right        |
|---------------------------------|--------------------------------------------|--------------------------------------|
| `RS` ✓, `S : I ⟶ B×C`           | `⟨R,S⟩(𝟙 ∩ π₁π₂(π₂π₁)°)⟨π₁π₁,π₂π₂⟩`        | rows of `R`, `S` at `i` whose        |
|                                 |                                            | middles agree                        |
| `R°` ✓                          | `R⟨π₂,π₁⟩`                                 | each row swapped                     |
| `R ∩ S`, `R ∪ S`, `R − S` ✓     | the same terms                             | a row is in both, either, one        |
| `∼R` ✓                          | `D⊤ − R`, `⊤ : I ⟶ A×B`                    | every pair of `A×B` at each key      |
| `R ⇒ S`                         | `D⊤ − R ∪ S`                               | the rows `∼`, `∪`                    |
| `𝟘`                             | `𝟘`                                        | no row                               |
| `𝟙 : A ⟶ A` ✓                   | `D⊤⟨𝟙,𝟙⟩`, `⊤ : I ⟶ A`                     | closed                               |
| `⊤ : A ⟶ B` ✓                   | `D⊤`, `⊤ : I ⟶ A×B`                        | closed                               |
| closed `C : A ⟶ B` ✓            | `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ A` on `dom(C)`         | the fibre `C` at each key            |
| `dom(R)` ✓                      | `R⟨π₁,π₁⟩`                                 | each row `(a,b)` gives `(a,a)`       |
| `ran(R)` ✓                      | `R⟨π₂,π₂⟩`                                 | each row `(a,b)` gives `(b,b)`       |
| `R\S`, `S : I ⟶ A×C`            | `∼(R°(∼S))` by the rows                    | universes of `A×C`, `B×C`            |
| `R/S`, `S : I ⟶ C×B`            | `∼((∼R)S°)` by the rows                    | universes of `A×B`, `A×C`            |
| `frac(R,S)`, `S : I ⟶ C×B`      | `R/S ∩ (S/R)°` by the rows                 | both inclusions                      |
| `⟨R,S⟩`, `S : I ⟶ A×C`          | `⟨R,S⟩(𝟙 ∩ π₁π₁(π₂π₁)°)⟨π₁π₁,⟨π₁π₂,π₂π₂⟩⟩` | pairs of rows of one source          |
| `π₁ π₂ inl inr`                 | closed                                     | the same map at every key            |
| `R×S`, `S : I ⟶ A'×B'`          | `⟨R,S⟩⟨⟨π₁π₁,π₂π₁⟩,⟨π₁π₂,π₂π₂⟩⟩`           | each row of `R` with each of `S`     |
| `[R,S]`, `S : I ⟶ A'×B`         | `R(inl×𝟙) ∪ S(inr×𝟙)`                      | `R`'s rows left, `S`'s right         |
| `R+S`, `S : I ⟶ A'×B'`          | `R(inl×inl) ∪ S(inr×inr)`                  | as `[R,S]`                           |
| `Λ(R)`                          | `(dom(Rᴵ)π₁)°⟨π₂,Λ(Rᴵ)⟩`                   | `Λ(Rᴵ)` groups each `(i,a)`          |
| `∋ ∈ union τ nil α cons°`       | closed, on the arrays in demand            | the same at every key                |
| `E(R)`                          | `Λ(∋R)` by the rows, `∋` closed            | `E(R) = Λ(∋R)`, Algebra.lean:1169    |
| `P(R)`                          | not liftable                               | target `𝒫B`: no universe, no demand  |
| `F(R) filter(p) takewhile(p)`   | closed: closed; a family: not liftable     | one `R` for every array              |
| `⦇e,S⦈`                         | closed: closed; a family: not liftable     | one step for every array             |
| `Λ(G)est(Q)`, `G : I ⟶ A×B`     | closed `Q`: `(dom(Gᴵ)π₁)°⟨π₂,Λ(Gᴵ)est(Q)⟩` | `est` at each `(i,a)`                |
|                                 | a family `Q`: `G ∩ (G°\Q°)` by the rows    | `Q`-below each value of `a`          |
| `thin(Q)` on `G : I ⟶ A×B`      | `G − G(Q − Q°)` by the rows                | `thin Q G`, Algebra.lean:1035        |
| `length sum head tail prefix …` | closed                                     | the same at every key                |
| `succ plus ≤ <`, `{(a,b),…}`    | closed                                     | the same at every key                |
| `R ⊑ S` ✓, a test               | `D − dom(R − S)`, a coreflexive on `I`     | `i` stays iff `R − S` is empty there |

Not liftable:

- `P(R)`: its target `𝒫B` has no universe and, as a target, no demand (§a) — the same error as unlifted.
- `F(R)`, `filter(p)`, `takewhile(p)`, `⦇e,S⦈` given a family: `map` and `foldBy` run ONE relation on every
  array; a relation per key needs the array, or the fold's value, keyed by `I` — a fold on `I×V`, a different
  program the author writes, not a row.

**Mixed terms.**

- The index of a lifted body is the product of the distinct indices of its family arguments. Arguments of one
  index object share the key: `S'(π₁∋,π₂)` has two families of index `St×(X×X)`, read at the same candidate.
  Arguments of different indices `I`, `J` give `I×J`, each re-keyed on demand (`S` at `I` becomes `π₁S`).
- A closed relation in the body (`G`, `𝟙`, `⊤`, a literal) or a plain argument takes the closed row.
- A defined operator applied inside a lifted body to a lifted term runs lifted at the same index (`R(S)` in
  `M`); applied to closed terms it runs plainly and enters by the closed row.
- Front-end errors: an argument type neither the declared one nor `I ⟶ A×B`; a row marked "not liftable" with a
  family argument; a lifted `∼`, `⊤`, `𝟙` or division on a fibre object with no universe; an index with no
  universe and no left context (§a); a test `R ⊑ S` applied to no family ("a test needs a family; write
  `check`").

**Back from a family.** Outside the body a family is an ordinary relation `I ⟶ A×B`. `Λ(F) : I ⟶ 𝒫(A×B)` gives
each key its set of pairs, one state per key, equal fibres one array (`transpose` sorts the values), and a key
with an empty fibre none. So `t ≜ cΛ(F)` is one move `St ⟶ St`: `c` takes each state to its candidates, `Λ(F)`
each candidate to the state it leads to. A test needs no way back: `h(∋)` is already a coreflexive on states.

## f. Not in the language

Lean `let`, lambdas, tuples of relations, `iter`, `Except`, `do`, a loop, recursion, `μ`, `*`, first-class
operators, arithmetic beyond `succ`/`plus`/`≤`/`<` on a declared number universe, row order (`num`, `enum`),
and every operator in the "not yet" list of §b. The only failures are the front end's: unknown name, object
mismatch, no universe for a term (§a), a lifting error (§e), each with its line.

## g. The blocks world and its search

A state is a map `S : X ⟶ X`, `(b,y)` putting `b` on `y` and `(b,b)` on the table. The note's formulas are
written for one state and lifted to the family `∋` of all states (§e). The search is three folds over `0…6`:
the reachable states from `s₀`, each state's walk lengths to a goal state (`est(≤)` gives the distance), and the
path that takes in each state the least move (`est(≼)`) dropping the distance by one.

```
obj X = {A,B,C}                               -- the blocks
obj N = 0…27                                  -- counts: a bound fixed before the search
obj St = 𝒫(X×X)                               -- a state: the set of its pairs
S₀ ≜ {(C,A),(A,A),(B,B)}                      -- C on A, A and B on the table
G ≜ {(A,B),(B,C)}                             -- A on B, B on C

R(S : X ⟶ X) ≜ S ∩ ∼𝟙                         -- b rests on another block
M(S : X ⟶ X) ≜ ∼(R(S)°⊤ ∪ ⊤R(S))              -- the moves allowed
S'(S : X ⟶ X, p : X ⟶ X) ≜ (S ∩ ∼(p⊤)) ∪ p    -- the state after the move p
h(S : X ⟶ X) ≜ G ⊑ S                          -- S holds the goal

c ≜ ⟨𝟙,M(∋)⟩                                  -- St ⟶ St×(X×X): a state, each move it allows
F ≜ S'(π₁∋,π₂)                                -- St×(X×X) ⟶ X×X: the pairs it leads to
t ≜ cΛ(F)                                     -- St ⟶ St: one move
s₀ ≜ ran(Λ(⊤⟨𝟙,S₀⟩))                          -- the start state
r ≜ Λ(s₀⊤(St,N))                              -- the array 0…6, one fold round each
L(D,B) ≜ ran(r⦇ran⟨D,D⊤{(0,0)}⟩, π₂ ∪ (π₂⟨π₁B,π₂ succ⟩)⦈)   -- (s,k): s is k steps of B from D
Q ≜ ran(L(s₀,t)π₁)                            -- the reachable states
H ≜ Qh(∋)                                     -- the reachable states holding G
C ≜ L(H,(Qt)°)                                -- each state with each walk length to H
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

Lines changed from the per-key version:

| line          | before (a per-key rewrite by hand)       | now                                  |
|---------------|------------------------------------------|--------------------------------------|
| `R`           | `R(S) ≜ S ran⟨𝟙,∼𝟙⟩`                     | `R(S : X ⟶ X) ≜ S ∩ ∼𝟙`              |
| `M`           | `M(S) ≜ Sπ₁⊤ − (R(S)π₂(π₁° ∪ π₂°))`      | `M(S : X ⟶ X) ≜ ∼(R(S)°⊤ ∪ ⊤R(S))`   |
| `S'`          | `S'(S,p) ≜ S − (pπ₁π₁°) ∪ p`             | `S'(S,p : X ⟶ X) ≜ (S ∩ ∼(p⊤)) ∪ p`  |
| `g`           | `g ≜ ran⟨𝟙,G⟩`                           | `h(S : X ⟶ X) ≜ G ⊑ S`               |
| `H`           | `H ≜ Q − dom(Q⊤g − (Q∋))`                | `H ≜ Qh(∋)`                          |
| `T`           | `T ≜ cΛ(F)`                              | `t ≜ cΛ(F)`: `T` reads as `⊤`        |

`c` and `F` keep their text; they now apply `M` and `S'` to families, where before the bodies were rewritten.

`plan` is `{(0,(C,C)),(1,(B,C)),(2,(A,B))}`; from all blocks on the table it is `{(0,(B,C)),(1,(A,B))}`; for
the goal `{(A,B),(B,A)}` no state is in `H`, `δ` is empty, so `σ` is, and `plan` is `𝟘`. `BlocksRel.lean`
guards these (as sets of pairs: `≫`, `pair` and `est` keep row multiplicity), the 13 reachable states, the law of
each lifted row marked ✓ in §e, the lifted `R`, `M`, `S'`, `h` against `Blocks.R`, `M`, `move` at every key of a
three-state family and on one state, and agreement with `Blocks.plan` and `Blocks.solve`.

Transcription rules the Lean check follows (they are what the interpreter does):

| language                        | `Alg`                                                    |
|---------------------------------|----------------------------------------------------------|
| `e` with a source on demand     | a function of the coreflexive `D` composed into it       |
| `𝟙`, `∋`, `⊤` on `D`            | `D`, `D ≫ mem D.val`, `D ≫ top D.val U`                  |
| `Rπ₁`, `Rπ₂`                    | `outl R`, `outr R`                                       |
| a lifted row (§e)               | `liftComp liftConv liftDom liftRan liftCompl liftConst   |
|                                 | liftLe`; `∩ ∪ −` as they are                             |
| a lifted body                   | a function of the keys in demand `D` and the families    |
| `Λ(G)est(Q)`                    | `est Q G`                                                |
| `R⦇e,S⦈`                        | `R ≫ foldOn e.val S (ran R).val`, `S` on the pairs met   |
| `succ` on `N = 0…n`             | `succ U ≫ idU U`                                         |

## h. New types, constructors, approval

Front end (parser data, no semantics): tokens `≜ ∩ ∪ − ⇒ ° ⟨ ⟩ ⦇ ⦈ : ⟶ 𝟙 𝟘 ⊤ ∋ ∈ Λ ⊑ …` and subscript digits;
`Decl` = `obj` (elements, number range, or object alias) | `def name params body` | `print` | `check`, a param
with its optional type; `Expr` = the grammar of §c; an object-name table (name ↦ `Obj` and universe), since
`Obj` has no names. Interpreter environment: name ↦ evaluated relation, or ↦ demand-form term for the
definitions whose source has no universe (`c F t`, the operator `L`); the lifting is a rewrite of a body by the
rows of §e before it runs, so it adds no runtime type.

Now in `Alg` (no new type, field or constructor):

| item                                   | in `Alg`                                                               |
|----------------------------------------|------------------------------------------------------------------------|
| `foldOn e S X`: `⦇e,S⦈` with `S` run   | `Alg.foldOn`; `fold`, `length`, `Arr.sum` are specialisations of it    |
| on the pairs each round meets          |                                                                        |
| a payload holds only the cells its     | `Vals.pick` gathers each picked row's slice (array) or value (sum),    |
| rows refer to                          | recursively, so `rows`, `≫`, `nub`, `∪` compact; `foldBy` nubs `pend`  |
| `succ` partial at the top              | `Alg.succ U` keeps `u ↦ u+1` only where `u+1 ∈ U`                      |
