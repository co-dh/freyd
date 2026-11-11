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
| `obj N = m…n`         | `atom long`        | the integers `m … n`, signed (`-3…3`); `succ` is partial at `n`     |
| `A×B`                 | `prod a b`         | `cross` of the two universes, when both have one                    |
| `A+B`                 | `sum a b`          | `inl` of `A`'s, `inr` of `B`'s, when both have one                  |
| `𝒫A`, `[A]`           | `arr a`            | none: `2^|A|` sets, unboundedly many lists                          |
| `obj St = 𝒫(X×X)`     | (alias)            | a name for a derived object; adds no universe                       |

- A universe belongs to the declared object NAME, not to the `Obj` type: `X` and `N` are both `atom long` and have
  different universes. The interpreter keeps a table name ↦ universe and passes it explicitly (`idU U`, `top U V`,
  `leq U`, `succ U`), which every `Alg` op already takes; `class Univ` (one universe per `Obj`) is not used.
- `succ` is partial at the top of its universe: on `N = m…n` it maps `n` to nothing, as `Alg.succ U` does.
- A number is a `long`, its code its value, so `m…n` may be signed: `obj Z = -3…3`, `obj Z = -5…-1`. A range with
  `n < m` is an error at `n` (`3…-3`). Every number word — a range's bound, a literal's word, its membership in a
  range — is read by `String.toInt?` alone, and `m`, `n` must fit a `long`.
- A print lists its rows sorted by element: a number by its value (`-3` before `-1` before `2` before `10`), a
  named element by its name, a pair and an array lexicographically (a prefix first), `inl` before `inr`.
- The universe of every object with one is computed once, when the program is loaded. An object built from an
  `arr` (`𝒫A`, `𝒫A×B`, …) has none.
- `𝟙`, `⊤`, `∼`, `∋`, `π₁`, `π₂`, `dom` on an object WITHOUT a universe run on DEMAND: in `Q e`, the term `e`
  runs on the keys `ran(Q)` composes into it (`𝟙` ↦ `ran(Q)`, `∋` ↦ `ran(Q)∋`, `⊤` ↦ `ran(Q)⊤`). This is exact
  for the operators whose value at a key depends only on that key (column "local" in §b). A term that needs
  such a universe with no left context, or through a non-local operator (`°`, division, `frac`), is a
  front-end error: "`⊤ : 𝒫(X×X) ⟶ N` has no universe; compose a set of states before it".
- An `arr` object as a TARGET has no demand: `⊤ : A ⟶ 𝒫B`, `∈`, `R/S` into `𝒫B`, `P(R)` are errors there; the
  program names the arrays it means (a coreflexive) and composes them.
- Inference: each constant (`𝟙 ⊤ 𝟘 ∋ π₁ π₂ ≤ < succ`, the value verbs of §b) gets fresh object variables, unified along the term.
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
| `inits`, `tails`, `init`       | prefixes, suffixes, all but the last      | `inits`, `tails`, `init`       |
| `cat`, `cat°`, `concat`        | join two lists, every cut in two, flatten | `cat`, `uncat`, `concat`       |
| `snoc`, `snoc°`, `zip`         | append one, split the last off, pair up   | `snoc`, `unsnoc`, `zip`        |
| `perm`, `subseq`               | rearrangements, subsequences              | `perm`, `subseq`               |
| `setify`, `bagify`             | the set, the bag of a list                | `setify`, `bagify`             |
| `ordered(Q)`, `sort(Q)`        | the `Q`-ordered lists, `perm ordered(Q)`  | `ordered`, `sort`              |
| `thinL(Q)`                     | binary thinning, among the subsequences   | `thinL`                        |
| `merge(Q)`, `loop(F)`, `tic`   | merge two lists, `F` folded from the      | `merge`, `loop`, `tic`         |
|                                | left, the non-empty prefixes of `a::xs`   |                                |
| `succ`, `≤`, `<`               | on a declared number universe             | `succ leq lt`                  |
| `plus times minus div mod`,    | `N×N ⟶ N` on a declared number universe:  | `arith` with `Ew.add mul sub`  |
| `max min`                      | `+ · − ⌊/⌋`, q's `mod`, the larger, less  | `idiv imod greater lesser`     |
| `{(a,b),…}`, `{((a,b),c),…}`   | a literal relation, rows nested (§c)      | `col`, a pair of `Vals`        |
| `R ⊑ S`                        | inclusion: in `check`, and as a test (§e) | `⊑`                            |

- `Λ(G) est(Q)` runs as `est Q G` (B&dM's `Λ(S) min R`): both are the `Q`-least value of each key of `G`.
- `−` replaces the earlier design's `\` for difference, because the note writes `\` for left division.
- The list builtins run on the arrays in demand (§a), as `head` does: a constant on its source's arrays, `cat`,
  `zip`, `snoc`, `merge(Q)`, `loop(F)`, `tic` on the pairs in demand; `Q`, `F` closed, as `filter(p)`'s `p`.
  A converse with a name runs as that op (`cat°`, `snoc°`).
- The value verbs `plus times minus div mod max min : N×N ⟶ N` are one builtin, `arith k` with the qlean kernel's
  opcode `k`, run on the pairs in demand (§a) as `Alg.arith k` then the universe of `N`. Each is partial, never a
  default: no row where the result falls outside `N` (`minus` below the bottom, `plus`, `times` past the top, as
  `succ` at the top), where the kernel answers q's null (a divisor `0`; a declared number is never null), or
  where `long` overflows. `div` floors and `mod` takes the divisor's sign, as q's do: on `Z = -3…3`,
  `(-3,2) div` is `-2`, `(3,-2) mod` is `-1`. `succ`, `≤`, `<` on a signed range are the numeric ones: `-1 succ`
  is `0`, `-3 < -1` (`Lang/Test.lean` guards each against Lean's `Int` on every pair of `-3…3`). `max`, `min` on numbers are not B&dM's
  `max R`, `min R` on sets, which the language writes `est(R°)`, `est(R)`. Not exposed: the kernel's `%` (`Ew.div`)
  and `xexp` (`Ew.pow`), whose results are float, and `^` (`Ew.fill`), which on numbers with no null is `π₂`.
- Not in the language yet (`no` in the architecture table): `⦇R⦈`, `F(R)` on datatypes other than lists;
  sorting sets (`setify° ordered(Q)`: its target is lists, which have no demand (§a), and a set has unboundedly
  many ordered listings with repeats); tabulation (`array`, `row`, `col`); `μX : φ(X)` and `R*` (§d).

## c. Grammar and precedence

Composition by juxtaposition and the infix operators `∩ ∪ − ⇒ / \ × +` are one precedence level, left to right;
any other grouping is written with parentheses: `M(S) ≜ ∼(R(S)°⊤ ∪ (⊤R(S)))`.

- On one atom, not operators: postfix `°`, application `N(e,…)`, `dom(R)`, `⊤(A,B)`, the brackets `⟨ ⟩ ⦇ ⦈ { }`,
  and prefix `∼` on the next atom (`∼𝟙`, `∼(p⊤)`).
- `e ⊑ f`, `e = f` is the whole of a test body (§e) or a `check`, not nested.
- A parameter may declare its type (§e), with object variables: `uniq(R : α ⟶ β)`.

```
program  := line*
line     := 'obj' Word '=' ( '{' Word (',' Word)* '}' | Num '…' Num | object )   -- Num ≤ Num
          | Name ('(' param (',' param)* ')')? '≜' ( expr | expr '⊑' expr )
            ( 'where' Name '≜' expr (',' Name '≜' expr)* )?   -- local items (below)
          | 'print' expr | 'check' expr ('⊑' | '=') expr
param    := Name ( ':' object '⟶' object )?             -- typed: lifted when given a family (§e)
expr     := primary ( op? primary )*                 -- composition and infix, one level, left to right
op       := '∩' | '∪' | '−' | '⇒' | '/' | '\' | '×' | '+'
primary  := '∼' primary | atom '°'*
atom     := Name | Name '(' expr (',' expr)* ')'     -- a defined operator, or E( ) P( ) Λ( ) est( ) …
          | '⟨' expr ',' expr '⟩' | '[' expr ',' expr ']' | '⦇' expr ',' expr '⦈'
          | const ( '(' object (',' object)? ')' )?   -- 𝟙 𝟘 ⊤ ∋ π₁ π₂ ≤ < succ plus …, objects optional
          | '{' row (',' row)* '}' | '(' expr ')'
row      := '(' tup ',' tup ')'                       -- a literal's row
tup      := Word | row                                -- a side: a word, or a pair nested to any depth
object   := Word | Var | object '×' object | object '+' object | '𝒫' object | '[' object ']'
Var      := 'α'…'ω' ( '\'' | SubscriptDigit )*            -- in a parameter's type only: an object variable (§e)
Name     := Letter ( '\'' | Digit | SubscriptDigit )*   -- never U u n T o; a Greek letter is a letter
          | Symbol                                    -- one character outside the grammar: `≼`
Word     := ( '-' Digit )? ( Letter | Digit | SubscriptDigit | '\'' )*   -- a name, an element, a number
Num      := '-'? Digit+                               -- a Word that `String.toInt?` reads, within `long`
```

- A sign is an ASCII `-` with a digit right after it, and only where a `Word` is read: a range's bound and a
  literal's word (`{(a,-1)}`, `{((-1,B),-20)}`). `--` starts a comment (`{(a,-1)} -- …` is a literal then a
  comment), and `−` (U+2212) is the difference `R − S`, never a sign. A term never starts with a number, so `R -3`
  is an error at the `-` ("expected the end of the line, found '-'") and `R −3` one at the `3` ("expected a term").

- A run of letters is split at its longest prefix in scope: `Qc` is `Q` then `c`, `π₁B` is `π₁` then `B`.
- A name is defined once: a definition, an object or a parameter may not take a builtin of §b (an entry of the
  operator table: `π₂ is a builtin`), and a definition or an object not a name already defined or declared (`K is
  already defined at line n`), each an error at the second. A parameter may shadow a top-level definition (Chess
  names its board `on` and its parameters `on`), never another parameter of its definition.
- `where x ≜ e, y ≜ f` after a body: each item is in scope in the body and in the items after it, nowhere
  else; its name obeys the rule above and is not a parameter of its definition nor an earlier item. An item is
  its term put in place (it lifts with the body, §e) and is evaluated once by the sharing of §d: `Pin(on) ≜
  q(s,→,ε,κ) ∪ … where s ≜ dom(on{(R,R),(Q,Q)}), ε ≜ e(on), …`.
- A one-argument builtin takes a pair as its parentheses: `ran⟨D,D⊤{(0,0)}⟩`.
- A literal's rows nest alike on each side, to any depth: `{((0,1),1),((1,0),1)} : B×B ⟶ B`. Each leaf position
  is the one declared object holding all its words (named elements, or numbers in its range); a side is the
  product of its leaf positions' objects, nested as the rows nest. Its value is built from one long column per
  leaf position, a product side the pair of its parts' columns.
- A definition with no parameters whose objects its body leaves open (`≼`) is elaborated at each use.

## d. Iteration: a fold

`R⦇e,S⦈` folds each array `R` reaches, from the values of `e` (a coreflexive), by `S : E×V ⟶ V`, which runs on
the pairs each round meets — so `S` may run on demand (§a). Bounded iteration is a fold over the array `0…n` of a
number universe: `n+1` rounds, each `S` once.

| iteration in Blocks                 | written as                    |
|-------------------------------------|-------------------------------|
| `Q`, the reachable states           | fold over `0…27`, step `t`     |
| `C`, walk lengths to a goal state   | fold over `0…27`, step `(Qt)°` |
| `Z`, the chosen path                | fold over `0…27`, step `ν`     |

The bound is the declared `N`: a shortest plan moves each block at most twice (to the table, then to its
place), so every distance is at most `2|X| = 6`.

Not in the language yet: `μX : φ(X)` and `R* ≜ μX : 𝟙 ∪ (RX)`. They would need a polarity check — `X` only under
arguments of polarity `+` (both of `RS ∩ ∪ ⟨,⟩ × [,] + ⦇,⦈`, the first of `− /`, the second of `⇒ \`, the one of
`° dom ran P F est`), never under `frac Λ E thin filter takewhile` — and no array growing inside the body; then
`iter` from `𝟘` until a round changes nothing reaches the least fixed point (AOP/A6_2.lean:53 `mu`).

Cost: a result keeps only the payload its rows refer to (§h), so `L(s₀,𝟙)` over the 28 rounds of `N = 0…27`
holds 28 rows on a payload of at most 3 pairs a row (`BlocksRel.lean` guards it). The interpreter evaluates
every definition, and every sub-term that does not read the round's pairs, once before the fold runs; the
step recomputes only what depends on the round (`Lang/Eval.lean`, `hoist`).

Equal sub-terms are evaluated once (`Lang/Eval.lean`, `hoist`, `ev`):

| sub-term                                  | evaluated                                                      |
|-------------------------------------------|----------------------------------------------------------------|
| closed                                    | once per program: one table of identities runs through it      |
| on demand, inside one evaluation          | once per demand (equal as a set): a lifted body, one fold step |

An identity is structural: the core constructor, its objects, the identities of its parts, and for a value its
rows as a set; nothing printed. Chess's pinned squares repeat `L(De)` per direction and `dom(on{(R,R),(Q,Q)})`
eight times: `rel chess.rel` 3.6 s → 0.7 s.

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
`∼(S°⊤ ∪ (⊤S))` types plainly with `S : St ⟶ X×X` — as a relation on `X×X`, a different meaning from "per state".
The declaration is the smallest marker: no new operator, only the parameter's type, and an undeclared
parameter keeps the plain reading.

**Object variables.** A parameter's type may name object variables: `uniq(R : α ⟶ β) ≜ R ∩ (R°\𝟙)`.

- A variable is a word of one lowercase Greek letter `α`…`ω`, then only primes and subscript digits, that is
  neither a declared object nor a definition in scope at that line (`π` defined as a relation is not a
  variable). A builtin's name (`α`, `τ`) may be a variable: a type holds no relation, so nothing collides.
- Each use instantiates the variables afresh, by first-order matching of the declared types against the
  arguments, left to right, one instantiation per use shared by all parameters: first `A ⟶ B` (one relation),
  and when that fails, `I ⟶ A×B` (a family of index `I`, the body lifted as for a ground type). A family met
  inside a lifted body is matched by its fibre. So `α ⟶ β` given `I ⟶ X×X` outside a lifted body is one
  relation, while `α ⟶ α` is a family.
- A definition with object variables is elaborated at each use, as every definition with parameters is.
- The same variable matched to two objects is a front-end error at the use: "`α` in the type of 'R' is both X
  and N: 'R : α ⟶ α' given X ⟶ N".

**Lifted rows.** `R : I ⟶ A×B`; `S` of the type the row names; `D` the keys in demand (a coreflexive on `I`,
by §a from the left context, or `𝟙` of `I` when `I` has a universe); `π₁`, `π₂` and `𝟙` in the right column run
on demand, and the right column is plain, `⟨R,S⟩` there the plain pair of two relations out of `I`. For a row
needing the key and the source together, `Rᴵ : I×A ⟶ B`, `(i,a) Rᴵ b ⟺ i R (a,b)`, on the pairs (key, source)
in demand: `R` read at their keys, each row `(i,(a,b))` re-keyed as `((i,a),b)` and joined with the pairs
(`Tm.flat`; no `ran` over all of `I`), or keyed through its rows (the cost paragraph below). The law of every row: at every key `i` in demand, the
fibre of the lifted term is the operator applied to the fibres at `i` (`BlocksRel.lean` guards it for each row
marked ✓ on three states and an empty key; `Lang/Test.lean` guards the `est` and `thin` rows against the closed
row).

| operator                        | lifted, `I ⟶ …`                            | why the fibre at `i` is right        |
|---------------------------------|--------------------------------------------|--------------------------------------|
| `RS` ✓, `S : I ⟶ B×C`           | `⟨R,S⟩(𝟙∩(π₁π₂(π₂π₁)°))⟨π₁π₁,π₂π₂⟩`        | rows of `R`, `S` at `i` whose        |
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
| `⟨R,S⟩`, `S : I ⟶ A×C`          | `⟨R,S⟩(𝟙∩(π₁π₁(π₂π₁)°))⟨π₁π₁,⟨π₁π₂,π₂π₂⟩⟩` | pairs of rows of one source          |
| `π₁ π₂ inl inr`                 | closed                                     | the same map at every key            |
| `R×S`, `S : I ⟶ A'×B'`          | `⟨R,S⟩⟨⟨π₁π₁,π₂π₁⟩,⟨π₁π₂,π₂π₂⟩⟩`           | each row of `R` with each of `S`     |
| `[R,S]`, `S : I ⟶ A'×B`         | `R(inl×𝟙) ∪ (S(inr×𝟙))`                    | `R`'s rows left, `S`'s right         |
| `R+S`, `S : I ⟶ A'×B'`          | `R(inl×inl) ∪ (S(inr×inr))`                | as `[R,S]`                           |
| `Λ(R)`                          | `⟨𝟙,Rπ₁⟩⟨π₂,Λ(Rᴵ)⟩`                        | `Λ(Rᴵ)` groups each `(i,a)`          |
| `∋ ∈ union τ nil α cons°`       | closed, on the arrays in demand            | the same at every key                |
| `E(R)`                          | `Λ(∋R)` by the rows, `∋` closed            | `E(R) = Λ(∋R)`, Algebra.lean:1169    |
| `P(R)`                          | not liftable                               | target `𝒫B`: no universe, no demand  |
| `F(R) filter(p) takewhile(p)`   | closed: closed; a family: not liftable     | one `R` for every array              |
| `X⦇e,S⦈` ✓, `X : I ⟶ A×[E]`,    | `⟨𝟙,X⟩⟨π₂π₁,⟨π₁,π₂π₂⟩⦇e,S'⦈ᴵ⟩`;            | each array folded by the seed and    |
| `e : I ⟶ V×V`,                  | `⦇e,S'⦈ᴵ : I×[E] ⟶ V` one `foldOn`,        | step of its own key: `S'` carries    |
| `S : I ⟶ (E×V)×V`               | carrier `I×V`, seeded at each key by `e`,  | the key                              |
|                                 | `S' ≜ ⟨π₂π₁,⟨π₁,π₂π₂⟩⟩⟨π₁,Sᴵ⟩`             |                                      |
| `⦇e,S⦈` alone                   | closed: closed; a family: not liftable     | its arrays come from its left        |
| `Xest(Q)`, `X : I ⟶ A×𝒫B`       | closed `Q`: `X⟨π₁,π₂est(Q)⟩`               | `est` on each value of `X`           |
|                                 | a family `Q`: `G ∩ (G°\Q°)` by the rows,   | `Q`-below each value of `a`          |
|                                 | `G ≜ X⟨π₁,π₂∋⟩`                            |                                      |
| `Xthin(Q)`, `X : I ⟶ A×𝒫B`      | closed `Q`: `X⟨π₁,π₂thin(Q)⟩`              | `thin` on each value of `X`          |
|                                 | a family `Q`: `Λ(G − (G(Q − Q°)))` by the  | `thin Q G`, Algebra.lean:1035        |
|                                 | rows, `G` as for `est`                     |                                      |
| `length sum head tail prefix …` | closed                                     | the same at every key                |
| `inits tails init cat cat°`,    | closed                                     | the same at every key                |
| `concat zip snoc snoc° perm`,   |                                            |                                      |
| `subseq setify bagify tic`      |                                            |                                      |
| `ordered(Q) sort(Q) thinL(Q)`,  | closed: closed; a family: not liftable     | one `Q`, `F` for every array or pair |
| `merge(Q) loop(F)`              |                                            |                                      |
| `succ ≤ <`, `{(a,b),…}`,        | closed                                     | the same at every key                |
| `plus times minus div mod`,     |                                            |                                      |
| `max min`                       |                                            |                                      |
| `R ⊑ S` ✓, a test               | `D − dom(R − S)`, a coreflexive on `I`     | `i` stays iff `R − S` is empty there |

Not liftable:

- `P(R)`: its target `𝒫B` has no universe and, as a target, no demand (§a) — the same error as unlifted.
- `F(R)`, `filter(p)`, `takewhile(p)` given a family: `map`, `filter`, `takewhile` run ONE relation on every
  array and are not `foldOn` with a step of the language, so the keyed fold above does not reach them. The same
  for `ordered(Q)`, `sort(Q)`, `thinL(Q)`, `merge(Q)`, `loop(F)` given a family (`Lang/Test.lean` guards the error).
- `⦇e,S⦈` given a family with nothing on its left: the keyed fold needs the arrays of each key, `X`.

Cost of the keyed fold: the lifted step runs on the pairs (key, (element, value)) a round meets, as the unlifted
step runs on the pairs (element, value). `Sᴵ` is keyed through the rows that built `S` (`Lang/Elab.lean`,
`keyed`), so a closed part runs on the sources in demand and never on its universe at each key:

| `R : I ⟶ A×B` built as                    | `Rᴵ : I×A ⟶ B`                                       |
|-------------------------------------------|------------------------------------------------------|
| `R ∪ S`, `R ∩ S`, `R − S`                 | the same operator on `Rᴵ`, `Sᴵ`                      |
| `D⊤`, `⊤ : I ⟶ A×B`                       | `D⊤`, `⊤ : I×A ⟶ B`                                  |
| closed `C`: `D⊤⟨𝟙,C⟩`, `⊤` onto `dom(C)`  | `dom(π₂C)π₂C`                                        |
| `RS`                                      | `⟨π₁,Rᴵ⟩Sᴵ`                                          |
| `⟨R,S⟩`                                   | `⟨Rᴵ,Sᴵ⟩`                                            |
| `R×S`                                     | `⟨⟨π₁,π₂π₁⟩Rᴵ,⟨π₁,π₂π₂⟩Sᴵ⟩`                          |
| `F` then closed `C`, `F⟨π₁,π₂C⟩`          | `FᴵC`                                                |
| `dom(F)`, `F⟨π₁,π₁⟩`                      | `dom(Fᴵ)π₂`                                          |
| any other (`R°`, `ran`, `Λ`, an argument) | `R` read at the keys in demand, re-keyed by a join   |

A closed sub-term of `Sᴵ` is evaluated once per program (`hoist`), not once per key. The fold reads each pair
(key, array) back by a join on both, never pairing a pair with every key's values of its array (keys squared).
Chess's `L` written as this fold over `0…6`, lifted over the boards and moves, makes `rel chess.rel` 2.6 s, against
0.7 s for the eight-term union and over 3 min with the step read whole at each key; the rest is the fold stepping
every value it holds each round, where `RRR` composes only the last power. So Chess keeps the union.

**Mixed terms.**

- The index of a lifted body is the product of the distinct indices of its family arguments. Arguments of one
  index object share the key: `S'(π₁∋,π₂)` has two families of index `St×(X×X)`, read at the same candidate.
  Arguments of different indices `I`, `J` give `I×J`, each re-keyed on demand (`S` at `I` becomes `π₁S`); a
  third `K` gives `(I×J)×K`, in the order the arguments first name them (`Lang/Test.lean` guards `St×N`).
- A closed relation in the body (`G`, `𝟙`, `⊤`, a literal) or a plain argument takes the closed row.
- A defined operator applied inside a lifted body to a lifted term runs lifted at the same index (`R(S)` in
  `M`); applied to closed terms it runs plainly and enters by the closed row.
- Front-end errors: an argument type neither the declared one nor `I ⟶ A×B`; a row marked "not liftable" with a
  family argument; a lifted `∼`, `⊤`, `𝟙` or division on a fibre object with no universe; an index with no
  universe and no left context (§a); a test `R ⊑ S` applied to no family ("a test needs a family; write
  `check`").

**Back from a family.** Outside the body a family is an ordinary relation `I ⟶ A×B`. `Λ(F) : I ⟶ 𝒫(A×B)` gives
each key its set of pairs, one state per key, equal fibres one array (`transpose` sorts the values), and a key
with an empty fibre none. So `t ≜ cΛ(⇝)` is one move `St ⟶ St`: `c` takes each state to its candidates, `Λ(⇝)`
each candidate to the state it leads to. A test needs no way back: `h(∋)` is already a coreflexive on states.

## f. Not in the language

Lean `let`, lambdas, tuples of relations, `iter`, `Except`, `do`, a loop, recursion, `μ`, `*`, first-class
operators, arithmetic beyond `succ`, `≤`, `<` and the value verbs of §b on a declared number universe (no float
`%`, `xexp`; no infix `+ · −` on numbers, which §c's `+ × −` already spell for relations), row order (`num`,
`enum`),
and every operator in the "not yet" list of §b, shadowing (§c). The only failures are the front end's: unknown
name, a name defined twice or a builtin's name taken (§c), object mismatch, no universe for a term (§a), a lifting
error (§e), each with its line.

## g. The blocks world and its search

A state is a map `S : X ⟶ X`, `(b,y)` putting `b` on `y` and `(b,b)` on the table. The note's formulas are
written for one state and lifted to the family `∋` of all states (§e). The search is three folds over `0…27`:
the reachable states from `s₀`, each state's walk lengths to a goal state (`est(≤)` gives the distance), and the
path that takes in each state the least move (`est(≼)`) dropping the distance by one.

```
obj X = {A,B,C}                               -- the blocks
obj N = 0…27                                  -- counts: a bound fixed before the search
obj St = 𝒫(X×X)                               -- a state: the set of its pairs
S₀ ≜ {(C,A),(A,A),(B,B)}                      -- C on A, A and B on the table
G ≜ {(A,B),(B,C)}                             -- A on B, B on C

R(S : X ⟶ X) ≜ S ∩ ∼𝟙                         -- b rests on another block
M(S : X ⟶ X) ≜ ∼(R(S)°⊤ ∪ (⊤R(S)))            -- the moves allowed
S'(S : X ⟶ X, p : X ⟶ X) ≜ (S ∩ ∼(p⊤)) ∪ p    -- the state after the move p
h(S : X ⟶ X) ≜ G ⊑ S                          -- S holds the goal

c ≜ ⟨𝟙,M(∋)⟩                                  -- St ⟶ St×(X×X): a state, each move it allows
⇝ ≜ S'(π₁∋,π₂)                                -- St×(X×X) ⟶ X×X: the pairs it leads to
t ≜ cΛ(⇝)                                     -- St ⟶ St: one move
s₀ ≜ ran(Λ(⊤(X,X)⟨𝟙,S₀⟩))                     -- the start state
r ≜ Λ(s₀⊤(St,N))                              -- the array 0…27, one fold round each
L(D,B) ≜ ran(r⦇ran⟨D,D⊤{(0,0)}⟩, π₂ ∪ (π₂⟨π₁B,π₂ succ⟩)⦈)   -- (s,k): s is k steps of B from D
Q ≜ ran(L(s₀,t)π₁)                            -- the reachable states
H ≜ Qh(∋)                                     -- the reachable states holding G
C ≜ L(H,(Qt)°)                                -- each state with each walk length to H
W ≜ (Cπ₁)°(Cπ₂)                               -- St ⟶ N
δ ≜ Λ(W)est(≤)                                -- the distance to the goal
K ≜ Qc dom(Λ(⇝)δ succ ∩ (π₁δ))                -- the moves that take the distance down by one
≼ ≜ π₁ < π₁° ∪ (π₁π₁° ∩ (π₂ ≤ π₂°))           -- moves in lexicographic order
σ ≜ Λ(Kπ₂)est(≼)                              -- the move chosen in each state
ν ≜ ⟨dom(σ),σ⟩Λ(⇝)                            -- the state it leads to
Z ≜ L(s₀,ν)                                   -- the chosen path, with each state's step
ζ ≜ (Zπ₂)°(Zπ₁)                               -- N ⟶ St: the k-th state
plan ≜ ζσ                                     -- N ⟶ X×X: the k-th move
```

Lines changed from the per-key version:

| line          | before (a per-key rewrite by hand)       | now                                  |
|---------------|------------------------------------------|--------------------------------------|
| `R`           | `R(S) ≜ S ran⟨𝟙,∼𝟙⟩`                     | `R(S : X ⟶ X) ≜ S ∩ ∼𝟙`              |
| `M`           | `M(S) ≜ Sπ₁⊤ − (R(S)π₂(π₁° ∪ π₂°))`      | `M(S : X ⟶ X) ≜ ∼(R(S)°⊤ ∪ (⊤R(S)))` |
| `S'`          | `S'(S,p) ≜ S − (pπ₁π₁°) ∪ p`             | `S'(S,p : X ⟶ X) ≜ (S ∩ ∼(p⊤)) ∪ p`  |
| `g`           | `g ≜ ran⟨𝟙,G⟩`                           | `h(S : X ⟶ X) ≜ G ⊑ S`               |
| `H`           | `H ≜ Q − dom(Q⊤g − (Q∋))`                | `H ≜ Qh(∋)`                          |
| `T`           | `T ≜ cΛ(F)`                              | `t ≜ cΛ(⇝)`: `T` reads as `⊤`        |

`c` and `⇝` (named `F` before, which is the list functor) keep their text; they now apply `M` and `S'` to families,
where before the bodies were rewritten.

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
| `succ` on `N = 0…n`             | `succ U`, partial at `n`                                 |

## h. New types, constructors, approval

Front end (parser data, no semantics): tokens `≜ ∩ ∪ − ⇒ ° ⟨ ⟩ ⦇ ⦈ : ⟶ 𝟙 𝟘 ⊤ ∋ ∈ Λ ⊑ …` and subscript digits;
`Decl` = `obj` (elements, number range, or object alias) | `def name params body` | `print` | `check`, a param
with its optional type; `Expr` = the grammar of §c; an object-name table (name ↦ `Obj` and universe), since
`Obj` has no names. Interpreter environment: name ↦ evaluated relation, or ↦ demand-form term for the
definitions whose source has no universe (`c ⇝ t`, the operator `L`); the lifting is a rewrite of a body by the
rows of §e before it runs, so it adds no runtime type.

Now in `Alg` (no new type, field or constructor):

| item                                   | in `Alg`                                                               |
|----------------------------------------|------------------------------------------------------------------------|
| `foldOn e S X`: `⦇e,S⦈` with `S` run   | `Alg.foldOn`; `fold`, `length`, `Arr.sum` are specialisations of it    |
| on the pairs each round meets          |                                                                        |
| a payload holds only the cells its     | `Vals.pick` gathers each picked row's slice (array) or value (sum),    |
| rows refer to                          | recursively, so `rows`, `≫`, `nub`, `∪` compact; `foldBy` nubs `pend`  |
| `succ` partial at the top              | `Alg.succ U` keeps `u ↦ u+1` only where `u+1 ∈ U`                      |
