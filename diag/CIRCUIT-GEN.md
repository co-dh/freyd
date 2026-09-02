# CIRCUIT-GEN — design for a circuit-diagram generator (design only, no implementation)

Target: generate the hand-drawn circuit rows of `diag/allegory-axioms.typ` (§13.3.x: `twrun`, `twbox`, `twbr`,
`boxrun`, `convrun`, `mconj`, `fpic`, `disc-copy`, `twrow`, `twpic`) from the same input `scripts/diagram`
already reads.  It is NOT a mode of `scripts/diagram`: the downstream is a different picture language
(wire = object, box = morphism, left to right), so it is its own program with its own table, sharing only
the input term.  The design is a functor: each primitive drawn once (§2), one clause per operator (§3).

Running example, shared verbatim with the spider generator (`cert:` at `diag/allegory-axioms.typ:4121`):

    formula  F(prefix) [nil,⊸ nil ∪ cons] list(p)      src F([A])      tgt [A]

The spider generator reads `[nil,⊸ nil ∪ cons]` as ONE bead; the circuit generator must open it into a
tape fork with a `nil` branch and a `∪` branch.  That difference drives everything below.


## 1. The input

### 1.1 What the shared input is

The input to `scripts/diagram` is the triple `(formula, src, tgt)` plus a signature table.  The formula is
parsed by `scripts/scanline`'s `parse` into the AST (`scanline:24`):

    ('atom', s) | ('comp', [e…]) | ('prod', [e…]) | ('hc', [e…]) | ('conv', e) | ('app', name, e)

Grammar: juxtaposition = composition in diagram order; `×` = product; postfix `°` = converse; `N(e)` =
application; `∘` = the across composite (`hc`); `(…)` groups.  Any OTHER bracket group — `[…]`, `⦇…⦈`,
`{…}` — rides through as ONE atom, unparsed (`⟨x,y⟩` is a node now, §3 row 20); `x%∋` glues to a
bracketed atom as one division token.
`∪`, `∩`, `→`, `,`, `⊸` are not operators: they only ever occur inside those opaque atoms.

### 1.2 Can the circuit generator consume `elaborate()`'s output?

**No, and no change to what `layout()` discards fixes that.**  `elaborate()` is already the SPIDER reading:
`expand()` flattens the term tree into a factor sequence, `peel()` turns objects into stacks of functor
wires, `Lane`s and `Row.arms/legs` are functor-wire bookkeeping, and a bracket atom arrives as a single
bead via `signature()`'s `[,]` lookup.  The circuit ontology (wire = object ×-factor, fork = coproduct)
needs exactly the structure `expand()` destroys.  The share point is UPSTREAM of `elaborate()`:

| shared                          | how                                                                    |
|---------------------------------|------------------------------------------------------------------------|
| `parse`, `spell`, `tidy`        | imported from `scripts/scanline` as `scripts/diagram` already does      |
| the cert triple                 | `(expect, src, tgt)` — same fields, same strings, same call sites       |
| the signature-table PATTERN     | a `diag/circuit-sigs.json` shaped like `hm-sigs.json`, different content|

**Not shared: `norm`.**  `norm` pushes `°` to atoms and applies relator laws — that erases the distinction
§3 needs between `(𝟙×R°)` (converse written on the atom → flipped box) and `(F(∋)f)°` (converse written on
the composite → cup/cap frame).  The circuit generator draws the term AS WRITTEN and has its own
normalizer with its own trust-laws (§1.4).

### 1.3 What each side needs that the other does not

| circuit needs, spider does not                        | spider needs, circuit does not                    |
|-------------------------------------------------------|---------------------------------------------------|
| the ×/+ structure of OBJECTS (`A×[A]`, `𝟏+A×X`)       | the functor-wire stack of an object (`peel`)      |
| map-vs-relation KIND per atom (drives the chamfer)    | bead signatures over functor schemes (`hm-sigs`)  |
| functor DEFINITIONS as polynomials (`FX=𝟏+A×X`)       | the `%∋` E-wire twist on a bead's target          |
| the parsed INTERIOR of `[…]` and `∪`/`⊸`/`→` (§1.5)   | the `hc` (`∘`) operator                           |

So `circuit-sigs.json` carries, per atom: source OBJECT, target OBJECT, `map: true/false`, and optionally
`generator:` (one of `delta nabla bang unit swap proj1 proj2`); per functor name: its polynomial, if any.
Typing is the same unification idea as `eat`/`grow`, run over objects instead of wire stacks: the elaborator
computes every subterm's src/tgt object, and `wires(X)` = the list of ×-factors of `X` (a `+` in an object
is never a wire — it forces a tape, §3).  `F([A])` at a port is one wire until a clause needs it open;
opening uses the same polynomial table (`F([A])=𝟏+A×[A]` is the object-level unfold).

### 1.4 The circuit normalizer (replaces `norm`)

Applied before drawing, on trust, exactly as `norm` trusts `F(R)F(S)=F(RS)`:

1. flatten nested `comp`/`prod`; keep `𝟙` in a `prod` (it is a wire), drop it in a `comp`.
2. `F(x) → unfold` when the table defines `F` as a polynomial: `F(R)` at `FX=𝟏+A×X` becomes the case
   picture of `𝟙_𝟏 + 𝟙_A×R` (a tape with an empty branch and an `𝟙×R` branch).
3. tape fusion `F(R)[f,g] = [f,(𝟙×R)g]` (for `FX=𝟏+A×X`): cancels the `join ▷ fork` that rule 2 followed
   by a case bracket would otherwise draw as two tapes in series.  This is what makes 13.3.3b rows 2–5
   come out as the ONE tape the note draws (§4b).

No `°`-pushing, no `interchange` requirement (fusing `(a×b)(c×d)` to `(ac)×(bd)` draws the same ink either
way; adopt it for tidiness, it is not load-bearing).

### 1.5 The grammar extension (the input change this design requires)

Today's shared grammar CANNOT EXPRESS what the circuit rows draw — `[nil,⊸ nil ∪ cons]` is an opaque atom.
The extension adds productions, in the shared parser, for:

| new node       | surface syntax             | today's reading            |
|----------------|----------------------------|----------------------------|
| `('cup',  …)`  | `x ∪ y`                    | `∪` is an atom character   |
| `('cap',  …)`  | `x ∩ y`                    | `∩` is an atom character   |
| `('case', …)`  | `[x,y]` (top-level comma)  | one opaque atom            |
| `('konst', e)` | `⊸ x`                      | `⊸` is an atom             |
| `('cond', …)`  | `(g→x,y)`                  | unparseable as an operator |
| `('cata', e)`  | `⦇x⦈`                      | one opaque atom            |
| `('fork', …)`  | `⟨x,y⟩` (top-level comma)  | one opaque atom            |

Conservativity condition, so the spider side is untouched: `spell` of every new node reproduces the
original string modulo spacing, and the spider's `signature()` treats any structured node it has no rule
for as its spelled label — i.e. the bracket stays one bead over there.  The `--roundtrip` count must not
move when the extension lands.


## 2. The components

Each primitive exists already; the generator invents no drawing layer.  From `diag/circuit.typ` unless said
otherwise (note-local helpers are in `diag/allegory-axioms.typ`).

| name          | helper                  | draws                                                                  |
|---------------|-------------------------|------------------------------------------------------------------------|
| wire          | `wire`                  | a horizontal strand — the identity on one object factor                |
| box           | `gbox`                  | a relation: chamfer cuts the top-right corner to say which way it runs |
| map box       | `gbox(chamfer: false)`  | a plain rectangle — a map runs one way by construction                 |
| converse box  | `gbox(flip: true, fill: TINT)` | the mirrored chamfer plus pale blue: `R°` at a glance           |
| fraction box  | `gbox` label `frc(x)`   | `x%∋ = Λ(x)`, the transpose — a RECTANGLE (the transpose is a map)     |
| division box  | `divbox`                | `x/y` (`flip:` for `y\x`): numerator ground, divisor tile, slack sliver|
| box run       | `boxrun`                | `((label, width, chamfer), …)` in series on one strand, `LEAD` stubs   |
| copy          | `delta`                 | `Δ : a → a⊗a`, solid dot, two bends out                                |
| merge         | `nabla`                 | `∇ : a⊗a → a`, mirror of copy                                          |
| discard       | `bang`                  | `! : a → I`, wire ending in a solid dot                                |
| create        | `unitR`                 | `? : I → a`, solid dot starting a wire                                 |
| crossing      | `swap`                  | two strands exchanged                                                  |
| cup / cap     | `cupAt` / `capAt`       | a strand bent back on itself, split dots by default                    |
| converse frame| `conv-frame`+`conv-body`| the cup/cap frame; whatever `draw(x)` yields rides the middle strand   |
| meet          | `meet`                  | `Δ ; (upper ⊗ lower) ; ∇` — the convolution `∩`                        |
| tape          | `tape`                  | the rounded pink region: the second product, which carries `+` and `∪` |
| tape fork/join| `tape-fork`/`tape-join` | `▷` opening / `◁` closing the branches; a particle takes one           |
| union region  | `unionbox` (note-local) | tape labelled `∪`: dashed fan hands the input to both branch bodies    |
| constant      | `disc-copy` shape       | `⊸ X`: every input wire discarded at a dot, `X` created box, no left ports |
| port label    | `lab` (note-local)      | the object's name at a wire end or a seam                              |

Derived component, defined once: the n-wire copy (needed by `∩` or a fan at a product object) is `delta`
per wire plus the `swap`s that interleave the copies — no current 13.3.x row uses it, but the clause set
is complete only with it.

Emit target: one generic `cpanel(tree, cert: …)` in the note, the exact analogue of `dpanel` — a walker
over these primitives interpreting a layout tree (`seq` / `stack` / `box` / `frac` / `tape` / `fan` /
`dot` / `frame` nodes), emitting the same lists as `#metadata` so a future circuit sweep can read them
(checker parked; the discipline of "the emitted list IS the list that draws" costs nothing to keep now).
`gbox`, `boxrun`, `unionbox`, `tape-fork/join`, `conv-frame`, `meet`, `divbox` are already the generic
vocabulary; `tw-cons` (hardcodes `cons`), `twpic` (hardcodes the `F([A])` fork), `twrow`, `twrun`, `twbr`,
`fpic` are instances the generator supersedes row by row.

Every `draw(e)` value is a picture with a width, left ports and right ports (each port: y-offset + object
label); `▷` glues right ports to left ports with a `LEAD` stub, `⊘` stacks with the note's strand spacing
(`UIP`, `UDY`).  Branch bodies inside one tape are padded with wire to a common right edge (the `w`
argument `disc-copy`/`tw-cons` already take, computed as the max branch width).


## 3. The operator table

Types reach a clause through the object elaborator of §1.3: every subterm carries its src/tgt object, and
`wires(X)` = the ×-factors of `X`.  Labels are spelled by the shared `spell` with spaces squeezed; in the
law column `⟦e⟧` abbreviates `draw(e)`.

| #  | operator           | type             | picture operation                     | law                          |
|----|--------------------|------------------|---------------------------------------|------------------------------|
| 1  | atom, relation     | sig table `s⟶t`  | chamfered `gbox` across the ports     | `⟦R⟧=box(R)`                 |
| 2  | atom, map          | `map: true`      | rectangle (`chamfer: false`)          | `⟦f⟧=mapbox(f)`              |
| 3  | atom, generator    | `generator:` set | the named dot/stub/crossing           | `⟦π₂⟧=bang⊘wire` `⟦Δ⟧=delta` |
| 4  | `𝟙` at object `X`  | `X⟶X`            | bare wires                            | `⟦𝟙_X⟧=wires(X)`             |
| 5  | `xy` (comp)        | `s⟶m`, `m⟶t`     | juxtaposition, ports glued            | `⟦xy⟧=⟦x⟧▷⟦y⟧`               |
| 6  | `x×y` (prod)       | `s×s'⟶t×t'`      | vertical stack, factors split by sigs | `⟦x×y⟧=⟦x⟧⊘⟦y⟧`              |
| 7  | `e°`, atom         | `t⟶s`            | same box mirrored: `flip` + `TINT`    | `⟦R°⟧=mirror(box(R))`        |
| 8  | `e°`, composite    | `t⟶s`            | cup/cap frame, content upright inside | `⟦e°⟧=frame(⟦e⟧)`            |
| 9  | `F(x)`, polynomial | the polynomial   | unfold and recurse (norm rule 2)      | `⟦F(x)⟧=⟦unfold_F(x)⟧`       |
| 10 | `F(x)`, opaque     | 1 wire `F s⟶F t` | chamfered box labelled `spell(F(x))`  | `⟦list(p)⟧=box("list(p)")`   |
| 11 | `x∪y`              | both `s⟶t`       | `∪` tape: dashed fan, stacked bodies  | `⟦x∪y⟧=fan▷(⟦x⟧⊘⟦y⟧)▷fan`    |
| 12 | `x∩y`              | both `s⟶t`       | convolution                           | `⟦x∩y⟧=Δ*▷(⟦x⟧⊘⟦y⟧)▷∇*`      |
| 13 | `[x,y]` at `𝟏+B`   | `𝟏⟶t`, `B⟶t`     | tape fork, branches, tape join        | `⟦[x,y]⟧=▷(⟦x⟧⊘⟦y⟧)◁`        |
| 14 | `⊸ x`              | `s⟶t`, `x: 𝟏⟶t`  | `bang` per input wire, then `⟦x⟧`     | `⟦⊸x⟧=bang^n▷⟦x⟧`            |
| 15 | `x%∋`              | `s⟶t`, a map     | RECTANGLE, label `frc(spell(x))`      | `⟦x%∋⟧=fracbox(x)`           |
| 16 | `x/y`, `y\x`       | division         | `divbox` (`flip:` = left division)    | `⟦x/y⟧=divbox(x,y)`          |
| 17 | `⦇x⦈`              | `[A]⟶t`          | one box, label spelled, kind by body  | `⟦⦇x⦈⟧=box(spell(⦇x⦈))`      |
| 18 | `(g→x,y)`          | `s⟶t`            | one box as written, kind from parts   | `⟦(g→x,y)⟧=box(spell)`       |
| 19 | `x∘y` (hc)         | —                | REJECTED: spider-only notion          | error naming `∘`             |
| 20 | `⟨x,y⟩`            | `s⟶t`, `s⟶t'`    | copy, both lanes, outputs stacked     | `⟦⟨x,y⟩⟧=Δ*▷(⟦x⟧⊘⟦y⟧)`       |

Notes pinned to rows:

- Rows 7/8 are ONE clause with two structural (syntax-directed) cases, never a term-identity test.  The
  formula decides which picture appears: `(𝟙×R°)` writes `°` on the atom and gets the flipped box
  (13.3.3c); `(F(∋)f)°` writes it on the composite and gets the frame (Theorem 7.1's `mconj` rows).
  Mirroring a composite's picture equals drawing the `°`-pushed form — the three presentations are the
  paper's own theorems (`conv_eq_recip` in `diag/RelSetCB.lean` is the precedent that frame = converse is
  a theorem, not a notation), so drawing the term as written is drawing ONE member of the equality class.
- Row 6: how the type reaches the clause — the src object's ×-factors are split between `x` and `y` by
  unifying each factor list against the two sigs, the same move `eat` makes over lanes.  A product is two
  wires, never one wire labelled `A×B`; only a functor-application object (`F([A])`, `E([A])`) is one wire.
- Rows 12/14: at a product object the copy/discard is per-wire (`Δ*`, `bang^n`), built from the derived
  n-wire copy of §2 — that is where a real crossing can appear, and it costs a `swap`, not an apology.
- Rows 15/17/18: kind (map vs relation, i.e. rectangle vs chamfer) is inferred compositionally — maps
  compose to maps, `x%∋` is always a map, a case/conditional of maps is a map, converse of a non-map is
  not.  That reproduces the note's own flags: `bx-cata` (contains `est`) is chamfered, `bx-prog` (all
  maps) is a rectangle.
- Row 20: a fork copies every input strand and runs both lanes on the copies; the outputs are `x`'s
  wires over `y`'s, unmerged — row 12 less its `∇*`, with row 12's crossing at a product.  The seam
  after a fork is printed whole, like the one after an injection: nothing else names those wires.
- Seam labels: every seam HAS an object (the elaborator knows it); which get printed is presentation.
  Uniform rule: print the ports always, and an interior seam exactly when its object is one wire and
  differs from both printed neighbours — that yields the `E([A])` between the fraction box and `est(R°)`
  in 13.3.3d/f and nothing else on those rows.

The running example through the table: `F(prefix) [nil,⊸ nil ∪ cons] list(p)` — rule 9 unfolds
`F(prefix)`, rule 3 of the normalizer fuses it into the bracket, giving
`[nil, (𝟙×prefix)(⊸ nil ∪ cons)] list(p)`; row 13 draws the fork (`nil` branch above, pair below), row 6+2
puts `prefix` on the tail strand, row 11 the `∪` region with row 14's `⊸ nil` above and row 2's `cons`
below, row 5 appends row 10's `list(p)` box after the join.  That is 13.3.3b row 2, component for
component.


## 4. Where it breaks

Ordered by how much they matter.

**(a) The shared grammar cannot express the circuit rows at all.**  This is the sharpest fact found: every
formula a 13.3.x circuit actually draws — `[nil,⊸ nil ∪ (p×𝟙) cons]`, `(π₁p→cons,⊸ nil)`,
`π₂∪(p×𝟙) cons` — is an opaque atom or unparseable to today's `parse`, because `∪ ∩ → , ⊸` are atom
characters and non-`(` brackets ride through whole.  "They share the input" is true only after the §1.5
grammar extension.  The fix is to the INPUT REPRESENTATION, done once, under the conservativity condition
(spell round-trips; the spider still sees one bead; `--roundtrip` count unchanged) — not an `if` in either
generator.

**(b) 13.3.3b rows 2–5 draw one tape where the functor draws two.**  Compositional `draw` of
`F(prefix) [nil, body]` is `fork ▷ (𝟙 ⊘ 𝟙×prefix) ▷ join` then `fork ▷ (nil ⊘ body) ▷ join` — two tapes in
series.  The note draws ONE tape with `prefix` inside on the tail strand (`twpic`'s `pre:`).  Fix: extend
the normalizer's algebra with the single trust-law `F(R)[f,g] = [f,(𝟙×R)g]` (§1.4 rule 3), the exact
analogue of `norm`'s `F(R)F(S)=F(RS)`.  Without it the generated picture is a correct but uglier equal;
with it, the note's.  Not a special case: it is keyed on node shapes, and it is a theorem.

**(c) The Theorem 7.1 `mconj` rows are two terms plus a `⊑` in one canvas.**  `mconj` draws
`f°Xf`-in-frame, the `⊑`, the right-hand run, AND the shared `A`/`F(EA)` end labels, all in one cetz body.
The term functor's scope is one term → one picture; the relation symbol between two pictures is TABLE
presentation, not an operator of the input.  Right answer: the generator reproduces each SIDE (the frame
side falls out of row 8 applied to `(F(∋)f)°F(est(R))f` — frame around the first factor, run after), and a
thin row helper composes two generated canvases around the `⊑`.  The helper survives; `mconj`'s drawing
body does not.  Accept that the assembly stays hand-shaped glue.

**(d) `twrun`/`mconj`'s `mid:`/`from:` type labels are the author's choice of seam.**  The uniform rule in
§3 reproduces the current rows, but nothing forces the note to keep choosing labellable seams; a future row
wanting a label the rule skips (or none where it prints one) needs a per-call override argument on
`cpanel` — presentation, not algebra.  Declare the rule, keep the override.

**(e) Branch-width equalisation is layout, and must live in the layout algebra only.**  The `w` every
branch body takes today (`disc-copy`, `tw-cons`, `pi2-copy` returning a function of the run) exists because
both copies of a `∪` must reach the same edge.  The generator computes it (max branch width, pad with
wire); if it leaked into the operator clauses the design would be wrong.

**(f) Box widths are hand-tuned per label today** (the `bx-*`/`mb-*` tuples).  Generate them from the
label (Typst `measure` inside `cpanel` at render time, so the generator never guesses font metrics).  The
note's existing widths are not the standard — matching them is a non-goal.

**(g) Rows that stay hand-drawn.**  The Hinze–Marsden column (`tw-hm`, `tpan`, `lpan`/`epan`) is the other
generator's territory.  `cbpan`/§7.4 quotation figures and the `cut`-based complement pictures (phase 9)
quote definitions rather than denote terms — no term input exists for them.  The §13.1 `unzip(F)` displays
DO fit the functor (a 1-in 2-out box from its sig) but are outside 13.3.x and not first-slice.


## 5. The smallest first slice

Three rows, in dependency order; each is one row of `diag/circuit-slice.typ` / `.pdf`, which `make slice` regenerates.

| # | row                | formula                                | src⟶tgt      | exercises                      |
|---|--------------------|----------------------------------------|--------------|--------------------------------|
| 1 | 13.3.3d r1 `twrun` | `S%∋ est(R°)`                          | `F([A])⟶[A]` | comp, fraction box, seam label |
| 2 | 13.3.3c r1 `twrow` | `(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)`           | `A×[A]⟶[A]`  | prod, `𝟙`, atom `°`, `∪`, `⊸`  |
| 3 | 13.3.3b r2 `twpic` | `F(prefix) [nil,⊸ nil ∪ cons] list(p)` | `F([A])⟶[A]` | F-unfold, fusion, fork, post   |

Rows 4–9 are the operator demonstrations `scripts/circuit`'s `SLICE` lists after these three.  Rows 10–39 (the
t60-ports round) are named `<section> :<note line> <helper>`: the ports of each were READ from the note's own
type labels beside the hand-drawn display at that line (`lab(…)[…]` on the helper's input/output wires, the
`ty-` tuple of `mss-pic`, `thpic`/`cyrun`'s first two arguments, or the labelled row of the same `=`-chain),
never typed by hand; two lines on one row draw the same formula at the same ports.

| #  | row                         | formula                                          | src⟶tgt            |
|----|-----------------------------|--------------------------------------------------|--------------------|
| 10 | subseq :2932 `sbA4`         | `[nil%∋,((𝟙×∋)(cons∪π₂))%∋]`                     | `F(E([A]))⟶E([A])` |
| 11 | subseq :2936 `sbA5`         | `[nil 𝟙%∋,((𝟙×∋)(cons∪π₂))%∋]`                   | `F(E([A]))⟶E([A])` |
| 12 | greedy :3920 `mbp`          | `R°R°`                                           | `A⟶A`              |
| 13 | greedy :3925 `mbp`          | `R°`                                             | `A⟶A`              |
| 14 | takewhile :4230 `twp`       | `α prefix list(p)`                               | `F([A])⟶[A]`       |
| 15 | takewhile :4239 `twp`       | `F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]`       | `F([A])⟶[A]`       |
| 16 | takewhile :4244 `twp`       | `[nil,⊸ nil ∪ (p×(prefix list(p))) cons]`        | `F([A])⟶[A]`       |
| 17 | takewhile :4247 `twp`       | `F(prefix list(p))S`                             | `F([A])⟶[A]`       |
| 18 | takewhile :4294 `twp`       | `(𝟙×R°)⊸ nil ∪ (p×R°) cons`                      | `A×[A]⟶[A]`        |
| 19 | takewhile :4299 `twp`       | `⊸ nil ∪ (p×R°) cons`                            | `A×[A]⟶[A]`        |
| 20 | takewhile :4303 `twp`       | `⊸ nil ∪ (p×𝟙) cons R°`                          | `A×[A]⟶[A]`        |
| 21 | takewhile :4307 `twp`       | `⊸ nil R° ∪ (p×𝟙) cons R°`                       | `A×[A]⟶[A]`        |
| 22 | takewhile :4312 `twp`       | `(⊸ nil ∪ (p×𝟙) cons)R°`                         | `A×[A]⟶[A]`        |
| 23 | takewhile :4345 `twp`       | `[nil%∋ est(R°),(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]` | `F([A])⟶[A]`       |
| 24 | takewhile :4348 `twp`       | `[nil,(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]`           | `F([A])⟶[A]`       |
| 25 | takewhile :4351 `twp`       | `[nil,(π₁p→cons,⊸ nil)]`                         | `F([A])⟶[A]`       |
| 26 | takewhile :4422 `twp`       | `(prefix list(p))%∋ est(R°)`                     | `[A]⟶[A]`          |
| 27 | takewhile :4433 :5120 `twp` | `⦇S%∋ est(R°)⦈`                                  | `[A]⟶[A]`          |
| 28 | takewhile :4440 `twp`       | `⦇[nil,(π₁p→cons,⊸ nil)]⦈`                       | `[A]⟶[A]`          |
| 29 | mss :4528 :4925 `mss-pic`   | `(segment sum)%∋ est(≥)`                         | `[A]⟶A`            |
| 30 | mss :4530 `mss-pic`         | `(suffix (prefix sum))%∋ est(≥)`                 | `[A]⟶A`            |
| 31 | mss :4533 `mss-pic`         | `suffix%∋ E(prefix sum) est(≥)`                  | `[A]⟶A`            |
| 32 | mss :4536 `mss-pic`         | `suffix%∋ E((prefix sum)%∋)union est(≥)`         | `[A]⟶A`            |
| 33 | mss :4541 `mss-pic`         | `suffix%∋ E((prefix sum)%∋)E(est(≥)) est(≥)`     | `[A]⟶A`            |
| 34 | mss :4544 :4933 `mss-pic`   | `suffix%∋ E((prefix sum)%∋ est(≥))est(≥)`        | `[A]⟶A`            |
| 35 | filter :5025 `twp`          | `(𝟙×R°)(π₂∪(p×𝟙) cons)`                          | `A×[A]⟶[A]`        |
| 36 | filter :5027 `twp`          | `(π₂∪(p×𝟙) cons)R°`                              | `A×[A]⟶[A]`        |
| 37 | filter :5052 `twp`          | `[nil,(π₂∪(p×𝟙) cons)%∋ est(R°)]`                | `F([A])⟶[A]`       |
| 38 | filter :5055 `twp`          | `[nil,(π₁p→cons,π₂)]`                            | `F([A])⟶[A]`       |
| 39 | filter :5128 `fpic`         | `⦇[nil,(π₁p→cons,π₂)]⦈`                          | `[A]⟶[A]`          |

"Reproduce" means: the generated picture has the same topology as the current row — the same forks,
branches, box order, labels, chamfer/flip/kind marks, dots — judged BY EYE against the rendered PDF
(pp. 43–44/53 today).  NOT byte-equality with the current source and NOT pixel-equality: the note's
existing pictures are explicitly not the standard, and widths, spacing and bend radii are the layout
algebra's to choose.  Step 1 needs no grammar extension (its formula already parses); steps 2 and 3 are
the acceptance test FOR the grammar extension and the two normalizer laws.  `mconj` is deliberately not in
the slice.
