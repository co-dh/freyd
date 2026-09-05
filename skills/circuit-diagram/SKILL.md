---
name: circuit-diagram
description: Drawing or reading the note's CIRCUIT pictures — a wire is an object, a box a morphism, a product two wires — plus the generator scripts/circuit, the cpanel/circuit Typst files, type labels, and cetz mechanics.
---

# Circuit diagrams

## Decide the convention first, and say so in the document

The note draws in two languages that share nothing but a pen. This file is the CIRCUIT one: a wire
is an OBJECT, a box a MORPHISM, parallel wires are `⊗`, and the picture reads left to right.

The other is Hinze–Marsden (`skills/string-diagram`): a wire is a FUNCTOR, a bead an arrow, a region
a category, and the picture reads top to bottom. **The decision rule:** a circuit cannot draw a
functor applied to a morphism without Melliès' functorial box, so anything whose content is a
functor's action on arrows — folds, monads, adjunctions, naturality — is NOT a circuit. Anything
whose content is copying, discarding, forking and converse IS. A document may use both; at the
switch, say in one line that the convention has changed and why.

A panel drawn in the wrong convention is not slightly wrong, it is transposed — every object becomes
a region, every arrow becomes a wire — and it still looks like a plausible picture. Check one label:
*is this thing an object or a functor?*

## The calculus

- A **wire is an object**, a **box is a morphism**; boxes strung along a wire compose.
- Parallel wires are the tensor `⊗`; the empty picture is the unit `I`.
- **A PRODUCT IS TWO WIRES. Never one wire labelled `A×B`.** The whole point of the notation is that
  `×` is not a box and costs no notation — it is the second wire. It follows that `R×S` is TWO boxes,
  one per wire, never a single box labelled `R×S`; that `π₁` is a discard on the second wire, not a
  box; and that a morphism into or out of a product has that many ports. If a box will not fit its
  ports, make the box taller or the picture wider — do NOT collapse the pair onto one wire. Collapsing
  is what makes a picture say nothing the formula did not already say.
- A cartesian / Frobenius structure adds four generators, drawn as dots and stubs rather than boxes:
  **copy** `Δ : A → A⊗A`, **discard** `! : A → I`, **merge** `∇ : A⊗A → A`, **create** `? : I → A`.
  Copy and discard are the comonoid, merge and create the monoid. In `Rel`, `∇ = Δ°` and `? = !°`.
- **Converse `°` is reflection**: flip the picture in the vertical axis. A cup and a cap bend a wire back
  on itself, and it is the bend, not the box, that makes the converse.
- Direction: pick left-to-right or right-to-left ONCE, state it in the file header, and never vary it. Two
  pictures of the same arrow that disagree about direction cannot be read against each other.
- Typical helper set: a straight `wire`; a labelled box with a corner cut so it says which way it runs; a
  `bend` for a strand that must arrive horizontally; a `dot` for a generator; `cup`/`cap`; a wire `swap`.
- **Square box = a map, chamfered box = a relation.** `E(R)` is ALWAYS a map (`E : Rel → Fun`,
  `E(R) = Λ(∋R)`), so its square is right; judge map-or-relation from the operator's own definition,
  never from the type of its argument.

## Count the ports from the TYPE, and label the wire with the object

- Every port comes off the source or target object, split all the way down its `×`-factors. A port
  the type says is a pair and the picture draws as one wire is a bug, not a simplification.
- **A wire may never be labelled with an arrow's name.** A label that would type-check as a morphism
  belongs in a box.
- Object labels at wire ends and seams (user decisions 2026-09-01): the label TOUCHES its wire — the
  wire runs 0.4 of a mono advance INTO the label box, because the gap people see is the glyph's side
  bearing, not an inset; the label is a muted steel blue (`TYCOL`, `#5f7fa0`, in `diag/note-style.typ`)
  so box names stay the loudest thing on the page.
- Application in a type label is juxtaposition — `F[A]`, `EF[A]`, `E[A]`, `E tree A`, `tree A` — a
  space only beside a multi-letter name, nothing between one-letter functors or before `[`; n equal
  factors print as a power, `[A]²`, `E[A]²`; binary `F(A,B)` keeps its parentheses. That is the LABEL
  PRINTER only (`lshow` in `scripts/circuit`) — the canonical object printer, the signature table and
  the `cert:` strings are unchanged.

## Some steps have no picture. Leave the cell empty.

A step whose content is a **conjunction** ("`X ⊑ A` and `X ⊑ B`") has no shape: the calculus draws
composites, not "and". A union `∪` DOES have one — a tape enclosing the branches — so a table column
in this convention answers for `∪` where a Hinze–Marsden column beside it cannot, which is fine as
long as each column says which calculus it is. An empty cell is the honest answer; a picture that
means nothing is not.

**When a law's algebra is a union of branches, draw the COMPLICATED branch.**
`[nil,(π₁p→cons,⊸ nil)]` and `⊸ zero ∪ plus` say everything interesting in one branch; the other is a
constant or an identity and its panel is a wire with one box on it. Drawing both doubles the width to
show a picture the reader can reconstruct from the formula. Draw the branch that carries the algebra's
work, and let the caption name the branch it is.

## Which tool draws which

| convention    | generator         | emits                    | signatures                |
|---------------|-------------------|--------------------------|---------------------------|
| circuit       | `scripts/circuit` | one `#cpanel(...)` call  | `diag/circuit-sigs.json`  |
| Hinze–Marsden | `scripts/diagram` | one `#dpanel(...)` call  | `diag/hm-sigs.json`       |

`scripts/circuit` reads the formula in the note's own notation and needs `--src`/`--tgt`, because a
formula alone does not fix the ports. It emits a `cert:` recording the input, so a pasted picture
certifies itself, and it has `--compare` (rebuild every `#cpanel` literal in the note from its own
`cert:` and fail on drift) and `--write` (splice the rebuild over it).

Run `./scripts/circuit -h` for its flags, its modes and one runnable line per mode. That help is the
flag list; it is not copied here, and it is where to look before reading the source.

## Where the code lives

| file                   | holds                                                                    |
|------------------------|--------------------------------------------------------------------------|
| `diag/circuit.typ`     | the primitives: `wire`, `bend`, `gbox`, `delta`/`nabla`, `tape`, `conv`   |
| `diag/cpanel.typ`      | `cpanel`, the panel a generated `cert:` renders through                   |
| `diag/cetz-nodraw.typ` | cetz with the `nodraw` switch, and `d`/`lw` — the pen BOTH conventions use |
| `scripts/circuit`      | the generator                                                             |
| `scripts/relexpr.py`   | the note's relation notation — `parse`, `spell`, `norm` — read by both     |
| `diag/circuit-sigs.json` | what each atom is an arrow between, and whether it is a map              |

`circuit.typ` and `cpanel.typ` import nothing from the Hinze–Marsden files, and those import nothing
from these. The one shared place is `cetz-nodraw.typ` (the pen) and `relexpr.py` (the notation): a
helper wanted by both goes there, never copied into both.

**IMPORT BY NAME, NOT WITH `*`.** `delta`, `nabla`, `cap`, `cup` and `dot` are also Typst math symbols
(δ, ∇, ∩, ∪, ⋅). A wildcard import shadows them and `$nabla$` then silently typesets a drawing function
instead of ∇, with no error.

## Check a panel by SCAN LINE — mechanical, and it needs no rendering

Sweep a vertical line across the picture, along the direction it composes. Every cut meets each live
wire in exactly ONE point, so it reads as an ordered list of objects — the object the composite is at,
at that stage.

- Between two consecutive boxes the cut may not change: same wires, same order.
- At a box, the cut just before it is exactly the box's SOURCE and the cut just after exactly its
  TARGET. Every wire the source names must touch the box, and no wire outside the source may touch it.
- At a copy, discard, merge or create, the cut changes by exactly that generator's arity — a strand
  appears or disappears and nothing else moves.
- The first cut is the whole composite's source, the last its target. If either disagrees with the
  statement above the picture, the picture is of a DIFFERENT ARROW — commonly one summand of it.
- Where a cut is not a well-formed object, or a box's source is not what the cut says, write down the
  failing cut's wire list. That list is the diagnosis; nothing further is needed.

The mechanical form of this check is `./scripts/circuit --compare diag/allegory-axioms.typ`: it
rebuilds every `#cpanel` literal from its `cert:` — the formula plus `--src`/`--tgt` — so a picture
that no longer denotes its stated arrow cannot survive a rebuild. It must end `0 drifted`.

## Composition order — where translations get silently reversed

- **Diagram order, by juxtaposition**: `xy` is first `x`, then `y`. It matches the picture, and it is
  what this note writes.
- **Applicative order**, used by Bird & de Moor and most category-theory texts: `h·f` is first `f`,
  then `h`.
- **Mirror rule**: `h·f ↦ f h`. Reverse every composite in the equation, not the equation term by term.
- Build a two-column table of source line against translated line before drawing anything, and check
  each row's source and target objects.
- Quote the source's original form once, verbatim, beside your translation, and flag which order it is
  in. After that one line, never mix the two again.
- **The mirror flips OPERATORS too, not only composites.** A source that reads relations right-to-left
  defines its order-sensitive operators from that end, so `est`, `/`, `\` and anything else built on a
  direction come out with an extra converse. Concrete instances agree (`≤` and its converse are both
  "the order"), so nothing looks wrong until an abstract chain fails to close at one endpoint. When a
  mirrored proof lands on `R°` where you wanted `R`, that is the symptom — look for the operator, not
  for an arithmetic slip.
- A chain that does not close after mirroring may need **one extra step**, not a repair. Say which
  hypothesis licenses it: an equivalence that only holds for a map is a real step.

## Squeeze the spaces out of labels

Inside a picture — box, wire and type labels, and the formula captioning a row — do NOT space around
`×`, around juxtaposition (composition), or around `⊑`/`=`. Write `(𝟙×list(R×R))S ⊑ S(R×R)`, not
`(𝟙 × list(R × R)) S ⊑ S (R × R)`. Diagram space is expensive and prose spacing rules do not apply in
one; a label that fits without wrapping is worth more than the airiness (user, 2026-08-23).

Single letters close up too: `SR`, not `S R`. The variables in this note are one letter each, so a run
of capitals cannot be a single name and nothing is lost. What still needs separation is a spelled-out
name — `cost sum`, `list concat` — where closing up would invent a word. `∪` keeps a space each side.
Prose outside the picture is unaffected.

## Drawing mechanics (cetz / typst)

- **ONE CANVAS PER EQUATION, with the `=` inside it.** Two canvases side by side in a grid each centre
  on their OWN bounding box; when the two panels put their boxes at different heights, the wires start
  and end at different heights and the `=` lines up with neither.
- **A chamfer is a MARK, not a proportion.** Cutting the corner by a fraction of the box's height works
  until a box is tall enough to carry two ports — then the cut runs past the upper port and its wire
  leaves from open air. Cap it (`min(k*h, k*BH)`) so every box wears the same size cut. The symptom is a
  wire that appears to start beside the box instead of on it, and the tempting "fix" — collapsing the two
  ports onto one wire — destroys the picture's content.
- **Forking a pair costs a crossing, and the crossing is real.** `⟨R,S⟩` on a two-wire input copies BOTH
  strands, so four strands run to two boxes and the middle two cross. Do not route around it: that
  shuffle is what the fork does. (Contrast the created strand of a `⟜`, which has no left end and so
  slides next to whatever it merges with — there the crossing is NOT forced and drawing one is a bug.)
- **Region fills go down FIRST, wires and boxes on top.** A closed path carrying both a fill and a stroke
  draws a floor under every region; fill with no stroke, then stroke the wires as their own paths.
- **Build a region boundary out of the same curve objects as the wire it follows** — the same bezier, the
  same control points, factored into one place. A boundary hand-fitted to a wire drifts the moment the
  geometry constants change, and then the colours say something the wires do not.
- **Colour the dot and its label together.** A generator whose name is a different colour from its mark
  reads as two different things.
- **Put the relation symbol at the START of each row** of a proof table, so `⊑` and `=` form a column
  down the left edge. Buried between formulas, the reader cannot tell whether a step loses information —
  and in a `⊑`-chain that is the whole content. Give `⊑` the accent colour and let `=` recede to grey.
- **Export FINISHED PICTURE FUNCTIONS, never primitives.** A host document very likely already binds
  `lab`, `dot`, `cap`, `cup`, `delta`, `nabla` — several of those are also Typst math symbols — and an
  imported primitive shadows one silently, with no error and a wrong picture. Export `homeq(w1, w2, …)`,
  not `wire`.
- Give those functions colour parameters defaulting to `black`, so the standalone preview stays neutral
  and the host document passes its own palette in.
- Parameterise a picture that appears in two documents rather than drawing it twice: one geometry kept
  in two files is one geometry that drifts.
- Keep one set of height constants across a family of pictures, so pictures stacked in one figure line up.
- A block whose content is centred needs `width: 100%`; otherwise it shrinks to its content and the
  `align(center)` inside has nothing left to centre in.
- Wrap a sentence and the figure it announces in one unbreakable block, or a page break will leave
  "drawn:" pointing at nothing.
- Headings orphan at the foot of a page. Fix with a weak page break immediately before the heading, and
  comment what would otherwise be orphaned.

## What the pictures buy

Associativity and bracketing become invisible: `(xy)z` and `x(yz)` are literally the same picture, so an
equation whose only content is re-bracketing is one picture drawn twice, and a proof step that only
re-brackets disappears. Units go the same way — an identity is a bare wire, so a law like `⦇α⦈ = 𝟙` reads
as "this box may be deleted", and the right-hand panel is drawn with nothing on it.

## Standalone preview file

Give every picture file its own compile line in its header comment, and keep it working:

```
typst compile --root . --format png --ppi 220 path/to/pic.typ path/to/pic.png
```

Set `page(width: auto, height: auto, margin: 0.8cm, fill: white)` in that file. A `#set page` or `#set
text` at the top level of an imported file does NOT reach the importer, so one file can be both the
standalone PNG and the library the note imports from — no lib/preview split is needed.

Read the produced PNG before believing it. Missing glyphs (`⦇`, `⦈`, `𝟙`, `∋`) render as tofu under a
font that lacks them, and only looking finds that.

## Prefer derived pictures to hand-drawn ones

A picture generated mechanically from a formal statement cannot drift from that statement. A hand-drawn
one can and does; the recurring failures are a picture of the neighbouring law, a dropped `=`, and an
equation drawn with its two sides swapped. Where a machine-checked statement exists, generate the picture
from it and keep the generator; hand-draw only what has no statement to generate from, and put a comment
above every hand-drawn picture saying WHY it is drawn that way — which geometry, which colours, what
would go wrong otherwise.

## A drawing fix lands with a check that fails on the old render

Every fix to how a picture is drawn — a port split, a chamfer capped, a colour shared across a row —
ships in the same change with a `circuit --compare` / gate check that goes red on the picture as it was
before the fix, and stays green after. He asked for it twice on 2026-09-04 ("add test for these 2, make
sure the test can catch current bottom", "add test to catch this, and fix"): the generator is regenerated
from a statement, so a fix without a check is undone by the next regeneration and nobody sees it go.
