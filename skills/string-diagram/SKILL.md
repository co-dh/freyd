---
name: string-diagram
description: Drawing or reading the note's HINZE–MARSDEN pictures — a wire is a functor, a bead a natural transformation, a region a category — plus the generator scripts/diagram, the scan-line check, regions and colour, composition order, cetz mechanics.
---

# String diagrams (Hinze & Marsden)

## Decide the convention first, and say so in the document

The note draws in two languages that share nothing but a pen. This file is the HINZE–MARSDEN one, after
*Introducing String Diagrams* §1.4.2 (p. 17) and §1.5.2 (p. 21): a wire is a FUNCTOR, a bead a natural
transformation or an arrow, a region a CATEGORY, and the picture reads top to bottom.

The other is the monoidal circuit calculus (`skills/circuit-diagram`): a wire is an OBJECT, a box a
MORPHISM, parallel wires are `⊗`, and the picture reads left to right. **The decision rule:** a circuit
cannot draw a functor applied to a morphism without Melliès' functorial box, so anything whose content is
a functor's action on arrows — folds, monads, adjunctions, naturality — wants THIS convention. Anything
whose content is copying, discarding, forking and converse wants the circuit. A document may use both; at
the switch, say in one line that the convention has changed and why.

## The calculus

- A **wire is a FUNCTOR**. An object is a functor out of the terminal category, so objects are wires too.
- A **bead** — a small filled dot with its name beside it — is an **arrow or a natural transformation**.
- `F A` is therefore TWO parallel wires, `F` and `A`. **Sugar hides this and must be undone before
  drawing**: `[A]` is the `list` wire beside the `A` wire, never one wire labelled `[A]`. Undo it at the
  wire ENDS too, where the label is written; a single `[A]` end label is the usual place it survives.
- **`F f` costs no notation**: it is the bead `f` on the object wire with the `F` wire running straight
  past it, untouched. That pass IS the functor's action.
- Reads TOP TO BOTTOM, source above target; labels sit at the ENDS of the wires, keeping the middle clear.
- An arrow out of `F A` is a bead where two wires join into one — the shape a monad `μ : M∘M ⇒ M` has.
- **Name a (lax) natural transformation with a GREEK letter** — `φ`, `ψ`, `χ` — and index it by the
  object where the component matters: `φ_A`. A Latin capital in that slot reads as a plain relation.
- **A BEAD'S INDEX IS THE OBJECT WIRE UNDER IT, and the fold is no exception** (user, 2026-09-05,
  reversing the earlier "the banana must carry its carrier"). `α` bare over a `B` wire is `α_B`, and
  `⦇α⦈` with `A` under it is `⦇αᴀ⦈` — the carrier is the fold's target, which IS that wire, so writing
  it in the label as well spells one object twice and lets the two drift. Two folds that read alike on
  a display are told apart by their wires: §11.4.2a's `⦇α⦈` over `B` and over `C`. Enforced both ways —
  `scripts/diagram` strips an index written anyway (and raises if it disagrees with the wire), and
  `scripts/scanline --strict` refuses one a hand-laid panel keeps. The formula captioning the row and
  the commutative square beside it keep the subscript: neither has a wire to read it off.
- **One set of letters across the whole row.** The formula, the commutative square and the string
  diagram beside each other must use the SAME names; generalising the formula's letters without
  redrawing is how the square ends up saying `X` where the picture says `φ`.

## The two readings are INVERSES — check every panel against the one you picked

Marsden also draws `Rel` one level down: regions are **objects**, wires are **relations**, beads are
**`⊑`**. That is the exact inverse of Hinze–Marsden, where regions are categories, wires are functors
and beads are arrows. Both are legitimate and a document can contain both — but a panel drawn in the
wrong one is not slightly wrong, it is transposed: every object becomes a region, every arrow becomes a
wire, and it still looks like a plausible picture. Nothing catches it but reading the labels against
the convention. When a document has settled on one, say so at the file's head and check each new panel
by asking of one label: *is this thing a functor or an arrow?*

## The book's own geometry — read off IntroString's pictures, 2026-09-03

The prose gives the semantics, the PICTURES give the geometry, and the geometry is not derivable from
the prose. Six facts, measured off p. 36 and p. 79 (eq. 3.8a/3.8b):

Measure them from the SVG, never from a raster: `pdftocairo -svg -f <pdf page> -l <same> IntroString.pdf
out.svg` puts every wire in the file as exact path data, at no image cost. That is where the numbers
below come from.

- **A merge is a symmetric cup — but only between FUNCTOR wires.** `μ : M∘M ⇒ M` — both `M` wires dip in
  by the SAME amount (14.2pt of a 28.3pt separation) and meet on a short hold, mirror-symmetric about
  the midline; drawn with cubic `C` segments. Never one wire running straight through with the other
  bending into it from the side. This does NOT extend to an arrow of the base category: p. 73 says the
  authors tried "very symmetrical drawings" for those and **discarded** them.
- **A base-category arrow sits on the object edge, and that edge is a straight "minor" diagonal at
  exactly 2 across : 1 down** — p. 74's paths are `L 56.694 -28.346` (2cm by 1cm) and `L 12.650 -6.326`,
  straight `L` segments, no curve. **The functor wire it produces then leaves as an exact vertical**
  (`L 0 -33.73`, `L 0 -47.91`). p. 73 gives the reason in words: the vertical edge came first because it
  let several monadic arrows line up on one line, and the diagonal replaced it precisely so the
  outgoing `M` edge could be drawn vertical.
- **No edge may have zero gradient** (p. 73): nothing horizontal, ever. That is also what makes a
  side-entering edge extendable to one entering from the top.
- **The output leaves the node straight down from its MIDPOINT** — the bead sits centred on that hold,
  at the midpoint of the two incoming wires, and the surviving wire drops vertically from it.
- **Wires are smooth cubic Béziers whose horizontal travel is comparable to or larger than the vertical
  drop** — 1:1 in 3.8a, 2:1 in 3.8b. A long diagonal sweep, not a small kink beside the node.
- **The object wire is ONE line** — a straight segment (p. 36) or one smooth Bézier (p. 79). No flat
  hold, no kink, no stair.
- **The object wire is the one that TRAVELS; the functor wires stay straight.** In 3.8b the two `M`
  wires are strictly vertical and the `A` wire sweeps 56.7pt sideways, passing under each `M` wire's
  foot in turn and picking up its bead there. This is the exact inverse of a fixed object column with
  every arm bending into it.
- **No functor-to-functor transformation touches the object wire.** On p. 79 `μ` is drawn entirely
  between the `M` wires while `A` runs past untouched; only `a` and `η` — a map and a unit, arrows of
  the base category — sit on `A`. Cf. p. 36: an object IS the constant functor `𝟏 → 𝒞` and an arrow IS
  a natural transformation between two of them, so a dot on the object wire *says* "an arrow here".

## Count the wires from the TYPE, and keep counting through nesting

`F A` is two wires; `F(E A)` is **three** — `F`, `E`, `A`. A port labelled `EA` is a bug: it hides a
functor that the picture's whole content may depend on. Read every port off the type and split it all
the way down before drawing anything.

Splitting pays immediately, because it tells you what the beads ARE:

- **A unit is where a wire is BORN** — `η : X ⟶ E X`, a bead with nothing above it, the new `E`
  starting there. In `Rel` the singleton `𝟙%∋` is this.
- **A counit is where a wire DIES** — `ε : E X ⟶ X`, the `E` strand ending on the object wire. In
  `Rel` the membership `∋` is this.
- Draw either as a bead sitting on an unsplit `EX` wire and the picture says nothing; the adjunction
  is exactly the birth and the death.
- One panel can carry **two wires of the same functor** — one arriving from the source and killed by a
  counit, another born by a unit and killed later. That is not a mistake to tidy away; it is the content.

**A wire may never be labelled with an arrow's name.** `∋ : EA ⟶ A` has a source and a target, so it
is a bead; the wire beside it is `E`. Symptom to grep for: a wire label that would type-check as a
morphism.

### A handle is born and dies inside the picture; a port is not

A "handle" — a strand that leaves the object wire, runs alongside, and returns — is only real when the
functor is **created and destroyed within the panel**, with the same object either side of the pair.
If the functor is already in the source type, there is nothing to open: it is a port, drawn as a wire
running in from the top edge. Drawing a handle there is the commonest way to get an extra loop that
means nothing — and it will survive review, because it looks like the neighbouring picture that
legitimately has one.

### Split an opaque bead when a law factors it

A bead whose name contains a functor applied to something is usually hiding a wire. Look for the law
that factors it and draw the factored form: `S%∋ = (𝟙%∋)E(S)` turns one flat bead into a unit, a
pass, and a death, and only then does `E` appear as a line. General rule: **if the picture has fewer
wires than the formula has functors, a bead is doing work the geometry should be doing.**

**Do this BEFORE drawing, not as a later cleanup, and do it in every panel of the table — a `S%∋` bead
left whole in one row while its neighbour shows `𝟙%∋` and `E(S)` makes the two rows look like different
arrows.** The check is mechanical: grep your finished panels for a bead whose label still contains `%∋`
or a functor application, and factor it.

`%` is **symmetric division** (the note draws it as a fraction bar), NOT the left division `/`. They
are different operators — `S%∋` is `Λ(S)`, the power transpose — so writing `S/∋` for it makes the
factorisation false. Same for `𝟙%∋`, the singleton.

## Some steps have no picture. Leave the cell empty.

A step whose content is a **conjunction** ("`X ⊑ A` and `X ⊑ B`") has no shape here — this calculus
draws 2-cells, not "and". Lattice operations are the same story: `∪` and `∩` are operations on
hom-sets, not wirings, so they can only be drawn as a sign between two panels. (The circuit calculus
*can* draw `∪`, as a tape — so the same operator gets different answers in the two columns of one
table, which is fine as long as each column says which calculus it is.) An empty cell is the honest
answer; a picture that means nothing is not.

**When a law's algebra is a union of branches, draw the COMPLICATED branch.** `[nil,(π₁p→cons,⊸ nil)]`
and `⊸ zero ∪ plus` say everything interesting in one branch; the other is a constant or an identity and
its panel is a wire with one bead on it. Drawing both doubles the width to show a picture the reader can
reconstruct from the formula, and the trivial branch is what a reader skips anyway. Draw the branch that
carries the algebra's work, and let the caption name the branch it is (`the cons branch of F(R)S⊑SR`).

## A transformation not known to be natural is a SPIDER, not a bead

IntroString.pdf §2.2.4, p. 40: the component `α X : F X ⟶ G X` is a node where the `F` and `X` wires bend
in and `G`, `X` bend out — a join and a split, arms drawn as bends with no horizontal tangent. Naturality
(1.15) is then exactly the freedom to slide an arrow `h` up and down past that node, and the bead on the
functor wire (§1.5.2) is the shorthand you may use only once that freedom holds.

In `Rel` it usually does not. The free theorem (Reynolds; Wadler) makes a polymorphic FUNCTION natural; a
relation of the same shape is only lax, because a relator `F(R)` demands every element have an `R`-image.
`prefix` at the coreflexive `p={(a,a)}` on `A={a,b}`, `xs=[b]`: `list(p) prefix` is empty while
`prefix list(p)` holds `([b],[])`. Draw the spider, and never let `F(f)`'s bead share its height.

**Arms come from the SOURCE, not from naturality.** A bead's arms are the functors of its source, its legs
those of its target (Ex 2.13, p. 59: `Id ⇒ F∘F` has "no arms, two legs"). A monad unit `η : Id ⇒ M`
therefore touches nothing: a lollipop, floating in the region, the `M` wire born at it, the object wire
running past unbroken — p. 64, and p. 74 draws exactly that beside an `A` wire, saying to reason with `η`
rather than `η A`. `Id` is "the corresponding region, without any associated edge" (p. 35). Putting a unit
on the object wire claims `A` is in its source. The (2.5) node is for a bead whose source really does
contain the object: a component `α X`, or an arrow like `guard p`.

**A composite object like `[A]` is ALWAYS two wires, `list` beside `A`, for the whole height of the
panel** — the default in `scripts/diagram` (`DEFSPLIT = "list"`), not a local widening. `prefix`,
`subseq`, an ordering `R : [A]⟶[A]` — every arrow ON the object — is a plain bead straddling both wires,
same as any other bead on a split object.

The generator's `split:` field on a panel's `cert:` overrides the default per panel, and `--fold-list`
on the command line turns the split off; a panel that declares `split: ""` keeps the composite folded
as one wire. The folded form is the declared exception, not the norm — §13.4.3c (`party-hm`) is the one
panel in the note that takes it, because `R : [A]⟶[A]` there is an ordering on parties and splitting
would need more than twice the available column width.

Two constraints on how the spider is drawn, both from the book, both easy to violate:

- **No horizontal tangent** (p. 40): "edges can be arbitrary curves with the important restriction that
  they must not have a horizontal tangent (zero gradient)". A bar with a dot at each end — the obvious
  way to join two wires — is zero gradient along its whole length. Every arm must leave at a slope.
- **The object wire stays STRAIGHT; only functor wires bend** (2.5, p. 46, `join` beside `filter p`).
  The node sits ON the straight object wire, the functor wire makes one excursion into it and bends back
  out. That also keeps the gray `𝟏` region a plain rectangle, since its left edge IS that wire.

## Regions are categories (Hinze & Marsden, Remark 2.1, p. 36)

- The two-dimensional AREAS between wires are **categories**. A wire separates the two categories its
  functor runs between, so region labels turn the picture into a type-check: cross the wires from the
  source side and the region names must chain up. Both sides of an equation must end with the same stack of
  regions and wires, or the two sides do not even have the same source and target.
- **Gray is reserved for the terminal category `𝟏`** — "We reserve this color for the category 1, so that
  it can be easily identified" (Remark 2.1, p. 36). Never spend gray on any other category.
- Why that matters: an object `X : 𝒞` IS a functor `X : 𝟏 → 𝒞`, and an arrow `f : X → Y` IS a natural
  transformation between two such functors — naturality is vacuous, since `𝟏` has one object and one arrow.
  So an ordinary morphism is legitimately a bead, and, in the book's words, "objects and arrows only appear
  on the left boundary of a gray region": the `𝟏` strip runs along the far side of the object wire.
- Shade one category with one colour, and keep that colour across every diagram in the document. Two
  regions of the SAME category get the same fill even when a wire runs between them.
- The gray strip's boundary IS the object wire, bends and all — where wires merge, the region changes
  shape. Follow the wire; a region edge that only approximately tracks its wire is a picture that lies.
- Label the regions ONCE, in the first picture that needs them, and omit the labels afterwards — that is
  the book's own practice, and unlabelled regions still carry their colour.
- A region needs a bounding **box** to be a region at all: draw the frame, and put the wire-end labels
  inside it.

## A bifunctor is not a wire

- Hinze & Marsden never draw one. **Every wire in the book is a UNARY functor**; a bifunctor is partially
  applied first — `M×−`, `−×P`, `(−)^P`, "the product bifunctor partially applied to the carrier"
  (Example 3.7).
- The two-argument content goes into a **commutative square** instead: Exercise 1.23 (IntroString.pdf,
  pp. 29–30) draws the exchange condition (1.24) with edges `f⊗B″` and `A′⊗g`, and the diagonal `f⊗g` is
  the arrow part, "given by either side of the equation".
- **PACK THE ARGUMENTS, don't partially apply and don't leave the wire unindexed** (user's decision
  2026-09-05, replacing the 2026-08-26 unindexed-`F` exception). Where the two arguments are *related* —
  `F(A,TA)`, `F(A,LA)` — a functor into the product category supplies both at once:

      ⟨𝟙,T⟩ : 𝒜 ⟶ 𝒜×𝒜     F : 𝒜×𝒜 ⟶ 𝒜     F(⟨𝟙,T⟩(A)) = F(A,TA)

  Now every wire is unary again, the region between `F` and `⟨𝟙,T⟩` is `𝒜×𝒜`, and — the whole point —
  **`F(f,T(f))` costs no notation**: it is the bead `f` on the object wire with `⟨𝟙,T⟩` and `F` running
  past, `⟨𝟙,T⟩` being what turns `f` into the pair. A law like `α_A T(f) = F(f,T(f)) α_B` is then plain
  naturality of `α : F∘⟨𝟙,T⟩ ⇒ T`, i.e. sliding the `f` bead past the `α` bead.
  - Partial application (`F(A,−)`) is the WRONG move here: it pins `A` in the lane's name, so `f : A⟶B`
    forces a second bead `F(f,𝟙) : F(A,−)⇒F(B,−)` beside the object bead, and those two beads are only
    the two components of the one arrow `F(f,T(f))` (Lean: `Freyd.prod_map_split`, `Freyd/S1_38.lean`).
  - `scripts/scanline`'s parser takes a bracketed fork as an application head, so `F(⟨𝟙,T⟩(A))` and
    `F(⟨𝟙,T⟩(f))α` go straight into `--src`/`--tgt`/`--sigs`. Give the new lane an `FCOL` entry.
  - `P` is the powerset relator in this repo — never reuse it for the packing functor.

## Which tool draws which

| convention    | generator         | emits                    | signatures                |
|---------------|-------------------|--------------------------|---------------------------|
| Hinze–Marsden | `scripts/diagram` | one `#dpanel(...)` call  | `diag/hm-sigs.json`       |
| circuit       | `scripts/circuit` | one `#cpanel(...)` call  | `diag/circuit-sigs.json`  |

`scripts/diagram` reads the formula in the note's own notation and needs `--src`/`--tgt`, because a formula
alone does not fix the ports. It emits a `cert:` recording the input, so a pasted picture certifies itself,
and it has `--compare` (rebuild every `#dpanel` literal in the note from its own `cert:` and fail on drift)
and `--write` (splice the rebuild over it). `scripts/scanline` reads a panel back and prints the composite
it denotes — the check, not a third convention.

Run `-h` on either for its flags, its modes and one runnable line per mode. That help is the flag list; it
is not copied here, and it is where to look before reading the source.

## Where the code lives

| file                   | holds                                                                       |
|------------------------|-----------------------------------------------------------------------------|
| `diag/hm.typ`          | the primitives: `hm-wire`, `hm-bead`, `hm-region`, `hm-port`, `hm-panel`     |
| `diag/dpanel.typ`      | `dpanel`/`dpan`, the note's panel, and `hm-meta`, which emits the sweep list |
| `diag/draw.typ`        | the note's finished pictures and its palettes — `FCOL`, `OCOL`, `BCOL`       |
| `diag/cetz-nodraw.typ` | cetz with the `nodraw` switch, and `d`/`lw` — the pen BOTH conventions use   |
| `scripts/diagram`      | the generator                                                               |
| `scripts/scanline`     | the sweep                                                                   |
| `scripts/relexpr.py`   | the note's relation notation — `parse`, `spell`, `norm` — read by both        |
| `diag/hm-sigs.json`    | one signature per bead label, checked across every panel of a display        |

`hm.typ` and `dpanel.typ` import nothing from the circuit files, and those import nothing from these. The
one shared place is `cetz-nodraw.typ` (the pen) and `relexpr.py` (the notation): a helper wanted by both
goes there, never copied into both.

## Check a whole panel by SCAN LINE — mechanical, and it needs no rendering

Sweep a horizontal line down the panel. No edge has a horizontal tangent (p. 40: "edges can be arbitrary
curves with the important restriction that they must not have a horizontal tangent (zero gradient)"), so
every cut meets each live wire in exactly ONE point and therefore reads as an ordered list of wires — a
1-cell. Read that list in the panel's horizontal order (applicative across, `𝟏` at the right edge); it
must spell the object the composite is at, at that step. The book's own version of this check is §4.7.3,
"Scan Lines, Snakes, and Hockey Sticks" (p. 119; the colour-flipper it builds on is p. 116).

- Between two consecutive beads the cut may not change: same wires, same order.
- At a bead, the cut just above it is exactly the bead's SOURCE and the cut just below exactly its
  TARGET. Every wire the source names must touch the bead, and no wire outside the source may touch it.
- The topmost cut is the whole composite's source, the bottom cut its target. If either disagrees with
  the statement above the picture, the picture is of a DIFFERENT ARROW — commonly one summand of it.
- Where a cut is not a well-formed 1-cell, or a bead's source is not what the cut says, write down the
  failing cut's wire list. That list is the diagnosis; nothing further is needed.

Run the sweep on the drawing code, not on a rendering: the wire list at a height is the panel's port list
minus the wires consumed above it, which is `x` constants and bead heights and nothing else.

### `make scan` runs that sweep for you, over the whole note

`make scan` (`scripts/scanline`) pulls every panel's lanes, beads and ports from `typst query
diag/allegory-axioms.typ metadata --field value` (`kind == "scanline"`) and sweeps all of them. Read the
counts off the run itself — a number written down here is a snapshot and rots; what must hold is
`0 unhandled, 0 failures`, and the certified count only rises as hand-laid panels are replaced by
generated ones. `dpanel` and `tpan` emit their own lists as `#metadata`, and `tw-hm` emits by hand from
the same bindings it draws with — the emitted list IS the list that draws, so it cannot drift from the
picture (`dpan` alone stays unchecked: it only ever sees an opaque drawing closure). A `cert:` dict
(`expect`, `src`, `tgt`, `branch`, `alias`) certifies a panel; `branch:` names the case-split arm drawn,
and a fired `alias:` prints `AGREE modulo <alias>` rather than hiding the residual. It caught a unit bead
moved onto the object wire and a top cut answering the wrong statement — and one error only IT catches: a
bead moved from the object wire onto a functor wire spells the same either way when nothing sits to its
left, so expression comparison alone is blind to it; only the cross-panel signature check sees it.
`tpanR` emits nothing and stays outside the sweep. Run it after any panel edit, and before arguing from a
rendering — cheaper than looking, and it checks what looking cannot.

The sweep is this convention's only: it reads the `kind == "scanline"` metadata that `dpanel`/`tpan`
emit, and a circuit panel emits `kind == "circuit"` instead and is checked by its own generator's
`--compare`.

## Crossings are zero and gated — one knee per bead and side

`scanline` reports crossings two ways — cut order (a wire born or killed off its own column has passed
every live lane between: says a crossing is *wrong*) and ink (bezier intersections: says one is *there*)
— and `make p` runs `scan-strict`, so either kind is a build failure. The note is at 0/0, every panel.

The cause of the old 201 was never the lane order: a lane's x is its instance index in `made`
(`scripts/diagram`), and `made` is already a linear extension of every cut, so no permutation removed
a single hit. It was UNEQUAL KNEES — the knee grew with the horizontal run, so strands converging on one
bead braided, the longer one turning early and overtaking the shorter one still falling vertically.
The cure (2026-09-02): for each bead height and side, every strand — arms, legs, dips — shares one knee
`K = min(0.45 + 0.25·maxrun, 0.5·gap)`, `gap` being the distance to the neighbouring bending event or
bead height, unit rows excluded. Equal drops into one point with the same bezier family keep nested arcs
nested; the half-gap cap keeps one bead's band from overlapping the next. **The 0.5 is load-bearing, not
a tuning knob:** 0.5 → 0 ink, 0.7 → 188, 0.85 → 244.

Given up: a per-strand knee whose aspect grows with the run. (The arrival *tangent* is vertical for any
knee, before and after — the old comment claiming "one angle" was wrong about that.)

The rule is implemented twice, Typst `dknees` in `diag/dpanel.typ` and Python `dknees` in
`scripts/scanline`, so a green sweep would not by itself prove the ink. That gap is closed: `dpanel`
emits the computed knees as `knees:` in `hm-meta` and `a_dpanel` compares them (`Panel.kdrift`). Change
one side and the other must move with it.

Two earlier cures were built and compared beside the original (bead sits on its own lane; algebra beads
drawn as a bar, which cannot intersect a wire) — **rejected on appearance ("both are worse than current",
2026-08-30).**

**Superseded 2026-09-03 — "Book is better."** The 2026-08-30 attempt moved the bead off the object
column but changed nothing else, so it kept asymmetric arms and still swept out and back to reach the
next bead. The book's geometry above is one package, and half of it looks worse than none: a merge is a
symmetric cup at the MIDPOINT of the wires it joins with the survivor dropping vertically from it, a
1→1 bead sits on its wire with no bend at all, and the object wire is one line that no polymorphic bead
touches. Rebuild in that shape, not in the 2026-08-30 shape.

## Read by scan line before arguing about a bead's position

A horizontal cut reads off the object at that height, and the composite is the beads you pass through
going down. So when a bead consumes a wire, **it reads the same whether the consumed strand bends in to
meet the survivor or simply ends beside it**: above the bead the cut crosses both wires, below it
crosses only the survivor, either way. Nothing is lost by a free end — the surviving wire was already
there.

**The scan line reading is identical; the picture's meaning is not.** A bead ON the object wire says
*an arrow of the base category, at this one object*; a bead among the functor wires with the object
wire running past says *a natural transformation — this works at any type*. That second fact is real
content the scan line simply does not carry, so "should this bead touch the object line?" is settled by
the bead's TYPE, not by taste (2026-09-03, reversing the earlier "presentational, never correctness"
ruling here): polymorphic in the object ⟹ off the object wire; fixed at one object ⟹ on it.

The test is NOT "does the row change the object wire's label", and NOT "is the bead's own signature
written with a free `x`" — both were tried and both are wrong (2026-09-03). It is: **does the bead
carry a parameter that names an object?** `est(R) : E(x)⟶x` reads polymorphic, but its `R` is one
relation at one object — every panel declares it concretely
(`"R": "list⁺(list⁺(Word))⟶list⁺(list⁺(Word))"`) — so `est(R)` is an arrow AT that object and its dot
stays on the object wire. Naturality would need `E(f) est(R_B) = est(R_A) f` for every `f`, and that
fails: taking the least under `R_A` and then mapping is not mapping and then taking the least under
`R_B`, because `f` need not be monotone. The natural member of that family is `∋ : E(x)⟶x` alone;
`est(R) ≜ ∋ ∩ (∈ \ R°)` is what `R` breaks. Same for `thin(Q)`, `fits(w)`, `⦇generate⦈`, `⦇Q⦈`. The
parameterless beads — `union`, `setify`, `∋`, `∈`, `concat`, `cons`, `π₂` — are the natural ones and
leave the object wire alone.

**Drawing INSIDE a `⦇ ⦈`: what goes in the box is the ALGEBRA, not the fold.** IntroString (5.8), p. 147 gives two
styles for `⦇a⦈` — a double circle annotated with the target algebra `a`, and, "if the algebra has structure", a
rounded box holding the algebra's own diagram, "so it avoids the need to mix symbols and diagrams". Both carry `a`,
never an unfolding of the recursion: the fold IS determined by its algebra. So the style pays exactly when the
algebra is a composite of beads on lanes (`⦇F(𝟙,f)g⦈`, `⦇S%∋ est(R;H)⦈`) and buys nothing when it is not. A
division is not: `%` is drawn only in the one shape `𝟙%∋`, the unit `Id⇒E`, which `isunit` heads a lane with — a
general `frac(X,∋)` has no bead, so §11.6.2a's algebra `frac(F(∋)R,∋)` would put the same `frac` symbols inside a
box that the bead label already carries.

**But a free end is only legible if something receives it.** Drawing a unit or counit free, to mark it
as structural against neighbouring beads that are data, needs the adjunction's other wire to land on —
`i` beside `E`. Without it, one and the same wire with a free end at the top and a bound end at the
bottom reads as a drafting slip, not as a rule, and the reader has to be told the convention instead of
seeing it. So the two decisions are coupled: free ends and the full pair of wires come together, or
neither does. The pair is not cheap — a panel that births AND kills it carries twice the wires and will
be the densest cell on the page. Decide both at once.

## Composition order — where translations get silently reversed

- **Diagram order, by juxtaposition**: `xy` is first `x`, then `y`. It matches the picture.
- **Applicative order**, used by Bird & de Moor and most category-theory texts: `h·f` is first `f`, then `h`.
- **Mirror rule**: `h·f ↦ f h`. Reverse every composite in the equation, not the equation term by term.
- Build a two-column table of source line against translated line before drawing anything, and check each
  row's source and target objects. `h·⦇f⦈ = ⦇g⦈ ⟸ h·f = g·F h` becomes `⦇R⦈ S = ⦇Q⦈ ⟸ R S = (F S) Q`.
- Quote the source's original form once, verbatim, beside your translation, and flag which order it is in.
  After that one line, never mix the two again.
- **The mirror flips OPERATORS too, not only composites.** A source that reads relations right-to-left
  defines its order-sensitive operators from that end, so `est`, `/`, `\` and anything else built on a
  direction come out with an extra converse. Concrete instances agree (`≤` and its converse are both
  "the order"), so nothing looks wrong until an abstract chain fails to close at one endpoint. When a
  mirrored proof lands on `R°` where you wanted `R`, that is the symptom — look for the operator, not
  for an arithmetic slip.
- A chain that does not close after mirroring may need **one extra step**, not a repair. Say which
  hypothesis licenses it: an equivalence that only holds for a map is a real step, and finding that it
  is used exactly once tells you what the theorem actually rests on.

### A picture has TWO axes and they need not agree (3.1a, p. 64)

- **DOWNWARDS** composes the arrows being drawn (2-cells), source above target — so downwards is diagram
  order. A document's "everything in diagram order" rule governs this axis and is already satisfied here.
- **ACROSS** composes the FUNCTORS — a different composition, on the 1-cell context, and a separate
  decision. Applicative across means the LEFTMOST wire is the last functor applied: `F T` stands `F` left,
  `T` right.
- **Where the grey `𝟏` sits and which order across reads in are ONE choice, not two.** An object `X : 𝒞` is
  the functor `𝟏 ⟶ 𝒞`, so `𝟏` is the source of the whole composite: diagram order across (source left)
  forces `𝟏` to the left edge; applicative (source right) forces it to the right, which is the book's.

**Default: keep the horizontal axis applicative and `𝟏` at the right, even in an otherwise diagram-order
document.** Freyd repo, user's decision 2026-08-17. Costs of flipping:

- Small: mirror every panel and every hand-placed label offset.
- Large, and silent: diagram-order `M⋄η` has the component classical `ηM` has — the same glyph order as
  classical `Mη`, with the opposite meaning. Both sides of a monad unit law are true, so a wrong flip still
  type-checks, still reads as the unit law, and nothing ever catches it.
- The one place a flip *is* checkable: `State = R∘L` vs `L⋄R`, i.e. `(A × P)^P` against `(A^P) × P`.
- A note that cites its source book by page is read beside it. Spell composites the way the book spells them.

State the two-axis split at the FIRST picture that uses it, not once per section. And say once that `⊣` is
not a composition — `L ⊣ R` two lines above `R∘L` reads as two opposite orders in one paragraph, and `⊣`
only names the left adjoint first.

## Colour belongs to regions; functor wires are coloured by name

**Colour is two-dimensional and lives on the REGIONS; wires and beads are always black.** A region is a
category, shaded flat — IntroString.pdf pp. 79, 82 (3.8a/3.8b): the left region yellow `#FFF657` is `𝒞`,
the right grey `#CDCDCD` is `𝟏`, while the object wire `A`, the functor wires `M`, and the beads `η`, `μ`,
`a` are all black with black labels. A wire's TYPE is the pair (colour on its left, colour on its right) =
(target category, source category); an endofunctor wire therefore carries the SAME colour on both sides —
p. 64, verbatim: "The diagrams are monochromatic as M is an endofunctor."

Grey is reserved for `𝟏` (Remark 2.1, above) and turns into a real colour only when a genuinely different
category takes `𝟏`'s place — p. 82, verbatim: "The gray region that is reserved for the terminal category
has turned into a colorful one; the corresponding category is called the source of the action." Beyond
that, the one palette rule the book states: "Where possible, we will consistently shade a category with
the same color, even across multiple diagrams."

**Consequence for this note (2026-09-01): every region is one colour, the object wire stays black, and
FUNCTOR wires are coloured BY NAME** — one muted colour per functor, the same in every panel, distinct
from any region colour. The palette is `FCOL` in `diag/draw.typ` — read it there, do not restate the
hexes anywhere else. It names EVERY functor wire the note draws and has no `default:`, so an
unregistered label is a compile error that names it, never a silently black wire (that silent black,
not the hue spacing, was what "the functor line color are too close" turned out to mean, 2026-09-02).
`𝟏` is in it: the constant functor, the nullary summand of `F(X) = 𝟏 + Int×X`, in the grey the note
reserves for `𝟏`. A wire, its end label and its mid-run name share the colour. Why: with the
leftward sweep a functor wire leaves its bead and runs across other lanes, and the reader can no longer
tell which functor it is (user: "once they move out from a bead it's hard to tell what is it").

The OBJECT wire's colour is its OBJECT (`OCOL` in `diag/draw.typ`): a wire that changes object at a bead
changes hue there, so `A` visibly ends and `B` begins instead of one line wearing two names.

What was rejected on 2026-08-30 ("the color is wrong") was a different system: wires coloured by TYPE,
object colours on the object wire. Do not bring that back. Beads keep the note's own by-which-arrow
colours (`GIVEN1`, `GIVEN2`, `INDUCED`, `SLACK`); colour the dot and its label together, always.

Those bead colours are FIXED OBSTACLES when `FCOL` is designed, and a bead sits on the wire it changes,
so the pair a reader compares is bead-against-lane, not lane-against-lane. Separate in CIELAB ΔE76:
≥ 25 from every bead colour and from the object wire's `BCOL`, ≥ 30 from any lane that shares a panel.
Two lanes that never co-occur may reuse a band. A palette checked lane-against-lane only is not checked
(`GIVEN1 #26734d` vs `list #3f7d4e` measured 7.1 and they are on the page together in 13.4.3c).

**An index functor `[k] : X ↦ X[k]` is a lane of its own, and each AXIS of a matrix gets its own colour**
(user, 2026-09-05, on `diag/vecgen.typ`: "need different color of different dimensions of vector"). `A[n][p][m]`
is the wires `[n] [p] [m] A`, and `[n]`, `[p]`, `[m]` are three functors, so one `Vec` hue for all of them
is the silent-black mistake again: once `trans` has swapped two of them the reader cannot tell which is
which. The colour follows the axis, not the length: `[p]` and `[3p]` are one candidate axis that `concat`
lengthened, `[m]` and `[m+1]` one path axis, so the wire keeps its hue across the bead that changed its
length. `fcol(label)` in `diag/draw.typ` is the rule — the letters inside the first `[…]` of the label
name the axis, a constant index (`[3]`) is an axis of its own, and a lift that carries one index
(`𝟙×[p]`, `[n]×[n]`, `⟨𝟙,[m]⟩`) takes that index's hue — and the four axis lanes are `FCOL` entries, so a
new axis letter draws through `fcol`'s free-hue path without an edit. Pass the
wire's own label to `fcol`; never a local `VEC = …` constant.

**Write an index functor POSTFIX in an object and applied in a formula, and give the generator the note's
abbreviation as a `--defn`.** `A[n][p]` is `[n]([p](A))` — the leftmost bracket is the outermost functor,
so the brackets read left to right in the same order as the wires of the cut — and `Vec(n)(h)` is that
same `[n]` applied to an arrow, drawn inside the `[n]` lane the way `N(union)` is drawn inside `N`. A
lower-case letter inside a bracket of a SIGNATURE is an index variable, matched and substituted textually
(`[3k]` takes `[3p]`, `[k+1]` takes `[m+1]`), so one row types the bead at every index. Where the note
abbreviates an object, state it as `--defn "A[k+1]≜F(A[k])"` rather than writing the abbreviation at the
port: the ports must draw what the picture IS, two wires, and the edge then writes `[m+1]` once under a
thin bracket spanning them — a per-wire label there would make the reader re-derive the abbreviation the
note already stated.

**Every `FCOL` addition moves every UNNAMED lane.** `fcol` indexes the free-hue list by the name's hash,
and the list shrinks around each new entry, so a lane that was drawing on a free hue lands on a different
one — `Digit×−` went from clear of `E` to ΔE76 12 from it when the four axis lanes were added. Name the
lane (`lanecheck`'s own message says which) rather than tuning the new entry around it.

## Isotopy: a bead's height relative to OTHER wires is free

IntroString.pdf p. 21, eq. (1.16): pictures differing only in the relative vertical position of beads on
distinct wires are IDENTIFIED — the SAME diagram, not two diagrams to compare. This is about IDENTITY.

The next rule is presentation, not a second, conflicting rule: it says where to PLACE a shared bead so a
proof reads as one motion. Identity says two placements denote the same diagram; presentation picks one.

## Align a shared bead across the `=`

**A bead that is the same arrow on both sides of an equation must sit at the same height on both sides.**
Then the picture says which bead actually moved, and the equation reads as one motion instead of a reshuffle.

Give each arrow its own row and leave the row EMPTY on the side that does not have it. In the F-algebra
homomorphism law `α h = (F h) R` the shared bead is `h`: put `h` on the middle row of both panels, `α` on
the row above it in the left panel, and `R` on the row below it in the right panel. The reader then sees the
algebra bead travel downwards past a stationary `h` — which is what the law says. Put `h` high on one side
and low on the other and the same picture says nothing at all.

Corollary for layout: keep one set of row heights for a whole family of pictures, and let panels skip rows
rather than compress to fit.

## Draw an unchanged wire identically on both sides

A wire with the same type and the same endpoints on both sides of the `=` did not change, so it must not
LOOK changed. Give it the same shape in both panels — a straight line where the geometry allows — and let
the other wire do all the bending into it. Sameness of shape is what says "this one did not move"; two
different curves for one unchanged wire make the reader check whether something happened to it.

At a junction this fixes which strand bends: the wire that survives the junction runs straight through, and
the wire that is consumed bends in and terminates on it. That is also the book's own shape for an algebra —
the carrier runs on and the functor wire ends on it — rather than a symmetric Y where both strands bend.

A payoff worth checking for: if the surviving wire is the boundary of a coloured region, drawing it straight
makes that region the same rectangle in both panels, and the two panels then match by inspection.

## Set the commutative diagram beside its string diagram, the formula below, one frame around the row

Do not stack law, commutative diagram and string diagram down the page. Put the two pictures SIDE BY SIDE
in one row, set the formula BELOW them as the row's caption, and frame the whole row with a light hairline
— match the document's existing rule weight (a printed note's, e.g. `0.4pt + luma(190)` with a small
radius, never a heavy slide border). The two answer different questions — the commutative diagram says
which arrows exist and between which objects, the string diagram says what the equation does to them — and
a reader checking one against the other should not have to scroll between them; the frame binds pictures
and caption into one unit the page cannot split.

One shared caption also stops the pair from drifting: there is a single statement under them, so a change
to the law cannot update one picture and leave the other behind. Make the caption a required argument of
the row helper, so no row can be built without it and no law can drift back to a floating formula.

The pairing only works if the two pictures agree ARROW BY ARROW on colour: the same arrow must be the same
hue in the square and in the diagram, or the reader has nothing to cross the gap with. Where the two
pictures cannot both fit the text width, scale them together and keep them in the row; if the row is
genuinely too wide, say so and pick which picture to abbreviate, rather than shrinking both to illegibility.

## What the pictures buy

Associativity and bracketing become invisible: `(xy)z` and `x(yz)` are literally the same picture, so an
equation whose only content is re-bracketing is one picture drawn twice, and a proof step that only
re-brackets disappears. Units go the same way — an identity is a bare wire, so a law like `⦇α⦈ = 𝟙` reads
as "this bead may be deleted", and the right-hand panel is drawn with nothing on it.

## Squeeze the spaces out of labels

Inside a picture — node, wire and bead labels, and the formula captioning a row — do NOT space around
`×`, around juxtaposition (composition), or around `⊑`/`=`. Write `(𝟙×list(R×R))S ⊑ S(R×R)`, not
`(𝟙 × list(R × R)) S ⊑ S (R × R)`. Diagram space is expensive and prose spacing rules do not apply in
one; a label that fits without wrapping is worth more than the airiness (user, 2026-08-23).

Single letters close up too: `SR`, not `S R`. The variables in this note are one letter each, so a
run of capitals cannot be a single name and nothing is lost (user, 2026-08-23). What still needs
separation is a spelled-out name — `cost sum`, `list concat` — where closing up would invent a word.
`∪` keeps a space each side. Prose outside the picture is unaffected.

## Drawing mechanics (cetz / typst)

- **ONE CANVAS PER EQUATION, with the `=` inside it.** Two canvases side by side in a grid each centre on
  their OWN bounding box; when the two panels put their beads at different heights, the wires start and end
  at different heights and the `=` lines up with neither.
- **Offset bead labels to one side** (e.g. 0.32 units east, anchored `west`). A label centred on the dot
  falls inside the fork of a merge.
- **Two wires merging into one**: one bezier per strand into the junction, with both control points at the
  SAME fraction of the drop (≈0.4). Both strands then leave and arrive along the wire direction, and the
  junction has no kink.
- **Colour the dot and its label together.** An arrow whose name is a different colour from its mark reads
  as two different things.
- **Region fills go down FIRST, wires and beads on top.** A closed path carrying both a fill and a stroke
  draws a floor under every region; fill with no stroke, then stroke the wires as their own paths.
- **Build a region boundary out of the same curve objects as the wire it follows** — the same bezier, the
  same control points, factored into one place. A boundary hand-fitted to a wire drifts the moment the
  geometry constants change, and then the colours say something the wires do not.
- **Put the relation symbol at the START of each row** of a proof table, so `⊑` and `=` form a column down
  the left edge. Buried between formulas, the reader cannot tell whether a step loses information — and in
  a `⊑`-chain that is the whole content. Give `⊑` the accent colour and let `=` recede to grey.
- **Export FINISHED PICTURE FUNCTIONS, never primitives.** A host document very likely already binds `lab`,
  `dot`, `cap`, `cup`, `delta`, `nabla` — several of those are also Typst math symbols — and an imported
  primitive shadows one silently, with no error and a wrong picture. Export `homeq(w1, w2, …)`, not `wire`.
- Give those functions colour parameters defaulting to `black`, so the standalone preview stays neutral and
  the host document passes its own palette in.
- Parameterise a picture that appears in two documents rather than drawing it twice: one geometry kept in
  two files is one geometry that drifts.
- Keep one set of height constants across a family of pictures, so pictures stacked in one figure line up.
- A block whose content is centred needs `width: 100%`; otherwise it shrinks to its content and the
  `align(center)` inside has nothing left to centre in.
- Wrap a sentence and the figure it announces in one unbreakable block, or a page break will leave
  "drawn:" pointing at nothing.
- Headings orphan at the foot of a page. Fix with a weak page break immediately before the heading, and
  comment what would otherwise be orphaned.

## Standalone preview file

Give every picture file its own compile line in its header comment, and keep it working:

```
typst compile --root . --format png --ppi 220 path/to/pic.typ path/to/pic.png
```

Set `page(width: auto, height: auto, margin: 0.8cm, fill: white)` in that file. A `#set page` or `#set
text` at the top level of an imported file does NOT reach the importer, so one file can be both the
standalone PNG and the library the note imports from — no lib/preview split is needed.

Read the produced PNG before believing it. Missing glyphs (`⦇`, `⦈`, `𝟙`, `∋`) render as tofu under a font
that lacks them, and only looking finds that.

## Prefer derived pictures to hand-drawn ones

A picture generated mechanically from a formal statement cannot drift from that statement. A hand-drawn one
can and does; the recurring failures are a picture of the neighbouring law, a dropped `=`, and an equation
drawn with its two sides swapped. Where a machine-checked statement exists, generate the picture from it
and keep the generator; hand-draw only what has no statement to generate from, and put a comment above
every hand-drawn picture saying WHY it is drawn that way — which geometry, which colours, what would go
wrong otherwise.

## A drawing fix lands with a check that fails on the old render

Every fix to how a picture is drawn — a bead moved off the object wire, an `αᴛ` where `α` stood, a colour
shared across a row — ships in the same change with a `scanline`/gate check that goes red on the picture as
it was before the fix, and stays green after. He asked for it twice on 2026-09-04 ("add test for these 2,
make sure the test can catch current bottom", "add test to catch this, and fix"): the generator is regenerated
from a statement, so a fix without a check is undone by the next regeneration and nobody sees it go.
