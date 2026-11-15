// Architecture of the Rel language (leetq/LeetQ/Rel): the run path on the left, what proves each layer on the right.
#set page(paper: "a4", flipped: true, margin: 1.2cm)
#set text(font: "New Computer Modern", size: 10pt)

#let layer(title, body, fill: rgb("#eef3fb")) = block(
  width: 100%, inset: 7pt, radius: 4pt, fill: fill, stroke: 0.6pt + rgb("#5577aa"),
)[*#title* \ #body]
#let proof(title, body) = layer(title, body, fill: rgb("#f3f8ee"))
#let down = align(center, text(14pt)[↓])
#let side = align(horizon + center, text(14pt)[⟵])

#align(center, text(15pt)[*Rel language — architecture*])
#v(4pt)

#grid(
  columns: (1fr, 1.6em, 1fr), row-gutter: 3pt, column-gutter: 4pt,
  [*Run path*], [], [*What proves it*],

  layer[Program][A `.rel` text, or `rel_program n where …` in Lean (`Programs/*`: AC3, Sudoku, Chess, Knapsack, …).
    Only relation constructs; iteration only by `μ` and `R*`.],
  [], [],

  down, [], [],

  layer[`Lang/`: Parse → Elab → Eval][`Parse`: text → `Program` AST. `Elab`: names resolved, every term typed
    `A ⟶ B`, definitions expanded → core term `Tm`. `Eval.ev`: runs `Tm` by `Alg`'s ops, each shared sub-term once.
    `Bits`: small objects as bit matrices, one kernel per inner node.],
  side,
  proof[`Lang/Calc`, `Lang/BitsSpec*`][`rel(t)` reads a Rel term as a term of the AOP allegory, so a Lean `calc` can
    be written in Rel. `BitsSpec*`: the bit-matrix path equals the table path.],

  down, [], [],

  layer[`Alg.lean`: the operators][`≫`, `°`, `∩`, `∪`, `⊑`, divisions, `Λ`, `∋`, `⟨R,S⟩`, `[R,S]`, fold, loop,
    `est`, `thin`, `fixOn`, … Every op is one body: `opC : … → Rel × Bool`, and `op := (opC ..).1`.
    The Bool is the *ok-bit*: false when a size or a code would not fit.],
  side,
  proof[`Rep*.lean`, `CRel*.lean`][`rep : Rel → ` relation of the allegory (`AOP.A6_1_RelSet`). \
    `rep_opC`: `(opC ..).2 = true → rep (opC ..).1 = ` the allegory's `op`. \
    Primitives: from the old `rep_op` (bit ⇒ its premises). Composites: from `rep_foldByC`, `iterC_run`
    (total bit ⇒ every round's bit).],

  down, [], [],

  layer[`Core.lean`, `Code.lean`: the representation][`Rel k v = {n, key : Arr k n, val : Arr v n}`. `Vals` by
    object: atom = one column; product = two; `arr` = `lo`, `hi` + one flat payload; sum = tag + two sides.
    `Code`: values coded to integers (`codesC`, `sortByC`), joins and gathers on the codes.],
  side,
  proof[`KernelWF/*`][What each kernel use computes, row by row: `Codes*` (equal code ⇔ equal value), `Join*`,
    `Pick*`, `Raze*`, `Nub`, `Sort`, `Gather`, …],

  down, [], [],

  layer[qlean: `QLean/Kernel/*` + `c/*.c`][`Column`: compressed payloads (`bytes`, `bits`, `syms`, `foR`, `alp`),
    the in-memory form equal to the on-disk form. Each kernel is a Lean `def` with `@[extern "qlean_…"]`:
    the compiled program calls the C function; the Lean body is its model.],
  side,
  proof[qlean `Verify/*`][Proofs about the kernels' Lean bodies (encoding, grade, search, gather, …).],
)

#v(8pt)
#block(inset: 7pt, radius: 4pt, stroke: 0.8pt + rgb("#bb4444"), width: 100%)[
  *Trust boundary.* Every proof is about the Lean body of an `@[extern]` kernel. That the C function computes the
  same as that body is tested (`QLean/Kernel/*Test.lean`), not proved. Above the C line each op is proved:
  when its ok-bit is true, its answer is the relation the allegory defines. `Lang/Eval.ev` does not yet carry the
  bit, so a program run does not report it.
]
