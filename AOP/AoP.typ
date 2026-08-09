// Bird & de Moor, "Algebra of Programming", chapters 5-10 on one sheet: the relational half of
// the book, mirrored item by item into Freyd's conventions.  Chapters 1-4 are not here — 1-3 are
// the functional warm-up and 4 is the allegory theory the Freyd note already covers.
//
// One PDF, A4 in two columns.  Each chapter is a level-1 heading (it starts a column) and each
// book section a level-2 heading (it flows where it falls); the bodies live one directory down,
// one per chapter, each opening with an audit of every numbered item it keeps or drops.
#import "/AOP/bdm.typ": *

// The legend rides in the subtitle, which is set full width ABOVE the columns.  Put in the body
// instead, it would sit at the top of column 1 and the first chapter heading's column break
// would then throw away the rest of that column.
#show: sheet.with(
  title: "Algebra of Programming",
  subtitle: [
    Bird & de Moor, chapters 5–10 — in Freyd diagram order
    #v(0.35em, weak: true)
    #text(size: 8.5pt, fill: dimc)[
      Composition is juxtaposition in diagram order: $R S$ is "first $R$, then $S$", so every
      composite here is the reverse of the book's. A row tagged *✓* has its mirrored statement
      machine-checked under `AOP/A*.lean`.]
  ],
  cols: 2,
)

#include "ch5/body.typ"
#include "ch6/body.typ"
#include "ch7/body.typ"
#include "ch8/body.typ"
#include "ch9/body.typ"
#include "ch10/body.typ"
