// The same sheet as Cheatsheet-2col.typ in the desktop shape — A4, two columns — but with the
// entries the Rel-focused build drops put back: this is all of chapter 1 from §1.4 on.
#import "style.typ": *

#if not full { panic("Cheatsheet-full.typ needs the full content: compile with `typst compile --input full=1 Cheatsheet-full.typ` (or run `make`).") }

#show: sheet.with(
  title: "Categories, Allegories",
  subtitle: [Freyd & Scedrov, all of chapter 1 from §1.4 — definitions, diagrams, theorems],
  cols: 2,
)

#include "body.typ"
