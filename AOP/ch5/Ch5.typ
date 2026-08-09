// Bird & de Moor, "Algebra of Programming" ch. 5, in the phone shape: a screen-sized
// page, one column.  The content lives in body.typ; Ch5-2col.typ pours the same body
// into A4.
#import "/AOP/bdm.typ": *

#show: sheet.with(
  title: "Datatypes in Allegories",
  subtitle: [Bird & de Moor, #emph[Algebra of Programming] ch. 5 — in Freyd diagram order],
  cols: 1,
)

#include "body.typ"
