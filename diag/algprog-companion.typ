// note-split: root — written by scripts/note-split and stripped by scripts/note-join
#import "note-prelude.typ": *


#show: conf.with(title: "Companion to Bird & de Moor, Algebra of Programming")

// `supplement: none` so a `@sec-…` reference prints the BARE number: the prose writes its own
// `§`, and the default supplement would set "Section §1.1." in the middle of a sentence.
#set heading(supplement: none)

// `▿` at the four generator glyphs' size and for the same reason: at running-text size it reads as a
// subscript, not an operator.  Not in note-style.typ — the proofs note shares that file and has no copair.
#show regex("▿"): it => text(size: 1.45em, it)
#show ref: it => context { import "shared-laws.typ": elsewhere; let t = str(it.target); if t in refname { law-gate(it); link(it.target, refname.at(t)) } else if t in elsewhere and query(it.target).len() == 0 { elsewhere.at(t) } else { it } }

#NOTEROOT.update(true)
#include "aop/00-laws.typ"
#include "aop/01-programs.typ"
#include "aop/02-categories.typ"
#include "aop/03-applications.typ"
#include "aop/04-relations.typ"
#include "aop/05-datatypes.typ"
#include "aop/06-recursive.typ"
#include "aop/07-optimisation.typ"
#include "aop/08-thinning.typ"
#include "aop/09-dynamic.typ"
#include "aop/10-greedy.typ"
