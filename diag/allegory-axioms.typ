// note-split: root — written by scripts/note-split and stripped by scripts/note-join
#import "note-prelude.typ": *


#show: conf.with(title: "Relation Algebra")

// `supplement: none` so a `@sec-…` reference prints the BARE number: the prose writes its own
// `§`, and the default supplement would set "Section §1.1." in the middle of a sentence.
#set heading(supplement: none)

// `▿` at the four generator glyphs' size and for the same reason: at running-text size it reads as a
// subscript, not an operator.  Not in note-style.typ — the proofs note shares that file and has no copair.
#show regex("▿"): it => text(size: 1.45em, it)
#show ref: it => if str(it.target) in refname { link(it.target, refname.at(str(it.target))) } else { it }

#NOTEROOT.update(true)
#include "ch/01-notation.typ"
#include "ch/02-relations.typ"
#include "ch/03.typ"
#include "ch/04.typ"
#include "ch/05-domain.typ"
#include "ch/06-maps.typ"
#include "ch/07-reduce.typ"
#include "ch/08.typ"
#include "ch/09-fracr.typ"
#include "ch/10-freyds.typ"
#include "ch/11-relator.typ"
#include "ch/12-combinatorial.typ"
#include "ch/13-optimisation.typ"
#include "ch/14-thinning.typ"
#include "ch/15-dynamic.typ"
#include "ch/16-greedy.typ"
