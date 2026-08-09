// The sheet's content, shared by both shapes: Cheatsheet.typ (phone, one column) and
// Cheatsheet-2col.typ (A4, two columns) differ only in the page they pour it into.
// Two contents, though, from this one source: those two build the Rel-focused selection,
// while Cheatsheet-full.typ passes `--input full=1` (see Makefile) and so also gets the
// entries the part files spread through `fullonly` — everything listed as full-only in
// their headers. What follows is omitted from both.
// Deliberately omitted: chapter 2 (allegories); the τ-category apparatus (§1.49–1.4(12))
// and the other machinery that exists only to prove metatheorems; every example built on
// ℒℋ (local homeomorphisms) and its slices 𝒮h(Y) (Lazard sheaves); the abelian block of
// §1.5 (Rel is only half-additive); the Heyting-algebra block §1.72–1.72(11) and the
// Heyting clauses elsewhere (Rel is no Heyting category); §1.(10) sconing, a gluing
// construction along Γ = (1,−) that never touches Rel; all proofs.
#import "style.typ": *

#include "part-1.4.typ"
#include "part-1.5.typ"
#include "part-1.6.typ"
#include "part-1.7.typ"
#include "part-1.8.typ"
#include "part-1.9.typ"
