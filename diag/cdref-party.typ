// cdref-party.typ — the note's OWN `party-mono` square, standing alone, so `scripts/svg-check
// --against` can hold the generated panel to it.  This is the first `#pair` of
// `diag/allegory-axioms.typ`'s `<party-mono>` — `(𝟙×list((R×R)°))S⊑S(R×R)°` — copied mark for
// mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.RelSet.Party.party_mono` IS that inequation.
//
//   typst compile --root . --format svg diag/cdref-party.typ diag/cdref-party.svg
//   ./scripts/diag-export --commutative Freyd.Alg.RelSet.Party.party_mono
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T, FB, B) = ((-4.2, 1.25), (4.2, 1.25), (-4.2, -1.25), (4.2, -1.25))
  ar(FT, T, GIVEN1, s0: 1.9, s1: 1.5); ar(FB, B, GIVEN1, s0: 1.9, s1: 1.5)
  ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 1.8, GIVEN1)[`S`]; lab(0, -1.8, GIVEN1)[`S`]
  lab(-6.4, 0, GIVEN2)[`𝟙×list((R×R)°)`]; lab(5.2, 0, GIVEN2)[`(R×R)°`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(FT.at(0), FT.at(1), black, `F([A]×[A])`); node(T.at(0), T.at(1), black, `[A]×[A]`)
  node(FB.at(0), FB.at(1), black, `F([A]×[A])`); node(B.at(0), B.at(1), black, `[A]×[A]`)
})
