// cdref-laxclosure.typ — the note's OWN `K(φ)` square, standing alone, so `scripts/svg-check
// --against` can hold the generated panel to it.  This is the `a relator K` row of
// `diag/allegory-axioms.typ`'s `<lax-closure>` — `K(G(R))K(φʙ)⊑K(φᴀ)K(F(R))` — copied mark for
// mark: same `laxsq` corners and labels, same `ar`/`lab`, same `length: 0.8cm`.
// `Freyd.Alg.Relator.map_slides` IS that statement, its binders named in the note's letters.
// The component labels are the note's `` `φ` ``#sub[`` `A` ``] set as the one raw name a generated
// label can write, `φA`: a generated label is one `raw`, and `raw` carries no subscript.
//
//   typst compile --root . --format svg diag/cdref-laxclosure.typ diag/cdref-laxclosure.svg
//   ./scripts/diag-export --commutative Freyd.Alg.Relator.map_slides
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (GT, FT, GB, FB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(GT, FT, GIVEN1, s0: 0.75, s1: 0.75); ar(GB, FB, GIVEN1, s0: 0.75, s1: 0.75)
  ar(GT, GB, GIVEN2, s0: 0.55, s1: 0.55); ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 1.8, GIVEN1)[`K(φA)`]; lab(0, -1.8, GIVEN1)[`K(φB)`]
  lab(-3.8, 0, GIVEN2)[`K(G(R))`]; lab(3.8, 0, GIVEN2)[`K(F(R))`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(GT.at(0), GT.at(1), black, `KGA`); node(FT.at(0), FT.at(1), black, `KFA`)
  node(GB.at(0), GB.at(1), black, `KGB`); node(FB.at(0), FB.at(1), black, `KFB`)
})
