// veccat1.typ — `cat : Vec(4)×Vec(5)⟶Vec(9)` in Hinze–Marsden's convention: the index is COMPUTED BY
// A WIRE.  `Vec : ℕ⟶𝒜` is `n ↦ Vec(n,Int)` (`Int` pinned; `ℕ` the discrete category, so nothing but
// identities travel on the object wire `(4,5)`), `+ : ℕ×ℕ⟶ℕ` is a functor because any function
// between discrete categories is one, `Vec×Vec : ℕ×ℕ⟶𝒜` is the composite `(m,n) ↦ Vec(m)×Vec(n)`
// (pairing and product as one wire), and `cat : Vec×Vec ⇒ Vec∘+` has one arm and two legs.  `9` is
// never written: the bottom cut reads `Vec(+(4,5))`, the `+` wire beside the `(4,5)` wire.
//
// HAND-DRAWN because `scripts/diagram` lays one category out beside `𝟏` and this needs `ℕ×ℕ`, `ℕ`
// and `𝒜`.  Applicative across, `𝟏` grey at the right, source above, target below.  Regions and the
// wires bounding them share one point list each, so a fill cannot drift off its wire.  The note
// imports `veccat-pic`; the `#set page` and the trailing call make this file its own PNG.
//
// typst compile --root . --format png --ppi 220 diag/veccat1.typ diag/veccat1.png
#import "hm.typ": cetz, d, hm-wire, hm-region, hm-bead, hm-port, hm-name
#import "draw.typ": AC, UC, GIVEN1

#set page(width: auto, height: auto, margin: 0.8cm, fill: white)

#let W = 5.0
#let H = 5.0
#let XL = 1.0         // the `Vec` leg
#let XR = 2.5         // the `+` leg
#let XO = 4.1         // the object wire `(4,5) : 𝟏⟶ℕ×ℕ`
#let B = (1.75, 2.5)  // the `cat` bead: one arm in, two legs out, off the object wire
#let KN = 0.6         // knee below the bead, `hm.typ`'s KNEE

#let arm = ((B.at(0), H), B)
#let legL = (B, (XL, B.at(1) - KN), (XL, 0))
#let legR = (B, (XR, B.at(1) - KN), (XR, 0))

#let VEC = rgb("#8193c9")   // `Vec×Vec` and `Vec`: one functor family, one hue
#let PLUS = rgb("#cc5500")  // `+`
#let CNN = rgb("#cfdff2")   // `ℕ×ℕ`
#let CN1 = rgb("#e9f0f9")   // `ℕ`

#let veccat-pic = cetz.canvas(length: 0.8cm, {
  hm-region(((0, 0), (0, H)) + arm + legL.slice(1), AC)             // 𝒜, left
  hm-region(legL.rev() + legR.slice(1), CN1)                        // ℕ, below the bead
  hm-region(arm + legR.slice(1) + ((XO, 0), (XO, H)), CNN)          // ℕ×ℕ, up to the object wire
  d.rect((XO, 0), (W, H), fill: UC, stroke: none)                   // 𝟏
  hm-wire(arm, col: VEC)
  hm-wire(legL, col: VEC); hm-wire(legR, col: PLUS)
  hm-wire(((XO, H), (XO, 0)), col: black)
  hm-bead(B, [`cat`], col: GIVEN1)
  hm-port((B.at(0), H), [`Vec×Vec`], col: VEC); hm-port((XO, H), [`(4,5)`])
  hm-port((XL, 0), [`Vec`], dir: -1, col: VEC); hm-port((XR, 0), [`+`], dir: -1, col: PLUS); hm-port((XO, 0), [`(4,5)`], dir: -1)
  hm-name((0.6, 4.3), [`𝒜`]); hm-name((1.75, 0.7), [`ℕ`])
  hm-name((3.3, 4.3), [`ℕ×ℕ`]); hm-name((4.55, 4.3), [`𝟏`])
})

#veccat-pic
