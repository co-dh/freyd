// vecgen.typ — `gen` on `Vec`, cons side, in Hinze–Marsden's convention: a wire is a functor, a bead a
// natural transformation.  `[k]` is the functor `Vec(k) : X ↦ X[k]`, so `A[n][p][m]` is the wires
// `[n] [p] [m] A`.  Source `A[n]×A[n][p][m] = × ([n]×[n]) (𝟙×[p]) ⟨𝟙,[m]⟩ A`; the middle region is `𝒜×𝒜`,
// and a bead there is the `𝟙×(−)` lift of the map it is named after (`F(𝟙,moves)` is `×` past `𝟙×moves`).
// `moves` births `𝟙×[3]`, `trans` swaps it past `[n]×[n]`, `concat` merges it with `𝟙×[p]` into `𝟙×[3p]`;
// `zip` pulls `[n]` out of the product, `cp` pulls `[3p]` out; what is left, `× ⟨𝟙,[m]⟩`, is `[m+1]` by
// `A[m+1] ≜ A×A[m]`.  Bottom cut `[n] [3p] [m+1] A = A[n][3p][m+1]`.
//
// typst compile --root . --format png --ppi 220 diag/vecgen.typ diag/vecgen.png
#import "hm.typ": cetz, d, hm-wire, hm-region, hm-bead, hm-port, hm-name
#import "draw.typ": AC, UC, GIVEN1, idxcol

#set page(width: auto, height: auto, margin: 0.8cm, fill: white)

#let W = 8.6
#let H = 8.4

#let PROD = rgb("#b1605a")
#let CAA = rgb("#f5dcc4")

#let M = (2.6, 7.0)
#let T = (2.6, 5.6)
#let C = (3.8, 4.2)
#let Z = (1.4, 2.8)
#let P = (3.0, 1.4)

#let xw = ((1.0, 8.4), (1.0, 3.3), Z, (2.2, 2.3), (2.2, 1.9), P, (3.8, 0.9), (3.8, 0))
#let nn = ((2.6, 8.4), M, (3.4, 6.5), (3.4, 6.1), T, (1.8, 5.1), (1.8, 3.3), Z)
#let v3 = (M, (1.8, 6.5), (1.8, 6.1), T, (3.4, 5.1), (3.4, 4.7), C)
#let vp = ((4.2, 8.4), (4.2, 4.7), C)
#let v3p = (C, (3.8, 1.9), P)
#let vn = (Z, (0.6, 2.3), (0.6, 0))
#let v3q = (P, (2.2, 0.9), (2.2, 0))
#let vm = ((5.8, 8.4), (5.8, 0))
#let aw = ((7.4, 8.4), (7.4, 0))

#let vecgen-pic = cetz.canvas(length: 0.8cm, {
  hm-region(((0, 0), (0, 8.4), (1.0, 8.4), (1.0, 3.3), (1.4, 2.8), (2.2, 2.3), (2.2, 1.9),
             (3.0, 1.4), (3.8, 0.9), (3.8, 0)), AC)
  hm-region(((1.0, 8.4), (1.0, 3.3), (1.4, 2.8), (2.2, 2.3), (2.2, 1.9), (3.0, 1.4), (3.8, 0.9),
             (3.8, 0), (5.8, 0), (5.8, 8.4)), CAA)
  d.rect((5.8, 0), (7.4, 8.4), fill: AC, stroke: none)
  d.rect((7.4, 0), (8.6, 8.4), fill: UC, stroke: none)

  hm-wire(xw, col: PROD)
  hm-wire(nn, col: idxcol(`[n]×[n]`))
  hm-wire(v3, col: idxcol(`𝟙×[3]`))
  hm-wire(vp, col: idxcol(`𝟙×[p]`))
  hm-wire(v3p, col: idxcol(`𝟙×[3p]`))
  hm-wire(vn, col: idxcol(`[n]`))
  hm-wire(v3q, col: idxcol(`[3p]`))
  hm-wire(vm, col: idxcol(`⟨𝟙,[m]⟩`))
  hm-wire(aw, col: black)

  hm-bead(M, [`moves`], col: GIVEN1)
  hm-bead(T, [`trans`], col: GIVEN1)
  hm-bead(C, [`concat`], col: GIVEN1)
  hm-bead(Z, [`zip`], col: GIVEN1)
  hm-bead(P, [`cp`], col: GIVEN1)

  hm-port((1.0, 8.4), [`×`], col: PROD)
  hm-port((2.6, 8.4), [`[n]×[n]`], col: idxcol(`[n]×[n]`))
  hm-port((4.2, 8.4), [`𝟙×[p]`], col: idxcol(`𝟙×[p]`))
  hm-port((5.8, 8.4), [`⟨𝟙,[m]⟩`], col: idxcol(`⟨𝟙,[m]⟩`))
  hm-port((7.4, 8.4), [`A`])
  hm-port((0.6, 0), [`[n]`], dir: -1, col: idxcol(`[n]`))
  hm-port((2.2, 0), [`[3p]`], dir: -1, col: idxcol(`[3p]`))
  hm-port((3.8, 0), [`×`], dir: -1, col: PROD)
  hm-port((5.8, 0), [`⟨𝟙,[m]⟩`], dir: -1, col: idxcol(`⟨𝟙,[m]⟩`))
  hm-port((7.4, 0), [`A`], dir: -1)

  d.line((3.8, -0.55), (3.8, -0.75), (5.8, -0.75), (5.8, -0.55),
         stroke: 0.4pt + idxcol(`[m+1]`))
  hm-name((4.8, -0.95), [`[m+1]`], col: idxcol(`[m+1]`))

  hm-name((0.5, 5.5), [`𝒜`])
  hm-name((5.0, 7.8), [`𝒜×𝒜`])
  hm-name((6.6, 7.8), [`𝒜`])
  hm-name((8.0, 7.8), [`𝟏`])
  hm-name((2.6, 6.3), [`𝟙×[3]`], col: idxcol(`𝟙×[3]`))
  hm-name((4.8, 3.0), [`𝟙×[3p]`], col: idxcol(`𝟙×[3p]`))
})

#vecgen-pic
