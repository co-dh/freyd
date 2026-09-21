// cdref-distnat.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the SECOND `cetz.canvas` of `diag/ch/13-optimisation.typ`'s
// `<dist-str>` as the author drew it, copied mark for mark: the distributivity square at `est(≤)`
// and `+` on `Nat`, each corner carrying its VALUE under its type inside the node's own box.
//
//   typst compile --root . diag/cdref-distnat.typ diag/cdref-distnat.svg
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let val(s) = { show raw: set text(size: 8.5pt); text(luma(110), s) }
  let vnode(p, ty, el) = node(p.at(0), p.at(1), black,
    grid(align: center, row-gutter: 2.5pt, ty, val(el)))
  let (FEA, EA, FA, A) = ((-4.8, 1.9), (4.8, 1.9), (-4.8, -1.9), (4.8, -1.9))
  ar(FEA, EA, GIVEN1, s0: 2.0, s1: 3.2); ar(FA, A, GIVEN1, s0: 2.15, s1: 2.05)
  ar(FEA, FA, GIVEN2, s0: 1.0, s1: 1.0); ar(EA, A, GIVEN2, s0: 1.0, s1: 1.0)
  lab(0, 2.75, GIVEN1)[$frac(#[`(∋×∋)+`], ∋)$]; lab(0, -2.5, GIVEN1)[`+`]
  lab(-6.75, 0, GIVEN2)[`est(≤)×est(≤)`]; lab(5.75, 0, GIVEN2)[`est(≤)`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  vnode(FEA, `E Nat×E Nat`, `(xs,ys)`); vnode(EA, `E Nat`, `{x+y∣x∈xs∧y∈ys}`)
  vnode(FA, `Nat×Nat`, `(min(xs),min(ys))`); vnode(A, `Nat`, `min(xs)+min(ys)`)
})
