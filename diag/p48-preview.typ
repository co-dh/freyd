// SCRATCH.  `scripts/diagram`'s output for IntroString p.48's two panels, pasted unedited, so the
// generator's picture can be put beside the page's own.  Not part of `make p`.
#import "allegory-axioms.typ": dpanel
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set text(11pt)

#stack(dir: ltr, spacing: 40pt,

// B(τ) μ B(ν) B(σ) λ
dpanel(6, 9.15, 6.3,
  ((1.125, 1, "bot", none, none), (3.425, 1, "bot", none, none), (1.125, 4, 1, [`B`], none), (0.55, "top", 4, none, none), (1.7, 5, 4, [`B`], none), (3.425, 2, 1, [`A`], none), (5.15, 2, "bot", none, none), (3.425, 3, 2, [`C`], none), (2.85, 5, 3, [`C`], none), (1.7, "top", 5, none, none), (2.85, "top", 5, none, none), (4, "top", 3, none, none), (5.15, "top", 2, none, none)),
  ((5, [`τ`], black, 1.7, 2.275), (4, [`μ`], black, 0.55, 1.125), (3, [`ν`], black, 2.85, 3.425), (2, [`σ`], black, 3.425, 4.2875), (1, [`λ`], black, 1.125, 2.275)),
  ((0.55, [`B`]), (1.7, [`C`]), (2.85, [`B`]), (4, [`C`]), (5.15, [`A`]), (6.3, [`x`])),
  ((1.125, [`A`]), (3.425, [`B`]), (5.15, [`C`]), (6.3, [`x`]))),

// B(τ) B(B(C(σ))) B(B(σ)) B(λ) λ A(μ) A(B(ν))
dpanel(8, 9.15, 6.3,
  ((0.55, 3, "bot", none, none), (2.275, 2, "bot", none, none), (1.7, 3, 2, [`B`], none), (0.55, "top", 3, none, none), (1.7, 4, 3, [`A`], none), (2.85, 4, 2, [`B`], none), (1.7, 7, 4, [`B`], none), (2.85, 5, 4, [`A`], none), (4.575, 1, "bot", none, none), (4, 5, 1, [`C`], none), (2.85, 7, 5, [`C`], none), (1.7, "top", 7, none, none), (2.85, "top", 7, none, none), (4, 6, 5, [`A`], none), (5.15, 6, 1, [`C`], none), (4, "top", 6, none, none), (5.15, "top", 6, none, none)),
  ((7, [`τ`], black, 1.7, 2.275), (6, [`σ`], black, 4, 4.575), (5, [`σ`], black, 2.85, 3.425), (4, [`λ`], black, 1.7, 2.275), (3, [`λ`], black, 0.55, 1.125), (2, [`μ`], black, 1.7, 2.275), (1, [`ν`], black, 4, 4.575)),
  ((0.55, [`B`]), (1.7, [`C`]), (2.85, [`B`]), (4, [`C`]), (5.15, [`A`]), (6.3, [`x`])),
  ((0.55, [`A`]), (2.275, [`B`]), (4.575, [`C`]), (6.3, [`x`]))),
)
