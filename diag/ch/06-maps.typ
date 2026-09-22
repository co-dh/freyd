#import "../note-prelude.typ": *
#show: note-chapter.with(6)
// note-split: chapter 6 — this header is written by scripts/note-split and stripped by scripts/note-join
= Maps

// A 2×2, not a list of four: the ROW says which composite (`R° R`, `R R°`), the COLUMN which way the
// containment runs, so each property's opposite is the cell diagonally across.
#disp[#table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: 10pt, stroke: 0.4pt + luma(190),

  [*surjective* \ #src[`𝟙⊑R°R`, that is, `R°` entire.]],
  [*single valued* \ #src[`R°R⊑𝟙`]],

  [*entire* \ #src[`𝟙⊑RR°`. With *single valued*, a *map*.]],
  [*injective* \ #src[`RR°⊑𝟙`]],
)]<map-square>

#disp[#table(
  columns: (1fr, 2.2fr),
  align: (center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*picture*]),

 [#leanf("Freyd.Alg.simple_dist_inter") \ #v(2pt) #src[`F` single valued]],
  // lean:Freyd.S2_10.simple_dist_inter@46ef7904
  grid(columns: 3, align: horizon, column-gutter: 10pt,
    [#P(p-236a, s: 74%) #v(-9pt) #align(center, src[one person who admires both])],
    text(17pt)[=],
    [#P(p-236b, s: 74%) #v(-9pt) #align(center, src[`a` at A, `b` at B])],
  ),
)]<map-meet>

