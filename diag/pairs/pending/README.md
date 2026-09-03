# Fixtures the generator cannot draw yet

`hm-check` reads `diag/pairs/*.json`, not this directory, so nothing here runs. Each file is a
page transcribed literally — `counts` and `bbox` still audit against the svg under
`hm-check --verify-fixtures` if it is moved back up — and each records one convention the
generator does not have. Move a file up one directory once its line below is fixed.

| fixture           | ours                              | the page                          | what has to change                                                                     |
|-------------------|-----------------------------------|-----------------------------------|----------------------------------------------------------------------------------------|
| `fig-p74-eta.json`| `η` eats `A` and re-emits `M A`   | `η` has no arms; `A` runs past    | An arm-less bead is recognised by LABEL (`isunit`, `scripts/diagram`, `𝟙%∋`), not by a signature whose source is the unit. Type `η : 𝟙 ⟶ M` and the label test goes away. |
| `3.1b.json`       | `μ∘M` spans all four wires        | `μ` spans the two `M` it names    | `across` splits `s∘t`, but the bead still takes the whole word as arms. `3.1a` passes only because its book side was transcribed bent-in. |
| `2.5.json`        | `join` spans `List List`          | the bar covers `A` as well        | The mirror of the row above: which wires a bar reaches has to follow from the signature, one rule for both directions. |
| `fig-p40-spider.json` | an object wire `x` on both edges | a 2-cell with no object at all | `object-wire-added` is declared by the transcriber and applied by hand; nothing applies it to a graph. |
