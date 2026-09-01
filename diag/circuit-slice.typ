// The rendered acceptance test for diag/CIRCUIT-GEN.md §5: `./scripts/circuit --slice`'s output,
// pasted verbatim, so the generated picture can be looked at beside the note's own row.  Rows 2 and
// 3 of the slice are missing because the shared grammar cannot open `∪`, `⊸` or `[f,g]` yet (§1.5);
// `--slice` names each of them, and each lands here as it starts generating.
#import "cpanel.typ": cpanel, frc
#set page(width: auto, height: auto, margin: 12pt)

// 13.3.3d r1  S%∋ est(R°)   [F([A]) ⟶ [A]]
#cpanel((k: "seq",
  items: ((label: frc([`S`]), chamfer: false, frac: true),
          (label: [`est(R°)`], chamfer: true)),
  seams: ((0, [`E([A])`]),),
  src: [`F([A])`], tgt: [`[A]`]),
  cert: (expect: "S%∋ est(R°)", src: "F([A])", tgt: "[A]"))
