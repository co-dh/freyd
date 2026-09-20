// Standalone preview of the fold's own panel, rendered once BEFORE the exporter change and once
// after, to compare the two shapes.  IntroString (5.8) middle draws a fold as a region that CLOSES
// at the bead; this page is how ours draws.
//   ./scripts/diag-export --string Freyd.Alg.fold
//   typst compile --root . diag/sample-fold.typ --format png --ppi 220 diag/fold-after.png
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#import "generated/Freyd.Alg.fold.typ": pic
#pic
