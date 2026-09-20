// Standalone preview of how the fold draws today (the BEFORE of the review pair): an opaque
// banana bead on a bare object wire.
//   ./scripts/diag-export --string Freyd.Alg.relCata_fusion
//   typst compile --root . diag/sample-fold-before.typ --format png --ppi 220 diag/sample-fold-before.png
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#import "generated/Freyd.Alg.relCata_fusion.typ": pic
#pic
