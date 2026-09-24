// vtree.typ — the walker `diag-export --value` emits into: a DATA VALUE that is a tree, drawn as one.
// The exporter reads the tree off the declaration and places it (`diag/tool/ValueTree.lean`): each
// node comes with its leaf column `x`, its level `depth` and its labels, each edge as the indices of
// parent and child.  This file only scales and draws, so a picture cannot disagree with the value.
// The first label is the node's name, set in raw; the rest are small and grey — the employee's
// rating beside the employee.

// `cetz` through `circuit.typ`, not from the package: that is where the `--input nodraw=1` shim lives.
#import "circuit.typ": cetz, d
#import "draw.typ": node
#import "note-style.typ": P

#let VX = 2.0   // one leaf column
#let VY = 2.2   // one level

#let vtree(nodes, edges) = P(cetz.canvas(length: 0.8cm, {
  let at(n) = (n.x * VX, -n.depth * VY)
  for (p, q) in edges { d.line(at(nodes.at(p)), at(nodes.at(q)), stroke: 0.75pt + black) }
  // Nodes last: `node` fills white, so each edge's stub under the label is covered.
  for n in nodes {
    node(..at(n), black, [#raw(n.labels.at(0))#for l in n.labels.slice(1) [ #text(9pt, luma(105))[#l]]])
  }
}), s: 100%)
