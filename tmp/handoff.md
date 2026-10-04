# Handoff: def-table cells the exporter could not print

Done:
- `--type` (TypeRender.render): plain functions, `Type`, `Prop` declarations print the Lean type of
  the name-cell term (declaration at its named binders); `IsThinlist(Q,thinlist) : Prop`.
- `--formula` def path (FormulaRender.render): a def whose value holds a matcher/recursor prints its
  Lean equations (`head[l] = l, head([l]⧺a) = l`); a hom-valued `fun x y => P` prints `x R y ⟺ P`.
- `Unknown constant null`: Label.branchesOnInput opened a 2-arm match on a non-Sum/Bool carrier, which
  reached sectionShow → stxShow → ppTerm on a `null` list node. Both fixed; `head` rule for headLine.

Left (vocabulary, not mechanism): names with no printing rule, refused by ExprReader.checkSpelled —
ListRel.total, ListRel.subseqP, Tour.{cost,replaceHead,Tour,outcost,nxt,incost,hd,droplAlgFn,
droprAlgFn}, Paragraph.{wasteFn,widthFn,partAlg,allFitP,sqr,new,newAlgFn,glue,glueAlgFn},
Knapsack.dropFn. Fix: `attribute [diag_noted] …` or an unexpander in diag/StrDiagNames.lean, or a
rename in Lean to the book's word.
