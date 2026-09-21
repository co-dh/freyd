[X] 13.3.5b didn't proved step by step, so is 13.3.5c
[X] remove the formuls in 13.3.5e row 2, 3, 4, 5.
[X] 13.3.4g row 2 , 1 over e.
[X] 12.1d no l, r. no desc in header. remove B&M $5.6. P.124, add type to 12.1e. it shuld be generated.
[X] make 13.2.3a diagram a 20% taller.
[X] 13.3.1c natural langauge. remove formulas. remove circuit
[X] 14.1d, thin Q on E line? is that correct?
[X] add space around ∪ everywhere in formulas and labels, `cons ∪ π₂` not `cons∪π₂` (12.1d and every other display, generator spelling included)
[X] circuit wire types print E[A], not E([A]); applies to every type label in every circuit diagram
[X] 12.1d rows 4–5 circuits are still hand-drawn (sbB4, sbB5); generate them with the fork kind
[X] 12.1d row 4 HM panel shows a horizontal bar; check it is generated and the bar goes with the straight-wire default
[X] scanline check on in make p; if slow, full scan once, then only the changed diagrams
[X] TODO.md: mark finished items with [X]
[X] six HM panels stay hand-drawn and uncertified because `scripts/scanline`'s `BRANCH` table names only
    cons/nil/plus/zero, so a case split on [base,step]°, [wrap,cat]°, [nil,extend]°, [nil,expand]°, β° or
    [arb,step]° cannot be cut; a sum of arrows (𝟙+(X×𝟙)) has no bead either.  Register the algebra's own
    branch names, or a general fallback, so all six generate and certify.
[X] all $14, $15, $16 HM diagram has function on functor line. regenerate them. no need for me to review for now. generate their circuit diagram too, no review from me.
[X] check claude session usage daily, find token usage and time usage, find opportunity to optimize. summarize as rule for review
[X] 11.4.2a bottom string diagram, make both side of = same height and align on alpah.  labeledas alpha_B sucks in S. ( use a better English). review png first
[X] replace every hand-draw picture with the generator, and remove code that used to hand draw. let user review png first.
    done: 13.6b rows 2/3/5 (van-fold deleted), 16.4b row 4, 13.4.3c rows 2/3 certified, and the four
    tinted literals in 7.2b/11.5.1c now regenerate (cert: tint carries a bead's colour).
    left: 11.6.4b rows 3/4/5 — tpan/tpanR, the last hand-draw helper, in §11.6.
[X] redraw 11.5.1b
[X] shrink the diagram in 11.4a and try to fit fusion 11.4.2 in the same page.
[X] on string diagram, (|alpha |) take type argument from the line under it. add this to 11.4a,  11.4.2a.
[X] 11.6.1a , 11.6.2a need revisit. like what we did for initial algebra.  alpha is natural.
[X] revisit 11.6.2a. alpha is natural and draw wrong. secondly, how to draw things inside (| |),
    IntroString has fold (| |) for different purpose, but claude said that catamorphsim is a special case of fold,
    maybe that can be used to draw inside catamorphism.
[X] break the circuit diagram code and skill into a separated one.
[X] there are hard coded name, color in the string diagram generator make it less general. make it general.
[X] HM diagram on both side of <=, = should have the same hight and aligned.
    e.g. for LaT, align on the φ. you can ask me
[X] 13.2b generate /string-diagram
[X] why 13.5.3a suddenly becomes so tall, with space wasted on top? same for 13.5.5b row 2.
[X] 13.5.2a make the 3 diagram same height. you do not fix a global(cross the note) height.
[X] 13.3b no HM diagram (13.3.1b done)
[X] 13.5.4 section title: prepend: generate is F-Alg.
[X] rename all generate to gen. the lean code, use our lean-refactor. and the allegory-axioms.typ.
[X] 13.5.5. section header, add type of Q : F(N A,N(L A))⟶N(L A), and say it's  F(N A,−)'s algebra
[X] squeeze the boxes around the diagrams. space has value.
[X] 13.4.4a too much space at the bottom of string diagrams. add checker, find root cause, fix in general.
[X] in general, the lable are covered by the text. e.g. (13.4.4a becomes 3.4.4a. add checker, find root cause, fix in general
[X] add $13.6.1 for prefix . secure <= secure . prefix. on Bird P185. add string diagram for secure(bmax def) and it,
[X] add string diagram of new, glue, fusion , old  in algprog.pdf P185 as 13.6.1. lean proof, mark.
[X] add string diagram of prove of 7.14 algprog.pdf P186 as 13.6.2. lean proof, mark.
[X] add string diagram of H as 2 string diagram for each branch of U of algprog.pdf P186 as 13.6.3. lean proof. mark.
[X] add string diagram of 7.16 and 7.17 algprog.pdf P187 as 13.6.4. lean proof. mark.
[X] add string diagram of 7.19, 20, 21 of algprog.pdf P187 as 13.6.5. plus the derive on P188. lean proof. mark.
[X] add 8.2 of algprog.pdf P194
[X] 14.1.2d need to add "given R∩(S°S)⊑Q ) in the title, and remove "keeping one ..."
[X] add string diagram of  the first formulas after 8.3 op algprog.pdf P194. prove the second with our table format like 14.1.2d.
[X] 3 circuit cells in ch12 were hand-laid `#cpanel` literals; every circuit in ch12–16 is a `#leanc`.
[X] 11.5.1b follows the declaration `alpha_natural_split`: five arrows, no chord `F(f,𝟙)α`, drawn
    by `#leancd` (his decision).
[X] Nothing in the note gates ran the whole-repository `lake build`: a rename left
    `AOP/A5_7_PartyBeads.lean` broken and `make p` stayed green, because the gates build only what
    `diag-export` imports. `make p` now runs `./scripts/cap lake build` first.
[ ] 4 commutative canvases name no declaration at all (11.2.1b, 13.2.1a, 13.2.3a, 13.3.1b#2). Each
    needs a new Lean declaration and a generator feature: node value labels; opening an `∃` at its
    witness plus a `⋢` face mark; three records on one canvas with bowed arrows; `Face.paste` as a
    fold over four faces.
[X] ch13's last four formula headers are `#leanf`. ch11's formulas (`#frc(...)`, canvas labels) are
    untouched.
[X] Delete the typst a conversion orphaned, in the same change that converts: a helper no chapter
    calls is dead. Swept for ch11–16 and the shared helper files; the rule stands for ch1–10.
[X] The python feed route is deleted (`scripts/circuit`, `relexpr.py`, `panels.py`,
    `circuit-check`, `circuit-panels.txt`, `circuit-slice.typ`); a circuit comes only from
    `diag-export --circuit`.
[ ] `cd-check` runs in neither `make c` nor `make p`. Put it in the routine gate once 11.5.1b and
    the four undeclared canvases above are settled — a gate nobody runs is not a gate. `types` is
    outside too; decide the same for it.
[X] `diff-crop --key` resolves the key against the pdf it is handed (a chapter pdf renumbers from
    1), and the whole-pdf mode exits nonzero when pages differ and nothing was written.
[X] `diff-crop --key` anchors on the FIRST `(key)` a pdf prints, which for 13.2.1a and 13.3.1b is a
    cross-reference on an earlier page, so both halves came out as the same unrelated text and the
    pair was refused as pixel-identical. The display's own number is the one set in the margin
    column; anchor on that occurrence.
    `find_anchor` takes the occurrence furthest right; an unverified seed runs down from the label by
    the row's `h`, and the window opens at the label so the section heading stays out.
[X] Chapters 1–10: 5b/dom-collapse, 5.1a/dom-slide, 7b/banana-split and 10.1a's two panels are
    drawn from declarations (`Freyd.Diag.dom_cd`, `Freyd.Diag.dom_comp_le`,
    `pair_relCata_eq_relCata_pair`, `singletonMap_comp_eps`, `Λ_eps_reflection`); `snake` and
    `domstr` are deleted.
[ ] Two pictures of named people, 8.1a/div-comp-pic and 9c/syq-pic, are the last hand-laid
    canvases of chapters 1–10 and no route draws them: a finite relation between named elements
    is neither a string, a circuit nor a commutative diagram. None of those chapters' formulas
    is a `#leanf`.
[X] `diag-regen --missing` could not draw a NEW `#import "generated/<decl>.typ"` of
    `diag/note-prelude.typ`: it lists the obligations by `typst query`, which fails on the very
    import that is missing, so the first panel of a new declaration has to be written by hand
    with `./scripts/diag-export <decl>`. The imports are now drawn before the listings run.
