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
[.] replace every hand-draw picture with the generator, and remove code that used to hand draw. let user review png first.
    done: 13.6b rows 1/2/4 (van-fold deleted), 16.4b row 4, 13.4.3c rows 2/3 certified.
    left: 11.6.4b rows 3/4/5 (tpan/tpanR, §11.6 held by another agent); the four dpanel literals in
    §7.2 and §11.5.1c that carry bead colours the generator does not emit.
[.] redraw 11.5.1b
[X] shrink the diagram in 11.4a and try to fit fusion 11.4.2 in the same page.
[ ] on string diagram, (|alpha |) take type argument from the line under it. add this to 11.4a,  11.4.2a.
[ ] 11.6.1a , 11.6.2a need revisit. like what we did for initial algebra.  alpha is natural.
[ ] revisit 11.6.2a. alpha is natural and draw wrong. secondly, how to draw things inside (| |),
    IntroString has fold (| |) for different purpose, but claude said that catamorphsim is a special case of fold,
    maybe that can be used to draw inside catamorphism.
[X] break the circuit diagram code and skill into a separated one.
[X] there are hard coded name, color in the string diagram generator make it less general. make it general.
[.] HM diagram on both side of <=, = should have the same hight and aligned.
    e.g. for LaT, align on the φ. you can ask me
[X] 13.2b generate /string-diagram
[X] why 13.5.3a suddenly becomes so tall, with space wasted on top? same for 13.5.5b row 2.
[X] 13.5.2a make the 3 diagram same height. you do not fix a global(cross the note) height.
[.] 13.3b no HM diagram (13.3.1b done)
[X] 13.5.4 section title: prepend: generate is F-Alg.
[X] rename all generate to gen. the lean code, use our lean-refactor. and the allegory-axioms.typ.
[X] 13.5.5. section header, add type of Q : F(N A,N(L A))⟶N(L A), and say it's  F(N A,−)'s algebra
