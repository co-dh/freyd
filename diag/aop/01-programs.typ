#import "../note-prelude.typ": *
#show: note-chapter.with(1)
// note-split: chapter 1 — this header is written by scripts/note-split and stripped by scripts/note-join
= Programs <sec-programs>

== Datatypes

== Natural numbers

== Lists

== Trees

== Inverses

== Polymorphic functions

== Pointwise and point-free

// B&dM §1.7, p.21–22: the calculation `listr outl · filter outr · zip · pair (id, listr p) = filter p`,
// one Lean theorem per step, in diagram order.  The hints are the book's, with its equation numbers.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Pointfree.filter_pointfree") \
    #src[pairing each element with its answer under `p` (`⟨𝟙,list(p)⟩ zip`), keeping the pairs
     answered `true` (`filter(π₂)`) and dropping the answers (`list(π₁)`) is `filter(p)`]],
  // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree@fa231941
  // two rows: ten panels in one row shrink the labels past reading
  lean-chain((
    (none, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step1.lhs", src[the starting composite]),
    (DF, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step1.rhs", src[definition of filter: `filter(p) ≜ list((p → wrap, nil)) concat`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step1@d635eea6
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step2.rhs", src[(1.6): `concat list(f) = list(list(f)) concat`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step2@1323a4f7
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step3.rhs", src[(1.8) backwards: `list(f) list(g) = list(fg)`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step3@5695cc7d
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step4.rhs", src[(1.11): `(p → f, g)h = (p → fh, gh)`; (1.5): `wrap list(f) = f wrap`; (1.4): `nil list(f) = nil`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step4@fdcb5b7c
  ), (
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step5.rhs", src[(1.9) backwards: `𝟙 = list(𝟙)`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step5@bb60f1c3
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step6.rhs", src[(1.7): `⟨list(f),list(g)⟩ zip = list(⟨f,g⟩)`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step6@f9681c65
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step7.rhs", src[(1.8) backwards: `list(f) list(g) = list(fg)`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step7@48d30922
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step8.rhs", src[(1.10): `h(p → f, g) = (hp → hf, hg)`; (1.1): `⟨f,g⟩π₁ = f`; (1.3): `f nil = nil`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step8@18b2392f
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step9.rhs", src[(1.12): `𝟙 f = f`]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step9@711631d0
    (EQ, "Freyd.Alg.RelSet.Pointfree.filter_pointfree_step10.rhs", src[definition of filter]),
    // lean:AOP.A1_7_Pointfree.RelSet.Pointfree.filter_pointfree_step10@2397640c
  )),
)]<filter-pointfree>
