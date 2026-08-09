// Bird & de Moor, "Algebra of Programming", chapter 10 "Greedy Algorithms" (book pp. 245-264),
// mirrored item by item into Freyd's conventions: composition by juxtaposition in DIAGRAM order.
//
// AUDIT — every numbered item of chapter 10, kept or dropped.
//   §10.1  Theorem 10.1 and Proposition 10.1 kept; the book states both without proof (Theorem
//          10.1 is Theorem 9.2's proof again, Proposition 10.1 is Proposition 9.1's).  The
//          recalled Proposition 9.4 is one row, with the caveat the section adds to it.
//   §10.2  (10.1) kept.  The `loop'` transformation, the specification, both conditions, the
//          counterexample against `V = prefix`, the derivation and the final catamorphism kept.
//          Ex 10.1, 10.3, 10.7, 10.8 kept (each states a law usable away from its problem).
//          Ex 10.2 DROPPED (a question the book does not answer), 10.4 DROPPED (it discharges
//          the two claims inside one derivation) — the claims themselves are on the sheet, since
//          the derivation cites them.  The proof of `V expand ⊂ expand ∪ πV` is DROPPED: it is
//          five conditional-pushing steps over those two claims and adds nothing once they are
//          stated.
//   §10.3  (10.2)-(10.8) kept, with the (10.7)+(10.8) chain, the greedy-condition chain — the
//          one tricky proof in the chapter, and where `Q` comes from — and the closing shunt.
//          Both worked tables kept.  Ex 10.5, 10.6 DROPPED (missing proofs), 10.9-10.11 DROPPED
//          (variations the book poses without answering).
//   §10.4  (10.9) kept.  Specification, the removal of `round°`, the fusion that makes
//          `inrange° val` a catamorphism, the reason `step°` is a map, `Q`, the program and the
//          integer version kept.  The 10-step greedy chain is given as its shape, not its steps:
//          it is nine shunts around one inequation, `!nil ⊂ cons R`, which is the whole content.
//          Ex 10.14, 10.15 kept.  Ex 10.12 DROPPED (discharges one claim), 10.13 DROPPED (asks
//          for the derivation again).
//   The Gofer programs are dropped throughout; what each computes and what it costs is one row.
//   Chapter 10 prints no figure and no diagram at all.
//   Nothing is dropped for being false in Rel.
#import "/AOP/bdm.typ": *

= 10 Greedy Algorithms

== 10.1 Theory

Weed out all but a #emph[single] decomposition at each step and dynamic programming becomes greedy.
The theory is chapter 9's; the chapter is its applications.

#dt(
  ("10.1 ✓", [#Th[#D("the greedy theorem") $H = ⦇T⦈^degree ⦇h⦈$ and $M = Lambda(H)(min R)$, $h$
    monotonic on $R$, and $Q$ with $Q^degree (F H) h subset (F H) h thin R^degree$ — exactly
    Theorem 9.2's hypotheses. Then
    $ (mu X : Lambda(T^degree)(min Q)(F X) h) subset M. $]]),
  ("", [$min Q$ where Theorem 9.2 had $"thin" Q$: commit to one decomposition instead of keeping a
    thinned set. Same hypotheses, far stronger conclusion — and the price is a further, very
    strong condition for the refinement to a program: $Q$ must be a #emph[connected] preorder on
    the sets $Lambda(T^degree)$ returns. Distinct from Theorem 7.2, which greedily folds a
    catamorphism.]),
  ("P 10.1", [$F alpha$ is usually a coproduct. If $V_1 V_2^degree = nothing$ then
    $ Lambda([V_1,V_2]^degree)(min(Q_1+Q_2))[U_1,U_2] \
      = ("ran" V_1 -> W_1, W_2), $
    $ W_i = Lambda(V_i^degree)(min Q_i) U_i. $
    This is the step that turns each case study's fixed point into a conditional program.]),
  ("", [Proposition 9.4 still supplies $Q = F(U,V)$ from preorders with $F(U,R) h subset h R$ and
    $V^degree H subset H R^degree$ — but now $Lambda(T^degree)(min Q)$ must also be #emph[entire],
    which that choice does not guarantee.]),
)

== 10.2 The detab–entab problem

#dt(
  ("10.2 ✓", [Two exercises of Kernighan and Ritchie. #emph[detab] replaces each tab by blanks up to
    the next stop, every $n$ columns; #emph[entab] replaces runs of blanks by the fewest tabs and
    blanks giving the same spacing. They belong together because #emph[entab] is specified as an
    optimal converse of #emph[detab].]),
  ("", [Snoc-lists. $"detab" = ⦇"nil", "expand"⦈$ with
    $ "expand"(x,a) = (a = "TB" -> "fill" x, x cc [a]), $
    $ "fill" x = x cc "blanks"(n - ("col" x) mod n), $
    $ "col" = ⦇"zero", "count"⦈, $
    $ "count"(c,a) = (a = "NL" -> 0, c+1). $]),
  ("", [Tupling keeps the column count: $chevron.l "detab", "detab" "col" chevron.r =
    ⦇"base", "step"⦈$ with $"base" = ([],0)$ and, writing $m = n - c mod n$,
    $ "step"((x,c),a) = cases(
        (x cc ["NL"], 0) & a = "NL",
        (x cc "blanks" m, c+m) & a = "TB",
        (x cc [a], c+1) & "else.") $]),
  ("Ex 10.1", [#D("loop") a snoc-list catamorphism is a loop over the cons-list:
    $"convert" ⦇"base","step"⦈ = chevron.l "base", 1 chevron.r ("loop" "step")$. And when the two
    have the special shape $"base" = chevron.l "nil", c_0 chevron.r$ and
    $"step"((x,c),a) = (x cc f(c,a), thin g(c,a))$, the accumulator can go:
    $ chevron.l "base", 1 chevron.r ("loop" "step") thin pi
      = chevron.l c_0, 1 chevron.r ("loop"'(f,g)), $
    $ "loop"'(f,g)(c, []) = [], $
    $ "loop"'(f,g)(c, [a] cc x) \
      = f(c,a) cc "loop"'(f,g)(g(c,a), x). $]),
  ("", [Why it pays: the left side builds $((x_1 cc x_2) cc dots.c) cc x_n$ and the right side
    $x_1 cc (x_2 cc (dots.c cc x_n))$. Where $cc$ is defined by $"cons"$, the second is
    asymptotically cheaper.]),
  ("", [#emph[entab] is a shortest output that decodes back:
    $"entab" subset Lambda("detab"^degree)(min R)$ with
    $R = "length" "leq" "length"^degree$.]),
  ("", [$"nil"$ and $"expand"$ have disjoint ranges, so look for $Q = F(U,V)$ with
    $F(U,V) = 1 + (V times U)$. Proposition 9.4 asks for
    $ F(U,R) sans("in") subset sans("in") R quad "and" quad "detab" V subset R thin "detab", $
    and, on top, $Lambda(["nil","expand"]^degree)(min Q)$ must be entire.]),
  ("Ex 10.3 ✓", [The first holds for #emph[every] preorder $U$ on characters, since
    $F(Pi, R) sans("in") subset sans("in") R$. Taking $U = 1 union (Pi thin "TB")$ — everything
    above the tab — prefers tabs to blanks.]),
  ("", [$V = "prefix"$ #emph[fails]. #rel[at $n = 8$,
    $"detab"[a,b,c,d,e,"TB"] = [a,b,c,d,e,"BL","BL","BL"]$, and the prefix
    $[a,b,c,d,e,"BL","BL"]$ is longer than $[a,b,c,d,e,"TB"]$.] Allow only prefixes that do not
    cross a tab stop: $V = "prefix" inter ("fill" "fill"^degree)$.]),
)

#deriv(
  $"detab" V$,
  ("=", [$"detab"$ is a catamorphism]),
    $["nil","snoc"]^degree F(1,"detab") ["nil","expand"] V$,
  ("=", [coproducts, and $"nil" V = "nil"$]),
    $["nil","snoc"]^degree F(1,"detab") ["nil", "expand" V]$,
  ("⊂", [claim: $"expand" V subset "expand" union (pi V)$]),
    $["nil","snoc"]^degree F(1,"detab") ["nil", "expand" union (pi V)]$,
  ("=", [distribute $union$; catamorphisms; $F$]),
    $"detab" union ("snoc"^degree ("detab" times 1) pi thin V)$,
  ("=", [naturality of $pi$, and $"init" = "snoc"^degree pi$]),
    $"detab" union ("init" thin "detab" thin V)$,
)

#dt(
  ("", [So $X = "detab" V$ solves $X subset "detab" union ("init" X)$. $"init"$ is inductive, so the
    greatest solution of the inequation is the unique solution of the equation, namely
    $X = "prefix" thin "detab"$; and $"prefix" subset R$.]),
  ("Ex 10.4", [The claim rests on $"nil" V = "nil"$, $"fill" V = "fill"$ and
    $"snoc" V subset "snoc" union (pi V)$ — the last is the one $V = "prefix"$ breaks.]),
  ("", [The greedy theorem now applies, and Proposition 10.1 peels the base case:
    $ X = Lambda(["nil","expand"]^degree)(min Q)(1 + (X times 1))["nil","snoc"], $
    $ Q = 1 + (V times U), $
    $ X = ("null" -> "nil", thin Lambda("expand"^degree)(min(V times U))(X times 1)"snoc"). $]),
  ("", [$Lambda("expand"^degree)(x cc [a]) = {(y, "TB") | "fill" y = x cc [a]} union {(x,a)}$, and
    the first set is non-empty exactly when $a = "BL"$ and $"col"(x cc [a]) mod n = 0$. Its
    $V$-minimum is $("unfill" x, "TB")$, where $"unfill" x$ is the shortest prefix with
    $"fill"("unfill" x) = "fill" x$:
    $ "unfill" [] = [], $
    $ "unfill"(x cc [a]) = cases(
        "unfill" x & a = "BL" and not "stop",
        x cc [a] & "else,") $
    writing $"stop"$ for the test that the new column is a tab stop,
    $"col"(x cc [a]) mod n = 0$, equivalently $(c+1) mod n = 0$ for $c$ the column count.]),
  ("(10.1) ✓", [$"entab" x = "entab"("unfill" x) cc "blanks"("tbc" x)$, with $"tbc"$ the count of
    trailing blanks. This is what turns $"entab"$ into a snoc-list catamorphism:
    $ "tbc" [] = 0, $
    $ "tbc"(x cc [a]) = cases(
        0 & a = "BL" and "stop",
        "tbc" x + 1 & "else,") $]),
  ("", [$chevron.l "tbc","col" chevron.r$ is a catamorphism, and so is the triple
    $"triple" = chevron.l "unfill" thin "entab", chevron.l "tbc","col" chevron.r chevron.r =
    ⦇"base","op"⦈$ from $([],(0,0))$ with
    $ "op"((x,(t,c)),a) = cases(
        (x, (t+1, c+1)) & a = "BL" and not "stop",
        (x cc ["TB"], (0, c+1)) & a = "BL" and "stop",
        (x cc "blanks" t cc ["NL"], (0,0)) & a = "NL",
        (x cc "blanks" t cc [a], (0, c+1)) & "else,") $
    $ "entab" = "triple" thin "assocl" thin pi thin (1 times "blanks") "cat", $
    and then $"loop"'$ applies to $"triple"$ exactly as it did to $"detab"$.]),
)

== 10.3 The minimum tardiness problem

#dt(
  ("10.3 ✓", [Given a #emph[bag] of jobs, find a permutation of it — a #emph[schedule] — minimising
    the largest penalty for lateness. Each job $j$ has a completion time $"ct" j$, a due time
    $"dt" j$ and a weight $"wt" j$, all positive, and
    $ "penalty"(x,j) = ("sum"("list" "ct" x) + "ct" j - "dt" j) times "wt" j. $
    Bonuses do not count: the cost is the largest penalty incurred, never negative.]),
  ("", [$"schedule" subset Lambda("bagify"^degree)(min R)$ with
    $R = "cost" "leq" "cost"^degree$, $"bagify" = ⦇"nil","snag"⦈$ ($"snag"$ drops a job into a
    bag), and
    $ "cost" = Lambda("prefix") thin P(sans("in")^degree ["zero","penalty"]) thin (max "leq"), $
    $ "cost"(x cc [j]) = "bmax"("cost" x, "penalty"(x,j)). $]),
)

#align(center, block(inset: (y: 3pt), grid(columns: 2, column-gutter: 22pt,
  table(columns: 4, align: right, inset: (x: 5pt, y: 1.2pt),
    stroke: (x, y) => (right: if x == 0 { 0.4pt }, bottom: if y == 0 { 0.4pt }),
    [], [1], [2], [3],
    $"ct"$, [5], [10], [15],
    $"dt"$, [10], [20], [20],
    $"wt"$, [1], [3], [3]),
  table(columns: 4, align: right, inset: (x: 5pt, y: 1.2pt),
    stroke: (x, y) => (right: if x == 0 { 0.4pt }, bottom: if y == 0 { 0.4pt }),
    [], [2], [3], [1],
    $"time"$, [10], [25], [30],
    $"dt"$, [20], [20], [10],
    $"penalty"$, [0], [15], [20]),
)))

#dt(
  ("", [#rel[three jobs, and the walk-through of $[2,3,1]$ — one of the two best schedules, cost
    20, the other being $[3,2,1]$.]]),
  ("", [The algorithm will pick the job best placed #emph[last]: a #D("backward greedy") algorithm,
    which is why snoc-lists. Taking the input as a list instead of a bag,
    $"schedule" subset Lambda("perm")(min R)$ with $"perm" = ⦇"nil","add"⦈$, where
    $"add"(x,j) = y cc [j] cc z$ for any split $x = y cc z$.]),
  ("", [Chapter 7's method does not reach this problem. A snoc-list catamorphism solves every
    #emph[prefix] of the input too, and #rel[for $[1,2,3]$ the best schedule of the prefix $[1,2]$
    is $[1,2]$, at cost zero, which extends to neither $[2,3,1]$ nor $[3,2,1]$.] Context has to be
    brought into both conditions:]),
  ("(10.2) ✓", [$F(R inter ("bagify" "bagify"^degree)) sans("in") subset sans("in") R$, with
    $sans("in") = ["nil","snoc"]$ and $F X = 1 + (X times "Job")$.]),
  ("(10.3) ✓", [$(Q^degree inter (beta beta^degree)) F("bagify"^degree) sans("in") subset
    F("bagify"^degree) sans("in") R^degree$, with $beta = ["nil","snag"]$.]),
  ("", [For (10.2), $"penalty"(x,j)$ depends only on the jobs of $x$, not their order, so
    $"cost"(x cc [j]) = "bmax"("cost" x, "penalty"("perm" x, j))$ and Proposition 9.3 applies with
    $ sans("in") "cost" = F chevron.l "cost", "bagify" chevron.r thin k, $
    $ k = ["zero", "assocr" thin (1 times (("bagify"^degree times 1)"penalty")) thin "bmax"]. $]),
  ("(10.4) ✓", [$sans("in") "cost" = chevron.l g, h chevron.r "bmax"$, the original $"cost"$
    resplit,]),
  ("(10.5) ✓", [$g = ["zero", "penalty"]$,]),
  ("(10.6) ✓", [$h = ["zero", pi thin "cost"]$.]),
  ("(10.7) ✓", [$"add" subset pi thin R^degree$ — adding a job can only raise the cost.]),
  ("(10.8) ✓", [$beta thin "bagify"^degree = F("bagify"^degree)["nil","add"]$ —
    $"bagify"^degree$ is a catamorphism on bags.]),
)

#deriv(
  $beta thin "bagify"^degree$,
  ("=", [(10.8)]), $F("bagify"^degree)["nil","add"]$,
  ("⊂", [(10.7)]), $F("bagify"^degree)["nil", pi thin R^degree]$,
  ("⊂", [$R$; and $"nil" subset "zero" "geq" "cost"^degree$]),
    $F("bagify"^degree)["zero", pi thin "cost"] "geq" thin "cost"^degree$,
  ("=", [(10.6)]), $F("bagify"^degree) h thin "geq" thin "cost"^degree$,
)

#deriv(
  $(Q^degree inter (beta beta^degree)) F("bagify"^degree) sans("in")$,
  ("⊂", [composition is monotonic]),
    $(Q^degree F("bagify"^degree) sans("in")) inter (beta beta^degree F("bagify"^degree) sans("in"))$,
  ("=", [$"bagify" = ⦇beta⦈$]),
    $(Q^degree F("bagify"^degree) sans("in")) inter (beta thin "bagify"^degree)$,
  ("⊂", [the chain above]),
    $(Q^degree F("bagify"^degree) sans("in")) inter (F("bagify"^degree) h thin "geq" thin "cost"^degree)$,
  ("⊂", [modular law]),
    $F("bagify"^degree)((F("bagify") Q^degree F("bagify"^degree)) inter
      (h thin "geq" thin "cost"^degree sans("in")^degree)) sans("in")$,
  ("=", [choose $Q$ with $F("bagify") Q^degree F("bagify"^degree) = g thin "geq" thin g^degree$]),
    $F("bagify"^degree)((g thin "geq" thin g^degree) inter
      (h thin "geq" thin "cost"^degree sans("in")^degree)) sans("in")$,
  ("=", [products]),
    $F("bagify"^degree) chevron.l g thin "geq", h thin "geq" chevron.r
      chevron.l g, sans("in") "cost" chevron.r^degree sans("in")$,
)

#dt(
  ("", [$Q = f thin "leq" thin f^degree$ with $f = ["zero", ("bagify"^degree times 1)"penalty"]$
    meets that specification: a $Q$-minimum is a job of least penalty. What is left, after shunting
    $"cost"$ across, is:]),
)

#deriv(
  $chevron.l g thin "geq", h thin "geq" chevron.r
    chevron.l g, sans("in") "cost" chevron.r^degree sans("in") "cost"$,
  ("⊂", [(10.4), and $chevron.l g, sans("in")"cost" chevron.r$ simple]),
    $chevron.l g thin "geq", h thin "geq" chevron.r "bmax"$,
  ("⊂", [$"bmax"$ monotonic]), $chevron.l g, h chevron.r "bmax" "geq"$,
  ("=", [(10.4)]), $sans("in") "cost" "geq"$,
)

#dt(
  ("", [The greedy theorem applies, and Proposition 10.1 gives the program:
    $ X = Lambda(["nil","snag"]^degree)(min Q)(1 + (X times 1))["nil","snoc"], $
    $ "schedule" = ("null" -> "nil", thin "pick" thin ("schedule" times 1) "snoc"), $
    where $"pick"$ refines $Lambda("snag"^degree)(min Q')$ with
    $Q' = f' thin "leq" thin f'^degree$, $f' = ("bagify"^degree times 1)"penalty"$. (The book
    prints both $f$ and $f'$ as $f$.) Bags are lists paired with $"sum"("list" "ct" x)$;
    $"pick"$ takes the first job of least penalty, and the program is quadratic.]),
  ("Ex 10.7", [$"add"$ is itself a least fixed point:
    $"add" = (mu X : "snoc" union (("snoc"^degree times 1)"exch"(X times 1)"snoc"))$, with
    $"exch" : (A times B) times C -> (A times C) times B$. Fixed-point induction plus
    $("add" times 1)"penalty" subset (pi times 1) "penalty" thin "geq"$ then proves (10.7).]),
  ("Ex 10.8 ✓", [$"perm" = "bagify" "bagify"^degree = ⦇"nil","add"⦈$ proves (10.8).]),
)

== 10.4 The TeX problem – part two

#dt(
  ("10.4 ✓", [Convert between decimal fractions and integer multiples of $2^(-16)$, in integer
    arithmetic only. $"extern" subset Lambda("intern"^degree)(min R)$ with
    $R = "length" "leq" "length"^degree$ and
    $ "intern" = "val" thin "round", $
    $ "round" r = floor.l 2^16 r + 1 slash 2 floor.r, $
    $ "val" = ⦇"zero", "shift"⦈, $
    $ "shift"(d,r) = (d+r) slash 10. $]),
  ("", [$"round"^degree$ is not a map, so it cannot leave the $Lambda$. But
    $n = floor.l 2^16 r + 1 slash 2 floor.r <==> 2n-1 <= 2^17 r < 2n+1$, which factors it through
    a map:
    $ "round"^degree = "interval" thin "inrange", $
    $ "interval" n = ((2n-1) slash 2^17, (2n+1) slash 2^17), $
    $ (a,b) "inrange" r <==> a <= r < b, $
    $ "extern" subset "interval" thin Lambda("inrange" thin "val"^degree)(min R). $]),
  ("", [Fusion makes $"val" thin "inrange"^degree$ a catamorphism $⦇"arb","step"⦈$: the conditions
    are $"zero" thin "inrange"^degree = "arb"$ and
    $"shift" thin "inrange"^degree = (1 times "inrange"^degree)"step"$, and the second unfolds
    pointwise to $"step"(d,(a',b')) = ((d+a') slash 10, (d+b') slash 10)$.]),
  ("(10.9) ✓", [Every interval reached satisfies $0 < b < 1$ and $a < b$ — true of
    $"interval" n$ for $0 <= n < 2^16$, preserved by $"step"$, and imposable on $"arb"$. So
    $["arb","step"] : 1 + ("Digit" times "Interval") -> "Interval"$, and the derivation lives
    inside that type.]),
  ("", [$sans("in") = ["nil","cons"]$ is monotonic under $R$, leaving the greedy condition: a $Q$
    over $F "Interval"$, $F A = 1 + ("Digit" times A)$, with
    $sans("in")^degree (F h) Q subset R thin sans("in")^degree (F h)$ for
    $h = ⦇"arb","step"⦈$.]),
  ("", [$Q$ need only choose between two things, because (10.9) makes $"step"^degree$ a #emph[map]:
    $ Lambda("arb"^degree)(a,b) = (a <= 0 -> {*}, {}), $
    $ Lambda("step"^degree)(a,b) \
      = {(d, (10a-d, 10b-d)) | 0 < 10b-d < 1}, $
    and $0 < 10b-d_1 < 1$ with $0 < 10b-d_2 < 1$ forces $d_1 = d_2$, so
    $"step"^degree(a,b) = (d, (10a-d,10b-d))$ at $d = floor.l 10b floor.r$. Hence
    $Lambda(["arb","step"]^degree)(a,b)$ is $\u{7B} iota thin *, thin iota'(d, dots.c) \u{7D}$ when
    $a <= 0$ and $\u{7B} iota'(d, dots.c) \u{7D}$ otherwise, and
    $ Q = (iota'^degree thin ! thin iota) union 1, $
    $ ! : "Digit" times "Interval" -> 1, $
    which prefers the terminal inhabitant — stop — whenever stopping is possible.]),
  ("", [The greedy proof is nine shuntings around one inequation. Unfold $Q$; drop the $1$ disjunct
    ($R$ reflexive); use the universal property of $!$ with $iota' sans("in") = "cons"$ and
    $iota thin sans("in") = "nil"$ to reduce everything to $! thin "nil" subset "cons" R$, which
    is $! thin "nil" thin "length" subset "cons" "length" "leq"$: the empty decimal is no longer
    than any other.]),
  ("", [So compute the least solution of
    $X = Lambda(["arb","step"]^degree)(min Q)(F X) sans("in")$, which simplifies to
    $"extern" = "interval" f$ with
    $ f(a,b) = cases([] & a <= 0, [d] cc f(10a-d, 10b-d) & "else,") $
    $ quad d = floor.l 10 b floor.r. $]),
  ("", [Integers last: every interval reached is $(p slash w, q slash w)$ for $w = 2^17$, since
    $"interval" n = ((2n-1) slash w, (2n+1) slash w)$ and
    $10a - d = (10p - w d) slash w$. Representing it by $(p,q)$:
    $"extern" n = f(2n-1, 2n+1)$ with
    $ f(p,q) = cases([] & p <= 0, [d] cc f(10p - w d, thin 10q - w d) & "else,") $
    $ quad d = (10q) "div" w. $]),
  ("Ex 10.14", [The only property of $w = 2^17$ used is that $10 q slash w$ is never an integer for
    $0 < q < w$.]),
  ("Ex 10.15", [Knuth asked for the shortest #emph[and] closest decimal to $n slash 2^16$. This
    algorithm delivers only the shortest; which one it picks, and how to get the closest, the book
    leaves open.]),
)
