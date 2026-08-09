// Bird & de Moor, "Algebra of Programming", chapter 8 "Thinning Algorithms" (book pp. 193-218),
// mirrored item by item into Freyd's conventions: composition by juxtaposition in DIAGRAM order.
//
// AUDIT — every numbered item of chapter 8, kept or dropped.
//   §8.1  (8.1)-(8.4) kept, with the universal property of `thin` and the proof of (8.3).
//         Theorem 8.1 and Corollary 8.1 kept, Theorem 8.1 with its proof — it is the chapter's
//         one theorem and the proof is four steps.  Ex 8.1-8.6, 8.8, 8.9 kept.  Ex 8.7 DROPPED
//         (it asks for (8.4)'s proof, and (8.4) is stated).
//   §8.2  specification, why `Q = R` fails, the thinning preorder, the whole elimination chain
//         and the side condition kept.  Ex 8.11 kept (it is the general law the section
//         instantiates).  Ex 8.10 DROPPED (asks what a variant functor would mean).
//   §8.3  the specification of `thinlist`, `bump`, (8.5)-(8.11), (8.6) with its proof, Lemma 8.1
//         and Theorem 8.2 with their proofs kept — the binary thinning theorem is what the last
//         three sections run on.  Ex 8.12, 8.17, 8.19, 8.21, 8.22 kept.  Ex 8.13-8.16, 8.18,
//         8.20 DROPPED (alternative `thinlist` definitions the book does not develop, missing
//         proofs, and open questions).
//   §8.4-8.6  three case studies.  Specification, the reason greedy fails, the thinning preorder
//         `Q`, the choice of `P` and the final catamorphism kept; the Gofer programs dropped,
//         with one row for what each computes and costs.  Ex 8.25 kept (it is why the tour
//         algorithm is quadratic) and Ex 8.29 (one more problem in one line).  Ex 8.23, 8.24,
//         8.26-8.28, 8.30, 8.31 DROPPED (missing proofs, and variations posed without answers).
//   Figures: both kept.  8.1 is two paragraphs of the same sentence, which is the whole argument
//         that greedy loses; 8.2 is the seven-point tour, redrawn without the book's axes.
//   Nothing is dropped for being false in Rel.
#import "/AOP/bdm.typ": *

= 8 Thinning Algorithms

Between the greedy theorem's single partial solution and Eilenberg–Wright's exhaustive set, keep a
#emph[representative] collection: those partial solutions that might still extend to an optimum.

== 8.1 Thinning

#dt(
  ("(8.1) ✓", [#D("thin") $"thin" Q = (eps slash eps) inter (eps^degree backslash (Q eps^degree)) :
    [alpha] -> [alpha]$ — take a set $y$ to a subset $x$ of it such that every member of $y$ has a
    $Q$-lower bound in $x$. Nothing is lost that a $Q$-minimum could have used. Unlike $min R$,
    $Q$ need not be a connected preorder for $"thin" Q$ to be implementable (§8.3).]),
  ("✓", [#D("universal property")
    $X subset Lambda(S)("thin" Q) <==> X eps subset S and S^degree X subset Q eps^degree$ — as
    usual the workhorse; every proof below is this property applied twice.]),
  ("✓", [$Q subset R ==> "thin" Q subset "thin" R$; and $"thin" Q$ is reflexive, transitive, a
    preorder exactly when $Q$ is. #emph[From here on $Q$ is a preorder.]]),
  ("✓", [#D("thin-introduction") $min R = ("thin" Q)(min R)$ when $Q subset R$ — thinning first
    changes no minimum.]),
  ("(8.2) ✓", [#D("thin-elimination") $"thin" Q ⊃ (min Q) tau$, where $tau$ wraps a value in a
    singleton. So thinning can always be refined to "take the minimum". Two cautions: unless $Q$
    is connected, $(min Q) tau$ has the smaller domain — $"thin" 1$ is entire while
    $(min 1) tau$ is defined only on singletons, so the refinement can be infeasible. At the other
    end $"thin" Q ⊃ 1$, so it can always be refined away entirely.]),
  ("(8.3) ✓", [The usable form: $Lambda(S)("thin" Q) ⊃ Lambda(S)(min R) tau$ provided
    $R inter (S^degree S) subset Q$.]),
)

#deriv(
  $S^degree Lambda(S)(min R) tau subset Q eps^degree$,
  ("≡", [shunt $tau$; $tau eps = 1$]), $S^degree Lambda(S)(min R) subset Q$,
  ("≡", [context, (7.6)]), $S^degree Lambda(S)(min(R inter (S^degree S))) subset Q$,
  ("⇐", [$S^degree Lambda(S) subset eps^degree$]),
    $eps^degree thin min(R inter (S^degree S)) subset Q$,
  ("⇐", [definition of $min$]), $R inter (S^degree S) subset Q$,
)

#dt(
  ("(8.4) ✓", [$union.big ("thin" Q) ⊃ (P("thin" Q)) union.big$ — thinning each set and then
    uniting refines uniting and then thinning.]),
  ("T 8.1 ✓", [#Th[#D("the thinning theorem") $S$ monotonic on $Q^degree$. Then
    $ ⦇Lambda((F eps) S)("thin" Q)⦈ subset Lambda(⦇S⦈)("thin" Q). $]]),
  ("", [Two conditions, by the universal property: $⦇dots.c⦈ eps subset ⦇S⦈$, an exercise in
    fusion, and $⦇S⦈^degree ⦇dots.c⦈ subset Q eps^degree$, which by the hylomorphism theorem
    follows from:]),
)

#deriv(
  $S^degree F(Q eps^degree) Lambda((F eps) S)("thin" Q)$,
  ("⊂", [$S^degree (F Q) subset Q S^degree$, monotonicity converted]),
    $Q S^degree (F eps^degree) Lambda((F eps) S)("thin" Q)$,
  ("⊂", [$X^degree Lambda(X) subset eps^degree$]), $Q eps^degree ("thin" Q)$,
  ("⊂", [$eps^degree ("thin" Q) subset Q eps^degree$]), $Q Q eps^degree$,
  ("=", [$Q$ transitive]), $Q eps^degree$,
)

#dt(
  ("C 8.1 ✓", [$Q subset R$ and $S$ monotonic on $Q^degree$:
    $⦇Lambda((F eps) S)("thin" Q)⦈(min R) subset Lambda(⦇S⦈)(min R)$ — thin-introduction applied
    to Theorem 8.1. Exhaustive search ($Q = 1$) and the greedy algorithm are the two extremes.]),
  ("Ex 8.1 ✓", [$"thin" 1 = 1$.]),
  ("Ex 8.2 ✓", [$"thin" Q$ is a preorder if $Q$ is.]),
  ("Ex 8.3 ✓", [$("thin" Q)(min R) subset min R$ when $Q subset R$ — half of thin-introduction.]),
  ("Ex 8.4 ✓", [$chevron.l "thin" R, "thin" Q chevron.r "cup" subset "thin" R$, from the stronger
    $chevron.l "thin" R, eps slash eps chevron.r "cup" subset "thin" R$, which needs
    $eps times eps subset "cup" chevron.l eps, eps chevron.r$.]),
  ("Ex 8.5 ✓", [$min R = ("thin" R) tau^degree$, whence thin-elimination.]),
  ("Ex 8.6 ✓", [#D("context") $Lambda(S)("thin" Q) = Lambda(S)("thin"(Q inter (S^degree S)))$.]),
  ("Ex 8.8 ✓", [The greedy algorithm is Theorem 8.1 at the other extreme.]),
  ("Ex 8.9 ✓", [$Q$ well-supported (Ex 7.30) $==> Lambda("mnl" Q) subset "thin" Q$ — keeping the
    minimal elements is a legitimate thinning.]),
)

== 8.2 Paths in a layered network

#dt(
  ("8.2 ✓", [A #emph[layered network] is a non-empty sequence of sets of vertices; a #emph[path]
    picks one vertex from each layer, at cost
    $"cost"[a_0, dots.c, a_n] = sum_(0 <= j < n) "wt"(a_j, a_(j+1))$. Find a least-cost path.
    Non-empty cons-lists, paths built right to left, $R = "cost" "leq" "cost"^degree$:
    $ "minpath" subset Lambda("list"^+ eps)(min R) = Lambda(⦇F(eps,1) sans("in")⦈)(min R), $
    with $sans("in") = ["wrap","cons"]$ and $F$ the base bifunctor.]),
  ("", [$"cost"$ is not a catamorphism, but pairs with one:
    $ ⦇"wrapz","consw"⦈ = chevron.l 1, "cost" chevron.r, $
    $ "wrapz" = chevron.l "wrap","zero" chevron.r, $
    $ "consw"(a,(x,n)) = ("cons"(a,x), thin "wt"(a, "head" x) + n). $]),
  ("", [Corollary 8.1 needs $Q subset R$ with
    $F(eps, Q^degree) sans("in") subset F(eps,1) sans("in") Q^degree$. $Q = R$ #emph[fails]: for
    paths $p, q$ with $"cost" p >= "cost" q$ it would demand
    $"wt"(a, "head" p) - "wt"(a, "head" q) >= "cost" q - "cost" p$, and $"wt"(a, "head" q)$ can be
    arbitrarily large. The fix is to compare only paths with the same first vertex:
    $ Q = R inter ("head" "head"^degree), $
    $ "minpath" subset ⦇Lambda(F(eps,eps) sans("in"))("thin" Q)⦈(min R). $]),
  ("", [Operationally: keep one partial solution per starting vertex, a shortest path beginning
    there. That is exactly what the thinning step can be eliminated into.]),
)

#deriv(
  $Lambda(F(eps,eps) sans("in"))("thin" Q)$,
  ("=", [bifunctors]), $Lambda(F(eps,1) thin F(1,eps) sans("in"))("thin" Q)$,
  ("=", [$Lambda$ of a composite]),
    $Lambda(F(eps,1)) thin P(Lambda(F(1,eps) sans("in"))) thin union.big thin ("thin" Q)$,
  ("⊃", [(8.4)]),
    $Lambda(F(eps,1)) thin P(Lambda(F(1,eps) sans("in"))("thin" Q)) thin union.big$,
  ("⊃", [(8.3)]),
    $Lambda(F(eps,1)) thin P(Lambda(F(1,eps) sans("in"))(min R) tau) thin union.big$,
  ("=", [$(P tau) union.big = 1$]),
    $Lambda(F(eps,1)) thin P(Lambda(F(1,eps) sans("in"))(min R))$,
  ("=", [$P = E$ on maps]),
    $Lambda(F(eps,1)) thin P(Lambda(F(1,eps))(P sans("in"))(min R))$,
)

#dt(
  ("", [(8.3) applies because $R inter (S^degree S) subset Q$: it reduces to
    $S^degree S subset "head" "head"^degree$, that is $S thin "head"$ simple, and
    $S thin "head" subset [1, pi]$.]),
  ("", [Nothing above used the datatype. For non-empty cons-lists,
    $Lambda(F(eps,1)) = 1 + "cpl"$ and
    $Lambda(F(1,eps))(P sans("in"))(min R) = ["wrap","step"]$ with
    $"step" = "cpr" thin (P "cons")(min R)$, so finally
    $ "minpath" subset ⦇P "wrap", thin "cpl" thin (P "step")⦈(min R), $
    which represents a path $p$ by $(p, ("head" p, "cost" p))$.]),
  ("Ex 8.11", [The general law behind the whole section: $Q subset R$, $S = S_2 S_1$ monotonic on
    $Q^degree$, $R inter (S_1^degree S_1) subset Q$. Then
    $⦇Lambda((F eps) S_2) thin P(Lambda(S_1)(min R))⦈(min R) subset Lambda(⦇S⦈)(min R)$.]),
)

== 8.3 Implementing thin

#dt(
  ("8.3 ✓", [$"thin" Q$ becomes a program only on finite sets — but, unlike $min R$, the sets may
    be empty and $Q$ need not be connected. On lists:
    $ ("thinlist" Q)"setify" subset "setify"("thin" Q), $
    $ "thinlist" Q subset "subseq", $
    the second saying the relative order survives.]),
  ("(8.5)", [The ideal is linear time and a shortest result; in particular
    $"thinlist" Q thin x = ["minlist" Q thin x]$ when $Q$ is connected and $x$ non-empty.
    $"thinlist" Q = 1$ is legitimate and useless.]),
  ("", [Drop an element when a neighbour bumps it — linear in the number of $Q$-tests, though not
    always shortest:
    $ "thinlist" Q = ⦇"nil", "bump" Q⦈, $
    $ "bump" Q(a,[]) = [a], $
    $ "bump" Q(a, [b] cc x) = cases([a] cc x & a Q b,
        [b] cc x & b Q a, [a] cc [b] cc x & "else.") $]),
)

#sub[Sorting sets]

#dt(
  ("8.3", [$"sort" P = "setify"^degree ("ordered" P)$ for a connected preorder $P$ — not a map even
    for a linear order, since #rel[$"sort" "leq" {1,2,3}$ may give $[1,2,3]$ or $[1,1,2,3]$.]]),
  ("(8.6)", [$("sort" P)("thinlist" Q) subset ("thin" Q)("sort" P)$ — sorting then thinning a list
    refines thinning the set.]),
)

#deriv(
  $("sort" P)("thinlist" Q)$,
  ("=", [$"sort" P$]), $"setify"^degree ("ordered" P)("thinlist" Q)$,
  ("⊂", [$("ordered" P)("thinlist" Q) subset ("thinlist" Q)("ordered" P)$, since
    $("ordered" P)"subseq" subset "ordered" P$ for connected $P$]),
    $"setify"^degree ("thinlist" Q)("ordered" P)$,
  ("⊂", [specification of $"thinlist"$, shunted]),
    $("thin" Q) "setify"^degree ("ordered" P)$,
  ("=", [$"sort" P$]), $("thin" Q)("sort" P)$,
)

#dt(
  ("", [$P$ is not free: it should bring $Q$-comparable elements together. If $Q$ is connected and
    $P = Q$, thinning is just "return the first element".]),
  ("(8.7)", [$("sort" P)("minlist" Q) subset min Q$.]),
  ("(8.8)", [$"sort"(f P f^degree)("list" f) subset (P f)("sort" P)$.]),
  ("(8.9)", [$("sort" P)("filter" p) subset (E p)("sort" P)$, for $p$ a coreflexive.]),
  ("(8.10)", [$("sort" P)^2 ("merge" P) subset "cup"("sort" P)$.]),
  ("(8.11)", [$F("sort" P)("listcp"(F)) subset "cp"(F)("sort"(F P))$, where
    $"cp"(F) = Lambda(F eps)$ is §5.6's cartesian product and $"listcp"(F)$ its list version. Not
    every $F$ admits one: $F$ must distribute over arbitrary joins. A polynomial functor that does
    is called #D("linear"), and for those (8.11) can be met — assumed from here on.]),
  ("L 8.1", [#Th[$f$ monotonic on $P$, $p$ a coreflexive. Then
    $F("sort" P)("listcp"(F))("list" f)("filter" p) subset Lambda((F eps) f thin p)("sort" P)$.]]),
)

#deriv(
  $Lambda((F eps) f thin p)("sort" P)$,
  ("=", [$Lambda$ of a composite; $"cp"(F) = Lambda(F eps)$]),
    $"cp"(F)(E(f thin p))("sort" P)$,
  ("=", [$E$ a functor, and $E = P$ on maps]), $"cp"(F)(P f)(E p)("sort" P)$,
  ("⊃", [(8.9)]), $"cp"(F)(P f)("sort" P)("filter" p)$,
  ("⊃", [(8.8)]), $"cp"(F)("sort"(f P f^degree))("list" f)("filter" p)$,
  ("⊃", [$f$ monotonic on $P$]), $"cp"(F)("sort"(F P))("list" f)("filter" p)$,
  ("⊃", [(8.11)]), $F("sort" P)("listcp"(F))("list" f)("filter" p)$,
)

#sub[Binary thinning]

#dt(
  ("T 8.2", [#Th[#D("the binary thinning theorem") Suppose $S = (f_1 p_1) union (f_2 p_2)$ with
    $p_1, p_2$ coreflexive; $Q$ a preorder, $Q subset R$, with $f_1 p_1$ and $f_2 p_2$ both
    monotonic on $Q^degree$; and $P$ a connected preorder with $f_1, f_2$ monotonic on $P$. Then,
    for $g_i = ("list" f_i)("filter" p_i)$,
    $ ⦇"listcp" chevron.l g_1, g_2 chevron.r ("merge" P)("thinlist" Q)⦈("minlist" R) \
      subset Lambda(⦇S⦈)(min R). $]]),
)

#deriv(
  $Lambda(⦇S⦈)(min R)$,
  ("⊃", [Theorem 8.1, $S$ monotonic on $Q^degree$]),
    $⦇Lambda((F eps) S)("thin" Q)⦈(min R)$,
  ("⊃", [(8.7)]), $⦇Lambda((F eps) S)("thin" Q)⦈("sort" P)("minlist" R)$,
  ("⊃", [fusion, by the chain below]),
    $⦇"listcp" chevron.l g_1,g_2 chevron.r ("merge" P)("thinlist" Q)⦈("minlist" R)$,
)

#deriv(
  $Lambda((F eps) S)("thin" Q)("sort" P)$,
  ("⊃", [(8.6)]), $Lambda((F eps) S)("sort" P)("thinlist" Q)$,
  ("=", [definition of $S$]),
    $chevron.l Lambda((F eps) f_1 p_1), Lambda((F eps) f_2 p_2) chevron.r
      "cup" ("sort" P)("thinlist" Q)$,
  ("⊃", [(8.10)]),
    $chevron.l Lambda((F eps) f_1 p_1)("sort" P), Lambda((F eps) f_2 p_2)("sort" P) chevron.r \
      ("merge" P)("thinlist" Q)$,
  ("⊃", [Lemma 8.1]),
    $F("sort" P)"listcp" chevron.l g_1,g_2 chevron.r ("merge" P)("thinlist" Q)$,
)

#dt(
  ("Ex 8.12", [On snoc-lists $"thinlist" Q = ⦇1, "bump" Q⦈$ — a different function from the
    cons-list one above.]),
  ("Ex 8.17", [$("sort" P)"subseq" subset (eps slash eps)("sort" P)$ for connected $P$.]),
  ("Ex 8.19", [$"listcp"$ of a product and of a coproduct from the parts; $"listcp"$ of the
    identity functor and of a constant functor.]),
  ("Ex 8.21", [(8.11) genuinely needs linearity: there is a polynomial relator that is not linear
    and for which it fails.]),
  ("Ex 8.22", [The mirror-image theorem, for $S = (p_1 f_1) union (p_2 f_2)$.]),
)

== 8.4 The knapsack problem

#dt(
  ("8.4 ✓", [Pack items of given weight and value into a knapsack of capacity $w$, at greatest
    total value. Selections are subsequences:
    $ "subseq" = ⦇["nil","cons"] union ["nil",pi']⦈, $
    $ "value" = ("list" "val")"sum", $
    $ "weight" = ("list" "wt")"sum", $
    $ "knapsack" w subset Lambda("subseq"("within" w))(max R), $
    with $R = "value" "leq" "value"^degree$ — or the same with $min$ and
    $R = "value" "geq" "value"^degree$. Weights are non-negative, so fusion pushes the capacity
    test inside:
    $"within" w thin "subseq" = ⦇(["nil","cons"]("within" w)) union ["nil",pi']⦈$ — written as a
    union of two, not collapsed, because that is the shape binary thinning wants.]),
  ("", [No greedy algorithm: $["nil","cons"]$ and $["nil",pi']$ are monotonic on $R^degree$, but
    $["nil","cons"]("within" w)$ is not — a lighter selection of no greater value may still be the
    one that fits. It #emph[is] monotonic on $Q^degree$ for
    $ Q = R inter ("weight" "leq" "weight"^degree), $
    and so is $["nil",pi']$. The cons-list functor is linear, so with $P = R$ — sorting by
    descending value — the binary thinning theorem applies.]),
  ("", [With $F A = 1 + ("Item" times A)$, $"listcp" = "wrap" + "cpr"$, and $g_1, g_2$ split as
    coproducts, everything simplifies to
    $ "knapsack" w = ⦇"nil", thin "cpr" chevron.l h_1, h_2 chevron.r ("merge" R)("thinlist" Q)⦈ \
      ("minlist" R), $
    $ h_1 = ("list" "cons")("filter"("within" w)), $
    $ h_2 = "list" pi'. $
    Packings come out in descending value, so $"minlist" R$ is just $"head"$.]),
  ("", [Exponential in the worst case, fast in practice, and — unlike the textbook dynamic
    programming solution — it does not need the weights and the capacity to be integers. When they
    are, it is as efficient.]),
)

== 8.5 The paragraph problem

#dt(
  ("8.5 ✓", [Break a sequence of words into lines of width at most $w$, wasting as little as
    possible. $"Line" = "list"^+ "Word"$, $"Para" = "list"^+ "Line"$, cons-lists:
    $ "paragraph" w subset Lambda("partition"("list"^+("fits" w)))(min R), $
    $ R = ("waste" w) "leq" ("waste" w)^degree, $
    $ "partition" = ⦇"wrap" "wrap", thin "new" union "glue"⦈, $
    $ "new"(a, x s) = [[a]] cc x s, $
    $ "glue"(a, x s) = [[a] cc "head" x s] cc "tail" x s. $]),
  ("", [$"glue"$ is a total map on non-empty lists — which the algorithm needs. Width counts one
    unit per interword space, and waste ignores the last line:
    $ "width" = ⦇"length", ("length" times 1)"plus" thin "succ"⦈, $
    $ "waste" w = "init"("list"("white" w))"collect", $
    $ "white" w thin x = w - "width" x, $
    $ "collect" = ("list" "sqr")"sum". $]),
  ("", [Assuming each word fits on a line by itself, fusion gives
    $"paragraph" w subset Lambda(⦇"wrap" "wrap", thin "new" union "glue"("ok" w)⦈)(min R)$, and
    the algebra rewrites as a union of two maps,
    $["wrap" "wrap", "new"] union (["wrap" "wrap","glue"]("ok" w))$ — binary thinning again.]),
)

#align(center, block(inset: (y: 4pt), box(stroke: 0.4pt, inset: 6pt, grid(
  columns: 2, column-gutter: 16pt,
  text(size: 0.9em)[Before proceeding \ with the derivation \ of an algorithm, we \ note that the \
    obvious greedy \ algorithm does not \ solve this \ specification.],
  text(size: 0.9em)[Before proceeding \ with the derivation \ of an algorithm, \ we note that the \
    obvious greedy \ algorithm does \ not solve this \ specification.],
))))

#dt(
  ("", [#emph[Figure 8.1: a greedy and an optimal paragraph.] The greedy algorithm fills each line
    as far as it will go; $"glue"$ is not monotonic on $R^degree$, and two partitions of the same
    input compare only when their first lines agree. So]),
  ("", [$Q = R inter ("head" "head"^degree)$ — and both $"new"$ and $"glue"("ok" w)$ are monotonic
    on $Q^degree$, given that $"cons"$ is monotonic under
    $"collect" "leq" "collect"^degree$, which the squared-white-space $"collect"$ satisfies.]),
  ("", [$P = R$ is out, as the monotonicity fails. $P = "head"^degree L thin "head"$ for a linear
    order $L$ on lines works — $"prefix"$ will do, being linear on lines of one input. But the
    simplest choice suffices: $P = Pi$. Every map is monotonic on $Pi$, and $"merge" Pi = "cat"$,
    which already brings together every partial solution with the same first line.]),
  ("", [With $F A = "Word" + ("Word" times A)$ and $"listcp" = "wrap" + "cpr"$:
    $ "paragraph" w = ⦇"start", thin "cpr" chevron.l h_1,h_2 chevron.r "cat"("thinlist" Q)⦈ \
      ("minlist" R), $
    $ "start" = "wrap" "wrap" "wrap", $
    $ h_1 = "list" "new", $
    $ h_2 = ("list" "glue")("filter"("ok" w)). $
    A partition $[x] cc x s$ is carried as $([x] cc x s, (w - "width" x, "waste" w thin x s))$.]),
)

== 8.6 Bitonic tours

#dt(
  ("8.6 ✓", [A #emph[bitonic] tour starts at the leftmost city, goes strictly left to right to the
    rightmost, and returns strictly right to left. The euclidean travelling salesman problem is
    NP-complete; its bitonic restriction is quadratic. Generalised here: costs $"tc"(a,b)$ need be
    neither euclidean, nor positive, nor symmetric.]),
)

#let pts = ((0,6),(1,0),(2,3),(5,4),(6,1),(7,5),(8,2))
#let dot(p) = node((p.at(0), -p.at(1)), circle(radius: 1.4pt, fill: black, stroke: none), inset: 0pt)
#let seg(p, q) = edge((p.at(0), -p.at(1)), (q.at(0), -q.at(1)), "-", stroke: 0.5pt)
#let plot(es) = diagram(spacing: (3.4mm, 2.6mm), node-inset: 0pt,
  ..pts.map(dot), ..es.map(e => seg(e.at(0), e.at(1))))

#align(center, block(inset: (y: 4pt), grid(columns: 2, column-gutter: 10pt,
  plot(((pts.at(0), pts.at(2)), (pts.at(2), pts.at(1)), (pts.at(1), pts.at(4)),
        (pts.at(4), pts.at(6)), (pts.at(6), pts.at(5)), (pts.at(5), pts.at(3)),
        (pts.at(3), pts.at(0)))),
  plot(((pts.at(0), pts.at(1)), (pts.at(0), pts.at(2)), (pts.at(2), pts.at(3)),
        (pts.at(3), pts.at(5)), (pts.at(5), pts.at(6)), (pts.at(6), pts.at(4)),
        (pts.at(4), pts.at(1)))),
)))

#dt(
  ("", [#emph[Figure 8.2: an optimal and an optimal bitonic tour] of the same seven points. On the
    right the outward journey runs left to right along the upper chain and the return comes back
    along the lower one.]),
  ("", [A tour is a #emph[pair] of lists $(x,y)$, the outward journey and the return, read right to
    left; both are subsequences of the input of length at least two, sharing their first and last
    elements. #rel[$(["New York","Rome"], ["New York","London","Rome"])$ visits London on the way
    back, and is a different tour from the pair the other way round, because costs may depend on
    direction.] Base functor $F A = ("City" times "City") + ("City" times A)$ and
    $ "tour" = ⦇"start", thin "dropl" union "dropr"⦈, $
    $ "start"(a,b) = ([a,b],[a,b]), $
    $ "dropl"(a, ([b] cc x, y)) = ([a] cc x, [a] cc y), $
    $ "dropr"(a, (x, [b] cc y)) = ([a] cc x, [a] cc y), $
    the two ways of not visiting the dropped city twice.
    $"cost"(x,y) = "outcost" x + "incost" y$, and $"mintour"$ refines
    $Lambda("tour")(min R)$ with $R = "cost" "leq" "cost"^degree$.]),
  ("", [Monotonicity on $R^degree$ needs
    $(1 times R^degree)"dropl" subset "dropl" R^degree$ and the same for $"dropr"$. Expanding
    $"cost"("dropl"(a,(x,y)))$ shows these hold only when the two tours agree on their first
    #emph[and] second elements; the first is automatic for tours of one input, so
    $ Q = R inter ("next"^2 ("next"^2)^degree), $
    $ "next"([a] cc [b] cc x) = b. $]),
  ("", [As in §8.5, $P = R$ fails and $P = Pi$ works, $"merge" Pi = "cat"$. Binary thinning, with
    $"listcp" = "wrap" + "cpr"$:
    $ "mintour" = ⦇"start" "wrap", thin "cpr"
      chevron.l "list" "dropl", "list" "dropr" chevron.r \
      "cat"("thinlist" Q)⦈
      ("minlist" R). $]),
  ("Ex 8.25", [Exactly two tours are added per step, so the list of partial solutions grows
    linearly and the algorithm is quadratic: after $[a_0, dots.c, a_n]$ the $"next"$ pairs are
    $(a_n, a_1), dots.c, (a_2,a_1), (a_1,a_2), dots.c, (a_1,a_n)$.]),
  ("Ex 8.29", [Longest upsequence: $Lambda("subseq" "ordered")(max R)$ for
    $R = "length" "leq" "length"^degree$ is another thinning algorithm.]),
)
