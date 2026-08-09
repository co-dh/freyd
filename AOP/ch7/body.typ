// Bird & de Moor, "Algebra of Programming", chapter 7 "Optimisation Problems" (book pp. 165-190),
// mirrored item by item into Freyd's conventions: composition by juxtaposition in DIAGRAM order.
//
// A row tagged ✓ has its mirrored statement machine-checked in this repo, under AOP/A7_*.lean.
//
// AUDIT — every numbered item of chapter 7, kept or dropped.
//   §7.1  (7.1)-(7.12) all kept, with the universal properties and `minlist`.
//         Ex 7.1, 7.2, 7.4-7.16, 7.19, 7.20, 7.22-7.32 kept.
//         7.3, 7.17, 7.18 DROPPED (technical division lemmas whose mirrored statement is longer
//         than its use; 7.3 serves only 7.4, 7.18 only the hard half of (7.9), 7.17 defines a
//         `sup` the book never uses again).  7.21 DROPPED (an open question).
//   §7.2  the definition of monotonic, of distributes, Theorem 7.1 and Theorem 7.2 (greedy) kept.
//         Ex 7.33, 7.34, 7.37, 7.38 kept.  7.35, 7.36 DROPPED (ask for a definition to be
//         invented).  7.39-7.42 kept as one row each — they are the standard list functions
//         falling out of the greedy theorem.
//   §7.3-7.5  three case studies.  Their SPECIFICATIONS, the monotonicity condition each turns
//         on, and the spine of each derivation are kept; the subclaim proofs and the Gofer
//         programs are dropped — they are problem-specific and run for pages.  Ex 7.43-7.47,
//         7.48-7.56 DROPPED for the same reason (they supply those missing proofs); Ex 7.57 is
//         kept, since it states the refined order the section's moral is about.
//   Nothing is dropped for being false in Rel.
#import "/AOP/bdm.typ": *

= 7 Optimisation Problems

== 7.1 Minimum and maximum

#dt(
  ("7.1", [$min R eq.delta eps inter (eps^degree backslash R) : [alpha] -> alpha$ — $a$ is a
    minimum of $x$ under $R$ when $a$ is #emph[in] $x$ and is a lower bound of $x$.  $R$ need not
    be a preorder for the definition to make sense, only for it to be useful.]),
  ("", [#D("universal property") $X subset min R <==> X subset eps and eps^degree X subset R$.]),
  ("", [$max R = min R^degree$.]),
  ("", [Three consequences of $f (R slash S) = (f^degree S) slash R$, all about dividing by
    $eps$:]),
  ("(7.1) ✓", [$tau (eps^degree backslash R) = R$.]),
  ("(7.2)", [$Lambda(S)(eps^degree backslash R) = S^degree backslash R$.]),
  ("(7.3) ✓", [$union.big (eps^degree backslash R) = eps^degree backslash (eps^degree backslash R)$.]),
  ("(7.4) ✓", [$tau (min R) = 1 inter R$ — so $R$ is reflexive exactly when the minimum of a
    singleton is its inhabitant.]),
  ("(7.5) ✓", [$Lambda(S)(min R) = S inter (S^degree backslash R)$, whose universal property
    $ X subset Lambda(S)(min R) <==> X subset S and S^degree X subset R $
    is the workhorse of the chapter; calculations cite it as
    #emph[universal property of $min$].]),
  ("(7.6) ✓", [#D("context") $Lambda(S)(min R) = Lambda(S)(min(R inter S^degree S))$ — for the
    purpose of minimising over the sets $Lambda S$ returns, $R$ only has to be constrained on
    values related to one and the same element by $S$.]),
)

#sub[Fusion with the power functor]

#dt(
  ("(7.7)", [$(E S)(min R) = (eps S) inter ((eps S)^degree backslash R)$, from (7.5) and
    $E S = Lambda(eps S)$.]),
  ("(7.8)", [Shunting a map through a minimum:
    $(P f)(min R) = (min(f R f^degree)) f$.]),
  ("(7.9)", [$R$ reflexive: $(P S)(min R) = (eps S) inter (eps^degree backslash (S R))$.  One
    direction needs tabulations.]),
  ("(7.10) ✓", [#D("fusion with the power functor") $(P S)(min R) subset (eps S) inter
    (eps^degree backslash (S R))$, always — this half is all that is used later, and it follows
    in two lines from the naturality of $eps$.]),
)

#sub[Distribution over union]

#dt(
  ("(7.11) ✓", [$R$ a preorder: $(P(min R))(min R) subset union.big (min R)$ — take a minimum in
    each set and then a minimum of those.  Only an inclusion, because a set in the collection may
    be empty.]),
  ("(7.12)", [$(P(min R))(min R) = (P("dom"(min R))) union.big (min R)$, using
    $min R = ("dom"(min R))(min R)$.]),
)

#sub[Implementing min]

#dt(
  ("7.1", [$min R$ refines to a map only on non-empty finite sets, and only for $R$ a connected
    preorder.  With $"setify" : "list"^+ alpha -> [alpha]$ the specification is
    $"minlist" R subset "setify"(min R)$, and]),
  ("", [$"minlist" R = ⦇1, "bmin" R⦈$ with $"bmin" R (a,b) = (a R b -> a, thin b)$ — the
    #emph[leftmost] minimum, in the case of ties.]),
)

#sub[Exercises]

#dt(
  ("Ex 7.1 ✓", [$"subset"^degree (eps^degree backslash R) = eps^degree backslash R$, where
    $"subset" = eps slash eps$.]),
  ("Ex 7.2 ✓", [$(E R)"subset" = (eps R) slash eps$.]),
  ("Ex 7.4", [$(P S)(eps^degree backslash R) = eps^degree backslash (S R)$.]),
  ("Ex 7.5 ✓", [$R$ a preorder: $(eps^degree backslash R) R = eps^degree backslash R$.]),
  ("Ex 7.6 ✓", [$min(R inter S) = (min R) inter (min S)$.]),
  ("Ex 7.7 ✓", [$eps^degree eps = Pi$ — every element is in some set; hence
    $min R = eps <==> R = Pi$.]),
  ("Ex 7.8", [$R, S$ reflexive: $R inter S^degree = (min S)^degree (min R)$.]),
  ("Ex 7.9", [$R$ reflexive: $R = eps^degree (min R)$.]),
  ("Ex 7.10 ✓", [$R, S$ reflexive: $min R subset min S <==> R subset S$.]),
  ("Ex 7.11 ✓", [$min R$ is simple $<==>$ $R$ is anti-symmetric.]),
  ("Ex 7.12", [$R$ a preorder: $min R = eps inter ((min R) R)$.]),
  ("Ex 7.13", [$R$ a preorder and $S$ a map: $R inter (S S^degree)$ is a preorder.]),
  ("Ex 7.14 ✓", [$R$ a preorder: $Lambda(R)(max R) = R inter R^degree$.]),
  ("Ex 7.15", [$chevron.l S(min R), T(min R) chevron.r subset
    Lambda chevron.l S,T chevron.r (min(R times R))$.]),
  ("Ex 7.16", [$R$ reflexive, $S$ a preorder:
    $Lambda(min S)(min R) = min(S semi R)$, with $S semi R = S inter (S^degree => R)$.]),
  ("Ex 7.19 ✓", [#D("minimal elements") $"mnl" R eq.delta min(R^degree => R)$.  $(R^degree => R)$
    is reflexive for every $R$, but need not be a preorder even when $R$ is.]),
  ("Ex 7.20 ✓", [$min R subset "mnl" R$, with equality exactly when $R$ is a connected preorder.]),
  ("Ex 7.22", [$(P f)("mnl" R) = ("mnl"(f R f^degree)) f$ — Ex 7.8 for $"mnl"$.]),
  ("Ex 7.23", [$"mnl" R = eps <==> R$ symmetric.]),
  ("Ex 7.25", [$"class" Q = chevron.l 1, eps Lambda(Q) chevron.r "cap"$ picks an equivalence class
    of $Q$; for $R$ a preorder,
    $"mnl"(R semi S) = Lambda("mnl" R) thin "class"(R inter R^degree) thin "mnl" S$.]),
  ("Ex 7.26", [$R$ #D("well bounded") $eq.delta "dom" eps = "dom"(min R)$ — every non-empty set
    has a minimum.  A well-bounded preorder is necessarily connected, and $R$ is well bounded
    $<==>$ its strict part $R inter not R^degree$ is well-founded.]),
  ("Ex 7.27", [$R$ well bounded $==> f R f^degree$ well bounded, for any map $f$.]),
  ("Ex 7.28", [$R$ well bounded $<==> eps subset (min R) R^degree$.]),
  ("Ex 7.29", [$R$ a well-bounded preorder: $union.big (min R) = (E(min R))(min R)$ — (7.11)
    strengthened to an equality, which is what makes $"setify"(min R)$ a catamorphism.]),
  ("Ex 7.30", [$R$ #D("well supported") $eq.delta "dom" eps = "dom"("mnl" R)$ — weaker than well
    bounded.]),
  ("Ex 7.31", [$R$ a well-supported preorder: $eps subset ("mnl" R) R^degree$.]),
  ("Ex 7.32", [$R$ a well-supported preorder:
    $union.big ("mnl" R) = (E("mnl" R))("mnl" R)$.]),
)

== 7.2 Monotonic algebras

#dt(
  ("7.2 ✓", [An $F$-algebra $S : F alpha -> alpha$ is #D("monotonic on") $R : alpha -> alpha$ if
    $ (F R) S subset S R. $
    Addition is monotonic on $<=$: $("leq" times "leq")"plus" subset "plus" "leq"$, i.e.
    $c = a + b and a <= a' and b <= b' ==> c <= a' + b'$.]),
  ("", [For a map: $f$ monotonic on $R$ $<==> f^degree (F R) f subset R <==> F R subset
    f R f^degree$; by shunting, $f$ is monotonic on $R$ $<==>$ on $R^degree$.  Neither
    equivalence survives for a general $S$.]),
  ("", [$f$ #D("distributes over") $R$ if
    $F(min R) f subset Lambda((F eps) f)(min R)$ — pointwise, for $+$ over $<=$,
    $min x + min y = min{a + b | a ∈ x and b ∈ y}$ on non-empty $x, y$.]),
  ("T 7.1 ✓", [#Th[A map $f$ is monotonic over $R$ $<==>$ it distributes over $R$.]]),
)

// dvdtyp's theorem box sets `breakable` on its own block, so style.typ's `set block` inside the
// figure loses; an unbreakable wrapper is what actually keeps the box in one column.
#block(breakable: false)[
#theorem("Theorem 7.2 — the greedy theorem  ✓", numbering: none)[
  $S$ monotonic on the preorder $R^degree$:
  $ ⦇Lambda(S)(min R)⦈ thin subset thin Lambda(⦇S⦈)(min R). $
  Take the locally best step at every stage and the result is globally optimal.  The proof is the
  universal property of $min$, then the hylomorphism theorem: the greedy fold is below every
  prefixed point of the associated recursion, and transitivity of $R$ discharges it.  For $max$
  the condition is monotonicity on $R$, not $R^degree$; and context can always be brought in, so
  monotonicity on $R^degree inter (⦇S⦈^degree ⦇S⦈)$ suffices.
]
]

#dt(
  ("Ex 7.33 ✓", [$a + b <= a + b' ==> b <= b'$, point-free.]),
  ("Ex 7.34 ✓", [$sans("in")$ monotonic on $R$ $==>$ $R$ is reflexive.]),
  ("Ex 7.37 ✓", [A variant: $f$ monotonic on $R$ and $f subset Lambda(S)(min R)$ $==>$
    $⦇f⦈ subset Lambda(⦇S⦈)(min R)$.]),
  ("Ex 7.38 ✓", [$S$ monotonic on $R^degree$ $==>$
    $(min(F R)) Lambda(S)(min R) subset (E S)(min R)$ — optimal substeps.]),
  ("Ex 7.39", [$"takewhile" p = Lambda(("list" p)("prefix"))(max R)$ with
    $R = "length" "leq" "length"^degree$; with
    $"prefix" = ⦇"nil", "cons" union "nil"⦈$ the greedy theorem gives the standard program.]),
  ("Ex 7.40", [#D("maximum segment sum") $"mss" = Lambda("segment" thin "sum")(max)$, and with
    $"segment" = "suffix" thin "prefix"$,
    $"mss" = Lambda "suffix" thin P(Lambda("prefix" thin "sum")(max))(max)$; the greedy theorem
    gives $⦇"zero", "oplus"⦈ subset Lambda("prefix" thin "sum")(max)$ with
    $"oplus" = Lambda("zero" union "plus")(max)$, and a linear-time program follows.]),
  ("Ex 7.41", [$"filter" p = Lambda(("list" p)("subseq"))(max R)$; with
    $"subseq" = ⦇"nil", "cons" union pi'⦈$ the greedy theorem gives the standard program.]),
  ("Ex 7.42", [$L$ the lexical order: $(1 times L)"cons" subset "cons" L$, hence
    $⦇"nil", Lambda("cons" union pi')(max L)⦈ subset Lambda("subseq")(max L)$; the greedy step is
    $("ok" -> "cons", pi')$ with $"ok"(a,x)$ iff $x = []$ or $a >= "head" x$.]),
)

== 7.3 Planning a company party

#dt(
  ("7.3 ✓", [A company is a $"tree" alpha ::= "node"(alpha, "list"("tree" alpha))$; each employee
    has a #emph[conviviality] $"rating"$, and no employee may attend with their immediate
    supervisor.  Maximise the total rating of the guest list.  Base functor
    $F(A,B) = A times "list" B$.]),
  ("", [$Lambda "party"(max R)$ with
    $R = ("list" "rating" thin "sum") "leq" ("list" "rating" thin "sum")^degree$ and
    $"party" = ⦇chevron.l "include", "exclude" chevron.r⦈ thin "choose"$,
    $"choose" = pi union pi'$ — one catamorphism producing the two parties, one with the root and
    one without.]),
  ("", [$"include" = (1 times ("list" pi' thin "concat"))"cons"$ #h(0.4em) (a map: take the root,
    so the roots of the immediate subtrees are excluded), #h(0.4em)
    $"exclude" = (1 times ("list" "choose" thin "concat")) pi'$ #h(0.4em) (not a map: each
    immediate subtree is free to include or exclude its root).]),
)

#deriv(
  $Lambda "party" (max R)$,
  ("=", [definition of $"party"$]),
  $Lambda(⦇chevron.l "include","exclude" chevron.r⦈ "choose")(max R)$,
  ("=", [$Lambda(X Y) = Lambda(X)(E Y)$]),
  $Lambda ⦇chevron.l "include","exclude" chevron.r⦈ (E "choose")(max R)$,
  ("⊇", [Ex 7.38, since $"choose"$ is monotonic on $R$]),
  $Lambda ⦇chevron.l "include","exclude" chevron.r⦈ (max (R times R)) Lambda "choose" (max R)$,
  ("⊇", [greedy, since $chevron.l "include","exclude" chevron.r$ is monotonic on $R times R$]),
  $⦇Lambda chevron.l "include","exclude" chevron.r (max(R times R))⦈ thin Lambda "choose" (max R)$,
)

#dt(
  ("7.3 ✓", [The two conditions are $(R times R)"choose" subset "choose" R$ and
    $(1 times "list"(R times R)) chevron.l "include","exclude" chevron.r subset
    chevron.l "include","exclude" chevron.r (R times R)$, the second reducing by Ex 7.15 to
    $Lambda "include"(max R)$ and $Lambda "exclude"(max R)$ separately.]),
  ("", [$"include"$ is already a map, and $"exclude"$ refines to
    $pi'("list"(Lambda "choose"(max R)))"concat"$.  The result: a linear-time greedy sweep for a
    problem posed as an exercise in dynamic programming.]),
)

== 7.4 Shortest paths on a cylinder

#dt(
  ("7.4 ✓", [An $n times m$ array of positive integers rolled into a cylinder, the top and bottom
    rows adjacent.  A path enters at the left, and from a square may step to one of the three
    adjacent squares of the next column.  Find a path of least total cost, in $O(n m)$.]),
  ("", [$N$ is the type functor of $n$-tuples, $L = "list"^+$ with base functor
    $F(A,X) = A + (A times X)$.  The problem is $Lambda "paths"(min R)$ with
    $R = "sum" "leq" "sum"^degree$ and $"paths" : "L N Nat" -> [alpha]$.]),
  ("", [$"paths"$ is not the transpose of a catamorphism, so it is built from one:
    $"paths" = ⦇"generate"⦈ thin "setify" thin union.big$ with
    $"generate" : F("N" alpha, "N P L" alpha) -> "N P L" alpha$, a #emph[lax natural
    transformation], assembled by type from
    $"generate" = F(1, "moves" thin "trans" thin "N" union.big) thin "zip" thin "cp" thin
    "N"(P sans("in"))$.]),
  ("", [$"moves" x = {"up" x, x, "down" x}$ rotates columns, $"trans"$ transposes a set of
    tuples, $"zip"$ commutes $N$ with $F$, $"cp" = Lambda(F(1, eps))$.]),
  ("(7.13) ✓", [The crux is Theorem 7.1, not the greedy theorem: $sans("in")$ is a monotonic map,
    hence distributes, so
    $ F(1, min R) sans("in") subset "cp" thin (P sans("in")) thin (min R). $]),
)

#deriv(
  $Lambda "paths" (min R)$,
  ("=", [definition of $"paths"$]),
  $Lambda ⦇"generate"⦈ thin "setify" thin union.big thin (min R)$,
  ("⊇", [distribution over union (7.11), $R$ a preorder]),
  $Lambda ⦇"generate"⦈ thin "setify" thin (P(min R))(min R)$,
  ("⊇", [naturality of $"setify"$]),
  $Lambda ⦇"generate"⦈ thin ("N"(min R)) thin "setify" thin (min R)$,
  ("⊇", [fusion, for the $Q$ below]),
  $⦇Q⦈ thin "setify" thin (min R)$,
)

#dt(
  ("7.4 ✓", [The fusion condition is
    $"generate" thin "N"(min R) supset F(1, "N"(min R)) Q$, and unfolding it through (7.13) and
    the naturalities of $"zip"$, $"trans"$ and $"moves"$ gives
    $Q = "moves" thin "trans" thin ("N P"(min R))("N"(min R)) thin F(1,dot) thin "zip" thin
    "N" sans("in")$, which as a coproduct is
    $Q = ["N" "wrap", thin (1 times ("moves" thin "trans" thin "N"(min R)))"zip"' thin
    "N" "cons"]$.]),
  ("", [Sets and $n$-tuples both become lists, $min R$ becomes $"minlist" R$, and $"zip"$ the
    standard function — a single left-to-right sweep, one column at a time.]),
)

== 7.5 The security van problem

#dt(
  ("7.5 ✓", [A bank's cash must stay between $0$ and $N$; a security van tops it up or takes a
    surplus.  Given a sequence of transactions, cut it into as few #emph[secure] segments as
    possible.  The moral of the section: when the monotonicity condition fails, refine the
    #emph[ordering] instead of abandoning the greedy algorithm.]),
  ("", [$"ceiling" = Lambda("prefix" thin "sum")(max "leq")$ and
    $"floor" = Lambda("prefix" thin "sum")(min "leq")$; $x$ is secure iff
    $"bmax"("ceiling" x, thin "ceiling" x - "floor" x) <= N$.  $"secure"$ is the corresponding
    coreflexive.]),
  ("", [The problem is $Lambda("partition" thin "list" "secure")(min R)$ with
    $R = "length" "leq" "length"^degree$; fusing $"list" "secure"$ into
    $"partition" = ⦇"nil", "new" union "glue"⦈$ gives
    $ "partition" thin "list" "secure" = ⦇"nil", "new" union "old"⦈, $
    $ "old" = (1 times "cons"^degree)"assocl"(("cons" thin "secure") times 1)"cons". $]),
  ("", [Greedy needs $["nil", "new" union "old"]$ monotonic on $R^degree$, i.e.]),
  ("(7.14)", [$(1 times R^degree)"new" subset ("new" union "old") R^degree$ — true.]),
  ("(7.15)", [$(1 times R^degree)"old" subset ("new" union "old") R^degree$ — *false*: two
    partitions of the same sequence may have equal length without $"secure"([a] cc x)$ implying
    $"secure"([a] cc y)$.]),
  ("", [$"secure"$ is #emph[prefix-closed] — $"secure" thin "prefix" subset "prefix" thin
    "secure"$ — so refine $R$ to $R semi H$, where
    $H = ("head" thin "prefix" thin "head"^degree) union ("nil"^degree "nil")$ and
    $R semi H = R inter (R^degree => H)$: same length, and the first component a prefix.]),
  ("", [With the refined order, (7.16) $(1 times (R semi H)^degree)"new" subset
    (R semi H)^degree ("new" union "old")$ follows from
    (7.18) $(1 times Pi)"new" subset "new" H^degree$, and (7.17) for $"old"$ from the three
    claims (7.19)–(7.21) about the strict part $abs(R) = R inter not R^degree$.  Hence
    $ ⦇("ok" -> "glue", "new") thin ("wrap" thin "wrap")⦈ subset
      ⦇Lambda(S)(min (R semi H))⦈, $
    with $"ok"$ holding at $(a, italic("xs"))$ when $italic("xs") eq.not []$ and
    $[a] cc "head" italic("xs")$ is secure.]),
  ("", [$"secure"$ turns out to be suffix-closed too, which is what makes the test efficient:
    $"ceiling" = ⦇"zero", "omax" thin "plus"⦈$ and $"floor" = ⦇"zero", "omin" thin "plus"⦈$ (two
    baby applications of the greedy theorem), so
    $"ok" N (a, [x] cc italic("xs")) = ("omax"(a + "ceiling" x) - "omin"(a + "floor" x) <= N)$.]),
  ("Ex 7.57", [The refined order can be given directly:
    $Q = ("nil"^degree thin !) union ("prefix" semi ("tail"^degree Q thin "tail"))$, a preorder
    and a linear order on partitions of one sequence.  $Q subset.not R$, yet
    $Lambda(⦇S⦈)(min Q) subset Lambda(⦇S⦈)(min R)$ whenever $"secure"$ is suffix-closed.]),
)
