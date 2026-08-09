// Bird & de Moor, "Algebra of Programming", chapter 5 "Datatypes in Allegories" (book
// pp. 111-135), mirrored item by item into Freyd's conventions: composition by
// juxtaposition in DIAGRAM order.  The dictionary that does the mirroring is printed on
// the sheet itself, in Conventions.  All proofs are dropped; the book gives them as
// calculation chains and none of them is a statement to look up.
//
// A row tagged ✓ has its mirrored statement machine-checked in this repo, under
// AOP/A5_1..A5_7.lean; the rest are hand-mirrored from the page.
//
// AUDIT — every numbered item of chapter 5, kept or dropped.
//   §5.1  Lemma 5.1 kept.  Theorem 5.1 kept.  Corollary 5.1 kept.
//         Ex 5.1 DROPPED (asks for an example, states nothing).  5.2 kept.
//         5.3 DROPPED (open question).  5.4 kept.  5.5 kept.
//   §5.2  (5.1)-(5.8) all kept.  Ex 5.6, 5.7, 5.8, 5.9, 5.10 kept.
//         5.11 DROPPED (open question: exponentials in Rel).
//   §5.3  (5.9), (5.10), (5.11) kept, with the p.118 coproduct diagram.
//         Ex 5.12 kept.  5.13 DROPPED (proof).  5.14 kept.
//   §5.4  the P R formula and its Rel reading kept; the relator laws kept.
//         Ex 5.15 kept (as the caution it settles).  5.16 kept.
//   §5.5  (5.12) kept, with the p.121 diagram.  Type-relator converse law kept.
//         Ex 5.17, 5.18, 5.19 kept.
//   §5.6  subseq, setify, the cp family, prefix/suffix, partition, perm all kept, both
//         point-free and pointwise.  Ex 5.20-5.29 kept.
//   §5.7  (5.13) kept, with the p.133 square.  Theorem 5.2 kept.  Ex 5.30 kept.
//   Nothing is dropped for being false in Rel: chapter 5 is about Rel throughout.
// The page shapes, the Conventions section and the notation helpers are shared by every B&dM
// chapter sheet and live in AOP/bdm.typ.
#import "/AOP/bdm.typ": *

#conventions

= 5.1 Relators

#dt(
  ("5.1 ✓", [#D("relator") $F : cal(A) -> cal(B)$ between tabular allegories $eq.delta$ a
    #emph[monotonic] functor: $R subset S ==> F R subset F S$.]),
  ("Lem 5.1 ✓", [#Th[$F$ a relator and $f$ a map $==>$ $F f$ is a map and
    $(F f)^degree = F(f^degree)$.]]),
  ("Thm 5.1 ✓", [#Th[A functor is a relator $<==>$ it preserves converse:
    $F(R^degree) = (F R)^degree$.]]),
  ("Cor 5.1 ✓", [#Th[Relators agreeing on maps are equal: $(forall f. thin F f = G f) ==> F = G$.]
    Tabulate: $F R = F(f^degree g) = (F f)^degree (F g)$.]),
  ("", [Hence $F R^degree$ is unambiguous — it names $(F R)^degree$ and $F(R^degree)$ alike.]),
  ("Ex 5.2 ✓", [A relator preserves meets of coreflexives, $F(C inter D) = F C inter F D$.
    The restriction $C, D subset 1$ is needed.]),
  ("Ex 5.5 ✓", [$F("dom" R) = "dom"(F R)$.]),
  ("Ex 5.4", [Not every functor on $sans("Fun")$ extends to a relator: for $F A = nothing$
    if $A = nothing$ and ${0}$ otherwise, the constant maps $"one", "two" : {0} -> {1,2}$
    give $F("two" thin "one"^degree) = 1$, while preservation of converse forces $nothing$.]),
)

= 5.2 Relational products

$(pi, pi')$ tabulates $Pi$, so $chevron.l f,g chevron.r = (f pi^degree) inter (g pi'^degree)$
for maps; (5.1) reads that same formula for arbitrary relations.

#dt(
  ("(5.1) ✓", [$chevron.l R,S chevron.r eq.delta (R pi^degree) inter (S pi'^degree)$.
    #h(0.5em) #rel[$c thin chevron.l R,S chevron.r thin (a,b) <==> c R a and c S b$.]]),
  ("(5.2) ✓", [$R times S eq.delta chevron.l pi R, pi' S chevron.r$.]),
  ("", [$times$ is monotonic in both arguments and $(R times S)^degree = R^degree times S^degree$,
    so it is a relator — but it is #emph[not] a categorical product.]),
  ("(5.3) ✓", [#D("absorption") $chevron.l X,Y chevron.r (R times S) = chevron.l X R, Y S chevron.r$;
    hence $(R times S)(U times V) = (R U) times (S V)$.]),
  ("(5.4) ✓", [$chevron.l X R, Y chevron.r subset chevron.l X, Y chevron.r (R times 1)$ — one of the
    two special cases (5.3) is staged through.]),
  ("(5.5) ✓", [$chevron.l X, Y S chevron.r subset chevron.l X, Y chevron.r (1 times S)$, symmetric to
    (5.4).]),
  ("(5.6) ✓", [$chevron.l R,S chevron.r pi = ("dom" S) R$.]),
  ("(5.7) ✓", [$chevron.l R,S chevron.r pi' = ("dom" R) S$.]),
  ("", [So $chevron.l R, nothing chevron.r pi = nothing$, not $R$: precisely why $(pi, pi')$ is
    no categorical product in an allegory.]),
  ("(5.8) ✓", [#D("cancellation") $chevron.l X,Y chevron.r chevron.l R,S chevron.r^degree
    = (X R^degree) inter (Y S^degree)$.]),
  ("Ex 5.6 ✓", [$(1 times S)(R times 1) supset R times S$, from (5.4) and (5.2) alone.]),
  ("Ex 5.7", [$chevron.l R,S chevron.r^degree chevron.l P,Q chevron.r
    subset (R^degree P) times (S^degree Q)$.]),
  ("Ex 5.8", [$chevron.l X,Y chevron.r (R times S) subset chevron.l X R, Y S chevron.r$ — the easy
    half of (5.3).]),
  ("Ex 5.9 ✓", [$f chevron.l R,S chevron.r = chevron.l f R, f S chevron.r$ for a map $f$; false for
    an arbitrary arrow.]),
  ("Ex 5.10", [$"unzip"(F) eq.delta chevron.l F pi, F pi' chevron.r$, and
    $F(R times S) thin "unzip"(F) = "unzip"(F) thin (F R times F S)$.]),
)

= 5.3 Relational coproducts

A coproduct of $alpha, beta$ in $sans("Fun")(cal(A))$ is a coproduct in the whole power
allegory $cal(A)$: $ iota T = R and iota' T = S <==> T = [Lambda R, Lambda S] eps. $

#dia(
  spacing: (21mm, 12mm),
  node((1,0), $alpha + beta$), node((0,1), $alpha$), node((2,1), $beta$),
  node((1,1), $[gamma]$), node((1,2), $gamma$),
  edge((0,1), (1,0), $iota$, "->"),
  edge((2,1), (1,0), $iota'$, "->"),
  edge((1,0), (1,1), $[Lambda R, Lambda S]$, "-->", label-side: left),
  edge((0,1), (1,1), $Lambda R$, "->"),
  edge((2,1), (1,1), $Lambda S$, "->"),
  edge((1,1), (1,2), $eps$, "->", label-side: left),
  edge((0,1), (1,2), $R$, "->", bend: -35deg),
  edge((2,1), (1,2), $S$, "->", bend: 35deg),
)

#dt(
  ("5.3 ✓", [#D("junc") $[R,S] eq.delta [Lambda R, Lambda S] eps$.]),
  ("(5.9) ✓", [$[R,S] = (iota^degree R) union (iota'^degree S)$.]),
  ("(5.10) ✓", [$R + S eq.delta [R iota, S iota']$, monotonic in both arguments, so $+$ is a
    relator.]),
  ("(5.11) ✓", [#D("cancellation") $[U,V]^degree [R,S] = (U^degree R) union (V^degree S)$.
    Easier than (5.8) — but still not the dual of it, an allegory being its own opposite.]),
  ("Ex 5.12 ✓", [$iota [1,nothing] = 1$ and $iota' [1,nothing] = nothing$, and
    $[1,nothing] iota union [nothing,1] iota' = [iota,iota'] = 1$; hence
    $[1,nothing] = iota^degree$, $[nothing,1] = iota'^degree$, which gives (5.9).]),
  ("Ex 5.14", [$(R + S) inter ([P,Q][U,V]^degree)
    = (R inter P U^degree) + (S inter Q V^degree)$.]),
)

= 5.4 The power relator

#dt(
  ("5.4 ✓", [On maps $P f = ((eps f) slash eps) inter (eps^degree backslash (f eps^degree))$;
    read as a definition for relations,
    $ P R eq.delta ((eps R) slash eps) inter (eps^degree backslash (R eps^degree)). $]),
  ("", [#rel[$x thin (P R) thin y <==> (forall a ∈ x. thin exists b ∈ y. thin a R b) and
    (forall b ∈ y. thin exists a ∈ x. thin a R b)$.]  Every element of $x$ has an $R$-partner
    in $y$, and conversely.]),
  ("✓", [$P$ is monotone in $R$, straight from monotonicity of division.]),
  ("✓", [$P 1 = 1$ — this is the antisymmetry of $"subset" = eps slash eps$ restated, so it
    needs the allegory unitary and tabular.]),
  ("✓", [$(P R)(P S) = P(R S)$, so $P$ is a relator.  $subset$ is division cancellation;
    $supset$ needs a tabulation $(x,z)$ of $P(R S)$ and the mediating map
    $y = Lambda((x eps R^degree) inter (z eps S))$.]),
  ("✓", [$P$ and $E$ agree on maps: $P f = Lambda(eps f) = E f$.]),
  ("Ex 5.15", [They differ on relations, and Corollary 5.1 does not object: $E$ is not
    monotonic — distinct maps are never comparable, so $R subset S$ says nothing about
    $Lambda(eps R)$ and $Lambda(eps S)$ — hence not a relator.]),
  ("Ex 5.16", [$P("dom" R)(E R) subset P R$.]),
)

= 5.5 Relational catamorphisms

Let $F$ have initial algebra $sans("in") : F T -> T$ #emph[in the subcategory of maps].  It
is then initial for relational algebras as well.

#dt(
  ("(5.12) ✓", [#Th[$sans("in") X = (F X) R <==> X = ⦇Lambda((F eps) R)⦈ eps$.]]),
  ("5.5 ✓", [$⦇R⦈ eq.delta ⦇Lambda((F eps) R)⦈ eps$ — the unique $X$ with
    $sans("in") X = (F X) R$.]),
  ("5.5 ✓", [#D("Eilenberg–Wright") $Lambda ⦇R⦈ = ⦇Lambda((F eps) R)⦈$: the transpose of a
    relational catamorphism is a catamorphism of maps.  This is what turns a relational
    specification into a functional fold over sets, and it is used throughout §5.6.]),
  ("✓", [Over a map algebra the relational catamorphism is the ordinary one.]),
  ("5.5", [#D("type relator") $F$ binary with initial type $(alpha, T)$: then
    $(T R)^degree = T(R^degree)$, so $T$ is a relator.  By uniqueness — both sides solve
    $sans("in") X = F(R^degree, X) sans("in")$.]),
  ("Ex 5.17 ✓", [In a Boolean allegory each coreflexive $C$ has a $tld C$ with
    $C inter tld C = nothing$ and $C union tld C = 1$.  Then
    $"guard" C eq.delta [C, tld C]^degree$ is a map,
    $(C -> R, S) eq.delta ("guard" C)(R + S)$, and conditionals behave like cases:
    $ R subset (C -> S, T) <==> C R subset S and (tld C) R subset T. $]),
  ("Ex 5.18", [$F$ preserves meets $==>$ so does the type relator $T$ it induces; in
    particular $"list"$ does.]),
  ("Ex 5.19", [$R$ entire $==> ⦇R⦈$ entire (reflection gives $"dom" ⦇R⦈ = 1$).]),
)

#dia(
  spacing: (26mm, 13mm),
  node((0,0), $F T$), node((1,0), $T$),
  node((0,1), $F[alpha]$), node((1,1), $[alpha]$),
  node((0,2), $F alpha$), node((1,2), $alpha$),
  edge((0,0), (1,0), $sans("in")$, "->"),
  edge((0,0), (0,1), $F ⦇Lambda((F eps) R)⦈$, "->", label-side: right),
  edge((1,0), (1,1), $⦇Lambda((F eps) R)⦈$, "->", label-side: left),
  edge((0,1), (1,1), $Lambda((F eps) R)$, "->"),
  edge((0,1), (0,2), $F eps$, "->", label-side: right),
  edge((1,1), (1,2), $eps$, "->", label-side: left),
  edge((0,2), (1,2), $R$, "->"),
)

= 5.6 Combinatorial functions

Lists mean cons-lists, and $"list"$ is their type functor,
$"list" R = ⦇"nil", (R times 1) "cons"⦈$.  Each relation below is specified as a
catamorphism, transposed by Eilenberg–Wright, then implemented on lists.

#sub[Subsequences]

#dt(
  ("5.6", [$"subseq" = ⦇["nil", "cons" union pi']⦈ : "list" alpha -> "list" alpha$ — at each
    step keep the head or drop it.]),
  ("", [$Lambda "subseq" = ⦇"nil" tau, thin
    chevron.l Lambda(1 times eps)(P "cons"), pi' chevron.r "cup"⦈$, by expanding
    $Lambda(["nil", "cons" union pi'] thin F(1, eps))$ for $F(A,B) = 1 + (A times B)$.
    Pointwise: $e = {[]}$ and
    $f(a, italic("xs")) = {"cons"(a,x) | x ∈ italic("xs")} union italic("xs")$.]),
  ("", [$Lambda(R union S) = chevron.l Lambda R, Lambda S chevron.r "cup"$, where $"cup"$ unions
    a pair of sets.]),
  ("5.6", [Sets replaced by lists: $"subseqs" = ⦇"nil" "wrap", thin
    chevron.l "cpr" ("list" "cons"), pi' chevron.r "cat"⦈$, i.e. $e = [[]]$ and
    $f(a,italic("xs")) = ["cons"(a,x) | x <- italic("xs")] cc italic("xs")$.]),
  ("", [$"cpr" : alpha times "list" beta -> "list"(alpha times beta)$ ("cartesian product,
    right"), $"cpr"(a,x) = [(a,b) | b <- x]$.]),
  ("5.6", [$"setify" eq.delta ⦇omega, (tau times 1) "cup"⦈ : "list" alpha -> [alpha]$, a
    list's set of elements; $omega$ returns the empty set.]),
  ("Ex 5.21", [$"nil" thin "setify" = omega$, #h(0.4em) $"wrap" thin "setify" = tau$,
    #h(0.4em) $"cat" thin "setify" = ("setify" times "setify")"cup"$, #h(0.4em)
    $("list" f) "setify" = "setify" (P f)$.]),
  ("", [$"concat" thin "setify" = ("list" "setify") thin "setify" thin union.big$, #h(0.4em)
    $"cpr" thin "setify" = (1 times "setify") Lambda(1 times eps)$.]),
  ("Ex 5.22", [$"subseqs" thin "setify" = Lambda "subseq"$ — the list program implements the
    set specification.  By fusion, from the identities above.]),
  ("Ex 5.23", [$"subseq"$ is the converse of a catamorphism, the one computing
    supersequences.]),
)

#sub[Cartesian product]

#dt(
  ("5.6", [$"cpp"(x,y) = [(a,b) | a <- x, b <- y]$ and $"cpl"(x,b) = [(a,b) | a <- x]$, with
    $"cpp" thin "setify" = Lambda(eps times eps)$ and
    $"cpl" thin "setify" = Lambda(eps times 1)$.]),
  ("5.6", [$"cp"(F) eq.delta Lambda(F eps) : F[alpha] -> [F alpha]$ — one choice from each
    slot.  $"cpr", "cpp", "cpl"$ implement it for $F A = alpha times A$, $A times A$ and
    $A times beta$.]),
  ("", [$"cp"("list") = ⦇Lambda["nil", (eps times eps)"cons"]⦈
    = ⦇"nil" tau, thin Lambda(eps times eps)(P "cons")⦈$ by Eilenberg–Wright;
    $"cp"("list")[x_1,...,x_n] = {[a_1,...,a_n] | a_j ∈ x_j}$.  On lists:
    $"cplist" = ⦇"nil" "wrap", thin "cpp" ("list" "cons")⦈$.]),
  ("Ex 5.20 ✓", [$Lambda(R union S) = chevron.l Lambda R, Lambda S chevron.r "cup"$, #h(0.4em)
    $Lambda(R inter S) = chevron.l Lambda R, Lambda S chevron.r "cap"$, #h(0.4em)
    $Lambda(R times S) = (Lambda R times Lambda S) "cross"$, with
    $"cup" = Lambda((pi eps) union (pi' eps))$ and
    $"cap" = Lambda((pi eps) inter (pi' eps))$.]),
)

#sub[Prefix and suffix]

#dt(
  ("5.6", [$"prefix" = "cat"^degree pi$: #h(0.4em) $x thin "prefix" thin y$ when
    $x cc z = y$ for some $z$.  Also $"prefix" = "init"^*$ with
    $"init" = "snoc"^degree pi$, and $"prefix" = ⦇"nil", "nil" union "cons"⦈$ — the second
    $"nil"$ being $! thin "nil" : alpha times "list" alpha -> "list" alpha$.]),
  ("", [$Lambda "prefix" = ⦇"nil" tau, thin chevron.l "nil" tau,
    Lambda(1 times eps)(P "cons") chevron.r "cup"⦈$.]),
  ("5.6", [$"inits" = ⦇"nil" "wrap", thin chevron.l "nil" "wrap",
    "cpr" ("list" "cons") chevron.r "cat"⦈$, i.e. $"inits" [] = [[]]$ and
    $"inits" ([a] cc x) = [[]] cc [[a] cc y | y <- "inits" x]$ — initial segments in
    increasing order of length.]),
  ("5.6", [$"suffix" = "tail"^*$ with $"tail" = "cons"^degree pi'$, the snoc-list dual of
    $"prefix"$.  $"tails" [] = [[]]$ and
    $"tails" (x cc [a]) = [y cc [a] | y <- "tails" x] cc [[]]$ — decreasing length.]),
  ("", [Not implementable as it stands; as a cons-list catamorphism
    $"tails" = ⦇"nil" "wrap", "extend"⦈$ with
    $"extend"(a, [x] cc italic("xs")) = [[a] cc x] cc [x] cc italic("xs")$.]),
  ("5.6", [$"splits" = chevron.l "inits", "tails" chevron.r "zip"$ implements
    $Lambda("cat"^degree)$, every way of splitting a list in two — and works only because
    $"inits"$ and $"tails"$ order their segments oppositely.]),
  ("Ex 5.24", [$"init" : "list"^+ alpha -> "list" alpha$ is itself a catamorphism.]),
)

#sub[Partitions]

#dt(
  ("5.6", [$"partition" eq.delta "concat"^degree : "list" alpha -> "list"("list"^+ alpha)$ —
    cut a list into non-empty contiguous segments.  #rel[$"partition" [1,2,3] =
    {[[1],[2],[3]], [[1,2],[3]], [[1],[2,3]], [[1,2,3]]}$.]]),
  ("", [As a catamorphism $"partition" = ⦇"nil", "new" union "glue"⦈$ with
    $"new" = ("wrap" times 1)"cons"$ and
    $"glue" = (1 times "cons"^degree) "assocl" ("cons" times 1) "cons"$: at each step either
    open a segment or glue the element onto the first one.  Pointwise
    $"new"(a,italic("xs")) = [[a]] cc italic("xs")$ and
    $"glue"(a, [x] cc italic("xs")) = [[a] cc x] cc italic("xs")$.]),
  ("6", [The two agree by the converse-catamorphism theorem of the next chapter:
    $"ran" R = 1$ and $R f subset F(1,f) sans("in") ==> f^degree = ⦇R⦈$, applied to
    $f = "concat"$ and $R = ["nil", "new" union "glue"]$.]),
  ("Ex 5.25", [Its surjectivity rests on
    $"new"^degree "new" = "cons"^degree ("wrap"^degree "wrap" times 1) "cons"$ and
    $"glue"^degree "glue" = "cons"^degree ("cons"^degree "cons" times 1) "cons"$.]),
  ("", [$Lambda "partition" = ⦇Lambda "nil", thin
    Lambda((1 times eps)("new" union "glue"))⦈$, whose step simplifies (Ex 5.27) to
    $Lambda(1 times eps) thin P(chevron.l "new" tau, Lambda "glue" chevron.r "cup") thin union.big$.]),
  ("5.6", [$"partitions" = ⦇"nil" "wrap", thin
    "cpr" ("list" (chevron.l "new", "glues" chevron.r "cons")) "concat"⦈$, where $"glues"$
    implements $Lambda "glue"$: $"glues"(a,[]) = []$ and
    $"glues"(a, [x] cc italic("xs")) = [[[a] cc x] cc italic("xs")]$.]),
  ("Ex 5.26", [$"partitions" thin "setify" = Lambda "partition"$.]),
)

#sub[Permutations]

#dt(
  ("5.6", [$"bag" alpha$ is the initial algebra $["bnil", "bcons"]$ of
    $F(A,B) = 1 + A times B$ whose $"bcons"$ commutes,
    $(1 times "bcons")"bcons" = "exch" (1 times "bcons") "bcons"$, i.e.
    $"bcons"(a, "bcons"(b,x)) = "bcons"(b, "bcons"(a,x))$: order is irrelevant, duplicates
    are not.  $"exch" = "assocl" ("swap" times 1) "assocr"$.]),
  ("5.6", [$"bagify" = ⦇"bnil", "bcons"⦈ : "list" alpha -> "bag" alpha$ is surjective,
    $"bagify"^degree "bagify" = 1$.]),
  ("5.6", [$"perm" eq.delta "bagify" thin "bagify"^degree$ — equal bags of values.  At once
    $"perm" = "perm"^degree$.]),
  ("", [As a catamorphism $"perm" = ⦇"nil", "add"⦈$ with $"add" = "cons" thin "perm"$, or
    with the usable $"add" = (1 times "cat"^degree) "exch" (1 times "cons") "cat"$:
    $"add"(a,x) = y cc [a] cc z$ where $y cc z = x$, so $a$ goes in anywhere.]),
  ("Ex 5.28", [$"cons" thin "perm" = (1 times "perm") "cons" thin "perm"$, from
    $"bagify"^degree "bagify" = 1$.]),
  ("5.6", [$"adds"(a,x) = [y cc [a] cc z | (y,z) <- "splits" x]$ and
    $"perms" = ⦇"nil" "wrap", thin "cpr" ("list" "add")⦈$.]),
  ("Ex 5.29", [$"interleave"$, all interleavings of two lists, is the converse of a
    catamorphism.]),
)

= 5.7 Lax natural transformations

Some equalities of the functional world become inequalities in the relational one.

#dt(
  ("(5.13) ✓", [#D("lax natural") $phi : F arrow.hook G$ #h(0.4em) $eq.delta$ #h(0.4em)
    $phi (F R) supset (G R) phi$ for every $R$, where $phi_alpha : G alpha -> F alpha$.
    The $supset$ is the way the hook points.]),
)

#dia(
  spacing: (20mm, 12mm),
  node((0,0), $G alpha$), node((1,0), $F alpha$),
  node((0,1), $G beta$),  node((1,1), $F beta$),
  node((0.5,0.5), $supset$),
  edge((0,0), (1,0), $phi$, "->"),
  edge((0,0), (0,1), $G R$, "->", label-side: right),
  edge((1,0), (1,1), $F R$, "->", label-side: left),
  edge((0,1), (1,1), $phi$, "->"),
)

#dt(
  ("5.7", [Example: $eps : 1 arrow.hook P$, that is $(P R) eps subset eps R$ — immediate
    from the definition of $P R$.]),
  ("Thm 5.2 ✓", [#Th[$F, G$ relators: $phi$ is lax natural $F arrow.hook G$ $<==>$ $phi$ is
    strictly natural on maps, $phi (F f) = (G f) phi$.]  So lax naturality adds nothing to
    naturality of the underlying map functors — it only records how it extends.]),
  ("Ex 5.30", [Three instances: $R tau subset tau (P R)$, #h(0.4em)
    $R chevron.l 1,1 chevron.r subset chevron.l 1,1 chevron.r (R times R)$, #h(0.4em)
    $(P R times P R) "cup" subset "cup" (P R)$.]),
)
