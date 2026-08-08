// §1.4 CARTESIAN CATEGORIES
// kept: 1.41 1.412 1.413 1.414 1.415 1.421 1.423 1.424 1.425 1.426 1.428 1.429 1.43
//       1.431 1.432 1.433 1.434 1.435 1.437 1.438 1.439 1.44 1.441 1.442 1.443 1.444
//       1.45 1.451 1.452 1.453 1.454 1.46 1.462 1.463 1.464 1.465 1.47 1.471 1.472 1.473
//       1.474 1.48 1.481
// dropped: 1.411 1.422 1.427 (non-Rel examples: ordered fields, LH, Sh(Y), S^A co-ideals);
//       1.436 (16-row table of finitely-presented counterexamples); 1.461 (LH: the whole item
//       is the cartesian structure of LH and Sh(Y)); 1.475 (Z-set counterexample);
//       1.49-1.4(12) (tau-category apparatus and its metatheorem — proof machinery).
// Diagrams are Freyd's own figures, in his diagrammatic language; the abbreviating
// "we denote it thusly" figures are not reproduced.
#import "style.typ": *

= 1.4 Cartesian categories

#dt(
  ("1.41", [#D("monic pair") — $!$ reads "there is at most one extension to": #sent(
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->")),
    qbar[$forall$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->")),
    qbar[$!$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->"),
      edge((1, -1), (1, 0), "->")),
  )
  in symbols: $square x = square y and forall_(u, v) [(u x = v x) and (u y = v y)] ==> u = v$.]),

  ("", [a single #D("monic") $x$, written $A arrow.r.tail B$ — variously called monomorphism, mono, injection; here always monic: #sent(
    pan(vx((0, 0)), vx((1, 0)), edge((0, 0), (1, 0), "->")),
    qbar[$forall$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, -1)),
      edge((0, 0), (1, 0), "->"), edge((0, -1), (1, 0), "->")),
    qbar[$!$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, -1)),
      edge((0, 0), (1, 0), "->"), edge((0, -1), (1, 0), "->"),
      edge((0, -1), (0, 0), "->")),
  )]),

  ("1.412", [monic family: $forall_(x in cal(F)) u x = v x ==> u = v$. A #D("table") $chevron.l T; x_1, ..., x_n chevron.r$ is the #D("top") $T$ with a monic finite sequence out of it; the targets are the #D("feet"), the $x_i$ the #D("columns").]),

  ("", [an isomorphism class of tables is a #D("relation"), $Rel(A_1, ..., A_n)$ the family of them on given feet. $n = 1$: a #D("subobject") of $A$, family $Sub(A)$. $n = 0$: a #D("value"), family $Val$.]),

  ("", [#D("sub-terminator") — the top of a columnless table: #sent(
    pan(vx((0, 0))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, -1))),
    qbar[$!$],
    pan(vx((0, 0)), vx((0, -1)), edge((0, -1), (0, 0), "->")),
  )]),

  ("1.413", [#D("contained"), $chevron.l T; x_i chevron.r subset chevron.l T'; x'_i chevron.r$: some $z: T -> T'$ with $z x'_i = x_i$ — necessarily unique and monic. Containment pre-orders tables and partially orders relations, mutual containment being isomorphism; $Rel$, $Sub$, $Val$ are posets.]),

  ("1.414", [$A -> B$ is monic in $bold(A)$ iff it is a sub-terminator of $bold(A) slash B$. Hence $Sub_bold(A)(B) tilde.eq Val_(bold(A) slash B)$.]),

  ("1.415", [#rel[a table on $A, B$ lists, without repetition, the instances of a relation from $A$ to $B$ — the extensional and the categorical notions coincide.]]),

  ("1.421", [#D("terminator") (elsewhere: final, terminal), written $1$, with $p_A: A -> 1$; a sub-terminator, representing the maximum value, unique up to a unique isomorphism: #sent(
    pan(vx((0, 0))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, -1))),
    qbar[$exists!$],
    pan(vx((0, 0)), vx((0, -1)), edge((0, -1), (0, 0), "->")),
  )]),

  ("", [a category has a terminator if #sent(
    qbar[$exists$],
    pan(vx((0, 0))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, -1))),
    qbar[$exists!$],
    pan(vx((0, 0)), vx((0, -1)), edge((0, -1), (0, 0), "->")),
  )]),

  ("1.423", [binary #D("product") diagram: #sent(
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->")),
    qbar[$forall$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->")),
    qbar[$exists!$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->"),
      edge((1, -1), (1, 0), "->")),
  )]),

  ("", [written $A times B$ with $ell: A times B -> A$, $kappa.alt: A times B -> B$; $chevron.l f, g chevron.r$ the unique map with $chevron.l f, g chevron.r ell = f$, $chevron.l f, g chevron.r kappa.alt = g$; and $(x times y) = chevron.l ell' x, kappa.alt' y chevron.r$. $A times B$ is a table on $A, B$ and the maximum of $Rel(A, B)$, so products are unique up to isomorphism.]),

  ("", [a category has binary products if — the cross marking a product diagram: #sent(
    qbar[$forall$],
    pan(vx((0, 0)), vx((1, 0))),
    qbar[$exists$],
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"), prodm((1, 0.45))),
  )]),

  ("1.424", [#rel[products are the disjoint sums.] In a poset, products are greatest lower bounds.]),

  ("1.425", [indexed product: $P$ with $\{p_i: P -> A_i\}_I$ through which every $\{x_i: X -> A_i\}$ factors uniquely, $z p_i = x_i$; written $Pi_I A_i$. Empty product $=$ terminator; finite products $=$ terminator $+$ binary products. A poset has all finite products iff it is a semi-lattice.]),

  ("1.426", [#dia(
    node((1, 0), $T$), node((0, 1), $A$), node((2, 1), $B$),
    edge((1, 0), (0, 1), $x$, "->", label-side: right), edge((1, 0), (2, 1), $y$, "->"))
    is a table iff $chevron.l x, y chevron.r: T -> A times B$ is monic, so $Rel(A, B) tilde.eq Sub(A times B)$, generally $Rel(A_1, ..., A_n) tilde.eq Sub(A_1 times dots.c times A_n)$, and $Val = Sub(1)$.]),

  ("1.428", [#D("equalizer") diagram — the puncture mark removes just the one equation, so the square carrying it need not commute: #sent(
    pan(spacing: (8mm, 5.5mm), vx((0, 0)), vx((1, 0)), vx((2, 0)),
      edge((0, 0), (1, 0), "->"),
      edge((1, 0), (2, 0), "->", shift: 3pt), edge((1, 0), (2, 0), "->", shift: -3pt),
      punc((1.5, 0))),
    qbar[$forall$],
    pan(spacing: (8mm, 5.5mm), vx((0, 0)), vx((1, 0)), vx((2, 0)), vx((1, -1)),
      edge((0, 0), (1, 0), "->"),
      edge((1, 0), (2, 0), "->", shift: 3pt), edge((1, 0), (2, 0), "->", shift: -3pt),
      punc((1.5, 0)), edge((1, -1), (1, 0), "->")),
    qbar[$exists!$],
    pan(spacing: (8mm, 5.5mm), vx((0, 0)), vx((1, 0)), vx((2, 0)), vx((1, -1)),
      edge((0, 0), (1, 0), "->"),
      edge((1, 0), (2, 0), "->", shift: 3pt), edge((1, 0), (2, 0), "->", shift: -3pt),
      punc((1.5, 0)), edge((1, -1), (1, 0), "->"), edge((1, -1), (0, 0), "->")),
  )]),

  ("", [equalizers are monic, so they represent subobjects, and are essentially unique. In $cal(S)$: $\{x | f x = g x\}$.]),

  ("1.429", [if $e, 1_A$ has an equalizer for every idempotent $e$, then #Th[all idempotents split.]]),

  ("1.43", [#D("cartesian category"): finite products and equalizers (elsewhere: finitely complete, left-exact).]),

  ("1.431", [#D("pullback") diagram — its upper half is a monic pair, and the relation that pair represents is fixed by the lower half: #sent(
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->")),
    qbar[$forall$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->")),
    qbar[$exists!$],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->"),
      edge((1, -1), (1, 0), "->")),
  )]),

  ("", [a category has pullbacks if — the corner mark $lr(⌐)$ standing for the whole sentence above: #sent(
    qbar[$forall$],
    pan(vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->")),
    qbar[$exists$],
    pan(vx((1, -1)), vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((1, -1), (0, 0), "->"), edge((1, -1), (2, 0), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      ..pb((1, -1), (0, 0), (2, 0))),
  )]),

  ("1.432", [#Th[Binary products $+$ equalizers $=>$ pullbacks] — construct in sequence; the outer diagram on the right is the pullback: #sent(
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"), prodm((1, 0.45)),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"), punc((1, 1.55))),
    [],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, -1), (1, 0), ">->"),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"), prodm((1, 0.45)),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"), punc((1, 1.55))),
    [],
    pan(vx((1, -1)), vx((1, 0)), vx((0, 1)), vx((2, 1)), vx((1, 2)),
      edge((1, -1), (1, 0), ">->"),
      edge((1, -1), (0, 1), "->"), edge((1, -1), (2, 1), "->"),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"), prodm((1, 0.45)),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"), punc((1, 1.55))),
  )]),

  ("1.433", [#Th[Pullbacks $+$ a terminator $=>$ binary products]: #sent(
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)), node((1, 2), $1$),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"),
      edge((0, 1), (1, 2), "->"), edge((2, 1), (1, 2), "->"),
      ..pb((1, 0), (0, 1), (2, 1))),
    text(size: 7.5pt)[#emph[implies]],
    pan(vx((1, 0)), vx((0, 1)), vx((2, 1)),
      edge((1, 0), (0, 1), "->"), edge((1, 0), (2, 1), "->"), prodm((1, 0.45))),
  )]),

  ("1.434", [#Th[Binary products $+$ pullbacks $=>$ equalizers] — given $x, y: A -> B$, then $u = v$ and $u$ equalizes $x, y$: #dia(
    node((1, 0), $E$), node((0, 1), $A$), node((2, 1), $A$), node((1, 2), $A times B$),
    edge((1, 0), (0, 1), $u$, "->", label-side: right), edge((1, 0), (2, 1), $v$, "->"),
    edge((0, 1), (1, 2), $chevron.l 1, x chevron.r$, "->", label-side: right),
    edge((2, 1), (1, 2), $chevron.l 1, y chevron.r$, "->", label-side: left),
    ..pb((1, 0), (0, 1), (2, 1)))]),

  ("1.435–6", [combining the last two: #Th[pullbacks and a terminator imply cartesian.] The three lemmas are exhaustive — all sixteen combinations of terminator / binary products / equalizers / pullbacks not forced by them are realized.]),

  ("1.437", [a functor preserving finite products and equalizers is a #D("representation of cartesian categories"); such preserve pullbacks. Preserving pullbacks $+$ the terminator suffices; so does preserving finite products $+$ pullbacks of monics.]),

  ("1.438", [#Th[A functor reflecting equalizers reflects isomorphisms] ($A -> B$ is iso iff it equalizes $1_B, 1_B$). From a category with equalizers, an isomorphism-reflecting equalizer-preserving functor is an embedding, hence faithful. A faithful functor preserving terminators / products / equalizers / pullbacks reflects them too.]),

  ("1.439", [#Th[With pullbacks, if $A ->^(f, g) B -> C$ then $f, g$ have an equalizer] — $P = B times_C B$ replaces $B times B$, and $E -> A$ is the equalizer: #dia(
    node((1.5, 0), $X$), node((1.5, 1), $E$), node((0, 1.9), $B$), node((3, 1.9), $A$),
    node((1.5, 2.8), $P$), node((0, 3.7), $B$), node((3, 3.7), $B$), node((1.5, 4.6), $C$),
    edge((1.5, 0), (0, 1.9), "->"), edge((1.5, 0), (3, 1.9), "->"),
    edge((1.5, 1), (0, 1.9), "->"), edge((1.5, 1), (3, 1.9), "->"),
    ..pb((1.5, 1), (0, 1.9), (3, 1.9)),
    edge((0, 1.9), (1.5, 2.8), "->"), edge((3, 1.9), (1.5, 2.8), "->"),
    edge((0, 1.9), (0, 3.7), $1$, "->", label-side: right),
    edge((0, 1.9), (3, 3.7), $1$, "-->"),
    edge((3, 1.9), (0, 3.7), $f$, "->", bend: -18deg),
    edge((3, 1.9), (3, 3.7), $g$, "->"),
    edge((1.5, 2.8), (0, 3.7), "->"), edge((1.5, 2.8), (3, 3.7), "->"),
    ..pb((1.5, 2.8), (0, 3.7), (3, 3.7)),
    edge((0, 3.7), (1.5, 4.6), "->"), edge((3, 3.7), (1.5, 4.6), "->"))]),

  ("", [#Th[A functor from a cartesian category preserving pullbacks preserves equalizers.]]),

  ("1.44", [$Sigma: bold(A) slash B -> bold(A)$ does not preserve terminators — $bold(A) slash B$ has the distinguished terminator $1_B$, carried to $B$ — and is universal in that: for $T: bold(C) -> bold(A)$ with $T(1) = B$ there is a unique $T': bold(C) -> bold(A) slash B$ with $T'(1) = 1_B$ and $T = T' Sigma$.]),

  ("", [specializing to $T = B times -$ gives the #D("diagonal functor") $Delta(A) = (B times A ->^kappa.alt B)$ and the factorization $bold(A) ->^Delta bold(A) slash B ->^Sigma bold(A)$.]),

  ("1.441", [if $bold(A)$ has pullbacks then $bold(A) slash B$ is cartesian and $Sigma$ preserves pullbacks and equalizers; $Sigma$ is always faithful.]),

  ("1.442", [the Cayley representation preserves and reflects pullbacks and equalizers; factoring it as $bold(A) ->^(C') cal(S)^(|bold(A)|) ->^Sigma cal(S)$ gives a faithful representation. #Th[Every small cartesian category is faithfully represented in a power of $cal(S)$.]]),

  ("", [the $A$-th coordinate of $C'$ is the #D("representable functor") $(A, -)$: $B |-> (A, B)$, $f |-> (A, f)$, i.e. $g |-> g f$. #Th[Representable functors from a cartesian category are representations of cartesian categories, and are collectively faithful.]]),

  ("1.443", [a universal sentence in the pullback / equalizer predicates with a counterexample anywhere has one in $cal(S)$: cut down to a small subcategory, then apply Cayley.]),

  ("1.444", [#D("horn sentence"): a universally quantified $(P_1 and ... and P_n) ==> Q$ with all $P_i, Q$ primitive; for cartesian categories the primitives are the categorical ones plus "is a terminator / product / equalizer". #Th[Any Horn sentence in the theory of cartesian categories true for $cal(S)$ is true for every cartesian category] — apply a collectively faithful $(A, -)$ to the counterexample.]),

  ("1.45", [pullbacks transfer monics: #sent(
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), ">->"),
      ..pb((0, 0), (1, 0), (0, 1))),
    text(size: 7.5pt)[#emph[implies]],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->"),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), ">->"),
      ..pb((0, 0), (1, 0), (0, 1))),
  )]),

  ("", [that is, if #dia(
    node((0, 0), $$), node((1, 0), $$), node((0, 1), $$), node((1, 1), $$),
    edge((0, 0), (1, 0), $overline(x)$, "->"), edge((0, 0), (0, 1), "->"),
    edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), $x$, "->", label-side: right))
    is a pullback and $x$ is monic, then so is $overline(x)$.]),

  ("1.451", [$A_1 arrow.r.tail A$ is an #D("inverse image") of $B_1 arrow.r.tail B$ along $f$: #dia(
    node((0, 0), $A_1$), node((1, 0), $A$), node((0, 1), $B_1$), node((1, 1), $B$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((1, 0), (1, 1), $f$, "->"), edge((0, 1), (1, 1), ">->"),
    ..pb((0, 0), (1, 0), (0, 1)))]),

  ("", [inverse images preserve containment, hence are well defined on subobjects: an order-preserving $f^\# : Sub(B) -> Sub(A)$, making $Sub(-)$ a contravariant poset-valued functor.]),

  ("1.452", [pulling back two monics gives their greatest lower bound in $Sub(A)$: #dia(
    node((1, 0), $A_(1 2)$), node((0, 1), $A_1$), node((2, 1), $A_2$), node((1, 2), $A$),
    edge((1, 0), (0, 1), ">->"), edge((1, 0), (2, 1), ">->"),
    edge((0, 1), (1, 2), ">->"), edge((2, 1), (1, 2), ">->"),
    ..pb((1, 0), (0, 1), (2, 1)))]),

  ("", [so $Sub(A)$ is a #D("semi-lattice") — a poset with finite intersections, the empty one $1_A$ — and $Sub(-)$ lands in semi-lattices, inverse images preserving intersections.]),

  ("1.453", [#D("lemma") #Th[$bold(A)$ cartesian, $T$ preserving pullbacks: $T$ is faithful iff $T$ preserves properness of subobjects] — if $A' arrow.r.tail A$ is not iso, neither is $T A' arrow.r.tail T A$.]),

  ("1.454", [the kernel-pair of $f$ measures how far $f$ is from monic: the #D("level") of $f$ (elsewhere: kernel-pair, congruence). $f$ is monic iff $Delta$ is iso; this monic $Delta: A -> L$ is the #D("diagonal") morphism, representing the diagonal subobject. #dia(
    node((1, 0), $A$), node((1, 1), $L$), node((0, 2), $A$), node((2, 2), $A$), node((1, 3), $B$),
    edge((1, 0), (1, 1), $Delta$, ">->"),
    edge((1, 0), (0, 2), $1$, "->", bend: -22deg), edge((1, 0), (2, 2), $1$, "->", bend: 22deg),
    edge((1, 1), (0, 2), $l$, "->", label-side: right), edge((1, 1), (2, 2), $r$, "->"),
    edge((0, 2), (1, 3), $f$, "->", label-side: right), edge((2, 2), (1, 3), $f$, "->"),
    ..pb((1, 1), (0, 2), (2, 2)))]),

  ("1.46", [the cartesian structure of the prime examples.]),

  ("1.462", [for small $bold(A)$, $cal(S)^bold(A)$ is cartesian and the #D("evaluation functors") $E_A: cal(S)^bold(A) -> cal(S)$, $E_A (F) = F(A)$, are representations of cartesian categories, collectively faithful. Assembled into the forgetful $cal(S)^bold(A) -> cal(S)^(|bold(A)|)$ they give a faithful representation into a power of $cal(S)$. Hence $F_1 -> F_2$ is monic iff every $F_1 A -> F_2 A$ is.]),

  ("1.463", [$H^A$ denotes $(A, -)$ viewed in $cal(S)^bold(A)$. As a right $bold(A)$-set it is the sub $bold(A)$-set of $bold(A)$ generated by $1_A$: for any right $bold(A)$-set $X$ and $x in X$ with $x square = A$ there is a unique $H^A -> X$ sending $1_A |-> x$, $y |-> x y$. So $(H^A, X) tilde.eq \{x in X | x square = A\}$, and for the functor $F$ associated to $X$, $(H^A, F) tilde.eq F(A)$, naturally — $(H^A, -)$ and $E_A$ are conjugate.]),

  ("1.464", [$(H^A, H^B) tilde.eq (B, A)$, so each $x: B -> A$ gives $H^x: H^A -> H^B$ and a contravariant full embedding $H: bold(A) -> cal(S)^bold(A)$, the #D("yoneda representation").]),

  ("", [$"Hom": bold(A)^circle.small times bold(A) -> cal(S)$ sends $A, B$ to $(A, B)$; the composite $bold(A) times cal(S)^bold(A) ->^(H^circle.small times 1) (cal(S)^bold(A))^circle.small times cal(S)^bold(A) ->^"Hom" cal(S)$ is naturally equivalent to $E: A, F |-> F(A)$.]),

  ("1.465", [$H_B$ denotes the contravariant $(-, B)$ viewed in $cal(S)^(bold(A)^circle.small)$; again $(H_B, F) tilde.eq F(B)$, giving a covariant full embedding $bold(A) -> cal(S)^(bold(A)^circle.small)$, also called the yoneda representation. It preserves and reflects the cartesian predicates.]),

  ("1.47", [$bold(A)$ is #emph[special] if every universal (not merely Horn) sentence in the cartesian predicates true for $cal(S)$ holds in $bold(A)$.]),

  ("1.471–4", [#Th[A special cartesian category has at most two values.] If every finite sequence of morphisms is preserved-and-reflected by some $T: bold(A) -> cal(S)$, then $bold(A)$ is special. One-valued $bold(A)$: special iff every $B times -$ is faithful. Two-valued $bold(A)$, with $0$ the proper subobject of $1$: special iff $B times -$ is faithful for every $B tilde.eq.not 0$.]),

  ("1.48", [a class $cal(D)$ of monics in a cartesian $bold(A)$ is #D("dense") if it holds the isomorphisms and is closed under composition and pullback. The #D("rational category") $bold(A)[cal(D)^(-1)]$, with $T_cal(D)$, inverts every dense monic and is universal among functors that do.]),

  ("1.481", [#Th[$bold(A)[cal(D)^(-1)]$ is cartesian and $T_cal(D)$ is a representation of cartesian categories.]]),
)
