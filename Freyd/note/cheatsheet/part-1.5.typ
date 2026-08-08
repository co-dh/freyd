// §1.5 REGULAR CATEGORIES
// kept: 1.51 1.511 1.512 1.513 1.514 1.52 1.521 1.522 1.523 1.524 1.525 1.526 1.53 1.531
//       1.535 1.54 1.541 1.542 1.543 1.544 1.545 1.547 1.55 1.551 1.552 1.56 1.561 1.562
//       1.563 1.564 1.565 1.566 1.567 1.568 1.569 1.56(10) 1.56(11) 1.57 1.571 1.572 1.58
//       1.581 1.582 1.583 1.584 1.586 1.587
// dropped: 1.59 1.591 1.592 1.593 1.594 1.595 1.596 1.597 1.598 1.599 1.59(10) — the whole
//       abelian block. Rel is not abelian: its hom-sets are idempotent monoids under union,
//       so they have no additive inverses. It is only half-additive.
//       1.532 1.533 1.534 (proof of the slice lemma); 1.546 (proof: the choice-based
//       well-ordering construction); 1.573 1.574 (example: the primitive-recursive category P
//       and its splitting); 1.585 (LH: irrational rotation, coequalizers in Sh(Y)). Partial
//       drops: the LH / Sh(Y) / stalk-functor halves of 1.521 and 1.596 (LH); the group and
//       monoid illustrations of 1.514, the Z_2 + Z_3 counterexample of 1.56(10), the G-set
//       illustration of 1.57 (example).
#import "style.typ": *

= 1.5 Regular categories

#dt(
  ("1.51", [a subobject $B' arrow.r.tail B$ #D("allows") $f$ iff $f$ factors through it: #dia(
    node((1, 0), $A$), node((0, 1), $B'$), node((1, 1), $B$),
    edge((1, 0), (1, 1), $f$, "->"), edge((1, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), ">->"))]),

  ("", [with pullbacks: $B'$ allows $f$ iff $f^(\#)(B')$ is entire, all of $A$. A faithful pullback-preserving functor reflects allowance.]),

  ("", [the #D("image") of $f$ is the smallest subobject allowing $f$; a category #D("has images") if every morphism has one. Then $f: Sub(A) -> Sub(B)$ sends $A' arrow.r.tail A$ to the image of $A' arrow.r.tail A ->^f B$.]),

  ("", [with pullbacks too, the first adjoint pair of poset functions: $f(A') subset B'$ iff $A' subset f^(\#)(B')$. $f$ is the #D("left-adjoint") of $f^\#$, $f^\#$ the #D("right-adjoint") of $f$.]),

  ("1.511", [#Th[If $bold(A)$ has images and $T$ is faithful and preserves images, then $T$ reflects images.]]),

  ("1.512", [$A -> B$ is a #D("cover"), written $A ->> B$, if its image is entire — every monic it factors through is invertible: #sent(
    pan(vx((0, 0)), vx((0, 1)), edge((0, 0), (0, 1), marks: cover)),
    qbar[$forall$],
    pan(vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((1, 0), (1, 1), marks: cover), edge((1, 0), (0, 1), "->"),
      edge((0, 1), (1, 1), ">->")),
    qbar[$exists$],
    pan(vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((1, 0), (1, 1), marks: cover), edge((1, 0), (0, 1), "->"),
      edge((0, 1), (1, 1), ">->"), edge((1, 1), (0, 1), "->", shift: 5pt)),
  )]),

  ("", [covers are closed under composition and left cancellation ($A -> B -> C$ a cover forces $B -> C$ to be one); a monic cover is an isomorphism.]),

  ("1.513", [$\{A_i -> B\}$ #D("covers") if no proper subobject of $B$ allows all of them — the arc across the two arrows says the pair covers: #sent(
    pan(spacing: (8mm, 7mm), vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      edge((0.58, 0.58), (1.42, 0.58), "-", bend: 55deg, stroke: 0.4pt)),
    qbar[$forall$],
    pan(spacing: (8mm, 7mm), vx((0, 0)), vx((1, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((2, 0), (1, 0), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      edge((1, 0), (1, 1), ">->")),
    qbar[$exists$],
    pan(spacing: (8mm, 7mm), vx((0, 0)), vx((1, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((2, 0), (1, 0), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      edge((1, 0), (1, 1), ">->", shift: -3pt), edge((1, 1), (1, 0), "->", shift: -3pt)),
  )]),

  ("1.514", [$\{A_i -> B\}$ is #D("epic") if its members collectively cancel — a monic family in the opposite category. With equalizers, cover implies epic; the converse is a special property.]),

  ("1.52", [a #D("regular category") is a cartesian category with images in which pullbacks transfer covers — one sentence for both clauses, the right-hand vertex being the image of the right leg: #sent(
    qbar[$forall$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), marks: cover),
      ..pb((0, 0), (1, 0), (0, 1))),
    qbar[$exists$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)), vx((2, 0.5)),
      edge((0, 0), (1, 0), marks: cover), edge((0, 0), (0, 1), "->"),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), marks: cover),
      edge((1, 0), (2, 0.5), marks: cover), edge((2, 0.5), (1, 1), ">->"),
      ..pb((0, 0), (1, 0), (0, 1))),
  )]),

  ("", [a #D("pre-regular category") is cartesian, with or without images, and transfers covers by pullback — the strength at which the statements below hold. A #D("representation of pre-regular categories") preserves finite products, equalizers and covers, hence whatever images exist.]),

  ("1.521", [for small $bold(A)$, $cal(S)^bold(A)$ is regular and the evaluation functors are collectively faithful representations of regular categories.]),

  ("1.522", [the #D("support") $cal("Spt")(A)$ is the image of $A -> 1$; $A$ is #D("well-supported") if $cal("Spt")(A) = 1$ — pre-regularly, if $A -> 1$ covers.]),

  ("1.523", [$A$ is #D("well-pointed") if all of $1 -> A$ covers $A$: no proper subobject of $A$ allows every point. #sent(
    pan(vx((0, 1))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, 1)), edge((0, 0), (0, 1), ">->")),
    qbar[$exists$],
    pan(vx((0, 0)), vx((0, 1)), node((1, 1), $1$),
      edge((0, 0), (0, 1), ">->"), edge((1, 1), (0, 1), "->")),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, 1)), node((1, 1), $1$),
      edge((0, 0), (0, 1), ">->"), edge((1, 1), (0, 1), "->"),
      edge((1, 1), (0, 0), "->")),
    qbar[$exists$],
    pan(vx((0, 0)), vx((0, 1)),
      edge((0, 0), (0, 1), ">->", shift: -3pt), edge((0, 1), (0, 0), "->", shift: -3pt)),
  )]),

  ("1.524", [$P$ is #D("projective") if $(P, -)$ preserves covers — every $P -> B$ lifts through every cover: #sent(
    pan(vx((1, 0))),
    qbar[$forall$],
    pan(vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), marks: cover)),
    qbar[$exists$],
    pan(vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((1, 0), (1, 1), "->"), edge((0, 1), (1, 1), marks: cover),
      edge((1, 0), (0, 1), "->")),
  )
    Pre-regularly it suffices that every cover targeted at $P$ have a left inverse.]),

  ("1.525", [a pre-regular category is #D("capital") if every well-supported object is well-pointed. In a capital pre-regular category the terminator is projective.]),

  ("1.526", [so for capital pre-regular $bold(A)$ the functor $Gamma$ represented by $1$ is a representation of pre-regular categories.]),

  ("1.53", [#D("the slice lemma") factor $(B times -)$ as $bold(A) arrow.long^Delta bold(A) slash B arrow.long^Sigma bold(A)$, $Delta$ the diagonal functor [1.44], $Delta(1) = (B ->^1 B)$. #Th[If $bold(A)$ is (pre-)regular so is $bold(A) slash B$; $Delta$ is a representation of pre-regular categories; $Delta$ is faithful iff $B$ is well-supported.]]),

  ("1.531", [$Sigma: bold(A) slash B -> bold(A)$ preserves and reflects covers and pullbacks and carries factorizations back, so images in $bold(A)$ give images in $bold(A) slash B$.]),

  ("1.535", [#emph[Diagonal] also names the morphism $A -> Pi_I A$ with identity coordinates; $Delta$ is not that functor but is conjugate to it.]),
)

#dt(
  ("1.54", [#D("the capitalization lemma") let $cal(C)$ have small pre-regular categories as objects and faithful representations as morphisms.]),

  ("1.541", [$cal(C)$ meets the #emph[equivalence condition] if $bold(A) in cal(C)$ and an equivalence $bold(A) -> bold(B)$ force $bold(B), (bold(A) -> bold(B)) in cal(C)$; the #emph[slice condition] if $bold(A) in cal(C)$ and $B$ well-supported force $bold(A) slash B, Delta in cal(C)$; the #emph[union condition] if a #D("directed union") $bold(A) = union cal(F)$ of $cal(C)$-subcategories with $cal(C)$-inclusions has $bold(A), (bold(A)' subset bold(A)) in cal(C)$.]),

  ("1.542", [all three hold for the small pre-regular and the small regular categories, the slice condition being [1.53].]),

  ("1.543", [#Th[Under the three conditions every $bold(A) in cal(C)$ admits a capital $underline(underline(bold(A))) in cal(C)$ with $bold(A) -> underline(underline(bold(A)))$ faithful in $cal(C)$.]]),

  ("1.544", [to read $bold(A)$ inside $bold(A) slash B$, pass to the #D("inflation") $bold(A)'$ — objects finite sequences of objects, binary product concatenation — giving strict cancellation $B times A = B times A' ==> A = A'$, then replace the image of $Delta$ by $bold(A)$.]),

  ("1.545", [$bold(A) subset bold(A)^*$ is a #D("relative capitalization") if every proper $B' arrow.r.tail B$ of $bold(A)$, $B$ well-supported, fails to allow some $x: 1 -> B$ of $bold(A)^*$. Iterated union gives $underline(underline(bold(A)))$; each slicing step supplies $Delta B$ with its generic point, which $Delta B'$ cannot allow: #dia(
    node((0, 0), $B$), node((1, 0), $B times B$), node((0.5, 1), $B$),
    edge((0, 0), (1, 0), $chevron.l 1, 1 chevron.r$, "->"),
    edge((0, 0), (0.5, 1), $1$, "->", label-side: right), edge((1, 0), (0.5, 1), "->"))]),

  ("1.547", [choice-free variant: the rational category [1.48] of pairs $chevron.l A, F chevron.r$, $F$ a finite set of morphisms to distinct well-supported targets — a directed union of slices $bold(A) slash Pi U$.]),

  ("1.55", [#D("the henkin–lubkin theorem") #Th[Every small pre-regular category is faithfully represented in a power of the category of sets:] $T_B = bold(A) arrow.long^Delta bold(A) slash B -> underline(underline(bold(A) slash B)) arrow.long^Gamma cal(S)$; for regular $bold(A)$ the $\{T_U\}_(U subset 1)$ already suffice.]),

  ("1.551", [#Th[Every Horn sentence in the defining predicates of regular categories true for the category of sets is true for every regular category.]]),

  ("1.552", [a pre-regular category is #D("special") if every universally quantified sentence in the relevant predicates true for $cal(S)$ holds in it; the conditions of [1.47] stay necessary. #Th[Special iff $A -> U arrow.r.tail 1$ forces $A -> U$ or $U arrow.r.tail 1$ to be an isomorphism]]),

  ("", [equivalently: one-valued ($|pi_0 bold(A)| = 1$), or two-valued ($|pi_0 bold(A)| = 2$) with every object well-supported or isomorphic to $0$, the unique proper sub-terminator.]),
)

#dt(
  ("1.56", [tables $T_1$ on $A, B$ and $T_2$ on $B, C$: a table $T_(1 2)$ on $A, C$ is a #D("composition") if there exists #dia(
    node((2, 0), $T_(1 2)$), node((2, 1), $dot$), node((1, 2), $T_1$), node((3, 2), $T_2$),
    node((0, 3), $A$), node((2, 3), $B$), node((4, 3), $C$),
    edge((2, 1), (2, 0), marks: cover),
    edge((2, 1), (1, 2), "->"), edge((2, 1), (3, 2), "->"),
    edge((2, 0), (0, 3), "->"), edge((2, 0), (4, 3), "->"),
    edge((1, 2), (0, 3), "->"), edge((1, 2), (2, 3), "->"),
    edge((3, 2), (2, 3), "->"), edge((3, 2), (4, 3), "->"),
    ..pb((2, 1), (1, 2), (3, 2)))]),

  ("", [cartesian $+$ images builds one exactly so; shrinking either factor shrinks the composite, giving an order-preserving $Rel(A, B) times Rel(B, C) -> Rel(A, C)$. #emph[Caution:] not necessarily associative [1.569].]),

  ("1.561", [the #D("reciprocal") $R^circle.small$ of $R$ from $A$ to $B$ twists the columns: $R^(circle.small circle.small) = R$, $(R S)^circle.small = S^circle.small R^circle.small$. Reciprocation reverses composition, preserves the ordering.]),

  ("1.562", [$Rel(A, B) tilde.eq Sub(A times B)$ makes $Rel(A, B)$ a semi-lattice: $(R inter S) T subset R T inter S T$, $(R inter S)^circle.small = S^circle.small inter R^circle.small$.]),

  ("1.563", [#Th[$F$ preserving the cartesian structure and images induces $Rel(A, B) -> Rel(F A, F B)$ preserving composition, reciprocation and intersection; faithful $F$ reflects them.]]),

  ("", [#Th[Hence a Horn sentence on maps and relations — the regular predicates, plus composition, reciprocation and intersection — true of binary relations between sets is true in every regular category.]]),

  ("", [in particular $R(S T) = (R S)T$, and the #D("modular identity") $R S inter T subset (R inter T S^circle.small) S$. Every containment is an equation: $R subset S$ iff $R = R inter S$.]),

  ("1.564", [$Rel(bold(A))$ is the category of relations; the #D("graph") of $x$ is tabulated by #dia(
    node((1, 0), $A$), node((0, 1), $A$), node((2, 1), $B$),
    edge((1, 0), (0, 1), $1$, "->"), edge((1, 0), (2, 1), $x$, "->"))
    giving $bold(A) -> Rel(bold(A))$. Treat $bold(A)$ as a subcategory: #D("map") means a morphism of $Rel(bold(A))$ lying in $bold(A)$, and $chevron.l T; x, y chevron.r$ tabulates one iff $x$ is an isomorphism.]),

  ("", [$R$ is #D("entire") iff $1 subset R R^circle.small$, #D("simple") iff $R^circle.small R subset 1$. For $R$ tabulated by $x, y$: $x$ covers iff $R$ is entire, $x$ is monic iff $R$ is simple. So $R$ is a map iff entire and simple — hence as soon as every representation $F: bold(A) -> cal(S)$ makes $F(R)$ one.]),

  ("1.565", [a #D("pushout") is a pullback in the opposite category; the corner mark moves to the far vertex of the square, $C$.]),

  ("", [#Th[In a regular category a pullback of covers is a pushout] — all four edges then cover, the mediating map being the relation $(x^circle.small u) inter (y^circle.small v)$, a map because it is one in $cal(S)$: #sent(
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), marks: cover), edge((0, 0), (0, 1), marks: cover),
      edge((1, 0), (1, 1), marks: cover), edge((0, 1), (1, 1), marks: cover),
      ..pb((0, 0), (1, 0), (0, 1))),
    text(size: 7.5pt)[#emph[implies]],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), marks: cover), edge((0, 0), (0, 1), marks: cover),
      edge((1, 0), (1, 1), marks: cover), edge((0, 1), (1, 1), marks: cover),
      ..pb((0, 0), (1, 0), (0, 1)), ..pb((1, 1), (1, 0), (0, 1))),
  )]),

  ("1.566", [a #D("coequalizer") — an equalizer in the opposite category — is always a cover. #Th[In a regular category every cover is a coequalizer] — of its own level: #dia(
    vx((1, 0)), node((0, 1), $A$), node((2, 1), $A$), node((1, 2), $B$),
    edge((1, 0), (0, 1), $l$, "->", label-side: right), edge((1, 0), (2, 1), $r$, "->"),
    edge((0, 1), (1, 2), $x$, marks: cover, label-side: right),
    edge((2, 1), (1, 2), $x$, marks: cover, label-side: left),
    ..pb((1, 0), (0, 1), (2, 1)))]),

  ("1.567", [an endo-relation $E$ is an #D("equivalence relation") if $1 subset E$, $E^circle.small subset E$, $E E subset E$. Levels are equivalence relations: #dia(
    vx((1, 0)), node((0, 1), $A$), node((2, 1), $A$), node((1, 2), $B$),
    edge((1, 0), (0, 1), $l$, "->", label-side: right), edge((1, 0), (2, 1), $r$, "->"),
    edge((0, 1), (1, 2), $x$, "->", label-side: right),
    edge((2, 1), (1, 2), $x$, "->", label-side: left),
    ..pb((1, 0), (0, 1), (2, 1)))]),

  ("", [$E$ is #D("effective") if it is the level of some map; an #D("effective regular category") is one where every equivalence relation is effective. The metatheorem [1.551] extends to these, $cal(S)$ being effective.]),

  ("1.568", [covers out of $A$ are preordered by $f <= g$ iff $f$ factors through $g$: #dia(
    node((0, 0), $A$), node((1, 0), $B$), node((1, 1), $C$),
    edge((0, 0), (1, 0), $g$, marks: cover), edge((0, 0), (1, 1), $f$, marks: cover, label-side: right),
    edge((1, 0), (1, 1), "-->"))
    the associated poset is $cal("Quot")(A)$, of #D("quotient-objects") — not the dual of $Sub(A)$. By [1.566] a faithful order-reversing functor sends it to the poset of equivalence relations on $A$.]),

  ("1.569", [#Th[For $bold(A)$ cartesian with images, composition of relations is associative iff $bold(A)$ is regular] — $x$ covers iff $x^circle.small x = 1$; if $z$ fails to cover, $(y x^circle.small)x$ is not even a map.]),

  ("1.56(10)", [$x$ is a #D("constant morphism") if $y x = y' x$ for all $y, y': C -> A$. In a regular category its image is a sub-terminator.]),

  ("1.56(11)", [#Th[In a regular category an object is projective iff every entire relation out of it contains a map.]]),

  ("1.57", [an object is #D("choice") if every entire relation targeted at it contains a map. Every object is projective iff every object is choice; an #D("ac regular category") is a regular category with either — equivalently, a cartesian category where every morphism is a left-invertible followed by a monic.]),

  ("1.571", [if $bold(A)$ is cartesian and every $x: A -> B$ admits $e: A -> A$ with $e^2 = e$, $e x = x$, then $e$ and $x$ share a level and $bold(A)$ is AC regular — the image of $x$ appears as a subobject of $A$.]),

  ("1.572", [the category $bold(R)$ of recursive functions on $0, 1, 2, ..., omega$ is AC regular but not effective: a left inverse would choose representatives, forcing a recursively enumerable equivalence relation to be recursive.]),
)

#dt(
  ("1.58", [a #D("bicartesian category") is both cartesian and #D("cocartesian"), the latter meaning the opposite category is cartesian. Dual to a terminator is a #D("coterminator"), written $0$; dual to a product a #D("coproduct"), written $A + B$.]),

  ("", [in a cartesian category an object $0$ whose incoming morphisms are all isomorphisms is a coterminator, then called a #D("strict coterminator") — agreeing with the earlier $0$ [1.474, 1.552].]),

  ("1.581", [between regular cocartesian categories a representation of bicartesian categories is a representation of regular categories: it preserves coequalizers, hence covers [1.566].]),

  ("1.582", [for bicartesian $bold(A)$ regularity is a pair of Horn sentences in the bicartesian predicates — the image of $x$ is $A ->> C arrow.r.tail B$, with $A ->> C$ the coequalizer of the level of $x$.]),

  ("1.583", [effectiveness likewise: for $l, r$ tabulating an equivalence relation and $x$ their coequalizer, $E$ is effective iff #dia(
    node((1, 0), $E$), node((0, 1), $A$), node((2, 1), $A$), node((1, 2), $C$),
    edge((1, 0), (0, 1), $l$, "->"), edge((1, 0), (2, 1), $r$, "->"),
    edge((0, 1), (1, 2), $x$, "->", label-side: right),
    edge((2, 1), (1, 2), $x$, "->", label-side: left))
    is a pullback.]),

  ("1.584", [$bold(A) slash B$ is cocartesian and $Sigma$ a faithful representation of cocartesian categories.]),

  ("1.586", [for small $bold(A)$, $cal(S)^bold(A)$ is cocartesian with collectively faithful evaluation functors, hence effective regular.]),

  ("1.587", [no elementary characterization of the bicartesian categories obeying every Horn sentence true for $cal(S)$: $1 + NN arrow.long^binom(0, s) NN$ iso plus $NN -> 1$ a coequalizer of $1, s$ pins down $NN, 0, s$, then addition and multiplication; the equalizer of two polynomials is a coterminator iff the equation is unsolvable, so those Horn sentences encode the diophantine problems and are not recursively enumerable.]),
)
