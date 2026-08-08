// §1.6 PRE-LOGOI
// kept: 1.6 1.61 1.611 1.612 1.613 1.614 1.615 1.616 1.62 1.621 1.623 1.624 1.625 1.63
//       1.631 1.632 1.633 1.634 1.635 1.636 1.637 1.64 1.641 1.644 1.645 1.646 1.647
//       1.648 1.65 1.651 1.652 1.653 1.654 1.655 1.657 1.658 1.66 1.661 1.662
// dropped: 1.622 (example: Z_2, Z_3 inside S_3, plus the abelian-category aside);
//       1.626 (example: a distributive lattice has coproducts without positivity — its
//       [2.217] forward reference is kept in 1.635 and 1.65); 1.638 (example: S^A special
//       iff well-joined); 1.639 (example: recursive and primitive recursive functions);
//       1.642 (example: S^A boolean iff A a groupoid); 1.643 (LH: Sh(Y) boolean iff Y
//       discrete); 1.656 (diversion: the abelian analogue and its failure); 1.659 (LH:
//       decidable sheaves, germs of continuous functions); the topological-basis sentence
//       of 1.632 and the Diaconescu / G-set remarks closing 1.662 (example, diversion).
#import "style.typ": *

= 1.6 Pre-logoi

#dt(
  ("1.6", [A #D("pre-logos"): a regular category in which $Sub(A)$ is a lattice, not just a semi-lattice, for each $A$, and $f^\#: Sub(B) -> Sub(A)$ is a lattice homomorphism for each $f: A -> B$.]),
  ("", [Elementary form: each pair of subobjects has a union, preserved under inverse image.]),
  ("", [Equivalently: a cartesian category with images in which pullbacks transfer finite covers. For a cover $\{B_i -> B\}_(i = 1)^n$ and a map $A -> B$ there exist #dia(
    node((0, 0), $A_i$), node((1, 0), $A$), node((0, 1), $B_i$), node((1, 1), $B$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), "->"), edge((1, 0), (1, 1), "->"),
  ) $i = 1, ..., n$, with $\{A_i -> A\}_(i = 1)^n$ a cover. Their existence forces the pullback squares to be such.]),
  ("1.61", [$0$ = the minimal subobject of $1$; $p_A^\# (0)$ = the minimal subobject of $A$. #Th[Any morphism to $0$ is an isomorphism.] Each $A$ receives exactly one $0 -> A$: $0$ is a coterminator.]),
  ("", [A pre-logos is degenerate iff it is one-valued, $0 tilde.eq 1$.]),
  ("1.611", [Hence a pre-logos is a cartesian category with images and three sentences. First, $0$ exists and every morphism to it is invertible: #sent(
    qbar[$exists$],
    pan(vx((0, 1))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, 1)), edge((0, 0), (0, 1), "->")),
    qbar[$exists$],
    pan(vx((0, 0)), vx((0, 1)),
      edge((0, 0), (0, 1), "->", shift: -3pt), edge((0, 1), (0, 0), "->", shift: -3pt)),
  )]),
  ("", [second, any two morphisms with a common target have a union — the arc says the pair covers it: #sent(
    qbar[$forall$],
    pan(spacing: (8mm, 7mm), vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->")),
    qbar[$exists$],
    pan(spacing: (8mm, 7mm), vx((0, 0)), vx((1, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((2, 0), (1, 0), "->"),
      edge((0.5, 0), (1.5, 0), "-", bend: 65deg, stroke: 0.4pt),
      edge((1, 0), (1, 1), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->")),
  )]),
  ("", [third, inverse image preserves unions — the squares of 1.6 again, now with both pairs covering: #sent(
    qbar[$forall$],
    pan(vx((1, -0.4)), vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((1, -0.4), (1, 1), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      edge((0.58, 0.58), (1.42, 0.58), "-", bend: 55deg, stroke: 0.4pt)),
    qbar[$exists$],
    pan(vx((0, -1)), vx((2, -1)), vx((1, -0.4)), vx((0, 0)), vx((2, 0)), vx((1, 1)),
      edge((0, -1), (0, 0), "->"), edge((2, -1), (2, 0), "->"),
      edge((0, -1), (1, -0.4), "->"), edge((2, -1), (1, -0.4), "->"),
      edge((0.58, -0.65), (1.42, -0.65), "-", bend: 55deg, stroke: 0.4pt),
      edge((1, -0.4), (1, 1), "->"),
      edge((0, 0), (1, 1), "->"), edge((2, 0), (1, 1), "->"),
      edge((0.58, 0.58), (1.42, 0.58), "-", bend: 55deg, stroke: 0.4pt)),
  )]),
  ("1.612", [For monic $f: A arrow.r.tail B$ the inverse image sends $B' subset B$ to $A inter B'$.]),
  ("", [Every such $f^\#$ preserves binary unions iff $Sub(B)$ is a #D("distributive lattice"): $A inter (B_1 union B_2) = (A inter B_1) union (A inter B_2)$.]),
  ("1.613", [A poset viewed as a category is cartesian iff it is a semi-lattice (intersections are products, equalizers hold by default); a semi-lattice is regular, the only covers being identities. A semi-lattice is a pre-logos iff it is a distributive lattice.]),
  ("1.614", [A #D("representation of pre-logoi"): a functor between pre-logoi preserving the cartesian structure, images, and finite unions, the empty union included.]),
  ("1.615", [In a bicartesian category with images the union of $x_1: A_1 arrow.r.tail A$, $x_2: A_2 -> A$ is the image of $vec(x_1, x_2): A_1 + A_2 -> A$.]),
  ("", [Building on [1.582], a finite set of Horn sentences in the bicartesian predicates holds for a bicartesian category iff it is a pre-logos.]),
  ("1.616", [$Rel(A, B) tilde.eq Sub(A times B)$ is a distributive lattice, so relations carry $R union S$.]),
)

#laws(
  [$Sub(A times B)$ distributive], $R inter (S union T) = (R inter S) union (R inter T)$,
  [reciprocation], $(R union S)^circle.small = S^circle.small union R^circle.small$,
  [$y S = (y times 1)^\# (S)$, inverse images], $y(S union T) = y S union y T$,
  [$x^circle.small (y S) = (x times 1)(y S)$, direct images], $R(S union T) = R S union R T$,
  [reciprocate the line above], $(S union T)R' = S R' union T R'$,
)

#dt(
  ("1.62", [#D("pasting lemma") #Th[For subobjects $A_1, A_2$ of $A$ in a pre-logos, #dia(
    node((0, 0), $A_1 inter A_2$), node((1, 0), $A_2$), node((0, 1), $A_1$), node((1, 1), $A_1 union A_2$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), "->"), edge((1, 0), (1, 1), "->"),
  ) is a pushout] — the mediating map out of $A_1 union A_2$ is unique because $A_1, A_2$ cover it.]),
  ("", [Restated: a pullback whose two morphisms into the lower right corner cover is a pushout. #sent(
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), ">->"),
      edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), ">->"),
      edge((0.6, 1), (1, 0.6), "-", bend: 55deg, stroke: 0.4pt),
      ..pb((0, 0), (1, 0), (0, 1))),
    text(size: 7.5pt)[#emph[implies]],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
      edge((0, 1), (1, 1), "->"), edge((1, 0), (1, 1), "->"),
      ..pb((1, 1), (0, 1), (1, 0))),
  )]),
  ("1.621", [#Th[If $A_1 inter A_2 = 0$ and $A_1 union A_2 = A$ then $A$ is a coproduct of $A_1, A_2$] — the special case of the square above.]),
  ("1.623", [A #D("positive pre-logos"): a pre-logos in which every pair $A, B$ admits #dia(
    node((0, 0), $0$), node((1, 0), $B$), node((0, 1), $A$), node((1, 1), $C$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), ">->"),
    ..pb((0, 0), (1, 0), (0, 1)),
  ) Choosing $C$ with $A union B = C$, a positive pre-logos has coproducts.]),
  ("1.624", [In a positive pre-logos any $f: A -> B_1 + B_2$ yields a decomposition, $A_i = f^\# (B_i)$: #dia(
    node((0, 0), $A$), node((1, 0), $A_1 + A_2$), node((1, 1), $B_1 + B_2$),
    edge((0, 0), (1, 0), $tilde$, "->"), edge((1, 0), (1, 1), $f_1 + f_2$, "->", label-side: left),
    edge((0, 0), (1, 1), $f$, "->", label-side: right),
  )]),
  ("1.625", [For $bold(A), bold(B)$ positive pre-logoi and $T: bold(A) -> bold(B)$ a representation of regular categories: #Th[$T$ is a representation of pre-logoi iff it preserves disjoint unions.]]),
  ("1.63", [$Sigma: bold(A) slash B -> bold(A)$ yields $Sub_(bold(A) slash B)(-) tilde.eq Sub_bold(A) (Sigma(-))$, respecting inverse images when $bold(A)$ has pullbacks, and unions in $bold(A)$ give unions in $bold(A) slash B$.]),
  ("", [#Th[If $bold(A)$ is a (positive) pre-logos so is $bold(A) slash B$], and $Delta: bold(A) -> bold(A) slash B$ is a representation of pre-logoi.]),
  ("", [The capitalization lemma [1.543] applies: #Th[any (positive) pre-logos is faithfully representable in a capital (positive) pre-logos.]]),
  ("1.631", [$A_1 subset A$ is a #D("complemented subobject") if some $A_2 subset A$ has $A_1 inter A_2 = 0$, $A_1 union A_2 = A$ [1.621]; distributivity of $Sub(A)$ makes $A_2$ unique.]),
  ("", [In a positive pre-logos a complemented subobject of a projective object is projective. With [1.525]: #Th[the #D("complemented subterminators") — complemented subobjects of $1$ — in a capital pre-logos are projective.]]),
  ("1.632", [$cal(G) subset |bold(A)|$ is a #D("generating set") if $\{(G, -)\}_(G in cal(G))$ collectively yields an embedding; $cal(B) subset |bold(A)|$ is a #D("basis") if $\{(B, -)\}_(B in cal(B))$ is collectively faithful. Both elementary.]),
  ("", [For cartesian $bold(A)$, $cal(B)$ is a basis iff every proper $A' arrow.r.tail A$ admits #dia(
    node((0, 0), $B'$), node((1, 0), $B$), node((0, 1), $A'$), node((1, 1), $A$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), "->"),
    ..pb((0, 0), (1, 0), (0, 1)),
  ) with $B in cal(B)$ and $B' arrow.r.tail B$ proper [1.442].]),
  ("1.633", [#Th[A positive pre-logos is capital iff the complemented subterminators are projective and form a basis.]]),
  ("1.634", [$cal(F) subset P$ is a #D("pre-filter") if non-empty and any $x, y in cal(F)$ have $z in cal(F)$ with $z <= x$, $z <= y$; a #D("filter") if also an updeal.]),
  ("", [For $cal(F)$ a pre-filter in $Val_bold(A)$: $T_cal(F)(A)$ has elements named by $x: U -> A$, $U in cal(F)$, with $x$ and $y: V -> A$ naming the same element when #dia(
    node((0, 0), $W$), node((1, 0), $U$), node((0, 1), $V$), node((1, 1), $A$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), $y$, "->", label-side: right), edge((1, 0), (1, 1), $x$, "->", label-side: left),
  ) for some $W in cal(F)$, $W subset U$, $W subset V$.]),
  ("", [$T_cal(F)$ preserves finite products and equalizers; it preserves covers when the elements of $cal(F)$ are projective.]),
  ("", [#Th[In a pre-logos $T_cal(F)$ preserves disjoint unions iff $0 in.not cal(F)$, and $U_1 + U_2 in cal(F)$ implies $U_1 in cal(F)$ or $U_2 in cal(F)$.]]),
  ("1.635", [#D("the representation theorem for pre-logoi") #Th[Every small positive pre-logos is faithfully representable in a power of the category of sets.] 'Positive' is removable, every pre-logos being faithfully representable in a positive one [2.217].]),
  ("", [In a capital positive pre-logos a representative set $cal(B)$ of complemented subterminators, as a sublattice of $Sub$, is distributive with every element complemented — a #D("boolean algebra").]),
  ("", [Every pre-filter $cal(F) subset cal(B)$ extends, by the axiom of choice, to an #D("ultra-filter") $overline(cal(F))$: a maximal pre-filter with $0 in.not overline(cal(F))$, necessarily a filter.]),
  ("", [#Th[For $overline(cal(F))$ an ultra-filter, $T_overline(cal(F))$ is a representation of pre-logoi.] Collectively faithful, because $cal(B)$ is a basis.]),
  ("1.636", [#Th[Any Horn sentence in the predicates of pre-logoi true for the category of sets is true for all positive pre-logoi] — 'positive' again removable [2.217].]),
  ("1.637", [A #emph[special] pre-logos satisfies every universal sentence in the predicates of pre-logoi satisfied by $cal(S)$. A pre-logos is a special regular category iff two-valued.]),
  ("", [#Th[A pre-logos is special iff $(A' times B) union (A times B')$ is a proper subobject of $A times B$ for every pair of proper $A' subset A$, $B' subset B$.]]),
  ("1.64", [A #D("boolean pre-logos"): a pre-logos in which $Sub(A)$ is a boolean algebra for all $A$. $Sub(A)$ being distributive, only complements need be required, and they are then unique: #sent(
    qbar[$forall$],
    pan(vx((0, 0)), vx((0, 1)), edge((0, 0), (0, 1), ">->")),
    qbar[$exists$],
    pan(node((0, 0), $0$), vx((1, 0)), vx((0, 1)), vx((1, 1)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"),
      edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), ">->"),
      edge((0.6, 1), (1, 0.6), "-", bend: 55deg, stroke: 0.4pt),
      ..pb((0, 0), (1, 0), (0, 1))),
  )]),
  ("1.641", [#Th[A representation of pre-logoi between boolean pre-logoi preserves the boolean structure automatically]: each $Sub(A) -> Sub(T A)$ preserves complements and is a map of boolean algebras.]),
  ("1.644", [Any power of $cal(S)$ is a boolean capital positive pre-logos; confuse $Val_(cal(S)^I)$ with the power set of $I$.]),
  ("", [For an ultra-filter $cal(F) subset Val_(cal(S)^I)$, $T_cal(F)$ is an #D("ultra-product functor") and the composite an #D("ultra-power functor"). Both are representations of boolean pre-logoi: $cal(S) arrow.long^Delta cal(S)^I arrow.long^(T_cal(F)) cal(S)$.]),
  ("1.645", [For $T: bold(A) -> bold(B)$ a representation of boolean pre-logoi: $cal("Ker")(T) = \{U subset 1 | T(U) = 0\}$, the values killed by $T$; $cal("prop")(A' subset A)$, the #emph[properness], is the support of the complement of $A'$.]),
  ("", [$A' subset A$ is proper iff $cal("prop")(A' subset A) != 0$; $T A' subset T A$ is proper iff $cal("prop")(A' subset A) subset.not cal("Ker")(T)$; $T$ is faithful iff $cal("Ker")(T) = 0$.]),
  ("", [$1 in cal("Ker")(T)$ iff $bold(B)$ is degenerate, so $bold(A)$ two-valued and $bold(B)$ non-degenerate forces $T$ faithful — every ultra-power functor is faithful. $cal("Ker")(T_cal(F))$ is the complement of $cal(F)$ in $Val_bold(A)$.]),
  ("1.646", [Two propositions with the same proof: #Th[every small special cartesian category, and every small special positive pre-logos, is faithfully representable in the category of sets.]]),
  ("1.647", [For proper $A_i subset B_i$ with complement $A'_i$ $(i = 1, 2)$, the complement of $(A_1 times B_2) union (B_1 times A_2)$ in $B_1 times B_2$ is $A'_1 times A'_2$. Hence, by [1.637], #Th[a boolean pre-logos is special iff it is two-valued.]]),
  ("1.648", [If an ultra-power functor preserves coequalizers — one built from $NN, 0, s$ [1.587] suffices — then $cal(F)$ meets every countable partitioning of $I$: such an ultra-filter is a #D("complete measure").]),
  ("", [The #D("atomic measures") are those of the form $\{j | i <= j\}$; for $cal(F)$ atomic, $T_cal(F)$ is conjugate to a projection and the ultra-power functor to the identity functor.]),
)

#dt(
  ("1.65", [A #D("pre-topos"): an effective positive pre-logos. Every pre-logos is faithfully represented in a pre-topos [2.217].]),
  ("1.651", [#D("the amalgamation lemma") #Th[Monics with a common source $x: A arrow.r.tail B$, $y: A arrow.r.tail C$ in a pre-topos extend to #dia(
    node((0, 0), $A$), node((1, 0), $C$), node((0, 1), $B$), node((1, 1), $D$),
    edge((0, 0), (1, 0), $y$, ">->"), edge((0, 0), (0, 1), $x$, ">->", label-side: right),
    edge((0, 1), (1, 1), $overline(y)$, ">->", label-side: right), edge((1, 0), (1, 1), $overline(x)$, ">->"),
    ..pb((0, 0), (1, 0), (0, 1)), ..pb((1, 1), (0, 1), (1, 0)),
  )] — take $D$ with level $E = l^circle.small x^circle.small y r union 1 union r^circle.small y^circle.small x l$ on $B + C$, for $l, r$ the coproduct injections. The square is a pullback, hence by [1.62] a pushout.]),
  ("1.652", [#Th[In a pre-topos covers coincide with epics and monics coincide with cocovers] — every monic is an equalizer, so the image of an epic is entire.]),
  ("1.653", [#Th[For $A -> B$ and monic $y: A arrow.r.tail C$ in a pre-topos there exist #dia(
    node((0, 0), $A$), node((1, 0), $C$), node((0, 1), $B$), node((1, 1), $D$),
    edge((0, 0), (1, 0), $y$, ">->"), edge((0, 0), (0, 1), "->"),
    edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), "->"),
    ..pb((0, 0), (1, 0), (0, 1)), ..pb((1, 1), (0, 1), (1, 0)),
  )] — factor $A -> B$ through its image and stack the square with [1.651].]),
  ("1.654", [A pre-topos need not be cocartesian. If it is, the last two sections show its opposite category is regular.]),
  ("1.655", [#Th[If $bold(A), bold(B)$ are pre-topoi and $T: bold(A) -> bold(B)$ preserves $0$, pushouts, finite products and monics, then $T$ is a bicartesian representation.]]),
  ("1.657", [In an effective regular category, for $R$ tabulated by #dia(
    node((1, 0), $T$), node((0, 1), $A$), node((2, 1), $A$),
    edge((1, 0), (0, 1), $x$, "->", label-side: right), edge((1, 0), (2, 1), $y$, "->"),
    ..pb((1, 0), (0, 1), (2, 1)),
  ) and $f: A -> B$ a coequalizer of $x, y$: $f f^circle.small$ is the minimal equivalence relation containing $R$.]),
  ("", [#Th[A pre-topos is cocartesian iff for every endo-relation $R$ there is a minimal equivalence relation containing $R$. A functor between bicartesian pre-topoi preserves the bicartesian structure iff it is a representation of pre-logoi preserving minimal equivalence relations.]]),
  ("1.658", [An object $A$ in a pre-logos is #D("decidable") if the diagonal $chevron.l 1, 1 chevron.r: A arrow.r.tail A times A$ has a complement. #Th[Every object of a pre-topos is decidable iff the pre-topos is boolean] — pullbacks of complemented subobjects are complemented.]),
  ("1.66", [Choice objects [1.57]: #Th[in any regular category a subobject of a choice object is choice, and a quotient of a choice object is choice] — a quotient $x: A -> B$ [1.568] is also a subobject of $A$, via a map contained in $x^circle.small$.]),
  ("1.661", [#Th[In a regular category finite products of choice objects are choice] — an entire relation targeted at a terminator is already a map.]),
  ("1.662", [#Th[In a pre-topos: (1) binary coproducts of choice objects are choice; (2) $1 + 1$ is choice; (3) the pre-topos is boolean — are equivalent.]]),
  ("", [(2) restated by $Rel(B, 1 + 1) tilde.eq Sub(B) times Sub(B)$: an entire relation $B -> 1 + 1$ is a pair of subobjects covering $B$, a map $B -> 1 + 1$ a partition of $B$ — so $X union Y = B$ in $Sub(B)$ gives $X' subset X$, $Y' subset Y$ with $X' union Y' = B$, $X' inter Y' = 0$.]),
)
