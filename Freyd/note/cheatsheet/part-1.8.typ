// §1.8 ADJOINT FUNCTORS, GROTHENDIECK TOPOI, AND EXPONENTIAL CATEGORIES
// kept: 1.81 1.811 1.813 1.814 1.815 1.816 1.817 1.818 1.82 1.821 1.822 1.823 1.824 1.825
//       1.827 1.828 1.829 1.82(10) 1.83 1.831 1.832 1.833 1.834 1.835 1.836 1.837 1.838
//       1.839 1.83(10) 1.83(11) 1.84 1.842 1.843 1.844 1.845 1.846 1.847 1.85 1.852 1.853
//       1.854 1.856 1.857 1.858 1.859
// dropped: 1.812 (example: free groups over a forgetful functor); 1.841 (LH: Sh(Y)
//       subterminators, S^A representables); 1.851 (example: B^A in sets, posets, small
//       categories); 1.855 (example: the classical product of a B-indexed family of sets).
// dropped inside kept items: every BECAUSE (proof); the 1.813 'reflexion/reflexive' aside and
//       the 1.847 opening remark (diversion); the 1.814 abelianization / Stone-Cech /
//       field-of-quotients list and the non-full lattice-ideal case, the 1.816 torsion-group
//       and universal-covering-space cases, the 1.828 homotopy-category and COSCANECOF cases,
//       the 1.836 non-splitting-idempotent construction, the 1.838 ring-with-distinguished-
//       element and group-ring cases, the 1.839 compact-Hausdorff-group cardinality bounds,
//       the 1.856 poset construction (example); every Heyting clause — the 1.852 pointer to
//       the Heyting arrow, the 1.858 remark that the open elements form a Heyting algebra, and
//       the theorem that the closed elements of an L-T closure operation on a Heyting algebra
//       form an exponential ideal (Rel is no Heyting category, see part-1.7).
// note: the source carries no numbered item 1.826 — the two statements dual to 1.825 are
//       printed under 1.825 and are gathered into its row.
#import "style.typ": *

= 1.8 Adjoint functors, Grothendieck topoi, and exponential categories

#dt(
  ("1.81", [#D("adjoint pair of functors") $F: bold(A) -> bold(B)$, $G: bold(B) -> bold(A)$: some natural equivalence $(F A, B) tilde.eq (A, G B)$ exists, natural in both variables — as functors $bold(A)^circle.small times bold(B) -> cal(S)$. $F$ a #D("left-adjoint") of $G$, $G$ a #D("right-adjoint") of $F$.]),
)

#laws(
  [$F tack.l G$], [$(F A, B) tilde.eq (A, G B)$],
  [in posets], [$F A lt.eq B$ #h(0.4em) iff #h(0.4em) $A lt.eq G B$],
  [$bold(A)' subset bold(A)$ reflective], [$(overline(A), B) tilde.eq (A, B)$, #h(0.4em) $B in bold(A)'$],
  [$bold(A)' subset bold(A)$ coreflective], [$(B, G A) tilde.eq (B, A)$, #h(0.4em) $B in bold(A)'$],
  [adjoint on the right], [$(B, F A) tilde.eq (A, G B)$, #h(0.4em) $F, G$ contravariant],
  [adjoint on the left], [$(F A, B) tilde.eq (G B, A)$, #h(0.4em) $F, G$ contravariant],
)

#dt(
  ("1.811", [poset hom-sets have at most one element, so adjointness is $(F A, B) != nothing$ iff $(A, G B) != nothing$. Direct image is a left-adjoint of inverse image $f^\#$.]),

  ("1.813", [#D("reflective subcategory") $bold(A)' subset bold(A)$: the inclusion has a left-adjoint, whose values are #D("reflections"). Elementary form — every $A$ has $A -> overline(A)$, $overline(A) in bold(A)'$, and every $A -> B$, $B in bold(A)'$, factors by a unique $(overline(A) -> B) in bold(A)'$: #dia(
    node((0, 0.5), $A$), node((1, 0), $overline(A)$), node((1, 1), $B$),
    edge((0, 0.5), (1, 0), "->"), edge((0, 0.5), (1, 1), "->", label-side: right),
    edge((1, 0), (1, 1), "-->"))]),

  ("", [one $A -> overline(A)$ chosen per $A$ makes reflection a functor: $overline(x)$ is the unique map with #dia(
    node((0, 0), $A_1$), node((1, 0), $overline(A)_1$), node((0, 2), $A_2$), node((1, 2), $overline(A)_2$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 2), $x$, "->", label-side: right),
    edge((1, 0), (1, 2), $overline(x)$, "-->"), edge((0, 2), (1, 2), "->"))]),

  ("1.814", [most reflective subcategories are full; fullness is necessary and sufficient for the reflection functor to be idempotent.]),

  ("1.815", [#D("closure operation"): the reflection functor of a full reflective subcategory $P'$ of a poset $P$ — order-preserving, idempotent, inflationary. $x lt.eq y ==> overline(x) lt.eq overline(y)$, #h(0.3em) $overline(overline(x)) = overline(x)$, #h(0.3em) $x lt.eq overline(x)$. Conversely its values form a full reflective subcategory.]),

  ("1.816", [#D("coreflective") $bold(A)' subset bold(A)$: the inclusion has a right-adjoint.]),

  ("1.817", [$G$ has a left-adjoint $F$ iff every $(A, G(-))$ is representable, by $F A$; $F x$ is then the unique map with #dia(
    node((0, 0), $(A_2, G(-))$), node((1, 0), $(F A_2, -)$),
    node((0, 2), $(A_1, G(-))$), node((1, 2), $(F A_1, -)$),
    edge((0, 0), (1, 0), $tilde.eq$, "->"), edge((0, 0), (0, 2), $(x, G(-))$, "->", label-side: right),
    edge((1, 0), (1, 2), $(F x, -)$, "-->"), edge((0, 2), (1, 2), $tilde.eq$, "->"))]),

  ("1.818", [contravariant $F: bold(A) -> bold(B)$, $G: bold(B) -> bold(A)$ are #D("adjoint on the right") if $(B, F A) tilde.eq (A, G B)$ naturally, #D("adjoint on the left") if $(F A, B) tilde.eq (G B, A)$. Between posets, adjoint on the right $=$ Galois connection.]),

  ("", [adjoint on the right iff $F$ then $bold(B) -> bold(B)^circle.small$ is left-adjoint of $bold(B)^circle.small -> bold(B)$ then $G$; adjoint on the left iff $bold(A)^circle.small -> bold(A)$ then $F$ is left-adjoint of $G$ then $bold(A) -> bold(A)^circle.small$. Covariant theorems thus yield contravariant ones.]),

  ("1.82", [$bold(B)^bold(D)$: objects the functors $bold(D) -> bold(B)$, maps the natural transformations; $bold(D)$ usually small. #D("diagonal functor") $Delta: bold(B) -> bold(B)^bold(D)$: $B |-> $ the functor constant at $B$, $x |->$ the transformation constant at $x$.]),

  ("", [$bold(D) != nothing$: $Delta$ is an embedding, $bold(B)$ the subcategory of constant functors. $bold(D) = nothing$: $bold(B)^bold(D)$ is the terminator among categories, and $Delta$ has a right-adjoint iff $bold(B)$ has a terminator, a left-adjoint iff $bold(B)$ has a coterminator.]),

  ("1.821", [objects of $bold(B)^bold(D)$ are diagrams modelled on $bold(D)$, whose objects $i, j, k$ are the vertices. A map $Delta(B) -> D$ is a #emph[lower-bound]: a family $\{B -> D_i\}_(|bold(D)|)$ compatible with every $x: i -> j$ of $bold(D)$. #dia(
    node((0, 0.5), $B$), node((1, 0), $D_i$), node((1, 1), $D_j$),
    edge((0, 0.5), (1, 0), "->"), edge((0, 0.5), (1, 1), "->", label-side: right),
    edge((1, 0), (1, 1), $D_x$, "->", label-side: left))]),

  ("", [$D$ has a coreflection in $Delta$ iff it has a greatest lower-bound $\{L -> D_i\}$: every lower-bound has a unique map over it, all $i$. #dia(
    node((0, 0), $B$), node((1, 0), $L$), node((0.5, 1), $D_i$),
    edge((0, 0), (1, 0), "-->"), edge((0, 0), (0.5, 1), "->", label-side: right),
    edge((1, 0), (0.5, 1), "->")) Discrete $bold(D)$: compatibility evaporates, greatest lower-bound $=$ product diagram.]),

  ("1.822", [#D("limits") $lim D$: the values of a right-adjoint of $Delta: bold(B) -> bold(B)^bold(D)$. #D("colimits") $"colim" D$: the values of a left-adjoint — least upper bounds.]),

  ("", [$lim nothing$ is a terminator, $"colim" nothing$ a coterminator. For $bold(D)$ finitely presented by $dot.c arrows.rr dot.c$ (two objects, two non-identity maps) the right-adjoint delivers equalizers, the left-adjoint coequalizers.]),

  ("1.823", [#D("complete"): every small diagram has a limit. #D("cocomplete"): every small diagram has a colimit.]),

  ("1.824", [a family of monics $\{A_i arrow.r.tail A\}_I$ is a diagram modelled on $I'$ ($I$ discrete plus a terminator). Its limit is more than the intersection in $Sub(A)$: any $B -> A$, monic or not, factors through $lim A_i$ iff it factors through every $A_i$.]),

  ("1.825", [#Th[complete iff equalizers and arbitrary products]; dually #Th[cocomplete iff coequalizers and arbitrary coproducts]; and #Th[(co-)cartesian iff every finite diagram has a (co-)limit.]]),

  ("1.827", [#D("continuous"): preserves all small limits — from a complete source, iff it preserves equalizers and arbitrary products. #D("cocontinuous"): preserves all small colimits, from a cocomplete source iff it preserves coequalizers and arbitrary coproducts. A contravariant functor is continuous if it carries colimits to limits.]),

  ("1.828", [#emph[weak-] removes uniqueness. #D("weak-limit") of $D$: a compatible $\{W -> D_i\}$ admitting, for every compatible $\{B -> D_i\}$, at least one #dia(
    node((0, 0), $B$), node((1, 0), $W$), node((0.5, 1), $D_i$),
    edge((0, 0), (1, 0), "-->"), edge((0, 0), (0.5, 1), "->", label-side: right),
    edge((1, 0), (0.5, 1), "->")) #D("weakly-complete"): every small diagram has a weak-limit.]),

  ("", [a functor preserving one weak-limit of a diagram preserves them all; a continuous functor from a complete category preserves all weak-limits.]),

  ("1.829", [avoid "weakly continuous": #Th[a functor that preserves weak-limits preserves limits] — preserving weak-limits already forces preservation of monic families.]),

  ("1.82(10)", [#D("pre-limit") for $D: bold(D) -> bold(B)$: a #emph[set] of lower-bounds cofinal in the class of all of them — compatible families $\{\{P_j -> D_i\}_(|bold(D)|)\}_J$ such that every lower-bound $\{B -> D_i\}$ admits $j in J$ with #dia(
    node((0, 0), $B$), node((1, 0), $P_j$), node((0.5, 1), $D_i$),
    edge((0, 0), (1, 0), "-->"), edge((0, 0), (0.5, 1), "->", label-side: right),
    edge((1, 0), (0.5, 1), "->")) for all $i in |bold(D)|$.]),

  ("", [#D("pre-complete"): every small diagram has a pre-limit. Preserving pre-limits $==>$ preserving weak-limits $==>$ [1.829] preserving limits.]),

  ("1.83", [#D("pre-adjoint") for $A in bold(A)$, given $G: bold(B) -> bold(A)$: a set $\{A -> G(B_i)\}_I$ such that every $A -> G(B)$ admits $i in I$, $x: B_i -> B$ with #dia(
    node((0.5, 0), $A$), node((0, 1), $G(B_i)$), node((1, 1), $G(B)$),
    edge((0.5, 0), (0, 1), "->", label-side: right), edge((0.5, 0), (1, 1), "->"),
    edge((0, 1), (1, 1), $G(x)$, "-->", label-side: right)) Locally small $bold(A)$: a set $\{B_i\}_I$ in $bold(B)$ through one of which every $A -> G(B)$ factors this way.]),

  ("", [$bold(B)$ full, $G$ its inclusion: a pre-adjoint is a #D("pre-reflection") of $A$ — a set $\{B_i\}$ through one of which every map from $A$ to a $bold(B)$-object factors. #D("pre-adjoint functor"): every $A in bold(A)$ has a pre-adjoint.]),

  ("", [#D("the general adjoint functor theorem") #Th[If $bold(B)$ is locally small and complete then $G: bold(B) -> bold(A)$ has a left-adjoint iff it is continuous and pre-adjoint.]]),

  ("1.831", [#D("uniformly continuous") $G: bold(B) -> bold(A)$: for every small $D: bold(D) -> bold(B)$, $G$ carries the lower-bounds of $D$ to a cofinal family of lower-bounds of $bold(D) ->^D bold(B) ->^G bold(A)$ — every $\{A -> G(D_i)\}$ admits a lower-bound $\{B -> D_i\}$ and #dia(
    node((0, 0), $A$), node((1, 0), $G(B)$), node((0.5, 1), $G(D_i)$),
    edge((0, 0), (1, 0), "-->"), edge((0, 0), (0.5, 1), "->", label-side: right),
    edge((1, 0), (0.5, 1), "->")) for all $i$.]),

  ("", [such $G$ preserves pre-limits, hence weak-limits, hence limits. $bold(B)$ pre-complete: uniformly continuous $=$ preserves pre-limits. $bold(B)$ (weakly) complete: $=$ preserves (weak) limits.]),

  ("", [#D("the more general adjoint functor theorem") #Th[If $bold(B)$ is locally small and idempotents split in $bold(B)$ then $G$ has a left-adjoint iff it is uniformly continuous and pre-adjoint.]]),

  ("1.832", [#D("pointwise continuous") $T: bold(B) -> cal(S)$: for every small $D$, every lower-bound $\{1 -> T(D_i)\}$ in $cal(S)$ comes from a lower-bound $\{B -> D_i\}$ in $bold(B)$ and a point #dia(
    node((0, 0), $1$), node((1, 0), $T(B)$), node((0.5, 1), $T(D_i)$),
    edge((0, 0), (1, 0), "-->"), edge((0, 0), (0.5, 1), "->", label-side: right),
    edge((1, 0), (0.5, 1), "->")) $G$ is uniformly continuous iff every $(A, G(-))$ is pointwise continuous.]),

  ("1.833", [smallest subfunctor $T' subset T$ containing $\{x_i in T(B_i)\}_I$: $y in T'(B)$ iff $(T f)(x_i) = y$ for some $i in I$, $f: B_i -> B$. $T' = T$: $T$ is generated by the $x_i$. #D("petty-functor"): generated by some set of elements. $G$ is pre-adjoint iff every $(A, G(-))$ is petty.]),

  ("1.834", [#D("the general representability theorem") #Th[If $bold(B)$ is locally small and idempotents split in $bold(B)$ then $T: bold(B) -> cal(S)$ is representable iff it is a pointwise continuous petty-functor.]]),

  ("1.835", [#Th[A locally small category in which idempotents split has a coterminator iff it has a pre-coterminator and all small diagrams have lower-bounds.]]),

  ("1.836", [$hat(bold(B)) = "Split"(bold(B))$ formally splits every idempotent; $bold(B) -> hat(bold(B))$ is full, uniformly continuous and pre-adjoint, with a left-adjoint only where idempotents already split. #Th[A set-valued functor from a locally small category is a retract of a representable iff it is a pointwise continuous petty-functor.]]),

  ("1.837", [$bold(B)$ complete: $Delta: bold(B) -> bold(B)^bold(D)$ is continuous, and pre-adjoint iff all diagrams modelled on $bold(D)$ have pre-colimits. Hence #Th[a complete locally small category is cocomplete iff it is pre-cocomplete.]]),

  ("1.838", [#D("well-powered") $bold(B)$: $Sub(B)$ is a set for every $B$. Distinct maps have distinct graphs, so this implies local smallness.]),

  ("", [#emph[minimal] object: no proper subobject (an atom is not minimal — it has exactly one). #Th[Each object of a complete well-powered category has a unique minimal subobject.]]),

  ("", [minimal objects form an initial class $cal(M)$, pre-ordered ($f, g: M -> A$ have a non-proper equalizer, so $f = g$), every subset of which has a lower bound; an initial set exists iff $cal(M)$ has one. Any map between minimal objects is a cover.]),

  ("1.839", [pre-adjoints come from a #emph[cardinality function] $K$: objects to cardinals, with $K^\#(alpha)$ a set of isomorphism types for every cardinal $alpha$. For continuous $G: bold(B) -> bold(A)$, $bold(B)$ complete well-powered: $B$ is #emph[generated by $A$ through $G$] if $A -> G(B)$ factors through no $G(B') subset G(B)$ with $B' subset.neq B$.]),

  ("1.83(10)", [#D("cogenerating set") $\{C_i\}_I$: the $\{(-, C_i)\}_I$ are collectively an embedding — $f != g: A -> B$ gives $i in I$, $h: B -> C_i$ with $f h != g h$. In a complete category: iff every object is embeddable in a product of the $C_i$.]),

  ("", [#D("the special adjoint functor theorem") #Th[If $bold(B)$ is complete, well-powered and has a cogenerating set, and $bold(A)$ is locally small, then every continuous $G: bold(B) -> bold(A)$ has a left-adjoint.]]),

  ("", [#Th[A complete well-powered category with a cogenerating set has a coterminator] — the minimal subobject of $Pi_I C_i$.]),

  ("1.83(11)", [dually: #Th[if $bold(A)$ is cocomplete, well-co-powered and has a generating set, every cocontinuous functor from $bold(A)$ to a locally small category has a right-adjoint, and every contravariant continuous functor to a locally small category has an adjoint on the right.]]),

  ("1.84", [#D("giraud definition") of a Grothendieck topos (the first of four): locally small, cocomplete, effective regular, pullbacks preserve arbitrary unions, disjoint unions of objects exist, and there is a generating set. Such is a pre-topos and a logos.]),

  ("1.842", [#Th[If $bold(E)$ is a Grothendieck topos then the graphing functor $bold(E) -> Rel(bold(E))$ has a right-adjoint.] Via 1.843–6 and the special adjoint functor theorem; chapter 2 proves it directly.]),

  ("1.843", [#Th[A Grothendieck topos is well-powered]: a generating set $\{G_i\}_I$ is a basis, every subobject being an equalizer, so $B' subset B$ is fixed by $\{(G_i, B') subset (G_i, B)\}_I$. Hence #Th[$Rel(bold(E))$ is locally small.]]),

  ("", [comonics coincide with covers, and covers out of $A$ correspond to the equivalence relations on $A$: #Th[a Grothendieck topos is well-copowered.]]),

  ("1.844", [#Th[A Grothendieck topos is locally complete] — the union of $\{A_i arrow.r.tail A\}$ is the image of $Sigma A_i -> A$, $Sigma$ the disjoint union. Inverse images preserve arbitrary unions, so #Th[composition of relations distributes with arbitrary unions.]]),

  ("1.845", [coproduct $\{u_i: A_i -> S\}_I$: $u_i u_i^circle.small = 1$, $u_i u_j^circle.small = 0$ for $i != j$, $union.big u_i^circle.small u_i = 1_S$ — arbitrary coproducts are disjoint unions. #Th[A coproduct in $bold(E)$ remains a coproduct in $Rel(bold(E))$]: $R = union.big u_i^circle.small R_i$ is the unique relation with $u_i R = R_i$, all $i$.]),

  ("1.846", [#Th[A coequalizer in $bold(E)$ remains a coequalizer in $Rel(bold(E))$.] A Grothendieck topos is $bold(E)$-standard: the smallest equivalence relation containing $R$ is $union.big_(n = -oo)^oo R^n$, with $R^0 = 1$, $R^(-n) = (R^circle.small)^n$.]),

  ("1.847", [#rel[the ordering relation on the two-element ordered set is idempotent in $Rel(cal(S))$ but cannot be split.] So $Rel(bold(E))$ is not cocomplete, though disjoint unions give it coproducts — and, reciprocation making it self-dual, products too.]),

  ("1.85", [#D("exponential") $bold(A)$ with binary products (elsewhere: cartesian closed): every $A times -$ has a right-adjoint; equivalently every $(A times -, B)$ is representable, by an object $B^A$.]),

  ("", [an equivalence $eta: (-, B^A) -> (A times -, B)$ carries $1 in (B^A, B^A)$ to an #D("evaluation map") $e: A times B^A -> B$, and every $f: A times X -> B$ has a unique $lambda f: X -> B^A$ with #dia(
    node((0.5, 0), $A times X$), node((0, 1), $A times B^A$), node((1, 1), $B$),
    edge((0.5, 0), (0, 1), $1 times lambda f$, "-->", label-side: right),
    edge((0.5, 0), (1, 1), $f$, "->"), edge((0, 1), (1, 1), $e$, "->", label-side: right))]),

  ("", [in the diagrammatic language — the cross marking a product diagram: #sent(
    qbar[$forall$],
    pan(vx((0.5, 1.5)), vx((1.5, 1.5))),
    qbar[$exists$],
    pan(vx((0.5, 1.5)), vx((1.5, 1.5)), vx((1, 2)), vx((0, 3)),
      edge((1, 2), (0.5, 1.5), "->"), edge((1, 2), (1.5, 1.5), "->"),
      edge((1, 2), (0, 3), "->"), prodm((0.75, 2))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((1, 1)), vx((0.5, 1.5)), vx((1.5, 1.5)), vx((1, 2)), vx((0, 3)),
      edge((1, 1), (0, 0), "->"), edge((1, 1), (0.5, 1.5), "->"), edge((1, 1), (1.5, 1.5), "->"),
      edge((1, 2), (0.5, 1.5), "->"), edge((1, 2), (1.5, 1.5), "->"), edge((1, 2), (0, 3), "->"),
      prodm((0.75, 1)), prodm((0.75, 2))),
    qbar[$exists!$],
    pan(vx((0, 0)), vx((1, 1)), vx((0.5, 1.5)), vx((1.5, 1.5)), vx((1, 2)), vx((0, 3)),
      edge((1, 1), (0, 0), "->"), edge((1, 1), (0.5, 1.5), "->"), edge((1, 1), (1.5, 1.5), "->"),
      edge((1, 2), (0.5, 1.5), "->"), edge((1, 2), (1.5, 1.5), "->"), edge((1, 2), (0, 3), "->"),
      edge((0, 0), (0, 3), "->"), edge((1, 1), (1, 2), "->"),
      prodm((0.75, 1)), prodm((0.75, 2))),
  )]),

  ("1.852", [a poset is exponential iff it has binary intersections and every $a, b$ have $b^a$ with $x lt.eq b^a$ iff $a and x lt.eq b$.]),

  ("1.853", [$B^A$ is a bifunctor $bold(A)^circle.small times bold(A) -> bold(A)$, with $f^A = lambda(A times B_1^A ->^e B_1 ->^f B_2)$ and $B^g = lambda(A_1 times B^(A_2) ->^(g times 1) A_2 times B^(A_2) ->^e B)$: #dia(
    node((0, 0), $B_1^(A_2)$), node((1, 0), $B_2^(A_2)$),
    node((0, 2), $B_1^(A_1)$), node((1, 2), $B_2^(A_1)$),
    edge((0, 0), (1, 0), $f^(A_2)$, "->"), edge((0, 0), (0, 2), $B_1^g$, "->", label-side: right),
    edge((1, 0), (1, 2), $B_2^g$, "->"), edge((0, 2), (1, 2), $f^(A_1)$, "->", label-side: right))]),

  ("", [$(-)^A$ has the left-adjoint $A times -$, so preserves limits. Commutativity of products makes $B^((-))$ adjoint on the right to itself, $(A_1, B^(A_2)) tilde.eq (A_2 times A_1, B) tilde.eq (A_2, B^(A_1))$, hence continuous: colimits to limits.]),

  ("", [bicartesian exponential: $1^A tilde.eq 1$, $(B_1 times B_2)^A tilde.eq B_1^A times B_2^A$, $B^0 tilde.eq 1$, $B^(A_1 + A_2) tilde.eq B^(A_1) times B^(A_2)$, $(B^(A_1))^(A_2) tilde.eq B^(A_1 times A_2)$, $B^1 tilde.eq B$.]),

  ("", [$A times -$ has a right-adjoint, so preserves colimits: $A times (B_1 + B_2) tilde.eq (A times B_1) + (A times B_2)$, $A times 0 tilde.eq 0$ — the last equivalent to strictness of the coterminator.]),

  ("", [caution: $0^A$ is not $0$, and $0^0 tilde.eq 1$. $(-)^A$ preserves monics, so $0^A$ is a subterminator: the largest $U$ with $A times U = 0$.]),

  ("1.854", [in any category with binary products, $Sigma: bold(A) slash B -> bold(A)$ is a left-adjoint of $Delta: bold(A) -> bold(A) slash B$: $(Sigma f, C) tilde.eq (f, Delta C)$, with $f: A -> B$ a slice object and $Delta C$ the projection $B times C -> B$.]),

  ("", [a right-adjoint of $Delta$, where it exists, is written $Pi: bold(A) slash B -> bold(A)$: products of families in $bold(A)$ indexed on $B$.]),

  ("", [#Th[If $Pi: bold(A) slash B -> bold(A)$ exists then $A^B$ exists for every $A$]: $(B times -, A) tilde.eq (Sigma Delta(-), A) tilde.eq (Delta(-), Delta A) tilde.eq (-, Pi Delta(A))$.]),

  ("", [#Th[If $bold(A)$ is cartesian and exponential then $Delta: bold(A) -> bold(A) slash B$ has a right-adjoint $Pi$ for every $B$] — for $f: A -> B$ take the pullback #dia(
    node((0, 0), $Pi(f)$), node((1, 0), $A^B$), node((0, 1), $1$), node((1, 1), $B^B$),
    corner((0.32, 0.3)),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((1, 0), (1, 1), $f^B$, "->"), edge((0, 1), (1, 1), $lambda 1_B$, "->", label-side: right))]),

  ("", [$(C, Pi(f))$, as a subset of $(B times C, A)$, is then the set of $g$ with #dia(
    node((0, 0), $B times C$), node((1, 0), $A$), node((0.5, 1), $B$),
    edge((0, 0), (1, 0), $g$, "->"), edge((0, 0), (0.5, 1), $ell$, "->", label-side: right),
    edge((1, 0), (0.5, 1), $f$, "->")) which is exactly $(Delta(C), f)$.]),

  ("1.856", [the slice lemma fails for exponential categories: $bold(P)$ the posets, $3$ the three-element chain, $bold(P) slash 3$ not exponential. #Th[$bold(P) slash A$ is exponential iff $A$ contains no three-element chain.]]),

  ("1.857", [#Th[A full coreflective subcategory of an exponential category closed under binary products is exponential]: $(A times C, B) tilde.eq (C, B^A) tilde.eq (C, G(B^A))$ for the coreflection $G$.]),

  ("", [#D("exponential ideal"): a full $bold(A)' subset bold(A)$ with $B^A in bold(A)'$ for all $A in bold(A)$, $B in bold(A)'$. #D("replete subcategory"): closed under isomorphism type.]),

  ("", [#Th[A full replete reflective subcategory of an exponential category is an exponential ideal iff reflections preserve products] — from $(C, B^A) tilde.eq (overline(C), B^A)$, every $C -> B^A$ with $B in bold(A)'$ extends uniquely: #dia(
    node((0, 0), $C$), node((2, 0), $overline(C)$), node((1, 1), $B^A$),
    edge((0, 0), (2, 0), "->"), edge((0, 0), (1, 1), "->", label-side: right),
    edge((2, 0), (1, 1), "-->")) At $C = B^A$ this forces $C -> overline(C)$ to be an isomorphism.]),

  ("1.858", [#D("kuratowski interior operation") on a lattice: deflationary, idempotent, intersection-preserving — $x^bullet lt.eq x$, #h(0.3em) $x^bullet = (x^bullet)^bullet$, #h(0.3em) $(x and y)^bullet = x^bullet and y^bullet$. Its values are the #emph[open] elements.]),

  ("", [#D("lawvere-tierney closure operation") (L-T): inflationary, idempotent, intersection-preserving — $x lt.eq overline(x)$, #h(0.3em) $overline(overline(x)) = overline(x)$, #h(0.3em) $overline(overline(x) and overline(y)) = overline(x) and overline(y)$. Its values are the #emph[closed] elements.]),

  ("1.859", [#D("baseable") $B$, in a category with binary products: $B^A$ exists — i.e. $(A times -, B)$ is representable — for every $A$. The baseable objects form a full subcategory $bold(B)$, with $f^A: B_1^A -> B_2^A$ defined as if all objects were baseable.]),

  ("", [#Th[The inclusion $bold(B) -> bold(A)$ preserves equalizers]: the equalizer of $f^A, g^A$ is $B_0^A$. $bold(B)$ is itself always exponential, since $(B^A)^(A') tilde.eq B^(A times A')$.]),
)
