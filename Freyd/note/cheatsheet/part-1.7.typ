// §1.7 LOGOI
// kept: 1.7 1.71 1.711 1.712 1.714 1.73 1.731 1.732 1.733 1.734 1.735 1.74 1.742 1.743
//       1.744 1.745 1.746 1.74(10) 1.75 1.751 1.752 1.761 1.77 1.771 1.772 1.773 1.775
//       1.776 1.78 1.781 1.782 1.783 1.784 1.785 1.786 1.787
// dropped: 1.72 1.721 1.722 1.723 1.724 1.725 1.726 1.727 1.728 1.729 1.72(10) 1.72(11)
//       — the whole Heyting-algebra block (Heyting algebras, locales, ↔, negation, excluded
//       middle, the scone). Rel is no Heyting category: ∅ is at once initial and terminal, so
//       1 = 0 and the subobject logic collapses; its product is the disjoint sum, so it is not
//       cartesian closed; and its monics are the R whose direct image is injective on
//       subsets, so Sub(A) is not the powerset.
// dropped: 1.713 (S^A and Sh(Y) are locally complete: example); 1.741 1.747 1.748 1.753
//       1.754 1.755 1.76 (Sh(SR), Lazard sheaves on 2*, pullback of sheaves along a
//       continuous map, the construction of T: A -> Sh(X), micro-sheaves: LH); 1.749
//       (Wilson space, sobrification: LH — only the space 2* u 2^N survives, folded into
//       1.74(10)); 1.774 ((primitive) recursive pre-logoi: example); 1.777 (the dense
//       G-delta in the Stone space: proof).
// full-only: 1.73 1.731 1.732 (Fil(T) and the quotient A/F), the focal-logos sentence of
//       1.733, 1.734 1.735 1.74 1.742 1.743 1.744 1.745 1.746 1.74(10) 1.75 1.751 1.752
//       1.761 (focal representations, S^D, domination by trees, the freyd curve, the stone
//       representation theorem and its space) and 1.776 (its countable corollaries) — the
//       apparatus that carries a logos into sheaves, which says nothing about Rel: it needs
//       f^## and Rel has none. The Rel-focused build drops them; `--input full=1` keeps them.
//       Kept from the run: 1.733's coprime / connected, and 1.77 onwards (closures, R/S).
#import "style.typ": *

= 1.7 Logoi

#dt(
  ("1.7", [a #D("logos") is a regular category in which every $Sub(A)$ is a lattice and every $f^\#: Sub(B) -> Sub(A)$ has a right adjoint $f^(\#\#): Sub(A) -> Sub(B)$: $f^(\#)(B') subset A'$ iff $B' subset f^(\#\#)(A')$.]),

  ("", [restated: $f^(\#\#)(A')$ is the maximal subobject $B' subset B$ with $f^(\#)(B') subset A'$.]),

  ("1.71", [in $cal(S)$, $f^(\#\#)(A') = \{b in B | forall_a [f(a) = b => a in A']\}$. In a boolean pre-logos $f^(\#\#)(A') = not (f(not A'))$, since $f^\#$ preserves complements.]),

  ("1.711", [a logos is a pre-logos: $f^\#$ preserves every union that exists, since $f^(\#)(union B_i) subset A'$ iff every $f^(\#)(B_i) subset A'$.]),

  ("1.712", [#D("locally complete"): every $Sub(A)$ is a complete lattice. A locally complete regular category whose $f^\#$ preserve all unions is a logos, with $f^(\#\#)(A') = union \{B_i | f^(\#)(B_i) subset A'\}$.]),

  ("1.714", [the axiom drawn — the corner marks make the squares pullbacks, so each left vertex is the inverse image of the right one; the last panel returns $B'' subset B'$, so no $B''$ properly containing $B'$ has $f^(\#)(B'') subset A'$. #sent(
    qbar[$forall$],
    pan(vx((0, 2)), vx((0, 3)), vx((1, 3)),
      edge((0, 2), (0, 3), "->"), edge((0, 3), (1, 3), "->")),
    qbar[$exists$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 2)), vx((0, 3)), vx((1, 3)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 2), "->"), edge((1, 0), (1, 3), "->"),
      edge((0, 2), (0, 3), "->"), edge((0, 3), (1, 3), "->"), corner((0.2, 0.2))),
    qbar[$forall$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)), vx((0, 2)), vx((0, 3)), vx((1, 3)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"), edge((1, 0), (1, 1), "->"),
      edge((0, 1), (1, 1), "->"), edge((0, 1), (0, 2), "->"), edge((1, 1), (1, 3), "->"),
      edge((0, 2), (0, 3), "->"), edge((0, 3), (1, 3), "->"),
      corner((0.2, 0.2)), corner((0.2, 1.2))),
    qbar[$exists$],
    pan(vx((0, 0)), vx((1, 0)), vx((0, 1)), vx((1, 1)), vx((0, 2)), vx((0, 3)), vx((1, 3)),
      edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->"), edge((1, 0), (1, 1), "->"),
      edge((0, 1), (1, 1), "->"), edge((0, 1), (0, 2), "->"), edge((1, 1), (1, 3), "->"),
      edge((0, 2), (0, 3), "->"), edge((0, 3), (1, 3), "->"),
      edge((1, 1), (1, 0), "->", shift: -4pt),
      corner((0.2, 0.2)), corner((0.2, 1.2))),
  )]),

  ..fullonly(
    ("1.73", [for a representation of logoi $T: bold(A) -> bold(B)$, $cal("Fil")(T) subset Val_bold(A)$ collects the values $U$ with $T(U) = 1$; it is a filter.]),

    ("", [with $p_A: A -> 1$: $A' subset.neq A$ iff $p_A^(\#\#)(A') subset.neq 1$, and $T(A') subset.neq T(A)$ iff $p_A^(\#\#)(A') in.not cal("Fil")(T)$. #Th[$T$ is faithful iff $cal("Fil")(T)$ is trivial, $cal("Fil")(T) = \{1\}$.]]),

    ("1.731", [every filter $cal(F) subset Val_bold(A)$ gives a logos $bold(A) slash cal(F)$ and a representation $T_cal(F)$ with $cal("Fil")(T_cal(F)) = cal(F)$, universal among $T'$ with $cal(F) subset cal("Fil")(T')$: #dia(
      node((0, 0), $bold(A)$), node((2, 0), $bold(A) slash cal(F)$), node((1, 1), $bold(B)$),
      edge((0, 0), (2, 0), $T_cal(F)$, "->"),
      edge((0, 0), (1, 1), $T'$, "->", label-side: right),
      edge((2, 0), (1, 1), "-->"))
      the mediator is unique up to conjugation, and faithful iff $cal(F) = cal("Fil")(T')$.]),

    ("", [cartesian / regular / pre-logos $bold(A)$ give cartesian / regular / pre-logos $bold(A) slash cal(F)$.]),

    ("1.732", [logoi meet the capitalization lemma's union, equivalence and slice conditions: $Sigma$ matches $Sub_(bold(A) slash A)$ with $Sub_bold(A)(Sigma(\_))$ and preserves inverse images, so double-sharps descend to $bold(A) slash A$; $Delta$ preserves them because $A times (\_)$ does.]),
  ),

  ("1.733", [$A$ in a pre-logos is #D("coprime") if $(A, \_)$ preserves finite unions: any finite collection of subobjects of $A$ whose union is $A$ contains $A$. $A$ is #D("connected") if it has exactly two complemented subobjects.]),

  ..fullonly(
    ("", [a #D("focal logos") is a logos whose terminator is a coprime projective, i.e. one for which $Gamma = (1, \_)$ is a representation of pre-logoi. #Th[a positive pre-logos is focal iff its terminator is a connected projective.]]),
  ),

  ..fullonly(
    ("1.734", [$bold(A) -> bold(F)$ is a #D("focal representation") if $bold(F)$ is focal, i.e. $bold(A) -> bold(F) arrow.long^Gamma cal(S)$ is a representation of pre-logoi.]),

    ("", [#Th[any small (positive) logos has a small, collectively faithful family of focal representations.]]),

    ("", [#Th[a logos may be faithfully represented in a single focal logos iff its terminator is coprime.] ('Positive' is removable by [2.217, 2.343].)]),

    ("1.735", [capitalization raises no cardinality unless the category is finite, and positivization preserves infinite cardinalities. #Th[any countable (positive) logos has a countable, collectively faithful family of focal representations; a countable logos with coprime terminator is faithfully representable in a countable focal logos.]]),

    ("1.74", [#D("geometric representation theorem") #Th[every countable (positive) logos may be faithfully represented in a countable power of the logos of sheaves on the real line; with a coprime terminator, in that logos itself.]]),

    ("1.742", [#Th[for any small (positive) logos $bold(A)$ there is a small category $bold(D)$ and a faithful representation $bold(A) -> cal(S)^bold(D)$.] Objects of $bold(D)$: focal representations $bold(A) -> bold(F)$; morphisms: the focal $bold(F) -> bold(F)'$ under $bold(A)$. #dia(
      node((0, 1), $bold(A)$), node((1, 0), $bold(F)$), node((1, 2), $bold(F)'$),
      edge((0, 1), (1, 0), "->"), edge((0, 1), (1, 2), "->", label-side: right),
      edge((1, 0), (1, 2), "->"))]),

    ("", [$T(A)(bold(A) -> bold(F)) = bold(F)(1, A)$: #dia(
      node((0, 1), $bold(A)$), node((1.4, 0), $cal(S)^bold(D)$), node((2.8, 1), $cal(S)$),
      node((1.4, 2), $bold(F)$),
      edge((0, 1), (1.4, 0), $T$, "->"),
      edge((1.4, 0), (2.8, 1), $"ev"(bold(A) -> bold(F))$, "->"),
      edge((0, 1), (1.4, 2), "->", label-side: right),
      edge((1.4, 2), (2.8, 1), $Gamma$, "->", label-side: right))
      $bold(D)$ is enlarged until the morphisms out of each of its objects are collectively faithful.]),

    ("1.743", [$cal(S)^bold(D)$ is focal iff $bold(D)$ has a coterminator; e.g. when $bold(A)$ is focal.]),

    ("1.744", [a functor $bold(D)' -> bold(D)$ induces a representation of pre-logoi $cal(S)^bold(D) -> cal(S)^(bold(D)')$ by composition, faithful when the functor is onto on objects.]),

    ("", [$bold(D)'$ #D("dominates") $bold(D)$ if some $F: bold(D)' -> bold(D)$ is onto on objects and #D("left-full"): every $g: F(D) -> B$ in $bold(D)$ is $F(f)$ for some $f: D -> A$ in $bold(D)'$. Such $F$ need not be full.]),

    ("", [#Th[if $bold(D)'$ dominates $bold(D)$ then $cal(S)^bold(D)$ is faithfully representable in $cal(S)^(bold(D)')$ as a logos.]]),

    ("1.745", [#Th[every category (with a coterminator) is dominated by a (rooted) tree]: $bold(P)(bold(D))$, the finite nonempty paths of composable morphisms ordered by prolongation on the right, each sent to the target of its last map.]),

    ("1.746", [$bold(D)^+$, the tree of finite words of morphisms with the greedy functor $bold(D)^+ -> bold(P)(bold(D))$, is homogeneous and dominates $bold(D)$. #Th[every countable category with a coterminator is dominated by the binary tree $2^*$]: finite words on two symbols, ordered by prolongation on the right.]),

    ("1.74(10)", [the #D("freyd curve") maps $[-1 slash 2, 1 slash 2]$ onto $2^* union 2^NN$, the finite and infinite binary words with the updeals of the finite words as basic opens.]),

    ("", [write $x = sum_i a_i slash 3^i$ with $a_i = -1, 0, +1$; delete the zeros to leave $\{a_(n_i)\}_(i = 1)^L$, $L <= infinity$; send $x$ to $\{(-1)^(n_(i - 1)) a_(n_i)\}_(i = 1)^L$, taking $n_0 = 0$ and reading $2$ as $\{-1, +1\}$. Open, continuous and onto, which is what [1.74] needs.]),

    ("1.75", [#D("stone representation theorem") #Th[for every small (positive) logos $bold(A)$ there is a space $X$ and a faithful representation $bold(A) -> cal(S)h(X)$;] $X$ may be taken compact, totally disconnected and without isolated points, and for countable $bold(A)$ it may be taken to be the Cantor space, the rationals, or the irrationals.]),

    ("1.751", [an object is an #D("atom") if $0$ is its unique proper subobject. A logos is #D("atomically based") if its atoms form a basis, which forces it boolean; it is #D("atomless") if it has no atoms.]),

    ("", [the periodic power $Pi bold(A)$ (the periodic functions $NN -> bold(A)$) is a sublogos of $bold(A)^NN$ with the diagonal $bold(A) -> Pi bold(A)$ faithful; it is atomless for non-degenerate $bold(A)$ and stays positive and capital. So: positive capital atomless logoi.]),

    ("1.752", [$cal(B)$, the boolean algebra of complemented subterminators of $bold(A)$, is a basis, and atomless when $bold(A)$ is.]),

    ("", [the #D("stone space") $hat(cal(B))$ has the ultrafilters on $cal(B)$ as points and the $hat(U) = \{cal(F) | U in cal(F)\}$, $U in cal(B)$, as basic opens; it is compact and totally disconnected.]),

    ("", [a boolean algebra is isomorphic to the lattice of #D("clopens") (sets both open and closed) of its Stone space, so its atoms are the isolated points; $hat(cal(B))$ here has none.]),

    ("1.761", [$cal(F)$ closed under countable intersection: $bold(A) slash cal(F)$ inherits $bold(A)$'s countable unions and coproducts and $bold(A) -> bold(A) slash cal(F)$ preserves them; if closure fails at some size, so does preservation of unions of that size. Closed under arbitrary intersection: $U in cal(F)$ iff $inter.big cal(F) subset U$, and $bold(A) slash cal(F) = bold(A) slash (inter.big cal(F))$.]),
  ),

  ("1.77", [for a binary endo-relation $R$ in a regular category, the #D("transitive closure") $R^dagger$ is the minimal transitive relation containing $R$, and the #D("transitive-reflexive closure") $R^*$ the minimal transitive-reflexive one. In a pre-logos each exists iff the other does: $R^* = 1 union R^dagger$ and $R^dagger = R R^*$.]),

  ("", [a #D("transitive logos"), likewise a #D("transitive pre-logos"), is one in which every endo-relation has a transitive closure.]),

  ("1.771", [countable unions in every $Sub$, preserved by inverse images (as a logos forces): $R^dagger = R union R^2 union dots.c union R^n union dots.c$, transitive because composition then distributes with countable union.]),

  ("1.772", [a #D("σ-transitive logos") is a transitive logos in which $R^dagger$ is the least upper bound of the finite powers of $R$; a #D("σ-transitive pre-logos") wants that union stable: $R^dagger = union.big_(n = 1)^infinity R^n$, preserved under inverse images.]),

  ("", [σ-transitivity is an infinitary Horn sentence: $(R subset T) and (R^2 subset T) and dots.c$ implies $R^dagger subset T$; for pre-logoi, $f^(\#)(R^n) subset A'$ for all $n$ implies $f^(\#)(R^dagger) subset A'$. Its models are closed under products and substructures, and $cal(S)$ is σ-transitive, so representing transitive pre-logoi in a power of $cal(S)$ requires it.]),

  ("1.773", [#Th[every locally complete regular category is transitive] ($R^dagger$ is the intersection of all transitive relations containing $R$), but need not be σ-transitive: $R_1 = R$, $R_(alpha + 1) = R_alpha union (R_alpha)^2$, $R_beta = union.big_(alpha < beta) R_alpha$ at limits.]),

  ("1.775", [the #D("equivalence closure") $R^equiv$ is the minimal equivalence relation containing $R$; in a transitive pre-logos $R^equiv = (R union R^circle.small)^*$. An effective regular category has all equivalence closures iff it has coequalizers.]),

  ("", [a pre-logos is #D("e-standard") if every $R$ has an equivalence closure and $R^equiv$ is always the stable union of the finite powers of $R^circle.small union 1 union R$. σ-transitive implies E-standard, and E-standardness is necessary for a faithful family of set-valued representations preserving equivalence closures.]),

  ..fullonly(
    ("1.776", [#Th[every countable positive σ-transitive pre-logos is faithfully representable in a power of $cal(S)$; every countable positive σ-transitive logos in $cal(S)h(X)$ with $X$ the rationals or the irrationals; every countable E-standard bicartesian pre-topos in a power of $cal(S)$.]]),

    ("", [the last characterizes the countable bicartesian categories representable in a power of $cal(S)$. 'Positive' is removable [2.217, 2.343]; 'countable' is not.]),
  ),

  ("1.78", [for relations $R, S$ with a common target, $R slash S$ is the maximum relation $T$, if it exists, with $T S subset R$: $T subset R slash S$ iff $T S subset R$. The triangle only semi-commutes, as the containment sign says. #dia(
    node((0, 0), $bullet$), node((0, 2), $bullet$), node((2, 1), $bullet$),
    edge((0, 0), (2, 1), $R$, "->"),
    edge((0, 0), (0, 2), $R slash S$, "->", label-side: right),
    edge((0, 2), (2, 1), $S$, "->", label-side: right),
    node((0.8, 1), $subset$))]),

  ("1.781", [#rel[$x (R slash S) y$ iff $forall_z (y S z) => (x R z)$.]]),

  ("1.782", [for a map $f$ with the same target as $R$: $R slash f$ exists and equals $R f^circle.small$.]),

  ("1.783", [$(R slash S_1) slash S_2 = R slash (S_2 S_1)$: if the left side exists so does the right, and they agree.]),

  ("1.784", [#Th[in a logos $R slash S$ exists for every pair of relations with a common target.] Every $S$ is $l^circle.small r$, reducing the question to $R slash f^circle.small$; there $T f^circle.small = (1 times f)^(\#)(T)$, so $R slash f^circle.small = (1 times f)^(\#\#)(R)$.]),

  ("1.785", [conversely, read $A' arrow.r.tail A$ followed by the diagonal $chevron.l 1, 1 chevron.r: A -> A times A$ as a relation on $A$: if $A' slash f^circle.small$ exists then $f^(\#\#)(A') = 1_B inter (A' slash f^circle.small)^circle.small (A' slash f^circle.small)$.]),

  ("1.786", [for $R, S, T$ with a common target, $(R slash S)(S slash T) subset R slash T$; and $R slash R$ is transitive and reflexive.]),

  ("1.787", [$overline(R)$ is the minimum reflexive relation with $R overline(R) subset overline(R)$. #Th[in a logos $overline(R) = R^*$: if either exists so does the other, and they are equal.]]),
)
