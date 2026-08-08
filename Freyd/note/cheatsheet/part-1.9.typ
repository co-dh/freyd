// §1.9 TOPOI
// kept: 1.9 1.911 1.912 1.913 1.914 1.919 1.91(10) 1.92 1.921 1.922 1.923 1.926 1.93
//       1.931 1.932 1.933 1.934 1.935 1.94 1.941 1.942 1.943 1.944 1.945 1.946 1.947
//       1.949 1.94(10) 1.95 1.951 1.952 1.954 1.955 1.961 1.962 1.963 1.964 1.965
//       1.966 1.967 1.968 1.969 1.96(11) 1.971 1.972 1.973 1.974 1.976 1.977 1.979
//       1.98 1.981 1.983 1.984 1.985 1.986 1.987 1.988 1.989 1.98(10) 1.98(11)
//       1.98(12) 1.98(13) 1.98(14)
// headings carrying no statement of their own: 1.96, 1.97
// dropped: 1.915 (example: S^G); 1.916 (example: N-sets, monoid Omega); 1.917 (example:
//       S^A power-objects, "no use"); 1.918 (LH); 1.924 1.925 (example: S^A exponentials,
//       the N-set A^A); 1.948 (example: G-sets); 1.953 (example: the S computation of
//       A/E and A+B); 1.96(10) (example: three counterexample topoi); 1.975 (diversion:
//       "a left inverse exists locally"); 1.978 (LH: etendue is sheaf-theoretic);
//       1.982 (example: recursion in S).
#import "style.typ": *

= 1.9 Topoi

#dt(
  ("1.9", [Any category with pullbacks composes a map with a relation: for $f: A -> B$ and a table $chevron.l R; b, c chevron.r$ on $B, C$, pull $b$ back along $f$. #dia(
    node((0, 0), $R'$), node((1, 0), $R$), node((2, 0), $C$), node((0, 1), $A$), node((1, 1), $B$),
    edge((0, 0), (1, 0), "->"), edge((1, 0), (2, 0), $c$, "->"),
    edge((0, 0), (0, 1), "->", label-side: right), edge((1, 0), (1, 1), $b$, "->"),
    edge((0, 1), (1, 1), $f$, "->"), corner((0.2, 0.28)),
  )
  $R' -> A$, $R' -> C$ is still a monic pair; that table is $f R$. No regularity needed, and $g(f R) = (g f) R$.]),

  ("", [$U$ targeted at $C$ is a #D("universal relation") if every relation $R$ targeted at $C$ is uniquely $f U$; that $f$ is written $Lambda R$. A #D("power-object") of $C$, written $[C]$, is the source of a universal relation, itself written $eps subset [C] times C$. #dia(
    node((0, 0), $R$), node((1, 0), $eps$), node((2, 0), $C$), node((0, 1), $A$), node((1, 1), $[C]$),
    edge((0, 0), (1, 0), "->"), edge((1, 0), (2, 0), "->"),
    edge((0, 0), (0, 1), "->", label-side: right), edge((1, 0), (1, 1), "->"),
    edge((0, 1), (1, 1), $Lambda R$, "-->"), corner((0.2, 0.28)),
  )]),

  ("", [A #D("topos") is a cartesian category in which each object has a power-object. #Th[A topos is a positive effective transitive logos], hence a pre-topos.]),

  ("1.911", [$Rel(-, B)$ is contravariant set-valued on any category with pullbacks, $Rel(f, B)$ sending $R$ to $f R$. $[B]$ exists iff $Rel(-, B) tilde.eq (-, [B])$. A regular $bold(A)$ is a topos iff the graphing functor $bold(A) -> Rel(bold(A))$ [1.564] has a right adjoint. In $cal(S)$, $[B]$ is the set of subsets of $B$.]),

  ("1.912", [$Rel(-, 1) tilde.eq Sub(-)$, so $[1]$ — traditionally $Omega$ — is a #D("subobject classifier"). A universal subobject is a monic $Omega' arrow.r.tail Omega$ of which every monic $A' arrow.r.tail A$ is a unique pullback; $chi_A$ is the #D("characteristic map") of $A' subset A$, equivalently the unique $chi$ with $chi^\# (Omega') = A'$. #dia(
    node((0, 0), $A'$), node((1, 0), $A$), node((0, 1), $Omega'$), node((1, 1), $Omega$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), $chi_A$, "-->"), corner((0.2, 0.28)),
  )]),

  ("", [Uniqueness of $chi_A$ forces uniqueness of $A' -> Omega'$. Taking $A' arrow.r.tail A$ to be $1_A$ gives a unique pullback for every $A$, so each object has exactly one map to $Omega'$: the universal subobject is a point, henceforth written $1 ->^t Omega$.]),

  ("1.913", [#Th[In any cartesian category with a subobject classifier every subobject is an equalizer] — $A' arrow.r.tail A$ equalizes $chi_A$ and $p_A t$. #Th[Consequently covers coincide with epics.]]),

  ("1.914", [An $n$-ary $g: Omega^n -> Omega$ induces $hat(g)$ on each $Sub(A)$: $hat(g)(A_1, ..., A_n)$ is the subobject with characteristic map $chevron.l chi_(A_1), ..., chi_(A_n) chevron.r g$. Every operation on $Sub(-)$ so arises, and each commutes with inverse images: $hat(g)(f^\# A_1, ..., f^\# A_n) = f^\# hat(g)(A_1, ..., A_n)$.]),

  ("", [$g = chi$ of $chevron.l t, t chevron.r: 1 -> Omega times Omega$ gives $hat(g)(A_1, A_2) = A_1 inter A_2$: $Omega$ is a semi-lattice with unit $1 ->^t Omega$. $g = chi$ of $chevron.l 1, 1 chevron.r: Omega -> Omega times Omega$ makes $hat(g)(A_1, A_2)$ the equalizer of $chi_(A_1), chi_(A_2)$, so $A' subset hat(g)(A_1, A_2)$ iff $A_1 inter A' = A_2 inter A'$ — the Heyting $<->$, with $x -> y = x <-> (x and y)$. Each $Sub(A)$ is a Heyting semi-lattice.]),

  ("1.919", [#Th[Every monic endomorphism of $Omega$ is an involution.] Absence of non-automorphic monic endomorphisms is a finiteness condition; $Omega$ need not satisfy the dual condition.]),

  ("1.91(10)", [#Th[A nonempty category with binary products, equalizers and power-objects has a terminator, hence is a topos] — the equalizer of $1_([B])$ and the constant $Lambda M_([B], B)$, where $M_(A, B)$ is the relation tabulated by $A times B$.]),

  ("1.92", [$Lambda 1: B arrow.r.tail [B]$ is the #D("singleton map"); in $cal(S)$ it sends $b$ to $\{b\}$. For any $f: A -> B$, $(f Lambda 1) eps = f$ and $f Lambda 1$ is a map, hence $f Lambda 1 = Lambda f$; consequently $Lambda 1$ is monic.]),

  ("", [#Th[A topos is exponential.] Power-objects are baseable, $(A times -, [B]) tilde.eq Sub(- times A times B) tilde.eq (-, [A times B])$, so $[B]^A$ is constructible as $[A times B]$; and $B$ is the equalizer of the characteristic map $chi$ of $Lambda 1$ and of $p t$, hence baseable [1.859]. #dia(
    node((0, 0), $B$), node((1, 0), $[B]$), node((2, 0), $Omega$),
    edge((0, 0), (1, 0), $Lambda 1$, ">->"),
    edge((1, 0), (2, 0), $chi$, "->", bend: 22deg),
    edge((1, 0), (2, 0), $p t$, "->", bend: -22deg, label-side: right),
  )]),

  ("1.921", [$Rel(-, B) tilde.eq Sub(- times B) tilde.eq (- times B, Omega) tilde.eq (-, Omega^B)$: $[B]$ is definable as $Omega^B$. Lawvere's original axioms — bicartesian, exponential, with partial map classifiers [1.934] — follow from power-objects alone.]),

  ("1.922", [$[-]$ is the covariant power-object functor, right adjoint of the graphing functor; $Omega^(-)$ is contravariant. For $g: B_1 -> B_2$, $Omega^g$ is the unique map inducing $R |-> R g^circle.small$ from $Rel(-, B_2)$ to $Rel(-, B_1)$; so $Omega^g = [g^circle.small]$.]),

  ("1.923", [$B^A$ is cut out of $[A times B]$ by a pullback. #dia(
    node((0, 0), $B^A$), node((1, 0), $[A times B]$), node((0, 1), $1$), node((1, 1), $[A]$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), $⌜A⌝$, "->"), edge((1, 0), (1, 1), $f$, "->"), corner((0.2, 0.28)),
  )
  In $cal(S)$, $f$ sends $R subset A times B$ to $\{a | exists! b, chevron.l a, b chevron.r in R\}$, and $1 -> [A]$ names the entire subobject.]),

  ("1.926", [#Th[In a topos exponential structure restricts to the Heyting algebra structure on $Sub(1)$.]]),

  ("1.93", [#Th[Slice lemma for topoi: for a topos $bold(E)$ and an object $B$, $bold(E) slash B$ is a topos and $Delta: bold(E) -> bold(E) slash B$ is a representation of topoi.] $Delta[A]$ is the power-object of $Delta(A)$; and for $A' subset A$, $[A']$ is the equalizer of $1_([A])$ and the idempotent $e = Lambda(eps inter ([A] times A'))$.]),

  ("1.931", [In any cartesian category $f: A -> B$ gives $f^\#: bold(A) slash B -> bold(A) slash A$ by pulling back, with left adjoint $Sigma_f$ by composing. #dia(
    node((0, 0), $f^\#C$), node((1, 0), $C$), node((0, 1), $A$), node((1, 1), $B$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), $f$, "->"), edge((1, 0), (1, 1), "->"), corner((0.2, 0.28)),
  )]),

  ("", [#D("the fundamental lemma of topoi") #Th[For $f: A -> B$ in a topos $bold(E)$, $f^\#: bold(E) slash B -> bold(E) slash A$ has a right adjoint $Pi_f: bold(E) slash A -> bold(E) slash B$.]]),

  ("1.932", [$f^\#$ restricted to $Sub(B)$ is inverse image, so $Pi_f$ restricted to $Sub(A)$ is the double-sharp operation [1.7]. #Th[The double-sharp axiom holds for topoi.]]),

  ("1.933", [#Th[Pullbacks preserve covering families: for $f: A -> B$ and a cover $\{C_i -> B\}_I$, the $\{D_i -> A\}$ below are a cover.] #dia(
    node((0, 0), $D_i$), node((1, 0), $C_i$), node((0, 1), $A$), node((1, 1), $B$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), $f$, "->"), edge((1, 0), (1, 1), "->"), corner((0.25, 0.3)),
  )
  #Th[Consequently a topos is pre-regular.]]),

  ("1.934", [$cal("Par")(bold(C))$ has the objects of $bold(C)$, and as morphisms $A -> B$ the pairs $chevron.l A', f chevron.r$ with $A' subset A$, $f: A' -> B$; composition of $chevron.l A', f chevron.r$ and $chevron.l B', g chevron.r$ is $chevron.l f^\# (B'), f g chevron.r$.]),

  ("", [#Th[For a topos $bold(E)$ the inclusion $bold(E) subset cal("Par")(bold(E))$ has a right adjoint: $cal("Par")(-, A) tilde.eq (-, tilde(A))$.] #dia(
    node((0, 0), $B'$), node((1, 0), $B$), node((0, 1), $A$), node((1, 1), $tilde(A)$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), $f$, "->", label-side: right),
    edge((0, 1), (1, 1), ">->"), edge((1, 0), (1, 1), "-->"), corner((0.2, 0.28)),
  )
  $tilde(A) = Pi_t (A)$; $tilde(1) = Omega$, and in a boolean positive logos $tilde(A) = A + 1$.]),

  ("1.935", [Topoi are pre-regular and satisfy the slice condition [1.541]. #Th[Every topos may be faithfully represented in a capital topos.]]),

  ("1.94", [For $F subset [A]$, $Gamma(F)$ is a subset of $Sub(A)$: the #D("subobjects named by") $F$. The #D("internally defined intersection") $inter F$: #dia(
    node((0, 0), $inter F$), node((1, 0), $A$), node((0, 1), $1$), node((1, 1), $Omega^F$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), "->"), edge((1, 0), (1, 1), "->"), corner((0.25, 0.3)),
  )
  $A -> Omega^F$ is the adjoint of $F arrow.r.tail [A] tilde.eq Omega^A$, and $1 -> Omega^F$ the adjoint of $F -> 1 ->^t Omega$.]),

  ("1.941", [#Th[$inter F$ is preserved by representations of topoi, and is the largest subobject of $A$ that stays a lower bound of the subobjects named by $T(F)$ under every representation $T$.] "Internally defined" is coextensive with being preserved by representations.]),

  ("1.942", [The adjoint $1 -> Omega^A$ of $chi_(A')$ is the #D("name of") $A'$, written $⌜A'⌝$; $A'$ is named by $F$ iff $⌜A'⌝ subset F$, and the $1 -> Omega^F$ of $inter F$ is the name of the entire subobject. $Omega^f$ is the internally defined inverse image: $⌜B'⌝ Omega^f = ⌜f^\# B'⌝$.]),

  ("", [#Th[For $A' subset A$ named by $F$, the composite $A -> Omega^F$ followed by $Omega^(⌜A'⌝)$ is $chi_(A')$.]]),

  ("1.943", [#Th[$inter F$ is contained in every subobject named by $F$.] #Th[If $F$ is well-pointed, $inter F$ is their greatest lower bound, and $B -> A$ factors through $inter F$ iff it factors through each subobject named by $F$.]]),

  ("1.944", [#Th[A topos has a strict coterminator] — $inter Omega$ in $Sub(1)$, minimal and stably so under every $p^\#$.]),

  ("1.945", [#Th[A topos is regular.] Image of $f: A -> B$: let $F subset [B]$ name the $B'$ with $f^\# (B') = A$; then $inter F = "Im" f$.]),

  ("1.946", [#Th[A topos is a logos.] Binary unions: $F_i subset [A]$ names the $A'$ containing $A_i$; $F = F_1 inter F_2$ names those containing both, and $inter F = A_1 union A_2$.]),

  ("1.947", [#Th[A topos is a transitive logos.] For reflexive $R$ on $B$: $F_1$, the equalizer of $1$ and $[R times 1]$ in $[B times B]$, names the $S$ with $R S subset S$; $F_2$ names the reflexive ones; $inter (F_1 inter F_2) = R^*$.]),

  ("1.949", [The #D("internally defined union") $union F$ is the direct image $mu(eps inter (F times A))$ along $mu: [A] times A -> A$. #Th[It is an upper bound of every subobject named by $F$, and the least one when $F$ is well-pointed.]]),

  ("", [$A' subset A$ is a permanent lower (upper) bound of $F$ if $T(A')$ stays one under every representation $T$. #Th[$inter F$ is the greatest permanent lower bound, $union F$ the least permanent upper bound.]]),

  ("1.94(10)", [$Lambda 1: A -> [A]$ names the subobjects which are points; $union (Lambda 1)$ is always entire, and is their least upper bound only when $A$ is well-pointed.]),

  ("", [A subobject of $A$ is its #D("well-pointed part") $A dot.c$ if it is the least upper bound of the points of $A$, equivalently the greatest well-pointed subobject; no internal construction of $A dot.c$ is possible. A #D("solvable topos") is one in which every object has a well-pointed part; there $Sub(A)$ has bounds for every elementarily definable family, but the slice lemma fails. Capital topoi are solvable, so every topos is faithfully represented in a solvable one.]),

  ("1.95", [#Th[A topos is a pre-topos.]]),

  ("1.951", [#Th[A topos is effective.] For an equivalence relation $E$ on $A$, factor $Lambda E$ as $A ->^h B arrow.r.tail [A]$; then $h^circle.small h = 1$ and $h h^circle.small = E$.]),

  ("1.952", [#Th[A topos is positive.] #dia(
    node((0, 0), $0$), node((1, 0), $1$), node((0, 1), $A$), node((1, 1), $[A]$),
    edge((0, 0), (1, 0), "->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((0, 1), (1, 1), $Lambda 1$, "->"), edge((1, 0), (1, 1), $⌜0⌝$, "->"), corner((0.2, 0.28)),
  )
  since $Lambda R$ factors through $Lambda 1$ iff $R$ is a map, and through $⌜0⌝$ iff $R = 0$. So $A + 1$ exists; generally $chevron.l Lambda 1, ⌜0⌝ chevron.r$ and $chevron.l ⌜0⌝, Lambda 1 chevron.r$ are disjoint monics into $[A] times [B] tilde.eq [A + B]$, tabulating $A + B$.]),

  ("1.954–5", [#Th[A topos has coequalizers]: for $f, g: A -> B$ put $R = f^circle.small g$ and $S = (R union R^circle.small)^*$; effectiveness makes $S$ the level of some $B -> C$, the coequalizer. #Th[A topos is bicartesian] (coequalizers, coterminator, binary coproducts).]),
)

#dt(
  ("1.961", [$E$ is an #D("injective") if $(-, E)$ carries monics to epics. #dia(
    node((0, 0), $A$), node((1, 0), $B$), node((0, 1), $E$),
    edge((0, 0), (1, 0), ">->"), edge((0, 0), (0, 1), "->", label-side: right),
    edge((1, 0), (0, 1), "-->"),
  )
  In a pre-topos, pushouts of monics are monic [1.651], so $E$ is injective iff every monic $E arrow.r.tail A$ has a right inverse.]),

  ("", [$E$ in an exponential category is #D("internally injective") if $E^(-)$ carries monics to epics. #Th[In a topos $Omega$ is internally injective]: for monic $f$, $Omega^f = [f^circle.small]$ has left inverse $[f]$, since $Omega^f [f] = [f^circle.small f] = 1$. #Th[In a topos $Omega$ is (externally) injective.]]),

  ("1.962", [#Th[If $E$ is injective in an exponential category then so is $E^A$], since $(-, E^A) tilde.eq (- times A, E)$ and $- times A$ preserves monics; likewise internally. Hence $Omega^A$ is injective, and $Lambda 1$ embeds every object in an injective.]),

  ("1.963", [#Th[$tilde(A)$ [1.934] is injective] — a partial map $B_1 -> A$ is a partial map $B_2 -> A$ whenever $B_1 arrow.r.tail B_2$.]),

  ("1.964", [A category is #D("value-based") if its values form a basis; capital topoi are. #Th[In a value-based topos $Omega$ is a cogenerator.]]),

  ("1.965", [$C$ in an exponential category #D("internally cogenerates") if $C^(-)$ is a contravariant embedding; a cogenerator does. #Th[In a topos $Omega$ internally cogenerates.]]),

  ("1.966", [A #D("progenitor") is an object whose subobjects form a generating set. A topos is value-based iff $1$ is a progenitor; every Grothendieck topos has one. #Th[If $G$ is a progenitor then $Omega^G$ is a cogenerator.]]),

  ("1.967", [#Th[Equivalent on a locally small topos: (a) arbitrary powers exist; (b) arbitrary copowers exist; (c) arbitrary copowers of $1$ exist. Each implies local completeness.] (a) says contravariant representables have adjoints, (b) that covariant ones do, (c) that $Gamma$ does.]),

  ("1.968", [#Th[A locally small topos is complete iff it is cocomplete.]]),

  ("1.969", [The #D("lawvere definition") of a Grothendieck topos: a cocomplete topos with a generating set. The #D("tierney definition"): a topos with a progenitor and arbitrary copowers of $1$ — equivalently, with a geometric morphism to $cal(S)$.]),

  ("1.96(11)", [#Th[Slice lemma for Grothendieck topoi: $bold(E) slash B$ is a Grothendieck topos, and $Delta: bold(E) -> bold(E) slash B$ preserves progenitors.]]),

  ("1.971", [$A$ is small if it is a subquotient of a $bold(G)$-object: $A <- G' arrow.r.tail G$ with the left arrow a cover. #Th[In a boolean Grothendieck topos every object is a coproduct of small objects.]]),

  ("1.972", [#Th[In a boolean logos with $1$ projective, $1$ is a progenitor.] #Th[Equivalent on a Grothendieck topos: (1) boolean and $1$ projective; (2) boolean and value-based; (3) boolean with a choice progenitor; (4) every object a coproduct of sub-terminators; (5) AC.]]),

  ("1.973", [A topos is #D("IAC") (internal axiom of choice) if $(-)^A$ [1.853] preserves epics for every $A$.]),

  ("1.974", [#Th[A topos is AC iff it is IAC and $1$ is projective.] Every functor from an AC topos preserves epics, since it preserves left-invertibility.]),

  ("1.976", [#Th[A small topos may be faithfully represented in an AC topos iff it is IAC] — take $C_A subset A^([A]^+)$ naming the choice maps contained in the universal relation.]),

  ("1.977", [#Th[Any universal sentence in the predicates of topoi which follows from AC follows from IAC.] In particular #Th[an IAC topos is boolean.]]),

  ("1.979", [#Th[For any topos $bold(A)$ there is a boolean topos $bold(B)$ and a faithful bicartesian representation $bold(A) -> bold(B)$] [2.542].]),
)

#dt(
  ("1.98", [A #D("natural numbers object") (NNO) is $1 ->^0 N ->^s N$ such that every $1 ->^a A ->^t A$ admits a unique $N -> A$: #dia(
    node((0, 0), $1$), node((1, 0), $N$), node((2, 0), $N$), node((1, 1), $A$), node((2, 1), $A$),
    edge((0, 0), (1, 0), $0$, "->"), edge((1, 0), (2, 0), $s$, "->"),
    edge((0, 0), (1, 1), $a$, "->", label-side: right),
    edge((1, 0), (1, 1), "-->"), edge((2, 0), (2, 1), "-->"),
    edge((1, 1), (2, 1), $t$, "->"),
  )
  Unique up to isomorphism. In $cal(S)$: zero and successor. The topos of finite sets has no NNO.]),

  ("1.981", [#Th[For a NNO and any $A ->^x B ->^t B$ there is a unique $A times N -> B$:] #dia(
    node((0, 0), $A$), node((1, 0), $A times N$), node((2, 0), $A times N$),
    node((1, 1), $B$), node((2, 1), $B$),
    edge((0, 0), (1, 0), $chevron.l 1_A, 0 chevron.r$, "->"), edge((1, 0), (2, 0), $1_A times s$, "->"),
    edge((0, 0), (1, 1), $x$, "->", label-side: right),
    edge((1, 0), (1, 1), "-->"), edge((2, 0), (2, 1), "-->"),
    edge((1, 1), (2, 1), $t$, "->"),
  )
  — transpose $x, t$ into $1 -> B^A -> B^A$.]),

  ("1.983", [#Th[Recursion: for a NNO and any $g: A -> B$, $h: A times N times B -> B$ there is a unique $f: A times N -> B$ with] $chevron.l 1_A, 0 chevron.r f = g$ #Th[and] $(1_A times s) f = chevron.l p_1, p_2, f chevron.r h$.]),

  ("1.984", [Addition, multiplication and exponentiation on a NNO by the usual recursion equations: $chevron.l 1_N, 0 chevron.r a = 1_N$, $(1_N times s) a = a s$; $chevron.l 1_N, 0 chevron.r m = 0$, $(1_N times s) m = chevron.l p_1, m chevron.r a$; $chevron.l 1_N, 0 chevron.r e = 0 s$, $(1_N times s) e = chevron.l p_1, e chevron.r m$.]),

  ("1.985", [#Th[For a NNO, $1 ->^0 N <-^s N$ is a coproduct and $N ⇉ N -> 1$ (by $1_N$ and $s$) is a coequalizer.] #dia(
    node((0, 0), $1$), node((1, 0), $N$), node((0.5, 1), $N$),
    edge((0, 0), (0.5, 1), $0$, "->", label-side: right), edge((1, 0), (0.5, 1), $s$, "->"),
  )
  #dia(
    node((0, 0), $N$), node((1, 0), $N$), node((2, 0), $1$),
    edge((0, 0), (1, 0), $1_N$, "->", bend: 22deg),
    edge((0, 0), (1, 0), $s$, "->", bend: -22deg, label-side: right),
    edge((1, 0), (2, 0), "->"),
  )]),

  ("1.986", [#Th[Given $1 ->^a A$ and $A ->^f A$ there is $A' subset A$ carrying $a', f'$ with] #dia(
    node((0, 0), $1$), node((1, 0), $A'$), node((2, 0), $A'$), node((1, 1), $A$), node((2, 1), $A$),
    edge((0, 0), (1, 0), $a'$, "->"), edge((1, 0), (2, 0), $f'$, "->"),
    edge((0, 0), (1, 1), $a$, "->", label-side: right),
    edge((1, 0), (1, 1), ">->"), edge((2, 0), (2, 1), ">->"),
    edge((1, 1), (2, 1), $f$, "->"),
  )
  #Th[and with $binom(a', f'): 1 + A' -> A$ a cover] — in $Rel(bold(A))$ take $A'' = a f^*$, $f'' = A'' f$.]),

  ("1.987", [$1 ->^a A$, $A ->^t A$ has the #D("peano property") iff every subobject $B subset A$ that allows $a$ and allows $t harpoon.tr B$, the composite $B subset A ->^t A$, is entire. #Th[The $A'$ of 1.986 is the least subobject allowing both $a$ and $A' subset A ->^f A$, and it has the Peano property.]]),

  ("1.988", [#Th[In a boolean topos, if $1 ->^a A <-^t A$ is a coproduct and $A ⇉ A -> 1$ (by $1_A$ and $t$) a coequalizer, then $1 ->^a A ->^t A$ has the Peano property.] ("Boolean" is removable by [2.542].)]),

  ("1.989", [#Th[Under the hypotheses of 1.988, if $binom(c, u): 1 + C -> C$ is a cover and $c f = a$, $u f = f t$, then $f: C -> A$ is monic.]]),

  ("1.98(10)", [#Th[Converse of 1.985: in any topos, if $1 ->^a A <-^t A$ is a coproduct and $A ⇉ A -> 1$ a coequalizer, then $1 ->^a A ->^t A$ is a NNO.] Uniqueness from the Peano property applied to the equalizer of two candidates; existence from 1.986 applied to $chevron.l a, b chevron.r$ and $t times v$.]),

  ("1.98(11)", [#Th[A bicartesian functor $T: bold(A) -> bold(A)'$ of topoi carries a NNO to a NNO] — by the bicartesian characterization [1.985, 1.98(10)].]),

  ("1.98(12)", [An #D("A-action") is an object $B$ with $1 ->^b B$ and $A times B ->^v B$. A #D("free A-action") is an $A$-action $A times 1 ->^(1_A times e) A times A^* ->^s A^*$ universal among them: #dia(
    node((0, 0), $A times 1$), node((1, 0), $A times A^*$), node((2, 0), $A^*$),
    node((1, 1), $A times B$), node((2, 1), $B$),
    edge((0, 0), (1, 0), $1_A times e$, "->"), edge((1, 0), (2, 0), $s$, "->"),
    edge((0, 0), (1, 1), $1_A times b$, "->", label-side: right),
    edge((1, 0), (1, 1), $1_A times f$, "-->"), edge((2, 0), (2, 1), $f$, "-->"),
    edge((1, 1), (2, 1), $v$, "->"),
  )
  Unique up to isomorphism; a NNO is a free $1$-action. In $cal(S)$, $A^*$ is the set of finite lists, $e$ the empty list, $s$ prefixing.]),

  ("1.98(13)", [#Th[$A times 1 -> A times A^* -> A^*$ is a free $A$-action iff $binom(e, s): 1 + A times A^* -> A^*$ is iso and $A times A^* ⇉ A^* -> 1$ is a coequalizer.]]),

  ("1.98(14)", [#Th[In a topos with a NNO every object $A$ has a free $A$-action] — take $A^*$ the least subobject of $(1 + A)^N$ allowing $e$ and $A times A^* subset A times (1 + A)^N -> (1 + A)^N$.]),
)
