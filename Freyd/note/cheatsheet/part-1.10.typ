// §1.(10) SCONING
// kept: 1.(10) 1.(10)1 1.(10)11 1.(10)12 1.(10)13 1.(10)14 1.(10)3 1.(10)31 1.(10)32
//       1.(10)4 1.(10)41
// dropped: 1.(10)2 1.(10)21 (LH: the scone of Sh(X), sheaves over the one-point extension);
//       the abelian/projective-module asides (example).
#import "style.typ": *

= 1.(10) Sconing

#dt(
  ("1.(10)", [a category with a terminator is #D("exacting") if $Gamma = (1, -)$ is exact, i.e. preserves whatever finite colimits exist (it always preserves whatever small limits exist). An exacting pre-logos is focal, the pasting lemma describing unions as pushouts; a Grothendieck topos is exacting iff $1$ is a connected projective.]),

  ("1.(10)1", [#Th[Every category $bold(A)$ with a terminator is a slice of an exacting category $hat(bold(A))$] — and regular / pre-logos / pre-topos / logos / cartesian closed / topos / Grothendieck topos / having a natural numbers object all transfer to $hat(bold(A))$.]),

  ("", [the #D("scone") $hat(bold(A))$: objects $chevron.l S, A, f chevron.r$ with $S$ a set and $f: S -> Gamma(A)$, morphisms $chevron.l g, x chevron.r$ over the square #dia(
    node((0, 0), $S$), node((1, 0), $S'$), node((0, 1), $Gamma(A)$), node((1, 1), $Gamma(A')$),
    edge((0, 0), (1, 0), $g$, "->"), edge((0, 0), (0, 1), $f$, "->", label-side: right),
    edge((1, 0), (1, 1), $f'$, "->"), edge((0, 1), (1, 1), $Gamma(x)$, "->", label-side: right))
    written $chevron.l S, A chevron.r$, the third coordinate being clear.]),

  ("1.(10)11", [$chevron.l Gamma(1), 1 chevron.r$ is the terminator; $M = chevron.l nothing, 1 chevron.r$ is a proper subobject containing every proper subterminator, so $1$ is no union of proper subobjects — it is coprime. $hat(bold(A)) slash M eq.triple bold(A)$.]),

  ("1.(10)12–13", [the scone is exacting, $Gamma: hat(bold(A)) -> cal(S)$ preserving whatever small colimits exist. $hat(bold(A)) -> hat(bold(A)) slash M -> bold(A)$ has both adjoints — $A |-> chevron.l nothing, A chevron.r$ left, $A |-> chevron.l Gamma(A), A chevron.r$ right — hence preserves all limits and colimits that exist.]),

  ("1.(10)14", [structure lifts coordinatewise:
    $ chevron.l f, x chevron.r^(\#\#) chevron.l S, A chevron.r = chevron.l f^(\#\#) S, x^(\#\#) A chevron.r, quad chevron.l T, B chevron.r^(chevron.l S, A chevron.r) = chevron.l hat(bold(A))(chevron.l S, A chevron.r, chevron.l T, B chevron.r), B^A chevron.r, $
    $ [chevron.l S, A chevron.r] = chevron.l Sub_(hat(bold(A))) chevron.l S, A chevron.r, [A] chevron.r, quad N_(hat(bold(A))) = chevron.l N_cal(S), N_bold(A) chevron.r, $
    and $cal(C)$ generating $bold(A)$ makes $\{chevron.l 1, C chevron.r: C in cal(C)\}$ generate $hat(bold(A))$.]),

  ("1.(10)3", [for free $bold(A)$ the composite $bold(A) -> hat(bold(A)) -> hat(bold(A)) slash M -> bold(A)$ is the identity, so $bold(A)$ is a #D("retract") of $hat(bold(A))$.]),

  ("1.(10)31–2", [#Th[A retract of an exacting category is exacting], hence #Th[various free categories are exacting.]]),

  ("1.(10)4", [$A$ in a cocomplete abelian category is a #D("small projective") if $(A, -)$ preserves all colimits, equivalently all sums.]),

  ("1.(10)41", [#Th[For $E$ a Grothendieck topos and $A$ a connected projective, $(A, -): E -> cal(S)$ preserves all small colimits.]]),
)
