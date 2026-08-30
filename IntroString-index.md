# Page index for IntroString.pdf (Hinze & Marsden, *Introducing String Diagrams*, CUP 2023)

**Page rule: stream page = printed page + 15.** All pages below are printed numbers.

## Table of contents

| Section                                        | Printed page |
|------------------------------------------------|--------------|
| Prologue                                       | ix           |
| 1 Category Theory                              | 1            |
| 1.1 Categories                                 | 1            |
| 1.2 Properties of Arrows                       | 6            |
| 1.3 Thinking in Terms of Arrows                | 8            |
| 1.4 Functors                                   | 13           |
| 1.5 Natural Transformations                    | 18           |
| 1.6 Properties of Functors                     | 22           |
| 1.7 Equational Reasoning                       | 23           |
| Exercises (ch. 1)                              | 27           |
| 2 String Diagrams                              | 33           |
| 2.1 Composition of Functors                    | 34           |
| 2.2 Composition of Natural Transformations     | 36           |
| 2.3 Converting between Symbols and Diagrams    | 40           |
| 2.4 Equational Reasoning                       | 45           |
| 2.5 Natural Isomorphisms                       | 50           |
| 2.6 Duality                                    | 53           |
| Exercises (ch. 2)                              | 56           |
| 3 Monads                                       | 63           |
| 3.1 Monads                                     | 63           |
| 3.2 Monad Maps                                 | 67           |
| 3.3 Comonads                                   | 70           |
| 3.4 Kleisli Categories                         | 72           |
| 3.5 Eilenberg–Moore Categories                 | 76           |
| 3.6 Actions of a Monad                         | 82           |
| Exercises (ch. 3)                              | 88           |
| 4 Adjunctions                                  | 91           |
| 4.1 Adjunction                                 | 91           |
| 4.2 Reasoning with Adjunctions                 | 96           |
| 4.3 Composition of Adjunctions                 | 100          |
| 4.4 Mates                                      | 102          |
| 4.5 Adjoint Comonads and Monads                | 106          |
| 4.6 Reflective and Coreflective Subcategories  | 108          |
| 4.7 Equivalences of Categories                 | 110          |
| Exercises (ch. 4)                              | 123          |
| 5 Putting It All Together                      | 129          |
| 5.1 Huber's Construction                       | 129          |
| 5.2 Universal Constructions                    | 136          |
| 5.3 Free Monads                                | 146          |
| 5.4 The Resumption Monad                       | 157          |
| Exercises (ch. 5)                              | 164          |
| Epilogue                                       | 167          |
| Appendix                                       | 169          |
| Notation                                       | 174          |
| References                                     | 179          |
| Index                                          | after 179 (page not captured from TOC) |

Spot-checked against page headers: 2.4 -> 45, 3.5 Eilenberg–Moore -> 76-77, 5.2 Universal Constructions -> 137,
5.3 Free Monads -> 146-147.

## Where the pictures are

| Picture / convention                        | Page    | What is drawn                                                    |
|---------------------------------------------|---------|------------------------------------------------------------------|
| Regions = categories, edges = functors      | 34-35   | Colored regions separated by wires; wire labels at top and bottom |
| Identity functor                            | 35      | A bare region with no edge at all; composing with Id does nothing |
| Beads = natural transformations             | 36-37   | Dots on wires; vertical composition stacks beads on one wire      |
| Elevator equations (2.1), (2.2)             | 38      | Beads on parallel wires slide up/down past each other freely      |
| Interchange law (2.3)                       | 39      | Vertical/horizontal composition order does not matter             |
| Spider vertex, arms and legs as bends       | 40      | Multi-wire transformation; arms/legs bend in, never straight-flat |
| No-horizontal-tangent rule                  | 40      | Edges are arbitrary curves but never have zero gradient           |
| Joyal–Street deformation + sweep-line       | 43      | Plane deformation soundness; algorithm reading a diagram back     |
| filter p := join A . List (guard p)  (2.4)  | 45      | Definition drawn := ; guard p rotated label on the gray band      |
| Property (2.5); join associativity (2.6)    | 46      | Two panels joined by =, equation number at right margin           |
| Four-step diagram chain, rotated hints      | 47      | Panels left-to-right, wrap; hint in braces rotated 90° above an = |
| Two-step chain vs 12-polygon diagram        | 48-49   | String-diagram proof beside Cheng's commutative diagram (Fig 2.1) |
| Component alpha A; hourglass spider  (2.7)  | 51      | Component = two parallel wires + dot left; spider = 2 arms 2 legs |
| Naturality-of-inverse chain                 | 51      | Four panels one row; hints { iso (2.7) } { naturality }           |
| Lollipop eta, tuning-fork mu                | 64      | Unit = dot ending a wire born in the open region; mu = fork       |
| Kleisli arrow, three candidate styles       | 73      | Chosen: object wire as "minor" diagonal, M exits straight down    |
| Side entries / exits of edges               | 73      | Edges may enter diagram sides; extended by no-tangent rule        |
| Kleisli identity = unit beside object wire  | 74      | eta dot next to the A diagonal, emitting the vertical M wire      |
| Kleisli composition (f ; g)                 | 74      | Two Kleisli arrows lined up on the diagonal, mu merging the Ms    |
| F-algebra a : F A -> A                      | 76      | A = static "minor diagonal" top-right to bottom-left; F wire ends |
|                                             |         | in a black dot on it; gray region right of the object wire        |
| Homomorphism axiom (3.6): the slide         | 77      | h slides along the wire across action a, transmogrifying into b   |
| Homomorphism composition chain              | 77      | Three panels; hints { h homomorphic (3.6) } { k homomorphic (3.6) } |
| Eilenberg–Moore axioms (3.8a), (3.8b)       | 79      | eta / mu absorbed by the diagonal, leaving 0 or 2 copies of a     |
| Symbolic Feijen proof, two columns          | 80      | Monoid unit/assoc proofs side by side in the vertical hint format |
| Collection types table (Figure 3.2)         | 81      | Monads vs algebraic theories                                      |
| Monad action: gray region turns colorful    | 82      | Same curvy shapes as (3.8) with a second nontrivial category      |
| Lollipop/fork dropped on an action prong    | 85      | Action absorbing unit or multiplication                           |
| Exercise box around f-dagger                | 89      | Exercise 3.10: rho A as an edge, a box around f to lift it        |
| Adjunction bijection (4.1)                  | 92      | Transposes floor/ceiling; unit and counit as bent wires (cup/cap) |
| Snake equations (4.3a), (4.3b)              | 93      | Bent wire pulled straight; re-displayed with arrows on 97         |
| Kan extensions deferred                     | 94      | Remark: notational choices for Kan extensions live in ESD ch. 6   |
| Uniqueness of adjoints via snakes           | 96      | Section 4.2.1                                                     |
| Mates                                       | 102     | Section 4.4; "Categories, adjunctions, and mates form the         |
|                                             |         | 2-category Adj" stated on 122                                     |
| Doughnut and hourglass (equivalences)       | 116     | Gadgets for adjoint equivalences, Section 4.7                     |
| Oval "blobs"; vertex shapes are free        | 130     | State transformers as ovals; dots/boxes/ovals all legal vertices  |
| Universal property box, open/closed borders | 137     | Transpose integrated as a box; open station marked by a hole      |
| Bending <-> boxing equivalence (5.3)        | 138     | Universal = bending device; computation law (5.4a): bending is a  |
|                                             |         | pre-inverse of boxing                                             |
| Fusion law (5.4c)                           | 139     | Arrow k freely crosses the open border; proof done symbolically   |
| Functorial boxes redrawn (5.2.3 Boxing)     | 145     | L transmogrifies into Id entering the box, R into Id leaving      |
| Fold as double circle; rounded-box form     | 147     | (5.8): fold node = circle-with-dot annotated a; alternative puts  |
|                                             |         | the algebra's own diagram inside a rounded box on the wire        |
| Universal property of fold (5.9)            | 148     | Two picture-equations joined by <=>                               |
| in drawn as a tuning fork                   | 148     | So the free-algebra equation resembles the EM mult axiom (3.8b)   |
| Computation rules (5.10a), (5.10b)          | 148-149 | Fold of a variable does nothing; fold is a Sigma-homomorphism     |
| Elevation rule (5.10c)                      | 149     | Equivalence, four panels with <=> in the middle                   |
| Isolating the algebra under a fold          | 150     | Three-panel chain; hints { (5.10b) } { (5.10a) }; emb defined     |
| Up / Dn functors (5.12a,b); (5.13)          | 151     | EM category of the free monad iso to Sigma-Alg                    |
| Up.Dn chain                                 | 152     | Four panels; hints { (5.13) } { b respects sub (3.8b) }           |
|                                             |         | { naturality }                                                    |
| M-compatible actions equivalence (5.14)     | 153     | Four panels around a <=>                                          |

## Quotable lines

- p. ix: string diagrams are "a two-dimensional form of notation, which retains the vital type information while
  permitting an equational style of reasoning."
- p. 23: "Each step of the calculation is justified by a hint, enclosed in curly braces. The hints should enable the
  reader to easily verify that the calculation constitutes a valid proof."
- p. 35: "we represent the identity functor on a category C ... by the corresponding region, without any associated
  edge".
- p. 38: "We obtain the vital elevator equations (Dubuc and Szyld, 2013), allowing us to move natural transformations
  up and down wires in an intuitive manner".
- p. 40: "edges can be arbitrary curves with the important restriction that they must not have a horizontal tangent
  (zero gradient)."
- p. 45: "To emphasize, we use string diagrams in defining equations, in to-be-established properties, and in
  calculational proofs."
- p. 47: "there is no need to appeal to the functoriality of List or the naturality of join, as both laws are built
  into the diagrammatic notation."
- p. 47: "We have essentially retained the proof format discussed in Section 1.7.1, except that we have replaced
  horizontal hints by vertical ones: this saves horizontal space to avoid stretching calculations over several pages."
- p. 50: "to avoid a horizontal tangent, we need to lift the rightmost point before the final drag."
- p. 51: "the component of the natural transformation is given by two parallel lines with a dot on the left; by
  contrast, the component of the transformation is represented by a small spider with two arms and two legs, an
  'hourglass.'"
- p. 59: "a cap is a natural transformation of type Id -> F.F (no arms, two legs)" (Exercise 2.13).
- p. 64: "Drawn as a string diagram, eta looks a tad like a lollipop – recall that the identity functor is drawn as a
  region – whereas mu resembles a tuning fork".
- p. 73: "This enables us to draw the outgoing M edge as a straight vertical, which blends well with the way we have
  drawn the monad operations."
- p. 76: "the carrier of an algebra can be seen as static, which is why it is drawn as a 'minor' diagonal".
- p. 76: "Observe that the diagram is a vertical reflection of the diagram for a Kleisli arrow (except for the types)."
- p. 77: "It allows us to slide h along the wire across the action a, which is transmogrified into b in the process."
- p. 82: "The gray region that is reserved for the terminal category has turned into a colorful one".
- p. 130: "Vertices can be depicted as dots, boxes, ovals, or other shapes that permit the convenient connection of
  their input and output wires."
- p. 139: "In diagrammatic proofs, we may decide to omit explicit invocations of (5.4c)." (fusion, free border
  crossings)
- p. 145-146: "Choosing which gadgets and which techniques to use is ultimately a matter of good taste. Bending works
  well for proofs that involve mainly natural transformations, in particular, as naturality is built into the
  notation. Boxing is often the technique of choice if mainly objects and arrows are involved. The proofs are,
  however, more pedestrian, as naturality has to be invoked explicitly. Whatever your preferred choice, keep in mind
  that boxing is bending."
- p. 147: "the fold (|a|) is depicted by a double circle, annotated with the target algebra a".
- p. 147: "There, the algebra is drawn as a separate diagram within the box. This style is preferable if the algebra
  has structure, as it avoids the need to mix symbols and diagrams."
- p. 148: "We decided to draw the action of the free algebra as a tuning fork, so that the shape of the resulting
  equation resembles the multiplication axiom of Eilenberg–Moore algebras (3.8b)."

## Numbered equations and figures actually sighted

| Number      | Page | Number      | Page | Number       | Page |
|-------------|------|-------------|------|--------------|------|
| (1.8)       | 10   | (2.9a)-(f)  | 52   | (5.4c)       | 139  |
| (1.19)      | 23   | (3.5)       | 76   | (5.6), (5.7) | 146  |
| (1.20)      | 23   | (3.6)       | 77   | (5.8)        | 147  |
| (1.21)      | 24   | (3.7a,b)    | 79   | (5.9)        | 148  |
| (1.22)      | 24   | (3.8a,b)    | 79   | (5.10a)      | 148  |
| (1.23)      | 24   | (3.9a)-(d)  | 80   | (5.10b)      | 149  |
| (2.1)       | 38   | Figure 3.2  | 81   | (5.10c)      | 149  |
| (2.2)       | 38   | (4.1)       | 92   | (5.10d)      | 150  |
| (2.3)       | 39   | (4.3a,b)    | 93   | (5.11)       | 150  |
| (2.4)       | 45   | (5.3)       | 137  | (5.12a,b)    | 151  |
| (2.5), (2.6)| 46   | (5.4a)      | 138  | (5.13)       | 151  |
| (2.7), (2.8)| 51   | (5.4b)      | 138  | (5.14)       | 153  |
| Figure 2.1  | 49   |             |      |              |      |

Figure 3.3 (relating algebras and actions) sits near the end of Section 3.6, ~p. 86 — page not verified.

## The book does NOT do this

- No coproduct or case split `[f,g]` in any string diagram; coproducts and `g1 join g2` live only in commutative
  diagrams and symbols, Section 1.3.2 (pp. 10-12). Sigma A = 1 + A x A stays one opaque Sigma wire (pp. 78, 147).
- No union of two parallel arrows; Rel appears only as the Kleisli category of Pow (pp. 75-76) and Exercise 1.4
  (p. 27), never with a drawn join of relations.
- No formula column beside a diagram chain; chain lines are pictures plus rotated brace hints only (pp. 47, 150, 152).
  Symbolic proofs use the separate vertical Feijen format (pp. 23-24, 80, 139).
- No statement drawn twice in two calculi; bending and boxing are alternatives chosen per proof, and boxing is defined
  in terms of bending (pp. 145-146).
- No numbering of the intermediate lines of a proof; only definitions and laws carry equation numbers, which the hints
  cite (p. 47).
- No Kan extensions; deferred to "ESD Chapter 6" (remark, p. 94).
