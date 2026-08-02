# CategoricalQuantum.pdf, read for AOP

Heunen and Vicary, *Categorical Quantum Mechanics* (`../CategoricalQuantum.pdf`), filtered for what the allegory and
AOP layers of this repo actually use: ONE Frobenius structure, and the hom order `≤`. The test is NOT whether `Rel`
appears as a theorem — chapters 6 and 7 pass that test and are skipped below. The book's subject is two interacting
structures and pure equations, so much of its `Rel` content answers a question we never ask. Page numbers are the
book's own.

**The verdict, after reading it.** For *doing* AOP in `Rel` this book adds nothing to
`functorialSemanticsForRelationalTheories.pdf`, which is the source the calculus here was formalised from: the four
generators, Frobenius, special, cup and cap, the converse laws, (37)–(43), maps as left adjoints — all of it is
already there, and HV states the same things in quantum dress. Three items are genuinely his: Thm. 5.36, which
counts the OTHER Frobenius structures a set carries and so says why a cartesian bicategory must name its comonoid;
the three no-go theorems, which are the reason the lax laws cannot be equations; and Lemma 3.20, the one lead that
could change code — see gap 2 below. Neither source has the half AOP is actually about: the order, division, folds.

## What we already have

Everything in this table is formalised; the book is a second account of it, not a source of new work.

| book                                            | here                                                                |
| ----------------------------------------------- | ------------------------------------------------------------------- |
| dagger of `Rel` is converse `R°` (2.3, p. 61)   | `conv` CB.lean:265, `conv_conv` 462, `conv_comp` 480                |
| superposition is union, zero object `∅` (2.2)   | `Biprod.union` Tape.lean:84, `union_comm`, `comp_union`, `conv_union` |
| biproduct is disjoint union (2.2.3, p. 57)      | `Biprod` class Tape.lean:44                                          |
| compact closed, cup and cap (3.1, p. 72)        | `cup`/`cap` CB.lean:195, 198; `snake` 204, `snake'` 221, `snakes` 236 |
| the cup is symmetric (eq. 3.48)                 | `cup_swap` CB.lean:336                                               |
| name and coname (Def. 3.3, p. 74)               | `bend`/`unbend` CB.lean:246, 252; `unbend_bend` 367                  |
| comonoid and monoid laws (4.1, p. 101)          | CB.lean:48–59, the two shuffles 63, 67                               |
| comonoid homomorphism = map (Def. 4.5)          | `lax_Δ` 87 and `lax_!` 90, as inequalities; equality exactly on maps |
| Frobenius law (5.1, p. 121)                     | `frob_left`/`frob_right` CB.lean:81, 83                              |
| special (Def. 5.5, p. 123)                      | `special` CB.lean:134 — derived here, not an axiom                   |
| the surviving halves of the bialgebra laws      | `«∇≤𝟙!»` CB.lean:116, `«Δ≤?𝟙»` 159                                   |
| `⊗` distributes over `∪`                        | `FbCbRig.tensHom_union` Tape.lean:243, `meet_union_distrib` 255      |
| duals give the modular law (5.1 + 3.1)          | `modular_of_frobenius`, drawn in allegory-axioms.typ                 |

Four gaps, in the order they are worth closing:

1. **`Rel(Set)` is not yet a `CartBicat`.** RelSetWord.lean builds the model only as far as `instance : SymMonCat`
   (line 344). Nothing checks the eight axioms against the model they were abstracted from.
2. **`FbCbRig.tensHom_union` may be redundant.** It is a class field (Tape.lean:243), but HV's Lemma 3.20 proves
   exactly that law from biproducts, a zero object, and one object having a dual — and `CartBicat` has duals at every
   object (`snake`/`snake'`). If it goes through, `meet_union_distrib` becomes a pure theorem too.
3. **The spider normal form (5.2) is not formalised.** It is the theorem behind "a connected diagram of generators is
   determined by its endpoints", which is what makes `diag-export` free to route wires.
4. **Theorem 5.36 is not formalised and need not be** — see the mismatch below; it is used in reverse, as motivation.

## What AOP needs and this book does not have

The hom order beyond equations (`⊑`, monotonicity, the lax laws as *content* rather than as an obstruction),
division and residuals `R/S`, folds and hylomorphisms and their fusion laws, the power transpose. None of it appears
in HV. The book gives the equational skeleton — converse, cup and cap, Frobenius, spider — and is silent on
everything AOP is actually about.

## Read

- **2.2 Superposition** (54–60). Zero object is `∅`, superposition is union, biproducts are disjoint union — the
  union section of the axiom note, from the other side.
- **2.3 Daggers** (61–65). The dagger of `Rel` *is* relational converse `R°`.
- **3.1 Dual objects** (72–83). `Rel` is compact closed and every object is its own dual, the cup and cap being the
  diagonal. 3.2 Pivotality can be skimmed: in `Rel` it degenerates (`π = 𝟙`, `θ = 𝟙`), which is the licence for
  drawing wires with no arrowheads.
- **4.2.2 Monoids of operators** (108–110). The pair of pants monoid on `A* ⊗ A`: multiplication is a cap in the
  middle, unit is the cup. In `Rel` that is composition of pairs, `((a,b), (c,d)) ↦ (a,d)` when `b = c` — the
  indiscrete groupoid on `A`, the *quantum structure* end of Thm. 5.36. Read it to know what you are NOT using.
- **4.4 Products** (116–117). When `⊗` is a categorical product, which in `Rel` it is not.
- **5.1–5.2** (121–132). The definition, and the spider normal form.
- **5.4.3 Groupoids** (140–143). The page worth the most here. Special dagger Frobenius structures in `Rel`
  correspond exactly to GROUPOIDS (Thm. 5.36); classical structures to abelian groupoids; quantum structures to
  indiscrete ones.

## One sentence, then skip

Three no-go theorems. None of them computes anything in `Rel`; they justify the SHAPE of laws already written, and
that is one sentence each. Read the statements, not the proofs.

- **4.2.3 Uniform deleting** (110). If `⊸` were *natural* — `R ⊸ = ⊸` for every arrow, not only for maps — a compact
  category would collapse to a preorder (Thm. 4.17). `Rel` is compact and is not a preorder, so the law can only be
  `lax_!`, `R ⊸ ≤ ⊸`, with equality exactly for entire `R`. Witness of the failure: `R = ∅` gives `∅ ⊸ = ∅ ≠ ⊸`.
- **4.3 Cloning** (111–115). The same for `◁`, with a different collapse — uniform copying makes every endomorphism a
  scalar multiple of the identity (Thm. 4.27), which in `Rel` would force every `R : A ⟶ A` to be `∅` or `𝟙`. Hence
  `lax_Δ`, `R ◁ ≤ ◁ (R ⊗ R)`, with equality exactly for single-valued `R`. The two laws are therefore equations on
  exactly `Map(Rel) = Set`, which is why `Set` may have both (Ex. 4.19) without collapsing: it is not compact. Keep
  one line of 4.3.2: Def. 4.22, *discrete* = only identities, *indiscrete* = exactly one arrow between any two
  objects. Those two words are what 5.4.3 classifies by.
- **6.3 Bialgebras** (166–171). A monoid and comonoid that are *both* Frobenius and a bialgebra force `A ≃ I`
  (Thm. 6.22) — the Frobenius law equates connected diagrams, the bialgebra laws equate connected ones with
  disconnected ones. So for `◁ ▷ ⊸ ⟜` the bialgebra laws `▷⊸ = ⊸ ⊗ ⊸` and `⟜◁ = ⟜ ⊗ ⟜` *must* fail; what survives is
  the `≤` half of each, which is `«∇≤𝟙!»` and `«Δ≤?𝟙»`. The other two bialgebra laws hold on the nose.

## Skip

| section                                      | p.      | why                                                              |
| -------------------------------------------- | ------- | ----------------------------------------------------------------- |
| 0.1 Category theory                          | 3–13    | an introduction to what this repo already builds                  |
| 0.2 Hilbert spaces, 0.3 Quantum information  | 14–26   | Hilbert-space and qubit background; `Rel` occurs zero times       |
| 1.3 Coherence                                | 40–45   | the `Word` tower is strict, so there is no associator to cohere   |
| 5.4.1–5.4.2, the `FHilb` half                | 136–140 | direct sums of matrix algebras                                    |
| 5.6 Modules                                  | 147–151 | measurement, controlled operations, teleportation — Hilbert       |
| 6 Complementarity, all of it                 | 155–178 | see below                                                         |
| 7 Complete positivity, all of it             | 179–207 | see below                                                         |
| 8 Monoidal bicategories, except Def. 8.8      | 208–229 | see below                                                         |

**Chapter 6** has genuine `Rel` theorems: complementary groupoids are a coordinate grid — `a ↦ (dom_G a, dom_H a)` is
a bijection onto `Ob(G) × Ob(H)` (Prop. 6.8) — and in `Rel` complementary implies bialgebra for free (Lem. 6.23),
which already fails in `FHilb`. All of it needs a SECOND Frobenius structure on the object, and this repo has one.
The complement of `◁ ⊸` is a group structure on the underlying set; AOP never has one. Keep only Thm. 6.22, above.

**Chapter 7**: `CP[Rel]` is relations between groupoids that respect inverses, a compact dagger category
(Prop. 7.10, p. 184) — clean, and about the wrong thing. The book says of its own model: "even though we have
sketched `Rel` as a model of 'possibilistic quantum mechanics', it is a nonstandard model of quantum mechanics".

**Chapter 8** is 2–Hilbert spaces, and its bicategories have *categories* as objects and natural transformations as
2-cells (Def. 8.5, `Cat`). Two definitions in 8.1 are worth two minutes anyway, because they name what §1.1 of the
axiom note already does. 8.1.2's calculus is objects = regions, 1-cells = vertical lines, 2-cells = vertices; read
onto `Rel` that is sets, relations, and inclusions, and it degenerates — locally posetal means at most one 2-cell, so
every vertex is unlabelled and a picture says only that one inclusion holds. But Def. 8.8 puts `L ⊣ R` on 1-cells,
and in a locally posetal 2-category its snake equations are automatic, since parallel 2-cells are equal. So an
adjunction in `Rel` is exactly a pair of inclusions,

    R ⊣ S   ⟺   𝟙_A ≤ R S   and   S R ≤ 𝟙_B

which is what (37)–(40) are: `◁ ⊣ ▷` and `⊸ ⊣ ⟜`. Taking `S = R°` gives `R ⊣ R° ⟺ R` is a function — entire on the
left, single-valued on the right. *Maps are the left adjoints*, the same statement as Def. 4.5's comonoid
homomorphisms and as Freyd's entire-and-simple. Example 8.9: in `Cat` the same definition is an ordinary adjunction
of functors. Everything after 8.1.3 is 2–Hilbert spaces.

## The mismatch to keep in mind

This book reads `Rel` as a DAGGER COMPACT category and never uses the hom order `≤`. So it classifies *all* special
dagger Frobenius structures on a set, and the answer is: one per groupoid. The `◁`, `▷` of a cartesian bicategory are
the most degenerate of them — the discrete groupoid on `A`, no arrows but the identities — and the order and the lax
laws, which are the whole allegory, are structure this book never has. Theorem 5.36 is therefore useful in reverse:
it counts how many OTHER Frobenius structures a set carries, and so says why a cartesian bicategory must name the one
comonoid it means.

## What are `f` and `g` in `L ⊣ R`?

HV write dual objects as `L ⊣ R` (Def. 3.1) and give a unit, a counit and two commuting squares — never a hom-set
bijection. It is one, and the only thing in the way is the letters. In `f(x) ≤ y ⟺ x ≤ g(y)`: `x`, `y` are objects
`X`, `Y`; `≤` is "there is an arrow"; and `f`, `g` are *not* `L` and `R` — those are objects, and an object is not a
function. An object becomes a function by tensoring with it, `f = L ⊗ −` and `g = R ⊗ −`, so `L ⊣ R` is shorthand
for `(L ⊗ −) ⊣ (R ⊗ −)` and the adjunction says

    L ⊗ X ⟶ Y   naturally corresponds to   X ⟶ R ⊗ Y

That is currying, and the `⟺` of the poset form is that natural correspondence. In `Set`, currying `A × X ⟶ Y` gives
`X ⟶ Yᴬ`, an exponential; saying `L` has a dual says the right adjoint is another tensor. In `Rel` every object is
its own dual, `L = R = A`, so `A × −` is left adjoint to itself.

## Two words that mean something else here

**Cartesian.** Thm. 4.31's "Cartesian" is a property of the MONOIDAL structure: the tensor is the categorical product
and the unit is terminal. `(Rel, ×, 1)` is neither — the product is `⊎` and the terminal object is `∅`, so
`Rel(A, 1) = P(A)` has `2^|A|` arrows. The *category* `Rel` is cartesian in Def. 4.30's weaker sense, having products
and a terminal object, which is the trap: having products is not the tensor being one. `(Rel, ⊎, ∅)` *is* cartesian
monoidal and does have uniform copying and deleting — and no duals, since `η : ∅ ⟶ R ⊎ L` is a zero morphism and the
snake then forces `L ≅ ∅`. Carboni and Walters' "cartesian bicategory", the `CartBicat` of CB.lean, is a third thing
again: a comonoid on every object whose naturality holds only up to `≤`.

**Bicategory.** `Rel` is one, and strictly (a 2-category, Def. 8.3): objects are sets, 1-cells relations, 2-cells
inclusions `R ⊆ S`, and relational composition is strictly associative. It is locally posetal — at most one 2-cell
between two 1-cells — which is `OrderedCat` here. That is the sense in "cartesian bicategory", and it is not what
chapter 8 studies.

## `Rel` 里的 name 和 coname

(CategoricalQuantum.pdf, Def. 3.3, p. 74)

`Rel` 里每个对象自对偶，`A* = A`，`I = 1`，`η = ⟜◁ = {(•, (a,a))}`，`ε = ▷⊸ = {((a,a), •)}`。于是对 `R ⊆ A × B`：

| 名字            | 类型          | 是什么                       |
| --------------- | ------------- | ---------------------------- |
| name `⌜R⌝`      | `1 ⟶ A × B`   | `{(•, (a,b)) \| a R b}`      |
| coname `⌞R⌟`    | `A × B ⟶ 1`   | `{((a,b), •) \| a R b}`      |

右列是同一个子集 `R`，一次读成 state，一次读成 effect，`⌞R⌟ = ⌜R⌝†`。

`⌜R⌝` 不是 `R` 的子集，它就是 `R`：`1 ⟶ A × B` 的数据按定义是 `1 × (A × B) ≅ A × B` 的子集。hom-set 双射

    Rel(A, B) ≅ Rel(1, A × B)

两边都是「`A × B` 的子集」，在 `Rel` 里是恒等，一个字节不动；变的只是把这堆 pair 叫作过程还是叫作状态。

所以它在 `Rel` 里像废话，书里却要专门定义：`FHilb` 里同一个双射把矩阵 `A ⟶ B` 变成 `A* ⊗ B` 里的一个向量，那是
map–state duality（Choi–Jamiołkowski），两边的数据长得完全不一样。`Rel` 是它退化成恒等的那个模型。
