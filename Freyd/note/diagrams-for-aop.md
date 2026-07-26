# Diagrammatic calculi for `Rel(Set)`: what reaches AOP and what does not

Goal: Algebra of Programming, drawn. Wires are sets, boxes are relations, derivations are diagram rewrites. This note
records how far the existing diagram languages get and where each one stops. Companion: `Freyd/note/state.md`.


## Freyd's layering is the checklist

The book adds the operations in a fixed order, and each level is defined *on top of* the previous one:

| book   | level                  | operations added         |
| ------ | ---------------------- | ------------------------ |
| §2.1   | allegory               | `;`, `∩`, `°`, modular   |
| §2.2   | distributive allegory  | `0`, `∪`                 |
| §2.31  | division allegory      | `R / S`                  |
| §2.4   | power allegory         | `∋`, `Λ`                 |

## Level §2.1 — the Frobenius framework (arXiv:1711.08699, local)

Bonchi, *Functorial Semantics for Relational Theories*. 

| where                 | content                                                                                                  |
| --------------------- | ---------------------------------------------------------------------------                              |
| §4.1, p. 23           | `Rel` is the semantic **universe**, not the syntax — a model is a cartesian bifunctor `F_T → Rel`        |
| Def. 4.15             | a Frobenius theory = signature + inequations, with `ICW` (Frobenius) and `ILCH` bundled in automatically |
| eq. (3), p. 4         | `R;Δ ⊑ Δ;(R⊕R)` and `R;⊥ ⊑ ⊥` — every relation is only a *lax* comonoid homomorphism                     |
| Lemma 4.8, p. 21      | `R` is a map iff it has a right adjoint, and the adjoint is `R†` — the shunting rule                     |
| Cor. 4.5, p. 21       | lax squares commute strictly once the arrows are maps                                                    |
| §7, p. 37             | the fragment `⊤, ∩, †, ;, id` *"coincides exactly"* with the algebra of relations, citing Freyd [12]     |

Because `Rel` is the target and not the presented category, there is no completeness theorem to lean on here: you get
soundness of diagram reasoning in `Rel(Set)`, not a diagrammatic axiomatisation of it.

**Equation (3) is not new mathematics.** Both halves are in the book, in the product-free encoding:

```
R ; ⊥  ⊑  ⊥                    // §2.152's step "p_α is maximal in (α,λ), hence R p_β ⊆ p_α"
R ; Δ  ⊑  Δ ; (R ⊕ R)          // the instance S := π₁°, T := π₂° of §2.136's  R(S ∩ T) ⊑ RS ∩ RT
```

Equality in the two cases is Freyd's **entire** and **simple** (§2.13) — the paper's "total" and "single valued". Lean:
`Entire`/`Simple`/`Map` at `Freyd/S2_10.lean:408`, `:417`, `:420`; §2.136 as `simple_dist_inter` at `:476`.

**The framework's own stated limit**, §7 p. 37: the operations beyond the black structure are *"not exactly the same:
`⊥` is not the empty relation and `⊳` is not the union"*, closing with *"We believe that the connection with relational
algebra is worth exploring further."* So union is not merely undrawn here — this paper does not have it.

**Notation clash.** In this paper `(−)†` is the converse (p. 19: *"`R†` is just the opposite relation"*). The `(−)°` of
§7 is **colour swap**, is listed against *complement*, and the paper warns it *"does not preserve the posetal structure
— it is not true in general that `R ≤ S` entails `S° ≤ R°`"*. Freyd's `R°` is the paper's `R†`. Use `†` when quoting it.

## Level §2.2 — tape diagrams solve union (arXiv:2210.09950, local)

Bonchi, *Deconstructing the Calculus of Relations with Tape Diagrams* (2022). This is the
one place union is genuinely diagrammatic, and it is sound **and complete**:

- Theorem 7.5 / Corollary 7.8: the tape axioms *"prove all and only the valid equivalences between expressions of
  CR"*, where CR is the **positive fragment** of Tarski's calculus of relations — `;`, `∩`, `∪`, `⊤`, `⊥`, `°`, `id`.
  That fragment is exactly Freyd §2.2.
- Mechanism: a rig category with two monoidal products — `⊗` carries `∩` (copy and merge on the same product), `⊕`
  is the biproduct and carries `∪`. Tapes are "string diagrams of string diagrams": a whole circuit is wrapped, and
  the tape forks for choice.
- Why two layers are unavoidable: a string diagram is the language of *one* monoidal category. `∩` reuses `⊗`; `∪`
  needs the second product, so it needs the second layer.
- Not in it: complement, residuals, Kleene star. The conclusion names iteration as the next step — *"the extension of
  CR with Kleene star … can be obtained by adding a trace to the monoidal structure given by `⊕`"*.

## Level §2.31 — division *is* diagrammatic (arXiv:2401.07055, local)

Bonchi, *Diagrammatic Algebra of First Order Logic* (2024) — the calculus of
**neo-Peircean relations**. Abstract: *"a string diagrammatic extension of the calculus of binary relations that has
the same expressivity as first order logic and comes with a complete axiomatisation. The axioms are obtained by
combining two well known categorical structures: cartesian and linear bicategories."*

It has the whole Tarski signature: `∪`, `∩`, `⊥`, `⊤`, converse `(·)†`, and complement `R̄ = {(x,y) | (x,y) ∉ R}`.
Residuals come out of the linear structure, §5:

```
a⊥                     the right linear adjoint of a           // written with the black composition ,•
b ,• a⊥ : Z → X        the left residual of b : Z → Y by a      // greatest arrow making the square commute laxly
c ,◦ a ≤ b   ⟺   c ≤ b ,• a⊥                                   // the division adjunction, drawn
Lemma 5.4              a ≤ b  iff  id_X◦ ≤ b ,• a⊥
```

**How this escapes the variance obstruction.** The argument that blocked division was: every operation of the
*monotone* calculus — `;`, `⊗`, cups, caps, spider fusion, `†` — is monotone in each hole, while `R/S` is antitone in
`S`. That argument is correct and this paper does not contradict it; it deliberately leaves the monotone fragment by
adding two things: an order-reversing generator (complement, drawn as a colour switch — Peirce's "cut") and a *second*
composition `,•` alongside `,◦`, i.e. a linear bicategory in the sense of two composition operations. The residual is
then not a monotone composite at all, which is why it can exist.

The bridge to Freyd is explicitly *open*, per §10: *"The connection with allegories [29] is also worth to be explored:
since cartesian bicategories are equivalent to unitary pretabular allegories, Prop. 6.5 suggests that fo-bicategories
are closely related to Peirce allegories [58]."* [29] is Freyd & Scedrov, [58] is Olivier & Serrato, *Peirce
allegories* (1997). Bird & de Moor is reference [2]. So: division allegory ↔ fo-bicategory is conjectural, not proved.

## Level §2.4 and recursion — the one real gap

`Λ` needs the power object, not just division, and nothing above has it. Folds and hylomorphisms are absent from every
language here: these are papers about presenting algebraic *theories* and logical fragments, not recursion schemes.
The tape paper is the only one that names iteration, as future work — *"the extension of CR with Kleene star … can be
obtained by adding a trace to the monoidal structure given by `⊕`"*.

Getting a hylomorphism and a relational composite into one picture is the actual open problem in this programme.
(Hinze & Marsden's *Introducing String Diagrams* is often reached for here. It is a 2-categorical calculus — wires are
functors, boxes natural transformations — so at best it would draw folds on a different sheet from the one where a
wire is a set. Whether it treats catamorphisms at all is **unverified**: no copy on hand, no network access.)

## The three papers are compatible, by construction

They are the same group building one tower on one base — the **cartesian bicategory** of Carboni & Walters (1987).
Same generators `◀, !, ▶, ¡`, same diagram conventions, same `Rel` semantics; each layer keeps the one below.

```
CB_Σ                                        the free cartesian bicategory on Σ      §2.1     1711.08699
CB_Σ wrapped in tapes  (⊗ inside, ⊕ outside)  + biproduct                            §2.2     2210.09950
CB_Σ + cocartesian + linear = fo-bicategory   + complement, second composition       §2.31    2401.07055
```

The FOL paper restates the functorial-semantics setup verbatim: *"`CB_Σ` is the free cartesian bicategory generated by
Σ and, like in Lawvere's functorial semantics, models are morphisms of cartesian bicategories `M : CB_Σ → Rel◦`"*. The
tape paper builds `TCB_Σ` by wrapping the same `CB_Σ` (its Example 6.12), and its Definition 7.1 asks for *"rig
categories where `⊗` forms a cartesian bicategory and `⊕` a [biproduct]"*.

So learning the Frobenius/`CB_Σ` layer first is not wasted work — both extensions assume it. What is *not* settled is
whether the two extensions combine with each other: tapes give `∪` by a second monoidal product, fo-bicategories give
`∪` by cocartesian structure in one layer. Nothing here reconciles the two presentations.

## Verdict

| AOP needs                  | Freyd level | diagrammatic status                                          |
| -------------------------- | ----------- | ------------------------------------------------------------ |
| `;`, `∩`, `°`, `⊤`, maps   | §2.1        | done, sound, and the fragment is faithful (1711.08699 §7)     |
| `∪`, `⊥`                   | §2.2        | done and complete for the positive fragment (2210.09950)      |
| `R / S`, `R \ S`           | §2.31       | done and complete, at the cost of leaving the monotone fragment (2401.07055) |
| `Λ`, power transpose       | §2.4        | open                                                          |
| folds, hylos, `μ`          | —           | open — nothing internal to `Rel`; the real gap                |

The allegory-side dictionary for the bottom two rows does not exist yet; §10 of 2401.07055 lists it as future work.

## Sources

| status         | file / reference                                                                                        |
| -------------- | ------------------------------------------------------------------------------------------------------- |
| local, primary | `functorialSemanticsForRelationalTheories.pdf` — Bonchi, Pavlović, Sobociński, arXiv:1711.08699 (2017)   |
| local, primary | `2210.09950v1.pdf` — Bonchi, Di Giorgio, Santamaria, *Deconstructing the Calculus of Relations with Tape Diagrams* |
| local          | `Frobenius.pdf` — notes stating the Carboni–Walters cartesian-bicategory axioms as [CW87]                |
| local          | `point-free-calculational-proofs-…-graphical-syntax.pdf` — Mota, Paixão, Martelotte, JFP 35 e13 (2025), doi:10.1017/S0956796825000085 |
| local, primary | `DiagrammaticAlgebraOfFirstOrderLogic.pdf` — Bonchi, Di Giorgio, Haydon, Sobociński, arXiv:2401.07055 (2024) — residuals, complement, complete for FOL |
| local          | `GraphicalConjunctiveQueries.pdf` — Bonchi, Seeber, Sobociński, arXiv:1804.07626 (2018) — the `∃∧` fragment |
| unverified     | Carboni & Walters, *Cartesian bicategories I*, JPAA 49 (1987) — the origin of the axioms, cited as [16]/[18] by all three papers above |
| unverified     | Olivier & Serrato, *Peirce allegories* (1997) — cited as [58] by 2401.07055 as the likely allegory counterpart |
| unverified     | Hinze & Marsden, *Introducing String Diagrams*, CUP (2023) — 2-categorical; whether it covers folds is unchecked |

"Unverified" means the title, authors, or year come from memory or from another paper's reference list, and were not
checked against a copy — no network access to arXiv from this repo. Check before citing in writing.

The JFP paper is the closest existing instance of this programme: point-free program derivation in a graphical
syntax, citing Bird & de Moor, carried out in `LinRel_ℝ` rather than `Rel(Set)`. Its lattice is the subspace lattice
— modular but not distributive, so no union and no complement — which is why it never has to solve the §2.2 problem.
