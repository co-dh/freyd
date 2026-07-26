# PQP reading list, for AOP and visualizing `Rel(Set)`

Goal: do Algebra of Programming, and visualize `Rel(Set)` diagrammatically. `AllegoryStringDiagrams.typ` already covers the
Frobenius generators, converse-as-bending, meet-as-convolution, and the map inequations — so read *Picturing Quantum Processes*
only for the parts that ground or extend that. About 70 pages out of 900. Companion note: `Freyd/note/state.md`.

## Read

| section                | what it gives                                                                        |
| ---------------------- | ------------------------------------------------------------------------------------ |
| §3.3.1–3.3.4           | Sets, Functions, Relations, Functions vs. relations — `Rel(Set)` as a process theory |
| §3.4.1–3.4.3           | states/effects/numbers, zero diagrams, processes equal "up to a number"               |
| §4.1.1–4.1.4           | separability, process–state duality, the yanking equations, string diagrams           |
| §4.2.1–4.2.3           | the transpose, transposition of composite systems, trace and partial trace            |
| §4.3.1–4.3.2           | adjoints and conjugates — which of the three reflections `R°` actually is             |
| §4.6.2, §4.6.3\*       | dual types and self-duality; dagger compact closed categories — the `b*` question     |
| §8.2.2–8.2.4, §8.6.1\* | copying and deleting, spiders, "if it behaves like a spider it is one", Frobenius     |

Ignore the quantum framing around the spider material in §8.1 and §8.3–8.5.

Two of these hit gaps in `AllegoryStringDiagrams.typ` directly:

- Its §6 says union and `⊥` cannot be drawn. PQP §3.4.2, "Saying the impossible: zero diagrams", is precisely about `⊥`.
- Its §1 *posits* the Frobenius structure. §8.2.3–8.2.4 plus §8.6.1 derive it, including the converse direction — anything behaving
  like a spider is one.

## Skip

Ch. 5 (bases, matrices, Hilbert spaces), Ch. 6–7 (quantum maps, measurement), Ch. 9–14 (phases, ZX, protocols, computation). None of
it touches `Rel`.

## *Picturing Quantum Software* — not for this

Checked its table of contents. PQS is strictly less useful than PQP for AOP, on two counts. It opens from Hilbert spaces (§2.1.2)
rather than building a general process theory, so `Rel` never appears as an example at all; and everything from Ch. 3 on is
ZX-calculus, Clifford circuits, stabiliser theory, circuit synthesis, measurement-based computation and error correction. The
order/residual gap is the same as PQP's, with the relational content removed.

Two sections are worth knowing about anyway:

| section                | why                                                                                       |
| ---------------------- | ----------------------------------------------------------------------------------------- |
| §3.1.1–3.1.5           | spiders, symmetries, scalars, adjoint/transpose/conjugate — spiders as primitives, faster than PQP Ch. 8, but Z/X-coloured and phase-carrying, so there is noise |
| §3.6.1                 | formal rewriting and soundness — the model to copy if `AllegoryStringDiagrams` is ever to become a real rewriting calculus |

## What PQP will not give you — the half AOP runs on

PQP's calculus is **equational**; AOP is **inequational**. There is no order on processes anywhere in the book, hence no residuals,
hence no `Λ`. Concretely, AOP p.107's

```
ΛR = (∈\R) ∩ (R\∈)°        // = Freyd's R /ₛ ∋, noted at AOP/A4_6.lean:11
```

needs division, and division is not drawable in the monotone fragment: every diagram operation — `;`, `⊗`, cups, caps, spider
fusion, `°` — is monotone in each hole, while `R/S` is antitone in `S`. Catamorphisms and hylomorphisms are absent from PQP too.

Sources for the missing layer, the status of each one, and which Freyd level it reaches:
`Freyd/note/diagrams-for-aop.md`.

## One trap, while reading §4.1.2

Two different things get called the transpose:

```
process–state duality   R : A → B  ↦  a STATE of A ⊗ B      // the graph of R as a subset of A × B; a bent wire
AOP's Λ                 R : A → B  ↦  a FUNCTION A → P B     // the power adjunction
```

Different adjunctions — compact closure versus the power adjunction — and only the first is a bent wire.
