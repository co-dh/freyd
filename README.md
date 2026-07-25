# Freyd and Algebra of Programming in Lean

This repository formalizes two related bodies of work in Lean 4:

- Peter Freyd and Andre Scedrov's *Categories, Allegories*;
- Richard Bird and Oege de Moor's *Algebra of Programming*.

The goal is to turn the books' definitions, notation, and arguments into a
machine-checkable reference. Besides supporting formal verification, the
corpus can be given to an AI assistant as grounded context for studying the
books, tracing dependencies, and answering questions more reliably than from
the prose alone.

## Layout

- `Freyd/` — the core formalization of *Categories, Allegories*, organized by
  book section.
- `AOP/` — the *Algebra of Programming* development.
- `leet/` — algorithm case studies derived with the AOP machinery.
- `rel/` — a relation-algebra interpreter, examples, and derivation tools.
- `graph/` — declaration and dependency data extracted from the Lean sources.

The project follows the books' terminology and diagram-order composition
convention: `xy` means “first `x`, then `y`.”

## Build

Install [Lean 4](https://lean-lang.org/) through
[elan](https://github.com/leanprover/elan), then run:

```sh
lake build
```

The repository is self-contained and intentionally mathlib-free; its Lean
version is pinned in `lean-toolchain`.
