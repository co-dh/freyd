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
- `graph/` — an interactive, Obsidian-style knowledge graph of declarations
  and their dependencies, implemented in JavaScript.
- `Freyd/tool/LeanRefactor.lean` — a Lean-aware refactoring tool for safe
  moves, renames, parameter changes, and unused-code cleanup.

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

## Tools

Explore the knowledge graph in a browser with:

```sh
scripts/lean-graph
```

Run `scripts/lean-refactor` without arguments to see the available
refactorings. Changes are previewed by default and applied only with
`--apply`. The tool itself lives in a sibling repository,
[lean-refactor](https://github.com/co-dh/lean-refactor) — it carries no book
content, so it was promoted out; the script runs it against this repository.
