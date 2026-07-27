# States: PQP's `I → A` vs Freyd's coreflexives

Coecke & Kissinger (*Picturing Quantum Processes*, §3.4.1) call a process with no input a STATE, one with no output an EFFECT, and
one with neither a NUMBER. This note works out what each becomes in an allegory. Short answer: a state is a **subobject**, and Freyd
reaches it through coreflexives rather than through a terminated wire.

```
   PQP state  ψ : I ⟶ α            Freyd coreflexive  A ⊑ 1_α

        │ α                              │ α
     ┌──┴──┐                          ┌──┴──┐
     │  ψ  │                          │  A  │
     └─────┘                          └──┬──┘
                                         │ α
   the wire starts here            the wire passes through, filtered
```

## Why "no wire" means the one-element set

PQP's Example 3.35 says "since 'no wire' means the single element set `{*}` (see Section 3.3.1)". The reason is that a missing wire
is not *nothing* — it is the wire of the monoidal unit `I`, drawn invisibly. In the process theory of functions the monoidal product
is cartesian product, so the unit is forced by

```
I × α ≅ α        // the system whose presence changes nothing
```

and `{*}` is the only set with that property: `∅ × α = ∅`, and a two-element `I` would double `α`. Two further checks confirm it is
the right choice rather than a convention:

- **It carries no information.** A system of type `{*}` has exactly one possible configuration, so naming its state says nothing.
  A wire that cannot carry information need not be drawn. Drawing it instead of nothing is harmless — the coherence isomorphism
  `I × α ≅ α` makes the two readings equal, and string-diagram notation is sound modulo exactly those isomorphisms.
- **It makes "state" mean "element".** Functions `{*} → α` biject with elements of `α`, which is the whole point of §3.4.1. With
  `I = ∅` there would be exactly one function `∅ → α` and no elements at all; with a two-element `I` you would get pairs.

Example 3.35 then reports the degenerate consequences for functions: effects `α → {*}` are unique, so "effects are boring", and
numbers `{*} → {*}` number exactly one, so "numbers are boring". That is a fact about `Set`, not a defect in the convention —
Example 3.36 keeps the same `{*}` and relations give 4 states, 4 effects and 2 numbers on the two-element set.

## Freyd's unit

`λ` is a UNIT (§2.15) if `1_λ` is its largest endomorphism (a PARTIAL UNIT) and every object is the source of an entire morphism
into `λ`; an allegory with one is UNITARY. §2.152 shows `λ` is a terminator in `Map(𝐀)`, so it plays the `{*}` role. States are then
`(λ, α)`, Freyd's notation for the hom-set, and §2.152 identifies them with coreflexives via `Dom R = 1 ∩ RR°`:

```
ψ : λ ⟶ α       ↦   1_α ∩ ψ°ψ  ∈ Cor(α)        // the subset ψ picks out, as a partial identity
A ⊑ 1_α         ↦   p_α° A     ∈ (λ, α)        // restrict the maximal state p_α° along A
```

`Cor(α)` is the coreflexives on `α`, which §2.1 identifies with the subobjects of `α`. So a state *is* a subobject.

## Dictionary

| PQP                  | allegory (unitary `𝒜`, unit `λ`) | in `Rel(𝒮)`              |
| -------------------- | -------------------------------- | ------------------------ |
| `I`                  | `λ`                              | the one-element set      |
| state `ψ : I → α`    | `ψ ∈ (λ, α)`                     | a subset of `α`          |
| effect `π : α → I`   | `π ∈ (α, λ)`, i.e. `ψ°`          | a subset of `α`          |
| number `I → I`       | `(λ, λ) = Cor(λ)`                | a boolean                |
| state then effect    | `ψπ ∈ (λ, λ)`                    | do the two subsets meet? |

The allegory predicates say exactly what one wants about the subset `ψ` names:

```
ψ entire   (1_λ ⊑ ψψ°)     ψ is nonempty
ψ simple   (ψ°ψ ⊑ 1_α)     ψ has at most one element
ψ a map    (both)          ψ is a point — a global element of α, since λ is terminal in Map(𝐀)
```

PQP's "the numbers of the relational process theory are the booleans" is, on Freyd's side, just the partial-unit axiom: every
endomorphism of `λ` is below `1_λ`, so `(λ, λ) = Cor(λ)`, and in `Rel(𝒮)` that is the two subobjects of `1`. Composing a state with
an effect asks whether the two subsets meet — the `∃` of relational composition, division's `∀` being the other side of that coin.

## Why Freyd uses coreflexives instead

A bare allegory has no unit; "unitary" is an extra axiom introduced only in §2.15, well after the theory is running. Coreflexives
need nothing but the order, since `R ⊑ 1` is always meaningful. So `Dom R = 1 ∩ RR°` is the unit-free replacement for "the state
that `R` prepares", and every result about `Dom` holds in allegories where a state cannot even be written. Terminating a wire is a
luxury; putting a loop on it is not.

## In the repo

| declaration                                             | file                                |
| ------------------------------------------------------- | ----------------------------------- |
| `Coreflexive`, `dom`                                     | `Freyd/S2_10.lean:189`, `:325`      |
| `PartialUnit`, `IsUnit`                                  | `Freyd/S2_10.lean:541`, `:545`      |
| §2.151 injectivity of `Dom`                              | `dom_injective_partial_unit` `:983` |
| §2.151 `Dom R = Dom S → R = S`                           | `dom_eq_iff_eq_of_partial_unit` `:999` |
| §2.35 symmetric division `R /ₛ S` (the `∀` counterpart)  | `Freyd/S2_30.lean:203`              |
