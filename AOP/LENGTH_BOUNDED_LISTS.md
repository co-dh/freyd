# Lists of length at least k: which representation

Design question (2026-10-11), raised by B&dM §8.6 bitonic tours: the note printed `head(wrap(p))` for a journey, and
the user asked whether to define a list type per length bound (with its own `wrap`, `cat`), use a dependent type, or
use ordinary lists with partial functions. Analysis by a fable agent.

## Facts from the index

- `ConsList L E` is ONE inductive (`AOP/A6_ConsList.lean:26`) with one fold stack shared by every base (`cataFold`,
  `cataR`, `initial`, `cata_converse_eq`, `consFold_unique`, `cfold`, `F_eq_relator`, GreedyDP/DPCount — about 60
  generic declarations). Base functor `CL.F L E X = L + E×X`.
- Bases in use:

  | base `L`    | type                          | where                                                  | decls |
  |-------------|-------------------------------|--------------------------------------------------------|-------|
  | `Unit`      | `[A]`, `wrap () = []`         | AOP, leet, rel                                         | ~700  |
  | `A`         | `NEList A`, `wrap a = [a]`    | `A5_6_ListCombinators:636`; A9_3_Bracket, A8_2, A8_5   | ~240  |
  | `City×City` | `Journey`, `wrap (a,b)=[a,b]` | `A8_6_Tour` only                                       | 44/77 |
  | `List A`    | nets                          | `A8_2_Exec`                                            |       |

- Nothing is re-declared per length bound for `wrap`, `cons` or the fold.
- Duplicated per base today:
  - the elementwise relator: `listP` / `nelistP` / `journeyP` + `journeyRel` + `journeyRelator`
    (`A8_6_Tour.lean:67-141`, 75 lines re-proving id/comp/mono);
  - `head`, 5 copies: `A8_2:447` (graph of total `headOf` on `ConsList A A`), `A8_5:80`, `A8_6:144`,
    `A9_2_Edit:1547` (`[Inhabited]` default), `A7_5_Van:207` (`headR`, a partial relation `∃ t, p = cons s t`);
  - `cat`: `A5_6:224` (relation on `[A]`), `A9_3:55` (function on `NEList`, own `cat_cons`/`cat_ne_wrap`).
- `A5_6:631` already names the cure: the two-parameter relator `cl(Rl,Re)`, `list = cl(𝟙,R)`, `list⁺ = cl(R,R)`,
  deferred only to keep stmt_keys.
- Theorem 8.2 as formalised, `thinningList` (`A8_3.lean:1539`):
  - base `CL.F L E`, fold carrier `A` free;
  - algebras `graph fᵢ ≫ pᵢ` with `fᵢ : L ⊕ E×A → A` TOTAL functions and `pᵢ` coreflexive on the output;
  - `hQ : preorder Q` (reflexive and transitive on ALL of `A`).
  `tour_laws` (`A8_6:586`) passes `p₁ = p₂ = 𝟙`, `Q = Qc`, and needs `Qc_refl : 𝟙 ⊑ Qc`.
- B&dM p.213: the INPUT's base functor is `FA = (City×City) + (City×A)` under every option; only the carrier `Tour` is
  in question. B&dM's tours are pairs of ordinary lists, `start(a,b) = ([a,b],[a,b])`, `head` the ordinary head.

## The four options

**(a) one generic type, the base `L` as the length bound (current).**
- Fold: free.
- Proofs: `cases x <;> rfl` for `head`/`next`/`replaceHead`/`cost_dropl`; `Qc_refl` trivial.
- DRY: fold shared; relator, `head`, `cat` not yet (fixable generically).
- Note: `Journey(City) ≜ μF`, the same `F` as the input. But it prints `start(a) ≜ (wrap(a),wrap(a))` and
  `head(wrap(p)) = π₁(p)` where the book writes `[a,b]`. `wrap` here is the base constructor; B&dM's `wrap(x) = [x]`
  is `singleR` (`A6_ConsList:450`) — a printing clash, not a semantic one.
- One departure from the book: `dropl` is total.

**(b) dependent type: subtype `{x : [City] // 2 ≤ len x}` or a length-indexed vector.**
- The carrier stops being an initial algebra: `cons a` on a journey carries a proof, every `cases` becomes
  `obtain ⟨x,hx⟩` plus arithmetic.
- Needs a fresh relator and `head`/`len` lemmas for the subtype.
- The diagram exporter has no wire for a subtype (wires come from the base functor).
- Highest proof burden, worst DRY, no book precedent. Rejected.

**(c) B&dM literally, `head` total via `Option` or an `[Inhabited]` default.**
- `Qc`, `cost_dropl` and the printed note carry a value the book never wrote (`head(nil) = default`).
- `cost_dropl` is false on junk tours, so `tour_mono_*` needs a coreflexive "both journeys have length ≥ 2" the book
  does not have.
- Strictly worse than (d).

**(d) ordinary lists, partial `head`/`dropl` as simple relations (no `Option`; repo idiom `Van.headR`).**
- `head x a ↔ ∃ t, x = [a]⧺t`, `dropl (a,(x,y)) t ↔ ∃ b x', x = [b]⧺x' ∧ t = ([a]⧺x',[a]⧺y)` — the book's equations
  verbatim.
- `Tour`'s relator is `list×list` for free (the 75 lines of `journeyP` go); `start(a,b) = ([a,b],[a,b])` prints as in
  the book.
- Two real costs, both outside §8.6:
  1. `thinningList` takes `graph fᵢ` of TOTAL functions; it must be generalised to simple `φᵢ` (A8_3, also under
     §8.5's `para_laws`).
  2. `preorder Qc` on all of `[City]×[City]` is FALSE with a partial `head` (`head₂ head₂°` is not reflexive at
     `([],y)`), so `hQ` must become the in-context form of `Λ_comp_thinRel_context` (`A8_1.lean:546`, `Q ∩ S°S`) —
     a new Theorem 8.2 variant.
- Plus all 77 declarations of A8_6 and its 25 note citations (`diag/aop/08-thinning.typ`) re-keyed.

## Recommendation: keep (a)

There is no "type per k" to define: the base type is the length bound, and `wrap`/`cons`/fold exist once. A length-≥2
carrier is the book's own p.214 sentence ("both parts have lengths at least two") stated as a type; that is what makes
`head`/`next` total and `Qc` reflexive without touching Theorem 8.2. Concrete change for §8.6:

1. Printing only, no stmt_key moves: a delab beside `delabWrapRAsNil` (`A6_ConsList.lean:504`) printing
   `ConsList.wrap (a,b)` at base `A×A` as `[a,b]`, so the note reads `start(a,b) ≜ ([a,b],[a,b])`,
   `head([a,b]) = a`, and `wrap` no longer names a base constructor anywhere in the note.
2. DRY: delete `journeyP`/`journeyRel`/`journeyRelator` (`A8_6:67-141`) and instantiate the generic two-parameter
   relator `cl(R×R,R)` (`Poly.relator (clF L)`, `F_eq_relator` `A6_ConsList:89`) — the refactor `A5_6:631` already
   names. It serves `list`, `list⁺` and `Journey` alike; next, one `head`/`cat` over `L`.

Revisit (d) only if `thinningList` is generalised to simple relations for some other section anyway.
