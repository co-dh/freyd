# `⟦−⟧` as a Lean function: design

Scope: `leetq/LeetQ/Run/Lang/*`, `leetq/LeetQ/Rel/Lang/*`, read at master `a4eb3d5`. Nothing here is
implemented; D2's canonical tables (7.1) are in progress. Decided: D1 = T, D2 = C.
Composition is in diagram order: `R S` is first `R` then `S` (`≫` in Lean).

## 0. What the code already has

| fact                                                                                   | where                         |
|----------------------------------------------------------------------------------------|-------------------------------|
| `Tm.den : Tm A B d → A.El → B.El → Prop` exists, structural, total                     | `Rel/Lang/BitsSpec.lean:21`   |
| it covers `val comp conv meet join diff ldiv`, and is `False` at every other node      | same                          |
| `rep_tableC`, `rep_runC`, `PSound` are stated against it, `rep_tableC` by `induction`  | `BitsSpec.lean:34`, `GenSpec` |
| `Den A B` is the `RelSet.{0}` hom `⟨A.El⟩ ⟶ ⟨B.El⟩`                                    | `GenSpec.lean:23`             |
| every `Gen.*_sound` lemma has the shape `Sound parts → Sound (Gen.op parts) T`         | `GenSpec.lean`                |
| the code of a term is a `Lean.Expr` built by `Expand.code`/`node`/`planOr` (`partial`) | `Run/Lang/Expand.lean:611`    |
| `Freyd.Alg.AllegoryFunctor` (`obj map map_id map_comp map_recip map_inter`)            | `Freyd/S2_147_MapCat.lean`    |
| `Tm.id : Tm A A true`, `Tm.conv : Tm A B false → Tm B A false`                         | `Run/Lang/Tm.lean`            |
| `var`, `prim`, `call`, `arg` are NOT intrinsically typed: any `A`, `B` is accepted     | `Run/Lang/Tm.lean`            |
| `Rel.Holds` already depends on `Classical.choice` (through qlean's `Carrier`)          | `Rel/Rep.lean:53`             |

Consequences:
- `⟦−⟧` is not a new concept. It is the existing `Tm.den` with its `False` clause replaced by a real clause per
  constructor. The bit-matrix proofs keep using the same function.
- The reason there is one `rep_` proof per program is not the missing `den`. It is that `code` is not a Lean
  function of the term, so no theorem can quantify over the term. Decision D1 = T (section 3) makes it one.

## 1. Domain and codomain

### 1.1 Recommended shape

```lean
-- Rel/Lang/Den.lean (new file; `Den` moves here from GenSpec, `Tm.den` from BitsSpec)
abbrev Den (A B : Obj) := (⟨A.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩
abbrev Sem := (X Y : Obj) × Den X Y                  -- a meaning with its objects, as `Res` is a term with its
abbrev Val := Nat → (A B : Obj) → Den A B            -- the variable `k` read at the type the term asks for

def Val.bind (ρ : Val) (k : Nat) {A B : Obj} (X : Den A B) : Val := fun k' A' B' =>
  if h : k' = k ∧ A' = A ∧ B' = B then h.2.1 ▸ h.2.2 ▸ X else ρ k' A' B'

/-- `⟦t⟧` under `ρ`; `as` the meanings of the relations a row of `prims` was given (`Tm.arg`). -/
def Tm.denA (ρ : Val) : {A B : Obj} → {d : Bool} → Tm A B d → List Sem → Den A B
def Tm.den (ρ : Val) {A B : Obj} {d : Bool} (t : Tm A B d) : Den A B := t.denA ρ []
notation "⟦" t "⟧" ρ => Tm.den ρ t
```

| question                      | answer                                                                                |
|-------------------------------|---------------------------------------------------------------------------------------|
| what `⟦−⟧` takes              | `Tm A B d` as it is. No new typed core.                                               |
| the demand bit `d`            | ignored by `den`. It says how a term runs, not what it means; `Sound` reads it.       |
| the untyped leaves            | `var k` reads `ρ k A B`. A request at the wrong type gets the outer `ρ`, never a cast. |
| what it returns               | `Den A B`, a `RelSet.{0}` arrow.                                                      |
| `share k R`, `own R`          | `⟦R⟧`.                                                                                |
| `call`, a non-row `arg`       | `𝟘` until stage 5; their code has ok bit `false` there, so `Sound` holds vacuously.   |

A typed-request valuation needs `DecidableEq Obj` only inside `Val.bind`. `Expand.checkOf` already uses that
instance.

### 1.2 The clauses

Each clause is the `T` of the `Gen.*_sound` lemma of that node. A `T` that is more than a `RelSet` operator
becomes one named definition that both the clause and the lemma cite (`ldivDen` is already written this way).

| node                          | `⟦t⟧ρ`                                                  | lemma that is the induction case |
|-------------------------------|----------------------------------------------------------|----------------------------------|
| `val R`                       | `rep R`                                                  | `val_sound`                      |
| `uni U`                       | `rep (idU U)`                                            | `uni_sound`                      |
| `zero`, `id`                  | `𝟘`, `𝟙 _`                                               | `zero_sound`, `id_sound`         |
| `top V`                       | `relTop ≫ ⟦V⟧`                                           | `top_sound`                      |
| `outl`, `outr`                | `graph Prod.fst`, `graph Prod.snd`                       | `outl_sound`, `outr_sound`       |
| `comp R S`                    | `⟦R⟧ ≫ ⟦S⟧`                                              | `comp_sound`, `compB_sound`      |
| `conv R`                      | `⟦R⟧°`                                                   | `conv_sound`                     |
| `meet`, `join`                | `⟦R⟧ ∩ ⟦S⟧`, `⟦R⟧ ∪ ⟦S⟧`                                  | `meet_sound`, `join_sound`       |
| `diff R S`                    | `diffDen ⟦R⟧ ⟦S⟧`                                        | `diff_sound`, `diffB_sound`      |
| `dom R`, `ran R`              | `𝟙 _ ∩ ⟦R⟧ ≫ ⟦R⟧°`, `𝟙 _ ∩ ⟦R⟧° ≫ ⟦R⟧°°`                  | `dom_sound`, `ran_sound`         |
| `ldiv`, `rdiv`                | `ldivDen …`, `rdivDen …` (relative to the universes)     | `ldivB_sound`, `rdiv_sound`      |
| `pair`, `prod`                | `rpair ⟦R⟧ ⟦S⟧`, `rprodMap ⟦R⟧ ⟦S⟧`                      | `pair_sound`, `prod_sound`       |
| `junc`, `juncD`               | `Freyd.Alg.junc (sumCop _ _) ⟦R⟧ ⟦S⟧`                    | `junc_sound`; `juncD`: missing   |
| `nil`, `atPos k`              | `nilDen`, `atDen k`                                      | `nil_sound`, `atPos_sound`       |
| `succ`, `arith`, `leq`, `lt`  | `succDen ⟦U⟧` …                                          | `succ_sound` … `lt_sound`        |
| `est Q`, `fold e S`           | `estDen ⟦Q⟧`, `foldDen ⟦e⟧ ⟦S⟧`                          | `est_sound`, `fold_sound`        |
| `lam R`, `E R`, `thin Q`      | `lamDen ⟦R⟧`, `EDen ⟦R⟧`, `thinDen ⟦Q⟧` (section 7.1)    | missing; D2 = C makes them total |
| `foldI`, `flat`               | `foldIDen …`, `flatDen ⟦R⟧`                              | missing                          |
| `prim r` under `arg`s         | `Row.den` of the row `r` at `A`, `B`, `as` (1.3)         | the row's `sound` field          |
| `var k`                       | `ρ k A B`                                                | the hypothesis `Env.Sound`       |
| `mu k _ _ b`, `refold k _ _ b` | `lfp fun X => ⟦b⟧(ρ.bind k X)`                          | new, from `CRel.rep_fixOn`       |
| `nu k S b`                    | `gfp fun X => ⟦b⟧(ρ.bind k X)`                           | new, from `CRel.rep_fixOn`       |

### 1.3 The rows of `prims`

`Prim` holds a `Lean.Name` (`sig.1`, `sound`). No Lean function can go from a name to a relation, so a row's
meaning has to be a field of a typed record.

```lean
-- Rel/Lang/GenSpec.lean
abbrev Code := (X Y : Obj) × (e : Bool) × Fn e X Y
/-- A row of `prims` with its code, its meaning and the proof, each at the type asked for. -/
structure Row where
  sym   : String                                            -- the key of its `Prim`
  run   : (A B : Obj) → List Code → Option (Fn true A B)    -- what `Expand.primE` finds by unification today
  den   : (A B : Obj) → List Sem → Den A B
  sound : ∀ A B cs ss f, Args.Sound cs ss → run A B cs = some f → Sound f (den A B ss)
def rows : List Row
```

- `Row` replaces three things: `Prim.sound : Option Lean.Name`, the `run_cmd` that checks the name is declared,
  and the wrapper search `primE`/`fitConst`/`primWrappers`. The lemma is type-checked where the row is written.
- A row's `run` and `den` match `A`, `B` against the row's object pattern and return `none` / `𝟘` otherwise.
  `prim%` already reads the constant's type; it can write both matches, so a row stays one line.
- `Prim` (in `Run`, read by the parser and the elaborator) keeps `sym sig conv written prelude aop mono`.

### 1.4 `RelSet` or any allegory

Recommendation: `RelSet` now, and no generic target until decision D3 is taken.

| point                        | `Tm.den` (this design)                    | `Calc.toTerm`                                  |
|------------------------------|-------------------------------------------|------------------------------------------------|
| domain                       | `Tm A B d`: typed, objects are `Obj`      | `Lang.Expr`: surface term, objects are Lean's  |
| kind of map                  | a Lean function                           | a `TermElabM` translation to notation          |
| codomain                     | `RelSet.{0}`                              | any allegory with the instances the term needs |
| `𝒫A`                         | `List A.El`, the same object as `[A]`     | the power object `P A`                         |
| `∋`                          | `fun xs x => x ∈ xs`                      | `PowerAllegory.eps`                            |
| `R\S`, `R/S`                 | relative to two universes (`ldivDen`)     | the book's division                            |
| `R − S`                      | pointwise `∧ ¬`                           | `BooleanAllegory` `sub`                        |
| `⦇e,S⦈`                      | fold from the values of a coreflexive `e` | `relCata [e',S]` over an `InitialAlgebra`      |
| `μ`, `ν`, definitions, calls | covered                                   | refused                                        |

- So `⟦−⟧` is not `toTerm` made total. They agree on `≫ ° ∩ ∪ 𝟙 𝟘 ⟨,⟩ × [,] dom ran inl inr π₁ π₂`, where the
  clause of `den` is literally the `RelSet` instance of the operator `toTerm` writes. They differ on the power
  group, on division and on fold, and the difference is in the meaning, not in the encoding.
- A single generic `den` needs the objects generalised (`Obj` with atoms from a parameter), a bundle of
  `Has*` classes for every operator at every object, and a second model. All `RelSet` instances it would use
  live in `AOP`, which `LeetQ.Rel` does not import; the generic function would have to live in `LeetQAop`.
- The DRY step that is available now: write the allegory clauses of `den` with the class operators (`≫`, `°`,
  `∩`, `∪`, `𝟙`), never pointwise. A later generalisation then replaces `RelSet` by `𝒜` clause by clause.
- The honest link between the two readings is a per-row theorem in `LeetQAop`: where a row has `aop := .ok f`,
  `Row.den = f` at the objects where both are typed. Today that is not stated for any row.

## 2. Totality and termination

| item                              | status                                                                         |
|-----------------------------------|--------------------------------------------------------------------------------|
| `Tm.den`, `Tm.denA`               | structural recursion on `Tm`, as today's `Tm.den`; `as` is an accumulator      |
| `Expand.fv`                       | must become total: `den_congr` (below) is stated with it                       |
| `Expand.mus`, `Expand.number`     | stay `partial`: passes run before the term the theorem is about exists         |
| `Pre.at`, `Pre.nilSrcs`           | stay `partial`: they act on `Pre`, before `build`; no statement here reads `Pre` |
| `μ`, `ν`                          | impredicative, choice-free, defined for every `Φ`                              |
| program calls                     | stage 5: a `let` node, not a name-keyed environment                            |

- `fv` is `partial` only because it recurses through `t.parts`, a `List Res` that hides the structure. Written
  with one clause per binder and one structural clause per shape, it is a `def`. No `Tm.size` is needed.

```lean
def lfp {A B : Obj} (Φ : Den A B → Den A B) : Den A B := fun x y => ∀ Y, (∀ a b, Φ Y a b → Y a b) → Y x y
def gfp {A B : Obj} (Φ : Den A B → Den A B) : Den A B := fun x y => ∃ Y, (∀ a b, Y a b → Φ Y a b) ∧ Y x y

theorem lfp_le  (h : ∀ a b, Φ Y a b → Y a b) : ∀ a b, lfp Φ a b → Y a b
theorem lfp_fix (hΦ : Monotone Φ) : Φ (lfp Φ) = lfp Φ
theorem le_gfp  (h : ∀ a b, Y a b → Φ Y a b) : ∀ a b, Y a b → gfp Φ a b
theorem gfp_fix (hΦ : Monotone Φ) : Φ (gfp Φ) = gfp Φ

/-- `X` occurs only positively in `t`: the `Tm` form of `Pre.polarity`. -/
def Tm.Pos (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Bool
theorem Tm.den_mono (h : t.Pos k) (hXY : X ⊑ Y) : (⟦t⟧ρ.bind k X) ⊑ ⟦t⟧ρ.bind k Y
theorem Tm.den_congr (h : ∀ k ∈ fv t, ∀ A B, ρ k A B = ρ' k A B) : (⟦t⟧ρ) = ⟦t⟧ρ'
```

- `lfp` and `gfp` use no axiom beyond `propext`/`funext` (for the two `_fix` equations). They can live in
  `Freyd/RelSet.lean`; they are placed in `Den.lean` until a second user exists.
- `AOP/A6_FixedPoint` has `LeastPrefixedPoint` and `LeastFixedPoint` as predicates. `LeetQ.Rel` cannot import
  `AOP`, so `LeastFixedPoint (·=·) (·⊑·) Φ (lfp Φ)` is stated in `LeetQAop`, as a bridge.
- `CRel.rep_fixOn` already concludes "a fixed point, below every pre-fixed point that contains `X₀`". With
  `X₀ = 𝟘` that is `rep (fixOn …) = lfp Φ` by `lfp_le` in one direction and the fixed-point equation in the other.
- Choice: `Freyd/` and `AOP/` must be choice-free. `leetq/` is outside that rule and already uses `Classical`
  (`distinct_sound`, `merge_sound`, and `Rel.Holds` itself). `den` adds none except in the clause of `merge`,
  whose `T` is `decide (∃ c, …)`.

## 3. Soundness as one theorem

### 3.1 Decision D1 = T

Today the code of a term is a `Lean.Expr` that the meta-program `Expand.code`/`node`/`planOr` builds
(`Run/Lang/Expand.lean`, `partial`), so `prfNode` has to follow `node` case by case at elaboration time.

- `compile : Tm A B d → Fn d A B` replaces the meta-program: one ordinary structural `def` over the existing `Tm`.
- At elaboration time `rel_program` emits, for each program `p`, a `def` whose body is `compile t_p` fully
  unfolded. The runtime code is the unfolded `CRel` composite, exactly as today: nothing interprets a term at
  run time. The `ev` interpreter was removed on 2026-11-15 ("We can remove interpreter and a lot of proof. It's
  simpler, right? And speed is the same"); T keeps it removed.
- The macro also emits `p = compile t_p`, proved by `rfl`, or by `simp only [compile]` where `rfl` is too slow
  on a large program (5.2).
- Soundness is one theorem by induction on `t`: `compile_sound : (compile t).ok → rep (compile t) = ⟦t⟧`. Each
  case is one existing `CRel.rep_*`/`Gen.*_sound` lemma. A program's `rep` theorem is `compile_sound` plus its
  `rfl` equation; no per-program stitching remains.
- As functors: `rep ∘ compile = ⟦−⟧`. `compile` is a functor from the syntactic category (4.1) to the category
  of canonical `CRel` tables (7.1), and `rep` is a faithful functor from that category to `RelSet`.

| option       | where the term is walked                                         | soundness                                              |
|--------------|------------------------------------------------------------------|--------------------------------------------------------|
| A (rejected) | at run time: `Tm.run` interpreted the term on every call         | one induction, with an interpreter at run time         |
| B (rejected) | at elaboration time, by the meta-program `code` over `Lean.Expr` | per program: no theorem quantifies over a meta-program |
| T (decided)  | at elaboration time, by the Lean function `compile`, unfolded    | one induction, `compile_sound`                         |

### 3.2 Definitions

```lean
-- Run/Lang/Compile.lean (new; replaces Expand.code, node, plan?, planOr, spine, body, share)
abbrev Env := Nat → (A B : Obj) → (d : Bool) → Pl d A B     -- the code side of `Val`
def Env.bind (η : Env) (k : Nat) {A B : Obj} (c : CRel A B) : Env

mutual
/-- `t`'s code: one `Gen` combinator per constructor. -/
def compile (η : Env) : {A B : Obj} → {d : Bool} → Tm A B d → Fn d A B
/-- `t`'s bit-matrix plan where its node has a bit rule, else its table as a leaf (`Gen.pleaf`). -/
def Tm.plan (η : Env) : {A B : Obj} → {d : Bool} → Tm A B d → Pl d A B
end

-- Rel/Lang/GenSpec.lean
def Env.Sound (η : Env) (ρ : Val) : Prop := ∀ k A B d, PSound (η k A B d) (ρ k A B)
/-- Every node of `t` has its lemma: `n.unproved` as a function of the term. -/
def Tm.gap : {A B : Obj} → {d : Bool} → Tm A B d → Option String

theorem compile_sound {η : Env} {ρ : Val} (hη : η.Sound ρ) {A B : Obj} {d : Bool} (t : Tm A B d)
    (hg : t.gap = none) (hp : t.Pos') :
    Sound (compile η t) (⟦t⟧ρ) ∧ PSound (t.plan η) (⟦t⟧ρ)
```

- `η` stays: it binds the variable of a `μ`/`ν` body (7.2) and the earlier bindings of a program (3.3). A
  `fun X =>` callback in the code is unfolded at compile time like every other node.
- `Sound f T` is unchanged: for every coreflexive demand `D` with `(f D).ok = true`, at each key `x` of `D`,
  `rep (f D).rel x y ↔ T x y`. At the full demand of a closed term it is the form of 3.1,
  `(compile t).ok → rep (compile t) = ⟦t⟧`.

### 3.3 The program theorem

- A shared closed sub-term is a let-bound variable: `number`'s `.share k R` is reified as `.var k`, and `η`
  binds `k` to the constant emitted for that binding.
- For each binding `x` of program `n`, `rel_program n` emits three constants. `η.Sound ρ` at the earlier
  bindings is their own `rep_` theorems, with `ρ k = ⟦t_k⟧`. No lemma is chosen per node.

| constant                       | content                                             | proof                                  |
|--------------------------------|-----------------------------------------------------|----------------------------------------|
| `n.x`                          | `compile η t_x` fully unfolded: a `CRel` composite  | —                                      |
| `n.x_eq : n.x = compile η t_x` | the equation                                        | `rfl`, or `simp only [compile]`        |
| `n.rep_x`                      | `rep n.x = ⟦t_x⟧` when `n.x` is ok                  | `compile_sound`, rewritten by `n.x_eq` |

### 3.4 What happens to each piece

| piece                                         | fate                                                               |
|-----------------------------------------------|--------------------------------------------------------------------|
| `Gen.*_sound`, `p*_sound`, `runP_sound`       | survive unchanged: each is one case of `compile_sound`             |
| `demL`, `demR`, `atKeys`, `demP_spec`         | survive: used by those cases                                       |
| the per-row lemmas (`cons_sound`, …)          | survive as the `sound` field of their `Row`                        |
| `ofVals_sound`, `after_sound`                 | survive: they build a row's `sound`                                |
| `const_sound`                                 | survives: the `var` case of a binding bound to an earlier constant |
| `RelRep.prf`, `pprf`, `prfNode`, `lem`, `lemO` | deleted                                                           |
| `Expand.code`, `node`, `plan?`, `planOr`, `spine`, `body`, `share` | deleted; `compile`/`Tm.plan` replace them     |
| `primE`, `fitConst`, `primWrappers`, `fnTy`   | deleted; `Row.run` replaces them                                   |
| `n.rep_x`                                     | kept, same statement with `T` now `⟦t_x⟧`; one application each    |
| `n.unproved`                                  | kept, computed by `Tm.gap`                                         |
| `TestRep`                                     | kept: checks `n.rep_x` for every registered program                |
| `RegEntry.rep`                                | shrinks to the numbered terms; the constant maps go                |

### 3.5 The parallel agent's work

- Its `GenSpec` lemmas (`nil_sound`, `atPos_sound`, `est_sound`, `succ_sound`, `leq_sound`, `lt_sound`,
  `arith_sound`, `fold_sound`) are stepping stones: each is a case of `compile_sound` as written.
- Its ten new `prfNode` arms are superseded at stage 4, when `prfNode` is deleted.
- One adjustment makes the lemmas fit without restating: each inline `T` becomes a named definition
  (`foldDen`, `estDen`, …) that the `den` clause cites. That is a mechanical edit at stage 1.

## 4. Functoriality

### 4.1 The syntactic category

```lean
-- Rel/Lang/Syn.lean
/-- Two terms with one meaning under every valuation. -/
def Tm.Eqv (s : (d : Bool) × Tm A B d) (t : (d : Bool) × Tm A B d) : Prop := ∀ ρ, (⟦s.2⟧ρ) = ⟦t.2⟧ρ
def Syn := Obj
instance : Cat Syn where
  Hom A B := Quot (Tm.Eqv (A := A) (B := B))
  id A    := Quot.mk _ ⟨true, .id⟩
  comp    := Quot.lift₂ (fun R S => Quot.mk _ ⟨R.1, .comp R.2 S.2⟩) …
def Syn.den (ρ : Val) : Freyd.Functor Syn RelSet.{0}      -- `obj A = ⟨A.El⟩`, `map = Quot.lift (⟦·⟧ρ)`
```

- `Syn` is a category and `Syn.den ρ` a functor, faithful jointly over `ρ`. It is the image of `⟦−⟧`, presented
  as a quotient of terms.
- `Syn` is not an allegory, and this is a fact about `Tm`: `conv` exists only at `d = false`, and `id` only at
  `d = true`. The fragment that is an allegory is the closed terms between declared finite objects, with
  `uni U` as the identity of `(A, U)`. `AllegoryFunctor` is the existing concept for that fragment (D4).
- The free allegory in the sense of `doc/rel-semantics.typ` (terms modulo the allegory axioms, with the
  program's `⊑`-tests and theorems as extra inequations) needs an inductive provable-equality relation with
  about 20 rules. It is not in the staged plan (D4).

### 4.2 The laws

| law                                                        | holds by                                                |
|------------------------------------------------------------|---------------------------------------------------------|
| `⟦R S⟧ = ⟦R⟧ ⟦S⟧`                                          | `rfl`                                                   |
| `⟦𝟙⟧ = 𝟙`, `⟦𝟘⟧ = 𝟘`                                       | `rfl`                                                   |
| `⟦R°⟧ = ⟦R⟧°` for a closed `R`                             | `rfl`                                                   |
| `⟦R ∩ S⟧ = ⟦R⟧ ∩ ⟦S⟧`, `⟦R ∪ S⟧ = ⟦R⟧ ∪ ⟦S⟧`               | `rfl`                                                   |
| `⟦⟨R,S⟩⟧ = rpair ⟦R⟧ ⟦S⟧`, `⟦R × S⟧`, `⟦[R,S]⟧`            | `rfl`                                                   |
| `⟦dom(R)⟧ = 𝟙 ∩ ⟦R⟧ ⟦R⟧°`, `⟦ran(R)⟧`                      | `rfl`                                                   |
| `⟦share k R⟧ = ⟦R⟧`, `⟦own R⟧ = ⟦R⟧`                       | `rfl`                                                   |
| `⟦R − S⟧ = ⟦R⟧ − ⟦S⟧` with the `BooleanAllegory` `sub`     | proof, in `LeetQAop`                                    |
| `⟦π₁⟧ = RelProd.π₁`, `⟦inl⟧ = Coproduct.u₁` over `RelSet`  | proof or `rfl`, in `LeetQAop` (the instances live there) |
| `⟦R\S⟧ = ⟦R⟧\⟦S⟧`                                          | proof, and only when the two universes cover `R`'s target and `S`'s |
| `⟦μX : φ⟧ = ⟦φ⟧[X ↦ ⟦μX : φ⟧]`                             | proof: `lfp_fix` with `den_mono`                        |
| `⟦νX : φ⟧ = ⟦φ⟧[X ↦ ⟦νX : φ⟧]`                             | proof: `gfp_fix` with `den_mono`                        |
| `R ⊑ R' ⟹ ⟦C[R]⟧ ⊑ ⟦C[R']⟧` at a positive position         | proof: `den_mono`                                       |
| `convTm t = .ok u ⟹ ⟦u⟧ = ⟦t⟧°`                            | proof by induction; nothing checks `convTm` today       |
| `⟦flat R⟧`, `⟦foldI e S⟧` against the unlifted `R`, `⦇e,S⦈` | proof; nothing states the family lifting today         |
| a call is its body with the parameters bound (stage 5)     | `rfl`: the clause of the `let` node                     |

## 5. Cost and migration

### 5.1 Stages

Each stage ends with `lake build LeetQ` green in `leetq/`, including `TestRep` and the `#guard`s of `Test`.

| stage | content                                                                            | deletes                         | net lines |
|-------|------------------------------------------------------------------------------------|---------------------------------|-----------|
| 1     | `Den.lean`: total `den`, named `T`s, `lfp`/`gfp`, `Tm.Pos`, `den_mono`; total `fv`, `den_congr` | `Tm.den` in `BitsSpec` | +230      |
| 2     | `Syn.lean`: `Tm.Eqv`, `Cat Syn`, `Syn.den`, the `rfl` laws, `convTm_den`           | nothing                         | +110      |
| 3     | `Row` and `rows`; `compile`/`Tm.plan`; `mu_sound`, `nu_sound`; `Tm.gap`; `compile_sound`. A differential `#guard` compares `compile` with the generated code on `Test`'s programs. The generator still runs the programs. | `Prim.sound`, its `run_cmd` | +330      |
| 4     | reify the numbered terms (`tmE`); `rel_program` emits each constant as `compile t_x` unfolded, its `rfl` equation `n.x_eq`, and `rep_x` by `compile_sound` | `prf pprf prfNode lem lemO`; `code node plan? planOr spine body share`; `primE fitConst primWrappers` | −130      |
| 5     | calls and generic definitions: a `let` node, a definition's term as a function of its objects | `Tm.call`'s plan-passing constants | +80       |
| 6     | optional: `LeetQAop` bridge theorems `Row.den = aop` and the `RelSet` instance laws of 4.2 | nothing                  | +120      |

- Total through stage 5: about +620 lines, with about 320 deleted inside that figure.
- Stage 1's one non-additive change: `Tm.den`'s `ldiv` clause reads `UB.tab.val.row`; the general clause reads
  `⟦UB⟧`. `rep_tableC` then needs `Tm.tableC` to return bit `false` at an `ldiv` whose universes are not tables
  (a two-token change in `Bits.lean`), or a hypothesis `UB.isVal`. The first is recommended.
- Stages 1 and 2 build on D1 = T and D2 = C and do not touch the generator.
- Stage 3 can land node by node: `Tm.gap` names the nodes with no lemma yet, as `n.unproved` does today.

### 5.2 Risks

| risk                 | where                                                             | mitigation                                      |
|----------------------|-------------------------------------------------------------------|-------------------------------------------------|
| plan fusion          | a call passes plans (`Gen.Pl`) so the caller's bit plan runs through it | `Env` holds `Pl`, not `CRel`; stage 5 keeps that |
| elaboration speed    | a 40-constructor structural recursion; `rfl` proofs that reduce `gap`/`Pos` over a reified term | no overlapping patterns (dispatch on `d` inside a clause); `gap` evidence built as a term if `rfl` is slow |
| unfolding `compile`  | the macro reduces `compile η t_p` to a `CRel` composite at elaboration time; a large program (`chess.mate`) is a deep term | unfold one `compile` equation per node, never `decide`; try `chess.mate` first |
| the `rfl` check cost | the kernel checks `n.x = compile η t_x` by unfolding `compile` over a term holding table payloads | `simp only [compile]` where `rfl` is slow; no `decide`, no `native_decide` |
| universes            | none: `Obj.El : Type`, `Den` in `RelSet.{0}`, `lfp` quantifies over `Den A B → Prop` in `Prop` | —      |
| `Classical`          | only through `merge`'s `T` and what `Rel.Holds` already carries   | `#print axioms` on `Tm.den`, `lfp_fix`, `compile_sound` in the gate |
| monotonicity         | `Pre.polarity` and `Tm.Pos` are two checks of one property        | D5                                              |
| reified term size    | a shared sub-term repeated inside every parent                    | reified as `.var k`, so each sub-term is written once |

### 5.3 New types

| type                          | kind        | why no existing one serves                                                                 |
|-------------------------------|-------------|--------------------------------------------------------------------------------------------|
| `Row`                         | `structure` | `Prim` names its kernel and lemma by `Lean.Name`; a function of a term cannot follow a name. `Prim` cannot hold a `Den`: it lives in the precompiled `Run` lib, which imports no proof module. |
| `Syn` (the `Quot` hom)        | `def`       | `QuotAllegory` quotients an allegory by a `Congruence`; `Tm` is not an allegory (4.1).     |
| `Sem`, `Code`, `Val`, `Env`   | `abbrev`    | sigma and function types over existing ones; `Sem` is to `Den` what `Res` is to `Tm`. |
| `let` node on `Tm` (stage 5)  | constructor | `arg f x` gives `f` one more argument but not the variable it binds; `call` holds a `Lean.Name`. |

No new term language: `Tm` stays the only core.

## 6. Decisions

| id | question                                              | options                                                                                         | status        |
|----|-------------------------------------------------------|-------------------------------------------------------------------------------------------------|---------------|
| D1 | how a term becomes code, and where soundness is proved (3.1) | A `Tm.run` interprets the term at run time · B keep the meta-program `code`, stitch per program · T `compile` a Lean function, unfolded at elaboration time, one `compile_sound` | decided: T |
| D2 | the meaning of `Λ(R)`, `E(R)` when `𝒫A` is `[A]` (7.1) | C every `CRel` table canonical: `Sound` keeps `=` · D `Sound` up to set-equality `≈`, every node lemma restated with a side condition | decided: C |
| D3 | one generic `den` over any allegory, replacing `toTerm`'s clauses | E not now; per-row bridge theorems in `LeetQAop` (stage 6) · F now                    | decided: E |
| D4 | how far the syntactic category goes                   | G `Syn` as a category with `Functor` (stage 2) · H also the `AllegoryFunctor` on closed terms between finite objects · I also the free allegory with an inductive equational theory | decided: G |
| D5 | where the monotonicity check lives                    | J `Tm.Pos` is the one check and `Pre.polarity` only locates the error · K both stay, independent | decided: J |
| D6 | `Row` generated by `prim%` or written by hand         | L generated · M 25 hand-written rows                                                            | decided: L |
| D7 | a sum table whose rows name an empty side (7.4)       | P `juncD`'s code checks it and clears its ok bit · Q a well-formedness invariant carried by `Cor` and by every `Sound` conclusion | decided: P |
| D8 | a `μ` body that is not positive in `X` (7.3)          | R meaning stays `lfp`, the node is reported by `Tm.gap` · S the meaning becomes "the value the rounds stop at" | decided: R |

- The 8 decisions, decided or recommended: D1 T · D2 C · D3 E · D4 G · D5 J · D6 L · D7 P · D8 R.
- D1: T differs from A in that no term is walked at run time, and from B in that `compile` is a Lean function,
  so one theorem quantifies over every term.
- D2 blocked a proof, not a choice of convenience: `rep_lamOn` and `rep_E` fix the result list only up to its
  elements, `Sound` is an `↔`, and `[A]` exposes order and length (`length`, `at`), so `⟦Λ(R)⟧` must name one
  list.

## 7. The nodes `prfNode` could not cover

The per-node wiring is finished for `nil atPos est succ leq lt arith fold`. What it left, by count of `unproved`
nodes: `Gen.lam` 36, `mu` 5, `refold` 2, `nu` 2, `nuAC` 1; plus `E`, `thin`, `juncD`, `flat`, `var`. Each has a
different cause, and the total `⟦−⟧` with `compile_sound` answers each differently.

| node                        | why `prfNode` stops                                           | what the design does          |
|-----------------------------|---------------------------------------------------------------|-------------------------------|
| `lam`, `E`, `thin`          | the output list is fixed only up to its elements              | 7.1: canonical tables (D2 = C) |
| `var`, `mu`, `nu`, `refold` | `prfNode` builds closed proofs; the body's must be parametric | 7.2: `∀ η ρ` in the induction |
| `mu`, `nu`                  | `CRel.rep_fixOn` needs the body monotone (`hm`)               | 7.3: `Tm.pol`, `den_mono`     |
| `juncD`                     | `Vals.row` returns `dflt` on a row that names an empty side   | 7.4: the ok bit               |
| `flat`                      | `isDefEq` timeout in `TestRep` (`chess.mate`)                 | 7.5: no per-program unification |

### 7.1 `𝒫` outputs: canonical tables (D2 = C)

- The fact: `rep_lamOn`, `rep_E`, `rep_transpose` give `y ∈ ys ↔ …`. The list `ys` follows the row order of the
  table `R` is held as, so it is not a function of `⟦R⟧`. No clause `lamDen ⟦R⟧` can name it, whatever the proof.
- Measured before the change (scratch test `/data/tmp/assoc/Assoc.lean`):
  - `(R S) T` and `R (S T)` were already identical lists, because `compC` is a left-major nested-loop join,
    i.e. list bind;
  - `𝟙 R ≠ R` as data, since `𝟙 R` reorders the rows by `𝟙`'s keys;
  - `compC` emitted duplicate pairs.
- So `CRel` with `comp` was a category only up to `rep`, and the kernel's `Λ` was not compositional; this is a
  property of the code, not of the proof method.

The decided design (an agent is implementing it):
- Every `CRel` table an op returns is canonical: its rows are strictly increasing in the semantic order on
  `(key, val)`, so sorted with no duplicates. The order is each atom's own order, lexicographic on products,
  arrays and sums, with `inl < inr`.
- A `canon` step (sort, then distinct, with qlean kernels) follows each op not proved to preserve canonical form.
- Consequence: `Canon R → Canon S → rep R = rep S → R = S`. So `CRel` with `comp` is a category on the data
  itself: associativity, both unit laws, `R ∩ R = R` and `R ∪ R = R` hold as data equalities.
- `⟦Λ(R)⟧`, `⟦E(R)⟧` and setify name the canonical list, so `Sound` keeps `=`.
- D (`Sound` up to set-equality `≈`) was rejected: `(R S) ≫ (≈)` is `(R ≫ (≈)) (S ≫ (≈))` only when `S` respects
  `≈`, which `length`, `at(k)`, `sum`, `uncons` do not, and `∩`, `−`, `\`, `/` do not commute with `≫ (≈)`.

```lean
/-- A total order on the elements of `A`, by recursion on `A`: the order `canon` sorts by. -/
def Obj.lt : (A : Obj) → A.El → A.El → Prop
/-- `ys` is the one list of its set: strictly increasing. -/
def Canon {A : Obj} (ys : List A.El) : Prop := ys.Pairwise (A.lt)
theorem Canon.ext (h : Canon ys) (h' : Canon zs) (he : ∀ b, b ∈ ys ↔ b ∈ zs) : ys = zs
def lamDen (T : Den A B) : Den A (.arr B) := fun a ys => Canon ys ∧ ∀ b, b ∈ ys ↔ T a b
def EDen   (T : Den A B) : Den (.arr A) (.arr B) := fun xs ys => Canon ys ∧ ∀ b, b ∈ ys ↔ ∃ a ∈ xs, T a b
```

- On canonical lists `=` is "same elements" (`Canon.ext`), so the `↔` of `Sound` goes through and no other
  lemma changes. `lamDen` is a relation, not a choice of list: it holds of no `ys` when `T a` is infinite, and
  needs no `Classical`.
- `thin(Q)` is a relation with several answers in the book and one in the kernel. Its clause is an inductive
  relation that follows the kernel's scan over the canonical input, composed with `Canon`.
- `Obj.lt` must be the order `canon` sorts by, at every atom; a float atom with NaN has no strict total order
  and is refused by `gap`. Until the change lands, the 36 `lam` nodes stay in `gap`.

### 7.2 Binders: open terms

- `compile_sound` is proved for every `η`, `ρ` with `η.Sound ρ`, so the induction hypothesis of a body is
  already parametric in the bound variable. This is what a proof assembled per closed program cannot have.
- The `fun X =>` that `compile` passes to `Gen.mu` is unfolded at compile time with the rest of the term; the
  emitted code holds the unfolded body, not a call back into `compile`.

| node          | case of the induction                                                                        |
|---------------|----------------------------------------------------------------------------------------------|
| `var k`       | `compile η (.var k) = Gen.ofPl (η k A B d)`; sound by `hη k A B d`                           |
| `mu k _ cap b` | below                                                                                       |
| `nu k S b`    | as `mu`, from `⟦S⟧` downward, `gfp`                                                          |
| `refold`      | `mu`'s clause plus locality (below)                                                          |
| `nuAC`        | `Gen.nuAC … = Gen.nu …` as one lemma about the two codes; the case is then `nu`'s            |

```lean
-- compile η (.mu k w cap b) = Gen.mu A B cap fun X => compile (η.bind k X) b
theorem Env.Sound.bind (hη : η.Sound ρ) (X : CRel A B) (hX : X.ok = true) :
    (η.bind k X).Sound (ρ.bind k (rep X.rel))                     -- `const_sound` at `k`, `hη` elsewhere
theorem mu_sound {φ : CRel A B → Fn false A B} {Φ : Den A B → Den A B} (hΦ : Monotone Φ)
    (h : ∀ X, X.ok = true → Sound (φ X) (Φ (rep X.rel))) : Sound (Gen.mu A B cap φ) (lfp Φ)
```

- In the `mu` case `Φ Y = ⟦b⟧(ρ.bind k Y)`. Hypothesis `h` is the induction hypothesis of `b` at
  `η.bind k X`, `ρ.bind k (rep X.rel)`, given `Env.Sound.bind`. `mu_sound` is `CRel.rep_fixOn` with `lfp_le`.
- A round whose table is not ok clears the result's ok bit (`also`), so `h` is needed only at ok tables.
- `refold` computes each node's value once, after its children. That equals `lfp` at the demanded keys only if
  the body reads `X` at the children of the key and nowhere else. The clause needs
  `den_local : (∀ y, ⟦ch⟧ x y → X y = X' y) → ⟦b⟧(ρ.bind k X) x = ⟦b⟧(ρ.bind k X') x`. Nothing states it today;
  `refold` stays in `gap` until it is proved for the shape `c G(X) S` the elaborator builds.
- `nuAC` needs the correctness of the arc-consistency rounds against plain rounds. It is a lemma about `Gen`
  alone and can be proved before any of this lands.

### 7.3 Monotonicity for `μ` and `ν`

- "The body contains `diff` or `ldiv`" is not the failure. `R − S` is monotone in `R`; `R\S` is monotone in `S`.
  The failure is `X` inside `S` of `R − S`, or inside `R` of `R\S`. A body with `X`-free `S` is monotone, and
  the proof of that is `den_congr`: `⟦S⟧` does not move when `X` does. That is why `fv` has to be total.

```lean
/-- `X` (the variable `k`) occurs in `t` only with sign `s`: `true` positive, `false` negative. -/
def Tm.pol (s : Bool) (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Bool
theorem Tm.den_mono (h : t.pol true k)  (hXY : X ⊑ Y) : (⟦t⟧ρ.bind k X) ⊑ ⟦t⟧ρ.bind k Y
theorem Tm.den_anti (h : t.pol false k) (hXY : X ⊑ Y) : (⟦t⟧ρ.bind k Y) ⊑ ⟦t⟧ρ.bind k X
```

| node                                       | `pol s k`                                                         |
|--------------------------------------------|-------------------------------------------------------------------|
| `var k`                                    | `s`                                                               |
| `var j` (`j ≠ k`), a leaf                  | `true`                                                            |
| `comp meet join pair prod junc dom top`    | `pol s` of every part                                             |
| `conv`, `ran`, `share`, `own`              | `pol s` of the part                                               |
| `diff R S`                                 | `R.pol s && S.pol (!s)`                                           |
| `ldiv R S UB UC`                           | `R.pol (!s) && S.pol s`, and `k ∉ fv UB`, `k ∉ fv UC`             |
| `rdiv R S UA UB`                           | `R.pol s && S.pol (!s)`, and `k` free in neither universe         |
| `lam`, `E`, `est`, `thin`, `atPos`, `nil`  | `k ∉ fv t`: a map's value changes, it does not grow               |
| `fold`, `foldI`, `flat`                    | `k ∉ fv t` until its `Den` has a monotonicity lemma               |
| `prim r` under `arg`s                      | `r.mono` and `pol s` of every argument, else `k ∉ fv t`           |
| an inner `mu`, `nu`, `refold` on `j ≠ k`   | `pol s` of the body (`lfp`, `gfp` are monotone in a parameter)    |

- `Tm.pol` replaces the `Tm.Pos` of section 2; `den_mono` and `den_anti` are one mutual induction.
- `Prim.mono : Bool` exists already. `Row` gains the proof: `mono : r.mono = true → ∀ …, ss ⊑ ss' → den A B ss ⊑
  den A B ss'`.
- `lfp`/`gfp` are defined for every `Φ`, so `⟦−⟧` is total with no monotonicity hypothesis. Monotonicity is a
  hypothesis of the soundness case and of the unfolding law only. `Tm.gap` reports a `μ`/`ν` whose body fails
  `pol true k`.
- D8, for a body that is not positive. R: the meaning stays `lfp`, and the node is a gap, with the message
  naming the negative occurrence. S: the meaning becomes `stab Φ := fun x y => ∃ j, Φ^[j+1] 𝟘 = Φ^[j] 𝟘 ∧
  Φ^[j] 𝟘 x y`, which every ok run equals without any hypothesis, and `stab Φ = lfp Φ` becomes a law that needs
  `pol`. R is recommended: `μ` then means what the book says, and `Pre.polarity` is expected to refuse such a
  body before a `Tm` exists (not verified here: `Elab.lean` was not read for it).

### 7.4 `juncD` and the empty side

- `Vals.row` on a sum table returns `dflt` for a row whose tag names a side with no values. Such a row makes
  `rep` relate a value that is not in the table, and nothing excludes it.

| option | where the exclusion lives                                             | cost                                    |
|--------|-----------------------------------------------------------------------|-----------------------------------------|
| P      | `juncD`'s code checks its demand's tags and clears the ok bit         | one linear scan per `juncD`; `Sound` and every other lemma unchanged |
| Q      | `Vals.WF`, assumed by `Cor D` and concluded by every `Sound`          | one more conjunct in about 60 lemmas    |
| —      | change the sum representation so `row` is total                       | a data structure change                 |

- P is recommended: the ok bit is already how every code says "this result cannot be vouched for".
- Whether a demand with such a row can arise from sound code was not established. If it cannot, Q's invariant
  is provable once and P's scan is redundant; that is worth one probe before choosing.

### 7.5 `flat`

- The lemma `flat_sound` (`/data/tmp/gate/flat_attempt.patch`) has the shape of an induction case and is used
  as written: `flatDen T := fun x b => T x.1 (x.2, b)`.
- The timeout is in the stitching: `prfNode` unifies the lemma's code with the code of one node of
  `chess.mate`, a closed term with table payloads. `compile_sound` applies `flat_sound` once, inside the
  induction, to variables. The per-program step is `compile_sound` with the `rfl` equation `n.x_eq`; no lemma is
  unified with a program's code.
- The cost that remains per program is `t.gap = none` over the reified term, the unfolding of `compile` and the
  `rfl` check of `n.x_eq` (section 5.2, rows "elaboration speed", "unfolding `compile`", "the `rfl` check
  cost"). `chess.mate` is the test of that; it should be the first program stage 4 is tried on.

### 7.6 Effect on the stages

| stage | change                                                                                                  |
|-------|---------------------------------------------------------------------------------------------------------|
| 1     | `Tm.pol`, `den_anti` beside `den_mono`; `Obj.lt`, `Canon`, `lamDen`, `EDen` (D2 = C; about +60 lines)   |
| 3     | `mu_sound`, `nu_sound`, `Env.Sound.bind`; `nuAC = nu`; `flat_sound` from the patch; `juncD` per D7      |
| 3     | `lam`, `E`, `thin` cases only after the canonical tables of D2 land; `refold` only after `den_local`    |

- After stage 4 with D7 = P, D8 = R, the expected content of `Tm.gap` is `refold` (2 nodes) and the rows
  with no lemma (`filter takewhile thinL loop asc`), against 46 `unproved` nodes today.
