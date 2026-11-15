# Rel program for B&dM §7.3 "Planning a company party" — design

Design only; nothing is added to `leetq/`. Target file: `leetq/LeetQ/Rel/Programs/Party.lean`. Every line of §1–§3 was
elaborated and run in the scratch program `/data/tmp/party/Party.lean` (source `/data/tmp/party/party.rel.md`):
`party.ok = true` in 2.4 s (there the direct set description is the definition and `fold choose` the check). Lines
marked "not run" were not. Sources: B&dM pp. 175–178, `AOP/A7_3_Party.lean`,
`diag/aop/07-optimisation.typ` "Planning a company party".

## 1. Data and specification (book form over `boss`)

The tree is the coalgebra `⟨𝟙, kids⟩ : E ⟶ E×[E]` of `boss`; an employee stands for the subtree under him, so
`party : E ⟶ [E]` is the book's `party : list A ← tree A`. A party is an array made by `Λ`/`union`: ascending, no repeats.

```
obj E = {a,b,c,d,e,f,g,h,i,k,l,m}                 -- exStaff a…f, a chain g h i, a tie k l, one employee m
obj N = 0…40
boss : E ⟶ E ≜ {(b,a),(c,a),(d,b),(e,b),(f,c),(h,g),(i,h),(l,k)}
rating : E ⟶ N ≜ {(a,3),(b,7),(c,2),(d,5),(e,1),(f,8),(g,4),(h,5),(i,4),(k,2),(l,2),(m,0)}

under : E ⟶ E ≜ μX : 𝟙 ∪ (boss° X)                -- e and everyone below e
leaf : E ⟶ E ≜ 𝟙 − ran(boss)
kids : E ⟶ [E] ≜ Λ(boss°) ∪ (leaf nil)            -- Λ has no row at a leaf (measured), so [] is added
cost(r : α ⟶ β) : [α] ⟶ β ≜ F(r)sum               -- Lean cost_eq
R(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≥ cost(r)°     -- the converse of Lean R_eq, see B4

choose : [E]×[E] ⟶ [E] ≜ π₁ ∪ π₂
include : E×[[E]×[E]] ⟶ [E] ≜ ⟨π₁τ τ, π₂F(π₂)⟩cat union      -- book: cons (id × concat list outr)
exclude : E×[[E]×[E]] ⟶ [E] ≜ π₂F(choose)union               -- book: outr (id × concat list choose)
S : E×[[E]×[E]] ⟶ [E]×[E] ≜ ⟨include, exclude⟩
B : E ⟶ [E]×[E] ≜ ⟨P,P⟩ where P ≜ Λ(under)subseq             -- the bound ν needs: all pairs of subsets
fold : E ⟶ [E]×[E] ≜ νX : B ∩ (⟨𝟙, kids F(X)⟩S)             -- ⦇S⦈: X = out F(X) S, out = ⟨𝟙,kids⟩
party : E ⟶ [E] ≜ fold choose                                -- Lean party_eq
best : E ⟶ [E] ≜ Λ(party)est(R(rating))                      -- the problem: max R · Λparty

check party = Λ(under)subseq(𝟙 − dom(∋ ∩ (∋ boss)))          -- the sets with no employee beside his boss
```

- `⦇S⦈` is the unique solution of `X = ⟨𝟙, kids F(X)⟩S` because `boss` is a finite tree, so the greatest solution
  below `B` is the fold. `μ` is refused for this `X` (B1).
- `include` puts the root in as `[[e]]` joined to the children's parties, then `union`: no `cons`. `union` of the
  children's parties is the book's `concat` on sets.
- Measured `best`: `a ↦ a d e f` (cost 17, Lean `party_example_run`), `g ↦ g i`, `k ↦ [k]` and `[l]`, `m ↦ []` and `[m]`.

## 2. The derived program

Book form, the result of the greedy derivation (p. 178), still array-valued:

```
exclude₁ : E×[[E]×[E]] ⟶ [E] ≜ π₂F(Λ(choose)est(R(rating)))union     -- book: concat list(max R Λchoose) outr
gfold : E ⟶ [E]×[E] ≜ νX : B ∩ (⟨𝟙, kids F(X)⟩⟨include, exclude₁⟩)
check gfold Λ(choose)est(R(rating)) ⊑ best                            -- party_laws
```

Efficient form. The book's program carries `(party, cost)`; here the cost is the relation `c`, and a party is a relation
into `E`, so "`concat list f` over the children" is the composition `boss° f` and no array is built:

```
c : E ⟶ N×N ≜ μX : ⟨rating + (kids F(X π₂)sum), kids F(X max)sum⟩    -- (cost with e, cost without e)
win : E ⟶ E ≜ dom((c π₁ ≥) ∩ (c π₂))                                 -- include wins; ties to include (bmax)
guests : E ⟶ E ≜ μX : win(𝟙 ∪ (boss° boss° X)) ∪ ((𝟙 − win)boss° X)  -- party as a relation into E
check Λ(guests) ⊑ best
check c max = best cost(rating)
```

| def      | book counterpart                     | reading                                                              |
|----------|--------------------------------------|----------------------------------------------------------------------|
| `c π₁`   | cost of `include`                    | `rating(e)` + sum over children of their `c π₂`                      |
| `c π₂`   | cost of `concat list(bmax) outr`     | sum over children of the larger of their two costs                   |
| `win`    | `bmax r = cond r (outl, outr)`       | employees whose subtree's best party holds them                      |
| `guests` | `party = bmax r ⦇⟨include,exclude⟩⦈` | `include = 𝟙 ∪ (boss° exclude)`, `exclude = boss° party`, substituted |

- `guests` has one `μ` because a program has no mutual recursion: `exclude` is substituted into `include`.
- `c` is defined at `e` only after every child has a value (`F` needs every element's image), so its rounds go bottom-up.
- q reading, for orientation only: `kids` is `group boss`, `kids F(v)sum` is `sum each v group boss`, `μ` is converge.
- Measured: `c` at `a` is `(17,15)`, `Λ(guests)` at `a` is `a d e f`; both checks hold on all 12 employees.
- The coming `scan` builtin is not needed: no step here is a running reduce along one array.

## 3. Builtins per definition (each confirmed in `Op.table`, `Run/Lang/Syntax.lean:55`, or the prelude)

| def                    | builtins                                   | prelude        | other syntax         |
|------------------------|--------------------------------------------|----------------|----------------------|
| `under`                | `𝟙`                                        |                | `μ`, `°`, `∪`        |
| `leaf`, `kids`         | `𝟙`, `ran`, `Λ`, `nil`                     |                | `−`, `°`, `∪`        |
| `cost`, `R`            | `F`, `sum`                                 | `≥`            | `°`                  |
| `choose`               | `π₁`, `π₂`                                 |                | `∪`                  |
| `include`              | `π₁`, `π₂`, `τ`, `F`, `cat`, `union`       |                | `⟨,⟩`                |
| `exclude`, `exclude₁`  | `π₂`, `F`, `union`, `Λ`, `est`             |                |                      |
| `B`, `fold`, `gfold`   | `Λ`, `𝟙`, `F`                              | `subseq`       | `ν`, `∩`, `⟨,⟩`      |
| `party`, `best`, check | `Λ`, `est`, `∋`, `dom`, `𝟙`                | `subseq`       | `−`, `∩`             |
| `c`                    | `F`, `sum`, `π₂`, `max`                    | `_+_`          | `μ`, `⟨,⟩`           |
| `win`, `guests`        | `dom`, `π₁`, `π₂`, `𝟙`                     | `≥`            | `μ`, `∩`, `∪`, `−`   |

`subseq` is the prelude's `⦇ran(nil), cons ∪ π₂⦈`; `F` runs as a `cons` fold inside the engine (`mapC`, Alg.lean:761).
Both are engine-side (`doc/rel-avoid-cons.md` class N and M); the program text has no `cons`, `snoc`, `head`, `tail`.

## 4. Blockers and limits (all measured unless marked)

| id | what happens                                                  | consequence; op or rule needed                        |
|----|---------------------------------------------------------------|-------------------------------------------------------|
| B1 | `μX : E ⟶ [E]×[E]` refused: "has no universe" (Elab.lean:875) | `fold`, `gfold` use `ν` below `B` (4ⁿ rows); needs `μ` |
|    |                                                               | on an array target, or a tree fold `⦇S⦈`              |
| B2 | `Λ(boss°)` has no row at a leaf                               | `kids` adds `leaf nil`; none, or a total `Λ`          |
| B3 | `est(RR)`, `RR ≜ (π₁R π₁°) ∩ (π₂R π₂°)`: "not testable on     | `party_greedy` as stated has no check; needs a pair   |
|    | pairs"                                                        | test for a product order                              |
| B4 | resolved: `est(R(rating)°)` and a monomorphic `R : [E] ⟶ [E]` | `R` can take the book's `R ≜ cost ≤ cost°` with       |
|    | run (τ(Q°) is τ(Q) on swapped pairs; Test.lean `estConv`)     | `est(R°)`; Party.lean still uses the conversed form   |
| B5 | `μ` on `E ⟶ N×N` builds the universe of `N×N`: `0…1500` runs, | costs bounded by about 1500; needs `μ` not building   |
|    | `0…2000` is OOM                                               | the target universe (or option H)                     |
| B6 | `μ` is not semi-naive: height+1 rounds, each over all rows    | work is n·height, not linear; needs a delta `μ`       |
| B7 | `est` compares all pairs of one key's candidates              | `best` is OOM on a 13-node tree; fine for a spec      |

## 5. Cost at run time (one core, default 12 GB address cap of `scripts/cap`)

| program part                          | input                              | result                                        |
|---------------------------------------|------------------------------------|-----------------------------------------------|
| everything in §1–§2                   | the 12-employee forest above       | 2.4 s                                         |
| `party`, `best`, `fold`, `B` from the independent sets | 9-node binary tree | 1.5 s                                 |
| `best` alone                          | 13-node binary tree                | OOM (B7); `fold` with `B` of §1: OOM (4¹³)    |
| `c`, `win`, `guests`                  | 255-node binary tree, `N = 0…1500` | 5.7 s, root cost 682                          |
| `c`, `win`, `guests`                  | 200-node path, `N = 0…1500`        | 5.5 s, root cost 456; about 200 rounds        |

- The specification explodes: `Λ(under)subseq` is 2ⁿ per subtree and `B` is 4ⁿ. Keep each tree of the check at most 6
  employees with `B` as written, at most 9 with `B ≜ ⟨Q,Q⟩`, `Q` the right side of the last check of §1.
- `μ` over `boss` (`under`, `c`, `guests`) stops after height+1 rounds: each round settles one more level.

## 6. Correspondence to Lean, for the later one-law-per-step theorems (`doc/rel-mss-proof-design.md` style)

| Rel step                                             | Lean (`AOP.A7_3_Party`)                           |
|------------------------------------------------------|---------------------------------------------------|
| `party = fold choose`                                | `party_eq` (`≜`)                                  |
| `include`, `exclude`, `choose`, `S`                  | `include_eq`, `exclude_eq`, `choose`, `S`         |
| `Λ(fold choose) = Λ(fold)E(choose)`                  | `party_absorb`                                    |
| `est(RR)Λ(choose)est(R) ⊑ E(choose)est(R)`           | `party_est_choose`                                |
| greedy fold `⊑ Λ(fold)est(RR)`                       | `party_greedy` (no run-time check, B3)            |
| `⟨Λ(include)est(R), Λ(exclude)est(R)⟩ ⊑ Λ(S)est(RR)` | `party_pair_step`, `include_step`, `exclude_step` |
| `gfold Λ(choose)est(R) ⊑ Λ(party)est(R)`             | `party_laws`                                      |
| `fold` as `ν` equals `⦇S⦈`; `gfold … cost = c max`; `Λ(guests) ⊑ gfold Λ(choose)est(R)` | no Lean statement yet: three new laws |

## 7. Open decisions

| letter | option                                                                                    | note                              |
|--------|-------------------------------------------------------------------------------------------|-----------------------------------|
| A      | one forest in one `E`; every employee is a tree of the check                              | recommended; measured             |
| B      | definitions take `boss`, `rating` as parameters, one literal pair per tree                | every def gains two parameters    |
| C      | a family keyed by an instance object `K`                                                  | `μ` is not liftable to a family   |
| D      | the book fold as `ν` below `B`                                                            | recommended now; works today      |
| E      | admit `μ` on an array target when the source has a universe                               | changes `Elab`; needs approval    |
| F      | a tree fold builtin over a coalgebra `E ⟶ E×[E]`                                          | new op; needs approval            |
| G      | efficient version = `c` (pair) + `win` + `guests`                                         | recommended; measured             |
| H      | one cost, `μX : ⟨rating + (grand F(X)sum), kids F(X)sum⟩max`, `grand` the grandchildren   | no `N×N` universe (B5); not run   |
| I      | stop at `gfold`                                                                           | exponential bound, not linear     |
| J      | ratings in `N = 0…40`                                                                     | recommended                       |
| K      | a signed range, as the book's reals                                                       | `Λ(guests)` loses the empty party |
| L      | names not in the book — `fold`, `kids`, `under`, `c`, `win`, `guests` — kept as written   | say the names to use instead      |
