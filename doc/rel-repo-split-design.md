# Rel as its own repository: one Lean package, one Rust crate

Design only, 2026-11-16. Nothing is created or edited by this document.

Request: "I want the rel language separate out of freyd and qlean, only take what's necessary. It will need
allegory, fixed point, and qlean rust part used by rel. As a new repo." Then: "Packages what ever rel used as a
package, one lean package, and one crate, that do not depend on others. Qlean depends on that crate."

So the new repository holds exactly one Lean package and one Rust crate. Neither depends on freyd or qlean. qlean
is inverted: it stops owning the kernels Rel uses and depends on the new repository for them.

## 0. Sources and their limits

| source                                  | state                                                   |
|-----------------------------------------|---------------------------------------------------------|
| freyd `.lake/build/refactor-index.db`   | 2026-11-16; 16,865 `LeetQ.*` declarations, 8,376 public |
| qlean `.lake/build/refactor-index.db`   | 2026-10-26, older than qlean HEAD `88249ea`             |
| `doc/rel-c-kernels.md` (C reachability) | computed at qlean `369841b`                             |
| qlean branch `rust-port-0` at `77b82f0` | 2026-11-16, read with `git grep`; not in qlean `master` |

- Every cone below is a `WITH RECURSIVE` closure over the index table `dep`, declaration to declaration, never a
  read of `import` lines. Import closures are quoted only to show what the cone saves.
- Counts are public declarations (`internal = 0`); a count in parentheses includes compiler-generated ones.
- The qlean numbers miss any declaration added to qlean after 2026-10-26. Step 0 of the plan rebuilds that index.
- The brief places `Syntax/Parse/Elab/Expand/Tm/Gen/Bits` under `Rel/Lang`; on disk they are in `LeetQ/Run/Lang`.
  `Refold` is `LeetQ/Rel/RefoldSpec.lean`.

## 1. The dependency cone

### 1.1 What leetq is today

| group                         | modules | declarations | names Freyd | names AOP | names QLean |
|-------------------------------|--------:|-------------:|-------------|-----------|-------------|
| `LeetQ.Run.*` (runtime)       |      18 |          780 | no          | no        | yes         |
| `LeetQ.Run.Lang.*` (compiler) |      10 |        1,503 | no          | no        | yes         |
| `LeetQ.Rel.*` (laws, specs)   |      88 |        1,671 | 6 modules   | no        | yes         |
| `LeetQ.Rel.Lang.*`            |      24 |        3,265 | 6 modules   | no        | yes         |
| `LeetQ.Rel.Programs.*`        |      17 |        1,024 | no          | no        | no          |
| `LeetQ.Aop.*` (bridge)        |       6 |          133 | 10 modules  | 12        | no          |
| total                         |     163 |        8,376 |             |           |             |

"Rel proper" below is the 157 modules that are not `LeetQ.Aop`.

### 1.2 The cone Rel → AOP → Freyd, at declaration level

"It don't need every declaration from freyd. Just those used in aop." The closure starts at Rel's declarations
and follows `dep` from `src` to `dst`. A module contributes the declarations reached, never the module.

Run as `sqlite3 -readonly .lake/build/refactor-index.db "attach '<qlean index>' as q" ".read cone.sql"` (68 s).
The seed line is for Rel proper; drop its second condition to include the bridge.

```sql
create temp table di as select name, module, internal from decl_info;
create index temp.idi on di(name);
create temp table qn as select distinct name from q.decl_info;  -- tells qlean's names from the toolchain's
create index temp.iqn on qn(name);
-- keyed by (name, module): `main` is declared in several modules, and a closure keyed by name alone
-- walks from LeetQ's `main` into `diag` and `Freyd.tool` (1,067 and 105 false hits)
create temp table cl as
with recursive c(n, m) as (
  select name, module from di where module like 'LeetQ.%' and module not like 'LeetQ.Aop.%'
  union
  select d.dst, x.module from c join dep d on d.src = c.n and d.module = c.m
                         left join di x on x.name = d.dst)
select n, m from c;
create temp table lib as
select cl.n, cl.m, coalesce(di.internal, 0) internal,
       case when cl.m is not null then substr(cl.m, 1, instr(cl.m, '.') - 1)
            when qn.name is not null then 'QLean' else 'Init/Std/Lean' end lib
from cl left join di on di.name = cl.n and di.module = cl.m left join qn on qn.name = cl.n;
select lib, count(*), sum(internal = 0) from lib group by 1;
-- statement-needed: some declaration of the closure names it in its TYPE; otherwise proofs and bodies only
create temp table ty as
select distinct d.dst n from dep d join cl on cl.n = d.src and cl.m = d.module where d.in_type > 0;
select l.m, sum(l.internal = 0), sum(l.internal = 0 and ty.n is not null), sum(l.internal = 0 and ty.n is null)
from lib l left join ty on ty.n = l.n where l.lib in ('Freyd', 'AOP') group by 1 order by 1;
```

| library             | Rel proper     | with the bridge | library total |
|---------------------|---------------:|----------------:|--------------:|
| `LeetQ`             | 8,243 (16,647) |  8,376 (16,865) |         8,376 |
| `AOP`               |              0 |       281 (386) |         5,996 |
| `Freyd`             |       58 (111) |       226 (281) |        10,472 |
| `rel`, `leet`       |              0 |               0 |   263 + 3,143 |
| `QLean`             |    765 named   |     765 named   |         8,391 |
| `Init`/`Std`/`Lean` |  2,895 named   |   3,009 named   |             — |

- The freyd index holds no edges inside qlean or the toolchain, so the last two rows count names reached, not a
  closure. Section 1.6 closes the qlean row in qlean's own index.
- **Only the six `LeetQ.Aop` modules name anything in AOP.** Rel proper reaches no AOP declaration and reaches
  Freyd in 58. So the chain Rel → AOP → Freyd exists only through the bridge.
- Today's import closures are far larger than either cone: 8 Freyd modules and 674 declarations for Rel proper,
  93 Freyd and AOP modules and 5,621 declarations for the bridge.

### 1.3 The Freyd declarations in the cone, by book section

"stmt" is named in the type of some declaration of the closure. "proof" is named in proofs and bodies only, so
it is a candidate to re-prove concretely.

| book section                | module                | bridge: stmt + proof | Rel proper: stmt + proof | module |
|-----------------------------|-----------------------|---------------------:|-------------------------:|-------:|
| 1.1 categories              | `Freyd.S1_10`         |           8 =  4 + 4 |              6 =  4 +  2 |     15 |
| 1.18 functors               | `Freyd.S1_18`         |           6 =  3 + 3 |                        0 |     30 |
| 2.1 allegories              | `Freyd.S2_10`         |         55 = 19 + 36 |             11 =  5 +  6 |    121 |
| 2.14 maps, tabular, unitary | `Freyd.S2_147_MapCat` |         20 = 18 +  2 |                        0 |    198 |
| 2.2 distributive            | `Freyd.S2_20`         |         42 = 12 + 30 |             18 =  7 + 11 |    213 |
| 2.22 locally complete       | `Freyd.S2_22`         |          4 =  3 +  1 |              4 =  3 +  1 |    170 |
| 2.3 division                | `Freyd.S2_30`         |         38 = 27 + 11 |                        0 |    120 |
| 2.4 power                   | `Freyd.S2_40`         |         20 = 11 +  9 |                        0 |    129 |
| 2.41 power, continued       | `Freyd.S2_41b`        |         14 = 10 +  4 |                        0 |     51 |
| `[R,S]`                     | `Freyd.Junc`          |          1 =  1 +  0 |              1 =  1 +  0 |      1 |
| the model `Rel(Set)`        | `Freyd.RelSet`        |         18 = 12 +  6 |             18 = 12 +  6 |     20 |
| total                       |                       |      226 = 120 + 106 |             58 = 32 + 26 |  1,068 |

- AOP in the bridge's cone: 281 = 107 stmt + 174 proof, in 21 of 108 modules. Largest: `A7_7_MSS` 56 of 100,
  `A6_2` 36 of 83, `A5_5` 28 of 59, `A6_ConsList` 25 of 100, `A6_1_RelSet` 24 of 74, `A6_Poly` 19 of 91.
- `Freyd.S2_30` is in scope in 34 modules of Rel proper only as the notations `/` and `\`, which parse as an
  ambiguity with `Nat` division there and never elaborate to a division.

### 1.4 Abstract or concrete: how Rel proper uses its 58

"Chapter 2 build allegory bottom up by layer, and rel may not need that." Checked against the index:

- No declaration of Rel proper has an allegory, a category or `𝒜` as a binder. Every statement is about `RelSet`.
  Nothing in Rel proper is proved for an arbitrary allegory.
- Each class operator is elaborated at the one concrete instance: `RelSet.instCat` in 744 declarations,
  `RelSet.instAllegory` in 337, `RelSet.instDistributiveAllegory` in 166.

| Freyd declarations                           | kind  | used                       | concrete replacement         |
|----------------------------------------------|-------|----------------------------|------------------------------|
| `RelSet`, `mk`, `carrier`                    | stmt  | concretely                 | a relation between two types |
| `Cat.Hom`, `comp`, `id`                      | stmt  | class, at `instCat`        | definitions on relations     |
| `Allegory.recip`, `inter`; `le`              | stmt  | class, at `instAllegory`   | definitions on relations     |
| `DistributiveAllegory.union`, `zero`         | stmt  | class, at the instance     | definitions on relations     |
| `rpair relTop graph corefl rprodMap sumCop`  | stmt  | concretely                 | the same definitions         |
| `Coproduct.u₁`, `u₂`; `junc`                 | stmt  | class, at `sumCop`         | `inl`, `inr`, `junc`         |
| class types and `to…` projections (10)       | stmt  | instance path only         | none needed                  |
| `hom_ext le_iff comp_apply union_apply`      | proof | concrete lemma             | the same lemmas              |
| `inter_apply recip_apply`                    | proof | concrete lemma             | the same lemmas              |
| `Cat.assoc inter_idem union_idem`            | proof | abstract law, 1 user each  | one concrete lemma each      |
| `le_antisymm le_trans`                       | proof | abstract law, 1 user each  | one concrete lemma each      |
| class constructors and axiom fields (15)     | proof | instance definitions only  | none needed                  |

So the concrete set suffices. Rel proper needs relations `α → β → Prop`, their operations, five laws, six
unfolding lemmas, and the fixed points. It needs no class of chapter 2.

### 1.5 Verdict per source

| source                                  | verdict                                                         |
|-----------------------------------------|-----------------------------------------------------------------|
| the 58 Freyd declarations of Rel proper | replace by the concrete core of section 2: about 27             |
| `Freyd.S2_30`, `Freyd.S1_41`            | drop: reached by import only                                    |
| the bridge's 281 AOP + 226 Freyd        | not copied: stay in freyd with the six bridge modules (4.4)     |
| `rel.*`, `leet.*`                       | drop: not reached                                               |

### 1.6 qlean, Lean side (closure inside qlean's own index)

| qlean module(s)               | used / all  | callers in leetq                              | verdict   |
|-------------------------------|------------:|-----------------------------------------------|-----------|
| `QLean.Value`                 |   219 / 393 | `Run.Core`, `Run.ValEq`                       | extract   |
| `QLean.Kernel.*` (7 modules)  | 318 / 1,258 | `Run.Core`, `Run.Code`, `Run.KernelWF.*`,     | extract   |
|                               |             | `Run.Lang.Syntax`                             |           |
| `QLean.Verify.*` (20 modules) |   224 / 721 | `Run.Core`, `Run.Code`, `Rel.KernelWF.*` (49) | extract   |
| `QLean.Db.Own`                |     10 / 17 | `Run.Lang.Plan`                               | extract   |
| `QLean.Eval.Val`              |     5 / 171 | `Rel.KernelWF.PickSpec`                       | extract 5 |
| `QLean.Dep.Val`               |      3 / 32 | `Run.Core`                                    | extract 3 |
| `QLean.Dep.Monadic`           |      3 / 39 | `Run.Core`                                    | extract 3 |
| `QLean.Db.ObjectFile`         |      1 / 44 | through `Db.Own`                              | extract 1 |
| the other 152 modules         |           0 | 57 of them reached by import only             | drop      |

- Total: 783 public declarations in 33 modules (1,689), out of 8,391 in 185. The import closure is 90 modules:
  the evaluator, the q parser and the wire format come in through 8 imports that carry no constant:
  `Kernel.Elementwise → Prim.Dyadic`, `Kernel.Reduce → Prim.Monadic`, `Kernel.Scan → Prim.Verb`,
  `Eval.Val → Syntax.Ast, Syntax.Normalize`, `Dep.Val → Verify.Shape`, `Dep.Monadic → Verify.Monadic`,
  `Verify.Elementwise → Eval.Dyad`, `Db.ObjectFile → Wire.Decode`.
- The seven kernel modules, declarations named directly: Elementwise 92 / 257, Structural 37 / 105, Sort 34 / 89,
  Coc 31 / 78, Scan 30 / 124, Search 24 / 110, Reduce 6 / 83. `Kernel.Index` is not used.

### 1.7 qlean, C and Rust side (from `doc/rel-c-kernels.md`)

| column           | entries (`qlean_*`) | function lines | note                                            |
|------------------|--------------------:|---------------:|-------------------------------------------------|
| (a) `LeetQ.Run`  |           77 of 269 |          5,924 | 48% of the 12,316 function lines of `c/`        |
| (b) native ABI   |                   3 |            817 | `own_write`, `sort_group_ids`, `sort_id_groups` |
| (a) ∪ (b)        |                  78 |          6,001 | 28% of the 21,170 file lines                    |

| file            | reached lines | entries reached (prefix `qlean_` omitted)                               |
|-----------------|--------------:|-------------------------------------------------------------------------|
| `coc.h`         |         1,455 | none: helpers compiled into each `.c`                                   |
| `sort.c`        |         1,089 | 19: `grade*`, `group_ids*`, `id_groups`, `ranks*`, `invert`, …          |
| `structural.c`  |         1,083 | 22: `gather*`, `concat*`, `scatter`, `til`, `expand`, `rows_of`, …      |
| `elementwise.c` |           676 | 7: `ew_bit ew_cast ew_chain ew_cmp ew_eq_ids ew_val ew_widen`           |
| `search.c`      |           535 | 12: `bin`, `find_*`, `member_*`, `run_starts*`, `where_bits`            |
| `coc.c`         |           507 | 13: `alp_*`, `coc_block_start decode encode encode_below over shift`    |
| `pass.h`        |           170 | none: the thread pool                                                   |
| `ids.h`         |           148 | none                                                                    |
| `reduce.c`      |            96 | 2: `bit_rows_over`, `over_bytes`                                        |
| `scan.c`        |            91 | 1: `scan`                                                               |
| `own.c`         |            77 | 1, on (b): `own_write`                                                  |
| `sym.h`         |            69 | none                                                                    |
| `env.c`         |             5 | 1: `stop`                                                               |

- Not reached: `handle.c`, `interp.c`, `time.c`, `zip.c`, the rest of `own.c`, and 192 of the 269 entries.
- The table is the C of qlean `master`. `doc/qlean-rust-progress.md` is stale; the port's state is the next section.

### 1.8 The Rust port today, against the 78 reached entries

Read from branch `rust-port-0` at `77b82f0` (2026-11-16) without checking it out: the Rust set is every
`fn qlean_*` under `rust/src`, the C set every `LEAN_EXPORT … qlean_*` under `c/`, both intersected with the 78
names of `/data/tmp/relc-audit/out.tsv`.

| measure                                             | value                                              |
|-----------------------------------------------------|----------------------------------------------------|
| Rust in `rust/src`                                  | 22,315 lines, 111 `qlean_*` entries                |
| C files deleted on the branch                       | `coc.c scan.c reduce.c own.c env.c handle.c`       |
|                                                     | `interp.c time.c zip.c`                            |
| C files left                                        | `sort.c structural.c search.c elementwise.c`,      |
|                                                     | `abi.c rt.c`, headers `coc.h ids.h pass.h sym.h`   |
| reached entries whose Lean entry is Rust            | 28 of 78                                           |
| more on `rs2-B13`, `B18`, `B22`, `B31`, not merged  | 19                                                 |
| reached entries whose Lean entry is still C         | 31                                                 |

The 31 still C after those four branches merge:

- `sort.c` (12): `distinct_syms grade_guid grade_ids grade_syms group_ids group_ids_foR group_ids_pair`
  `group_ids_pair_ids group_sizes id_groups id_longs intern_syms rank_slices` — two of them, `group_ids` and
  `id_groups`, are the native ABI (b).
- `structural.c` (13): `all_below concat_ids expand gather gather_bits gather_foR gather_foR_idx gather_ids`
  `gather_ids_foR gather_syms rows_of scatter`, and `symdict_concat`.
- `search.c` (4): `bin find_sym_scalar run_starts run_starts_bits`.
- `elementwise.c` (1): `ew_chain`.

Limits of this count: an entry counts as C when its `LEAN_EXPORT` is in C, even if its loop already calls a Rust
`qrs_*` function, so the C left to port is less than 31 entries suggests. The reached list is of 2026-11-15; step
0 reruns `Reach.lean`. So the crate is mostly an extraction of Rust that exists, plus these 31 entries.

## 2. The allegory and fixed-point core the new package carries

### 2.1 Contents: concrete relations, no class

Leading option (decision A of section 6). The package carries the model; freyd keeps the abstract layers.

| piece               | declarations                                                  | count    | written from        |
|---------------------|---------------------------------------------------------------|---------:|---------------------|
| type and operations | `Rel α β ≜ α → β → Prop`; `id comp recip inter union zero le` |        8 | `Freyd/RelSet.lean` |
| structure maps      | `top graph corefl rpair rprodMap inl inr junc`                |        8 | `RelSet`, `Junc`    |
| unfolding lemmas    | `ext le_iff comp_apply recip_apply inter_apply union_apply`   |        6 | `RelSet`            |
| laws                | `comp_assoc inter_idem union_idem le_antisymm le_trans`       |        5 | pointwise, one line |
| fixed points        | `mu`, `nu`, `Monotonic`, and the laws now in `Den.lean`       | 3 + laws | `Rel/Lang/Den.lean` |

- Size: about 27 declarations and 120 source lines, plus the fixed points. Against 58 (111) if the class chain
  were copied, and 226 if the bridge's cone were.
- The 26 proof-only declarations of section 1.3 become the 11 lemmas above; the other 15 have no counterpart.
- Notation stays what the sources write: `≫ ° ∩ ∪ ⊑ 𝟙 𝟘`, declared on `Rel`. So decision D3 = E of
  `doc/rel-denotation-design.md` (write `den` with the operators, never pointwise) still holds. What changes: a
  generalisation to another allegory happens in the bridge, not in `den`.
- Unbundled: `Den A B ≜ Rel A.El B.El`. Freyd's `RelSet` bundles the carrier in a structure only so that its
  instances do not collide with the category on `Type`; with no instance there is nothing to collide.
- Why this is not a duplicate of `Freyd/RelSet.lean`. Freyd's file states that `Rel(Set)` satisfies the book's
  axioms, layer by layer, and changes when a layer of chapter 2 changes. The package's file states what a Rel
  program means and changes when the language gains an operator. Freyd's hom-set `A.carrier → B.carrier → Prop`
  is `Rel A.carrier B.carrier` by definition, so the bridge ties each operator by `rfl` (section 4.4).
- Not carried, because Rel proper does not reach them: the classes of 2.1 to 2.4, division, power, tabular and
  unitary structure, `relCata`, `InitialAlgebra`. The request names division, power and fold; Rel defines all
  three on relations directly (`ldivDen`, `List A.El` as `𝒫A`, the fold from the values of a coreflexive,
  `doc/rel-denotation-design.md` section 1.4) and cites no Freyd or AOP declaration for them.
- The core uses no axiom beyond `propext` and `Quot.sound` today; a gate keeps it so (section 4.3).

### 2.2 Duplicates and the one survivor

| knowledge                       | copies                                                           | survivor    |
|---------------------------------|------------------------------------------------------------------|-------------|
| least, greatest fixed point of  | `LeetQ.Rel.Lang.lfp`, `gfp` (`Den.lean:40,43`, on `Den A B`)     | `mu`, `nu`  |
| a map on a hom-set              | `LeetQ.Rel.Refold.lfp` (`RefoldSpec.lean:19`, on `α → β → Prop`) | on `Rel α β`|
|                                 | `Freyd.Alg.mu`, `nu` (`AOP/A6_2.lean:53,56`, by `Inf`, `Sup`)    |             |
| monotonic map                   | `Refold.Mono`; `Freyd.Alg.Monotonic` (`A6_2.lean:49`)            | `Monotonic` |
| a relation as a predicate       | `Refold.Rl α β`; `Den A B`; the `RelSet` hom                     | `Rel α β`   |

- Name: B&dM write `(μX : φX)` and `(νX : φX)` (Theorem 6.1), and the Rel surface syntax writes `μ`, `ν`. So the
  survivor is `mu`/`nu`, and `lfp`/`gfp` go.
- Definition: `mu φ ≜ fun x y => ∀ Y, φ Y ⊑ Y → Y x y`, stated once for `φ : Rel α β → Rel α β`. `Den A B` is
  `Rel A.El B.El` and `Rl α β` is `Rel α β`, so both copies become uses. `Refold.lfp` and `Refold.Mono` are
  deleted; `RefoldSpec` states `rounds_lfp` against `mu`.
- `AOP.A6_2.mu` stays in freyd: the same fixed point in any locally complete allegory. The bridge proves
  `Rel.mu φ = Freyd.Alg.mu φ` at `RelSet` once; both are the meet of the prefixed points.
- `Gen.mu`, `Gen.nu` (`Run/Lang/Gen.lean:229,211`) are the code that computes them, not a copy; they stay.
- `A6_FixedPoint.LeastFixedPoint` is AoPA's point-level predicate, not an operator; out of scope.
- The `Rel k v` / `RelRep` / `FinRel` clashes in `duplicated.md` are not in the cone; the split does not carry them.

## 3. The qlean part

### 3.1 Where the Lean model and FFI of each kernel live

In the new Lean package. A kernel is one `@[extern "qlean_…"] def` whose Lean body is the specification
(`SURVEY.md` section 4), so model and FFI declaration are one declaration and cannot be in two places.

| new module         | from                                               | content                                |
|--------------------|----------------------------------------------------|----------------------------------------|
| `Rel.Kernel.Value` | `QLean/Value.lean`, 219 of 393                     | `Column`, `QAtom`, readers, writers    |
| `Rel.Kernel.<Fam>` | `QLean/Kernel/<Fam>.lean`, 7 families, 318 of 1258 | the `@[extern]` defs of the 77 entries |
| `Rel.Kernel.Own`   | `QLean/Db/Own.lean`, 1 of `Db.ObjectFile`          | `own_write` for the native path        |
| `Rel.Kernel.Dep`   | 3 + 3 + 5 of `Dep.Val`, `Dep.Monadic`, `Eval.Val`  | the value helpers `Run.Core` names     |
| `Rel.KernelSpec.*` | `QLean/Verify/*`, 20 modules, 224 of 721           | the lemmas `Rel.KernelWF` cites        |

What "qlean depends on that crate" forces without stating:

- **qlean must also `require` the new Lean package.** Otherwise `Column` and each kernel's Lean body exist twice,
  and two bodies can disagree with one C function.
- **The unit of the split is the declaration, not the module.** A precompiled Lean module that keeps an
  `@[extern]` for a function outside the crate fails to link. So each kernel module is split in qlean first: the
  declarations in the closure move, the rest stay in `QLean/Kernel/<Fam>.lean` and import the moved part.
- `QLean.Value` is one of qlean's shared files (`AGENTS.md` rule 3). Its `Column` half becomes owned by the new
  repository; a change to it is a change there plus a pin bump in qlean.
- The trust hole is unchanged: `#print axioms` cannot see a Lean body disagreeing with its kernel. The checks on
  it (`decide` beside `#guard` in `Kernel/Test.lean`) move with the declarations they test.

### 3.2 The crate

One crate, here called `relk`, in `crate/`. It is an extraction from `qrs` on `rust-port-0`, not a new port.

| `qrs` module on `rust-port-0`                                     | goes to                               |
|-------------------------------------------------------------------|---------------------------------------|
| `lean rt pod simd c ffi` (the Lean object mirror, the scaffold)   | `relk`; qlean's crate uses them       |
| `coc cocops codec enc alp bits res unpack layout kwin key`        | `relk`: the column encoding           |
| `sort group ids sym search structural ew reduce scan pool`        | `relk`, split by function as in 3.4   |
| `ffi/{coc,ew,reduce,scan,search,structural}`, `ffi/sort` (B22)    | `relk`: the reached entries; the rest |
|                                                                   | of each file stays in qlean's crate   |
| `own`, `ffi/own`                                                  | `relk`: `own_write`; the rest stays   |
| `zip interp os why`, `ffi/{zip,interp,handle,time,env}`           | qlean's crate, except `env`'s `stop`  |

- The crate is pure Rust if the cut waits for the 31 entries of section 1.8 (decision N). Otherwise it carries
  `sort.c`, `structural.c`, `search.c`, `elementwise.c` and the four headers in `crate/c/` behind a `build.rs`
  (decision M), until they are ported.
- `crate-type = ["staticlib", "rlib"]`. The `#[no_mangle]` exports sit behind a cargo feature `ffi`, on by default.
- Kept from the existing design: `no_std` + `alloc`, `panic = "abort"`, no dependency, the pinned Rust toolchain
  of `rust/rust-toolchain.toml`, `unsafe` confined to the named modules, `objcopy -G` so that only the exports are
  global. `rust/GATES.md`, `BENCH.md`, `reach.sh` and `testdata/` move with the code they test.
- The module-to-crate table is by name and by the families of 1.7. Step 1 replaces it by the measured one: the
  Rust items reachable from the 78 entries, from `reach.sh` or the compiler's dead-code report on a crate that
  exports only those.

### 3.3 How qlean consumes it

| what qlean needs                       | how                                                                  |
|----------------------------------------|----------------------------------------------------------------------|
| `Column`, kernel defs, their lemmas    | `require rel from git "<url>" @ "<rev>"` in qlean's lakefile         |
| the kernel objects at link time        | the `extern_lib` of package `rel`; qlean's `qleankernel` drops them  |
| Rust types and safe functions          | Cargo: `relk = { path = "<lake packages>/rel/crate",`                |
|                                        | `default-features = false }`                                         |
| C headers, only under decision M       | `-I <rel package>/crate/c` until the last reached entry is Rust      |

- One pin. The Cargo dependency is a path into the checkout lake fetched, so the lake manifest's revision decides
  both the Lean package and the crate. A `git` Cargo dependency would be a second pin that can disagree.
- `default-features = false` drops the `ffi` exports from the copy compiled into qlean's crate, so each exported
  symbol is defined once, in `librelk.a`. Gate: `nm -g` over qlean's final link shows no symbol defined twice.
- For development qlean overrides the path with `lake -K rel=<dir>`, as leetq does for qlean today.

### 3.4 Which C has to become Rust first, and what is split

The Rel-used kernels still C-only are the 31 entries of section 1.8, in four files. For a pure-Rust crate they
are ported before the cut; that is the port's own remaining work on Rel's path, and its order does not change.

What the cut itself decides, function by function, is ownership inside each Rust module:

| Rust                                                    | at the cut                                          |
|---------------------------------------------------------|-----------------------------------------------------|
| the 78 reached entries and what only they call          | move to `relk`                                      |
| helpers both a reached and an unreached entry call      | move to `relk`, made `pub`; qlean's crate calls     |
|                                                         | them through the Cargo dependency                   |
| unreached entries and what only they call               | stay in qlean's crate                               |

- In Rust the shared-helper case costs a visibility change, where in C it needed a header moved between
  repositories. That is the reason to cut after the port rather than before.
- While any reached entry is still C, its headers (`coc.h`, `ids.h`, `sym.h`, `pass.h`) are needed on both sides;
  under decision M they move to `crate/c/` and qlean's C includes them from there.
- `c/rt.c` (the Lean runtime symbols a native Rel program links without the Lean runtime) and `c/abi.c` are
  small and Rel-only or boundary-only; `rt.c` moves to the crate as is.

### 3.5 Vendor, depend, or split

Recommendation: **split qlean by declaration and by function into the new repository; qlean depends on it.** That
is what the request states. Vendoring leaves two copies of the kernels and of 783 declarations to keep in step.
The new package depending on qlean is what leetq does now, and pulls 90 modules for 33.

### 3.6 The first new kernel: row comparison

CRel performance work is deferred to the new repository, and this is its first item.

- Motivation. `master` makes every `CRel` answer canonical (sorted by `Obj.lt`, no duplicate) by sorting after
  every op. `Lang/Test` went from 52.9 s to 74 s, mostly sorting `.arr`-valued rows. Checking orderedness in Lean,
  row by row through `Vals.row`, made `SudokuPC9` 4 times slower. Producing canonical output by construction
  needs the comparison in native code.

| kernel                 | what it computes                                             | used by            |
|------------------------|--------------------------------------------------------------|--------------------|
| row comparison         | lexicographic `Obj.lt` on two rows, over symbol, `arr`, sum  | the three below    |
|                        | and product values                                           |                    |
| strictly ascending     | every adjacent pair of rows is `Obj.lt`: canonical or not    | skipping the sort  |
| merge with dedup       | two canonical tables to one canonical table                  | `∪`                |
| per-key k-way merge    | k canonical runs per key to one canonical run                | `comp`             |

- Each is one `@[extern] def` in `Rel.Kernel.Row`, written in Rust from the start (no C twin), with the Lean body
  as its model.
- The spec of the first is one theorem: the kernel's result equals `Obj.lt` (`Rel/Spec/ObjOrder`) on the two
  decoded rows. The other three are specified against it: ascending is `List.Pairwise Obj.lt` of the rows; the
  merges return the canonical form of the union of their inputs.
- `Obj.lt` is the one definition of the order. The kernel's Lean body calls it and does not restate it by cases,
  so the Rust is the only second statement of the order, and the `decide` beside `#guard` pair checks that one.
- Gate for the item: `Lang/Test` at or below 52.9 s, and `SudokuPC9` no slower than before the Lean-side check.

## 4. Repository layout

### 4.1 Names and tree

Repository `rel`, Lean package `rel`, crate `relk`. Every module is under the root `Rel`: today's `LeetQ.Rel.*`
namespaces lose the `LeetQ.` prefix and `QLean.Kernel` becomes `Rel.Kernel`.

```
rel/
  lakefile.lean  lean-toolchain  lake-manifest.json  Makefile  CLAUDE.md
  Rel/Core/       Rel Mu                                                  (section 2)
  Rel/Kernel/     Value Coc Elementwise Structural Sort Scan Search Reduce Own Dep Row
  Rel/KernelSpec/ the used lemmas of the 20 Verify modules; LeetQ/Rel/KernelWF (49)
  Rel/Run/        LeetQ/Run/*  and  LeetQ/Run/Lang/*                      (runtime, compiler)
  Rel/Spec/       LeetQ/Rel/{CRel*,Rep*,ObjOrder,OkBit,AC3,RefoldSpec}    (laws)
  Rel/Lang/       LeetQ/Rel/Lang/{Den,GenSpec,BitsSpec*,PlanSpec,EmitC,RelRep}
  Rel/Programs/   Prelude, and the programs decision G/H/I assigns
  Rel/Test/       LeetQ/Rel/Lang/Test*, CanonTest, AlgTest, EmbedTest, ModuleTest
  crate/          Cargo.toml rust-toolchain.toml src/ c/rt.c   (build.rs and more of c/ only under decision M)
  doc/            the moved documents (section 5.3)
```

### 4.2 Lake targets

| target               | modules                        | precompiled | imports                     |
|----------------------|--------------------------------|-------------|-----------------------------|
| `lean_lib RelCore`   | `Rel.Core.*`                   | no          | toolchain only              |
| `extern_lib relk`    | runs `cargo build` in `crate/` | —           | —                           |
| `lean_lib RelKernel` | `Rel.Kernel.*`                 | yes         | toolchain                   |
| `lean_lib RelRun`    | `Rel.Run.*`                    | yes         | `RelKernel`                 |
| `lean_lib Rel`       | all the rest                   | no          | `RelCore`, `RelRun`         |
| `lean_exe relc`      | `Rel.Test.Native`              | —           | —                           |
| `target rel-native`  | as `rel-native-1a` today       | —           | `librelk.a`, `crate/c/rt.c` |

- `lakefile.lean`, not TOML: an `extern_lib` and the cargo target need it. No `require`.
- `lean-toolchain` is `leanprover/lean4:v4.28.0`, which freyd, leetq and qlean all pin today.
- Two precompiled libraries keep today's property that an edit to a proof rebuilds no shared library.
- `Run.Core` and `Run.Code` import proof modules (`Verify.*`); that is item 2 of `doc/rel-architecture-review.md`.
  The split does not fix it, it only puts both ends in one package.

### 4.3 Gates (`make check`)

| gate                                              | reads                                                 |
|---------------------------------------------------|-------------------------------------------------------|
| `scripts/cap lake build`                          | everything, with the `#guard` and `decide` pairs      |
| `cargo test` in `crate/`                          | the crate's unit and differential tests               |
| axioms of `Rel.Core.*` ⊆ `{propext, Quot.sound}`  | every declaration of `RelCore`, by enumeration        |
| no `sorryAx`, no `Lean.ofReduceBool`              | the index table `dep`, every module                   |
| `panic!` only on the allowlist                    | the index table `dep` (`panicWithPosWithDecl`)        |
| every `@[extern]` name is defined in `librelk.a`  | `Lean.getExternNameFor` over `RelKernel` against `nm` |
| the native executable links libc, libm, libpthread | `ldd` (gate 1 of `rel-native-design.md`)             |

The differential corpus against a live q (`qlean-test`) stays in qlean: it needs the q licence and tests q.

### 4.4 What freyd and qlean keep

- **freyd drops leetq and keeps the bridge.** `leetq/` shrinks to the six `LeetQ.Aop` modules, renamed `relaop/`,
  with `require freyd from ".."` and `require rel`. It is the only place that sees both the book and Rel.
  `Freyd/` and `AOP/` never import the new package, so their import rule holds unchanged.
- The bridge gains the theorems that tie model to axioms. Per operator, the package's definition is the field of
  freyd's `RelSet` instance, by `rfl`: `Rel.comp R S = R ≫ S`, the same for `recip inter union zero id le` and the
  eight structure maps; then `Rel.mu = Freyd.Alg.mu` at `RelSet`. About 18 one-line theorems.
- The bridge is where the 281 AOP and 226 Freyd declarations are used. It imports freyd; nothing is copied.
- qlean keeps the q checker, evaluator, parser, wire format, database files, and the 192 unreached kernels with
  their Lean models. It gains `require rel` and the Cargo path dependency.
- freyd's index drops `LeetQ.*`; `scripts/lean-refactor index` runs in the new repository for its own database.

## 5. Migration plan

Each step ends with every listed build green. Renames go through `scripts/lean-refactor`.

| # | where | change                                                                          | green after         |
|---|-------|---------------------------------------------------------------------------------|---------------------|
| 0 | qlean | merge `rs2-B13`, `B18`, `B22`, `B31`; port the 31 entries of 1.8 (decision N);  | freyd, leetq, qlean |
|   |       | merge `rust-port-0` into `master`; rebuild the index; rerun `Reach.lean`;       |                     |
|   |       | in freyd commit the untracked `doc/rel-*`, `doc/qlean-*`; tag both              |                     |
| 1 | qlean | recompute 1.6 to 1.8; split the 7 kernel modules, `Value`, `Db.Own` and the 20  | qlean, leetq        |
|   |       | `Verify` modules by declaration into `QLean/RelPart/*`; cut the 8 imports;      |                     |
|   |       | split `rust/` into two crates in one workspace, `rust/relk` and `rust/qrs`      |                     |
| 2 | leetq | write the concrete core as `LeetQ/Core/*`; switch Rel proper from `Freyd.*` to  | freyd, leetq        |
|   |       | it (`⟨A.El⟩ ⟶ ⟨B.El⟩` becomes `Rel A.El B.El`); merge `lfp`, `gfp`,             |                     |
|   |       | `Refold.lfp` into `mu`, `nu`; `LeetQAop` gains the tying theorems               |                     |
| 3 | leetq | import `QLean.RelPart.*` only; Rel proper now names nothing in freyd and        | leetq               |
|   |       | nothing of qlean outside `RelPart`; rerun the query of 1.2 to confirm           |                     |
| 4 | new   | create the repository from history (5.2); rename modules and namespaces to      | new                 |
|   |       | `Rel.*`; write the lakefile with the cargo target, the gates of 4.3             |                     |
| 5 | qlean | delete `QLean/RelPart`, `rust/relk`; `require rel`; Cargo path dependency;      | new, qlean          |
|   |       | run `qlean-test` against q                                                      |                     |
| 6 | freyd | delete `leetq/` except the bridge, renamed `relaop/`; drop `-K qlean`; reindex  | all four            |
| 7 | new   | the row comparison kernel (3.6)                                                 | new, qlean          |

Steps 1 to 3 do the whole cut inside the old repositories along file boundaries. Step 4 is then a move of paths
and a rename, and a failure before step 4 costs nothing to undo.

### 5.2 History

`git filter-repo` on a fresh clone of each repository, then one merge of the two unrelated histories:

- freyd clone: keep `leetq/` and the `doc/` files of 5.3; rename paths to the tree of 4.1.
- qlean clone: keep `QLean/RelPart/`, `rust/relk/`, `c/rt.c`; rename paths. A function moved between Rust files
  in step 1 shows that step as its origin.
- No `Freyd/` file is filtered: the concrete core is written in step 2 inside `leetq/` and comes with it.
- `git blame` then works on every Rel, kernel and C line. A file split in step 1 shows the split as its origin;
  the older history is one `git log --follow` away in qlean.

### 5.3 Documents

- Move with history: `doc/rel-*` except this file, `doc/qrel-total-*`, `doc/leetq-*`, `doc/qlean-rust-*`,
  `doc/qlean-kernel-*`, `doc/qlean-usize-audit.md`, `doc/rel-bench*`, `doc/rel-done-tasks.md`, `leetq/CLAUDE.md`,
  and `SURVEY.md` from qlean (untracked there today).
- Stay in freyd: `doc/rel-lean-mapping.md` and `doc/rel-mss-proof-design.md`, which describe the bridge.
- This file stays in freyd until step 6 and is then replaced by one line naming the new repository.

### 5.4 Risks

- **Notation clash in the bridge.** The package and freyd both declare `≫ ° ∩ ∪ ⊑ 𝟙 𝟘`, and the bridge imports
  both. No declaration name is shared (`Rel.*` against `Freyd.*`). Both notation sets are scoped; a bridge file
  opens one and writes the other side by name.
- **Step 2 touches many statements.** 1,137 declarations mention `RelSet.mk` after elaboration. In source most
  come through `Den`, `Rl` and a few abbreviations, so the rewrite is of those; build module by module.
- **Namespace written twice.** lean-refactor has doubled a namespace on rename before. After each rename, query
  the index for `Rel.Rel.` and `Rel.LeetQ.`.
- **Module root `Rel` beside freyd's `rel/`.** They differ only in case, and are never in one package; the bridge
  imports `Rel.*` and `AOP.*`, never `rel.*`.
- **Choice.** `Rel.Core` is choice-free and gated. The rest is not: 89 declarations in 28 modules of
  `LeetQ.Rel` name `Classical.propDecidable`, 11 name `byContradiction`, and `Rel.Holds` has choice through
  `Column.atoms`. The new `CLAUDE.md` states that the constructive rule covers `Rel.Core` only.
- **`Freyd/` stays Mathlib-free.** Holds under decision A: nothing in `Freyd/` or `AOP/` imports the package.
  Decisions B and C add one toolchain-only import.
- **`sorry`, `native_decide`.** None in leetq or in the qlean cone by the index; gated.
- **`panic!`.** 12 declarations in leetq (10 in `Rel`, 2 in `Run`) and 6 in the qlean cone. They go on the
  allowlist at step 4 and are removed later; no new one passes the gate.
- **A cut import was load-bearing.** The 8 imports of 1.6 carry no constant, but may carry an instance or a
  notation. Step 1 builds qlean after each cut.
- **A symbol defined twice.** `relk` is linked as a static library and also compiled into qlean's crate. Feature
  `ffi` is off in qlean, and the `nm` gate checks it.
- **Build time in qlean.** A kernel relink rebuilds 547 precompiled jobs, about 5 minutes. Unchanged, but now paid
  on every pin bump.
- **The aima session's programs.** `Programs/*` are edited elsewhere. Decision G/H/I; freeze them for step 4.

## 6. Open decisions

**1. What allegory does the new package carry, and how does freyd relate to it?**
The new package may depend on nothing. Freyd's import rule exists to keep Mathlib, Batteries and Aesop out; a
package that depends on the toolchain only meets that reason, so freyd importing it is possible (B, C).

- **A — concrete relations only; freyd keeps its abstract layers and imports nothing.** The package has `Rel α β`,
  its operations, five laws and `mu`/`nu`: about 27 declarations (section 2.1). Freyd is untouched: chapter 2
  stays where the book puts it and no `lean:` marker moves. The bridge in freyd ties model to axioms by about 18
  `rfl` theorems. What exists twice is the pointwise definition of 16 operations, as two different things: the
  fields of an instance in freyd, the meaning of a language in the package.
- **B — as A, and freyd imports the package.** `Freyd/RelSet.lean` builds its instances from the package's
  operations and lemmas, so the 16 pointwise definitions exist once. Cost: one exception to "`Freyd/` imports
  only the toolchain and `Freyd.*`"; every `lake` call in freyd elaborates a lakefile with a cargo target; the
  statement keys of the `RelSet` declarations change, so their `lean:` markers are recomputed; a change to the
  language's core can rebuild the book.
- **C — the abstract core moves to the package and Freyd's `S2_*` files build on it.** One copy of `Cat`,
  `Allegory`, `DistributiveAllegory`: 58 declarations, or 226 with division and power if the bridge moves too.
  Cost: as B; the book's section 2 terms are defined outside the book repository; every `lean:` marker to them
  follows; and Rel carries class layers that section 1.4 shows it does not use.

Decided: **A** (2026-11-16).

Recommendation: **A**. Section 1.4 shows Rel proper uses no class and proves nothing for an arbitrary allegory,
so C moves 58 declarations to serve no user and pays for it in the notes. B removes a real but small repetition
(16 one-line definitions) at the price of a build edge from the language into the book. B can be taken later
without redoing anything: its only prerequisite is that the package exists.

**2. How much of each kernel family moves?**

- **D — by declaration: the 78 reached entries and their closures.** 783 Lean declarations and the Rust they
  reach. Needs step 1's split of 7 Lean modules and of each Rust module by function.
- **E — by file: the seven kernel families whole.** About 1,650 Lean declarations and nearly all of `rust/src`
  except `zip interp handle time`. No split, but 192 entries Rel never calls move into the Rel repository.
- **F — only the native ABI (b) now, the rest later.** 3 entries. The interpreter path keeps a dependency on
  qlean, so the new package is not independent yet.

Decided: **D** (2026-11-16).

Recommendation: **D**. It is what "only take what's necessary" says. E is the fallback if step 1 shows that the
helpers shared with unreached entries are most of `sort.rs` or `structural.rs`.

**3. Where do `Programs/*` live?** They belong to the aima session.

- **G — all 17 move** to `Rel/Programs`. `TestChess`, `TestWumpus`, `TestKnapsack` and others import them, so
  they are the language's test corpus.
- **H — `Prelude` and the programs a test imports move; the rest go to a package of the aima session** that
  requires `rel`.
- **I — only `Prelude` moves**; the tests that need a program move out with the programs.

Decided: **G** (2026-11-16): all 17 `Programs/*` move with Rel.

Recommendation: **H**. The language keeps the tests that exercise it; the AIMA work keeps its files and its pace.

**4. History.**

- **J — `git filter-repo` from both repositories, merged** (5.2).
- **K — fresh start**: one initial commit naming the two source shas.
- **L — `git subtree split` of `leetq/` only**; qlean's part as a fresh commit.

Decided: **J** (2026-11-16).

Recommendation: **J**. Steps 1 to 3 put every moving file on a path of its own, which is what makes J cheap.

**5. Does the cut wait for the last 31 entries to be Rust?**

- **M — no: cut now; the crate carries `sort.c`, `structural.c`, `search.c`, `elementwise.c` and four headers**
  behind a `build.rs`, and qlean's C includes headers from the crate until the port ends.
- **N — yes: steps 0 to 3 run now, step 4 runs when the 31 entries are Rust.** The crate is pure Rust from its
  first commit: no `build.rs`, no C header shared across repositories.
- **O — cut now and leave the 31 entries in qlean**; the new package depends on qlean for them until ported.

Decided: **N** (2026-11-16). The 31 entries were ported since; all 78 are Rust at qlean `rust-port-0` `6ce2f09`.

Recommendation: **N**. 47 of the 78 entries are Rust or on a finished branch, nine C files are already deleted,
and steps 1 to 3 (the Lean split, the concrete core) do not wait for the rest. O breaks "do not depend on others".
