# Counts become `USize`: implementation plan

Decided design (2026-11-11): the count of a vector is a `USize` in qlean (`QValue.vector`, `WFAt`, `Enc.WF`, every
dispatcher) and in leetq (`Arr`'s index); an op whose result count is computed asserts at run time that it fits.
The qlean signature and representation changes are approved.

Sources: qlean `master` at `a260b4e` (`/home/dh/repo/qlean`), leetq in the freyd checkout at `54603fa`. A declaration
name is the anchor, a line is a pointer. Nothing was built with lake. Three scratch files were checked with `lean`
(toolchain `v4.28.0`, core only) under `/data/tmp/qlean-len/`: `NatKernel.lean`, `Call.lean`, `Assert.lean`. "Ran"
marks a claim resting on them, "read" one resting on a source line, "unread" a part nobody has read yet.

```
                today                                      after
vector          n : Nat                                    n : USize
dispatcher      gradeColumn (n : Nat) … n.toUSize          gradeColumn (n : USize) … n
kernel          grade (n : USize)   model: n.toNat         unchanged
leetq           Arr t (n : Nat),  K … n.toUSize            Arr t (n : USize),  K … n
theorem         (K n.toUSize).size = (n % USize.size) * w  (K n).size = n.toNat * w   = what Enc.WF asks
growing op      n + m in Nat, no bound                     need (n.toNat + m.toNat < USize.size) … else stop
```

Each kernel already takes `n : USize` and its model already says `n.toNat` elements (read: `tilLongs`
`Kernel/Structural.lean:588`, `Ew.val` `Kernel/Elementwise.lean:428`, `Scan.scan` `Kernel/Scan.lean:253`, `grade`
`Kernel/Sort.lean:188`, `Coc.decode` `Kernel/Coc.lean:159`). The modulus came from converting a `Nat` count at the
call: 147 `toUSize` in `leetq/LeetQ/Rel`, about 230 in `QLean/Kernel`, about 209 in the rest of `QLean`. With the
count a `USize` from the header down, those conversions are deleted and no kernel or C stub changes for a count.

## 1. The new definitions

qlean, `QLean/Value.lean` (today at `:267`, `:930`, `:1119`, `:2205`; the only change is the type of `n` and `.toNat`
on the right sides):

```lean
  | vector : (t : QAtomicType) → (n : USize) → (enc : Enc) → (attr : Option (UInt8 × IndexCell)) → QValue

def WF (t : QAtomicType) (n : USize) (e : Enc) : Prop :=
  match t, e with
  | .general, .gen xs => xs.size = n.toNat
  | .boolean, .bits b => b.size = (n.toNat + 7) / 8
  | .symbol, .syms _ offs => offs.size = n.toNat + 1
  | .symbol, .enum _ offs ids => idsCap ids (idWidth offs) n.toNat = n.toNat
  | .boolean, .bytes _ => False
  | t, .bytes b => match t.width with
    | some w => b.size = n.toNat * w
    | none => False
  | t, .foR metadata _ =>
    t.width.isSome ∧ t ≠ .boolean ∧ t ≠ .guid ∧ n.toNat ≤ blk * nblk metadata
  | t, .alp metadata _ a =>
    (t = .real ∨ t = .float ∨ t = .datetime) ∧ n.toNat ≤ blk * nblk metadata ∧ alpF32 a = (t.width == some 4)
  | _, _ => False

def QValue.WFAt (t : QAtomicType) (n : USize) : QValue → Prop
  | .vector t' n' e _ => t' = t ∧ n' = n ∧ Enc.WF t n e
  | _ => False
```

Each right side is computed in `Nat` from `n.toNat`: "the payload holds exactly `n.toNat` elements at its layout".
`(n.toNat + 7) / 8` and `n.toNat + 1` must not be written `(n + 7) / 8`, `n + 1` in `USize`, which wrap.
`QValue.count : QValue → Option Nat` (`Value.lean:2203`) keeps its type and answers `some n.toNat` for a vector: a
table's or a slice list's count is not a vector header.

leetq, `leetq/LeetQ/Rel/Core.lean:31`:

```lean
abbrev Arr (t : QAtomicType) (n : USize) := {v : QValue // v.WFAt t n}
```

and with it `Arr.get (x : Arr t n) (i : Fin n.toNat)`, `length_toList : x.toList.length = n.toNat`,
`Vals A (n : USize)`, `Rel.n : USize`, `Part A := (n : USize) × Vals A n`, `Code.n : USize`.

One new constructor, the value a failed assert's model returns (section 2):

```lean
/-- `n` null elements of `t`, for every `n`: replicated payloads, sizes by `Array.size_replicate`. -/
def Enc.blank (t : QAtomicType) (n : USize) : Enc
theorem Enc.blank_WF (t : QAtomicType) (n : USize) : Enc.WF t n (Enc.blank t n)
```

`Enc.blank` is `.gen (Array.replicate n.toNat _)` at `general`, `.bits` of `(n.toNat + 7) / 8` zero bytes at
`boolean`, `.syms` with `n.toNat + 1` zero offsets at `symbol`, `.bytes` of `n.toNat * w` zero bytes elsewhere. It
needs no bound because a replicated array has the size asked for. leetq lifts it to `Vals.blank (A : Obj) (n : USize)
: Vals A n`, by the same recursion as `Vals.empty` (`Code.lean:423`). Unread: whether qlean already has such a
constructor under another name; search the index before adding it.

## 2. The one run-time assert

```
op (x : Arr t n) (y : Arr t m) : Arr t (n + m) :=
  need (n.toNat + m.toNat < USize.size)          -- the check, on the operand counts, before the kernel runs
    (fun _ => s!"concat: counts {n} and {m} do not fit a USize")
    (fun _ => Arr.blank t (n + m))               -- the model's value where the check fails; the C never returns it
    fun h => ⟨kernel x y, proof using h⟩
```

Two declarations in qlean serve every growing op and every entry point (ran: `Assert.lean`, where `concat`,
`concat_val` and `ofBytes` are built with them and print `[propext, Quot.sound]`):

```lean
/-- Model: the fallback value. C: prints `msg ()` to stderr and exits 1; it never returns. -/
@[extern "qlean_stop"]
def stop {α : Type} (msg : Unit → String) (model : Unit → α) : α := model ()

/-- The one assert: `k` with the proof where `p` holds, `stop` where it does not. -/
@[macro_inline] def need {α : Type} (p : Prop) [Decidable p] (msg : Unit → String) (model : Unit → α)
    (k : p → α) : α :=
  if h : p then k h else stop msg model
```

```c
LEAN_EXPORT lean_obj_res qlean_stop(lean_obj_arg msg, lean_obj_arg model) {
    lean_object *s = lean_apply_1(msg, lean_box(0));
    fprintf(stderr, "qlean: %s\n", lean_string_cstr(s));
    exit(1);
}
```

- Where the check sits: in the op, as `if h : p`. The proof obtains `h` as the argument of `k`.
- What the failing branch does: at run time `qlean_stop` prints the message, which names the op and the counts, and
  exits with status 1. It is not a silent default: the fallback is never computed by a running program.
- How the failing branch has a value of the result type with no axiom and no `sorry`: in the logic `stop msg model`
  IS `model ()`, a real value (`Arr.blank t (n + m)`, or `⟨0, Vals.empty A⟩` for a result that carries its own
  count). This is the shape of core's own `panicCore` (`@[extern "lean_panic_fn"] def panicCore [Inhabited α] (msg) : α
  := default`); the difference is that the C stops.
- Why not `panic!`: it returns `default` and the run CONTINUES unless `LEAN_ABORT_ON_PANIC` is set, which is a silent
  default; and it needs `Inhabited` of the result type, whose instance would be built before the call. `stop` takes
  the fallback as a thunk, so nothing is allocated for it (read in the emitted C of `Assert.lean`: the two closures are
  allocated between the failed test and the `qlean_stop` call).
- What the C side costs: one export of six lines in an existing object (`c/env.c`, so `lakefile.lean` is untouched);
  the extern receives two arguments, the type `α` being erased (ran: `qlean_stop(lean_object*, lean_object*)`).
- What is trusted: as for every `@[extern]`, that the C agrees with the body WHENEVER IT RETURNS. `qlean_stop` never
  returns, so it adds nothing that can disagree. qlean's stubs already stop this way on a bad kind
  (`c/scan.c:310-312`: `fprintf` then `exit(1)`).
- Recommended: `need` with the C `stop`, as above. One helper, three uses:

| use                         | `p`                                        | fallback                 |
|-----------------------------|--------------------------------------------|--------------------------|
| operand counts, `n + m`     | `n.toNat + m.toNat < USize.size`           | `blank` at `n + m`       |
| operand counts, `n * m`     | `n.toNat * m.toNat < USize.size`           | `blank` at `n * m`       |
| a count a payload reports   | `len b < USize.size` (or `xs.size`, `xs.length`) | `⟨0, empty⟩`       |

Supporting lemmas, once, in qlean: `USize.toNat_add_of_fits (h : n.toNat + m.toNat < USize.size) : (n + m).toNat =
n.toNat + m.toNat` (ran), the same for `*`, and core's `USize.toNat_ofNat_of_lt'`. Each reads "under the bound, the
machine operation is the `Nat` operation".

A law of a growing op holds under the same bound and only under it (ran: `concat_val … (h : n.toNat + m.toNat <
USize.size) : (concat x y).1 = x.1 ++ y.1`). Section 6 says what that costs.

Run-time cost per growing call: two `USize → Nat` conversions, one `Nat` add or multiply, one comparison with the
constant `USize.size` (a `lean_nat_dec_lt` against a closed term). Per call, never per element. Measure on the
growing ops only, at a count of 1, 10⁷ calls, 3 runs, before from the last log.

## 3. Every site and every growing op

"Type" = the kernel is called at the index `n : USize` itself and answers `n.toNat` elements, which is `Enc.WF` at
`n`; no check remains. "Assert" = `need`. Lines are leetq `LeetQ/Rel/`.

The step-4 sites of `doc/leetq-arch-steps-245.md`:

| site                      | closes by | how                                                               |
|---------------------------|-----------|-------------------------------------------------------------------|
| `tilCol` `Code:462`       | type      | `tilLongs n`, `tilLongs_wf n` as it stands (`KernelWF/Raze:77`)   |
| `Vals.compact` `Code:528` | type      | `len (tilLongs n) = n.toNat`                                      |
| `shiftArr` `Code:453`     | type      | `Ew.val … n`, `Ew.val_size` as it stands (`KernelWF/Raze:82`)     |
| `place` `Code:478`        | type      | `Ew.widen … n`, `Ew.val … n`                                      |
| `Vals.pick` arr `Code:499`| type      | every kernel at the index column's count; `decode_size` for `longsOf` |
| `Vals.pick` sum `Code:507`| type      | the same                                                          |
| `Ops.rank` `KernelWF/Reduce:264` | type | `gradeColumn t false n …`; `gradeColumn_isSome` loses `hn`      |
| `raze` `Code:244`         | assert    | `p` = the parts' counts sum below `USize.size`; `hb` is this check |
| `sliceIds` `Code:649`     | assert    | `p` = `ids.size = 8 * (len o - 1)`, the count `rankSlices` reports |
| `setIds` `Code:784`       | assert    | `p` = `ids.size = 8 * len s`                                      |
| `longCol`, `genCol`, `pick` | assert  | their count is read off a payload: third row of the table in section 2 |

`Vals.pick` closes by the type once it takes the index column's count: `Vals.pick A x i (n : USize) (h : len i =
n.toNat) : Vals A n`. A caller whose index column is `tilLongs n` or a gather of one has `h` by a size theorem; a
caller whose index column is data-dependent gets `n` and `h` from one `need` on `len i`.

`sliceIds` and `setIds` are not count sites: `rankSlices` (`Kernel/Sort.lean:396`) answers the EMPTY payload when its
offsets do not ascend or pass its payload. The assert is the same helper on the count the kernel reports. The
references `slicesRef`, `setIdsRef`, `setIdsRef_size` and the guard that compares them are deleted, and so is
`raze`'s `Enc.ofAtoms` branch.

Growing ops (read in `Core.lean`, `Code.lean`; `Alg.lean` read only at the lines a search for `len`, `+`, `*` named):

| op                                         | new count                   | closes by |
|--------------------------------------------|-----------------------------|-----------|
| `col xs` `Code:37`, `ofPairs` `Code:41`    | `xs.length`                 | assert    |
| `colFn n f` `Core:119`                     | `n` given                   | type      |
| `genCol xs` `Code:203`                     | `xs.size`                   | assert    |
| `longCol b` `Code:390`, `setIdCol` `Code:807` | `len b`                  | assert    |
| `pick`, `pickArr`, `Vals.pick`, `pickShared`, `pickN` | `len i`          | type, given the index count |
| `raze`, `Obj.raze` `Code:244,543`          | `Σ` of the parts' counts    | assert    |
| `Code.cat` `Code:159`                      | `Σ` of the parts' counts    | assert    |
| `expand` `Core:509`                        | `Σ max(cnt[i], 0)`, reported | assert   |
| `join` `Code:707`                          | the matches, reported       | assert    |
| `cross n m` `Code:748`                     | `n * m`                     | assert    |
| `anti`, `whereEqV`, every `whereBits`      | the set bits, reported; at most `n` | type: `≤ n.toNat` |
| `tags`, `sumVals`, `junc`, `sum` `Alg:231-257` | `n + m`                 | assert, once, in `raze` |
| `inl`, `inr` `Alg:243,246`                 | `n`                         | type      |
| `≫`, ops at `Alg:63,122,149,175,192,368`   | `len ij.2`, reported        | assert, where the index is made |
| `lt` `Alg:415`                             | `n * n`                     | assert    |
| the `min (len ix) …` ops `Alg:324-655`     | a minimum of reported counts | assert on one count |
| `Lang/Elab.lean:1122,1135`, `Lang/Eval.lean:335,337` | through `col`     | assert in `col` |

A count that a kernel reports and that is at most an existing `USize` count needs no assert: `x ≤ n.toNat` gives
`x < USize.size`. That rule covers `whereBits` (at most `n` positions), `gather` (the index column's count), `fit`.

The list is not the method. After the type of `Arr`'s index changes, every producer whose count is not the kernel's
own argument is a type error; the build enumerates them, and each is fixed by a size theorem or by `need`. A site
that compiles holds no hidden modulus.

qlean's own growing ops (`razeColumn` `Kernel/Structural.lean:1199`, `appendColumn` `:1246`, `expandColumn` `:977`,
the evaluator's `,`, `#`, `where`, the wire readers) are found the same way and take the same `need`. Unread beyond
those names.

## 4. Steps

Gates. qlean: `lake build` in `/home/dh/repo/qlean`, clean, then `./.lake/build/bin/qlean-test` (`AGENTS.md:17-18`; the
test binary needs the q licence daemon). leetq: `lake build <modules>` in `/home/dh/repo/freyd/leetq`, with
`-K qlean=<dir>` to point at a qlean branch (`leetq/lakefile.lean`); the last step's gate is `lake build
LeetQ.Rel.Algebra LeetQ.Rel.Lang.Test rel` with the 228 `#guard` lines of `AlgTest.lean` holding. Run each gate
without a pipe.

Estimates come from the indexes (leetq's current; qlean's from Oct 26, stale) and from text counts in the working
tree; they size a step, they are not obligations lists.

| step | repo  | unit                                                        | serial or parallel                    |
|------|-------|-------------------------------------------------------------|---------------------------------------|
| Q0   | qlean | `stop`, `need`, `qlean_stop`, the two `toNat` lemmas        | alone, first                          |
| Q1   | qlean | `vector`'s `n : USize`; `WF`, `WFAt`, `count`; `Enc.blank`  | serial, one agent                     |
| Q2   | qlean | dispatchers take `n : USize`, one family per agent          | parallel, 7 worktrees                 |
| Q3   | qlean | growing ops through `need`                                  | parallel with Q2 where files differ   |
| Q4   | qlean | size theorems moved in from leetq's `KernelWF`              | after Q2                              |
| L1   | leetq | `Core.lean`: `Arr`, `Vals`, `Rel`, `Obj`, `colFn`, `blank`  | serial                                |
| L2   | leetq | `KernelWF/Raze`, `Gather`, `Reduce`                         | serial after L1                       |
| L3   | leetq | `Code.lean`: the sites and growing ops of section 3         | serial after L2                       |
| L4   | leetq | `Alg.lean`, `AlgTest.lean`                                  | serial after L3                       |
| L5   | leetq | `Lang/`, then `Blocks`, `Chess`, `Wumpus`, `Circuit`        | `Lang/` serial, the programs parallel |

- **Q0.** Files: `QLean/Kernel/Need.lean` (new), `c/env.c`. Theorems: 2 new. No existing declaration changes, so it is
  green alone. The failing branch cannot be a `#guard` (it would stop `lake build`): test it by one run of a small
  executable that must exit 1 with the message on stderr. Gate: `lake build`.
- **Q1.** Files: `QLean/Value.lean` (a shared file: assigned by this plan), then every use the build names. Size:
  972 textual uses of `.vector` in `QLean`, 24 of `Enc.WF`; 32 theorems state something over `.vector` in the stale
  index. This is an error-driven loop: one build shows one wave of errors. Where a dispatcher still wants a `Nat`,
  pass `n.toNat` and leave the dispatcher for Q2; where a `Nat` count must become the header, it is a producer:
  give it `need` here if the file is `Value.lean`, else pass `Nat.toUSize` under a `need` placed in Q3. Serial
  because one inductive's field changes under every file at once. Gate: `lake build`, then `qlean-test`.
- **Q2.** One agent per family module: `Kernel/Coc.lean` (`Enc.bytesOf`), `Sort.lean` (`gradeColumn`, …),
  `Structural.lean` (`razeColumn`, `gatherColumn`, …), `Scan.lean`, `Reduce.lean`, `Search.lean`,
  `Elementwise.lean`, each with its `*Test.lean`. Per family: the dispatcher's `n : Nat` becomes `n : USize`, the
  `.toUSize` inside it and the `.toNat` Q1 put at its callers are deleted. About 230 `toUSize` in `Kernel/`, 209 in
  the callers. `Verify.countFits` (`Verify/Gather.lean:74`) becomes `True` and is deleted with the hypothesis it feeds
  (7 theorems). Callers in `Eval/` are shared between families but in different sections; merge by hunk. A worktree
  agent builds only its family module and its test module; the full `lake build` and `qlean-test` run once in main
  before the merge.
- **Q3.** `razeColumn`, `appendColumn`, `expandColumn` and the evaluator's growing verbs through `need`. Same files as
  Q2's `Structural` agent for the first three: give them to that agent.
- **Q4.** `QLean/Verify/Count.lean` (new): `tilLongs_wf`, `Ew.val_size`, `decode_size`, `grade_size`, `ranks_size`,
  `gradeIds_size`, `gradeColumn_isSome`, `gradeColumn_wf`, `razeColumn_count`, `razeColumn_wf`, `razeColumn_isSome`,
  `bytesOf_size`, restated with no `< USize.size` premise where the count is the argument; `Ew.widen_size` and
  `Scan.scan_size` are new. About 14 theorems; 19 leetq theorems mention `USize.size` today. Gate: `lake build`.
- **L1–L5.** leetq imports are linear (`Core` ← `KernelWF` ← `Code` ← `Alg` ← `Lang` ← programs), so each step is
  green by building its own modules: `lake build LeetQ.Rel.Core`, then `LeetQ.Rel.KernelWF.Reduce`, then
  `LeetQ.Rel.Code`, then `LeetQ.Rel.Alg LeetQ.Rel.AlgTest`, then the final gate. Size: 229 declarations state
  something over `Arr`, `Vals` or `Enc.WF` (56 theorems); 147 `toUSize` are deleted. L2 deletes the theorems Q4 took.
  L3 removes every reference branch of section 3 and the definitions `slicesRef`, `setIdsRef`, `setIdsRef_size`,
  `rankAt`. L4 is where the laws take their bound (section 6). Only L5's four programs are independent files.
- Renames and signature changes go through `scripts/lean-refactor` where it can express them; the index must be
  rebuilt before L1 so that it knows qlean's new statements.

Relation to `doc/qlean-kernel-coverage-plan.md`: its decisions I/J/K (the hypothesis `n < USize.size` of
`scanColumn_isSome`, `mwinColumn_isSome`, `groupedOver_isSome`) are settled by Q2: those dispatchers take the header's
`USize` and the hypothesis goes. Its packages P1, P2, P7 edit `Kernel/Reduce.lean`, `Kernel/Scan.lean`, `c/scan.c`,
the files of two Q2 agents: run them before Q1 or after Q4, not between.

## 5. Optional hardening of the C stubs

Read: the stubs size an answer by `n * w` in `size_t` with no check (`c/structural.c:2379` `til`,
`c/elementwise.c:528` `ew_val`, `:2110` `ew_widen`), and `expand` sums its counts unchecked (`c/structural.c:1299`).
With `n : USize` a site that closes by the type can still be called at a count whose BYTE size wraps (`tilCol n` at
`n ≥ 2⁶¹`): the model says `n.toNat * 8` bytes, the C allocates the wrapped size and writes past it. This gap exists
today and the plan neither opens nor closes it. Closing it is one helper in `c/pass.h` used where a stub sizes its
answer, with `lean_internal_panic_out_of_memory` on overflow, as core does for a non-scalar capacity
(`lean.h:972`). It changes no answer and no Lean file.

## 6. What still cannot close

- **The laws of growing ops take the bound as a hypothesis.** `(raze t cs).1 = Σ counts`, the `toList` of a
  concatenation, and every law of `∪`, `≫`, `junc`, `cross` that goes through them hold in the logic only under
  `Σ counts < USize.size`, because past it the model's value is `blank`. The hypothesis propagates to each law that
  uses a growing op (`Code.lean`'s and `Alg.lean`'s `Laws` sections; `raze_len` `Code:276` is the first). Not counted:
  `Alg.lean`'s laws were not read. This is the main cost of the design and it lands in L3 and L4.
- **`sliceIds`, `setIds`.** The assert turns `rankSlices`' decline into a stop. For `sliceIds` the decline needs a sum
  of counts past `2⁶³`, which no process reaches. For `setIds` it is reached by starts that do not ascend, a
  precondition `setIds` does not take (`doc/leetq-arch-steps-245.md`, Step 4): today the reference answers there,
  after L3 the run stops naming `setIds`. Their laws take the kernel's guards as hypotheses.
- **`a.size < USize.size` for a Lean `Array` or `ByteArray`** is still not a theorem and no axiom is added. Every
  place that would need it is an assert (`col`, `genCol`, `longCol`).
- **That the C agrees with a `def` body** is trusted for every kernel, before and after; `#print axioms` cannot see it.
- **A failed assert under `#guard` or `#eval`** stops the `lean` process that runs it, so it stops `lake build`. A
  guard must not exercise a failing assert.
- **The byte-size wrap inside a stub** (section 5), unless the hardening is taken.

## 7. Open points

- `Enc.blank`: confirm no existing qlean constructor does this before adding it.
- Whether `Code.n` (`Code.lean:70`, not an `Arr`) becomes `USize` in L3 with the rest; the plan assumes yes.
- Whether qlean's evaluator, which already returns `Except`/`Option`, should raise q's own error at a growing verb
  instead of `need`. The plan uses `need` everywhere, as decided; this is the one place a second form was available.
- The section 5 hardening: take it with Q0 or leave it.
- `setIds` on non-ascending starts stops the run after L3; say if it must keep answering.
