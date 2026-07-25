/-
  ShellCommands — the ten most-used data-processing shell commands, each modeled as a DISTINCT
  relation-algebra construct in the executable finite allegory `FinRel` (`rel.RelInterp`),
  grounded in real Linux syscalls.

  A case study (like `AOP.A6_1_Digits` / `rel.UnixPipe`), NOT a book section.  Where
  `UnixPipe` builds ONE pipeline `ls | grep | sort`, this file catalogues TEN commands and the
  point is that each lands on a GENUINELY DIFFERENT piece of the allegory vocabulary:

      ls      one-to-many relation (a non-`Map` atom)          `.atom`
      grep    coreflexive filter (`id ∩ ·`)                     `.meet (.id) _`   §2.121
      sort    power-transpose SET + `min`/`max` extremum        `AE` , `maxRelE`  §2.41 / B&dM 7.1
      find    reflexive-transitive closure                      `.join (.id) (reach …)`
      cat     union (a commutative monoid)                      `.join`           §2.21
      wc -l   catamorphism to ℕ (fold = length)                 `foldr`
      head-k  BOUNDED coreflexive                                `.meet (.id) _`
      uniq    adjacent-dedup cons-fold                           suffix-as-lookahead fold
      rm p    COMPLEMENT coreflexive (keep the non-matching)     `.meet (.id) _`
      mv      graph of a rename permutation (a `Map`)            `graphB`          §2.13

  HONEST SCOPE (what this is and is NOT).
    * SNAPSHOT, not streaming.  The algebra models one fixed directory listing of n = 5 entries;
      a real pipe is a stream.  We commit the 5-entry snapshot as the fixture.  Every PER-SNAPSHOT
      fact (`sort_head_bridge`, `mv_involution`, `uniq_idem`) is settled by kernel `decide` on the
      fixture (the power object `[Entry]` has only `2^5 = 32` rows).
    * UNIVERSAL laws (`grep_fusion`, `grep_rm_empty`, `cat_comm`, `cat_assoc`, `contains_le_find`)
      come from the ABSTRACT Chapter-2 allegory instances and hold for every atom — they are NOT
      re-proved by hand on the matrix.
    * The algebra never inspects a string or a byte.  Match (`isTxt` = "name ends .txt"), compare
      (`leSize` by byte size) and rename (`renamePerm`) are INJECTED as ground Boolean atoms; the
      terms only compose/converse/meet/join/divide them.  A `#eval` cross-checks the `isTxt` table
      against the real `String.endsWith ".txt"` so the fixture is not fiction — but no `String` op
      ever enters a `decide` or a theorem.
    * State-mutation `rm`/`mv` are modeled as RELATIONS on the entry SET of a snapshot: `rm p`
      keeps every entry NOT matching `p` (a complement coreflexive); `mv` renames entries by a
      permutation (the graph of `renamePerm`, a `Map`).  No file is deleted or moved; the relation
      is the post-state view of the snapshot.
    * `sort` has no total-order object inside `FinRel`, so the fully sorted SEQUENCE is not an `RE`
      term.  Sort has TWO sides: the SPEC side (`eval`, exponential) computes the survivor SET as a
      power-object point `Λ(ls ≫ grep)` and its size-least member (the sorted HEAD) with `max` of
      the size order (B&dM §7.1); the PROGRAM side (polynomial) is a filter+insertion-sort FOLD
      over a plain `List (Fin 5)`.  `sort_head_bridge` connects the two on the fixture.
    * The `main` glue is the "grounded in Linux syscalls" part: it `readDir`s a real directory,
      reads each entry's `metadata.byteSize` and `.isDir` (all Lean core, mathlib-free; mirrors
      `scripts/ExtractGraph.lean`), builds RUNTIME atoms over the live arrays, runs `eval`/the fold
      for every command, builds a runtime `contains` DAG from `.isDir` + a one-level `readDir` of
      subdirectories and runs `find` (the closure) on it, and prints the pipeline laws' Boolean on
      the LIVE snapshot.  No compile-time IO in any `def`, so the build is filesystem-independent.

  STRICTLY mathlib-free / Std-free; imports are `rel.RelInterp`/`S2_1`/`A4_2` + Lean core only.
  (`rel.UnixPipe` is deliberately NOT imported: it has its own root `main`.)  Sorry-free; every
  theorem's `#print axioms` ⊆ {propext, Quot.sound}.  Never `native_decide`.
-/
import rel.RelInterp
import Freyd.S2_01
import AOP.A4_2

set_option linter.unusedVariables false

namespace Freyd.Alg.FinRel.Shell

open Freyd

/-! ## The committed directory SNAPSHOT (fixture): 5 entries

  One directory (`Dir`) listing five entries (`Entry`).  Two of the five are text files, one is a
  subdirectory (`src`), and the `contains` DAG below makes a little tree so `find` has something to
  walk. -/

/-- The one directory (`ls`'s single input). -/
abbrev Dir : FinObj := ⟨1⟩
/-- The 5 directory entries. -/
abbrev Entry : FinObj := ⟨5⟩

/-- Hard-coded entry names, in directory order (entry 1 `src` is the subdirectory). -/
def nameOf : Fin 5 → String := fun i =>
  match i.val with
  | 0 => "readme.txt" | 1 => "src" | 2 => "notes.txt" | 3 => "a.log" | _ => "todo.txt"

/-- Hard-coded byte sizes (the `-l` key), all distinct. -/
def sizeOf : Fin 5 → Nat := fun i =>
  match i.val with
  | 0 => 100 | 1 => 4096 | 2 => 40 | 3 => 900 | _ => 175

/-- Hard-coded `grep`-match table: does the name end in `.txt`?  Injected as an atom — the algebra
    never runs a regex.  Kept in sync with `nameOf` by the `#eval` cross-check below. -/
def isTxt : Fin 5 → Bool := fun i =>
  match i.val with
  | 0 => true | 1 => false | 2 => true | 3 => false | _ => true

/-- The directory tree (for `find`): entry 0 (dir) contains 1,2; entry 1 (`src`) contains 3; entry
    2 contains 4.  A DAG; reachable from 0 is everything.  Injected as a ground atom. -/
def contains : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 => true | 0, 2 => true | 1, 3 => true | 2, 4 => true
  | _, _ => false

/-- Size comparison `e ≤ f` by byte size — the key `sort` orders on. -/
def leSize (e f : Fin 5) : Bool := decide (sizeOf e ≤ sizeOf f)

-- CROSS-CHECK the hard-coded `isTxt` table against the REAL `String.endsWith ".txt"` on the real
-- names, so the fixture is not fiction.  `String` ops live only here, never in a `decide`/theorem.
-- Prints `true`.
#eval (List.ofFn fun i : Fin 5 => isTxt i == (nameOf i).endsWith ".txt").all (fun b => b)

/-! ## 1. `ls` — a genuine one-to-many relation `Dir ⟶ Entry` (a non-`Map` atom)

  `ls` relates the one directory to ALL five entries: one input, five outputs, so this atom is a
  genuine NON-functional relation — the simplest allegory citizen, a bare `.atom`. -/

/-- The single directory contains all 5 entries. -/
def containsTop : Dir ⟶ Entry := fun _ _ => true
/-- **`ls`** as a term. -/
def lsE : RE Dir Entry := .atom containsTop

-- `ls` relates the directory to every entry (the column `0 ↦ *`).
#eval List.ofFn fun e : Fin 5 => eval lsE 0 e

/-! ## 2. `grep p` — a COREFLEXIVE filter `Entry ⟶ Entry` (§2.121)

  `grep p = id ∩ ⟨e ↦ (e = e ∧ p e)⟩`, the sub-diagonal keeping exactly the matching entries.
  Coreflexive (`⊑ id`); composing greps is intersecting predicates, by the abstract §2.121 law. -/

/-- The match-diagonal atom for predicate `p`: `pDiag p e f = (e = f) ∧ p e`. -/
def pDiag (p : Fin 5 → Bool) : Entry ⟶ Entry := fun e f => decide (e = f) && p e

/-- **`grep p`** as a term: `meet id (match-diagonal of p)`. -/
def grepE (p : Fin 5 → Bool) : RE Entry Entry := .meet (.id Entry) (.atom (pDiag p))

/-- **`grep p` evaluates to a COREFLEXIVE** (`⊑ id`): it is a filter, a sub-diagonal.  Immediate
    from `id ∩ _ ⊑ id`.  (`Coreflexive R` unfolds to `R ⊑ id`, so this IS `grep ⊑ id`.) -/
theorem grepE_coref (p : Fin 5 → Bool) : Coreflexive (eval (grepE p)) :=
  inter_lb_left (Cat.id Entry) (pDiag p)

/-- **grep FUSION**: `grep p ≫ grep q = grep (p ∧ q)`.  The composition collapses to an
    intersection by the ABSTRACT §2.121 law `coreflexive_comp_eq_inter` (a real reuse — the
    comp→inter step is the ALGEBRA, not a `decide`); only the residual predicate-lattice identity
    `p ∧ q` is pointwise Boolean. -/
theorem grep_fusion (p q : Fin 5 → Bool) :
    eval (RE.comp (grepE p) (grepE q)) = eval (grepE (fun x => p x && q x)) := by
  show eval (grepE p) ≫ eval (grepE q) = eval (grepE (fun x => p x && q x))
  rw [coreflexive_comp_eq_inter (grepE_coref p) (grepE_coref q)]
  funext e f
  simp only [grepE, eval, inter_apply, id_apply, pDiag]
  cases decide (e = f) <;> cases p e <;> cases q e <;> rfl

/-- **grep IDEMPOTENCE**: `grep p ≫ grep p = grep p` — a corollary of fusion (`p ∧ p = p`). -/
theorem grep_idem (p : Fin 5 → Bool) :
    eval (RE.comp (grepE p) (grepE p)) = eval (grepE p) := by
  have hpp : (fun x => p x && p x) = p := funext fun x => Bool.and_self (p x)
  rw [grep_fusion p p, hpp]

/-! ## 3. `sort` — power-transpose SET + `min`/`max` extremum (SPEC) and insertion-sort FOLD (PROGRAM)

  SPEC side (`eval`, exponential): the survivor SET as a power-object point `Λ(ls ≫ grep isTxt)`
  and its size-least member (the ascending sorted output's HEAD) via `max` of the size order — in
  B&dM's `min R = ∋ ∩ (∋°\R)` the selected element sits ABOVE the whole set, so the size-MINIMUM is
  `maxRelE leqE` (`max R = min R°`).  Runs by brute-forcing all `2^5 = 32` subset codes.

  PROGRAM side (polynomial): a fused filter+insertion-sort FOLD over a plain `List (Fin 5)` (NOT a
  `Prog.cata`, because `grep` can empty the list).  `sort_head_bridge` connects the two. -/

/-- The `-l` size key as a comparison relation on entries. -/
def leqE : RE Entry Entry := .atom leSize
/-- The survivor SET (txt files) as a power-object point `Λ(ls ≫ grep isTxt) : Dir ⟶ [Entry]`. -/
def pipeSet : RE Dir (pow Entry) := AE (RE.comp lsE (grepE isTxt))
/-- **`sort`, SPEC side**: the HEAD of the ascending sorted output — the smallest-size survivor. -/
def sortHeadE : RE Dir Entry := RE.comp pipeSet (maxRelE leqE)

/-- Insertion into an ascending (by `le`) list, generic in the order. -/
def linsertBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: linsertBy le x ys

/-- **`sort`, PROGRAM side**: fold keeping matches and insertion-sorting them by `le`. -/
def pipeFold {α : Type} (keep : α → Bool) (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc e => if keep e then linsertBy le e acc else acc) []

/-- The 5 entries in directory order. -/
def entriesList : List (Fin 5) := [0, 1, 2, 3, 4]

-- PROGRAM: sorted txt output `[notes.txt(40), readme.txt(100), todo.txt(175)] = [2,0,4]`.
#eval pipeFold isTxt leSize entriesList
-- SPEC: the head column over the 5 entries — `true` only at entry 2 (notes.txt, size 40).
#eval List.ofFn fun e : Fin 5 => eval sortHeadE 0 e

/-- **SORT SPEC↔PROGRAM HEAD BRIDGE** (`eval` vs the fold): the entry the exponential SPEC term
    `Λ(ls ≫ grep) ≫ max(≤)` (size-least survivor) relates `Dir` to IS the head the polynomial
    filter+insertion-sort program emits — checked column-wise by `decide` on the fixture. -/
theorem sort_head_bridge :
    (List.ofFn fun e : Fin 5 => eval sortHeadE 0 e)
      = (List.ofFn fun e : Fin 5 =>
          decide ((pipeFold isTxt leSize entriesList).head? = some e)) := by
  decide

/-! ## 4. `find` — the REFLEXIVE-TRANSITIVE CLOSURE of `contains`

  A recursive directory walk = a closure.  `reachE` is the transitive-closure recursion of
  `RelInterp.Demo207.reachE` (`reach 0 = R`, `reach (k+1) = R ∪ (R ≫ reach k)`), here generic in
  the object so the live `main` can reuse it; `findE` prefixes the identity to make it REFLEXIVE:
  `findE = id ∪ reach^{K}(contains)`, with fuel `K = 5 ≥ n`.  This is where the allegory genuinely
  earns its keep — the recursive walk is a term. -/

/-- Paths of length `1..k+1` as a term (`RelInterp.Demo207.reachE`, generic in the object). -/
def reachE {a : FinObj} (R : RE a a) : Nat → RE a a
  | 0 => R
  | k + 1 => .join R (.comp R (reachE R k))

/-- `contains` as a term. -/
def containsE : RE Entry Entry := .atom contains
/-- **`find`**: the reflexive-transitive closure of `contains` (fuel `5 ≥ 5`). -/
def findE : RE Entry Entry := .join (.id Entry) (reachE containsE 5)

-- The entries reachable from the root directory (entry 0): `true` at 0,1,2,3,4 — the whole tree.
#eval List.ofFn fun e : Fin 5 => eval findE 0 e

/-- Every relation sits inside its own transitive closure: `R ⊑ reach^{k}(R)`, by induction on the
    fuel (the closure always starts with a `∪ R`). -/
theorem reachE_ge {a : FinObj} (R : RE a a) : ∀ k, eval R ⊑ eval (reachE R k)
  | 0 => le_refl _
  | k + 1 => le_union_left (eval R) (eval (.comp R (reachE R k)))

/-- **`contains ⊑ find`**: every DIRECT child is reachable by `find`.  `contains ⊑ reach ⊑ id ∪
    reach = find`, from `reachE_ge` and `le_union_right` — no `decide`, pure abstract order. -/
theorem contains_le_find : eval containsE ⊑ eval findE :=
  le_trans (reachE_ge containsE 5)
    (le_union_right (Cat.id Entry) (eval (reachE containsE 5)))

/-- **`ls` is subsumed by `find`** (the well-typed reading of "ls ⊑ find": `lsE : Dir ⟶ Entry` and
    `findE : Entry ⟶ Entry` have different sources, so `lsE ⊑ findE` is a type error).  Since `find`
    is REFLEXIVE (`id ⊑ find`), every listed entry is `find`-reachable from the directory:
    `ls ⊑ ls ≫ find`. -/
theorem ls_le_ls_find : eval lsE ⊑ eval lsE ≫ eval findE := by
  have hid : Cat.id Entry ⊑ eval findE := le_union_left (Cat.id Entry) (eval (reachE containsE 5))
  have h := comp_mono_left (eval lsE) hid
  rw [Cat.comp_id] at h
  exact h

/-! ## 5. `cat` — union of file contents (a commutative monoid, §2.21), plus a list-append PROGRAM

  RELATIONAL model: a file's content is a one-to-many relation `One ⟶ Line` (the single point to
  the SET of its lines); `cat` is their UNION.  Commutativity and associativity of `cat` are FREE
  from the `DistributiveAllegory.union` laws — no re-proof.  (Union is idempotent, so this models
  the SET of lines, not the multiset; the sequence view is the program below.)

  PROGRAM model: `concatLines` appends the line-LISTS of a list of files — the sequence view, a
  different aspect (list append is not idempotent).  Both are honest, complementary models. -/

/-- The single point (`cat`'s one output stream). -/
abbrev One : FinObj := ⟨1⟩
/-- Six possible lines across the files. -/
abbrev Line : FinObj := ⟨6⟩

/-- Which lines each of 3 files holds (a fixed table): file 0 = {0,1}, file 1 = {2,3}, 2 = {1,4}. -/
def linesOf : Fin 3 → Fin 6 → Bool := fun f l =>
  match f.val, l.val with
  | 0, 0 => true | 0, 1 => true
  | 1, 2 => true | 1, 3 => true
  | 2, 1 => true | 2, 4 => true
  | _, _ => false

/-- A file's content as a one-to-many relation `One ⟶ Line`. -/
def fileLines (i : Fin 3) : RE One Line := .atom (fun _ l => linesOf i l)
/-- **`cat`** of two content relations: their UNION. -/
def catE (f g : RE One Line) : RE One Line := .join f g

/-- **`cat` COMMUTES** — free from `union_comm` (§2.21): `cat f g = cat g f`. -/
theorem cat_comm (f g : RE One Line) : eval (catE f g) = eval (catE g f) :=
  DistributiveAllegory.union_comm (eval f) (eval g)

/-- **`cat` is ASSOCIATIVE** — free from `union_assoc` (§2.21): `cat f (cat g h) = cat (cat f g) h`. -/
theorem cat_assoc (f g h : RE One Line) :
    eval (catE f (catE g h)) = eval (catE (catE f g) h) :=
  DistributiveAllegory.union_assoc (eval f) (eval g) (eval h)

/-- **`cat`, PROGRAM side**: concatenate the line-LISTS of a list of files (sequence view). -/
def concatLines {α : Type} (files : List (List α)) : List α := files.foldr (· ++ ·) []

-- `cat` of three files' line-lists, in order → one flat stream.
#eval concatLines [[0, 1], [2, 3], [1, 4]]
example : concatLines [[0, 1], [2, 3], [1, 4]] = [0, 1, 2, 3, 1, 4] := by decide

/-! ## 6. `wc -l` — a CATAMORPHISM to ℕ (the fold = length)

  `wc -l` is `foldr (fun _ n => n+1) 0`, the length catamorphism.  Its interaction with `grep` is
  the payoff: filtering can only shrink the count. -/

/-- **`wc -l`** as a catamorphism (fold) to ℕ. -/
def wcFold {α : Type} : List α → Nat := List.foldr (fun _ n => n + 1) 0

/-- **`wc (grep xs) ≤ wc xs`**: the line count is MONOTONE under `grep` — a filter never adds
    lines.  By induction on the list (the grep/wc interaction). -/
theorem wc_filter_le {α : Type} (p : α → Bool) :
    ∀ xs : List α, wcFold (xs.filter p) ≤ wcFold xs
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := wc_filter_le p xs
    show wcFold ((x :: xs).filter p) ≤ wcFold (x :: xs)
    cases hp : p x
    · have he : (x :: xs).filter p = xs.filter p := by simp [List.filter, hp]
      rw [he]
      show wcFold (xs.filter p) ≤ wcFold xs + 1
      omega
    · have he : (x :: xs).filter p = x :: xs.filter p := by simp [List.filter, hp]
      rw [he]
      show wcFold (xs.filter p) + 1 ≤ wcFold xs + 1
      omega

-- `wc -l` of the txt survivors vs the whole listing: 3 ≤ 5.
#eval (wcFold ((entriesList).filter isTxt), wcFold entriesList)

/-! ## 7. `head -k` — a BOUNDED COREFLEXIVE `Entry ⟶ Entry`

  `head -k = id ∩ ⟨e ↦ (e = e ∧ e < k)⟩`: like `grep`, a sub-diagonal, but the predicate is the
  POSITION bound `e < k`, keeping the first `k` entries.  Coreflexive. -/

/-- The position-bound diagonal atom: keep entry `e` iff `e < k`. -/
def boundDiag (k : Nat) : Entry ⟶ Entry := fun e f => decide (e = f) && decide (e.val < k)
/-- **`head -k`** as a term. -/
def headKE (k : Nat) : RE Entry Entry := .meet (.id Entry) (.atom (boundDiag k))

/-- **`head -k` is COREFLEXIVE** (`⊑ id`): it only keeps a prefix, never adds.  `Coreflexive R`
    unfolds to `R ⊑ id`, so this IS `head ⊑ id`. -/
theorem headKE_coref (k : Nat) : Coreflexive (eval (headKE k)) :=
  inter_lb_left (Cat.id Entry) (boundDiag k)

-- `head -3` keeps entries 0,1,2 (the diagonal column is `true` there, `false` at 3,4).
#eval List.ofFn fun e : Fin 5 => eval (headKE 3) e e

/-! ## 8. `uniq` — adjacent-dedup cons-fold (suffix-as-lookahead, the `L26` pattern)

  `uniq` drops each element equal to the PREVIOUS surviving one.  A plain cons-fold cannot peek at
  the neighbour — but folding from the RIGHT, the folded suffix's own head IS the lookahead
  (`leet.L26_derived`'s trick).  A polynomial `List` fold, run applicatively (`evalP`-style). -/

/-- Cons a new element onto the deduped suffix, comparing against the suffix's own head. -/
def uniqStep {α : Type} [DecidableEq α] (x : α) (acc : List α) : List α :=
  match acc.head? with
  | some h => if x = h then acc else x :: acc
  | none   => x :: acc

/-- **`uniq`** as an adjacent-dedup cons-fold. -/
def uniqFold {α : Type} [DecidableEq α] (xs : List α) : List α := xs.foldr uniqStep []

-- Adjacent dups collapse: `[0,0,1,2,2,2,4] → [0,1,2,4]`.
#eval uniqFold ([0, 0, 1, 2, 2, 2, 4] : List (Fin 5))

/-- **`uniq` is IDEMPOTENT on the fixture** (`uniq (uniq xs) = uniq xs`): a second pass finds no
    adjacent duplicates left.  `decide` on representative fixture lists. -/
theorem uniq_idem :
    uniqFold (uniqFold ([0, 0, 1, 2, 2, 2, 4] : List (Fin 5)))
      = uniqFold ([0, 0, 1, 2, 2, 2, 4] : List (Fin 5))
    ∧ uniqFold (uniqFold ([3, 3, 3, 1, 1, 0] : List (Fin 5)))
      = uniqFold ([3, 3, 3, 1, 1, 0] : List (Fin 5)) := by
  decide

/-! ## 9. `rm p` — a COMPLEMENT COREFLEXIVE (keep every entry NOT matching `p`)

  `rm p = id ∩ ⟨e ↦ (e = e ∧ ¬p e)⟩`: the mutation "delete the matching files" is the post-state
  RELATION on the snapshot's entry SET — keep the complement.  Also coreflexive, but the DUAL
  predicate of `grep`, so `grep p` then `rm p` deletes exactly what it kept: the EMPTY relation. -/

/-- The complement match-diagonal: keep `e` iff it does NOT match `p`. -/
def notDiag (p : Fin 5 → Bool) : Entry ⟶ Entry := fun e f => decide (e = f) && !p e
/-- **`rm p`** as a term: keep everything not matching `p`. -/
def rmE (p : Fin 5 → Bool) : RE Entry Entry := .meet (.id Entry) (.atom (notDiag p))

/-- **`rm p` is COREFLEXIVE** (`⊑ id`): it only removes.  `Coreflexive R` unfolds to `R ⊑ id`, so
    this IS `rm ⊑ id`. -/
theorem rmE_coref (p : Fin 5 → Bool) : Coreflexive (eval (rmE p)) :=
  inter_lb_left (Cat.id Entry) (notDiag p)

/-- **`grep p ≫ rm p = ∅`**: grep-then-rm-same deletes exactly the survivors — the empty relation.
    The composition collapses to an intersection by the ABSTRACT §2.121 law
    `coreflexive_comp_eq_inter`; the residual `p e ∧ ¬p e = false` is pointwise Boolean. -/
theorem grep_rm_empty (p : Fin 5 → Bool) :
    eval (RE.comp (grepE p) (rmE p)) = eval (RE.bot Entry Entry) := by
  show eval (grepE p) ≫ eval (rmE p) = 𝟘
  rw [coreflexive_comp_eq_inter (grepE_coref p) (rmE_coref p)]
  funext e f
  simp only [grepE, rmE, eval, inter_apply, id_apply, pDiag, notDiag]
  cases decide (e = f) <;> cases p e <;> rfl

/-! ## 10. `mv` — the graph of a rename PERMUTATION (a `Map`, §2.13)

  `mv` renames entries by a bijection `renamePerm` (here the involution swapping `0↔1`, `2↔3`,
  fixing `4`).  Its relation is the GRAPH of that function — single-valued and total, a `Map`
  (`graphB_map`).  Since `renamePerm` is a permutation, `mv ≫ mv° = id` (rename then un-rename). -/

/-- The rename bijection: an involution (swap `0↔1`, `2↔3`, fix `4`). -/
def renamePerm : Fin 5 → Fin 5 := fun i =>
  match i.val with
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | _ => 4
/-- **`mv`** as a term: the graph of the rename permutation. -/
def mvE : RE Entry Entry := .atom (graphB renamePerm)

/-- **`mv` is a `Map`** (single-valued + total): it is the graph of a function (`graphB_map`). -/
theorem mv_map : Map (eval mvE) := graphB_map renamePerm

/-- **`mv ≫ mv⁻¹ = id`**: renaming then un-renaming (`mv°`, the converse) is the identity, because
    `renamePerm` is a permutation.  Checked as a `5×5` Boolean matrix by `decide` on the fixture. -/
theorem mv_involution :
    (List.ofFn fun e : Fin 5 => List.ofFn fun f : Fin 5 => eval (RE.comp mvE (RE.conv mvE)) e f)
      = (List.ofFn fun e : Fin 5 => List.ofFn fun f : Fin 5 => eval (RE.id Entry) e f) := by
  decide

end Freyd.Alg.FinRel.Shell

open Freyd.Alg.FinRel Freyd.Alg.FinRel.Shell

/-! ## Live kernel glue — real `readDir` + `metadata.byteSize` + `.isDir` (the Linux-syscall grounding)

  `main` reads a real directory, reads each entry's byte size and `.isDir` via
  `System.FilePath.metadata` (Lean core, mathlib-free — mirrors `scripts/ExtractGraph.lean`'s
  `readDir` idiom), builds RUNTIME atoms over the live arrays, and runs EVERY command on the live
  snapshot: `ls -l`, `grep .txt`, `wc -l`, `head -3`, `uniq`, `sort` (the fold), and `find` (the
  closure `reachE`, on a `contains` DAG built from `.isDir` + a one-level `readDir` of subdirs).  It
  then prints the pipeline laws' Boolean (grep-fusion, rm-removes-only) computed by RUNNING `eval`
  on the live matrices.  Self-contained: no compile-time IO, so the build is filesystem-independent. -/

/-- Flatten a `Fin k` Boolean matrix so two of them can be compared with `==` at runtime. -/
def matToList (k : Nat) (R : Fin k → Fin k → Bool) : List (List Bool) :=
  List.ofFn fun i : Fin k => List.ofFn fun j : Fin k => R i j

/-- Runtime "row `R` only removes": every column in `R` is in `S` (`R ⊑ S` as a live Bool). -/
def rowLe (k : Nat) (R S : Fin k → Bool) : Bool :=
  (List.ofFn fun j : Fin k => !(R j) || S j).all id

def main : IO Unit := do
  let dir : System.FilePath := "."
  let dents ← dir.readDir
  let names : Array String := dents.map (·.fileName)
  let paths : Array System.FilePath := dents.map (·.path)
  let n := dents.size
  let mut sizes : Array Nat := #[]
  let mut isDirs : Array Bool := #[]
  for d in dents do
    let md ← d.path.metadata
    let isd ← d.path.isDir
    sizes := sizes.push md.byteSize.toNat
    isDirs := isDirs.push isd

  IO.println s!"# ls -l  ({n} entries in {dir})"
  for i in List.range n do
    let tag := if isDirs[i]! then "d" else "-"
    let txt := if (names[i]!).endsWith ".txt" then "txt" else "   "
    IO.println s!"  {tag}  {sizes[i]!}\t{txt}\t{names[i]!}"

  -- Runtime predicates over the live snapshot (real regex + real byte size).
  let liveList : List (Fin n) := List.ofFn (fun i => i)
  let keepTxt : Fin n → Bool := fun i => (names[i.val]!).endsWith ".txt"
  let leLive  : Fin n → Fin n → Bool := fun i j => decide (sizes[i.val]! ≤ sizes[j.val]!)

  -- 2. grep .txt
  let survivors := liveList.filter keepTxt
  IO.println s!"\n# grep .txt   ({survivors.length} survivors)"
  for e in survivors do IO.println s!"  {names[e.val]!}"

  -- 6. wc -l  (count of all entries, and of txt survivors)
  IO.println s!"\n# wc -l : {wcFold liveList} total, {wcFold survivors} match .txt"

  -- 7. head -3
  IO.println s!"\n# head -3"
  for e in liveList.take 3 do IO.println s!"  {names[e.val]!}"

  -- 3. sort (the polynomial fold: filter .txt + insertion-sort by size)
  let sortedTxt := pipeFold keepTxt leLive liveList
  IO.println s!"\n# ls | grep .txt | sort   (evalP-style fold, by size)"
  for e in sortedTxt do IO.println s!"  {sizes[e.val]!}\t{names[e.val]!}"

  -- 8. uniq  (sort all sizes ascending, then collapse adjacent equal sizes = `sort | uniq`)
  let sizesSorted := (sizes.toList).foldr (linsertBy (fun a b => decide (a ≤ b))) []
  let sizesUniq := uniqFold sizesSorted
  IO.println s!"\n# sort | uniq  (byte sizes):  {sizesSorted}  ->  {sizesUniq}"

  -- 4. find  (build the `contains` DAG from `.isDir` + a one-level readDir of each subdir)
  let mut edges : List (Nat × Nat) := []
  for i in List.range n do
    if isDirs[i]! then
      let subs ← (paths[i]!).readDir
      for s in subs do
        -- a child of subdir `i` that also appears at top level induces an edge `i → j`
        for j in List.range n do
          if names[j]! == s.fileName then edges := (i, j) :: edges
  let contRT : Fin n → Fin n → Bool := fun i j => edges.any (fun e => e.1 == i.val && e.2 == j.val)
  let ErtObj : FinObj := ⟨n⟩
  -- reflexive-transitive closure with fuel n, as a term run by `eval`
  let closureRT : RE ErtObj ErtObj := .join (.id ErtObj) (reachE (.atom contRT) n)
  IO.println s!"\n# find  (reflexive-transitive closure of the .isDir tree, {edges.length} edges)"
  for i in (List.ofFn (fun e : Fin n => e)) do
    if isDirs[i.val]! then
      let reach := (List.ofFn (fun e : Fin n => e)).filter
        (fun e => e.val != i.val && eval closureRT i e)
      IO.println s!"  {names[i.val]!}/ reaches: {reach.map (fun e => names[e.val]!)}"

  -- Pipeline LAWS on the LIVE snapshot (runtime Booleans, computed by RUNNING `eval`).
  let bigCap : Fin n → Bool := fun i => decide (sizes[i.val]! ≥ 100)
  let grepRT : (Fin n → Bool) → RE ErtObj ErtObj :=
    fun p => .meet (.id ErtObj) (.atom (fun e f => decide (e = f) && p e))
  let rmRT   : (Fin n → Bool) → RE ErtObj ErtObj :=
    fun p => .meet (.id ErtObj) (.atom (fun e f => decide (e = f) && !p e))
  let lsRT   : RE (⟨1⟩ : FinObj) ErtObj := .atom (fun _ _ => true)
  -- grep-fusion: run `eval` of the COMPOSED greps vs `eval` of the single fused grep.
  let grepFuse :=
    matToList n (eval (RE.comp (grepRT keepTxt) (grepRT bigCap)))
      == matToList n (eval (grepRT (fun e => keepTxt e && bigCap e)))
  -- rm removes only: `ls ≫ rm ⊑ ls` on the live row (the well-typed "rm ⊑ ls").
  let rmRemoves :=
    rowLe n (eval (RE.comp lsRT (rmRT keepTxt)) 0) (eval lsRT 0)
  IO.println s!"\n# pipeline laws on THIS directory:"
  IO.println s!"  grep .txt ≫ grep ≥100  ==  grep (.txt ∧ ≥100)   : {grepFuse}"
  IO.println s!"  ls ≫ rm .txt  ⊑  ls   (rm only removes)          : {rmRemoves}"
