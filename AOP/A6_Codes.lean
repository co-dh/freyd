/-
  The codes of the RelRep redesign and the algebra of their denotations.  A code `t : Ty` names a value
  type (k's type tag, lifted to an index); `El t` is the Lean type that reads a value of code `t`; a
  `Key s` says what a relation with keys of code `s` is defined on; `Fun s t = El s → List (El t)` is
  the denotation, order and multiplicity kept.  The relation laws (`comp`, `pair`, `Λ`, fold, hylo) are
  stated here once, on `Fun`, through `Fun.rel`; the executed family `Rel : Key s → Ty → Type`, its
  column leaves and its evaluator live outside AOP and rewrite against these laws.
-/
module

public import AOP.A6_FinRel
import AOP.A7_2_RelSet

@[expose] public section

namespace Freyd.Alg.RelSet

open Freyd DistributiveAllegory

/-! ## The codes -/

/-- The atomic codes `A` of a host language and the Lean type `El a` that reads each; `idx` is the
    integer code an interval relation and a list position are indexed by.  The atoms are a parameter, not
    an enum here, so the host's own list of atomic types is the only copy.  Intended q instance (leetq,
    `QAtomicType`): boolean ↦ Bool, guid ↦ 16 bytes, byte ↦ UInt8, short ↦ Int16, int ↦ Int32,
    long ↦ Int64 (= `idx`), real ↦ Float32, float ↦ Float, char ↦ UInt8, symbol ↦ String,
    timestamp/timespan ↦ Int64, month/date/minute/second/time ↦ Int32, datetime ↦ Float. -/
class Atoms (A : Type) where
  El : A → Type
  idx : A
  idx_el : El idx = Int64

/-- A value code over atoms `A`: an atom, a pair column, a segmented column (CSR), or a table row. -/
inductive Ty (A : Type) | atom (a : A)
  | prod (a b : Ty A) | seg (a : Ty A) | row (s : List (String × Ty A))
  deriving Repr, Inhabited

variable {A : Type}

-- `deriving DecidableEq` has no handler for the nested `row`, so the two deciders recurse together.
mutual
def Ty.decEq [DecidableEq A] : (a b : Ty A) → Decidable (a = b)
  | .atom a, .atom b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Ty.atom.inj e)
  | .prod a b, .prod c d => match Ty.decEq a c, Ty.decEq b d with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (Ty.prod.inj e).1
    | _, isFalse h => isFalse fun e => h (Ty.prod.inj e).2
  | .seg a, .seg b => match Ty.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Ty.seg.inj e)
  | .row s, .row r => match Ty.decEqRow s r with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (Ty.row.inj e)
  | .atom _, .prod .. | .atom _, .seg _ | .atom _, .row _ | .prod .., .atom _ | .prod .., .seg _
  | .prod .., .row _ | .seg _, .atom _ | .seg _, .prod .. | .seg _, .row _ | .row _, .atom _
  | .row _, .prod .. | .row _, .seg _ => isFalse nofun
def Ty.decEqRow [DecidableEq A] : (s r : List (String × Ty A)) → Decidable (s = r)
  | [], [] => isTrue rfl
  | (x, a) :: s, (y, b) :: r => if hx : x = y then match Ty.decEq a b, Ty.decEqRow s r with
      | isTrue h1, isTrue h2 => isTrue (hx ▸ h1 ▸ h2 ▸ rfl)
      | isFalse h, _ => isFalse fun e => h (Prod.mk.inj (List.cons.inj e).1).2
      | _, isFalse h => isFalse fun e => h (List.cons.inj e).2
    else isFalse fun e => hx (Prod.mk.inj (List.cons.inj e).1).1
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
end

/-- Codes are compared; `El` never is (it is not injective). -/
instance [DecidableEq A] : DecidableEq (Ty A) := Ty.decEq

variable [Atoms A]

/-- The integer code: `Atoms.idx` as a value code. -/
abbrev Ty.idx : Ty A := .atom Atoms.idx

mutual
/-- The Lean type that reads a value of code `t`. -/
def El : Ty A → Type
  | .atom a => Atoms.El a
  | .prod a b => El a × El b | .seg a => List (El a) | .row s => Row s
/-- A row of a table: one value per column, in column order. -/
def Row : List (String × Ty A) → Type
  | [] => Unit
  | (_, t) :: s => El t × Row s
end

/-- A value of the integer code read as an `Int64`, and back. -/
def El.toIdx (i : El (Ty.idx : Ty A)) : Int64 := cast (Atoms.idx_el (A := A)) i
def El.ofIdx (i : Int64) : El (Ty.idx : Ty A) := cast (Atoms.idx_el (A := A)).symm i

/-- What a relation is defined on, indexed by the key's code: every value (`all`: a function, a test, an
    interval, an atom), the positions of a list, a key column with repeats, or a sorted key column stored
    as offsets of its `g` distinct keys over `n` rows. -/
inductive Key : Ty A → Type
  | all {s : Ty A} : Key s
  | pos (n : Nat) : Key .idx
  | col {s : Ty A} (n : Nat) : Key s
  | off {s : Ty A} (g n : Nat) : Key s

/-- The rows a key index stores; an intensional `all` stores none. -/
def Key.rows {s : Ty A} : Key s → Nat
  | .all => 0 | .pos n => n | .col n => n | .off _ n => n

/-! ## The denotation -/

/-- A relation from code `s` to code `t`: each key's values, in order, with repeats. -/
def Fun (s t : Ty A) := El s → List (El t)

namespace Fun

variable {s t u v l e : Ty A}

/-- `f` as a relation: `x ↦ y` when `y ∈ f(x)`. -/
def rel (f : Fun s t) : (⟨El s⟩ : RelSet.{0}) ⟶ ⟨El t⟩ := fun x y => y ∈ f x

theorem rel_ext {f g : Fun s t} (h : ∀ x, f x = g x) : f.rel = g.rel := by
  rw [show f = g from funext h]

/-- `𝟙`: each value to itself. -/
def idn (s : Ty A) : Fun s s := fun x => [x]

/-- A total single-valued relation, the graph of `g`. -/
def ofFn (g : El s → El t) : Fun s t := fun x => [g x]

theorem rel_ofFn (g : El s → El t) : (ofFn g).rel = (graph g : (⟨El s⟩ : RelSet.{0}) ⟶ ⟨El t⟩) :=
  hom_ext fun x y => List.mem_singleton.trans (Iff.of_eq (graph_apply g x y).symm)

/-- `RS`: first `R`, then `S` on each of its values, in order. -/
def comp (R : Fun s t) (S : Fun t u) : Fun s u := fun x => (R x).flatMap S

theorem rel_comp (R : Fun s t) (S : Fun t u) : (comp R S).rel = R.rel ≫ S.rel :=
  hom_ext fun x z => by
    simp only [rel, comp, List.mem_flatMap, comp_apply]

theorem comp_assoc (R : Fun s t) (S : Fun t u) (T : Fun u v) : comp (comp R S) T = comp R (comp S T) :=
  funext fun _ => List.flatMap_assoc

theorem idn_comp (R : Fun s t) : comp (idn s) R = R := funext fun _ => by simp [comp, idn]

theorem comp_idn (R : Fun s t) : comp R (idn t) = R := funext fun x => by
  show (R x).flatMap (fun y => [y]) = R x
  induction R x <;> simp_all

/-- `⟨R,S⟩`: each value of `R`, in order, with each value of `S`. -/
def pair (R : Fun s t) (S : Fun s u) : Fun s (.prod t u) := fun x => (R x).flatMap fun a => (S x).map (a, ·)

theorem rel_pair (R : Fun s t) (S : Fun s u) : (pair R S).rel = rpair R.rel S.rel :=
  hom_ext fun x q => by
    show q ∈ (R x).flatMap (fun a => (S x).map (a, ·)) ↔ q.1 ∈ R x ∧ q.2 ∈ S x
    rw [← RelRep.mem_cross]; exact Iff.rfl

/-- `Λ(R)`: each key's values as one list, a value of the segmented code. -/
def lam (R : Fun s t) : Fun s (.seg t) := fun x => [R x]

theorem rel_lam (R : Fun s t) : (lam R).rel ≫ Λ (lmem (El t)) = Λ R.rel := by
  rw [Λ_eq_classifier, Λ_eq_classifier]
  exact hom_ext fun x G => ⟨fun ⟨_, hw, (hG : G = _)⟩ => by
      rw [List.mem_singleton.1 hw] at hG; exact hG,
    fun (hG : G = _) => ⟨R x, List.mem_singleton_self _, hG⟩⟩

open CL in
/-- `⦇[B,S]⦈`: the base's values at `wrap`, the step's over each value at `cons`.  A cons-list has no code,
    so the fold is a reading of `ConsList (El l) (El e)` rather than a `Fun`. -/
def fold (B : Fun l t) (S : Fun (.prod e t) t) : ConsList (El l) (El e) → List (El t) :=
  RelRep.foldList id B S

open CL in
theorem rel_fold (B : Fun l t) (S : Fun (.prod e t) t) :
    (fun x y => y ∈ fold B S x : (⟨ConsList (El l) (El e)⟩ : RelSet.{0}) ⟶ ⟨El t⟩)
      = ⦇(junc (sumCop (dL (El l)) ⟨El e × El t⟩) B.rel S.rel : Alg (F (El l) (El e)) ⟨El t⟩)⦈ := by
  have hj := RelRep.junc_apply B.rel S.rel
  rw [← cataR_eq_relCata]
  refine hom_ext fun x => ?_
  induction x with
  | wrap a => intro y; change _ ↔ cataFold _ (ConsList.wrap a) y; rw [cataFold_wrap]; exact (hj.1 a y).symm
  | cons a x ih =>
    intro y
    change _ ↔ cataFold _ (ConsList.cons a x) y
    rw [cataFold_cons]
    change y ∈ (fold B S x).flatMap (fun r => S (a, r)) ↔ _
    rw [List.mem_flatMap]
    exact ⟨fun ⟨r, hr, hy⟩ => ⟨r, (ih r).1 hr, (hj.2 (a, r) y).2 hy⟩,
      fun ⟨r, hr, hy⟩ => ⟨r, (ih r).2 hr, (hj.2 (a, r) y).1 hy⟩⟩

/-- The terminating hylomorphism on `Fun`: `step` iterated on a fuel of `μ(x) + 1`. -/
def hylo (μ : El s → Nat) (d : Fun s t) (step : Fun s t → Fun s t) : Fun s t := RelRep.hylo μ d step

/-- **The hylomorphism law** on `Fun`: if `step` computes `φ` under `rel`, `rel(hylo)` is a fixed point
    of `φ`. -/
theorem rel_hylo {μ : El s → Nat} {d : Fun s t} {step : Fun s t → Fun s t}
    {φ : ((⟨El s⟩ : RelSet.{0}) ⟶ ⟨El t⟩) → ((⟨El s⟩ : RelSet.{0}) ⟶ ⟨El t⟩)}
    (hρ : ∀ X, (step X).rel = φ X.rel) (hg : RelRep.Guarded μ step) :
    φ (hylo μ d step).rel = (hylo μ d step).rel :=
  RelRep.rel_hylo rel hρ hg

end Fun

/-! ## Interval relations -/

/-- Relations on the integer code kept symbolic until composed after a column. -/
inductive Ivl | idn | tot (n : Nat) | gt | ge | win (w : Nat) | shift (d : Int)

/-- `[0 … n)` as `Int64`s. -/
def upto (n : Nat) : List Int64 := (List.range n).map Int64.ofNat

/-- `idn i = [i]`; `tot n _ = [0…n)`; `gt c = [0…c)`; `ge c = [0…c]`; `win w i = [i-w+1…i]`;
    `shift d i = [i+d]`; computed on `Int64` and read back into the integer code. -/
def Ivl.den : Ivl → Fun (Ty.idx : Ty A) .idx
  | .idn => fun i => [i]
  | .tot n => fun _ => (upto n).map El.ofIdx
  | .gt => fun c => (upto c.toIdx.toInt.toNat).map El.ofIdx
  | .ge => fun c => (upto (c.toIdx.toInt + 1).toNat).map El.ofIdx
  | .win w => fun i => (List.range w).reverse.map fun j => El.ofIdx (i.toIdx - Int64.ofNat j)
  | .shift d => fun i => [El.ofIdx (i.toIdx + Int64.ofInt d)]

end Freyd.Alg.RelSet

end
