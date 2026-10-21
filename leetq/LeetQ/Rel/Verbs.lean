/-
  q's verbs, each one composite of the basis (`LeetQ.Rel.Basis`) on the span of `LeetQ.Rel.Container`,
  grouped as q's reference groups them.  A verb acts on the positions, so it serves a list, a dict, a
  table and a keyed table alike; an atom answer is the fibre at the point `0`.
-/
import LeetQ.Rel.Container
import LeetQ.Q.Agg

namespace LeetQ.Rel.Q

open Freyd.Alg.RelSet (RelRep RelTest)
open scoped Freyd.Alg.RelSet.RelRep
open LeetQ.Q.Agg (QF qfdiv)

variable {K V W J R S κ' : Type} [DecidableEq K] [DecidableEq V] [DecidableEq W] [DecidableEq J]
  [DecidableEq R] [DecidableEq S] [DecidableEq κ']

/-! ## Reindexing the positions -/

/-- `reverse C = (n-1-·) ≫ C`. -/
def reverse (C : Q K V) : Q K V := C.pull C.n (.ofFn (C.n - 1 - ·))
/-- `k#C`, cycling; a negative `k` takes from the end. -/
def take (k : Int) (C : Q K V) : Q K V := C.pull k.natAbs (.ofFn fun i => (((i : Int) + min k 0) % C.n).toNat)
/-- `k_C`. -/
def drop (k : Int) (C : Q K V) : Q K V := C.pull (C.n - k.natAbs) (.ofFn (· + k.toNat))
/-- `k sublist C`: `k#C` without cycling. -/
def sublist (k : Int) (C : Q K V) : Q K V :=
  C.pull (min k.natAbs C.n) (.ofFn (· + if k < 0 then C.n - min k.natAbs C.n else 0))
/-- `(s;l) sublist C`. -/
def sublist2 (s l : Nat) (C : Q K V) : Q K V := C.pull (min l (C.n - s)) (.ofFn (· + s))
/-- `k rotate C`. -/
def rotate (k : Int) (C : Q K V) : Q K V := C.pull C.n (.ofFn fun i => (((i : Int) + k) % C.n).toNat)
/-- `next C = shift 1 ≫ C`. -/
def next (C : Q K V) : Q K V := C.pull C.n (shift 1)
/-- `prev C = pred ≫ C`. -/
def prev (C : Q K V) : Q K V := C.pull C.n (shift (-1))
/-- `k xprev C`. -/
def xprev (k : Nat) (C : Q K V) : Q K V := C.pull C.n (shift (-k))
/-- `first C = est(<)(⊤) ≫ ν`, an atom. -/
def first (C : Q K V) : RelRep Nat V := (top C.n).first ≫ C.ν
/-- `last C = est(>)(⊤) ≫ ν`, an atom. -/
def last (C : Q K V) : RelRep Nat V := (top C.n).last ≫ C.ν
/-- `til n`. -/
def til (n : Nat) : Q Nat Nat := ⟨n, .pos rfl, idn n⟩
/-- `x,y` for lists and tables: `idn ≫ x ∪ shift(-n) ≫ y`. -/
def join (x y : Q Nat V) : Q Nat V := ⟨x.n + y.n, .pos rfl, (idn x.n ≫ x.ν).union (shift (-x.n) ≫ y.ν)⟩
/-- `raze xs = ⦇(), ,⦈`. -/
def raze (xs : List (Q Nat V)) : Q Nat V := xs.foldr join (list [])
/-- `x cross y = ⟨(·/m) ≫ x, (·%m) ≫ y⟩`. -/
def cross (x : Q Nat V) (y : Q Nat W) : Q Nat (V × W) :=
  ⟨x.n * y.n, .pos rfl, (.ofFn (· / y.n) ≫ x.ν).pair (.ofFn (· % y.n) ≫ y.ν)⟩
/-- `flip` of two columns: the table `⟨x, y⟩`. -/
def flip (x : Q Nat V) (y : Q Nat W) : Q Nat (V × W) := ⟨x.n, .pos rfl, x.ν.pair y.ν⟩

/-! ## Search -/

/-- `key C`: a dict's keys, a keyed table's key rows.  On a list q answers its type (`key 3 1 -> `long`), so
    there this is not q's `key` but `til count`. -/
def key (C : Q K V) : Q Nat K := ⟨C.n, .pos rfl, C.κ⟩
/-- `value C`. -/
def value (C : Q K V) : Q Nat V := ⟨C.n, .pos rfl, C.ν⟩

/-- The container as a relation key ↦ value: `first(κ°) ≫ ν`. -/
def get (C : Q K V) : RelRep K V := (cv C.n C.κ).first ≫ C.ν
/-- `C@ys`, `C ys`: `ys ≫ first(κ°) ≫ ν`. -/
def index (C : Q K V) (ys : Q J K) : Q J V := ys.put (ys.ν ≫ get C)
/-- `C?ys`, the key: `ys ≫ (first(ν°) else n) ≫ κ` — a list's index or its count, a dict's key or null. -/
def find (C : Q K V) (ys : Q J V) : Q J K := ys.put ((ys.ν ≫ (cv C.n C.ν).first).override (.ofFn fun _ => C.n) ≫ C.κ)
/-- `where C` of booleans: the keys at `(ν ≫ true?)`. -/
def whereB (C : Q K Bool) : Q Nat K := ofPt (top C.n ≫ (C.ν ≫ RelRep.corefl id).dom ≫ C.κ)
/-- `where C` of counts: each key `ν` times, `⟨id, ν ≫ >⟩ ≫ π₁ ≫ κ`. -/
def whereN (C : Q K Nat) : Q Nat K := ofPt (top C.n ≫ (idn C.n).pair (C.ν ≫ gt) ≫ .ofFn Prod.fst ≫ C.κ)
/-- `distinct C`: the values at the positions `first(ν°)` picks. -/
def distinct (C : Q K V) : Q Nat V := ofPt (top C.n ≫ (C.ν ≫ (cv C.n C.ν).first).inter (idn C.n) ≫ C.ν)
/-- `group C = Λ(ν° ≫ κ)` on the distinct values. -/
def group (C : Q K V) : Q V (List K) := ⟨(distinct C).n, .rel (distinct C).ν, (distinct C).ν ≫ Λ(cv C.n C.ν ≫ C.κ)⟩
/-- `x union y = distinct(x,y)`. -/
def union (x y : Q Nat V) : Q Nat V := distinct (join x y)
/-- `x inter y = ν ≫ (∈ ran y)?`. -/
def inter (x : Q K V) (y : Q J V) : Q Nat V := ofPt (top x.n ≫ x.ν ≫ (cv y.n y.ν).dom)
/-- `x except y = ν ≫ (∉ ran y)?`. -/
def except (x : Q K V) (y : Q J V) : Q Nat V := ofPt (top x.n ≫ x.ν ≫ ndom (cv y.n y.ν))
/-- `x in y`. -/
def in_ (x : Q K V) (y : Q J V) : Q K Bool :=
  x.put (x.ν ≫ ((cv y.n y.ν).dom ≫ .ofFn fun _ => true).override (.ofFn fun _ => false))
/-- The positions of `C` holding a value `L`-related to `v`: `⊤ ∩ (ν ≫ L)°`. -/
def below (L : RelTest V V) (C : Q K V) : RelRep V Nat := (top C.n).inter (C.ν.compT L).conv
/-- `x bin y`: the last position at or below, else `-1`. -/
def bin [LE V] [DecidableLE V] (x : Q K V) (y : Q J V) : Q J Int :=
  y.put ((y.ν ≫ (below (.test (decide <| · ≤ ·)) x).last ≫ .ofFn Int.ofNat).override (.ofFn fun _ => -1))
/-- `x binr y`: the first position at or above, else `n`. -/
def binr [LE V] [DecidableLE V] (x : Q K V) (y : Q J V) : Q J Nat :=
  y.put ((y.ν ≫ (below (.test (decide <| · ≥ ·)) x).first).override (.ofFn fun _ => x.n))
/-- `cs cut C = Λ(seg° ≫ ν)`, `seg` the last cut at or below a position. -/
def cut (cs : List Nat) (C : Q K V) : Q Nat (List V) :=
  ⟨cs.length, .pos rfl, Λ(cv C.n (below (.test (decide <| · ≤ ·)) (list cs)).last ≫ C.ν)⟩
/-- `within`: `ν ≫ (lo ≤ · ≤ hi)`. -/
def within [LE V] [DecidableLE V] (lo hi : V) (C : Q K V) : Q K Bool := C.put (C.ν ≫ .ofFn fun a => decide (lo ≤ a ∧ a ≤ hi))

/-! ## Sort -/

/-- `rank` in the order `lt`: `Λ(⊤ ∩ (⟨ν,id⟩ ≫ lex ≫ ⟨ν,id⟩°)) ≫ #`. -/
def rankBy (lt : V → V → Bool) (C : Q K V) : Q K Nat :=
  C.put (Λ((top C.n).inter (via (C.ν.pair (idn C.n)) (lex lt) (C.ν.pair (idn C.n)))) ≫ len)
/-- `rank`. -/
def rank [LT V] [DecidableLT V] (C : Q K V) : Q K Nat := rankBy (decide <| · < ·) C
/-- `iasc C = rank° ≫ κ`. -/
def iasc [LT V] [DecidableLT V] (C : Q K V) : Q Nat K := ⟨C.n, .pos rfl, cv C.n (rank C).ν ≫ C.κ⟩
/-- `idesc C = rank(>)° ≫ κ`. -/
def idesc [LT V] [DecidableLT V] (C : Q K V) : Q Nat K := ⟨C.n, .pos rfl, cv C.n (rankBy (decide <| · > ·) C).ν ≫ C.κ⟩
/-- `asc C`: the positions reindexed by `rank°`. -/
def asc [LT V] [DecidableLT V] (C : Q K V) : Q K V := C.pull C.n (cv C.n (rank C).ν)
/-- `desc C`. -/
def desc [LT V] [DecidableLT V] (C : Q K V) : Q K V := C.pull C.n (cv C.n (rankBy (decide <| · > ·) C).ν)
/-- `` `c xasc T ``. -/
def xasc [LT W] [DecidableLT W] (k : V → W) (T : Q K V) : Q K V := T.pull T.n (cv T.n (rank (T.put (T.ν ≫ .ofFn k))).ν)
/-- `` `c xdesc T ``. -/
def xdesc [LT W] [DecidableLT W] (k : V → W) (T : Q K V) : Q K V :=
  T.pull T.n (cv T.n (rankBy (decide <| · > ·) (T.put (T.ν ≫ .ofFn k))).ν)

/-! ## Each, neighbours, nulls -/

/-- `f each C = ν ≫ f`: a monadic map, a dict's values or a table's rows. -/
def each (f : V → W) (C : Q K V) : Q K W := C.put (C.ν ≫ .ofFn f)
/-- `x f' y = ⟨x, y⟩ ≫ f`. -/
def each2 (f : V → W → R) (x : Q K V) (y : Q J W) : Q K R := x.put (x.ν.pair y.ν ≫ .ofFn fun p => f p.1 p.2)
/-- `differ C = ⟨ν, pred ≫ ν⟩ ≫ (≠)`, true at the first. -/
def differ (C : Q K V) : Q K Bool :=
  C.put ((C.ν.pair (shift (-1) ≫ C.ν) ≫ .ofFn fun p => p.1 != p.2).override (.ofFn fun _ => true))
/-- `null C`. -/
def null (C : Q K V) : Q K Bool := C.put ((C.ν ≫ .ofFn fun _ => false).override (.ofFn fun _ => true))
/-- `fills C = last(≥ ≫ ν)`, run as one pass keeping the last value (`fills_spec`). -/
def fills (C : Q K V) : Q K V := C.put (scanR C.n none (fun _ a => some a) C.ν ≫ .enum Option.toList)

theorem fills_spec (C : Q K V) (i : Nat) (h : i < C.n) : (fills C).ν.app i = (ge ≫ C.ν).last.app i := by
  show (scanR C.n none (fun _ a => some a) C.ν ≫ .enum Option.toList).app i = _
  rw [RelRep.app_comp, app_scanR _ _ _ _ _ h, app_Λ, RelRep.last_eq, RelRep.app_enum]
  simp only [fold, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil, RelRep.app_enum,
    foldl_some, Option.or_none]

/-! ## Aggregates: an atom at the point -/

/-- `f/ C` seeded: `Λ(⊤ ≫ ν) ≫ ⦇z, f⦈`. -/
def over (f : W → V → W) (z : W) (C : Q K V) : RelRep Nat W := Λ(top C.n ≫ C.ν) ≫ fold z f
/-- `f/ C`: `Λ(⊤ ≫ ν) ≫ ⦇f⦈`. -/
def over1 (f : V → V → V) (C : Q K V) : RelRep Nat V := Λ(top C.n ≫ C.ν) ≫ fold1 f
/-- `count C = Λ(⊤) ≫ #`. -/
def count (C : Q K V) : RelRep Nat Nat := Λ(top C.n) ≫ len
/-- `sum = +/`. -/
def sum [Add V] [Zero V] (C : Q K V) : RelRep Nat V := over (· + ·) 0 C
/-- `prd = */`. -/
def prd [Mul V] [OfNat V 1] (C : Q K V) : RelRep Nat V := over (· * ·) 1 C
/-- `min C = first(est(≤)(⊤ ≫ ν))`. -/
def qmin [LE V] [DecidableLE V] (C : Q K V) : RelRep Nat V := ((top C.n ≫ C.ν).est (.test (decide <| · ≤ ·))).first
/-- `max C = first(est(≥)(⊤ ≫ ν))`. -/
def qmax [LE V] [DecidableLE V] (C : Q K V) : RelRep Nat V := ((top C.n ≫ C.ν).est (.test (decide <| · ≥ ·))).first
/-- `all = &/`. -/
def all (C : Q K Bool) : RelRep Nat Bool := over (· && ·) true C
/-- `any = |/`. -/
def any (C : Q K Bool) : RelRep Nat Bool := over (· || ·) false C
/-- `avg = sum % count`. -/
def avg (C : Q K Int) : RelRep Nat QF := (sum C).pair (count C) ≫ .ofFn fun p => qfdiv p.1 p.2
/-- `var = avg(x²) - avg(x)²`. -/
def var (C : Q K Int) : RelRep Nat QF := (avg (each (· ^ 2) C)).pair (avg C) ≫ .ofFn fun p => .of (p.1.f - p.2.f * p.2.f)
/-- `dev = sqrt var`. -/
def dev (C : Q K Int) : RelRep Nat QF := var C ≫ .ofFn fun v => .of v.f.sqrt
/-- `med`: the mean of the middle two positions of `asc`. -/
def med (C : Q K Int) : RelRep Nat QF :=
  Λ(.enum (fun _ => [(C.n - 1) / 2, C.n / 2]) ≫ (asc C).ν) ≫ fold 0 (· + ·) ≫ .ofFn (qfdiv · 2)
/-- `w wsum x = sum(w*x)`. -/
def wsum (w : Q K Int) (x : Q J Int) : RelRep Nat Int := sum (each2 (· * ·) w x)
/-- `w wavg x = wsum % sum w`. -/
def wavg (w : Q K Int) (x : Q J Int) : RelRep Nat QF := (wsum w x).pair (sum w) ≫ .ofFn fun p => qfdiv p.1 p.2
/-- `x cov y = avg(xy) - avg(x) avg(y)`. -/
def cov (x : Q K Int) (y : Q J Int) : RelRep Nat QF :=
  (avg (each2 (· * ·) x y)).pair ((avg x).pair (avg y)) ≫ .ofFn fun p => .of (p.1.f - p.2.1.f * p.2.2.f)
/-- `x cor y = cov % dev(x) dev(y)`. -/
def cor (x : Q K Int) (y : Q J Int) : RelRep Nat QF :=
  (cov x y).pair ((dev x).pair (dev y)) ≫ .ofFn fun p => .of (p.1.f / (p.2.1.f * p.2.2.f))

/-! ## Running and moving aggregates: one per position -/

/-- `f\ C` seeded: `Λ(≥ ≫ ν) ≫ ⦇z, f⦈`, run as one pass by the scan law (`scan_spec`). -/
def scan (f : W → V → W) (z : W) (C : Q K V) : Q K W := C.put (scanR C.n z f C.ν)

theorem scan_spec (f : W → V → W) (z : W) (C : Q K V) (i : Nat) (h : i < C.n) :
    (scan f z C).ν.app i = (Λ(ge ≫ C.ν) ≫ fold z f).app i := app_scanR _ _ _ _ _ h

/-- `f\ C`: `Λ(≥ ≫ ν) ≫ ⦇f⦈`, run as `scan` of `step1` from nothing (`scan1_spec`). -/
def scan1 (f : V → V → V) (C : Q K V) : Q K V := C.put (scanR C.n none (step1 f) C.ν ≫ .enum Option.toList)

theorem scan1_spec (f : V → V → V) (C : Q K V) (i : Nat) (h : i < C.n) :
    (scan1 f C).ν.app i = (Λ(ge ≫ C.ν) ≫ fold1 f).app i := by
  show (scanR C.n none (step1 f) C.ν ≫ .enum Option.toList).app i = _
  rw [RelRep.app_comp, app_scanR _ _ _ _ _ h, app_Λ, app_Λ, fold1_eq]
  simp only [fold, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil, RelRep.app_enum]
/-- `sums = +\`. -/
def sums [Add V] [Zero V] (C : Q K V) : Q K V := scan (· + ·) 0 C
/-- `prds = *\`. -/
def prds [Mul V] [OfNat V 1] (C : Q K V) : Q K V := scan (· * ·) 1 C
/-- `mins C = first(est(≤)(≥ ≫ ν))`. -/
def mins [LE V] [DecidableLE V] (C : Q K V) : Q K V := C.put ((ge ≫ C.ν).est (.test (decide <| · ≤ ·))).first
/-- `maxs C = first(est(≥)(≥ ≫ ν))`. -/
def maxs [LE V] [DecidableLE V] (C : Q K V) : Q K V := C.put ((ge ≫ C.ν).est (.test (decide <| · ≥ ·))).first
/-- `a ema C = Λ(≥ ≫ ν) ≫ ⦇(1-a)e + ax⦈`. -/
def ema (a : Float) (C : Q K QF) : Q K QF := scan1 (fun e x => .of (a * x.f + (1 - a) * e.f)) C
/-- `deltas C = ⟨ν, (pred ≫ ν) else 0⟩ ≫ (-)`. -/
def deltas [Sub V] [Zero V] (C : Q K V) : Q K V :=
  C.put (C.ν.pair ((shift (-1) ≫ C.ν).override (.ofFn fun _ => 0)) ≫ .ofFn fun p => p.1 - p.2)
/-- `ratios C = ⟨ν, (pred ≫ ν) else 1⟩ ≫ (%)`. -/
def ratios (C : Q K Int) : Q K QF :=
  C.put (C.ν.pair ((shift (-1) ≫ C.ν).override (.ofFn fun _ => 1)) ≫ .ofFn fun p => qfdiv p.1 p.2)
/-- `n msum C = Λ(W(n) ≫ ν) ≫ ⦇0,+⦈`. -/
def msum [Add V] [Zero V] (n : Nat) (C : Q K V) : Q K V := C.put (Λ(win n ≫ C.ν) ≫ fold 0 (· + ·))
/-- `n mcount C = Λ(W(n) ≫ ν) ≫ #`. -/
def mcount (n : Nat) (C : Q K V) : Q K Nat := C.put (Λ(win n ≫ C.ν) ≫ len)
/-- `n mavg C = msum % mcount`. -/
def mavg (n : Nat) (C : Q K Int) : Q K QF := C.put ((msum n C).ν.pair (mcount n C).ν ≫ .ofFn fun p => qfdiv p.1 p.2)
/-- `n mmin C = first(est(≤)(W(n) ≫ ν))`. -/
def mmin [LE V] [DecidableLE V] (n : Nat) (C : Q K V) : Q K V := C.put ((win n ≫ C.ν).est (.test (decide <| · ≤ ·))).first
/-- `n mmax C = first(est(≥)(W(n) ≫ ν))`. -/
def mmax [LE V] [DecidableLE V] (n : Nat) (C : Q K V) : Q K V := C.put ((win n ≫ C.ν).est (.test (decide <| · ≥ ·))).first

/-! ## Dicts and keyed tables -/

/-- `ks#C`: `ks!C@ks`. -/
def takeK (ks : Q J K) (C : Q K V) : Q K V := ⟨ks.n, .rel ks.ν, ks.ν ≫ get C⟩
/-- `ks _ C`: the positions with `κ ≫ (∉ ks)?`. -/
def dropK (ks : Q J K) (C : Q K V) : Q K V := C.sel (C.κ ≫ ndom (cv ks.n ks.ν))
/-- `d,e` on dicts: the keys of both, `e`'s value else `d`'s. -/
def upsert (d e : Q K V) : Q K V :=
  let ks := distinct (join (key d) (key e)); ⟨ks.n, .rel ks.ν, ks.ν ≫ (get e).override (get d)⟩
/-- `d f e` on dicts, a missing side `z`: `ks ≫ ⟨d else z, e else z⟩ ≫ f`. -/
def zipD (f : V → V → V) (z : V) (d e : Q K V) : Q K V :=
  let ks := distinct (join (key d) (key e))
  ⟨ks.n, .rel ks.ν, ks.ν ≫ ((get d).override (.ofFn fun _ => z)).pair ((get e).override (.ofFn fun _ => z)) ≫ .ofFn fun p => f p.1 p.2⟩

/-! ## qSQL -/

/-- `` `k xkey T ``: `κ = ν ≫ k`, `ν ≫ v`. -/
def xkey (k : V → K) (v : V → W) (T : Q J V) : Q K W := ⟨T.n, .rel (T.ν ≫ .ofFn k), T.ν ≫ .ofFn v⟩
/-- `select from T where p`. -/
def selectW (p : V → Bool) (T : Q K V) : Q K V := T.sel (T.ν ≫ RelRep.corefl p)
/-- `delete from T where p`. -/
def deleteW (p : V → Bool) (T : Q K V) : Q K V := T.sel (T.ν ≫ RelRep.corefl (!p ·))
/-- `exec f from T where p`. -/
def exec (f : V → W) (p : V → Bool) (T : Q K V) : Q Nat W := value (each f (selectW p T))
/-- `update f from T where p = ν ≫ (p? ≫ f ∪ ¬p?)`. -/
def update (p : V → Bool) (f : V → V) (T : Q K V) : Q K V :=
  T.put (T.ν ≫ (RelRep.corefl p ≫ .ofFn f).union (RelRep.corefl (!p ·)))
/-- `` `k xgroup T ``: `Λ((ν ≫ k)° ≫ ν ≫ v)` on the distinct keys. -/
def xgroup (k : V → κ') (v : V → W) (T : Q J V) : Q κ' (List W) :=
  let ks := distinct (each k T); ⟨ks.n, .rel ks.ν, ks.ν ≫ Λ(cv T.n (T.ν ≫ .ofFn k) ≫ T.ν ≫ .ofFn v)⟩
/-- `select agg v by k from T`: the groups at the sorted keys, each folded by `agg`. -/
def selby [LT κ'] [DecidableLT κ'] (agg : RelRep (List W) R) (k : V → κ') (v : V → W) (T : Q J V) : Q κ' R :=
  let ks := asc (distinct (each k T)); ⟨ks.n, .rel ks.ν, ks.ν ≫ Λ(cv T.n (T.ν ≫ .ofFn k) ≫ T.ν ≫ .ofFn v) ≫ agg⟩
/-- `ungroup G = ⟨κ, ν ≫ ∋⟩`. -/
def ungroup (G : Q K (List V)) : Q Nat (K × V) := ofPt (top G.n ≫ G.κ.pair (G.ν ≫ mem))

/-! ## Joins -/

/-- `T ij KT = ⟨id, ν ≫ k ≫ first(κ°) ≫ ν'⟩` where it is defined. -/
def ij (k : V → K) (T : Q J V) (KT : Q K W) : Q J (V × W) :=
  let J := T.ν.pair (T.ν ≫ .ofFn k ≫ get KT); (T.put J).sel J
/-- `T lj KT`: as `ij`, a missing match null. -/
def lj (k : V → K) (T : Q J V) (KT : Q K W) : Q J (V × Option W) :=
  T.put (T.ν.pair ((T.ν ≫ .ofFn k ≫ get KT ≫ .ofFn some).override (.ofFn fun _ => none)))
/-- `ej[k;T;U]`: every match, `⟨ν, ν ≫ k ≫ (ν' ≫ k')° ≫ ν'⟩`. -/
def ej (k : V → K) (k' : S → K) (w : S → W) (T : Q J V) (U : Q J S) : Q Nat (V × W) :=
  ofPt (top T.n ≫ T.ν.pair (T.ν ≫ .ofFn k ≫ cv U.n (U.ν ≫ .ofFn k') ≫ U.ν ≫ .ofFn w))
/-- `T pj KT`: `f` of the row and the match, else `0`. -/
def pj [Zero W] (k : V → K) (f : V → W → V) (T : Q J V) (KT : Q K W) : Q J V :=
  T.put (T.ν.pair ((T.ν ≫ .ofFn k ≫ get KT).override (.ofFn fun _ => 0)) ≫ .ofFn fun p => f p.1 p.2)
/-- `T uj U` of two tables: the rows of both, each mapped to the common columns. -/
def uj (f : V → W) (g : S → W) (T : Q Nat V) (U : Q Nat S) : Q Nat W := join (each f T) (each g U)
/-- The rows of `U` with the key of `T`'s row: `ν ≫ k ≫ (ν' ≫ k')°`. -/
def km (k : V → K) (k' : S → K) (T : Q J V) (U : Q J S) : RelRep Nat Nat := T.ν ≫ .ofFn k ≫ cv U.n (U.ν ≫ .ofFn k')
/-- `aj[k,t;T;U] = last(km ∩ (ν ≫ t ≫ ≥ ≫ (ν' ≫ t')°)) ≫ ν' ≫ w`, null where none. -/
def aj (k : V → K) (t : V → Int) (k' : S → K) (t' : S → Int) (w : S → W) (T : Q J V) (U : Q J S) : Q J (V × Option W) :=
  T.put (T.ν.pair ((((km k k' T U).inter (via (T.ν ≫ .ofFn t) (.test (decide <| · ≥ ·)) (U.ν ≫ .ofFn t'))).last ≫ U.ν ≫ .ofFn (some ∘ w)).override (.ofFn fun _ => none)))
/-- `wj1`: `Λ(km ∩ (t+lo ≤ t' ≤ t+hi)) ≫ ν' ≫ w ≫ ⦇0,+⦈`. -/
def wj1 [Add W] [Zero W] (lo hi : Int) (k : V → K) (t : V → Int) (k' : S → K) (t' : S → Int) (w : S → W) (T : Q J V) (U : Q J S) : Q J (V × W) :=
  T.put (T.ν.pair (Λ((km k k' T U).inter (via (T.ν ≫ .ofFn t) (.test fun a b => decide (a + lo ≤ b ∧ b ≤ a + hi)) (U.ν ≫ .ofFn t')) ≫ U.ν ≫ .ofFn w) ≫ fold 0 (· + ·)))
/-- `wj`: as `wj1`, with the row prevailing at `t+lo` for those at or before it. -/
def wj [Add W] [Zero W] (lo hi : Int) (k : V → K) (t : V → Int) (k' : S → K) (t' : S → Int) (w : S → W) (T : Q J V) (U : Q J S) : Q J (V × W) :=
  T.put (T.ν.pair (Λ((((km k k' T U).inter (via (T.ν ≫ .ofFn t) (.test fun a b => decide (b ≤ a + lo)) (U.ν ≫ .ofFn t'))).last.union ((km k k' T U).inter (via (T.ν ≫ .ofFn t) (.test fun a b => decide (a + lo < b ∧ b ≤ a + hi)) (U.ν ≫ .ofFn t')))) ≫ U.ν ≫ .ofFn w) ≫ fold 0 (· + ·)))

end LeetQ.Rel.Q
