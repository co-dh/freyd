import LeetQ.Rel.Algebra
import LeetQ.Rel.Blocks

/-! The machine check of `doc/rel-lang-design.md` §e and §g: the lifting of a relation formula to a family, and
    the blocks world and its search written with the note's formulas, one Lean definition per program line,
    transcribed by the rules of the design:

    - `≜` is a `def`; `−` is `\`; composition is `≫`; `R π₁`, `R π₂` are `outl R`, `outr R` (the same pairs).
    - A term whose source object has no universe (`𝒫(X×X)` and the products holding it) runs on the keys its
      left context composes into it: its Lean form is a function of that coreflexive, the DEMAND `D`. On `D`,
      `𝟙` is `D`, `∋` is `D ≫ mem D.val`, `⊤` is `D ≫ top D.val U`, `π₁`, `π₂` are `outl D`, `outr D`.
    - A definition whose parameter is declared `S : A ⟶ B` and is given a family `I ⟶ A×B` runs its body with
      the lifted operators (`lift…` below) on the keys in demand `D : I ⟶ I`; `∩`, `∪`, `−` lift to themselves.
    - `Λ(G) est(Q)` is `est Q G` (both are the `Q`-least value of each key of `G`).
    - `R⦇e,S⦈` is `R ≫ foldOn e.val S (ran R).val`, `S` in its demand form: the pairs each round meets.

    Not imported by any aggregator: a scratch module, checked by its own build. -/

namespace LeetQ.Rel.BlocksRel

open Alg QLean

/-! ### Objects and their universes -/

abbrev X : Obj := .long
/-- `N` is `long` as `X` is: `Obj` has no names, so the two universes are passed by hand, never by `Univ`. -/
abbrev N : Obj := .long
abbrev XX : Obj := .prod X X
/-- A state, the array `Λ` gives the set of its pairs: `𝒫(X×X)`, no universe. -/
abbrev St : Obj := .arr XX
/-- A candidate: a state and a move. -/
abbrev Cn : Obj := .prod St XX
/-- A state and a count. -/
abbrev SN : Obj := .prod St N

/-- `obj X = {A,B,C}`. -/
def xs := col [0, 1, 2]
local instance : Univ X := ⟨_, xs⟩
/-- `X×X`, the product universe. -/
local instance : Univ XX := ⟨_, (prod (𝟙 : Rel X X) 𝟙).key⟩
/-- `obj N = 0…6`: a shortest plan moves each block at most twice (to the table, then to its place), so no
    distance exceeds `2|X| = 6`. -/
def Nu := tilCol 7
/-- `succ` on `N`, partial at its top: `Alg.succ` maps `6` to `7`, which `𝟙` on `N` drops. -/
def succN : Rel N N := succ Nu ≫ idU Nu

/-- `π₁`, `π₂ : X×X ⟶ X`. -/
def π₁ : Rel XX X := outl (𝟙 : Rel XX XX)
def π₂ : Rel XX X := outr (𝟙 : Rel XX XX)

/-! ### The helper: a fold whose step runs on the pairs it meets -/

/-- `⦇e,S⦈` on the arrays `xa`, `S` in demand form: each round `S` runs on the pairs (element, value) it
    meets. `Alg.fold` takes `S` as a relation, which an object without a universe cannot give. -/
def foldOn {E V : Obj} {m n : Nat} (e : Vals V m) (S : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (xa : Vals (.arr E) n) : Rel (.arr E) V :=
  foldBy xa e fun el pend => pair el pend ≫ S (ran (pair el pend))

/-! ### The lifted operators: a family `I ⟶ A×B` holds at each key `i` a relation `A ⟶ B`, its fibre at `i`.
    Each row is built from `Alg` ops on the family as one relation; `∩`, `∪`, `−` need no row, as the fibre of
    `R ∩ S` at `i` is the meet of the fibres already. -/

section Lift

variable {I A B C : Obj}

/-- A closed `C : A ⟶ B` in a lifted position: `D⊤⟨𝟙,C⟩` (`⊤ : I ⟶ A` on `dom(C)`), the fibre `C` at every key
    in demand `D`. `𝟙`, `⊤`, `π₁`, `π₂` and every literal lift so. -/
def liftConst (D : Rel I I) (C : Rel A B) : Rel I (.prod A B) := D ≫ top D.val (dom C).val ≫ pair (dom C) C

/-- `RS` lifted: `⟨R,S⟩(𝟙 ∩ π₁π₂(π₂π₁)°)⟨π₁π₁,π₂π₂⟩`. `⟨R,S⟩` pairs each row of a key with each row of the same
    key; the coreflexive keeps the pairs whose middles agree. -/
def liftComp (R : Rel I (.prod A B)) (S : Rel I (.prod B C)) : Rel I (.prod A C) :=
  pair R S ≫ (ran (pair R S) ∩ outr (outl (ran (pair R S))) ≫ (outl (outr (ran (pair R S))))°) ≫
    pair (outl (outl (ran (pair R S)))) (outr (outr (ran (pair R S))))

/-- `R°` lifted: `R⟨π₂,π₁⟩`. -/
def liftConv (R : Rel I (.prod A B)) : Rel I (.prod B A) := R ≫ pair (outr (ran R)) (outl (ran R))

/-- `dom(R)` lifted: `R⟨π₁,π₁⟩`. -/
def liftDom (R : Rel I (.prod A B)) : Rel I (.prod A A) := R ≫ pair (outl (ran R)) (outl (ran R))

/-- `ran(R)` lifted: `R⟨π₂,π₂⟩`. -/
def liftRan (R : Rel I (.prod A B)) : Rel I (.prod B B) := R ≫ pair (outr (ran R)) (outr (ran R))

/-- `∼R` lifted: `D⊤ − R`, `⊤ : I ⟶ A×B` on the keys in demand `D` and the universes `Ua`, `Ub`. -/
def liftCompl {ma mb : Nat} (D : Rel I I) (Ua : Vals A ma) (Ub : Vals B mb) (R : Rel I (.prod A B)) :
    Rel I (.prod A B) :=
  liftConst D (top Ua Ub) \ R

/-- `R ⊑ S` lifted: `D − dom(R − S)`, the keys in demand at which the fibre of `R` is in that of `S`. -/
def liftLe (D : Rel I I) (R S : Rel I (.prod A B)) : Rel I I := D \ dom (R \ S)

end Lift

/-! ### The note's formulas, verbatim: `S : X ⟶ X`, run lifted on the keys in demand `D` of a family -/

variable {I : Obj}

/-- `R(S : X ⟶ X) ≜ S ∩ ∼𝟙`: `b` rests on another block. -/
def R (D : Rel I I) (S : Rel I XX) : Rel I XX := S ∩ liftCompl D xs xs (liftConst D (𝟙 : Rel X X))

/-- `M(S : X ⟶ X) ≜ ∼(R(S)°⊤ ∪ ⊤R(S))`: the moves allowed. -/
def M (D : Rel I I) (S : Rel I XX) : Rel I XX :=
  liftCompl D xs xs
    (liftComp (liftConv (R D S)) (liftConst D (⊤ : Rel X X)) ∪ liftComp (liftConst D (⊤ : Rel X X)) (R D S))

/-- `S'(S : X ⟶ X, p : X ⟶ X) ≜ (S ∩ ∼(p⊤)) ∪ p`: the state after the move `p`. -/
def S' (D : Rel I I) (S p : Rel I XX) : Rel I XX :=
  (S ∩ liftCompl D xs xs (liftComp p (liftConst D (⊤ : Rel X X)))) ∪ p

/-- `h(S : X ⟶ X) ≜ G ⊑ S`: `S` holds the goal; on a family, the keys whose state does. -/
def h (G : Rel X X) (D : Rel I I) (S : Rel I XX) : Rel I I := liftLe D (liftConst D G) S

/-! ### The search -/

/-- `c ≜ ⟨𝟙, M(∋)⟩ : St ⟶ St×(X×X)`, each state to itself and each move it allows: `M` lifted on the family `∋`. -/
def c (D : Rel St St) : Rel St Cn := pair D (M D (D ≫ mem D.val))

/-- `F ≜ S'(π₁∋, π₂) : St×(X×X) ⟶ X×X`, the pairs of the state a candidate leads to: `S'` lifted on two
    families of one index `St×(X×X)`. -/
def F (D : Rel Cn Cn) : Rel Cn XX := S' D (outl D ≫ mem (outl D).val) (outr D)

/-- `t ≜ cΛ(F) : St ⟶ St`, one move: `Λ` of the family `F`, one state per candidate. -/
def t (D : Rel St St) : Rel St St := c D ≫ Λ(F (ran (c D)))

/-- `L(D,B) ≜ ran(r⦇ran⟨D, D⊤{(0,0)}⟩, π₂ ∪ (π₂⟨π₁B, π₂ succ⟩)⦈)`: the step of the fold. -/
def step (B : Rel St St → Rel St St) (A : Rel (.prod N SN) (.prod N SN)) : Rel (.prod N SN) SN :=
  outr A ∪ outr A ≫ pair (outl (ran (outr A)) ≫ B (ran (outl (ran (outr A))))) (outr (ran (outr A)) ≫ succN)

variable (S₀ G : Rel X X)

/-- `s₀ ≜ ran(Λ(⊤⟨𝟙,S₀⟩))`, the start state. -/
def s₀ : Rel St St := ran Λ((⊤ : Rel X X) ≫ pair (𝟙 : Rel X X) S₀)

/-- `r ≜ Λ(s₀⊤(St,N))`, the array `0…6`: one round of a fold per number. -/
def r : Rel St (.arr N) := Λ(s₀ S₀ ≫ top (s₀ S₀).val Nu)

/-- `L(D,B)`: `(s, k)` when `s` is `k` steps of `B` from `D`, `k ≤ 6`. -/
def lay (D : Rel St St) (B : Rel St St → Rel St St) : Rel SN SN :=
  ran (r S₀ ≫ foldOn (ran (pair D (D ≫ top D.val Nu ≫ ofPairs [(0, 0)]))).val (step B) (ran (r S₀)).val)

/-- `Q ≜ ran(L(s₀,t)π₁)`, the reachable states. -/
def Q : Rel St St := ran (outl (lay S₀ (s₀ S₀) t))

/-- `H ≜ Qh(∋)`, the reachable states holding `G`: `h` lifted on the family `∋`, on the keys `Q`. -/
def H : Rel St St := h G (Q S₀) (Q S₀ ≫ mem (Q S₀).val)

/-- `C ≜ L(H, (Qt)°)`, each state with each length of a walk to a goal state. -/
def C : Rel SN SN := lay S₀ (H S₀ G) fun _ => (Q S₀ ≫ t (Q S₀))°

/-- `W ≜ (Cπ₁)°(Cπ₂) : St ⟶ N`. -/
def W : Rel St N := (outl (C S₀ G))° ≫ outr (C S₀ G)

/-- `δ ≜ Λ(W) est(≤)`, the distance to the goal. -/
def δ : Rel St N := est (leq Nu) (W S₀ G)

/-- `K ≜ Qc dom(Λ(F)δ succ ∩ (π₁δ))`, the candidates whose move takes the distance down by one. -/
def K : Rel St Cn :=
  c (Q S₀) ≫ dom (Λ(F (ran (c (Q S₀)))) ≫ δ S₀ G ≫ succN ∩ outl (ran (c (Q S₀))) ≫ δ S₀ G)

/-- `≼ ≜ π₁ < π₁° ∪ (π₁π₁° ∩ (π₂ ≤ π₂°))`, the moves in lexicographic order. -/
def «≼» : Rel XX XX := π₁ ≫ lt xs ≫ π₁° ∪ (π₁ ≫ π₁° ∩ π₂ ≫ leq xs ≫ π₂°)

/-- `σ ≜ Λ(Kπ₂) est(≼)`, the move chosen in each state. -/
def σ : Rel St XX := est «≼» (outr (K S₀ G))

/-- `ν ≜ ⟨dom(σ),σ⟩Λ(F)`, the state it leads to. -/
def ν : Rel St St := pair (dom (σ S₀ G)) (σ S₀ G) ≫ Λ(F (ran (pair (dom (σ S₀ G)) (σ S₀ G))))

/-- `Z ≜ L(s₀,ν)`, the chosen path's states with their step. -/
def Z : Rel SN SN := lay S₀ (s₀ S₀) fun _ => ν S₀ G

/-- `ζ ≜ (Zπ₂)°(Zπ₁) : N ⟶ St`, the `k`-th state. -/
def ζ : Rel N St := (outr (Z S₀ G))° ≫ outl (Z S₀ G)

/-- `plan ≜ ζσ : N ⟶ X×X`, the `k`-th move. -/
def plan : Rel N XX := ζ S₀ G ≫ σ S₀ G

section Checks

private def moves (S₀ G : Rel X X) : List (Int64 × Int64) :=
  ((plan S₀ G).nub.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

private def S₁ : Rel X X := Blocks.S₀
private def G₁ : Rel X X := Blocks.G
private def tbl : Rel X X := 𝟙
private def AB : Rel X X := ofPairs [(0, 1), (1, 0)]
/-- A on B on C: holds `G₁`. -/
private def tw : Rel X X := ofPairs [(0, 1), (1, 2), (2, 2)]

/-- `S` as the fibre at the key `k`. -/
private def st (k : Int64) (S : Rel X X) : Rel .long XX := top (A := .long) (col [k]) xs ≫ pair 𝟙 S

/-- The fibre of the family `F` at the key `k`, as a relation. -/
private def fib {A B : Obj} (k : Int64) (F : Rel .long (.prod A B)) : Rel A B :=
  (outl (ran (idU (t := .long) (col [k]) ≫ F)))° ≫ outr (ran (idU (t := .long) (col [k]) ≫ F))

/-- Three different states, and one move each, under the keys `0, 1, 2`. -/
private def Fs : Rel .long XX := st 0 S₁ ∪ st 1 tbl ∪ st 2 tw
private def Ps : Rel .long XX := st 0 (ofPairs [(2, 2)]) ∪ st 1 (ofPairs [(1, 2)]) ∪ st 2 (ofPairs [(0, 0)])
/-- The keys in demand: `3` too, where both families are empty, so `∼` holds `⊤` there. -/
private def Ds : Rel .long .long := idU (t := .long) (col [0, 1, 2, 3])
/-- The law holds at every key in demand. -/
private def every (p : Int64 → Bool) : Bool := p 0 && p 1 && p 2 && p 3

-- the law of each lifted row: its fibre at every key is the operator on the fibres there
#guard every fun k => fib k (liftComp Fs Ps) == fib k Fs ≫ fib k Ps
#guard every fun k => fib k (liftComp Ps Fs) == fib k Ps ≫ fib k Fs
#guard every fun k => fib k (liftConv Fs) == (fib k Fs)°
#guard every fun k => fib k (Fs ∩ Ps) == fib k Fs ∩ fib k Ps
#guard every fun k => fib k (Fs ∪ Ps) == fib k Fs ∪ fib k Ps
#guard every fun k => fib k (Fs \ Ps) == fib k Fs \ fib k Ps
#guard every fun k => fib k (liftCompl Ds xs xs Fs) == ∼(fib k Fs)
#guard every fun k => fib k (liftConst Ds (𝟙 : Rel X X)) == 𝟙
#guard every fun k => fib k (liftConst Ds (⊤ : Rel X X)) == ⊤
#guard every fun k => fib k (liftConst Ds G₁) == G₁
#guard every fun k => fib k (liftDom Fs) == dom (fib k Fs)
#guard every fun k => fib k (liftRan Fs) == ran (fib k Fs)
#guard every fun k => (idU (t := .long) (col [k]) ⊑ liftLe Ds (liftConst Ds G₁) Fs) == (G₁ ⊑ fib k Fs)
#guard every fun k => (idU (t := .long) (col [k]) ⊑ liftLe Ds Ps Fs) == (fib k Ps ⊑ fib k Fs)
-- the note's formulas, lifted: at every key, the formula on that key's state
#guard every fun k => fib k (R Ds Fs) == Blocks.R (fib k Fs)
#guard every fun k => fib k (M Ds Fs) == Blocks.M (fib k Fs)
#guard every fun k => fib k (S' Ds Fs Ps) == Blocks.move (fib k Fs) (fib k Ps)
#guard every fun k => (idU (t := .long) (col [k]) ⊑ h G₁ Ds Fs) == (G₁ ⊑ fib k Fs)
-- on a one-key family: the note's formulas on one state
#guard R (dom (Blocks.lvl S₁)) (Blocks.lvl S₁) == Blocks.lvl (Blocks.R S₁)
#guard M (dom (Blocks.lvl S₁)) (Blocks.lvl S₁) == Blocks.lvl (Blocks.M S₁)
#guard M (dom (Blocks.lvl tbl)) (Blocks.lvl tbl) == Blocks.lvl (Blocks.M tbl)
#guard S' (dom (Blocks.lvl S₁)) (Blocks.lvl S₁) (Blocks.lvl (ofPairs [(2, 2)])) ==
  Blocks.lvl (Blocks.move S₁ (ofPairs [(2, 2)]))
-- `∪` razes both parts' flat payloads and keeps every element: the payload under the states grows by a factor
-- per round, not by the rows (`L(s₀,𝟙)` at 7 rounds: 7 rows of 3 pairs over the payload below)
#guard (lay S₁ (s₀ S₁) fun D => D).n == 7
#guard (lay S₁ (s₀ S₁) fun D => D).val.1.1 == 2295
-- the 13 states of three blocks
#guard (Q S₁).n == 13
#guard (Q tbl).n == 13
-- MoveToTable C, Move B onto C, Move A onto B
#guard moves S₁ G₁ == [(2, 2), (1, 2), (0, 1)]
#guard moves S₁ G₁ == Blocks.plan
-- from all on the table: Move B onto C, Move A onto B
#guard moves tbl G₁ == [(1, 2), (0, 1)]
#guard moves tbl G₁ == Blocks.solve 𝟙 G₁
-- A on B and B on A: no state holds it
#guard moves tbl AB == []
#guard moves tbl AB == Blocks.solve 𝟙 AB

end Checks

end LeetQ.Rel.BlocksRel
