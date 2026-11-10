import LeetQ.Rel.Algebra
import LeetQ.Rel.Blocks

/-! The machine check of `doc/rel-lang-design.md` §g: the blocks world and its search as the Rel language
    writes them, one Lean definition per program line, transcribed by the rules of the design:

    - `≜ ` is a `def`; `−` is `\`; composition is `≫`; `R π₁`, `R π₂` are `outl R`, `outr R` (the same pairs).
    - A term whose source object has no universe (`𝒫(X×X)` and the products holding it) runs on the keys its
      left context composes into it: its Lean form is a function of that coreflexive, the DEMAND `D`. On `D`,
      `𝟙` is `D`, `∋` is `D ≫ mem D.val`, `⊤` is `D ≫ top D.val U`, `π₁`, `π₂` are `outl D`, `outr D`.
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
/-- `obj N = 0…27`, fixed before the search and not read off it. -/
def Nu := tilCol 28
/-- `succ` on `N`, partial at its top: `27` goes to nothing. -/
def succN : Rel N N := succ Nu

/-- `π₁`, `π₂ : X×X ⟶ X`. -/
def π₁ : Rel XX X := outl (𝟙 : Rel XX XX)
def π₂ : Rel XX X := outr (𝟙 : Rel XX XX)

/-! ### The helper `μ` -/

/-- `μY : φ(Y)` from `𝟘` until a round changes nothing; `bound` is never reached on a finite hom-set. -/
def mu {A B : Obj} (bound : Nat) (φ : Rel A B → Rel A B) : Rel A B :=
  (iter bound (fun p => p.1 == p.2) (fun p => (p.2, φ p.2)) (zero, φ zero)).2

/-- `S R*` as `μY : S ∪ Y R` (`comp_star_eq_mu`, AOP/A6_7.lean:264), `R` in demand form. -/
def star {A B : Obj} (bound : Nat) (S : Rel A B) (R : Rel B B → Rel B B) : Rel A B :=
  mu bound fun Y => S ∪ Y ≫ R (ran Y)

/-- More rounds than any `μ` below takes: `2⁹` sets of pairs times `7` counts. -/
def cap : Nat := 2 ^ 9 * 7

/-! ### The note's formulas, per key: `S : I ⟶ X×X` holds one state per key -/

variable {I : Obj}

/-- `R(S) ≜ S ran⟨𝟙,∼𝟙⟩`: the note's `S ∩ ∼𝟙`, per key. -/
def R (S : Rel I XX) : Rel I XX := S ≫ ran (pair (𝟙 : Rel X X) ∼𝟙)

/-- `M(S) ≜ Sπ₁⊤ − (R(S)π₂(π₁° ∪ π₂°))`: the note's `∼(R°⊤ ∪ ⊤R)`, per key. -/
def M (S : Rel I XX) : Rel I XX := S ≫ π₁ ≫ ⊤ \ R S ≫ π₂ ≫ (π₁° ∪ π₂°)

/-- `S'(S,p) ≜ S − (pπ₁π₁°) ∪ p`: the note's `(S ∩ ∼(p⊤)) ∪ p`, per key. -/
def S' (S p : Rel I XX) : Rel I XX := S \ p ≫ π₁ ≫ π₁° ∪ p

/-! ### The search -/

/-- `c ≜ ⟨𝟙, M(∋)⟩ : St ⟶ St×(X×X)`, each state to itself and each move it allows. -/
def c (D : Rel St St) : Rel St Cn := pair D (M (D ≫ mem D.val))

/-- `F ≜ S'(π₁∋, π₂) : St×(X×X) ⟶ X×X`, the pairs of the state a candidate leads to. -/
def F (D : Rel Cn Cn) : Rel Cn XX := S' (outl D ≫ mem (outl D).val) (outr D)

/-- `T ≜ cΛ(F) : St ⟶ St`, one move. -/
def T (D : Rel St St) : Rel St St := c D ≫ Λ(F (ran (c D)))

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

/-- `Q ≜ ran(L(s₀,T)π₁)`, the reachable states. -/
def Q : Rel St St := ran (outl (lay S₀ (s₀ S₀) T))

/-- `g ≜ ran⟨𝟙,G⟩`, the goal's pairs. -/
def g : Rel XX XX := ran (pair (𝟙 : Rel X X) G)

/-- `H ≜ Q − dom(Q⊤g − (Q∋))`, the reachable states holding `G`. -/
def H : Rel St St := Q S₀ \ dom (Q S₀ ≫ top (Q S₀).val Univ.xs ≫ g G \ Q S₀ ≫ mem (Q S₀).val)

/-- `C ≜ L(H, (QT)°)`, each state with each length of a walk to a goal state. -/
def C : Rel SN SN := lay S₀ (H S₀ G) fun _ => (Q S₀ ≫ T (Q S₀))°

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

/-! ### The same three iterations with `μ` and `*`, for comparison -/

namespace Mu

/-- `Q ≜ ran(s₀T*)`. -/
def Q : Rel St St := ran (star cap (s₀ S₀) T)

/-- `W ≜ μY : H⊤{(0,0)} ∪ (QTY succ)`. -/
def W : Rel St N :=
  mu cap fun Y => H S₀ G ≫ top (H S₀ G).val Nu ≫ ofPairs [(0, 0)] ∪ Q S₀ ≫ T (Q S₀) ≫ Y ≫ succN

/-- `ζ ≜ μY : (s₀⊤{(0,0)})° ∪ (succ°Yν)`. -/
def ζ : Rel N St :=
  mu cap fun Y => (s₀ S₀ ≫ top (s₀ S₀).val Nu ≫ ofPairs [(0, 0)])° ∪ (succN)° ≫ Y ≫ ν S₀ G

end Mu

section Checks

private def moves (S₀ G : Rel X X) : List (Int64 × Int64) :=
  ((plan S₀ G).nub.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

private def S₁ : Rel X X := Blocks.S₀
private def G₁ : Rel X X := Blocks.G
private def tbl : Rel X X := 𝟙
private def AB : Rel X X := ofPairs [(0, 1), (1, 0)]

-- the per-key formulas on a one-key family are the note's formulas on one state
#guard R (Blocks.lvl S₁) == Blocks.lvl (Blocks.R S₁)
#guard M (Blocks.lvl S₁) == Blocks.lvl (Blocks.M S₁)
#guard M (Blocks.lvl tbl) == Blocks.lvl (Blocks.M tbl)
#guard S' (Blocks.lvl S₁) (Blocks.lvl (ofPairs [(2, 2)])) == Blocks.lvl (Blocks.move S₁ (ofPairs [(2, 2)]))
-- the 13 states of three blocks
-- a payload holds only the cells its rows refer to (`Vals.pick`): `L(s₀,𝟙)`, one row per count, each state 3 pairs
#guard let L := lay S₁ (s₀ S₁) fun D => D; L.n == 28 && L.val.1.1 ≤ 3 * L.n
-- each state's chosen move is one pair, held in 3 rows: row multiplicity is kept by `≫`, `est`, `pair`
#guard (σ S₁ G₁).n == 3 * (σ S₁ G₁).nub.n
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
-- the folds and the fixed points agree
#guard Mu.Q S₁ == Q S₁
#guard Mu.W S₁ G₁ == W S₁ G₁
#guard Mu.ζ S₁ G₁ == ζ S₁ G₁
#guard Mu.W tbl AB == W tbl AB

end Checks

end LeetQ.Rel.BlocksRel
