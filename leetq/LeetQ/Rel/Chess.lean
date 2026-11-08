import LeetQ.Rel.Algebra

/-! Mate in one as relation algebra. A square is the long `0 … 63` (a1 = 0, b1 = 1, …, h8 = 63), a piece
    the long `colour*6 + kind` (kind 0 P, 1 N, 2 B, 3 R, 4 Q, 5 K; white `0 … 5`, black `6 … 11`), a
    position the long id `x`. The board is one relation `on : X ⟶ Sq×Pc`, one row per piece, so a
    position with other pieces is other rows, never other code. Mate is relation algebra on two base
    relations `att`, `nxt : X×Sq ⟶ X×Sq`; only they know how a piece moves. -/

namespace LeetQ.Rel.Chess

open Alg QLean

abbrev X : Obj := .long
abbrev Sq : Obj := .long
abbrev Pc : Obj := .long
abbrev Sq2 : Obj := .prod Sq Sq
abbrev Pc2 : Obj := .prod Pc Pc
/-- A square of a position, `(x, s)`. -/
abbrev At : Obj := .prod X Sq
/-- A board: `x ⟶ (s, p)`, in `x` the square `s` holds `p`. -/
abbrev Board := Rel X (.prod Sq Pc)
/-- `(piece, from, to)`. -/
abbrev Move : Obj := .prod Pc Sq2
/-- A move read in a position, `(x, (p, (s, t)))`. -/
abbrev W : Obj := .prod X (.prod Pc Sq2)

/-- A literal long column; `Arr.ofPart` checks the count. -/
def col (n : Nat) (xs : List Int64) : Except String (Arr .long n) := Arr.ofPart .long n (longs (packLongs xs)) "col"

/-- A relation from its pairs of longs. -/
def ofPairs (ps : List (Int64 × Int64)) : Except String (Rel .long .long) := do
  pure ⟨ps.length, ← col ps.length (ps.map (·.1)), ← col ps.length (ps.map (·.2))⟩

/-! ## The tables, built in Lean: only `att` and `nxt` read them -/

def line (a b : Nat) : Bool := a != b && (a % 8 == b % 8 || a / 8 == b / 8)
def adj (a b : Nat) : Bool := a != b && a % 8 ≤ b % 8 + 1 && b % 8 ≤ a % 8 + 1 && a / 8 ≤ b / 8 + 1 && b / 8 ≤ a / 8 + 1
def sqPairs (f : Nat → Nat → Bool) : List (Nat × Nat) := (List.range 64).flatMap fun a => ((List.range 64).filter (f a)).map (a, ·)

/-- `pat : Pc×Sq ⟶ Sq`, the piece `p` on `s` reaches `t` on an empty board; its kinds are the implemented ones. -/
def pat : Except String (Rel (.prod Pc Sq) Sq) := do
  let ps : List (Int64 × Nat × Nat) := [((3 : Int64), line), (9, line), (5, adj), (11, adj)].flatMap fun (p, f) => (sqPairs f).map fun (a, b) => (p, a, b)
  let n := ps.length
  pure ⟨n, (← col n (ps.map (·.1)), ← col n (ps.map (Int64.ofNat ·.2.1))), ← col n (ps.map (Int64.ofNat ·.2.2))⟩

/-- `Btw : Sq² ⟶ Sq`, `s` strictly between `a` and `b` on a rank or file. -/
def Btw : Except String (Rel Sq2 Sq) := do
  let ps := (sqPairs line).flatMap fun (a, b) => ((List.range 64).filter fun s =>
    (s % 8 == a % 8 && a % 8 == b % 8 || s / 8 == a / 8 && a / 8 == b / 8) && min a b < s && s < max a b).map (a, b, ·)
  let n := ps.length
  pure ⟨n, (← col n (ps.map (Int64.ofNat ·.1)), ← col n (ps.map (Int64.ofNat ·.2.1))), ← col n (ps.map (Int64.ofNat ·.2.2))⟩

/-- The coreflexive on the piece pairs `(p, q)` with `f p q`. -/
def pcRel (f : Int64 → Int64 → Bool) : Except String (Rel Pc2 Pc2) := do
  let cs := (List.range 12).map Int64.ofNat
  let ps := cs.flatMap fun p => (cs.filter (f p ·)).map (p, ·)
  let P ← ofPairs ps; pure (idU (P.key, P.val))

/-- `(p, q)`: `q` cuts `p`'s line in `att`, every piece but `p`'s opposing king. -/
def cutsAtt : Except String (Rel Pc2 Pc2) := pcRel fun p q => q != if p < 6 then 11 else 5
/-- `(p, q)`: `q` cuts `p`'s line in `nxt`, every piece. -/
def cutsNxt : Except String (Rel Pc2 Pc2) := pcRel fun _ _ => true
/-- `(p, q)`: `p` and `q` have one colour. -/
def same : Except String (Rel Pc2 Pc2) := pcRel fun p q => p / 6 == q / 6

/-! ## `att` and `nxt` -/

/-- `x×s ⟶ p`, the piece on each occupied square. -/
def pcs (on : Board) : Rel At Pc := ⟨on.n, (on.key, on.val.1), on.val.2⟩

/-- The rows `(x, (p, (s, t)))` with `t` in `pat` of `p` on `s`; a kind with no `pat` is an error. -/
def cand (on : Board) : Except String (Rel W W) := do
  let O := pcs on; let pt ← pat
  if let ((x, s), p) :: _ := (← antiJoin O (← dom (⟨pt.n, pt.key.1, pt.key.1⟩ : Rel Pc Pc))).toList then
    throw s!"Chess: piece {p} on square {s} of position {x} has no att/nxt yet"
  let M ← comp (⟨O.n, O.key, (O.val, O.key.2)⟩ : Rel At (.prod Pc Sq))
    (⟨pt.n, pt.key, (pt.key.1, (pt.key.2, pt.val))⟩ : Rel (.prod Pc Sq) (.prod Pc Sq2))
  pure (idU (M.key.1, M.val))

/-- The rows `w = (x, (p, …))` of `S : W ⟶ Sq` whose square holds, in `x`, a piece `q` with `(p, q)` in `B`. -/
def meets (on : Board) (S : Rel W Sq) (B : Rel Pc2 Pc2) : Except String (Rel W W) := do
  let Q ← comp (⟨S.n, S.key, (S.key.1, S.val)⟩ : Rel W At) (pcs on)
  dom (← comp (⟨Q.n, Q.key, (Q.key.2.1, Q.val)⟩ : Rel W Pc2) B)

/-- The rows of `C` with a piece of `B` strictly between `s` and `t`. -/
def cut (on : Board) (C : Rel W W) (B : Rel Pc2 Pc2) : Except String (Rel W W) := do
  meets on (← comp (⟨C.n, C.key, C.key.2.2⟩ : Rel W Sq2) (← Btw)) B

/-- `(x, (p, (s, t))) ↦ ((x, s), (x, t))`. -/
def toAt (C : Rel W W) : Rel At At := ⟨C.n, (C.key.1, C.key.2.2.1), (C.key.1, C.key.2.2.2)⟩

/-- `att : X×Sq ⟶ X×Sq`, in `x` the piece on `s` attacks `t`, which may hold a piece of either colour.
    The opposing king does not cut a line, so the square behind a checked king counts as attacked. -/
def att (on : Board) : Except String (Rel At At) := do
  let C ← cand on; pure (toAt (← diff C (← cut on C (← cutsAtt))))

/-- `nxt : X×Sq ⟶ X×Sq`, in `x` the piece on `s` can move to `t`: every piece cuts a line, not onto its
    own colour, a capture allowed; whether the mover's king is left in check is not asked. -/
def nxt (on : Board) : Except String (Rel At At) := do
  let C ← cand on; let C ← diff C (← cut on C (← cutsNxt))
  pure (toAt (← diff C (← meets on ⟨C.n, C.key, C.key.2.2.2⟩ (← same))))

/-! ## Mate -/

/-- `x ⟶ (x, s)`, the squares of the pieces `cs`. -/
def side (cs : List Int64) (on : Board) : Except String (Rel X At) := do
  let O ← comp (pcs on) (idU (← col cs.length cs)); pure ⟨O.n, O.key.1, O.key⟩

/-- `onʷ, k : X ⟶ X×Sq`: the white-occupied squares; the black king's square. -/
def onW : Board → Except String (Rel X At) := side [0, 1, 2, 3, 4, 5]
def k : Board → Except String (Rel X At) := side [11]

/-- `Aʷ ≜ onʷ att : X ⟶ X×Sq`, the squares white attacks. -/
def Aw (on : Board) : Except String (Rel X At) := do comp (← onW on) (← att on)

/-- `D ≜ Aʷ / nxt : X ⟶ X×Sq`, `Z ⊑ D ⟺ Z nxt ⊑ Aʷ`: the pieces all of whose next squares are attacked.
    The universes: the positions, the occupied squares. -/
def D (on : Board) : Except String (Rel X At) := do rightDiv (← Aw on) (← nxt on) (← dom on).key (pcs on).key

/-- `Mate ≜ k ∩ Aʷ ∩ D`: the black king, attacked, all of whose next squares are attacked. -/
def Mate (on : Board) : Except String (Rel X At) := do inter (← k on) (← inter (← Aw on) (← D on))

/-- `k ⊑ Aʷ ∩ D`, for a board of one position. -/
def isMate (on : Board) : Except String Bool := do le (← k on) (← inter (← Aw on) (← D on))

/-- The mate-in-one moves of white on the board `on` of position `0`: every white piece's `nxt`, the move
    of row `i` reaching position `i + 1`, whose board is `on` without the rows on the move's `s` and `t`,
    with `(t, p)`; the moves to `dom Mate`. -/
def mateIn1 (on : Board) : Except String (Rel Move Move) := do
  let Mv ← pair (pcs on) (← comp (idU (← onW on).val) (← nxt on))
  let n := Mv.n
  let y ← col n ((List.range n).map (Int64.ofNat · + 1))
  let M : Rel Move X := ⟨n, (Mv.val.1, (Mv.key.2, Mv.val.2.2)), y⟩
  let T ← top y on.val
  let G ← union (⟨n, y, Mv.key.2⟩ : Rel X Sq) ⟨n, y, Mv.val.2.2⟩
  let K ← antiJoin (⟨T.n, T.val.2, (T.key, T.val.1)⟩ : Rel Pc At) (idU (G.key, G.val))
  let on1 ← union (⟨K.n, K.val.1, (K.val.2, K.key)⟩ : Board) ⟨n, y, (Mv.val.2.2, Mv.val.1)⟩
  dom (← comp M (← dom (← Mate on1)))

/-- The board of position `0` from its `(square, piece)` rows. -/
def pos (ps : List (Nat × Int64)) : Except String Board := do
  let n := ps.length
  pure ⟨n, ← col n (List.replicate n 0), (← col n (ps.map (Int64.ofNat ·.1)), ← col n (ps.map (·.2)))⟩

section Checks

private def answer (ps : List (Nat × Int64)) : Except String (List (List Int64)) :=
  (do mateIn1 (← pos ps)).map fun (R : Rel Move Move) =>
    (R.toList.map fun (m : (Int64 × Int64 × Int64) × (Int64 × Int64 × Int64)) => [m.1.1, m.1.2.1, m.1.2.2]).mergeSort fun a b => decide (a ≤ b)

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates
#guard (answer [(6, 5), (48, 3), (1, 3), (60, 11)]).toOption == some [[3, 1, 57]]
-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
#guard (answer [(6, 5), (48, 3), (1, 3), (58, 11)]).toOption == some []
-- W Kg1 Ra7 Rb8: Ke8 is mated (f8 is behind the king on b8's line); Kc8 takes the undefended b8
#guard (do isMate (← pos [(6, 5), (48, 3), (57, 3), (60, 11)])).toOption == some true
#guard (do isMate (← pos [(6, 5), (48, 3), (57, 3), (58, 11)])).toOption == some false
-- a third rook, no new code: Rb1-b8 and Rh2-h8 (h8 = 63, the bit of Int64.minValue)
#guard (answer [(6, 5), (48, 3), (1, 3), (15, 3), (60, 11)]).toOption == some [[3, 1, 57], [3, 15, 63]]
-- a white knight on f3: no att/nxt for it yet
#guard answer [(6, 5), (48, 3), (1, 3), (21, 1), (60, 11)] matches .error "Chess: piece 1 on square 21 of position 0 has no att/nxt yet"

end Checks

end LeetQ.Rel.Chess
