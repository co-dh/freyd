/-
The bit run's bookkeeping: which columns a plan reads (`colsL`), the picked parts `run?` sizes its matrices by
(`spOf`), and a leaf's matrix from `codeAll`'s codes under `uOf`.
-/
import LeetQ.Rel.Lang.BitsSpecLdiv
import LeetQ.Rel.Lang.BitsSpecPairs
import LeetQ.Rel.Lang.BitsSpecCode

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

/-- The columns `TP.cols` appends, in its order. -/
def TP.colsL : {A B : Obj} → TP A B → List Col
  | A, B, .leaf R => [⟨A, ⟨R.n, R.key⟩⟩, ⟨B, ⟨R.n, R.val⟩⟩]
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S => R.colsL ++ S.colsL
  | _, _, .conv R => R.colsL
  | B, C, .ldiv R S UB UC =>
    R.colsL ++ S.colsL ++ [⟨B, ⟨UB.n, UB.key⟩⟩, ⟨B, ⟨UB.n, UB.val⟩⟩, ⟨C, ⟨UC.n, UC.key⟩⟩, ⟨C, ⟨UC.n, UC.val⟩⟩]

theorem cols_toList : ∀ {A B : Obj} (p : TP A B) (acc : Array Col), (p.cols acc).toList = acc.toList ++ p.colsL
  | _, _, .leaf _, _ => by simp [TP.cols, TP.colsL, relCols]
  | _, _, .comp R S, acc | _, _, .meet R S, acc | _, _, .join R S, acc | _, _, .diff R S, acc => by
    simp [TP.cols, TP.colsL, cols_toList S, cols_toList R]
  | _, _, .conv R, acc => by simp [TP.cols, TP.colsL, cols_toList R]
  | _, _, .ldiv R S _ _, acc => by simp [TP.cols, TP.colsL, relCols, cols_toList S, cols_toList R]

/-- An object's picked part as `run?` reads it from `codeAll`'s second result. -/
def spOf (sps : Array Col) (X : Obj) : Part X := match sps.find? (·.1 == X) with
  | some ⟨Y, q⟩ => if h : Y = X then h ▸ q else ⟨0, Vals.empty X⟩
  | none => ⟨0, Vals.empty X⟩

theorem spOf_eq {sps : Array Col} {X : Obj} {q : Part X} (h : sps.find? (·.1 == X) = some ⟨X, q⟩) :
    spOf sps X = q := by simp [spOf, h]

/-- `run?` is `codeAll`, `fits` and the root read back at `spOf`. -/
theorem run?_eq {A B : Obj} (p : TP A B) : run? p = (do
    let (ids, sps) ← codeAll (p.cols #[])
    guard (p.fits fun X => (spOf sps X).1.toNat)
    pure ((Id.run ((p.bits ids fun X => (spOf sps X).1.toNat).run' 0)).table (spOf sps A) (spOf sps B))) := rfl

/-- A leaf's matrix reads the two code columns at the state and moves it by two. -/
theorem bits_leaf (ids : Array ByteArray) (sz : Obj → Nat) {A B : Obj} (R : Rel A B) (n : Nat) :
    ((TP.leaf R).bits ids sz).run n = (Bits.ofCodes (sz A) (sz B) (ids.getD n .empty) (ids.getD (n + 1) .empty), n + 2) :=
  by rw [TP.bits]; rfl

/-- **A leaf at position `n` of the coded columns** holds `TP.leaf R`'s relation under `uOf`, its shape the objects'
    picked counts. -/
theorem enc_leaf (cs : Array Col) {out : Array ByteArray} {sps : Array Col} (h : codeAll cs = some (out, sps))
    {A B : Obj} (R : Rel A B) {n : Nat} (hj : n + 1 < cs.size) (ek : cs[n] = ⟨A, ⟨R.n, R.key⟩⟩)
    (ev : cs[n + 1] = ⟨B, ⟨R.n, R.val⟩⟩)
    (hfit : (spOf sps A).1.toNat * (spOf sps B).1.toNat ≤ 2 ^ 27) :
    let x := (((TP.leaf R).bits out fun X => (spOf sps X).1.toNat).run n).1
    x.na = (spOf sps A).1.toNat ∧ x.w = (spOf sps B).1.toNat ∧ x.Enc (uOf cs A) (uOf cs B) (TP.leaf R).den := by
  obtain ⟨qa, qb, ha, hb, he⟩ := codeAll_leaf cs h R (by omega) hj ek ev
  rw [spOf_eq ha, spOf_eq hb] at hfit; simp only [bits_leaf, spOf_eq ha, spOf_eq hb]
  exact ⟨rfl, rfl, he hfit⟩

#print axioms enc_leaf

end LeetQ.Rel.Lang.Bits
