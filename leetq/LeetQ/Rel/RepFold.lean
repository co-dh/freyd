/-
  The fold ops of `Alg` read back. `fold`, `foldOn`, `map`, … all run `foldRows`: rounds that pair each row still
  pending with its element `k` from the end, hand both to the step, `nub` the result, and move the rows that have
  no element `k` to `out`. This file reads one round in `Rel(Set)` and the rounds' `out` by induction.
-/
import LeetQ.Rel.RepDiv

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

-- `RepDiv`'s `c1`, `nubI`, `PQ` (local notations, so restated here)
set_option hygiene false in
local notation "c1(" X ", " n ", " x ")" => (Obj.codes X (#v[⟨n, x⟩] : Vector (Part X) 1))[0]
set_option hygiene false in
local notation "nubI(" X ", " Y ", " R ")" =>
  (tuples.tupleIds (c1(X, Rel.n R, Rel.key R)) #[c1(Y, Rel.n R, Rel.val R)]).2
set_option hygiene false in
local notation "PQ(" Y ", " Z ")" =>
  (⟨_, Obj.raze Y #[⟨Rel.n P, Rel.key P⟩, ⟨Rel.n Q, Rel.key Q⟩] hNk,
    Obj.raze Z #[⟨Rel.n P, Rel.val P⟩, ⟨Rel.n Q, Rel.val Q⟩] hNv⟩ : Rel Y Z)
-- the parts `antiJoin pend° (idU el.key)` codes: the rows of `pend`, the rows of `el`
set_option hygiene false in
local notation "jparts" => (#v[⟨Rel.n (pend°), Rel.val (pend°)⟩,
  ⟨Rel.n (idU (Rel.key el)), Rel.val (idU (Rel.key el))⟩] : Vector (Part .long) 2)

/-- **One round of `foldRows`, read back**: the new state `S.nub` (`S` the step's result) is `S`, and the new
    `out`, `P ∪ (antiJoin pend° (idU el.key))°`, adds to `P` the pairs of `pend` whose row has no element this
    round. `antiJoin`'s and `∪`'s intermediate values are bound by their defining equations (`hjc`, `hI`, `hQ`).
    Hypotheses: `Obj.CodesFit` of every coded part, `Vals.PickFits` where a part is picked, the counts fit. -/
theorem round_rep {E V : Obj} (el : Rel .long E) (pend P S : Rel .long V)
    (hSK : Obj.CodesFit .long (#v[⟨S.n, S.key⟩] : Vector (Part .long) 1))
    (hSV : V.CodesFit (#v[⟨S.n, S.val⟩] : Vector (Part V) 1))
    (hSk : Vals.PickFits .long S.key (ids nubI(.long, V, S)))
    (hSv : Vals.PickFits V S.val (ids nubI(.long, V, S)))
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long jparts) (hjf : Obj.CodesFit .long jparts)
    (I : ByteArray) (hI : I = anti (jc[0]'(by decide)) (jc[1]'(by decide)))
    (hJk : Vals.PickFits V (Rel.key (pend°)) (ids I)) (hJv : Vals.PickFits .long (Rel.val (pend°)) (ids I))
    (Q : Rel .long V) (hQ : Q = (antiJoin (pend°) (idU (Rel.key el)))°)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part .long)).toList.map fun c : Part .long => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part V)).toList.map fun c : Part V => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits .long P.key Q.key) (hFv : Vals.RazeFits V P.val Q.val)
    (hUK : Obj.CodesFit .long (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).key⟩] : Vector (Part .long) 1))
    (hUV : V.CodesFit (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).val⟩] : Vector (Part V) 1))
    (hUk : Vals.PickFits .long (PQ(.long, V)).key (ids nubI(.long, V, PQ(.long, V))))
    (hUv : Vals.PickFits V (PQ(.long, V)).val (ids nubI(.long, V, PQ(.long, V)))) :
    rep (Rel.nub S) = rep S ∧
      ∀ r v, rep (P ∪ Q) r v ↔ rep P r v ∨ (rep pend r v ∧ ¬ ∃ e, rep el r e) := by
  refine ⟨rep_nub S (one_ok _ hSK) (one_ok _ hSV) hSk hSv, fun r v => ?_⟩
  rw [rep_union_full P Q hU hNk hNv hFk hFv (one_ok _ hUK) (one_ok _ hUV) hUk hUv]
  show rep P r v ∨ rep Q r v ↔ _
  subst hjc hI hQ
  have hA := congrFun (congrFun (rep_antiJoin (pend°) (idU (Rel.key el))
    (codes_faithful_wf .long _ hjf).1 hJk hJv) v) r
  rw [rep_conv]
  show _ ∨ rep (antiJoin (pend°) (idU (Rel.key el))) v r ↔ _
  rw [hA]
  show _ ∨ (∃ y, rep (pend°) v y ∧ y = r ∧ ¬ ∃ x, rep (idU (Rel.key el)) x y) ↔ _
  rw [rep_conv, rep_idU]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hp, rfl, hn⟩
    exact ⟨hp, fun ⟨_, i, hi, _⟩ => hn ⟨_, rfl, i, hi⟩⟩
  · rintro ⟨hp, hn⟩
    exact ⟨r, hp, rfl, fun ⟨x, hx, i, hi⟩ => hn ⟨Vals.row (Rel.val el) i, i, hi.trans hx, rfl⟩⟩

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.round_rep
