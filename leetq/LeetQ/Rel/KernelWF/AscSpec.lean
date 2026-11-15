/-
  `Obj.sortBy` realises q's `asc` order `Obj.lt` (`ObjOrder.lean`): at every atom a kernel grades by its key
  (`orderKind t = some k`, the boolean included) the answer lists the rows ascending by `Obj.lt`, ties in the
  order they came in, and a product of two such sides sorts lexicographically.
-/
import LeetQ.Rel.KernelWF.SortSpec
import LeetQ.Rel.KernelWF.PickSpec
import LeetQ.Rel.KernelWF.RazeSpec
import LeetQ.Rel.ObjOrder
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.CodesRec
import QLean.Verify.Grade

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- Row `i` of `c` comes no later than row `j` in q's `asc` order, rows of one key ordered by `R`. -/
def ascBy (A : Obj) {n : USize} (c : Vals A n) (R : Nat → Nat → Prop) (i j : Nat) : Prop :=
  ∀ (hi : i < n.toNat) (hj : j < n.toNat), A.lt (c.row ⟨i, hi⟩) (c.row ⟨j, hj⟩) ∨
    (A.key (c.row ⟨i, hi⟩) = A.key (c.row ⟨j, hj⟩) ∧ R i j)

/-- Every array payload and sum side of `x` holds fewer than `2^63` values: the longs `place` and `addc`
    compute `Vals.row`'s positions in. `Vals.pickShared` keeps it (`pickShared_small`), sharing the payloads. -/
def _root_.LeetQ.Rel.Vals.Small : {A : Obj} → {n : USize} → Vals A n → Prop
  | .atom _, _, _ => True
  | .prod _ _, _, x => x.1.Small ∧ x.2.Small
  | .arr _, _, x => x.1.toNat < 2 ^ 63 ∧ x.2.2.2.Small
  | .sum _ _, _, x => x.1.toNat < 2 ^ 63 ∧ x.2.1.toNat < 2 ^ 63 ∧ x.2.2.2.2.1.Small ∧ x.2.2.2.2.2.Small

/-- `sortBy` at `A` sorts stably by `Obj.lt`: refining a `p` listed in `R` order, it answers `p` again, ascending
    by `Obj.lt`, rows of one key still in `R` order — on a column whose payloads are `Small`. -/
def SortsAsc (A : Obj) : Prop :=
  ∀ {n : USize} (c : Vals A n), c.Small → ∀ p : ByteArray, len p < USize.size → (∀ i ∈ ids p, i < n.toNat) →
    ∀ R : Nat → Nat → Prop, (ids p).Pairwise R →
      (ids (A.sortBy c p)).Perm (ids p) ∧ (ids (A.sortBy c p)).Pairwise (ascBy A c R)

/-- A grade ordered by a `UInt64` key `κ` that is each row's `Obj.key`, read as one number, is ascending by
    `Obj.lt` with ties in index order. -/
theorem ascBy_of_keyOrd {t : QAtomicType} {n : USize} (x : Arr t n) (κ : Nat → UInt64)
    (hκ : ∀ i (hi : i < n.toNat), (Obj.atom t).key (x.get ⟨i, hi⟩) = [(κ i).toNat]) {g : List Nat}
    (hs : g.Pairwise fun i j => keyOrd false (κ i) (κ j) ∧ (keyOrd false (κ j) (κ i) → i < j)) :
    g.Pairwise (ascBy (.atom t) (n := n) x (· < ·)) := by
  refine hs.imp fun {i j} ⟨h1, h2⟩ hi hj => ?_
  simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1 h2
  simp only [Vals.row_atom, Obj.lt]
  rw [hκ i hi, hκ j hj]
  rcases UInt64.lt_or_eq_of_le h1 with hl | he
  · exact .inl (List.cons_lt_cons_iff.2 (.inl (UInt64.lt_iff_toNat_lt.1 hl)))
  · exact .inr ⟨by rw [he], h2 (by rw [he]; exact UInt64.le_refl _)⟩

/-- **An atom a kernel grades sorts stably by `Obj.lt`**, given that its `gradeColumn` answers a permutation of
    `til n` ascending by `Obj.lt`, ties in index order. -/
theorem sortsAsc_atom (t : QAtomicType)
    (hg : ∀ {n : USize} (x : Arr t n), ∃ g, gradeColumn t false n x.enc = some (.bytes g) ∧
      (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom t) (n := n) x (· < ·))) :
    SortsAsc (.atom t) := by
  intro n c _ p hl hp R hR
  obtain ⟨g, hgc, hgp, hgs⟩ := hg (pick t ⟨_, c⟩ p).2
  have hx := pick_len t ⟨_, c⟩ p hl
  have hsb : (Obj.atom t).sortBy c p = gather 8 p g := by simp only [Obj.sortBy, Obj.sortByC, hgc]
  rw [hx] at hgp
  have hGm : ∀ s ∈ ids g, s < len p := fun s hs => List.mem_range.1 (hgp.mem_iff.1 hs)
  have hlen : (ids p).length = len p := (len_eq_ids p).symm
  have hd : ∀ s (hs : s < len p), (ids p).getD s 0 = (ids p)[s]'(hlen ▸ hs) := fun s hs => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hs), Option.getD_some]
  have hrow : ∀ s (hs : s < len p) (hin : (ids p).getD s 0 < n.toNat),
      c.get ⟨_, hin⟩ = (pick t ⟨_, c⟩ p).2.get ⟨s, hx ▸ hs⟩ := fun s hs hin => by
    have hin' : (Column.bitsAt p (s * 8) 8).toNat < n.toNat := by rwa [hd s hs, ids_getElem] at hin
    rw [pick_get ⟨_, c⟩ p hl s _ hin']
    exact congrArg c.get (Fin.ext (by simp only [hd s hs, ids_getElem]))
  rw [hsb]
  refine ⟨gather_perm hgp, ?_⟩
  rw [ids_gather8 hGm, List.pairwise_map]
  refine hgs.imp_of_mem fun {a a'} ha ha' hrel hi hj => ?_
  have hal := hGm a ha; have hal' := hGm a' ha'
  show (Obj.atom t).lt (c.get _) (c.get _) ∨ (Obj.atom t).key (c.get _) = (Obj.atom t).key (c.get _) ∧ _
  rw [hrow a hal hi, hrow a' hal' hj]
  rcases hrel (hx ▸ hal) (hx ▸ hal') with h | ⟨e, h⟩
  · exact .inl h
  · refine .inr ⟨e, ?_⟩
    rw [hd a hal, hd a' hal']
    exact List.pairwise_iff_getElem.1 hR a a' _ _ h

/-- **A product sorts lexicographically**: `sortBy` refines by the second component, then stably by the first. -/
theorem sortsAsc_prod {a b : Obj} (ha : SortsAsc a) (hb : SortsAsc b) : SortsAsc (.prod a b) := by
  intro n c hc p hl hp R hR
  have hsb : (Obj.prod a b).sortBy c p = a.sortBy c.1 (b.sortBy c.2 p) := rfl
  obtain ⟨p1, s1⟩ := hb c.2 hc.2 p hl hp R hR
  have hl1 : len (b.sortBy c.2 p) < USize.size := by rw [len_eq_ids, p1.length_eq, ← len_eq_ids]; exact hl
  obtain ⟨p2, s2⟩ := ha c.1 hc.1 _ hl1 (fun i hi => hp i (p1.mem_iff.1 hi)) _ s1
  rw [hsb]
  refine ⟨p2.trans p1, s2.imp fun {i j} h hi hj => ?_⟩
  show (Obj.prod a b).lt (c.1.row _, c.2.row _) (c.1.row _, c.2.row _) ∨
    a.key (c.1.row _) ++ b.key (c.2.row _) = a.key (c.1.row _) ++ b.key (c.2.row _) ∧ R i j
  rw [Obj.lt_prod]
  rcases h hi hj with h | ⟨e, h⟩
  · exact .inl (.inl h)
  · rcases h hi hj with h | ⟨e', h⟩
    · exact .inl (.inr ⟨e, h⟩)
    · exact .inr ⟨by rw [e, e'], h⟩

/-- **The target**: on a side that sorts by `Obj.lt`, no row of the answer is before an earlier one. -/
theorem sortBy_asc {A : Obj} (hA : SortsAsc A) {n : USize} (c : Vals A n) (hc : c.Small) (p : ByteArray)
    (hl : len p < USize.size) (hp : ∀ i ∈ ids p, i < n.toNat) :
    (ids (A.sortBy c p)).Pairwise fun i j => ∀ (hi : i < n.toNat) (hj : j < n.toNat),
      ¬ A.lt (c.row ⟨j, hj⟩) (c.row ⟨i, hi⟩) :=
  (hA c hc p hl hp (fun _ _ => True) (List.pairwise_iff_getElem.2 fun _ _ _ _ _ => trivial)).2.imp
    fun h hi hj => (h hi hj).elim (A.lt_asymm ·) fun ⟨e, _⟩ => by unfold Obj.lt; rw [e]; exact List.lt_irrefl _

/-! ## The numeric atoms: `grade` and `gradeFoR` by `Order.keyAt` -/

/-- At a type `orderKind` keys by a byte layout, `gradeColumn` is `gradeFoR` on the encoded form and `grade`
    on the dense bytes. -/
theorem gradeColumn_num {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit)
    (n : USize) (e : Enc) : gradeColumn t false n e = match e with
      | .foR md pk => some (.bytes (Order.gradeFoR k false n md pk))
      | e => match Enc.bytesOf t n e with
        | some b => if b.size < n.toNat * k.width then none else some (.bytes (Order.grade k false n b))
        | none => none := by
  cases t <;> simp only [orderKind, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact absurd rfl hk | (cases e <;> rfl)

theorem width_num {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit) :
    t.width = some k.width := by
  cases t <;> simp only [orderKind, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact absurd rfl hk | rfl

/-- **The key bridge**: element `i` of a numeric column, its key as `Obj.key` reads it, is the one number
    `Order.keyAt` grades it by, over the column's dense bytes. -/
theorem key_get {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit) {n : USize}
    (x : Arr t n) {b : ByteArray} (hb : Enc.bytesOf t n x.enc = some b) (i : Nat) (hi : i < n.toNat) :
    (Obj.atom t).key (x.get ⟨i, hi⟩) = [(Order.keyAt k b i).toNat] := by
  have hw := width_num h hk
  have hne : t ≠ .general := by rintro rfl; simp [orderKind] at h
  have hnb : t ≠ .boolean := by rintro rfl; simp only [orderKind, Option.some.injEq] at h; exact hk h.symm
  rw [Arr.get_ne _ _ hne, ← get_bytesOf hw hnb x.wf hb hi]
  have hka : Order.keyAt k b i = Order.rank k (Column.bitsAt b (i * k.width) k.width) := by
    cases k <;> first | exact absurd rfl hk | rfl
  have hv := bitsAt_lt b (i * k.width) k.width (by cases k <;> decide)
  have hget : Enc.get t n (.bytes b) i = some (Column.atomOfBits t (Column.bitsAt b (i * k.width) k.width) hne) := by
    cases t <;> simp only [orderKind, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      first | exact absurd rfl hk | (simp only [Enc.get, if_pos hi]; rfl)
  rw [hka, hget]
  generalize Column.bitsAt b (i * k.width) k.width = v at hv
  cases t <;> simp only [orderKind, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact absurd rfl hk | skip
  all_goals simp only [Option.bind_some, Column.atomOfBits, Carrier.of?, Option.getD_some, Obj.key, Order.rank,
    Scan.Kind.width, List.cons.injEq, and_true] at hv ⊢
  all_goals first
    | (congr 3; simp; done)
    | ((try congr 2) <;> (try apply UInt64.toNat_inj.1) <;> simp at hv ⊢ <;> omega)
    | rw [show v.toUInt32.toUInt64.toUInt32 = v.toUInt32 from UInt32.toNat_inj.1 (by simp <;> omega)]

/-- **`gradeColumn` at a numeric type sorts by `Obj.lt`**, stable, on every encoding. -/
theorem grade_num {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit) {n : USize}
    (x : Arr t n) : ∃ g, gradeColumn t false n x.enc = some (.bytes g) ∧
      (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom t) (n := n) x (· < ·)) := by
  have hw := width_num h hk
  have hnb : t ≠ .boolean := by rintro rfl; simp only [orderKind, Option.some.injEq] at h; exact hk h.symm
  obtain ⟨b, hb, hs⟩ := bytesOf_size hnb hw x.wf
  have hk0 : 0 < k.width := by cases k <;> decide
  rw [gradeColumn_num h hk]
  cases he : x.enc
  case foR md pk =>
    rw [he] at hb
    simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at hb
    subst hb
    obtain ⟨hav, hkey⟩ := decode_keyAt k hk n md pk
    obtain ⟨hp, hsrt⟩ := gradeFoR_spec k hk false n md pk
    refine ⟨_, rfl, hp, ascBy_of_keyOrd x (Order.keyAt k (Coc.decode k.width.toUSize md pk n))
      (key_get h hk x (by rw [he]; simp [Enc.bytesOf, hw]) ) ?_⟩
    have hlt : ∀ {i}, i ∈ ids (Order.gradeFoR k false n md pk) → i < n.toNat := fun hi =>
      List.mem_range.1 (hp.mem_iff.1 hi)
    exact hsrt.imp_of_mem fun hi hj hr => by rw [hkey _ (hlt hi), hkey _ (hlt hj)]; exact hr
  all_goals
    rw [he] at hb
    simp only [hb, if_neg (show ¬ b.size < n.toNat * k.width by omega)]
    obtain ⟨hp, hsrt⟩ := grade_spec k false n b
    have hav : min n.toNat (k.avail b) = n.toNat := by
      have : k.avail b = b.size / k.width := by cases k <;> first | exact absurd rfl hk | rfl
      rw [this, hs, Nat.mul_div_cancel _ hk0, Nat.min_self]
    rw [hav] at hp
    exact ⟨_, rfl, hp, ascBy_of_keyOrd x _ (key_get h hk x (by rw [he]; exact hb)) hsrt⟩

theorem sortsAsc_num {t : QAtomicType} {k : Scan.Kind} (h : orderKind t = some k) (hk : k ≠ .bit) :
    SortsAsc (.atom t) := sortsAsc_atom t fun x => grade_num h hk x

/-! ## The boolean: `grade .bit` -/

theorem grade_boolean {n : USize} (x : Arr .boolean n) : ∃ g, gradeColumn .boolean false n x.enc = some (.bytes g) ∧
    (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom .boolean) (n := n) x (· < ·)) := by
  have hwf := x.wf
  cases he : x.enc
  case bits b =>
    rw [he] at hwf
    obtain ⟨hp, hsrt⟩ := grade_spec .bit false n b
    have hav : min n.toNat (Scan.Kind.avail .bit b) = n.toNat := by
      simp only [Scan.Kind.avail]; simp only [Enc.WF] at hwf; omega
    rw [hav] at hp
    refine ⟨_, rfl, hp, ascBy_of_keyOrd x _ (fun i hi => ?_) hsrt⟩
    rw [Arr.get_bool_bits x he]
    simp only [Obj.key, Order.keyAt, Scan.Kind.bitsAt, Order.rank]
    split <;> rfl
  all_goals rw [he] at hwf; simp [Enc.WF] at hwf

theorem sortsAsc_boolean : SortsAsc (.atom .boolean) := sortsAsc_atom .boolean grade_boolean

/-! ## Bytes compared by `symCmp`: the lexicographic order of their symbol keys -/

/-- `compare` on bytes answers `.gt` exactly when the second is below the first as a number. -/
theorem compare_gt_u8 (u v : UInt8) : compare u v = .gt ↔ v.toNat < u.toNat := by
  show compareOfLessAndEq u v = .gt ↔ _
  unfold compareOfLessAndEq
  split
  · rename_i h1; rw [UInt8.lt_iff_toNat_lt] at h1; simp only [reduceCtorEq, false_iff]; omega
  · split
    · rename_i h2; subst h2; simp
    · rename_i h1 h2
      have : u.toNat ≠ v.toNat := fun e => h2 (UInt8.toNat_inj.1 e)
      rw [UInt8.lt_iff_toNat_lt] at h1; simp only [true_iff]; omega

/-- `symCmp`'s body over two byte lists answers `.gt` exactly when the second's symbol key (each byte `+1`, then
    `0`, as `Obj.key` keys a symbol) is below the first's. -/
theorem symCmp_gt_list (a b : List UInt8) :
    (match (List.range (min a.length b.length)).find? (fun i => a[i]?.getD 0 != b[i]?.getD 0) with
      | some i => compare (a[i]?.getD 0) (b[i]?.getD 0)
      | none => compare a.length b.length) = .gt ↔
      b.map (·.toNat + 1) ++ [0] < a.map (·.toNat + 1) ++ [0] := by
  induction a generalizing b with
  | nil => cases b <;> simp [compare, compareOfLessAndEq, List.cons_lt_cons_iff]
  | cons u a ih => cases b with
    | nil => simp [compare, compareOfLessAndEq, List.cons_lt_cons_iff]
    | cons v b =>
      simp only [List.length_cons]
      rw [show min (a.length + 1) (b.length + 1) = min a.length b.length + 1 by omega, List.range_succ_eq_map,
        List.find?_cons]
      by_cases huv : u = v
      · subst huv
        simp only [List.length_cons, List.getElem?_cons_zero, Option.getD_some, bne_self_eq_false,
          List.find?_map, List.map_cons, List.cons_append, List.cons_lt_cons_iff, Nat.lt_irrefl, false_or,
          true_and]
        simp only [Function.comp_def, List.getElem?_cons_succ]
        rw [← ih b]
        rcases (List.range (min a.length b.length)).find? (fun i => a[i]?.getD 0 != b[i]?.getD 0) with _ | j
        · simp only [Option.map_none, Nat.compare_eq_gt]; omega
        · simp only [Option.map_some, Nat.succ_eq_add_one, List.getElem?_cons_succ]
      · have hn : u.toNat ≠ v.toNat := fun h => huv (UInt8.toNat_inj.1 h)
        simp only [List.getElem?_cons_zero, Option.getD_some, bne_iff_ne, ne_eq, huv, not_false_eq_true,
          decide_true, List.map_cons, List.cons_append, List.cons_lt_cons_iff, compare_gt_u8]
        simp only [show (u != v) = true from bne_iff_ne.2 huv, List.getElem?_cons_zero, Option.getD_some, compare_gt_u8]
        constructor
        · intro h; exact .inl (by omega)
        · rintro (h | ⟨h, -⟩) <;> omega

/-- **`symCmp` is the symbol key's order**: `x` is not after `y` exactly when `y`'s key is not below `x`'s. -/
theorem symCmp_ne_gt (x y : ByteArray) : (Column.symCmp x y != .gt) = true ↔
    ¬ y.data.toList.map (·.toNat + 1) ++ [0] < x.data.toList.map (·.toNat + 1) ++ [0] := by
  rw [← symCmp_gt_list, bne_iff_ne, ne_eq]
  unfold Column.symCmp
  simp only [← bget, ByteArray.size, Array.length_toList]
  exact Iff.rfl

/-- A grade sorted by a total preorder `le` that reads `x`'s order — `le i j` exactly when row `j` is not before
    row `i` — with ties in index order is ascending by `Obj.lt`, ties in index order. -/
theorem ascBy_of_le {t : QAtomicType} {n : USize} (x : Arr t n) (le : Nat → Nat → Bool) {g : List Nat}
    (hle : ∀ i j (hi : i < n.toNat) (hj : j < n.toNat),
      le i j = true ↔ ¬ (Obj.atom t).lt (x.get ⟨j, hj⟩) (x.get ⟨i, hi⟩))
    (hs : g.Pairwise fun i j => le i j ∧ (le j i → i < j)) : g.Pairwise (ascBy (.atom t) (n := n) x (· < ·)) := by
  refine hs.imp fun {i j} ⟨h1, h2⟩ hi hj => ?_
  simp only [Vals.row_atom]
  rcases (Obj.atom t).lt_trichotomy (x.get ⟨i, hi⟩) (x.get ⟨j, hj⟩) with h | h | h
  · exact .inl h
  · refine .inr ⟨h, h2 ((hle j i hj hi).2 ?_)⟩
    unfold Obj.lt; rw [h]; exact List.lt_irrefl _
  · exact absurd h ((hle i j hi hj).1 h1)

/-- `symCmp`'s comparator is a total preorder: the symbol keys' `≤`. -/
theorem symLe_trans {x y z : ByteArray} (h1 : (Column.symCmp x y != .gt) = true)
    (h2 : (Column.symCmp y z != .gt) = true) : (Column.symCmp x z != .gt) = true := by
  rw [symCmp_ne_gt] at h1 h2 ⊢
  exact List.not_lt.2 (List.le_trans (List.not_lt.1 h1) (List.not_lt.1 h2))

theorem symLe_total (x y : ByteArray) : ((Column.symCmp x y != .gt) || (Column.symCmp y x != .gt)) = true := by
  rw [Bool.or_eq_true, symCmp_ne_gt, symCmp_ne_gt]
  exact (List.le_total _ _).imp List.not_lt.2 List.not_lt.2 |>.symm

/-- Two byte strings of one length: their symbol keys are ordered as their bytes. -/
theorem symKey_lt_iff : ∀ (a b : List UInt8), a.length = b.length →
    (a.map (·.toNat + 1) ++ [0] < b.map (·.toNat + 1) ++ [0] ↔ a.map (·.toNat) < b.map (·.toNat))
  | [], [], _ => by simp
  | u :: a, v :: b, hl => by
    simp only [List.map_cons, List.cons_append, List.cons_lt_cons_iff, Nat.add_right_cancel_iff,
      Nat.add_lt_add_iff_right, symKey_lt_iff a b (by simpa using hl)]
  | [], _ :: _, hl | _ :: _, [], hl => by simp at hl

/-! ## The guid: `gradeGuid` by its sixteen bytes -/

/-- Element `i` of a guid column, its `Obj.key`, is its sixteen stored bytes. -/
theorem key_guid {n : USize} (x : Arr .guid n) {b : ByteArray} (he : x.enc = .bytes b) (i : Nat)
    (hi : i < n.toNat) :
    (Obj.atom .guid).key (x.get ⟨i, hi⟩) = (b.extract (16 * i) (16 * i + 16)).data.toList.map (·.toNat) := by
  have hs : b.size = n.toNat * 16 := by have := x.wf; rw [he] at this; exact this
  rw [Arr.get_ne _ _ (by decide), he]
  simp only [Enc.get, if_pos hi, Option.bind_some, Carrier.of?, Option.getD_some, Obj.key]
  congr 1
  rw [extract_toList]
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [Vector.toList_ofFn, List.getElem_ofFn, List.getElem_take, List.getElem_drop, bget]
  rw [List.getElem?_eq_getElem (by simp at h2 ⊢; omega)]
  simp only [Option.getD_some]; congr 1; omega

theorem grade_guid {n : USize} (x : Arr .guid n) : ∃ g, gradeColumn .guid false n x.enc = some (.bytes g) ∧
    (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom .guid) (n := n) x (· < ·)) := by
  have hwf := x.wf
  cases he : x.enc
  case bytes b =>
    rw [he] at hwf
    have hs : b.size / 16 = n.toNat := by
      have : b.size = n.toNat * 16 := hwf
      omega
    obtain ⟨hp, hsrt⟩ := range_mergeSort (le := fun i j => Column.symCmp (b.extract (16 * i) (16 * i + 16)) (b.extract (16 * j) (16 * j + 16)) != .gt)
      (fun _ _ _ => symLe_trans) (fun _ _ => symLe_total _ _) (b.size / 16)
    rw [hs] at hp hsrt
    have hm : ∀ i ∈ (List.range n.toNat).mergeSort (fun i j => Column.symCmp (b.extract (16 * i) (16 * i + 16)) (b.extract (16 * j) (16 * j + 16)) != .gt),
        i < 2 ^ 64 := fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) (usize_lt n)
    refine ⟨_, rfl, ?_⟩
    simp only [Order.gradeGuid, Bool.false_eq_true, ↓reduceIte, hs]
    rw [ids_indices _ hm]
    refine ⟨hp, ascBy_of_le x _ (fun i j hi hj => ?_) hsrt⟩
    rw [symCmp_ne_gt]
    show ¬ _ < _ ↔ ¬ (Obj.atom .guid).key _ < (Obj.atom .guid).key _
    rw [key_guid x he j hj, key_guid x he i hi,
      symKey_lt_iff _ _ (by
        have : b.size = n.toNat * 16 := hwf
        rw [Array.length_toList, Array.length_toList]
        show (b.extract _ _).size = (b.extract _ _).size
        simp only [ByteArray.size_extract]; omega)]
  all_goals rw [he] at hwf; simp [Enc.WF] at hwf

theorem sortsAsc_guid : SortsAsc (.atom .guid) := sortsAsc_atom .guid grade_guid

/-! ## The symbol: `gradeSyms` and `gradeIds` by the stored bytes -/

/-- Row `i` of a symbol column that `Enc.get` decodes from valid UTF-8 bytes `s`: its `Obj.key` is `s`'s symbol
    key, the decode-then-`toUTF8` round trip returning the bytes. -/
theorem key_symAt {n : USize} (x : Arr .symbol n) {i : Nat} (hi : i < n.toNat) {s : ByteArray}
    (hs : s.IsValidUTF8) (hg : Enc.get .symbol n x.enc i = some (.symbol ((String.fromUTF8? s).getD ""))) :
    (Obj.atom .symbol).key (x.get ⟨i, hi⟩) = s.data.toList.map (·.toNat + 1) ++ [0] := by
  rw [Arr.get_ne _ _ (by decide), hg]
  simp only [Option.bind_some, Carrier.of?, Option.getD_some, Obj.key, String.fromUTF8?, dif_pos hs]
  rfl

/-- **`gradeSyms` sorts a `.syms` column by `Obj.lt`**, stable. -/
theorem grade_syms {n : USize} (x : Arr .symbol n) {blob : ByteArray} {offs : Array Nat}
    (he : x.enc = .syms blob offs) : ∃ g, gradeColumn .symbol false n x.enc = some (.bytes g) ∧
      (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom .symbol) (n := n) x (· < ·)) := by
  have hwf := x.wf; rw [he] at hwf
  obtain ⟨hsz, -, hv⟩ := hwf
  have hs : offs.size - 1 = n.toNat := by omega
  have hk : ∀ i (hi : i < n.toNat), (Obj.atom .symbol).key (x.get ⟨i, hi⟩) =
      (Column.symKey blob offs i).data.toList.map (·.toNat + 1) ++ [0] := fun i hi =>
    key_symAt x hi (hv i hi) (by rw [he]; simp only [Enc.get, if_pos hi]; rfl)
  obtain ⟨hp, hsrt⟩ := range_mergeSort
    (le := fun i j => Column.symCmp (Column.symKey blob offs i) (Column.symKey blob offs j) != .gt)
    (fun _ _ _ => symLe_trans) (fun _ _ => symLe_total _ _) (offs.size - 1)
  rw [hs] at hp hsrt
  have hm : ∀ i ∈ (List.range n.toNat).mergeSort
      (fun i j => Column.symCmp (Column.symKey blob offs i) (Column.symKey blob offs j) != .gt), i < 2 ^ 64 :=
    fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) (usize_lt n)
  refine ⟨_, by rw [he]; rfl, ?_⟩
  simp only [Order.gradeSyms, Bool.false_eq_true, ↓reduceIte, hs]
  rw [ids_indices _ hm]
  refine ⟨hp, ascBy_of_le x _ (fun i j hi hj => ?_) hsrt⟩
  rw [symCmp_ne_gt]
  show ¬ _ < _ ↔ ¬ (Obj.atom .symbol).key _ < (Obj.atom .symbol).key _
  rw [hk j hj, hk i hi]

/-- Two byte strings whose symbol keys are each `≤` the other are equal. -/
theorem symLe_antisymm {x y : ByteArray} (h1 : (Column.symCmp x y != .gt) = true)
    (h2 : (Column.symCmp y x != .gt) = true) : x.data.toList = y.data.toList := by
  rw [symCmp_ne_gt] at h1 h2
  have e := List.le_antisymm (List.not_lt.1 h2) (List.not_lt.1 h1)
  have e' := List.append_cancel_right e
  exact ((List.map_inj_right fun a b h => UInt8.toNat_inj.1 (by simpa using h)).1 e').symm

/-- The entry at a member's first index is that member. -/
private theorem getElem_idxOf : ∀ (L : List Nat) (a : Nat) (h : L.idxOf a < L.length), L[L.idxOf a] = a
  | [], _, h => by simp at h
  | x :: L, a, h => by
    by_cases e : x = a
    · subst e; simp
    · have hb : (x == a) = false := by simpa using e
      have hi : (x :: L).idxOf a = L.idxOf a + 1 := by simp [List.idxOf_cons, hb]
      have h' : L.idxOf a < L.length := by rw [hi] at h; simpa using h
      simpa [hi] using getElem_idxOf L a h'

/-- A map with no repeat on a list is one-to-one on its members. -/
private theorem inj_of_nodup_map {β : Type} {f : Nat → β} : ∀ {l : List Nat}, (l.map f).Nodup →
    ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (by rw [e]; exact List.mem_map_of_mem hb') h.1
    · exact absurd (by rw [← e]; exact List.mem_map_of_mem ha') h.1
    · exact inj_of_nodup_map h.2 ha' hb' e

/-- **The rank `gradeIds` grades by is the symbols' order**: in `ord`, a stable sort of the `d` dictionary entries
    by their bytes, no two entries holding one string, entry `a` is placed no later than `b` exactly when its bytes
    are not after `b`'s. -/
theorem idxOf_le_iff {dict : ByteArray} {dof : Array Nat}
    (hnd : ((List.range (dof.size - 1)).map fun i => (Column.symKey dict dof i).data.toList).Nodup)
    {a b : Nat} (ha : a < dof.size - 1) (hb : b < dof.size - 1) :
    ((List.range (dof.size - 1)).mergeSort fun a b =>
        Column.symCmp (Column.symKey dict dof a) (Column.symKey dict dof b) != .gt).idxOf a ≤
      ((List.range (dof.size - 1)).mergeSort fun a b =>
        Column.symCmp (Column.symKey dict dof a) (Column.symKey dict dof b) != .gt).idxOf b ↔
      (Column.symCmp (Column.symKey dict dof a) (Column.symKey dict dof b) != .gt) = true := by
  obtain ⟨hp, hsrt⟩ := range_mergeSort
    (le := fun a b => Column.symCmp (Column.symKey dict dof a) (Column.symKey dict dof b) != .gt)
    (fun _ _ _ => symLe_trans) (fun _ _ => symLe_total _ _) (dof.size - 1)
  generalize (List.range (dof.size - 1)).mergeSort _ = L at hp hsrt
  have hma : a ∈ L := hp.mem_iff.2 (List.mem_range.2 ha)
  have hmb : b ∈ L := hp.mem_iff.2 (List.mem_range.2 hb)
  have hla := List.idxOf_lt_length_of_mem hma
  have hlb := List.idxOf_lt_length_of_mem hmb
  have hga : L[L.idxOf a] = a := getElem_idxOf L a hla
  have hgb : L[L.idxOf b] = b := getElem_idxOf L b hlb
  have hpw := List.pairwise_iff_getElem.1 hsrt
  constructor
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := (hpw _ _ hla hlb h).1; rwa [hga, hgb] at this
    · have : a = b := by rw [← hga, ← hgb]; simp only [h]
      subst this
      have := symLe_total (Column.symKey dict dof a) (Column.symKey dict dof a)
      simpa using this
  · intro h
    refine Nat.le_of_not_lt fun hlt => ?_
    have h2 := (hpw _ _ hlb hla hlt).1
    rw [hga, hgb] at h2
    have e := symLe_antisymm h h2
    have hab : a = b := inj_of_nodup_map (f := fun i => (Column.symKey dict dof i).data.toList) hnd (List.mem_range.2 ha) (List.mem_range.2 hb) e
    subst hab
    exact Nat.lt_irrefl _ hlt

/-- **`gradeIds` sorts an `.enum` column by `Obj.lt`**, stable. -/
theorem grade_ids {n : USize} (x : Arr .symbol n) {dict : ByteArray} {dof : Array Nat} {ids' : ByteArray}
    (he : x.enc = .enum dict dof ids') : ∃ g, gradeColumn .symbol false n x.enc = some (.bytes g) ∧
      (ids g).Perm (List.range n.toNat) ∧ (ids g).Pairwise (ascBy (.atom .symbol) (n := n) x (· < ·)) := by
  have hwf := x.wf; rw [he] at hwf
  obtain ⟨-, -, hin, hnd, hv⟩ := hwf
  let w := Column.idWidth dof
  let ord := (List.range (dof.size - 1)).mergeSort fun a b =>
    Column.symCmp (Column.symKey dict dof a) (Column.symKey dict dof b) != .gt
  let rank (i : Nat) : Nat := ord.idxOf (Column.idAt ids' w i)
  have hk : ∀ i (hi : i < n.toNat), (Obj.atom .symbol).key (x.get ⟨i, hi⟩) =
      (Column.symKey dict dof (Column.idAt ids' w i)).data.toList.map (·.toNat + 1) ++ [0] := fun i hi =>
    key_symAt x hi (hv _ (hin i hi)) (by rw [he]; simp only [Enc.get, if_pos hi]; rfl)
  obtain ⟨hp, hsrt⟩ := range_mergeSort (le := fun i j => decide (rank i ≤ rank j))
    (fun _ _ _ h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) n.toNat
  have hm : ∀ i ∈ (List.range n.toNat).mergeSort (fun i j => decide (rank i ≤ rank j)), i < 2 ^ 64 :=
    fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) (usize_lt n)
  refine ⟨_, by rw [he]; rfl, ?_⟩
  simp only [Order.gradeIds, Bool.false_eq_true, ↓reduceIte]
  rw [ids_indices _ hm]
  refine ⟨hp, ascBy_of_le x _ (fun i j hi hj => ?_) hsrt⟩
  rw [decide_eq_true_iff, idxOf_le_iff hnd (hin i hi) (hin j hj), symCmp_ne_gt]
  show ¬ _ < _ ↔ ¬ (Obj.atom .symbol).key _ < (Obj.atom .symbol).key _
  rw [hk j hj, hk i hi]

/-- **The symbol sorts stably by `Obj.lt`**, on both of its encodings. -/
theorem sortsAsc_symbol : SortsAsc (.atom .symbol) := sortsAsc_atom .symbol fun x => by
  cases he : x.enc
  case syms blob offs => exact he ▸ grade_syms x he
  case enum dict dof ids' => exact he ▸ grade_ids x he
  all_goals have hwf := x.wf; rw [he] at hwf; simp [Enc.WF, QAtomicType.width] at hwf

/-! ## Arrays and sums: `sortSide`, a side sorted at positions picked whole -/

theorem pickShared_small : (B : Obj) → {s : USize} → (x : Vals B s) → (i : ByteArray) → (k : USize) →
    (h : len i = k.toNat) → x.Small → (Vals.pickShared B x i k h).Small
  | .atom _, _, _, _, _, _, _ => trivial
  | .prod a b, _, x, i, k, h, hx => ⟨pickShared_small a x.1 i k h hx.1, pickShared_small b x.2 i k h hx.2⟩
  | .arr _, _, _, _, _, _, hx => hx
  | .sum _ _, _, _, _, _, _, hx => hx

/-- **`Vals.pickShared` read back**: row `q` is `x`'s row `i[q]`, at every side, wherever that is a row. -/
theorem pickShared_row (B : Obj) {s : USize} (x : Vals B s) (i : ByteArray) (k : USize)
    (h : len i = k.toNat) (q : Fin k.toNat) (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < s.toNat) :
    (Vals.pickShared B x i k h).row q = x.row ⟨_, hin⟩ := by
  induction B generalizing s with
  | atom t => rw [Vals.pickShared, Vals.row_atom, Vals.row_atom]; exact pickArr_get ⟨_, x⟩ i k h q hin
  | prod a b iha ihb =>
    show (Vals.row (Vals.pickShared a x.1 i k h) q, Vals.row (Vals.pickShared b x.2 i k h) q) =
      (Vals.row x.1 ⟨_, hin⟩, Vals.row x.2 ⟨_, hin⟩)
    rw [iha, ihb]
  | arr b _ =>
    obtain ⟨_, lo, hi, _⟩ := x
    simp only [Vals.pickShared, Vals.row, pickArr_get ⟨_, lo⟩ i k h q hin, pickArr_get ⟨_, hi⟩ i k h q hin]
  | sum a b _ _ =>
    obtain ⟨_, _, tag, idx, _, _⟩ := x
    simp only [Vals.pickShared, Vals.row, pickArr_get ⟨_, tag⟩ i k h q hin, pickArr_get ⟨_, idx⟩ i k h q hin]

/-- **`sortSide` sorts by the values its rows read**: row `r` of `q` reading `f r`, `x`'s row at `ps[r]`, the
    answer is ascending in `f` by `Obj.lt`, rows of one key in `R` order — given that `B` sorts by `Obj.lt`. -/
theorem sortSide_asc {B : Obj} (hB : SortsAsc B) {s : USize} (x : Vals B s) (hx : x.Small) (hs : 0 < s.toNat)
    (ps q : ByteArray) (hq : len q < USize.size) (hps : ∀ r ∈ ids q, r < len ps ∧ (ids ps).getD r 0 < s.toNat)
    (R : Nat → Nat → Prop) (hR : (ids q).Pairwise R) (f : Nat → B.El)
    (hf : ∀ r ∈ ids q, ∀ h : (ids ps).getD r 0 < s.toNat, f r = x.row ⟨_, h⟩) :
    (ids (sortSide x (fun v r => (B.sortByC v r).1) ps q)).Pairwise fun i j =>
      B.lt (f i) (f j) ∨ B.key (f i) = B.key (f j) ∧ R i j := by
  have hm : ((len q).toUSize).toNat = len q := USize.toNat_ofNat_of_lt' hq
  unfold sortSide
  rw [dif_pos ⟨hs, hq⟩]
  have hg := ids_gather8 fun t ht => (hps t ht).1
  have hRr : (List.range (len q)).Pairwise fun a b => R ((ids q).getD a 0) ((ids q).getD b 0) := by
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.getElem_range, List.length_range] at ha hb ⊢
    rw [len_eq_ids] at ha hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hb, Option.getD_some, Option.getD_some]
    exact List.pairwise_iff_getElem.1 hR a b ha hb hab
  obtain ⟨hperm, hsrt⟩ := hB (Vals.pickShared B x (gather 8 ps q) (len q).toUSize (by rw [gather_len]; exact hm.symm))
    (pickShared_small B x _ _ _ hx) (tilLongs (len q).toUSize) (by rw [len_tilLongs, hm]; exact hq)
    (fun t ht => by rw [ids_tilLongs] at ht; exact List.mem_range.1 ht) _ (by rw [ids_tilLongs, hm]; exact hRr)
  have hgr : ∀ t ∈ ids (B.sortBy (Vals.pickShared B x (gather 8 ps q) (len q).toUSize
      (by rw [gather_len]; exact hm.symm)) (tilLongs (len q).toUSize)), t < len q := fun t ht => by
    have := hperm.mem_iff.1 ht; rw [ids_tilLongs, hm] at this; exact List.mem_range.1 this
  have hrow : ∀ a (ha : a < ((len q).toUSize).toNat), (Vals.pickShared B x (gather 8 ps q) (len q).toUSize
      (by rw [gather_len]; exact hm.symm)).row ⟨a, ha⟩ = f ((ids q).getD a 0) := fun a ha => by
    have hal : a < (ids q).length := by rw [← len_eq_ids, ← hm]; exact ha
    have hmem : (ids q)[a]'hal ∈ ids q := List.getElem_mem hal
    have hl2 : a < (ids (gather 8 ps q)).length := by rw [hg, List.length_map]; exact hal
    have e1 : (Column.bitsAt (gather 8 ps q) (a * 8) 8).toNat = (ids ps).getD ((ids q)[a]'hal) 0 := by
      have := List.getElem_of_eq hg hl2; rw [List.getElem_map, ids_getElem hl2] at this; exact this
    have hin : (Column.bitsAt (gather 8 ps q) (a * 8) 8).toNat < s.toNat := by rw [e1]; exact (hps _ hmem).2
    have eq : (ids q).getD a 0 = (ids q)[a]'hal := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hal, Option.getD_some]
    rw [pickShared_row B x _ _ _ ⟨a, ha⟩ hin, eq, hf _ hmem (by rw [← e1]; exact hin)]
    exact congrArg x.row (Fin.ext e1)
  show (ids (gather 8 q (B.sortBy _ _))).Pairwise _
  rw [ids_gather8 hgr, List.pairwise_map]
  refine hsrt.imp_of_mem fun {a b} ha hb hab => ?_
  have hi : a < ((len q).toUSize).toNat := by rw [hm]; exact hgr a ha
  have hj : b < ((len q).toUSize).toNat := by rw [hm]; exact hgr b hb
  rcases hab hi hj with h | ⟨e, h⟩
  · rw [hrow a hi, hrow b hj] at h; exact .inl h
  · rw [hrow a hi, hrow b hj] at e; exact .inr ⟨e, h⟩

/-- A row `i` of `p` that `whereBits` of `g` keeps is `p`'s long `k` for a marked `k`. -/
theorem mem_where {p g : ByteArray} (hl : len p < USize.size) {i : Nat}
    (hi : i ∈ ids (gather 8 p (whereBits (len p).toUSize g))) :
    ∃ k, k < len p ∧ Column.bitAt g k = true ∧ i = (ids p).getD k 0 := by
  have hm : ((len p).toUSize).toNat = len p := USize.toNat_ofNat_of_lt' hl
  have hin : ∀ t ∈ ids (whereBits (len p).toUSize g), t < len p := fun t ht => by
    rw [(whereBits_ids _ g).1, List.mem_filter, List.mem_range, hm] at ht; exact ht.1
  rw [ids_gather8 hin, List.mem_map] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  rw [(whereBits_ids _ g).1, List.mem_filter, List.mem_range, hm] at hk
  exact ⟨k, hk.1, hk.2, rfl⟩

/-- `whereBits` of `g` keeps a sublist of `p`'s rows. -/
theorem where_sublist {p g : ByteArray} (hl : len p < USize.size) :
    (ids (gather 8 p (whereBits (len p).toUSize g))).Sublist (ids p) := by
  have hm : ((len p).toUSize).toNat = len p := USize.toNat_ofNat_of_lt' hl
  have hin : ∀ t ∈ ids (whereBits (len p).toUSize g), t < len p := fun t ht => by
    rw [(whereBits_ids _ g).1, List.mem_filter, List.mem_range, hm] at ht; exact ht.1
  have e : (List.range (len p)).map (fun t => (ids p).getD t 0) = ids p := by
    rw [len_eq_ids]; exact map_range_getD _
  rw [ids_gather8 hin, (whereBits_ids _ g).1, hm]
  exact (List.filter_sublist.map _).trans (by rw [e]; exact List.Sublist.refl _)


/-- **A sum sorts by its tag, then by its side's own order**: `inl` rows first, each side by `sortSide`. -/
theorem sortsAsc_sum {a b : Obj} (ha : SortsAsc a) (hb : SortsAsc b) : SortsAsc (.sum a b) := by
  intro n c hc p hl hp R hR
  refine ⟨sortBy_permutes _ _ p hl, ?_⟩
  obtain ⟨l, r, tag, idx, x, y⟩ := c
  obtain ⟨hl63, hr63, hx, hy⟩ := hc
  have hm : ((len p).toUSize).toNat = len p := USize.toNat_ofNat_of_lt' hl
  have hcl : ∀ {g : ByteArray}, len (gather 8 p (whereBits (len p).toUSize g)) < USize.size := fun {g} => by
    rw [len_eq_ids]; exact Nat.lt_of_le_of_lt (where_sublist hl).length_le (by rw [← len_eq_ids]; exact hl)
  let tb := tagBits (pickArr .boolean ⟨n, tag⟩ p (len p).toUSize hm.symm)
  let ps := longsOf (place (A := a) (B := b) ⟨l, r, tag, idx, x, y⟩ ((l.toNat : Int) - 1) ((r.toNat : Int) - l.toNat) 0 0)
  -- a kept row: a row of `p`, its tag the side's, its position `Vals.row`'s
  have hside : ∀ (s : Bool) {g : ByteArray}, (∀ k < len p, Column.bitAt g k = true → Column.bitAt tb k = s) →
      ∀ i ∈ ids (gather 8 p (whereBits (len p).toUSize g)), ∃ hi : i < n.toNat, tag.get ⟨i, hi⟩ = s ∧
        i < len ps ∧ (ids ps).getD i 0 = min (max (idx.get ⟨i, hi⟩).toInt 0).toNat ((if s then r.toNat else l.toNat) - 1) := by
    intro s g hg i hi
    obtain ⟨k, hk, hgk, rfl⟩ := mem_where hl hi
    have hkl : k < (ids p).length := by rw [← len_eq_ids]; exact hk
    have hpk : (ids p).getD k 0 = (ids p)[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl, Option.getD_some]
    have hin : (ids p)[k] < n.toNat := hp _ (List.getElem_mem hkl)
    have ht := hg k hk hgk
    rw [show k = (⟨k, by rw [hm]; exact hk⟩ : Fin ((len p).toUSize).toNat).1 from rfl, pickArr_tag_bit,
      dif_pos (by rw [← ids_getElem hkl]; exact hin)] at ht
    rw [hpk]
    have htag : tag.get ⟨(ids p)[k], hin⟩ = s := by rw [← ht]; congr 1; exact Fin.ext (ids_getElem hkl)
    have hlen : (ids p)[k] < len ps := by rw [len_longsOf]; exact hin
    refine ⟨hin, htag, hlen, ?_⟩
    have hpl : (ids p)[k] < (ids ps).length := by rw [← len_eq_ids]; exact hlen
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl, Option.getD_some, ids_getElem hpl,
      longsOf_get _ hin, place_get _ hl63 hr63]
    simp only [htag]
    have h1 : l.toNat < 2 ^ 63 := hl63
    have h2 : r.toNat < 2 ^ 63 := hr63
    have h3 : UInt64.size = 2 ^ 64 := rfl
    rw [UInt64.toNat_ofNat_of_lt' (by cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]
  have hL := hside false fun k hk h => by rw [notBits_bitAt _ _ (by rw [hm]; exact hk)] at h; simpa using h
  have hRt := hside true fun k _ h => h
  simp only [Obj.sortBy, Obj.sortByC, dif_pos hl]
  rw [ids_concat2 (sortSide_size8 _ _ _ _ (gather_size8 _ _)), List.pairwise_append]
  -- the rows of one side, in its own order
  have side : ∀ {B : Obj} (hB : SortsAsc B) {s : USize} (v : Vals B s), v.Small → ∀ (t : Bool) (g : ByteArray)
      (inj : B.El → (Obj.sum a b).El), (∀ u w, (Obj.sum a b).lt (inj u) (inj w) ↔ B.lt u w) →
      (∀ u, (Obj.sum a b).key (inj u) = (if t then 1 else 0) :: B.key u) →
      (∀ i ∈ ids (gather 8 p (whereBits (len p).toUSize g)), ∃ hi : i < n.toNat, tag.get ⟨i, hi⟩ = t ∧
        i < len ps ∧ (ids ps).getD i 0 = min (max (idx.get ⟨i, hi⟩).toInt 0).toNat (s.toNat - 1)) →
      (∀ (i : Nat) (hi : i < n.toNat), tag.get ⟨i, hi⟩ = t → Vals.row (A := .sum a b) ⟨l, r, tag, idx, x, y⟩ ⟨i, hi⟩ =
        inj (if h : 0 < s.toNat then v.row ⟨min (max (idx.get ⟨i, hi⟩).toInt 0).toNat (s.toNat - 1), by omega⟩
          else B.dflt)) →
      (ids (sortSide v (fun v r => (B.sortByC v r).1) ps (gather 8 p (whereBits (len p).toUSize g)))).Pairwise
        (ascBy (.sum a b) ⟨l, r, tag, idx, x, y⟩ R) := by
    intro B hB s v hv t g inj hlt hkey hmem hrow
    have hsub := List.Pairwise.sublist (where_sublist (g := g) hl) hR
    have hperm := sortSide_perm v (fun v r => (B.sortByC v r).1) (fun v r hr => sortBy_permutes B v r hr) ps
      (gather 8 p (whereBits (len p).toUSize g))
    by_cases hs : 0 < s.toNat
    · let f (i : Nat) : B.El := if h : (ids ps).getD i 0 < s.toNat then v.row ⟨_, h⟩ else B.dflt
      have hS := sortSide_asc hB v hv hs ps _ hcl (fun i hi => by
          obtain ⟨_, _, h1, h2⟩ := hmem i hi; exact ⟨h1, by rw [h2]; omega⟩) R hsub f
        (fun i _ h => dif_pos h)
      refine hS.imp_of_mem fun {i j} hi hj hij hi' hj' => ?_
      obtain ⟨_, ti, _, pi⟩ := hmem i (hperm.mem_iff.1 hi)
      obtain ⟨_, tj, _, pj⟩ := hmem j (hperm.mem_iff.1 hj)
      have fi : Vals.row (A := .sum a b) ⟨l, r, tag, idx, x, y⟩ ⟨i, hi'⟩ = inj (f i) := by
        rw [hrow i hi' ti, dif_pos hs]; simp only [f, pi]; rw [dif_pos (by omega)]
      have fj : Vals.row (A := .sum a b) ⟨l, r, tag, idx, x, y⟩ ⟨j, hj'⟩ = inj (f j) := by
        rw [hrow j hj' tj, dif_pos hs]; simp only [f, pj]; rw [dif_pos (by omega)]
      show Obj.lt _ (Vals.row _ _) (Vals.row _ _) ∨ Obj.key _ (Vals.row _ _) = Obj.key _ (Vals.row _ _) ∧ R i j
      rw [fi, fj, hlt, hkey, hkey]
      rcases hij with h | ⟨e, h⟩
      · exact .inl h
      · exact .inr ⟨by rw [e], h⟩
    · unfold sortSide
      rw [dif_neg fun h => hs h.1]
      refine hsub.imp_of_mem fun {i j} hi hj hij hi' hj' => .inr ⟨?_, hij⟩
      obtain ⟨_, ti, _, _⟩ := hmem i hi
      obtain ⟨_, tj, _, _⟩ := hmem j hj
      show Obj.key _ (Vals.row _ _) = Obj.key _ (Vals.row _ _)
      rw [hrow i hi' ti, hrow j hj' tj, dif_neg hs, dif_neg hs]
  refine ⟨side ha x hx false _ Sum.inl (Obj.lt_inl a b) (fun _ => rfl) (fun i hi => by simpa using hL i hi)
      (fun i hi ht => ?_),
    side hb y hy true _ Sum.inr (Obj.lt_inr a b) (fun _ => rfl) (fun i hi => by simpa using hRt i hi)
      (fun i hi ht => ?_), ?_⟩
  · simp only [Vals.row, ht, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [Vals.row, ht, ↓reduceIte]; rfl
  · intro i hi j hj hi' hj'
    have pl := sortSide_perm x (fun v r => (a.sortByC v r).1) (fun v r hr => sortBy_permutes a v r hr) ps
      (gather 8 p (whereBits (len p).toUSize (Ew.notBits (len p).toUSize tb)))
    have pr := sortSide_perm y (fun v r => (b.sortByC v r).1) (fun v r hr => sortBy_permutes b v r hr) ps
      (gather 8 p (whereBits (len p).toUSize tb))
    obtain ⟨_, ti, -⟩ := hL i (pl.mem_iff.1 hi)
    obtain ⟨_, tj, -⟩ := hRt j (pr.mem_iff.1 hj)
    refine .inl ?_
    show Obj.lt _ (Vals.row _ _) (Vals.row _ _)
    simp only [Vals.row, ti, tj]
    exact Obj.lt_inl_inr a b _ _
/-! ## Every side whose atoms qlean orders

A `.general` atom is left out: qlean states no order on it (`orderKind .general = none`, `Obj.key` keys it `[]`),
and its rows sort by `codes`, an order of one call. -/

/-- `A` holds no `.general` atom: each of its atoms is one qlean's sort kernels order. -/
def _root_.LeetQ.Rel.Obj.Ordered : Obj → Prop
  | .atom t => t ≠ .general
  | .prod a b => a.Ordered ∧ b.Ordered
  | .arr b => b.Ordered
  | .sum a b => a.Ordered ∧ b.Ordered

/-- **Every atom but `.general` sorts stably by `Obj.lt`.** -/
theorem sortsAsc_ordered_atom {t : QAtomicType} (h : t ≠ .general) : SortsAsc (.atom t) := by
  cases t
  case boolean => exact sortsAsc_boolean
  case symbol => exact sortsAsc_symbol
  case guid => exact sortsAsc_guid
  case general => exact absurd rfl h
  all_goals exact sortsAsc_num rfl (by decide)

/-- **Every ordered side sorts stably by `Obj.lt`**, given that an array of a side that does, does: the LSD
    passes of `Obj.sortByC` at `.arr`, the open obligation `harr`. -/
theorem sortsAsc_ordered (harr : ∀ b, SortsAsc b → SortsAsc (.arr b)) :
    ∀ A : Obj, A.Ordered → SortsAsc A
  | .atom _, h => sortsAsc_ordered_atom h
  | .prod a b, ⟨ha, hb⟩ => sortsAsc_prod (sortsAsc_ordered harr a ha) (sortsAsc_ordered harr b hb)
  | .arr b, h => harr b (sortsAsc_ordered harr b h)
  | .sum a b, ⟨ha, hb⟩ => sortsAsc_sum (sortsAsc_ordered harr a ha) (sortsAsc_ordered harr b hb)

#print axioms sortsAsc_ordered
#print axioms sortsAsc_symbol
#print axioms sortsAsc_guid
#print axioms sortBy_asc
#print axioms sortsAsc_prod
#print axioms sortsAsc_num
#print axioms sortsAsc_boolean
#print axioms sortsAsc_sum

end LeetQ.Rel.Alg
