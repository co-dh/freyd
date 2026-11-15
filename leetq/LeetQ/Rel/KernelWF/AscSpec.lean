/-
  `Obj.sortBy` realises q's `asc` order `Obj.lt` (`ObjOrder.lean`): at every atom a kernel grades by its key
  (`orderKind t = some k`, the boolean included) the answer lists the rows ascending by `Obj.lt`, ties in the
  order they came in, and a product of two such sides sorts lexicographically.
-/
import LeetQ.Rel.KernelWF.SortSpec
import LeetQ.Rel.KernelWF.PickSpec
import LeetQ.Rel.KernelWF.RazeSpec
import LeetQ.Rel.ObjOrder
import QLean.Verify.Grade

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- Row `i` of `c` comes no later than row `j` in q's `asc` order, rows of one key ordered by `R`. -/
def ascBy (A : Obj) {n : USize} (c : Vals A n) (R : Nat → Nat → Prop) (i j : Nat) : Prop :=
  ∀ (hi : i < n.toNat) (hj : j < n.toNat), A.lt (c.row ⟨i, hi⟩) (c.row ⟨j, hj⟩) ∨
    (A.key (c.row ⟨i, hi⟩) = A.key (c.row ⟨j, hj⟩) ∧ R i j)

/-- `sortBy` at `A` sorts stably by `Obj.lt`: refining a `p` listed in `R` order, it answers `p` again, ascending
    by `Obj.lt`, rows of one key still in `R` order. -/
def SortsAsc (A : Obj) : Prop :=
  ∀ {n : USize} (c : Vals A n) (p : ByteArray), len p < USize.size → (∀ i ∈ ids p, i < n.toNat) →
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
  intro n c p hl hp R hR
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
  intro n c p hl hp R hR
  have hsb : (Obj.prod a b).sortBy c p = a.sortBy c.1 (b.sortBy c.2 p) := rfl
  obtain ⟨p1, s1⟩ := hb c.2 p hl hp R hR
  have hl1 : len (b.sortBy c.2 p) < USize.size := by rw [len_eq_ids, p1.length_eq, ← len_eq_ids]; exact hl
  obtain ⟨p2, s2⟩ := ha c.1 _ hl1 (fun i hi => hp i (p1.mem_iff.1 hi)) _ s1
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
theorem sortBy_asc {A : Obj} (hA : SortsAsc A) {n : USize} (c : Vals A n) (p : ByteArray)
    (hl : len p < USize.size) (hp : ∀ i ∈ ids p, i < n.toNat) :
    (ids (A.sortBy c p)).Pairwise fun i j => ∀ (hi : i < n.toNat) (hj : j < n.toNat),
      ¬ A.lt (c.row ⟨j, hj⟩) (c.row ⟨i, hi⟩) :=
  (hA c p hl hp (fun _ _ => True) (List.pairwise_iff_getElem.2 fun _ _ _ _ _ => trivial)).2.imp
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

#print axioms sortBy_asc
#print axioms sortsAsc_prod
#print axioms sortsAsc_num
#print axioms sortsAsc_boolean

end LeetQ.Rel.Alg
