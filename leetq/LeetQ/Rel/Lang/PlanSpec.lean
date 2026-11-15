import LeetQ.Rel.Lang.EmitC

/-! # A builder's plan means its def (`doc/rel-native-design.md` §13, stage 1b)

`Builds abi fs gs b rs out`: the instructions `b` appends, run after the registers `rs`, answer `out`. One lemma per
builder primitive — `emit1` (so `lit`), `emit` (so `call`), `ite` — and one per instruction run (`runI_call`) say
what each does; a builder's theorem is a rewrite through them, never an unfolding of `runB`. -/

namespace LeetQ.Rel.Lang.Plan

open QLean QLean.Kernel

/-! ### Reading registers -/

/-- `Except`'s bind on a success, which `simp` does not reduce by itself. -/
theorem ok_bind {α β : Type} (a : α) (f : α → Except String β) : (Except.ok a >>= f) = f a := rfl

/-- What `emit` appends: `i`, defining the next `nres` registers. -/
theorem emit_run (i : Instr) (nres : Nat) (is : Array Instr) (n : Nat) (fg : Array Fun × Array Fun) :
    (emit i nres).run (is, n, fg) = .ok ((List.range' n nres).toArray, is.push i, n + nres, fg) := rfl

theorem reg_of {rs : Array Val} {a : Nat} {v : Val} (h : rs[a]? = some v) (who : String) :
    reg rs who a = .ok v := by unfold reg; rw [h]; rfl

theorem mapM_ok_length {α β : Type} {f : α → Except String β} :
    ∀ (l : List α) {bs : List β}, l.mapM f = .ok bs → bs.length = l.length
  | [], bs, h => by rw [List.mapM_nil] at h; injection h with h; subst h; rfl
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      cases hl : l.mapM f with
      | error e => rw [ha, hl] at h; cases h
      | ok cs => rw [ha, hl] at h; injection h with h; subst h; simp [mapM_ok_length l hl]

theorem mapM_ok_size {α β : Type} {f : α → Except String β} {as : Array α} {bs : Array β}
    (h : as.mapM f = .ok bs) : bs.size = as.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : as.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok cs => rw [hl] at h; injection h with h; subst h; simp [mapM_ok_length _ hl]

/-- The registers `xs` defined after `rs`, read back by their numbers. -/
theorem mapM_reg_range (rs xs : Array Val) (who : String) :
    (List.range' rs.size xs.size).toArray.mapM (reg (rs ++ xs) who) = .ok xs := by
  have key : ∀ (l : List Val) k, (∀ i (h : i < l.length), (rs ++ xs)[k + i]? = some l[i]) →
      (List.range' k l.length).mapM (reg (rs ++ xs) who) = .ok l := by
    intro l; induction l with
    | nil => intro k _; rfl
    | cons a l ih =>
      intro k h
      have h0 : (rs ++ xs)[k]? = some a := by simpa using h 0 (by simp)
      have h1 : ∀ i (hi : i < l.length), (rs ++ xs)[k + 1 + i]? = some l[i] := fun i hi => by
        rw [show k + 1 + i = k + (i + 1) by omega]; simpa using h (i + 1) (by simp; omega)
      rw [List.length_cons, List.range'_succ, List.mapM_cons, reg_of h0, ih (k + 1) h1]; rfl
  rw [List.mapM_toArray, ← Array.length_toList (xs := xs), key xs.toList rs.size ?_]
  · rfl
  · intro i h; rw [Array.getElem?_append_right (by omega)]; simp

/-! ### The primitives -/

/-- `b`, built after the registers `rs`, appends instructions which, run after `rs` and any writes, define the
    registers `xs` and write nothing, and answers registers holding `out`. -/
def Builds (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) (b : Bld (Array Nat))
    (rs out : Array Val) : Prop :=
  ∀ is fg, ∃ js xs r fg', b.run (is, rs.size, fg) = .ok (r, is ++ js, (rs ++ xs).size, fg') ∧
    (∀ ws, runB abi fs gs js.toList rs ws = .ok (rs ++ xs, ws)) ∧ ∀ who, r.mapM (reg (rs ++ xs) who) = .ok out

variable {abi : String → Option Kernel} {fs : Array Sem} {gs : Array (Array Val)}

/-- A kernel call: its arguments read, its pure answer appended. -/
theorem runI_call {sym : String} {as : Array Nat} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {vs out rs : Array Val} {ws : Writes} (hk : abi sym = some k) (hf : k.run = .inl f)
    (ha : as.mapM (reg rs sym) = .ok vs) (ho : f vs = .ok out) (hs : out.size = k.res.size) :
    runI abi fs gs (.call sym as) rs ws = .ok (rs ++ out, ws) := by
  simp [runI, hk, hf, ha, ho, hs, ok_bind, pure, Except.pure]

/-- One register defined by `i`, then `k` on it. `lit v` is `emit1 (.lit v)`. -/
theorem Builds.emit1 {i : Instr} {v : Val} {k : Nat → Bld (Array Nat)} {rs out : Array Val}
    (hi : ∀ ws, runI abi fs gs i rs ws = .ok (rs.push v, ws)) (hk : Builds abi fs gs (k rs.size) (rs.push v) out) :
    Builds abi fs gs (Plan.emit1 i >>= k) rs out := by
  intro is fg
  obtain ⟨js, xs, r, fg', hr, hb, hm⟩ := hk (is.push i) fg
  refine ⟨#[i] ++ js, #[v] ++ xs, r, fg', ?_, fun ws => ?_, fun who => ?_⟩
  · show (k rs.size).run (is.push i, rs.size + 1, fg) = _
    rw [← Array.size_push (xs := rs) v, hr]; simp [← Array.append_assoc]
  · rw [Array.toList_append, show (#[i] : Array Instr).toList = [i] from rfl, List.singleton_append,
      runB.eq_2, hi]
    exact (hb ws).trans (by simp [← Array.append_assoc])
  · simpa [← Array.append_assoc] using hm who

/-- An instruction defining `out`, last. `call sym as nres` is `emit (.call sym as) nres`. -/
theorem Builds.emit {i : Instr} {nres : Nat} {rs out : Array Val}
    (hi : ∀ ws, runI abi fs gs i rs ws = .ok (rs ++ out, ws)) (hn : out.size = nres) :
    Builds abi fs gs (Plan.emit i nres) rs out := by
  intro is fg; subst hn
  refine ⟨#[i], out, (List.range' rs.size out.size).toArray, fg, ?_, fun ws => ?_, mapM_reg_range rs out⟩
  · show Except.ok ((List.range' rs.size out.size).toArray, is.push i, rs.size + out.size, fg) = _
    simp [← Array.append_assoc]
  · rw [show (#[i] : Array Instr).toList = [i] from rfl, runB.eq_2, hi]; rfl

/-- `if c then t else e`: the branch the bit in `c` names; the other must build, as many registers wide. -/
theorem Builds.ite {c : Nat} {bt : Bool} {t e : Bld (Array Nat)} {rs ot oe : Array Val}
    (hc : rs[c]? = some (.bit bt)) (ht : Builds abi fs gs t rs ot) (he : Builds abi fs gs e rs oe)
    (hs : ot.size = oe.size) : Builds abi fs gs (Plan.ite c t e) rs (if bt then ot else oe) := by
  intro is fg
  obtain ⟨jt, xt, rt, fg1, hrt, hbt, hmt⟩ := ht #[] fg
  obtain ⟨je, xe, re, fg2, hre, hbe, hme⟩ := he #[] fg1
  have st : ot.size = rt.size := mapM_ok_size (hmt "")
  have se : oe.size = re.size := mapM_ok_size (hme "")
  have ho : (if bt then ot else oe).size = rt.size := by cases bt <;> simp <;> omega
  refine ⟨#[.ite c jt.toList rt je.toList re], if bt then ot else oe, (List.range' rs.size rt.size).toArray, fg2,
    ?_, fun ws => ?_, fun who => ho ▸ mapM_reg_range rs _ who⟩
  · have hrs : rt.size = re.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, hrt, hre,
      ok_bind, pure_bind, bind_assoc]
    simp [ok_bind, hrs, emit_run, ← st, ho, ← Array.append_assoc]
  · rw [show (#[Instr.ite c jt.toList rt je.toList re] : Array Instr).toList = [.ite c jt.toList rt je.toList re]
      from rfl, runB.eq_2]
    cases bt <;> simp [runI, reg_of hc, hbt, hbe, hmt, hme, runB.eq_1, ok_bind, pure, Except.pure, Functor.map, Except.map]

/-! ### `Code.groupIds` -/

theorem toUSize_eq_iff {a b : Nat} (ha : a < USize.size) (hb : b < USize.size) :
    a.toUSize = b.toUSize ↔ a = b :=
  ⟨fun h => by
    rw [← USize.toNat_ofNat_of_lt' ha, ← USize.toNat_ofNat_of_lt' hb]; exact congrArg USize.toNat h,
   fun h => h ▸ rfl⟩

theorem push_keep {C rs : Array Val} {x : Val} (h4 : C.size ≤ rs.size) (hr : ∀ i < C.size, rs[i]? = C[i]?) :
    C.size ≤ (rs.push x).size ∧ ∀ i < C.size, (rs.push x)[i]? = C[i]? :=
  ⟨by simp; omega, fun i hi => by rw [Array.getElem?_push, if_neg (by omega)]; exact hr i hi⟩

theorem abiOf_decEq : abiOf "lean_usize_dec_eq" = some (kernel% USize.decEq) := by simp [abiOf, abi, List.find?]
theorem abiOf_groupIds : abiOf "qlean_sort_group_ids" = some (kernel% QLean.Kernel.Order.groupIds) := by
  simp [abiOf, abi, List.find?]
theorem abiOf_idGroups : abiOf "qlean_sort_id_groups" = some (kernel% QLean.Kernel.Order.idGroups) := by
  simp [abiOf, abi, List.find?]

/-- `groupIdsB.go` on lanes `ks`: `groupIds` at the first lane of the code's width, `idGroups` past the last. -/
theorem groupIdsB_go (c : Alg.Code) (hw : c.w < USize.size) (ks : List (Nat × Scan.Kind))
    (hks : ∀ p ∈ ks, p.1 < USize.size) (rs : Array Val) (h4 : (codeVals c).size ≤ rs.size)
    (hr : ∀ i < (codeVals c).size, rs[i]? = (codeVals c)[i]?) :
    Builds abiOf fs gs (groupIdsB.go 0 1 2 3 ks) rs
      (let g := match (ks.find? (·.1 == c.w)).map (·.2) with
        | some k => Order.groupIds k c.n c.b
        | none => Order.idGroups c.card.toUSize c.n c.w.toUSize c.b
       #[.bytes g.1, .bytes g.2]) := by
  have rd : ∀ {R : Array Val}, (codeVals c).size ≤ R.size → (∀ i < (codeVals c).size, R[i]? = (codeVals c)[i]?) →
      ∀ i (hi : i < (codeVals c).size), R[i]? = some (codeVals c)[i] := fun _ hr i hi => by
    rw [hr i hi]; simp [hi]
  induction ks generalizing rs with
  | nil =>
    rw [groupIdsB.go]
    have ha : #[2, 1, 0, 3].mapM (reg rs "qlean_sort_id_groups") =
        .ok #[.size c.card.toUSize, .size c.n, .size c.w.toUSize, .bytes c.b] := by
      rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
      rw [reg_of (rd h4 hr 2 (by simp [codeVals])), reg_of (rd h4 hr 1 (by simp [codeVals])), reg_of (rd h4 hr 0 (by simp [codeVals])),
        reg_of (rd h4 hr 3 (by simp [codeVals]))]; rfl
    exact Builds.emit (fun ws => runI_call abiOf_idGroups rfl ha rfl rfl) rfl
  | cons p ks ih =>
    obtain ⟨v, k⟩ := p
    have hv : v < USize.size := hks _ (List.mem_cons_self ..)
    have hks' : ∀ p ∈ ks, p.1 < USize.size := fun p hp => hks p (List.mem_cons_of_mem _ hp)
    rw [groupIdsB.go]
    refine Builds.emit1 (v := .size v.toUSize) (fun _ => rfl) ?_
    obtain ⟨h4₁, hr₁⟩ := push_keep (x := .size v.toUSize) h4 hr
    have ha : #[0, rs.size].mapM (reg (rs.push (.size v.toUSize)) "lean_usize_dec_eq") =
        .ok #[.size c.w.toUSize, .size v.toUSize] := by
      rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
      rw [reg_of (rd h4₁ hr₁ 0 (by simp [codeVals])), reg_of (Array.getElem?_push_size)]; rfl
    refine Builds.emit1 (v := .bit (decide (c.w.toUSize = v.toUSize))) (fun ws => by
      rw [Array.push_eq_append (as := rs.push (.size v.toUSize))]
      exact runI_call abiOf_decEq rfl ha rfl rfl) ?_
    obtain ⟨h4₂, hr₂⟩ := push_keep (x := .bit (decide (c.w.toUSize = v.toUSize))) h4₁ hr₁
    have key := Builds.ite (fs := fs) (gs := gs) (Array.getElem?_push_size)
      (show Builds abiOf fs gs (do Plan.call "qlean_sort_group_ids" #[← lit (Reg.put k), 1, 3] 2) _
          #[.bytes (Order.groupIds k c.n c.b).1, .bytes (Order.groupIds k c.n c.b).2] from by
        refine Builds.emit1 (v := Reg.put k) (fun _ => rfl) ?_
        obtain ⟨h4₃, hr₃⟩ := push_keep (x := Reg.put k) h4₂ hr₂
        have ha : #[(rs.push (.size v.toUSize) |>.push (.bit (decide (c.w.toUSize = v.toUSize)))).size, 1, 3].mapM
            (reg ((rs.push (.size v.toUSize) |>.push (.bit (decide (c.w.toUSize = v.toUSize)))).push (Reg.put k))
              "qlean_sort_group_ids") = .ok #[Reg.put k, .size c.n, .bytes c.b] := by
          rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
          rw [reg_of (Array.getElem?_push_size), reg_of (rd h4₃ hr₃ 1 (by simp [codeVals])),
            reg_of (rd h4₃ hr₃ 3 (by simp [codeVals]))]; rfl
        exact Builds.emit (fun ws => runI_call abiOf_groupIds rfl ha (by cases k <;> rfl) rfl) rfl)
      (ih hks' _ h4₂ hr₂) rfl
    by_cases h : c.w = v
    · subst h; simpa using key
    · have hne : decide (c.w.toUSize = v.toUSize) = false := by simp [toUSize_eq_iff hw hv, h]
      have hb : (v == c.w) = false := by simpa using Ne.symm h
      rw [hne] at key; simpa [List.find?, hne, hb] using key

/-- The lanes `groupIdsB` tests, found by width, are `laneKind`. -/
theorem lanes_find (w : Nat) :
    ((([1, 8, 16, 32, 64].filterMap fun v => (Alg.laneKind v).map (v, ·)).find? (·.1 == w)).map (·.2)) =
      Alg.laneKind w := by
  show (([(1, Scan.Kind.bit), (8, .u8), (16, .i16), (32, .i32), (64, .i64)] : List _).find? (·.1 == w)).map (·.2) = _
  unfold Alg.laneKind
  split <;> (try (simp_all [List.find?]; done))
  rename_i h1 h8 h16 h32 h64
  have hb : ∀ v, v ≠ w → (v == w) = false := fun v h => by simpa using h
  simp [List.find?, hb 1 (Ne.symm h1), hb 8 (Ne.symm h8), hb 16 (Ne.symm h16), hb 32 (Ne.symm h32),
    hb 64 (Ne.symm h64)]

/-- `groupIdsB` run on a code's registers answers `Code.groupIds` of that code. -/
theorem groupIdsB_builds (c : Alg.Code) (hw : c.w < USize.size) :
    Builds abiOf fs gs (groupIdsB 0 1 2 3) (codeVals c) #[.bytes c.groupIds.1, .bytes c.groupIds.2] := by
  have hl : ∀ p ∈ ([1, 8, 16, 32, 64].filterMap fun v => (Alg.laneKind v).map (v, ·)), p.1 < USize.size := by
    intro p hp
    have : p = (1, .bit) ∨ p = (8, .u8) ∨ p = (16, .i16) ∨ p = (32, .i32) ∨ p = (64, .i64) := by
      simpa [Alg.laneKind] using hp
    rcases USize.size_eq with hs | hs <;> rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [hs]
  have := groupIdsB_go (fs := fs) (gs := gs) c hw _ hl (codeVals c) (Nat.le_refl _) (fun _ _ => rfl)
  rw [lanes_find] at this
  exact this

end LeetQ.Rel.Lang.Plan
