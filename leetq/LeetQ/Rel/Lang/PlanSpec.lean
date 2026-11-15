import LeetQ.Rel.Lang.EmitC

/-! # A builder's plan means its def (`doc/rel-native-design.md` §13, stage 1b)

`Builds abi fg fg' b rs out`: `b`, built while the plan's functions and globals grow from `fg` to `fg'`, appends
instructions which, run after the registers `rs` under any meaning of `fg'` (`Env`), answer `out`. One lemma per
builder primitive — `emit1` (so `lit`), `emit` (so `call`, `apply`), `ite`, `defFun`, `global` — and one per
instruction run (`runI_call`, `runI_apply`) say what each does; a builder's theorem is a rewrite through them, never
an unfolding of `runB`. -/

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

/-! ### What the plan's functions and globals mean -/

/-- `fs` means the functions `F`: each entry is its function's meaning over the entries before it, as `sems` makes. -/
def FEnv (abi : String → Option Kernel) (fs : Array Sem) (F : Array Fun) : Prop :=
  ∀ i (h : i < F.size), fs[i]? = some (F[i].sem abi (fs.extract 0 i))

/-- `fs`, `gs` mean the functions and globals `fg`: a global holds what its body answers, writing nothing, under
    some meaning of the functions — any, as a built body answers the same under each. -/
def Env (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) (fg : Array Fun × Array Fun) :
    Prop :=
  FEnv abi fs fg.1 ∧ ∀ i (h : i < fg.2.size), ∃ v, gs[i]? = some v ∧
    ∃ fs', FEnv abi fs' fg.1 ∧ ∀ ws, fg.2[i].sem abi fs' (gs.extract 0 i) #[] ws = .ok (v, ws)

variable {abi : String → Option Kernel}

theorem FEnv.mono {fs : Array Sem} {F a : Array Fun} (h : FEnv abi fs (F ++ a)) : FEnv abi fs F := fun i hi => by
  have := h i (by simp; omega); rwa [Array.getElem_append_left hi] at this

/-- A function's meaning reads only the entries before it, so a prefix of `fs` means a prefix of the functions. -/
theorem FEnv.extract {fs : Array Sem} {F a : Array Fun} (h : FEnv abi fs (F ++ a)) :
    FEnv abi (fs.extract 0 F.size) F := fun i hi => by
  have h1 := h i (by simp; omega)
  have hs : i < fs.size := by
    rcases Nat.lt_or_ge i fs.size with hs | hs
    · exact hs
    · rw [Array.getElem?_eq_none hs] at h1; cases h1
  rw [Array.getElem_append_left hi] at h1
  rw [Array.getElem?_extract, if_pos (by simp; omega), Array.extract_extract]
  simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using h1

/-- A prefix of the functions and globals, under any meaning `fs'` of those functions and globals `gs'` agreeing
    with `gs` on that prefix. -/
theorem Env.restrict {fs fs' : Array Sem} {gs gs' : Array (Array Val)} {F a G b : Array Fun}
    (h : Env abi fs gs (F ++ a, G ++ b)) (hf : FEnv abi fs' F) (hg : gs'.extract 0 G.size = gs.extract 0 G.size) :
    Env abi fs' gs' (F, G) := by
  refine ⟨hf, fun i hi => ?_⟩
  simp only at hi
  obtain ⟨v, hv, fs'', h1, h2⟩ := h.2 i (by simp; omega)
  have ex : ∀ x : Array (Array Val), (x.extract 0 G.size)[i]? = x[i]? := fun x => by
    rw [Array.getElem?_extract]; split
    · simp
    · rw [Array.getElem?_eq_none (by omega)]
  have e1 : gs'[i]? = gs[i]? := by rw [← ex gs', hg, ex gs]
  have e2 : gs'.extract 0 i = gs.extract 0 i := by
    have := congrArg (·.extract 0 i) hg; simpa [Array.extract_extract, Nat.min_eq_left (Nat.le_of_lt hi)] using this
  refine ⟨v, e1.trans hv, fs'', FEnv.mono h1, fun ws => ?_⟩
  rw [e2]; simpa [Array.getElem_append_left hi] using h2 ws

theorem Env.mono {fs : Array Sem} {gs : Array (Array Val)} {fg fg' : Array Fun × Array Fun}
    (h1 : ∃ a, fg'.1 = fg.1 ++ a) (h2 : ∃ a, fg'.2 = fg.2 ++ a) (h : Env abi fs gs fg') : Env abi fs gs fg := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  obtain rfl : fg' = (fg.1 ++ a, fg.2 ++ b) := Prod.ext ha hb
  exact h.restrict (FEnv.mono h.1) rfl

/-! ### The primitives -/

/-- `b`, built after the registers `rs` while the functions and globals grow from `fg` to `fg'`, appends
    instructions which, run after `rs` and any writes under any meaning of `fg'`, define the registers `xs` and write
    nothing, and answers registers holding `out`. -/
def Builds (abi : String → Option Kernel) (fg fg' : Array Fun × Array Fun) (b : Bld (Array Nat))
    (rs out : Array Val) : Prop :=
  (∃ a, fg'.1 = fg.1 ++ a) ∧ (∃ a, fg'.2 = fg.2 ++ a) ∧ ∀ is, ∃ js xs r,
    b.run (is, rs.size, fg) = .ok (r, is ++ js, (rs ++ xs).size, fg') ∧
    (∀ fs gs, Env abi fs gs fg' → ∀ ws, runB abi fs gs js.toList rs ws = .ok (rs ++ xs, ws)) ∧
    ∀ who, r.mapM (reg (rs ++ xs) who) = .ok out

variable {fs : Array Sem} {gs : Array (Array Val)}

/-- A kernel call: its arguments read, its pure answer appended. -/
theorem runI_call {sym : String} {as : Array Nat} {k : Kernel} {f : Array Val → Except String (Array Val)}
    {vs out rs : Array Val} {ws : Writes} (hk : abi sym = some k) (hf : k.run = .inl f)
    (ha : as.mapM (reg rs sym) = .ok vs) (ho : f vs = .ok out) (hs : out.size = k.res.size) :
    runI abi fs gs (.call sym as) rs ws = .ok (rs ++ out, ws) := by
  simp [runI, hk, hf, ha, ho, hs, ok_bind, pure, Except.pure]

/-- A function application: its arguments read, its answer appended. -/
theorem runI_apply {f : Nat} {as : Array Nat} {g : Sem} {vs out rs : Array Val} {ws : Writes}
    (hf : fs[f]? = some g) (ha : as.mapM (reg rs s!"apply f{f}") = .ok vs) (ho : g gs vs ws = .ok (out, ws)) :
    runI abi fs gs (.apply f as) rs ws = .ok (rs ++ out, ws) := by
  simp [runI, hf, ha, ho, ok_bind, pure, Except.pure]

/-- Nothing built: `r` read. -/
theorem Builds.pure {fg : Array Fun × Array Fun} {r : Array Nat} {rs out : Array Val}
    (hm : ∀ who, r.mapM (reg rs who) = .ok out) : Builds abi fg fg (Pure.pure r) rs out :=
  ⟨⟨#[], by simp⟩, ⟨#[], by simp⟩, fun is => ⟨#[], #[], r, by simp only [Array.append_empty]; rfl,
    fun _ _ _ ws => by rw [Array.append_empty]; rfl, by simpa using hm⟩⟩

/-- One register defined by `i`, then `k` on it. `lit v` is `emit1 (.lit v)`. -/
theorem Builds.emit1 {fg fg' : Array Fun × Array Fun} {i : Instr} {v : Val} {k : Nat → Bld (Array Nat)}
    {rs out : Array Val} (hi : ∀ fs gs, Env abi fs gs fg' → ∀ ws, runI abi fs gs i rs ws = .ok (rs.push v, ws))
    (hk : Builds abi fg fg' (k rs.size) (rs.push v) out) : Builds abi fg fg' (Plan.emit1 i >>= k) rs out := by
  obtain ⟨h1, h2, hk⟩ := hk
  refine ⟨h1, h2, fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hb, hm⟩ := hk (is.push i)
  refine ⟨#[i] ++ js, #[v] ++ xs, r, ?_, fun fs gs hE ws => ?_, fun who => ?_⟩
  · show (k rs.size).run (is.push i, rs.size + 1, fg) = _
    rw [← Array.size_push (xs := rs) v, hr]; simp [← Array.append_assoc]
  · rw [Array.toList_append, show (#[i] : Array Instr).toList = [i] from rfl, List.singleton_append,
      runB.eq_2, hi fs gs hE]
    exact (hb fs gs hE ws).trans (by simp [← Array.append_assoc])
  · simpa [← Array.append_assoc] using hm who

/-- An instruction defining `o`, then `k` on its registers. `call`, `apply` are `emit`s. -/
theorem Builds.emit_bind {fg fg' : Array Fun × Array Fun} {i : Instr} {o : Array Val} {k : Array Nat → Bld (Array Nat)}
    {rs out : Array Val} (hi : ∀ fs gs, Env abi fs gs fg' → ∀ ws, runI abi fs gs i rs ws = .ok (rs ++ o, ws))
    (hk : Builds abi fg fg' (k (List.range' rs.size o.size).toArray) (rs ++ o) out) :
    Builds abi fg fg' (Plan.emit i o.size >>= k) rs out := by
  obtain ⟨h1, h2, hk⟩ := hk
  refine ⟨h1, h2, fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hb, hm⟩ := hk (is.push i)
  refine ⟨#[i] ++ js, o ++ xs, r, ?_, fun fs gs hE ws => ?_, fun who => ?_⟩
  · show (k _).run (is.push i, rs.size + o.size, fg) = _
    rw [show rs.size + o.size = (rs ++ o).size by simp, hr]; simp [← Array.append_assoc]
  · rw [Array.toList_append, show (#[i] : Array Instr).toList = [i] from rfl, List.singleton_append,
      runB.eq_2, hi fs gs hE]
    exact (hb fs gs hE ws).trans (by simp [← Array.append_assoc])
  · simpa [← Array.append_assoc] using hm who

/-- An instruction defining `out`, last. -/
theorem Builds.emit {fg : Array Fun × Array Fun} {i : Instr} {nres : Nat} {rs out : Array Val}
    (hi : ∀ fs gs, Env abi fs gs fg → ∀ ws, runI abi fs gs i rs ws = .ok (rs ++ out, ws)) (hn : out.size = nres) :
    Builds abi fg fg (Plan.emit i nres) rs out := by
  subst hn
  have := Builds.emit_bind (k := Pure.pure) hi (Builds.pure (mapM_reg_range rs out))
  rwa [bind_pure] at this

/-- `apply f(as)` of a function answering `o` on the arguments `vs`, then `k` on its registers. -/
theorem Builds.apply {fg fg' : Array Fun × Array Fun} {f : Nat} {as : Array Nat} {vs o : Array Val}
    {k : Array Nat → Bld (Array Nat)} {rs out : Array Val}
    (hf : ∀ fs gs, Env abi fs gs fg' → ∀ ws, ∃ g, fs[f]? = some g ∧ g gs vs ws = .ok (o, ws))
    (ha : as.mapM (reg rs s!"apply f{f}") = .ok vs)
    (hk : Builds abi fg fg' (k (List.range' rs.size o.size).toArray) (rs ++ o) out) :
    Builds abi fg fg' (Plan.apply f as o.size >>= k) rs out :=
  Builds.emit_bind (fun fs gs hE ws => let ⟨_, hg, ho⟩ := hf fs gs hE ws; runI_apply hg ha ho) hk

/-- `if c then t else e`: the branch the bit in `c` names; the other must build, as many registers wide. -/
theorem Builds.ite {fg fg1 fg2 : Array Fun × Array Fun} {c : Nat} {bt : Bool} {t e : Bld (Array Nat)}
    {rs ot oe : Array Val} (hc : rs[c]? = some (.bit bt)) (ht : Builds abi fg fg1 t rs ot)
    (he : Builds abi fg1 fg2 e rs oe) (hs : ot.size = oe.size) :
    Builds abi fg fg2 (Plan.ite c t e) rs (if bt then ot else oe) := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, ht⟩ := ht
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, he⟩ := he
  obtain ⟨jt, xt, rt, hrt, hbt, hmt⟩ := ht #[]
  obtain ⟨je, xe, re, hre, hbe, hme⟩ := he #[]
  have st : ot.size = rt.size := mapM_ok_size (hmt "")
  have se : oe.size = re.size := mapM_ok_size (hme "")
  have ho : (if bt then ot else oe).size = rt.size := by cases bt <;> simp <;> omega
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ⟨#[.ite c jt.toList rt je.toList re], if bt then ot else oe, (List.range' rs.size rt.size).toArray,
    ?_, fun fs gs hE ws => ?_, fun who => ho ▸ mapM_reg_range rs _ who⟩⟩
  · have hrs : rt.size = re.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self, hrt, hre,
      ok_bind, pure_bind, bind_assoc]
    simp [ok_bind, hrs, emit_run, ← st, ho, ← Array.append_assoc]
  · have hE1 : Env abi fs gs fg1 := Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE
    rw [show (#[Instr.ite c jt.toList rt je.toList re] : Array Instr).toList = [.ite c jt.toList rt je.toList re]
      from rfl, runB.eq_2]
    cases bt <;> simp [runI, reg_of hc, hbt fs gs hE1, hbe fs gs hE, hmt, hme, runB.eq_1, ok_bind, pure, Except.pure,
      Functor.map, Except.map]

/-- `defFun ps b`, then `k` on its number. `Q pv o` says what the function answers: `o` on the parameters `pv`;
    `pv₀` is one such, from which the body is built. `k` may apply the function at any later table. -/
theorem Builds.defFun {fg fg1 fg' : Array Fun × Array Fun} {ps : Array Ty} {b : Array Nat → Bld (Array Nat)}
    {k : Nat → Bld (Array Nat)} {Q : Array Val → Array Val → Prop} {pv₀ o₀ rs out : Array Val}
    (hq : ∀ pv o, Q pv o → pv.size = ps.size) (h₀ : Q pv₀ o₀)
    (hb : ∀ pv o, Q pv o → Builds abi fg fg1 (b (List.range ps.size).toArray) pv o)
    (hk : ∀ F : Fun, (∀ fs gs F' G', (∃ a, F' = fg1.1.push F ++ a) → (∃ a, G' = fg1.2 ++ a) →
        Env abi fs gs (F', G') → ∀ pv o ws, Q pv o → ∃ g, fs[fg1.1.size]? = some g ∧ g gs pv ws = .ok (o, ws)) →
      Builds abi (fg1.1.push F, fg1.2) fg' (k fg1.1.size) rs out) :
    Builds abi fg fg' (Plan.defFun ps b >>= k) rs out := by
  obtain ⟨F0, G0⟩ := fg; obtain ⟨F1, G1⟩ := fg1
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, hb₀⟩ := hb pv₀ o₀ h₀
  obtain ⟨body, xs₀, r, hrun, -, -⟩ := hb₀ #[]
  rw [hq _ _ h₀, Array.empty_append] at hrun
  have hF : ∀ fs gs F' G', (∃ a, F' = F1.push ⟨ps, body.toList, r⟩ ++ a) → (∃ a, G' = G1 ++ a) →
      Env abi fs gs (F', G') → ∀ pv o ws, Q pv o → ∃ g, fs[F1.size]? = some g ∧ g gs pv ws = .ok (o, ws) := by
    rintro fs gs F' G' ⟨a, rfl⟩ ⟨c, rfl⟩ hE pv o ws hpo
    rw [Array.push_eq_append, Array.append_assoc] at hE
    refine ⟨Fun.sem abi (fs.extract 0 F1.size) ⟨ps, body.toList, r⟩, by simpa using hE.1 F1.size (by simp; omega), ?_⟩
    obtain ⟨-, -, h⟩ := hb pv o hpo
    obtain ⟨js, xs, r', hr', hrun', hm'⟩ := h #[]
    rw [hq _ _ hpo, Array.empty_append, hrun] at hr'
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl, -⟩ := hr'
    have hE' : Env abi (fs.extract 0 F1.size) gs (F1, G1) := hE.restrict (FEnv.extract hE.1) rfl
    simp [Fun.sem, hrun' _ gs hE' ws, hm' "result", ok_bind, pure, Except.pure, Functor.map, Except.map]
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, hk₀⟩ := hk _ hF
  refine ⟨⟨a1 ++ #[⟨ps, body.toList, r⟩] ++ a2, ?_⟩, ⟨b1 ++ b2, ?_⟩, fun is => ?_⟩
  · rw [ha2]; simp only at ha1 ⊢; subst ha1; simp only [Array.push_eq_append, Array.append_assoc]
  · rw [hb2]; simp only at hb1 ⊢; subst hb1; simp only [Array.append_assoc]
  obtain ⟨js, xs, r2, hr2, hbk, hm2⟩ := hk₀ is
  refine ⟨js, xs, r2, ?_, hbk, hm2⟩
  simp only [Plan.defFun, StateT.run_bind, StateT.run_get, StateT.run_set, liftM, StateT.run_monadLift,
    monadLift_self, pure_bind, bind_assoc, hrun, ok_bind]
  exact hr2

/-- `global b`, then `k` on its registers: the global holds what `b` answers on no register. -/
theorem Builds.global {fg fgB fg' : Array Fun × Array Fun} {b : Bld (Array Nat)} {k : Array Nat → Bld (Array Nat)}
    {v rs out : Array Val} (hb : Builds abi fg fgB b #[] v)
    (hk : ∀ G : Fun, Builds abi (fgB.1, fgB.2.push G) fg' (k (List.range' rs.size v.size).toArray) (rs ++ v) out) :
    Builds abi fg fg' (Plan.global b >>= k) rs out := by
  obtain ⟨F0, G0⟩ := fg; obtain ⟨FB, GB⟩ := fgB
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, hb⟩ := hb
  obtain ⟨body, xs0, r, hrun, hsem, hm⟩ := hb #[]
  simp only [Array.empty_append, Array.size_empty] at hrun hm hsem
  have hv : v.size = r.size := mapM_ok_size (hm "")
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, hk₀⟩ := hk ⟨#[], body.toList, r⟩
  refine ⟨⟨a1 ++ a2, ?_⟩, ⟨b1 ++ #[⟨#[], body.toList, r⟩] ++ b2, ?_⟩, fun is => ?_⟩
  · rw [ha2]; simp only at ha1 ⊢; subst ha1; simp only [Array.append_assoc]
  · rw [hb2]; simp only at hb1 ⊢; subst hb1; simp only [Array.push_eq_append, Array.append_assoc]
  obtain ⟨js, xs, r2, hr2, hbk, hm2⟩ := hk₀ (is.push (.global GB.size))
  refine ⟨#[.global GB.size] ++ js, v ++ xs, r2, ?_, fun fs gs hE ws => ?_, fun who => by
    simpa [← Array.append_assoc] using hm2 who⟩
  · simp only [Plan.global, StateT.run_bind, StateT.run_get, StateT.run_set, liftM, StateT.run_monadLift,
      monadLift_self, pure_bind, bind_assoc, hrun, ok_bind, emit_run]
    rw [← hv, show rs.size + v.size = (rs ++ v).size by simp, hr2]; simp [← Array.append_assoc]
  · have hE1 := Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE
    obtain ⟨v', hv', fs', hf', hs'⟩ := hE1.2 GB.size (by simp)
    have hE2 : Env abi fs gs (FB ++ #[], GB ++ #[⟨#[], body.toList, r⟩]) := by
      rw [Array.append_empty, ← Array.push_eq_append]; exact hE1
    have hEB : Env abi fs' (gs.extract 0 GB.size) (FB, GB) :=
      hE2.restrict (by simpa using hf') (by simp [Array.extract_extract])
    have e : v' = v := by
      have h1 := hs' ws
      simp [Fun.sem, hsem fs' _ hEB ws, hm "result", ok_bind, pure, Except.pure, Functor.map, Except.map] at h1
      exact h1.symm
    subst e
    have hi : runI abi fs gs (.global GB.size) rs ws = .ok (rs ++ v', ws) := by
      simp only [runI, hv']; rfl
    rw [Array.toList_append, show (#[Instr.global GB.size] : Array Instr).toList = [.global GB.size] from rfl,
      List.singleton_append, runB.eq_2, hi]
    exact (hbk fs gs hE ws).trans (by simp [← Array.append_assoc])

/-- A block of two parts runs as the first, then the second on what it left. -/
theorem runB_append (l1 l2 : List Instr) (rs : Array Val) (ws : Writes) :
    runB abi fs gs (l1 ++ l2) rs ws = (runB abi fs gs l1 rs ws >>= fun p => runB abi fs gs l2 p.1 p.2) := by
  induction l1 generalizing rs ws with
  | nil => rfl
  | cons i l ih =>
    rw [List.cons_append, runB.eq_2, runB.eq_2]
    cases runI abi fs gs i rs ws with
    | error e => rfl
    | ok p => exact ih p.1 p.2

/-- `b`, then `k` on its registers: `k` built after whatever `b` defined, holding `b`'s answer at `b`'s
    registers. -/
theorem Builds.bind {fg fg1 fg' : Array Fun × Array Fun} {b : Bld (Array Nat)} {k : Array Nat → Bld (Array Nat)}
    {rs o out : Array Val} (hb : Builds abi fg fg1 b rs o)
    (hk : ∀ r xs, (∀ who, r.mapM (reg (rs ++ xs) who) = .ok o) → Builds abi fg1 fg' (k r) (rs ++ xs) out) :
    Builds abi fg fg' (b >>= k) rs out := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, hb⟩ := hb
  obtain ⟨_, xs0, r0, -, -, hm0⟩ := hb #[]
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, -⟩ := hk r0 xs0 hm0
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ?_⟩
  obtain ⟨js, xs, r, hr, hs, hm⟩ := hb is
  obtain ⟨-, -, hk'⟩ := hk r xs hm
  obtain ⟨js2, xs2, r2, hr2, hs2, hm2⟩ := hk' (is ++ js)
  refine ⟨js ++ js2, xs ++ xs2, r2, ?_, fun fs gs hE ws => ?_, fun who => by simpa [Array.append_assoc] using hm2 who⟩
  · simp only [StateT.run_bind, hr, ok_bind]; simpa [Array.append_assoc] using hr2
  · rw [Array.toList_append, runB_append, hs fs gs (Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE) ws, ok_bind]
    simpa [Array.append_assoc] using hs2 fs gs hE ws

/-- `if c then t else e` with the bit in `c` set: only `t` runs, so `e` need only build, as many registers wide. -/
theorem Builds.ite_then {fg fg1 fg2 : Array Fun × Array Fun} {c : Nat} {t e : Bld (Array Nat)} {rs ot : Array Val}
    (hc : rs[c]? = some (.bit true)) (ht : Builds abi fg fg1 t rs ot)
    (he : (∃ a, fg2.1 = fg1.1 ++ a) ∧ (∃ a, fg2.2 = fg1.2 ++ a) ∧
      ∃ re je n', e.run (#[], rs.size, fg1) = .ok (re, je, n', fg2) ∧ ot.size = re.size) :
    Builds abi fg fg2 (Plan.ite c t e) rs ot := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩, ht⟩ := ht
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩, re, je, n', hre, hs⟩ := he
  obtain ⟨jt, xt, rt, hrt, hbt, hmt⟩ := ht #[]
  have st : ot.size = rt.size := mapM_ok_size (hmt "")
  refine ⟨⟨a1 ++ a2, by rw [ha2, ha1, Array.append_assoc]⟩, ⟨b1 ++ b2, by rw [hb2, hb1, Array.append_assoc]⟩,
    fun is => ⟨#[.ite c jt.toList rt je.toList re], ot, (List.range' rs.size rt.size).toArray,
    ?_, fun fs gs hE ws => ?_, fun who => st ▸ mapM_reg_range rs _ who⟩⟩
  · have hrs : rt.size = re.size := by omega
    simp only [Plan.ite, block, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, monadLift_self,
      hrt, hre, ok_bind, pure_bind, bind_assoc]
    simp [ok_bind, hrs, emit_run, ← st]; omega
  · have hE1 : Env abi fs gs fg1 := Env.mono ⟨a2, ha2⟩ ⟨b2, hb2⟩ hE
    rw [show (#[Instr.ite c jt.toList rt je.toList re] : Array Instr).toList = [.ite c jt.toList rt je.toList re]
      from rfl, runB.eq_2]
    simp [runI, reg_of hc, hbt fs gs hE1, hmt, runB.eq_1, ok_bind, Functor.map, Except.map]

/-- `guard c` with the bit in `c` set defines no register: `k` runs after the registers so far. -/
theorem Builds.guard {fg fg' : Array Fun × Array Fun} {c : Nat} {msg : String} {as : Array Nat} {k : Bld (Array Nat)}
    {rs out : Array Val} (hc : rs[c]? = some (.bit true)) (hk : Builds abi fg fg' k rs out) :
    Builds abi fg fg' (Plan.guard c msg as >>= fun _ => k) rs out := by
  have e : (Plan.guard c msg as >>= fun _ => k) =
      (Plan.emit (.ite c [] #[] [.fail msg as] #[]) (#[] : Array Val).size >>= fun _ => k) := by
    funext st; rfl
  rw [e]
  refine Builds.emit_bind (fun _ _ _ ws => ?_) (by simpa using hk)
  simp only [runI, reg_of hc, ok_bind, runB.eq_1]
  simp [ok_bind]; rfl

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
theorem abiOf_add : abiOf "lean_usize_add" = some (kernel% USize.add) := by simp [abiOf, abi, List.find?]
theorem abiOf_groupIds : abiOf "qlean_sort_group_ids" = some (kernel% QLean.Kernel.Order.groupIds) := by
  simp [abiOf, abi, List.find?]
theorem abiOf_idGroups : abiOf "qlean_sort_id_groups" = some (kernel% QLean.Kernel.Order.idGroups) := by
  simp [abiOf, abi, List.find?]

/-- `groupIdsB.go` on lanes `ks`: `groupIds` at the first lane of the code's width, `idGroups` past the last. -/
theorem groupIdsB_go {fg : Array Fun × Array Fun} (c : Alg.Code) (hw : c.w < USize.size) (hc : 0 < c.card) (ks : List (Nat × Scan.Kind))
    (hks : ∀ p ∈ ks, p.1 < USize.size) (rs : Array Val) (h4 : (codeVals c).size ≤ rs.size)
    (hr : ∀ i < (codeVals c).size, rs[i]? = (codeVals c)[i]?) :
    Builds abiOf fg fg (groupIdsB.go 0 1 2 3 ks) rs
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
    have hadd : (c.card - 1).toUSize + 1 = c.card.toUSize := by
      rw [show c.card.toUSize = (c.card - 1 + 1).toUSize by rw [Nat.sub_add_cancel hc]]
      exact (USize.ofNat_add _ _).symm
    refine Builds.emit1 (v := .size 1) (fun _ _ _ _ => rfl) ?_
    obtain ⟨h4₁, hr₁⟩ := push_keep (x := .size 1) h4 hr
    have ha₁ : #[2, rs.size].mapM (reg (rs.push (.size 1)) "lean_usize_add") =
        .ok #[.size (c.card - 1).toUSize, .size 1] := by
      rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
      rw [reg_of (rd h4₁ hr₁ 2 (by simp [codeVals])), reg_of (Array.getElem?_push_size)]; rfl
    refine Builds.emit1 (v := .size c.card.toUSize) (fun _ _ _ ws => by
      rw [Array.push_eq_append (as := rs.push (.size 1))]
      exact runI_call abiOf_add rfl ha₁ (by rw [← hadd]; rfl) rfl) ?_
    obtain ⟨h4₂, hr₂⟩ := push_keep (x := .size c.card.toUSize) h4₁ hr₁
    have ha : #[(rs.push (.size 1)).size, 1, 0, 3].mapM
        (reg ((rs.push (.size 1)).push (.size c.card.toUSize)) "qlean_sort_id_groups") =
        .ok #[.size c.card.toUSize, .size c.n, .size c.w.toUSize, .bytes c.b] := by
      rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
      rw [reg_of (Array.getElem?_push_size), reg_of (rd h4₂ hr₂ 1 (by simp [codeVals])),
        reg_of (rd h4₂ hr₂ 0 (by simp [codeVals])), reg_of (rd h4₂ hr₂ 3 (by simp [codeVals]))]; rfl
    exact Builds.emit (fun _ _ _ ws => runI_call abiOf_idGroups rfl ha rfl rfl) rfl
  | cons p ks ih =>
    obtain ⟨v, k⟩ := p
    have hv : v < USize.size := hks _ (List.mem_cons_self ..)
    have hks' : ∀ p ∈ ks, p.1 < USize.size := fun p hp => hks p (List.mem_cons_of_mem _ hp)
    rw [groupIdsB.go]
    refine Builds.emit1 (v := .size v.toUSize) (fun _ _ _ _ => rfl) ?_
    obtain ⟨h4₁, hr₁⟩ := push_keep (x := .size v.toUSize) h4 hr
    have ha : #[0, rs.size].mapM (reg (rs.push (.size v.toUSize)) "lean_usize_dec_eq") =
        .ok #[.size c.w.toUSize, .size v.toUSize] := by
      rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
      rw [reg_of (rd h4₁ hr₁ 0 (by simp [codeVals])), reg_of (Array.getElem?_push_size)]; rfl
    refine Builds.emit1 (v := .bit (decide (c.w.toUSize = v.toUSize))) (fun _ _ _ ws => by
      rw [Array.push_eq_append (as := rs.push (.size v.toUSize))]
      exact runI_call abiOf_decEq rfl ha rfl rfl) ?_
    obtain ⟨h4₂, hr₂⟩ := push_keep (x := .bit (decide (c.w.toUSize = v.toUSize))) h4₁ hr₁
    have key := Builds.ite (Array.getElem?_push_size)
      (show Builds abiOf fg fg (do Plan.call "qlean_sort_group_ids" #[← lit (Reg.put k), 1, 3] 2) _
          #[.bytes (Order.groupIds k c.n c.b).1, .bytes (Order.groupIds k c.n c.b).2] from by
        refine Builds.emit1 (v := Reg.put k) (fun _ _ _ _ => rfl) ?_
        obtain ⟨h4₃, hr₃⟩ := push_keep (x := Reg.put k) h4₂ hr₂
        have ha : #[(rs.push (.size v.toUSize) |>.push (.bit (decide (c.w.toUSize = v.toUSize)))).size, 1, 3].mapM
            (reg ((rs.push (.size v.toUSize) |>.push (.bit (decide (c.w.toUSize = v.toUSize)))).push (Reg.put k))
              "qlean_sort_group_ids") = .ok #[Reg.put k, .size c.n, .bytes c.b] := by
          rw [List.mapM_toArray]; simp only [List.mapM_cons, List.mapM_nil]
          rw [reg_of (Array.getElem?_push_size), reg_of (rd h4₃ hr₃ 1 (by simp [codeVals])),
            reg_of (rd h4₃ hr₃ 3 (by simp [codeVals]))]; rfl
        exact Builds.emit (fun _ _ _ ws => runI_call abiOf_groupIds rfl ha (by cases k <;> rfl) rfl) rfl)
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
theorem groupIdsB_builds {fg : Array Fun × Array Fun} (c : Alg.Code) (hw : c.w < USize.size) (hc : 0 < c.card) :
    Builds abiOf fg fg (groupIdsB 0 1 2 3) (codeVals c) #[.bytes c.groupIds.1, .bytes c.groupIds.2] := by
  have hl : ∀ p ∈ ([1, 8, 16, 32, 64].filterMap fun v => (Alg.laneKind v).map (v, ·)), p.1 < USize.size := by
    intro p hp
    have : p = (1, .bit) ∨ p = (8, .u8) ∨ p = (16, .i16) ∨ p = (32, .i32) ∨ p = (64, .i64) := by
      simpa [Alg.laneKind] using hp
    rcases USize.size_eq with hs | hs <;> rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [hs]
  have := groupIdsB_go (fg := fg) c hw hc _ hl (codeVals c) (Nat.le_refl _) (fun _ _ => rfl)
  rw [lanes_find] at this
  exact this

end LeetQ.Rel.Lang.Plan
