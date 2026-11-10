/-
  qlean's atom-level dyad succeeds on typed atoms: for every verb `v` the rule `Eval.ewType` types at the
  atoms' types, `dyadAtom` answers `.ok` at the type the rule names. `Verify.dyadAtom_type` is the type half;
  this is the success half, which is what lets the reference branch of `Ew.dyad` take `.get` of it. An atom
  is never `general`, so the atom form needs no hypothesis on `t`, `u`; `Dep.elem` does, because at
  `general` it boxes and the boxed dyad can fail (`(.add, .general, .long)` on `` `a ``).
-/
import QLean.Dep.Dyadic

namespace LeetQ.Rel.KernelWF

open QLean QLean.Eval

/-! ## Facts over the type lattice, decided over `allTypes` -/

theorem mem_allTypes {t : QAtomicType} (h : t ≠ .general) : t ∈ allTypes.toList := by
  cases t <;> simp_all [allTypes]

/-- The common type of two atomic types is atomic and both cast to it. -/
theorem common_castable {t u c : QAtomicType} (ht : t ≠ .general) (hu : u ≠ .general)
    (h : Prim.common t u = some c) : c ≠ .general ∧ Prim.castable c t = true ∧ Prim.castable c u = true := by
  have hall : allTypes.toList.all (fun t => allTypes.toList.all fun u => match Prim.common t u with
      | some c => c != .general && Prim.castable c t && Prim.castable c u
      | none => true) = true := by decide +kernel
  have := List.all_eq_true.1 (List.all_eq_true.1 hall t (mem_allTypes ht)) u (mem_allTypes hu)
  rw [h] at this
  simpa [Bool.and_eq_true, and_assoc] using this

/-- The arithmetic rule never answers `general`. -/
theorem arith_ne_general {v : Prim.Dyadic} {t u r : QAtomicType} (hv : v ∈ [Prim.Dyadic.add, .sub, .mul, .div])
    (ht : t ≠ .general) (hu : u ≠ .general) (h : Prim.arith v t u = some r) : r ≠ .general := by
  have hall : [Prim.Dyadic.add, .sub, .mul, .div].all (fun v => allTypes.toList.all fun t =>
      allTypes.toList.all fun u => (Prim.arith v t u).all (· != .general)) = true := by decide +kernel
  have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 hall v hv) t (mem_allTypes ht)) u
    (mem_allTypes hu)
  rw [h] at this
  simpa using this

/-- No element-wise rule answers `general` on two atomic types. -/
theorem ewType_ne_general {v : Prim.Dyadic} {t u rt : QAtomicType} (ht : t ≠ .general) (hu : u ≠ .general)
    (h : Eval.ewType v t u = some rt) : rt ≠ .general := by
  cases v <;> simp only [Eval.ewType, Prim.elementwise] at h
  case add | sub | mul | div => all_goals exact arith_ne_general (by simp) ht hu h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨c, hc⟩ : ∃ c, Prim.common t u = some c := by cases hc : Prim.common t u <;> simp_all
       have hcg := (common_castable ht hu hc).1
       rw [hc] at h
       cases c <;> simp_all <;> (subst h; decide))

/-- An operand of the arithmetic rule has a numeric payload. -/
theorem arith_numeric {v : Prim.Dyadic} {t u r : QAtomicType} (h : Prim.arith v t u = some r) :
    Prim.nonNumeric t = false ∧ Prim.nonNumeric u = false := by
  unfold Prim.arith at h
  split at h
  · exact absurd h (by simp)
  · simp_all

/-- A cast to another type reads a numeric payload. -/
theorem castable_numeric {c s : QAtomicType} (h : Prim.castable c s = true) (hne : (s == c) = false) :
    Prim.nonNumeric s = false := by
  unfold Prim.castable at h
  split at h
  · have := eq_of_beq h; subst this; simp at hne
  · next hn => simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn; exact hn.2

/-! ## The payload readers answer on every numeric atom -/

theorem floatPayload_isSome {a : QAtom} (h : Prim.nonNumeric a.type = false) : (floatPayload a).isSome := by
  cases a <;> simp_all [floatPayload, intPayload, Prim.nonNumeric, QAtom.type]

theorem temporalNanos_isSome {a : QAtom} (h : (temporalScale a.type).isSome) : (temporalNanos a).isSome := by
  cases a <;> simp_all [temporalNanos, temporalScale, intPayload, QAtom.type]

theorem cmpAtoms_isSome {a b : QAtom} (h : a.type = b.type) : (cmpAtoms a b).isSome := by
  cases a <;> cases b <;> simp [QAtom.type] at h <;> simp only [cmpAtoms, intPayload, floatPayload] <;>
    (repeat' split) <;> simp_all

/-! ## Casts -/

theorem castTemporal_isSome {t : QAtomicType} {a : QAtom} (hg : t ≠ .general)
    (hc : Prim.castable t a.type = true) (ht : (Prim.temporal t).isSome) (ha : (Prim.temporal a.type).isSome) :
    (castTemporal t a).isSome := by
  have hs : (temporalScale a.type).isSome := by
    generalize a.type = s at ha; cases s <;> simp_all [temporalScale, Prim.temporal]
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (temporalNanos_isSome hs)
  unfold castTemporal
  rw [dif_neg hg]
  generalize a.type = s at *
  cases s <;> cases t <;> simp_all (config := { decide := true }) [temporalScale]
  all_goals (split <;> simp_all)

theorem castAtom_isSome {t : QAtomicType} {a : QAtom} (hg : t ≠ .general) (hc : Prim.castable t a.type = true) :
    (castAtom t a).isSome := by
  unfold castAtom
  rw [dif_neg hg]
  by_cases he : (a.type == t) = true
  · simp [he]
  rw [if_neg he, if_neg (by simp [hc])]
  have hnum := castable_numeric hc (by simpa using he)
  split
  · next hb =>
    have hbt : t = .boolean := eq_of_beq hb
    subst hbt
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1
      (cmpAtoms_isSome (a := a) (b := atomOfInt a.type 0 a.type_ne_general) (by simp))
    simp [ho]
  split
  · rfl
  split
  · next htm => simp only [Bool.and_eq_true] at htm; exact castTemporal_isSome hg hc htm.1 htm.2
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (floatPayload_isSome hnum)
  split
  · simp [hx]
  · split
    · rfl
    · simp [hx]

/-- Two atoms whose types have a common type reach it. -/
theorem toCommon_ok {a b : QAtom} {c : QAtomicType} (h : Prim.common a.type b.type = some c) :
    ∃ x y, toCommon a b = some (c, x, y) ∧ x.type = c ∧ y.type = c := by
  unfold toCommon
  split
  · next he =>
    have he' : a.type = b.type := by simpa using he
    have : c = a.type := by simp [Prim.common, he'] at h; rw [he']; exact h.symm
    subst this
    exact ⟨a, b, rfl, rfl, he'.symm⟩
  · obtain ⟨hcg, hca, hcb⟩ := common_castable a.type_ne_general b.type_ne_general h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (castAtom_isSome hcg hca)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (castAtom_isSome hcg hcb)
    exact ⟨x, y, by simp [h, hx, hy], Verify.castAtom_type hx, Verify.castAtom_type hy⟩

/-! ## Arithmetic -/

theorem floatIn_isSome {t : QAtomicType} {a : QAtom} (h : Prim.nonNumeric a.type = false) :
    (floatIn t a).isSome := by
  unfold floatIn
  split
  · rfl
  · exact floatPayload_isSome h

theorem intIn_isSome {t : QAtomicType} {a : QAtom} (h : Prim.nonNumeric a.type = false) :
    (intIn t a).isSome := by
  unfold intIn roundedPayload
  split
  · rfl
  · split
    · rfl
    · simpa using floatPayload_isSome h

theorem negClock_type (b : QAtom) : (negClock b).type = b.type := by
  cases b <;> rfl

theorem arithAtoms_ok {v : Prim.Dyadic} {t : QAtomicType} {a b : QAtom} (hg : t ≠ .general)
    (ha : Prim.nonNumeric a.type = false) (hb : Prim.nonNumeric b.type = false) :
    ∃ z, arithAtoms v t a b = .ok z := by
  unfold arithAtoms
  rw [dif_neg hg]
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (floatIn_isSome (t := t) ha)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (floatIn_isSome (t := t)
      (a := if v == .sub && Prim.clockIntoDays t b.type then negClock b else b) (by split <;> simp_all [negClock_type]))
    rw [hx, hy]
    exact ⟨_, rfl⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (intIn_isSome (t := t) ha)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (intIn_isSome (t := t) hb)
    rw [hx, hy]
    exact ⟨_, rfl⟩

/-! ## The dyad -/

/-- **`dyadAtom` succeeds where the rule types the pair.** For every verb `v` and atoms `a`, `b` of types
    `t`, `u` that `ewType` types at `rt`, the dyad answers `.ok` at an atom of `rt`. -/
theorem dyadAtom_ok {v : Prim.Dyadic} {t u rt : QAtomicType} {a b : QAtom} (h : Eval.ewType v t u = some rt)
    (ha : a.type = t) (hb : b.type = u) : ∃ z, dyadAtom v a b = .ok z ∧ z.type = rt := by
  subst ha hb
  suffices hz : ∃ z, dyadAtom v a b = .ok z by
    obtain ⟨z, hz⟩ := hz
    exact ⟨z, hz, Option.some.inj ((Verify.dyadAtom_type hz).symm.trans h)⟩
  cases v
  case add | sub | mul | div =>
    all_goals (
      simp only [Eval.ewType] at h
      simp only [dyadAtom, h]
      obtain ⟨hna, hnb⟩ := arith_numeric h
      exact arithAtoms_ok (arith_ne_general (by simp) a.type_ne_general b.type_ne_general h) hna hnb)
  all_goals first
    | (simp [Eval.ewType, Prim.elementwise] at h; done)
    | (obtain ⟨c, hc⟩ : ∃ c, Prim.common a.type b.type = some c := by
          cases hc : Prim.common a.type b.type <;> simp_all [Eval.ewType, Prim.elementwise]
       obtain ⟨x, y, hxy, hx, hy⟩ := toCommon_ok hc
       obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (cmpAtoms_isSome (hx.trans hy.symm))
       simp only [Eval.ewType] at h
       simp [dyadAtom, h, hxy, ho, cmpTolerant])

/-- The same, in the form a `.get` consumes: the dyad's `toOption` is `some`. -/
theorem dyadAtom_isSome {v : Prim.Dyadic} {t u rt : QAtomicType} {a b : QAtom} (h : Eval.ewType v t u = some rt)
    (ha : a.type = t) (hb : b.type = u) : (dyadAtom v a b).toOption.isSome := by
  obtain ⟨z, hz, -⟩ := dyadAtom_ok h ha hb
  simp [hz, Except.toOption]

/-- What that `.get` reads is an atom of `rt`. -/
theorem dyadAtom_get_type {v : Prim.Dyadic} {t u rt : QAtomicType} {a b : QAtom}
    (h : Eval.ewType v t u = some rt) (ha : a.type = t) (hb : b.type = u) :
    ((dyadAtom v a b).toOption.get (dyadAtom_isSome h ha hb)).type = rt := by
  obtain ⟨z, hz, hzt⟩ := dyadAtom_ok h ha hb
  simp [hz, Except.toOption, hzt]

/-- `Dep.elem` succeeds off `general`: there it is `dyadAtom` on the two atoms. -/
theorem elem_ok {v : Prim.Dyadic} {t u rt : QAtomicType} (h : Eval.ewType v t u = some rt)
    (ht : t ≠ .general) (hu : u ≠ .general) (x : Dep.Carrier t) (y : Dep.Carrier u) :
    ∃ z, Dep.elem v h x y = .ok z := by
  obtain ⟨z, hz, -⟩ := dyadAtom_ok h (Dep.Carrier.atom_type x ht) (Dep.Carrier.atom_type y hu)
  unfold Dep.elem
  rw [dif_neg ht, dif_neg hu]
  split
  · next hz' => rw [hz] at hz'; exact absurd hz' (by simp)
  · exact ⟨_, rfl⟩

/-- **The list form.** Over two atom lists of types `t`, `u` and one length `n`, the dyad answers `.ok`
    pair by pair, and what it answers is a list `Enc.ofAtoms` takes to `n` well-formed elements of `rt`. -/
theorem dyadAtoms_wf {v : Prim.Dyadic} {t u rt : QAtomicType} {n : Nat} (h : Eval.ewType v t u = some rt)
    (ht : t ≠ .general) (hu : u ≠ .general) {as bs : List QAtom} (ha : ∀ a ∈ as, a.type = t) (hb : ∀ b ∈ bs, b.type = u) (has : as.length = n)
    (hbs : bs.length = n) :
    ∃ zs, (as.zip bs).mapM (fun p => dyadAtom v p.1 p.2) = .ok zs ∧
      ∃ e, Enc.ofAtoms rt zs.toArray (ewType_ne_general ht hu h) = some e ∧ Enc.WF rt n e := by
  obtain ⟨zs, hzs, hl, hty⟩ : ∃ zs, (as.zip bs).mapM (fun p => dyadAtom v p.1 p.2) = .ok zs ∧
      zs.length = (as.zip bs).length ∧ ∀ z ∈ zs, z.type = rt := by
    clear has hbs
    induction as generalizing bs with
    | nil => exact ⟨[], rfl, rfl, by simp⟩
    | cons a as ih =>
      cases bs with
      | nil => exact ⟨[], rfl, rfl, by simp⟩
      | cons b bs =>
        obtain ⟨z, hz, hzt⟩ := dyadAtom_ok h (ha a (by simp)) (hb b (by simp))
        obtain ⟨zs, hzs, hl, hty⟩ := ih (bs := bs) (fun x hx => ha x (by simp [hx]))
          (fun x hx => hb x (by simp [hx]))
        refine ⟨z :: zs, ?_, by simp [hl], ?_⟩
        · rw [List.zip_cons_cons, List.mapM_cons, hz, hzs]; rfl
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact hzt
          · exact hty w hw
  have hall : ∀ z ∈ zs.toArray, z.type = rt := fun z hz => hty z (by simpa using hz)
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (Column.ofAtoms_isSome (ewType_ne_general ht hu h) hall)
  refine ⟨zs, hzs, e, he, ?_⟩
  have hw := Column.ofAtoms_WF hall he
  simpa [hl, has, hbs] using hw


end LeetQ.Rel.KernelWF
