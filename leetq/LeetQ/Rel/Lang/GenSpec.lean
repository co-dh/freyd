import LeetQ.Rel.Lang.Gen
import LeetQ.Rel.Lang.BitsSpecRun
import LeetQ.Rel.CRelRel
import LeetQ.Rel.CRelRelDef
import LeetQ.Rel.CRelArith
import LeetQ.Rel.CRelArithDef
import LeetQ.Rel.CRelFold
import LeetQ.Rel.CRelFoldDef

/-! The code of `Gen` read back: one lemma per combinator, saying that where its ok bit is set its relation is
    the allegory's operation on its parts' relations, so `Expand` assembles the correctness of a definition from
    these lemmas structurally over its term. A term that runs on demand is read only at the keys it is given
    (§a), so `Sound f T` says that `f` and `T` agree on those keys: `D ≫ rep(f D) = D ≫ T`, pointwise. A closed
    term has no keys, and there it is the equation `rep(f ()) = T` (`Sound.eq`). -/

namespace LeetQ.Rel.Lang.Gen

open LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep Freyd Freyd.Alg Freyd.Alg.RelSet

/-- An arrow `A ⟶ B` of `Rel(Set)` between the elements of two objects. -/
abbrev Den (A B : Obj) := (⟨A.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩

/-- The keys `D` as a relation: the coreflexive itself on demand, `𝟙` for a closed term. -/
def keys : {d : Bool} → {A : Obj} → Dem d A → Den A A
  | true, _, D => rep D
  | false, _, _ => 𝟙 _

/-- The keys a term is given form a coreflexive. -/
def Cor : {d : Bool} → {A : Obj} → Dem d A → Prop
  | true, _, D => ∀ x y, rep D x y → x = y
  | false, _, _ => True

/-- `f` computes `T` on its keys: given a coreflexive `D` and its ok bit, `x {rep(f D)} y ↔ x {T} y` at each key
    `x` of `D`. -/
def Sound {d : Bool} {A B : Obj} (f : Fn d A B) (T : Den A B) : Prop :=
  ∀ D : Dem d A, Cor D → (f D).ok = true → ∀ x y, keys D x x → (rep (f D).rel x y ↔ T x y)

/-- A closed term's `Sound` is the equation of its relation. -/
theorem Sound.eq {A B : Obj} {f : Fn false A B} {T : Den A B} (h : Sound f T) (hb : (f ()).ok = true) :
    rep (f ()).rel = T :=
  hom_ext fun x y => h () trivial hb x y rfl

/-- A plan computes `T` on its keys, read by `TP.den`, the relation it denotes. -/
def PSound {d : Bool} {A B : Obj} (p : Pl d A B) (T : Den A B) : Prop :=
  ∀ D : Dem d A, Cor D → (p D).2 = true → ∀ x y, keys D x x → ((p D).1.den x y ↔ T x y)

/-! ### Keys -/

theorem demL {A : Obj} : ∀ (d e : Bool) (D : Dem (d || e) A) (x : A.El), Cor D → keys D x x →
    Cor (Dem.l d e D) ∧ keys (Dem.l d e D) x x
  | true, _, _, _, h, k => ⟨h, k⟩
  | false, _, _, _, _, _ => ⟨trivial, rfl⟩

theorem demR {A : Obj} : ∀ (d e : Bool) (D : Dem (d || e) A) (x : A.El), Cor D → keys D x x →
    Cor (Dem.r d e D) ∧ keys (Dem.r d e D) x x
  | true, true, _, _, h, k => ⟨h, k⟩
  | false, true, _, _, h, k => ⟨h, k⟩
  | _, false, _, _, _, _ => ⟨trivial, rfl⟩

/-- A coreflexive `K` given as the keys of `S`: `S` agrees with `T` at every key of `K`. -/
theorem atKeys {B C : Obj} {e : Bool} {S : Fn e B C} {T : Den B C} (hS : Sound S T) (K : Rel B B)
    (hc : ∀ x y, rep K x y → x = y) (hb : (S (Dem.of e K)).ok = true) :
    ∀ b c, rep K b b → (rep (S (Dem.of e K)).rel b c ↔ T b c) := by
  cases e
  · exact fun b c _ => hS () trivial hb b c rfl
  · exact fun b c hk => hS K hc hb b c hk

/-- A coreflexive's row values: on the keys of `D`, every key is one of `D.val`'s rows. -/
theorem keyRow {A : Obj} {D : Rel A A} {x : A.El} (h : rep D x x) : ∃ i, D.val.row i = x :=
  let ⟨i, _, e⟩ := h; ⟨i, e⟩

theorem rowKey {A : Obj} {D : Rel A A} (hD : ∀ x y, rep D x y → x = y) {x : A.El} :
    (∃ i, D.val.row i = x) → rep D x x := by
  rintro ⟨i, rfl⟩
  have h : rep D (D.key.row i) (D.val.row i) := ⟨i, rfl, rfl⟩
  rw [hD _ _ h] at h; exact h

/-- `ranC`'s and `CRel.ran`'s relation: the coreflexive on `R`'s values. -/
theorem ran_iff {A B : Obj} (R : Den A B) (y y' : B.El) :
    (𝟙 _ ∩ R° ≫ R°° : Den B B) y y' ↔ y = y' ∧ ∃ x, R x y ∧ R x y' := Iff.rfl

theorem ok_and {A B : Obj} {b : Bool} {k : Unit → CRel A B} (h : (CRel.guard b k).ok = true) : b = true := by
  rw [CRel.guard_ok, Bool.and_eq_true] at h; exact h.1

/-! ### Leaves -/

theorem const_sound {A B : Obj} {c : CRel A B} {T : Den A B} (h : c.ok = true → rep c.rel = T) :
    Sound (const A B c) T := fun ⟨⟩ _ hb x y _ => by rw [show (const A B c ()) = c from rfl, h hb] at *

theorem val_sound {A B : Obj} (R : Rel A B × Bool) : Sound (val A B R) (rep R.1) :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem uni_sound {A : Obj} {m : USize} (U : Vals A m × Bool) : Sound (uni A m U) (rep (idU U.1)) :=
  fun _ _ _ _ _ _ => Iff.rfl

theorem zero_sound {A B : Obj} : Sound (zero A B) 𝟘 := fun _ _ _ x y _ => by
  show rep (Alg.zero : Rel A B) x y ↔ _; rw [rep_zero]

theorem id_sound {A : Obj} : Sound (id A) (𝟙 _) := fun D hD _ x y hx =>
  ⟨fun h => hD x y h, fun e => e ▸ hx⟩

theorem outl_sound {A B : Obj} : Sound (outl A B) (graph Prod.fst) := fun D hD _ x y hx => by
  show rep (Alg.outl D) x y ↔ _; rw [rep_outl]
  exact ⟨fun ⟨z, h, e⟩ => (hD x z h) ▸ e, fun e => ⟨x, hx, e⟩⟩

theorem outr_sound {A B : Obj} : Sound (outr A B) (graph Prod.snd) := fun D hD _ x y hx => by
  show rep (Alg.outr D) x y ↔ _; rw [rep_outr]
  exact ⟨fun ⟨z, h, e⟩ => (hD x z h) ▸ e, fun e => ⟨x, hx, e⟩⟩

theorem inl_sound {A B : Obj} : Sound (inl A B) (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ := fun D _ hb x y hx => by
  show rep (CRel.inl (B := B) D.val).rel x y ↔ _; rw [CRel.rep_inl _ hb]
  exact ⟨fun ⟨z, ⟨e, _⟩, h⟩ => e ▸ h, fun h => ⟨x, ⟨rfl, keyRow hx⟩, h⟩⟩

theorem inr_sound {A B : Obj} : Sound (inr A B) (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ := fun D _ hb x y hx => by
  show rep (CRel.inr (A := A) D.val).rel x y ↔ _; rw [CRel.rep_inr _ hb]
  exact ⟨fun ⟨z, ⟨e, _⟩, h⟩ => e ▸ h, fun h => ⟨x, ⟨rfl, keyRow hx⟩, h⟩⟩

theorem mem_sound {B : Obj} : Sound (mem B) (fun xs x => x ∈ xs) := fun D _ hb xs x hx => by
  show rep (CRel.mem D.val).rel xs x ↔ _; rw [CRel.rep_mem _ hb]
  exact ⟨fun h => h.2, fun h => ⟨keyRow hx, h⟩⟩

/-! ### The allegory's operations -/

theorem comp_sound {A B C : Obj} {e : Bool} {R : Fn true A B} {S : Fn e B C} {TR : Den A B} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (comp A B C e R S) (TR ≫ TS) := by
  intro D hD hb x z hx
  have hr := hR D hD
  unfold comp at hb ⊢
  by_cases h0 : ((R D).rel.n == 0) = true
  · rw [if_pos h0] at hb ⊢
    show rep (Alg.zero : Rel A C) x z ↔ _
    rw [rep_zero]
    refine ⟨False.elim, fun ⟨y, hy, _⟩ => ?_⟩
    obtain ⟨i, -⟩ := (hr hb x y hx).2 hy
    have : (R D).rel.n.toNat = 0 := by simp [beq_iff_eq.1 h0]
    exact absurd i.2 (by omega)
  · rw [if_neg h0] at hb ⊢
    simp only [also, Bool.and_eq_true] at hb ⊢
    obtain ⟨hk, hc⟩ := hb
    have hc2 := ok_and hc; rw [Bool.and_eq_true] at hc2
    have hro : (R D).ok = true := hc2.1
    rw [CRel.rep_comp _ _ hc]
    have hK := CRel.rep_ran (R D) hk
    have hs := atKeys hS (CRel.ran (R D)).rel (fun a b h => ((ran_iff _ a b).1 (hK ▸ h)).1) hc2.2
    refine ⟨fun ⟨y, h1, h2⟩ => ⟨y, (hr hro x y hx).1 h1, ?_⟩, fun ⟨y, h1, h2⟩ => ?_⟩
    · exact (hs y z (hK ▸ (ran_iff _ y y).2 ⟨rfl, x, h1, h1⟩)).1 h2
    · have h1' := (hr hro x y hx).2 h1
      exact ⟨y, h1', (hs y z (hK ▸ (ran_iff _ y y).2 ⟨rfl, x, h1', h1'⟩)).2 h2⟩

theorem conv_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) : Sound (conv A B R) T° :=
  fun ⟨⟩ _ hb y x _ => by
    show rep ((R ()).rel°) y x ↔ _; rw [rep_conv]; exact hR () trivial hb x y rfl

theorem meet_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (meet A B d e R S) (TR ∩ TS) := fun D hD hb x y hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.inter _ _).rel x y ↔ _; rw [CRel.rep_inter _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hc.1 x y kl) (hS _ cr hc.2 x y kr)

theorem join_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (join A B d e R S) (TR ∪ TS) := fun D hD hb x y hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.union _ _).rel x y ↔ _; rw [CRel.rep_union _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact or_congr (hR _ cl hc.1 x y kl) (hS _ cr hc.2 x y kr)

theorem diff_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (diff A B d e R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  fun D hD hb x y hx => by
    have hc := ok_and hb; rw [Bool.and_eq_true] at hc
    show rep (CRel.diff _ _).rel x y ↔ _; rw [CRel.rep_diff _ _ hb]
    obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
    exact and_congr (hR _ cl hc.1 x y kl) (not_congr (hS _ cr hc.2 x y kr))

theorem dom_sound {A B : Obj} {d : Bool} {R : Fn d A B} {T : Den A B} (hR : Sound R T) :
    Sound (dom A B d R) (𝟙 _ ∩ T ≫ T°) := fun D hD hb x x' hx => by
  have hro : (R D).ok = true := ok_and hb
  show rep (CRel.dom (R D)).rel x x' ↔ _; rw [CRel.rep_dom _ hb]
  exact ⟨fun ⟨e, y, h, _⟩ => ⟨e, y, (hR D hD hro x y hx).1 h, e ▸ (hR D hD hro x y hx).1 h⟩,
    fun ⟨e, y, h, _⟩ => ⟨e, y, (hR D hD hro x y hx).2 h, e ▸ (hR D hD hro x y hx).2 h⟩⟩

theorem ran_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) :
    Sound (ran A B R) (𝟙 _ ∩ T° ≫ T°°) := fun ⟨⟩ _ hb y y' _ => by
  show rep (CRel.ran (R ())).rel y y' ↔ _; rw [CRel.rep_ran _ hb, (hR.eq (ok_and hb))]

theorem pair_sound {A B C : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A C} {TR : Den A B} {TS : Den A C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (pair A B C d e R S) (rpair TR TS) := fun D hD hb x p hx => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.pair _ _).rel x p ↔ _; rw [CRel.rep_pair _ _ hb]
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hc.1 x p.1 kl) (hS _ cr hc.2 x p.2 kr)

theorem prod_sound {A B C D : Obj} {R : Fn false A B} {S : Fn false C D} {TR : Den A B} {TS : Den C D}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (prod A B C D R S) (rprodMap TR TS) := fun ⟨⟩ _ hb x y _ => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.prod _ _).rel x y ↔ _; rw [CRel.rep_prod _ _ hb, hR.eq hc.1, hS.eq hc.2]

theorem junc_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {TR : Den A C} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) :
    Sound (junc A B C R S) (Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) TR TS) := fun ⟨⟩ _ hb x y _ => by
  have hc := ok_and hb; rw [Bool.and_eq_true] at hc
  show rep (CRel.junc _ _).rel x y ↔ _; rw [CRel.rep_junc _ _ hb, hR.eq hc.1, hS.eq hc.2]

/-- A relation's value rows are the values its `rep` reaches. -/
theorem valRow {A B : Obj} (U : Rel A B) (b : B.El) : (∃ p, U.val.row p = b) ↔ ∃ a, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.key.row p, p, rfl, e⟩, fun ⟨_, p, _, e⟩ => ⟨p, e⟩⟩

theorem top_sound {A B : Obj} {V : Fn false B B} {TV : Den B B} (hV : Sound V TV) :
    Sound (top A B V) (relTop ≫ TV) := fun D _ hb x y hx => by
  simp only [top, also, ofC, Bool.and_eq_true] at hb ⊢
  rw [rep_topC _ _ hb.2, ← hV.eq hb.1]
  exact ⟨fun ⟨_, _, _, _, e, hq⟩ => let ⟨a, h⟩ := (valRow _ _).1 hq; ⟨a, trivial, e ▸ h⟩,
    fun ⟨a, _, hy⟩ => ⟨x, ⟨rfl, keyRow hx⟩, y, trivial, rfl, (valRow _ _).2 ⟨a, hy⟩⟩⟩

theorem rdiv_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {UA : Fn false A A} {UB : Fn false B B}
    {TR : Den A C} {TS : Den B C} {TA : Den A A} {TB : Den B B} (hR : Sound R TR) (hS : Sound S TS)
    (hA : Sound UA TA) (hB : Sound UB TB) :
    Sound (rdiv A B C R S UA UB)
      (fun x y => (∀ c, TS y c → TR x c) ∧ ((∃ c, TS y c) ∨ ((∃ a, TA a x) ∧ ∃ b, TB b y))) :=
  fun ⟨⟩ _ hb x y _ => by
    simp only [rdiv, also, Bool.and_eq_true] at hb ⊢
    have hc := ok_and hb.2; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_rightDiv _ _ _ _ hb.2, hR.eq hc.1, hS.eq hc.2, valRow, valRow, hA.eq hb.1.1, hB.eq hb.1.2]

/-! ### The bit-matrix plans -/

/-- **`runC`'s answer is the plan's relation** under its bit, on either path, in check mode too (`die` is its
    argument). -/
theorem rep_runC {A B : Obj} (p : Bits.TP A B) (hb : (Bits.runC p).2 = true) (a : A.El) (b : B.El) :
    rep (Bits.runC p).1 a b ↔ p.den a b := by
  match p with
  | .leaf _ => exact Iff.rfl
  | .comp .. | .conv .. | .meet .. | .join .. | .diff .. | .ldiv .. =>
    simp only [Bits.runC] at hb ⊢
    revert hb; split
    · rename_i R h; simp only [dbgTrace, Bits.die, ite_self]; exact fun _ => Bits.bits_table h a b
    · by_cases hc : (Bits.checkOn == 0) = true
      · rw [if_pos hc]; exact fun hb => Bits.rep_tableC _ hb a b
      · rw [if_neg hc]; simp only [dbgTrace]; exact fun hb => Bits.rep_table _ hb a b

/-- The demand `demP` hands `S` in `R S`: a coreflexive holding every value of `R`'s plan. -/
theorem demP_spec {A B : Obj} (e : Bool) (r : Bits.TP A B) (hb : (demP e r).2 = true) :
    Cor (demP e r).1 ∧ ∀ a b, r.den a b → keys (demP e r).1 b b := by
  cases e
  · exact ⟨trivial, fun _ _ _ => rfl⟩
  · simp only [demP, Bool.and_eq_true] at hb
    have hK := rep_ranC _ hb.2
    have hR := rep_runC r hb.1
    refine ⟨fun a b h => ?_, fun a b h => ?_⟩
    · have h' : rep (ranC (Bits.runC r).1).1 a b := h
      rw [hK] at h'; exact h'.1
    · show rep (ranC (Bits.runC r).1).1 b b
      rw [hK]; exact ⟨rfl, a, (hR a b).2 h, (hR a b).2 h⟩

theorem pleaf_sound {A B : Obj} {d : Bool} {f : Fn d A B} {T : Den A B} (hf : Sound f T) :
    PSound (pleaf A B d f) T := fun D hD hb x y hx => hf D hD hb x y hx

theorem pcomp_sound {A B C : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pcomp A B C d e R S) (TR ≫ TS) := by
  intro D hD hb x z hx
  simp only [pcomp, Bool.and_eq_true] at hb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  obtain ⟨kc, kk⟩ := demP_spec e _ h2
  have hr := hR D hD h1
  have hs := hS _ kc h3
  exact ⟨fun ⟨b, p1, p2⟩ => ⟨b, (hr x b hx).1 p1, (hs b z (kk x b p1)).1 p2⟩,
    fun ⟨b, p1, p2⟩ => have p1' := (hr x b hx).2 p1; ⟨b, p1', (hs b z (kk x b p1')).2 p2⟩⟩

theorem pconv_sound {A B : Obj} {R : Pl false A B} {T : Den A B} (hR : PSound R T) : PSound (pconv A B R) T° :=
  fun ⟨⟩ _ hb y x _ => hR () trivial hb x y rfl

theorem pmeet_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pmeet A B d e R S) (TR ∩ TS) := fun D hD hb x y hx => by
  simp only [pmeet, Bool.and_eq_true] at hb
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact and_congr (hR _ cl hb.1 x y kl) (hS _ cr hb.2 x y kr)

theorem pjoin_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pjoin A B d e R S) (TR ∪ TS) := fun D hD hb x y hx => by
  simp only [pjoin, Bool.and_eq_true] at hb
  obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
  exact or_congr (hR _ cl hb.1 x y kl) (hS _ cr hb.2 x y kr)

theorem pdiff_sound {A B : Obj} {d e : Bool} {R : Pl d A B} {S : Pl e A B} {TR TS : Den A B}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pdiff A B d e R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  fun D hD hb x y hx => by
    simp only [pdiff, Bool.and_eq_true] at hb
    obtain ⟨cl, kl⟩ := demL d e D x hD hx; obtain ⟨cr, kr⟩ := demR d e D x hD hx
    exact and_congr (hR _ cl hb.1 x y kl) (not_congr (hS _ cr hb.2 x y kr))

/-- `R\S` within the universes `UB`, `UC`: the book's left division where `R` has a column, every pair of the
    universes where it has none. -/
abbrev ldivDen {A B C : Obj} (TR : Den A B) (TS : Den A C) (TB : Den B B) (TC : Den C C) : Den B C :=
  fun b c => (∀ a, TR a b → TS a c) ∧ ((∃ a, TR a b) ∨ ((∃ b', TB b' b) ∧ ∃ c', TC c' c))

theorem pldiv_sound {A B C : Obj} {R : Pl false A B} {S : Pl false A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : PSound (pldiv A B C R S UB UC) (ldivDen TR TS TB TC) :=
  fun ⟨⟩ _ hb b c _ => by
    simp only [pldiv, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    have r a b := hR () trivial h1 a b rfl
    have s a c := hS () trivial h2 a c rfl
    show ((∀ a, _ → _) ∧ ((∃ a, _) ∨ ((∃ p, _) ∧ ∃ j, _))) ↔ _
    rw [valRow, valRow, hB.eq h3, hC.eq h4]
    simp only [r, s]

/-- A closed plan run as bits (`Bits.runC`), its leaves' bits kept: the plan's relation. -/
theorem runP_sound {A B : Obj} {p : Pl false A B} {T : Den A B} (hp : PSound p T) :
    Sound (fun _ => also (p ()).2 (ofC (Bits.runC (p ()).1)) : Fn false A B) T := fun ⟨⟩ _ hb x y _ => by
  simp only [also, ofC, Bool.and_eq_true] at hb ⊢
  exact (rep_runC _ hb.2 x y).trans (hp () trivial hb.1 x y rfl)

theorem compB_sound {A B C : Obj} {e : Bool} {R : Pl false A B} {S : Pl e B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : Sound (compB A B C e R S) (TR ≫ TS) :=
  runP_sound (pcomp_sound hR hS)

theorem meetB_sound {A B : Obj} {R S : Pl false A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (meetB A B R S) (TR ∩ TS) :=
  runP_sound (pmeet_sound (d := false) (e := false) hR hS)

theorem diffB_sound {A B : Obj} {R S : Pl false A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (diffB A B R S) (fun x y => TR x y ∧ ¬ TS x y) :=
  runP_sound (pdiff_sound (d := false) (e := false) hR hS)

theorem ldivB_sound {A B C : Obj} {R : Pl false A B} {S : Pl false A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : Sound (ldivB A B C R S UB UC) (ldivDen TR TS TB TC) :=
  runP_sound (pldiv_sound hR hS hB hC)

end LeetQ.Rel.Lang.Gen
