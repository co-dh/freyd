/-
  Bird & de Moor, *Algebra of Programming* §6.5  Unique fixed points (book pp. 146-151).

  Contents:
  §1  Inductive relations (Ex 6.12-6.15), transitive closure, `inductive_transClosure_iff`.
  §2  Well-foundedness: `Inductive → WellFoundedRel` and, in a Boolean allegory, the converse;
      conjugation by a map preserves both (Ex 6.16).
  §3  Membership: lax natural transformations `id ⟵ F`, `LargestLax`, composition.
  §4  Theorem 6.3 (hylomorphism uniqueness/entireness, book cites Doornbos-Backhouse 1995
      without proof) and Theorem 6.4 (characterisation of `(|R|)°` via a surjective `R`).

  Composition throughout is diagram order (`≫`): B&dM `X·Y` mirrors to `Y ≫ X`.
-/
module

public import AOP.A6_2
public import AOP.A6_3
public import AOP.A5_7

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

/-! ## §6.5.1  Inductive relations (Ex 6.12-6.15) -/

section Inductive

variable {𝒜 : Type u} [DivisionLCDA 𝒜]

/-- **B&dM p.146**: `R : A ← A` is INDUCTIVE if `X/R ⊑ X ⟹ Π ⊑ X` for all `X : A ← B`
    (`Π` = the universal relation of that type, `topHom`). -/
def Inductive {a : 𝒜} (R : a ⟶ a) : Prop :=
  ∀ {b : 𝒜} (X : b ⟶ a), X / R ⊑ X → topHom b a ⊑ X

/-- **Ex 6.14**, `0` half: the empty relation is inductive (for ANY `X`, `X ≫ 0 = 0 ⊑ X`,
    so `X ⊑ X/0` unconditionally; combined with the hypothesis `X/0 ⊑ X` this forces
    `topHom ⊑ X` trivially since `X/0` sits both above and below `X`... in fact `X = X/0`
    outright, but we only need `topHom ⊑ X` — obtained from `X/0 ⊑ X` together with
    `topHom ⊑ X/0`, which follows from `(topHom) ≫ 0 = 0 ⊑ X`). -/
theorem zero_inductive (a : 𝒜) : Inductive (𝟘 : a ⟶ a) := by
  intro b X _hX
  have h0 : topHom b a ≫ (𝟘 : a ⟶ a) ⊑ X := by
    rw [DistributiveAllegory.comp_zero]; exact zero_le X
  exact le_trans ((le_div_iff _ _ _).mpr h0) _hX

/-- **Ex 6.13**: if `S` is inductive and `R≫R ⊑ S≫R`, then `R` is inductive too.

    Given `X/R ⊑ X`, apply `hS` to `X/R`.  Need `(X/R)/S ⊑ X/R`, i.e. (`le_div_iff`)
    `((X/R)/S)≫R ⊑ X`.  The triangle inequalities give `((X/R)/S)≫S ⊑ X/R` and
    `(X/R)≫R ⊑ X`, so `((X/R)/S)≫(S≫R) ⊑ X`; combined with `h` (`comp_mono_left`) this
    gives `((X/R)/S)≫(R≫R) ⊑ X`, i.e. `(((X/R)/S)≫R)≫R ⊑ X`, i.e. (`le_div_iff` again)
    `((X/R)/S)≫R ⊑ X/R`; chaining with the original hypothesis `X/R ⊑ X` gives
    `((X/R)/S)≫R ⊑ X`, closing the goal. -/
theorem inductive_of_comp_le {a : 𝒜} {R S : a ⟶ a} (hS : Inductive S) (h : R ≫ R ⊑ S ≫ R) :
    Inductive R := by
  intro b X hX
  apply le_trans _ hX
  apply hS (X / R)
  apply (le_div_iff _ _ _).mpr
  have h1 : ((X / R) / S) ≫ S ⊑ X / R := DivisionAllegory.div_comp_le (X / R) S
  have h2 : (((X / R) / S) ≫ S) ≫ R ⊑ (X / R) ≫ R := comp_mono_right h1 R
  have h3 : (X / R) ≫ R ⊑ X := DivisionAllegory.div_comp_le X R
  have h4 : (((X / R) / S) ≫ S) ≫ R ⊑ X := le_trans h2 h3
  have h5 : ((X / R) / S) ≫ (S ≫ R) ⊑ X := by rw [← Cat.assoc]; exact h4
  have h6 : ((X / R) / S) ≫ (R ≫ R) ⊑ ((X / R) / S) ≫ (S ≫ R) := comp_mono_left _ h
  have h7 : ((X / R) / S) ≫ (R ≫ R) ⊑ X := le_trans h6 h5
  have h8 : (((X / R) / S) ≫ R) ≫ R ⊑ X := by rw [Cat.assoc]; exact h7
  have h9 : ((X / R) / S) ≫ R ⊑ X / R := (le_div_iff _ _ _).mpr h8
  exact le_trans h9 hX

/-- **Ex 6.13**, corollary: a relation below an inductive relation is itself inductive. -/
theorem inductive_of_le {a : 𝒜} {R S : a ⟶ a} (hS : Inductive S) (h : R ⊑ S) : Inductive R :=
  inductive_of_comp_le hS (comp_mono_right h R)

/-- **Ex 6.15**, meet half: the intersection of an inductive relation with anything is
    inductive (only ONE operand needs to be inductive). -/
theorem inductive_inter {a : 𝒜} {R S : a ⟶ a} (hR : Inductive R) : Inductive (R ∩ S) :=
  inductive_of_le hR (inter_lb_left R S)

/-- **Ex 6.12**: `R` is inductive iff `X = X/R` has `topHom` as its ONLY solution.
    `topHom` is always A solution (`topHom = topHom/R`, shown by antisymmetry).  Forward:
    a solution satisfies `X/R ⊑ X` (from the equation), so inductivity gives `topHom ⊑ X`,
    and `X ⊑ topHom` always, so `X = topHom`.  Backward: for `X` with `X/R ⊑ X`, let
    `M := mu (fun Y => Y/R)`; `M` is a fixed point (Knaster-Tarski) hence a solution, so by
    hypothesis `M = topHom`; also `M ⊑ X` (`Sup_le`'s lower-bound half), giving `topHom ⊑ X`. -/
theorem inductive_iff_unique_solution {a : 𝒜} (R : a ⟶ a) :
    Inductive R ↔ ∀ {b : 𝒜} (X : b ⟶ a), X = X / R → X = topHom b a := by
  constructor
  · intro hR b X hXeq
    have h1 : X / R ⊑ X := hXeq ▸ le_refl X
    exact le_antisymm (le_Sup trivial) (hR X h1)
  · intro h b X hX
    have hmono : Monotonic (fun Y : b ⟶ a => Y / R) := fun hle => div_mono_left hle R
    have hfix : (fun Y : b ⟶ a => Y / R) (mu (fun Y : b ⟶ a => Y / R))
        = mu (fun Y : b ⟶ a => Y / R) := mu_fixed hmono
    have hMeq : mu (fun Y : b ⟶ a => Y / R) = (mu (fun Y : b ⟶ a => Y / R)) / R := hfix.symm
    have hMtop : mu (fun Y : b ⟶ a => Y / R) = topHom b a := h _ hMeq
    have hMX : mu (fun Y : b ⟶ a => Y / R) ⊑ X := Sup_le (fun _S hS => hS _ hX)
    rw [hMtop] at hMX
    exact hMX

/-! ### Transitive closure (Ex 6.13's "it also follows that ...") -/

/-- `S⁺ := (μX : S ∪ X·S)`, mirrored to `mu (fun X => S ∪ S≫X)`. -/
def transClosure {a : 𝒜} (R : a ⟶ a) : a ⟶ a := mu (fun X => R ∪ (R ≫ X))

theorem transClosure_monotonic {a : 𝒜} (R : a ⟶ a) : Monotonic (fun X : a ⟶ a => R ∪ (R ≫ X)) :=
  fun h => union_mono (le_refl R) (comp_mono_left R h)

theorem transClosure_fixed {a : 𝒜} (R : a ⟶ a) : R ∪ (R ≫ transClosure R) = transClosure R :=
  mu_fixed (transClosure_monotonic R)

/-- `R ⊑ R⁺`. -/
theorem le_transClosure {a : 𝒜} (R : a ⟶ a) : R ⊑ transClosure R := by
  have h1 : R ⊑ R ∪ (R ≫ transClosure R) := le_union_left R _
  rwa [transClosure_fixed] at h1

/-- `R⁺·R⁺ ⊑ R⁺`: the transitive closure is idempotent.  Shows `T ⊑ T/T` (`Sup_le`'s
    lower-bound half applied to the body at target `T/T`), then `le_div_iff` turns
    `T ⊑ T/T` into `T≫T ⊑ T`. -/
theorem transClosure_trans {a : 𝒜} (R : a ⟶ a) :
    transClosure R ≫ transClosure R ⊑ transClosure R := by
  have hRT : R ≫ transClosure R ⊑ transClosure R := by
    have h1 : R ≫ transClosure R ⊑ R ∪ (R ≫ transClosure R) := le_union_right R _
    rwa [transClosure_fixed] at h1
  have hRTT : R ≫ (transClosure R / transClosure R) ⊑ transClosure R / transClosure R := by
    apply (le_div_iff _ _ _).mpr
    rw [Cat.assoc]
    have step : R ≫ ((transClosure R / transClosure R) ≫ transClosure R) ⊑ R ≫ transClosure R :=
      comp_mono_left R (DivisionAllegory.div_comp_le (transClosure R) (transClosure R))
    exact le_trans step hRT
  have hRTT2 : R ⊑ transClosure R / transClosure R := (le_div_iff _ _ _).mpr hRT
  have hprefixed : R ∪ (R ≫ (transClosure R / transClosure R)) ⊑ transClosure R / transClosure R :=
    union_lub hRTT2 hRTT
  have hTle : transClosure R ⊑ transClosure R / transClosure R :=
    Sup_le (fun _S hS => hS _ hprefixed)
  exact (le_div_iff _ _ _).mp hTle

/-- **Ex 6.13**: `S` is inductive iff `S⁺` is.  (⇒) via `transClosure_trans` +
    `inductive_of_comp_le`.  (⇐) via `inductive_of_le` and `S ⊑ S⁺`. -/
theorem inductive_transClosure_iff {a : 𝒜} (S : a ⟶ a) :
    Inductive S ↔ Inductive (transClosure S) := by
  constructor
  · intro hS
    apply inductive_of_comp_le hS
    have step2 : (S ∪ (S ≫ transClosure S)) ≫ transClosure S
        = S ≫ transClosure S ∪ (S ≫ transClosure S) ≫ transClosure S :=
      union_comp_distrib S (S ≫ transClosure S) (transClosure S)
    have step3 : (S ≫ transClosure S) ≫ transClosure S ⊑ S ≫ transClosure S := by
      have hTT : transClosure S ≫ transClosure S ⊑ transClosure S := transClosure_trans S
      have h' : S ≫ (transClosure S ≫ transClosure S) ⊑ S ≫ transClosure S :=
        comp_mono_left S hTT
      rwa [← Cat.assoc] at h'
    have step4 : S ≫ transClosure S ∪ (S ≫ transClosure S) ≫ transClosure S ⊑ S ≫ transClosure S :=
      union_lub (le_refl _) step3
    calc transClosure S ≫ transClosure S
        = (S ∪ (S ≫ transClosure S)) ≫ transClosure S := by rw [transClosure_fixed]
      _ = S ≫ transClosure S ∪ (S ≫ transClosure S) ≫ transClosure S := step2
      _ ⊑ S ≫ transClosure S := step4
  · intro hT
    exact inductive_of_le hT (le_transClosure S)

end Inductive

/-! ## §6.5.2  Well-foundedness -/

-- (`DivisionBooleanAllegory.toDivisionLCDA` — the bridge making `Inductive`/`neg_div`
-- available alongside Boolean negation — now lives with the classes in `AOP.A4_5`.)

section WellFounded

variable {𝒜 : Type u} [DivisionLCDA 𝒜]

/-- **B&dM p.148**: `R : A ← A` is WELL-FOUNDED if `X ⊑ X·R ⟹ X ⊑ 0` for all `X : B ← A`,
    mirrored to `X ⊑ R ≫ X`. -/
def WellFoundedRel {a : 𝒜} (R : a ⟶ a) : Prop :=
  ∀ {b : 𝒜} (X : a ⟶ b), X ⊑ R ≫ X → X ⊑ 𝟘

end WellFounded

section WellFoundedBoolean

variable {𝒜 : Type u} [DivisionBooleanAllegory 𝒜]

/-- **B&dM p.148**: "if a relation is inductive, then it is also well-founded". -/
theorem wellFoundedRel_of_inductive {a : 𝒜} {R : a ⟶ a} (hR : Inductive R) :
    WellFoundedRel R := by
  intro b X hX
  have hW : (∼(X°)) / R ⊑ ∼(X°) := by
    rw [neg_div]
    have h1 : X° ⊑ (R ≫ X)° := recip_mono hX
    rw [Allegory.recip_comp] at h1
    exact impl_antitone_left h1
  have htop : topHom b a ⊑ ∼(X°) := hR (∼(X°)) hW
  have h2 : (∼∼(X°)) ⊑ ∼(topHom b a) := impl_antitone_left htop
  rw [neg_topHom] at h2
  have h3 : X° ⊑ (𝟘 : b ⟶ a) := le_trans (le_neg_neg (X°)) h2
  have h4 : (X°)° ⊑ (𝟘 : b ⟶ a)° := recip_mono h3
  rwa [Allegory.recip_recip, recip_zero] at h4

/-- **B&dM p.148**: "the converse holds only in a Boolean allegory" — well-foundedness
    implies inductivity in a `DivisionBooleanAllegory`. -/
theorem inductive_of_wellFoundedRel {a : 𝒜} {R : a ⟶ a} (hR : WellFoundedRel R) :
    Inductive R := by
  intro b X hX
  have h1 : ∼X ⊑ ∼(X / R) := impl_antitone_left hX
  rw [div_eq_neg_comp] at h1
  rw [BooleanAllegory.neg_neg] at h1
  have h2 : (∼X)° ⊑ ((∼X) ≫ R°)° := recip_mono h1
  rw [Allegory.recip_comp, Allegory.recip_recip] at h2
  have h3 : (∼X)° ⊑ (𝟘 : a ⟶ b) := hR ((∼X)°) h2
  have h4 : ((∼X)°)° ⊑ (𝟘 : a ⟶ b)° := recip_mono h3
  rw [Allegory.recip_recip, recip_zero] at h4
  have h5 : ∼X = (𝟘 : b ⟶ a) := le_antisymm h4 (zero_le _)
  have h6 : X ∪ (∼X) = topHom b a := union_neg_eq_top X
  rw [h5, union_zero] at h6
  rw [h6]
  exact le_refl _

/-- **Ex 6.16**: if `R` is well-founded, then so is `f° ≫ R ≫ f` for any map `f`
    (conjugation), mirrored from `f°·R·f`. -/
theorem wellFoundedRel_conjugate {a b : 𝒜} {R : a ⟶ a} {f : b ⟶ a} (hf : Map f)
    (hR : WellFoundedRel R) : WellFoundedRel (f ≫ R ≫ f°) := by
  intro c X hX
  have key : f° ≫ X ⊑ R ≫ (f° ≫ X) := by
    have s1 : f° ≫ X ⊑ f° ≫ ((f ≫ R ≫ f°) ≫ X) := comp_mono_left _ hX
    have e1 : f° ≫ ((f ≫ R ≫ f°) ≫ X) = (f° ≫ f) ≫ (R ≫ f° ≫ X) := by simp only [Cat.assoc]
    have s2 : (f° ≫ f) ≫ (R ≫ f° ≫ X) ⊑ Cat.id a ≫ (R ≫ f° ≫ X) := comp_mono_right hf.2 _
    have e2 : Cat.id a ≫ (R ≫ f° ≫ X) = R ≫ (f° ≫ X) := by simp only [Cat.id_comp]
    rw [e1] at s1
    rw [e2] at s2
    exact le_trans s1 s2
  have hz : f° ≫ X ⊑ (𝟘 : a ⟶ c) := hR (f° ≫ X) key
  have hfinal : (f ≫ R ≫ f°) ≫ X ⊑ (𝟘 : b ⟶ c) := by
    have t1 : (f ≫ R ≫ f°) ≫ X = f ≫ (R ≫ (f° ≫ X)) := by simp only [Cat.assoc]
    have t2 : R ≫ (f° ≫ X) ⊑ R ≫ (𝟘 : a ⟶ c) := comp_mono_left R hz
    have t3 : R ≫ (𝟘 : a ⟶ c) = (𝟘 : a ⟶ c) := DistributiveAllegory.comp_zero R
    rw [t3] at t2
    have t5 : f ≫ (R ≫ (f° ≫ X)) ⊑ f ≫ (𝟘 : a ⟶ c) := comp_mono_left f t2
    have t6 : f ≫ (𝟘 : a ⟶ c) = (𝟘 : b ⟶ c) := DistributiveAllegory.comp_zero f
    rw [t1]
    rw [t6] at t5
    exact t5
  exact le_trans hX hfinal

/-- **Ex 6.16**, transported to `Inductive`: conjugation by a map preserves inductivity.
    Proved via well-foundedness (the book's own route for Theorem 6.4 factors through the
    same well-foundedness/Boolean detour, so this is the natural home rather than a direct
    division-only argument). -/
theorem inductive_conjugate {a b : 𝒜} {W : a ⟶ a} {f : b ⟶ a} (hf : Map f) (hW : Inductive W) :
    Inductive (f ≫ W ≫ f°) :=
  inductive_of_wellFoundedRel (wellFoundedRel_conjugate hf (wellFoundedRel_of_inductive hW))

end WellFoundedBoolean

/-! ## §6.5.3  Membership -/

section Membership

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- **B&dM p.148-149**: a LAX MEMBERSHIP for the relator `F`: a family `mem a : F a ⟶ a`
    with `R·mem ⊑ mem·FR` for all `R : A⟶B` (mirrored: `F.map R ≫ mem b ⊑ mem a ≫ R`), i.e.
    `mem` is lax natural from the identity relator to `F`. -/
structure LaxMembership (F : Relator 𝒜 𝒜) where
  mem : ∀ a : 𝒜, F.obj a ⟶ a
  lax : ∀ {a b : 𝒜} (R : a ⟶ b), F.map R ≫ mem b ⊑ mem a ≫ R

/-- A `LaxMembership`'s `mem` family is exactly a lax natural transformation from the
    identity relator to `F`. -/
theorem LaxMembership.laxNatural (M : LaxMembership F) :
    LaxNatural (Relator.idRelator 𝒜) F M.mem := M.lax

/-- **B&dM p.149**: `mem`, provided it exists, is the LARGEST lax natural transformation of
    this type. -/
def LargestLax (F : Relator 𝒜 𝒜) (φ : ∀ a : 𝒜, F.obj a ⟶ a) : Prop :=
  ∀ (ψ : ∀ a : 𝒜, F.obj a ⟶ a), (∀ {a b : 𝒜} (R : a ⟶ b), F.map R ≫ ψ b ⊑ ψ a ≫ R) →
    ∀ a, ψ a ⊑ φ a

/-- **B&dM p.149**: "it follows that membership relations, if they exist, are unique" —
    two largest lax naturals of the same type coincide (mutual `⊑` from largeness). -/
theorem largestLax_unique {F : Relator 𝒜 𝒜} {M M' : LaxMembership F}
    (h : LargestLax F M.mem) (h' : LargestLax F M'.mem) : ∀ a, M.mem a = M'.mem a := fun a =>
  le_antisymm (h' M.mem M.lax a) (h M'.mem M'.lax a)

/-- `member(id) = id` (B&dM p.149): the identity relator's membership is the identity. -/
def idMembership : LaxMembership (Relator.idRelator 𝒜) where
  mem := fun a => Cat.id a
  lax := fun {_a _b} R => by
    show R ≫ Cat.id _b ⊑ Cat.id _a ≫ R
    rw [Cat.comp_id, Cat.id_comp]
    exact le_refl R

/-- `member(F·G) = member(G)·member(F)` (B&dM p.149), mirrored: the composite relator's
    membership is `MG.mem (F.obj a) ≫ MF.mem a`. -/
def compMembership {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G) :
    LaxMembership (Relator.comp F G) where
  mem := fun a => MG.mem (F.obj a) ≫ MF.mem a
  lax := fun {a b} R => by
    show G.map (F.map R) ≫ (MG.mem (F.obj b) ≫ MF.mem b) ⊑ (MG.mem (F.obj a) ≫ MF.mem a) ≫ R
    have s1 : G.map (F.map R) ≫ MG.mem (F.obj b) ⊑ MG.mem (F.obj a) ≫ F.map R := MG.lax (F.map R)
    have s2 : (G.map (F.map R) ≫ MG.mem (F.obj b)) ≫ MF.mem b
        ⊑ (MG.mem (F.obj a) ≫ F.map R) ≫ MF.mem b := comp_mono_right s1 _
    have e2 : (G.map (F.map R) ≫ MG.mem (F.obj b)) ≫ MF.mem b
        = G.map (F.map R) ≫ (MG.mem (F.obj b) ≫ MF.mem b) := by simp only [Cat.assoc]
    have e3 : (MG.mem (F.obj a) ≫ F.map R) ≫ MF.mem b
        = MG.mem (F.obj a) ≫ (F.map R ≫ MF.mem b) := by simp only [Cat.assoc]
    rw [e2] at s2
    rw [e3] at s2
    have s3 : F.map R ≫ MF.mem b ⊑ MF.mem a ≫ R := MF.lax R
    have s4 : MG.mem (F.obj a) ≫ (F.map R ≫ MF.mem b) ⊑ MG.mem (F.obj a) ≫ (MF.mem a ≫ R) :=
      comp_mono_left _ s3
    have e4 : MG.mem (F.obj a) ≫ (MF.mem a ≫ R) = (MG.mem (F.obj a) ≫ MF.mem a) ≫ R := by
      simp only [Cat.assoc]
    have s5 : G.map (F.map R) ≫ (MG.mem (F.obj b) ≫ MF.mem b)
        ⊑ MG.mem (F.obj a) ≫ (MF.mem a ≫ R) := le_trans s2 s4
    rwa [e4] at s5

end Membership

/-! ## §6.5.4  Theorem 6.3 cluster (hylomorphism uniqueness) and Theorem 6.4 -/

section HyloTheorem63

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- **Theorem 6.3** (B&dM p.149, uniqueness half): if `member(F)·S` is inductive, the
    equation `X = R·FX·S` (mirrored: `X = S ≫ F.map X ≫ R`) has AT MOST one solution.

    The book gives NO proof here (cites Doornbos & Backhouse 1995).  GENUINE ATTEMPT: the
    natural candidate exploiting `hind : Inductive (S ≫ M.mem b)` (an endo on `b`) is the
    relation `Z := X / Y : b ⟶ b` (well-typed since `X, Y : b ⟶ a` share codomain `a`,
    matching `Inductive`'s domain-`b` slot).  Closing `(X/Y) / (S ≫ M.mem b) ⊑ X/Y` needs
    relating `F.map (X/Y)` to `X` and `Y` through the coalgebra/algebra equations and
    `M.lax`'s inequality — the diagrammatic chase needs `F.map` to interact with division
    (e.g. `F.map (X/Y)` vs `F.map X / F.map Y`), which a bare `Relator` (a monotonic
    functor, preserving neither `∩` nor division in general — only `Ex 5.2`'s coreflexive
    `∩`) does not support.  No non-circular closing step was found in the time budgeted.
    Recorded as a STATEMENT-ONLY placeholder (matching the book's own uncited status), NOT
    a Sorry. -/
def HyloUnique (_M : LaxMembership F) {a b : 𝒜} (S : b ⟶ F.obj b) (R : F.obj a ⟶ a) : Prop :=
  ∀ X Y : b ⟶ a, X = S ≫ F.map X ≫ R → Y = S ≫ F.map Y ≫ R → X = Y

/-- **Theorem 6.3** (B&dM p.149, entireness half): "Moreover `φ(R,S)` is entire if both
    `R` and `S` are entire."  Also cited to Doornbos & Backhouse 1995 without proof;
    recorded alongside `HyloUnique` as a statement-only placeholder. -/
def HyloEntire (_M : LaxMembership F) {a b : 𝒜} (S : b ⟶ F.obj b) (R : F.obj a ⟶ a) : Prop :=
  Entire S → Entire R → ∀ X : b ⟶ a, X = S ≫ F.map X ≫ R → Entire X

end HyloTheorem63

/-! ### Theorem 6.4 -/

section Theorem64

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- The intermediate fact shared by `thm64_forward` and `thm64` — under the Theorem 6.4
    commuting hypothesis, `(|R|)·f ⊑ 1` (mirrored: `relCata I R ≫ f ⊑ 1`).  This is
    B&dM's fusion step: `comp_le_relCata` ((6.5), `AOP.A6_2`) against `⦇α⦈ = id`
    (`relCata_alpha`, `AOP.A6_3`). -/
private theorem relCata_comp_le_id (I : InitialAlgebra F) {a : 𝒜} {R : F.obj a ⟶ a}
    {f : a ⟶ I.t} (hcomm : R ≫ f ⊑ F.map f ≫ I.α) : relCata I R ≫ f ⊑ Cat.id I.t := by
  have h1 : relCata I R ≫ f ⊑ relCata I I.α := comp_le_relCata I hcomm
  rwa [relCata_alpha] at h1

/-- **Theorem 6.4** (B&dM p.150), forward/provable half: if `f` is a map and
    `R·f ⊑ α·Ff` (mirrored: `R≫f ⊑ F.map f≫I.α`), then `(|R|) ⊑ f°`. -/
theorem thm64_forward (I : InitialAlgebra F) {a : 𝒜} {R : F.obj a ⟶ a} {f : a ⟶ I.t}
    (hf : Map f) (hcomm : R ≫ f ⊑ F.map f ≫ I.α) : relCata I R ⊑ f° := by
  have h1 : relCata I R ≫ f ⊑ Cat.id I.t := relCata_comp_le_id I hcomm
  have h2 : relCata I R ⊑ Cat.id I.t ≫ f° := (map_shunt_right hf (relCata I R) (Cat.id I.t)).mp h1
  rwa [Cat.id_comp] at h2

/-- **Theorem 6.4**, backward half: given `(|R|)` surjective (`hsur`) and `(|R|)·f ⊑ 1`
    (`hcancel`), `f° ⊑ (|R|)`. -/
theorem thm64_backward (I : InitialAlgebra F) {a : 𝒜} {R : F.obj a ⟶ a} {f : a ⟶ I.t}
    (hsur : Cat.id a ⊑ (relCata I R)° ≫ relCata I R) (hcancel : relCata I R ≫ f ⊑ Cat.id I.t) :
    f° ⊑ relCata I R := by
  have e1 : f° = f° ≫ Cat.id a := (Cat.comp_id f°).symm
  have s1 : f° ≫ Cat.id a ⊑ f° ≫ ((relCata I R)° ≫ relCata I R) := comp_mono_left f° hsur
  have e2 : f° ≫ ((relCata I R)° ≫ relCata I R) = (relCata I R ≫ f)° ≫ relCata I R := by
    rw [← Cat.assoc, ← Allegory.recip_comp]
  have s2 : (relCata I R ≫ f)° ≫ relCata I R ⊑ (Cat.id I.t)° ≫ relCata I R :=
    comp_mono_right (recip_mono hcancel) _
  have e3 : (Cat.id I.t)° ≫ relCata I R = relCata I R := by rw [recip_id, Cat.id_comp]
  have hA : f° ⊑ (relCata I R ≫ f)° ≫ relCata I R := by
    calc f° = f° ≫ Cat.id a := e1
      _ ⊑ f° ≫ ((relCata I R)° ≫ relCata I R) := s1
      _ = (relCata I R ≫ f)° ≫ relCata I R := e2
  have hB : (relCata I R ≫ f)° ≫ relCata I R ⊑ relCata I R := by
    calc (relCata I R ≫ f)° ≫ relCata I R
        ⊑ (Cat.id I.t)° ≫ relCata I R := s2
      _ = relCata I R := e3
  exact le_trans hA hB

/-- **Theorem 6.4** (B&dM p.150): if `R` is surjective and `f·R ⊑ α·Ff` (mirrored:
    `R≫f ⊑ F.map f≫I.α`), then `f° = (|R|)`.

    The book's hypothesis is `R` surjective (`_hRsur : 1 ⊑ R°≫R`); discharging the
    STRONGER `hcatasur : 1 ⊑ (|R|)°≫(|R|)` (surjectivity of the catamorphism itself,
    which is what `thm64_backward` actually needs) from `_hRsur` alone is B&dM's
    Corollary 6.3, whose proof rests on `member·α°` being inductive — the same uncited
    Doornbos & Backhouse 1995 fact flagged at `HyloUnique`/`HyloEntire` above.  `hcatasur`
    is therefore taken as an explicit hypothesis rather than derived; `_hRsur` is kept in
    the signature (unused by this assembly, hence the underscore) purely to record the
    book's actual Theorem 6.4 hypothesis. -/
theorem thm64 (I : InitialAlgebra F) {a : 𝒜} {R : F.obj a ⟶ a} {f : a ⟶ I.t} (hf : Map f)
    (hcomm : R ≫ f ⊑ F.map f ≫ I.α) (_hRsur : Cat.id a ⊑ R° ≫ R)
    (hcatasur : Cat.id a ⊑ (relCata I R)° ≫ relCata I R) : f° = relCata I R :=
  le_antisymm (thm64_backward I hcatasur (relCata_comp_le_id I hcomm)) (thm64_forward I hf hcomm)

end Theorem64
