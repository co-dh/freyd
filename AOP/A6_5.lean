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
import AOP.CalcSteps

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

/-! ## §6.5.1  Inductive relations (Ex 6.12-6.15) -/

section Inductive

variable {𝒜 : Type u} [DivisionLCDA 𝒜]

/-- **B&dM p.146**: `R : A ← A` is INDUCTIVE if `X/R ⊑ X ⟹ Π ⊑ X` for all `X : A ← B`
    (`Π` = the universal relation of that type, `topHom`). -/
@[expose] public def Inductive {A : 𝒜} (R : A ⟶ A) : Prop :=
  ∀ {B : 𝒜} (X : B ⟶ A), X / R ⊑ X → topHom B A ⊑ X

/-- **Ex 6.14**, `0` half: the empty relation is inductive (for ANY `X`, `X ≫ 0 = 0 ⊑ X`,
    so `X ⊑ X/0` unconditionally; combined with the hypothesis `X/0 ⊑ X` this forces
    `topHom ⊑ X` trivially since `X/0` sits both above and below `X`... in fact `X = X/0`
    outright, but we only need `topHom ⊑ X` — obtained from `X/0 ⊑ X` together with
    `topHom ⊑ X/0`, which follows from `(topHom) ≫ 0 = 0 ⊑ X`). -/
public theorem zero_inductive (A : 𝒜) : Inductive (𝟘 : A ⟶ A) := by
  intro B X _hX
  have h0 : topHom B A ≫ (𝟘 : A ⟶ A) ⊑ X := by
    rw [DistributiveAllegory.comp_zero]; exact zero_le X
  exact le_trans ((le_div_iff _ _ _).mpr h0) _hX

/-- Ex 6.13, the inequality its proof derives: `((X/R)/S)RR ⊑ X` when `RR ⊑ SR`. -/
public theorem div_div_comp_le {A B : 𝒜} {R S : A ⟶ A} (h : R ≫ R ⊑ S ≫ R) (X : B ⟶ A) :
    ((X / R) / S) ≫ R ≫ R ⊑ X :=
  calc ((X / R) / S) ≫ R ≫ R ⊑ ((X / R) / S) ≫ S ≫ R := comp_mono_left _ h
    _ ⊑ (X / R) ≫ R := by
      rw [← Cat.assoc]; exact comp_mono_right (DivisionAllegory.div_comp_le (X / R) S) R
    _ ⊑ X := DivisionAllegory.div_comp_le X R

calc_steps div_div_comp_le

/-- **Ex 6.13**: if `S` is inductive and `R≫R ⊑ S≫R`, then `R` is inductive too.

    Given `X/R ⊑ X`, apply `hS` to `X/R`.  Need `(X/R)/S ⊑ X/R`, i.e. (`le_div_iff`)
    `((X/R)/S)≫R ⊑ X`.  The triangle inequalities give `((X/R)/S)≫S ⊑ X/R` and
    `(X/R)≫R ⊑ X`, so `((X/R)/S)≫(S≫R) ⊑ X`; combined with `h` (`comp_mono_left`) this
    gives `((X/R)/S)≫(R≫R) ⊑ X`, i.e. `(((X/R)/S)≫R)≫R ⊑ X`, i.e. (`le_div_iff` again)
    `((X/R)/S)≫R ⊑ X/R`; chaining with the original hypothesis `X/R ⊑ X` gives
    `((X/R)/S)≫R ⊑ X`, closing the goal. -/
public theorem inductive_of_comp_le {A : 𝒜} {R S : A ⟶ A} (hS : Inductive S) (h : R ≫ R ⊑ S ≫ R) :
    Inductive R := by
  intro B X hX
  apply le_trans _ hX
  apply hS (X / R)
  apply (le_div_iff _ _ _).mpr
  have h7 := div_div_comp_le h X
  rw [← Cat.assoc] at h7
  exact le_trans ((le_div_iff _ _ _).mpr h7) hX

/-- **Ex 6.13**, corollary: a relation below an inductive relation is itself inductive. -/
public theorem inductive_of_le {A : 𝒜} {R S : A ⟶ A} (hS : Inductive S) (h : R ⊑ S) : Inductive R :=
  inductive_of_comp_le hS (comp_mono_right h R)

/-- **Ex 6.15**, meet half: the intersection of an inductive relation with anything is
    inductive (only ONE operand needs to be inductive). -/
public theorem inductive_inter {A : 𝒜} {R S : A ⟶ A} (hR : Inductive R) : Inductive (R ∩ S) :=
  inductive_of_le hR (inter_lb_left R S)

/-- **Ex 6.16**, for `Inductive`: conjugation by a map preserves inductivity, `f W f°` inductive
    when `W` is.  Division alone does it: `Z/f°` is the test relation for `W` (a Boolean detour
    through well-foundedness would tie Theorem 6.4 to a Boolean allegory). -/
public theorem inductive_conjugate {A B : 𝒜} {W : A ⟶ A} {f : B ⟶ A} (hf : Map f) (hW : Inductive W) :
    Inductive (f ≫ W ≫ f°) := by
  intro C Z hZ
  have h1 : (Z / f°) / W ⊑ Z / f° := by
    apply (le_div_iff _ _ _).mpr
    apply le_trans _ hZ
    apply (le_div_iff _ _ _).mpr
    have e : (((Z / f°) / W) ≫ f°) ≫ (f ≫ W ≫ f°) = ((Z / f°) / W) ≫ (f° ≫ f) ≫ W ≫ f° := by
      simp only [Cat.assoc]
    rw [e]
    have s1 : ((Z / f°) / W) ≫ (f° ≫ f) ≫ W ≫ f° ⊑ ((Z / f°) / W) ≫ W ≫ f° := by
      have := comp_mono_left ((Z / f°) / W) (comp_mono_right hf.2 (W ≫ f°))
      rwa [Cat.id_comp] at this
    have s2 : ((Z / f°) / W) ≫ W ≫ f° ⊑ Z := by
      rw [← Cat.assoc]
      exact le_trans (comp_mono_right (DivisionAllegory.div_comp_le _ W) f°)
        (DivisionAllegory.div_comp_le Z f°)
    exact le_trans s1 s2
  have h2 : topHom C A ⊑ Z / f° := hW _ h1
  have s1 : topHom C B ⊑ topHom C B ≫ (f ≫ f°) := by
    have := comp_mono_left (topHom C B) (map_entire_le hf); rwa [Cat.comp_id] at this
  have s2 : topHom C B ≫ (f ≫ f°) ⊑ topHom C A ≫ f° := by
    rw [← Cat.assoc]; exact comp_mono_right (le_Sup trivial) f°
  exact le_trans s1 (le_trans s2 (le_trans (comp_mono_right h2 f°) (DivisionAllegory.div_comp_le Z f°)))

/-- **Ex 6.12**: `R` is inductive iff `X = X/R` has `topHom` as its ONLY solution.
    `topHom` is always A solution (`topHom = topHom/R`, shown by antisymmetry).  Forward:
    a solution satisfies `X/R ⊑ X` (from the equation), so inductivity gives `topHom ⊑ X`,
    and `X ⊑ topHom` always, so `X = topHom`.  Backward: for `X` with `X/R ⊑ X`, let
    `M := mu (fun Y => Y/R)`; `M` is a fixed point (Knaster-Tarski) hence a solution, so by
    hypothesis `M = topHom`; also `M ⊑ X` (`Sup_le`'s lower-bound half), giving `topHom ⊑ X`. -/
public theorem inductive_iff_unique_solution {A : 𝒜} (R : A ⟶ A) :
    Inductive R ↔ ∀ {B : 𝒜} (X : B ⟶ A), X = X / R → X = topHom B A := by
  constructor
  · intro hR B X hXeq
    have h1 : X / R ⊑ X := hXeq ▸ le_refl X
    exact le_antisymm (le_Sup trivial) (hR X h1)
  · intro h B X hX
    have hmono : Monotonic (fun Y : B ⟶ A => Y / R) := fun hle => div_mono_left hle R
    have hfix : (fun Y : B ⟶ A => Y / R) (mu (fun Y : B ⟶ A => Y / R))
        = mu (fun Y : B ⟶ A => Y / R) := mu_fixed hmono
    have hMeq : mu (fun Y : B ⟶ A => Y / R) = (mu (fun Y : B ⟶ A => Y / R)) / R := hfix.symm
    have hMtop : mu (fun Y : B ⟶ A => Y / R) = topHom B A := h _ hMeq
    have hMX : mu (fun Y : B ⟶ A => Y / R) ⊑ X := Sup_le (fun _S hS => hS _ hX)
    rw [hMtop] at hMX
    exact hMX

/-! ### Transitive closure (Ex 6.13's "it also follows that ...") -/

/-- `S⁺ := (μX : S ∪ X·S)`, mirrored to `mu (fun X => S ∪ S≫X)`. -/
public def transClosure {A : 𝒜} (R : A ⟶ A) : A ⟶ A := mu (fun X => R ∪ (R ≫ X))

public theorem transClosure_monotonic {A : 𝒜} (R : A ⟶ A) : Monotonic (fun X : A ⟶ A => R ∪ (R ≫ X)) :=
  fun h => union_mono (le_refl R) (comp_mono_left R h)

public theorem transClosure_fixed {A : 𝒜} (R : A ⟶ A) : R ∪ (R ≫ transClosure R) = transClosure R :=
  mu_fixed (transClosure_monotonic R)

/-- `R ⊑ R⁺`. -/
public theorem le_transClosure {A : 𝒜} (R : A ⟶ A) : R ⊑ transClosure R := by
  have h1 : R ⊑ R ∪ (R ≫ transClosure R) := le_union_left R _
  rwa [transClosure_fixed] at h1

/-- `R⁺·R⁺ ⊑ R⁺`: the transitive closure is idempotent.  Shows `T ⊑ T/T` (`Sup_le`'s
    lower-bound half applied to the body at target `T/T`), then `le_div_iff` turns
    `T ⊑ T/T` into `T≫T ⊑ T`. -/
public theorem transClosure_trans {A : 𝒜} (R : A ⟶ A) :
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
public theorem inductive_transClosure_iff {A : 𝒜} (S : A ⟶ A) :
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
public def WellFoundedRel {A : 𝒜} (R : A ⟶ A) : Prop :=
  ∀ {B : 𝒜} (X : A ⟶ B), X ⊑ R ≫ X → X ⊑ 𝟘

end WellFounded

section WellFoundedBoolean

variable {𝒜 : Type u} [DivisionBooleanAllegory 𝒜]

/-- **B&dM p.148**: "if a relation is inductive, then it is also well-founded". -/
public theorem wellFoundedRel_of_inductive {A : 𝒜} {R : A ⟶ A} (hR : Inductive R) :
    WellFoundedRel R := by
  intro B X hX
  have hW : (∼(X°)) / R ⊑ ∼(X°) := by
    rw [neg_div]
    have h1 : X° ⊑ (R ≫ X)° := recip_mono hX
    rw [Allegory.recip_comp] at h1
    exact impl_antitone_left h1
  have htop : topHom B A ⊑ ∼(X°) := hR (∼(X°)) hW
  have h2 : (∼∼(X°)) ⊑ ∼(topHom B A) := impl_antitone_left htop
  rw [neg_topHom] at h2
  have h3 : X° ⊑ (𝟘 : B ⟶ A) := le_trans (le_neg_neg (X°)) h2
  have h4 : (X°)° ⊑ (𝟘 : B ⟶ A)° := recip_mono h3
  rwa [Allegory.recip_recip, recip_zero] at h4

/-- **B&dM p.148**: "the converse holds only in a Boolean allegory" — well-foundedness
    implies inductivity in a `DivisionBooleanAllegory`. -/
public theorem inductive_of_wellFoundedRel {A : 𝒜} {R : A ⟶ A} (hR : WellFoundedRel R) :
    Inductive R := by
  intro B X hX
  have h1 : ∼X ⊑ ∼(X / R) := impl_antitone_left hX
  rw [div_eq_neg_comp] at h1
  rw [BooleanAllegory.neg_neg] at h1
  have h2 : (∼X)° ⊑ ((∼X) ≫ R°)° := recip_mono h1
  rw [Allegory.recip_comp, Allegory.recip_recip] at h2
  have h3 : (∼X)° ⊑ (𝟘 : A ⟶ B) := hR ((∼X)°) h2
  have h4 : ((∼X)°)° ⊑ (𝟘 : A ⟶ B)° := recip_mono h3
  rw [Allegory.recip_recip, recip_zero] at h4
  have h5 : ∼X = (𝟘 : B ⟶ A) := le_antisymm h4 (zero_le _)
  have h6 : X ∪ (∼X) = topHom B A := union_neg_eq_top X
  rw [h5, union_zero] at h6
  rw [h6]
  exact le_refl _

/-- **Ex 6.16**: if `R` is well-founded, then so is `f° ≫ R ≫ f` for any map `f`
    (conjugation), mirrored from `f°·R·f`. -/
public theorem wellFoundedRel_conjugate {A B : 𝒜} {R : A ⟶ A} {f : B ⟶ A} (hf : Map f)
    (hR : WellFoundedRel R) : WellFoundedRel (f ≫ R ≫ f°) := by
  intro C X hX
  have key : f° ≫ X ⊑ R ≫ (f° ≫ X) := by
    have s1 : f° ≫ X ⊑ f° ≫ ((f ≫ R ≫ f°) ≫ X) := comp_mono_left _ hX
    have e1 : f° ≫ ((f ≫ R ≫ f°) ≫ X) = (f° ≫ f) ≫ (R ≫ f° ≫ X) := by simp only [Cat.assoc]
    have s2 : (f° ≫ f) ≫ (R ≫ f° ≫ X) ⊑ Cat.id A ≫ (R ≫ f° ≫ X) := comp_mono_right hf.2 _
    have e2 : Cat.id A ≫ (R ≫ f° ≫ X) = R ≫ (f° ≫ X) := by simp only [Cat.id_comp]
    rw [e1] at s1
    rw [e2] at s2
    exact le_trans s1 s2
  have hz : f° ≫ X ⊑ (𝟘 : A ⟶ C) := hR (f° ≫ X) key
  have hfinal : (f ≫ R ≫ f°) ≫ X ⊑ (𝟘 : B ⟶ C) := by
    have t1 : (f ≫ R ≫ f°) ≫ X = f ≫ (R ≫ (f° ≫ X)) := by simp only [Cat.assoc]
    have t2 : R ≫ (f° ≫ X) ⊑ R ≫ (𝟘 : A ⟶ C) := comp_mono_left R hz
    have t3 : R ≫ (𝟘 : A ⟶ C) = (𝟘 : A ⟶ C) := DistributiveAllegory.comp_zero R
    rw [t3] at t2
    have t5 : f ≫ (R ≫ (f° ≫ X)) ⊑ f ≫ (𝟘 : A ⟶ C) := comp_mono_left f t2
    have t6 : f ≫ (𝟘 : A ⟶ C) = (𝟘 : B ⟶ C) := DistributiveAllegory.comp_zero f
    rw [t1]
    rw [t6] at t5
    exact t5
  exact le_trans hX hfinal

end WellFoundedBoolean

/-! ## §6.5.3  Membership -/

section Membership

variable {𝒜 : Type u} [Allegory 𝒜] {F : Relator 𝒜 𝒜}

/-- **B&dM p.148-149**: a LAX MEMBERSHIP for the relator `F`: a family `mem a : F a ⟶ a`
    with `R·mem ⊑ mem·FR` for all `R : A⟶B` (mirrored: `F.map R ≫ mem b ⊑ mem a ≫ R`), i.e.
    `mem` is lax natural from the identity relator to `F`. -/
public structure LaxMembership (F : Relator 𝒜 𝒜) where
  mem : ∀ A : 𝒜, F.obj A ⟶ A
  lax : ∀ {A B : 𝒜} (R : A ⟶ B), F.map R ≫ mem B ⊑ mem A ≫ R

/-- A `LaxMembership`'s `mem` family is exactly a lax natural transformation from the
    identity relator to `F`. -/
public theorem LaxMembership.laxNatural (M : LaxMembership F) :
    LaxNatural (Relator.idRelator 𝒜) F M.mem := M.lax

/-- **B&dM p.149**: `mem`, provided it exists, is the LARGEST lax natural transformation of
    this type. -/
public def LargestLax (F : Relator 𝒜 𝒜) (φ : ∀ A : 𝒜, F.obj A ⟶ A) : Prop :=
  ∀ (ψ : ∀ A : 𝒜, F.obj A ⟶ A), (∀ {A B : 𝒜} (R : A ⟶ B), F.map R ≫ ψ B ⊑ ψ A ≫ R) →
    ∀ A, ψ A ⊑ φ A

/-- **B&dM p.149**: "it follows that membership relations, if they exist, are unique" —
    two largest lax naturals of the same type coincide (mutual `⊑` from largeness). -/
public theorem largestLax_unique {F : Relator 𝒜 𝒜} {M M' : LaxMembership F}
    (h : LargestLax F M.mem) (h' : LargestLax F M'.mem) : ∀ A, M.mem A = M'.mem A := fun A =>
  le_antisymm (h' M.mem M.lax A) (h M'.mem M'.lax A)

/-- `member(id) = id` (B&dM p.149): the identity relator's membership is the identity. -/
public def idMembership : LaxMembership (Relator.idRelator 𝒜) where
  mem := fun A => Cat.id A
  lax := fun {_a _b} R => by
    show R ≫ Cat.id _b ⊑ Cat.id _a ≫ R
    rw [Cat.comp_id, Cat.id_comp]
    exact le_refl R

/-- `member(F·G) = member(G)·member(F)` (B&dM p.149), mirrored: the composite relator's
    membership is `MG.mem (F.obj a) ≫ MF.mem a`. -/
public def compMembership {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G) :
    LaxMembership (Relator.comp F G) where
  mem := fun A => MG.mem (F.obj A) ≫ MF.mem A
  lax := fun {A B} R => by
    show G.map (F.map R) ≫ (MG.mem (F.obj B) ≫ MF.mem B) ⊑ (MG.mem (F.obj A) ≫ MF.mem A) ≫ R
    have s1 : G.map (F.map R) ≫ MG.mem (F.obj B) ⊑ MG.mem (F.obj A) ≫ F.map R := MG.lax (F.map R)
    have s2 : (G.map (F.map R) ≫ MG.mem (F.obj B)) ≫ MF.mem B
        ⊑ (MG.mem (F.obj A) ≫ F.map R) ≫ MF.mem B := comp_mono_right s1 _
    have e2 : (G.map (F.map R) ≫ MG.mem (F.obj B)) ≫ MF.mem B
        = G.map (F.map R) ≫ (MG.mem (F.obj B) ≫ MF.mem B) := by simp only [Cat.assoc]
    have e3 : (MG.mem (F.obj A) ≫ F.map R) ≫ MF.mem B
        = MG.mem (F.obj A) ≫ (F.map R ≫ MF.mem B) := by simp only [Cat.assoc]
    rw [e2] at s2
    rw [e3] at s2
    have s3 : F.map R ≫ MF.mem B ⊑ MF.mem A ≫ R := MF.lax R
    have s4 : MG.mem (F.obj A) ≫ (F.map R ≫ MF.mem B) ⊑ MG.mem (F.obj A) ≫ (MF.mem A ≫ R) :=
      comp_mono_left _ s3
    have e4 : MG.mem (F.obj A) ≫ (MF.mem A ≫ R) = (MG.mem (F.obj A) ≫ MF.mem A) ≫ R := by
      simp only [Cat.assoc]
    have s5 : G.map (F.map R) ≫ (MG.mem (F.obj B) ≫ MF.mem B)
        ⊑ MG.mem (F.obj A) ≫ (MF.mem A ≫ R) := le_trans s2 s4
    rwa [e4] at s5

end Membership

section ConstMembership

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- `member(K_B) = 𝟘` (B&dM p.148): a constant records no elements. -/
@[expose] public def constMembership (B : 𝒜) : LaxMembership (Relator.const (𝒜 := 𝒜) B) where
  mem _ := 𝟘
  lax _ := by rw [DistributiveAllegory.comp_zero, DistributiveAllegory.zero_comp]; exact le_refl _

/-- The p.148 row `member(K) = 𝟘`. -/
public theorem member_const (B A : 𝒜) : (constMembership B).mem A = 𝟘 := rfl

end ConstMembership

-- Each polynomial relator's membership in the least structure its relator needs: a sum needs the
-- coproducts, a product the tabulated pairs.
section SumMembership

variable {𝒜 : Type u} [PositiveAllegory 𝒜]

/-- `member(F+G) = [member(F), member(G)]` (B&dM p.148): a member of either summand. -/
@[expose] public def sumMembership {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G) :
    LaxMembership (Relator.sum F G) where
  mem A := junc (PositiveAllegory.has_coproduct _ _) (MF.mem A) (MG.mem A)
  lax R := junc_slides _ _ (MF.lax R) (MG.lax R)

/-- The p.148 row `member(F+G) = [member(F), member(G)]`, as the arrow `sumMembership` IS. -/
public theorem member_sum {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G) (A : 𝒜) :
    (sumMembership MF MG).mem A = junc (PositiveAllegory.has_coproduct _ _) (MF.mem A) (MG.mem A) :=
  rfl

end SumMembership

section ProdMembership

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] [HasRelProd 𝒜]

/-- `member(F×G) = outl member(F) ∪ outr member(G)` (B&dM p.148), mirrored: a member of either
    component. -/
@[expose] public def prodMembership {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G) :
    LaxMembership (Relator.prod F G) where
  mem A := (relProd (F.obj A) (G.obj A)).outl ≫ MF.mem A ∪ (relProd (F.obj A) (G.obj A)).outr ≫ MG.mem A
  lax {A B} R := by
    show prodMap _ _ (F.map R) (G.map R) ≫ ((relProd _ _).outl ≫ MF.mem B ∪ (relProd _ _).outr ≫ MG.mem B)
      ⊑ ((relProd _ _).outl ≫ MF.mem A ∪ (relProd _ _).outr ≫ MG.mem A) ≫ R
    rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
    refine union_mono ?_ ?_
    · have := comp_mono_right (outl_laxNatural F G R) (MF.mem B)
      simp only [Cat.assoc] at this ⊢
      exact le_trans this (comp_mono_left _ (MF.lax R))
    · have := comp_mono_right (outr_laxNatural F G R) (MG.mem B)
      simp only [Cat.assoc] at this ⊢
      exact le_trans this (comp_mono_left _ (MG.lax R))

/-- The p.148 row `member(F×G) = outl member(F) ∪ outr member(G)`, mirrored. -/
public theorem member_prod {F G : Relator 𝒜 𝒜} (MF : LaxMembership F) (MG : LaxMembership G)
    (A : 𝒜) : (prodMembership MF MG).mem A
      = (relProd (F.obj A) (G.obj A)).outl ≫ MF.mem A ∪ (relProd (F.obj A) (G.obj A)).outr ≫ MG.mem A :=
  rfl

end ProdMembership

section MembershipAll

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜]

/-- **B&dM Ex 6.18**, the coreflexive half of the formal definition: a MEMBERSHIP is a lax
    membership whose relator keeps every `s` all of whose members pass the coreflexive `Q`.  The
    lax inequality alone does not pin `mem` down — `mem = 𝟘` satisfies it, and then Theorem 6.3
    would solve p.146's equation uniquely, which `X = 𝟙` refutes. -/
public structure Membership (F : Relator 𝒜 𝒜) extends LaxMembership F where
  all : ∀ {B : 𝒜} {Q : B ⟶ B}, cor Q → 𝟙 (F.obj B) ∩ ((mem B ≫ Q) / mem B) ⊑ F.map Q

end MembershipAll

/-! ## §6.5.4  Theorem 6.3 (unique fixed points) and its corollaries -/

section Theorem63

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- Every `W` factors through the coreflexive of the points it reaches: `W ⊑ Π(𝟙 ∩ ΠW)`. -/
public theorem le_topHom_dom {C B : 𝒜} (W : C ⟶ B) : W ⊑ topHom C B ≫ (𝟙 B ∩ topHom B C ≫ W) := by
  have h := modular_le_right (topHom C B) (𝟙 B) W
  rw [Cat.comp_id, recip_topHom] at h
  exact le_trans (le_inter (le_Sup trivial) (le_refl W)) h

/-- A coreflexive `Q` with `Π ⊑ ΠQ` is the identity. -/
public theorem id_le_of_topHom_le {B : 𝒜} {Q : B ⟶ B} (hQ : cor Q)
    (h : topHom B B ⊑ topHom B B ≫ Q) : 𝟙 B ⊑ Q := by
  have h1 : 𝟙 B ⊑ (topHom B B ≫ Q) ∩ 𝟙 B := le_inter (le_trans (le_Sup trivial) h) (le_refl _)
  have h2 : topHom B B ∩ 𝟙 B ≫ Q° ⊑ 𝟙 B := by
    rw [Cat.id_comp]; exact le_trans (inter_lb_right _ _) (by have := recip_mono hQ; rwa [recip_id] at this)
  have h3 := comp_mono_right h2 Q
  exact le_trans h1 (le_trans (modular_le _ _ _) (le_trans h3 (by rw [Cat.id_comp]; exact le_refl _)))

/-- The induction step of Theorem 6.3: where every member of an `S`-image passes `Q` after `W`,
    the points `P` that `W` reaches go through `S` into `F(Q)`. -/
public theorem membership_step (M : Membership F) {B C : 𝒜} (S : B ⟶ F.obj B) {Q : B ⟶ B}
    (hQ : cor Q) (W : C ⟶ B) (hW : W ≫ S ≫ M.mem B ⊑ topHom C B ≫ Q) :
    (𝟙 B ∩ topHom B C ≫ W) ≫ S ⊑ S ≫ F.map Q := by
  have hUS : (𝟙 B ∩ topHom B C ≫ W) ≫ S ⊑ S := by
    have := comp_mono_right (inter_lb_left (𝟙 B) (topHom B C ≫ W)) S; rwa [Cat.id_comp] at this
  have hUm : ((𝟙 B ∩ topHom B C ≫ W) ≫ S) ≫ M.mem B ⊑ topHom B B ≫ Q := by
    have s1 := comp_mono_right (comp_mono_right (inter_lb_right (𝟙 B) (topHom B C ≫ W)) S) (M.mem B)
    have e : ((topHom B C ≫ W) ≫ S) ≫ M.mem B = topHom B C ≫ (W ≫ S ≫ M.mem B) := by
      simp only [Cat.assoc]
    rw [e] at s1
    have s2 : topHom B C ≫ (topHom C B ≫ Q) ⊑ topHom B B ≫ Q := by
      rw [← Cat.assoc]; exact comp_mono_right (le_Sup trivial) Q
    exact le_trans s1 (le_trans (comp_mono_left _ hW) s2)
  generalize (𝟙 B ∩ topHom B C ≫ W) ≫ S = U at hUS hUm
  have hU : U ⊑ U ≫ (𝟙 (F.obj B) ∩ U° ≫ U) := by
    have := modular_le_right U (𝟙 (F.obj B)) U
    rw [Cat.comp_id] at this
    exact le_trans (le_inter (le_refl U) (le_refl U)) this
  have hG : 𝟙 (F.obj B) ∩ U° ≫ U ⊑ 𝟙 (F.obj B) ∩ ((M.mem B ≫ Q) / M.mem B) := by
    refine le_inter (inter_lb_left _ _) ((le_div_iff _ _ _).mpr ?_)
    have s1 := inter_comp_le (𝟙 (F.obj B)) (U° ≫ U) (M.mem B)
    rw [Cat.id_comp, Cat.assoc] at s1
    have s2 : U° ≫ U ≫ M.mem B ⊑ (U° ≫ topHom B B) ≫ Q := by
      rw [Cat.assoc]; exact comp_mono_left _ hUm
    have s3 : M.mem B ∩ U° ≫ U ≫ M.mem B ⊑ ((U° ≫ topHom B B) ≫ Q) ∩ M.mem B :=
      le_inter (le_trans (inter_lb_right _ _) s2) (inter_lb_left _ _)
    have s4 : (U° ≫ topHom B B ∩ M.mem B ≫ Q°) ≫ Q ⊑ M.mem B ≫ Q := by
      have hQr : Q° ⊑ 𝟙 B := by have := recip_mono hQ; rwa [recip_id] at this
      have t1 : (U° ≫ topHom B B ∩ M.mem B ≫ Q°) ≫ Q ⊑ (M.mem B ≫ Q°) ≫ Q :=
        comp_mono_right (inter_lb_right _ _) Q
      have t2 : (M.mem B ≫ Q°) ≫ Q ⊑ (M.mem B ≫ 𝟙 B) ≫ Q :=
        comp_mono_right (comp_mono_left _ hQr) Q
      rw [Cat.comp_id] at t2
      exact le_trans t1 t2
    exact le_trans s1 (le_trans s3 (le_trans (modular_le _ _ _) s4))
  exact le_trans hU (le_trans (comp_mono_left U hG)
    (le_trans (comp_mono_right hUS _) (comp_mono_left S (M.all hQ))))

/-- **Theorem 6.3**, its induction principle: when `S member(F)` is inductive, a coreflexive `Q`
    that holds wherever `S` sends every member into `Q` holds everywhere. -/
public theorem thm63_induction (M : Membership F) {B : 𝒜} (S : B ⟶ F.obj B)
    (hind : Inductive (S ≫ M.mem B)) {Q : B ⟶ B} (hQ : cor Q)
    (hclosed : ∀ P : B ⟶ B, P ⊑ 𝟙 B → P ≫ S ⊑ S ≫ F.map Q → P ⊑ Q) : 𝟙 B ⊑ Q := by
  apply id_le_of_topHom_le hQ
  apply hind
  have hP := hclosed _ (inter_lb_left _ _)
    (membership_step M S hQ _ (DivisionAllegory.div_comp_le (topHom B B ≫ Q) (S ≫ M.mem B)))
  have h := le_topHom_dom ((topHom B B ≫ Q) / (S ≫ M.mem B))
  exact le_trans h (comp_mono_left _ hP)

/-- **Theorem 6.3**, uniqueness as an inequality: when `S member(F)` is inductive, a solution of
    `X = SF(X)R` lies below every `Y` with `SF(Y)R ⊑ Y`. -/
public theorem thm63_le (M : Membership F) {A B : 𝒜} {S : B ⟶ F.obj B} {R : F.obj A ⟶ A}
    (hind : Inductive (S ≫ M.mem B)) {X Y : B ⟶ A} (hX : X = S ≫ F.map X ≫ R)
    (hY : S ≫ F.map Y ≫ R ⊑ Y) : X ⊑ Y := by
  have hQ : cor (𝟙 B ∩ (Y / X)) := inter_lb_left _ _
  have h := thm63_induction M S hind hQ (fun P hP hPS => by
    refine le_inter hP ((le_div_iff _ _ _).mpr ?_)
    have hQX : (𝟙 B ∩ (Y / X)) ≫ X ⊑ Y :=
      le_trans (comp_mono_right (inter_lb_right _ _) X) (DivisionAllegory.div_comp_le Y X)
    calc P ≫ X = (P ≫ S) ≫ F.map X ≫ R := by rw [Cat.assoc, ← hX]
      _ ⊑ (S ≫ F.map (𝟙 B ∩ (Y / X))) ≫ F.map X ≫ R := comp_mono_right hPS _
      _ = S ≫ F.map ((𝟙 B ∩ (Y / X)) ≫ X) ≫ R := by rw [F.map_comp]; simp only [Cat.assoc]
      _ ⊑ S ≫ F.map Y ≫ R := comp_mono_left S (comp_mono_right (F.map_mono hQX) R)
      _ ⊑ Y := hY)
  have := comp_mono_right (le_trans h (inter_lb_right _ _)) X
  rw [Cat.id_comp] at this
  exact le_trans this (DivisionAllegory.div_comp_le Y X)

/-- **Theorem 6.3** (B&dM p.149): if `S member(F)` is inductive, `X = SF(X)R` has at most one
    solution. -/
public theorem thm63_unique (M : Membership F) {A B : 𝒜} {S : B ⟶ F.obj B} {R : F.obj A ⟶ A}
    (hind : Inductive (S ≫ M.mem B)) {X Y : B ⟶ A} (hX : X = S ≫ F.map X ≫ R)
    (hY : Y = S ≫ F.map Y ≫ R) : X = Y :=
  le_antisymm (thm63_le M hind hX (by rw [← hY]; exact le_refl _))
    (thm63_le M hind hY (by rw [← hX]; exact le_refl _))

/-- **Theorem 6.3** (B&dM p.149), entire half: if `S member(F)` is inductive and `R`, `S` are
    entire, every `X` with `SF(X)R ⊑ X` is entire — the unique solution in particular. -/
public theorem thm63_entire (M : Membership F) {A B : 𝒜} {S : B ⟶ F.obj B} {R : F.obj A ⟶ A}
    (hind : Inductive (S ≫ M.mem B)) (hS : Entire S) (hR : Entire R) {X : B ⟶ A}
    (hX : S ≫ F.map X ≫ R ⊑ X) : Entire X := by
  have hQ : cor (𝟙 B ∩ X ≫ topHom A B) := inter_lb_left _ _
  have hRtop : topHom (F.obj A) B ⊑ R ≫ topHom A B := by
    have := comp_mono_right (entire_id_le hR) (topHom (F.obj A) B)
    rw [Cat.id_comp, Cat.assoc] at this
    exact le_trans this (comp_mono_left R (le_Sup trivial))
  have h := thm63_induction M S hind hQ (fun P hP hPS => by
    refine le_inter hP ?_
    have s1 : P ⊑ (P ≫ S) ≫ S° := by
      have := comp_mono_left P (entire_id_le hS); rwa [Cat.comp_id, ← Cat.assoc] at this
    have s2 : F.map (𝟙 B ∩ X ≫ topHom A B) ≫ S° ⊑ F.map X ≫ topHom (F.obj A) B := by
      have := comp_mono_right (F.map_mono (inter_lb_right (𝟙 B) (X ≫ topHom A B))) S°
      rw [F.map_comp, Cat.assoc] at this
      exact le_trans this (comp_mono_left _ (le_Sup trivial))
    calc P ⊑ (P ≫ S) ≫ S° := s1
      _ ⊑ (S ≫ F.map (𝟙 B ∩ X ≫ topHom A B)) ≫ S° := comp_mono_right hPS _
      _ ⊑ S ≫ F.map X ≫ topHom (F.obj A) B := by rw [Cat.assoc]; exact comp_mono_left S s2
      _ ⊑ S ≫ F.map X ≫ R ≫ topHom A B := comp_mono_left S (comp_mono_left _ hRtop)
      _ ⊑ X ≫ topHom A B := by
        have := comp_mono_right hX (topHom A B); simp only [Cat.assoc] at this; exact this)
  have h2 : 𝟙 B ⊑ X ≫ X° := by
    have := modular_le_right X (topHom A B) (𝟙 B)
    rw [Cat.comp_id] at this
    exact le_trans (le_trans h (le_inter (inter_lb_right _ _) (inter_lb_left _ _)))
      (le_trans this (comp_mono_left X (inter_lb_right _ _)))
  have := (cover_iff_recip_entire X°).mp (by rwa [Allegory.recip_recip])
  rwa [Allegory.recip_recip] at this

/-- **Theorem 6.3** (B&dM p.149): if `S member(F)` is inductive, the equation `X = SF(X)R` has a
    unique solution `φ(R,S) = μX : SF(X)R` — its least fixed point solves it (Knaster–Tarski),
    every solution equals it (`thm63_unique`), and it is entire when `R` and `S` are
    (`thm63_entire`). -/
public theorem thm63 (M : Membership F) {A B : 𝒜} {S : B ⟶ F.obj B} {R : F.obj A ⟶ A}
    (hind : Inductive (S ≫ M.mem B)) :
    mu (fun X : B ⟶ A => S ≫ F.map X ≫ R) = S ≫ F.map (mu (fun X : B ⟶ A => S ≫ F.map X ≫ R)) ≫ R
    ∧ (∀ Y : B ⟶ A, Y = S ≫ F.map Y ≫ R → Y = mu (fun X : B ⟶ A => S ≫ F.map X ≫ R))
    ∧ (Entire S → Entire R → Entire (mu (fun X : B ⟶ A => S ≫ F.map X ≫ R))) := by
  have hfix : mu (fun X : B ⟶ A => S ≫ F.map X ≫ R)
      = S ≫ F.map (mu (fun X : B ⟶ A => S ≫ F.map X ≫ R)) ≫ R :=
    (mu_fixed (fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R))).symm
  exact ⟨hfix, fun Y hY => thm63_unique M hind hY hfix,
    fun hS hR => thm63_entire M hind hS hR (by rw [← hfix]; exact le_refl _)⟩

/-- Corollary 6.2, simple half: when `X = gF(X)f`, `g` and `f` are simple and `Y°X ⊑ 𝟙`, then
    `(gF(Y)f)°X ⊑ 𝟙`; one law per step. -/
public theorem cor62_simple {A B : 𝒜} {g : B ⟶ F.obj B} {f : F.obj A ⟶ A} {X Y : B ⟶ A}
    (hX : X = g ≫ F.map X ≫ f) (hg : Simple g) (hf : Simple f) (hY : Y° ≫ X ⊑ 𝟙 A) :
    (g ≫ F.map Y ≫ f)° ≫ X ⊑ 𝟙 A :=
  calc (g ≫ F.map Y ≫ f)° ≫ X = (g ≫ F.map Y ≫ f)° ≫ g ≫ F.map X ≫ f := by rw [← hX]
    _ = f° ≫ (F.map Y)° ≫ g° ≫ g ≫ F.map X ≫ f := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Cat.assoc, Cat.assoc]
    _ = f° ≫ F.map Y° ≫ g° ≫ g ≫ F.map X ≫ f := by rw [Relator.preservesRecip_of_tabular F Y]
    _ ⊑ f° ≫ F.map Y° ≫ 𝟙 (F.obj B) ≫ F.map X ≫ f := by
        rw [← Cat.assoc g°]; exact comp_mono_left f° (comp_mono_left _ (comp_mono_right hg _))
    _ = f° ≫ F.map Y° ≫ F.map X ≫ f := by rw [Cat.id_comp]
    _ = f° ≫ F.map (Y° ≫ X) ≫ f := by rw [F.map_comp, Cat.assoc]
    _ ⊑ f° ≫ F.map (𝟙 A) ≫ f := comp_mono_left f° (comp_mono_right (F.map_mono hY) f)
    _ = f° ≫ 𝟙 (F.obj A) ≫ f := by rw [F.map_id]
    _ = f° ≫ f := by rw [Cat.id_comp]
    _ ⊑ 𝟙 A := hf

calc_steps cor62_simple

/-- **Corollary 6.2** (B&dM p.149): if `g member(F)` is inductive and `f`, `g` are maps, the
    solution of `X = gF(X)f` is a map — entire by Theorem 6.3, simple (Ex 6.10) by Theorem 6.3's
    induction against `X ∩ (𝟙/X)°`. -/
public theorem cor62 (M : Membership F) {A B : 𝒜} {g : B ⟶ F.obj B} {f : F.obj A ⟶ A}
    (hind : Inductive (g ≫ M.mem B)) (hg : Map g) (hf : Map f) {X : B ⟶ A}
    (hX : X = g ≫ F.map X ≫ f) : Map X := by
  refine ⟨thm63_entire M hind hg.1 hf.1 (by rw [← hX]; exact le_refl _), ?_⟩
  have hYX : (X ∩ (𝟙 A / X)°)° ≫ X ⊑ 𝟙 A := by
    have := comp_mono_right (recip_mono (inter_lb_right X (𝟙 A / X)°)) X
    rw [Allegory.recip_recip] at this
    exact le_trans this (DivisionAllegory.div_comp_le (𝟙 A) X)
  have hY : g ≫ F.map (X ∩ (𝟙 A / X)°) ≫ f ⊑ X ∩ (𝟙 A / X)° := by
    refine le_inter ?_ ?_
    · have := comp_mono_left g (comp_mono_right (F.map_mono (inter_lb_left X (𝟙 A / X)°)) f)
      rwa [← hX] at this
    · have h := cor62_simple hX hg.2 hf.2 hYX
      have := recip_mono ((le_div_iff _ _ _).mpr h)
      rwa [Allegory.recip_recip] at this
  have h1 := recip_mono (le_trans (thm63_le M hind hX hY) (inter_lb_right _ _))
  rw [Allegory.recip_recip] at h1
  exact (le_div_iff _ _ _).mp h1

/-- **Corollary 6.2** (B&dM p.149), the book's proof: the unique solution of `X = gF(X)f` is the
    hylomorphism `⦇f⦈⦇g°⦈°` (Theorem 6.2), and it is a function (`cor62`). -/
public theorem cor62_hylo (I : InitialAlgebra F) (M : Membership F) {A B : 𝒜} {g : B ⟶ F.obj B}
    {f : F.obj A ⟶ A} (hind : Inductive (g ≫ M.mem B)) (hg : Map g) (hf : Map f) :
    Map ((relCata g°)° ≫ relCata f)
    ∧ ∀ Y : B ⟶ A, Y = g ≫ F.map Y ≫ f → Y = (relCata g°)° ≫ relCata f := by
  have h := hylo_eq_mu I f g°
  simp only [Allegory.recip_recip] at h
  obtain ⟨hfix, huniq, -⟩ := thm63 M (R := f) hind
  rw [h]
  exact ⟨cor62 M hind hg hf hfix, huniq⟩

/-- **Corollary 6.3** (B&dM p.149): if `R° member(F)` is inductive, `⦇R⦈` is surjective when `R`
    is — `⦇R⦈°` solves `X = R°F(X)α`, entire by Theorem 6.3. -/
public theorem cor63 (I : InitialAlgebra F) (M : Membership F) {A : 𝒜} {R : F.obj A ⟶ A}
    (hind : Inductive (R° ≫ M.mem A)) (hR : 𝟙 A ⊑ R° ≫ R) :
    𝟙 A ⊑ (relCata R)° ≫ relCata R := by
  have hfix : relCata R = I.α° ≫ F.map (relCata R) ≫ R := (eq_relCata_iff_fixed I R _).mpr rfl
  have hX : R° ≫ F.map (relCata R)° ≫ I.α ⊑ (relCata R)° := by
    conv => rhs; rw [hfix]
    simp only [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc,
      Relator.preservesRecip_of_tabular F]
    exact le_refl _
  have hE := thm63_entire M hind ((cover_iff_recip_entire R).mp hR) I.α_map.1 hX
  have := entire_id_le hE
  rwa [Allegory.recip_recip] at this

end Theorem63

/-! ### Theorem 6.4 -/

section Theorem64

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- The intermediate fact shared by `thm64_forward` and `thm64` — under the Theorem 6.4
    commuting hypothesis, `(|R|)·f ⊑ 1` (mirrored: `relCata I R ≫ f ⊑ 1`).  This is
    B&dM's fusion step: `comp_le_relCata` ((6.5), `AOP.A6_2`) against `⦇α⦈ = id`
    (`relCata_alpha`, `AOP.A6_3`). -/
private theorem relCata_comp_le_id (I : InitialAlgebra F) {A : 𝒜} {R : F.obj A ⟶ A}
    {f : A ⟶ I.t} (hcomm : R ≫ f ⊑ F.map f ≫ I.α) : relCata R ≫ f ⊑ 𝟙 I.t := by
  have h1 : relCata R ≫ f ⊑ relCata I.α := comp_le_relCata I hcomm
  rwa [relCata_alpha] at h1

/-- **Theorem 6.4** (B&dM p.150), forward/provable half: if `f` is a map and
    `R·f ⊑ α·Ff` (mirrored: `R≫f ⊑ F.map f≫I.α`), then `(|R|) ⊑ f°`. -/
public theorem thm64_forward (I : InitialAlgebra F) {A : 𝒜} {R : F.obj A ⟶ A} {f : A ⟶ I.t}
    (hf : Map f) (hcomm : R ≫ f ⊑ F.map f ≫ I.α) : relCata R ⊑ f° := by
  have h1 : relCata R ≫ f ⊑ 𝟙 I.t := relCata_comp_le_id I hcomm
  have h2 : relCata R ⊑ 𝟙 I.t ≫ f° := (map_shunt_right hf (relCata R) (𝟙 I.t)).mp h1
  rwa [Cat.id_comp] at h2

/-- **Theorem 6.4**, backward half: given `(|R|)` surjective (`hsur`) and `(|R|)·f ⊑ 1`
    (`hcancel`), `f° ⊑ (|R|)`. -/
public theorem thm64_backward (I : InitialAlgebra F) {A : 𝒜} {R : F.obj A ⟶ A} {f : A ⟶ I.t}
    (hsur : 𝟙 A ⊑ (relCata R)° ≫ relCata R) (hcancel : relCata R ≫ f ⊑ 𝟙 I.t) :
    f° ⊑ relCata R := by
  have s1 : f° ≫ 𝟙 A ⊑ f° ≫ ((relCata R)° ≫ relCata R) := comp_mono_left f° hsur
  have e2 : f° ≫ ((relCata R)° ≫ relCata R) = (relCata R ≫ f)° ≫ relCata R := by
    rw [← Cat.assoc, ← Allegory.recip_comp]
  have s2 : (relCata R ≫ f)° ≫ relCata R ⊑ (𝟙 I.t)° ≫ relCata R :=
    comp_mono_right (recip_mono hcancel) _
  rw [Cat.comp_id, e2] at s1
  rw [recip_id, Cat.id_comp] at s2
  exact le_trans s1 s2

/-- The claim in Theorem 6.4, its shunting half: `Rf ⊑ F(f)α` shunted and conversed to
    `R°F(f) ⊑ fα°`, against `F(f)` entire, gives `R° ⊑ fα°F(f°)`. -/
public theorem thm64_recip_le (I : InitialAlgebra F) {A : 𝒜} {R : F.obj A ⟶ A} {f : A ⟶ I.t}
    (hf : Map f) (hcomm : R ≫ f ⊑ F.map f ≫ I.α) : R° ⊑ f ≫ I.α° ≫ F.map f° := by
  have hE : 𝟙 (F.obj A) ⊑ F.map f ≫ F.map f° := by
    rw [← F.map_comp, ← F.map_id]; exact F.map_mono (map_entire_le hf)
  have s1 := comp_mono_left R° hE
  rw [Cat.comp_id] at s1
  have h2 := recip_mono ((map_shunt_right hf R _).mp hcomm)
  simp only [Allegory.recip_comp, Allegory.recip_recip] at h2
  have h3 : R° ≫ F.map f ⊑ f ≫ I.α° := by
    have := comp_mono_right h2 (F.map f)
    simp only [Cat.assoc] at this
    have hs := comp_mono_left f (comp_mono_left I.α° (Relator.map_is_map F hf).2)
    rw [Cat.comp_id] at hs
    exact le_trans this hs
  have s2 := comp_mono_right h3 (F.map f°)
  simp only [Cat.assoc] at s2
  exact le_trans s1 s2

/-- **Theorem 6.4**, the claim (B&dM p.150): `R° member ⊑ f α° member f°`, so `R° member` is
    inductive when `α° member` is (Ex 6.16, conjugation, then p.147, below an inductive):
    `R° ⊑ fα°F(f°)`, then `member` lax natural. -/
public theorem thm64_claim (I : InitialAlgebra F) (M : Membership F) {A : 𝒜} {R : F.obj A ⟶ A}
    {f : A ⟶ I.t} (hf : Map f) (hcomm : R ≫ f ⊑ F.map f ≫ I.α) :
    R° ≫ M.mem A ⊑ f ≫ (I.α° ≫ M.mem I.t) ≫ f° :=
  calc R° ≫ M.mem A ⊑ f ≫ I.α° ≫ F.map f° ≫ M.mem A := by
        rw [← Cat.assoc I.α°, ← Cat.assoc f]; exact comp_mono_right (thm64_recip_le I hf hcomm) _
    _ ⊑ f ≫ (I.α° ≫ M.mem I.t) ≫ f° := by
        rw [Cat.assoc I.α°]; exact comp_mono_left f (comp_mono_left I.α° (M.lax f°))

calc_steps thm64_claim

/-- **B&dM p.148**, "the central result": `member(F)·α°` (mirrored: `α° ≫ member`) is inductive.
    Given `X/(α°member) ⊑ X`, the points `W` that `X` reaches from everywhere satisfy
    `α°F(W)α ⊑ W` by lax naturality of `member`, so `𝟙 = ⦇α⦈ ⊑ W` by initiality. -/
public theorem alpha_member_inductive (I : InitialAlgebra F) (M : LaxMembership F) :
    Inductive (I.α° ≫ M.mem I.t) := by
  intro B X hX
  -- `W` is the largest relation with `ΠW ⊑ X`.
  have hW : topHom B I.t ≫ (X° / topHom I.t B)° ⊑ X := by
    have := recip_mono (DivisionAllegory.div_comp_le X° (topHom I.t B))
    simpa only [Allegory.recip_comp, Allegory.recip_recip, recip_topHom] using this
  have hleW : ∀ V : I.t ⟶ I.t, topHom B I.t ≫ V ⊑ X → V ⊑ (X° / topHom I.t B)° := fun V h => by
    have h1 := recip_mono h
    simp only [Allegory.recip_comp, recip_topHom] at h1
    have := recip_mono ((le_div_iff _ _ _).mpr h1)
    rwa [Allegory.recip_recip] at this
  have hid : 𝟙 I.t ⊑ (X° / topHom I.t B)° := by
    rw [← relCata_alpha I]
    refine relCata_le_of_prefixed I (hleW _ (le_trans ?_ hX))
    refine (le_div_iff _ _ _).mpr ?_
    have e : (topHom B I.t ≫ I.α° ≫ F.map (X° / topHom I.t B)° ≫ I.α) ≫ I.α° ≫ M.mem I.t
        = topHom B I.t ≫ I.α° ≫ F.map (X° / topHom I.t B)° ≫ M.mem I.t := by
      simp only [Cat.assoc]; rw [← Cat.assoc I.α, I.alpha_alpha_recip, Cat.id_comp]
    rw [e]
    have s1 := comp_mono_left (topHom B I.t ≫ I.α°) (M.lax (X° / topHom I.t B)°)
    have s2 : (topHom B I.t ≫ I.α°) ≫ M.mem I.t ≫ (X° / topHom I.t B)°
        ⊑ topHom B I.t ≫ (X° / topHom I.t B)° := by
      rw [← Cat.assoc]; exact comp_mono_right (le_Sup trivial) _
    simp only [Cat.assoc] at s1 s2
    exact le_trans s1 (le_trans s2 hW)
  have := comp_mono_left (topHom B I.t) hid
  rw [Cat.comp_id] at this
  exact le_trans this hW

/-- **Theorem 6.4** (B&dM p.150): if `R` is surjective and `Rf ⊑ F(f)α`, then `f° = ⦇R⦈`. -/
public theorem thm64 (I : InitialAlgebra F) (M : Membership F) {A : 𝒜} {R : F.obj A ⟶ A}
    {f : A ⟶ I.t} (hf : Map f) (hcomm : R ≫ f ⊑ F.map f ≫ I.α) (hR : 𝟙 A ⊑ R° ≫ R) :
    f° = relCata R :=
  le_antisymm
    (thm64_backward I (cor63 I M (inductive_of_le
      (inductive_conjugate hf (alpha_member_inductive I M.toLaxMembership))
      (thm64_claim I M hf hcomm)) hR) (relCata_comp_le_id I hcomm))
    (thm64_forward I hf hcomm)

end Theorem64
