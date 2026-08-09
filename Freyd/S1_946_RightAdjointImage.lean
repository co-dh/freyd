/-
  Freyd & Scedrov, *Categories and Allegories* §1.946 — the SUBOBJECT-LEVEL
  RIGHT ADJOINT to inverse image, `f## = ∀_f : Sub(A) → Sub(B)`, for `f : A → B`
  in any topos, built (Sorry-free) via the internal-∀ family-glb machinery of
  `Freyd/InternalForallTopos.lean`.

  ## What this file builds

  For `f : A → B` and `A' ↣ A`, the right adjoint `f## A' ↣ B` has characteristic
  map `radjChar f A' : B → Ω`,

      χ_{f## A'}(b)  =  ∀ a : A.  (f(a) = b) ⇒ (a ∈ A').

  The quantified body `radjBody f A' : prod A B → Ω` sends `(a,b) ↦ (f(a)=b) ⇒ (a∈A')`,
  where `f(a)=b` is the diagonal-classifier equality predicate `⟨fst≫f, snd⟩ ≫ χ_{Δ_B}`
  and `a∈A'` is `fst ≫ χ_{A'}`.  Currying in the `a`-slot and post-composing with
  `forallC A` performs the universal quantification over `a` (the §1.94 fibered-∀ trick,
  identical to `predF`/`tStable`/`bigInterChar`).

  Then `f## A' := InverseImage (radjChar f A') {true}` (the subobject of `B` classified by
  `radjChar f A'`, via `classify_invImage_true`), and we PROVE the adjunction

      (InverseImage f B').le A'  ↔  B'.le (radjImage f A')          (`f* ⊣ f##`)

  closing the `HasRightAdjointImage` field (S1_70) that `S1_94` needs.
-/

module

public import Freyd.S1_94_InternalForallTopos
public import Freyd.S1_987_LeastClosedTopos

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.946  The body `(a,b) ↦ (f(a)=b) ⇒ (a∈A')` and the characteristic map -/

/-- The equality predicate `eqPred f : prod A B → Ω`, `(a,b) ↦ (f(a) = b)`.  It is the
    diagonal classifier of `B` precomposed with `⟨fst≫f, snd⟩`; `diag_classify_iff` makes
    it `⊤` at `⟨a,b⟩` exactly when `f(a) = b`. -/
@[expose] public noncomputable def eqPred {A B : 𝒞} (f : A ⟶ B) : prod A B ⟶ omega (𝒞 := 𝒞) :=
  pair (fst ≫ f) snd ≫ HasSubobjectClassifier.classify (diag B) (diag_mono B)

/-- The right-adjoint body `prod A B → Ω`: `(a,b) ↦ (f(a)=b) ⇒ (a∈A')`.  `f(a)=b` is
    `eqPred f`; `a∈A'` is `fst ≫ subChar A'`; combined with `impΩ`. -/
@[expose] public noncomputable def radjBody {A B : 𝒞} (f : A ⟶ B) (A' : Subobject 𝒞 A) :
    prod A B ⟶ omega (𝒞 := 𝒞) :=
  pair (eqPred f) (fst ≫ subChar A') ≫ impΩ

/-- The characteristic map `radjChar f A' : B → Ω` of `f## A'`: curry the body in the
    `A`-slot, then universally quantify over `a : A` with `forallC A`. -/
@[expose] public noncomputable def radjChar {A B : 𝒞} (f : A ⟶ B) (A' : Subobject 𝒞 A) :
    B ⟶ omega (𝒞 := 𝒞) :=
  curry (radjBody f A') ≫ forallC A

/-- **§1.946 — the right adjoint `f## A'`** to inverse image, as the subobject of `B`
    classified by `radjChar f A'` (the pullback of `true` along it). -/
@[expose] public noncomputable def radjImage {A B : 𝒞} (f : A ⟶ B) (A' : Subobject 𝒞 A) : Subobject 𝒞 B :=
  InverseImage (radjChar f A') ⟨one, true (𝒞 := 𝒞), HasSubobjectClassifier.true_monic⟩

/-- `radjImage f A'` is classified by `radjChar f A'`. -/
public theorem classify_radjImage {A B : 𝒞} (f : A ⟶ B) (A' : Subobject 𝒞 A) :
    HasSubobjectClassifier.classify (radjImage f A').arr (radjImage f A').monic
      = radjChar f A' :=
  classify_invImage_true (radjChar f A')

/-! ## §1.946  The adjunction `(f* B').le A' ↔ B'.le (f## A')` -/

/-- **`eqPred` at a generalized point.**  `k ≫ eqPred f = ⊤∘!` iff `(k≫fst)≫f = k≫snd`,
    i.e. the `A`-component maps to the `B`-component under `f`.  From `diag_classify_iff`. -/
public theorem eqPred_true_iff {A B K : 𝒞} (f : A ⟶ B) (k : K ⟶ prod A B) :
    k ≫ eqPred f = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
      ↔ (k ≫ fst) ≫ f = k ≫ snd := by
  rw [eqPred, ← Cat.assoc]
  rw [show k ≫ pair (fst ≫ f) snd = pair ((k ≫ fst) ≫ f) (k ≫ snd) from by
        apply pair_uniq
        · rw [Cat.assoc, fst_pair, Cat.assoc]
        · rw [Cat.assoc, snd_pair]]
  exact diag_classify_iff ((k ≫ fst) ≫ f) (k ≫ snd)

/-- **Forward — `(f* B').le A' → B'.le (f## A')`.**

    Reduces (via `le_iff_classify`, `classify_radjImage`, `forall_beta`, `curry_precomp`)
    to the prod-body equation `prodMap A B'.dom B B'.arr ≫ radjBody f A' = ⊤∘!` over
    `prod A B'.dom`, i.e. the §1.91 Heyting implication `S_eq ⇒ S_∈A'` is entire, which by
    `impΩ_entire_of_le` is `S_eq ≤ S_∈A'`.  On the carrier of `S_eq`, `f(a) = B'.arr(d)` is
    in `B'`, so `f(a) ∈ B'` ⟹ (hypothesis `f* B' ≤ A'`) `a ∈ A'`. -/
public theorem radjImage_adjunction_forward {A B : 𝒞} (f : A ⟶ B)
    (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A)
    (hle : (InverseImage f B').le A') : B'.le (radjImage f A') := by
  apply (le_iff_classify B' (radjImage f A')).2
  rw [classify_radjImage, radjChar, ← Cat.assoc]
  rw [forall_beta A (B'.arr ≫ curry (radjBody f A'))]
  rw [curry_precomp]
  rw [show topName A
        = curry (fst ≫ HasSubobjectClassifier.classify (Subobject.entire A).arr
            (Subobject.entire A).monic) from rfl]
  rw [curry_precomp]
  apply congrArg curry
  rw [← Cat.assoc, prodMap_fst, classify_entire, ← Cat.assoc,
    term_uniq (fst ≫ term A) (term (prod A B'.dom))]
  -- Goal: prodMap A B'.dom B B'.arr ≫ radjBody f A' = term ≫ true.  Split into impΩ.
  let chiEq : prod A B'.dom ⟶ omega (𝒞 := 𝒞) := prodMap A B'.dom B B'.arr ≫ eqPred f
  let chiA' : prod A B'.dom ⟶ omega (𝒞 := 𝒞) := fst ≫ subChar A'
  have hsplit : prodMap A B'.dom B B'.arr ≫ radjBody f A'
      = pair chiEq chiA' ≫ impΩ := by
    rw [radjBody, ← Cat.assoc]
    congr 1
    apply pair_uniq
    · show _ = chiEq
      rw [Cat.assoc, fst_pair]
    · show _ = chiA'
      rw [Cat.assoc, snd_pair, ← Cat.assoc, prodMap_fst]
  rw [hsplit, pair_impΩ]
  -- Realize chiEq, chiA' as subobjects S_eq, S_A' of prod A B'.dom.
  obtain ⟨_, mEq, hmEq, hSEq⟩ := classify_surjective chiEq
  obtain ⟨_, mA', hmA', hSA'⟩ := classify_surjective chiA'
  let S_eq : Subobject 𝒞 (prod A B'.dom) := ⟨_, mEq, hmEq⟩
  let S_A' : Subobject 𝒞 (prod A B'.dom) := ⟨_, mA', hmA'⟩
  have hcEq : subChar S_eq = chiEq := hSEq
  have hcA' : subChar S_A' = chiA' := hSA'
  rw [show pair chiEq (pair chiEq chiA' ≫ omegaMeet) ≫ heytingDoubleArrow
        = subChar (Sub.imp S_eq S_A') by rw [classify_imp, impChar, hcEq, hcA']]
  -- entire ≤ (S_eq ⇒ S_A') iff S_eq ≤ S_A'.
  have hp : HasPullback S_eq.arr (Subobject.entire (prod A B'.dom)).arr := HasPullbacks.has _ _
  have hSle : S_eq.le S_A' := by
    apply (allows_iff_classify S_A' S_eq.arr).2
    rw [show HasSubobjectClassifier.classify S_A'.arr S_A'.monic = chiA' from hcA']
    -- carrier k := S_eq.arr satisfies chiEq = ⊤: f(k≫fst) = B'.arr(k≫snd) (eqPred_true_iff).
    have hcarEq : S_eq.arr ≫ chiEq = term S_eq.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [show chiEq = HasSubobjectClassifier.classify S_eq.arr S_eq.monic from hcEq.symm]
      exact HasSubobjectClassifier.classify_sq S_eq.arr S_eq.monic
    -- the eqPred over the carrier k≫prodMap : f((k≫prodMap)≫fst) = (k≫prodMap)≫snd.
    have hkeq : (S_eq.arr ≫ prodMap A B'.dom B B'.arr) ≫ eqPred f
        = term S_eq.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      rw [Cat.assoc]; exact hcarEq
    have hfeq := (eqPred_true_iff f (S_eq.arr ≫ prodMap A B'.dom B B'.arr)).1 hkeq
    -- hfeq : ((k≫prodMap)≫fst)≫f = (k≫prodMap)≫snd, i.e. f(k≫fst) = B'.arr(k≫snd).
    -- Goal: S_eq.arr ≫ (fst ≫ subChar A') = ⊤, i.e. k≫fst ∈ A'.
    -- Build a point of f* B' = pullback of f and B'.arr at (a, d) = (k≫fst, k≫snd).
    have hcone : (S_eq.arr ≫ fst) ≫ f = (S_eq.arr ≫ snd) ≫ B'.arr := by
      have e1 : (S_eq.arr ≫ prodMap A B'.dom B B'.arr) ≫ fst = S_eq.arr ≫ fst := by
        rw [Cat.assoc, prodMap_fst]
      have e2 : (S_eq.arr ≫ prodMap A B'.dom B B'.arr) ≫ snd = (S_eq.arr ≫ snd) ≫ B'.arr := by
        rw [Cat.assoc, prodMap_snd, ← Cat.assoc]
      calc (S_eq.arr ≫ fst) ≫ f
          = ((S_eq.arr ≫ prodMap A B'.dom B B'.arr) ≫ fst) ≫ f := by rw [e1]
        _ = (S_eq.arr ≫ prodMap A B'.dom B B'.arr) ≫ snd := hfeq
        _ = (S_eq.arr ≫ snd) ≫ B'.arr := e2
    -- The pullback P = f* B' = InverseImage f B'; lift (k≫fst, k≫snd) into it.
    let pb := HasPullbacks.has f B'.arr
    let lift := pb.lift ⟨S_eq.dom, S_eq.arr ≫ fst, S_eq.arr ≫ snd, hcone⟩
    -- lift ≫ (f*B').arr = S_eq.arr ≫ fst.
    have hlift : lift ≫ (InverseImage f B').arr = S_eq.arr ≫ fst :=
      pb.lift_fst ⟨S_eq.dom, S_eq.arr ≫ fst, S_eq.arr ≫ snd, hcone⟩
    -- f* B' ≤ A' gives (f*B').arr ≫ χ_{A'} = ⊤; precompose with lift.
    obtain ⟨w, hw⟩ := hle
    -- hw : w ≫ A'.arr = (InverseImage f B').arr.
    -- So S_eq.arr ≫ fst = lift ≫ (InverseImage f B').arr = lift ≫ w ≫ A'.arr factors through A'.
    have hfactor : (lift ≫ w) ≫ A'.arr = S_eq.arr ≫ fst := by
      rw [Cat.assoc, hw, hlift]
    -- Conclude S_eq.arr ≫ (fst ≫ subChar A') = ⊤.
    show S_eq.arr ≫ (fst ≫ subChar A') = _
    rw [← Cat.assoc]
    apply (allows_iff_classify A' (S_eq.arr ≫ fst)).1
    exact ⟨lift ≫ w, hfactor⟩
  -- entire ≤ S_eq ⇒ S_A' via imp_adjunction.
  have hentireLe : (Subobject.entire (prod A B'.dom)).le (Sub.imp S_eq S_A') := by
    rw [imp_adjunction S_eq S_A' (Subobject.entire (prod A B'.dom)) hp]
    obtain ⟨h₁, e₁⟩ := Sub.inter_le_left S_eq (Subobject.entire (prod A B'.dom)) hp
    obtain ⟨h₂, e₂⟩ := hSle
    exact ⟨h₁ ≫ h₂, by rw [Cat.assoc, e₂, e₁]⟩
  have hcl := (le_iff_classify (Subobject.entire (prod A B'.dom))
    (Sub.imp S_eq S_A')).mp hentireLe
  show subChar (Sub.imp S_eq S_A') = term (prod A B'.dom) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)
  rw [show (Subobject.entire (prod A B'.dom)).arr ≫ subChar (Sub.imp S_eq S_A')
        = subChar (Sub.imp S_eq S_A') from Cat.id_comp _] at hcl
  rw [hcl]
  congr 1

/-- **Backward — `B'.le (f## A') → (f* B').le A'`.**

    On the carrier `P = f* B'` (the pullback of `f` and `B'.arr`, legs `π₁ = (f*B').arr : P→A`,
    `π₂ : P→B'.dom`, with `π₁≫f = π₂≫B'.arr`), the generalized point `b := π₂≫B'.arr : P→B`
    satisfies `radjChar f A'` (precompose the hypothesis `B'.arr ≫ radjChar = ⊤`).  By
    `forall_beta`, `b ≫ curry(radjBody) = topName A`; `forall_elim` at `a = π₁` makes
    `radjBody(π₁,b) = (f(π₁)=b) ⇒ (π₁∈A')` true.  Since `f(π₁) = π₂≫B'.arr = b`, the antecedent
    `eqPred` is true; modus ponens (`impΩ_forward`) gives `π₁ ∈ A'`, i.e. `(f*B').arr ≫ χ_{A'} = ⊤`. -/
public theorem radjImage_adjunction_backward {A B : 𝒞} (f : A ⟶ B)
    (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A)
    (hle : B'.le (radjImage f A')) : (InverseImage f B').le A' := by
  apply (le_iff_classify (InverseImage f B') A').2
  -- abbreviations for the pullback legs.
  let pb := HasPullbacks.has f B'.arr
  let P := (InverseImage f B').dom
  -- π₁ = (f*B').arr : P → A ; π₂ : P → B'.dom.
  have hπ₁ : (InverseImage f B').arr = pb.cone.π₁ := rfl
  -- the pullback square: π₁ ≫ f = π₂ ≫ B'.arr.
  have hsq : pb.cone.π₁ ≫ f = pb.cone.π₂ ≫ B'.arr := pb.cone.w
  -- The generalized point b := π₂ ≫ B'.arr : P → B satisfies radjChar f A'.
  let b : P ⟶ B := pb.cone.π₂ ≫ B'.arr
  have hb : b ≫ radjChar f A' = term P ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    -- B'.arr ≫ radjChar = ⊤ (from hle via le_iff_classify + classify_radjImage), precompose π₂.
    have hB' : B'.arr ≫ radjChar f A' = term B'.dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
      have := (le_iff_classify B' (radjImage f A')).1 hle
      rwa [classify_radjImage] at this
    show (pb.cone.π₂ ≫ B'.arr) ≫ radjChar f A' = _
    rw [Cat.assoc, hB', ← Cat.assoc, term_uniq (pb.cone.π₂ ≫ term B'.dom) (term P)]
  -- forall_beta: b ≫ curry(radjBody) = term P ≫ topName A.
  rw [radjChar, ← Cat.assoc] at hb
  have hentire : b ≫ curry (radjBody f A') = term P ≫ topName A :=
    (forall_beta A (b ≫ curry (radjBody f A'))).mp hb
  -- forall_elim at a = π₁ : ⟨π₁, b ≫ curry body⟩ ≫ eval = ⊤; eval_curry_point ⟹ ⟨π₁,b⟩ ≫ body = ⊤.
  have helim := forall_elim (b ≫ curry (radjBody f A')) hentire pb.cone.π₁
  rw [eval_curry_point (radjBody f A') pb.cone.π₁ b] at helim
  -- ⟨π₁,b⟩ ≫ radjBody = ⟨eqPred, π₁∈A'⟩ ≫ impΩ; split components.
  rw [radjBody, ← Cat.assoc] at helim
  have hsplit : pair pb.cone.π₁ b ≫ pair (eqPred f) (fst ≫ subChar A')
      = pair (pair pb.cone.π₁ b ≫ eqPred f) (pb.cone.π₁ ≫ subChar A') := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, fst_pair]
  rw [hsplit] at helim
  -- antecedent eqPred is true: f(π₁) = b = π₂ ≫ B'.arr.
  have heq : pair pb.cone.π₁ b ≫ eqPred f = term P ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    apply (eqPred_true_iff f (pair pb.cone.π₁ b)).2
    rw [fst_pair, snd_pair]
    exact hsq
  -- modus ponens (impΩ_forward): π₁ ∈ A' = ⊤.
  have hmp := impΩ_forward _ _ (Cat.id P)
    (by rw [Cat.id_comp]; exact helim)
    (by rw [Cat.id_comp]; exact heq)
  rw [Cat.id_comp] at hmp
  -- hmp : π₁ ≫ subChar A' = ⊤; goal is (f*B').arr ≫ subChar A' = term (f*B').dom ≫ true.
  rw [hπ₁]
  show pb.cone.π₁ ≫ HasSubobjectClassifier.classify A'.arr A'.monic = _
  exact hmp

/-- **§1.946 — the right-adjoint adjunction `f* ⊣ f##`.**  For `f : A → B`, the subobject
    `radjImage f A' = f## A'` is the right adjoint to inverse image `f* = InverseImage f`:

        (InverseImage f B').le A'  ↔  B'.le (radjImage f A').

    This is exactly the `adjunction` field of `HasRightAdjointImage` (S1_70), closing
    the §1.946 right-adjoint construction Sorry-free via the internal-∀ family-glb machinery. -/
public theorem radjImage_adjunction {A B : 𝒞} (f : A ⟶ B)
    (B' : Subobject 𝒞 B) (A' : Subobject 𝒞 A) :
    (InverseImage f B').le A' ↔ B'.le (radjImage f A') :=
  ⟨radjImage_adjunction_forward f B' A', radjImage_adjunction_backward f B' A'⟩

-- The `HasRightAdjointImage 𝒞` instance (bundling `radjImage` + `radjImage_adjunction` into the
-- §1.946/§1.70 interface) is registered in `Freyd.S1_94`.  Keeping it there avoids an import cycle
-- (S1_94 imports this file for `radjImage`/`radjImage_adjunction`).

end Freyd
