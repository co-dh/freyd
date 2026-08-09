/-
  §2.218 / §1.621 (lax) — the §1.547 base-change capitalization stage `ratCapCat P` is a
  DISJOINT BINARY COPRODUCT (positive) when the base `𝒞` is positive.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This instantiates the generic lax positivity entry point `laxColimPositive`
  (`Freyd/LaxColimitPositive.lean`) for `L := laxOfProjSystem' P` (fibres `Over (P.pr i)`,
  transitions `g* = baseChangeObj (P.proj hij)`).  The substantive math input is

    PIECE 1 — **base change preserves binary coproducts** (`baseChange_coprod_jointEpi`/
              `baseChange_coprod_copair`).  In a positive category, the pullback functor `g*`
              carries a slice coproduct `a + b` to a coproduct `g*a + g*b`.  This is Freyd's
              "positive ⟹ universal coproducts" applied to base change.  The engine is the
              §1.62 complemented-pair iso `complementedSub_legs_iso`: on the apex `(g*(a+b)).dom`
              the inverse-image pair `(π₁# inl, π₁# inr)` is complemented (cover by transporting
              `inl ∪ inr = ⊤` along `π₁#`; disjoint by transporting `inl ∩ inr ≤ ⊥`), and each
              half is identified with the base change `g*a`/`g*b` via the pullback-pasting iso
              `bcSummandIso`.

  PIECE 2/3/4 wire `hcoppres`/`hcoppres_case`/`hinitpres` and gather the bundles exactly as
  `ratCapHasImages` does, then call `laxColimPositive`.

  Mathlib-free.  Single universe (forced by `laxColimPositive`).
-/
module

public import Freyd.S1_543_RatCapImages
public import Freyd.S1_63_LaxColimitPositive
public import Freyd.S1_543_UnionFromCoproduct

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u

/-! ## PIECE 1 — base change preserves binary coproducts (generic, positive base `𝒞`)

  Throughout this section `𝒞` is a positive (`DisjointBinaryCoproduct`) category, `g : C ⟶ D`,
  and `a b : Over D`.  Write `cp := a + b` (slice coproduct, `overHasBinaryCoproducts`),
  `il := inl`, `ir := inr`.  We show the two underlying base-change injections
  `(g* il).f`, `(g* ir).f` exhibit `(g*(a+b)).dom` as the binary coproduct of `(g*a).dom`,
  `(g*b).dom`, from which the slice joint-epi and copairing follow. -/

section BaseChangeCoproduct

variable {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- The first pullback leg of the base-change map: `(g*m).f ≫ π₁ = π₁ ≫ m.f` (the `π₁`-leg of
    `baseChangeCone`).  `π₂`-leg is `(g*m).w`. -/
public theorem bcMap_fst {C D : 𝒞} (g : C ⟶ D) {X Y : Over D} (m : OverHom X Y) :
    (baseChangeMap g m).f ≫ (HasPullbacks.has Y.hom g).cone.π₁
      = (HasPullbacks.has X.hom g).cone.π₁ ≫ m.f :=
  (HasPullbacks.has Y.hom g).lift_fst (baseChangeCone g m)

/-- The composite of two two-sided inverses is a two-sided inverse: if `a ⊣⊢ a'` and `b ⊣⊢ b'`,
    then `a ≫ b ⊣⊢ b' ≫ a'`.  Fully abstract (no `let`-bound types), so `Cat.id_comp` rewrites
    cleanly when consumed with defeq-but-not-syntactic concrete arguments. -/
public theorem comp_iso_inv {X Y Z : 𝒞} {a : X ⟶ Y} {a' : Y ⟶ X} {b : Y ⟶ Z} {b' : Z ⟶ Y}
    (ha : a ≫ a' = Cat.id X) (ha' : a' ≫ a = Cat.id Y)
    (hb : b ≫ b' = Cat.id Y) (hb' : b' ≫ b = Cat.id Z) :
    (a ≫ b) ≫ (b' ≫ a') = Cat.id X ∧ (b' ≫ a') ≫ (a ≫ b) = Cat.id Z := by
  refine ⟨?_, ?_⟩
  · calc (a ≫ b) ≫ (b' ≫ a') = a ≫ ((b ≫ b') ≫ a') := by simp only [Cat.assoc]
      _ = a ≫ a' := by rw [hb, Cat.id_comp]
      _ = Cat.id X := ha
  · calc (b' ≫ a') ≫ (a ≫ b) = b' ≫ ((a' ≫ a) ≫ b) := by simp only [Cat.assoc]
      _ = b' ≫ b := by rw [ha', Cat.id_comp]
      _ = Cat.id Z := hb'

/-- **Pullback-pasting iso (the `bcSummandIso` engine).**  For a mono summand-inclusion
    `j : X ↣ K` over `D` (`j ≫ kh = xh`), the inverse image `π₁# ⟨X, j⟩` of the base-change apex
    `K ×_D C` is isomorphic to the base change `X ×_D C`, and the iso carries the subobject
    inclusion to the base-change map `m` (the underlying arrow of `g*` applied to the slice
    injection).  This is the pasting of the two pullback squares `(X ×_D C)` and `(π₁# ⟨X,j⟩)`,
    done by hand with explicit pullback lifts so the leg `θ ≫ arr = m` is on the nose. -/
public theorem bcSummandIso {C D K X : 𝒞} (g : C ⟶ D) (kh : K ⟶ D) {j : X ⟶ K} (hj : Monic j)
    (xh : X ⟶ D) (hjk : j ≫ kh = xh)
    (m : (HasPullbacks.has xh g).cone.pt ⟶ (HasPullbacks.has kh g).cone.pt)
    (hm1 : m ≫ (HasPullbacks.has kh g).cone.π₁ = (HasPullbacks.has xh g).cone.π₁ ≫ j)
    (hm2 : m ≫ (HasPullbacks.has kh g).cone.π₂ = (HasPullbacks.has xh g).cone.π₂) :
    ∃ θ : (HasPullbacks.has xh g).cone.pt ⟶ (InverseImage (HasPullbacks.has kh g).cone.π₁
              (⟨X, j, hj⟩ : Subobject 𝒞 K)).dom,
      ∃ θinv, θ ≫ θinv = Cat.id _ ∧ θinv ≫ θ = Cat.id _ ∧
        θ ≫ (InverseImage (HasPullbacks.has kh g).cone.π₁ (⟨X, j, hj⟩ : Subobject 𝒞 K)).arr = m := by
  let Pk := HasPullbacks.has kh g
  let Px := HasPullbacks.has xh g
  let Sj : Subobject 𝒞 K := ⟨X, j, hj⟩
  -- the pullback defining `InverseImage Pk.cone.π₁ Sj`: of `(Pk.cone.π₁, j)`.
  let upb := HasPullbacks.has Pk.cone.π₁ Sj.arr
  -- θ : Px.pt → upb.pt, lift of cone `(m, Px.cone.π₁)` over `(Pk.cone.π₁, j)`.
  let cθ : Cone Pk.cone.π₁ Sj.arr := ⟨Px.cone.pt, m, Px.cone.π₁, hm1⟩
  let θ : Px.cone.pt ⟶ upb.cone.pt := upb.lift cθ
  have hθ1 : θ ≫ upb.cone.π₁ = m := upb.lift_fst cθ
  have hθ2 : θ ≫ upb.cone.π₂ = Px.cone.π₁ := upb.lift_snd cθ
  -- θinv : upb.pt → Px.pt, lift of cone `(upb.cone.π₂, upb.cone.π₁ ≫ Pk.cone.π₂)` over `(xh, g)`.
  have hcinv : upb.cone.π₂ ≫ xh = (upb.cone.π₁ ≫ Pk.cone.π₂) ≫ g := by
    calc upb.cone.π₂ ≫ xh
        = upb.cone.π₂ ≫ (j ≫ kh) := by rw [hjk]
      _ = (upb.cone.π₂ ≫ j) ≫ kh := (Cat.assoc _ _ _).symm
      _ = (upb.cone.π₁ ≫ Pk.cone.π₁) ≫ kh := by rw [← upb.cone.w]
      _ = upb.cone.π₁ ≫ (Pk.cone.π₁ ≫ kh) := Cat.assoc _ _ _
      _ = upb.cone.π₁ ≫ (Pk.cone.π₂ ≫ g) := by rw [Pk.cone.w]
      _ = (upb.cone.π₁ ≫ Pk.cone.π₂) ≫ g := (Cat.assoc _ _ _).symm
  let cinv : Cone xh g := ⟨upb.cone.pt, upb.cone.π₂, upb.cone.π₁ ≫ Pk.cone.π₂, hcinv⟩
  let θinv : upb.cone.pt ⟶ Px.cone.pt := Px.lift cinv
  have hθinv1 : θinv ≫ Px.cone.π₁ = upb.cone.π₂ := Px.lift_fst cinv
  have hθinv2 : θinv ≫ Px.cone.π₂ = upb.cone.π₁ ≫ Pk.cone.π₂ := Px.lift_snd cinv
  -- θ ≫ θinv = id, via Px.lift_uniq on Px's own cone.
  have hθθinv : θ ≫ θinv = Cat.id _ := by
    have e1 : (θ ≫ θinv) ≫ Px.cone.π₁ = Px.cone.π₁ := by
      rw [Cat.assoc, hθinv1, hθ2]
    have e2 : (θ ≫ θinv) ≫ Px.cone.π₂ = Px.cone.π₂ := by
      rw [Cat.assoc, hθinv2, ← Cat.assoc, hθ1, hm2]
    rw [Px.lift_uniq Px.cone (θ ≫ θinv) e1 e2,
        Px.lift_uniq Px.cone (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)]
  -- θinv ≫ m = upb.cone.π₁, via Pk.lift_uniq (jointly monic legs).
  have hθinv_m : θinv ≫ m = upb.cone.π₁ := by
    let cone : Cone kh g := ⟨upb.cone.pt, upb.cone.π₁ ≫ Pk.cone.π₁, upb.cone.π₁ ≫ Pk.cone.π₂,
      by rw [Cat.assoc, Pk.cone.w, ← Cat.assoc]⟩
    have e1 : (θinv ≫ m) ≫ Pk.cone.π₁ = upb.cone.π₁ ≫ Pk.cone.π₁ := by
      rw [Cat.assoc, hm1, ← Cat.assoc, hθinv1, upb.cone.w]
    have e2 : (θinv ≫ m) ≫ Pk.cone.π₂ = upb.cone.π₁ ≫ Pk.cone.π₂ := by
      rw [Cat.assoc, hm2, hθinv2]
    rw [Pk.lift_uniq cone (θinv ≫ m) e1 e2, Pk.lift_uniq cone upb.cone.π₁ rfl rfl]
  -- θinv ≫ θ = id, via monicity of `upb.cone.π₁` (= the InverseImage arr).
  have hθinvθ : θinv ≫ θ = Cat.id _ := by
    apply (InverseImage Pk.cone.π₁ Sj).monic
    show (θinv ≫ θ) ≫ upb.cone.π₁ = Cat.id _ ≫ upb.cone.π₁
    rw [Cat.assoc, hθ1, hθinv_m, Cat.id_comp]
  exact ⟨θ, θinv, hθθinv, hθinvθ, hθ1⟩

variable {C D : 𝒞} (g : C ⟶ D) (a b : Over D)

/-- **Base change preserves the binary coproduct: the iso.**  There is an iso
    `Φ : (g*a).dom + (g*b).dom ≅ (g*(a+b)).dom` whose legs are the base-change injections
    `(g* inl).f`, `(g* inr).f`.  The two summands are identified via `bcSummandIso`; the apex
    decomposition is the §1.62 complemented-pair iso `complementedSub_legs_iso`. -/
public theorem baseChange_coprod_iso :
    ∃ (Φ : HasBinaryCoproducts.coprod (baseChangeObj g a).dom (baseChangeObj g b).dom
            ⟶ (baseChangeObj g (HasBinaryCoproducts.coprod a b)).dom)
      (Φinv : (baseChangeObj g (HasBinaryCoproducts.coprod a b)).dom
            ⟶ HasBinaryCoproducts.coprod (baseChangeObj g a).dom (baseChangeObj g b).dom),
      Φ ≫ Φinv = Cat.id _ ∧ Φinv ≫ Φ = Cat.id _ ∧
      HasBinaryCoproducts.inl ≫ Φ = (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ∧
      HasBinaryCoproducts.inr ≫ Φ = (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f := by
  -- abbreviations.
  let cp : Over D := HasBinaryCoproducts.coprod a b
  let il : a ⟶ cp := HasBinaryCoproducts.inl (𝒞 := Over D) (A := a) (B := b)
  let ir : b ⟶ cp := HasBinaryCoproducts.inr (𝒞 := Over D) (A := a) (B := b)
  let il' := (baseChangeMap g il).f
  let ir' := (baseChangeMap g ir).f
  let pbcp := HasPullbacks.has cp.hom g
  let π₁ := pbcp.cone.π₁
  -- the two inverse-image halves of the apex `cp ×_D C`.
  let Ul := InverseImage π₁ (inlSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inl_mono)
  let Ur := InverseImage π₁ (inrSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inr_mono)
  -- leg equations for the base-change injections.
  have hil1 : il' ≫ π₁ = (HasPullbacks.has a.hom g).cone.π₁ ≫ HasBinaryCoproducts.inl :=
    bcMap_fst g il
  have hir1 : ir' ≫ π₁ = (HasPullbacks.has b.hom g).cone.π₁ ≫ HasBinaryCoproducts.inr :=
    bcMap_fst g ir
  have hil2 : il' ≫ pbcp.cone.π₂ = (baseChangeObj g a).hom := (baseChangeMap g il).w
  have hir2 : ir' ≫ pbcp.cone.π₂ = (baseChangeObj g b).hom := (baseChangeMap g ir).w
  -- summand isos via bcSummandIso.
  obtain ⟨θl, θlinv, hθlθinv, hθinvθl, hθl⟩ :=
    bcSummandIso g cp.hom (inl_mono (A := a.dom) (B := b.dom)) a.hom
      (HasBinaryCoproducts.case_inl a.hom b.hom) il' hil1 hil2
  obtain ⟨θr, θrinv, hθrθinv, hθinvθr, hθr⟩ :=
    bcSummandIso g cp.hom (inr_mono (A := a.dom) (B := b.dom)) b.hom
      (HasBinaryCoproducts.case_inr a.hom b.hom) ir' hir1 hir2
  -- complemented-pair iso on the apex.
  -- cover: entire ≤ π₁#(entire) ≤ π₁#(inl ∪ inr) ≤ π₁#inl ∪ π₁#inr.
  have hcover : (Subobject.entire pbcp.cone.pt).le (HasSubobjectUnions.union Ul Ur) := by
    refine Subobject.le_trans (entire_le_inverseImage_entire π₁) ?_
    refine Subobject.le_trans (inverseImage_mono π₁ inl_union_inr_entire) ?_
    exact (PreLogos.invImage_preserves_union π₁ _ _).1
  -- disjoint: a point of `Ul ∩ Ur` collides `inl`/`inr`, hence is initial (`≤ ⊥`).
  have hdisj : (Subobject.inter Ul Ur).le (PreLogos.bottom pbcp.cone.pt) := by
    let pb := HasPullbacks.has Ul.arr Ur.arr
    let ulπ₂ := (HasPullbacks.has π₁ (inlSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inl_mono).arr).cone.π₂
    let urπ₂ := (HasPullbacks.has π₁ (inrSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inr_mono).arr).cone.π₂
    have hUlw : Ul.arr ≫ π₁ = ulπ₂ ≫ HasBinaryCoproducts.inl :=
      (HasPullbacks.has π₁ (inlSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inl_mono).arr).cone.w
    have hUrw : Ur.arr ≫ π₁ = urπ₂ ≫ HasBinaryCoproducts.inr :=
      (HasPullbacks.has π₁ (inrSub (𝒞 := 𝒞) (A := a.dom) (B := b.dom) inr_mono).arr).cone.w
    have hcollide : (pb.cone.π₁ ≫ ulπ₂) ≫ HasBinaryCoproducts.inl
                  = (pb.cone.π₂ ≫ urπ₂) ≫ HasBinaryCoproducts.inr := by
      have hw := pb.cone.w   -- pb.cone.π₁ ≫ Ul.arr = pb.cone.π₂ ≫ Ur.arr
      calc (pb.cone.π₁ ≫ ulπ₂) ≫ HasBinaryCoproducts.inl
          = pb.cone.π₁ ≫ (ulπ₂ ≫ HasBinaryCoproducts.inl) := Cat.assoc _ _ _
        _ = pb.cone.π₁ ≫ (Ul.arr ≫ π₁) := by rw [hUlw]
        _ = (pb.cone.π₁ ≫ Ul.arr) ≫ π₁ := (Cat.assoc _ _ _).symm
        _ = (pb.cone.π₂ ≫ Ur.arr) ≫ π₁ := by rw [hw]
        _ = pb.cone.π₂ ≫ (Ur.arr ≫ π₁) := Cat.assoc _ _ _
        _ = pb.cone.π₂ ≫ (urπ₂ ≫ HasBinaryCoproducts.inr) := by rw [hUrw]
        _ = (pb.cone.π₂ ≫ urπ₂) ≫ HasBinaryCoproducts.inr := (Cat.assoc _ _ _).symm
    obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞)
      (pb.cone.π₁ ≫ ulπ₂) (pb.cone.π₂ ≫ urπ₂) hcollide
    exact le_bottom_of_map_to_bottom (Subobject.inter Ul Ur) e
  obtain ⟨ψ, ψinv, hψψinv, hψinvψ, hψinl, hψinr⟩ :=
    complementedSub_legs_iso Ul Ur hdisj hcover
  -- comparison map `cm : (g*a + g*b) → (Ul.dom + Ur.dom)` from the summand isos, and its inverse.
  let cm := HasBinaryCoproducts.case (θl ≫ HasBinaryCoproducts.inl) (θr ≫ HasBinaryCoproducts.inr)
  let cminv := HasBinaryCoproducts.case (θlinv ≫ HasBinaryCoproducts.inl)
                                        (θrinv ≫ HasBinaryCoproducts.inr)
  have hcm_l : HasBinaryCoproducts.inl ≫ cm = θl ≫ HasBinaryCoproducts.inl :=
    HasBinaryCoproducts.case_inl _ _
  have hcm_r : HasBinaryCoproducts.inr ≫ cm = θr ≫ HasBinaryCoproducts.inr :=
    HasBinaryCoproducts.case_inr _ _
  have hcminv_l : HasBinaryCoproducts.inl ≫ cminv = θlinv ≫ HasBinaryCoproducts.inl :=
    HasBinaryCoproducts.case_inl _ _
  have hcminv_r : HasBinaryCoproducts.inr ≫ cminv = θrinv ≫ HasBinaryCoproducts.inr :=
    HasBinaryCoproducts.case_inr _ _
  have hcm_id : cm ≫ cminv = Cat.id _ := by
    refine (HasBinaryCoproducts.case_uniq _ _ (cm ≫ cminv) ?_ ?_).trans
      (HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
    · rw [← Cat.assoc, hcm_l, Cat.assoc, hcminv_l, ← Cat.assoc, hθlθinv, Cat.id_comp]
    · rw [← Cat.assoc, hcm_r, Cat.assoc, hcminv_r, ← Cat.assoc, hθrθinv, Cat.id_comp]
  have hcminv_id : cminv ≫ cm = Cat.id _ := by
    refine (HasBinaryCoproducts.case_uniq _ _ (cminv ≫ cm) ?_ ?_).trans
      (HasBinaryCoproducts.case_uniq _ _ (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
    · rw [← Cat.assoc, hcminv_l, Cat.assoc, hcm_l, ← Cat.assoc, hθinvθl, Cat.id_comp]
    · rw [← Cat.assoc, hcminv_r, Cat.assoc, hcm_r, ← Cat.assoc, hθinvθr, Cat.id_comp]
  -- Φ := cm ≫ ψ, Φinv := ψinv ≫ cminv; the two iso identities via the abstract `comp_iso_inv`.
  obtain ⟨hΦΦinv, hΦinvΦ⟩ := comp_iso_inv hcm_id hcminv_id hψψinv hψinvψ
  refine ⟨cm ≫ ψ, ψinv ≫ cminv, hΦΦinv, hΦinvΦ, ?_, ?_⟩
  · -- inl ≫ Φ = il'
    calc HasBinaryCoproducts.inl ≫ (cm ≫ ψ)
        = (HasBinaryCoproducts.inl ≫ cm) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = (θl ≫ HasBinaryCoproducts.inl) ≫ ψ := by rw [hcm_l]
      _ = θl ≫ (HasBinaryCoproducts.inl ≫ ψ) := Cat.assoc _ _ _
      _ = θl ≫ Ul.arr := by rw [hψinl]
      _ = il' := hθl
  · -- inr ≫ Φ = ir'
    calc HasBinaryCoproducts.inr ≫ (cm ≫ ψ)
        = (HasBinaryCoproducts.inr ≫ cm) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = (θr ≫ HasBinaryCoproducts.inr) ≫ ψ := by rw [hcm_r]
      _ = θr ≫ (HasBinaryCoproducts.inr ≫ ψ) := Cat.assoc _ _ _
      _ = θr ≫ Ur.arr := by rw [hψinr]
      _ = ir' := hθr

/-- **Base change preserves binary coproducts — JOINT-EPI (slice).**  Two slice maps out of
    `g*(a+b)` agreeing after `g* inl` and after `g* inr` are equal. -/
public theorem baseChange_coprod_jointEpi (z : Over C)
    (u v : OverHom (baseChangeObj g (HasBinaryCoproducts.coprod a b)) z)
    (hl : baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b)) ⊚ u
        = baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b)) ⊚ v)
    (hr : baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b)) ⊚ u
        = baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b)) ⊚ v) :
    u = v := by
  obtain ⟨Φ, Φinv, _, hΦinvΦ, hΦl, hΦr⟩ := baseChange_coprod_iso g a b
  apply OverHom.ext
  -- underlying: il' ≫ u.f = il' ≫ v.f and ir' ≫ u.f = ir' ≫ v.f.
  have hlf : (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ u.f
           = (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ v.f :=
    congrArg OverHom.f hl
  have hrf : (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ u.f
           = (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ v.f :=
    congrArg OverHom.f hr
  -- Φ ≫ u.f and Φ ≫ v.f both copair the same legs.
  have hu : Φ ≫ u.f = HasBinaryCoproducts.case
      ((baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ u.f)
      ((baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ u.f) :=
    HasBinaryCoproducts.case_uniq _ _ _ (by rw [← Cat.assoc, hΦl]) (by rw [← Cat.assoc, hΦr])
  have hv : Φ ≫ v.f = HasBinaryCoproducts.case
      ((baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ v.f)
      ((baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ v.f) :=
    HasBinaryCoproducts.case_uniq _ _ _ (by rw [← Cat.assoc, hΦl]) (by rw [← Cat.assoc, hΦr])
  have hΦuv : Φ ≫ u.f = Φ ≫ v.f := by rw [hu, hv, hlf, hrf]
  -- cancel Φ on the left (Φ is split epi: section Φinv, `Φinv ≫ Φ = id`).
  calc u.f = (Φinv ≫ Φ) ≫ u.f := by rw [hΦinvΦ, Cat.id_comp]
    _ = Φinv ≫ (Φ ≫ u.f) := Cat.assoc _ _ _
    _ = Φinv ≫ (Φ ≫ v.f) := by rw [hΦuv]
    _ = (Φinv ≫ Φ) ≫ v.f := (Cat.assoc _ _ _).symm
    _ = v.f := by rw [hΦinvΦ, Cat.id_comp]

/-- **Base change preserves binary coproducts — COPAIRING (slice).**  Given slice maps
    `p : g*a ⟶ z`, `q : g*b ⟶ z`, there is a copairing `r : g*(a+b) ⟶ z` restricting to `p`/`q`. -/
public theorem baseChange_coprod_copair (z : Over C)
    (p : OverHom (baseChangeObj g a) z) (q : OverHom (baseChangeObj g b) z) :
    ∃ r : OverHom (baseChangeObj g (HasBinaryCoproducts.coprod a b)) z,
      baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b)) ⊚ r = p ∧
      baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b)) ⊚ r = q := by
  obtain ⟨Φ, Φinv, hΦΦinv, hΦinvΦ, hΦl, hΦr⟩ := baseChange_coprod_iso g a b
  -- il' ≫ Φinv = inl, ir' ≫ Φinv = inr (Φ ≫ Φinv = id).
  have hΦinv_l : (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ Φinv
      = HasBinaryCoproducts.inl := by
    rw [← hΦl, Cat.assoc, hΦΦinv, Cat.comp_id]
  have hΦinv_r : (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ Φinv
      = HasBinaryCoproducts.inr := by
    rw [← hΦr, Cat.assoc, hΦΦinv, Cat.comp_id]
  -- candidate underlying arrow and its copairing legs.
  let rf := Φinv ≫ HasBinaryCoproducts.case p.f q.f
  have hrl : (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f ≫ rf = p.f := by
    show (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).f
        ≫ (Φinv ≫ HasBinaryCoproducts.case p.f q.f) = p.f
    rw [← Cat.assoc, hΦinv_l, HasBinaryCoproducts.case_inl]
  have hrr : (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f ≫ rf = q.f := by
    show (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).f
        ≫ (Φinv ≫ HasBinaryCoproducts.case p.f q.f) = q.f
    rw [← Cat.assoc, hΦinv_r, HasBinaryCoproducts.case_inr]
  -- structure-map check: rf ≫ z.hom = π₂, checked after Φ (split epi) then cancelled.
  have hrw : rf ≫ z.hom = (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom := by
    have hcase1 : Φ ≫ (rf ≫ z.hom)
        = HasBinaryCoproducts.case (baseChangeObj g a).hom (baseChangeObj g b).hom :=
      HasBinaryCoproducts.case_uniq _ _ _
        (by rw [← Cat.assoc, hΦl, ← Cat.assoc, hrl]; exact p.w)
        (by rw [← Cat.assoc, hΦr, ← Cat.assoc, hrr]; exact q.w)
    have hcase2 : Φ ≫ (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom
        = HasBinaryCoproducts.case (baseChangeObj g a).hom (baseChangeObj g b).hom :=
      HasBinaryCoproducts.case_uniq _ _ _
        (by rw [← Cat.assoc, hΦl]; exact (baseChangeMap g (HasBinaryCoproducts.inl (A := a) (B := b))).w)
        (by rw [← Cat.assoc, hΦr]; exact (baseChangeMap g (HasBinaryCoproducts.inr (A := a) (B := b))).w)
    have key : Φ ≫ (rf ≫ z.hom) = Φ ≫ (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom := by
      rw [hcase1, hcase2]
    calc rf ≫ z.hom = (Φinv ≫ Φ) ≫ (rf ≫ z.hom) := by rw [hΦinvΦ, Cat.id_comp]
      _ = Φinv ≫ (Φ ≫ (rf ≫ z.hom)) := Cat.assoc _ _ _
      _ = Φinv ≫ (Φ ≫ (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom) := by rw [key]
      _ = (Φinv ≫ Φ) ≫ (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom := (Cat.assoc _ _ _).symm
      _ = (baseChangeObj g (HasBinaryCoproducts.coprod a b)).hom := by rw [hΦinvΦ, Cat.id_comp]
  exact ⟨⟨rf, hrw⟩, OverHom.ext hrl, OverHom.ext hrr⟩

end BaseChangeCoproduct

/-! ## PIECE 3 — base change preserves strict coterminators (strict initials)

  `hinitpres` needs `StrictCoterminator (g* Z)` for `Z` the slice strict-initial `0`.  Pullback of a
  strict initial along any map is strict initial: the underlying `Z.dom` is strict initial in `𝒞`
  (any base map into it is iso), so the pullback projection `π₁ : (g*Z).dom → Z.dom` is iso, the
  apex is strict initial, and a slice map into `g*Z` is iso (its underlying arrow is).  Needs only
  `HasPullbacks`. -/

section BaseChangeInitial

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasPullbacks 𝒞]

/-- **Base change preserves strict coterminators.**  `g*` of a strict initial of `Over D` is a strict
    initial of `Over C`. -/
public theorem baseChange_strictCoterminator {C D : 𝒞} (g : C ⟶ D) {Z : Over D}
    (hZ : StrictCoterminator Z) : StrictCoterminator (baseChangeObj g Z) := by
  have hZdom : StrictCoterminator Z.dom :=
    fun {Y} h => overIso_underlying (hZ (X := ⟨Y, h ≫ Z.hom⟩) ⟨h, rfl⟩)
  have hπ₁ : IsIso (HasPullbacks.has Z.hom g).cone.π₁ := hZdom (HasPullbacks.has Z.hom g).cone.π₁
  -- the pullback apex is strict initial in `𝒞`.
  have hpt : StrictCoterminator (HasPullbacks.has Z.hom g).cone.pt := by
    intro Y h
    obtain ⟨π₁inv, hπa, hπb⟩ := hπ₁
    have hsplit : h = (h ≫ (HasPullbacks.has Z.hom g).cone.π₁) ≫ π₁inv := by
      rw [Cat.assoc, hπa, Cat.comp_id]
    rw [hsplit]
    exact isIso_comp (hZdom (h ≫ (HasPullbacks.has Z.hom g).cone.π₁))
      ⟨(HasPullbacks.has Z.hom g).cone.π₁, hπb, hπa⟩
  -- lift to the slice: a slice map into `g*Z` has iso underlying arrow.
  intro X f
  exact overIso_of_underlying f (hpt f.f)

end BaseChangeInitial

/-! ## PIECE 2 + 4 — assembly: `ratCapCat P` is a disjoint binary coproduct

  Instantiate `laxColimPositive` for `L := laxOfProjSystem' P`.  The per-fibre data are the slice
  instances (`overDisjointBinaryCoproduct`/`overPreLogos`/`overHasImages`); the transition bundles
  are `ratLax*Data` (RatCapPreReg) + the PIECE 1/2 coproduct preservation + PIECE 3 `hinitpres`; the
  `RegularCategory`/`HasSubobjectUnions` come from `ratCapPreRegular_of_projCover` + `ratCapHasImages`
  exactly as `ratCapHasImages` sources them. -/

section Assembly
open PreRegularCategory

variable {ι : Type u} {D : Directed ι} {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

-- Keep the lax positivity data on the shared finite-limit representatives.
/-- **§2.218 / §1.621: `ratCapCat P` is a disjoint binary coproduct (positive) when the base `𝒞` is.**
    Single entry point: instantiates `laxColimPositive` with the slice fibre data and the base-change
    transition-preservation bundles (PIECE 1–3). -/
@[expose] public noncomputable def ratCapDisjointBinaryCoproduct [Nonempty ι] (P : ProjSystem ι D 𝒞)
    (hpc : ∀ {i j : ι} (h : D.le i j), Cover (P.proj h)) :
    @DisjointBinaryCoproduct (Obj (laxOfProjSystem' P)) (ratCapCat P) := by
  letI iCat : Cat (Obj (laxOfProjSystem' P)) := ratCat P
  -- transition mono/cover preservation (shared with `himgpres`), sourced as in `ratCapHasImages`.
  have hmono : ∀ {i j : ι} (hij : D.le i j),
      @PreservesMono _ ((laxOfProjSystem' P).catA i) _ ((laxOfProjSystem' P).catA j)
        ((laxOfProjSystem' P).functF hij) :=
    fun {i j} hij {X Y} {f} hf => projStage_preservesMono P hij f hf
  have hcovpres : ∀ {i j : ι} (hij : D.le i j),
      @PreservesCovers _ _ ((laxOfProjSystem' P).catA i) ((laxOfProjSystem' P).catA j)
        ((laxOfProjSystem' P).functF hij) :=
    fun {i j} hij {A B} f hf => projStage_preservesCover P hij f hf
  -- RegularCategory (ratCapCat P) = pre-regular (cover-projections) + images.
  letI preReg : @PreRegularCategory (Obj (laxOfProjSystem' P)) (ratCat P) :=
    ratCapPreRegular_of_projCover P (fun h => hpc h)
  letI imgs : @HasImages (Obj (laxOfProjSystem' P)) (ratCat P) := ratCapHasImages P (fun h => hpc h)
  letI hReg : @RegularCategory (Obj (laxOfProjSystem' P)) (ratCat P) :=
    { preReg with toHasImages := imgs }
  -- the lax binary coproducts, for the subobject-union instance `hUn`.
  letI hbc : @HasBinaryCoproducts (Obj (laxOfProjSystem' P)) (ratCat P) :=
    laxColimCoprodOfDisjoint (laxOfProjSystem' P) (coherentProj P)
      (fun i => overDisjointBinaryCoproduct (P.pr i))
      (fun {i j} hij a b z u v hl hr => baseChange_coprod_jointEpi (P.proj hij) a b z u v hl hr)
      (fun {i j} hij a b z p q => baseChange_coprod_copair (P.proj hij) a b z p q)
  letI hUn : @HasSubobjectUnions (Obj (laxOfProjSystem' P)) (ratCat P) hReg.toHasImages :=
    @hasSubobjectUnions_of_coproducts_images (Obj (laxOfProjSystem' P)) (ratCat P) hReg.toHasImages hbc
  -- instantiate `laxColimPositive`.
  exact laxColimPositive (laxOfProjSystem' P) (coherentProj P)
    (fun i => overDisjointBinaryCoproduct (P.pr i)) hmono (fun i => overPreLogos (P.pr i))
    (fun {i j} hij => baseChange_strictCoterminator (P.proj hij)
      (fun {X} f => any_map_to_zero_is_iso (overPreLogos (P.pr i)) f))
    (ratLaxTerminalData P) (ratLaxProductData P) (ratLaxEqualizerData P)
    (fun {i j} hij a b z u v hl hr => baseChange_coprod_jointEpi (P.proj hij) a b z u v hl hr)
    (fun {i j} hij a b z p q => baseChange_coprod_copair (P.proj hij) a b z p q)
    (fun i => overHasImages (P.pr i))
    (fun {i j} hij {x y} p q heq => projStage_faithful P hij (hpc hij) p q heq)
    (fun {i j} hij {X Y} f =>
      letI : HasImages ((laxOfProjSystem' P).A i) := overHasImages (P.pr i)
      letI : HasPullbacks ((laxOfProjSystem' P).A j) := overHasPullbacks (P.pr j)
      transitions_preserve_images ((laxOfProjSystem' P).functF hij)
        (hmono hij) (hcovpres hij) f)

end Assembly

end Freyd.LaxColim
