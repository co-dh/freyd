/-
  `thinLOn` read back: `foldBy` at a `demandStep` whose body bumps each element `a` into the thinned rest `y` —
  `[a]` when `y` is empty, else with `b` its head `a` replaces `b` when `(a, b)` passes the test, `y` stays when
  `(b, a)` passes, and `a :: y` when neither does. The test is `q` at the pairs the round meets, read as `le`.
-/
import LeetQ.Rel.RepMerge

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN Prim

-- the state of `thinLOn`'s step: an element and the thinned rest
set_option hygiene false in
local notation "SP" => Obj.prod B (.arr B)

section Body

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **`thinLOn`'s body on a coreflexive `D`, read back from its primitives' read-backs**: `(a, y)` in `D` goes to
    `[a]` when `y` is empty; with `y = b :: bs`, to `a :: bs` when `le a b`, to `y` when `le b a`, and to `a :: y`
    when neither. Each hypothesis is one primitive's read-back at the body's values (`rep_uncons`, `rep_comp`,
    `rep_pair`, `rep_ran`, `rep_dom`, `rep_diff`, `rep_union_full`, `rep_cons`); `ht1`, `ht2` read the test on the
    pairs of heads `rab` the body meets, and on their swaps `rs`. -/
theorem thin_body_set {B : Obj} (le : B.El → B.El → Bool) (D : Rel SP SP) (Dm : (SP).El → Prop)
    (hD : rep D = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) Dm)
    (ta : Rel SP B) (hta : ta = outl D) (ty : Rel SP (.arr B)) (hty : ty = outr D)
    (tu : Rel SP (.prod B (.arr B)))
    (hUn : ∀ (xs : List B.El) b bs, rep (uncons (Rel.val ty)) xs (b, bs) ↔
      (∃ j, (Rel.val ty).row j = xs) ∧ xs = b :: bs)
    (htu : rep tu = rep ty ≫ rep (uncons (Rel.val ty)))
    (tab : Rel SP (.prod B B)) (htab : rep tab = rpair (rep ta) (rep (outl tu)))
    (rab : Rel (.prod B B) (.prod B B))
    (hrab : rep rab = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun c => ∃ s, rep tab s c)
    (G1 : Rel (.prod B B) (.prod B B)) (ht1 : ∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true))
    (tq1 : Rel SP (.prod B B)) (htq1 : rep tq1 = rep tab ≫ rep G1)
    (tup : Rel SP SP) (htup : rep tup = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tq1 s c)
    (ss : Rel (.prod B B) (.prod B B)) (hss : rep ss = rpair (rep (outr rab)) (rep (outl rab)))
    (rs : Rel (.prod B B) (.prod B B))
    (hrs : rep rs = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun c => ∃ x, rep ss x c)
    (G2 : Rel (.prod B B) (.prod B B)) (ht2 : ∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true))
    (tq2 : Rel (.prod B B) (.prod B B)) (htq2 : rep tq2 = rep ss ≫ rep G2)
    (sw : Rel (.prod B B) (.prod B B))
    (hsw : rep sw = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun x => ∃ c, rep tq2 x c)
    (tq3 : Rel SP (.prod B B)) (htq3 : rep tq3 = rep tab ≫ rep sw)
    (tdn : Rel SP SP) (htdn : rep tdn = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tq3 s c)
    (du : Rel SP SP) (hdu : rep du = corefl (A := (⟨(SP).El⟩ : RelSet.{0})) fun s => ∃ c, rep tu s c)
    (l1 : Rel SP SP) (hl1 : ∀ s s', rep l1 s s' ↔ rep D s s' ∧ ¬ rep du s s')
    (l2 : Rel SP SP) (hl2 : ∀ s s', rep l2 s s' ↔ rep du s s' ∧ ¬ rep tup s s')
    (l3 : Rel SP SP) (hl3 : ∀ s s', rep l3 s s' ↔ rep l2 s s' ∧ ¬ rep tdn s s')
    (lone : Rel SP SP) (hlone : rep lone = rep l1 ∪ rep l3)
    (c1 : Rel SP (.arr B)) (hc1 : ∀ s z, rep c1 s z ↔ ∃ b bs, rep lone s (b, bs) ∧ z = b :: bs)
    (ua : Rel SP B) (hua : rep ua = rep tup ≫ rep ta)
    (uu : Rel SP (.prod B (.arr B))) (huu : rep uu = rep tup ≫ rep tu)
    (ru : Rel (.prod B (.arr B)) (.prod B (.arr B)))
    (hru : rep ru = corefl (A := (⟨(Obj.prod B (.arr B)).El⟩ : RelSet.{0})) fun c => ∃ s, rep tu s c)
    (ut : Rel SP (.arr B)) (hut : rep ut = rep uu ≫ rep (outr ru))
    (pu : Rel SP (.prod B (.arr B))) (hpu : rep pu = rpair (rep ua) (rep ut))
    (c2 : Rel SP (.arr B)) (hc2 : ∀ s z, rep c2 s z ↔ ∃ b bs, rep pu s (b, bs) ∧ z = b :: bs)
    (dy : Rel SP (.arr B)) (hdy : rep dy = rep tdn ≫ rep ty)
    (b1 : Rel SP (.arr B)) (hb1 : rep b1 = rep c1 ∪ rep c2)
    (body : Rel SP (.arr B)) (hbody : rep body = rep b1 ∪ rep dy) :
    ∀ a (y v : List B.El), rep body (a, y) v ↔ Dm (a, y) ∧ ((y = [] ∧ v = [a]) ∨ ∃ b bs, y = b :: bs ∧
      ((le a b = true ∧ v = a :: bs) ∨ (le b a = true ∧ v = y) ∨ (le a b = false ∧ le b a = false ∧ v = a :: y))) := by
  have eD : ∀ s s', rep D s s' ↔ s = s' ∧ Dm s := fun s s' => by rw [hD]; exact Iff.rfl
  -- the element and the rest of a state, read off `D`
  have eA : ∀ a y x, rep ta (a, y) x ↔ Dm (a, y) ∧ x = a := by
    intro a y x; rw [hta]
    refine (outl_holds D (a, y) x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eD _ _).1 h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨y, (eD _ _).2 ⟨rfl, hm⟩⟩
  have eY : ∀ a y x, rep ty (a, y) x ↔ Dm (a, y) ∧ x = y := by
    intro a y x; rw [hty]
    refine (outr_holds D (a, y) x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eD _ _).1 h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨a, (eD _ _).2 ⟨rfl, hm⟩⟩
  -- `uncons` of the rest
  have eU : ∀ a y b bs, rep tu (a, y) (b, bs) ↔ Dm (a, y) ∧ y = b :: bs := by
    intro a y b bs; rw [htu, comp_apply]
    constructor
    · rintro ⟨v, h1, h2⟩; obtain ⟨hm, rfl⟩ := (eY _ _ _).1 h1; exact ⟨hm, ((hUn _ b bs).1 h2).2⟩
    · rintro ⟨hm, e⟩
      have h1 : rep ty (a, y) y := (eY _ _ _).2 ⟨hm, rfl⟩
      obtain ⟨i, -, hi⟩ := id h1
      exact ⟨y, h1, (hUn _ b bs).2 ⟨⟨i, hi⟩, e⟩⟩
  -- the pair of heads `(a, b)`
  have eAB : ∀ a y a' b, rep tab (a, y) (a', b) ↔ Dm (a, y) ∧ a' = a ∧ ∃ bs, y = b :: bs := by
    intro a y a' b; rw [htab]
    show rep ta (a, y) a' ∧ rep (outl tu) (a, y) b ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, rfl⟩ := (eA _ _ _).1 h1
      obtain ⟨bs, h3⟩ := (outl_holds tu _ b).1 h2
      exact ⟨hm, rfl, bs, ((eU _ _ _ _).1 h3).2⟩
    · rintro ⟨hm, rfl, bs, e⟩
      exact ⟨(eA _ _ _).2 ⟨hm, rfl⟩, (outl_holds tu _ b).2 ⟨bs, (eU _ _ _ _).2 ⟨hm, e⟩⟩⟩
  have eRab : ∀ c c', rep rab c c' ↔ c = c' ∧ ∃ s, rep tab s c := fun c c' => by rw [hrab]; exact Iff.rfl
  -- `up`: the rest is `b :: bs` and `le a b`
  have eUp : ∀ a y s', rep tup (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true := by
    intro a y s'; rw [htup]
    show (a, y) = s' ∧ (∃ c, rep tq1 (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq1, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _ _).1 h1
      exact ⟨hm, b, bs, e, (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).1 ⟨c, h2⟩⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab (a, y) (a, b) := (eAB _ _ _ _).2 ⟨hm, rfl, bs, e⟩
      obtain ⟨c, h2⟩ := (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨c, by rw [htq1, comp_apply]; exact ⟨_, h1, h2⟩⟩
  -- the swap `(b, a)` of a pair of heads, and `down`: the swap passes
  have eOR : ∀ c x, rep (outr rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.2 := by
    intro c x
    refine (outr_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.1, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eOL : ∀ c x, rep (outl rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.1 := by
    intro c x
    refine (outl_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.2, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eSS : ∀ a' b d, rep ss (a', b) d ↔ (∃ s, rep tab s (a', b)) ∧ d = (b, a') := by
    intro a' b d; rw [hss]
    show rep (outr rab) (a', b) d.1 ∧ rep (outl rab) (a', b) d.2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, e1⟩ := (eOR _ _).1 h1
      obtain ⟨-, e2⟩ := (eOL _ _).1 h2
      exact ⟨hm, Prod.ext e1 e2⟩
    · rintro ⟨hm, rfl⟩; exact ⟨(eOR _ _).2 ⟨hm, rfl⟩, (eOL _ _).2 ⟨hm, rfl⟩⟩
  have eRs : ∀ c c', rep rs c c' ↔ c = c' ∧ ∃ x, rep ss x c := fun c c' => by rw [hrs]; exact Iff.rfl
  have eSw : ∀ a' b c', rep sw (a', b) c' ↔ (a', b) = c' ∧ (∃ s, rep tab s (a', b)) ∧ le b a' = true := by
    intro a' b c'; rw [hsw]
    show (a', b) = c' ∧ (∃ d, rep tq2 (a', b) d) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨d, hd⟩
      rw [htq2, comp_apply] at hd
      obtain ⟨x, h1, h2⟩ := hd
      obtain ⟨hm, rfl⟩ := (eSS _ _ _).1 h1
      exact ⟨hm, (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).1 ⟨d, h2⟩⟩
    · rintro ⟨hm, hl⟩
      have h1 : rep ss (a', b) (b, a') := (eSS _ _ _).2 ⟨hm, rfl⟩
      obtain ⟨d, h2⟩ := (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨d, by rw [htq2, comp_apply]; exact ⟨_, h1, h2⟩⟩
  have eDn : ∀ a y s', rep tdn (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le b a = true := by
    intro a y s'; rw [htdn]
    show (a, y) = s' ∧ (∃ c, rep tq3 (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq3, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _ _).1 h1
      obtain ⟨-, -, hl⟩ := (eSw _ _ _).1 h2
      exact ⟨hm, b, bs, e, hl⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab (a, y) (a, b) := (eAB _ _ _ _).2 ⟨hm, rfl, bs, e⟩
      exact ⟨(a, b), by rw [htq3, comp_apply]; exact ⟨_, h1, (eSw _ _ _).2 ⟨rfl, ⟨_, h1⟩, hl⟩⟩⟩
  have eDu : ∀ a y s', rep du (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧ ∃ b bs, y = b :: bs := by
    intro a y s'; rw [hdu]
    show (a, y) = s' ∧ (∃ c, rep tu (a, y) c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨⟨b, bs⟩, h⟩; obtain ⟨hm, e⟩ := (eU _ _ _ _).1 h; exact ⟨hm, b, bs, e⟩
    · rintro ⟨hm, b, bs, e⟩; exact ⟨(b, bs), (eU _ _ _ _).2 ⟨hm, e⟩⟩
  -- `lone`: the rest is empty, or neither pair of heads passes
  have eLone : ∀ a y s', rep lone (a, y) s' ↔ (a, y) = s' ∧ Dm (a, y) ∧
      (y = [] ∨ ∃ b bs, y = b :: bs ∧ le a b = false ∧ le b a = false) := by
    intro a y s'; rw [hlone]
    show rep l1 (a, y) s' ∨ rep l3 (a, y) s' ↔ _
    rw [hl1, hl3, hl2, eD, eDu, eUp, eDn]
    constructor
    · rintro (⟨⟨e, hm⟩, hn⟩ | ⟨⟨⟨e, hm, b, bs, hy⟩, hn1⟩, hn2⟩)
      · refine ⟨e, hm, Or.inl ?_⟩
        cases y with
        | nil => rfl
        | cons b bs => exact absurd ⟨e, hm, b, bs, rfl⟩ hn
      · refine ⟨e, hm, Or.inr ⟨b, bs, hy, ?_, ?_⟩⟩
        · cases h : le a b
          · rfl
          · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn1
        · cases h : le b a
          · rfl
          · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn2
    · rintro ⟨e, hm, hy | ⟨b, bs, hy, h1, h2⟩⟩
      · refine Or.inl ⟨⟨e, hm⟩, ?_⟩
        rintro ⟨-, -, b, bs, hb⟩
        rw [hy] at hb
        exact List.cons_ne_nil _ _ hb.symm
      · refine Or.inr ⟨⟨⟨e, hm, b, bs, hy⟩, ?_⟩, ?_⟩
        · rintro ⟨-, -, b', bs', hb, h⟩
          rw [hy] at hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj hb
          exact Bool.false_ne_true (h1.symm.trans h)
        · rintro ⟨-, -, b', bs', hb, h⟩
          rw [hy] at hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj hb
          exact Bool.false_ne_true (h2.symm.trans h)
  -- each branch of the body
  have eC1 : ∀ a y v, rep c1 (a, y) v ↔ Dm (a, y) ∧
      (y = [] ∨ ∃ b bs, y = b :: bs ∧ le a b = false ∧ le b a = false) ∧ v = a :: y := by
    intro a y v; rw [hc1]
    constructor
    · rintro ⟨b, bs, h, rfl⟩
      obtain ⟨e, hm, hc⟩ := (eLone _ _ _).1 h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨hm, hc, rfl⟩
    · rintro ⟨hm, hc, rfl⟩; exact ⟨a, y, (eLone _ _ _).2 ⟨rfl, hm, hc⟩, rfl⟩
  have eUA : ∀ a y x, rep ua (a, y) x ↔ (Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true) ∧ x = a := by
    intro a y x; rw [hua, comp_apply]
    constructor
    · rintro ⟨s, h1, h2⟩; obtain ⟨rfl, hu⟩ := (eUp _ _ _).1 h1; exact ⟨hu, ((eA _ _ _).1 h2).2⟩
    · rintro ⟨hu, hx⟩; subst x; exact ⟨(a, y), (eUp _ _ _).2 ⟨rfl, hu⟩, (eA _ _ _).2 ⟨hu.1, rfl⟩⟩
  have eRu : ∀ c c', rep ru c c' ↔ c = c' ∧ ∃ s, rep tu s c := fun c c' => by rw [hru]; exact Iff.rfl
  have eUT : ∀ a y x, rep ut (a, y) x ↔ (Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true) ∧ ∃ b, y = b :: x := by
    intro a y x; rw [hut, comp_apply]
    constructor
    · rintro ⟨⟨b, bs⟩, h1, h2⟩
      rw [huu, comp_apply] at h1
      obtain ⟨s, h3, h4⟩ := h1
      obtain ⟨rfl, hu⟩ := (eUp _ _ _).1 h3
      obtain ⟨w, h5⟩ := (outr_holds ru (b, bs) x).1 h2
      obtain ⟨e, -⟩ := (eRu _ _).1 h5
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact ⟨hu, b, ((eU _ _ _ _).1 h4).2⟩
    · rintro ⟨hu, b, e⟩
      have h4 : rep tu (a, y) (b, x) := (eU _ _ _ _).2 ⟨hu.1, e⟩
      refine ⟨(b, x), ?_, (outr_holds ru (b, x) x).2 ⟨b, ?_⟩⟩
      · rw [huu, comp_apply]; exact ⟨(a, y), (eUp _ _ _).2 ⟨rfl, hu⟩, h4⟩
      · exact (eRu _ _).2 ⟨rfl, _, h4⟩
  have eC2 : ∀ a y v, rep c2 (a, y) v ↔ Dm (a, y) ∧ ∃ b bs, y = b :: bs ∧ le a b = true ∧ v = a :: bs := by
    intro a y v; rw [hc2]
    constructor
    · rintro ⟨a', bs, h, rfl⟩
      rw [hpu] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨⟨hm, b, bs', e, hl⟩, ea⟩ := (eUA _ _ _).1 h1
      obtain ⟨-, b', e'⟩ := (eUT _ _ _).1 h2
      subst ea
      rw [e] at e'
      obtain ⟨rfl, rfl⟩ := List.cons.inj e'
      exact ⟨hm, _, _, e, hl, rfl⟩
    · rintro ⟨hm, b, bs, e, hl, rfl⟩
      refine ⟨a, bs, ?_, rfl⟩
      rw [hpu]
      show rep ua (a, y) a ∧ rep ut (a, y) bs
      exact ⟨(eUA _ _ _).2 ⟨⟨hm, b, bs, e, hl⟩, rfl⟩, (eUT _ _ _).2 ⟨⟨hm, b, bs, e, hl⟩, b, e⟩⟩
  have eDY : ∀ a y v, rep dy (a, y) v ↔ Dm (a, y) ∧ (∃ b bs, y = b :: bs ∧ le b a = true) ∧ v = y := by
    intro a y v; rw [hdy, comp_apply]
    constructor
    · rintro ⟨s, h1, h2⟩; obtain ⟨rfl, hm, hd⟩ := (eDn _ _ _).1 h1; exact ⟨hm, hd, ((eY _ _ _).1 h2).2⟩
    · rintro ⟨hm, hd, hv⟩; subst v; exact ⟨(a, y), (eDn _ _ _).2 ⟨rfl, hm, hd⟩, (eY _ _ _).2 ⟨hm, rfl⟩⟩
  intro a y v
  rw [show rep body (a, y) v ↔ (rep c1 (a, y) v ∨ rep c2 (a, y) v) ∨ rep dy (a, y) v by
    rw [hbody, hb1]; exact Iff.rfl, eC1, eC2, eDY]
  constructor
  · rintro ((⟨hm, hc, rfl⟩ | ⟨hm, b, bs, e, h1, rfl⟩) | ⟨hm, ⟨b, bs, e, h1⟩, rfl⟩)
    · rcases hc with hc | ⟨b, bs, e, h1, h2⟩
      · exact ⟨hm, Or.inl ⟨hc, by rw [hc]⟩⟩
      · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inr (Or.inr ⟨h1, h2, rfl⟩)⟩⟩
    · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inl ⟨h1, rfl⟩⟩⟩
    · exact ⟨hm, Or.inr ⟨b, bs, e, Or.inr (Or.inl ⟨h1, rfl⟩)⟩⟩
  · rintro ⟨hm, ⟨hn, rfl⟩ | ⟨b, bs, e, ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩⟩⟩
    · exact Or.inl (Or.inl ⟨hm, Or.inl hn, by rw [hn]⟩)
    · exact Or.inl (Or.inr ⟨hm, b, bs, e, h1, rfl⟩)
    · exact Or.inr ⟨hm, ⟨b, bs, e, h1⟩, rfl⟩
    · exact Or.inl (Or.inl ⟨hm, Or.inr ⟨b, bs, e, h1, h2⟩, rfl⟩)

end Body

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.thin_body_set
