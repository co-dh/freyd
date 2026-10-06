#import "../note-prelude.typ": *
#show: note-chapter.with(2)
// note-split: chapter 2 — this header is written by scripts/note-split and stripped by scripts/note-join
= Functions and Categories <sec-categories>

== Categories

== Functors

== Natural transformations

== Constructing datatypes

== Products and coproducts

== Initial algebras

// §11.4's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus `s: 100%`,
// the squares' own size.  An algebra is an ARROW AT ITS CARRIER — `f : F(A)⟶A`, `α : F(T)⟶T`, B&dM
// (2.10) — so its bead spans the object wire and carries no dot; only the type functor's `αᴀ`
// (@tfun-defn), a family over the parameter `A`, is a transformation and draws on the functor lane.
#let ia-hom-l = "Freyd.Alg.IsFHom.lhs"
#let ia-hom-r = "Freyd.Alg.IsFHom.rhs"
#let ia-cata-l = "Freyd.Alg.InitialAlgebra.cata_comm.lhs"
#let ia-cata-r = "Freyd.Alg.InitialAlgebra.cata_comm.rhs"

#disp[#definition[
The *initial algebra* `α : F(T)⟶T` has exactly one F-homomorphism `⦇f⦈ : T⟶A` to every F-algebra `f : F(A)⟶A`.

  // ONE OBJECT, ONE HUE down the display: `A` is amber in both rows.  The positional defaults would
  // paint the same carrier red in the row below and cyan in the row above.
  #pair(
    leancd("Freyd.Alg.IsFHom"),
    lean(ia-hom-l, ia-hom-r, op: [=]),
    [#leanf("Freyd.Alg.IsFHom")],
  )
  #pair(
    leancd("Freyd.Alg.InitialAlgebra.cata_comm"),
    lean(ia-cata-l, ia-cata-r, op: [=]),
    [#leanf("Freyd.Alg.InitialAlgebra.cata_comm")],
  )
  // lean:AOP.A5_5.relCata_cancel@c83d7b44
]]<initial-defn>

// B&dM p.47: `h = ⦇c,f⦈` on `Nat`, `α = [zero,succ]`, `F(A) = 1+A`, `F(h) = 𝟙+h`.  The book's chain
// is of equivalences between equations; its first four steps each rewrite ONE side, so the right
// side's two steps are the first row, the left side's two the second, and cancellation the third.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.nat_fold_spec") \
    #src[`h` is a homomorphism from `α = [zero,succ]` to `[c,f]` exactly when `h` sends `zero` to
     `c` and `succ` then `h` equals `h` then `f`]],
  // lean:AOP.A2_6.nat_fold_spec@15a8703a
  lean-chain(
    (
      (none, "Freyd.Alg.nat_fold_spec_step1.lhs", src[the right side]),
      (EQ, "Freyd.Alg.nat_fold_spec_step1.rhs", src[definition of `F`]),
      // lean:AOP.A2_6.nat_fold_spec_step1@3617b276
      (EQ, "Freyd.Alg.nat_fold_spec_step2.rhs", src[coproduct]),
      // lean:AOP.A2_6.nat_fold_spec_step2@34821c4d
    ),
    (
      (none, "Freyd.Alg.nat_fold_spec_step3.lhs", src[the left side]),
      (EQ, "Freyd.Alg.nat_fold_spec_step3.rhs", src[since `α = [zero,succ]`]),
      // lean:AOP.A2_6.nat_fold_spec_step3@a9a30fd5
      (EQ, "Freyd.Alg.nat_fold_spec_step4.rhs", src[coproduct]),
      // lean:AOP.A2_6.nat_fold_spec_step4@46340f81
    ),
    (
      (IFF, ("Freyd.Alg.nat_fold_spec_step5_zero",), src[cancellation, `zero` arm]),
      (src[and], ("Freyd.Alg.nat_fold_spec_step5_succ",), src[cancellation, `succ` arm]),
      // lean:AOP.A2_6.nat_fold_spec_step5@35ed707e
      // lean:AOP.A2_6.nat_fold_spec_step5_zero@9c564d74
      // lean:AOP.A2_6.nat_fold_spec_step5_succ@ba04cad9
    ),
  ),
)]<nat-fold-spec>

=== Reflection

// THE LAW ITSELF, not the square that proves it.  The identity natural transformation "is represented by
// the edge for the corresponding functor" (IntroString p. 37), so the right of the `=` is the `T` wire
// alone in its grey `𝟏` box — a panel with no bead, not an empty cell.  The `T` on the wire under the
// bead is the fold's carrier: this is the fold of the initial algebra itself, `α : F(T)⟶T`.
#let ia-refl-l = "Freyd.Alg.relCata_alpha.lhs"
#let ia-refl-r = "Freyd.Alg.relCata_alpha.rhs"

#disp[#pair(
  leancd("Freyd.Alg.relCata_alpha"),
  lean(ia-refl-l, ia-refl-r, op: [=]),
 [#leanf("Freyd.Alg.relCata_alpha") #h(6pt) #src[(2.11)]],
)]<cata-reflection>

// `relCata_alpha`, AOP/A6_3.lean:40.
Taking a value apart with `α` and putting it straight back is doing nothing.

=== #leanf("Freyd.Alg.relCata_fusion") — folding with `R`, then applying `S`, is folding with `Q`

// `T` is already the initial algebra's carrier, so the two algebras of the law take their own letters,
// `R` on `B` and `Q` on `C`; `S` is the homomorphism between them, not an algebra.
When `S : B⟶C` is an F-homomorphism from `R : F(B)⟶B` to `Q : F(C)⟶C`, folding with `R` and
then applying `S` is folding with `Q`.

// `s: 92%`: the one row that does not fit at full size.  The side condition is the homomorphism
// square of @initial-defn at `f := R`, `g := Q`, `h := S`.
#let ia-fuse-l = "Freyd.Alg.relCata_fusion#h.lhs"
#let ia-fuse-r = "Freyd.Alg.relCata_fusion#h.rhs"
// The conclusion, generated like the side condition above it: the two folds differ by their algebra,
// and the wire under each says where it lands — `B` on the left, `C` on the right.
#let ia-fuse-cl = "Freyd.Alg.relCata_fusion.lhs"
#let ia-fuse-cr = "Freyd.Alg.relCata_fusion.rhs"

#disp[#pair(
  leancd("Freyd.Alg.relCata_fusion"),
  grid(
    columns: 2, align: horizon, column-gutter: 16pt, row-gutter: 10pt,
    src[the side condition],
    lean(ia-fuse-l, ia-fuse-r, op: [=]),
    src[the conclusion],
    lean(ia-fuse-cl, ia-fuse-cr, op: [=]),
  ),
  [#leanf("Freyd.Alg.relCata_fusion") #h(6pt)
 #src[(2.12)]],
  s: 92%,
)]<cata-fusion>

== Type functors

#disp[#definition[
#leanf("Freyd.Alg.typeMap") #h(4pt) — the type functor `T` acts on a map `f : A⟶B` through the initial algebras `α`#sub[`A`]` : F(A,TA)⟶TA`.
]]<tfun-defn>

// The square is the five arrows `alpha_natural_split` states; the algebra `F(f,𝟙)α_B` is the path
// through `F(B,TB)`, not a sixth arrow, because the statement names no such composite.
// TWO WIRES, not one indexed `F`: `⟨𝟙,T⟩ : 𝒜⟶𝒜×𝒜` packs the two arguments and `F : 𝒜×𝒜⟶𝒜` is then
// unary, so every wire is a functor again and the region between them is `𝒜×𝒜`.  That is what makes
// `F(f,T(f))` free — it is `f` on the object wire with `⟨𝟙,T⟩` and `F` running past — and the law the
// naturality of `α`, the `f` bead sliding past it.  Not `P`, which is the powerset relator already.
// This REPLACES the 2026-08-26 unindexed-`F` exception, which needed a second bead `F(f,𝟙)`.
#let tfun-l = "Freyd.Alg.alphaT_natural.lhs"
#let tfun-r = "Freyd.Alg.alphaT_natural.rhs"
#disp[#pair(
  leancd("Freyd.Alg.alpha_natural_split"),
  row((lean(tfun-l, tfun-r, op: [=]),), s: 92%),
  [#leanf("Freyd.Alg.alpha_natural") #h(6pt)
 #src[]],
)]<tfun-sq>

- `F : 𝒜×𝒜⟶𝒜` is a bifunctor and a wire is a unary functor, so the two arguments are packed first:
  `⟨𝟙,T⟩ : 𝒜⟶𝒜×𝒜` sends `A` to `(A,TA)`, and `F(⟨𝟙,T⟩(A))` is `F(A,TA)`.
- The picture is three wires — `F`, `⟨𝟙,T⟩`, and the object — and the region between the first two
  is `𝒜×𝒜`.
- `α` is then an ordinary natural transformation `F∘⟨𝟙,T⟩⇒T`: its bead eats the `F` and `⟨𝟙,T⟩` wires,
  and the `T` wire is born under it.
- `F(f,T(f))` costs no notation. It is the bead `f` on the object wire with `⟨𝟙,T⟩` and `F` running
  past: `⟨𝟙,T⟩` is what turns `f` into the pair `(f,T(f))`, and `F` is what applies it.
- The law is the naturality of `α`, which is exactly the freedom to slide that `f` bead past it.

// The defining square of `⦇F(f,𝟙)h⦈`, its right column drawn twice: straight down as the one fold, and
// bowed out through `TB` as `T(f)` then `⦇h⦈`.  That the two paths agree IS the law.
#disp[#pair(
  leancd("Freyd.Alg.typeMap_fusion_cancel"),
  row((
    lean("Freyd.Alg.typeMap_fusion"),
  )),
  [#leanf("Freyd.Alg.typeMap_fusion") #h(6pt)
 #src[]],
)]<tfun-fusion>

// Moved from §5.5's @tf-laws (rows 2-4, ch2 items): same table helper, same widths and stroke.
#disp[#table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [functor],
  [#leanf("Freyd.Alg.typeMap_id") and #leanf("Freyd.Alg.typeMap_comp")],
  [Acting by the identity changes nothing, and two actions in a row are one action.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_id@602faba9 lean:AOP.A5_5_TypeFunctor.typeMap_comp@74556074

  [type functor fusion],
  [#leanf("Freyd.Alg.typeMap_fusion")],
  [A relator action followed by a fold is a single fold — the intermediate structure is never built.
   The side condition holds because `F` is a bifunctor —
   `F(R,𝟙)F(𝟙,⦇Q⦈)=F(R,⦇Q⦈)=F(𝟙,⦇Q⦈)F(R,𝟙)`.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_fusion@fde772c0 lean:AOP.A5_5_TypeFunctor.interchange@cc0eb4af

  [naturality of `α`],
  [#leanf("Freyd.Alg.alpha_natural")],
  [Building and then mapping is the same as mapping the parts and then building, so `α` is natural
   from `G(R)=F(R,T(R))` to `T`.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.alpha_natural@ee446834
)]<tf-laws-2>
