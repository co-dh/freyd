import Freyd.S1_1
import Freyd.S1_24
import Freyd.S1_28
import Freyd.S1_39
import Freyd.S1_8
import Freyd.S1_9
import Freyd.S1_18
import Freyd.S1_81
import Freyd.S1_85
import Freyd.S1_97_ToposDistributive
import Freyd.S1_91
import Freyd.S1_92
import Freyd.S1_934_PartialMapClassifier
import Freyd.S1_94
import Freyd.S1_97
import Freyd.S1_26
import Freyd.S1_27
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_44
import Freyd.S1_438_FunctorReflects
import Freyd.S1_45
import Freyd.S1_47
import Freyd.S1_444_Horn
import Freyd.S1_421_Initial
import Freyd.S1_51
import Freyd.S1_513_CoveringFamily
import Freyd.S1_52
import Freyd.S1_53
import Freyd.S1_53_SliceRegular
import Freyd.S1_93_SliceTopos
import Freyd.S1_93_SlicePower
import Freyd.S1_931_SlicePi
import Freyd.S1_532_SliceDeltaCartesian
import Freyd.S1_53_BaseChangeDescent
import Freyd.S1_55
import Freyd.S1_36
import Freyd.S1_54
import Freyd.S1_58
import Freyd.S1_59
import Freyd.S1_595_AbCategory
import Freyd.S1_594_AbAbelian
import Freyd.S1_595_AbRegular
import Freyd.S1_596_AbFunctorCategory
import Freyd.S1_59_ExactRepresentation
import Freyd.S1_60
import Freyd.S1_70
import Freyd.S1_59_10_Frobenius
import Freyd.S1_56
import Freyd.S1_568_Quot
import Freyd.S1_57
import Freyd.S1_572_Recursive
import Freyd.S1_572b_NotEffective
import Freyd.S1_573_PrimRec
import Freyd.S1_62
import Freyd.S1_64
import Freyd.S1_65
import Freyd.S1_662_Diaconescu
import Freyd.S1_72
import Freyd.S1_14
import Freyd.S1_74
import Freyd.S1_75
import Freyd.S1_77
import Freyd.S1_82
import Freyd.S1_84
import Freyd.S1_95
import Freyd.S1_943_ToposRTC
import Freyd.S1_95_ToposColimits
import Freyd.S1_967_ToposIndexedJoins
import Freyd.S1_967_ToposExists
import Freyd.S1_967_ToposCopowers
import Freyd.S1_543_DirectedColimit
import Freyd.S1_543_WellOrdering
import Freyd.S1_543_CatColimit
import Freyd.S1_543_CatColimitRegular
import Freyd.S1_543_Capitalization
import Freyd.S1_543_CapitalizationTransfinite
import Freyd.S1_541_RelativeCapitalization
-- §1.543 capitalization: the FULL sorry-free closure of `Freyd.capData_exists`.  `CapDataWiring`
-- discharges `∀ A, Nonempty (CapData A)` by the §1.547 uniform cofinal successor (`uniformStep`) plus
-- the §1.546 fibre-density obligation, and transitively imports the whole cofinal-route stack:
--   UniformCapStep → UniformWellPoints → FibreDensityProof → CapDataWiring (all sorry-free).
-- `capData_exists`/`capitalization_lemma` are LIVE here; `#print axioms` = [propext, Classical.choice,
-- Quot.sound].  (The alternative §1.547 `PairObj` route — `RationalCapitalization`/`SliceWellPointed` —
-- is NOT imported; it carried isolated sorries and is unreachable from this chain.)
import Freyd.S1_543_CapitalizationLaxColimit
import Freyd.S1_543_LaxColimitPreReg
import Freyd.S1_543_CofinalHstage
import Freyd.S1_543_RatCapPreReg
import Freyd.S1_543_RatCapHcanon
import Freyd.S1_543_RatCapStagePTC
import Freyd.S1_547_CofinalProjSystem
import Freyd.S1_547_UniformCapStep
import Freyd.S1_543_UniformWellPoints
import Freyd.S1_546_FibreDensityProof
import Freyd.S1_543_CapDataWiring
import Freyd.S1_543_LaxColimitImages
import Freyd.S1_543_LaxColimitCoproduct
import Freyd.S1_543_LaxGermProducts
import Freyd.S1_543_LaxGermImages
import Freyd.S1_543_LaxGermEqualizers
import Freyd.S1_543_LaxGermCoproduct
import Freyd.S1_61_LaxStrictInitial
import Freyd.S1_63_LaxInvImageUnion
import Freyd.S1_621_LaxDisjoint
import Freyd.S1_63_LaxColimitPositive
import Freyd.S2_218_RatCapPositive
import Freyd.S2_218_CapDataPositive
import Freyd.S1_547_UniformStepCoproduct
import Freyd.S2_218_CapDataPositiveTower
import Freyd.S1_543_RatCapImages
import Freyd.S1_543_CapDataRegular
import Freyd.S2_218_PowerAllegoryFamily
import Freyd.S1_635_StalkFamily
import Freyd.S1_635_StalkDetect
import Freyd.S1_634_TstarRegular
import Freyd.S1_635_TstarConservative
import Freyd.S1_635_StalkRepr
import Freyd.S1_543_UnionFromCoproduct
import Freyd.S1_621_ColimitPositive
import Freyd.S1_543_ColimitCoproductGerm
import Freyd.S1_63_ColimitInvImageUnion
import Freyd.S2_218_ColimitPreLogos
import Freyd.S1_544_Inflation
import Freyd.S2_1
import Freyd.S2_16
import Freyd.S2_2
import Freyd.S2_22
import Freyd.S2_16b
import Freyd.S2_16c
import Freyd.S2_55
import Freyd.S2_43
import Freyd.S2_433_SplEqInstance2
import Freyd.S2_42
import Freyd.S2_3
import Freyd.S2_31
import Freyd.S2_11
import Freyd.S2_4
import Freyd.S2_44
import Freyd.S2_417_Generator
import Freyd.S2_417b_NotPower
import Freyd.S2_417c_ProperLabels
import Freyd.S2_438_Godel
import Freyd.S2_437_REAllegory
import Freyd.S2_437b_NotDivision
import Freyd.S2_441_StraightJoin
import Freyd.S2_5
import Freyd.S2_51
import Freyd.S2_53
import Freyd.S2_54
import Freyd.S2_52
import Freyd.S2_34
import Freyd.S1_38b
import Freyd.S1_637_FiniteSeparation
import Freyd.S1_646_Representation
import Freyd.S1_13
import Freyd.S1_10
import Freyd.S1_422_FunctorCategory
import Freyd.S2_147_MapCat
import Freyd.S2_165_Spl
import Freyd.S2_216_MatrixAllegory
import Freyd.S2_217_PositiveRepr
import Freyd.S1_723_Locale
import Freyd.S2_168_ValuedSetsTabular
import Freyd.S2_111_RelCat
import Freyd.S2_154_CategoriesIso
import Freyd.S2_41
import Freyd.S2_41b
import Freyd.S2_424_ConnectedPowerTopos
import Freyd.S2_21
import Freyd.S2_21b
import Freyd.S2_21c
import Freyd.S1_526_StalkConservative
import Freyd.S2_153_Assemblies
import Freyd.S2_16d
import Freyd.S2_16e_TwoPresentations
import Freyd.S2_16_Recursive
import Freyd.S2_153_NonEffective
import Freyd.S2_153b_RecursiveModulus
import Freyd.S2_153c_ConcreteNonEffective
import Freyd.S2_153d_NonEffWitness
import Freyd.S2_153e_ComposeCaucus
import Freyd.S2_153f_ParityWitness
import Freyd.S2_155_BiEntire
import Freyd.S2_156_PartitionRep
import Freyd.S2_157_ProjectivePlane
import Freyd.S2_157b_Desargues
import Freyd.S2_157c_Converse
import Freyd.S2_157d_HornTop
import Freyd.S2_157e_HornCenter
import Freyd.S2_157f_HornLine
import Freyd.S2_157g_ConverseHeadline
import Freyd.S2_157h_VeblenWedderburn
import Freyd.S2_157i_NotRepresentable
import Freyd.S2_158_GraphAllegory
import Freyd.S2_158b_NoFiniteAxiom
import Freyd.S2_158c_StepRigidity
import Freyd.S2_158d_SPWall
import Freyd.S2_158e_InstanceBound
import Freyd.S2_158f_SPWallProof
import Freyd.S2_33
import Freyd.S1_631_CapitalProjective
-- Bird & de Moor, Algebra of Programming, ch. 4 (only material not already in Freyd S2_*)
import AOP.A4_1
import AOP.A4_2
import AOP.A4_3
import AOP.A4_4
import AOP.A4_5
import AOP.A4_6
-- Bird & de Moor ch. 5: relators and datatypes in allegories
import AOP.A5_1
import AOP.A5_2
import AOP.A5_3
import AOP.A5_4
import AOP.A5_5
import AOP.A5_6
import AOP.A5_7
-- Bird & de Moor ch. 6: recursive programs (fixed points, hylomorphisms, closure)
import AOP.A6_2
import AOP.A6_3
import AOP.A6_5
import AOP.A6_7
-- Bird & de Moor ch. 7: optimisation problems (min/max, monotonic algebras, greedy theorem)
import AOP.A7_1
import AOP.A7_2
-- Bird & de Moor ch. 8: thinning algorithms (thin, thinning theorem)
import AOP.A8_1
-- Bird & de Moor ch. 9: dynamic programming (principle of optimality, DP + thinning theorems)
import AOP.A9_1
-- Beyond B&dM: ∞-completed dynamic programming (dead branches via a top-valued fallback;
-- fixes Theorem 9.1's Egli–Milner gap on value-axis DPs — instantiated in leet.L322_dp)
import AOP.A9_2
-- Bird & de Moor ch. 10: greedy algorithms (Theorem 10.1 — greedy as extreme dynamic programming)
import AOP.A10_1
-- Concrete model Rel(Set) for the AoP case studies (objects = types, morphisms = relations):
-- the full allegory stack (power/LCDA/tabular/unitary) in which the §6.1+ programs actually run.
import AOP.A6_1_RelSet
-- Bird & de Moor §6.1: Digits of a number — Decimal as an initial algebra of `F A = Digit⁺ + A×Digit`,
-- the reading catamorphism `val`, and the recursive equation for `val°` (first worked AoP program).
import AOP.A6_1_Digits
-- Generic snoc-list datatype `SnocList L E = L + (·)×E` as an initial algebra (reusable engine).
import AOP.A6_SnocList
-- Bird & de Moor §6.4: fast exponentiation/modulus — `exp`/`mod` as hylomorphisms over the binary
-- datatype `Bin = SnocList Unit Bit`, giving the O(log) divide-and-conquer least fixed point.
import AOP.A6_4_FastExp
-- Generic cons-list `ConsList L E = L + E×(·)` (head/tail) as an initial algebra; `list A = ConsList Unit A`.
import AOP.A6_ConsList
-- Bird & de Moor §6.6: sorting by selection — `sort = ⦇[nil, select°]⦈°` (converse of a catamorphism)
-- with its recursion; correctness `sort ⊆ ordered·perm` by fusion (given the select proviso).
import AOP.A6_6_Sort
-- Bird & de Moor §7.3: planning a company party — `choose` monotonicity + party planning solved by
-- the greedy theorem (`greedy_max`); the rose-tree datatype `tree A = node(A, list(tree A))` deferred.
import AOP.A7_3_Party
-- Bird & de Moor §5.6: combinatorial list relations — perm/prefix/subseq/inlist over `list A = ConsList
-- Unit A`, with reflexivity/symmetry/transitivity (the coalgebra/spec layer for the case studies).
import AOP.A5_6_ListCombinators
-- Bird & de Moor §6.6 FULLY CONCRETE: selection sort correctness with NO hypotheses — concrete
-- `select`/ordered algebra + the fusion proviso discharged via the §5.6 `perm`/`inlist`.
import AOP.A6_6b_SortConcrete
-- Bird & de Moor §10.2: detab-entab — the tupled catamorphism `(detab, col·detab) = ⦇[base,step]⦈`
-- over snoc-lists of chars, with its loop recursion (base/step case).
import AOP.A10_2_Detab
-- Bird & de Moor §8.4: the knapsack problem — binary thinning; `knapsack_thinning` = the thinning
-- theorem `thinning_min` instantiated (selections=subsequences, order by value, thin by weight).
import AOP.A8_4_Knapsack
-- Bird & de Moor case studies §7.4–§10.4 (each = the relevant abstract optimisation theorem —
-- greedy/thinning/DP — instantiated for the problem; concrete problem-specific data deferred).
import AOP.A7_4_Cylinder
import AOP.A7_5_SecurityVan
import AOP.A8_2_LayeredNetwork
import AOP.A8_3_ImplementingThin
import AOP.A8_5_Paragraph
import AOP.A8_6_Bitonic
import AOP.A9_2_StringEdit
import AOP.A9_3_Bracketing
import AOP.A9_4_Compression
import AOP.A10_3_Tardiness
import AOP.A10_4_TeX
-- LeetCode 121 (Best Time to Buy and Sell Stock) — programmed in the allegory Rel(Set): the O(n)
-- scan as a snoc-list catamorphism, proven equal to max(≤)·Λspec.  Uses the copied `exacts` tactic.
import Freyd.Exacts
import leet.L121
-- LeetCode 322 (Coin Change) re-derived through the ∞-DP theorem `A9_2.dynamic_programming_inf`:
-- the value-axis DP whose optimality now comes from the A-layer, not a hand fuel-induction.
import leet.L322_dp
-- A relation-algebra INTERPRETER: a term AST + two sound evaluators — `eval` into finite Bool
-- matrices (`FinRel`, a proven allegory ⇒ soundness free; runs ground terms + the exponential
-- powerset specs) and `evalP`, a structural fold running the derived catamorphism programs in
-- polynomial time — bridged by the proven `solve = A spec ≫ maxRel D` (differential testing).
import rel.RelInterp
-- Auto-derive: a generic driver theorem `RunningBest` that discharges every `horner_correct` side
-- condition (monotonicity, greedy refinement, order transitivity) from 8 one-line arithmetic facts,
-- so a new running-best-pair greedy problem supplies only its creative inputs (pair state + generator
-- + dominance order), not the ~100 lines of relational boilerplate. Kadane (L53) is derived through it.
import rel.AutoDerive
import leet.L53
-- Auto-derive increment 2: DP drivers (`DPInf` ∞-DP + `DPCount` step-counting) that discharge every
-- `dynamic_programming_inf` hypothesis + the concrete memo packaging from a small bundle. Cuts
-- `L322_dp` 518→189 lines; reused fresh on `L279` (Perfect Squares).
import rel.AutoDeriveDP
import leet.L279
-- Thread B — propose→test→certify glue: enumerate candidate program shapes from a catalog, TEST each
-- (run the spec `A spec ≫ maxRel D` via FinRel.eval vs the candidate fold via evalP) to auto-select
-- the correct shape, then CERTIFY the winner via `RunningBest`. Demo picks L121's pair program (proved
-- `= prog121` by rfl) after rejecting 17 wrong shapes. Soundness caveat: the runnable-spec ↔ Rel(Set)-
-- spec link is by construction, not yet a Lean proof (the spec-transport gap, next to close).
import rel.AutoDeriveSearch
-- Auto-derive: thinning driver (`ThinBest`) — discharges Theorem-8.1/Cor-8.1 side conditions + a
-- verified generic Pareto prune (`thinList`, closing §8.3's deferred implementation) + the set-valued
-- fold-bridge. Demo closes B&dM §8.4's concrete 0/1-knapsack binary-thinning program (was only abstract).
import rel.AutoDeriveThin
