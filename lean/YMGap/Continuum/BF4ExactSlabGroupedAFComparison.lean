/-
# Exact corrected slab versus the grouped BF4 Mehler endpoint

The exact Peter--Weyl coefficient of a Yang--Mills slab is signed.  It is
therefore not an entrywise-positive Markov joint law, and its row sum is not
a probability marginal.  The weighted Schur comparison nevertheless applies
to two symmetric signed matrices once a positive row scale is supplied.

This file supplies the canonical scale available on the geometric BF4
boundary: the diagonal of the exact five-holonomy Haar--L2 Gram.  Labels with
zero Haar norm are removed by a decidable filter.  On this carrier we compare

* the normalized literal 72-face/116-link corrected-slab Haar network; and
* the normalized positive grouped Feynman--Kac/Mehler feature Gram.

The finite perturbation theorem then gives the exact additive error
`rate + epsilon`.  Two spacing-uniform eighth bounds imply the desired
quarter bound by rational order alone.

Honest frontier.  Exact reflection symmetry is proved on the literal slab.
Vacuum positivity has two concrete consumers: a signed-tail bound, and the
stronger termwise exposed-link annihilation statement which proves that the
vacuum partition is exactly one.  The latter is pinned to the displayed
116-link dual term; its all-spin one-link Peter--Weyl proof remains open.
The grouped endpoint mean-zero rate and row-relative analytic estimate also
remain named data.  No arbitrary "physical kernel" field and no
multiplicity-product surrogate occurs.  In particular this module does not
claim that a signed Peter--Weyl matrix is a Markov law.  Identification of the
displayed weighted mean-zero hyperplane with the physical Perron complement
remains a separate theorem.

## Axiom gate

Finite lists, exact `Q'` order, product-Haar polynomial positivity, and the
constructive Schur/Young estimate only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactSlabVacuumReflection
import YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
import YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
import YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
import YMGap.Continuum.BF4GeometricAllSpinHaarGram
import YMGap.Continuum.BF4ReflectedAllSpinMehlerGramAFRow

namespace YMGap.Continuum.BF4ExactSlabGroupedAFComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumFixedFaceGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
open YMGap.Continuum.BF4GeometricAllSpinHaarGram
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Canonical positive Haar--L2 diagonal carrier -/

/-- The exact five-holonomy Haar--L2 squared norm of one geometric BF4
boundary spin network.  Distinct labels need not be orthogonal. -/
def exactSlabBoundaryHaarDiagonalWeight
    (state : EdgeLabelling) : Q' :=
  geometricAllSpinHaarKernel state state

/-- The diagonal Haar weight is nonnegative for every all-spin label. -/
theorem exactSlabBoundaryHaarDiagonalWeight_nonnegative
    (state : EdgeLabelling) :
    (0 : Q') ≤ exactSlabBoundaryHaarDiagonalWeight state := by
  exact geometricAllSpinHaarKernel_diagonal_nonnegative state

/-- The vacuum boundary vector has strictly positive (indeed normalized)
Haar norm. -/
theorem exactSlabBoundaryHaarDiagonalWeight_vacuum_pos :
    (0 : Q') <
      exactSlabBoundaryHaarDiagonalWeight zeroEdgeLabelling := by
  decide

/-- The finite cutoff carrier with every zero-norm geometric boundary vector
removed.  This filter is constructive because exact rational strict order is
decidable. -/
def exactSlabPositiveHaarStates (K : Nat) : List EdgeLabelling :=
  (centralHalfStates K 0).filter
    (fun state => (0 : Q') < exactSlabBoundaryHaarDiagonalWeight state)

theorem mem_exactSlabPositiveHaarStates_iff
    {K : Nat} {state : EdgeLabelling} :
    state ∈ exactSlabPositiveHaarStates K ↔
      state ∈ centralHalfStates K 0 ∧
        (0 : Q') < exactSlabBoundaryHaarDiagonalWeight state := by
  simp [exactSlabPositiveHaarStates]

private theorem zeroEdgeLabelling_mem_centralHalfStates (K : Nat) :
    zeroEdgeLabelling ∈ centralHalfStates K 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

/-- The canonical retained carrier is nonempty at every cutoff: it contains
the normalized vacuum boundary vector. -/
theorem zeroEdgeLabelling_mem_exactSlabPositiveHaarStates (K : Nat) :
    zeroEdgeLabelling ∈ exactSlabPositiveHaarStates K := by
  exact mem_exactSlabPositiveHaarStates_iff.mpr
    ⟨zeroEdgeLabelling_mem_centralHalfStates K,
      exactSlabBoundaryHaarDiagonalWeight_vacuum_pos⟩

private theorem boundedEdgeLabellings_length_local (K : Nat) :
    ∀ ids : List Nat,
      (boundedEdgeLabellings K ids).length =
        (K + 1) ^ ids.length
  | [] => rfl
  | head :: tail => by
      unfold boundedEdgeLabellings
      have hflat :=
        YMGap.Continuum.Z4FiniteBoxTrivalentResolution.length_flatMap_fixed
        (List.range (K + 1))
        (fun spin =>
          (boundedEdgeLabellings K tail).map
            (fun label => setEdgeLabel label head spin))
        ((K + 1) ^ tail.length)
        (fun _ => by
          simp [boundedEdgeLabellings_length_local K tail])
      rw [hflat, List.length_range, List.length_cons, Nat.pow_succ]
      exact Nat.mul_comm _ _

/-- The unfiltered extent-one lower boundary has exactly 24 independent
labels, hence `(K+1)^24` states. -/
theorem centralHalfStates_zero_length (K : Nat) :
    (centralHalfStates K 0).length = (K + 1) ^ 24 := by
  unfold centralHalfStates
  rw [boundedEdgeLabellings_length_local]
  congr

/-- The positive Haar carrier grows no faster than the explicit
24-label cube.  This is the cardinality appearing in the entry-decay
payment, now exposed independently of the filter implementation. -/
theorem exactSlabPositiveHaarStates_length_le (K : Nat) :
    (exactSlabPositiveHaarStates K).length ≤ (K + 1) ^ 24 := by
  exact Nat.le_trans
    (List.length_filter_le _ _)
    (Nat.le_of_eq (centralHalfStates_zero_length K))

/-- Every retained row has a strictly positive, canonical Haar-diagonal
scale. -/
theorem exactSlabBoundaryHaarDiagonalWeight_pos_on
    {K : Nat} {state : EdgeLabelling}
    (hstate : state ∈ exactSlabPositiveHaarStates K) :
    (0 : Q') < exactSlabBoundaryHaarDiagonalWeight state :=
  (mem_exactSlabPositiveHaarStates_iff.mp hstate).2

/-- Weighted square used by the signed-matrix Schur comparison. -/
def exactSlabBoundaryWeightedSquare
    (K : Nat) (observable : EdgeLabelling → Q') : Q' :=
  finiteWeightedSquare
    (exactSlabPositiveHaarStates K)
    exactSlabBoundaryHaarDiagonalWeight
    observable

theorem exactSlabBoundaryWeightedSquare_nonnegative
    (K : Nat) (observable : EdgeLabelling → Q') :
    (0 : Q') ≤ exactSlabBoundaryWeightedSquare K observable := by
  unfold exactSlabBoundaryWeightedSquare finiteWeightedSquare
  apply listQSum_nonnegative_on
  intro state _
  exact Q'.mul_nonneg _ _
    (exactSlabBoundaryHaarDiagonalWeight_nonnegative state)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (observable state))

/-- Concrete weighted-zero hyperplane on the retained geometric boundary.
The later physical Perron identification must prove that this is the desired
vacuum-orthogonal carrier; it is not asserted by definition. -/
def ExactSlabBoundaryMeanZero
    (K : Nat) (observable : EdgeLabelling → Q') : Prop :=
  listQSum
      (fun state =>
        exactSlabBoundaryHaarDiagonalWeight state * observable state)
      (exactSlabPositiveHaarStates K) ≈
    0

/-! ## 2. Literal exact-slab normalization -/

/-- The literal signed reflected kernel of the corrected extent-one slab. -/
def exactSlabRawKernel
    (w : Q') (K : Nat)
    (left right : EdgeLabelling) : Q' :=
  exactCorrectedSlabReflectedKernel w K 0 left right

/-- Its displayed vacuum--vacuum coefficient. -/
def exactSlabVacuumPartition (w : Q') (K : Nat) : Q' :=
  exactSlabRawKernel w K zeroEdgeLabelling zeroEdgeLabelling

/-- Every non-vacuum fixed-interface contribution to the literal
vacuum--vacuum entry.  Signed Haar contractions are retained, so the
absolute smallness of this displayed tail is the exact positivity target. -/
def exactSlabVacuumBoundaryTerm
    (w : Q') (K : Nat) (boundary : EdgeLabelling) : Q' :=
  exactCorrectedSlabDualTerm w K 1
    (assembleReflectedSlabLabelling 0
      zeroEdgeLabelling boundary zeroEdgeLabelling)

def exactSlabVacuumTail (w : Q') (K : Nat) : Q' :=
  listQSum
    (exactSlabVacuumBoundaryTerm w K)
    ((centralBoundaryChannels K 0).filter (fun boundary =>
      !(labelWithinB 0 (centralFixedFaceIds 0) boundary)))

private theorem listQSum_eq_value_add_filter_not
    {A : Type} (value : A → Q') (test : A → Bool)
    (target : A) (items : List A)
    (hfilter : items.filter test = [target]) :
    listQSum value items ≈
      value target +
        listQSum value (items.filter (fun item => !(test item))) := by
  refine Q'.eqv_trans _ _ _
    (listQSum_filter_partition value test items) ?_
  rw [hfilter]
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_of_eq (Q'.add_zero' (value target)))

private theorem listQSum_eqv_zero_of_mem
    {A : Type} (value : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_mem value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem rangeNodupLocal (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

private theorem centralFixedFaceIds_nodup_local (half : Nat) :
    (centralFixedFaceIds half).Nodup := by
  have hfull :
      (slabPhysicalFaceEdges (centralExtent half)).Nodup := by
    unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  have hall :
      ((centralLowerFaceIds half ++ centralFixedFaceIds half) ++
        centralUpperFaceIds half).Nodup := by
    simpa [centralLowerFaceIds, centralFixedFaceIds,
      centralUpperFaceIds] using
      ((centralSlabFaceIdParts_perm half).symm.nodup hfull)
  exact (List.nodup_append.mp
    (List.nodup_append.mp hall).1).2.1

/-- Exact decomposition of the signed vacuum partition into its normalized
all-zero channel and the displayed non-vacuum tail. -/
theorem exactSlabVacuumPartition_eq_one_add_tail
    (w : Q') (K : Nat) :
    exactSlabVacuumPartition w K ≈
      1 + exactSlabVacuumTail w K := by
  unfold exactSlabVacuumPartition exactSlabRawKernel
    exactCorrectedSlabReflectedKernel
  have hfilter :
      (centralBoundaryChannels K 0).filter
          (labelWithinB 0 (centralFixedFaceIds 0)) =
        [zeroEdgeLabelling] := by
    unfold centralBoundaryChannels
    rw [boundedEdgeLabellings_filter_cutoff
      (K := 0) (L := K) (Nat.zero_le K)
      (centralFixedFaceIds 0) (centralFixedFaceIds_nodup_local 0),
      boundedEdgeLabellings_zero]
  refine Q'.eqv_trans _
    (exactSlabVacuumBoundaryTerm w K zeroEdgeLabelling +
      exactSlabVacuumTail w K) _
    (listQSum_eq_value_add_filter_not
      (exactSlabVacuumBoundaryTerm w K)
      (labelWithinB 0 (centralFixedFaceIds 0))
      zeroEdgeLabelling (centralBoundaryChannels K 0) hfilter) ?_
  unfold exactSlabVacuumBoundaryTerm
  rw [YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget.assembleReflectedSlabLabelling_zero]
  exact Q'.add_eqv_congr_right _ _ _
    (exactCorrectedSlabDualTerm_vacuum w K 1)

/-- The exact, non-surrogate statement selected by exposed-link
orthogonality: every non-vacuum fixed-face labelling has zero literal
116-link Haar contraction.  This proposition is deliberately pinned to the
displayed dual term, rather than to an arbitrary kernel interface. -/
def ExactSlabVacuumNontrivialTermsVanish
    (w : Q') (K : Nat) : Prop :=
  ∀ boundary,
    boundary ∈ centralBoundaryChannels K 0 →
    boundary ≠ zeroEdgeLabelling →
      exactCorrectedSlabDualTerm w K 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling) ≈
        0

/-- Removing the positive heat coefficient from the obstruction: exact
unweighted Haar annihilation of every non-vacuum interface term implies the
weighted statement for every coupling. -/
theorem exactSlabVacuumNontrivialTermsVanish_of_haar
    {K : Nat}
    (hhaar : ExactVacuumNontrivialHaarTermsVanish K)
    (w : Q') : ExactSlabVacuumNontrivialTermsVanish w K := by
  intro boundary hboundary hnonvacuum
  unfold exactCorrectedSlabDualTerm
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor w K 1
        (assembleReflectedSlabLabelling 0
          zeroEdgeLabelling boundary zeroEdgeLabelling) * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (hhaar boundary hboundary hnonvacuum)
  · exact Q'.mul_zero_eqv _

/-- If the exposed-link Peter--Weyl statement holds termwise, the entire
non-vacuum tail vanishes exactly. -/
theorem exactSlabVacuumTail_eqv_zero_of_nontrivial_terms_vanish
    {w : Q'} {K : Nat}
    (hvanish : ExactSlabVacuumNontrivialTermsVanish w K) :
    exactSlabVacuumTail w K ≈ 0 := by
  unfold exactSlabVacuumTail
  apply listQSum_eqv_zero_of_mem
  intro boundary hboundary
  apply hvanish boundary
  · exact (List.mem_filter.mp hboundary).1
  · intro hzero
    subst boundary
    have hwithin :
        labelWithinB 0 (centralFixedFaceIds 0) zeroEdgeLabelling =
          true := by
      apply (labelWithinB_true_iff 0
        (centralFixedFaceIds 0) zeroEdgeLabelling).2
      intro edge hedge
      simp [zeroEdgeLabelling]
    have htest := (List.mem_filter.mp hboundary).2
    simp [hwithin] at htest

/-- The same exact termwise annihilation identifies the vacuum partition
with the normalized Haar value one. -/
theorem exactSlabVacuumPartition_eqv_one_of_nontrivial_terms_vanish
    {w : Q'} {K : Nat}
    (hvanish : ExactSlabVacuumNontrivialTermsVanish w K) :
    exactSlabVacuumPartition w K ≈ 1 := by
  refine Q'.eqv_trans _
    (1 + exactSlabVacuumTail w K) _
    (exactSlabVacuumPartition_eq_one_add_tail w K) ?_
  refine Q'.eqv_trans _ (1 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left 1 _ _
      (exactSlabVacuumTail_eqv_zero_of_nontrivial_terms_vanish hvanish)
  · exact Q'.eqv_of_eq (Q'.add_zero' 1)

theorem exactSlabVacuumPartition_pos_of_nontrivial_terms_vanish
    {w : Q'} {K : Nat}
    (hvanish : ExactSlabVacuumNontrivialTermsVanish w K) :
    (0 : Q') < exactSlabVacuumPartition w K := by
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    (by decide)
    (Q'.ge_of_eqv
      (exactSlabVacuumPartition_eqv_one_of_nontrivial_terms_vanish
        hvanish))

private theorem one_add_pos_of_abs_lt_one
    {tail : Q'} (htail : Q'.abs tail < (1 : Q')) :
    (0 : Q') < 1 + tail := by
  by_cases hnonnegative : (0 : Q') ≤ tail
  · exact Q'.pos_add_nonneg (by decide) hnonnegative
  · rw [Q'.abs, if_neg hnonnegative] at htail
    show (0 : Int) * (((1 : Q') + tail).den : Int) <
      ((1 : Q') + tail).num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one, Q'.add_num_cast]
    change (0 : Int) < 1 * (tail.den : Int) + tail.num * 1
    change (-tail.num) * 1 < 1 * (tail.den : Int) at htail
    omega

/-- The sole scalar input still needed for strict vacuum positivity. -/
structure ExactSlabVacuumTailBound (w : Q') (K : Nat) : Prop where
  abs_lt_one : Q'.abs (exactSlabVacuumTail w K) < (1 : Q')

/-- At cutoff zero there are no non-vacuum interface channels, so the exact
tail vanishes. -/
theorem exactSlabVacuumTail_cutoff_zero (w : Q') :
    exactSlabVacuumTail w 0 = 0 := by
  unfold exactSlabVacuumTail centralBoundaryChannels
  rw [YMGap.Continuum.Z4FiniteGraphVacuumCompletion.boundedEdgeLabellings_zero]
  rfl

def exactSlabVacuumTailBound_cutoff_zero
    (w : Q') : ExactSlabVacuumTailBound w 0 where
  abs_lt_one := by
    rw [exactSlabVacuumTail_cutoff_zero]
    decide

/-- A strict non-vacuum tail bound proves positivity of the literal signed
vacuum partition. -/
theorem exactSlabVacuumPartition_pos_of_tail
    {w : Q'} {K : Nat} (bound : ExactSlabVacuumTailBound w K) :
    (0 : Q') < exactSlabVacuumPartition w K := by
  have hpositive := one_add_pos_of_abs_lt_one bound.abs_lt_one
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    hpositive
    (Q'.ge_of_eqv
      (exactSlabVacuumPartition_eq_one_add_tail w K))

/-- A reflected fixed-face Gram factorization will naturally prove the
non-vacuum remainder nonnegative, which is stronger and structurally cleaner
than estimating its absolute value.  This theorem is the direct consumer of
that forthcoming matrix-coefficient factorization. -/
theorem exactSlabVacuumPartition_pos_of_tail_nonnegative
    {w : Q'} {K : Nat}
    (htail : (0 : Q') ≤ exactSlabVacuumTail w K) :
    (0 : Q') < exactSlabVacuumPartition w K := by
  have hpositive : (0 : Q') <
      1 + exactSlabVacuumTail w K :=
    Q'.pos_add_nonneg (by decide) htail
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
    hpositive
    (Q'.ge_of_eqv
      (exactSlabVacuumPartition_eq_one_add_tail w K))

/-- The two genuinely nontrivial finite-slab facts needed to normalize the
literal signed network as a symmetric operator on the geometric carrier.
Both fields mention the exact Haar-network definition directly. -/
structure ExactSlabNormalizationData
    (w : Q') (K : Nat) : Type where
  vacuum_partition_pos :
    (0 : Q') < exactSlabVacuumPartition w K
  raw_symmetric :
    ∀ left right,
      left ∈ exactSlabPositiveHaarStates K →
      right ∈ exactSlabPositiveHaarStates K →
        exactSlabRawKernel w K left right ≈
          exactSlabRawKernel w K right left

/-- Construct the exact normalization data from the one remaining scalar
tail estimate.  Reflection symmetry is now an unconditional theorem of the
literal slab. -/
def ExactSlabNormalizationData.ofVacuumTailBound
    {w : Q'} {K : Nat} (bound : ExactSlabVacuumTailBound w K) :
    ExactSlabNormalizationData w K where
  vacuum_partition_pos := exactSlabVacuumPartition_pos_of_tail bound
  raw_symmetric := by
    intro left right hleft hright
    exact exactCorrectedSlabReflectedKernel_symmetric w K left right

/-- Construct exact normalization directly from the nonnegative remainder
delivered by a fixed-face Peter--Weyl Gram. -/
def ExactSlabNormalizationData.ofVacuumTailNonnegative
    {w : Q'} {K : Nat}
    (htail : (0 : Q') ≤ exactSlabVacuumTail w K) :
    ExactSlabNormalizationData w K where
  vacuum_partition_pos :=
    exactSlabVacuumPartition_pos_of_tail_nonnegative htail
  raw_symmetric := by
    intro left right hleft hright
    exact exactCorrectedSlabReflectedKernel_symmetric w K left right

/-- The strongest exact normalization constructor: exposed-link
orthogonality makes the non-vacuum tail identically zero and the vacuum
partition identically one. -/
def ExactSlabNormalizationData.ofNontrivialTermsVanish
    {w : Q'} {K : Nat}
    (hvanish : ExactSlabVacuumNontrivialTermsVanish w K) :
    ExactSlabNormalizationData w K where
  vacuum_partition_pos :=
    exactSlabVacuumPartition_pos_of_nontrivial_terms_vanish hvanish
  raw_symmetric := by
    intro left right hleft hright
    exact exactCorrectedSlabReflectedKernel_symmetric w K left right

/-- Coupling-uniform exact normalization from the one remaining unweighted
exposed-link Haar theorem. -/
def ExactSlabNormalizationData.ofHaarNontrivialTermsVanish
    {w : Q'} {K : Nat}
    (hhaar : ExactVacuumNontrivialHaarTermsVanish K) :
    ExactSlabNormalizationData w K :=
  ExactSlabNormalizationData.ofNontrivialTermsVanish
    (exactSlabVacuumNontrivialTermsVanish_of_haar hhaar w)

/-- Full exact symmetry and strict vacuum positivity reduced to the literal
single-exposed-link Haar identity on the 24-face interior carrier. -/
def ExactSlabNormalizationData.ofFixedFaceConditionalHaarOrthogonality
    {w : Q'} {K : Nat}
    (orthogonality : ExactFixedFaceConditionalHaarOrthogonality) :
    ExactSlabNormalizationData w K :=
  ExactSlabNormalizationData.ofHaarNontrivialTermsVanish
    (exactVacuumNontrivialHaarTermsVanish_of_fixedFaceOrthogonality
      orthogonality K)

/-- A fully inhabited base-cutoff normalization certificate. -/
def exactSlabNormalizationData_cutoff_zero
    (w : Q') : ExactSlabNormalizationData w 0 :=
  ExactSlabNormalizationData.ofVacuumTailBound
    (exactSlabVacuumTailBound_cutoff_zero w)

/-- The normalized literal corrected-slab matrix. -/
def normalizedExactSlabKernel
    {w : Q'} {K : Nat}
    (normalization : ExactSlabNormalizationData w K)
    (left right : EdgeLabelling) : Q' :=
  Q'.divPos
    (exactSlabRawKernel w K left right)
    (exactSlabVacuumPartition w K)
    normalization.vacuum_partition_pos

theorem normalizedExactSlabKernel_symmetric
    {w : Q'} {K : Nat}
    (normalization : ExactSlabNormalizationData w K)
    (left right : EdgeLabelling)
    (hleft : left ∈ exactSlabPositiveHaarStates K)
    (hright : right ∈ exactSlabPositiveHaarStates K) :
    normalizedExactSlabKernel normalization left right ≈
      normalizedExactSlabKernel normalization right left := by
  unfold normalizedExactSlabKernel Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (normalization.raw_symmetric left right hleft hright)

/-! ## 3. The displayed grouped Feynman--Kac/Mehler matrix -/

/-- Normalized positive grouped feature-Gram endpoint. -/
def normalizedGroupedMehlerKernel
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) : Q' :=
  Q'.divPos
    (bf4MehlerGramNumerator
      (diagonalOrder + 1) crossOrder left right)
    (bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) crossOrder)
    (bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate diagonalOrder)
      crossOrder)

theorem normalizedGroupedMehlerKernel_symmetric
    (diagonalOrder crossOrder : Nat)
    (left right : EdgeLabelling) :
    normalizedGroupedMehlerKernel
        diagonalOrder crossOrder left right ≈
      normalizedGroupedMehlerKernel
        diagonalOrder crossOrder right left := by
  unfold normalizedGroupedMehlerKernel Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (bf4MehlerGramNumerator_symmetric
      (diagonalOrder + 1) crossOrder left right)

/-- Positivity of every finite quadratic is inherited from the literal
positive feature Gram, on the new Haar-diagonal carrier as on any list. -/
theorem normalizedGroupedMehlerKernel_quadratic_nonnegative
    (K diagonalOrder crossOrder : Nat)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      finiteJointQuadratic
        (exactSlabPositiveHaarStates K)
        observable
        (normalizedGroupedMehlerKernel
          diagonalOrder crossOrder) := by
  exact normalized_bf4MehlerGram_quadratic_nonnegative
    (shiftedDiagonalVacuumCertificate diagonalOrder)
    crossOrder
    (exactSlabPositiveHaarStates K)
    observable

/-- The remaining spectral statement for the displayed grouped endpoint on
the exact geometric boundary norm. -/
structure GroupedMehlerHaarBoundarySpectralData
    (K diagonalOrder crossOrder : Nat) : Type where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  meanZero_quadratic :
    ∀ observable,
      ExactSlabBoundaryMeanZero K observable →
        Q'.abs
            (finiteJointQuadratic
              (exactSlabPositiveHaarStates K)
              observable
              (normalizedGroupedMehlerKernel
                diagonalOrder crossOrder)) ≤
          rate * exactSlabBoundaryWeightedSquare K observable

/-! ## 4. Exact row-relative comparison and additive-rate consumer -/

/-- One-scale comparison of the literal exact slab with the displayed
grouped endpoint.  The row error is relative to the strictly positive
Haar--L2 diagonal boundary scale, not to a fictitious Fourier-row marginal. -/
structure ExactSlabGroupedRowComparison
    (w : Q') (K diagonalOrder crossOrder : Nat) : Type where
  normalization : ExactSlabNormalizationData w K
  spectral :
    GroupedMehlerHaarBoundarySpectralData
      K diagonalOrder crossOrder
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  row_relative_error :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        finiteJointDifferenceAbsRowMass
            (exactSlabPositiveHaarStates K)
            (normalizedExactSlabKernel normalization)
            (normalizedGroupedMehlerKernel
              diagonalOrder crossOrder)
            source ≤
          epsilon * exactSlabBoundaryHaarDiagonalWeight source

namespace ExactSlabGroupedRowComparison

/-- The exact-slab and grouped-reference quadratics differ by at most the
row-relative tolerance in the Haar-diagonal weighted square. -/
theorem quadratic_close
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (comparison :
      ExactSlabGroupedRowComparison
        w K diagonalOrder crossOrder)
    (observable : EdgeLabelling → Q') :
    Q'.abs
        (finiteJointQuadratic
            (exactSlabPositiveHaarStates K)
            observable
            (normalizedExactSlabKernel
              comparison.normalization) +
          (-finiteJointQuadratic
            (exactSlabPositiveHaarStates K)
            observable
            (normalizedGroupedMehlerKernel
              diagonalOrder crossOrder))) ≤
      comparison.epsilon *
        exactSlabBoundaryWeightedSquare K observable := by
  exact finiteJointQuadratic_abs_sub_le_weightedSquare
    (exactSlabPositiveHaarStates K)
    observable
    exactSlabBoundaryHaarDiagonalWeight
    (normalizedExactSlabKernel comparison.normalization)
    (normalizedGroupedMehlerKernel diagonalOrder crossOrder)
    comparison.epsilon
    (normalizedExactSlabKernel_symmetric comparison.normalization)
    (fun left right _ _ =>
      normalizedGroupedMehlerKernel_symmetric
        diagonalOrder crossOrder left right)
    comparison.row_relative_error

/-- The grouped spectral rate transfers to the literal exact slab with
additive loss `rate + epsilon`. -/
theorem exact_quadratic_abs_le
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (comparison :
      ExactSlabGroupedRowComparison
        w K diagonalOrder crossOrder)
    (observable : EdgeLabelling → Q')
    (hmean : ExactSlabBoundaryMeanZero K observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates K)
          observable
          (normalizedExactSlabKernel
            comparison.normalization)) ≤
      (comparison.spectral.rate + comparison.epsilon) *
        exactSlabBoundaryWeightedSquare K observable := by
  let exactQuadratic :=
    finiteJointQuadratic
      (exactSlabPositiveHaarStates K)
      observable
      (normalizedExactSlabKernel comparison.normalization)
  let referenceQuadratic :=
    finiteJointQuadratic
      (exactSlabPositiveHaarStates K)
      observable
      (normalizedGroupedMehlerKernel diagonalOrder crossOrder)
  have hsplit :
      exactQuadratic ≈
        (exactQuadratic + (-referenceQuadratic)) +
          referenceQuadratic := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        exactQuadratic (-referenceQuadratic) referenceQuadratic) ?_)
    refine Q'.eqv_trans _ (exactQuadratic + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left exactQuadratic _ _
        (Q'.neg_add_self_eqv referenceQuadratic)
    · exact Q'.eqv_of_eq (Q'.add_zero' exactQuadratic)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (exactQuadratic + (-referenceQuadratic))
      referenceQuadratic) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (quadratic_close comparison observable)
      (comparison.spectral.meanZero_quadratic observable hmean)) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv
        (comparison.epsilon *
          exactSlabBoundaryWeightedSquare K observable)
        (comparison.spectral.rate *
          exactSlabBoundaryWeightedSquare K observable))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          comparison.spectral.rate
          comparison.epsilon
          (exactSlabBoundaryWeightedSquare K observable))))

/-- Exact rational arithmetic: two eighth budgets give the quarter budget. -/
theorem rate_add_epsilon_le_quarter
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (comparison :
      ExactSlabGroupedRowComparison
        w K diagonalOrder crossOrder)
    (hrate :
      comparison.spectral.rate ≤ Q'.mkPos 1 8 (by decide))
    (hepsilon :
      comparison.epsilon ≤ Q'.mkPos 1 8 (by decide)) :
    comparison.spectral.rate + comparison.epsilon ≤
      Q'.mkPos 1 4 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add hrate hepsilon)
    (by decide)

/-- One-scale quarter contraction for the literal signed slab matrix. -/
theorem exact_quadratic_abs_le_quarter
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (comparison :
      ExactSlabGroupedRowComparison
        w K diagonalOrder crossOrder)
    (hrate :
      comparison.spectral.rate ≤ Q'.mkPos 1 8 (by decide))
    (hepsilon :
      comparison.epsilon ≤ Q'.mkPos 1 8 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean : ExactSlabBoundaryMeanZero K observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates K)
          observable
          (normalizedExactSlabKernel
            comparison.normalization)) ≤
      Q'.mkPos 1 4 (by decide) *
        exactSlabBoundaryWeightedSquare K observable := by
  exact Q'.le_trans' _ _ _
    (exact_quadratic_abs_le comparison observable hmean)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (rate_add_epsilon_le_quarter
        comparison hrate hepsilon)
      (exactSlabBoundaryWeightedSquare_nonnegative K observable))

end ExactSlabGroupedRowComparison

/-! ## 5. Entrywise decay versus carrier growth -/

/-- A strictly smaller analytic producer for the row comparison.  It asks
for a pointwise exact-slab/Mehler entry envelope and the explicit payment of
the retained-carrier cardinality by the positive Haar diagonal.  The
row-relative `1/8` estimate is derived, not stored. -/
structure ExactSlabGroupedEntrywiseEighthData
    (w : Q') (K diagonalOrder crossOrder : Nat) : Type where
  normalization : ExactSlabNormalizationData w K
  spectral :
    GroupedMehlerHaarBoundarySpectralData
      K diagonalOrder crossOrder
  rate_le_oneEighth :
    spectral.rate ≤ Q'.mkPos 1 8 (by decide)
  entryBudget : EdgeLabelling → Q'
  entryBudget_nonnegative :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        (0 : Q') ≤ entryBudget source
  pointwise_entry_error :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
      ∀ target,
        target ∈ exactSlabPositiveHaarStates K →
          Q'.abs
              (normalizedExactSlabKernel
                  normalization source target +
                (-normalizedGroupedMehlerKernel
                  diagonalOrder crossOrder source target)) ≤
            entryBudget source
  cube_growth_payment :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        Q'.ofNat ((K + 1) ^ 24) *
            entryBudget source ≤
          Q'.mkPos 1 8 (by decide) *
            exactSlabBoundaryHaarDiagonalWeight source

namespace ExactSlabGroupedEntrywiseEighthData

/-- The pointwise envelope and cardinality payment establish the full
row-relative eighth estimate for the literal kernels. -/
theorem row_relative_error_le_oneEighth
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      ExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder) :
    ∀ source,
      source ∈ exactSlabPositiveHaarStates K →
        finiteJointDifferenceAbsRowMass
            (exactSlabPositiveHaarStates K)
            (normalizedExactSlabKernel data.normalization)
            (normalizedGroupedMehlerKernel
              diagonalOrder crossOrder)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            exactSlabBoundaryHaarDiagonalWeight source := by
  intro source hsource
  have hcarrier :
      Q'.ofNat (exactSlabPositiveHaarStates K).length *
          data.entryBudget source ≤
        Q'.ofNat ((K + 1) ^ 24) *
          data.entryBudget source := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.ofNat_le_ofNat
        (exactSlabPositiveHaarStates_length_le K))
      (data.entryBudget_nonnegative source hsource)
  exact finiteJointDifferenceAbsRowMass_le_of_entrywise_budget
    (exactSlabPositiveHaarStates K)
    (normalizedExactSlabKernel data.normalization)
    (normalizedGroupedMehlerKernel diagonalOrder crossOrder)
    data.entryBudget
    exactSlabBoundaryHaarDiagonalWeight
    (Q'.mkPos 1 8 (by decide))
    (data.entryBudget_nonnegative source hsource)
    (data.pointwise_entry_error source hsource)
    (Q'.le_trans' _ _ _ hcarrier
      (data.cube_growth_payment source hsource))

/-- Entrywise decay data produces the exact row-comparison object with
`epsilon = 1/8`. -/
def toRowComparison
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      ExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder) :
    ExactSlabGroupedRowComparison
      w K diagonalOrder crossOrder where
  normalization := data.normalization
  spectral := data.spectral
  epsilon := Q'.mkPos 1 8 (by decide)
  epsilon_nonnegative := by decide
  row_relative_error := data.row_relative_error_le_oneEighth

theorem toRowComparison_epsilon
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      ExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder) :
    data.toRowComparison.epsilon = Q'.mkPos 1 8 (by decide) :=
  rfl

/-- The pointwise decay/cardinality certificate already yields the exact
quarter quadratic bound. -/
theorem exact_quadratic_abs_le_quarter
    {w : Q'} {K diagonalOrder crossOrder : Nat}
    (data :
      ExactSlabGroupedEntrywiseEighthData
        w K diagonalOrder crossOrder)
    (observable : EdgeLabelling → Q')
    (hmean : ExactSlabBoundaryMeanZero K observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates K)
          observable
          (normalizedExactSlabKernel data.normalization)) ≤
      Q'.mkPos 1 4 (by decide) *
        exactSlabBoundaryWeightedSquare K observable := by
  exact ExactSlabGroupedRowComparison.exact_quadratic_abs_le_quarter
    data.toRowComparison
    data.rate_le_oneEighth
    (Q'.le_refl' (Q'.mkPos 1 8 (by decide)))
    observable hmean

end ExactSlabGroupedEntrywiseEighthData

/-! ## 6. AF-uniform specialization to the physical matched trajectory -/

/-- The exact-slab/grouped-Mehler comparison at every AF scale.  The
displayed weight and cutoff reduce definitionally to the matched BF4 block
output and its same-action spacing cutoff. -/
structure ExactSlabGroupedAFQuarterCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  comparison :
    ∀ scale,
      ExactSlabGroupedRowComparison
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (diagonalOrder scale)
        (crossOrder scale)
  rate_le_oneEighth :
    ∀ scale,
      (comparison scale).spectral.rate ≤
        Q'.mkPos 1 8 (by decide)
  epsilon_le_oneEighth :
    ∀ scale,
      (comparison scale).epsilon ≤
        Q'.mkPos 1 8 (by decide)

namespace ExactSlabGroupedAFQuarterCertificate

/-- The requested spacing-uniform scalar budget
`r(a) + epsilon(a) <= 1/4`. -/
theorem rate_add_epsilon_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactSlabGroupedAFQuarterCertificate
        family law spacing coupling) :
    ∀ scale,
      (certificate.comparison scale).spectral.rate +
          (certificate.comparison scale).epsilon ≤
        Q'.mkPos 1 4 (by decide) := by
  intro scale
  exact ExactSlabGroupedRowComparison.rate_add_epsilon_le_quarter
    (certificate.comparison scale)
    (certificate.rate_le_oneEighth scale)
    (certificate.epsilon_le_oneEighth scale)

/-- Uniform quarter contraction on every finite matched-AF carrier. -/
theorem exact_quadratic_abs_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactSlabGroupedAFQuarterCertificate
        family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      ExactSlabBoundaryMeanZero
        (matchedAllSpinCutoff family coupling scale)
        observable) :
    Q'.abs
        (finiteJointQuadratic
          (exactSlabPositiveHaarStates
            (matchedAllSpinCutoff family coupling scale))
          observable
          (normalizedExactSlabKernel
            (certificate.comparison scale).normalization)) ≤
      Q'.mkPos 1 4 (by decide) *
        exactSlabBoundaryWeightedSquare
          (matchedAllSpinCutoff family coupling scale)
          observable := by
  exact ExactSlabGroupedRowComparison.exact_quadratic_abs_le_quarter
    (certificate.comparison scale)
    (certificate.rate_le_oneEighth scale)
    (certificate.epsilon_le_oneEighth scale)
    observable hmean

end ExactSlabGroupedAFQuarterCertificate

/-- AF-uniform producer phrased at the genuinely analytic pointwise layer.
The exact row-relative `epsilon(a) <= 1/8` conclusion is generated by the
finite carrier-growth theorem above. -/
structure ExactSlabGroupedAFEntrywiseEighthCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  entrywise :
    ∀ scale,
      ExactSlabGroupedEntrywiseEighthData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (diagonalOrder scale)
        (crossOrder scale)

namespace ExactSlabGroupedAFEntrywiseEighthCertificate

def toAFQuarterCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) :
    ExactSlabGroupedAFQuarterCertificate
      family law spacing coupling where
  coupling_pos := certificate.coupling_pos
  coupling_le_window := certificate.coupling_le_window
  diagonalOrder := certificate.diagonalOrder
  crossOrder := certificate.crossOrder
  comparison := fun scale =>
    (certificate.entrywise scale).toRowComparison
  rate_le_oneEighth := fun scale =>
    (certificate.entrywise scale).rate_le_oneEighth
  epsilon_le_oneEighth := fun _ =>
    Q'.le_refl' (Q'.mkPos 1 8 (by decide))

/-- AF-uniform exact `r(a) + epsilon(a) <= 1/4`, now with the epsilon side
derived from pointwise entry decay and carrier growth. -/
theorem rate_add_epsilon_le_quarter
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      ExactSlabGroupedAFEntrywiseEighthCertificate
        family law spacing coupling) :
    ∀ scale,
      ((certificate.toAFQuarterCertificate.comparison scale).spectral.rate +
          (certificate.toAFQuarterCertificate.comparison scale).epsilon) ≤
        Q'.mkPos 1 4 (by decide) :=
  certificate.toAFQuarterCertificate.rate_add_epsilon_le_quarter

end ExactSlabGroupedAFEntrywiseEighthCertificate

end YMGap.Continuum.BF4ExactSlabGroupedAFComparison

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabBoundaryHaarDiagonalWeight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabBoundaryHaarDiagonalWeight_vacuum_pos
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.zeroEdgeLabelling_mem_exactSlabPositiveHaarStates
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.centralHalfStates_zero_length
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabPositiveHaarStates_length_le
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabBoundaryWeightedSquare_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumPartition_eq_one_add_tail
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumNontrivialTermsVanish_of_haar
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumTail_eqv_zero_of_nontrivial_terms_vanish
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumPartition_eqv_one_of_nontrivial_terms_vanish
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumPartition_pos_of_nontrivial_terms_vanish
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumPartition_pos_of_tail
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumPartition_pos_of_tail_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabVacuumTailBound_cutoff_zero
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabNormalizationData.ofVacuumTailBound
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabNormalizationData.ofNontrivialTermsVanish
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabNormalizationData.ofHaarNontrivialTermsVanish
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabNormalizationData.ofFixedFaceConditionalHaarOrthogonality
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.exactSlabNormalizationData_cutoff_zero
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.normalizedExactSlabKernel_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.normalizedGroupedMehlerKernel_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.normalizedGroupedMehlerKernel_quadratic_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedRowComparison.quadratic_close
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedRowComparison.exact_quadratic_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedRowComparison.exact_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedEntrywiseEighthData.row_relative_error_le_oneEighth
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedEntrywiseEighthData.toRowComparison
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedEntrywiseEighthData.exact_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedAFQuarterCertificate.rate_add_epsilon_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedAFQuarterCertificate.exact_quadratic_abs_le_quarter
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedAFEntrywiseEighthCertificate.toAFQuarterCertificate
#print axioms YMGap.Continuum.BF4ExactSlabGroupedAFComparison.ExactSlabGroupedAFEntrywiseEighthCertificate.rate_add_epsilon_le_quarter
