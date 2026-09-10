/-
# Minimum-occupation heat payment in the accepted response residue

The cubic response estimate records only that the switched left and right
rows are nonempty.  For aggregation that is too lossy: every occupied face
common to the two rows must continue to pay its heat weight.

This module packages the two orientations of the exact occupation-skew
formula into one signed residual.  The full cofactor is exactly

  w^(3 * min(leftOccupation,rightOccupation)) * residual,

and the residual has the same geometric-series ceiling as before.  The
accepted response-defect summand therefore retains the heat payment of the
smaller switched row.  No sum over sources or volume-uniform contraction is
claimed here.

Constructive contract: decidable natural-number comparison and rational
setoid algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseMinHeat

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.LargeFieldSuppression
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseCubic
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginBinaryHybrid
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginLocalInsertion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact minimum-occupation factor -/

/-- The signed geometric residual left after removing the heat power of the
smaller occupation count. -/
def fineCouplingPhysicalOccupationSkewMinResidual
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) : Q' :=
  if fineCouplingPhysicalOccupiedFaceCount S pair.2 ≤
      fineCouplingPhysicalOccupiedFaceCount S pair.1 then
    geomSum S.fine.coupling
      (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 -
        fineCouplingPhysicalOccupiedFaceCount S pair.2))
  else
    -(geomSum S.fine.coupling
      (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
        fineCouplingPhysicalOccupiedFaceCount S pair.1)))

/-- The complete occupation skew pays the exact heat power of the smaller
row.  This combines the two oriented formulas without weakening either. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_eqv_minHeat
    (S : SlabScalePair) (pair : FineCouplingPhysicalSourcePair) :
    fineCouplingPhysicalOccupationSkewCoefficient S pair ≈
      qpow S.fine.coupling
          (3 * Nat.min
            (fineCouplingPhysicalOccupiedFaceCount S pair.1)
            (fineCouplingPhysicalOccupiedFaceCount S pair.2)) *
        fineCouplingPhysicalOccupationSkewMinResidual S pair := by
  by_cases hright : fineCouplingPhysicalOccupiedFaceCount S pair.2 ≤
      fineCouplingPhysicalOccupiedFaceCount S pair.1
  · simp only [Nat.min_eq_right hright,
      fineCouplingPhysicalOccupationSkewMinResidual, hright, if_true]
    exact fineCouplingPhysicalOccupationSkewCoefficient_eqv_of_right_le_left
      S pair hright
  · have hleft : fineCouplingPhysicalOccupiedFaceCount S pair.1 ≤
        fineCouplingPhysicalOccupiedFaceCount S pair.2 := by omega
    simp only [Nat.min_eq_left hleft,
      fineCouplingPhysicalOccupationSkewMinResidual, hright, if_false]
    refine Q'.eqv_trans _
      (-(qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S pair.1) *
        geomSum S.fine.coupling
          (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
            fineCouplingPhysicalOccupiedFaceCount S pair.1)))) _ ?_ ?_
    · exact
        fineCouplingPhysicalOccupationSkewCoefficient_eqv_neg_of_left_le_right
          S pair hleft
    · exact Q'.eqv_symm
        (Q'.mul_neg_eqv
          (qpow S.fine.coupling
            (3 * fineCouplingPhysicalOccupiedFaceCount S pair.1))
          (geomSum S.fine.coupling
            (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
              fineCouplingPhysicalOccupiedFaceCount S pair.1))))

/-! ## 2. Uniform ceiling only after retaining the minimum heat power -/

/-- The signed minimum-occupation residual is only a finite geometric sum,
up to orientation, so its absolute value is bounded by `1/(1-w)`. -/
theorem fineCouplingPhysicalOccupationSkewMinResidual_abs_le_recip
    (S : SlabScalePair) (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (pair : FineCouplingPhysicalSourcePair) :
    Q'.abs (fineCouplingPhysicalOccupationSkewMinResidual S pair) ≤
      Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap := by
  by_cases hright : fineCouplingPhysicalOccupiedFaceCount S pair.2 ≤
      fineCouplingPhysicalOccupiedFaceCount S pair.1
  · simp only [fineCouplingPhysicalOccupationSkewMinResidual,
      hright, if_true]
    rw [ExpNeg.abs_of_nonneg
      (geomSum_nonneg hw0
        (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.1 -
          fineCouplingPhysicalOccupiedFaceCount S pair.2)))]
    exact geomSum_le_recip hw0 hgap _
  · simp only [fineCouplingPhysicalOccupationSkewMinResidual,
      hright, if_false]
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_neg'
          (geomSum S.fine.coupling
            (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
              fineCouplingPhysicalOccupiedFaceCount S pair.1))))) ?_
    rw [ExpNeg.abs_of_nonneg
      (geomSum_nonneg hw0
        (3 * (fineCouplingPhysicalOccupiedFaceCount S pair.2 -
          fineCouplingPhysicalOccupiedFaceCount S pair.1)))]
    exact geomSum_le_recip hw0 hgap _

/-- The occupation cofactor is bounded by the heat weight of the smaller
row times one geometric ceiling. -/
theorem fineCouplingPhysicalOccupationSkewCoefficient_abs_le_minHeat_recip
    (S : SlabScalePair) (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (pair : FineCouplingPhysicalSourcePair) :
    Q'.abs (fineCouplingPhysicalOccupationSkewCoefficient S pair) ≤
      qpow S.fine.coupling
          (3 * Nat.min
            (fineCouplingPhysicalOccupiedFaceCount S pair.1)
            (fineCouplingPhysicalOccupiedFaceCount S pair.2)) *
        Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap := by
  let power := qpow S.fine.coupling
    (3 * Nat.min
      (fineCouplingPhysicalOccupiedFaceCount S pair.1)
      (fineCouplingPhysicalOccupiedFaceCount S pair.2))
  let residual := fineCouplingPhysicalOccupationSkewMinResidual S pair
  have heqv := fineCouplingPhysicalOccupationSkewCoefficient_eqv_minHeat
    S pair
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr heqv)) ?_
  have hmul := ExpNeg.abs_mul_le power residual
  rw [ExpNeg.abs_of_nonneg
    (qpow_nonneg S.fine.coupling hw0
      (3 * Nat.min
        (fineCouplingPhysicalOccupiedFaceCount S pair.1)
        (fineCouplingPhysicalOccupiedFaceCount S pair.2)))] at hmul
  exact Q'.le_trans' _ _ _ hmul
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (fineCouplingPhysicalOccupationSkewMinResidual_abs_le_recip
        S hw0 hgap pair)
      (qpow_nonneg S.fine.coupling hw0 _))

/-! ## 3. The complete accepted response summand -/

/-- The response summand after removing the exact minimum-occupation heat
power from its cofactor. -/
def fineCouplingAcceptedSeparatedResponseMinHeatResidualTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) : Q' :=
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  fineCouplingPhysicalOccupationSkewMinResidual S swapped *
    (fineUnitCouplingExpandedFiberPairWeight S swapped targetAssignments *
      fineCouplingPhysicalSupportSwapResponseDefect
        K event targetFaceId pair)

/-- The full response-defect summand has an exact minimum-row heat factor. -/
theorem fineCouplingAcceptedSeparated_responseDefectTerm_eqv_minHeat
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    fineCouplingPhysicalOccupationSkewCoefficient S swapped *
        (fineUnitCouplingExpandedFiberPairWeight S swapped targetAssignments *
          fineCouplingPhysicalSupportSwapResponseDefect
          K event targetFaceId pair) ≈
      qpow S.fine.coupling
          (3 * Nat.min
            (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
            (fineCouplingPhysicalOccupiedFaceCount S swapped.2)) *
        fineCouplingAcceptedSeparatedResponseMinHeatResidualTerm
          K event rootFaceId targetFaceId source targetAssignments := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair S targetFaceId pair
  let power := qpow S.fine.coupling
    (3 * Nat.min
      (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
      (fineCouplingPhysicalOccupiedFaceCount S swapped.2))
  let residual := fineCouplingPhysicalOccupationSkewMinResidual S swapped
  let rest := fineUnitCouplingExpandedFiberPairWeight
      S swapped targetAssignments *
    fineCouplingPhysicalSupportSwapResponseDefect
      K event targetFaceId pair
  change fineCouplingPhysicalOccupationSkewCoefficient S swapped * rest ≈
    power * (residual * rest)
  refine Q'.eqv_trans _ ((power * residual) * rest) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (fineCouplingPhysicalOccupationSkewCoefficient_eqv_minHeat S _)
  · exact Q'.mul_assoc_eqv _ _ _

/-- Pointwise, the complete accepted response term is bounded by the
minimum-row heat payment times the unit-coupling assignment weight and the
universal response constant two. -/
theorem fineCouplingAcceptedSeparated_responseDefectTerm_abs_le_minHeat_recip
    {S : SlabScalePair} (hw0 : (0 : Q') ≤ S.fine.coupling)
    (hgap : (0 : Q') < (1 : Q') - S.fine.coupling)
    (K : S.FiniteSlabKernel) (event : EdgeLabelling → Bool)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetAssignments :
      SlabFusionWitnessAssignment × SlabFusionWitnessAssignment) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    Q'.abs
      (fineCouplingPhysicalOccupationSkewCoefficient S swapped *
        (fineUnitCouplingExpandedFiberPairWeight S swapped targetAssignments *
          fineCouplingPhysicalSupportSwapResponseDefect
            K event targetFaceId pair)) ≤
      (qpow S.fine.coupling
          (3 * Nat.min
            (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
            (fineCouplingPhysicalOccupiedFaceCount S swapped.2)) *
        Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap) *
        (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments * (2 : Q')) := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair S targetFaceId pair
  let coefficient := fineCouplingPhysicalOccupationSkewCoefficient S swapped
  let weight := fineUnitCouplingExpandedFiberPairWeight
    S swapped targetAssignments
  let defect := fineCouplingPhysicalSupportSwapResponseDefect
    K event targetFaceId pair
  let ceiling := qpow S.fine.coupling
      (3 * Nat.min
        (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
        (fineCouplingPhysicalOccupiedFaceCount S swapped.2)) *
    Q'.divPos 1 ((1 : Q') - S.fine.coupling) hgap
  have hcoefficient : Q'.abs coefficient ≤ ceiling := by
    exact fineCouplingPhysicalOccupationSkewCoefficient_abs_le_minHeat_recip
      S hw0 hgap swapped
  have hweight : (0 : Q') ≤ weight :=
    fineUnitCouplingExpandedFiberPairWeight_nonnegative
      S swapped targetAssignments
  have hdefect : Q'.abs defect ≤ (2 : Q') :=
    fineCouplingAcceptedSeparated_responseDefect_abs_le_two
      K event rootFaceId targetFaceId source
  have hinner : Q'.abs (weight * defect) ≤ weight * (2 : Q') := by
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le weight defect) ?_
    rw [ExpNeg.abs_of_nonneg hweight]
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hdefect hweight
  have hceiling : (0 : Q') ≤ ceiling := by
    exact Q'.mul_nonneg _ _
      (qpow_nonneg S.fine.coupling hw0 _)
      (Q'.le_of_lt
        (Q'.divPos_pos 1 ((1 : Q') - S.fine.coupling)
          hgap (by decide)))
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le coefficient (weight * defect)) ?_
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoefficient
      (Q'.abs_nonneg (weight * defect)))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hceiling)

/-! ## 4. Recompile the accepted support-swap cocycle -/

/-- **Minimum-heat accepted response decomposition.**  The exact support-swap
cocycle retains the full heat exponent of the smaller switched row in its
analytic response residue. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition_minHeat
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingPhysicalSupportSwappedPair
      S targetFaceId pair
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        K event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          K event swapped targetAssignments +
        (((qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.1) +
            qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.2)) *
          fineCouplingPhysicalComponentOccupationSkewCoefficient
            S targetFaceId pair) *
          (fineUnitCouplingExpandedFiberPairWeight
              S pair sourceAssignments *
            fineCouplingPhysicalPairEventResponseDifference
              K event pair) +
          qpow S.fine.coupling
              (3 * Nat.min
                (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
                (fineCouplingPhysicalOccupiedFaceCount S swapped.2)) *
            fineCouplingAcceptedSeparatedResponseMinHeatResidualTerm
              K event rootFaceId targetFaceId source
                targetAssignments) := by
  dsimp only
  let pair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let swapped := fineCouplingPhysicalSupportSwappedPair
    S targetFaceId pair
  let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
    S rootFaceId targetFaceId source
  let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
    S rootFaceId targetFaceId htarget source choice
  let switchedTerm := fineCouplingExpandedOccupationResponseTerm
    K event swapped targetAssignments
  let componentTerm :=
    ((qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.1) +
        qpow S.fine.coupling
          (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
            S targetFaceId pair pair.2)) *
      fineCouplingPhysicalComponentOccupationSkewCoefficient
        S targetFaceId pair) *
      (fineUnitCouplingExpandedFiberPairWeight
          S pair sourceAssignments *
        fineCouplingPhysicalPairEventResponseDifference K event pair)
  let responseTerm :=
    fineCouplingPhysicalOccupationSkewCoefficient S swapped *
      (fineUnitCouplingExpandedFiberPairWeight
          S swapped targetAssignments *
        fineCouplingPhysicalSupportSwapResponseDefect
          K event targetFaceId pair)
  let minHeatTerm :=
    qpow S.fine.coupling
        (3 * Nat.min
          (fineCouplingPhysicalOccupiedFaceCount S swapped.1)
          (fineCouplingPhysicalOccupiedFaceCount S swapped.2)) *
      fineCouplingAcceptedSeparatedResponseMinHeatResidualTerm
        K event rootFaceId targetFaceId source targetAssignments
  have hdecomposition :
      fineCouplingExpandedOccupationResponseTerm
          K event pair sourceAssignments ≈
        switchedTerm + (componentTerm + responseTerm) := by
    exact fineCouplingExpandedOccupationResponseTerm_supportSwap_decomposition
      K event targetFaceId pair sourceAssignments targetAssignments
  have hminHeat : responseTerm ≈ minHeatTerm := by
    exact fineCouplingAcceptedSeparated_responseDefectTerm_eqv_minHeat
      K event rootFaceId targetFaceId source targetAssignments
  exact Q'.eqv_trans _ _ _ hdecomposition
    (Q'.add_eqv_congr_left switchedTerm _ _
      (Q'.add_eqv_congr_left componentTerm _ _ hminHeat))

#print axioms fineCouplingPhysicalOccupationSkewCoefficient_eqv_minHeat
#print axioms fineCouplingPhysicalOccupationSkewMinResidual_abs_le_recip
#print axioms fineCouplingPhysicalOccupationSkewCoefficient_abs_le_minHeat_recip
#print axioms fineCouplingAcceptedSeparated_responseDefectTerm_eqv_minHeat
#print axioms fineCouplingAcceptedSeparated_responseDefectTerm_abs_le_minHeat_recip
#print axioms fineCouplingAcceptedSeparatedOccupationResponse_decomposition_minHeat

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponseMinHeat
