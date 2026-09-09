/-
# Fully raw three-event form of each connected Gibbs row

The preceding source-resolved row cross is a signed combination of the
joint, root, and target cylinder crosses, but its root and target
coefficients are still normalized moments.  This module clears those final
fine and coarse partition factors without taking an absolute value.

The resulting numerator is an explicit polynomial in literal row event
masses, coarse physical event numerators, the pushed target event numerator,
and the fine/coarse physical partitions.  The selected positive-source row
action is exactly this numerator divided by one positive denominator.

No smallness estimate is asserted.  The final relative bound is an explicit
analytic input whose proof is the next frontier.

Constructive contract: exact rational algebra and already proved positive
partition witnesses only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawEventCross

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawCross
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawEventCross
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem distributeThree_mul_local
    (first second third factor : Q') :
    (first + (second + third)) * factor ≈
      first * factor + (second * factor + third * factor) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv first (second + third) factor)
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_mul_eqv second third factor))

private theorem divTerm_mul_product_eqv_local
    (numerator denominator value other : Q')
    (hdenominator : (0 : Q') < denominator) :
    (Q'.divPos numerator denominator hdenominator * value) *
        (denominator * other) ≈
      (numerator * value) * other := by
  let quotient := Q'.divPos numerator denominator hdenominator
  have hinter :
      value * (denominator * other) ≈
        denominator * (value * other) := by
    refine Q'.eqv_trans _ ((value * denominator) * other) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv value denominator other)
    refine Q'.eqv_trans _ ((denominator * value) * other) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ other
        (Q'.mul_comm_eqv value denominator)
    exact Q'.mul_assoc_eqv denominator value other
  refine Q'.eqv_trans _
    (quotient * (value * (denominator * other))) _ ?_ ?_
  · exact Q'.mul_assoc_eqv quotient value (denominator * other)
  refine Q'.eqv_trans _
    (quotient * (denominator * (value * other))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left quotient _ _ hinter
  refine Q'.eqv_trans _
    ((quotient * denominator) * (value * other)) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv quotient denominator (value * other))
  refine Q'.eqv_trans _ (numerator * (value * other)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (value * other)
      (Q'.divPos_mul_eqv numerator denominator hdenominator)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv numerator value other)

private theorem divTerm_mul_swapped_product_eqv_local
    (numerator denominator value other : Q')
    (hdenominator : (0 : Q') < denominator) :
    (Q'.divPos numerator denominator hdenominator * value) *
        (other * denominator) ≈
      (numerator * value) * other := by
  refine Q'.eqv_trans _
    ((Q'.divPos numerator denominator hdenominator * value) *
      (denominator * other)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv other denominator)
  exact divTerm_mul_product_eqv_local
    numerator denominator value other hdenominator

private theorem divPos_eqv_of_eqv_mul_local
    {numerator denominator value : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : numerator ≈ value * denominator) :
    Q'.divPos numerator denominator hdenominator ≈ value := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnumerator) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv value denominator
      (Q'.recipPos denominator hdenominator)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left value _ _
      (Q'.mul_recipPos_eqv denominator hdenominator)) ?_
  exact Q'.mul_one_eqv value

private theorem eqv_divPos_of_mul_local
    {value numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : value * denominator ≈ numerator) :
    value ≈ Q'.divPos numerator denominator hdenominator := by
  exact Q'.eqv_symm
    (divPos_eqv_of_eqv_mul_local hdenominator (Q'.eqv_symm hmul))

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross :
        -(budget * denominator) ≤ -(Q'.abs numerator) :=
      Q'.neg_le_neg hcross
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hcross

/-! ## 1. Clear the two remaining normalized moment coefficients -/

/-- The final fine/coarse partition scale hidden in the two moment
coefficients of the three-event row cross. -/
def connectedRawEventMomentScale (S : SlabScalePair) : Q' :=
  S.fine.physicalPartition * S.coarse.physicalPartition

theorem connectedRawEventMomentScale_pos (S : SlabScalePair) :
    (0 : Q') < connectedRawEventMomentScale S := by
  unfold connectedRawEventMomentScale
  exact Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)

/-- Explicit fully raw numerator.  Every input is an unnormalized event
numerator, a row event mass, or a physical partition. -/
def wholeSlabRecouplingConnectedFullyRawEventCrossNumerator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) : Q' :=
  let jointCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
  let rootCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePositiveB M.coarseRoot)
  let targetCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePositiveB M.coarseTarget)
  (-(jointCross * connectedRawEventMomentScale S) +
    ((pushedPhysicalEventNumerator K
          (slabPhysicalFacePositiveB M.coarseTarget) * rootCross) *
        S.coarse.physicalPartition +
      (physicalEventNumerator S.coarse
          (slabPhysicalFacePositiveB M.coarseRoot) * targetCross) *
        S.fine.physicalPartition))

theorem wholeSlabRecouplingConnectedRawEventCross_mul_scale_eqv_fullyRaw
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (K : S.FiniteSlabKernel) (M : SlabFaceBlockMap S) :
    wholeSlabRecouplingConnectedRawEventCrossNumerator source K M *
        connectedRawEventMomentScale S ≈
      wholeSlabRecouplingConnectedFullyRawEventCrossNumerator source K M := by
  let jointCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
  let rootCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePositiveB M.coarseRoot)
  let targetCross := wholeSlabRecouplingRawCylinderCrossNumerator source
    (slabPhysicalFacePositiveB M.coarseTarget)
  let blockedRaw := pushedPhysicalEventNumerator K
    (slabPhysicalFacePositiveB M.coarseTarget)
  let coarseRaw := physicalEventNumerator S.coarse
    (slabPhysicalFacePositiveB M.coarseRoot)
  let finePartition := S.fine.physicalPartition
  let coarsePartition := S.coarse.physicalPartition
  let hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  have hblocked :
      blockedFaceMoment K M.coarseTarget ≈
        Q'.divPos blockedRaw finePartition hfine := by
    unfold blockedFaceMoment blockedRaw finePartition hfine
    exact blockedEventMass_eqv_pushedRaw_divPos K
      (slabPhysicalFacePositiveB M.coarseTarget)
  have hcoarseMoment :
      coarseFaceMoment K M.coarseRoot ≈
        Q'.divPos coarseRaw coarsePartition hcoarse := by
    unfold coarseFaceMoment PhysicalKernel.coarseCylinderMass coarseRaw
      coarsePartition hcoarse
    simpa only [normalizedSlabEventMass] using
      (normalizedEventMass_eqv_raw_divPos S.coarse
        (slabPhysicalFacePositiveB M.coarseRoot))
  have hevents :
      wholeSlabRecouplingConnectedRawEventCrossNumerator source K M ≈
        -jointCross +
          (Q'.divPos blockedRaw finePartition hfine * rootCross +
            Q'.divPos coarseRaw coarsePartition hcoarse * targetCross) := by
    unfold wholeSlabRecouplingConnectedRawEventCrossNumerator
    simpa only [jointCross, rootCross, targetCross, blockedRaw, coarseRaw,
        finePartition, coarsePartition, hfine, hcoarse] using
      (Q'.add_eqv_congr'
        (Q'.eqv_refl (-jointCross))
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ rootCross hblocked)
          (Q'.mul_eqv_congr_right _ _ targetCross hcoarseMoment)))
  refine Q'.eqv_trans _
    ((-jointCross +
        (Q'.divPos blockedRaw finePartition hfine * rootCross +
          Q'.divPos coarseRaw coarsePartition hcoarse * targetCross)) *
      (finePartition * coarsePartition)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hevents
  refine Q'.eqv_trans _
    ((-jointCross) * (finePartition * coarsePartition) +
      ((Q'.divPos blockedRaw finePartition hfine * rootCross) *
          (finePartition * coarsePartition) +
        (Q'.divPos coarseRaw coarsePartition hcoarse * targetCross) *
          (finePartition * coarsePartition))) _ ?_ ?_
  · exact distributeThree_mul_local
      (-jointCross)
      (Q'.divPos blockedRaw finePartition hfine * rootCross)
      (Q'.divPos coarseRaw coarsePartition hcoarse * targetCross)
      (finePartition * coarsePartition)
  unfold wholeSlabRecouplingConnectedFullyRawEventCrossNumerator
    connectedRawEventMomentScale
  simpa only [jointCross, rootCross, targetCross, blockedRaw, coarseRaw,
      finePartition, coarsePartition, hfine, hcoarse] using
    (Q'.add_eqv_congr'
      (Q'.neg_mul_eqv jointCross (finePartition * coarsePartition))
      (Q'.add_eqv_congr'
        (divTerm_mul_product_eqv_local blockedRaw finePartition
          rootCross coarsePartition hfine)
        (divTerm_mul_swapped_product_eqv_local coarseRaw coarsePartition
          targetCross finePartition hcoarse)))

/-! ## 2. Positive physical row and one fully raw denominator -/

def positivePhysicalConnectedFullyRawEventCrossNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) : Q' :=
  wholeSlabRecouplingConnectedFullyRawEventCrossNumerator
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)
    (physicalKernel S hfineCutoff hcoarseCoupling) M

def positivePhysicalConnectedFullyRawEventCrossDenominator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source) : Q' :=
  positivePhysicalConnectedRawCrossDenominator
      S hfineCutoff hcoarseCoupling source hsource hpositive *
    connectedRawEventMomentScale S

theorem positivePhysicalConnectedFullyRawEventCrossDenominator_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source) :
    (0 : Q') <
      positivePhysicalConnectedFullyRawEventCrossDenominator
        S hfineCutoff hcoarseCoupling source hsource hpositive := by
  unfold positivePhysicalConnectedFullyRawEventCrossDenominator
  exact Q'.mul_pos
    (positivePhysicalConnectedRawCrossDenominator_pos
      S hfineCutoff hcoarseCoupling source hsource hpositive)
    (connectedRawEventMomentScale_pos S)

theorem positivePhysicalConnectedRawRowAction_eqv_fullyRawEventCross_divPos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawRowAction
        S hfineCutoff hcoarseCoupling source hsource hpositive M ≈
      Q'.divPos
        (positivePhysicalConnectedFullyRawEventCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M)
        (positivePhysicalConnectedFullyRawEventCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive)
        (positivePhysicalConnectedFullyRawEventCrossDenominator_pos
          S hfineCutoff hcoarseCoupling source hsource hpositive) := by
  let numerator := positivePhysicalConnectedRawEventCrossNumerator
    S hfineCutoff hcoarseCoupling source hsource hpositive M
  let denominator := positivePhysicalConnectedRawCrossDenominator
    S hfineCutoff hcoarseCoupling source hsource hpositive
  let scale := connectedRawEventMomentScale S
  let fullyRaw := positivePhysicalConnectedFullyRawEventCrossNumerator
    S hfineCutoff hcoarseCoupling source hsource hpositive M
  let hdenominator := positivePhysicalConnectedRawCrossDenominator_pos
    S hfineCutoff hcoarseCoupling source hsource hpositive
  let hscale := connectedRawEventMomentScale_pos S
  let hfully := positivePhysicalConnectedFullyRawEventCrossDenominator_pos
    S hfineCutoff hcoarseCoupling source hsource hpositive
  have hscaled : numerator * scale ≈ fullyRaw := by
    unfold numerator scale fullyRaw
      positivePhysicalConnectedRawEventCrossNumerator
      positivePhysicalConnectedFullyRawEventCrossNumerator
    exact wholeSlabRecouplingConnectedRawEventCross_mul_scale_eqv_fullyRaw
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source hsource hpositive)
      (physicalKernel S hfineCutoff hcoarseCoupling) M
  have hmul :
      Q'.divPos numerator denominator hdenominator *
          (denominator * scale) ≈ fullyRaw := by
    refine Q'.eqv_trans _
      ((Q'.divPos numerator denominator hdenominator * denominator) *
        scale) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.divPos numerator denominator hdenominator)
          denominator scale)
    exact Q'.eqv_trans _ (numerator * scale) _
      (Q'.mul_eqv_congr_right _ _ scale
        (Q'.divPos_mul_eqv numerator denominator hdenominator))
      hscaled
  refine Q'.eqv_trans _
    (Q'.divPos numerator denominator hdenominator) _ ?_ ?_
  · simpa only [numerator, denominator, hdenominator] using
      (positivePhysicalConnectedRawRowAction_eqv_threeEventCross_divPos
        S hfineCutoff hcoarseCoupling source hsource hpositive M)
  simpa only [numerator, denominator, scale, fullyRaw, hfully,
      positivePhysicalConnectedFullyRawEventCrossDenominator] using
    (eqv_divPos_of_mul_local hfully hmul)

/-! ## 3. Division-free relative calibration and normalized consumer -/

def PositivePhysicalConnectedFullyRawEventCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  ∀ source (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source),
    Q'.abs
        (positivePhysicalConnectedFullyRawEventCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M) ≤
      (kernelCeiling * (g * g)) *
        positivePhysicalConnectedFullyRawEventCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive

theorem positivePhysicalConnectedRawPointwiseCalibration_of_fullyRawEventCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcross : PositivePhysicalConnectedFullyRawEventCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    PositivePhysicalConnectedRawPointwiseCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold PositivePhysicalConnectedRawPointwiseCalibration
  intro source hsource hpositive
  let numerator := positivePhysicalConnectedFullyRawEventCrossNumerator
    S hfineCutoff hcoarseCoupling source hsource hpositive M
  let denominator := positivePhysicalConnectedFullyRawEventCrossDenominator
    S hfineCutoff hcoarseCoupling source hsource hpositive
  let hdenominator :=
    positivePhysicalConnectedFullyRawEventCrossDenominator_pos
      S hfineCutoff hcoarseCoupling source hsource hpositive
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positivePhysicalConnectedRawRowAction_eqv_fullyRawEventCross_divPos
          S hfineCutoff hcoarseCoupling source hsource hpositive M))) ?_
  exact abs_divPos_le_of_abs_le_mul_local hdenominator
    (by
      unfold PositivePhysicalConnectedFullyRawEventCrossCalibration at hcross
      simpa only [numerator, denominator] using
        hcross source hsource hpositive)

theorem coarseGibbsRefreshConnectedRemainderCalibration_of_fullyRawEventCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcross : PositivePhysicalConnectedFullyRawEventCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawPointwise
    S hfineCutoff hcoarseCoupling M g kernelCeiling
    (positivePhysicalConnectedRawPointwiseCalibration_of_fullyRawEventCross
      S hfineCutoff hcoarseCoupling M g kernelCeiling hcross)

#print axioms connectedRawEventMomentScale
#print axioms connectedRawEventMomentScale_pos
#print axioms wholeSlabRecouplingConnectedFullyRawEventCrossNumerator
#print axioms wholeSlabRecouplingConnectedRawEventCross_mul_scale_eqv_fullyRaw
#print axioms positivePhysicalConnectedFullyRawEventCrossNumerator
#print axioms positivePhysicalConnectedFullyRawEventCrossDenominator
#print axioms positivePhysicalConnectedFullyRawEventCrossDenominator_pos
#print axioms positivePhysicalConnectedRawRowAction_eqv_fullyRawEventCross_divPos
#print axioms PositivePhysicalConnectedFullyRawEventCrossCalibration
#print axioms positivePhysicalConnectedRawPointwiseCalibration_of_fullyRawEventCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_fullyRawEventCross

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCross
