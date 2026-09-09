/-
# Common-denominator raw cross for each connected Gibbs row

The positive-source connected row from the preceding milestone is a
difference of two normalized expectations.  This module clears those two
normalizations without splitting their signed cancellation.  For an
arbitrary observable, the conditional recoupling numerator and the coarse
physical numerator are placed over the positive product of the complete row
partition and the coarse physical partition.

Specializing to the connected observable gives a literal source-resolved
raw cross numerator.  A pointwise bound on its absolute value relative to
its exact positive denominator compiles, with no coefficient loss, through
the positive-row and centered-remainder calibration hierarchy.

This is an algebraic reduction, not an `O(g^2)` estimate.  The observable's
moment coefficients are deliberately retained, so a later expansion may
clear their fine/coarse partition factors while preserving the three-event
joint/root/target cancellation.

Constructive contract: finite rational sums and explicit positive rational
division only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic row-versus-coarse raw cross -/

/-- Signed cross numerator between one positive conditional recoupling row
and the normalized coarse physical expectation of the same observable. -/
def wholeSlabRecouplingRawObservableCrossNumerator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (observable : EdgeLabelling → Q') : Q' :=
  wholeSlabRecouplingRawObservableNumerator source observable *
      S.coarse.physicalPartition +
    -(physicalObservableNumerator S.coarse observable *
      wholeSlabRecouplingPartition source)

/-- Exact common denominator of the row-versus-coarse raw cross. -/
def wholeSlabRecouplingRawObservableCrossDenominator
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) : Q' :=
  wholeSlabRecouplingPartition source * S.coarse.physicalPartition

/-- The common denominator is strictly positive. -/
theorem wholeSlabRecouplingRawObservableCrossDenominator_pos
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) :
    (0 : Q') < wholeSlabRecouplingRawObservableCrossDenominator source := by
  unfold wholeSlabRecouplingRawObservableCrossDenominator
  exact Q'.mul_pos
    (wholeSlabRecouplingPartition_pos source)
    (slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)

/-- Exact cancellation-preserving normalization identity for one positive
conditional row and one arbitrary rational observable. -/
theorem wholeSlabRecouplingRawObservableRatio_sub_coarse_eqv_cross
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (observable : EdgeLabelling → Q') :
    wholeSlabRecouplingRawObservableRatio source observable -
        observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings observable ≈
      Q'.divPos
        (wholeSlabRecouplingRawObservableCrossNumerator source observable)
        (wholeSlabRecouplingRawObservableCrossDenominator source)
        (wholeSlabRecouplingRawObservableCrossDenominator_pos source) := by
  let hrow := wholeSlabRecouplingPartition_pos source
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  refine Q'.eqv_trans _
    (Q'.divPos
        (wholeSlabRecouplingRawObservableNumerator source observable)
        (wholeSlabRecouplingPartition source) hrow -
      Q'.divPos
        (physicalObservableNumerator S.coarse observable)
        S.coarse.physicalPartition hcoarse) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (normalizedObservableExpectation_eqv_raw_divPos
          S.coarse observable))
  simpa only [wholeSlabRecouplingRawObservableRatio,
      wholeSlabRecouplingRawObservableCrossNumerator,
      wholeSlabRecouplingRawObservableCrossDenominator] using
    (divPos_sub_divPos_eq_crossDifference
      (wholeSlabRecouplingRawObservableNumerator source observable)
      (physicalObservableNumerator S.coarse observable)
      (wholeSlabRecouplingPartition source)
      S.coarse.physicalPartition hrow hcoarse)

/-! ## 2. The connected positive-row specialization -/

/-- Source-resolved signed raw cross numerator for the selected connected
observable. -/
def positivePhysicalConnectedRawCrossNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) : Q' :=
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let coherent := positiveCoherentSource S hfineCutoff hcoarseCoupling
    source hsource hpositive
  wholeSlabRecouplingRawObservableCrossNumerator coherent
    (connectedRemainderObservable K M)

/-- Exact positive common denominator for the selected connected row. -/
def positivePhysicalConnectedRawCrossDenominator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source) : Q' :=
  wholeSlabRecouplingRawObservableCrossDenominator
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)

theorem positivePhysicalConnectedRawCrossDenominator_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source) :
    (0 : Q') <
      positivePhysicalConnectedRawCrossDenominator
        S hfineCutoff hcoarseCoupling source hsource hpositive := by
  unfold positivePhysicalConnectedRawCrossDenominator
  exact wholeSlabRecouplingRawObservableCrossDenominator_pos
    (positiveCoherentSource S hfineCutoff hcoarseCoupling
      source hsource hpositive)

/-- The selected positive-source row action is one signed raw cross divided
by its exact positive common denominator. -/
theorem positivePhysicalConnectedRawRowAction_eqv_rawCross_divPos
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
        (positivePhysicalConnectedRawCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M)
        (positivePhysicalConnectedRawCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive)
        (positivePhysicalConnectedRawCrossDenominator_pos
          S hfineCutoff hcoarseCoupling source hsource hpositive) := by
  simpa only [positivePhysicalConnectedRawRowAction,
      positivePhysicalConnectedRawCrossNumerator,
      positivePhysicalConnectedRawCrossDenominator] using
    (wholeSlabRecouplingRawObservableRatio_sub_coarse_eqv_cross
      (positiveCoherentSource S hfineCutoff hcoarseCoupling
        source hsource hpositive)
      (connectedRemainderObservable
        (physicalKernel S hfineCutoff hcoarseCoupling) M))

/-! ## 3. A division-free pointwise calibration -/

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

/-- Division-free pointwise input on every strictly positive fine source. -/
def PositivePhysicalConnectedRawCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  ∀ source (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source),
    Q'.abs
        (positivePhysicalConnectedRawCrossNumerator
          S hfineCutoff hcoarseCoupling source hsource hpositive M) ≤
      (kernelCeiling * (g * g)) *
        positivePhysicalConnectedRawCrossDenominator
          S hfineCutoff hcoarseCoupling source hsource hpositive

/-- A relative raw-cross estimate gives the positive-row pointwise
calibration with no coefficient loss. -/
theorem positivePhysicalConnectedRawPointwiseCalibration_of_rawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcross : PositivePhysicalConnectedRawCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    PositivePhysicalConnectedRawPointwiseCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold PositivePhysicalConnectedRawPointwiseCalibration
  intro source hsource hpositive
  let numerator := positivePhysicalConnectedRawCrossNumerator
    S hfineCutoff hcoarseCoupling source hsource hpositive M
  let denominator := positivePhysicalConnectedRawCrossDenominator
    S hfineCutoff hcoarseCoupling source hsource hpositive
  let hdenominator := positivePhysicalConnectedRawCrossDenominator_pos
    S hfineCutoff hcoarseCoupling source hsource hpositive
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positivePhysicalConnectedRawRowAction_eqv_rawCross_divPos
          S hfineCutoff hcoarseCoupling source hsource hpositive M))) ?_
  exact abs_divPos_le_of_abs_le_mul_local hdenominator
    (by
      unfold PositivePhysicalConnectedRawCrossCalibration at hcross
      simpa only [numerator, denominator] using
        hcross source hsource hpositive)

/-- The relative source-resolved raw-cross estimate compiles all the way to
the existing normalized centered-remainder calibration. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcross : PositivePhysicalConnectedRawCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawPointwise
    S hfineCutoff hcoarseCoupling M g kernelCeiling
    (positivePhysicalConnectedRawPointwiseCalibration_of_rawCross
      S hfineCutoff hcoarseCoupling M g kernelCeiling hcross)

#print axioms wholeSlabRecouplingRawObservableCrossNumerator
#print axioms wholeSlabRecouplingRawObservableCrossDenominator
#print axioms wholeSlabRecouplingRawObservableCrossDenominator_pos
#print axioms wholeSlabRecouplingRawObservableRatio_sub_coarse_eqv_cross
#print axioms positivePhysicalConnectedRawCrossNumerator
#print axioms positivePhysicalConnectedRawCrossDenominator
#print axioms positivePhysicalConnectedRawCrossDenominator_pos
#print axioms positivePhysicalConnectedRawRowAction_eqv_rawCross_divPos
#print axioms PositivePhysicalConnectedRawCrossCalibration
#print axioms positivePhysicalConnectedRawPointwiseCalibration_of_rawCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_positiveRawCross

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawCross
