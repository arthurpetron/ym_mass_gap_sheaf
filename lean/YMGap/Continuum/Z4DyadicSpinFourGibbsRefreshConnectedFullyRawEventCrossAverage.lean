/-
# Signed source average of the fully raw connected rows

The fully raw event-cross polynomial from the preceding module gives an
exact formula for each strictly positive fine Gibbs row.  Requiring every
one of those rows to be quadratically small is stronger than the physical
consumer: the centered pushed-law remainder only sees their signed fine-law
average.

This module keeps that source cancellation.  It forms the finite signed
average of the fully raw row ratios over exactly the positive Gibbs sources
and proves that it is exactly the already established centered-cylinder
remainder.  Thus a quadratic estimate on this aggregate is equivalent to
the normalized physical producer; the pointwise fully raw premise remains
available only as a stronger fallback.

No smallness estimate is asserted.  Cutoff/volume uniformity, continuum
persistence, OS/GNS reconstruction, the Hamiltonian gap, and the Yang--Mills
mass gap remain open.

Constructive contract: dependent finite rational recursion and positive
division witnesses only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCross

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCross
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Preserve the signed source aggregation -/

/-- Positive-source recursion whose summand is the normalized fine Gibbs
weight times the fully raw connected row ratio. -/
def positivePhysicalConnectedFullyRawSignedSourceAverageAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    (sources : List EdgeLabelling) →
      (∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings) → Q'
  | [], _ => 0
  | source :: tail, hphysical =>
      if hpositive : (0 : Q') < S.fine.physicalTerm source then
        S.fine.normalizedMass source *
            Q'.divPos
              (positivePhysicalConnectedFullyRawEventCrossNumerator
                S hfineCutoff hcoarseCoupling source
                (hphysical source List.mem_cons_self) hpositive M)
              (positivePhysicalConnectedFullyRawEventCrossDenominator
                S hfineCutoff hcoarseCoupling source
                (hphysical source List.mem_cons_self) hpositive)
              (positivePhysicalConnectedFullyRawEventCrossDenominator_pos
                S hfineCutoff hcoarseCoupling source
                (hphysical source List.mem_cons_self) hpositive) +
          positivePhysicalConnectedFullyRawSignedSourceAverageAux
            S hfineCutoff hcoarseCoupling M tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positivePhysicalConnectedFullyRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- The complete signed average of fully raw row ratios.  Gibbs-null rows
are omitted before any division witness is requested. -/
def positivePhysicalConnectedFullyRawSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  positivePhysicalConnectedFullyRawSignedSourceAverageAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

private theorem positiveRawSignedSourceAverageAux_eqv_fullyRawAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      positivePhysicalConnectedRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M sources hphysical ≈
        positivePhysicalConnectedFullyRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M sources hphysical
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let hsource := hphysical source List.mem_cons_self
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
      · simp only [positivePhysicalConnectedRawSignedSourceAverageAux,
          positivePhysicalConnectedFullyRawSignedSourceAverageAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (positivePhysicalConnectedRawRowAction_eqv_fullyRawEventCross_divPos
              S hfineCutoff hcoarseCoupling source hsource hpositive M))
          (positiveRawSignedSourceAverageAux_eqv_fullyRawAux
            S hfineCutoff hcoarseCoupling M tail htail)
      · simp only [positivePhysicalConnectedRawSignedSourceAverageAux,
          positivePhysicalConnectedFullyRawSignedSourceAverageAux,
          dif_neg hpositive]
        exact positiveRawSignedSourceAverageAux_eqv_fullyRawAux
          S hfineCutoff hcoarseCoupling M tail htail

/-- Replacing every positive raw row action by its fully raw ratio preserves
the complete signed fine-law average exactly. -/
theorem positivePhysicalConnectedRawSignedSourceAverage_eqv_fullyRaw
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      positivePhysicalConnectedFullyRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M := by
  unfold positivePhysicalConnectedRawSignedSourceAverage
    positivePhysicalConnectedFullyRawSignedSourceAverage
  exact positiveRawSignedSourceAverageAux_eqv_fullyRawAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
    (fun _ hsource => hsource)

/-- The aggregate signed fully raw ratio is exactly the normalized physical
centered-cylinder remainder. -/
theorem positivePhysicalConnectedFullyRawSignedSourceAverage_eqv_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedFullyRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (positivePhysicalConnectedRawSignedSourceAverage_eqv_fullyRaw
        S hfineCutoff hcoarseCoupling M))
    (positivePhysicalConnectedRawSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-! ## 2. The weakest exact fully raw calibration -/

/-- Quadratic premise on the signed source aggregate of fully raw row
ratios.  Unlike the pointwise premise, this retains cancellation between
distinct positive fine Gibbs sources. -/
def PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (positivePhysicalConnectedFullyRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M) ≤
    kernelCeiling * (g * g)

/-- The signed fully raw aggregate premise is equivalent, with no constant
loss, to the normalized centered-remainder premise. -/
theorem positiveFullyRawSignedSourceAverageCalibration_iff_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  unfold PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
    CoarseGibbsRefreshConnectedRemainderCalibration
  have hexact :=
    positivePhysicalConnectedFullyRawSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (Q'.eqv_symm hexact))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hexact)) h

/-- Exact two-way handoff from the signed fully raw source aggregate to the
established aggregate receiver-column cross.  Both positive partition-square
normalizations cancel, so neither direction loses a constant. -/
theorem positiveFullyRawSignedSourceAverageCalibration_iff_rawColumnCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          (kernelCeiling * (g * g)) := by
  exact Iff.trans
    (positiveFullyRawSignedSourceAverageCalibration_iff_centeredRemainder
      S hfineCutoff hcoarseCoupling M g kernelCeiling)
    (coarseGibbsRefreshConnectedRemainderCalibration_iff_rawColumnCross
      S hfineCutoff hcoarseCoupling M g kernelCeiling)

/-- Direct compiler from the cancellation-preserving fully raw aggregate to
the normalized centered producer. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_fullyRawSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (haverage :
      PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling :=
  (positiveFullyRawSignedSourceAverageCalibration_iff_centeredRemainder
    S hfineCutoff hcoarseCoupling M g kernelCeiling).mp haverage

/-- The earlier pointwise fully raw calibration remains a sufficient but
strictly stronger fallback for the signed aggregate calibration. -/
theorem fullyRawSignedSourceAverageCalibration_of_pointwise
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hpointwise : PositivePhysicalConnectedFullyRawEventCrossCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling :=
  (positiveFullyRawSignedSourceAverageCalibration_iff_centeredRemainder
    S hfineCutoff hcoarseCoupling M g kernelCeiling).mpr
      (coarseGibbsRefreshConnectedRemainderCalibration_of_fullyRawEventCross
        S hfineCutoff hcoarseCoupling M g kernelCeiling hpointwise)

#print axioms positivePhysicalConnectedFullyRawSignedSourceAverageAux
#print axioms positivePhysicalConnectedFullyRawSignedSourceAverage
#print axioms positivePhysicalConnectedRawSignedSourceAverage_eqv_fullyRaw
#print axioms positivePhysicalConnectedFullyRawSignedSourceAverage_eqv_centeredRemainder
#print axioms PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
#print axioms positiveFullyRawSignedSourceAverageCalibration_iff_centeredRemainder
#print axioms positiveFullyRawSignedSourceAverageCalibration_iff_rawColumnCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_fullyRawSignedSourceAverage
#print axioms fullyRawSignedSourceAverageCalibration_of_pointwise

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage
