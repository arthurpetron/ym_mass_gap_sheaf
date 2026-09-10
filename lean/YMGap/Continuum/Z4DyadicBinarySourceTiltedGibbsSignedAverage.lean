/-
# The connected remainder as a signed mixture of exact tilted Gibbs rows

The all-source conditional-law theorem can now replace every positive raw
recoupling ratio in the selected connected observable average.  This file
performs that substitution without taking an absolute value across coarse
targets or fine sources.

The resulting formula is a fine-Gibbs-weighted signed mixture of explicit
source-dependent integer-tilted coarse Gibbs expectations, each compared
with the same coarse Gibbs refresh expectation.  It is exactly equal to the
existing centered blocking remainder.  No smallness estimate is asserted.

Constructive contract: exact finite sums, rational equivalence, and the
already certified positive denominators only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSignedAverage

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRawRow
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRowAction
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-! ## 1. One explicit source-dependent tilted row -/

/-- The normalized integer-tilted coarse Gibbs kernel determined by one
positive cutoff-one fine source. -/
def positivePhysicalSourceTiltedGibbsKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Q' :=
  Q'.divPos
    (Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S source.1)
          targetState) *
      S.coarse.physicalTerm targetState)
    (positivePhysicalSourceTiltedGibbsRowMass S source)
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source)

/-- Connected observable action of one explicit tilted row minus the coarse
Gibbs refresh expectation. -/
def positivePhysicalConnectedTiltedGibbsRowAction
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (M : SlabFaceBlockMap S) : Q' :=
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let observable := connectedRemainderObservable K M
  observableExpectation
      (positivePhysicalSourceTiltedGibbsKernel
        S hfineCutoff hcoarseCoupling source)
      S.coarse.physicalLabellings observable -
    observableExpectation S.coarse.normalizedMass
      S.coarse.physicalLabellings observable

/-- The previously exposed raw-ratio connected action is exactly the
source-dependent normalized tilted-Gibbs action. -/
theorem positivePhysicalConnectedRawRowAction_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm source)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawRowAction
        S hfineCutoff hcoarseCoupling source hsource hpositive M ≈
      positivePhysicalConnectedTiltedGibbsRowAction
        S hfineCutoff hcoarseCoupling
          (⟨source, hsource, hpositive⟩ : PositivePhysicalSource S) M := by
  let proofSource : PositivePhysicalSource S :=
    ⟨source, hsource, hpositive⟩
  let coherent := positivePhysicalSourceCoherentSource
    S hfineCutoff hcoarseCoupling proofSource
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let observable := connectedRemainderObservable K M
  unfold positivePhysicalConnectedRawRowAction
    positivePhysicalConnectedTiltedGibbsRowAction
  exact sub_eqv_both_local
    (Q'.eqv_trans _
      (observableExpectation
        (wholeSlabRecouplingConditionalKernel coherent)
        S.coarse.physicalLabellings observable) _
      (Q'.eqv_symm
        (conditionalKernelObservableExpectation_eqv_rawRatio
          coherent observable))
      (by
        unfold observableExpectation
        apply listQSum_congr_on
        intro targetState htargetMem
        exact Q'.mul_eqv_congr_right _ _ (observable targetState)
          (wholeSlabRecouplingConditionalKernel_positivePhysicalSource_eqv_tiltedGibbs
            S hfineCutoff hcoarseCoupling proofSource
              targetState htargetMem)))
    (Q'.eqv_refl _)

/-! ## 2. Preserve the complete signed fine-source average -/

/-- Positive-source recursion after replacing every raw row ratio by its
explicit normalized tilted-Gibbs law. -/
def positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
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
            positivePhysicalConnectedTiltedGibbsRowAction
              S hfineCutoff hcoarseCoupling
              (⟨source, hphysical source List.mem_cons_self, hpositive⟩ :
                PositivePhysicalSource S) M +
          positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
            S hfineCutoff hcoarseCoupling M tail
            (fun item hitem =>
              hphysical item (List.mem_cons_of_mem source hitem))
      else
        positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M tail
          (fun item hitem =>
            hphysical item (List.mem_cons_of_mem source hitem))

/-- The complete signed fine-Gibbs mixture of explicit tilted-Gibbs row
actions, retaining cancellation across all positive fine sources. -/
def positivePhysicalConnectedTiltedGibbsSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
      (fun _ hsource => hsource)

private theorem positiveRawSignedSourceAverageAux_eqv_tiltedGibbsAux
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      positivePhysicalConnectedRawSignedSourceAverageAux
          S hfineCutoff hcoarseCoupling M sources hphysical ≈
        positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
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
          positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux,
          dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left
            (S.fine.normalizedMass source) _ _
            (positivePhysicalConnectedRawRowAction_eqv_tiltedGibbs
              S hfineCutoff hcoarseCoupling source hsource hpositive M))
          (positiveRawSignedSourceAverageAux_eqv_tiltedGibbsAux
            S hfineCutoff hcoarseCoupling M tail htail)
      · simp only [positivePhysicalConnectedRawSignedSourceAverageAux,
          positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux,
          dif_neg hpositive]
        exact positiveRawSignedSourceAverageAux_eqv_tiltedGibbsAux
          S hfineCutoff hcoarseCoupling M tail htail

/-- Exact substitution of every positive raw recoupling row by the explicit
source-dependent tilted-Gibbs row in the complete signed average. -/
theorem positivePhysicalConnectedRawSignedSourceAverage_eqv_tiltedGibbs
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedRawSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      positivePhysicalConnectedTiltedGibbsSignedSourceAverage
        S hfineCutoff hcoarseCoupling M := by
  unfold positivePhysicalConnectedRawSignedSourceAverage
    positivePhysicalConnectedTiltedGibbsSignedSourceAverage
  exact positiveRawSignedSourceAverageAux_eqv_tiltedGibbsAux
    S hfineCutoff hcoarseCoupling M S.fine.physicalLabellings
      (fun _ hsource => hsource)

/-- The explicit signed mixture of source-dependent tilted Gibbs rows is
exactly the selected centered physical blocking remainder. -/
theorem positivePhysicalConnectedTiltedGibbsSignedSourceAverage_eqv_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedTiltedGibbsSignedSourceAverage
        S hfineCutoff hcoarseCoupling M ≈
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (positivePhysicalConnectedRawSignedSourceAverage_eqv_tiltedGibbs
        S hfineCutoff hcoarseCoupling M))
    (positivePhysicalConnectedRawSignedSourceAverage_eqv_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-! ## 3. Axiom audit -/

#print axioms positivePhysicalSourceTiltedGibbsKernel
#print axioms positivePhysicalConnectedTiltedGibbsRowAction
#print axioms positivePhysicalConnectedRawRowAction_eqv_tiltedGibbs
#print axioms positivePhysicalConnectedTiltedGibbsSignedSourceAverageAux
#print axioms positivePhysicalConnectedTiltedGibbsSignedSourceAverage
#print axioms positivePhysicalConnectedRawSignedSourceAverage_eqv_tiltedGibbs
#print axioms positivePhysicalConnectedTiltedGibbsSignedSourceAverage_eqv_centeredRemainder

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSignedAverage
