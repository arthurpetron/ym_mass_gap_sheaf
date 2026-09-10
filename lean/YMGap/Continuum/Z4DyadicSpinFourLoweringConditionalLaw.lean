/-
# The canonical spin-four production row as a normalized tilted Gibbs law

The preceding exact calculation identifies the raw row partition.  Here it
is connected back to the literal normalized production kernel used by the
observable and covariance compilers.  At positive fine coupling, the same
closed binary support is a strictly positive fine Gibbs source.  Its actual
cutoff-one physical-kernel row is therefore exactly the normalization of the
integer-tilted coarse Gibbs weight on the lowering downset.

This is the first direct bridge from the spin-four recoupling calculation to
the normalized production Markov row.  It concerns the explicit canonical
preimage of each accepted endpoint; it does not claim that every positive
fine source has this form or that the source-averaged centered defect is
already small.

Constructive contract: existing positive binary-support witnesses, exact
rational equivalence, and positive division only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
import YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward

namespace YMGap.Continuum.Z4DyadicSpinFourLoweringConditionalLaw

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterJointCarrierRawRowMass
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourEndpointLift
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4DyadicSpinFourWholeSlabTargetExact

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The canonical lift is a strictly positive fine Gibbs source -/

/-- The proof-carrying positive source produced by the canonical spin-four
closed binary support. -/
def attachedEndpointSpinFourPositiveSource
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling) :
    PositivePhysicalSource S :=
  (((attachedEndpointSpinFourEvenBinarySupportCoverage S hfineCutoff
      ).toFusionChannelCoverage.toPositiveExpandedCoverage
        hfineCutoff hfineCoupling).lift endpoint).source.1

/-- The positive-source adapter does not change the canonical fine
labelling. -/
theorem attachedEndpointSpinFourPositiveSource_val
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling) :
    (attachedEndpointSpinFourPositiveSource
      S endpoint hfineCutoff hfineCoupling).1 =
        attachedEndpointSpinFourFineState S endpoint := by
  rfl

/-- Strict fine Gibbs positivity of the exact fine source whose recoupling
row was computed in the lowering calculation. -/
theorem attachedEndpointSpinFourFineState_physicalTerm_pos
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling) :
    (0 : Q') < S.fine.physicalTerm
      (attachedEndpointSpinFourFineState S endpoint) := by
  have hpositive :=
    (attachedEndpointSpinFourPositiveSource
      S endpoint hfineCutoff hfineCoupling).2.2
  rw [attachedEndpointSpinFourPositiveSource_val
    S endpoint hfineCutoff hfineCoupling] at hpositive
  exact hpositive

/-- The coherent source used by the actual positive branch of the cutoff-one
production kernel. -/
def attachedEndpointSpinFourCoherentSource
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    (attachedEndpointSpinFourFineState S endpoint)
    (attachedEndpointSpinFourFineState_mem S endpoint hfineCutoff)
    (attachedEndpointSpinFourFineState_physicalTerm_pos
      S endpoint hfineCutoff hfineCoupling)

/-! ## 2. Normalize the exact tilted Gibbs row -/

/-- The explicit integer-tilted Gibbs row partition attached to one accepted
coarse endpoint. -/
def attachedEndpointSpinFourTiltedGibbsRowMass
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse) : Q' :=
  listQSum
    (fun targetState =>
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct
            S endpoint.1.1 targetState) *
        S.coarse.physicalTerm targetState)
    (spinFourLoweringTargets S endpoint.1.1)

/-- The coherent recoupling partition is exactly the displayed tilted Gibbs
row mass. -/
theorem wholeSlabRecouplingPartition_attachedEndpointSpinFour_eqv_tiltedGibbs
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    wholeSlabRecouplingPartition
        (attachedEndpointSpinFourCoherentSource S endpoint hfineCutoff
          hfineCoupling hcoarseCoupling) ≈
      attachedEndpointSpinFourTiltedGibbsRowMass S endpoint := by
  unfold wholeSlabRecouplingPartition
    attachedEndpointSpinFourCoherentSource
    attachedEndpointSpinFourTiltedGibbsRowMass
  exact
    wholeSlabRawRowMass_spinFourProfile_eqv_multiplicityTiltedGibbs
      S (attachedEndpointSpinFourFineState S endpoint) endpoint.1.1
        hfineCutoff
        (attachedEndpointSpinFourWholeSlabPacketProfile
          S endpoint hfineCutoff)

/-- The exact tilted Gibbs row mass is strictly positive, with its witness
transported from the already constructed coherent production row. -/
theorem attachedEndpointSpinFourTiltedGibbsRowMass_pos
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    (0 : Q') < attachedEndpointSpinFourTiltedGibbsRowMass S endpoint := by
  have hpartition := wholeSlabRecouplingPartition_pos
    (attachedEndpointSpinFourCoherentSource S endpoint hfineCutoff
      hfineCoupling hcoarseCoupling)
  have heq :=
    wholeSlabRecouplingPartition_attachedEndpointSpinFour_eqv_tiltedGibbs
      S endpoint hfineCutoff hfineCoupling hcoarseCoupling
  exact Q'.pos_of_lt_of_le hpartition (Q'.le_of_eqv heq)

private theorem divPos_eqv_congr_local
    {numerator numerator' denominator denominator' : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hdenominator' : (0 : Q') < denominator')
    (hnumerator : numerator ≈ numerator')
    (hdenominatorEq : denominator ≈ denominator') :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator' denominator' hdenominator' := by
  apply Q'.eqv_of_le_le
  · apply Q'.le_divPos_of_mul_le
      numerator' denominator' hdenominator'
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator denominator hdenominator)
          denominator' denominator
          (Q'.eqv_symm hdenominatorEq))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator denominator hdenominator)
          hnumerator))
  · apply Q'.le_divPos_of_mul_le
      numerator denominator hdenominator
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos numerator' denominator' hdenominator')
          denominator denominator' hdenominatorEq)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv
            numerator' denominator' hdenominator')
          (Q'.eqv_symm hnumerator)))

/-- The literal coherent conditional row of the canonical fine lift is the
normalized integer-tilted Gibbs law. -/
theorem wholeSlabRecouplingConditionalKernel_attachedEndpointSpinFour_eqv_tiltedGibbs
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingConditionalKernel
        (attachedEndpointSpinFourCoherentSource S endpoint hfineCutoff
          hfineCoupling hcoarseCoupling) targetState ≈
      Q'.divPos
        (Q'.ofNat
            (spinFourLoweringMultiplicityProduct
              S endpoint.1.1 targetState) *
          S.coarse.physicalTerm targetState)
        (attachedEndpointSpinFourTiltedGibbsRowMass S endpoint)
        (attachedEndpointSpinFourTiltedGibbsRowMass_pos
          S endpoint hfineCutoff hfineCoupling hcoarseCoupling) := by
  let source := attachedEndpointSpinFourCoherentSource
    S endpoint hfineCutoff hfineCoupling hcoarseCoupling
  have hsourceState : source.fineState =
      attachedEndpointSpinFourFineState S endpoint := by
    rfl
  unfold wholeSlabRecouplingConditionalKernel
  exact divPos_eqv_congr_local
    (wholeSlabRecouplingPartition_pos source)
    (attachedEndpointSpinFourTiltedGibbsRowMass_pos
      S endpoint hfineCutoff hfineCoupling hcoarseCoupling)
    (Q'.eqv_trans _ _ _
      (by
        rw [hsourceState]
        exact
          wholeSlabRecouplingRawWeight_attachedEndpointSpinFour_eqv_loweringWeight
            S endpoint hfineCutoff targetState)
      (spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
        S endpoint.1.1 targetState htargetMem))
    (wholeSlabRecouplingPartition_attachedEndpointSpinFour_eqv_tiltedGibbs
      S endpoint hfineCutoff hfineCoupling hcoarseCoupling)

/-! ## 3. The same formula for the actual physical production kernel -/

/-- The row used by the physical pushforward/covariance chain is exactly the
same normalized tilted Gibbs law on the canonical endpoint lift. -/
theorem physicalKernel_attachedEndpointSpinFour_eqv_tiltedGibbs
    (S : SlabScalePair)
    (endpoint : SlabExpandedFineSourceEntry S.coarse)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (targetState : EdgeLabelling)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
        (attachedEndpointSpinFourFineState S endpoint) targetState ≈
      Q'.divPos
        (Q'.ofNat
            (spinFourLoweringMultiplicityProduct
              S endpoint.1.1 targetState) *
          S.coarse.physicalTerm targetState)
        (attachedEndpointSpinFourTiltedGibbsRowMass S endpoint)
        (attachedEndpointSpinFourTiltedGibbsRowMass_pos
          S endpoint hfineCutoff hfineCoupling hcoarseCoupling) := by
  refine Q'.eqv_trans _
    (wholeSlabRecouplingConditionalKernel
      (attachedEndpointSpinFourCoherentSource S endpoint hfineCutoff
        hfineCoupling hcoarseCoupling) targetState) _ ?_ ?_
  · unfold physicalKernel SlabScalePair.FiniteSlabKernel.kernel
      cutoffOneWholeSlabFiniteKernel
      attachedEndpointSpinFourCoherentSource
    exact cutoffOneWholeSlabKernel_eq_positive
      S hfineCutoff hcoarseCoupling
      (attachedEndpointSpinFourFineState_mem S endpoint hfineCutoff)
      (attachedEndpointSpinFourFineState_physicalTerm_pos
        S endpoint hfineCutoff hfineCoupling)
      targetState
  · exact
      wholeSlabRecouplingConditionalKernel_attachedEndpointSpinFour_eqv_tiltedGibbs
        S endpoint hfineCutoff hfineCoupling hcoarseCoupling
          targetState htargetMem

#print axioms attachedEndpointSpinFourPositiveSource_val
#print axioms attachedEndpointSpinFourFineState_physicalTerm_pos
#print axioms wholeSlabRecouplingPartition_attachedEndpointSpinFour_eqv_tiltedGibbs
#print axioms attachedEndpointSpinFourTiltedGibbsRowMass_pos
#print axioms wholeSlabRecouplingConditionalKernel_attachedEndpointSpinFour_eqv_tiltedGibbs
#print axioms physicalKernel_attachedEndpointSpinFour_eqv_tiltedGibbs

end YMGap.Continuum.Z4DyadicSpinFourLoweringConditionalLaw
