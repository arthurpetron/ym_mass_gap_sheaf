/-
# A translated cutoff-two leakage cell at the first growing half

The explicit positive cutoff-two cell at central half zero is translated by
one Euclidean-time unit and extended by zero into the central half-one slab.
This file decomposes the transported physical labelling into its lower,
fixed, and reflected-upper restrictions.  The intended endpoint is a literal
positive boundary channel outside the vacuum half-amplitude support, which
would inhabit the growing-reference posterior obstruction at volume zero.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakagePositiveTotalCertificate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundaryPosterior
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairBoundarySupportObstruction
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive retained boundary total and the obstruction inhabitant -/

theorem translatedSingleFaceReferenceAmplitude_eqv_zero :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 1
        (lowSpinCentralReferenceState 0)
        translatedSingleFaceBoundary ≈
      0 := by
  exact lowSpinCentralReferenceHalfAmplitude_eqv_zero_of_vacuum_eqv_zero
    (w := cutoffTwoHalfCoupling) (K := 2) (volume := 0)
    (by decide) translatedSingleFaceBoundary
    translatedSingleFaceBoundary_vacuum_eqv_zero

/-- The transported cutoff-two cell is an explicit support mismatch at the
first growing half. -/
def cutoffTwoHalfOneGrowingReferenceBoundarySupportMismatch :
    CoarseGrowingReferenceBoundarySupportMismatch
      cutoffTwoHalfCoupling
      (by decide : (0 : Q') < cutoffTwoHalfCoupling)
      2 (by decide : 1 ≤ 2) 0 where
  boundary := translatedSingleFaceBoundary
  boundary_mem := translatedSingleFaceBoundary_mem
  positive_total := translatedSingleFaceBoundary_positiveTotal
  reference_amplitude_zero :=
    translatedSingleFaceReferenceAmplitude_eqv_zero

/-- At coupling `1/2`, cutoff two, and volume zero, no finite ceiling can
make the selected growing-reference posterior a uniform floor. -/
theorem no_cutoffTwoHalfOneReferenceBoundaryPosteriorFloor
    (ceiling : Q') :
    CoarseGrowingReferenceBoundaryPosteriorFloor
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 (by decide : 1 ≤ 2) 0 ceiling → False := by
  exact
    cutoffTwoHalfOneGrowingReferenceBoundarySupportMismatch
      |>.noReferenceBoundaryPosteriorFloor ceiling

/-- The same finite witness refutes the division-free positive-boundary
cross-bound for every ceiling at least one. -/
theorem no_cutoffTwoHalfOnePositiveBoundaryHalfAmplitudeCrossBound
    (ceiling : Q') (hone : (1 : Q') ≤ ceiling) :
    CoarseGrowingPositiveBoundaryHalfAmplitudeCrossBound
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 (by decide : 1 ≤ 2) 0 ceiling → False := by
  exact
    cutoffTwoHalfOneGrowingReferenceBoundarySupportMismatch
      |>.noPositiveBoundaryHalfAmplitudeCrossBound ceiling hone

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceLowerAmplitude_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceBoundary_positiveTotal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceReferenceAmplitude_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.cutoffTwoHalfOneGrowingReferenceBoundarySupportMismatch
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.no_cutoffTwoHalfOneReferenceBoundaryPosteriorFloor
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.no_cutoffTwoHalfOnePositiveBoundaryHalfAmplitudeCrossBound
