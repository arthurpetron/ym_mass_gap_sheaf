/-
# Finite certificate for the translated cutoff-two leakage cell

This small module computes the one genuinely concrete certificate used by
the first-growing-half leakage construction.  It translates the known
half-zero cell, proves that the zero extension is supported on the half-one
slab, restricts it to lower/fixed/upper data, and checks one lower link whose
vacuum-source fusion multiplicity is zero.  Keeping this finite computation
in its own module lets downstream abstract positivity arguments import the
checked result without retaining its reduction proof in the same Lean
process.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeHalfAmplitudeFactorization
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
import YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
import YMGap.Continuum.Z4TimeShiftedPhysicalWeights

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedPhysicalWeights

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Translate and restrict the known positive cell -/

def translatedSingleFaceAmbientTwo : EdgeLabelling :=
  slabToAmbientPhysical 1 cutoffTwoCubeSingleFacePhysical

def translatedSingleFaceAmbientThree : EdgeLabelling :=
  timeShiftTransportPhysical 1 2 translatedSingleFaceAmbientTwo

def translatedSingleFaceAmbientFour : EdgeLabelling :=
  transportPhysical 3 4 translatedSingleFaceAmbientThree

def translatedSingleFaceSlab : EdgeLabelling :=
  ambientToSlabPhysical 3 translatedSingleFaceAmbientFour

def translatedSingleFaceLower : EdgeLabelling :=
  centralLowerRestriction 1 translatedSingleFaceSlab

def translatedSingleFaceBoundary : EdgeLabelling :=
  centralBoundaryRestriction 1 translatedSingleFaceSlab

def translatedSingleFaceUpper : EdgeLabelling :=
  centralReflectedUpperRestriction 1 translatedSingleFaceSlab

theorem cutoffTwoCubeSingleFacePhysical_mem_full :
    cutoffTwoCubeSingleFacePhysical ∈
      boundedEdgeLabellings 2 (slabPhysicalFaceEdges 1) := by
  exact assembleReflectedSlabLabelling_mem_full
    (centralLowerCubeState_mem_centralHalfStates (by decide : 1 ≤ 2))
    cutoffTwoCubeSingleFaceBoundary_mem_channels
    cutoffTwoSingleFaceTwoState_mem_halfStates

theorem translatedSingleFaceAmbientTwo_mem :
    translatedSingleFaceAmbientTwo ∈
      boundedEdgeLabellings 2 (List.range (plaquetteEdgeCount 2)) := by
  exact slabToAmbientPhysical_mem_bounded
    cutoffTwoCubeSingleFacePhysical_mem_full

theorem translatedSingleFaceAmbientThree_mem :
    translatedSingleFaceAmbientThree ∈
      boundedEdgeLabellings 2 (List.range (plaquetteEdgeCount 3)) := by
  exact timeShiftTransportPhysical_mem_bounded
    translatedSingleFaceAmbientTwo_mem

theorem translatedSingleFaceAmbientFour_mem :
    translatedSingleFaceAmbientFour ∈
      boundedEdgeLabellings 2 (List.range (plaquetteEdgeCount 4)) := by
  exact transportPhysical_mem_bounded translatedSingleFaceAmbientThree_mem

private theorem boxPlaquettes_three_subset_slab_three
    {plaquette : Z4Plaq}
    (hplaquette : plaquette ∈ boxPlaquettes 3) :
    plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  apply (mem_boundaryCompleteSlabPlaquettes 3 plaquette).2
  constructor
  · exact boxPlaquettes_mono (by omega) hplaquette
  · have hcoordinates := (mem_boxPlaquettes plaquette 3).1 hplaquette
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    change a < 3 ∧ b < 3 ∧ c < 3 ∧ d < 3 at hcoordinates
    cases plane <;> simp [plaquetteTimeAdmissible] <;> omega

theorem translatedSingleFaceAmbientFour_supported :
    ambientSlabSupportedB 3 translatedSingleFaceAmbientFour = true := by
  apply (ambientSlabSupportedB_true_iff_zero 3 _).2
  intro targetId htarget
  have hparts := (mem_ambientNonSlabFaceIds_iff 3 targetId).1 htarget
  have hlt := List.mem_range.mp hparts.1
  unfold translatedSingleFaceAmbientFour transportPhysical
  rw [if_pos hlt]
  apply geometricSpinOfPhysical_zero_of_not_mem
  intro hsmall
  exact hparts.2 (boxPlaquettes_three_subset_slab_three hsmall)

theorem translatedSingleFaceSlab_mem :
    translatedSingleFaceSlab ∈
      boundedEdgeLabellings 2 (slabPhysicalFaceEdges 3) := by
  exact ambientToSlabPhysical_mem_bounded translatedSingleFaceAmbientFour_mem

theorem translatedSingleFaceSlab_ambient :
    slabToAmbientPhysical 3 translatedSingleFaceSlab =
      translatedSingleFaceAmbientFour := by
  exact slabToAmbientPhysical_ambientToSlab
    translatedSingleFaceAmbientFour_mem
    translatedSingleFaceAmbientFour_supported

theorem translatedSingleFaceLower_mem :
    translatedSingleFaceLower ∈ centralHalfStates 2 1 := by
  exact centralLowerRestriction_mem translatedSingleFaceSlab_mem

theorem translatedSingleFaceBoundary_mem :
    translatedSingleFaceBoundary ∈ centralBoundaryChannels 2 1 := by
  exact centralBoundaryRestriction_mem translatedSingleFaceSlab_mem

theorem translatedSingleFaceUpper_mem :
    translatedSingleFaceUpper ∈ centralHalfStates 2 1 := by
  exact centralReflectedUpperRestriction_mem translatedSingleFaceSlab_mem

theorem translatedSingleFace_assemble :
    assembleReflectedSlabLabelling 1
        translatedSingleFaceLower
        translatedSingleFaceBoundary
        translatedSingleFaceUpper =
      translatedSingleFaceSlab := by
  exact assembleReflectedSlabLabelling_restrictions
    translatedSingleFaceSlab_mem

/-! ## 2. Exact transported weight -/

theorem cutoffTwoSingleFaceTerm_eqv_translated :
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoCubeSingleFacePhysical ≈
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 3
        translatedSingleFaceSlab := by
  have hambient := slabParametricKPhysicalTerm_ambient
    cutoffTwoHalfCoupling cutoffTwoCubeSingleFacePhysical_mem_full
  have hshift := parametricKPhysicalTerm_timeShift
    cutoffTwoHalfCoupling (shift := 1)
    translatedSingleFaceAmbientTwo_mem
  have hcross := parametricKPhysicalTerm_cross_volume
    cutoffTwoHalfCoupling (small := 3) (large := 4) (by omega)
    translatedSingleFaceAmbientThree_mem
  have htarget := slabParametricKPhysicalTerm_ambient
    cutoffTwoHalfCoupling translatedSingleFaceSlab_mem
  change
    slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 1
        cutoffTwoCubeSingleFacePhysical ≈
      parametricKPhysicalTerm cutoffTwoHalfCoupling 2 2
        translatedSingleFaceAmbientTwo at hambient
  change
    parametricKPhysicalTerm cutoffTwoHalfCoupling 2 2
        translatedSingleFaceAmbientTwo ≈
      parametricKPhysicalTerm cutoffTwoHalfCoupling 2 3
        translatedSingleFaceAmbientThree at hshift
  change
    parametricKPhysicalTerm cutoffTwoHalfCoupling 2 3
        translatedSingleFaceAmbientThree ≈
      parametricKPhysicalTerm cutoffTwoHalfCoupling 2 4
        translatedSingleFaceAmbientFour at hcross
  rw [translatedSingleFaceSlab_ambient] at htarget
  exact Q'.eqv_trans _ _ _ hambient
    (Q'.eqv_trans _ _ _ hshift
      (Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm htarget)))

theorem translatedSingleFaceTerm_pos :
    (0 : Q') <
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 3
        translatedSingleFaceSlab := by
  exact Q'.pos_of_lt_of_le cutoffTwoCubeSingleFacePhysicalTerm_pos
    (Q'.le_of_eqv cutoffTwoSingleFaceTerm_eqv_translated)

/-! ## 3. One computed vacuum-forcing link -/

def translatedSingleFaceVacuumPhysical : EdgeLabelling :=
  assembleReflectedSlabLabelling 1 zeroEdgeLabelling
    translatedSingleFaceBoundary zeroEdgeLabelling

private def fallbackLowerLink : Z4Link := ((0, 0, 0, 0), .x0)

def translatedSingleFaceVacuumForcingLink : Z4Link :=
  (centralLowerLinks 1).getD 8 fallbackLowerLink

theorem translatedSingleFaceVacuumForcingLink_mem :
    translatedSingleFaceVacuumForcingLink ∈ centralLowerLinks 1 := by
  decide

theorem translatedSingleFaceVacuumForcingLinkMultiplicity_zero :
    slabExplicitLinkMultiplicity 2 3 translatedSingleFaceVacuumPhysical
        translatedSingleFaceVacuumForcingLink =
      0 := by
  decide

theorem translatedSingleFaceBoundary_vacuum_eqv_zero :
    centralHalfAmplitude cutoffTwoHalfCoupling 2 1
        zeroEdgeLabelling translatedSingleFaceBoundary ≈
      0 := by
  have hproduct :
      slabLinkMultiplicityProductOn 2 3
          translatedSingleFaceVacuumPhysical (centralLowerLinks 1) =
        0 := by
    unfold slabLinkMultiplicityProductOn
    exact natListProduct_eq_zero_of_member
      (slabExplicitLinkMultiplicity 2 3
        translatedSingleFaceVacuumPhysical)
      (centralLowerLinks 1)
      translatedSingleFaceVacuumForcingLink_mem
      translatedSingleFaceVacuumForcingLinkMultiplicity_zero
  unfold centralHalfAmplitude centralLowerFactor
  change
    slabFaceFactorOn cutoffTwoHalfCoupling 2
          translatedSingleFaceVacuumPhysical (centralLowerFaceIds 1) *
        Q'.ofNat
          (slabLinkMultiplicityProductOn 2 3
            translatedSingleFaceVacuumPhysical (centralLowerLinks 1)) ≈
      0
  rw [hproduct]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ Q'.ofNat_zero_eqv)
    (Q'.mul_zero_eqv _)

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceAmbientFour_supported
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceSlab_ambient
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFace_assemble
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.cutoffTwoSingleFaceTerm_eqv_translated
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceTerm_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceVacuumForcingLinkMultiplicity_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceBoundary_vacuum_eqv_zero
