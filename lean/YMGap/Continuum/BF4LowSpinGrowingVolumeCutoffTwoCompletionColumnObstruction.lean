/-
# The translated cutoff-two cell refutes the full completion-column bound

The retained boundary mismatch is stronger than a failure of the posterior
sufficient producer.  At the completion consisting of the translated lower
state and boundary, the entire growing completion column is strictly positive,
while the selected low-spin reference completion is zero.  Hence no finite
ceiling can inhabit the literal completion-column cross-bound at this datum.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem q_left_pos_of_mul_pos_local
    {left right : Q'}
    (hright : (0 : Q') ≤ right)
    (hproduct : (0 : Q') < left * right) :
    (0 : Q') < left := by
  have hproductNum := Q'.num_pos_of_pos hproduct
  change (0 : Int) < left.num * right.num at hproductNum
  have hrightNum : (0 : Int) ≤ right.num :=
    (Q'.zero_le_iff_num_nonneg right).mp hright
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hleftNonpos
  have hmulNonpos : left.num * right.num ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg hleftNonpos hrightNum
  exact (Int.not_lt_of_ge hmulNonpos) hproductNum

theorem translatedSingleFaceBoundaryWeight_pos :
    (0 : Q') <
      centralBoundaryWeight cutoffTwoHalfCoupling 2 1
        translatedSingleFaceBoundary := by
  have hgram := centralPhysicalTerm_eq_gram_integrand
    cutoffTwoHalfCoupling translatedSingleFaceLower_mem
    translatedSingleFaceBoundary_mem translatedSingleFaceUpper_mem
  rw [translatedSingleFace_assemble] at hgram
  have hproduct :
      (0 : Q') <
        centralBoundaryWeight cutoffTwoHalfCoupling 2 1
            translatedSingleFaceBoundary *
          (centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceLower translatedSingleFaceBoundary *
            centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceUpper translatedSingleFaceBoundary) :=
    Q'.pos_of_lt_of_le translatedSingleFaceTerm_pos
      (Q'.le_of_eqv hgram)
  exact q_left_pos_of_mul_pos_local
    (Q'.mul_nonneg _ _
      (centralHalfAmplitude_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 1 translatedSingleFaceLower translatedSingleFaceBoundary)
      (centralHalfAmplitude_nonnegative
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 1 translatedSingleFaceUpper translatedSingleFaceBoundary))
    hproduct

theorem translatedSingleFaceCompletion_mem :
    (translatedSingleFaceLower, translatedSingleFaceBoundary) ∈
      centralPositiveCompletionPairs cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 1 := by
  unfold centralPositiveCompletionPairs
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨translatedSingleFaceLower_mem_positive,
      translatedSingleFaceBoundary_mem⟩

theorem translatedSingleFaceCompletionColumn_pos :
    (0 : Q') <
      growingCompletionColumnWeight cutoffTwoHalfCoupling 2 0
        (translatedSingleFaceLower, translatedSingleFaceBoundary) := by
  have hfactor :=
    growingCompletionColumnWeight_eqv_positiveBoundaryAmplitudeFactorization
      translatedSingleFaceLower_mem_positive
      translatedSingleFaceBoundary_mem
  have hright :
      (0 : Q') <
        centralBoundaryWeight cutoffTwoHalfCoupling 2 1
            translatedSingleFaceBoundary *
          (centralPositiveBoundaryTotalHalfAmplitude cutoffTwoHalfCoupling
              (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
              2 1 translatedSingleFaceBoundary *
            centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceLower translatedSingleFaceBoundary) :=
    Q'.mul_pos translatedSingleFaceBoundaryWeight_pos
      (Q'.mul_pos translatedSingleFaceBoundary_positiveTotal
        translatedSingleFaceLowerAmplitude_pos)
  exact Q'.pos_of_lt_of_le hright (Q'.ge_of_eqv hfactor)

theorem translatedSingleFaceReferenceCompletion_eqv_zero :
    centralPositiveCompletionWeight cutoffTwoHalfCoupling 2 1
        (lowSpinCentralReferenceState 0)
        (translatedSingleFaceLower, translatedSingleFaceBoundary) ≈
      0 := by
  have hrefMem :=
    (lowSpinCentralKPositiveRawReplication cutoffTwoHalfCoupling
      (by decide : (0 : Q') < cutoffTwoHalfCoupling)
      2 (by decide : 1 ≤ 2) 0).reference_mem
  have hrefHalf : lowSpinCentralReferenceState 0 ∈
      centralHalfStates 2 1 :=
    (mem_centralPositiveHalfStates_iff.mp hrefMem).1
  have hgram := centralPhysicalTerm_eq_gram_integrand
    cutoffTwoHalfCoupling hrefHalf translatedSingleFaceBoundary_mem
    translatedSingleFaceLower_mem
  have hfactor :
      centralPositiveCompletionWeight cutoffTwoHalfCoupling 2 1
          (lowSpinCentralReferenceState 0)
          (translatedSingleFaceLower, translatedSingleFaceBoundary) ≈
        centralBoundaryWeight cutoffTwoHalfCoupling 2 1
            translatedSingleFaceBoundary *
          (centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              (lowSpinCentralReferenceState 0)
              translatedSingleFaceBoundary *
            centralHalfAmplitude cutoffTwoHalfCoupling 2 1
              translatedSingleFaceLower translatedSingleFaceBoundary) := by
    simpa only [centralPositiveCompletionWeight] using hgram
  refine Q'.eqv_trans _ _ _ hfactor ?_
  refine Q'.eqv_trans _
    (centralBoundaryWeight cutoffTwoHalfCoupling 2 1
      translatedSingleFaceBoundary *
        (0 * centralHalfAmplitude cutoffTwoHalfCoupling 2 1
          translatedSingleFaceLower translatedSingleFaceBoundary)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        translatedSingleFaceReferenceAmplitude_eqv_zero)
  · exact Q'.eqv_trans _
      (centralBoundaryWeight cutoffTwoHalfCoupling 2 1
        translatedSingleFaceBoundary * 0) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.zero_mul_eqv _))
      (Q'.mul_zero_eqv _)

theorem fixedHalfSpinOneRawRow_cutoffTwoHalfCoupling_pos :
    (0 : Q') <
      fixedHalfSpinOneRawRow cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 := by
  simpa only [fixedHalfSpinOneRawRow] using
    (centralPhysicalPositiveRawRowMass_pos
      (centralLowerSpinCubeState_mem_centralPositiveHalfStates
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        (by decide : 1 ≤ 2)))

/-- The full literal completion-column Harnack structure is impossible at the
translated cutoff-two datum, for every proposed ceiling. -/
theorem no_cutoffTwoHalfOneCompletionColumnCrossBound
    (ceiling : Q') :
    CoarseGrowingCompletionColumnCrossBound
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 (by decide : 1 ≤ 2) 0 ceiling → False := by
  intro bound
  have hbound := bound.weighted_column_cross
    (translatedSingleFaceLower, translatedSingleFaceBoundary)
    translatedSingleFaceCompletion_mem
  have hleftPos :
      (0 : Q') <
        fixedHalfSpinOneRawRow cutoffTwoHalfCoupling
            (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 *
          growingCompletionColumnWeight cutoffTwoHalfCoupling 2 0
            (translatedSingleFaceLower, translatedSingleFaceBoundary) :=
    Q'.mul_pos fixedHalfSpinOneRawRow_cutoffTwoHalfCoupling_pos
      translatedSingleFaceCompletionColumn_pos
  have hrightZero :
      ceiling *
          (centralPositiveCompletionWeight cutoffTwoHalfCoupling 2 1
              (lowSpinCentralReferenceState 0)
              (translatedSingleFaceLower, translatedSingleFaceBoundary) *
            fixedHalfPhysicalPartition cutoffTwoHalfCoupling 2) ≈
        0 := by
    refine Q'.eqv_trans _
      (ceiling *
        (0 * fixedHalfPhysicalPartition cutoffTwoHalfCoupling 2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          translatedSingleFaceReferenceCompletion_eqv_zero)
    · exact Q'.eqv_trans _ (ceiling * 0) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.zero_mul_eqv _))
        (Q'.mul_zero_eqv _)
  have hnonpositive :=
    Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hrightZero)
  exact (Int.not_lt_of_ge hnonpositive) hleftPos

/-- The equivalent physical-fiber formulation of the same coarse repair is
also impossible at the translated datum. -/
theorem no_cutoffTwoHalfOneGrowingPhysicalFiberCrossBound
    (ceiling : Q') :
    CoarseGrowingPhysicalFiberCrossBound
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 (by decide : 1 ≤ 2) 0 ceiling → False := by
  intro bound
  exact no_cutoffTwoHalfOneCompletionColumnCrossBound ceiling
    (BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.CoarseGrowingPhysicalFiberCrossBound.toCompletionColumnCrossBound
      bound)

/-- Consequently the canonical coarse raw-partition repair package cannot be
inhabited at this datum either. -/
theorem no_cutoffTwoHalfOneCanonicalRawPartitionFiberBound
    (ceiling : Q') :
    CoarseCanonicalRawPartitionFiberBound
        cutoffTwoHalfCoupling
        (by decide : (0 : Q') < cutoffTwoHalfCoupling)
        2 (by decide : 1 ≤ 2) 0 ceiling → False := by
  intro bound
  exact no_cutoffTwoHalfOneGrowingPhysicalFiberCrossBound ceiling
    (BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.CoarseCanonicalRawPartitionFiberBound.toGrowingPhysicalFiberCrossBound
      bound)

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceBoundaryWeight_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceCompletionColumn_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceReferenceCompletion_eqv_zero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.no_cutoffTwoHalfOneCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.no_cutoffTwoHalfOneGrowingPhysicalFiberCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.no_cutoffTwoHalfOneCanonicalRawPartitionFiberBound
