/-
# Positive-row certificate for the translated cutoff-two cell

The transported full-slab term is strictly positive.  Therefore its concrete
lower restriction cannot be excluded by the positive-row carrier: exclusion
would force the whole physical term to vanish.  This file isolates that
argument so downstream obstruction assembly treats the large translated
labelling opaquely.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakageCertificate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairPositiveBoundaryAmplitude
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

theorem translatedSingleFaceSlab_mem_partition :
    translatedSingleFaceSlab ∈ centralPhysicalPartitionStates 2 1 := by
  simpa only [centralPhysicalPartitionStates] using
    translatedSingleFaceSlab_mem

theorem translatedSingleFaceLower_rowMarginal_pos :
    (0 : Q') <
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 1 translatedSingleFaceLower := by
  apply CReal.pos_of_num_pos
  apply Int.lt_of_not_ge
  intro hrowNumNonpos
  have hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 1 translatedSingleFaceLower := by
    intro hpos
    exact (Int.not_lt_of_ge hrowNumNonpos) (Q'.num_pos_of_pos hpos)
  have hzero :=
    centralPhysicalPartitionWeight_eqv_zero_of_lower_not_pos
      translatedSingleFaceSlab_mem_partition (by
        simpa only [translatedSingleFaceLower] using hnot)
  have hnonpositive :
      slabParametricKPhysicalTerm cutoffTwoHalfCoupling 2 3
          translatedSingleFaceSlab ≤
        0 := by
    exact Q'.le_of_eqv (by
      simpa only [centralPhysicalPartitionWeight] using hzero)
  exact (Int.not_lt_of_ge hnonpositive) translatedSingleFaceTerm_pos

theorem translatedSingleFaceLower_mem_positive :
    translatedSingleFaceLower ∈
      centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 1 := by
  exact mem_centralPositiveHalfStates_iff.mpr
    ⟨translatedSingleFaceLower_mem,
      translatedSingleFaceLower_rowMarginal_pos⟩

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceLower_rowMarginal_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceLower_mem_positive
