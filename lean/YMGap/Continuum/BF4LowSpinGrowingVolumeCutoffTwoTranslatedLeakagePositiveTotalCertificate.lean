/-
# Positive retained-boundary total for the translated cutoff-two cell

The positive lower state occurs in the retained carrier, so its strictly
positive half-amplitude is bounded above by the full retained boundary sum.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakageHalfAmplitudeCertificate
import YMGap.Continuum.BF4PositiveBoundaryTotalPositivity

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PositiveBoundaryTotalPositivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination

theorem translatedSingleFaceBoundary_positiveTotal :
    (0 : Q') <
      centralPositiveBoundaryTotalHalfAmplitude cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 1 translatedSingleFaceBoundary := by
  exact centralPositiveBoundaryTotalHalfAmplitude_pos_of_mem
    translatedSingleFaceLower_mem_positive
    translatedSingleFaceLowerAmplitude_pos

end YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCutoffTwoTranslatedLeakage.translatedSingleFaceBoundary_positiveTotal
