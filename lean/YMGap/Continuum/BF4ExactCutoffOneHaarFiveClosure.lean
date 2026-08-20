/-
# Unconditional cutoff-one BF4 Haar-five closure

The cutoff-one character expansion and the 128 closed-surface Haar evaluation
were developed as independent constructive certificates.  This module composes
those two finished halves.  It therefore removes the former abstract
`CutoffOneBinarySurfaceHaarBridge` hypothesis from the exact cutoff-one moment
formulas.

This is a finite exact-Haar result only.  It does not identify the signed Haar
quadratic with the separately normalized positive physical kernel.

## Axiom gate

Composition of already-audited finite certificates only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge

namespace YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeBridge
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion

local infix:50 " ≈ " => Q'.eqv

/-- The actual pointwise BF4 surface evaluation, assembled into the two finite
surface sums needed by the vacuum-row and constant moments. -/
def actualBF4CutoffOneClosedSurfaceSumEvaluation :
    CutoffOneClosedSurfaceSumEvaluation :=
  cutoffOneClosedSurfaceSumEvaluation_of_topologicalAmplitude
    actualBF4HaarFiveSurfaceBridge

/-- The unconditional cutoff-one Haar-five bridge: the literal 116-link
character expansion is reindexed over the certified 128 closed surfaces, and
every surviving surface is evaluated by the actual forest-gauge theorem. -/
def actualBF4CutoffOneBinarySurfaceHaarBridge :
    CutoffOneBinarySurfaceHaarBridge :=
  cutoffOneBinarySurfaceHaarBridge_of_parts
    cutoffOneCharacterExpansionReindex
    actualBF4CutoffOneClosedSurfaceSumEvaluation

/-- The actual cutoff-one vacuum row is exactly `R(w) = 1 + 4 w^18`. -/
theorem exactVacuumRightConstantCrossMoment_cutoffOne_actual
    (w : Q') :
    exactVacuumRightConstantCrossMoment w 1 ≈
      QPoly.eval expectedVacuumRowHeatPolynomial w :=
  exactVacuumRightConstantCrossMoment_cutoffOne_closedForm
    actualBF4CutoffOneBinarySurfaceHaarBridge w

/-- The actual cutoff-one constant moment is exactly
`C(w) = 1 + 32 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48`. -/
theorem exactConstantQuadraticMoment_cutoffOne_actual
    (w : Q') :
    exactConstantQuadraticMoment w 1 ≈
      QPoly.eval expectedConstantHeatPolynomial w :=
  exactConstantQuadraticMoment_cutoffOne_closedForm
    actualBF4CutoffOneBinarySurfaceHaarBridge w

/-- The actual signed-Haar centered numerator has the checked closed form
`C(w) - R(w)^2`. -/
theorem exactCenteredVacuumNumerator_cutoffOne_actual
    (w : Q') :
    (exactConstantQuadraticMoment w 1 +
      -(exactVacuumRightConstantCrossMoment w 1 *
        exactVacuumRightConstantCrossMoment w 1)).eqv
      (QPoly.eval expectedCenteredNumeratorHeatPolynomial w) :=
  exactCenteredVacuumNumerator_cutoffOne_closedForm
    actualBF4CutoffOneBinarySurfaceHaarBridge w

/-- For every positive heat coordinate, the actual signed-Haar centered
cutoff-one numerator is strictly positive. -/
theorem exactCenteredVacuumNumerator_cutoffOne_actual_positive
    (w : Q') (hw : (0 : Q') < w) :
    (0 : Q') <
      exactConstantQuadraticMoment w 1 +
        -(exactVacuumRightConstantCrossMoment w 1 *
          exactVacuumRightConstantCrossMoment w 1) :=
  exactCenteredVacuumNumerator_cutoffOne_positive
    actualBF4CutoffOneBinarySurfaceHaarBridge w hw

end YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure

#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.actualBF4CutoffOneClosedSurfaceSumEvaluation
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.actualBF4CutoffOneBinarySurfaceHaarBridge
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.exactVacuumRightConstantCrossMoment_cutoffOne_actual
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.exactConstantQuadraticMoment_cutoffOne_actual
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.exactCenteredVacuumNumerator_cutoffOne_actual
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveClosure.exactCenteredVacuumNumerator_cutoffOne_actual_positive
