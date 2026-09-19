/-
# Root/vacuum versus non-root strict contraction on the pulled carrier

The fixed cutoff-two pulled carrier already has a constructive dichotomy for
each coefficient: either all non-root coordinates vanish, or an explicit
non-root coordinate has positive magnitude.  This module connects that
dichotomy to the existing same-carrier uniform rate.  Root-supported data are
annihilated by the moving root-centering map, while the non-root branch has a
strict form inequality at every later cutoff covered by the finite certificate.

This is still a fixed finite SU(2) carrier.  It is not a cofinal capacity
comparison, a completed vacuum-complement theorem for the physical family, an
OS/continuum construction, or a Clay result.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering

local infix:50 " ≈ " => Q'.eqv

/-- Root-supported coefficients are killed by the moving centering map in both
the pulled matrix and pulled diagonal, for every pair of cutoffs. -/
theorem rootSupported_centered_forms_eqv_zero
    {coefficient : Nat → Q'}
    (witness : CutoffTwoRootSupportedWitness coefficient)
    (lawCutoff centeringCutoff : Nat) :
    cutoffTwoPulledMatrixAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 ∧
      cutoffTwoPulledDiagonalAt lawCutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt
          centeringCutoff coefficient) ≈ 0 := by
  exact ⟨
    cutoffTwoRootSupported_movingMatrix_eqv_zero
      witness.supported lawCutoff centeringCutoff,
    cutoffTwoRootSupported_movingDiagonal_eqv_zero
      witness.supported lawCutoff centeringCutoff⟩

/-- An explicit non-root coordinate makes the centered later diagonal
strictly positive, and the existing uniform finite certificate then yields a
strict form inequality for that same centered coefficient. -/
theorem nonRoot_strict_form_gap
    {coefficient : Nat → Q'}
    (witness : CutoffTwoNonRootCoefficientWitness coefficient)
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later) :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) <
      cutoffTwoPulledDiagonalAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let centered := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let rate := cutoffTwoConstructedUniformGapData.rate
  let diagonal := cutoffTwoPulledDiagonalAt later centered
  have htwo : 2 ≤ later := by
    exact Nat.le_trans
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two hlater
  have hgap := cutoffTwoConstructedUniformGapData.moving_abs_gap
    later hlater centered
  have hdiag : (0 : Q') < diagonal := by
    exact CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos
      witness htwo
  have hrate : rate < (1 : Q') :=
    cutoffTwoConstructedUniformGapData.rate_lt_one
  have hscaled : rate * diagonal < (1 : Q') * diagonal :=
    mul_lt_mul_of_pos_right hdiag hrate
  have hscaled' : rate * diagonal < diagonal := by
    exact Q'.lt_of_le_of_lt hscaled
      (Q'.lt_of_eqv (Q'.one_mul_eqv diagonal))
  exact Q'.lt_of_le_of_lt hgap hscaled'

/-- The coefficientwise fixed-carrier split: root-supported data are
annihilated by centering, while the non-root branch supplies the strict form
gap at every later cutoff covered by the certificate. -/
theorem coefficient_centered_gap_split
    (coefficient : Nat → Q') :
    Sum
      (CutoffTwoRootSupportedWitness coefficient)
      (∀ witness : CutoffTwoNonRootCoefficientWitness coefficient,
        ∀ later : Nat,
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later →
          Q'.abs
              (cutoffTwoPulledMatrixAt later
                (cutoffTwoPulledMovingCenteredCoefficientAt
                  later coefficient)) <
            cutoffTwoPulledDiagonalAt later
              (cutoffTwoPulledMovingCenteredCoefficientAt
                later coefficient)) := by
  cases cutoffTwoRootSupported_orNonRootData coefficient with
  | inl witness =>
      exact Sum.inl witness
  | inr witness =>
      exact Sum.inr (fun selected later hlater =>
        nonRoot_strict_form_gap selected later hlater)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.rootSupported_centered_forms_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.nonRoot_strict_form_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumComplementDichotomy.coefficient_centered_gap_split
