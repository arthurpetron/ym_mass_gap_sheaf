/-
# Exact cutoff-one evaluation frontier for the two five-cycle BF4 Haar moments

The 116-link-to-five-cycle theorem reduces the two moments to fivefold Haar
integrals.  `BF4CutoffOneBinarySurfaceCertificate` independently evaluates
the finite 128-surface sum, while `BF4CutoffOneBinarySurfaceEmbedding` checks
those surfaces against the literal 72-face/116-link slab incidence kernel.
This module states the remaining geometric bridge explicitly and proves the
closed forms conditional on that bridge.

The bridge is deliberately not inhabited here.  It packages the still-open
constructive proof that (1) cutoff-one character expansion reindexes the
fivefold Haar integral by the rank-seven closed surfaces and (2) each closed
surface has the topological amplitude used by the finite certificate.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
`noncomputable` declaration.  The uninhabited bridge is an explicit theorem
hypothesis, not an axiom or an assumed global instance.
-/

import YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
import YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding

namespace YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- Honest residual interface between the fivefold Haar expressions and the
independently checked binary-surface sum.  Constructing a value of this type
is precisely the remaining finite geometric argument. -/
structure CutoffOneBinarySurfaceHaarBridge : Prop where
  vacuumRowSurfaceExpansion : ∀ w : Q',
    quaternionHaar 5
        (exactVacuumRowBasedCycleFivePolynomialCutoffOne w) ≈
      QPoly.eval vacuumRowSurfaceHeatPolynomial w
  constantSurfaceExpansion : ∀ w : Q',
    quaternionHaar 5
        (exactConstantMomentBasedCycleFivePolynomialCutoffOne w) ≈
      QPoly.eval constantSurfaceHeatPolynomial w

/-- Under the explicit surface-expansion bridge, the cutoff-one vacuum row is
exactly `R(w) = 1 + 4w^18`. -/
theorem exactVacuumRightConstantCrossMoment_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    exactVacuumRightConstantCrossMoment w 1 ≈
      QPoly.eval expectedVacuumRowHeatPolynomial w := by
  have hsurface := bridge.vacuumRowSurfaceExpansion w
  rw [vacuumRowSurfaceHeatPolynomial_closedForm] at hsurface
  exact Q'.eqv_trans _ _ _
    (exactVacuumRightConstantCrossMoment_cutoffOne_eq_basedCycleFiveHaar w)
    hsurface

/-- Under the explicit surface-expansion bridge, the cutoff-one constant
moment is
`C(w) = 1 + 32w^18 + 96w^30 + 224w^36 + 192w^42 + 3w^48`. -/
theorem exactConstantQuadraticMoment_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    exactConstantQuadraticMoment w 1 ≈
      QPoly.eval expectedConstantHeatPolynomial w := by
  have hsurface := bridge.constantSurfaceExpansion w
  rw [constantSurfaceHeatPolynomial_closedForm] at hsurface
  exact Q'.eqv_trans _ _ _
    (exactConstantQuadraticMoment_cutoffOne_eq_basedCycleFiveHaar w)
    hsurface

private theorem q_num_pos_of_pos {value : Q'} (hvalue : (0 : Q') < value) :
    0 < value.num := by
  have h :
      (0 : Int) * (value.den : Int) < value.num * (1 : Int) := hvalue
  simpa using h

private theorem q_lt_of_sub_pos {left right : Q'}
    (hsub : (0 : Q') < right + (-left)) : left < right := by
  have hnum : (0 : Int) < (right + (-left)).num :=
    q_num_pos_of_pos hsub
  show left.num * (right.den : Int) < right.num * (left.den : Int)
  change (0 : Int) <
    right.num * (left.den : Int) + (-left.num) * (right.den : Int) at hnum
  rw [Int.neg_mul] at hnum
  omega

/-- Conditional on the one honest surface-expansion bridge, the constant
Haar-five value is strictly larger than the vacuum-row value for every
positive heat coordinate. -/
theorem exactVacuumRow_lt_exactConstant_cutoffOne
    (bridge : CutoffOneBinarySurfaceHaarBridge)
    (w : Q') (hw : (0 : Q') < w) :
    exactVacuumRightConstantCrossMoment w 1 <
      exactConstantQuadraticMoment w 1 := by
  have hrow :=
    exactVacuumRightConstantCrossMoment_cutoffOne_closedForm bridge w
  have hconstant :=
    exactConstantQuadraticMoment_cutoffOne_closedForm bridge w
  have hclosed := haarFiveDifferenceHeatPolynomial_closedForm w
  have hpositiveExpected :=
    expectedHaarFiveDifferenceHeatPolynomial_positive w hw
  have hpositiveDifference :
      (0 : Q') < QPoly.eval haarFiveDifferenceHeatPolynomial w :=
    Q'.pos_of_lt_of_le hpositiveExpected (Q'.ge_of_eqv hclosed)
  have hsub := QPoly.eval_psub
    expectedConstantHeatPolynomial expectedVacuumRowHeatPolynomial w
  have hmomentSub :
      (QPoly.eval haarFiveDifferenceHeatPolynomial w).eqv
        (exactConstantQuadraticMoment w 1 +
          (-exactVacuumRightConstantCrossMoment w 1)) :=
    Q'.eqv_trans _ _ _ hsub
      (QPoly.q_add_congr
        (Q'.eqv_symm hconstant)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hrow)))
  exact q_lt_of_sub_pos
    (Q'.pos_of_lt_of_le hpositiveDifference (Q'.le_of_eqv hmomentSub))

/-- Conditional on the surface bridge, the centered cutoff-one numerator is
the exact five-term polynomial `C(w) - R(w)^2`. -/
theorem exactCenteredVacuumNumerator_cutoffOne_closedForm
    (bridge : CutoffOneBinarySurfaceHaarBridge) (w : Q') :
    (exactConstantQuadraticMoment w 1 +
      -(exactVacuumRightConstantCrossMoment w 1 *
        exactVacuumRightConstantCrossMoment w 1)).eqv
      (QPoly.eval expectedCenteredNumeratorHeatPolynomial w) := by
  have hrow :=
    exactVacuumRightConstantCrossMoment_cutoffOne_closedForm bridge w
  have hconstant :=
    exactConstantQuadraticMoment_cutoffOne_closedForm bridge w
  have hrowSquare :
      (exactVacuumRightConstantCrossMoment w 1 *
        exactVacuumRightConstantCrossMoment w 1).eqv
      (QPoly.eval expectedVacuumRowHeatPolynomial w *
        QPoly.eval expectedVacuumRowHeatPolynomial w) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hrow)
      (Q'.mul_eqv_congr_left _ _ _ hrow)
  have hactual :
      (exactConstantQuadraticMoment w 1 +
        -(exactVacuumRightConstantCrossMoment w 1 *
          exactVacuumRightConstantCrossMoment w 1)).eqv
      (QPoly.eval expectedConstantHeatPolynomial w +
        -(QPoly.eval expectedVacuumRowHeatPolynomial w *
          QPoly.eval expectedVacuumRowHeatPolynomial w)) :=
    QPoly.q_add_congr hconstant
      (Q'.neg_eqv_congr _ _ hrowSquare)
  have hpolynomial :
      (QPoly.eval centeredNumeratorHeatPolynomial w).eqv
      (QPoly.eval expectedConstantHeatPolynomial w +
        -(QPoly.eval expectedVacuumRowHeatPolynomial w *
          QPoly.eval expectedVacuumRowHeatPolynomial w)) :=
    Q'.eqv_trans _ _ _
      (QPoly.eval_psub expectedConstantHeatPolynomial
        (QPoly.pmul expectedVacuumRowHeatPolynomial
          expectedVacuumRowHeatPolynomial) w)
      (QPoly.q_add_congr (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _
          (QPoly.eval_pmul expectedVacuumRowHeatPolynomial
            expectedVacuumRowHeatPolynomial w)))
  exact Q'.eqv_trans _ _ _ hactual
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hpolynomial)
      (centeredNumeratorHeatPolynomial_closedForm w))

/-- Hence the actual centered cutoff-one numerator is strictly positive at
every positive heat coordinate, conditional only on the explicit bridge. -/
theorem exactCenteredVacuumNumerator_cutoffOne_positive
    (bridge : CutoffOneBinarySurfaceHaarBridge)
    (w : Q') (hw : (0 : Q') < w) :
    (0 : Q') <
      exactConstantQuadraticMoment w 1 +
        -(exactVacuumRightConstantCrossMoment w 1 *
          exactVacuumRightConstantCrossMoment w 1) := by
  have hclosed :=
    exactCenteredVacuumNumerator_cutoffOne_closedForm bridge w
  exact Q'.pos_of_lt_of_le
    (expectedCenteredNumeratorHeatPolynomial_positive w hw)
    (Q'.le_of_eqv (Q'.eqv_symm hclosed))

/-- The exact centered numerator polynomial forced by the two closed forms. -/
theorem cutoffOne_centeredNumerator_closedForm (w : Q') :
    (QPoly.eval
      (QPoly.psub expectedConstantHeatPolynomial
        (QPoly.pmul expectedVacuumRowHeatPolynomial
          expectedVacuumRowHeatPolynomial)) w).eqv
      (QPoly.eval expectedCenteredNumeratorHeatPolynomial w) :=
  centeredNumeratorHeatPolynomial_closedForm w

/-- The cross-multiplied discrepancy between the signed and physically
normalized centered moments is exactly `(C - 1)(C - R²)`, with its checked
ten-term nonnegative polynomial expansion. -/
theorem cutoffOne_centeredNormalizationDefect_closedForm (w : Q') :
    (QPoly.eval
      (QPoly.pmul
        (QPoly.psub expectedConstantHeatPolynomial [1])
        expectedCenteredNumeratorHeatPolynomial) w).eqv
      (QPoly.eval expectedCenteredNormalizationDefectHeatPolynomial w) :=
  centeredNormalizationDefectHeatPolynomial_closedForm w

end YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation

#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactVacuumRightConstantCrossMoment_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactConstantQuadraticMoment_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactVacuumRow_lt_exactConstant_cutoffOne
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactCenteredVacuumNumerator_cutoffOne_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.exactCenteredVacuumNumerator_cutoffOne_positive
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOne_centeredNumerator_closedForm
#print axioms YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation.cutoffOne_centeredNormalizationDefect_closedForm
