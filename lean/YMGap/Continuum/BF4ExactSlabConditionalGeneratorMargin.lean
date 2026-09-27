/-
# Explicit margin associated with the completed conditional-pair coefficient

The signed pair coefficient gives a nome-dependent candidate margin for a
subsequent ordered-generator argument. This file proves only its scalar
upper bound and the strict positivity at the exact small-nome pilot.
-/

import YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

namespace YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabTwoLinkResidualLowerBound
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

/-- The explicit scalar margin associated with fifty times the pair error. -/
def margin {w : Q'} (hd : heatRemainderBound w < (1 : Q')) : Q' :=
  1 + -(50 * pairCoefficient hd)

/-- The candidate margin never exceeds one when the nome is positive. -/
theorem margin_le_one {w : Q'} (hw : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) : margin hd ≤ (1 : Q') := by
  have he : (0 : Q') ≤ pairCoefficient hd := pairCoefficient_nonnegative hw hd
  have h50 : (0 : Q') ≤ 50 * pairCoefficient hd :=
    Q'.mul_nonneg _ _ (by decide) he
  unfold margin
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 (-(50 * pairCoefficient hd)) 0 (Q'.neg_le_neg h50))
    (by decide)

/-- At the exact nome `1/1024`, the candidate margin is strictly positive.
This is a kernel computation for the specified pilot, not a uniform-nome
positivity assertion. -/
theorem existingNome_margin_positive :
    (0 : Q') < margin (w := nome) existingNome_guards.2 := by
  decide

end YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin

#print axioms YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin.margin
#print axioms YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin.margin_le_one
#print axioms YMGap.Continuum.BF4ExactSlabConditionalGeneratorMargin.existingNome_margin_positive
