/-
# Semantic low-mode evaluation of the exact septic certificate

The closed coefficient table for modes `0,...,7` is converted here from a
syntactic normal-form fact into the pointwise nonnegativity statement it was
designed to certify.  The only live variable is the nonnegative scale slack
`X` in `D = 8191 + X`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerLowEvaluation

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

/-- The one-variable evaluation environment for `D = 8191 + X`. -/
def lowEnvironment (X : Q') (i : Nat) : Q' := if i = 0 then X else 0

private theorem lowEnvironment_nonnegative (X : Q') (hX : (0 : Q') ≤ X) :
    ∀ i, (0 : Q') ≤ lowEnvironment X i := by
  intro i
  unfold lowEnvironment
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact hX
  · rw [if_neg hi]
    exact Q'.le_refl' 0

private theorem lowModeCertificate {n : Nat} (hn : n ≤ 7) :
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow n)) = true := by
  have hall := pExactLowerLow_coefficients_nonnegative
  have hcases :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
      n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h
  · subst n
    exact hall.1
  · subst n
    exact hall.2.1
  · subst n
    exact hall.2.2.1
  · subst n
    exact hall.2.2.2.1
  · subst n
    exact hall.2.2.2.2.1
  · subst n
    exact hall.2.2.2.2.2.1
  · subst n
    exact hall.2.2.2.2.2.2.1
  · subst n
    exact hall.2.2.2.2.2.2.2

/-- The cleared exact-error numerator is nonnegative for every low mode and
every production-scale slack `X ≥ 0`. -/
theorem pExactLowerLow_eval_nonnegative {n : Nat} (hn : n ≤ 7)
    (X : Q') (hX : (0 : Q') ≤ X) :
    (0 : Q') ≤ RingNormaliser.eval (lowEnvironment X) (pExactLowerLow n) :=
  eval_nonneg_of_fast_coefficients
    (lowEnvironment_nonnegative X hX) (lowModeCertificate hn)

#print axioms pExactLowerLow_eval_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerLowEvaluation
