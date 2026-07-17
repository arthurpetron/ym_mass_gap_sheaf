/-
# Semantic evaluation of the recentered exact low-mode certificate
-/

import YMGap.Continuum.HarmonicLowerSixExactLow390CoefficientCertificate

namespace YMGap.Continuum.HarmonicLowerSixExactLow390Evaluation

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixExactLow390CoefficientCertificate

/-- Evaluation environment for the nonnegative slack in `D = 392 + X`. -/
def low390Environment (X : Q') (i : Nat) : Q' :=
  if i = 0 then X else 0

private theorem low390Environment_nonnegative
    (X : Q') (hX : (0 : Q') ≤ X) :
    ∀ i, (0 : Q') ≤ low390Environment X i := by
  intro i
  unfold low390Environment
  by_cases hi : i = 0
  · rw [if_pos hi]
    exact hX
  · rw [if_neg hi]
    exact Q'.le_refl' 0

private theorem low390ModeCertificate {n : Nat} (hn : n ≤ 7) :
    RawCoefficientsNonnegative
      (fastNormalize (pExactLowerLow390 n)) = true := by
  have hall := pExactLowerLow390_coefficients_nonnegative
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

/-- The recentered cleared numerator evaluates nonnegatively for every
`X ≥ 0` and every mode `n ≤ 7`. -/
theorem pExactLowerLow390_eval_nonnegative {n : Nat} (hn : n ≤ 7)
    (X : Q') (hX : (0 : Q') ≤ X) :
    (0 : Q') ≤
      RingNormaliser.eval (low390Environment X) (pExactLowerLow390 n) :=
  eval_nonneg_of_fast_coefficients
    (low390Environment_nonnegative X hX) (low390ModeCertificate hn)

#print axioms pExactLowerLow390_eval_nonnegative

end YMGap.Continuum.HarmonicLowerSixExactLow390Evaluation
