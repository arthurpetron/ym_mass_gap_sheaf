/-
# Exact quaternion translation moments through degree five

These two finite kernel checks cover every exponent quadruple of total degree
at most five for both left and right quaternion multiplication.  They are
kept in a small standalone module so downstream structural degree proofs do
not recompute the tables while being developed.

## Axiom gate

Decidable exact rational-polynomial normalization only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

namespace YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

theorem leftTranslationMomentChecksThrough_five :
    translationMomentChecksThrough leftTranslationMomentCheck 5 = true := by
  decide

theorem rightTranslationMomentChecksThrough_five :
    translationMomentChecksThrough rightTranslationMomentCheck 5 = true := by
  decide

end YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive

#print axioms YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive.leftTranslationMomentChecksThrough_five
#print axioms YMGap.Continuum.SU2QuaternionTranslationMomentDegreeFive.rightTranslationMomentChecksThrough_five
