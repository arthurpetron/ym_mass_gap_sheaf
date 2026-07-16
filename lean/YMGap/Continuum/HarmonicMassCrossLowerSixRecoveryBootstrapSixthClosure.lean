/-
# Physical closure of the sixth exact lower-six recovery tranche

The replayed recovery certificates prove the growing lower-six residual
unconditionally through scale `647`.  The sharp Pascal sandwich consumes the
next-scale lower residual, so this module records the exact physical content:
the coefficient-two mass cross and the located harmonic GNS step through
scale `646`.  No sampled constant enters these statements.
-/

import YMGap.Continuum.HarmonicGNSMarginRecursion
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth
import YMGap.Continuum.HarmonicMassCrossPascalReduction

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGNSMarginRecursion
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixth
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicTrueMarginStep
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.SummableInverseSquare

/-- The exact recovery replay proves the sharp physical Pascal cross at every
scale below `647`; the one-scale offset is the lower sandwich's use of
`GrowingResidualLowerSix (k + 1)`. -/
theorem physicalPascalCrossResidual_below_sixFortySeven
    {k : Nat} (hk : k < 647) :
    PhysicalPascalCrossResidual k := by
  by_cases hsmall : k < 9
  · exact physicalPascalCrossResidual_below_nine hsmall
  · apply physicalPascalCrossResidual_of_six_eight (by omega)
      (physicalResidualUpperEight_all k)
    exact physicalResidualLowerSix_of_growing (by omega)
      (growingResidualLowerSix_below_sixFortyEight
        (k := k + 1) (by omega) (by omega))

/-- Unconditional coefficient-two harmonic mass cross on the replayed
physical range. -/
theorem harmonicMassCross_le_two_invSq_below_sixFortySeven
    (k : Nat) (hk : k < 647) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) :=
  harmonicMassCross_le_two_invSq_of_physicalPascalCross k
    (physicalPascalCrossResidual_below_sixFortySeven hk)

/-- Every located harmonic character-GNS margin step below scale `647` is
already unconditional, independently of the remaining symbolic tail proof. -/
theorem harmonicGNSMargin_singleStep_below_sixFortySeven
    (k : Nat) (hk : k < 647) :
    ((1 : Q') - BondMovingQuadratic.bondMovingDeltaRen 1
        UniformCouplingFromAF.pMult
          (HarmonicCutoffBoundary.harmW k)) *
        harmonicGNSMargin k ≤ harmonicGNSMargin (k + 1) := by
  rw [harmonicGNSMargin_eq_trueMargin,
    harmonicGNSMargin_eq_trueMargin]
  exact HarmonicTrueMarginAbsorption.harmonicTrueMargin_singleStep_of_mass_drop k
    (harmonicMass_drop_le_two_invSq_of_cross k
      (harmonicMassCross_le_two_invSq_below_sixFortySeven k hk))

#print axioms physicalPascalCrossResidual_below_sixFortySeven
#print axioms harmonicMassCross_le_two_invSq_below_sixFortySeven
#print axioms harmonicGNSMargin_singleStep_below_sixFortySeven

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryBootstrapSixthClosure
