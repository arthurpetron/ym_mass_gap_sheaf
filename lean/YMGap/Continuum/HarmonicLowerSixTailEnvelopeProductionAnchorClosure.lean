/-
# Unconditional production tail from the exact scale-8189 anchor

The generated Base/E8/E9 certificate supplies every adjacent-scale step from
`k = 8189` onward.  The finite recovery calculation supplies exactly the
interior sign at that first scale.  This file performs the load-bearing splice
and immediately transports it to the physical Pascal cross and harmonic mass
cross consumers on the corresponding high-scale tail.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionStep
import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
import YMGap.Continuum.HarmonicMassCrossResidualSandwich
import YMGap.Continuum.HarmonicMassCrossPascalReduction
import YMGap.Continuum.HarmonicGNSMarginRecursion

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionAnchorClosure

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionStep
open YMGap.Continuum.HarmonicGNSMarginRecursion
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTerminal8189
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.SummableInverseSquare

/-- The exact terminal recovery sign closes the generated production
induction without a remaining anchor hypothesis. -/
theorem growingResidualLowerSix_production
    {k : Nat} (hk : 8189 ≤ k) :
    GrowingResidualLowerSix k :=
  growingResidualLowerSix_production_of_anchor hk
    lowerSixInteriorPayment_8189_nonnegative

/-- First downstream physical consumer: the sharp Pascal cross is now
unconditional from scale 8188 onward. -/
theorem physicalPascalCrossResidual_production
    {k : Nat} (hk : 8188 ≤ k) :
    PhysicalPascalCrossResidual k := by
  apply physicalPascalCrossResidual_of_six_eight (by omega)
    (physicalResidualUpperEight_all k)
  exact physicalResidualLowerSix_of_growing (by omega)
    (growingResidualLowerSix_production (k := k + 1) (by omega))

/-- The coefficient-two harmonic mass cross reaches the production tail. -/
theorem harmonicMassCross_le_two_invSq_production
    {k : Nat} (hk : 8188 ≤ k) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) :=
  harmonicMassCross_le_two_invSq_of_physicalPascalCross k
    (physicalPascalCrossResidual_production hk)

/-- The exact GNS-margin `singleStep` inequality is therefore unconditional
on the production tail as well. -/
theorem harmonicGNSMargin_singleStep_production
    {k : Nat} (hk : 8188 ≤ k) :
    ((1 : Q') - BondMovingQuadratic.bondMovingDeltaRen 1
        UniformCouplingFromAF.pMult (HarmonicCutoffBoundary.harmW k)) *
        harmonicGNSMargin k ≤
      harmonicGNSMargin (k + 1) := by
  rw [harmonicGNSMargin_eq_trueMargin,
    harmonicGNSMargin_eq_trueMargin]
  exact HarmonicTrueMarginAbsorption.harmonicTrueMargin_singleStep_of_mass_drop k
    (harmonicMass_drop_le_two_invSq_of_cross k
      (harmonicMassCross_le_two_invSq_production hk))

#print axioms growingResidualLowerSix_production
#print axioms physicalPascalCrossResidual_production
#print axioms harmonicMassCross_le_two_invSq_production
#print axioms harmonicGNSMargin_singleStep_production

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionAnchorClosure
