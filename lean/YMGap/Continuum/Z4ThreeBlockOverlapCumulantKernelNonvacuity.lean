/-
# Non-vacuity of the three-block cumulant kernel

The generic overlap construction is instantiated on the correlated even-parity
law used by its cubic obstruction.  Thus the exact positive coupling is not
merely conditional on an uninhabited finite-law package.
-/

import YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

namespace YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernelNonvacuity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

local infix:50 " ≈ " => Q'.eqv

theorem minimalEvenParityMass_nonnegative (state : MinimalParityState) :
    (0 : Q') ≤ minimalEvenParityMass state := by
  rcases state with ⟨left, shared, right⟩
  cases left <;> cases shared <;> cases right <;> decide

/-- The correlated even-parity measure is an actual three-block finite law. -/
def minimalEvenParityLaw : ThreeBlockOverlapFiniteLaw MinimalParityState where
  mass := minimalEvenParityMass
  states := minimalParityStateSpace
  leftParameter := minimalParityHalf
  sharedParameter := minimalParityHalf
  rightParameter := minimalParityHalf
  leftEvent := minimalParityLeftEvent
  sharedEvent := minimalParitySharedEvent
  rightEvent := minimalParityRightEvent
  mass_nonnegative := minimalEvenParityMass_nonnegative
  left_nonnegative := by decide
  left_le_one := by decide
  shared_nonnegative := by decide
  shared_le_one := by decide
  right_nonnegative := by decide
  right_le_one := by decide
  left_mass := minimalEvenParity_left_mass
  shared_mass := minimalEvenParity_shared_mass
  right_mass := minimalEvenParity_right_mass
  normalized := minimalEvenParityMass_normalized

theorem minimalEvenParityLaw_thirdMoment_eqv_neg_eighth :
    overlapThirdMoment minimalEvenParityLaw ≈ -minimalParityEighth := by
  exact minimalEvenParity_thirdMoment_eqv_neg_eighth

/-- A concrete non-product, positive three-block coupling with both marginals
equal to the even-parity law. -/
def minimalEvenParityThreeBlockCoupling :
    PositiveFiniteConfigurationCoupling
      minimalEvenParityMass minimalParityStateSpace
      minimalEvenParityMass minimalParityStateSpace
      (threeBlockOverlapJointMass minimalEvenParityLaw minimalEvenParityLaw) :=
  threeBlockOverlapPositiveFiniteConfigurationCoupling
    minimalEvenParityLaw minimalEvenParityLaw

theorem minimalEvenParityThreeBlockKernel_nonnegative
    (source target : MinimalParityState) :
    (0 : Q') ≤ threeBlockOverlapConfigurationKernel
      minimalEvenParityLaw minimalEvenParityLaw threeBlockOverlapEpsilon
      source target := by
  exact threeBlockOverlapConfigurationKernel_nonnegative
    minimalEvenParityLaw minimalEvenParityLaw source target

theorem minimalEvenParityThreeBlockJoint_normalized :
    listQSum
        (fun source => listQSum
          (threeBlockOverlapJointMass minimalEvenParityLaw
            minimalEvenParityLaw source)
          minimalParityStateSpace)
        minimalParityStateSpace ≈ 1 := by
  exact threeBlockOverlapJointMass_normalized
    minimalEvenParityLaw minimalEvenParityLaw

#print axioms minimalEvenParityMass_nonnegative
#print axioms minimalEvenParityLaw_thirdMoment_eqv_neg_eighth
#print axioms minimalEvenParityThreeBlockCoupling
#print axioms minimalEvenParityThreeBlockKernel_nonnegative
#print axioms minimalEvenParityThreeBlockJoint_normalized

end YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernelNonvacuity
