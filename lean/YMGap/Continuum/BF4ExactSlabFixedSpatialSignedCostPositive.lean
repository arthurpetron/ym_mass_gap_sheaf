/-
# Nonnegative JOINT signed remainder for the original finite test family

Use one-sided, not jump, insertions in the existing positive quadratic.
The one-erasure flow matches the SAME corrected-sum norm in nu. Completing
the square proves marginalCost >= h*||S||_nu^2 and therefore D+2hR>=0.

Individual determinant crosses remain signed. No exact reciprocal, centering
of the supplied q_i, limiting producer, volume-uniform upper budget, or
spectral gap is assumed or established. This is the positivity needed to
test whether separated inactive-coordinate costs can be cancelled.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOneSidedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSignedCostPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalPair dualTest_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (endpointWeight fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels labels_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals (marginalCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
open YMGap.Continuum.BF4ExactSlabFixedSpatialDiagonalCost (correctedTest_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (sum_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOneSidedFamily
open YMGap.Continuum.BF4ExactSlabFixedSpatialCostFringeSplit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (qListSum)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight activeBlocks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

/-- The original finite cost dominates the SAME corrected-sum norm. No
conditional-centering hypothesis or positivity of that norm is needed. -/
theorem corrected_cost_norm_floor (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (hq : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    headFloor w * marginalPair w K width n
      (correctedSum hw0 hw1 K width hK n qs degrees)
      (correctedSum hw0 hw1 K width hK n qs degrees) ≤
      marginalCost w K width n (finiteTests hw0 hw1 K width hK n qs degrees) := by
  let tests := finiteTests hw0 hw1 K width hK n qs degrees
  let s := correctedSum hw0 hw1 K width hK n qs degrees
  have ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i) := by
    intro i hi
    dsimp only [tests, finiteTests]
    by_cases ha : i ∈ activeBlocks width
    · rw [if_pos ha]
      exact dualTest_supported hw0 hw1 K width hK n i (hq i hi) (degrees i)
    · rw [if_neg ha]
      exact hq i hi
  have hs : SupportedQuaternionBlocks (N width) s := by
    apply sum_supported
    intro i hi
    unfold corrected
    by_cases ha : i ∈ activeBlocks width
    · rw [if_pos ha]
      exact correctedTest_supported hw0 hw1 K width hK n i (hq i (labels_lt width i hi)) (degrees i)
    · rw [if_neg ha]
      exact hq i (labels_lt width i hi)
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  let A := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have M : Certificate (N width+N width) (endpointWeight w K width n) :=
    (certificate_extend (N width) ha A).mul (lift_certificate (N width) A)
  have hnorm := oneSidedFamily_square_pin w K width n tests s
  have hflow := Q'.eqv_trans _ _ _ (oneSidedFamily_flow_pin w K width n tests s)
    (flow_actual_pin hw0 hw1 K width hK n qs degrees s)
  have hmatch := Q'.eqv_trans _ _ _ hflow (Q'.eqv_symm hnorm)
  have h := finite_family_completed_square (headFloor_positive hw0 hw1)
    (oneSidedFamily w K width tests)
    (oneSidedFamily_floorCertificates hw0 hw1 K width hK tests)
    (oneSidedFamily_tests_supported w K width tests ht)
    M (lift_supported hs (N width)) hmatch
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hnorm))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (oneSidedFamily_cost_pin w K width n tests)))

/-- Only the combined remainder has this sign; individual determinant
cross terms are still signed and no upper coercivity budget follows. -/
theorem joint_remainder_nonnegative (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (hq : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    (0 : Q') ≤ diagonalRemainder hw0 hw1 K width hK n qs degrees +
      ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees := by
  have h := Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _
    (corrected_cost_norm_floor hw0 hw1 K width hK n qs degrees hq)
    (Q'.le_of_eqv (cost_actual_split hw0 hw1 K width hK n qs degrees)))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 0)))
      (.add (.var 1) (.var 2)) (by decide)
      (fun
        | 0 => headFloor w*marginalPair w K width n
            (correctedSum hw0 hw1 K width hK n qs degrees)
            (correctedSum hw0 hw1 K width hK n qs degrees)
        | 1 => diagonalRemainder hw0 hw1 K width hK n qs degrees
        | _ => ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees)))

/-- Determinant cancellation cannot pay for the original inactive-coordinate
norms: fringe determinant crosses vanish, and the remaining active joint cost
is nonnegative.
This applies to the actual finite seed family but asserts no approximation
after removing fringe tests and no growth of this lower bound with width. -/
theorem fringe_norm_cost_lower_bound (qs : Nat → RatPoly) (degrees : Nat → Nat)
    (hq : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (qs i)) :
    ((1 : Q') + -(headFloor w)) * qListSum ((fringeBlocks width).map
      (fun i => marginalPair w K width n (qs i) (qs i))) ≤
      diagonalRemainder hw0 hw1 K width hK n qs degrees +
        ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees := by
  let qa := activeTests width qs
  let A := diagonalRemainder hw0 hw1 K width hK n qa degrees
  let B := ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qa degrees
  let F := ((1 : Q') + -(headFloor w)) * qListSum ((fringeBlocks width).map
    (fun i => marginalPair w K width n (qs i) (qs i)))
  have ha : (0 : Q') ≤ A+B := joint_remainder_nonnegative hw0 hw1 K width hK n qa degrees
    (activeTests_supported width qs hq)
  have he : diagonalRemainder hw0 hw1 K width hK n qs degrees +
      ((2 : Q')*headFloor w)*determinantRemainder hw0 hw1 K width hK n qs degrees ≈ (A+B)+F := by
    rw [← determinantRemainder_activeTests hw0 hw1 K width hK n qs degrees]
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (diagonalRemainder_split hw0 hw1 K width hK n qs degrees) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 2)) (.var 1))
        (.add (.add (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => A | 1 => B | _ => F))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg F (A+B) ha)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv F (A+B))) (Q'.ge_of_eqv he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSignedCostPositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedCostPositive.corrected_cost_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedCostPositive.joint_remainder_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSignedCostPositive.fringe_norm_cost_lower_bound
