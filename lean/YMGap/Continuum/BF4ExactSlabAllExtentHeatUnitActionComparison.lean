/-
# The original unit norm and action integral have a vanishing cutoff mismatch

The common-form norm of the K-anchored full unit uses a computed interface
stage S(K), not K itself. The exact discrepancy is an ORIGINAL interface
product remainder between the two K-anchored boundary heat products.
Their cutoff-independent coefficient bounds rescale its explicit modulus.

The resulting two-sided estimate compares the SAME signed-law norm and full
action integral for all rational 0 < w < 1 and all odd extents. No equality
of the two finite quantities, strict positive lower bound, physical vacuum
stationarity or volume/spacing uniformity is asserted.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentActionLimit

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def boundaryNormProduct (w : Q') (half : Nat) : Q' :=
  heatProductBound w (centralExtent half) (centralLowerFaceIds half) *
    heatProductBound w (centralExtent half) (centralUpperFaceIds half)

theorem boundaryNormProduct_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (half : Nat) :
    (0 : Q') ≤ boundaryNormProduct w half :=
  Q'.mul_nonneg _ _ (heatProductBound_nonnegative hw _ _) (heatProductBound_nonnegative hw _ _)

def unitNormActionTolerance (w : Q') (half : Nat) (ε : Q') : Q' :=
  HKConv.divPos ε (boundaryNormProduct w half + 1)

theorem unitNormActionTolerance_pos (w : Q') (half : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < unitNormActionTolerance w half ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem unitNormActionTolerance_budget {w : Q'} (hw : (0 : Q') ≤ w) (half : Nat)
    {ε : Q'} (hε : (0 : Q') < ε) : unitNormActionTolerance w half ε * boundaryNormProduct w half ≤ ε := by
  have hB := boundaryNormProduct_nonnegative hw half
  have hp : (0 : Q') < boundaryNormProduct w half + 1 :=
    lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (unitNormActionTolerance_pos w half hε)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

def unitNormActionModulus (w : Q') (half : Nat) (ε : Q') : Nat :=
  heatProductCutoff w (centralExtent half) (centralFixedFaceIds half) (unitNormActionTolerance w half ε)

def interfaceActionRemainder (w : Q') (K L half : Nat) : RatPoly :=
  polyMul (lowerHeatProduct w K half)
    (polyMul (heatProductRemainder w (centralExtent half) K L (centralFixedFaceIds half)) (upperHeatProduct w K half))

theorem mixedHeatProduct_interface_append (w : Q') (K L half : Nat) :
    RatPolyCoeffEqv (mixedHeatProduct w K (K + L) K half)
      (polyAdd (fullHeatProduct w K half) (interfaceActionRemainder w K L half)) := by
  have hi := (heatProduct_cutoff_append w (centralExtent half) K L (centralFixedFaceIds half)).mul_right
    (upperHeatProduct w K half)
  rw [polyMul_add_left_exact] at hi
  exact (hi.mul_left (lowerHeatProduct w K half)).trans
    ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((central_product_factorization half (faceHeatPolynomial w K (centralExtent half))).symm.add (RatPolyCoeffEqv.refl _)))

private theorem left_swap (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) (Q'.mul_assoc_eqv b a c))

theorem interfaceActionRemainder_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat) (hK : unitNormActionModulus w half ε ≤ K) :
    polynomialCoefficientL1 (interfaceActionRemainder w K L half) ≤ ε := by
  have hδ := unitNormActionTolerance_pos w half hε
  have hr := heatProductRemainder_small hw0 hw1 (centralExtent half) (centralFixedFaceIds half)
    (unitNormActionTolerance w half ε) hδ K L hK
  have hu := Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hr (polynomialCoefficientL1_nonnegative _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (upperHeatProduct_bound hw0 hw1 K half) (Q'.le_of_lt hδ)))
  exact Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (lowerHeatProduct_bound hw0 hw1 K half) (polynomialCoefficientL1_nonnegative _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hu (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (left_swap _ _ _))
          (unitNormActionTolerance_budget (Q'.le_of_lt hw0) half hε))))

/-- Exact discrepancy at the independently computed interface stage. -/
theorem heatUnitNormAction_append (w : Q') (K half : Nat) :
    limitForm w (heatUnitCode K half) (heatUnitCode K half) ≈ fullActionValue w K half +
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (interfaceActionRemainder w K (heatUnitPairingStage w K K half - K) half) := by
  have hKS : K ≤ heatUnitPairingStage w K K half :=
    Nat.le_trans (Nat.le_max_left K K) (Nat.le_max_left _ _)
  have hp := mixedHeatProduct_interface_append w K (heatUnitPairingStage w K K half - K) half
  rw [Nat.add_sub_of_le hKS] at hp
  exact Q'.eqv_trans _ _ _ (heatUnitCode_limit_pairing w K K half)
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ hp) (quaternionHaar_append _ _ _))

theorem heatUnitNormAction_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (ε : Q') (hε : (0 : Q') < ε) (K : Nat) (hK : unitNormActionModulus w half ε ≤ K) :
    limitForm w (heatUnitCode K half) (heatUnitCode K half) ≤ fullActionValue w K half + ε ∧
      fullActionValue w K half ≤ limitForm w (heatUnitCode K half) (heatUnitCode K half) + ε :=
  close_of_add_remainder (heatUnitNormAction_append w K half)
    (Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
      (interfaceActionRemainder_small hw0 hw1 half ε hε K _ hK))

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.boundaryNormProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.boundaryNormProduct_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.unitNormActionTolerance
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.unitNormActionTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.unitNormActionTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.unitNormActionModulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.interfaceActionRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.mixedHeatProduct_interface_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.interfaceActionRemainder_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.heatUnitNormAction_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitActionComparison.heatUnitNormAction_close
