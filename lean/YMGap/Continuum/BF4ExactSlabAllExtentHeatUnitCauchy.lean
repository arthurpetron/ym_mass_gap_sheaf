/-
# The full heat-dressed unit in each ORIGINAL completed slab carrier

At fixed rational 0 < w < 1 and odd slab extent, the actual all-label unit
codes form a GNS-Cauchy sequence with an explicit squared-distance modulus.
The interface product has a cutoff-independent coefficient bound. Make the
upper remainder at most one and the lower remainder at most epsilon/(B+1).
Their joint original Haar norm is then at most epsilon, at every interface
stage. No square root or choice of quotient representatives is needed.

The full-unit representative and its completion class are constructed here.
Non-nullness/normalization of this full unit, physical vacuum stationarity,
inter-slab compatibility, time transfer, strict gap and continuum remain open.
The modulus depends explicitly on w and the slab; no spacing-uniform claim.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def interfaceNormBound (w : Q') (half : Nat) : Q' :=
  heatProductBound w (centralExtent half) (centralFixedFaceIds half)

def heatUnitNormTolerance (w : Q') (half : Nat) (ε : Q') : Q' :=
  HKConv.divPos ε (interfaceNormBound w half + 1)

theorem heatUnitNormTolerance_pos (w : Q') (half : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < heatUnitNormTolerance w half ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem heatUnitNormTolerance_budget {w : Q'} (hw : (0 : Q') ≤ w) (half : Nat)
    {ε : Q'} (hε : (0 : Q') < ε) : heatUnitNormTolerance w half ε * interfaceNormBound w half ≤ ε := by
  have hB : (0 : Q') ≤ interfaceNormBound w half := heatProductBound_nonnegative hw _ _
  have hp : (0 : Q') < interfaceNormBound w half + 1 :=
    lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (heatUnitNormTolerance_pos w half hε)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

/-- A squared-distance modulus: the two boundaries have independently budgeted tolerances. -/
def heatUnitModulus (w : Q') (half : Nat) (ε : Q') : Nat :=
  max (heatProductCutoff w (centralExtent half) (centralLowerFaceIds half) (heatUnitNormTolerance w half ε))
    (heatProductCutoff w (centralExtent half) (centralUpperFaceIds half) 1)

theorem heatUnitIncrementIntegrand_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (ε : Q') (hε : (0 : Q') < ε) (S K L : Nat) (hK : heatUnitModulus w half ε ≤ K) :
    polynomialCoefficientL1 (heatUnitIncrementIntegrand w S K L half) ≤ ε := by
  have hl := heatProductRemainder_small hw0 hw1 (centralExtent half) (centralLowerFaceIds half)
    (heatUnitNormTolerance w half ε) (heatUnitNormTolerance_pos w half hε) K L
    (Nat.le_trans (Nat.le_max_left _ _) hK)
  have hu := heatProductRemainder_small hw0 hw1 (centralExtent half) (centralUpperFaceIds half)
    1 (by decide) K L (Nat.le_trans (Nat.le_max_right _ _) hK)
  have hi : polynomialCoefficientL1 (polyMul (interfaceHeatProduct w S half) (upperHeatRemainder w K L half)) ≤
      interfaceNormBound w half :=
    Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (interfaceHeatProduct_bound hw0 hw1 S half) (polynomialCoefficientL1_nonnegative _))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hu (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _))
          (Q'.le_of_eqv (Q'.mul_one_eqv _))))
  exact Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hl (polynomialCoefficientL1_nonnegative _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hi (Q'.le_of_lt (heatUnitNormTolerance_pos w half hε)))
        (heatUnitNormTolerance_budget (Q'.le_of_lt hw0) half hε)))

theorem heatUnitIncrement_norm_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat) (hK : heatUnitModulus w half ε ≤ K) :
    limitForm w (heatUnitIncrement K L half) (heatUnitIncrement K L half) ≤ ε :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (heatUnitIncrement_limit_norm w K L half))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
        (heatUnitIncrementIntegrand_small hw0 hw1 half ε hε _ K L hK)))

theorem heatUnit_distSq_increment (w : Q') (hw : (0 : Q') ≤ w) (K L half : Nat) :
    (cutoffLimitGNSData w hw half).distSqQ (heatUnitCode (K + L) half) (heatUnitCode K half) ≈
      limitForm w (heatUnitIncrement K L half) (heatUnitIncrement K L half) := by
  have hc : (cutoffLimitGNSData w hw half).veq
      ((cutoffLimitGNSData w hw half).sub (heatUnitCode (K + L) half) (heatUnitCode K half))
      (heatUnitIncrement K L half) := by
    intro state
    change _ + (-(heatUnitCode K half).coefficient state) ≈ _ + (-1) * (heatUnitCode K half).coefficient state
    exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
  exact Q'.eqv_trans _ _ _ ((cutoffLimitGNSData w hw half).B_diag_congr hc)
    (Q'.eqv_of_eq (cutoffLimitGNSData_form w hw half _ _))

/-- The ACTUAL growing all-label codes, not a fixed-anchor surrogate. -/
def heatUnitCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    CauchyGNS (cutoffLimitGNSData w (Q'.le_of_lt hw0) half) where
  seq K := heatUnitCode K half
  modulus := heatUnitModulus w half
  isCauchy := by
    intro ε hε p q hp hq
    by_cases hqp : q ≤ p
    · have he := heatUnit_distSq_increment w (Q'.le_of_lt hw0) q (p - q) half
      rw [Nat.add_sub_of_le hqp] at he
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (heatUnitIncrement_norm_small hw0 hw1 half ε hε q (p - q) hq)
    · have hpq : p ≤ q := by omega
      have he := heatUnit_distSq_increment w (Q'.le_of_lt hw0) p (q - p) half
      rw [Nat.add_sub_of_le hpq] at he
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ((cutoffLimitGNSData w (Q'.le_of_lt hw0) half).distSqQ_comm _ _))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (heatUnitIncrement_norm_small hw0 hw1 half ε hε p (q - p) hp))

/-- Its class lies in the previously constructed ORIGINAL slab completion. -/
def completedHeatUnit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) :
    CutoffLimitCarrier w (Q'.le_of_lt hw0) half :=
  Quotient.mk (cauchySetoid (cutoffLimitGNSData w (Q'.le_of_lt hw0) half)) (heatUnitCauchy w hw0 hw1 half)

theorem heatUnitCauchy_seq (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half K : Nat) :
    (heatUnitCauchy w hw0 hw1 half).seq K = heatUnitCode K half := rfl

theorem heatUnitCauchy_modulus (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) (ε : Q') :
    (heatUnitCauchy w hw0 hw1 half).modulus ε = heatUnitModulus w half ε := rfl

/-- Explicit outer AND representative-index threshold for convergence to the supplied class. -/
theorem completedHeatUnit_representative_close (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (ε : Q') (hε : (0 : Q') < ε) (K n : Nat)
    (hK : heatUnitModulus w half ε ≤ K) (hn : heatUnitModulus w half ε ≤ n) :
    (cutoffLimitGNSData w (Q'.le_of_lt hw0) half).distSqQ
      (heatUnitCode K half) ((heatUnitCauchy w hw0 hw1 half).seq n) ≤ ε :=
  (heatUnitCauchy w hw0 hw1 half).isCauchy ε hε K n hK hn

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.interfaceNormBound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitNormTolerance
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitNormTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitNormTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitModulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitIncrementIntegrand_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitIncrement_norm_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnit_distSq_increment
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.completedHeatUnit
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitCauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.heatUnitCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitCauchy.completedHeatUnit_representative_close
