/-
# A nonvacuous finite ORIGINAL OWN-centered signed-gain witness

The original depth-zero odd center at w=1/16 is retained. Its actual
centered-square projection floor dominates the actual Young cost at
the six-link reference factor w^18. This gives an explicit positive
lower bound for the EXISTING original commutatorGain, not a new gain
or an interacting eigenpin. Cutoff one and width two remain fixed;
later cutoffs, terminal depths and physical scaling are not asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall (originalOddMean meanCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (commutatorGain)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow)

local infix:50 " ≈ " => Q'.eqv
local notation "half" => HalfPow.half
attribute [local irreducible] originalOddMean centeredOriginalGain centeredOriginalSquare
  centeredOriginalYoungCost commutatorGain

/-- Explicit rational gain floor at the witnessed positive finite nome. -/
def finiteGainFloor : Q' :=
  let z := qpow smallNome 12 * (coeffW smallNome 1 * meanCap)
  let a := qpow smallNome 18
  half * (half * (z*z) - (a*a)*128)

theorem finiteGainFloor_positive : (0 : Q') < finiteGainFloor := by decide

/-- All original signed terms are paid by the SAME OWN-centered square
and Young cost. The existing commutator source is joined explicitly. -/
theorem originalOwnGain_smallNome_floor :
    finiteGainFloor ≤ commutatorGain smallNome 1 2 0 bentObservable
      (originalOddMean smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap)
      (qpow smallNome 18) := by
  let c := originalOddMean smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap
  let a := qpow smallNome 18
  let z := qpow smallNome 12 * (coeffW smallNome 1 * meanCap)
  have hC : half*(z*z) ≤ centeredOriginalSquare smallNome c := by
    unfold centeredOriginalSquare
    exact originalOwnCenteredSquare_lower smallNome smallNome_pos
      smallNome_coeff_nonneg smallNome_coeff_le_cap
  have hQ : centeredOriginalYoungCost smallNome c ≤ 128 :=
    originalOwnYoungCost_le_128 smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap
  have hcost : (a*a)*centeredOriginalYoungCost smallNome c ≤ (a*a)*128 :=
    Q'.mul_le_mul_of_nonneg_left _ _ (a*a) hQ (SumOfSquares.q_mul_self_nonneg a)
  have hdelta : BF4ExactSlabFixedSpatialCubeFundamentalInterval.cubeFundamentalDelta smallNome ≤ 1 :=
    Q'.le_trans' _ _ _ smallNome_delta_le_cap (by decide : deltaCap ≤ (1 : Q'))
  have hYoung := gain_young_lower smallNome c a smallNome_coeff_nonneg hdelta
  have hraw : half*(z*z)-(a*a)*128 ≤ 2*centeredOriginalGain smallNome c a :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hC (Q'.neg_le_neg hcost)) hYoung
  have hhalf := Q'.mul_le_mul_of_nonneg_left _ _ half hraw HalfPow.half_nonneg
  have he : half*(2*centeredOriginalGain smallNome c a) ≈ centeredOriginalGain smallNome c a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half 2 _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : half*2 ≈ (1 : Q')))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hhalf
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.ge_of_eqv (original_commutator_gain_pin smallNome c a)))

theorem originalOwnGain_smallNome_positive :
    (0 : Q') < commutatorGain smallNome 1 2 0 bentObservable
      (originalOddMean smallNome smallNome_coeff_nonneg smallNome_coeff_le_cap)
      (qpow smallNome 18) :=
  HeatKernelRGStep.lt_of_lt_of_le finiteGainFloor_positive originalOwnGain_smallNome_floor

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain.finiteGainFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain.finiteGainFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain.originalOwnGain_smallNome_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFiniteOwnGain.originalOwnGain_smallNome_positive
