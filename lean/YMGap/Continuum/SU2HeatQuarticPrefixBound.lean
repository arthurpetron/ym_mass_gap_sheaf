/-
# A cutoff-independent SU(2) heat-variation budget

The squared character dimension times the Casimir is bounded by (n+1)^4.
This module sums that quartic Gaussian majorant with an explicit finite head
and geometric tail. The budget depends on the upper nome W<1; it is NOT
claimed uniform as W approaches one.
-/
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.SU2HeatQuarticPrefixBound

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)

def gainTarget : Q' := HKConv.divPos 1 32
def labelCutoff (W : Q') : Nat := powBaseCutoff W gainTarget

theorem ratio_le_half {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q')) :
    Q'.ofNat (2^4) * qpow W (2*labelCutoff W+3) ≤ HalfPow.half := by
  have hp := Q'.le_trans' _ _ _
    (qpow_antitone (Q'.le_of_lt hW0) (Q'.le_of_lt hW1)
      (labelCutoff W) (2*labelCutoff W+3) (by omega))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow W (labelCutoff W)))
      (pow_base_le_cutoff hW0 hW1 (by decide : (0 : Q') < gainTarget)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (by decide : (0 : Q') ≤ Q'.ofNat (2^4)))
    (by decide)

theorem shifted_geometric {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q')) (k : Nat) :
    tailTerm W 4 (labelCutoff W+k) ≤ tailTerm W 4 (labelCutoff W)*HalfPow.half^k := by
  refine CharacterTail.geom_dom (fun i => tailTerm W 4 (labelCutoff W+i))
    (tailTerm W 4 (labelCutoff W)) HalfPow.half HalfPow.half_nonneg (Q'.le_refl' _) ?_ k
  intro j
  dsimp only
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _
    (tailTerm_ratio_gen (Q'.le_of_lt hW0) (Q'.le_of_lt hW1) 4 (labelCutoff W) _ (by omega))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_le_half hW0 hW1)
      (tailTerm_nonneg (Q'.le_of_lt hW0) 4 _))

def tailBudget (W : Q') : Q' := geoTailBase (tailTerm W 4 (labelCutoff W)) HalfPow.half 0
def prefixBudget (W : Q') : Q' := finSum (tailTerm W 4) (labelCutoff W) + tailBudget W

theorem tailBudget_nonnegative {W : Q'} (hW0 : (0 : Q') < W) : (0 : Q') ≤ tailBudget W :=
  geoTailBase_nonneg (tailTerm_nonneg (Q'.le_of_lt hW0) 4 _) HalfPow.half_nonneg 0

theorem shifted_sum_bound {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q')) (L : Nat) :
    finSum (fun i => tailTerm W 4 (labelCutoff W+i)) L ≤ tailBudget W :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ (shifted_geometric hW0 hW1) L)
    (by simpa only [Nat.zero_add, geoIncrBase] using
      (geoTailBase_series_le (tailTerm_nonneg (Q'.le_of_lt hW0) 4 (labelCutoff W))
        (by decide : (0 : Q') < HalfPow.half) (by decide : HalfPow.half < (1 : Q')) 0 L))

theorem prefix_bound {W : Q'} (hW0 : (0 : Q') < W) (hW1 : W < (1 : Q')) (K : Nat) :
    finSum (tailTerm W 4) K ≤ prefixBudget W := by
  by_cases hK : K ≤ labelCutoff W
  · exact Q'.le_trans' _ _ _
      (finSum_monotone_of_nonneg _ (tailTerm_nonneg (Q'.le_of_lt hW0) 4) _ _ hK)
      (Q'.add_le_self_of_nonneg _ _ (tailBudget_nonnegative hW0))
  · have he : labelCutoff W + (K-labelCutoff W) = K := Nat.add_sub_of_le (by omega)
    have hs := finSum_split (tailTerm W 4) (labelCutoff W) (K-labelCutoff W)
    rw [he] at hs
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
      (Q'.add_le_add_left _ _ _ (shifted_sum_bound hW0 hW1 _))

theorem prefixBudget_nonnegative {W : Q'} (hW0 : (0 : Q') < W) : (0 : Q') ≤ prefixBudget W :=
  Q'.zero_le_add _ _
    (finSum_monotone_of_nonneg _ (tailTerm_nonneg (Q'.le_of_lt hW0) 4) 0 _ (Nat.zero_le _))
    (tailBudget_nonnegative hW0)

end YMGap.Continuum.SU2HeatQuarticPrefixBound

#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.gainTarget
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.labelCutoff
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.ratio_le_half
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.shifted_geometric
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.tailBudget
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.prefixBudget
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.tailBudget_nonnegative
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.shifted_sum_bound
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.prefix_bound
#print axioms YMGap.Continuum.SU2HeatQuarticPrefixBound.prefixBudget_nonnegative
