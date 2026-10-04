/-
# The computed linear channel credit cannot survive growing footprint

The actual local-band coefficient is at most (1/4)^size at EVERY strict
nome. Any fixed polynomial rescaling still tends to zero with an explicit
modulus, even if the nome changes at every size. This rejects a uniform floor
for THIS coarse certificate, not for the actual channel ratio, transfer or
Yang--Mills mass. Original finite credit theorems remain valid.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
import YMGap.Continuum.PolynomialGeometricDecay
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.Continuum.BF4OriginalChannelLinearCreditCollapse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
  (channelObservableSquareLinearVarianceCredit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localLower localUpper localLower_positive localUpper_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.ClusterCount (ofNat_nonneg)

local notation "quarter" => Q'.mkPos 1 4 (by decide)

private theorem one_le_pow (x : Q') (hx : (1 : Q') ≤ x) :
    ∀ n : Nat, (1 : Q') ≤ x^n
  | 0 => Q'.le_refl' _
  | n+1 => by
      rw [Q'.pow_succ]
      have hx0 := Q'.le_trans' _ _ _ Q'.zero_le_one hx
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ (x^n) hx (Q'.pow_nonneg x hx0 n)
      exact Q'.le_trans' _ _ _ (one_le_pow x hx n)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hm)

/-- Nome-independent ceiling for THIS already-computed credit. It is not an
upper bound for the actual retained-square/variance ratio. -/
theorem linearCredit_geometric_ceiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size : Nat) :
    channelObservableSquareLinearVarianceCredit hw0 hw1 size ≤ quarter^size := by
  let l := localLower w (4*size)
  let u := localUpper w (4*size)
  have hu : (0 : Q') < u := localUpper_positive hw0 hw1 _
  let r := Q'.recipPos u hu
  have hu1 : (1 : Q') ≤ u := one_le_pow _ (prefixCap_ge_one hw0 hw1) _
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos u hu)
  have hr1 : r ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv r))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ r hu1 hr0)
      (Q'.le_of_eqv (Q'.mul_recipPos_eqv u hu)))
  have hl0 : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hcredit : channelObservableSquareLinearVarianceCredit hw0 hw1 size ≤ l :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ l hr1 hl0)
      (Q'.le_of_eqv (Q'.mul_one_eqv l))
  have hfloor0 := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hfloorQuarter : headFloor w ≤ quarter := Q'.le_trans' _ _ _
    (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hfloor1 : headFloor w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hfloorQuarter (by decide)
  have hexponent : size ≤ 7*(4*size) := by omega
  have hl : l ≤ quarter^size := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone hfloor0 hfloor1 hexponent)
    (HKConv.pow_le_pow_base hfloor0 hfloorQuarter size)
  exact Q'.le_trans' _ _ _ hcredit hl

/-- All-later-indices modulus independent of nome or any nome schedule.
Amplitude and polynomial degree remain explicit computational inputs. -/
def creditCutoff (C : Q') (p : Nat) (epsilon : Q') : Nat :=
  PolynomialGeometricDecay.polynomialCutoff quarter C p epsilon

/-- No fixed polynomial rescaling rescues this band credit as size grows.
The bound applies independently at each nome, without regularity premises. -/
theorem polynomialCredit_small {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) {C epsilon : Q'} (hC : (0 : Q') ≤ C)
    (he : (0 : Q') < epsilon) (p size : Nat)
    (hsize : creditCutoff C p epsilon ≤ size) :
    channelObservableSquareLinearVarianceCredit hw0 hw1 size *
        (C*Q'.ofNat ((size+1)^p)) ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (linearCredit_geometric_ceiling hw0 hw1 size)
      (Q'.mul_nonneg _ _ hC (ofNat_nonneg _)))
    (PolynomialGeometricDecay.polynomial_bound
      (by decide : (0 : Q') ≤ quarter) (by decide : quarter < (1 : Q'))
      hC he p size hsize)

/-- Reject an eventual positive floor for THIS polynomially rescaled
coefficient, including arbitrary changing-nome families. This does not reject
an actual channel-ratio floor, a survival estimate, or a physical mass gap. -/
theorem no_eventual_polynomial_credit_floor (w : Nat → Q')
    (hw0 : ∀ size, (0 : Q') < w size) (hw1 : ∀ size, w size < (1 : Q'))
    {C delta : Q'} (hC : (0 : Q') ≤ C) (hdelta : (0 : Q') < delta)
    (p onset : Nat) :
    ¬ (∀ size, onset ≤ size → delta ≤
      channelObservableSquareLinearVarianceCredit (hw0 size) (hw1 size) size *
        (C*Q'.ofNat ((size+1)^p))) := by
  intro hfloor
  let e := HalfPow.half*delta
  have he : (0 : Q') < e := Q'.mul_pos (by decide) hdelta
  have heLt : e < delta := ClusteringImpliesGap.lt_of_lt_of_le
    (ClusteringImpliesGap.mul_lt_mul_of_pos_right hdelta
      (by decide : HalfPow.half < (1 : Q')))
    (Q'.le_of_eqv (Q'.one_mul_eqv delta))
  let size := max onset (creditCutoff C p e)
  have hlower := hfloor size (Nat.le_max_left _ _)
  have hupper := polynomialCredit_small (hw0 size) (hw1 size) hC he p size
    (Nat.le_max_right _ _)
  exact Int.not_lt.mpr (Q'.le_trans' _ _ _ hlower hupper) heLt

#print axioms linearCredit_geometric_ceiling
#print axioms creditCutoff
#print axioms polynomialCredit_small
#print axioms no_eventual_polynomial_credit_floor

end YMGap.Continuum.BF4OriginalChannelLinearCreditCollapse
