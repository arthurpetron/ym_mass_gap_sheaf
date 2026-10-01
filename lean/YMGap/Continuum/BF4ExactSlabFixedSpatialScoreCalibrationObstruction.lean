/-
# The current score envelope cannot supply small temporal energy

For every nonempty listed family and 1/2 <= w < 1, the coefficient in the
existing relative-Ward energy ceiling is at least 24. This is a lower bound
on THAT COMPUTED UPPER-BOUND COEFFICIENT, not on the true energy/variance
ratio. It rejects calibration of this envelope alone; signed cancellation
in the original complete error remains a distinct open route.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialScoreCalibrationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.JacobiShiftedRelativeSlope
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.JacobiHeatRelativeAngularBound (relativeCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound (marginalScoreCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyRelativeWard
  (familyLengthAngularVarianceFactor)
open YMGap.Continuum.BF4CompactActionCPOrder

local infix:50 " ≈ " => Q'.eqv

private theorem gap_le_one {w : Q'} (hw : (0 : Q') ≤ w) :
    (1 : Q')-w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hw))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.const 0))) (.const 1) (by decide) (fun _ => w)))

/-- The first Jacobi factor already has its exact squared-gap cost. -/
theorem squared_gap_budget_ge_one {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ (((1 : Q')-w)*((1 : Q')-w))*budget w := by
  have hw0 : (0 : Q') < w :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hw
  have hb := prefix_le_budget hw0 hw1 1
  have hprefix : HKConv.Cstar w ≈ finSum (rate w) 1 := by
    change HKConv.Cstar w ≈ 0 + HKConv.Cstar w * 1
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (QPoly.q_zero_add_eqv _)
      (Q'.mul_one_eqv _))
  have hcb := Q'.le_trans' _ _ _ (Q'.le_of_eqv hprefix) hb
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hh2 := Q'.mul_nonneg _ _ hh hh
  have hp : (((1 : Q')-w)*((1 : Q')-w))*HKConv.Cstar w ≈ w+w := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (HKPos.factorLB_pos hw1)))
  have hhalf := Q'.add_le_add hw hw
  have hone : (1 : Q') ≤ w+w :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q') ≈ HalfPow.half+HalfPow.half))
      hhalf
  exact Q'.le_trans' _ _ _ hone (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcb hh2))

/-- Exact dependence of the existing complete-marginal score envelope. -/
theorem marginalScoreCap_formula (w : Q') :
    marginalScoreCap w ≈ 24640*budget w+8 := by
  unfold marginalScoreCap relativeCap relativeCost
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 6) (.add (.mul (.const 4096) (.var 0)) (.const 1)))
      (.mul (.const 2) (.add (.mul (.const 32) (.var 0)) (.const 1))))
    (.add (.mul (.const 24640) (.var 0)) (.const 8))
    (by decide) (fun _ => budget w)

private theorem budget_le_score {w : Q'} (hw0 : (0 : Q') < w) :
    budget w ≤ marginalScoreCap w := by
  have hb0 := budget_nonnegative hw0
  have hscale : budget w ≤ 24640*budget w :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : (1 : Q') ≤ 24640) hb0)
  exact Q'.le_trans' _ _ _ hscale (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (by decide : (0 : Q') ≤ 8))
    (Q'.ge_of_eqv (marginalScoreCap_formula w)))

/-- A denominator-free quantitative barrier for the actual score cap. -/
theorem gap_score_square_ge_one {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ ((1 : Q')-w)*(marginalScoreCap w*marginalScoreCap w) := by
  have hw0 : (0 : Q') < w :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hw
  let h := (1 : Q')-w
  let C := marginalScoreCap w
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hh1 : h ≤ (1 : Q') := gap_le_one (Q'.le_of_lt hw0)
  have hC : (0 : Q') ≤ C := Q'.le_of_lt
    (YMGap.Continuum.BF4ExactSlabFixedSpatialRelativeWardBound.marginalScoreCap_positive hw0)
  have h2 : (1 : Q') ≤ (h*h)*C := Q'.le_trans' _ _ _
    (squared_gap_budget_ge_one hw hw1)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (budget_le_score hw0) (Q'.mul_nonneg _ _ hh hh))
  have hhc : h*C ≤ C := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ C hh1 hC)
    (Q'.le_of_eqv (Q'.one_mul_eqv C))
  have h2le : (h*h)*C ≤ h*C := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv h h C))
    (Q'.mul_le_mul_of_nonneg_left _ _ h hhc hh)
  have hfirst : (1 : Q') ≤ h*C := Q'.le_trans' _ _ _ h2 h2le
  have honeC : (1 : Q') ≤ C := Q'.le_trans' _ _ _ hfirst hhc
  have hCC : C ≤ C*C := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv C))
    (Q'.mul_le_mul_of_nonneg_right _ _ C honeC hC)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.mul_le_mul_of_nonneg_left _ _ h hCC hh)

/-- No late cutoff, width or depth can make THIS upper coefficient small.
This theorem asserts nothing about the actual interacting energy. -/
theorem family_energy_coefficient_ge_twentyFour {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q'))
    (qs : List Z4Plaq) (hqs : 0 < qs.length) :
    (24 : Q') ≤ ((1 : Q')-w)*familyLengthAngularVarianceFactor w qs := by
  let h := (1 : Q')-w
  let C := marginalScoreCap w
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hcount : (4 : Q') ≤ Q'.ofNat (4*qs.length) :=
    CReal.ofNat_le_ofNat (Nat.mul_le_mul_left 4 hqs)
  have hcoef : (24 : Q') ≤ 6*Q'.ofNat (4*qs.length) :=
    Q'.le_trans' _ _ _ (by decide : (24 : Q') ≤ 6*4)
      (Q'.mul_le_mul_of_nonneg_left _ _ 6 hcount (by decide))
  have hcore : (24 : Q') ≤ (6*Q'.ofNat (4*qs.length))*(h*(C*C)) :=
    Q'.le_trans' _ _ _ hcoef (Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (gap_score_square_ge_one hw hw1)
        (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 24) hcoef)))
  have hmain := Q'.add_le_self_of_nonneg ((6*Q'.ofNat (4*qs.length))*(h*(C*C)))
    (h*24) (Q'.mul_nonneg _ _ hh (by decide))
  exact Q'.le_trans' _ _ _ hcore (Q'.le_trans' _ _ _ hmain
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 6) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 2))))
        (.mul (.var 1) (.const 24)))
      (.mul (.var 1) (.add (.const 24)
        (.mul (.mul (.mul (.const 6) (.var 0)) (.var 2)) (.var 2))))
      (by decide) (fun | 0 => Q'.ofNat (4*qs.length) | 1 => h | _ => C))))

theorem not_family_energy_coefficient_lt_half {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q'))
    (qs : List Z4Plaq) (hqs : 0 < qs.length) :
    ¬ (((1 : Q')-w)*familyLengthAngularVarianceFactor w qs < HalfPow.half) := by
  have h := Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ (24 : Q'))
    (family_energy_coefficient_ge_twentyFour hw hw1 qs hqs)
  exact Int.not_lt.mpr h

#print axioms squared_gap_budget_ge_one
#print axioms marginalScoreCap_formula
#print axioms gap_score_square_ge_one
#print axioms family_energy_coefficient_ge_twentyFour
#print axioms not_family_energy_coefficient_lt_half

end YMGap.Continuum.BF4ExactSlabFixedSpatialScoreCalibrationObstruction
