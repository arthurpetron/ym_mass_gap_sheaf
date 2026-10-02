/-
# The existing endpoint-tail certificate loses the retained heat floor

For 1/2 <= w < 1, the displayed one-link source-tail budget can certify a
relative error at most one only at degrees L whose retained heat weight
w^(L*(L+2)) is at most 1/3. The first OMITTED Casimir (L+1)*(L+3) and the
largest RETAINED Casimir L*(L+2) are kept distinct throughout.

The actual endpointTailDegree modulus supplies this condition, so this is
not an obstruction with an uninhabited premise. It rules out combining THAT
angular upper budget with a near-identity retained-heat floor. It does not
bound the true tail below, the actual transfer response above, or the true
energy/OWN-variance ratio. Sharper source estimates and signed cancellation
are not ruled out; the centered-source and scaling joins remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail
import YMGap.Continuum.BF4ExactSlabFixedSpatialScoreCalibrationObstruction
import YMGap.Continuum.ReciprocalBernoulliUpper

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.JacobiShiftedRelativeSlope
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.JacobiHeatRelativeAngularBound (relativeCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail
open YMGap.Continuum.BF4ExactSlabFixedSpatialScoreCalibrationObstruction
  (squared_gap_budget_ge_one)
open YMGap.Continuum.ReciprocalBernoulliUpper

local infix:50 " ≈ " => Q'.eqv

/-- Exact nome dependence of the cap in the existing ORIGINAL source-tail
estimate. This is the endpoint cap, not the different marginal score cap. -/
theorem endpointRelativeCap_formula (w : Q') :
    endpointRelativeCap w ≈ 24608*budget w+7 := by
  unfold endpointRelativeCap relativeCap relativeCost
  exact poly_identity_of_normal_eq
    (.add (.mul (.const 6) (.add (.mul (.const 4096) (.var 0)) (.const 1)))
      (.add (.mul (.const 32) (.var 0)) (.const 1)))
    (.add (.mul (.const 24608) (.var 0)) (.const 7))
    (by decide) (fun _ => budget w)

private theorem budget_le_endpoint {w : Q'} (hw0 : (0 : Q') < w) :
    budget w ≤ endpointRelativeCap w := by
  have hb0 := budget_nonnegative hw0
  have hscale : budget w ≤ 24608*budget w :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : (1 : Q') ≤ 24608) hb0)
  exact Q'.le_trans' _ _ _ hscale (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (by decide : (0 : Q') ≤ 7))
    (Q'.ge_of_eqv (endpointRelativeCap_formula w)))

private theorem gap_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) :
    (1 : Q')-w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hw0))
    (Q'.le_of_eqv (by change (1 : Q') + -0 ≈ 1; decide))

/-- Denominator-free barrier for the actual computed endpoint cap. -/
theorem gap_endpoint_square_ge_one {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ ((1 : Q')-w)*(endpointRelativeCap w*endpointRelativeCap w) := by
  have hw0 : (0 : Q') < w :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hw
  let h := (1 : Q')-w
  let C := endpointRelativeCap w
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hh1 : h ≤ (1 : Q') := gap_le_one (Q'.le_of_lt hw0)
  have hC : (0 : Q') ≤ C :=
    Q'.le_trans' _ _ _ (budget_nonnegative hw0) (budget_le_endpoint hw0)
  have h2 : (1 : Q') ≤ (h*h)*C := Q'.le_trans' _ _ _
    (squared_gap_budget_ge_one hw hw1)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (budget_le_endpoint hw0)
      (Q'.mul_nonneg _ _ hh hh))
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

private theorem omitted_le_three_retained (L : Nat) (hL : 1 ≤ L) :
    (L+1)*(L+3) ≤ 3*(L*(L+2)) := by
  have hsq : 1 ≤ L*L := Nat.mul_le_mul hL hL
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_comm 3 (L*L)]
  omega

private theorem power_congr {a b : Q'} (hab : a ≈ b) :
    ∀ n : Nat, qpow a n ≈ qpow b n
  | 0 => Q'.eqv_refl 1
  | n+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ a (power_congr hab n))
      (Q'.mul_eqv_congr_left (qpow b n) _ _ hab)

/-- The displayed tail certificate forces loss of the retained heat floor.
This concerns the CERTIFICATE COEFFICIENT, not a lower bound on the true
source tail. No degree bound on the complete source is assumed. -/
theorem tail_certificate_heat_weight_ceiling {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q'))
    (L : Nat) (hL : 1 ≤ L)
    (ht : 6*(endpointRelativeCap w*endpointRelativeCap w) ≤
      Q'.ofNat ((L+1)*(L+3))) :
    3*qpow w (L*(L+2)) ≤ (1 : Q') := by
  let h := (1 : Q')-w
  let C := endpointRelativeCap w
  let r := Q'.ofNat (L*(L+2))
  have hw0 : (0 : Q') < w :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < HalfPow.half) hw
  have hh := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have h6 : (6 : Q') ≤ h*(6*(C*C)) := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv 6))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 6 (gap_endpoint_square_ge_one hw hw1) (by decide))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.const 6) (.mul (.var 0) (.mul (.var 1) (.var 1))))
        (.mul (.var 0) (.mul (.const 6) (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => h | _ => C))))
  have hnat : Q'.ofNat ((L+1)*(L+3)) ≤ 3*r := Q'.le_trans' _ _ _
    (CReal.ofNat_le_ofNat (omitted_le_three_retained L hL))
    (Q'.le_of_eqv (HeatKernelRGStep.ofNat_mul_eqv 3 (L*(L+2))))
  have hscaled : (6 : Q') ≤ 3*(h*r) := Q'.le_trans' _ _ _ h6
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ h (Q'.le_trans' _ _ _ ht hnat) hh)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 3) (.var 1)))
        (.mul (.const 3) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => h | _ => r))))
  have htwo : (2 : Q') ≤ h*r := Q'.le_of_mul_le_mul_left (c := 3)
    (Q'.le_trans' _ _ _ (by decide : (3 : Q')*2 ≤ 6) hscaled) (by decide)
  have hden : (3 : Q') ≤ bernDen h (L*(L+2)) := Q'.le_trans' _ _ _
    (by decide : (3 : Q') ≤ 1+2)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ htwo)
      (Q'.le_of_eqv (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_comm_eqv h r))))
  have hbase : oneSub h ≈ w := poly_identity_of_normal_eq
    (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => w)
  have hbern : qpow w (L*(L+2))*bernDen h (L*(L+2)) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (Q'.mul_eqv_congr_right _ _ (bernDen h (L*(L+2)))
        (power_congr hbase (L*(L+2)))))
      (oneSub_pow_mul_bernDen_le hh (gap_le_one (Q'.le_of_lt hw0)) (L*(L+2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv 3 _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hden
        (qpow_nonneg w (Q'.le_of_lt hw0) (L*(L+2)))) hbern)

/-- The ACTUAL computed endpoint-tail modulus satisfies the certificate
premise. Its epsilon-small raw-source tail does not preserve a near-one
retained heat floor, even before the centered-variance join is attempted. -/
theorem endpointTailDegree_heat_weight_ceiling {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (he1 : epsilon ≤ (1 : Q'))
    (L : Nat) (hL : max 1 (endpointTailDegree w epsilon he) ≤ L) :
    3*qpow w (L*(L+2)) ≤ (1 : Q') := by
  have ht := endpointTailDegree_sufficient w epsilon he L
    (Nat.le_trans (Nat.le_max_right _ _) hL)
  have hn : (0 : Q') ≤ Q'.ofNat ((L+1)*(L+3)) := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg _
  have hcoef : epsilon*Q'.ofNat ((L+1)*(L+3)) ≤
      Q'.ofNat ((L+1)*(L+3)) := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ he1 hn)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact tail_certificate_heat_weight_ceiling hw hw1 L
    (Nat.le_trans (Nat.le_max_left _ _) hL) (Q'.le_trans' _ _ _ ht hcoef)

/-- In particular, this certified truncation cannot supply even a one-half
bare retained heat floor. The actual Wilson response is NOT bounded above. -/
theorem endpointTailDegree_not_half_floor {w : Q'}
    (hw : HalfPow.half ≤ w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (he1 : epsilon ≤ (1 : Q'))
    (L : Nat) (hL : max 1 (endpointTailDegree w epsilon he) ≤ L) :
    ¬ (HalfPow.half ≤ qpow w (L*(L+2))) := by
  intro hf
  have h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 3 hf (by decide))
    (endpointTailDegree_heat_weight_ceiling hw hw1 epsilon he he1 L hL)
  exact (by decide : ¬ ((3 : Q')*HalfPow.half ≤ (1 : Q'))) h

#print axioms endpointRelativeCap_formula
#print axioms gap_endpoint_square_ge_one
#print axioms tail_certificate_heat_weight_ceiling
#print axioms endpointTailDegree_heat_weight_ceiling
#print axioms endpointTailDegree_not_half_floor

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction
