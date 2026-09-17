/-
# Scalar rates in the shared-link SU(2) heat covariance

The fundamental and trace-free quadratic heat multipliers are w^3 and w^8.
Their covariance matrix has transverse rate 1-w^8 and radial rate
1+3*w^8-4*w^6. The radial factorization retains its quadratic vanishing;
the two explicit upper bounds use only the existing Bernoulli power bound.

These rates are not multiplied by the six-private-link factor w^18. They
are intended for the actual adjacent-plaquette shared-link calculation.
No interacting measure comparison, spatial gap, or continuum limit is
asserted by these scalar inequalities.
-/

import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.R1CornerAtoms
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.SU2QuaternionHeatCovarianceRates

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

def transverseRate (w : Q') : Q' := (1 : Q') + -(qpow w 8)

def radialRate (w : Q') : Q' :=
  ((1 : Q') + 3*qpow w 8) + -(4*qpow w 6)

/-- The radial covariance vanishes to second order at w=1. -/
theorem radialRate_factorization (w : Q') :
    radialRate w ≈ qpow ((1 : Q') + -(qpow w 2)) 2 *
      (((1 : Q') + 2*qpow w 2) + 3*qpow w 4) :=
  poly_identity_of_normal_eq
    (.add (.add (.const 1) (.mul (.const 3) (.pow (.var 0) 8)))
      (.neg (.mul (.const 4) (.pow (.var 0) 6))))
    (.mul (.pow (.add (.const 1) (.neg (.pow (.var 0) 2))) 2)
      (.add (.add (.const 1) (.mul (.const 2) (.pow (.var 0) 2)))
        (.mul (.const 3) (.pow (.var 0) 4))))
    (by decide) (fun _ => w)

/-- The difference of the two rates has a nonnegative factorization. -/
theorem transverseRate_sub_radialRate (w : Q') :
    transverseRate w + -(radialRate w) ≈
      (4*qpow w 6) * ((1 : Q') + -(qpow w 2)) :=
  poly_identity_of_normal_eq
    (.add (.add (.const 1) (.neg (.pow (.var 0) 8)))
      (.neg (.add (.add (.const 1) (.mul (.const 3) (.pow (.var 0) 8)))
        (.neg (.mul (.const 4) (.pow (.var 0) 6))))))
    (.mul (.mul (.const 4) (.pow (.var 0) 6))
      (.add (.const 1) (.neg (.pow (.var 0) 2))))
    (by decide) (fun _ => w)

private theorem cofactor_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ ((1 : Q') + 2*qpow w 2) + 3*qpow w 4 :=
  Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _ (by decide) (RGTransport.qpow_nonneg w hw0 2)))
    (Q'.mul_nonneg _ _ (by decide) (RGTransport.qpow_nonneg w hw0 4))

theorem radialRate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ radialRate w := by
  have hdef : (0 : Q') ≤ (1 : Q') + -(qpow w 2) :=
    Q'.sub_nonneg_of_le (HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 2)
  have hprod := Q'.mul_nonneg _ _
    (RGTransport.qpow_nonneg _ hdef 2) (cofactor_nonnegative (Q'.le_of_lt hw0))
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv (radialRate_factorization w))

theorem radialRate_le_transverseRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    radialRate w ≤ transverseRate w := by
  apply Q'.le_of_sub_nonneg
  have hprod := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4)
      (RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) 6))
    (Q'.sub_nonneg_of_le (HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 2))
  exact Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv (transverseRate_sub_radialRate w))

theorem transverseRate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ transverseRate w :=
  Q'.sub_nonneg_of_le (HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 8)

/-- Linear control with a literal rational constant, not an asymptotic claim. -/
theorem transverseRate_le_eight_linear {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    transverseRate w ≤ (8 : Q') * ((1 : Q') + -w) :=
  R1CornerAtoms.oneSub_qpow_le (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 8

private theorem cofactor_le_six {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ((1 : Q') + 2*qpow w 2) + 3*qpow w 4 ≤ (6 : Q') := by
  have htwo : (2 : Q')*qpow w 2 ≤ 2 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (HeatKernelGap.qpow_le_one hw0 hw1 2)
        (by decide : (0 : Q') ≤ 2)) (Q'.le_of_eqv (Q'.mul_one_eqv 2))
  have hthree : (3 : Q')*qpow w 4 ≤ 3 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (HeatKernelGap.qpow_le_one hw0 hw1 4)
        (by decide : (0 : Q') ≤ 3)) (Q'.le_of_eqv (Q'.mul_one_eqv 3))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_left 1 _ _ htwo))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q')+2) _ _ hthree) (by decide))

/-- The radial rate has an explicit quadratic, rather than merely linear,
upper bound. No limit or reciprocal is required. -/
theorem radialRate_le_twentyFour_quadratic {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    radialRate w ≤ (24 : Q') * qpow ((1 : Q') + -w) 2 := by
  let u : Q' := (1 : Q') + -(qpow w 2)
  let v : Q' := (2 : Q') * ((1 : Q') + -w)
  have hu : (0 : Q') ≤ u :=
    Q'.sub_nonneg_of_le (HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 2)
  have huv : u ≤ v :=
    R1CornerAtoms.oneSub_qpow_le (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 2
  have hsquare : qpow u 2 ≤ qpow v 2 := HeatKernelGap.qpow_mono hu huv 2
  have hcofactor : qpow u 2 * (((1 : Q') + 2*qpow w 2) + 3*qpow w 4) ≤
      qpow u 2 * (6 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (cofactor_le_six (Q'.le_of_lt hw0) (Q'.le_of_lt hw1))
      (RGTransport.qpow_nonneg u hu 2)
  have hfinish : qpow v 2 * (6 : Q') ≈ (24 : Q') * qpow ((1 : Q') + -w) 2 :=
    poly_identity_of_normal_eq
      (.mul (.pow (.mul (.const 2) (.var 0)) 2) (.const 6))
      (.mul (.const 24) (.pow (.var 0) 2)) (by decide)
      (fun _ => (1 : Q') + -w)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (radialRate_factorization w))
    (Q'.le_trans' _ _ _ hcofactor
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsquare (by decide : (0 : Q') ≤ 6))
        (Q'.le_of_eqv hfinish)))

end YMGap.Continuum.SU2QuaternionHeatCovarianceRates

#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.transverseRate
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate_factorization
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.transverseRate_sub_radialRate
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate_le_transverseRate
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.transverseRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.transverseRate_le_eight_linear
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate_le_twentyFour_quadratic
