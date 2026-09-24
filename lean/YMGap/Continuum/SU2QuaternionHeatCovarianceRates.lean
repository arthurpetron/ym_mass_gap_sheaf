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
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CubeRoot

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

/-- The transverse rate retains at least one linear power of the nome deficit. -/
theorem linear_le_transverseRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 : Q') + -w ≤ transverseRate w :=
  Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg
    (HeatKernelGap.qpow_succ_le_self (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) 7))

/-- The quadratic radial rate is bounded by the first-order angular rate
times one additional nome deficit. This is a scalar comparison only; it is
not a lower bound for any temporal Dirichlet form. -/
theorem radialRate_le_eight_scaled_angular {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    radialRate w ≤
      (8 : Q') * ((1 : Q') + -w) * (3 * transverseRate w) := by
  let d : Q' := (1 : Q') + -w
  have hd : (0 : Q') ≤ d := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hlinear : d ≤ transverseRate w := linear_le_transverseRate hw0 hw1
  have hsquare : qpow d 2 ≤ d * transverseRate w := by
    have hpow : qpow d 2 ≈ d*d := by
      exact poly_identity_of_normal_eq (.pow (.var 0) 2)
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => d)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpow)
      (Q'.mul_le_mul_of_nonneg_left _ _ d hlinear hd)
  have hscaled : (24 : Q') * qpow d 2 ≤ 24 * (d * transverseRate w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ 24 hsquare (by decide)
  have hrearr : (24 : Q') * (d * transverseRate w) ≈
      (8 : Q') * d * (3 * transverseRate w) := by
    exact poly_identity_of_normal_eq
      (.mul (.const 24) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 8) (.var 0)) (.mul (.const 3) (.var 1)))
      (by decide) (fun | 0 => d | _ => transverseRate w)
  exact Q'.le_trans' _ _ _ (radialRate_le_twentyFour_quadratic hw0 hw1)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrearr))

/-- The linear angular rate cannot be controlled by a bounded multiple of
the quadratic radial rate near w=1. The quantitative guard is explicit;
the actual Haar moment interpretation must be supplied by the consumer. -/
theorem angularRate_not_le_multiple_radial {w C : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hC : (0 : Q') ≤ C)
    (hsmall : (24 : Q') * C * ((1 : Q') + -w) < 3) :
    ¬ (3 : Q') * transverseRate w ≤ C * radialRate w := by
  intro h
  let d : Q' := (1 : Q') + -w
  have hd : (0 : Q') < d := HKPos.one_sub_pos hw1
  have hlo : (3 : Q') * d ≤ 3 * transverseRate w :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (linear_le_transverseRate hw0 hw1) (by decide)
  have hhi : C * radialRate w ≤ C * ((24 : Q') * qpow d 2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (radialRate_le_twentyFour_quadratic hw0 hw1) hC
  have hrearr : C * ((24 : Q') * qpow d 2) ≈ d * ((24 : Q') * C * d) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 24) (.pow (.var 1) 2)))
      (.mul (.var 1) (.mul (.mul (.const 24) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => C | _ => d)
  have hcancel : (3 : Q') ≤ (24 : Q') * C * d :=
    Q'.le_of_mul_le_mul_left
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv d 3))
        (Q'.le_trans' _ _ _ hlo
          (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ hhi (Q'.le_of_eqv hrearr))))) hd
  exact (by decide : ¬ ((3 : Q') < 3)) (Q'.lt_of_le_of_lt hcancel hsmall)

/-! A computable near-one nome for every proposed comparison constant. -/

def obstructionDenominator (C : Q') : Q' := (24 : Q') * (C + 1)

theorem obstructionDenominator_pos {C : Q'} (hC : (0 : Q') ≤ C) :
    (0 : Q') < obstructionDenominator C := by
  unfold obstructionDenominator
  exact Q'.mul_pos (by decide) (HeatKernelRGStep.lt_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 1))))
      (Q'.add_le_add_right 0 C 1 hC)))

def obstructionDeficit (C : Q') (hC : (0 : Q') ≤ C) : Q' :=
  Q'.recipPos (obstructionDenominator C) (obstructionDenominator_pos hC)

def obstructionNome (C : Q') (hC : (0 : Q') ≤ C) : Q' :=
  (1 : Q') + -(obstructionDeficit C hC)

theorem obstructionDeficit_pos {C : Q'} (hC : (0 : Q') ≤ C) :
    (0 : Q') < obstructionDeficit C hC :=
  Q'.recipPos_pos _ _

theorem obstructionDeficit_lt_one {C : Q'} (hC : (0 : Q') ≤ C) :
    obstructionDeficit C hC < (1 : Q') := by
  let d := obstructionDenominator C
  let r := obstructionDeficit C hC
  have hd : (0 : Q') < d := obstructionDenominator_pos hC
  have hone : (1 : Q') < d := by
    unfold d obstructionDenominator
    have hc1 : (1 : Q') ≤ C + 1 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 1))))
        (Q'.add_le_add_right 0 C 1 hC)
    exact HeatKernelRGStep.lt_of_lt_of_le (by decide : (1 : Q') < 24)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv 24)))
        (Q'.mul_le_mul_of_nonneg_left _ _ 24 hc1 (by decide)))
  have hr : (0 : Q') < r := obstructionDeficit_pos hC
  have hmul := Q'.mul_lt_mul_of_pos_left hr hone
  have hcancel : r*d ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv d hd)
  exact HeatKernelRGStep.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.ge_of_eqv (Q'.mul_one_eqv r)) hmul)
    (Q'.le_of_eqv hcancel)

theorem obstructionNome_pos {C : Q'} (hC : (0 : Q') ≤ C) :
    (0 : Q') < obstructionNome C hC :=
  HKPos.one_sub_pos (obstructionDeficit_lt_one hC)

theorem obstructionNome_lt_one {C : Q'} (hC : (0 : Q') ≤ C) :
    obstructionNome C hC < (1 : Q') := by
  unfold obstructionNome
  show ((1 : Q') + -(obstructionDeficit C hC)).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -(obstructionDeficit C hC)).den : Int)
  have hnum : (0 : Int) < (obstructionDeficit C hC).num :=
    Q'.num_pos_of_pos (obstructionDeficit_pos hC)
  change
    (((1 : Int) * ((obstructionDeficit C hC).den : Int) +
      (-(obstructionDeficit C hC).num) * (1 : Int)) * (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * (obstructionDeficit C hC).den : Nat) : Int))
  simp only [Int.one_mul, Int.mul_one, Nat.one_mul]
  omega

theorem obstructionNome_smallness {C : Q'} (hC : (0 : Q') ≤ C) :
    (24 : Q') * C * ((1 : Q') + -(obstructionNome C hC)) < 3 := by
  let d := obstructionDenominator C
  let r := obstructionDeficit C hC
  have hd : (0 : Q') < d := obstructionDenominator_pos hC
  have hdef : ((1 : Q') + -(obstructionNome C hC)) ≈ r := by
    unfold obstructionNome r
    exact poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => obstructionDeficit C hC)
  have hC1 : C ≤ C + 1 := by
    have h := Q'.add_le_add_left C 0 1 (by decide)
    rwa [Q'.add_zero'] at h
  have hbound : (24 : Q') * C * r ≤ 24 * (C+1) * r :=
    Q'.mul_le_mul_of_nonneg_right _ _ r
      (Q'.mul_le_mul_of_nonneg_left _ _ 24 hC1 (by decide))
      (Q'.le_of_lt (obstructionDeficit_pos hC))
  have hrec : d*r ≈ (1 : Q') := Q'.mul_recipPos_eqv d hd
  have hreplace : (24 : Q') * C * ((1 : Q') + -(obstructionNome C hC)) ≈
      24*C*r := Q'.mul_eqv_congr_left (24*C) _ _ hdef
  exact Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreplace)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hrec))) (by decide)

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
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.linear_le_transverseRate
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.radialRate_le_eight_scaled_angular
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.angularRate_not_le_multiple_radial
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionNome
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionDenominator
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionDenominator_pos
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionDeficit
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionDeficit_pos
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionDeficit_lt_one
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionNome_pos
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionNome_lt_one
#print axioms YMGap.Continuum.SU2QuaternionHeatCovarianceRates.obstructionNome_smallness
