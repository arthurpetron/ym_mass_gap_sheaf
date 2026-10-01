/-
# Exceptional original SU(2) quartic heat coefficients

The bulk five-neighbor formula starts at spin two.  This module treats the
actual spin-zero and spin-one coefficients separately.  Both estimates are
finite rational polynomial facts about the original `coeffW` sequence; they
do not assemble the finite character insertion or its high-spin tail.
-/

import YMGap.Continuum.SU2HeatQuarticBulkCoefficient

namespace YMGap.Continuum.SU2HeatQuarticLowCoefficients

set_option autoImplicit false
set_option maxRecDepth 2048

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport (c4 dimQ)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (relativeBudget)

local infix:50 " ≈ " => Q'.eqv
local notation "rp" => RingNormaliser.qpow

/-- The literal spin-zero coefficient of `(2-χ₁)² H`. -/
def zeroCoeff (w : Q') : Q' :=
  (5 * coeffW w 0 + -(4 * coeffW w 1)) + coeffW w 2

/-- The literal spin-one coefficient of `(2-χ₁)² H`. -/
def oneCoeff (w : Q') : Q' :=
  (6 * coeffW w 1 + -(4 * (coeffW w 0 + coeffW w 2))) +
    coeffW w 3

private theorem ringQpow_eqv_pow (x : Q') : ∀ m, rp x m ≈ x ^ m
  | 0 => Q'.eqv_refl 1
  | m+1 => by
      have ih := ringQpow_eqv_pow x m
      show rp x m * x ≈ x * x ^ m
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ x ih)
        (Q'.mul_comm_eqv (x ^ m) x)

private theorem sourceQpow_eqv_ringQpow (w : Q') (m : Nat) :
    RGTransport.qpow w m ≈ rp w m :=
  Q'.eqv_trans _ _ _ (qpow_eqv_pow w m)
    (Q'.eqv_symm (ringQpow_eqv_pow w m))

private theorem coeff_one (w : Q') : coeffW w 1 ≈ 2 * rp w 3 := by
  unfold coeffW dimQ c4
  exact Q'.mul_eqv_congr_left _ _ _ (sourceQpow_eqv_ringQpow w 3)

private theorem coeff_two (w : Q') : coeffW w 2 ≈ 3 * rp w 8 := by
  unfold coeffW dimQ c4
  exact Q'.mul_eqv_congr_left _ _ _ (sourceQpow_eqv_ringQpow w 8)

private theorem coeff_three (w : Q') : coeffW w 3 ≈ 4 * rp w 15 := by
  unfold coeffW dimQ c4
  exact Q'.mul_eqv_congr_left _ _ _ (sourceQpow_eqv_ringQpow w 15)

private abbrev PE := RingNormaliser.PolyExpr
private def xExpr : PE := .var 0
private def hExpr : PE := .add (.const 1) (.neg xExpr)

private def zeroExpr : PE :=
  .add (.add (.const 5) (.neg (.mul (.const 8) (.pow xExpr 3))))
    (.mul (.const 3) (.pow xExpr 8))

private def oneExpr : PE :=
  .add
    (.add (.add (.mul (.const 12) (.pow xExpr 3)) (.neg (.const 4)))
      (.neg (.mul (.const 12) (.pow xExpr 8))))
    (.mul (.const 4) (.pow xExpr 15))

private def weightedExpr : List (Nat × Nat) → PE
  | [] => .const 0
  | (e, c) :: rest =>
      .add (.mul (.const c) (.pow xExpr e)) (weightedExpr rest)

private def zeroWeights : List (Nat × Nat) :=
  [(6,3), (5,6), (4,9), (3,12), (2,15), (1,10), (0,5)]

private def onePositiveWeights : List (Nat × Nat) :=
  [(13,4), (12,8), (11,12), (10,16), (9,20), (8,24),
    (7,28), (6,20), (5,12), (4,4)]

private def oneNegativeWeights : List (Nat × Nat) :=
  [(3,4), (2,12), (1,8), (0,4)]

private def weighted (w : Q') (xs : List (Nat × Nat)) : Q' :=
  eval (fun _ => w) (weightedExpr xs)

private def weightTotal : List (Nat × Nat) → Q'
  | [] => 0
  | (_, c) :: rest => Q'.ofNat c + weightTotal rest

private theorem ringQpow_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) :
    ∀ m, (0 : Q') ≤ rp w m
  | 0 => by change (0 : Q') ≤ 1; decide
  | m+1 => Q'.mul_nonneg _ _ (ringQpow_nonnegative hw m) hw

private theorem ringQpow_le_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (m : Nat) :
    rp w m ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (ringQpow_eqv_pow w m))
    (YMGap.Continuum.HKPos.pow_le_one hw0 hw1 m)

private theorem weighted_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) :
    ∀ xs, (0 : Q') ≤ weighted w xs
  | [] => by change (0 : Q') ≤ 0; exact Q'.le_refl' _
  | (e,c) :: rest => by
      change (0 : Q') ≤ Q'.ofNat c * rp w e + weighted w rest
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg c)
          (ringQpow_nonnegative hw e))
        (weighted_nonnegative hw rest)

private theorem weighted_le_total {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ xs, weighted w xs ≤ weightTotal xs
  | [] => by change (0 : Q') ≤ 0; exact Q'.le_refl' _
  | (e,c) :: rest => by
      change Q'.ofNat c * rp w e + weighted w rest ≤
        Q'.ofNat c + weightTotal rest
      apply Q'.add_le_add
      · exact Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (ringQpow_le_one hw0 hw1 e) (Q'.ofNat_nonneg c))
          (Q'.le_of_eqv (Q'.mul_one_eqv _))
      · exact weighted_le_total hw0 hw1 rest

private theorem zeroCoeff_polynomial (w : Q') :
    zeroCoeff w ≈ eval (fun _ => w) zeroExpr := by
  have h0 : coeffW w 0 ≈ 1 := by
    rw [coeffW_zero]
    exact Q'.eqv_refl _
  have hraw : zeroCoeff w ≈
      (5 * 1 + -(4 * (2 * rp w 3))) + 3 * rp w 8 := by
    unfold zeroCoeff
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ h0)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ (coeff_one w))))
      (coeff_two w)
  have hpoly : (5 * (1 : Q') + -(4 * (2 * rp w 3))) +
      3 * rp w 8 ≈ eval (fun _ => w) zeroExpr :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 5) (.const 1))
        (.neg (.mul (.const 4) (.mul (.const 2) (.var 0)))))
        (.mul (.const 3) (.var 1)))
      (.add (.add (.const 5) (.neg (.mul (.const 8) (.var 0))))
        (.mul (.const 3) (.var 1)))
      (by decide) (fun | 0 => rp w 3 | _ => rp w 8)
  exact Q'.eqv_trans _ _ _ hraw hpoly

private theorem oneCoeff_polynomial (w : Q') :
    oneCoeff w ≈ eval (fun _ => w) oneExpr := by
  have h0 : coeffW w 0 ≈ 1 := by
    rw [coeffW_zero]
    exact Q'.eqv_refl _
  have hraw : oneCoeff w ≈
      (6 * (2 * rp w 3) +
        -(4 * (1 + 3 * rp w 8))) + 4 * rp w 15 := by
    unfold oneCoeff
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (coeff_one w))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.add_eqv_congr' h0 (coeff_two w)))))
      (coeff_three w)
  have hpoly : (6 * (2 * rp w 3) +
        -(4 * (1 + 3 * rp w 8))) + 4 * rp w 15 ≈
        eval (fun _ => w) oneExpr :=
    poly_identity_of_normal_eq
      (.add
        (.add (.mul (.const 6) (.mul (.const 2) (.var 0)))
          (.neg (.mul (.const 4)
            (.add (.const 1) (.mul (.const 3) (.var 1))))))
        (.mul (.const 4) (.var 2)))
      (.add
        (.add (.add (.mul (.const 12) (.var 0)) (.neg (.const 4)))
          (.neg (.mul (.const 12) (.var 1))))
        (.mul (.const 4) (.var 2)))
      (by decide) (fun | 0 => rp w 3 | 1 => rp w 8 | _ => rp w 15)
  exact Q'.eqv_trans _ _ _ hraw hpoly

/-- Exact factorization of the original spin-zero coefficient. -/
theorem zeroCoeff_factor (w : Q') :
    zeroCoeff w ≈ rp ((1 : Q') + -w) 2 * weighted w zeroWeights := by
  have hfactor : eval (fun _ => w) zeroExpr ≈
      rp ((1 : Q') + -w) 2 * weighted w zeroWeights :=
    poly_identity_of_normal_eq zeroExpr
      (.mul (.pow hExpr 2) (weightedExpr zeroWeights))
      (by decide) (fun _ => w)
  exact Q'.eqv_trans _ _ _ (zeroCoeff_polynomial w) hfactor

/-- Exact factorization of the original spin-one coefficient.  Its quotient
has a positive ten-term part and a nonnegative four-term subtraction. -/
theorem oneCoeff_factor (w : Q') :
    oneCoeff w ≈ rp ((1 : Q') + -w) 2 *
      (weighted w onePositiveWeights + -(weighted w oneNegativeWeights)) := by
  have hfactor : eval (fun _ => w) oneExpr ≈
      rp ((1 : Q') + -w) 2 *
        (weighted w onePositiveWeights + -(weighted w oneNegativeWeights)) :=
    poly_identity_of_normal_eq oneExpr
      (.mul (.pow hExpr 2)
        (.add (weightedExpr onePositiveWeights)
          (.neg (weightedExpr oneNegativeWeights))))
      (by decide) (fun _ => w)
  exact Q'.eqv_trans _ _ _ (oneCoeff_polynomial w) hfactor

/-- Original exceptional spin zero is second order in the nome defect. -/
theorem zeroCoeff_le_sixty {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    zeroCoeff w ≤ 60 * rp ((1 : Q') + -w) 2 := by
  have hh : (0 : Q') ≤ (1 : Q') + -w := Q'.sub_nonneg_of_le hw1
  have hR : weighted w zeroWeights ≤ (60 : Q') :=
    Q'.le_trans' _ _ _ (weighted_le_total hw0 hw1 zeroWeights)
      (by decide)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hR
    (ringQpow_nonnegative hh 2)
  have hcomm : rp ((1 : Q') + -w) 2 * (60 : Q') ≈
      60 * rp ((1 : Q') + -w) 2 := Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (zeroCoeff_factor w))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hcomm))

/-- Original exceptional spin one has an unconditional second-order upper
bound.  The negative part of its exact quotient is retained until this step. -/
theorem oneCoeff_le_148 {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    oneCoeff w ≤ 148 * rp ((1 : Q') + -w) 2 := by
  let z := weighted w onePositiveWeights
  let t := weighted w oneNegativeWeights
  let h := (1 : Q') + -w
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have ht : (0 : Q') ≤ t := weighted_nonnegative hw0 oneNegativeWeights
  have hz : z ≤ (148 : Q') :=
    Q'.le_trans' _ _ _ (weighted_le_total hw0 hw1 onePositiveWeights)
      (by decide)
  have hzt : z + -t ≤ z := by
    have hneg : -t ≤ (0 : Q') := Q'.neg_le_neg ht
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_left z (-t) 0 hneg)
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv z))
  have hmul : rp h 2 * (z + -t) ≤ rp h 2 * z :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hzt (ringQpow_nonnegative hh 2)
  have htop : rp h 2 * z ≤ rp h 2 * (148 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hz (ringQpow_nonnegative hh 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (oneCoeff_factor w))
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ htop
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- The positive half-guard places the original spin-one heat coefficient
above the vacuum coefficient. -/
private theorem one_le_coeff_one {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hhalf : (1 : Q') ≤ 2 * w ^ 4) :
    (1 : Q') ≤ coeffW w 1 := by
  have h43 : w ^ 4 ≤ w ^ 3 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qpow_eqv_pow w 4))
      (Q'.le_trans' _ _ _
        (YMGap.Continuum.HeatKernelRGStep.qpow_antitone hw0 hw1 3 4
          (by decide))
        (Q'.le_of_eqv (qpow_eqv_pow w 3)))
  have hmul : 2 * w ^ 4 ≤ 2 * w ^ 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h43 (by decide)
  have hpin : coeffW w 1 ≈ 2 * w ^ 3 :=
    Q'.eqv_trans _ _ _ (coeff_one w)
      (Q'.mul_eqv_congr_left _ _ _ (ringQpow_eqv_pow w 3))
  exact Q'.le_trans' _ _ _ hhalf
    (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv hpin))

/-- The exceptional spin-one coefficient fits the same relative envelope
used for bulk spins, under its explicit center half-guard. -/
theorem oneCoeff_le_relative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hhalf : (1 : Q') ≤ 2 * w ^ 4) :
    oneCoeff w ≤ relativeBudget 2 (1 + -w) * coeffW w 1 := by
  let h := (1 : Q') + -w
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have hh2 : (0 : Q') ≤ rp h 2 := ringQpow_nonnegative hh 2
  have ha1 : (1 : Q') ≤ coeffW w 1 := one_le_coeff_one hw0 hw1 hhalf
  have ha0 : (0 : Q') ≤ coeffW w 1 :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) ha1
  have h148 : (0 : Q') ≤ 148 * rp h 2 :=
    Q'.mul_nonneg _ _ (by decide) hh2
  have hleMul : 148 * rp h 2 ≤ (148 * rp h 2) * coeffW w 1 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha1 h148)
  have hh4 : (0 : Q') ≤ (h*h)*(h*h) := by
    have h2 : (0 : Q') ≤ h*h := Q'.mul_nonneg _ _ hh hh
    exact Q'.mul_nonneg _ _ h2 h2
  have hbudget : 148 * rp h 2 ≤ relativeBudget 2 h := by
    have hp : rp h 2 ≈ h*h := by
      change ((1 : Q') * h) * h ≈ h*h
      exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv h)
    have hlin : 148 * rp h 2 ≤ 296 * rp h 2 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (by decide : (148 : Q') ≤ 296) hh2
    have htail : (0 : Q') ≤ 512 * ((h*h)*(h*h)) :=
      Q'.mul_nonneg _ _ (by decide) hh4
    have hform : 296 * rp h 2 + 512 * ((h*h)*(h*h)) ≈
        relativeBudget 2 h := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hp))
        (poly_identity_of_normal_eq
          (.add (.mul (.const 296) (.mul (.var 0) (.var 0)))
            (.mul (.const 512)
              (.mul (.mul (.var 0) (.var 0))
                (.mul (.var 0) (.var 0)))))
          (.add (.mul (.mul (.const 32)
              (.mul (.mul (.const 2) (.const 2))
                (.mul (.const 2) (.const 2))))
              (.mul (.mul (.var 0) (.var 0))
                (.mul (.var 0) (.var 0))))
            (.mul (.const 296) (.mul (.var 0) (.var 0))))
          (by decide) (fun _ => h))
    exact Q'.le_trans' _ _ _ hlin
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ htail)
        (Q'.le_of_eqv hform))
  exact Q'.le_trans' _ _ _ (oneCoeff_le_148 hw0 hw1)
    (Q'.le_trans' _ _ _ hleMul
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbudget ha0))

end YMGap.Continuum.SU2HeatQuarticLowCoefficients

#print axioms YMGap.Continuum.SU2HeatQuarticLowCoefficients.zeroCoeff_factor
#print axioms YMGap.Continuum.SU2HeatQuarticLowCoefficients.oneCoeff_factor
#print axioms YMGap.Continuum.SU2HeatQuarticLowCoefficients.zeroCoeff_le_sixty
#print axioms YMGap.Continuum.SU2HeatQuarticLowCoefficients.oneCoeff_le_148
#print axioms YMGap.Continuum.SU2HeatQuarticLowCoefficients.oneCoeff_le_relative
