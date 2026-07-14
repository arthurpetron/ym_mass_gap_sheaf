/-
Large-scale payment of the cubic Taylor debt by one old Hermite mass.

This combines the exact eighth-moment payment with the inter-scale weight
comparison.  All remaining constants are discharged by polynomial power
monotonicity and the explicit threshold `k >= 8189`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassComparison

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassPayment

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicDebt
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassComparison
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentSummation
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem mass_payment_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "mass_payment_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               mass_payment_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private abbrev PE := RingNormaliser.PolyExpr

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem ringQpow_mono {a b : Q'}
    (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ m, RingNormaliser.qpow a m ≤ RingNormaliser.qpow b m
  | 0 => Q'.le_refl' 1
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_le_mul_of_nonneg (ringQpow_mono ha hab m) hab
        (ringQpow_nonnegative (Q'.le_trans' _ _ _ ha hab) m) ha

private theorem squareCast_eqv_ringQpow_two (n : Nat) :
    Q'.ofNat (n * n) ≈ RingNormaliser.qpow (Q'.ofNat n) 2 := by
  refine Q'.eqv_trans _ (Q'.ofNat n * Q'.ofNat n) _
    (HeatKernelRGStep.ofNat_mul_eqv n n) ?_
  unfold RingNormaliser.qpow
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm (Q'.one_mul_eqv (Q'.ofNat n)))

private def pScalarCubeL : PE :=
  let A : PE := .var 0
  let E : PE := .var 1
  let P : PE := .var 2
  let e : PE := .var 3
  .mul (.mul E P) (.pow (.mul (.pow A 2) e) 3)

private def pScalarCubeR : PE :=
  let A : PE := .var 0
  let E : PE := .var 1
  let P : PE := .var 2
  let e : PE := .var 3
  .mul (.pow A 6) (.mul (.mul E P) (.mul e (.mul e e)))

private theorem pScalarCube_normal :
    RingNormaliser.normalize pScalarCubeL =
      RingNormaliser.normalize pScalarCubeR := by decide

private theorem scalar_cube_algebra (A E P e : Q') :
    (E * P) * RingNormaliser.qpow
        (RingNormaliser.qpow A 2 * e) 3 ≈
      RingNormaliser.qpow A 6 *
        ((E * P) * (e * (e * e))) := by
  let rho : Nat → Q' := fun
    | 0 => A
    | 1 => E
    | 2 => P
    | _ => e
  simpa [pScalarCubeL, pScalarCubeR, RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pScalarCubeL pScalarCubeR pScalarCube_normal rho)

/-- The profile and cubed drift scalar loses at most `351/D^6`. -/
theorem lowerSixPrefixCubicDebtScalar_scaled_six_le_351
    {k : Nat} (hk : 8189 ≤ k) :
    RingNormaliser.qpow (Q'.ofNat (k + 2)) 6 *
        lowerSixPrefixCubicDebtScalar k ≤ Q'.ofNat 351 := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  let P := lowerSixDirichletProfile (k + 1)
  let e := lowerSixDriftExcess k
  let X := RingNormaliser.qpow A 2 * e
  have hA0 : (0 : Q') ≤ A := by
    dsimp only [A]
    exact HeatKernelRGStep.zero_le_ofNat _
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact lowerSixDriftExcess_nonnegative k
  have hX0 : (0 : Q') ≤ X := by
    dsimp only [X]
    exact Q'.mul_nonneg _ _ (ringQpow_nonnegative hA0 2) he0
  have hscale := lowerSixDriftExcess_scaled_le_three
    (show 1 ≤ k by omega)
  have hsquare := squareCast_eqv_ringQpow_two (k + 2)
  have hX : X ≤ Q'.ofNat 3 := by
    dsimp only [X, A, e]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm hsquare))) hscale
  have hcube := ringQpow_mono hX0 hX 3
  have hcube27 : RingNormaliser.qpow X 3 ≤ Q'.ofNat 27 :=
    Q'.le_trans' _ _ _ hcube (Q'.le_of_eqv (by decide))
  have hprofile := lowerSixDirichletProfile_scaled_le_thirteen k
  change E * P ≤ Q'.ofNat 13 at hprofile
  have hmul := Q'.mul_le_mul_of_nonneg hprofile hcube27
    (by decide : (0 : Q') ≤ Q'.ofNat 13)
    (ringQpow_nonnegative hX0 3)
  have h351 : Q'.ofNat 13 * Q'.ofNat 27 ≈ Q'.ofNat 351 := by decide
  have halgebra := scalar_cube_algebra A E P e
  unfold lowerSixPrefixCubicDebtScalar
  dsimp only [A, E, P, e, X] at hmul halgebra ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv halgebra)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv h351))

private def pRatioLeft : PE :=
  let E : PE := .var 0
  .pow (.mul (.const 9) E) 4

private def pRatioLeftExpanded : PE :=
  let E : PE := .var 0
  .mul (.const 6561) (.pow E 4)

private def pRatioRight : PE :=
  let A : PE := .var 0
  .pow (.mul (.const 10) A) 4

private def pRatioRightExpanded : PE :=
  let A : PE := .var 0
  .mul (.const 10000) (.pow A 4)

private theorem pRatioLeft_normal :
    RingNormaliser.normalize pRatioLeft =
      RingNormaliser.normalize pRatioLeftExpanded := by decide

private theorem pRatioRight_normal :
    RingNormaliser.normalize pRatioRight =
      RingNormaliser.normalize pRatioRightExpanded := by decide

private theorem ratio_left_algebra (E : Q') :
    RingNormaliser.qpow (Q'.ofNat 9 * E) 4 ≈
      Q'.ofNat 6561 * RingNormaliser.qpow E 4 := by
  simpa [pRatioLeft, pRatioLeftExpanded, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pRatioLeft pRatioLeftExpanded pRatioLeft_normal (fun _ => E))

private theorem ratio_right_algebra (A : Q') :
    RingNormaliser.qpow (Q'.ofNat 10 * A) 4 ≈
      Q'.ofNat 10000 * RingNormaliser.qpow A 4 := by
  simpa [pRatioRight, pRatioRightExpanded, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pRatioRight pRatioRightExpanded pRatioRight_normal (fun _ => A))

private theorem large_fourth_power_ratio
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 14152320 * RingNormaliser.qpow (Q'.ofNat (k + 3)) 4 ≤
      Q'.ofNat 2916 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 5 := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  have hnatRatio : 9 * (k + 3) ≤ 10 * (k + 2) := by omega
  have hratioCast := CReal.ofNat_le_ofNat hnatRatio
  have h9 : Q'.ofNat (9 * (k + 3)) ≈ Q'.ofNat 9 * E := by
    dsimp only [E]
    exact HeatKernelRGStep.ofNat_mul_eqv 9 (k + 3)
  have h10 : Q'.ofNat (10 * (k + 2)) ≈ Q'.ofNat 10 * A := by
    dsimp only [A]
    exact HeatKernelRGStep.ofNat_mul_eqv 10 (k + 2)
  have hbase : Q'.ofNat 9 * E ≤ Q'.ofNat 10 * A :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv h9)
      (Q'.le_trans' _ _ _ hratioCast (Q'.le_of_eqv h10))
  have hbase0 : (0 : Q') ≤ Q'.ofNat 9 * E :=
    Q'.mul_nonneg _ _ (by decide) (HeatKernelRGStep.zero_le_ofNat _)
  have hpow := ringQpow_mono hbase0 hbase 4
  have hpowers : Q'.ofNat 6561 * RingNormaliser.qpow E 4 ≤
      Q'.ofNat 10000 * RingNormaliser.qpow A 4 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (ratio_left_algebra E))
      (Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv (ratio_right_algebra A)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 14152320)
    hpowers (by decide)
  have hnatThreshold :
      141523200000 ≤ 19131876 * (k + 2) := by omega
  have hthreshold := CReal.ofNat_le_ofNat hnatThreshold
  have hA4 : (0 : Q') ≤ RingNormaliser.qpow A 4 :=
    ringQpow_nonnegative (HeatKernelRGStep.zero_le_ofNat _) 4
  have hthresholdScaled := Q'.mul_le_mul_of_nonneg_right _ _
    (RingNormaliser.qpow A 4) hthreshold hA4
  have hleft :
      Q'.ofNat 6561 *
        (Q'.ofNat 14152320 * RingNormaliser.qpow E 4) ≈
      Q'.ofNat 14152320 *
        (Q'.ofNat 6561 * RingNormaliser.qpow E 4) := by mass_payment_ring
  have hmidLeft :
      Q'.ofNat 14152320 *
        (Q'.ofNat 10000 * RingNormaliser.qpow A 4) ≈
      Q'.ofNat 141523200000 * RingNormaliser.qpow A 4 := by
    mass_payment_ring
  have hthresholdRightCast :
      Q'.ofNat (19131876 * (k + 2)) * RingNormaliser.qpow A 4 ≈
      (Q'.ofNat 19131876 * A) * RingNormaliser.qpow A 4 := by
    exact Q'.mul_eqv_congr_right _ _ _
      (by
        dsimp only [A]
        exact HeatKernelRGStep.ofNat_mul_eqv 19131876 (k + 2))
  have hmidRight :
      Q'.ofNat 19131876 * A * RingNormaliser.qpow A 4 ≈
      Q'.ofNat 6561 *
        (Q'.ofNat 2916 * RingNormaliser.qpow A 5) := by
    change Q'.ofNat 19131876 * A * RingNormaliser.qpow A 4 ≈
      Q'.ofNat 6561 *
        (Q'.ofNat 2916 * (RingNormaliser.qpow A 4 * A))
    mass_payment_ring
  have hchain :
      Q'.ofNat 6561 *
          (Q'.ofNat 14152320 * RingNormaliser.qpow E 4) ≤
        Q'.ofNat 6561 *
          (Q'.ofNat 2916 * RingNormaliser.qpow A 5) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmidLeft)
            (Q'.le_trans' _ _ _ hthresholdScaled
              (Q'.le_trans' _ _ _ (Q'.le_of_eqv hthresholdRightCast)
                (Q'.le_of_eqv hmidRight)))))
  have hcancel := Q'.le_of_mul_le_mul_left hchain
    (by decide : (0 : Q') < Q'.ofNat 6561)
  dsimp only [A, E] at hcancel ⊢
  exact hcancel

private def pCoefficientScaledL : PE :=
  let A : PE := .var 0
  let E : PE := .var 1
  let S : PE := .var 2
  .mul (.pow A 2)
    (.mul (.const 40320) (.mul (.pow A 4) (.mul S (.pow E 4))))

private def pCoefficientScaledM : PE :=
  let A : PE := .var 0
  let E : PE := .var 1
  let S : PE := .var 2
  .mul (.const 40320) (.mul (.mul (.pow A 6) S) (.pow E 4))

private def pCoefficientScaledR : PE :=
  let A : PE := .var 0
  .mul (.pow A 2) (.mul (.const 2916) (.pow A 3))

private def pCoefficientScaledR5 : PE :=
  let A : PE := .var 0
  .mul (.const 2916) (.pow A 5)

private theorem pCoefficientScaledL_normal :
    RingNormaliser.normalize pCoefficientScaledL =
      RingNormaliser.normalize pCoefficientScaledM := by decide

private theorem pCoefficientScaledR_normal :
    RingNormaliser.normalize pCoefficientScaledR =
      RingNormaliser.normalize pCoefficientScaledR5 := by decide

/-- The complete constants left after moment and inter-scale comparison fit
inside the `486`-scaled old Hermite mass coefficient. -/
theorem lowerSixCubicDebt_momentCoefficient_le_massCoefficient
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 40320 *
        (RingNormaliser.qpow (Q'.ofNat (k + 2)) 4 *
          (lowerSixPrefixCubicDebtScalar k *
            RingNormaliser.qpow (Q'.ofNat (k + 3)) 4)) ≤
      Q'.ofNat 2916 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 := by
  let A := Q'.ofNat (k + 2)
  let E := Q'.ofNat (k + 3)
  let S := lowerSixPrefixCubicDebtScalar k
  have hscalar := lowerSixPrefixCubicDebtScalar_scaled_six_le_351 hk
  change RingNormaliser.qpow A 6 * S ≤ Q'.ofNat 351 at hscalar
  have hE4 : (0 : Q') ≤ RingNormaliser.qpow E 4 :=
    ringQpow_nonnegative (HeatKernelRGStep.zero_le_ofNat _) 4
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 40320)
    (Q'.mul_le_mul_of_nonneg_right _ _
      (RingNormaliser.qpow E 4) hscalar hE4) (by decide)
  have hratio := large_fourth_power_ratio hk
  change Q'.ofNat 14152320 * RingNormaliser.qpow E 4 ≤
    Q'.ofNat 2916 * RingNormaliser.qpow A 5 at hratio
  have hA2pos : (0 : Q') < RingNormaliser.qpow A 2 := by
    change (0 : Q') < (((1 : Q') * A) * A)
    have hApos : (0 : Q') < A := by
      dsimp only [A]
      exact Q'.ofNat_succ_pos (k + 1)
    exact Q'.mul_pos (Q'.mul_pos (by decide) hApos) hApos
  have hleft :
      RingNormaliser.qpow A 2 *
        (Q'.ofNat 40320 *
          (RingNormaliser.qpow A 4 * (S * RingNormaliser.qpow E 4))) ≈
      Q'.ofNat 40320 *
        ((RingNormaliser.qpow A 6 * S) * RingNormaliser.qpow E 4) := by
    simpa [pCoefficientScaledL, pCoefficientScaledM, RingNormaliser.eval] using
      (RingNormaliser.poly_identity_of_normal_eq
        pCoefficientScaledL pCoefficientScaledM
        pCoefficientScaledL_normal
        (fun | 0 => A | 1 => E | _ => S))
  have hmid :
      Q'.ofNat 40320 *
        (Q'.ofNat 351 * RingNormaliser.qpow E 4) ≈
      Q'.ofNat 14152320 * RingNormaliser.qpow E 4 := by
    mass_payment_ring
  have hright :
      Q'.ofNat 2916 * RingNormaliser.qpow A 5 ≈
      RingNormaliser.qpow A 2 *
        (Q'.ofNat 2916 * RingNormaliser.qpow A 3) := by
    exact Q'.eqv_symm (by
      simpa [pCoefficientScaledR, pCoefficientScaledR5, RingNormaliser.eval] using
        (RingNormaliser.poly_identity_of_normal_eq
          pCoefficientScaledR pCoefficientScaledR5
          pCoefficientScaledR_normal (fun _ => A)))
  have hcancel :
      RingNormaliser.qpow A 2 *
          (Q'.ofNat 40320 *
            (RingNormaliser.qpow A 4 * (S * RingNormaliser.qpow E 4))) ≤
        RingNormaliser.qpow A 2 *
          (Q'.ofNat 2916 * RingNormaliser.qpow A 3) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmid)
          (Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hright))))
  have hout := Q'.le_of_mul_le_mul_left hcancel hA2pos
  dsimp only [A, E, S] at hout ⊢
  exact hout

private theorem lowerSixPrefixCubicDebtScalar_nonnegative (k : Nat) :
    (0 : Q') ≤ lowerSixPrefixCubicDebtScalar k := by
  unfold lowerSixPrefixCubicDebtScalar
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (HeatKernelRGStep.zero_le_ofNat _)
      (lowerSixDirichletProfile_nonnegative_local _))
    (Q'.mul_nonneg _ _
      (lowerSixDriftExcess_nonnegative k)
      (Q'.mul_nonneg _ _
        (lowerSixDriftExcess_nonnegative k)
        (lowerSixDriftExcess_nonnegative k)))

/-- One old positive Hermite mass pays all four clearing-scale copies of the
finite cubic Taylor debt at every scale `k >= 8189`. -/
theorem lowerSixFourClearingScaleCubicDebt_le_HermiteMass_large
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 4 * lowerSixQuadraticTaylorClearingScale k *
        prefixCubicDebtSum k ≤
      lowerSixHermiteMassSum k := by
  let A := Q'.ofNat (k + 2)
  let E4 := lowerSixQPower (k + 3) 4
  let S := lowerSixPrefixCubicDebtScalar k
  let M0 := lowerSixNextGaussianMoment k 0 (thetaWindowRight k)
  let W := lowerSixHermiteWeightSum k
  let B := prefixCubicDebtSum k
  let C := lowerSixQuadraticTaylorClearingScale k
  let F := Q'.ofNat 4 * C
  let Mass := lowerSixHermiteMassSum k
  have hpay := prefixCubicDebt_momentPaid_large hk
  change Q'.ofNat 486 * B ≤ Q'.ofNat 105 * (S * (E4 * M0)) at hpay
  have hF0 : (0 : Q') ≤ F := by
    dsimp only [F, C]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt (lowerSixQuadraticTaylorClearingScale_pos k))
  have hscaledPay := Q'.mul_le_mul_of_nonneg_left _ _ F hpay hF0
  have hM0 := lowerSixNextGaussianMoment_zero_le_two_oldWeightSum_large hk
  change M0 ≤ Q'.ofNat 2 * W at hM0
  have hS0 : (0 : Q') ≤ S := by
    dsimp only [S]
    exact lowerSixPrefixCubicDebtScalar_nonnegative k
  have hE40 : (0 : Q') ≤ E4 := by
    dsimp only [E4, lowerSixQPower]
    exact ringQpow_nonnegative (HeatKernelRGStep.zero_le_ofNat _) 4
  have hmultiplier0 :
      (0 : Q') ≤ ((F * Q'.ofNat 105) * S) * E4 :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ hF0 (by decide)) hS0) hE40
  have hM0scaled := Q'.mul_le_mul_of_nonneg_left _ _
    (((F * Q'.ofNat 105) * S) * E4) hM0 hmultiplier0
  have hpayRight :
      F * (Q'.ofNat 105 * (S * (E4 * M0))) ≈
        (((F * Q'.ofNat 105) * S) * E4) * M0 := by
    mass_payment_ring
  have hcoefficient :=
    lowerSixCubicDebt_momentCoefficient_le_massCoefficient hk
  change Q'.ofNat 40320 *
      (RingNormaliser.qpow A 4 * (S * E4)) ≤
        Q'.ofNat 2916 * RingNormaliser.qpow A 3 at hcoefficient
  have hW0 : (0 : Q') ≤ W := by
    dsimp only [W, lowerSixHermiteWeightSum]
    induction growingAnchor k with
    | zero => exact Q'.le_refl' 0
    | succ N ih =>
        rw [RationalTail.finSum_succ]
        exact Q'.zero_le_add _ _ ih
          (lowerSixModeWeight_nonnegative k (N + 1))
  have hcoefficientW := Q'.mul_le_mul_of_nonneg_right _ _ W
    hcoefficient hW0
  have hpost :
      ((((F * Q'.ofNat 105) * S) * E4) * (Q'.ofNat 2 * W)) ≈
        (Q'.ofNat 40320 *
          (RingNormaliser.qpow A 4 * (S * E4))) * W := by
    dsimp only [F, C, A]
    unfold lowerSixQuadraticTaylorClearingScale
    mass_payment_ring
  have hmass := lowerSixHermiteMassSum_eqv_scaledWeightSum k
  change Mass ≈
    (Q'.ofNat 6 * RingNormaliser.qpow A 3) * W at hmass
  have hmassScaled : Q'.ofNat 486 * Mass ≈
      (Q'.ofNat 2916 * RingNormaliser.qpow A 3) * W := by
    refine Q'.eqv_trans _
      (Q'.ofNat 486 *
        ((Q'.ofNat 6 * RingNormaliser.qpow A 3) * W)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hmass
    · mass_payment_ring
  have hrightBound :
      F * (Q'.ofNat 105 * (S * (E4 * M0))) ≤
        Q'.ofNat 486 * Mass :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpayRight)
      (Q'.le_trans' _ _ _ hM0scaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpost)
          (Q'.le_trans' _ _ _ hcoefficientW
            (Q'.le_of_eqv (Q'.eqv_symm hmassScaled)))))
  have hleft : Q'.ofNat 486 * (F * B) ≈
      F * (Q'.ofNat 486 * B) := by mass_payment_ring
  have hcancel : Q'.ofNat 486 * (F * B) ≤
      Q'.ofNat 486 * Mass :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaledPay hrightBound)
  have hout := Q'.le_of_mul_le_mul_left hcancel
    (by decide : (0 : Q') < Q'.ofNat 486)
  dsimp only [F, C, B, Mass] at hout ⊢
  exact hout

#print axioms lowerSixPrefixCubicDebtScalar_scaled_six_le_351
#print axioms lowerSixCubicDebt_momentCoefficient_le_massCoefficient
#print axioms lowerSixFourClearingScaleCubicDebt_le_HermiteMass_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentMassPayment
