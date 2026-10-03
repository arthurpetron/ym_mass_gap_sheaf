/-
# Actual ORIGINAL centered Young-cost cap on the cutoff-one cube

The paid original spatial insertion retains Vcube and the literal original
U=T1. Their shared-coordinate interval product bounds Vcube*U^2, tested
against the supported square (F-c)^2. Bare F's norm one and mean zero are
used only after this source transport. No OWN variance, gain sign, head
cutoff, or changing-family estimate is identified with this cost.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (bent_square_haar bent_haar_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeFundamentalInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumInterval
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall
  (originalOddMean originalOddMean_abs_le meanCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (alphaCap deltaCap directKernelGuard_of_coeffW_cap cubeFundamentalDelta_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredGainTransport
  (centeredOriginalEndpoint centeredOriginalYoungCost youngCost_cube_pin)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_moment_expansion)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks cubeWeight transferStep centeredOriginalYoungCost
  bentObservable cubeFundamentalDelta

private def psi (c : Q') : RatPoly := polyAdd bentObservable (polySmul (-c) polyOne)

private theorem psi_supported (c : Q') : SupportedQuaternionBlocks N (psi c) :=
  supported_add bentObservable_supported (polySmul_supported (supported_one N) (-c))

private theorem unit_remainder_cancel (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd polyOne (polyAdd p (polyNeg polyOne))) p :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
    (by decide) (fun | 0 => p | _ => polyOne)

private def V_interval (w : Q') (ha : (0 : Q') ≤ coeffW w 1) :
    Interval N (cubeWeight w 1) (1+cubeFundamentalDelta w) := by
  have hs : SupportedQuaternionBlocks N (cubeWeight w 1) := by
    unfold cubeWeight
    exact heatProduct_supported w 1 2 cubeFaces
  exact Interval.ofCoeff hs (unit_remainder_cancel (cubeWeight w 1)).symm
    ((Interval.one N).add (cubeFundamentalInterval w ha))

private def U_interval (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1*2 ≤ 1) :
    Interval N (transferStep w 1 2 polyOne) (1+cubeFundamentalDelta w) :=
  Interval.ofCoeff (transferStep_supported w 1 2 (supported_one N))
    (unit_remainder_cancel (transferStep w 1 2 polyOne)).symm
    ((Interval.one N).add (cubeVacuumInterval w ha hcap))

private theorem haar_one : quaternionHaar N polyOne ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one N)) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.add_zero' 1))

private theorem bare_centered_square (c : Q') :
    quaternionHaar N (polyMul (psi c) (psi c)) ≈ 1+c*c := by
  have hs : RatPolyCoeffEqv (shifted bentObservable c) (psi c) :=
    (RatPolyCoeffEqv.one_smul bentObservable).add (RatPolyCoeffEqv.refl _)
  have hstart : quaternionHaar N (polyMul (psi c) (psi c)) ≈
      quaternionHaar N (polyMul polyOne
        (polyMul (shifted bentObservable c) (shifted bentObservable c))) :=
    haar_of_coeff (blocks := N) ((hs.symm.mul hs.symm).trans (RatPolyCoeffEqv.one_mul _).symm)
  have h0 := shifted_moment_expansion (Certificate.one N) bentObservable_supported c
  have h2 : quaternionHaar N (polyMul polyOne (polyMul bentObservable bentObservable)) ≈ 1 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul _)) bent_square_haar
  have h1 : quaternionHaar N (polyMul polyOne bentObservable) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.one_mul _)) bent_haar_zero
  have he := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' h2 (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (2*c) _ _ h1)))
    (Q'.mul_eqv_congr_left (c*c) _ _ haar_one)
  exact Q'.eqv_trans _ _ _ hstart (Q'.eqv_trans _ _ _ h0
    (Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.mul (.mul (.const 2) (.var 0)) (.const 0))))
        (.mul (.mul (.var 0) (.var 0)) (.const 1)))
      (.add (.const 1) (.mul (.var 0) (.var 0))) (by decide) (fun _ => c))))

private theorem triple_power (b : Q') : b*(b*b) ≈ b^3 := by
  change b*(b*b) ≈ b*(b*(b*1))
  exact Q'.mul_eqv_congr_left b _ _
    (Q'.mul_eqv_congr_left b _ _ (Q'.eqv_symm (Q'.mul_one_eqv b)))

/-- Sharp raw-cost ceiling, with arbitrary center and the ORIGINAL U retained. -/
theorem centeredYoungCost_sharp_upper (w c : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1*2 ≤ 1) :
    centeredOriginalYoungCost w c ≤ (1+cubeFundamentalDelta w)^3*(1+c*c) := by
  let U := U_interval w ha hcap
  let V := V_interval w ha
  have hpow : (1+cubeFundamentalDelta w)*
      ((1+cubeFundamentalDelta w)*(1+cubeFundamentalDelta w)) ≈ (1+cubeFundamentalDelta w)^3 :=
    triple_power (1+cubeFundamentalDelta w)
  let R := Interval.changeCap hpow (V.mul (U.mul U))
  have hcost : centeredOriginalYoungCost w c ≈
      quaternionHaar N (polyMul (polyMul (psi c) (psi c))
        (polyMul (cubeWeight w 1)
          (polyMul (transferStep w 1 2 polyOne) (transferStep w 1 2 polyOne)))) := by
    have hp : RatPolyCoeffEqv
        (polyMul (cubeWeight w 1) (polyMul (centeredOriginalEndpoint w c) (centeredOriginalEndpoint w c)))
        (polyMul (polyMul (psi c) (psi c))
          (polyMul (cubeWeight w 1) (polyMul (transferStep w 1 2 polyOne) (transferStep w 1 2 polyOne)))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 2) (.var 2)) (.mul (.var 0) (.mul (.var 1) (.var 1))))
        (by decide) (fun
          | 0 => cubeWeight w 1
          | 1 => transferStep w 1 2 polyOne
          | _ => psi c)
    exact Q'.eqv_trans _ _ _ (youngCost_cube_pin w c) (haar_of_coeff (blocks := N) hp)
  have h := R.weighted_haar_bound (Certificate.square (psi c) (psi_supported c))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcost)
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (bare_centered_square c)))))

/-- A coarse numerical ceiling for the original cost in the explicit finite regime. -/
theorem centeredYoungCost_le_128 (w c : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hcap : coeffW w 1*2 ≤ 1) (hdelta : cubeFundamentalDelta w ≤ HalfPow.half)
    (hc : Q'.abs c ≤ Q'.mkPos 1 4 (by decide)) : centeredOriginalYoungCost w c ≤ 128 := by
  let quarter : Q' := Q'.mkPos 1 4 (by decide)
  have hcc : c*c ≤ quarter*quarter := Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le c c)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs c) hc (Q'.abs_nonneg c))
        (Q'.mul_le_mul_of_nonneg_right _ _ quarter hc (by decide))))
  have hbase0 : (0 : Q') ≤ 1+cubeFundamentalDelta w :=
    Q'.zero_le_add _ _ Q'.zero_le_one (cubeFundamentalDelta_nonnegative w ha)
  have hbase : 1+cubeFundamentalDelta w ≤ 1+HalfPow.half := Q'.add_le_add_left 1 _ _ hdelta
  have hpow : (1+cubeFundamentalDelta w)^3 ≤ (1+HalfPow.half)^3 :=
    CRealLog.pow_le_pow_base _ _ hbase0 hbase 3
  have hmoment : (0 : Q') ≤ 1+c*c :=
    Q'.zero_le_add _ _ Q'.zero_le_one (SumOfSquares.q_mul_self_nonneg c)
  have hprod := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (1+c*c) hpow hmoment)
    (Q'.mul_le_mul_of_nonneg_left _ _ ((1+HalfPow.half)^3)
      (Q'.add_le_add_left 1 _ _ hcc) (by decide))
  exact Q'.le_trans' _ _ _ (centeredYoungCost_sharp_upper w c ha hcap)
    (Q'.le_trans' _ _ _ hprod (by decide))

/-- Actual OWN odd centering supplies every guard for the original numerical cost. -/
theorem originalOwnYoungCost_le_128 (w : Q') (ha : (0 : Q') ≤ coeffW w 1)
    (hα : coeffW w 1 ≤ alphaCap) :
    centeredOriginalYoungCost w (originalOddMean w ha hα) ≤ 128 :=
  centeredYoungCost_le_128 w (originalOddMean w ha hα) ha
    (directKernelGuard_of_coeffW_cap w hα)
    (Q'.le_trans' _ _ _ (cubeFundamentalDelta_le_cap w ha hα)
      (by decide : deltaCap ≤ HalfPow.half))
    (originalOddMean_abs_le w ha hα)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap.centeredYoungCost_sharp_upper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap.centeredYoungCost_le_128
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap.originalOwnYoungCost_le_128
