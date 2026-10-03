/-
# Derived angular Poincare bound for ORIGINAL conditional heat

The actual square interpolation, its literal scalar coefficient derivative,
the proved Bochner energy order and particular source endpoints give
H[W*(C_w(p^2)-(C_w p)^2)] <= (1-w^2)*H[W*C_w(Gamma(p))].
The source may depend on the existing retained output and all spectators.
W is any already-certified original output weight, including zero. Cutoff
guards are computed once from this fixed source; neither a derivative bound
nor conditional variance bound is an assumed premise.

This is one-link ordinary reference heat variance. Active-product joins,
the interacting signed cost versus SAME surviving norm, changing-family
scaling, OS, physical calibration, continuum QFT and Clay remain separate.
-/

import YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation
import YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints
import YMGap.Continuum.RationalLaurentQuadraticIncrement

namespace YMGap.Continuum.SU2QuaternionConditionalAngularPoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionHeadHeatCurves (squareNomeRows)
open YMGap.Continuum.QuaternionHaarNomeRows
open YMGap.Continuum.SU2QuaternionInverseNomeKernel (inverseNomeExponent)
open YMGap.Continuum.SU2QuaternionConditionalLaurentRows
open YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation
open YMGap.Continuum.SU2QuaternionHeatInterpolationEndpoints
open YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation
open YMGap.Continuum.RationalLaurentIntervalOrder (laurent)
open YMGap.Continuum.RationalLaurentQuadraticIncrement

local infix:50 " ≈ " => Q'.eqv

/-- Literal numerator of the ORIGINAL Haar-weighted square interpolation. -/
def squareNumerator (tail : Nat) (w : Q') (K : Nat) (p W : RatPoly) : Poly :=
  weightedNumerator tail W (conditionalLaurentRows w K (squareNomeRows tail p))

/-- Fixed-source computed onset retaining its Bochner margin and endpoints. -/
def poincareCutoff (tail : Nat) (p : RatPoly) : Nat :=
  max (marginCutoff tail p) (interpolationEndpointCutoff tail p)

/-- Original own-mean conditional variance, not a detached proxy. -/
def heatVariance (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (conditionalHeat w K (polyMul p p))
    (polyNeg (polyMul (conditionalHeat w K p) (conditionalHeat w K p)))

theorem squareNumerator_original_pin (tail : Nat) (w : Q') (K : Nat)
    (p W : RatPoly) (r : Q') :
    laurent (squareNumerator tail w K p W) (inverseNomeExponent K) r ≈
      quaternionHaar tail (polyMul W (squareInterpolation tail w K p r)) :=
  weightedNumerator_laurent_pin tail W
    (conditionalLaurentRows w K (squareNomeRows tail p)) (inverseNomeExponent K) r

/-- The literal scalar formal derivative of the actual square numerator is
the already-proved original weighted energy, not a newly assumed generator. -/
theorem squareNumerator_euler_energy (tail : Nat) (ht : 0 < tail)
    (w : Q') (K : Nat) (p W : RatPoly) (r : Q') (hr : (0 : Q') < r)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    Q'.recip (RGTransport.qpow r (inverseNomeExponent K)) *
      (r*QPoly.eval (pderiv (squareNumerator tail w K p W)) r +
        -(Q'.ofNat (inverseNomeExponent K)*QPoly.eval (squareNumerator tail w K p W) r)) ≈
      2*quaternionHaar tail (polyMul W (angularInterpolation tail w K p r)) := by
  let A := conditionalLaurentRows w K (squareNomeRows tail p)
  let s := Q'.recip (RGTransport.qpow r (inverseNomeExponent K))
  have he : s*(r*QPoly.eval (pderiv (squareNumerator tail w K p W)) r +
      -(Q'.ofNat (inverseNomeExponent K)*QPoly.eval (squareNumerator tail w K p W) r)) ≈
      quaternionHaar tail (polyMul W (squareInterpolationEuler tail w K p r)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left s _ _ (weightedNumerator_euler_eval tail W A (inverseNomeExponent K) r))
      (Q'.eqv_symm (quaternionHaar_polyMul_smul_right tail s W _))
  have hG := haar_of_coeff (blocks := tail)
    ((angularInterpolation_original_pin tail w K p r hr).mul_left W)
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ ((squareInterpolation_euler tail ht w K p r hr hp) W)
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right tail 2 W _)
        (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hG))))

/-- The TRUE square increment follows from the constructed energy estimate,
without an integration axiom or an assumed endpoint/variance inequality. -/
theorem squareInterpolation_weighted_increment (tail : Nat) (ht : 0 < tail)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : marginCutoff tail p ≤ K) (P : Certificate tail W) :
    quaternionHaar tail (polyMul W (squareInterpolation tail w K p 1)) +
      -quaternionHaar tail (polyMul W (squareInterpolation tail w K p w)) ≤
      (1-w*w)*quaternionHaar tail (polyMul W (angularInterpolation tail w K p 1)) := by
  have hEuler : ∀ r : Q', w ≤ r → r ≤ (1 : Q') →
      Q'.recip (RGTransport.qpow r (inverseNomeExponent K)) *
        (r*QPoly.eval (pderiv (squareNumerator tail w K p W)) r +
          -(Q'.ofNat (inverseNomeExponent K)*QPoly.eval (squareNumerator tail w K p W) r)) ≤
        2*(r*r)*quaternionHaar tail (polyMul W (angularInterpolation tail w K p 1)) := by
    intro r hr hr1
    have hrpos := HeatKernelRGStep.lt_of_lt_of_le hw0 hr
    have horder := angularInterpolation_weighted_quadratic tail ht w hw0 hw1 K p W hp hK P r hr hr1
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (squareNumerator_euler_energy tail ht w K p W r hrpos hp))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 horder (by decide))
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))
  have hinc := laurent_quadratic_increment (squareNumerator tail w K p W)
    (inverseNomeExponent K) w hw0 hw1
    (quaternionHaar tail (polyMul W (angularInterpolation tail w K p 1))) hEuler
  have hpin := Q'.add_eqv_congr' (squareNumerator_original_pin tail w K p W 1)
    (Q'.neg_eqv_congr _ _ (squareNumerator_original_pin tail w K p W w))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin) hinc

private theorem weighted_neg (blocks : Nat) (W p : RatPoly) :
    quaternionHaar blocks (polyMul W (polyNeg p)) ≈
      -quaternionHaar blocks (polyMul W p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((neg_smul p).mul_left W))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks (-1) W p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

/-- Derived one-link angular Poincare inequality for the SAME conditional
mean, arbitrary original source/output dependence and certified output W.
The explicit onset belongs to this fixed source, not a changing family. -/
theorem conditionalHeat_weighted_angular_variance (tail : Nat) (ht : 0 < tail)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : poincareCutoff tail p ≤ K) (P : Certificate tail W) :
    quaternionHaar tail (polyMul W (heatVariance w K p)) ≤
      (1-w*w)*quaternionHaar tail (polyMul W (conditionalHeat w K (angularSquare p))) := by
  have hmargin : marginCutoff tail p ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have hendpoint : interpolationEndpointCutoff tail p ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  have hinc := squareInterpolation_weighted_increment tail ht w hw0 hw1 K p W hp hmargin P
  have h1 := (squareInterpolation_one tail w K p hp) W
  have hw := (squareInterpolation_left_endpoint tail ht w hw0 K p hp hendpoint) W
  have hG := (angularInterpolation_one tail w K p hp) W
  have hv : quaternionHaar tail (polyMul W (heatVariance w K p)) ≈
      quaternionHaar tail (polyMul W (conditionalHeat w K (polyMul p p))) +
        -quaternionHaar tail (polyMul W (polyMul (conditionalHeat w K p) (conditionalHeat w K p))) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right tail W _ _)
      (Q'.add_eqv_congr_left _ _ _ (weighted_neg tail W _))
  have hleft := Q'.eqv_trans _ _ _ hv
    (Q'.eqv_symm (Q'.add_eqv_congr' h1 (Q'.neg_eqv_congr _ _ hw)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hinc (Q'.le_of_eqv (Q'.mul_eqv_congr_left (1-w*w) _ _ hG)))

end YMGap.Continuum.SU2QuaternionConditionalAngularPoincare

#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.squareNumerator
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.poincareCutoff
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.heatVariance
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.squareNumerator_original_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.squareNumerator_euler_energy
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.squareInterpolation_weighted_increment
#print axioms YMGap.Continuum.SU2QuaternionConditionalAngularPoincare.conditionalHeat_weighted_angular_variance
