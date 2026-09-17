/-
# Strict contraction of the original one-link heat on all centered polynomials

The input certificates and BOTH marginal identities are supplied by the
actual complete SU(2) character packet, not assumed mixing data. Subtract
headFloor(w) before weighted Cauchy--Schwarz to obtain squared-norm rate
(1-headFloor(w))^2 < 1 for every rational 0<w<1 and every K>=headCutoff(w).

The kernel map, Haar norm and centering are unchanged. There is no
character-diagonal restriction on the input polynomial, and no dependence
of the returned rate on its degree or on the late representation cutoff.
The rate DOES depend on the nome. Tensorizing across the actual kinetic
link set (including unused fringe projections), retaining spatial action
weights, and comparison with the physical OS transfer remain separate
obligations. This is not an interacting Yang--Mills spectral gap.
-/

import YMGap.Continuum.SU2QuaternionHaarMarkovContraction
import YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

namespace YMGap.Continuum.SU2QuaternionRelativeHeatContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarMarkovContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

local infix:50 " ≈ " => Q'.eqv

/-- Actual partial Haar integration against the full finite heat packet. -/
def heatMap (w : Q') (K : Nat) (f : RatPoly) : RatPoly :=
  kernelMap 1 (relativeHeat w K) f

theorem heatMap_supported (w : Q') (K : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks 1 f) : SupportedQuaternionBlocks 1 (heatMap w K f) :=
  kernelMap_supported (relativeHeat_supported w K) hf

/-- Exact mean preservation at every cutoff, before any positivity guard. -/
theorem heatMap_mean (w : Q') (K : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 1 (heatMap w K f) ≈ quaternionHaar 1 f :=
  Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHeads 1 1 _)
    (relativeHeat_lower_marginal w K f hf)

def relativeHeat_certificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate 2 (relativeHeat w K) :=
  .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (by decide)
    (fun | 0 => relativeHeat w K | _ => cap (headFloor w)))
    ((relativeHeat_floorCertificate hw0 hw1 K hK).add
      (.constant 2 (headFloor w) (Q'.le_of_lt (headFloor_positive hw0 hw1))))

/-- Ordinary Haar contraction, with no prefixCap penalty. -/
theorem heatMap_square_contraction {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f) :
    quaternionHaar 1 (polyMul (heatMap w K f) (heatMap w K f)) ≤
      quaternionHaar 1 (polyMul f f) :=
  kernelMap_square_contraction (relativeHeat_lower_marginal w K)
    (relativeHeat_upper_marginal w K) (relativeHeat_certificate hw0 hw1 K hK)
    (relativeHeat_supported w K) hf

/-- Nome-dependent norm rate, not a spatial or physical mass rate. -/
def heatRate (w : Q') : Q' := 1 + -headFloor w

def squaredHeatRate (w : Q') : Q' := heatRate w * heatRate w

private theorem floor_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    headFloor w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)

theorem heatRate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ heatRate w := Q'.sub_nonneg_of_le (floor_le_one hw0 hw1)

theorem heatRate_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    heatRate w < (1 : Q') := by
  have hp : (0 : Int) < (headFloor w).num := Q'.num_pos_of_pos (headFloor_positive hw0 hw1)
  change (((1 : Int) * ((headFloor w).den : Int) + (-(headFloor w).num) * (1 : Int)) * (1 : Int)) <
    ((1 : Int) * (((1 : Nat) * (headFloor w).den : Nat) : Int))
  simp only [Nat.one_mul, Int.one_mul, Int.mul_one]
  omega

theorem squaredHeatRate_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ squaredHeatRate w :=
  Q'.mul_nonneg _ _ (heatRate_nonnegative hw0 hw1) (heatRate_nonnegative hw0 hw1)

theorem squaredHeatRate_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    squaredHeatRate w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.le_of_lt (heatRate_lt_one hw0 hw1)) (heatRate_nonnegative hw0 hw1))
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) (heatRate_lt_one hw0 hw1)

/-- All supported Haar-centered polynomials, not only a diagonal character sector. -/
theorem heatMap_centered_square_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    {f : RatPoly} (hf : SupportedQuaternionBlocks 1 f)
    (hc : quaternionHaar 1 f ≈ 0) :
    quaternionHaar 1 (polyMul (heatMap w K f) (heatMap w K f)) ≤
      squaredHeatRate w * quaternionHaar 1 (polyMul f f) :=
  kernelMap_centered_square_bound (relativeHeat_lower_marginal w K)
    (relativeHeat_upper_marginal w K) (floor_le_one hw0 hw1)
    (relativeHeat_floorCertificate hw0 hw1 K hK) (relativeHeat_supported w K) hf hc

end YMGap.Continuum.SU2QuaternionRelativeHeatContraction

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatMap
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatMap_supported
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatMap_mean
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.relativeHeat_certificate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatMap_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatRate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.squaredHeatRate
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatRate_lt_one
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.squaredHeatRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.squaredHeatRate_lt_one
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatContraction.heatMap_centered_square_bound
