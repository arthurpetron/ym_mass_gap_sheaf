/-
# Finite product-map annihilation of the ordinary-Haar radical

The finite ordinary-Haar GNS carrier is now explicit.  This module consumes
the already checked centered product-map square bound and proves its first
quotient-facing consequence: a Haar-null supported input is sent to a
Haar-null output by a finite product heat map.

All regulator and list hypotheses remain explicit.  The result is not yet a
well-defined map on radical *classes* (that additionally requires a
difference-compatibility proof), and it is not a spectral-gap or continuum
statement.
-/

import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
import YMGap.Continuum.SU2QuaternionProductHeatTensorization
import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.SU2HeatCutoffCasimirBound

namespace YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionProductHeatTensorization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem eqv_zero_of_nonneg_of_le_zero {x : Q'}
    (hlo : (0 : Q') ≤ x) (hhi : x ≤ (0 : Q')) : x ≈ 0 := by
  show x.num * ((0 : Q').den : Int) = (0 : Q').num * (x.den : Int)
  exact Int.le_antisymm hhi hlo

/-- A finite product heat map sends a Haar-radical supported input to a
Haar-radical output.  The proof uses the explicit centered contraction and
the same ordinary finite Haar form on both sides. -/
theorem productMap_radical_zero
    (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hnodup : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f)
    (hrad : finiteHaarPair n f f ≈ 0) :
    finiteHaarPair n
        (productMap n w K ids f)
        (productMap n w K ids f) ≈ 0 := by
  have hrad' :
      ((finiteHaarGNSData n).B ⟨f, hf⟩ ⟨f, hf⟩).eqv 0 := by
    simpa [finiteHaarGNSData, finiteHaarPair] using hrad
  have hcross := (finiteHaarGNSData n).radical_form_zero
    ⟨f, hf⟩ ⟨polyOne, supported_one n⟩ hrad'
  have hone : finiteHaarPair n f polyOne ≈ quaternionHaar n f := by
    unfold finiteHaarPair
    exact haar_of_coeff (RatPolyCoeffEqv.mul_one f)
  have hcenter : quaternionHaar n f ≈ 0 := by
    have hleft : finiteHaarPair n f polyOne ≈ 0 := hcross
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hone) hleft
  have hbound := productMap_centered_square_bound n hw0 hw1 K hK ids
    hnodup hids hf hcenter
  have hupper : finiteHaarPair n
      (productMap n w K ids f) (productMap n w K ids f) ≤ 0 := by
    have hzero : squaredHeatRate w * finiteHaarPair n f f ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (squaredHeatRate w)
          (finiteHaarPair n f f) 0 hrad)
        (Q'.mul_zero_eqv (squaredHeatRate w))
    have hbound' : finiteHaarPair n
        (productMap n w K ids f) (productMap n w K ids f) ≤
        squaredHeatRate w * finiteHaarPair n f f := by
      simpa only [finiteHaarPair] using hbound
    exact Q'.le_trans' _ _ _ hbound' (Q'.le_of_eqv hzero)
  have hnonneg : (0 : Q') ≤ finiteHaarPair n
      (productMap n w K ids f) (productMap n w K ids f) := by
    unfold finiteHaarPair
    exact quaternionHaar_square_nonnegative n
      (productMap n w K ids f)
      (productMap_supported n w K ids hids hf)
  exact eqv_zero_of_nonneg_of_le_zero hnonneg hupper

end YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical

#print axioms YMGap.Continuum.SU2QuaternionFiniteHaarProductMapRadical.productMap_radical_zero
