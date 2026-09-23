/-
# All-cutoff norm contraction of the original full product through cyclic steps

The proved cyclic/head identification transfers the actual head norm bound
through two Haar-isometric reversals. Iteration then bounds the ORIGINAL
fully active product map, at every finite cutoff and 0<=w<=1, without a
pointwise heat floor. This is nonexpansion, not a strict rate or the desired
sum-of-angular-defects estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
import YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction

namespace YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionBlockReversal
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatCyclicFold
open YMGap.Continuum.SU2QuaternionProductHeatCyclicRotation
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem reindex_norm {n : Nat} (s : QuaternionBlockInvolution n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n (polyMul (reindexQuaternionPolynomial s p)
      (reindexQuaternionPolynomial s p)) ≈ quaternionHaar n (polyMul p p) := by
  rw [← reindexQuaternionPolynomial_mul]
  exact quaternionHaar_reindex s _ (supported_polyMul hp hp)

/-- Coordinate rotation need not be self-adjoint to preserve the norm. -/
theorem cycleStep_square_contraction (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1)
        (polyMul (cycleStep (tail+1) w K p) (cycleStep (tail+1) w K p)) ≤
      quaternionHaar (tail+1) (polyMul p p) := by
  have h := cycleStep_rotation_carrier tail w K p hp
  have hsq := haar_of_carrier (HaarCarrierEqv.mul h h)
  have hm := headMap_supported tail w K (reindex_supported (reverseTailBlocks (tail+1)) p)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (reindex_norm (reverseBlocks (tail+1)) _ hm))
      (Q'.le_trans' _ _ _
        (headMap_square_contraction tail hw0 hw1 K _ (reindex_supported _ _))
        (Q'.le_of_eqv (reindex_norm (reverseTailBlocks (tail+1)) p hp))))

/-- Every actual cyclic prefix is nonexpansive on its n-block carrier. -/
theorem cycleIterate_square_contraction (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) :
    ∀ (m : Nat) (p : RatPoly), SupportedQuaternionBlocks (tail+1) p →
      quaternionHaar (tail+1)
        (polyMul (cycleIterate (tail+1) w K m p) (cycleIterate (tail+1) w K m p)) ≤
      quaternionHaar (tail+1) (polyMul p p)
  | 0, _, _ => Q'.le_refl' _
  | m+1, p, hp => Q'.le_trans' _ _ _
      (cycleIterate_square_contraction tail hw0 hw1 K m _ (cycleStep_supported _ _ _ hp))
      (cycleStep_square_contraction tail hw0 hw1 K p hp)

/-- The ORIGINAL fully active product map is nonexpansive at every cutoff.
No centering, sufficient-cutoff or pointwise heat-positivity premise is used. -/
theorem productMap_range_square_contraction (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    quaternionHaar (tail+1)
        (polyMul (productMap (tail+1) w K (List.range (tail+1)) p)
          (productMap (tail+1) w K (List.range (tail+1)) p)) ≤
      quaternionHaar (tail+1) (polyMul p p) := by
  have h := productMap_range_cycle_carrier (tail+1) w K p
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_carrier (HaarCarrierEqv.mul h h)))
    (cycleIterate_square_contraction tail hw0 hw1 K (tail+1) p hp)

end YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction

#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction.cycleStep_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction.cycleIterate_square_contraction
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicContraction.productMap_range_square_contraction
