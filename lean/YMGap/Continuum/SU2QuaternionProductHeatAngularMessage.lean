/-
# Angular control of a product heat message with its whole positive input

Only the matching output heat factor is differentiated. Every remaining
factor and the full certified input stay inside the original Haar integral.
The two constructed certificates compare the derivative with the erased
message, using a nome-dependent constant with no cutoff or volume power.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
import YMGap.Continuum.SU2QuaternionHaarTailDerivative
import YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularMessage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative

private theorem heads_cap (n : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads n (polyMul (cap c) p))
      (polyMul (cap c) (partialHaarHeads n p)) :=
  (partialHaarHeads_congr n (cap_mul_left c p)).trans
    ((partialHaarHeads_smul n c p).trans (cap_mul_left c _).symm)

/-- Exact derivative of the actual product map: no input derivative and no
derivative of any of the unselected kinetic factors survives. -/
theorem productMap_angular_pin (n : Nat) (w : Q') (K s : Nat)
    (ids : List Nat) (hs : s < n) (hnot : s ∉ ids)
    (hids : ∀ k, k ∈ ids → k < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RatPolyCoeffEqv
      (angularDerivative (4*s+i) (4*s+j) (productMap n w K (s::ids) f))
      (partialHaarHeads n
        (polyMul (angularDerivative (4*(n+s)+i) (4*(n+s)+j) (heatAt s (n+s) w K))
          (polyMul (productHeat n w K ids) f))) := by
  let u := heatAt s (n+s) w K
  let r := polyMul (productHeat n w K ids) f
  have hr : QuaternionBlockIndependent (n+s) r :=
    quaternionBlockIndependent_polyMul
      (productHeat_independent_upper n w K ids hids s hs hnot)
      (supported_upper_independent hf s)
  have hz := angularDerivative_blockIndependent_zero hi hj hr
  have hd : RatPolyCoeffEqv
      (angularDerivative (4*(n+s)+i) (4*(n+s)+j) (polyMul u r))
      (polyMul (angularDerivative (4*(n+s)+i) (4*(n+s)+j) u) r) :=
    (angularDerivative_mul _ _ u r).trans
      (((RatPolyCoeffEqv.refl _).add
        ((hz.mul_left u).trans (RatPolyCoeffEqv.mul_zero_right u))).trans
          (RatPolyCoeffEqv.add_zero _))
  have ht := angularDerivative_partialHaarHeads n (4*s+i) (4*s+j)
    (polyMul (polyMul u (productHeat n w K ids)) f)
  rw [show 4*n+(4*s+i) = 4*(n+s)+i by omega,
    show 4*n+(4*s+j) = 4*(n+s)+j by omega] at ht
  exact ht.trans (partialHaarHeads_congr n
    ((angularDerivative_congr _ _ (RatPolyCoeffEqv.mul_assoc u _ f)).trans hd))

private def integratedProductBounds (n : Nat) {p r : RatPoly} {c : Q'}
    (P : Interval (n+n) p c) (R : Certificate (n+n) r) :
    Certificate n (polyAdd (polyMul (cap c) (partialHaarHeads n r))
      (polyNeg (partialHaarHeads n (polyMul p r)))) ×
    Certificate n (polyAdd (polyMul (cap c) (partialHaarHeads n r))
      (partialHaarHeads n (polyMul p r))) := by
  have hu : RatPolyCoeffEqv (polyMul (polyAdd (cap c) (polyNeg p)) r)
      (polyAdd (polyMul (cap c) r) (polyNeg (polyMul p r))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => cap c | 1 => p | _ => r)
  have hl : RatPolyCoeffEqv (polyMul (polyAdd (cap c) p) r)
      (polyAdd (polyMul (cap c) r) (polyMul p r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => cap c | 1 => p | _ => r)
  have U := partialHaarHeads_certificate n n (Certificate.ofCoeff hu.symm (P.upper.mul R))
  have L := partialHaarHeads_certificate n n (Certificate.ofCoeff hl.symm (P.lower.mul R))
  rw [partialHaarHeads_add] at U L
  exact ⟨.ofCoeff ((heads_cap n c r).add (partialHaarHeads_neg n _)).symm U,
    .ofCoeff ((heads_cap n c r).add (.refl _)).symm L⟩

/-- Two-sided derivative control by the erased-factor message, for the entire
certified input. The constant has no number-of-blocks or input-depth factor. -/
def productMap_angular_bounds (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (s : Nat) (ids : List Nat) (hs : s < n) (hnot : s ∉ ids)
    (hids : ∀ k, k ∈ ids → k < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    Certificate n
      (polyAdd (polyMul (cap (heatDerivativeCap w 32)) (productMap n w K ids f))
        (polyNeg (angularDerivative (4*s+i) (4*s+j) (productMap n w K (s::ids) f)))) ×
    Certificate n
      (polyAdd (polyMul (cap (heatDerivativeCap w 32)) (productMap n w K ids f))
        (angularDerivative (4*s+i) (4*s+j) (productMap n w K (s::ids) f))) := by
  let P := heatAngularInterval (show s < n+n by omega) (show n+s < n+n by omega)
    (show 4*(n+s)+i < 4*(n+n) by omega) (show 4*(n+s)+j < 4*(n+n) by omega)
    hw0 hw1 K
  let R := (productHeatCertificate n hw0 hw1 K hK ids hids).mul (certificate_extend n hf F)
  have B := integratedProductBounds n P R
  have pin := productMap_angular_pin n w K s ids hs hnot hids hf hi hj
  exact ⟨.ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg pin)) B.1,
    .ofCoeff ((RatPolyCoeffEqv.refl _).add pin) B.2⟩

end YMGap.Continuum.SU2QuaternionProductHeatAngularMessage

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularMessage.productMap_angular_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularMessage.productMap_angular_bounds
