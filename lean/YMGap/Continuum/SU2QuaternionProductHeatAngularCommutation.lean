/-
# Angular differentiation commutes with the original selected product heat

Simultaneous endpoint rotation removes the kernel derivative. Exact input
Haar integration by parts moves it onto the complete signed source instead.
The equality holds under EVERY surviving Haar insertion, including square
insertions. It is not asserted coefficientwise in the free polynomial ring.

No positivity, cutoff guard, kernel floor, derivative cap, or normalizer
inverse is needed for this identity. An interacting source V*f stays intact.
This identity alone supplies no norm-relative or changing-family estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularForm
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatAngularForm
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem carrier_neg_of_add_zero {n : Nat} {p q : RatPoly}
    (h : HaarCarrierEqv n (polyAdd p q) polyZero) :
    HaarCarrierEqv n q (polyNeg p) :=
  (RatPolyCoeffEqv.haarCarrier (coeffEvalExpr_eqv_of_normalize_eq
    (.var 1) (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
    (by decide) (fun | 0 => p | _ => q))).trans
      ((HaarCarrierEqv.add h (HaarCarrierEqv.refl n (polyNeg p))).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _)))

private theorem heads_zero : ∀ n : Nat,
    RatPolyCoeffEqv (partialHaarHeads n polyZero) polyZero
  | 0 => RatPolyCoeffEqv.refl _
  | n+1 => by simpa only [partialHaarHeads] using heads_zero n

/-- Tangential differentiation can be moved from the finite product kernel
onto its complete incoming source. Both sides retain every surviving test.
Repeated selected indices are allowed; no heat positivity is required. -/
theorem productMap_angular_carrier (n s i j : Nat)
    (hs : s < n) (hi : i < 4) (hj : j < 4) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ t, t ∈ ids → t < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    HaarCarrierEqv n
      (angularDerivative (4*s+i) (4*s+j) (productMap n w K ids p))
      (productMap n w K ids (angularDerivative (4*s+i) (4*s+j) p)) := by
  let W := productHeat n w K ids
  let dW := angularDerivative (4*s+i) (4*s+j) W
  let eW := angularDerivative (4*n+(4*s+i)) (4*n+(4*s+j)) W
  let dp := angularDerivative (4*s+i) (4*s+j) p
  let a := partialHaarHeads n (polyMul dW p)
  let b := partialHaarHeads n (polyMul eW p)
  let c := partialHaarHeads n (polyMul W dp)
  have hpair : HaarCarrierEqv (n+n) (polyAdd dW eW) polyZero := by
    have ht := productHeat_pairedAngular_carrier n s i j hs hi hj w K ids hids
    change HaarCarrierEqv (n+n)
      (polyAdd (angularDerivative (4*s+i) (4*s+j) W)
        (angularDerivative (4*(n+s)+i) (4*(n+s)+j) W)) polyZero at ht
    simpa only [dW, eW, Nat.mul_add, Nat.add_assoc] using ht
  have hpairp : HaarCarrierEqv (n+n)
      (polyAdd (polyMul dW p) (polyMul eW p)) polyZero := by
    simpa only [polyMul_add_left_exact] using
      ((HaarCarrierEqv.mul_right p hpair).trans
        (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_left p)))
  have hab : HaarCarrierEqv n (polyAdd a b) polyZero := by
    have ht := partialHaarHeads_carrier (tailBlocks := n) (headBlocks := n) hpairp
    have ht' : HaarCarrierEqv n (polyAdd a b) (partialHaarHeads n polyZero) := by
      simpa only [a, b, partialHaarHeads_add] using ht
    exact ht'.trans (RatPolyCoeffEqv.haarCarrier (heads_zero n))
  have hac : HaarCarrierEqv n (polyAdd a c) polyZero := by
    have ht := (partialHaarHeads_congr n
      (angularDerivative_mul (4*s+i) (4*s+j) W p).symm).trans
        (partialHaarHeads_angularDerivative_at_zero hs hi hj (polyMul W p))
    simpa only [a, c, dp, partialHaarHeads_add] using
      RatPolyCoeffEqv.haarCarrier ht
  have hbc : HaarCarrierEqv n b c :=
    (carrier_neg_of_add_zero hab).trans (carrier_neg_of_add_zero hac).symm
  have hpzero : RatPolyCoeffEqv
      (angularDerivative (4*n+(4*s+i)) (4*n+(4*s+j)) p) polyZero := by
    simpa only [Nat.mul_add, Nat.add_assoc] using
      angularDerivative_blockIndependent_zero hi hj (supported_upper_independent hp s)
  have hout : RatPolyCoeffEqv
      (angularDerivative (4*s+i) (4*s+j) (productMap n w K ids p)) b := by
    unfold productMap kernelMap
    exact (angularDerivative_partialHaarHeads n (4*s+i) (4*s+j) (polyMul W p)).trans
      (partialHaarHeads_congr n
        ((angularDerivative_mul _ _ W p).trans
          (((RatPolyCoeffEqv.refl _).add
            ((hpzero.mul_left W).trans (RatPolyCoeffEqv.mul_zero_right W))).trans
              (RatPolyCoeffEqv.add_zero _))))
  exact (RatPolyCoeffEqv.haarCarrier hout).trans hbc

end YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularCommutation.productMap_angular_carrier
