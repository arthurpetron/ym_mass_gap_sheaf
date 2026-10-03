/-
# Saturated nome-one reproduction at the ORIGINAL output

For p(x,y,z), the actual conditional heat integrates x and returns y,z.
At nome one, above the computed input cutoff, it reproduces p(y,y,z).
The proof substitutes the actual coefficient reassembly, then removes only
the explicit retained radius powers by the proved sphere-unit identity.
It does NOT substitute into an arbitrary Haar-carrier equality. All shared
spectators and arbitrary surviving insertions remain.

This is endpoint algebra, not positivity of the finite nome-one kernel or
a conditional Poincare, interacting signed-cost or scaling estimate.
-/

import YMGap.Continuum.SU2QuaternionConditionalHeatComposition
import YMGap.Continuum.SU2QuaternionRetainedImagePrefix

namespace YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier (carrierOfPrefix)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion (substituteRetained_supported)
open YMGap.Continuum.SU2QuaternionRetainedImagePrefix (substituteRetained_prefix)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatComposition
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.SU2HeatCutoffCasimirBound (attenuation)

/-- The particular selected-radius substitution, at coefficient strength.
The old head and the retained head become the same NEW block zero. -/
theorem substituteRetained_radius :
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusPolynomial 0))
      (quaternionRadiusPolynomial 0) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

/-- Explicit radial mode transport, not a general carrier pullback. -/
theorem substituteRetained_radiusIter (p : RatPoly) : ∀ count : Nat,
    RatPolyCoeffEqv (substituteRetained (quaternionRadiusIter 0 count p))
      (quaternionRadiusIter 0 count (substituteRetained p))
  | 0 => RatPolyCoeffEqv.refl _
  | count+1 =>
      (substituteRetained_mul _ _).trans
        ((substituteRetained_radiusIter p count).mul substituteRetained_radius)

private theorem radial_carrier (tail : Nat) (ht : 0 < tail) (p : RatPoly)
    (count : Nat) : HaarCarrierEqv tail
      (substituteRetained (quaternionRadiusIter 0 count p)) (substituteRetained p) :=
  (RatPolyCoeffEqv.haarCarrier (substituteRetained_radiusIter p count)).trans
    (fun test => quaternionHaar_radiusIter_pair_right tail 0 ht test
      (substituteRetained p) count)

private theorem mode_carrier (tail : Nat) (ht : 0 < tail) (m : Mode (tail+1)) :
    HaarCarrierEqv tail (substituteRetained m.value)
      (substituteRetained (harmonicPart m)) :=
  (RatPolyCoeffEqv.haarCarrier (substituteRetained_smul m.coefficient _)).trans
    ((HaarCarrierEqv.smul m.coefficient (radial_carrier tail ht m.polynomial m.radial)).trans
      (RatPolyCoeffEqv.haarCarrier (substituteRetained_smul m.coefficient m.polynomial)).symm)

private theorem substituted_reassembly (tail : Nat) (ht : 0 < tail) :
    ∀ ms : List (Mode (tail+1)), HaarCarrierEqv tail
      (substituteRetained (sumValues ms)) (substituteRetained (sumHarmonics ms))
  | [] => HaarCarrierEqv.refl tail _
  | m::ms =>
      (RatPolyCoeffEqv.haarCarrier (substituteRetained_add _ _)).trans
        ((HaarCarrierEqv.add (mode_carrier tail ht m) (substituted_reassembly tail ht ms)).trans
          (RatPolyCoeffEqv.haarCarrier (substituteRetained_add _ _)).symm)

/-- Padding is transported through its proved coordinate-prefix identity,
not through an arbitrary Haar-carrier equality. -/
theorem substituteRetained_paddedInput (tail : Nat) (ht : 0 < tail) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    HaarCarrierEqv tail (substituteRetained (paddedInput (tail+1) p))
      (substituteRetained p) :=
  carrierOfPrefix
    (substituteRetained_supported tail ht (paddedInput_supported (tail+1) p))
    (substituteRetained_supported tail ht hp)
    (substituteRetained_prefix (identityReindexQuaternionPolynomial_prefix (tail+1) p))

private theorem qpow_one : ∀ n : Nat, Q'.eqv (RGTransport.qpow 1 n) 1
  | 0 => Q'.eqv_refl _
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (qpow_one n)

private theorem harmonic_endpoint (tail : Nat) (ht : 0 < tail) (K : Nat)
    (m : Mode (tail+1)) (hK : m.degree ≤ K) :
    HaarCarrierEqv tail (conditionalHeat 1 K (harmonicPart m))
      (substituteRetained (harmonicPart m)) := by
  have ha : Q'.eqv (attenuation 1 K m.degree) 1 := by
    unfold attenuation
    rw [if_pos hK]
    exact qpow_one _
  exact (conditionalHeat_harmonic_carrier tail ht 1 K m.degree (harmonicPart m)
    (harmonicPart_degree m) (harmonicPart_harmonic m)).trans
      (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.smul_coefficient ha _).trans
        (RatPolyCoeffEqv.one_smul _)))

private theorem conditional_add (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat 1 K (polyAdd p q))
      (polyAdd (conditionalHeat 1 K p) (conditionalHeat 1 K q)) := by
  unfold conditionalHeat
  have h := partialHaarHead_congr
    (RatPolyCoeffEqv.mul_add_right (relativeHeat 1 K) p q)
  rw [partialHaarHead_add] at h
  exact h

private theorem harmonics_endpoint (tail : Nat) (ht : 0 < tail) (K : Nat) :
    ∀ ms : List (Mode (tail+1)), (∀ m, m ∈ ms → m.degree ≤ K) →
    HaarCarrierEqv tail (conditionalHeat 1 K (sumHarmonics ms))
      (substituteRetained (sumHarmonics ms))
  | [], _ => RatPolyCoeffEqv.haarCarrier
      (partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right (relativeHeat 1 K)))
  | m::ms, hK =>
      (RatPolyCoeffEqv.haarCarrier (conditional_add K _ _)).trans
        ((HaarCarrierEqv.add (harmonic_endpoint tail ht K m (hK m List.mem_cons_self))
          (harmonics_endpoint tail ht K ms
            (fun a ha => hK a (List.mem_cons_of_mem m ha)))).trans
          (RatPolyCoeffEqv.haarCarrier (substituteRetained_add _ _)).symm)

/-- True nome-one endpoint at the already-existing original output y.
All original tail coefficients survive; the cutoff is computed from p. -/
theorem conditionalHeat_one_endpoint (tail : Nat) (ht : 0 < tail) (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : modeCutoff (tail+1) p ≤ K) :
    HaarCarrierEqv tail (conditionalHeat 1 K p) (substituteRetained p) := by
  let ms := modes (tail+1) (Nat.zero_lt_succ tail) p
  have hh := conditionalHeat_carrier tail 1 K
    (polynomial_harmonic_carrier (Nat.zero_lt_succ tail) p hp)
  have he := harmonics_endpoint tail ht K ms (fun m hm =>
    Nat.le_trans (modes_degree_le_cutoff (tail+1) (Nat.zero_lt_succ tail) p m hm) hK)
  have hr : HaarCarrierEqv tail (substituteRetained (sumHarmonics ms))
      (substituteRetained p) :=
    (substituted_reassembly tail ht ms).symm.trans
      ((RatPolyCoeffEqv.haarCarrier (substituteRetained_congr
        (modes_reassembly (tail+1) (Nat.zero_lt_succ tail) p))).trans
        (substituteRetained_paddedInput tail ht p hp))
  exact hh.trans (he.trans hr)

end YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint

#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint.substituteRetained_radius
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint.substituteRetained_radiusIter
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint.substituteRetained_paddedInput
#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatEndpoint.conditionalHeat_one_endpoint
