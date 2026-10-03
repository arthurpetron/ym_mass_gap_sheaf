/-
# Saturation of the ORIGINAL retained-output conditional heat

Every computed input harmonic has degree at most modeCutoff. At either later
cutoff it therefore transmits with the SAME original nome power to the already
existing output link. All output-dependent coefficients and spectators remain
shared, and every surviving Haar insertion is retained.

This permits a larger positive auxiliary prefix to be transported to a fixed
interpolation cutoff for a fixed supported input. It does not assert positivity
of an arbitrary cutoff, a conditional variance estimate or scaling uniformity.
-/

import YMGap.Continuum.SU2QuaternionConditionalHeatComposition

namespace YMGap.Continuum.SU2QuaternionConditionalHeatSaturation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionFischerDecomposition (Mode)
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution (substituteRetained)
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatComposition
open YMGap.Continuum.SU2HeatCutoffCasimirBound (attenuation)

private def transmittedModes {blocks : Nat} (u : Q') : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => polyAdd
      (polySmul (RGTransport.qpow u (m.degree*(m.degree+2)))
        (substituteRetained (harmonicPart m)))
      (transmittedModes u ms)

private theorem conditional_add (u : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polyAdd p q))
      (polyAdd (conditionalHeat u K p) (conditionalHeat u K q)) := by
  unfold conditionalHeat
  have h := partialHaarHead_congr
    (RatPolyCoeffEqv.mul_add_right (relativeHeat u K) p q)
  rw [partialHaarHead_add] at h
  exact h

private theorem conditional_modes_saturated (tail : Nat) (ht : 0 < tail)
    (u : Q') (K : Nat) : ∀ ms : List (Mode (tail+1)),
      (∀ m, m ∈ ms → m.degree ≤ K) →
      HaarCarrierEqv tail (conditionalHeat u K (sumHarmonics ms))
        (transmittedModes u ms)
  | [], _ => RatPolyCoeffEqv.haarCarrier
      (partialHaarHead_congr (RatPolyCoeffEqv.mul_zero_right (relativeHeat u K)))
  | m::ms, hK => by
      have hm := conditionalHeat_harmonic_carrier tail ht u K m.degree
        (harmonicPart m) (harmonicPart_degree m) (harmonicPart_harmonic m)
      have hd : m.degree ≤ K := hK m List.mem_cons_self
      simp only [attenuation, if_pos hd] at hm
      exact (RatPolyCoeffEqv.haarCarrier
        (conditional_add u K (harmonicPart m) (sumHarmonics ms))).trans
          (HaarCarrierEqv.add hm
            (conditional_modes_saturated tail ht u K ms
              (fun a ha => hK a (List.mem_cons_of_mem m ha))))

/-- Both actual prefixes agree on this fixed supported input under EVERY
surviving insertion, at its ORIGINAL retained output. Signed nomes and
cutoff zero are included; no kernel-positive or output-independent premise. -/
theorem conditionalHeat_cutoff_stable (tail : Nat) (ht : 0 < tail) (u : Q')
    (K L : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : modeCutoff (tail+1) p ≤ K)
    (hL : modeCutoff (tail+1) p ≤ L) :
    HaarCarrierEqv tail (conditionalHeat u K p) (conditionalHeat u L p) := by
  let ms := modes (tail+1) (Nat.zero_lt_succ tail) p
  have hsource : HaarCarrierEqv (tail+1) p (sumHarmonics ms) :=
    polynomial_harmonic_carrier (Nat.zero_lt_succ tail) p hp
  have hdegrees : ∀ m, m ∈ ms → m.degree ≤ modeCutoff (tail+1) p :=
    modes_degree_le_cutoff (tail+1) (Nat.zero_lt_succ tail) p
  have hk : HaarCarrierEqv tail (conditionalHeat u K p) (transmittedModes u ms) :=
    (conditionalHeat_carrier tail u K hsource).trans
      (conditional_modes_saturated tail ht u K ms
        (fun m hm => Nat.le_trans (hdegrees m hm) hK))
  have hl : HaarCarrierEqv tail (conditionalHeat u L p) (transmittedModes u ms) :=
    (conditionalHeat_carrier tail u L hsource).trans
      (conditional_modes_saturated tail ht u L ms
        (fun m hm => Nat.le_trans (hdegrees m hm) hL))
  exact hk.trans hl.symm

end YMGap.Continuum.SU2QuaternionConditionalHeatSaturation

#print axioms YMGap.Continuum.SU2QuaternionConditionalHeatSaturation.conditionalHeat_cutoff_stable
