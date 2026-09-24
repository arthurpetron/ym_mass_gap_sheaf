/-
# Exact conditional pairing for a partially swapped second slice

Swapping precisely the selected lower quaternion blocks of the second factor
into an auxiliary slice realizes the ordinary family conditional projection
on both entries of the original Haar pairing.  The auxiliary variables are
used only for this finite Fubini identity; no product heat map or continuum
operator is introduced.
-/

import YMGap.Continuum.SU2QuaternionPartialSliceSwap
import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionProductHeatMarginals

namespace YMGap.Continuum.SU2QuaternionPartialSwapPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
  (quaternionHaar_extend_supported_endpoint)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionPartialSliceSwap
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private def upperIds (n : Nat) (ids : List Nat) : List Nat :=
  ids.map (fun i => n+i)

private theorem family_pair_selfAdjoint (n : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (p q : RatPoly) :
    quaternionHaar n (polyMul p (familyProject ids q)) ≈
      quaternionHaar n (polyMul (familyProject ids p) (familyProject ids q)) := by
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_eq_after_integratingBlocks n ids
        (familyProject ids q) p hids (familyProject_independent ids q))
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))

/-- The selected auxiliary-slice pairing is exactly the original pairing of
the two family conditional projections.  The selected schedule and all
carrier guards remain explicit. -/
theorem partialSwap_familyProject_pairing (n : Nat) (ids : List Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (_hnodup : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    quaternionHaar (n+n)
        (polyMul p (reindexQuaternionPolynomial (swap n ids) q)) ≈
      quaternionHaar n (polyMul (familyProject ids p) (familyProject ids q)) := by
  let Q := familyProject ids q
  have hupp : ∀ b, b ∈ upperIds n ids → b < n+n := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have := hids i hi
    omega
  have hpind : ∀ b, b ∈ upperIds n ids → QuaternionBlockIndependent b p := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact supported_upper_independent hp i
  have hintegrate := quaternionHaar_polyMul_eq_after_integratingBlocks (n+n)
    (upperIds n ids) p (reindexQuaternionPolynomial (swap n ids) q) hupp hpind
  have hreindex := reindex_familyProject n ids q hids
  have hQsupport := familyProject_supported ids hq
  have hfixed := reindex_familyProject_fixed n ids q hq hids
  have hmiddle : quaternionHaar (n+n)
      (polyMul p (familyProject (upperIds n ids)
        (reindexQuaternionPolynomial (swap n ids) q))) ≈
      quaternionHaar (n+n) (polyMul p Q) := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff (hreindex.symm.mul_left p))
      (haar_of_carrier (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ p) hfixed))
  exact Q'.eqv_trans _ _ _ hintegrate
    (Q'.eqv_trans _ _ _ hmiddle
      (Q'.eqv_trans _ _ _
        (quaternionHaar_extend_supported_endpoint (by omega : n ≤ n+n)
          (polyMul p Q) (supported_polyMul hp hQsupport))
        (family_pair_selfAdjoint n ids hids p q)))

end YMGap.Continuum.SU2QuaternionPartialSwapPairing

#print axioms YMGap.Continuum.SU2QuaternionPartialSwapPairing.partialSwap_familyProject_pairing
