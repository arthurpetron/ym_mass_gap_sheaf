/-
# Same-full-carrier harmonic heat reproduction

The selected head is integrated but reinserted as an empty block in the
computed output. Arbitrary head-independent insertions may depend on every
other variable, including the retained partner. Support is constructed from
the actual substitution, not supplied as an extra transport hypothesis.
-/

import YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
import YMGap.Continuum.SU2QuaternionHaarKernelBound

namespace YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatInsertion
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

/-- Restore the selected coordinate slot after exact retained substitution. -/
def retainedImage (p : RatPoly) : RatPoly := liftHead (substituteRetained p)

private theorem power_supported {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    ∀ n, SupportedQuaternionBlocks blocks (ratPolyPow p n)
  | 0 => by
      intro t ht
      have he := List.mem_singleton.mp ht
      subst t
      exact Nat.zero_le _
  | n+1 => supported_polyMul (power_supported hp n) hp

private theorem translated_supported (tailBlocks : Nat) (hb : 0 < tailBlocks) :
    ∀ p : RatPoly, SupportedQuaternionBlocks (tailBlocks+1) p →
      SupportedQuaternionBlocks (tailBlocks+1)
        (translatedHeadPolynomial (PolyQuaternion.coordinateVariable 1) p)
  | [], _ => by intro t ht; cases ht
  | term :: rest, hp => by
      have hc (i : Fin 4) : SupportedQuaternionBlocks (tailBlocks+1)
          (polyVar (4+i.val)) := coordinate_supported (by omega : 1 < tailBlocks+1) i
      have hmon : SupportedQuaternionBlocks (tailBlocks+1)
          (translatedHeadMonomial (PolyQuaternion.coordinateVariable 1)
            (exponentAt term.1 0) (exponentAt term.1 1)
            (exponentAt term.1 2) (exponentAt term.1 3)) :=
        supported_polyMul (power_supported (hc 0) _)
          (supported_polyMul (power_supported (hc 1) _)
            (supported_polyMul (power_supported (hc 2) _)
              (power_supported (hc 3) _)))
      have htail : SupportedQuaternionBlocks (tailBlocks+1) (headTailLiftTerm term) := by
        intro t ht
        have he := List.mem_singleton.mp ht
        subst t
        have hd := hp term List.mem_cons_self
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_drop]
        omega
      have hterm := supported_polyMul hmon htail
      have hrest := translated_supported tailBlocks hb rest
        (fun t ht => hp t (List.mem_cons_of_mem term ht))
      intro t ht
      exact (List.mem_append.mp ht).elim (hterm t) (hrest t)

theorem substituteRetained_supported (tailBlocks : Nat) (hb : 0 < tailBlocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    SupportedQuaternionBlocks tailBlocks (substituteRetained p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hh := translated_supported tailBlocks hb p hp s hs
  change (List.drop 4 s.1).length ≤ 4*tailBlocks
  rw [List.length_drop]
  omega

theorem retainedImage_supported (tailBlocks : Nat) (hb : 0 < tailBlocks)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (tailBlocks+1) p) :
    SupportedQuaternionBlocks (tailBlocks+1) (retainedImage p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have hh := substituteRetained_supported tailBlocks hb hp s hs
  change (0::0::0::0::s.1).length ≤ 4*(tailBlocks+1)
  simp only [List.length_cons]
  omega

theorem retainedImage_pairing (tailBlocks : Nat) (p r : RatPoly)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1) (polyMul (retainedImage p) r) ≈
      quaternionHaar tailBlocks (polyMul (substituteRetained p) (dropHeadPolynomial r)) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_headIndependent tailBlocks _ r hr)
    (haar_of_coeff ((partialHaarHeads_liftBoundary 1 (substituteRetained p)).mul_right _))

/-- Full original carrier on both sides, arbitrary independent insertion,
and explicit omitted-mode behavior when n exceeds the actual cutoff. -/
theorem harmonic_transmission_same_carrier (tailBlocks : Nat) (hb : 0 < tailBlocks)
    (w : Q') (K n : Nat) (p r : RatPoly)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tailBlocks+1)
      (polyMul (polyMul (relativeHeat w K) p) r) ≈
      if n ≤ K then qpow w (n*(n+2)) * quaternionHaar (tailBlocks+1)
        (polyMul (retainedImage p) r) else 0 := by
  have h := Q'.eqv_trans _ _ _ (independent_to_lift tailBlocks _ r hr)
    (heat_harmonic_reproduction tailBlocks hb w K n p hp hh (dropHeadPolynomial r))
  by_cases hK : n ≤ K
  · rw [if_pos hK] at h ⊢
    exact Q'.eqv_trans _ _ _ h
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (retainedImage_pairing tailBlocks p r hr)))
  · rw [if_neg hK] at h ⊢
    exact h

end YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion

#print axioms YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion.substituteRetained_supported
#print axioms YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion.retainedImage_supported
#print axioms YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion.retainedImage_pairing
#print axioms YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion.harmonic_transmission_same_carrier
