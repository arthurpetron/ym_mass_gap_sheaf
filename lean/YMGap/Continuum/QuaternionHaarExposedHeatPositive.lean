/-
# All-nome heat positivity for an exposed four-link word

The exposed word uses four coordinate quaternion blocks.  This file supplies
the support and Haar-unit hypotheses needed by the generic all-nome prefix
certificate on any carrier with at least four blocks.
-/

import YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
import YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

namespace YMGap.Continuum.QuaternionHaarExposedHeatPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)

private theorem oriented_supported {blocks block : Nat} (hblock : block < blocks)
    (reverse : Bool) : Supported blocks (orientedCoordinateQuaternion block reverse) := by
  cases reverse with
  | false =>
      simpa [orientedCoordinateQuaternion] using (Supported.coordinate hblock)
  | true =>
      simpa [orientedCoordinateQuaternion] using (Supported.conj (Supported.coordinate hblock))

private theorem oriented_unit {blocks block : Nat} (hblock : block < blocks)
    (reverse : Bool) :
    HaarCarrierEqv blocks
      (polyQuaternionNorm (orientedCoordinateQuaternion block reverse)) polyOne := by
  have hc := haarNorm_coordinate hblock
  cases reverse with
  | false =>
      simpa [orientedCoordinateQuaternion] using hc
  | true =>
      simpa [orientedCoordinateQuaternion] using
        (HaarCarrierEqv.trans
          (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)) hc)

/-- The exposed four-link word is supported on every carrier with `3 < blocks`.
The strict inequality is the explicit room guard for its four coordinates. -/
def exposedFourWord_supported {blocks : Nat} (hblocks : 3 < blocks)
    (r0 r1 r2 r3 : Bool) :
    Supported blocks (exposedFourWord r0 r1 r2 r3) := by
  have h0 : 0 < blocks := by omega
  have h1 : 1 < blocks := by omega
  have h2 : 2 < blocks := by omega
  have h3 : 3 < blocks := by omega
  exact (((oriented_supported h0 r0).mul (oriented_supported h1 r1)).mul
    (oriented_supported h2 r2)).mul (oriented_supported h3 r3)

/-- The exposed four-link word has Haar-unit quaternion norm on the same carrier. -/
def exposedFourWord_unit {blocks : Nat} (hblocks : 3 < blocks)
    (r0 r1 r2 r3 : Bool) :
    HaarCarrierEqv blocks
      (polyQuaternionNorm (exposedFourWord r0 r1 r2 r3)) polyOne := by
  have h0 : 0 < blocks := by omega
  have h1 : 1 < blocks := by omega
  have h2 : 2 < blocks := by omega
  have h3 : 3 < blocks := by omega
  exact haarNorm_mul
    (haarNorm_mul
      (haarNorm_mul
        (oriented_unit h0 r0) (oriented_unit h1 r1))
      (oriented_unit h2 r2))
    (oriented_unit h3 r3)

/-- All-nome positivity for the exposed word, at the explicit late cutoff. -/
def exposedHeatPrefixCertificate {blocks : Nat} (hblocks : 3 < blocks)
    (r0 r1 r2 r3 : Bool) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) :
    Certificate blocks (heatPrefix w K (exposedFourWord r0 r1 r2 r3).scalar) :=
  QuaternionHaarAllNomeHeatCertificate.prefixCertificate hw0 hw1
    (exposedFourWord_supported hblocks r0 r1 r2 r3)
    (exposedFourWord_unit hblocks r0 r1 r2 r3) K hK

#print axioms exposedFourWord_supported
#print axioms exposedFourWord_unit
#print axioms exposedHeatPrefixCertificate

end YMGap.Continuum.QuaternionHaarExposedHeatPositive
