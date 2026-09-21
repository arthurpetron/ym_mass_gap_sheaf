/-
# Original product heat messages with a Jacobi relative angular cost

The late unweighted heat prefix has a relative angular certificate directly
against itself. Every remaining kinetic factor and the entire positive input
are retained. Integrating these certificates gives a bound against the full
message, without first comparing to an erased message or dividing by a floor.
-/

import YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
import YMGap.Continuum.SU2QuaternionProductHeatAngularMessage

namespace YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound

/-- Same relative quaternion kinetic factor, with the original cutoff and
all representation labels retained. -/
def heatRelativeBound {blocks a b i j : Nat}
    (ha : a < blocks) (hb : b < blocks)
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K) :
    RelativeBound blocks i j (heatAt a b w K) (relativeCap w 32) := by
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable a)
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable b))
  have hp : Supported blocks word := (Supported.coordinate ha).mul (Supported.coordinate hb).conj
  have hu : HaarCarrierEqv blocks (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate ha)
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate hb))
  rw [heatAt_eq_prefix]
  exact heatPrefixRelativeBoundAt hw0 hw1 hi hj hp hu
    (scalarAngularInterval ha hb hi hj) K hK

private theorem heads_cap (n : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (partialHaarHeads n (polyMul (cap c) p))
      (polyMul (cap c) (partialHaarHeads n p)) :=
  (partialHaarHeads_congr n (cap_mul_left c p)).trans
    ((partialHaarHeads_smul n c p).trans (cap_mul_left c _).symm)

/-- Positive integration preserves the relative bound at output coordinates;
the derivative is the actual derivative of the integrated polynomial. -/
def integrateRelative (n m i j : Nat) {p : RatPoly} {c : Q'}
    (P : RelativeBound (m+n) (4*n+i) (4*n+j) p c) :
    RelativeBound m i j (partialHaarHeads n p) c where
  positive := partialHaarHeads_certificate m n P.positive
  nonnegative := P.nonnegative
  upper := by
    have U := partialHaarHeads_certificate m n P.upper
    rw [partialHaarHeads_add] at U
    exact .ofCoeff ((heads_cap n c p).symm.add
      ((RatPolyCoeffEqv.neg (angularDerivative_partialHaarHeads n i j p)).trans
        (partialHaarHeads_neg n _).symm)) U
  lower := by
    have L := partialHaarHeads_certificate m n P.lower
    rw [partialHaarHeads_add] at L
    exact .ofCoeff ((heads_cap n c p).symm.add (angularDerivative_partialHaarHeads n i j p)) L

/-- The full original product map, not an erased or normalized replacement,
has a single relative angular constant independent of input depth and width. -/
def productMapRelativeBound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : relativeCutoff w 32 ≤ K)
    (s : Nat) (ids : List Nat) (hs : s < n) (hnot : s ∉ ids)
    (hids : ∀ k, k ∈ ids → k < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound n (4*s+i) (4*s+j) (productMap n w K (s::ids) f) (relativeCap w 32) := by
  let u := heatAt s (n+s) w K
  let r := polyMul (productHeat n w K ids) f
  have hr : QuaternionBlockIndependent (n+s) r :=
    quaternionBlockIndependent_polyMul
      (productHeat_independent_upper n w K ids hids s hs hnot)
      (supported_upper_independent hf s)
  have hz := angularDerivative_blockIndependent_zero hi hj hr
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  let R := (productHeatCertificate n hw0 hw1 K hhead ids hids).mul (certificate_extend n hf F)
  let P := heatRelativeBound (show s < n+n by omega) (show n+s < n+n by omega)
    (show 4*(n+s)+i < 4*(n+n) by omega) (show 4*(n+s)+j < 4*(n+n) by omega) hw0 hw1 K hK
  have B : RelativeBound (n+n) (4*(n+s)+i) (4*(n+s)+j) (polyMul u r) (relativeCap w 32) :=
    (P.mul (RelativeBound.ofZeroDerivative R hz)).changeCap (QPoly.q_add_zero_eqv _)
  rw [show 4*(n+s)+i = 4*n+(4*s+i) by omega,
    show 4*(n+s)+j = 4*n+(4*s+j) by omega] at B
  exact .ofCoeff (partialHaarHeads_congr n (RatPolyCoeffEqv.mul_assoc u _ f))
    (integrateRelative n n (4*s+i) (4*s+j) B)

end YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage

#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage.heatRelativeBound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage.integrateRelative
#print axioms YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage.productMapRelativeBound
