/-
# Null reflection from the SAME strictly positive finite weight

A certified positive rational floor for W shows that a supported polynomial
whose W-weighted square has zero Haar integral also has zero ordinary Haar
square. The finite Haar radical then annihilates every supported insertion;
actual tail integration upgrades this to arbitrary insertions.

The floor may depend on all finite regulators. This is an exact nullness
statement, not a uniform norm comparison, excitation-survival estimate,
completed OS theorem or continuum mass-gap claim. Its consumer is the null
branch of the original finite adaptive signed-score payment.
-/

import YMGap.Constructive.CauchyConv
import YMGap.Continuum.QuaternionHaarPositiveFloorCancellation
import YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex

namespace YMGap.Continuum.QuaternionHaarPositiveWeightNullReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarPositiveFloorCancellation (floor_insertion)
open YMGap.Continuum.SU2QuaternionFiniteHaarGNSCarrier (finiteHaarGNSData)
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)

local infix:50 " ≈ " => Q'.eqv

/-- A zero square under the original positive weight is Haar-carrier null.
The conclusion includes EVERY polynomial insertion, not only supported tests. -/
theorem haar_null_of_positive_weight_square_zero {blocks : Nat}
    {b W : RatPoly} {c : Q'}
    (hp : SupportedQuaternionBlocks blocks b) (hc : (0 : Q') < c)
    (L : Certificate blocks (polyAdd W (polyNeg (cap c))))
    (hzero : quaternionHaar blocks (polyMul W (polyMul b b)) ≈ 0) :
    HaarCarrierEqv blocks b polyZero := by
  have hsquare : (0 : Q') ≤ quaternionHaar blocks (polyMul b b) :=
    (Certificate.square b hp).haar_nonnegative
  have hfloor := floor_insertion (Certificate.square b hp) L
  have hupper : c*quaternionHaar blocks (polyMul b b) ≤ 0 :=
    Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (haar_of_coeff
          (RatPolyCoeffEqv.mul_comm (polyMul b b) W)))
        (Q'.le_of_eqv hzero))
  have hlower : (0 : Q') ≤ c*quaternionHaar blocks (polyMul b b) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hc) hsquare
  have hproduct : c*quaternionHaar blocks (polyMul b b) ≈ 0 :=
    Int.le_antisymm hupper hlower
  have hbare : quaternionHaar blocks (polyMul b b) ≈ 0 :=
    Q'.mul_eqv_zero_of_pos hc hproduct
  have hz : SupportedQuaternionBlocks blocks polyZero := by
    intro term ht
    cases ht
  apply carrier_of_supported hp hz
  intro p hsupport
  have hdiag : (finiteHaarGNSData blocks).B ⟨b,hp⟩ ⟨b,hp⟩ ≈ 0 := hbare
  have hpair := (finiteHaarGNSData blocks).radical_form_zero_right
    ⟨p,hsupport⟩ ⟨b,hp⟩ hdiag
  exact Q'.eqv_trans _ _ _ hpair
    (Q'.eqv_symm (haar_of_coeff (blocks := blocks)
      (RatPolyCoeffEqv.mul_zero_right p)))

#print axioms haar_null_of_positive_weight_square_zero

end YMGap.Continuum.QuaternionHaarPositiveWeightNullReflection
