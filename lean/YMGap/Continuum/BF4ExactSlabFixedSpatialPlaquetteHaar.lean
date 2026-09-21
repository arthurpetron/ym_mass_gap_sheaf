/-
# Bare Haar moments of an actual spatial plaquette

The literal fundamental character of any original spatial face has bare Haar
mean zero and second moment one.  Consequently subtracting any rational
constant cannot lower its bare squared norm below one.

The shift is arbitrary: this file does not identify it with an interacting or
odd-window mean, and makes no positive-time or limiting claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceHeatMoment
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Support of the literal fundamental character on its original slice. -/
theorem plaquette_supported (width : Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (N width)
      (characterPolynomial (plaquette width face).scalar 1) :=
  character_supported
    (BF4ExactSlabFixedSpatialSpatialOrder.plaquette_supported width (N width)
      (Nat.le_refl _) face).scalar 1

/-- Bare Haar centering of the literal fundamental spatial face. -/
theorem plaquette_mean_zero (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    quaternionHaar (N width) (characterPolynomial (plaquette width face).scalar 1) ≈ 0 := by
  let l : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : l ∈ edgesOf face := by simp [l, edgesOf]
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff
      (RatPolyCoeffEqv.mul_one (characterPolynomial (plaquette width face).scalar 1))))
    (character_haar_zero hf l hl 1 (by decide) polyOne (supported_one _)
      (quaternionBlockIndependent_polyOne _))

/-- Bare Haar normalization of the literal fundamental spatial face. -/
theorem plaquette_square_one (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    quaternionHaar (N width)
      (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar 1)) ≈ 1 := by
  let l : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : l ∈ edgesOf face := by simp [l, edgesOf]
  have h := character_pair_moment hf l hl polyOne (supported_one _)
    (quaternionBlockIndependent_polyOne _) 1
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one
      (polyMul (characterPolynomial (plaquette width face).scalar 1)
        (characterPolynomial (plaquette width face).scalar 1)))))
    (Q'.eqv_trans _ _ _ h (QPolyHaarPositiveSubstitution.haar_one _))

/-- Every rational recentering retains at least the unit bare second moment. -/
theorem shifted_square_floor (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (m : Q') :
    (1 : Q') ≤ quaternionHaar (N width)
      (polyMul
        (QuaternionHaarDensityVariance.shifted
          (characterPolynomial (plaquette width face).scalar 1) m)
        (QuaternionHaarDensityVariance.shifted
          (characterPolynomial (plaquette width face).scalar 1) m)) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hs : quaternionHaar (N width) (polyMul f f) ≈ 1 :=
    plaquette_square_one width face hf
  have hz : quaternionHaar (N width) f ≈ 0 :=
    plaquette_mean_zero width face hf
  have hp : quaternionHaar (N width) f * quaternionHaar (N width) f ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (quaternionHaar (N width) f)
        (quaternionHaar (N width) f) 0 hz)
      (Q'.mul_zero_eqv _)
  have hn : -(quaternionHaar (N width) f * quaternionHaar (N width) f) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hp) (by decide)
  have hv : quaternionHaar (N width) (polyMul f f) +
      -(quaternionHaar (N width) f * quaternionHaar (N width) f) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hs hn) (QPoly.q_add_zero_eqv 1)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hv)
    (bare_variance_le_shifted (plaquette_supported width face) m)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar.plaquette_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar.plaquette_mean_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar.plaquette_square_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar.shifted_square_floor
