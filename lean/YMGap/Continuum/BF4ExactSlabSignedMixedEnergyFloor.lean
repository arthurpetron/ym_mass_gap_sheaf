/-
# Original signed-source two-edge energy floor

Exact coefficient isolation is joined to the mixed kinematics of the SAME
physical face, derivatives and Haar carrier. Every sign and rational
centering is retained. This bounds mixed angular energy from below, not
variance or a transfer gap; a matching upper bound remains necessary.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteMixedSquare

namespace YMGap.Continuum.BF4ExactSlabSignedMixedEnergyFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection (face_links_distinct)
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter)
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryDualFamily (sourceSpan)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (affineSource)
open YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation
open YMGap.Continuum.BF4ExactSlabPlaquetteMixedSquare
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_carrier six_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] correctedSlabPlaquettePolynomial

private theorem square_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polySmul c p) (polySmul c p))
      (polySmul (c*c) (polyMul p p)) :=
  (RatPolyCoeffEqv.polyMul_smul_left c p (polySmul c p)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right c p p).smul c).trans
      (RatPolyCoeffEqv.smul_assoc c c _))

/-- The entire centered signed source has precisely c_p^2 times the
selected face's physical mixed square, under every original insertion. -/
theorem affine_mixedSquare_isolates {extent : Nat} {p : Z4Plaq}
    (hf : p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs) (m : Q') :
    HaarCarrierEqv (N extent) (physicalMixedSquare hf (affineSource extent c qs m))
      (polySmul (c p*c p) (physicalMixedSquare hf (faceCharacter extent p))) := by
  let d := fun i j k l => mixedDerivative extent (faceLinkB p) (faceLinkA p)
    (second_mem hf) (first_mem hf) i j k l (faceCharacter extent p)
  have hone (i j k l : Nat) (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4) :
      RatPolyCoeffEqv
        (mixedDerivative extent (faceLinkB p) (faceLinkA p)
          (second_mem hf) (first_mem hf) i j k l (affineSource extent c qs m))
        (polySmul (c p) (d i j k l)) :=
    affineSource_mixedDerivative_isolates extent c p qs hn hp m
      (faceLinkB p) (faceLinkA p) (second_mem hf) (first_mem hf)
      (by simp [faceLinkB, edgesOf]) (by simp [faceLinkA, edgesOf])
      (Ne.symm (face_links_distinct p).1) hi hj hk hl
  have hs : HaarCarrierEqv (N extent)
      (physicalMixedSquare hf (affineSource extent c qs m))
      (six (fun i j => six (fun k l => polySmul (c p*c p)
        (polyMul (d i j k l) (d i j k l))))) := by
    apply six_carrier
    intro i j hi hj
    apply six_carrier
    intro k l hk hl
    have h := hone i j k l hi hj hk hl
    exact RatPolyCoeffEqv.haarCarrier ((h.mul h).trans (square_smul (c p) _))
  have hcollect : HaarCarrierEqv (N extent)
      (six (fun i j => six (fun k l => polySmul (c p*c p)
        (polyMul (d i j k l) (d i j k l)))))
      (polySmul (c p*c p) (physicalMixedSquare hf (faceCharacter extent p))) :=
    (six_carrier (fun i j _ _ => RatPolyCoeffEqv.haarCarrier
      (six_smul (c p*c p) (fun k l => polyMul (d i j k l) (d i j k l))))).trans
      (RatPolyCoeffEqv.haarCarrier (six_smul (c p*c p) _))
  exact hs.trans hcollect

/-- Exact original weighted identity, stronger than the ensuing floor. -/
theorem affine_mixedSquare_identity {extent : Nat} {p : Z4Plaq}
    (hf : p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs) (m : Q') :
    HaarCarrierEqv (N extent) (physicalMixedSquare hf (affineSource extent c qs m))
      (polySmul (c p*c p)
        (polyAdd (cap 8) (polyMul (faceCharacter extent p) (faceCharacter extent p)))) :=
  (affine_mixedSquare_isolates hf c qs hn hp m).trans
    (HaarCarrierEqv.smul (c p*c p) (physical_face_mixedSquare hf))

/-- A squared coefficient is detected in the original centered signed
source, with no family-size loss at this individual face. -/
theorem affine_mixed_energy_floor {extent : Nat} {p : Z4Plaq}
    (hf : p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs) (m : Q')
    (W : RatPoly) (hW : Certificate (N extent) W) :
    (c p*c p) * (8 * quaternionHaar (N extent) W) ≤
      quaternionHaar (N extent)
        (polyMul W (physicalMixedSquare hf (affineSource extent c qs m))) := by
  have hfloor := Q'.mul_le_mul_of_nonneg_left _ _ (c p*c p)
    (physical_face_weighted_floor hf W hW) (SumOfSquares.q_mul_self_nonneg (c p))
  have he := Q'.eqv_trans _ _ _ ((affine_mixedSquare_isolates hf c qs hn hp m) W)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (c p*c p) W _))
      (quaternionHaar_polySmul (N extent) (c p*c p) _))
  exact Q'.le_trans' _ _ _ hfloor (Q'.le_of_eqv (Q'.eqv_symm he))

/-- The complete specified original face action supplies the positive weight;
no positive-measure premise is left to be filled by the consumer. -/
theorem selected_action_mixed_energy_floor {extent : Nat} {p : Z4Plaq}
    (hf : p ∈ boundaryCompleteSlabPlaquettes extent) (c : Z4Plaq → Q')
    (qs : List Z4Plaq) (hn : qs.Nodup) (hp : p ∈ qs) (m : Q')
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    let W := polynomialProduct (faceHeatPolynomial w K extent) ids
    (c p*c p) * (8 * quaternionHaar (N extent) W) ≤
      quaternionHaar (N extent)
        (polyMul W (physicalMixedSquare hf (affineSource extent c qs m))) :=
  affine_mixed_energy_floor hf c qs hn hp m _
    (headProduct_certificate hw0 hw1 K extent hK ids hids)

#print axioms affine_mixedSquare_isolates
#print axioms affine_mixedSquare_identity
#print axioms affine_mixed_energy_floor
#print axioms selected_action_mixed_energy_floor

end YMGap.Continuum.BF4ExactSlabSignedMixedEnergyFloor
