/-
# Exact two-edge square on the actual full-slab plaquette

Both differentiated physical links and the character are those of the
original corrected slab. The full Haar carrier and arbitrary insertions
are retained. This joins the exposed kinematic identity to the literal
physical derivative used by signed-source coefficient isolation.
-/

import YMGap.Continuum.QuaternionHaarMixedAngularTransport
import YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier

namespace YMGap.Continuum.BF4ExactSlabPlaquetteMixedSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabPlaquetteMixedDerivativeIsolation
open YMGap.Continuum.BF4ExactSlabPlaquettePhysicalDerivativeCarrier
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOrientedWordSelection (word word_supported)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (six)
open YMGap.Continuum.QuaternionHaarAngularLaplacianLinear (six_carrier)
open YMGap.Continuum.QuaternionHaarMixedAngularTransport
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] correctedSlabPlaquettePolynomial

theorem first_mem {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    faceLinkA face ∈ boundaryCompleteSlabLinks extent :=
  (mem_boundaryCompleteSlabLinks_iff extent _).mpr
    ⟨face, hf, by simp [faceLinkA, edgesOf]⟩

theorem second_mem {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    faceLinkB face ∈ boundaryCompleteSlabLinks extent :=
  (mem_boundaryCompleteSlabLinks_iff extent _).mpr
    ⟨face, hf, by simp [faceLinkB, edgesOf]⟩

/-- Differentiate at B first and A second, matching mixedSquare A B.
The original signed-source detector allows precisely this ordered pair. -/
def physicalMixedSquare {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (p : RatPoly) : RatPoly :=
  six (fun i j => six (fun k l =>
    let d := mixedDerivative extent (faceLinkB face) (faceLinkA face)
      (second_mem hf) (first_mem hf) i j k l p
    polyMul d d))

/-- Both physical head-swap derivatives are the literal A/B block derivatives
under every original Haar insertion. -/
theorem physicalMixedSquare_carrier {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N extent) p) :
    HaarCarrierEqv (N extent) (physicalMixedSquare hf p)
      (mixedSquare (blockA hf).val (blockB hf).val p) := by
  apply six_carrier
  intro i j hi hj
  apply six_carrier
  intro k l hk hl
  have hd := mixedDerivative_carrier extent (faceLinkB face) (faceLinkA face)
    (second_mem hf) (first_mem hf) hi hj hk hl hp
  exact HaarCarrierEqv.mul hd hd

/-- The exposed mixed identity specialized to the SAME corrected-slab face. -/
theorem fullSlabFaceCharacter_mixedSquare {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (N extent)
      (mixedSquare (blockA hf).val (blockB hf).val (faceCharacter extent face))
      (polyAdd (cap 8) (polyMul (faceCharacter extent face) (faceCharacter extent face))) := by
  let a := blockA hf
  let b := blockB hf
  let c := blockC hf
  let d := blockD hf
  let f := faceCharacter extent face
  let v := characterPolynomial (word a.val b.val c.val d.val false false true true).scalar 1
  have hword : RatPolyCoeffEqv f v := original_character_eq_coordinateWord hf 1
  have hvs := word_supported a.isLt b.isLt c.isLt d.isLt false false true true 1
  have hfs := faceCharacter_supported extent face
  have h := oriented_word_mixedSquare_of_exposure (face_carrier_four_blocks hf)
    a b c d (faceExposure hf) false false true true
  exact (mixedSquare_carrier a.isLt b.isLt hfs hvs (RatPolyCoeffEqv.haarCarrier hword)).trans
    (h.trans (RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add (hword.symm.mul hword.symm))))

/-- This is the mixed square of the physical derivatives used by isolation,
not merely the canonical exposed word. -/
theorem physical_face_mixedSquare {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (N extent) (physicalMixedSquare hf (faceCharacter extent face))
      (polyAdd (cap 8) (polyMul (faceCharacter extent face) (faceCharacter extent face))) :=
  (physicalMixedSquare_carrier hf _ (faceCharacter_supported extent face)).trans
    (fullSlabFaceCharacter_mixedSquare hf)

/-- The actual two-edge energy is at least eight times the SAME weight's
mass. Weight positivity is witnessed, without a heat-minimum comparison. -/
theorem physical_face_weighted_floor {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (W : RatPoly) (hW : Certificate (N extent) W) :
    8 * quaternionHaar (N extent) W ≤ quaternionHaar (N extent)
      (polyMul W (physicalMixedSquare hf (faceCharacter extent face))) := by
  let f := faceCharacter extent face
  have hs : (0 : Q') ≤ quaternionHaar (N extent) (polyMul W (polyMul f f)) :=
    Q'.le_trans' _ _ _ (hW.square_insertion_nonnegative f (faceCharacter_supported extent face))
      (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm (polyMul f f) W)))
  have hc : Q'.eqv (quaternionHaar (N extent) (polyMul W (cap 8)))
      (8 * quaternionHaar (N extent) W) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      ((RatPolyCoeffEqv.mul_comm W (cap 8)).trans (cap_mul_left 8 W)))
      (quaternionHaar_polySmul (N extent) 8 W)
  have he := Q'.eqv_trans _ _ _ (physical_face_mixedSquare hf W)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right W _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (N extent) _ _)
        (Q'.add_eqv_congr' hc (Q'.eqv_refl _))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hs)
    (Q'.le_of_eqv (Q'.eqv_symm he))

#print axioms first_mem
#print axioms second_mem
#print axioms physicalMixedSquare
#print axioms physicalMixedSquare_carrier
#print axioms fullSlabFaceCharacter_mixedSquare
#print axioms physical_face_mixedSquare
#print axioms physical_face_weighted_floor

end YMGap.Continuum.BF4ExactSlabPlaquetteMixedSquare
