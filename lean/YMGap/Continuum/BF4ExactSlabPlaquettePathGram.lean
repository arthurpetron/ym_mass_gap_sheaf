/-
# Actual plaquette path pairs and their all-spin Haar Gram channels

The literal boundary word a b c^-1 d^-1 is (a b)(d c)^-1.
Its scalar character is therefore the conjugate-product character of the
two actual paths d c and a b, not a substituted independent kernel.
Both path radii are proved Haar units on the original slab link carrier.
The existing all-spin Gram theorem then applies under every insertion.

On a crossing face, the paths are respectively fixed-then-upper and
lower-then-fixed. The two shared time links remain present. Their Haar
gluing into a reflected square is NOT asserted by this local identity.
-/

import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
import YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.BF4ExactSlabPlaquettePathGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- The four positive-direction links of the ORIGINAL oriented boundary.
The third and fourth are read inversely in that boundary word. -/
def faceLinkA (face : Z4Plaq) : Z4Link := (face.1, (dirsOf face.2).1)
def faceLinkB (face : Z4Plaq) : Z4Link := (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2)
def faceLinkC (face : Z4Plaq) : Z4Link := (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1)
def faceLinkD (face : Z4Plaq) : Z4Link := (face.1, (dirsOf face.2).2)

/-- First direction then second, using the actual slab coordinates. -/
def pathAB (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA face))
    (correctedSlabLinkPolynomial extent (faceLinkB face))

/-- Second direction then first, with the same endpoints as pathAB. -/
def pathDC (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkD face))
    (correctedSlabLinkPolynomial extent (faceLinkC face))

/-- Field-preserving recoding; no word or coefficient is replaced. -/
def asRepresentationQuaternion (p : PolyQuaternion) : RatPolyQuaternion :=
  ⟨p.scalar, p.iPart, p.jPart, p.kPart⟩

private def environment (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | 7 => q.kPart | _ => polyZero
private def conjProductExpr : PolyQuaternionExpr := PolyQuaternionExpr.conj
  (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 0) (PolyQuaternionExpr.coordinate 4))
private def reversedConjExpr : PolyQuaternionExpr := PolyQuaternionExpr.mul
  (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 4))
  (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))

theorem conjugate_product (p q : PolyQuaternion) :
    PolyQuaternionCoeffEqv (PolyQuaternion.conj (PolyQuaternion.mul p q))
      (PolyQuaternion.mul (PolyQuaternion.conj q) (PolyQuaternion.conj p)) := by
  constructor
  · exact coeffEvalExpr_eqv_of_normalize_eq conjProductExpr.scalar reversedConjExpr.scalar (by decide) (environment p q)
  · exact coeffEvalExpr_eqv_of_normalize_eq conjProductExpr.iPart reversedConjExpr.iPart (by decide) (environment p q)
  · exact coeffEvalExpr_eqv_of_normalize_eq conjProductExpr.jPart reversedConjExpr.jPart (by decide) (environment p q)
  · exact coeffEvalExpr_eqv_of_normalize_eq conjProductExpr.kPart reversedConjExpr.kPart (by decide) (environment p q)

/-- The actual ordered four-link fold is the difference of its two paths,
coefficientwise, before any cyclic scalarity or Haar relation. -/
theorem slabPlaquette_eq_pathProduct (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face)
      (PolyQuaternion.mul (pathAB extent face) (PolyQuaternion.conj (pathDC extent face))) := by
  let a := correctedSlabLinkPolynomial extent (faceLinkA face)
  let b := correctedSlabLinkPolynomial extent (faceLinkB face)
  let c := correctedSlabLinkPolynomial extent (faceLinkC face)
  let d := correctedSlabLinkPolynomial extent (faceLinkD face)
  change PolyQuaternionCoeffEqv
    (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul (PolyQuaternion.mul PolyQuaternion.one a) b)
      (PolyQuaternion.conj c)) (PolyQuaternion.conj d))
    (PolyQuaternion.mul (PolyQuaternion.mul a b) (PolyQuaternion.conj (PolyQuaternion.mul d c)))
  exact ((((PolyQuaternionCoeffEqv.one_mul a).mul (PolyQuaternionCoeffEqv.refl b)).mul
      (PolyQuaternionCoeffEqv.refl (PolyQuaternion.conj c))).mul
      (PolyQuaternionCoeffEqv.refl (PolyQuaternion.conj d))).trans
    ((PolyQuaternionCoeffEqv.mul_assoc _ _ _).trans
      ((PolyQuaternionCoeffEqv.refl (PolyQuaternion.mul a b)).mul (conjugate_product d c).symm))

private def rawConjProductScalar : PolyExpr :=
  .add (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.neg (.var 1)) (.var 5))))
    (.add (.neg (.mul (.neg (.var 2)) (.var 6))) (.neg (.mul (.neg (.var 3)) (.var 7))))

/-- Scalar cyclicity plus the field-preserving raw-carrier recoding. The
noncommutative quaternion products themselves are NOT commuted. -/
theorem pathProduct_scalar (p q : PolyQuaternion) :
    RatPolyCoeffEqv (PolyQuaternion.mul q (PolyQuaternion.conj p)).scalar
      (RationalQuaternionRatPoly.mul (RationalQuaternionRatPoly.conj (asRepresentationQuaternion p))
        (asRepresentationQuaternion q)).r :=
  coeffEvalExpr_eqv_of_normalize_eq
    (PolyQuaternionExpr.mul (PolyQuaternionExpr.coordinate 4)
      (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))).scalar
    rawConjProductScalar (by decide) (environment p q)

theorem slabPlaquette_character_eq_pathKernel (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    RatPolyCoeffEqv (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
      (characterPolynomial (RationalQuaternionRatPoly.mul
        (RationalQuaternionRatPoly.conj (asRepresentationQuaternion (pathDC extent face)))
        (asRepresentationQuaternion (pathAB extent face))).r spin) :=
  characterPolynomial_coeffEqv ((slabPlaquette_eq_pathProduct extent face).scalar.trans
    (pathProduct_scalar (pathDC extent face) (pathAB extent face))) spin

private theorem norm_link {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) {link : Z4Link} (hlink : link ∈ edgesOf face) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (correctedSlabLinkPolynomial extent link)) polyOne :=
  haarNorm_orientedSlabLink ⟨link, false⟩ ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hface, hlink⟩)

theorem pathAB_haar_unit {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (radiusPolynomial (asRepresentationQuaternion (pathAB extent face))) polyOne :=
  haarNorm_mul (norm_link hface (by simp [faceLinkA, edgesOf]))
    (norm_link hface (by simp [faceLinkB, edgesOf]))

theorem pathDC_haar_unit {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (radiusPolynomial (asRepresentationQuaternion (pathDC extent face))) polyOne :=
  haarNorm_mul (norm_link hface (by simp [faceLinkD, edgesOf]))
    (norm_link hface (by simp [faceLinkC, edgesOf]))

/-- The all-spin Gram kernel of the TWO LITERAL slab paths. -/
def slabFacePathGram (extent : Nat) (face : Z4Plaq) (spin : Nat) :=
  polynomialGramKernel (asRepresentationQuaternion (pathDC extent face))
    (asRepresentationQuaternion (pathAB extent face)) spin

/-- Original plaquette character equals its actual path-pair Gram kernel
under EVERY insertion on the same slab Haar carrier. No analytic input. -/
theorem slabPlaquette_character_haar_pathGram {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
      (slabFacePathGram extent face spin).1 ∧
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (slabFacePathGram extent face spin).2 polyZero := by
  have h := character_haar_gram_of_unit_radii
    (asRepresentationQuaternion (pathDC extent face)) (asRepresentationQuaternion (pathAB extent face))
    (pathDC_haar_unit hface) (pathAB_haar_unit hface) spin
  exact ⟨QuaternionHaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier (slabPlaquette_character_eq_pathKernel extent face spin)) h.1, h.2⟩

private theorem spatial_not_fixed (half time : Nat) : spatialHalfSide half time ≠ .fixed := by
  unfold spatialHalfSide
  split <;> decide

private theorem temporal_fixed_time {half time : Nat} (h : temporalHalfSide half time = .fixed) : time = half := by
  unfold temporalHalfSide at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- A fixed crossing face uses one lower, two fixed, and one upper link.
Thus neither two-edge path is silently treated as living in an open half. -/
theorem crossing_face_path_sides {half : Nat} {face : Z4Plaq}
    (hfixed : plaquetteHalfSide half face = .fixed) :
    linkHalfSide half (faceLinkA face) = .lower ∧
    linkHalfSide half (faceLinkB face) = .fixed ∧
    linkHalfSide half (faceLinkC face) = .upper ∧
    linkHalfSide half (faceLinkD face) = .fixed := by
  obtain ⟨⟨x, y, z, time⟩, plane⟩ := face
  cases plane <;> first
    | exact False.elim (spatial_not_fixed half time hfixed)
    | have ht := temporal_fixed_time hfixed
      subst time
      simp [faceLinkA, faceLinkB, faceLinkC, faceLinkD, dirsOf, addE,
        linkHalfSide, spatialHalfSide, temporalHalfSide]

/-- The actual fixed face IDs consume the same path Gram identity at every
odd slab extent and every spin. -/
theorem crossing_face_character_haar_pathGram {half id : Nat}
    (hid : id ∈ centralFixedFaceIds half) (spin : Nat) :
    QuaternionHaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length
      (characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half)
        (slabPlaquetteAt (centralExtent half) id)).scalar spin)
      (slabFacePathGram (centralExtent half) (slabPlaquetteAt (centralExtent half) id) spin).1 :=
  (slabPlaquette_character_haar_pathGram (slabPlaquetteAt_mem (mem_centralFixedFaceIds.mp hid).1) spin).1

end YMGap.Continuum.BF4ExactSlabPlaquettePathGram

#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.faceLinkA
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.faceLinkB
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.faceLinkC
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.faceLinkD
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.pathAB
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.pathDC
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.asRepresentationQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.conjugate_product
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.slabPlaquette_eq_pathProduct
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.pathProduct_scalar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.slabPlaquette_character_eq_pathKernel
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.pathAB_haar_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.pathDC_haar_unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.slabFacePathGram
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.slabPlaquette_character_haar_pathGram
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.crossing_face_path_sides
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePathGram.crossing_face_character_haar_pathGram
