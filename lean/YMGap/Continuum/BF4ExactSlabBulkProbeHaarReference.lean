/-
# Volume-independent bare Haar reference on the ORIGINAL translated links

The probe is the actual fundamental character of the translated lower face.
The scalar test is the product of its four literal scalar link coordinates.
The existing block embedding transports the extent-one moments: both means
are zero and the mixed moment is exactly 1/128, at every half-size.

Any supported spectator polynomial avoiding those four links factors out
of each reference moment. This is signed product-Haar factorization, not a
claim that the full interacting action is independent of the probe.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeInterface
import YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
import YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

theorem probeId_translated_lower (half : Nat) : translatedId half 0 ∈ centralLowerFaceIds half := by
  have hp := (mem_centralLowerFaceIds.mp probeId_lower).1
  apply mem_centralLowerFaceIds.mpr
  refine ⟨translatedId_physical hp, ?_⟩
  rw [translatedId_pin hp, translated_side]
  exact (mem_centralLowerFaceIds.mp probeId_lower).2

def bulkProbe (half : Nat) : PlaquetteExpression half :=
  .character (translatedId half 0) (probeId_translated_lower half) 1

theorem bulkProbe_pin (half : Nat) : lower (bulkProbe half) =
    characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent half) (probeFace half)).scalar 1 := by
  unfold lower bulkProbe
  simp only [evaluate]
  rw [translatedId_pin (half := half) (id := 0) (mem_centralLowerFaceIds.mp probeId_lower).1]
  rfl

def scalarProduct (extent : Nat) : List Z4Link → RatPoly
  | [] => polyOne
  | link :: links => polyMul (correctedSlabLinkPolynomial extent link).scalar (scalarProduct extent links)

def bulkScalar (half : Nat) : RatPoly := scalarProduct (centralExtent half) (probeLinks half)

theorem scalarProduct_exposed (extent : Nat) : ∀ ids : List Nat,
    scalarProduct extent (ids.map (fun id => faceLinkA (slabPlaquetteAt extent id))) =
      polynomialProduct (fun id => (correctedSlabLinkPolynomial extent (faceLinkA (slabPlaquetteAt extent id))).scalar) ids
  | [] => rfl
  | id :: ids => by
      change polyMul _ (scalarProduct extent (ids.map _)) = polyMul _ (polynomialProduct _ ids)
      rw [scalarProduct_exposed extent ids]

/-- The test polynomial is exactly the product of the selected ORIGINAL
scalar-coordinate channel polynomials, in the translated face order. -/
theorem bulkScalar_coordinate_pin (half : Nat) : bulkScalar half =
    polynomialProduct (fun id => faceCoordinatePolynomial half id false false) (crossingIds half) := by
  unfold bulkScalar
  rw [← crossingIds_links, scalarProduct_exposed]
  rfl

theorem scalarProduct_supported (extent : Nat) : ∀ links : List Z4Link,
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (scalarProduct extent links)
  | [] => supported_one _
  | link :: links => supported_polyMul (supported_slabLink extent link).scalar (scalarProduct_supported extent links)

theorem scalarProduct_local (extent : Nat) : ∀ links : List Z4Link,
    LinkLocal extent links (scalarProduct extent links)
  | [] => BlockLocal.one _ _
  | link :: links => by
      have hc : LinkLocal extent (link :: links) (correctedSlabLinkPolynomial extent link).scalar := by
        by_cases hm : link ∈ boundaryCompleteSlabLinks extent
        · rw [correctedSlabLinkPolynomial_of_mem hm]
          apply BlockLocal.coordinate
          rw [show (4*(boundaryCompleteSlabLinks extent).idxOf link)/4 =
            (boundaryCompleteSlabLinks extent).idxOf link by omega, correctedSlabLinkAt_idxOf hm]
          exact List.mem_cons_self
        · rw [correctedSlabLinkPolynomial_of_not_mem hm]
          exact BlockLocal.one _ _
      exact hc.mul ((scalarProduct_local extent links).mono (fun _ h => List.mem_cons_of_mem link h))

theorem bulkProbe_local (half : Nat) : LinkLocal (centralExtent half) (probeLinks half) (lower (bulkProbe half)) := by
  rw [bulkProbe_pin]
  exact (face_scalar_local _ _).character 1

theorem bulkScalar_local (half : Nat) : LinkLocal (centralExtent half) (probeLinks half) (bulkScalar half) :=
  scalarProduct_local _ _

theorem bulkScalar_supported (half : Nat) : SupportedQuaternionBlocks (blocks half) (bulkScalar half) :=
  scalarProduct_supported _ _

theorem source_scalar_pin : scalarProduct 1 (edgesOf (slabPlaquetteAt 1 0)) =
    loopPolynomial (fun _ => (false,false)) := by decide +kernel

theorem scalar_link_embedding {source padding : Nat} {link : Z4Link}
    (hp : link ∈ boundaryCompleteSlabLinks (centralExtent source)) :
    QuaternionPrefixPolynomialEqv (blocks (source+padding))
      ((slabEmbedding source padding).polynomial (correctedSlabLinkPolynomial (centralExtent source) link).scalar)
      (correctedSlabLinkPolynomial (centralExtent (source+padding)) (shiftLink padding padding link)).scalar :=
  (link_pin hp).scalar

theorem scalarProduct_embedding (half : Nat) : ∀ links : List Z4Link,
    (∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks 1) →
    QuaternionPrefixPolynomialEqv (blocks half)
      ((slabEmbedding 0 half).polynomial (scalarProduct 1 links))
      (scalarProduct (centralExtent half) (links.map (shiftLink half half)))
  | [], _ => by simpa only [Nat.zero_add] using (slabEmbedding 0 half).polynomial_one_prefix
  | link :: links, hp => by
      simp only [scalarProduct, List.map_cons, BlockEmbedding.polynomial_mul]
      have h := scalar_link_embedding (source := 0) (padding := half) (hp link List.mem_cons_self)
      apply QuaternionPrefixPolynomialEqv.mul
      · simpa only [Nat.zero_add] using h
      · exact scalarProduct_embedding half links (fun l hl => hp l (List.mem_cons_of_mem link hl))

theorem bulkScalar_embedding (half : Nat) : QuaternionPrefixPolynomialEqv (blocks half)
    ((slabEmbedding 0 half).polynomial (loopPolynomial (fun _ => (false,false)))) (bulkScalar half) := by
  unfold bulkScalar probeLinks probeFace
  rw [edgesOf_shiftFace, ← source_scalar_pin]
  exact scalarProduct_embedding half _ (fun link hl => (mem_boundaryCompleteSlabLinks_iff _ _).mpr
    ⟨slabPlaquetteAt 1 0, slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp probeId_lower).1, hl⟩)

theorem bulkProbe_embedding (half : Nat) : QuaternionPrefixPolynomialEqv (blocks half)
    ((slabEmbedding 0 half).polynomial (lower probe)) (lower (bulkProbe half)) := by
  rw [bulkProbe_pin]
  simpa only [Nat.zero_add] using character_pin (half := 0) (padding := half)
    (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp probeId_lower).1) 1

theorem embedded_moment (half : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks 116 p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (he : QuaternionPrefixPolynomialEqv (blocks half) ((slabEmbedding 0 half).polynomial p) q) :
    quaternionHaar (blocks half) q ≈ quaternionHaar 116 p := by
  have hsupport : SupportedQuaternionBlocks (blocks half) ((slabEmbedding 0 half).polynomial p) := by
    simpa only [Nat.zero_add] using (slabEmbedding 0 half).polynomial_supported p
  have h := haar_embedding 0 half p (by simpa only [carrier_count] using hp)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ he hsupport hq))
    (by simpa only [Nat.zero_add, carrier_count] using h)

theorem bulkProbe_haar_zero (half : Nat) : quaternionHaar (blocks half) (lower (bulkProbe half)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (embedded_moment half (by simpa only [carrier_count] using lower_supported probe)
    (lower_supported _) (bulkProbe_embedding half)) probe_haar_zero

theorem source_scalar_supported : SupportedQuaternionBlocks 116 (loopPolynomial (fun _ => (false,false))) := by
  rw [← source_scalar_pin]
  have h := scalarProduct_supported 1 (edgesOf (slabPlaquetteAt 1 0))
  rw [correctedSlabLinks_extent_one_length] at h
  exact h

theorem bulkScalar_haar_zero (half : Nat) : quaternionHaar (blocks half) (bulkScalar half) ≈ 0 :=
  Q'.eqv_trans _ _ _ (embedded_moment half source_scalar_supported (bulkScalar_supported half)
    (bulkScalar_embedding half)) scalarChannel_haar_zero

theorem bulk_mixed_haar (half : Nat) :
    quaternionHaar (blocks half) (polyMul (lower (bulkProbe half)) (bulkScalar half)) ≈ Q'.invSucc 127 := by
  apply Q'.eqv_trans _ _ _ (embedded_moment half
    (supported_polyMul (by simpa only [carrier_count] using lower_supported probe) source_scalar_supported)
    (supported_polyMul (lower_supported _) (bulkScalar_supported half)) ?_) probe_scalarChannel_haar
  rw [BlockEmbedding.polynomial_mul]
  exact (bulkProbe_embedding half).mul (bulkScalar_embedding half)

/-- Signed spectator insertions are allowed; disjointness is a proved
syntactic block condition, and no positive-law replacement is used. -/
theorem spectator_factor (half : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks half) p) (hq : SupportedQuaternionBlocks (blocks half) q)
    (hl : LinkLocal (centralExtent half) (probeLinks half) p)
    (hr : LinkLocal (centralExtent half) (faceLinks (centralExtent half) (lowerSpectators half)) q) :
    quaternionHaar (blocks half) (polyMul p q) ≈
      quaternionHaar (blocks half) p * quaternionHaar (blocks half) q :=
  haar_product hp hq (linkLocal_disjoint hl hr (lowerSpectators_disjoint half))

theorem mixed_spectator_moment (half : Nat) {q : RatPoly}
    (hq : SupportedQuaternionBlocks (blocks half) q)
    (hr : LinkLocal (centralExtent half) (faceLinks (centralExtent half) (lowerSpectators half)) q) :
    quaternionHaar (blocks half) (polyMul (polyMul (lower (bulkProbe half)) (bulkScalar half)) q) ≈
      Q'.invSucc 127 * quaternionHaar (blocks half) q :=
  Q'.eqv_trans _ _ _ (spectator_factor half (supported_polyMul (lower_supported _) (bulkScalar_supported half))
    hq ((bulkProbe_local half).mul (bulkScalar_local half)) hr)
    (Q'.mul_eqv_congr_right _ _ _ (bulk_mixed_haar half))

end YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.probeId_translated_lower
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkProbe_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.scalarProduct_exposed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkScalar_coordinate_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.scalarProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.scalarProduct_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkProbe_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkScalar_local
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkScalar_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.source_scalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.scalar_link_embedding
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.scalarProduct_embedding
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkScalar_embedding
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkProbe_embedding
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.embedded_moment
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkProbe_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.source_scalar_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulkScalar_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.bulk_mixed_haar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.spectator_factor
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference.mixed_spectator_moment
