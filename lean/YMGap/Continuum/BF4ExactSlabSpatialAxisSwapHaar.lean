/-
# Literal slab spatial-swap Haar change of variables

The x1/x2 swap permutes the SAME complete slab link list. All four link
coordinates are transported without signs, including physical-time links.
The p12 boundary reversal is handled by the checked conjugate-word scalar
identity, not by commuting quaternion factors. Polynomial padding is retained.

Haar invariance requires support in the actual slab carrier. This finite
change of variables does not assert continuum rotations or a width isometry.
-/

import YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local infix:50 " ≈ " => Q'.eqv

/-- The index of the literal swapped slab link, not an abstract permutation. -/
def swapBlock (extent block : Nat) : Nat :=
  (boundaryCompleteSlabLinks extent).idxOf
    (swapLink (correctedSlabLinkAt extent block))

theorem swapBlock_physical {extent block : Nat}
    (hb : block < (boundaryCompleteSlabLinks extent).length) :
    swapBlock extent block < (boundaryCompleteSlabLinks extent).length :=
  List.idxOf_lt_length_of_mem
    (swapLink_mem_complete (correctedSlabLinkAt_mem (List.mem_range.mpr hb)))

theorem linkAt_swapBlock {extent block : Nat}
    (hb : block < (boundaryCompleteSlabLinks extent).length) :
    correctedSlabLinkAt extent (swapBlock extent block) =
      swapLink (correctedSlabLinkAt extent block) :=
  correctedSlabLinkAt_idxOf
    (swapLink_mem_complete (correctedSlabLinkAt_mem (List.mem_range.mpr hb)))

theorem swapBlock_involutive {extent block : Nat}
    (hb : block < (boundaryCompleteSlabLinks extent).length) :
    swapBlock extent (swapBlock extent block) = block := by
  apply correctedSlabLinkAt_injective_on_physical
    (List.mem_range.mpr (swapBlock_physical (swapBlock_physical hb)))
    (List.mem_range.mpr hb)
  rw [linkAt_swapBlock (swapBlock_physical hb), linkAt_swapBlock hb]
  exact swapLink_involutive _

def swapQuaternionBlockInvolution (extent : Nat) :
    QuaternionBlockInvolution (boundaryCompleteSlabLinks extent).length where
  map := swapBlock extent
  map_lt := fun _ hb => swapBlock_physical hb
  involutive := fun _ hb => swapBlock_involutive hb

theorem swapBlock_idxOf {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    swapBlock extent ((boundaryCompleteSlabLinks extent).idxOf link) =
      (boundaryCompleteSlabLinks extent).idxOf (swapLink link) := by
  unfold swapBlock
  rw [correctedSlabLinkAt_idxOf hl]

def swapPolynomial (extent : Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (swapQuaternionBlockInvolution extent) p

theorem swapPolynomial_one_prefix (extent : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent polyOne) polyOne :=
  reindex_polyOne_prefix (swapQuaternionBlockInvolution extent)

/-- Reindexing produces precisely the full carrier-length exponent vectors.
This is support, not preservation of variables outside the physical carrier. -/
theorem swapPolynomial_supported (extent : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent p) :=
  fun t ht => Nat.le_of_eq
    (reindex_term_length (swapQuaternionBlockInvolution extent) p t ht)

theorem swapPolynomial_haar (extent : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length (swapPolynomial extent p) ≈
      quaternionHaar (boundaryCompleteSlabLinks extent).length p :=
  quaternionHaar_reindex (swapQuaternionBlockInvolution extent) p hp

theorem coordinate_swap_prefix {extent block : Nat}
    (hb : block < (boundaryCompleteSlabLinks extent).length)
    (component : Nat) (hc : component < 4) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent (polyVar (4 * block + component)))
      (polyVar (4 * swapBlock extent block + component)) :=
  reindex_coordinate_prefix (swapQuaternionBlockInvolution extent) block hb component hc

def swapQuaternion (extent : Nat) (q : PolyQuaternion) : PolyQuaternion :=
  reindexPolyQuaternion (swapQuaternionBlockInvolution extent) q

/-- Every link direction has the same sign-free coordinate pin. The identity
fallback is also preserved, so the statement holds even outside the link list. -/
theorem link_swap_prefix (extent : Nat) (link : Z4Link) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks extent).length
      (swapQuaternion extent (correctedSlabLinkPolynomial extent link))
      (correctedSlabLinkPolynomial extent (swapLink link)) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · have hs := swapLink_mem_complete hl
    rw [correctedSlabLinkPolynomial_of_mem hl, correctedSlabLinkPolynomial_of_mem hs]
    have hb := List.idxOf_lt_length_of_mem hl
    have h := reindex_coordinateVariable_prefix (swapQuaternionBlockInvolution extent)
      (swapBlock_physical hb) (swapBlock_involutive hb)
    change QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks extent).length
      (swapQuaternion extent (PolyQuaternion.coordinateVariable
        ((boundaryCompleteSlabLinks extent).idxOf link)))
      (PolyQuaternion.coordinateVariable (swapBlock extent
        ((boundaryCompleteSlabLinks extent).idxOf link))) at h
    rw [swapBlock_idxOf hl] at h
    exact h
  · have hs : swapLink link ∉ boundaryCompleteSlabLinks extent :=
      fun h => hl ((swapLink_mem_complete_iff extent link).mp h)
    rw [correctedSlabLinkPolynomial_of_not_mem hl,
      correctedSlabLinkPolynomial_of_not_mem hs]
    exact reindex_polyQuaternionOne_prefix (swapQuaternionBlockInvolution extent)

theorem link_swap (extent : Nat) (link : Z4Link) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapQuaternion extent (correctedSlabLinkPolynomial extent link))
      (correctedSlabLinkPolynomial extent (swapLink link)) :=
  .of_prefix (link_swap_prefix extent link)

private theorem word_swap (extent : Nat) (face : Z4Plaq) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapQuaternion extent
        (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
          (correctedSlabLinkPolynomial extent (faceLinkB face))
          (correctedSlabLinkPolynomial extent (faceLinkC face))
          (correctedSlabLinkPolynomial extent (faceLinkD face))))
      (swappedFaceWord (correctedSlabLinkPolynomial extent) face) := by
  unfold swapQuaternion plaquetteWord swappedFaceWord
  rw [reindexPolyQuaternion_mul, reindexPolyQuaternion_mul,
    reindexPolyQuaternion_mul, reindexPolyQuaternion_conj, reindexPolyQuaternion_conj]
  exact (((link_swap extent (faceLinkA face)).mul
    (link_swap extent (faceLinkB face))).mul
    (link_swap extent (faceLinkC face)).conj).mul
    (link_swap extent (faceLinkD face)).conj

private theorem plaquette_word_swap (extent : Nat) (face : Z4Plaq) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapQuaternion extent (correctedSlabPlaquettePolynomial extent face))
      (swappedFaceWord (correctedSlabLinkPolynomial extent) face) :=
  (PaddedQuaternionCoeffEqv.of_coeff
    (reindex_coeffEqv (swapQuaternionBlockInvolution extent)
      (plaquette_eq_word extent face))).trans (word_swap extent face)

theorem plaquette_scalar_swap (extent : Nat) (face : Z4Plaq) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent (correctedSlabPlaquettePolynomial extent face).scalar)
      (correctedSlabPlaquettePolynomial extent (swapPlaquette face)).scalar := by
  have hsource : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent (correctedSlabPlaquettePolynomial extent face).scalar)
      (swappedFaceWord (correctedSlabLinkPolynomial extent) face).scalar := by
    simpa only [PaddedPolynomialCoeffEqv, swapPolynomial, swapQuaternion,
      reindexPolyQuaternion] using (plaquette_word_swap extent face).scalar
  have htarget : PolyQuaternionCoeffEqv
      (correctedSlabPlaquettePolynomial extent (swapPlaquette face))
      (targetFaceWord (correctedSlabLinkPolynomial extent) face) :=
    plaquette_eq_word extent (swapPlaquette face)
  have hword : RatPolyCoeffEqv
      (swappedFaceWord (correctedSlabLinkPolynomial extent) face).scalar
      (correctedSlabPlaquettePolynomial extent (swapPlaquette face)).scalar :=
    (swappedFaceWord_scalar (correctedSlabLinkPolynomial extent) face).trans htarget.scalar.symm
  exact hsource.trans (PaddedPolynomialCoeffEqv.of_coeff hword)

theorem plaquette_character_swap (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (swapPolynomial extent
        (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin))
      (characterPolynomial
        (correctedSlabPlaquettePolynomial extent (swapPlaquette face)).scalar spin) :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reindexQuaternionPolynomial_character_prefix (swapQuaternionBlockInvolution extent)
      (correctedSlabPlaquettePolynomial extent face).scalar spin)).trans
    ((plaquette_scalar_swap extent face).character spin)

end YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar

#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapBlock_physical
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.linkAt_swapBlock
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapBlock_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapQuaternionBlockInvolution
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapBlock_idxOf
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapPolynomial_one_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapPolynomial_supported
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.swapPolynomial_haar
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.coordinate_swap_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.link_swap_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.link_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.plaquette_scalar_swap
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapHaar.plaquette_character_swap
