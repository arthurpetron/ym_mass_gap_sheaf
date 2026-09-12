/-
# Literal polynomial reflection of every physical spatial link

The original slab reflection permutes physical link blocks and conjugates
time-link vector coordinates. For a spatial link the sign is absent, so all
four components are those of its literal reflected mate. The proof is
structural at every extent and carries common padding explicitly.

This is the coordinate input to reflection of the actual representation
channels. Global reflected-square gluing, slab positivity and the physical
transfer/gap/continuum construction remain open.
-/

import YMGap.Continuum.BF4ExactSlabTemporalGaugeHaarForm

namespace YMGap.Continuum.BF4ExactSlabSpatialLinkReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
open YMGap.Continuum.SU2QuaternionCoordinateConjugation
open YMGap.Continuum.SU2QuaternionTranslationWordComposition

theorem correctedSlabLinkAt_idxOf {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    correctedSlabLinkAt extent ((boundaryCompleteSlabLinks extent).idxOf link) = link := by
  unfold correctedSlabLinkAt
  rw [← List.getElem_eq_getD (h := List.idxOf_lt_length_of_mem hl)]
  exact eq_of_beq (List.findIdx_getElem (w := List.idxOf_lt_length_of_mem hl))

theorem reflectedBlock_idxOf {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    correctedSlabLinkReflectBlock extent ((boundaryCompleteSlabLinks extent).idxOf link) =
      (boundaryCompleteSlabLinks extent).idxOf (timeReflectLink extent link) := by
  have hi : (boundaryCompleteSlabLinks extent).idxOf link ∈ correctedSlabLinkBlocks extent :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hl)
  have hr := timeReflectLink_mem_boundaryCompleteSlabLinks hl
  apply correctedSlabLinkAt_injective_on_physical (correctedSlabLinkReflectBlock_physical hi)
    (List.mem_range.mpr (List.idxOf_lt_length_of_mem hr))
  rw [correctedSlabLinkAt_reflectBlock hi, correctedSlabLinkAt_idxOf hl, correctedSlabLinkAt_idxOf hr]

/-- A single arbitrary block involution has the expected coordinate image;
the initial identity padding in the double-reindex theorem is removed only
through its proved prefix relation. -/
theorem reindex_coordinate_prefix {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (block : Nat) (hb : block < blocks) (component : Nat) (hc : component < 4) :
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial permutation (polyVar (4 * block + component)))
      (polyVar (4 * permutation.map block + component)) := by
  have h := reindexTwice_polyVar_prefix (identityQuaternionBlockInvolution blocks) permutation
    (permutation.map_lt block hb) hc (permutation.involutive block hb)
  exact (prefix_symm (QuaternionPrefixPolynomialEqv.reindex permutation
    (identityReindexQuaternionPolynomial_prefix blocks (polyVar (4 * block + component))))).trans h

theorem spatial_sign_false {extent block : Nat} (hb : block ∈ correctedSlabLinkBlocks extent)
    (hs : (correctedSlabLinkAt extent block).2 ≠ .x3) (component : Nat) (hc : component < 4) :
    correctedSlabTimeVectorCoordinate extent (4 * correctedSlabLinkReflectBlock extent block + component) = false := by
  unfold correctedSlabTimeVectorCoordinate
  rw [show (4 * correctedSlabLinkReflectBlock extent block + component) / 4 =
    correctedSlabLinkReflectBlock extent block by omega,
    correctedSlabLinkAt_reflectBlock hb, timeReflectLink_direction]
  exact decide_eq_false (fun h => hs h.1)

theorem spatial_coordinate_reflection_prefix {extent block : Nat}
    (hb : block ∈ correctedSlabLinkBlocks extent)
    (hs : (correctedSlabLinkAt extent block).2 ≠ .x3) (component : Nat) (hc : component < 4) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (reflectCorrectedSlabPolynomial extent (polyVar (4 * block + component)))
      (polyVar (4 * correctedSlabLinkReflectBlock extent block + component)) := by
  have h := (reindex_coordinate_prefix (correctedSlabQuaternionBlockInvolution extent)
    block (correctedSlabLinkBlock_lt hb) component hc).signSelected (correctedSlabTimeVectorCoordinate extent)
  change QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
    (reflectCorrectedSlabPolynomial extent (polyVar (4 * block + component)))
    (signSelectedPolynomial (4 * (boundaryCompleteSlabLinks extent).length)
      (correctedSlabTimeVectorCoordinate extent)
      (polyVar (4 * correctedSlabLinkReflectBlock extent block + component))) at h
  have hi := correctedSlabLinkBlock_lt (correctedSlabLinkReflectBlock_physical hb)
  rw [signSelectedPolynomial_var _ _ _ (by omega), spatial_sign_false hb hs component hc] at h
  exact h

def reflectSlabQuaternion (extent : Nat) (q : PolyQuaternion) : PolyQuaternion where
  scalar := reflectCorrectedSlabPolynomial extent q.scalar
  iPart := reflectCorrectedSlabPolynomial extent q.iPart
  jPart := reflectCorrectedSlabPolynomial extent q.jPart
  kPart := reflectCorrectedSlabPolynomial extent q.kPart

theorem spatial_link_reflection_prefix {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hs : link.2 ≠ .x3) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks extent).length
      (reflectSlabQuaternion extent (correctedSlabLinkPolynomial extent link))
      (correctedSlabLinkPolynomial extent (timeReflectLink extent link)) := by
  have hb : (boundaryCompleteSlabLinks extent).idxOf link ∈ correctedSlabLinkBlocks extent :=
    List.mem_range.mpr (List.idxOf_lt_length_of_mem hl)
  have hsp : (correctedSlabLinkAt extent ((boundaryCompleteSlabLinks extent).idxOf link)).2 ≠ .x3 := by
    rw [correctedSlabLinkAt_idxOf hl]
    exact hs
  have coordinate (i : Nat) (hi : i < 4) := spatial_coordinate_reflection_prefix hb hsp i hi
  simp only [reflectedBlock_idxOf hl] at coordinate
  rw [correctedSlabLinkPolynomial_of_mem hl,
    correctedSlabLinkPolynomial_of_mem (timeReflectLink_mem_boundaryCompleteSlabLinks hl)]
  exact ⟨coordinate 0 (by omega), coordinate 1 (by omega), coordinate 2 (by omega), coordinate 3 (by omega)⟩

/-- Coefficient-sensitive reflection pin for all four actual spatial-link
components. This supplies the real/imaginary representation-channel input. -/
theorem spatial_link_reflection {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hs : link.2 ≠ .x3) :
    PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (reflectSlabQuaternion extent (correctedSlabLinkPolynomial extent link))
      (correctedSlabLinkPolynomial extent (timeReflectLink extent link)) :=
  .of_prefix (spatial_link_reflection_prefix hl hs)

end YMGap.Continuum.BF4ExactSlabSpatialLinkReflection

#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.correctedSlabLinkAt_idxOf
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.reflectedBlock_idxOf
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.reindex_coordinate_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.spatial_sign_false
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.spatial_coordinate_reflection_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.reflectSlabQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.spatial_link_reflection_prefix
#print axioms YMGap.Continuum.BF4ExactSlabSpatialLinkReflection.spatial_link_reflection
