/-
# Active plaquette characters omit the fixed-slice fringe

Every link of a fully active spatial plaquette belongs to the active block
family. Hence its literal fundamental character is syntactically independent
of every fringe block. Strict spatial padding supplies the activity premise
automatically for a face from the smaller slice.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence
  (characterFace_independent_index)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)

/-- A fully active literal spatial plaquette character has no dependence on
any block in the complementary fringe family. -/
theorem plaquette_fringe_independent (width : Nat) (face : Z4Plaq)
    (_hf : face ∈ spatialFaces width) (hactive : FullyActive width face)
    (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i
      (characterPolynomial (plaquette width face).scalar 1) := by
  apply characterFace_independent_index width face i 1 (fringeBlocks_lt width i hi)
  intro l hl _ he
  exact ((fringeBlocks_mem_iff width i).mp hi).2 (he ▸ hactive l hl)

/-- Strict padding makes every original face fully active, so its character
is automatically independent of the padded carrier's fringe. -/
theorem plaquette_fringe_independent_after_padding {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (i : Nat) (hi : i ∈ fringeBlocks width) :
    QuaternionBlockIndependent i
      (characterPolynomial (plaquette width face).scalar 1) :=
  plaquette_fringe_independent width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf) i hi

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent.plaquette_fringe_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent.plaquette_fringe_independent_after_padding
