/-
# Head degree of an arbitrary original physical plaquette

The actual corrected slab face word has degree one in each of its four
physical boundary links. A supported predictor omitting the selected link
has degree zero after the same original-carrier head swap. These are exact
finite polynomial statements, not an interacting variance estimate.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteIncidentLinear
import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection

namespace YMGap.Continuum.BF4ExactSlabSelectedPlaquetteDegree

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The fundamental character of EVERY original physical slab face is
head-linear at any one of its four physical links. -/
theorem faceCharacter_head_degree_one {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) {link : Z4Link}
    (hedge : link ∈ edgesOf face) :
    let hl : link ∈ boundaryCompleteSlabLinks extent :=
      (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hedge⟩
    HasQuaternionBlockDegree 0 1
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl)
        (faceCharacter extent face)) := by
  let hl : link ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hedge⟩
  have hdegree : HasQuaternionBlockDegree
      ((boundaryCompleteSlabLinks extent).idxOf link) 1
      (faceCharacter extent face) := by
    have hp := face_degree extent ((boundaryCompleteSlabLinks extent).idxOf link) face hf
    have hpin : faceDegree extent ((boundaryCompleteSlabLinks extent).idxOf link) face = 1 := by
      rw [faceDegree_pin extent link face hl hf, if_pos hedge]
    unfold faceCharacter
    simpa [characterPolynomial] using
      (HasQuaternionBlockDegree.relabel hpin hp).smul 2
  exact blockDegree_reindex (linkHeadSwap extent link hl)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
    (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl)) hdegree

/-- Every literal link-local predictor missing the chosen physical link is
head-independent on the SAME complete-slab carrier. -/
theorem linkLocal_head_degree_zero {extent : Nat} {links : List Z4Link}
    {q : RatPoly} (hq : LinkLocal extent links q) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hfree : link ∉ links) :
    HasQuaternionBlockDegree 0 0
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) q) :=
  blockDegree_reindex (linkHeadSwap extent link hl)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
    (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl))
    (linkLocal_degree_zero hq link hl hfree)

#print axioms faceCharacter_head_degree_one
#print axioms linkLocal_head_degree_zero

end YMGap.Continuum.BF4ExactSlabSelectedPlaquetteDegree
