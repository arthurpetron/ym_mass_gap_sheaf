/-
# All-spin Haar cancellation at any original plaquette link

The actual ordered plaquette is pinned to four distinct physical blocks.
Cyclic rotation exposes whichever link is independent of the retained
insertion. Every positive spin then vanishes, including the even-spin
cases not detected by center parity. No replacement carrier is used.
-/

import YMGap.Continuum.SU2QuaternionOrientedWordSelection
import YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

theorem linkLocal_degree_zero {extent : Nat} {links : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent links p) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hn : link ∉ links) :
    HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0 p := by
  intro t ht
  have hz := hp t ht _ (List.idxOf_lt_length_of_mem hl)
    (fun h => hn ((correctedSlabLinkAt_idxOf hl) ▸ h))
  have h0 := hz 0 (by decide)
  simp only [Nat.add_zero] at h0
  unfold quaternionBlockDegree
  rw [h0, hz 1 (by decide), hz 2 (by decide), hz 3 (by decide)]

/-- The selected link may be A, B, C or D of the literal oriented boundary. -/
theorem original_character_link_zero {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (link : Z4Link) (hl : link ∈ edgesOf face)
    (spin : Nat) (hs : 0 < spin) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hd : HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0 q) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) q) ≈ 0 := by
  have hn := face_blocks_distinct hf
  have he : link = faceLinkA face ∨ link = faceLinkD face ∨ link = faceLinkC face ∨ link = faceLinkB face := by
    simpa only [edgesOf, faceLinkA, faceLinkB, faceLinkC, faceLinkD, List.mem_cons, List.not_mem_nil, or_false] using hl
  have hm : (boundaryCompleteSlabLinks extent).idxOf link = (blockA hf).val ∨
      (boundaryCompleteSlabLinks extent).idxOf link = (blockB hf).val ∨
      (boundaryCompleteSlabLinks extent).idxOf link = (blockC hf).val ∨
      (boundaryCompleteSlabLinks extent).idxOf link = (blockD hf).val := by
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    ((original_character_eq_coordinateWord hf spin).mul (RatPolyCoeffEqv.refl q)))
    (any_slot_zero (face_carrier_four_blocks hf) (blockA hf) (blockB hf) (blockC hf) (blockD hf)
      hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
      false false true true spin hs q hq _ hm hd)

theorem original_character_local_zero {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (link : Z4Link) (hl : link ∈ edgesOf face)
    (spin : Nat) (hs : 0 < spin) (q : RatPoly) (links : List Z4Link)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hlocal : LinkLocal extent links q) (hn : link ∉ links) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) q) ≈ 0 :=
  original_character_link_zero hf link hl spin hs q hq (linkLocal_degree_zero hlocal link
    ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face,hf,hl⟩) hn)

end YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection

#print axioms YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection.linkLocal_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection.original_character_link_zero
#print axioms YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection.original_character_local_zero
