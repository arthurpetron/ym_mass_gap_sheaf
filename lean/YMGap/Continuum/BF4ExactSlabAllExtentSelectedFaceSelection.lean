/-
# High-spin selection for original crossing faces at every odd extent

Every actual plaquette supplies four distinct physical link blocks. A
computed four-swap exposure pins its ORIGINAL oriented character to the
canonical word. On a central crossing face, all other crossing characters
have degree zero in its exposed block. Consequently the full retained
product vanishes above a bound computed solely from the fixed insertion.

This is exact full-carrier Haar cancellation at arbitrary odd extent, not
a positive-law substitution or a strict gap. Cutoff resummation, slab
compatibility, physical time and continuum limits are separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree
import YMGap.Continuum.SU2QuaternionFourBlockSelection
import YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection

namespace YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabVacuumInteriorReduction
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionFourBlockExposure
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

theorem face_links_distinct (face : Z4Plaq) :
    faceLinkA face ≠ faceLinkB face ∧ faceLinkA face ≠ faceLinkC face ∧
    faceLinkA face ≠ faceLinkD face ∧ faceLinkB face ≠ faceLinkC face ∧
    faceLinkB face ≠ faceLinkD face ∧ faceLinkC face ≠ faceLinkD face := by
  obtain ⟨⟨x, y, z, t⟩, plane⟩ := face
  cases plane <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he
  all_goals simp only [faceLinkA, faceLinkB, faceLinkC, faceLinkD, dirsOf, addE, Prod.mk.injEq] at he
  all_goals first | contradiction | omega

private theorem link_physical {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) {link : Z4Link} (hl : link ∈ edgesOf face) :
    link ∈ boundaryCompleteSlabLinks extent :=
  (mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hl⟩

/-- Index and bound for the original physical link list. -/
def physicalBlock {extent : Nat} {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks extent) :
    Fin (boundaryCompleteSlabLinks extent).length := ⟨_, List.idxOf_lt_length_of_mem hl⟩

def blockA {extent : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :=
  physicalBlock (link_physical hf (show faceLinkA face ∈ edgesOf face by simp [faceLinkA, edgesOf]))
def blockB {extent : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :=
  physicalBlock (link_physical hf (show faceLinkB face ∈ edgesOf face by simp [faceLinkB, edgesOf]))
def blockC {extent : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :=
  physicalBlock (link_physical hf (show faceLinkC face ∈ edgesOf face by simp [faceLinkC, edgesOf]))
def blockD {extent : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :=
  physicalBlock (link_physical hf (show faceLinkD face ∈ edgesOf face by simp [faceLinkD, edgesOf]))

theorem face_blocks_distinct {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    (blockA hf).val ≠ (blockB hf).val ∧ (blockA hf).val ≠ (blockC hf).val ∧
    (blockA hf).val ≠ (blockD hf).val ∧ (blockB hf).val ≠ (blockC hf).val ∧
    (blockB hf).val ≠ (blockD hf).val ∧ (blockC hf).val ≠ (blockD hf).val := by
  have hn := face_links_distinct face
  have inj {a b : Z4Link} (ha : a ∈ edgesOf face) (hb : b ∈ edgesOf face) (hne : a ≠ b) :
      (boundaryCompleteSlabLinks extent).idxOf a ≠ (boundaryCompleteSlabLinks extent).idxOf b :=
    fun h => hne (idxOf_injective_on_members (link_physical hf ha) (link_physical hf hb) h)
  exact ⟨inj (by simp [faceLinkA, edgesOf]) (by simp [faceLinkB, edgesOf]) hn.1,
    inj (by simp [faceLinkA, edgesOf]) (by simp [faceLinkC, edgesOf]) hn.2.1,
    inj (by simp [faceLinkA, edgesOf]) (by simp [faceLinkD, edgesOf]) hn.2.2.1,
    inj (by simp [faceLinkB, edgesOf]) (by simp [faceLinkC, edgesOf]) hn.2.2.2.1,
    inj (by simp [faceLinkB, edgesOf]) (by simp [faceLinkD, edgesOf]) hn.2.2.2.2.1,
    inj (by simp [faceLinkC, edgesOf]) (by simp [faceLinkD, edgesOf]) hn.2.2.2.2.2⟩

theorem face_carrier_four_blocks {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) : 3 < (boundaryCompleteSlabLinks extent).length := by
  have ha := (blockA hf).isLt
  have hb := (blockB hf).isLt
  have hc := (blockC hf).isLt
  have hd := (blockD hf).isLt
  have hn := face_blocks_distinct hf
  omega

/-- A constructed coordinate witness for this actual face; not an assumed pin. -/
def faceExposure {extent : Nat} {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    FourBlockExposure (blockA hf) (blockB hf) (blockC hf) (blockD hf) :=
  let hn := face_blocks_distinct hf
  fourBlockExposure (face_carrier_four_blocks hf) (blockA hf) (blockB hf) (blockC hf) (blockD hf)
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem original_character_eq_coordinateWord {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    RatPolyCoeffEqv (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
      (characterPolynomial (coordinateWord (blockA hf).val (blockB hf).val (blockC hf).val (blockD hf).val).scalar spin) := by
  have hw := (plaquette_eq_word extent face).scalar
  rw [correctedSlabLinkPolynomial_of_mem (link_physical hf (show faceLinkA face ∈ edgesOf face by simp [faceLinkA, edgesOf])),
    correctedSlabLinkPolynomial_of_mem (link_physical hf (show faceLinkB face ∈ edgesOf face by simp [faceLinkB, edgesOf])),
    correctedSlabLinkPolynomial_of_mem (link_physical hf (show faceLinkC face ∈ edgesOf face by simp [faceLinkC, edgesOf])),
    correctedSlabLinkPolynomial_of_mem (link_physical hf (show faceLinkD face ∈ edgesOf face by simp [faceLinkD, edgesOf]))] at hw
  exact characterPolynomial_coeffEqv hw spin

/-- Computed from the fixed insertion and actual selected face only. -/
def selectedFaceBound {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (p : RatPoly) : Nat :=
  selectionBound (faceExposure hf) p

theorem original_character_product_zero {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hd : HasQuaternionBlockDegree (blockA hf).val 0 q) (hs : selectedFaceBound hf p < spin) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length (polyMul
      (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) (polyMul p q)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ ((original_character_eq_coordinateWord hf spin).mul
    (RatPolyCoeffEqv.refl _)))
    (selected_product_zero (face_carrier_four_blocks hf) (faceExposure hf) spin p q hp hq hd hs)

def faceProduct (extent : Nat) (boundary : EdgeLabelling) (faces : List Z4Plaq) : RatPoly :=
  faces.foldr (fun face p => polyMul (correctedSlabPlaquetteSpinFactor extent boundary face) p) polyOne

/-- All other crossing-face characters are retained at unrestricted spins. -/
theorem crossing_faces_product_zero {half : Nat} {selected : Z4Plaq}
    (hf : selected ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hs : plaquetteHalfSide half selected = .fixed) (boundary : EdgeLabelling)
    (others : List Z4Plaq)
    (ho : ∀ face, face ∈ others → face ∈ boundaryCompleteSlabPlaquettes (centralExtent half) ∧
      plaquetteHalfSide half face = .fixed ∧ face ≠ selected)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (hspin : selectedFaceBound hf p < boundary ((boundaryCompleteSlabPlaquettes (centralExtent half)).idxOf selected)) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (polyMul
      (correctedSlabPlaquetteSpinFactor (centralExtent half) boundary selected)
      (polyMul p (faceProduct (centralExtent half) boundary others))) ≈ 0 := by
  apply original_character_product_zero hf _ p _ hp
    (correctedSlabSpinNetworkFaces_support _ boundary others) _ hspin
  exact other_characters_degree_zero hf hs
    (fun face => boundary ((boundaryCompleteSlabPlaquettes (centralExtent half)).idxOf face)) others ho

end YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.face_links_distinct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.physicalBlock
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.face_blocks_distinct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.face_carrier_four_blocks
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.faceExposure
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.original_character_eq_coordinateWord
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.selectedFaceBound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.original_character_product_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.faceProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection.crossing_faces_product_zero
