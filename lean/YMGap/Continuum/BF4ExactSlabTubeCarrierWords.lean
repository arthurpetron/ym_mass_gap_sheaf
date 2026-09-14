/-
# Ordered tube words in the full ORIGINAL carrier

All four plaquette slices and twelve swept temporal characters are pinned
to one full carrier permutation, for every volume margin. The selected
product retains arbitrary coefficients, endpoint centers and a spectator
polynomial. This is coefficient-sensitive recoding, not a lower bound for
the full action or permission to discard its other face selections.
-/

import YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding

namespace YMGap.Continuum.BF4ExactSlabTubeCarrierWords

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabTubeCarrierEmbedding
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation

local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

def compactSlice (time : Fin 4) : RatPoly :=
  plaquette (4*time.val) (4*time.val+1) (4*time.val+2) (4*time.val+3)

def literalSlice (margin : Nat) (time : Fin 4) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial (responseExtent margin) (sliceFace margin time.val)).scalar 1

private theorem slice_link_pins (margin : Nat) (time : Fin 4) :
    sourceLink margin (4*time.val) = faceLinkA (sliceFace margin time.val) ∧
    sourceLink margin (4*time.val+1) = faceLinkB (sliceFace margin time.val) ∧
    sourceLink margin (4*time.val+2) = faceLinkC (sliceFace margin time.val) ∧
    sourceLink margin (4*time.val+3) = faceLinkD (sliceFace margin time.val) := by
  have h0 := sourceLink_slice margin time ⟨0,by decide⟩
  have h1 := sourceLink_slice margin time ⟨1,by decide⟩
  have h2 := sourceLink_slice margin time ⟨2,by decide⟩
  have h3 := sourceLink_slice margin time ⟨3,by decide⟩
  rw [← slice_word_links] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

private theorem face_word (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face)
      (plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))) := by
  simp only [correctedSlabPlaquettePolynomial, orientedPlaquetteBoundary,
    List.foldl_cons, List.foldl_nil, orientedCorrectedSlabLinkPolynomial,
    Bool.false_eq_true, if_false, if_true, plaquetteWord, faceLinkA, faceLinkB,
    faceLinkC, faceLinkD]
  exact (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)

theorem slice_embedding_pin (margin : Nat) (time : Fin 4) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (compactSlice time)) (literalSlice margin time) := by
  have ht := time.isLt
  have hw : QuaternionPrefixPolyQuaternionEqv (N margin)
      ((carrierEmbedding margin).quaternion (plaquetteWord
        (PolyQuaternion.coordinateVariable (4*time.val))
        (PolyQuaternion.coordinateVariable (4*time.val+1))
        (PolyQuaternion.coordinateVariable (4*time.val+2))
        (PolyQuaternion.coordinateVariable (4*time.val+3))))
      (plaquetteWord
        (correctedSlabLinkPolynomial (responseExtent margin) (sourceLink margin (4*time.val)))
        (correctedSlabLinkPolynomial (responseExtent margin) (sourceLink margin (4*time.val+1)))
        (correctedSlabLinkPolynomial (responseExtent margin) (sourceLink margin (4*time.val+2)))
        (correctedSlabLinkPolynomial (responseExtent margin) (sourceLink margin (4*time.val+3)))) := by
    simp only [plaquetteWord, (carrierEmbedding margin).quaternion_mul,
      (carrierEmbedding margin).quaternion_conj]
    exact (((carrier_link_pin margin _ (by omega)).mul (carrier_link_pin margin _ (by omega))).mul
      (carrier_link_pin margin _ (by omega)).conj).mul (carrier_link_pin margin _ (by omega)).conj
  rcases slice_link_pins margin time with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3] at hw
  exact (PaddedPolynomialCoeffEqv.of_prefix ((carrierEmbedding margin).character_of_quaternion hw 1)).trans
    (PaddedPolynomialCoeffEqv.of_coeff (characterPolynomial_coeffEqv (face_word _ _).symm.scalar 1))

def sideFace (margin : Nat) (time : Fin 3) (edge : Fin 4) : Z4Plaq :=
  shiftFace margin margin ((baseLayer time.val).getD edge.val ((0,0,0,0),.p01))

theorem sideFace_mem (margin : Nat) (time : Fin 3) (edge : Fin 4) : sideFace margin time edge ∈ tubeSides margin := by
  have hb : ∀ t : Fin 3, ∀ e : Fin 4,
      (baseLayer t.val).getD e.val ((0,0,0,0),.p01) ∈ baseSides := by decide +kernel
  exact List.mem_map.mpr ⟨_,hb time edge,rfl⟩

theorem side_link_pins (margin : Nat) (time : Fin 3) (edge : Fin 4) :
    faceLinkA (sideFace margin time edge) = sourceLink margin (4*time.val+edge.val) ∧
    faceLinkC (sideFace margin time edge) = sourceLink margin (4*(time.val+1)+edge.val) := by
  have ht := time.isLt
  rw [sourceLink_slice margin ⟨time.val,by omega⟩ edge,
    sourceLink_slice margin ⟨time.val+1,by omega⟩ edge]
  rcases edge with ⟨e,he⟩
  have he' : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases he' with rfl | rfl | rfl | rfl
  all_goals simp [sideFace, baseLayer, sliceLinks, shiftFace, shiftVertex,
    faceLinkA, faceLinkC, dirsOf, addE, Nat.add_comm, Nat.add_assoc]

def compactSide (time : Fin 3) (edge : Fin 4) : RatPoly :=
  sideCharacter (4*time.val+edge.val) (4*(time.val+1)+edge.val)

def literalSide (margin : Nat) (time : Fin 3) (edge : Fin 4) : RatPoly :=
  sweptCharacter (responseExtent margin) (margin+3) (sideFace margin time edge) 1

/-- Same full permutation for every edge of every layer; no independent gauges. -/
theorem side_embedding_pin (margin : Nat) (time : Fin 3) (edge : Fin 4) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (compactSide time edge)) (literalSide margin time edge) := by
  have ht := time.isLt
  have he := edge.isLt
  unfold literalSide
  rw [tube_side_character_pin margin _ (sideFace_mem margin time edge) 1]
  apply PaddedPolynomialCoeffEqv.of_prefix
  apply (carrierEmbedding margin).character_of_quaternion
  rw [(carrierEmbedding margin).quaternion_mul, (carrierEmbedding margin).quaternion_conj]
  rw [(side_link_pins margin time edge).1, (side_link_pins margin time edge).2]
  exact (carrier_link_pin margin _ (by omega)).mul (carrier_link_pin margin _ (by omega)).conj

def sideIds : List (Fin 3 × Fin 4) :=
  (List.finRange 3).flatMap fun time => (List.finRange 4).map fun edge => (time,edge)

theorem sideIds_length : sideIds.length = 12 := rfl

/-- The literal factors enumerate the existing tube face list in its order. -/
theorem side_faces_pin (margin : Nat) :
    (sideIds.map fun i => sideFace margin i.1 i.2) = tubeSides margin := rfl

def compactSides : RatPoly := factorProduct (sideIds.map fun i => compactSide i.1 i.2)

def literalSides (margin : Nat) : RatPoly := factorProduct (sideIds.map fun i => literalSide margin i.1 i.2)

theorem sides_embedding_pin (margin : Nat) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial compactSides) (literalSides margin) := by
  have go : ∀ ids : List (Fin 3 × Fin 4), PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (factorProduct (ids.map fun i => compactSide i.1 i.2)))
      (factorProduct (ids.map fun i => literalSide margin i.1 i.2)) := by
    intro ids
    induction ids with
    | nil => exact .of_prefix (carrierEmbedding margin).polynomial_one_prefix
    | cons i ids ih =>
      simp only [List.map_cons, factorProduct, (carrierEmbedding margin).polynomial_mul]
      exact (side_embedding_pin margin i.1 i.2).mul ih
  exact go sideIds

def compactCenteredSlice (time : Fin 4) (c : Q') : RatPoly :=
  polyAdd (compactSlice time) (polySmul (-c) polyOne)

def literalCenteredSlice (margin : Nat) (time : Fin 4) (c : Q') : RatPoly :=
  polyAdd (literalSlice margin time) (polySmul (-c) polyOne)

theorem centered_slice_embedding_pin (margin : Nat) (time : Fin 4) (c : Q') :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (compactCenteredSlice time c)) (literalCenteredSlice margin time c) := by
  unfold compactCenteredSlice literalCenteredSlice
  rw [(carrierEmbedding margin).polynomial_add, (carrierEmbedding margin).polynomial_smul]
  exact (slice_embedding_pin margin time).add
    ((PaddedPolynomialCoeffEqv.of_prefix (carrierEmbedding margin).polynomial_one_prefix).smul (-c))

/-- Both centered ORIGINAL endpoints, all twelve signed side characters,
an arbitrary scalar weight and the entire mapped spectator polynomial. -/
theorem selected_product_pin (margin : Nat) (weight c d : Q') (spectator : RatPoly) :
    PaddedPolynomialCoeffEqv (N margin)
      ((carrierEmbedding margin).polynomial (polySmul weight
        (polyMul (compactCenteredSlice ⟨0,by decide⟩ c)
          (polyMul compactSides (polyMul (compactCenteredSlice ⟨3,by decide⟩ d) spectator)))))
      (polySmul weight (polyMul (literalCenteredSlice margin ⟨0,by decide⟩ c)
        (polyMul (literalSides margin) (polyMul (literalCenteredSlice margin ⟨3,by decide⟩ d)
          ((carrierEmbedding margin).polynomial spectator))))) := by
  simp only [(carrierEmbedding margin).polynomial_smul, (carrierEmbedding margin).polynomial_mul]
  apply PaddedPolynomialCoeffEqv.smul
  apply PaddedPolynomialCoeffEqv.mul
  · exact centered_slice_embedding_pin margin _ c
  · apply PaddedPolynomialCoeffEqv.mul
    · exact sides_embedding_pin margin
    · exact (centered_slice_embedding_pin margin _ d).mul (.refl _ _)

end YMGap.Continuum.BF4ExactSlabTubeCarrierWords

#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.compactSlice
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.literalSlice
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.slice_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.sideFace
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.sideFace_mem
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.side_link_pins
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.compactSide
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.literalSide
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.side_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.sideIds
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.sideIds_length
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.side_faces_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.compactSides
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.literalSides
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.compactCenteredSlice
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.literalCenteredSlice
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.sides_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.centered_slice_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabTubeCarrierWords.selected_product_pin
