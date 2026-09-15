/-
# Common auxiliary vertex gauges on the actual corrected slab

One vertex-tag function supplies BOTH endpoints of EVERY physical link.
The original all-link ledger has that common coordinate image, preserves
the whole supported Haar integral, and sends every physical plaquette word
to its consistently gauged word. All-spin plaquette characters are invariant
under arbitrary insertions on the augmented original Haar carrier.

The three added gauge variables precede the ORIGINAL slab coordinates.
This is the global coordinate/plaquette part of the scalar-test identification.
The full original action/insertion image and resulting cutoff/volume/completion
comparison remain to be composed. `BF4ExactSlabBulkScalarVertexImage` supplies
the concrete probe's tags and its literal scalar image under this same ledger.
No completed scalar-test identity or actual-transfer preimage is asserted.
-/

import YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
import YMGap.Continuum.BF4ExactSlabBulkScalarGaugeAverage

namespace YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

def linkCount (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

private theorem lift_var (k : Nat) : liftHead (polyVar k) = polyVar (k + 4) := by
  simp only [liftHead, polyVar, varMono, List.map_cons, List.map_nil,
    List.replicate_succ, List.cons_append]

private theorem lift_coordinate (k : Nat) :
    liftQuaternion (PolyQuaternion.coordinateVariable k) = PolyQuaternion.coordinateVariable (k + 1) := by
  simp only [liftQuaternion, PolyQuaternion.coordinateVariable, lift_var]
  congr 2 <;> omega

/-- Reserving the three gauge blocks gives exactly the original index +3. -/
theorem liftThree_coordinate (k : Nat) :
    liftThree (PolyQuaternion.coordinateVariable k) = PolyQuaternion.coordinateVariable (k + 3) := by
  simp only [liftThree, lift_coordinate]

def sourceLink (extent : Nat) (i : Fin (linkCount extent)) : Z4Link :=
  correctedSlabLinkAt extent i.val

def startTag (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (i : Fin (linkCount extent)) : Option (Fin 3) :=
  tags (sourceLink extent i).1

def finishTag (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (i : Fin (linkCount extent)) : Option (Fin 3) :=
  tags (addE (sourceLink extent i).1 (sourceLink extent i).2)

def slabGaugePolynomial (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (p : RatPoly) : RatPoly :=
  gaugePolynomial (startTag extent tags) (finishTag extent tags) p

def slabGaugeQuaternion (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (p : PolyQuaternion) : PolyQuaternion :=
  gaugeQuaternion (startTag extent tags) (finishTag extent tags) p

def liftedLink (extent : Nat) (link : Z4Link) : PolyQuaternion :=
  liftThree (correctedSlabLinkPolynomial extent link)

def vertexLink (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (link : Z4Link) : PolyQuaternion :=
  gaugeLink (auxiliaryGauge (tags link.1)) (liftedLink extent link)
    (auxiliaryGauge (tags (addE link.1 link.2)))

/-- The ENTIRE common ledger has the literal endpoint image on every
physical link, not just on one selected plaquette. -/
theorem slabGauge_link {extent : Nat} (tags : Z4Vertex → Option (Fin 3)) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    PaddedQuaternionCoeffEqv (linkCount extent + 3)
      (slabGaugeQuaternion extent tags (liftedLink extent link)) (vertexLink extent tags link) := by
  let i : Fin (linkCount extent) := ⟨(boundaryCompleteSlabLinks extent).idxOf link,
    List.idxOf_lt_length_of_mem hl⟩
  have hs : sourceLink extent i = link := correctedSlabLinkAt_idxOf hl
  have hp : liftedLink extent link = originalLink i := by
    rw [liftedLink, correctedSlabLinkPolynomial_of_mem hl, liftThree_coordinate]
    rfl
  have h := gaugeQuaternion_link (startTag extent tags) (finishTag extent tags) i
  simpa only [slabGaugeQuaternion, vertexLink, hp, linkImage, startTag, finishTag, hs] using h

theorem slabGauge_haar (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (linkCount extent + 3) p) :
    (quaternionHaar (linkCount extent + 3) (slabGaugePolynomial extent tags p)).eqv
      (quaternionHaar (linkCount extent + 3) p) :=
  gaugePolynomial_haar _ _ p hp

/-- The original ordered word in the augmented original coordinates. -/
def liftedFaceWord (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (liftedLink extent (faceLinkA face)) (liftedLink extent (faceLinkB face))
    (liftedLink extent (faceLinkC face)) (liftedLink extent (faceLinkD face))

def vertexFaceWord (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (vertexLink extent tags (faceLinkA face)) (vertexLink extent tags (faceLinkB face))
    (vertexLink extent tags (faceLinkC face)) (vertexLink extent tags (faceLinkD face))

theorem slabGauge_face_word {extent : Nat} (tags : Z4Vertex → Option (Fin 3)) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    PaddedQuaternionCoeffEqv (linkCount extent + 3)
      (slabGaugeQuaternion extent tags (liftedFaceWord extent face)) (vertexFaceWord extent tags face) := by
  have hlink (link : Z4Link) (hi : link ∈ edgesOf face) :=
    slabGauge_link tags ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hi⟩)
  have ha := hlink (faceLinkA face) (by simp [faceLinkA, edgesOf])
  have hb := hlink (faceLinkB face) (by simp [faceLinkB, edgesOf])
  have hc := hlink (faceLinkC face) (by simp [faceLinkC, edgesOf])
  have hd := hlink (faceLinkD face) (by simp [faceLinkD, edgesOf])
  have hm (p q : PolyQuaternion) : PaddedQuaternionCoeffEqv (linkCount extent + 3)
      (slabGaugeQuaternion extent tags (PolyQuaternion.mul p q))
      (PolyQuaternion.mul (slabGaugeQuaternion extent tags p) (slabGaugeQuaternion extent tags q)) :=
    applySteps_mul _ _ p q
  have hs (p : PolyQuaternion) : PaddedQuaternionCoeffEqv (linkCount extent + 3)
      (slabGaugeQuaternion extent tags (PolyQuaternion.conj p))
      (PolyQuaternion.conj (slabGaugeQuaternion extent tags p)) := applySteps_conj _ _ p
  exact (hm _ _).trans
    (((hm _ _).trans (((hm _ _).trans (ha.mul hb)).mul ((hs _).trans hc.conj))).mul
      ((hs _).trans hd.conj))

theorem auxiliaryGauge_unit (extent : Nat) (tag : Option (Fin 3)) :
    HaarCarrierEqv (linkCount extent + 3) (polyQuaternionNorm (auxiliaryGauge tag)) polyOne := by
  cases tag with
  | none => exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one
  | some j => exact haarNorm_coordinate (by have := j.isLt; omega)

private theorem far_corner (face : Z4Plaq) :
    addE (addE face.1 (dirsOf face.2).2) (dirsOf face.2).1 =
      addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2 := by
  rcases face with ⟨⟨x,y,z,t⟩, plane⟩
  cases plane <;> rfl

/-- The SAME vertex field preserves every spin character, under arbitrary
insertions including neighboring action factors sharing original links. -/
theorem vertexFace_character (extent : Nat) (tags : Z4Vertex → Option (Fin 3))
    (face : Z4Plaq) (spin : Nat) :
    HaarCarrierEqv (linkCount extent + 3)
      (characterPolynomial (vertexFaceWord extent tags face).scalar spin)
      (characterPolynomial (liftedFaceWord extent face).scalar spin) := by
  have h := plaquette_gauge_character
    (auxiliaryGauge (tags face.1))
    (auxiliaryGauge (tags (addE face.1 (dirsOf face.2).1)))
    (auxiliaryGauge (tags (addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2)))
    (auxiliaryGauge (tags (addE face.1 (dirsOf face.2).2)))
    (liftedLink extent (faceLinkA face)) (liftedLink extent (faceLinkB face))
    (liftedLink extent (faceLinkC face)) (liftedLink extent (faceLinkD face))
    (auxiliaryGauge_unit extent _) (auxiliaryGauge_unit extent _)
    (auxiliaryGauge_unit extent _) (auxiliaryGauge_unit extent _) spin
  simp only [vertexFaceWord, vertexLink, faceLinkA, faceLinkB, faceLinkC, faceLinkD, far_corner]
  exact h

end YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge

#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.linkCount
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.liftThree_coordinate
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.sourceLink
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.startTag
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.finishTag
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.slabGaugePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.slabGaugeQuaternion
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.liftedLink
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.vertexLink
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.slabGauge_link
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.slabGauge_haar
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.liftedFaceWord
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.vertexFaceWord
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.slabGauge_face_word
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.auxiliaryGauge_unit
#print axioms YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge.vertexFace_character
