/-
# Coordinate-preserving inclusion of the ORIGINAL slab carrier

For source <= target, the actual source links and ordered plaquette words
are included at the SAME coordinates. Only their indices in the finite
enumerations change. This gives a computable injective quaternion-block
map and pins every original character. Product-Haar preservation is the
existing BlockEmbedding theorem, not a new interacting marginal claim.

In particular this includes an odd slab in the adjacent even slab. It is
the finite carrier map needed to compare site positivity with the original
one-step pairing; the exterior action and that pairing pin remain separate.
-/

import YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

namespace YMGap.Continuum.BF4ExactSlabCoordinateInclusion

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

private theorem shift_zero (v : Z4Vertex) : shiftVertex 0 0 v = v := by
  obtain ⟨a,b,c,d⟩ := v
  rfl

theorem face_mem {source target : Nat} (h : source ≤ target) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes source) :
    p ∈ boundaryCompleteSlabPlaquettes target := by
  have hm := shiftFace_mem (space := 0) (time := 0) h h hp
  simpa only [shiftFace, shift_zero] using hm

theorem link_mem {source target : Nat} (h : source ≤ target) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks source) :
    link ∈ boundaryCompleteSlabLinks target := by
  have hm := shiftLink_mem (space := 0) (time := 0) h h hl
  simpa only [shiftLink, shift_zero] using hm

def faceId (source target id : Nat) : Nat :=
  listIndexOf (slabPlaquetteAt source id) (boundaryCompleteSlabPlaquettes target)

theorem faceId_physical {source target id : Nat} (h : source ≤ target)
    (hi : id ∈ slabPhysicalFaceEdges source) :
    faceId source target id ∈ slabPhysicalFaceEdges target :=
  List.mem_range.mpr (listIndexOf_lt_of_mem _ _ (face_mem h (slabPlaquetteAt_mem hi)))

theorem faceId_pin {source target id : Nat} (h : source ≤ target)
    (hi : id ∈ slabPhysicalFaceEdges source) :
    slabPlaquetteAt target (faceId source target id) = slabPlaquetteAt source id :=
  getD_listIndexOf_of_mem _ _ _ (face_mem h (slabPlaquetteAt_mem hi))

theorem faceId_injective {source target i j : Nat} (h : source ≤ target)
    (hi : i ∈ slabPhysicalFaceEdges source) (hj : j ∈ slabPhysicalFaceEdges source)
    (he : faceId source target i = faceId source target j) : i = j := by
  apply slabPlaquetteAt_injective_on_physical hi hj
  rw [← faceId_pin h hi, ← faceId_pin h hj, he]

/-- No coordinates move and no link variables are identified. -/
def embedding {source target : Nat} (h : source ≤ target) :
    BlockEmbedding (boundaryCompleteSlabLinks source).length (boundaryCompleteSlabLinks target).length where
  image := (boundaryCompleteSlabLinks source).map (boundaryCompleteSlabLinks target).idxOf
  length := List.length_map _
  nodup := nodup_map_of_injOn _ _ (boundaryCompleteSlabLinks_nodup _)
    (fun _ ha _ hb => idxOf_injective_on_members (link_mem h ha) (link_mem h hb))
  physical := by
    intro block hb
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp hb
    exact List.idxOf_lt_length_of_mem (link_mem h hl)

theorem embedding_block {source target : Nat} (h : source ≤ target) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks source) :
    (embedding h).block ((boundaryCompleteSlabLinks source).idxOf link) =
      (boundaryCompleteSlabLinks target).idxOf link := by
  have hi := List.idxOf_lt_length_of_mem hl
  change ((boundaryCompleteSlabLinks source).map _).getD _ 0 = _
  rw [← List.getElem_eq_getD (h := by rw [List.length_map]; exact hi), List.getElem_map]
  exact congrArg (fun link => (boundaryCompleteSlabLinks target).idxOf link)
    (eq_of_beq (List.findIdx_getElem (w := hi)))

theorem link_pin {source target : Nat} (h : source ≤ target) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).quaternion (correctedSlabLinkPolynomial source link))
      (correctedSlabLinkPolynomial target link) := by
  rw [correctedSlabLinkPolynomial_of_mem hl, correctedSlabLinkPolynomial_of_mem (link_mem h hl)]
  have he := (embedding h).quaternion_coordinate (List.idxOf_lt_length_of_mem hl)
  rw [embedding_block h hl] at he
  exact he

private theorem oriented_pin {source target : Nat} (h : source ≤ target) {entry : OrientedBF4Link}
    (hl : entry.link ∈ boundaryCompleteSlabLinks source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).quaternion (orientedCorrectedSlabLinkPolynomial source entry))
      (orientedCorrectedSlabLinkPolynomial target entry) := by
  unfold orientedCorrectedSlabLinkPolynomial
  cases hr : entry.reverse
  · exact link_pin h hl
  · simp only [ite_true]
    rw [BlockEmbedding.quaternion_conj]
    exact (link_pin h hl).conj

private theorem fold_pin {source target : Nat} (h : source ≤ target) : ∀ word : List OrientedBF4Link,
    (∀ entry, entry ∈ word → entry.link ∈ boundaryCompleteSlabLinks source) → ∀ p q : PolyQuaternion,
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks target).length ((embedding h).quaternion p) q →
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).quaternion (word.foldl
        (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial source entry)) p))
      (word.foldl (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial target entry)) q)
  | [], _, _, _, he => he
  | entry :: word, hw, p, q, he => by
      apply fold_pin h word (fun e hm => hw e (List.mem_cons_of_mem entry hm))
      rw [BlockEmbedding.quaternion_mul]
      exact he.mul (oriented_pin h (hw entry List.mem_cons_self))

theorem plaquette_pin {source target : Nat} (h : source ≤ target) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).quaternion (correctedSlabPlaquettePolynomial source p))
      (correctedSlabPlaquettePolynomial target p) :=
  fold_pin h _ (fun _ he => orientedPlaquetteBoundary_link_mem_slab hp he) _ _ (embedding h).quaternion_one

theorem character_pin {source target : Nat} (h : source ≤ target) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes source) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length
      ((embedding h).polynomial (characterPolynomial (correctedSlabPlaquettePolynomial source p).scalar spin))
      (characterPolynomial (correctedSlabPlaquettePolynomial target p).scalar spin) :=
  (embedding h).character_of_quaternion (plaquette_pin h hp) spin

theorem odd_even_room (radius : Nat) : centralExtent radius ≤ adjacentEvenExtent radius := by
  unfold adjacentEvenExtent
  omega

end YMGap.Continuum.BF4ExactSlabCoordinateInclusion

#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.face_mem
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.link_mem
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.faceId
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.faceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.faceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.faceId_injective
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.embedding
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.embedding_block
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.link_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.plaquette_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.character_pin
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateInclusion.odd_even_room
