/-
# Off-center time placement of an ORIGINAL slab Haar carrier

A placement carries half-size, enlargement, and an independent temporal
offset between zero and twice the enlargement. Spatial coordinates retain
the centered enlargement. Every original link and ordered plaquette word
is mapped to its actual target coordinate; Haar preservation is derived
from an explicitly injective block embedding. The previous centered map
is exactly the offset=padding specialization, not a different model.

These are original finite product-Haar identities, not invariance of the
full interacting target action. Its exterior factors must still be retained.
-/

import YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding

namespace YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding

structure Placement : Type where
  half : Nat
  padding : Nat
  time : Nat
  time_le : time ≤ padding+padding

namespace Placement

def source (P : Placement) : Nat := centralExtent P.half
def target (P : Placement) : Nat := centralExtent (P.half+P.padding)

theorem space_room (P : Placement) : P.source+P.padding ≤ P.target := central_room (by omega)
theorem time_room (P : Placement) : P.source+P.time ≤ P.target := central_room P.time_le

def faceId (P : Placement) (id : Nat) : Nat := shiftFaceId P.source P.target P.padding P.time id

theorem faceId_physical (P : Placement) {id : Nat} (hi : id ∈ slabPhysicalFaceEdges P.source) :
    P.faceId id ∈ slabPhysicalFaceEdges P.target := shiftFaceId_physical P.space_room P.time_room hi

theorem faceId_pin (P : Placement) {id : Nat} (hi : id ∈ slabPhysicalFaceEdges P.source) :
    slabPlaquetteAt P.target (P.faceId id) = shiftFace P.padding P.time (slabPlaquetteAt P.source id) :=
  shiftFaceId_pin P.space_room P.time_room hi

theorem faceId_injective (P : Placement) {i j : Nat}
    (hi : i ∈ slabPhysicalFaceEdges P.source) (hj : j ∈ slabPhysicalFaceEdges P.source)
    (he : P.faceId i = P.faceId j) : i=j :=
  shiftFaceId_injective P.space_room P.time_room hi hj he

def targetBlock (P : Placement) (link : Z4Link) : Nat :=
  (boundaryCompleteSlabLinks P.target).idxOf (shiftLink P.padding P.time link)

theorem targetBlock_lt (P : Placement) {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks P.source) :
    P.targetBlock link < (boundaryCompleteSlabLinks P.target).length :=
  List.idxOf_lt_length_of_mem (shiftLink_mem P.space_room P.time_room hl)

theorem targetBlock_injective (P : Placement) {a b : Z4Link}
    (ha : a ∈ boundaryCompleteSlabLinks P.source) (hb : b ∈ boundaryCompleteSlabLinks P.source)
    (he : P.targetBlock a = P.targetBlock b) : a=b := by
  have h := idxOf_injective_on_members
    (shiftLink_mem P.space_room P.time_room ha) (shiftLink_mem P.space_room P.time_room hb) he
  obtain ⟨⟨a0,a1,a2,a3⟩, da⟩ := a
  obtain ⟨⟨b0,b1,b2,b3⟩, db⟩ := b
  simpa only [shiftLink, shiftVertex, Prod.mk.injEq, Nat.add_right_cancel_iff] using h

def embedding (P : Placement) :
    BlockEmbedding (boundaryCompleteSlabLinks P.source).length (boundaryCompleteSlabLinks P.target).length where
  image := (boundaryCompleteSlabLinks P.source).map P.targetBlock
  length := List.length_map _
  nodup := nodup_map_of_injOn _ _ (boundaryCompleteSlabLinks_nodup _)
    (fun _ ha _ hb => P.targetBlock_injective ha hb)
  physical := by
    intro block hb
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp hb
    exact P.targetBlock_lt hl

private theorem getD_map_idxOf {A : Type} [BEq A] [LawfulBEq A]
    (f : A → Nat) (xs : List A) {a : A} (ha : a ∈ xs) :
    (xs.map f).getD (xs.idxOf a) 0 = f a := by
  have hi := List.idxOf_lt_length_of_mem ha
  rw [← List.getElem_eq_getD (h := by rw [List.length_map]; exact hi), List.getElem_map]
  exact congrArg f (eq_of_beq (List.findIdx_getElem (w := hi)))

theorem embedding_block (P : Placement) {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks P.source) :
    P.embedding.block ((boundaryCompleteSlabLinks P.source).idxOf link) = P.targetBlock link :=
  getD_map_idxOf _ _ hl

theorem link_pin (P : Placement) {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks P.source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.quaternion (correctedSlabLinkPolynomial P.source link))
      (correctedSlabLinkPolynomial P.target (shiftLink P.padding P.time link)) := by
  rw [correctedSlabLinkPolynomial_of_mem hl,
    correctedSlabLinkPolynomial_of_mem (shiftLink_mem P.space_room P.time_room hl)]
  have h := P.embedding.quaternion_coordinate (List.idxOf_lt_length_of_mem hl)
  rw [P.embedding_block hl] at h
  exact h

def shiftOriented (P : Placement) (entry : OrientedBF4Link) : OrientedBF4Link :=
  ⟨shiftLink P.padding P.time entry.link, entry.reverse⟩

theorem orientedBoundary_shift (P : Placement) (face : Z4Plaq) :
    orientedPlaquetteBoundary (shiftFace P.padding P.time face) =
      (orientedPlaquetteBoundary face).map P.shiftOriented := by
  simp only [orientedPlaquetteBoundary, shiftFace, shiftOriented, shiftLink,
    List.map_cons, List.map_nil, shiftVertex_addE]

theorem oriented_link_pin (P : Placement) {entry : OrientedBF4Link}
    (hl : entry.link ∈ boundaryCompleteSlabLinks P.source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.quaternion (orientedCorrectedSlabLinkPolynomial P.source entry))
      (orientedCorrectedSlabLinkPolynomial P.target (P.shiftOriented entry)) := by
  unfold orientedCorrectedSlabLinkPolynomial
  change QuaternionPrefixPolyQuaternionEqv _ (P.embedding.quaternion (if entry.reverse then _ else _))
    (if entry.reverse then _ else _)
  cases hr : entry.reverse
  · exact P.link_pin hl
  · simp only [ite_true]
    rw [BlockEmbedding.quaternion_conj]
    exact (P.link_pin hl).conj

private theorem fold_pin (P : Placement) : ∀ word : List OrientedBF4Link,
    (∀ entry, entry ∈ word → entry.link ∈ boundaryCompleteSlabLinks P.source) → ∀ p q : PolyQuaternion,
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks P.target).length (P.embedding.quaternion p) q →
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.quaternion (word.foldl
        (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial P.source entry)) p))
      ((word.map P.shiftOriented).foldl
        (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial P.target entry)) q)
  | [], _, _, _, h => h
  | entry :: word, hw, p, q, h => by
      apply fold_pin P word (fun e he => hw e (List.mem_cons_of_mem entry he))
      rw [BlockEmbedding.quaternion_mul]
      exact h.mul (P.oriented_link_pin (hw entry List.mem_cons_self))

theorem plaquette_pin (P : Placement) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes P.source) :
    QuaternionPrefixPolyQuaternionEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.quaternion (correctedSlabPlaquettePolynomial P.source face))
      (correctedSlabPlaquettePolynomial P.target (shiftFace P.padding P.time face)) := by
  unfold correctedSlabPlaquettePolynomial
  rw [P.orientedBoundary_shift]
  exact fold_pin P _ (fun _ he => orientedPlaquetteBoundary_link_mem_slab hf he) _ _ P.embedding.quaternion_one

theorem character_pin (P : Placement) {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes P.source) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial (characterPolynomial (correctedSlabPlaquettePolynomial P.source face).scalar spin))
      (characterPolynomial (correctedSlabPlaquettePolynomial P.target (shiftFace P.padding P.time face)).scalar spin) :=
  P.embedding.character_of_quaternion (P.plaquette_pin hf) spin

theorem haar (P : Placement) (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) :
    Q'.eqv (quaternionHaar (boundaryCompleteSlabLinks P.target).length (P.embedding.polynomial p))
      (quaternionHaar (boundaryCompleteSlabLinks P.source).length p) := P.embedding.haar p hp

end Placement

def centered (half padding : Nat) : Placement := ⟨half, padding, padding, by omega⟩

theorem centered_embedding (half padding : Nat) :
    (centered half padding).embedding = BF4ExactSlabBulkHaarEmbedding.slabEmbedding half padding := rfl

theorem centered_faceId (half padding id : Nat) :
    (centered half padding).faceId id = BF4ExactSlabPlaquetteBulkEmbedding.bulkFaceId half padding 0 id := rfl

end YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.source
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.target
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.space_room
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.time_room
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.faceId
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.faceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.faceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.faceId_injective
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.targetBlock
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.targetBlock_lt
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.targetBlock_injective
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.embedding
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.embedding_block
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.link_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.shiftOriented
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.orientedBoundary_shift
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.oriented_link_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.plaquette_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.character_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.Placement.haar
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.centered
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.centered_embedding
#print axioms YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding.centered_faceId
