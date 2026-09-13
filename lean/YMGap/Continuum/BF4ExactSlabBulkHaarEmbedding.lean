/-
# Literal bulk link embedding and ORIGINAL plaquette holonomy pin

The Haar block embedding is constructed from the actual translated source
link list, not supplied as a hypothesis. Every source link has one distinct
target block. The induced polynomial map preserves Haar and sends each
original ordered plaquette holonomy to its literal bulk translation.
No interaction is discarded and no boundary-response bound is asserted.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra
import YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse

namespace YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
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

local notation "links" => boundaryCompleteSlabLinks
local notation "extent" => centralExtent

def targetBlock (half padding : Nat) (link : Z4Link) : Nat :=
  (links (extent (half+padding))).idxOf (shiftLink padding padding link)

theorem targetBlock_lt {half padding : Nat} {link : Z4Link} (hl : link ∈ links (extent half)) :
    targetBlock half padding link < (links (extent (half+padding))).length :=
  List.idxOf_lt_length_of_mem (shiftLink_mem (central_room (by omega)) (central_room (by omega)) hl)

theorem targetBlock_injective {half padding : Nat} {a b : Z4Link}
    (ha : a ∈ links (extent half)) (hb : b ∈ links (extent half))
    (he : targetBlock half padding a = targetBlock half padding b) : a = b := by
  have h := idxOf_injective_on_members
    (shiftLink_mem (central_room (show padding ≤ padding+padding by omega)) (central_room (by omega)) ha)
    (shiftLink_mem (central_room (show padding ≤ padding+padding by omega)) (central_room (by omega)) hb) he
  obtain ⟨⟨a0, a1, a2, a3⟩, da⟩ := a
  obtain ⟨⟨b0, b1, b2, b3⟩, db⟩ := b
  simpa only [shiftLink, shiftVertex, Prod.mk.injEq, Nat.add_right_cancel_iff] using h

def slabEmbedding (half padding : Nat) :
    BlockEmbedding (links (extent half)).length (links (extent (half+padding))).length where
  image := (links (extent half)).map (targetBlock half padding)
  length := List.length_map _
  nodup := nodup_map_of_injOn _ _ (boundaryCompleteSlabLinks_nodup _)
    (fun _ ha _ hb => targetBlock_injective ha hb)
  physical := by
    intro block hb
    obtain ⟨link, hl, rfl⟩ := List.mem_map.mp hb
    exact targetBlock_lt hl

private theorem getD_map_idxOf {A : Type} [BEq A] [LawfulBEq A]
    (f : A → Nat) (xs : List A) {a : A} (ha : a ∈ xs) :
    (xs.map f).getD (xs.idxOf a) 0 = f a := by
  have hi := List.idxOf_lt_length_of_mem ha
  rw [← List.getElem_eq_getD (h := by rw [List.length_map]; exact hi), List.getElem_map]
  exact congrArg f (eq_of_beq (List.findIdx_getElem (w := hi)))

theorem slabEmbedding_block {half padding : Nat} {link : Z4Link} (hl : link ∈ links (extent half)) :
    (slabEmbedding half padding).block ((links (extent half)).idxOf link) = targetBlock half padding link :=
  getD_map_idxOf _ _ hl

theorem link_pin {half padding : Nat} {link : Z4Link} (hl : link ∈ links (extent half)) :
    QuaternionPrefixPolyQuaternionEqv (links (extent (half+padding))).length
      ((slabEmbedding half padding).quaternion (correctedSlabLinkPolynomial (extent half) link))
      (correctedSlabLinkPolynomial (extent (half+padding)) (shiftLink padding padding link)) := by
  rw [correctedSlabLinkPolynomial_of_mem hl,
    correctedSlabLinkPolynomial_of_mem (shiftLink_mem (central_room (by omega)) (central_room (by omega)) hl)]
  have h := (slabEmbedding half padding).quaternion_coordinate (List.idxOf_lt_length_of_mem hl)
  rw [slabEmbedding_block hl] at h
  exact h

def shiftOriented (padding : Nat) (entry : OrientedBF4Link) : OrientedBF4Link :=
  ⟨shiftLink padding padding entry.link, entry.reverse⟩

theorem orientedBoundary_shift (padding : Nat) (face : Z4Plaq) :
    orientedPlaquetteBoundary (shiftFace padding padding face) =
      (orientedPlaquetteBoundary face).map (shiftOriented padding) := by
  simp only [orientedPlaquetteBoundary, shiftFace, shiftOriented, shiftLink,
    List.map_cons, List.map_nil, shiftVertex_addE]

theorem oriented_link_pin {half padding : Nat} {entry : OrientedBF4Link}
    (hl : entry.link ∈ links (extent half)) :
    QuaternionPrefixPolyQuaternionEqv (links (extent (half+padding))).length
      ((slabEmbedding half padding).quaternion (orientedCorrectedSlabLinkPolynomial (extent half) entry))
      (orientedCorrectedSlabLinkPolynomial (extent (half+padding)) (shiftOriented padding entry)) := by
  unfold orientedCorrectedSlabLinkPolynomial
  change QuaternionPrefixPolyQuaternionEqv _ ((slabEmbedding half padding).quaternion (if entry.reverse then _ else _))
    (if entry.reverse then _ else _)
  cases hr : entry.reverse
  · exact link_pin hl
  · simp only [ite_true]
    rw [BlockEmbedding.quaternion_conj]
    exact (link_pin hl).conj

private theorem fold_pin {half padding : Nat} : ∀ (word : List OrientedBF4Link),
    (∀ entry, entry ∈ word → entry.link ∈ links (extent half)) → ∀ p q : PolyQuaternion,
    QuaternionPrefixPolyQuaternionEqv (links (extent (half+padding))).length ((slabEmbedding half padding).quaternion p) q →
    QuaternionPrefixPolyQuaternionEqv (links (extent (half+padding))).length
      ((slabEmbedding half padding).quaternion
        (word.foldl (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial (extent half) entry)) p))
      ((word.map (shiftOriented padding)).foldl
        (fun total entry => PolyQuaternion.mul total (orientedCorrectedSlabLinkPolynomial (extent (half+padding)) entry)) q)
  | [], _, _, _, h => h
  | entry :: word, hw, p, q, h => by
      apply fold_pin word (fun e he => hw e (List.mem_cons_of_mem entry he))
      rw [BlockEmbedding.quaternion_mul]
      exact h.mul (oriented_link_pin (hw entry List.mem_cons_self))

theorem plaquette_pin {half padding : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (extent half)) :
    QuaternionPrefixPolyQuaternionEqv (links (extent (half+padding))).length
      ((slabEmbedding half padding).quaternion (correctedSlabPlaquettePolynomial (extent half) face))
      (correctedSlabPlaquettePolynomial (extent (half+padding)) (shiftFace padding padding face)) := by
  unfold correctedSlabPlaquettePolynomial
  rw [orientedBoundary_shift]
  exact fold_pin _ (fun _ he => orientedPlaquetteBoundary_link_mem_slab hf he) _ _ (BlockEmbedding.quaternion_one _)

theorem character_pin {half padding : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes (extent half)) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (links (extent (half+padding))).length
      ((slabEmbedding half padding).polynomial (characterPolynomial (correctedSlabPlaquettePolynomial (extent half) face).scalar spin))
      (characterPolynomial (correctedSlabPlaquettePolynomial (extent (half+padding)) (shiftFace padding padding face)).scalar spin) :=
  (slabEmbedding half padding).character_of_quaternion
    (p := correctedSlabPlaquettePolynomial (extent half) face)
    (q := correctedSlabPlaquettePolynomial (extent (half+padding)) (shiftFace padding padding face))
    (plaquette_pin (half := half) (padding := padding) hf) spin

/-- Arbitrary supported polynomial insertions, before any action is inserted. -/
theorem haar_embedding (half padding : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (links (extent half)).length p) :
    Q'.eqv (quaternionHaar (links (extent (half+padding))).length ((slabEmbedding half padding).polynomial p))
      (quaternionHaar (links (extent half)).length p) := (slabEmbedding half padding).haar p hp

end YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.targetBlock
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.targetBlock_lt
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.targetBlock_injective
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.slabEmbedding
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.slabEmbedding_block
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.link_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.shiftOriented
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.orientedBoundary_shift
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.oriented_link_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.plaquette_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.character_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding.haar_embedding
