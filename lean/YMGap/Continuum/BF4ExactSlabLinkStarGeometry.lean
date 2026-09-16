/-
# The actual six-face link star and its independent heat complement

Partition the original physical face identifiers by incidence with a supplied
literal link. There are at most six incident faces in four dimensions. The
complete complementary heat product has degree zero in that link's actual
quaternion block; all other shared-link interactions remain present.

The product factorization is a polynomial identity, not a factorization of
the full Haar integral. These finite geometry facts supply the independence
premise for one-link conditional integration, not spatial decay or a gap.
-/

import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.BF4ExactSlabSelectedFaceFold
import YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
import YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
import YMGap.Continuum.SU2QuaternionSolidZonalCharacter

namespace YMGap.Continuum.BF4ExactSlabLinkStarGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold (blockDegree_reindex)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- Exactly the original physical plaquettes containing the selected link. -/
def incidentIds (extent : Nat) (link : Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter
    (fun id => decide (link ∈ edgesOf (slabPlaquetteAt extent id)))

/-- Every original physical plaquette not containing the selected link. -/
def complementIds (extent : Nat) (link : Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter
    (fun id => !(decide (link ∈ edgesOf (slabPlaquetteAt extent id))))

theorem mem_incidentIds_iff (extent : Nat) (link : Z4Link) (id : Nat) :
    id ∈ incidentIds extent link ↔
      id ∈ slabPhysicalFaceEdges extent ∧ link ∈ edgesOf (slabPlaquetteAt extent id) := by
  simp only [incidentIds, List.mem_filter, decide_eq_true_eq]

theorem mem_complementIds_iff (extent : Nat) (link : Z4Link) (id : Nat) :
    id ∈ complementIds extent link ↔
      id ∈ slabPhysicalFaceEdges extent ∧ link ∉ edgesOf (slabPlaquetteAt extent id) := by
  simp only [complementIds, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]

theorem incidentIds_physical {extent : Nat} {link : Z4Link} {id : Nat}
    (hi : id ∈ incidentIds extent link) : id ∈ slabPhysicalFaceEdges extent :=
  ((mem_incidentIds_iff extent link id).mp hi).1

theorem complementIds_physical {extent : Nat} {link : Z4Link} {id : Nat}
    (hi : id ∈ complementIds extent link) : id ∈ slabPhysicalFaceEdges extent :=
  ((mem_complementIds_iff extent link id).mp hi).1

theorem face_partition (extent : Nat) (link : Z4Link) :
    (incidentIds extent link ++ complementIds extent link).Perm (slabPhysicalFaceEdges extent) :=
  List.filter_append_perm _ _

theorem incidentIds_nodup (extent : Nat) (link : Z4Link) :
    (incidentIds extent link).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup _)

theorem complementIds_nodup (extent : Nat) (link : Z4Link) :
    (complementIds extent link).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup _)

/-- The old six-plaquette enumeration covers every member of this actual star. -/
theorem incidentIds_length_le_six (extent : Nat) (link : Z4Link) :
    (incidentIds extent link).length ≤ 6 := by
  have hm := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) _
    (incidentIds_nodup extent link)
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical
      (incidentIds_physical ha) (incidentIds_physical hb) he)
  have h := CayleyPruferInjection.nodup_subset_length_le
    ((incidentIds extent link).map (slabPlaquetteAt extent)) (edgePlaqs link.1 link.2) hm (by
      intro face hf
      obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hf
      exact edge_complete _ link.1 link.2 ((mem_incidentIds_iff extent link id).mp hi).2)
  simpa only [List.length_map, edgePlaqs_length] using h

theorem link_not_mem_complement (extent : Nat) (link : Z4Link) :
    link ∉ faceLinks extent (complementIds extent link) := by
  intro h
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp h
  exact ((mem_complementIds_iff extent link id).mp hi).2 he

def incidentHeat (w : Q') (K extent : Nat) (link : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (incidentIds extent link)

def complementHeat (w : Q') (K extent : Nat) (link : Z4Link) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (complementIds extent link)

theorem incidentHeat_supported (w : Q') (K extent : Nat) (link : Z4Link) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (incidentHeat w K extent link) :=
  heatProduct_supported w K extent _

theorem complementHeat_supported (w : Q') (K extent : Nat) (link : Z4Link) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length (complementHeat w K extent link) :=
  heatProduct_supported w K extent _

/-- Split the literal full action without deleting any factor or shared link. -/
theorem heatProduct_partition (w : Q') (K extent : Nat) (link : Z4Link) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent))
      (polyMul (incidentHeat w K extent link) (complementHeat w K extent link)) :=
  (polynomialProduct_perm _ (face_partition extent link).symm).trans (polynomialProduct_append _ _ _)

/-- Independence is proved at the index of the actual physical link, not
assumed from a picture of disjoint faces. Other links may still be shared. -/
theorem complementHeat_degree_zero (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0
      (complementHeat w K extent link) := by
  have hlocal : LinkLocal extent (faceLinks extent (complementIds extent link))
      (complementHeat w K extent link) := heatProduct_local w K extent (complementIds extent link)
  exact BF4ExactSlabSingleLinkCharacterSelection.linkLocal_degree_zero hlocal link hl
    (link_not_mem_complement extent link)

/-- The selected physical link is moved to block zero by the old explicit
Haar-preserving transposition; no new observable carrier is introduced. -/
def linkHeadSwap (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockInvolution (boundaryCompleteSlabLinks extent).length :=
  headSwapBlockInvolution _ _ (List.idxOf_lt_length_of_mem hl)

theorem complementHeat_headIndependent (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    HeadQuaternionIndependent
      (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (complementHeat w K extent link)) := by
  change HasQuaternionBlockDegree 0 0 _
  have hlt := List.idxOf_lt_length_of_mem hl
  exact blockDegree_reindex (linkHeadSwap extent link hl) (by omega)
    (headSwapBlockInvolution_map_zero _ _ hlt) (complementHeat_degree_zero w K extent link hl)

/-- Exact integration of an arbitrary supported insertion against the actual
complement. In the full action the insertion includes the incident factors.
Without those factors this is the free-link reference, not the original
conditioned law or its marginal. No pointwise conditional bound is asserted. -/
theorem complementHeat_fubini (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length
      (polyMul p (complementHeat w K extent link)) ≈
    quaternionHaar ((boundaryCompleteSlabLinks extent).length-1)
      (polyMul
        (partialHaarHead (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p))
        (dropHeadPolynomial
          (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (complementHeat w K extent link)))) := by
  have hlt := List.idxOf_lt_length_of_mem hl
  have hn : (boundaryCompleteSlabLinks extent).length =
      ((boundaryCompleteSlabLinks extent).length-1)+1 := by omega
  have hs := quaternionHaar_reindex (linkHeadSwap extent link hl)
    (polyMul p (complementHeat w K extent link))
    (supported_polyMul hp (complementHeat_supported w K extent link))
  rw [reindexQuaternionPolynomial_mul] at hs
  have hf := quaternionHaar_polyMul_headIndependent ((boundaryCompleteSlabLinks extent).length-1)
    (reindexQuaternionPolynomial (linkHeadSwap extent link hl) p)
    (reindexQuaternionPolynomial (linkHeadSwap extent link hl) (complementHeat w K extent link))
    (complementHeat_headIndependent w K extent link hl)
  rw [← hn] at hf
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hs) hf

end YMGap.Continuum.BF4ExactSlabLinkStarGeometry

#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentIds
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementIds
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.mem_incidentIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.mem_complementIds_iff
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.face_partition
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentIds_length_le_six
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.link_not_mem_complement
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentHeat
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementHeat
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.incidentHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.heatProduct_partition
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementHeat_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.linkHeadSwap
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementHeat_headIndependent
#print axioms YMGap.Continuum.BF4ExactSlabLinkStarGeometry.complementHeat_fubini
