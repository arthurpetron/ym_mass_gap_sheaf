/-
# A global finite-volume ceiling for the cutoff-one canonical gas

Delete, one at a time, every canonical-polymer layer pinned to a physical
face.  The previously proved half bound says that each deletion costs at
most a factor two.  After all physical faces have been deleted no canonical
polymer survives: every canonical polymer is nonempty and is a sub-support
of the physical face list.  Thus the remaining partition is exactly one.

This is deliberately a symbolic finite-volume estimate.  It does not
enumerate any of the exponentially many families.
-/

import YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor

namespace YMGap.Continuum.Z4CanonicalPolymerGlobalPartitionCeiling

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Deleting the layer pinned to every physical face leaves no canonical
polymer. -/
theorem deleteAllPhysicalFaceLayers_eq_nil (n : Nat) :
    deleteMarkedLayers
        (fun face polymer => canonicalContainsFaceB face polymer)
        (physicalFaceEdges n) (canonicalSurfacePolymers n) = [] := by
  cases hdeleted : deleteMarkedLayers
      (fun face polymer => canonicalContainsFaceB face polymer)
      (physicalFaceEdges n) (canonicalSurfacePolymers n) with
  | nil => rfl
  | cons head tail =>
      have hsurvives : head ∈ deleteMarkedLayers
          (fun face polymer => canonicalContainsFaceB face polymer)
          (physicalFaceEdges n) (canonicalSurfacePolymers n) := by
        rw [hdeleted]
        exact List.mem_cons_self
      have hcanonical : head ∈ canonicalSurfacePolymers n :=
        mem_deleteMarkedLayers_source
          (fun face polymer => canonicalContainsFaceB face polymer)
          (physicalFaceEdges n) (canonicalSurfacePolymers n) head hsurvives
      obtain ⟨face, hface⟩ :=
        canonicalSurfacePolymers_allNonempty n head hcanonical
      have hfacePhysical : face ∈ physicalFaceEdges n :=
        mem_of_mem_sublists (physicalFaceEdges n) head
          (canonicalSurfacePolymer_mem_faceSupports hcanonical) face hface
      have hmarkFalse : canonicalContainsFaceB face head = false :=
        mem_deleteMarkedLayers_mark_false
          (fun pinned polymer => canonicalContainsFaceB pinned polymer)
          (physicalFaceEdges n) (canonicalSurfacePolymers n) head
          hsurvives face hfacePhysical
      have hmarkTrue : canonicalContainsFaceB face head = true := by
        unfold canonicalContainsFaceB
        exact decide_eq_true hface
      rw [hmarkTrue] at hmarkFalse
      cases hmarkFalse

/-- At every nonnegative coupling below the proved anchor, the full
cutoff-one canonical partition is at most one factor two per physical face. -/
theorem canonicalPolymerPartition_le_two_pow_physicalFaces
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (n : Nat) :
    canonicalPolymerPartition coupling n (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^ (physicalFaceEdges n).length := by
  have hdelete := partition_le_two_pow_mul_deleteMarkedLayers
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity coupling n)
    (canonicalSurfaceActivity_nonnegative hcoupling n)
    (fun face polymer => canonicalContainsFaceB face polymer)
    (physicalFaceEdges n) (canonicalSurfacePolymers n)
    (fun face _ => couplingPinnedLayerActivity_le_half
      hcoupling hle n face)
  unfold canonicalPolymerPartition
  rw [deleteAllPhysicalFaceLayers_eq_nil, partition_nil] at hdelete
  exact Q'.le_trans' _ _ _ hdelete
    (Q'.le_of_eqv (Q'.mul_one_eqv
      ((Q'.ofNat 2) ^ (physicalFaceEdges n).length)))

/-- The exponent in the global ceiling is the exact number `6 n^4` of
physical plaquettes. -/
theorem physicalFaceEdges_length (n : Nat) :
    (physicalFaceEdges n).length = (n * n * n * n) * 6 := by
  unfold physicalFaceEdges plaquetteEdgeCount
  rw [List.length_range, boxPlaquettes_length]

/-- The concrete three-cube comparison box has exactly 7776 physical face
labels. -/
theorem physicalFaceEdges_six_length :
    (physicalFaceEdges 6).length = 7776 := by
  rw [physicalFaceEdges_length]

theorem canonicalPolymerPartition_six_le_two_pow_7776
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    canonicalPolymerPartition coupling 6 (canonicalSurfacePolymers 6) ≤
      (Q'.ofNat 2) ^ 7776 := by
  simpa only [physicalFaceEdges_six_length] using
    canonicalPolymerPartition_le_two_pow_physicalFaces
      hcoupling hle 6

#print axioms deleteAllPhysicalFaceLayers_eq_nil
#print axioms canonicalPolymerPartition_le_two_pow_physicalFaces
#print axioms physicalFaceEdges_length
#print axioms physicalFaceEdges_six_length
#print axioms canonicalPolymerPartition_six_le_two_pow_7776

end YMGap.Continuum.Z4CanonicalPolymerGlobalPartitionCeiling
