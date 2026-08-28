/-
# The exact observable-rooted finite-core complement

The localized exterior contraction controls precisely those positive
observable-rooted sources whose canonical rooted strand component passes the
high-spin reserve check.  This module constructs the literal complementary
carrier.  Every complementary source keeps the failed Boolean equation and
the explicit selected finite-core anchor decoded from that failure.

The two Boolean filters partition the original positive carrier exactly, both
before and after forgetting attachment proofs.  At arbitrary rational
`0 < w < 1`, the previous exterior contraction therefore reduces the complete
positive observable mass to

```text
positive mass <= (8/17) * physical partition + finite-core mass.
```

This is a reduction, not a coercive estimate on the finite-core term.

Constructive contract: Boolean complementation, finite attachment, and the
existing explicit reserve-failure decoder only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem split_left_le_budget_add_right
    (total exterior core budget : Q')
    (hsplit : total ≈ exterior + core)
    (hexterior : exterior <= budget) :
    total <= budget + core :=
  Q'.le_trans' total (exterior + core) (budget + core)
    (Q'.le_of_eqv hsplit)
    (Q'.add_le_add_right exterior budget core hexterior)

/-! ## 1. Literal complementary filter -/

/-- The positive observable-rooted entries whose reserve-paid test is false.
This is definitionally the Boolean complement of the exterior filter. -/
def slabObservableHighSpinCoreEntries
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  (slabObservablePositiveSourceEntries D faceId).filter fun entry =>
    !(decide
      (SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold = true))

/-- The underlying expanded source pairs in the finite-core branch. -/
def slabObservableHighSpinCoreSources
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabObservableHighSpinCoreEntries D faceId hface threshold).map
    Subtype.val

/-- Total weight of the positive observable-rooted source carrier. -/
def slabObservablePositiveSourceWeight
    (D : SlabPhysicalData) (faceId : Nat) : Q' :=
  listQSum (slabExpandedFineSourceWeight D)
    (slabObservablePositiveExpandedSources D faceId)

/-- Total weight of the localized exterior branch. -/
def slabObservableHighSpinExteriorSourceWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) : Q' :=
  listQSum (slabExpandedFineSourceWeight D)
    (slabObservableHighSpinExteriorSources D faceId hface threshold)

/-- Total weight of the complementary finite-core branch. -/
def slabObservableHighSpinCoreSourceWeight
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) : Q' :=
  listQSum (slabExpandedFineSourceWeight D)
    (slabObservableHighSpinCoreSources D faceId hface threshold)

/-- Membership in the complementary filter computes the failed reserve
equation required by the core-anchor decoder. -/
theorem slabObservableHighSpinCoreEntry_reserve_failed
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId)
    (hentry : entry ∈
      slabObservableHighSpinCoreEntries D faceId hface threshold) :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold = false := by
  have hcomplement := (List.mem_filter.mp hentry).2
  cases hcheck :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold with
  | false => rfl
  | true => simp [hcheck] at hcomplement

/-- The core source list remains duplicate-free. -/
theorem slabObservableHighSpinCoreSources_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    (slabObservableHighSpinCoreSources
      D faceId hface threshold).Nodup := by
  unfold slabObservableHighSpinCoreSources
  apply nodup_map_of_injOn
  · unfold slabObservableHighSpinCoreEntries
    exact (attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup D faceId)).filter _
  · intro left _ right _ heq
    exact Subtype.ext heq

/-! ## 2. Carry the decoded finite-core witness as data -/

/-- One reserve-failing observable source together with the actual selected
finite-core strand copy decoded from that failure. -/
structure SlabObservableHighSpinCoreCertificate
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) : Type where
  sourceEntry : SlabObservablePositiveSourceEntry D faceId
  reserve_failed :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (sourceEntry.seed D faceId hface) threshold = false
  anchor : SlabComponentCoreAnchor
    (sourceEntry.seed D faceId hface) threshold

/-- Decode one failed reserve equation immediately to its constructive core
certificate. -/
def slabObservableHighSpinCoreCertificateOfFailure
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat)
    (entry : SlabObservablePositiveSourceEntry D faceId)
    (hfailed :
      SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold = false) :
    SlabObservableHighSpinCoreCertificate
      D faceId hface threshold :=
  { sourceEntry := entry
    reserve_failed := hfailed
    anchor :=
      SlabFusionWitnessFaceStrandSeed.coreAnchorOfReserveFailure
        (entry.seed D faceId hface) threshold hfailed }

/-- Attach membership to each literal core entry and decode its anchor. -/
def slabObservableHighSpinCoreCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinCoreEntries
      D faceId hface threshold).attach.map fun attached =>
    slabObservableHighSpinCoreCertificateOfFailure
      D faceId hface threshold attached.1
      (slabObservableHighSpinCoreEntry_reserve_failed
        attached.1 attached.2)

/-- The certificate list covers the complementary source entries exactly and
in their original order. -/
theorem slabObservableHighSpinCoreCertificates_sourceEntries_eq
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    (slabObservableHighSpinCoreCertificates
        D faceId hface threshold).map
      (fun certificate => certificate.sourceEntry) =
    slabObservableHighSpinCoreEntries D faceId hface threshold := by
  unfold slabObservableHighSpinCoreCertificates
  rw [List.map_map]
  change
    (slabObservableHighSpinCoreEntries
        D faceId hface threshold).attach.map Subtype.val =
      slabObservableHighSpinCoreEntries D faceId hface threshold
  rw [List.attach_map_subtype_val]

/-- Every decoded core anchor lies on a displayed physical face. -/
theorem SlabObservableHighSpinCoreCertificate.anchor_face_physical
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    certificate.anchor.copy.faceId ∈ slabPhysicalFaceEdges D.extent :=
  certificate.anchor.face_physical

/-- Every decoded anchor has a literal selected slot below the threshold. -/
theorem SlabObservableHighSpinCoreCertificate.anchor_slot_lt
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    certificate.anchor.copy.slot.val < threshold :=
  certificate.anchor.slot_core

/-- The decoded anchor copy is genuinely selected by the observable-rooted
component. -/
theorem SlabObservableHighSpinCoreCertificate.anchor_selected
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (certificate.sourceEntry.seed D faceId hface).selected
        certificate.anchor.copy = true :=
  certificate.anchor.selected_true

/-! ## 3. Exact exterior/core mass decomposition -/

/-- The attached positive carrier is exactly the exterior/core Boolean split
at every threshold. -/
theorem slabObservableHighSpin_entries_weight_split
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum
        (fun entry : SlabObservablePositiveSourceEntry D faceId =>
          slabExpandedFineSourceWeight D entry.1)
        (slabObservablePositiveSourceEntries D faceId) ≈
      listQSum
          (fun entry : SlabObservablePositiveSourceEntry D faceId =>
            slabExpandedFineSourceWeight D entry.1)
          (slabObservableHighSpinExteriorEntries
            D faceId hface threshold) +
        listQSum
          (fun entry : SlabObservablePositiveSourceEntry D faceId =>
            slabExpandedFineSourceWeight D entry.1)
          (slabObservableHighSpinCoreEntries
            D faceId hface threshold) := by
  unfold slabObservableHighSpinExteriorEntries
    slabObservableHighSpinCoreEntries
  exact listQSum_filter_partition
    (fun entry : SlabObservablePositiveSourceEntry D faceId =>
      slabExpandedFineSourceWeight D entry.1)
    (fun entry =>
      decide
        (SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
          (entry.seed D faceId hface) threshold = true))
    (slabObservablePositiveSourceEntries D faceId)

/-- Forgetting attachment proofs preserves the exact exterior/core split of
the literal expanded source weight. -/
theorem slabObservableHighSpin_sources_weight_split
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) ≈
      listQSum (slabExpandedFineSourceWeight D)
          (slabObservableHighSpinExteriorSources
            D faceId hface threshold) +
        listQSum (slabExpandedFineSourceWeight D)
          (slabObservableHighSpinCoreSources
            D faceId hface threshold) := by
  have hsplit := slabObservableHighSpin_entries_weight_split
    D faceId hface threshold
  unfold slabObservablePositiveSourceEntries at hsplit
  rw [listQSum_attach] at hsplit
  unfold slabObservableHighSpinExteriorSources
    slabObservableHighSpinCoreSources
  rw [listQSum_map, listQSum_map]
  exact hsplit

/-- Short named form of the exact mass decomposition. -/
theorem slabObservableHighSpin_sourceWeight_split
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    slabObservablePositiveSourceWeight D faceId ≈
      slabObservableHighSpinExteriorSourceWeight
          D faceId hface threshold +
        slabObservableHighSpinCoreSourceWeight
          D faceId hface threshold := by
  exact slabObservableHighSpin_sources_weight_split
    D faceId hface threshold

/-! ## 4. Every exterior estimate reduces the problem to finite core -/

/-- Exact reduction compiler: a bound on the localized exterior branch leaves
only the literal finite-core mass.  Supplying the preceding arbitrary-coupling
exterior theorem with `budget = (8/17) * D.physicalPartition` gives the desired
uniform reduction without duplicating any summation argument. -/
theorem slabObservablePositiveSources_weight_le_exteriorBudget_add_core
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) (budget : Q')
    (hexterior :
      slabObservableHighSpinExteriorSourceWeight
        D faceId hface threshold <= budget) :
    slabObservablePositiveSourceWeight D faceId <=
      budget + slabObservableHighSpinCoreSourceWeight
        D faceId hface threshold := by
  exact split_left_le_budget_add_right
    (slabObservablePositiveSourceWeight D faceId)
    (slabObservableHighSpinExteriorSourceWeight
      D faceId hface threshold)
    (slabObservableHighSpinCoreSourceWeight
      D faceId hface threshold)
    budget
    (slabObservableHighSpin_sourceWeight_split
      D faceId hface threshold)
    hexterior

/-- At arbitrary `0 < w < 1`, the verified localized exterior contraction
leaves precisely the moving-threshold finite-core mass as the only remainder. -/
theorem slabObservablePositiveSourceWeight_le_eightSeventeenths_add_core
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservablePositiveSourceWeight D faceId <=
      Q'.mkPos 8 17 (by decide) * D.physicalPartition +
        slabObservableHighSpinCoreSourceWeight D faceId hface
          (anchorPaidExteriorThreshold w) := by
  apply slabObservablePositiveSources_weight_le_exteriorBudget_add_core
  unfold slabObservableHighSpinExteriorSourceWeight
  exact slabObservableHighSpinExteriorSources_weight_sum_le_partition
    hw0 hw1 cutoff half D hD faceId hface

#print axioms slabObservableHighSpinCoreEntries
#print axioms slabObservableHighSpinCoreSources
#print axioms slabObservablePositiveSourceWeight
#print axioms slabObservableHighSpinExteriorSourceWeight
#print axioms slabObservableHighSpinCoreSourceWeight
#print axioms slabObservableHighSpinCoreEntry_reserve_failed
#print axioms slabObservableHighSpinCoreSources_nodup
#print axioms SlabObservableHighSpinCoreCertificate
#print axioms slabObservableHighSpinCoreCertificateOfFailure
#print axioms slabObservableHighSpinCoreCertificates
#print axioms slabObservableHighSpinCoreCertificates_sourceEntries_eq
#print axioms SlabObservableHighSpinCoreCertificate.anchor_face_physical
#print axioms SlabObservableHighSpinCoreCertificate.anchor_slot_lt
#print axioms SlabObservableHighSpinCoreCertificate.anchor_selected
#print axioms slabObservableHighSpin_entries_weight_split
#print axioms slabObservableHighSpin_sources_weight_split
#print axioms slabObservableHighSpin_sourceWeight_split
#print axioms slabObservablePositiveSources_weight_le_exteriorBudget_add_core
#print axioms slabObservablePositiveSourceWeight_le_eightSeventeenths_add_core

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
