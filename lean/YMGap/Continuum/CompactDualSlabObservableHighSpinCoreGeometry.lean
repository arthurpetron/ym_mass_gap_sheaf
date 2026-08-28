/-
# Local/far geometry of the observable-rooted finite core

Every certificate in the reserve-failing carrier contains a selected strand
copy.  Selection means membership in the same rooted graph component as the
fixed observable.  Projecting that component to plaquettes therefore puts the
anchor in its genuine connected geometric support, and forces

```text
root-to-anchor L-infinity distance + 1 <= component peel size.
```

Filtering the certificate list at any radius gives an exact mass split.  The
near branch has a bounded-distance anchor with slot below the core threshold;
the far branch carries a component-size floor of `radius + 2`.  These are the
two concrete analytic frontiers: local finite-core coercivity and a long
low-spin connected tail.

Constructive contract: projection of explicit selected copies, Boolean list
partition, and finite rational summation only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
import YMGap.Continuum.CompactDualSlabObservableConnectedComponent

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableConnectedComponent
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A decoded core anchor lies in the rooted component -/

/-- The selected anchor copy is a literal member of the observable-rooted
strand component. -/
theorem slabObservableHighSpinCoreCertificate_anchor_mem_component
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    certificate.anchor.copy ∈
      (certificate.sourceEntry.seed D faceId hface).component := by
  have hselected := certificate.anchor_selected
  unfold SlabFaceStrandSeed.selected at hselected
  exact of_decide_eq_true hselected

/-- The anchor plaquette belongs to the genuine connected plaquette support
of the rooted strand component. -/
theorem slabObservableHighSpinCoreCertificate_anchorPlaquette_mem_support
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    slabPlaquetteAt D.extent certificate.anchor.copy.faceId ∈
      componentPlaquetteSupport
        (certificate.sourceEntry.seed D faceId hface) := by
  apply (mem_componentPlaquetteSupport_iff
    (certificate.sourceEntry.seed D faceId hface) _).mpr
  exact ⟨certificate.anchor.copy,
    slabObservableHighSpinCoreCertificate_anchor_mem_component certificate,
    rfl⟩

/-- Geometric distance from the fixed observable plaquette to the decoded
core-anchor plaquette. -/
def slabObservableHighSpinCoreCertificateAnchorDistance
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat :=
  linfDist (slabPlaquetteAt D.extent faceId)
    (slabPlaquetteAt D.extent certificate.anchor.copy.faceId)

/-- The rooted component size pays the full distance to its decoded core
anchor. -/
theorem slabObservableHighSpinCoreCertificateAnchorDistance_add_one_le_peel
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    slabObservableHighSpinCoreCertificateAnchorDistance certificate + 1 <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces
        (certificate.sourceEntry.seed D faceId hface)).length := by
  unfold slabObservableHighSpinCoreCertificateAnchorDistance
  have hfloor :=
    SlabFusionWitnessFaceStrandSeed.linfDist_add_one_le_peelFaces
      (certificate.sourceEntry.seed D faceId hface)
      (slabPlaquetteAt D.extent certificate.anchor.copy.faceId)
      (slabObservableHighSpinCoreCertificate_anchorPlaquette_mem_support
        certificate)
  simpa only [SlabObservablePositiveSourceEntry.seed] using hfloor

/-! ## 2. The certificate presentation preserves the exact core weight -/

/-- Weight of one decoded core certificate, inherited from its literal source
pair. -/
def slabObservableHighSpinCoreCertificateWeight
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Q' :=
  slabExpandedFineSourceWeight D certificate.sourceEntry.1

/-- Decoding anchors neither loses nor duplicates finite-core mass. -/
theorem slabObservableHighSpinCoreCertificates_weight_eq
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinCoreCertificates
          D faceId hface threshold) =
      slabObservableHighSpinCoreSourceWeight
        D faceId hface threshold := by
  unfold slabObservableHighSpinCoreCertificateWeight
    slabObservableHighSpinCoreSourceWeight
    slabObservableHighSpinCoreSources
  rw [← listQSum_map
    (fun entry : SlabObservablePositiveSourceEntry D faceId =>
      slabExpandedFineSourceWeight D entry.1)
    (fun certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold => certificate.sourceEntry)]
  rw [slabObservableHighSpinCoreCertificates_sourceEntries_eq]
  rw [listQSum_map]

/-! ## 3. Exact near/far split at an arbitrary radius -/

/-- Core certificates with anchor distance at most `radius`. -/
def slabObservableHighSpinNearCoreCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinCoreCertificates
      D faceId hface threshold).filter fun certificate =>
    decide
      (slabObservableHighSpinCoreCertificateAnchorDistance certificate <=
        radius)

/-- Core certificates with anchor distance strictly greater than `radius`. -/
def slabObservableHighSpinFarCoreCertificates
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  (slabObservableHighSpinCoreCertificates
      D faceId hface threshold).filter fun certificate =>
    !(decide
      (slabObservableHighSpinCoreCertificateAnchorDistance certificate <=
        radius))

/-- The complete core mass is exactly the near mass plus the far mass. -/
theorem slabObservableHighSpinCoreSourceWeight_split_near_far
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    slabObservableHighSpinCoreSourceWeight D faceId hface threshold ≈
      listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinNearCoreCertificates
            D faceId hface threshold radius) +
        listQSum slabObservableHighSpinCoreCertificateWeight
          (slabObservableHighSpinFarCoreCertificates
            D faceId hface threshold radius) := by
  rw [← slabObservableHighSpinCoreCertificates_weight_eq
    D faceId hface threshold]
  unfold slabObservableHighSpinNearCoreCertificates
    slabObservableHighSpinFarCoreCertificates
  exact listQSum_filter_partition
    slabObservableHighSpinCoreCertificateWeight
    (fun certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold =>
      decide
        (slabObservableHighSpinCoreCertificateAnchorDistance certificate <=
          radius))
    (slabObservableHighSpinCoreCertificates
      D faceId hface threshold)

/-- A near certificate exposes both bounded anchor distance and the existing
bounded core slot. -/
theorem slabObservableHighSpinNearCoreCertificate_bounds
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinNearCoreCertificates
        D faceId hface threshold radius) :
    slabObservableHighSpinCoreCertificateAnchorDistance certificate <=
        radius ∧
      certificate.anchor.copy.slot.val < threshold := by
  constructor
  · exact of_decide_eq_true (List.mem_filter.mp hcertificate).2
  · exact certificate.anchor_slot_lt

/-- A far certificate carries a strict distance lower bound. -/
theorem slabObservableHighSpinFarCoreCertificate_distance_gt
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreCertificates
        D faceId hface threshold radius) :
    radius <
      slabObservableHighSpinCoreCertificateAnchorDistance certificate := by
  have hfar := (List.mem_filter.mp hcertificate).2
  by_cases hnear :
      slabObservableHighSpinCoreCertificateAnchorDistance certificate <=
        radius
  · simp [hnear] at hfar
  · omega

/-- The far branch is a long-component problem: every member has at least
`radius + 2` selected physical copies in its rooted component. -/
theorem slabObservableHighSpinFarCoreCertificate_peel_floor
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (certificate : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hcertificate : certificate ∈
      slabObservableHighSpinFarCoreCertificates
        D faceId hface threshold radius) :
    radius + 2 <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces
        (certificate.sourceEntry.seed D faceId hface)).length := by
  have hdistance :=
    slabObservableHighSpinFarCoreCertificate_distance_gt
      certificate hcertificate
  have hpeel :=
    slabObservableHighSpinCoreCertificateAnchorDistance_add_one_le_peel
      certificate
  omega

#print axioms slabObservableHighSpinCoreCertificate_anchor_mem_component
#print axioms slabObservableHighSpinCoreCertificate_anchorPlaquette_mem_support
#print axioms slabObservableHighSpinCoreCertificateAnchorDistance
#print axioms slabObservableHighSpinCoreCertificateAnchorDistance_add_one_le_peel
#print axioms slabObservableHighSpinCoreCertificateWeight
#print axioms slabObservableHighSpinCoreCertificates_weight_eq
#print axioms slabObservableHighSpinNearCoreCertificates
#print axioms slabObservableHighSpinFarCoreCertificates
#print axioms slabObservableHighSpinCoreSourceWeight_split_near_far
#print axioms slabObservableHighSpinNearCoreCertificate_bounds
#print axioms slabObservableHighSpinFarCoreCertificate_distance_gt
#print axioms slabObservableHighSpinFarCoreCertificate_peel_floor

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
