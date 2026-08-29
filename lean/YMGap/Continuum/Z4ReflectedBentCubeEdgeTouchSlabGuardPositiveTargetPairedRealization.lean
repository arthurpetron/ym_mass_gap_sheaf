/-
# Paired observable realization of the guarded reflected target

Instantiate the symbolic paired-realization compiler at the guarded reflected
channel.  The source-side target is the structurally assembled positive
column, while the observable-side anchor is the literal guarded four-cell
source.  The resulting certificate identifies both observable realized
assignments with the already classified left and right target assignments.

Constructive contract: equality transport and the existing symbolic compiler
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabTransportedPairedRealizationCertificate
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingCanonicalTargetProduct
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice

/-! ## 1. Concrete instantiation of the symbolic paired compiler -/

opaque reflectedBentGuardGraftPairedRealizationCertificate
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftObservableRecouplingSource
      D hcutoff hextent state
    let anchor : SlabPhysicalPairCanonicalAnchor 1 5
        source.1.1.1.1 source.1.2.1.1 := by
      simpa only [hcutoff, hextent] using source.anchor
    TransportedPairedRealizationCertificate 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1
      (boundaryCompleteSlabLinks 5).attach
      (by
        simpa only [hextent] using
          reflectedBentGuardGraftObservableRecouplingPackages_eq
            D hcutoff hextent state)
      (reflectedBentGuardGraftTargetMembershipPackageFrom
        D hcutoff hextent state
          (boundaryCompleteSlabLinks 5).attach)
      anchor
      (reflectedBentGuardGraftRealizedLeftAssignment
        D hcutoff hextent state)
      (reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state) := by
  let source := reflectedBentGuardGraftObservableRecouplingSource
    D hcutoff hextent state
  let anchor : SlabPhysicalPairCanonicalAnchor 1 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [hcutoff, hextent] using source.anchor
  apply transportLinkedPairedRealizationCertificate
    (K := 1) (extent := 5)
    (leftPhysical₁ := reflectedBentGuardGraftLeftPhysical
      D hextent state)
    (rightPhysical₁ := reflectedBentGuardGraftRightPhysical
      D hextent state)
    (leftPhysical₂ := source.1.1.1.1)
    (rightPhysical₂ := source.1.2.1.1)
    (reflectedBentGuardGraftObservableRecouplingSource_leftPhysical
      D hcutoff hextent state).symm
    (reflectedBentGuardGraftObservableRecouplingSource_rightPhysical
      D hcutoff hextent state).symm
    (boundaryCompleteSlabLinks 5).attach rfl
    (by
      simpa only [source, hextent] using
        reflectedBentGuardGraftObservableRecouplingPackages_eq
          D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFrom
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_five
      D hcutoff hextent state)
    anchor
    (reflectedBentGuardGraftRealizedLeftAssignmentFrom
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentFrom
      D hcutoff hextent state)
  intro links
  exact reflectedBentGuardGraftRealizedAssignmentsFrom_eq_canonical
    D hcutoff hextent state links

/-- The same paired realization over the literal unsealed observable source.
This interface is definitionally lighter for downstream success certificates;
the source pair and all mathematical data are unchanged. -/
opaque reflectedBentGuardGraftRawPairedRealizationCertificate
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftRawObservableRecouplingSource
      D hcutoff hextent state
    let anchor : SlabPhysicalPairCanonicalAnchor 1 5
        source.1.1.1.1 source.1.2.1.1 := by
      simpa only [hcutoff, hextent] using source.anchor
    TransportedPairedRealizationCertificate 1 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1
      (boundaryCompleteSlabLinks 5).attach
      (by
        simpa only [hcutoff, hextent] using
          reflectedBentGuardGraftRawObservableRecouplingPackages_eq
            D hcutoff hextent state)
      (reflectedBentGuardGraftTargetMembershipPackageFrom
        D hcutoff hextent state
          (boundaryCompleteSlabLinks 5).attach)
      anchor
      (reflectedBentGuardGraftRealizedLeftAssignment
        D hcutoff hextent state)
      (reflectedBentGuardGraftRealizedRightAssignment
        D hcutoff hextent state) := by
  let source := reflectedBentGuardGraftRawObservableRecouplingSource
    D hcutoff hextent state
  let anchor : SlabPhysicalPairCanonicalAnchor 1 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [hcutoff, hextent] using source.anchor
  apply transportLinkedPairedRealizationCertificate
    (K := 1) (extent := 5)
    (leftPhysical₁ := reflectedBentGuardGraftLeftPhysical
      D hextent state)
    (rightPhysical₁ := reflectedBentGuardGraftRightPhysical
      D hextent state)
    (leftPhysical₂ := source.1.1.1.1)
    (rightPhysical₂ := source.1.2.1.1)
    (reflectedBentGuardGraftLeftPositiveEntry_physical
      D hcutoff hextent state).symm
    (reflectedBentGuardGraftRightExpandedEntry_physical
      D hcutoff hextent state).symm
    (boundaryCompleteSlabLinks 5).attach rfl
    (by
      simpa only [source, hcutoff, hextent] using
        reflectedBentGuardGraftRawObservableRecouplingPackages_eq
          D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFrom
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_bounded_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_five
      D hcutoff hextent state)
    anchor
    (reflectedBentGuardGraftRealizedLeftAssignmentFrom
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentFrom
      D hcutoff hextent state)
  intro links
  exact reflectedBentGuardGraftRealizedAssignmentsFrom_eq_canonical
    D hcutoff hextent state links

#print axioms reflectedBentGuardGraftPairedRealizationCertificate
#print axioms reflectedBentGuardGraftRawPairedRealizationCertificate

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealization
