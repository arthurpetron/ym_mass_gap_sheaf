/-
# Paired observable realization of the guarded target at every cutoff

Instantiate the symbolic paired-realization compiler at the ambient-cutoff
guarded choice.  The resulting certificate identifies both observable
realized assignments with the assignments whose projected graph has already
been classified.

Constructive contract: equality transport and the existing symbolic compiler
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealizationCutoffPersistence

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
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetRealizationCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabObservableChoice

opaque reflectedBentGuardGraftPairedRealizationCertificateAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
      D hcutoff hextent state
    let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
        source.1.1.1.1 source.1.2.1.1 := by
      simpa only [hextent] using source.anchor
    TransportedPairedRealizationCertificate D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1
      (boundaryCompleteSlabLinks 5).attach
      (by
        simpa only [hextent] using
          reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
            D hcutoff hextent state)
      (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
        D hcutoff hextent state
          (boundaryCompleteSlabLinks 5).attach)
      anchor
      (reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
        D hcutoff hextent state) := by
  let source := reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    D hcutoff hextent state
  let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [hextent] using source.anchor
  apply transportLinkedPairedRealizationCertificate
    (K := D.cutoff) (extent := 5)
    (leftPhysical₁ := reflectedBentGuardGraftLeftPhysical
      D hextent state)
    (rightPhysical₁ := reflectedBentGuardGraftRightPhysical
      D hextent state)
    (leftPhysical₂ := source.1.1.1.1)
    (rightPhysical₂ := source.1.2.1.1)
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
      D hcutoff hextent state).symm
    (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
      D hcutoff hextent state).symm
    (boundaryCompleteSlabLinks 5).attach rfl
    (by
      simpa only [source, hextent] using
        reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
          D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    anchor
    (reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
      D hcutoff hextent state)
  intro links
  exact reflectedBentGuardGraftRealizedAssignmentsFromAtCutoff_eq_canonical
    D hcutoff hextent state links

/-! ## The definitionally lighter literal source -/

opaque reflectedBentGuardGraftRawPairedRealizationCertificateAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
      D hcutoff hextent state
    let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
        source.1.1.1.1 source.1.2.1.1 := by
      simpa only [hextent] using source.anchor
    TransportedPairedRealizationCertificate D.cutoff 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      source.1.1.1.1 source.1.2.1.1
      (boundaryCompleteSlabLinks 5).attach
      (by
        simpa only [hextent] using
          reflectedBentGuardGraftRawObservableRecouplingPackagesAtCutoff_eq
            D hcutoff hextent state)
      (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
        D hcutoff hextent state
          (boundaryCompleteSlabLinks 5).attach)
      anchor
      (reflectedBentGuardGraftRealizedLeftAssignmentAtCutoff
        D hcutoff hextent state)
      (reflectedBentGuardGraftRealizedRightAssignmentAtCutoff
        D hcutoff hextent state) := by
  let source := reflectedBentGuardGraftRawObservableRecouplingSourceAtCutoff
    D hcutoff hextent state
  let anchor : SlabPhysicalPairCanonicalAnchor D.cutoff 5
      source.1.1.1.1 source.1.2.1.1 := by
    simpa only [hextent] using source.anchor
  apply transportLinkedPairedRealizationCertificate
    (K := D.cutoff) (extent := 5)
    (leftPhysical₁ := reflectedBentGuardGraftLeftPhysical
      D hextent state)
    (rightPhysical₁ := reflectedBentGuardGraftRightPhysical
      D hextent state)
    (leftPhysical₂ := source.1.1.1.1)
    (rightPhysical₂ := source.1.2.1.1)
    (reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical
      D hcutoff hextent state).symm
    (reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical
      D hcutoff hextent state).symm
    (boundaryCompleteSlabLinks 5).attach rfl
    (by
      simpa only [source, hextent] using
        reflectedBentGuardGraftRawObservableRecouplingPackagesAtCutoff_eq
          D hcutoff hextent state)
    (reflectedBentGuardGraftTargetMembershipPackageFromAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftLeftPhysical_bounded_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightPhysical_bounded_at_cutoff
      D hextent state)
    anchor
    (reflectedBentGuardGraftRealizedLeftAssignmentFromAtCutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRealizedRightAssignmentFromAtCutoff
      D hcutoff hextent state)
  intro links
  exact reflectedBentGuardGraftRealizedAssignmentsFromAtCutoff_eq_canonical
    D hcutoff hextent state links

#print axioms reflectedBentGuardGraftPairedRealizationCertificateAtCutoff
#print axioms reflectedBentGuardGraftRawPairedRealizationCertificateAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetPairedRealizationCutoffPersistence
