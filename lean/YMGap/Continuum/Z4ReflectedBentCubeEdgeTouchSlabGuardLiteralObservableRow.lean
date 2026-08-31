/-
# The guarded cylinder on the literal observable recoupling row

The abstract row presentation avoids normalizing the whole extent-five
dependent product.  The opaque observable source package already contains the
semantic equality needed to instantiate it: equality of the observable pair
with the guarded graft gives equality of both physical labellings and both
auxiliary assignments.  Exact production-source transport then identifies the
two rows by equality elimination alone.

Constructive contract: equality transport and proof irrelevance only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceTransport
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoice
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableChoiceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence

private abbrev LiteralObservableSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
    D hcutoff hextent state

/-- Name the observable production row once so its membership proofs and
nested source projections are not repeated in downstream types. -/
def literalObservableProductionSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabPhysicalPairRecouplingSourceAssignment D.extent
      (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.1.1.1
      (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.2.1.1 :=
  slabPhysicalPairRecouplingProductionSource
    D.cutoff D.extent
    (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.1.1.1
    (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.2.1.1
    (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.1.1.2
    (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.2.1.2
    (LiteralObservableSourceAtCutoff
      D hcutoff hextent state).1.1.assignment_mem
    (slabExpandedFineSourceEntryAssignment_mem
      (LiteralObservableSourceAtCutoff D hcutoff hextent state).1.2)

/-- The literal observable SU(2) row together with its exact package-list and
source-row identifications.  These two public equalities let downstream
target transport use the canonical observable kernel without unfolding the
extent-five heterogeneous product. -/
structure ReflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type 2 where
  row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
  packages_eq : row.packages =
    slabPhysicalPairRecouplingPackages D.extent
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state).1.1.1.1
      (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state).1.2.1.1
  source_eq :
    transportFiniteBistochasticSourceAssignment packages_eq.symm
        (literalObservableProductionSourceAtCutoff
          D hcutoff hextent state) =
      row.source

/-- Opaque construction of the proof-carrying literal row package. -/
opaque reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
      D hcutoff hextent state := by
  let packages := slabPhysicalPairRecouplingPackages D.extent
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.1
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.1
  let source := literalObservableProductionSourceAtCutoff
    D hcutoff hextent state
  let row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach := by
    refine
      { packages := packages
        packages_eq :=
          reflectedBentGuardGraftObservableRecouplingPackagesAtCutoff_eq
            D hcutoff hextent state
        source := source
        source_eq := ?_ }
    simpa only [source, literalObservableProductionSourceAtCutoff,
        LiteralObservableSourceAtCutoff,
        slabPhysicalPairRecouplingProductionSource] using
      (slabPhysicalPairRecouplingProductionSource_transport_extent
        D.cutoff D.extent 5 hextent
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftPhysical
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightPhysical
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.1.2
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.2.1.2
        (reflectedBentGuardGraftLeftAssignment D hextent state)
        (reflectedBentGuardGraftRightAssignment D hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_leftAssignment
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff_rightAssignment
          D hcutoff hextent state)
        (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
          D hcutoff hextent state).1.1.assignment_mem
        (slabExpandedFineSourceEntryAssignment_mem
          (reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
            D hcutoff hextent state).1.2)
        (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
          D hcutoff hextent state)
        (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
          D hcutoff hextent state))
  refine { row := row, packages_eq := rfl, source_eq := ?_ }
  rfl

abbrev reflectedBentGuardGraftLiteralObservableRowAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
    D hcutoff hextent state).row

#print axioms reflectedBentGuardGraftLiteralObservableRowPackageAtCutoff
#print axioms reflectedBentGuardGraftLiteralObservableRowAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
