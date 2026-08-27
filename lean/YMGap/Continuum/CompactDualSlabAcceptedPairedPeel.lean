/-
# Accepted two-replica states and one-sided component peels

The connected observable residue is initially represented by a positive
first replica and an arbitrary accepted second replica.  Iterated peeling
cannot retain positivity at the original root, so this module replaces that
asymmetric carrier by a pair of arbitrary accepted expanded sources.

Every positive physical face of either accepted replica has its canonical
slot-zero rooted strand component.  Lowering that component produces another
accepted expanded source.  On the paired carrier, a left or right peel obeys
an exact mass conservation law and strictly decreases total pair mass.

This is the closure interface needed before a canonical face search can be
iterated.

Constructive contract: explicit subtype membership and exact natural-number
mass identities only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
import YMGap.Continuum.CompactDualSlabExpandedTargetKey

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedPeel

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The closed accepted paired carrier -/

/-- Two arbitrary accepted expanded slab sources.  Unlike the original
observable carrier, neither replica is required to remain positive at the
initial root face. -/
abbrev SlabAcceptedTwoReplicaState (D : SlabPhysicalData) :=
  SlabExpandedFineSourceEntry D × SlabExpandedFineSourceEntry D

/-- Forget the initial observable-root positivity while retaining its exact
expanded-source membership witness. -/
def slabObservablePositiveSourceEntryToAccepted
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D rootFaceId) :
    SlabExpandedFineSourceEntry D :=
  ⟨entry.1, SlabObservablePositiveSourceEntry.source_mem_expanded entry⟩

/-- Embed the original asymmetric observable pair in the closed paired
carrier used by the iteration. -/
def slabObservableTwoReplicaPairToAcceptedState
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabAcceptedTwoReplicaState D :=
  (slabObservablePositiveSourceEntryToAccepted pair.1, pair.2)

/-- Total physical twice-spin mass of an accepted paired state. -/
def slabAcceptedTwoReplicaStateMass
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D) : Nat :=
  slabPhysicalLabellingMass D.extent state.1.1.1 +
    slabPhysicalLabellingMass D.extent state.2.1.1

private theorem listNatWeight_add
    {A : Type} (left right : A → Nat) :
    ∀ items : List A,
      listNatWeight (fun item => left item + right item) items =
        listNatWeight left items + listNatWeight right items
  | [] => rfl
  | head :: tail => by
      simp only [listNatWeight]
      rw [listNatWeight_add left right tail]
      omega

/-- The new paired mass is definitionally the same physical quantity used by
the preceding connected-residue mass floor. -/
theorem slabObservableTwoReplicaPairToAcceptedState_mass
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabAcceptedTwoReplicaStateMass
        (slabObservableTwoReplicaPairToAcceptedState pair) =
      slabObservableTwoReplicaPairTotalPhysicalMass D pair := by
  unfold slabObservableTwoReplicaPairToAcceptedState
    slabObservablePositiveSourceEntryToAccepted
    slabAcceptedTwoReplicaStateMass
    slabObservableTwoReplicaPairTotalPhysicalMass
    slabPhysicalLabellingMass
  exact (listNatWeight_add pair.1.1.1 pair.2.1.1
    (slabPhysicalFaceEdges D.extent)).symm

/-! ## 2. A canonical accepted peel at any positive physical face -/

theorem acceptedExpandedSourcePhysical_mem
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D) :
    entry.1.1 ∈ D.physicalLabellings :=
  (mem_slabExpandedFineSources_iff.mp entry.2).1

/-- The exact assignment-membership witness carried by an arbitrary accepted
expanded source. -/
def acceptedExpandedSourceAssignment_mem
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D) :
    entry.1.2 ∈ slabFusionWitnessAssignmentsOn
      D.cutoff D.extent entry.1.1
        (boundaryCompleteSlabLinks D.extent) :=
  (mem_slabExpandedFineSources_iff.mp entry.2).2

/-- The canonical slot-zero rooted component at an arbitrary positive face
of an accepted expanded source. -/
def acceptedExpandedSourceRootSeed
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    SlabFusionWitnessFaceStrandSeed D.cutoff D.extent entry.1.1
      (boundaryCompleteSlabLinks D.extent) entry.1.2
        (acceptedExpandedSourceAssignment_mem entry) :=
  slabObservableRootSeed D.cutoff D.extent faceId hface entry.1.1
    hpositive entry.1.2
      (acceptedExpandedSourceAssignment_mem entry)

/-- The accepted expanded source obtained by peeling the canonical rooted
component at one positive face. -/
def acceptedExpandedSourceLowerAt
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    SlabExpandedFineSourceEntry D :=
  let seed := acceptedExpandedSourceRootSeed D faceId hface entry hpositive
  ⟨(SlabFusionWitnessFaceStrandSeed.lowerPhysical seed,
      SlabFusionWitnessFaceStrandSeed.lowerAssignment seed),
    SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
      D (acceptedExpandedSourcePhysical_mem entry) seed⟩

/-- The number of physical strand copies removed by `lowerAt`. -/
def acceptedExpandedSourcePeelSizeAt
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.peelFaces
    (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)).length

/-- Exact one-replica mass conservation for the accepted lowering map. -/
theorem acceptedExpandedSourceLowerAt_mass_add_peelSize
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    slabPhysicalLabellingMass D.extent
          (acceptedExpandedSourceLowerAt
            D faceId hface entry hpositive).1.1 +
        acceptedExpandedSourcePeelSizeAt
          D faceId hface entry hpositive =
      slabPhysicalLabellingMass D.extent entry.1.1 := by
  exact SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_add_peel_length
    (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)

/-- Every accepted `lowerAt` operation strictly decreases physical mass. -/
theorem acceptedExpandedSourceLowerAt_mass_lt
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabExpandedFineSourceEntry D)
    (hpositive : 0 < entry.1.1 faceId) :
    slabPhysicalLabellingMass D.extent
        (acceptedExpandedSourceLowerAt
          D faceId hface entry hpositive).1.1 <
      slabPhysicalLabellingMass D.extent entry.1.1 := by
  exact SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_lt
    (acceptedExpandedSourceRootSeed D faceId hface entry hpositive)

/-! ## 3. Exact paired descent on either replica -/

def slabAcceptedTwoReplicaStateLowerLeftAt
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.1.1.1 faceId) :
    SlabAcceptedTwoReplicaState D :=
  (acceptedExpandedSourceLowerAt
      D faceId hface state.1 hpositive,
    state.2)

def slabAcceptedTwoReplicaStateLowerRightAt
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.2.1.1 faceId) :
    SlabAcceptedTwoReplicaState D :=
  (state.1,
    acceptedExpandedSourceLowerAt
      D faceId hface state.2 hpositive)

theorem slabAcceptedTwoReplicaStateLowerLeftAt_mass_add_peelSize
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.1.1.1 faceId) :
    slabAcceptedTwoReplicaStateMass
          (slabAcceptedTwoReplicaStateLowerLeftAt
            state faceId hface hpositive) +
        acceptedExpandedSourcePeelSizeAt
          D faceId hface state.1 hpositive =
      slabAcceptedTwoReplicaStateMass state := by
  have hmass := acceptedExpandedSourceLowerAt_mass_add_peelSize
    D faceId hface state.1 hpositive
  unfold slabAcceptedTwoReplicaStateLowerLeftAt
    slabAcceptedTwoReplicaStateMass
  change
    (slabPhysicalLabellingMass D.extent
          (acceptedExpandedSourceLowerAt
            D faceId hface state.1 hpositive).1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1) +
        acceptedExpandedSourcePeelSizeAt
          D faceId hface state.1 hpositive =
      slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1
  omega

theorem slabAcceptedTwoReplicaStateLowerRightAt_mass_add_peelSize
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.2.1.1 faceId) :
    slabAcceptedTwoReplicaStateMass
          (slabAcceptedTwoReplicaStateLowerRightAt
            state faceId hface hpositive) +
        acceptedExpandedSourcePeelSizeAt
          D faceId hface state.2 hpositive =
      slabAcceptedTwoReplicaStateMass state := by
  have hmass := acceptedExpandedSourceLowerAt_mass_add_peelSize
    D faceId hface state.2 hpositive
  unfold slabAcceptedTwoReplicaStateLowerRightAt
    slabAcceptedTwoReplicaStateMass
  change
    (slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent
          (acceptedExpandedSourceLowerAt
            D faceId hface state.2 hpositive).1.1) +
        acceptedExpandedSourcePeelSizeAt
          D faceId hface state.2 hpositive =
      slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1
  omega

theorem slabAcceptedTwoReplicaStateLowerLeftAt_mass_lt
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.1.1.1 faceId) :
    slabAcceptedTwoReplicaStateMass
        (slabAcceptedTwoReplicaStateLowerLeftAt
          state faceId hface hpositive) <
      slabAcceptedTwoReplicaStateMass state := by
  have hmass := acceptedExpandedSourceLowerAt_mass_lt
    D faceId hface state.1 hpositive
  unfold slabAcceptedTwoReplicaStateLowerLeftAt
    slabAcceptedTwoReplicaStateMass
  change
    slabPhysicalLabellingMass D.extent
          (acceptedExpandedSourceLowerAt
            D faceId hface state.1 hpositive).1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1 <
      slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1
  omega

theorem slabAcceptedTwoReplicaStateLowerRightAt_mass_lt
    {D : SlabPhysicalData} (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (hpositive : 0 < state.2.1.1 faceId) :
    slabAcceptedTwoReplicaStateMass
        (slabAcceptedTwoReplicaStateLowerRightAt
          state faceId hface hpositive) <
      slabAcceptedTwoReplicaStateMass state := by
  have hmass := acceptedExpandedSourceLowerAt_mass_lt
    D faceId hface state.2 hpositive
  unfold slabAcceptedTwoReplicaStateLowerRightAt
    slabAcceptedTwoReplicaStateMass
  change
    slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent
          (acceptedExpandedSourceLowerAt
            D faceId hface state.2 hpositive).1.1 <
      slabPhysicalLabellingMass D.extent state.1.1.1 +
        slabPhysicalLabellingMass D.extent state.2.1.1
  omega

end YMGap.Continuum.CompactDualSlabAcceptedPairedPeel

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabObservablePositiveSourceEntryToAccepted
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabObservableTwoReplicaPairToAcceptedState_mass
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.acceptedExpandedSourceLowerAt
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.acceptedExpandedSourceLowerAt_mass_add_peelSize
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabAcceptedTwoReplicaStateLowerLeftAt_mass_add_peelSize
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabAcceptedTwoReplicaStateLowerRightAt_mass_add_peelSize
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabAcceptedTwoReplicaStateLowerLeftAt_mass_lt
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedPeel.slabAcceptedTwoReplicaStateLowerRightAt_mass_lt
