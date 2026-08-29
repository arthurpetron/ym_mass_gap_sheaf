/-
# Canonical peeling of the reflected-channel guard

Run the existing deterministic accepted paired-component peeler on the fixed
reflected guard list.  For every accepted state on an extent-five corrected
slab, the output is accepted, both physical replicas vanish on the whole
guard, and the recorded positive peel sizes telescope exactly against total
paired physical mass.

The output retains the full reconstruction trace.  This is the executable
clearing stage preceding a background graft; no graft or weight summation is
claimed here.

Constructive contract: the existing well-founded canonical recursion and its
exact trace theorems only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard

/-! ## 1. The fixed guard is physical in every extent-five datum -/

theorem reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    {faceId : Nat} (hface : faceId ∈ reflectedBentPatternGuardFaceIds) :
    faceId ∈ slabPhysicalFaceEdges D.extent := by
  rw [hextent]
  exact reflectedBentPatternGuardFaceId_mem_physical hface

/-! ## 2. Executable guard peeling -/

/-- Canonically clear every currently positive face in the fixed reflected
guard.  A selected root may peel its whole strand component, and the complete
inverse record is retained by the generic process. -/
def reflectedBentGuardCanonicalPeeling
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabAcceptedPairedCanonicalPeelingOutput D :=
  slabAcceptedPairCanonicalPeeling D
    reflectedBentPatternGuardFaceIds
    (fun _ hface =>
      reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
        D hextent hface)
    state

/-! ## 3. Exact clearing and trace conservation -/

/-- Both terminal replicas vanish on every face of the separating collar. -/
theorem reflectedBentGuardCanonicalPeeling_final_zero
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hface : faceId ∈ reflectedBentPatternGuardFaceIds) :
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId = 0 ∧
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 faceId = 0 := by
  exact slabAcceptedPairCanonicalPeeling_final_zero
    D reflectedBentPatternGuardFaceIds
      (fun query hquery =>
        reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
          D hextent hquery)
      state faceId hface

/-- Every retained reconstruction record removes strictly positive physical
multiplicity. -/
theorem reflectedBentGuardCanonicalPeeling_trace_peelSize_pos
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (record : SlabAcceptedPairedPeelRecord)
    (hrecord : record ∈
      (reflectedBentGuardCanonicalPeeling D hextent state).2) :
    0 < record.peelSize := by
  exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
    D reflectedBentPatternGuardFaceIds
      (fun query hquery =>
        reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
          D hextent hquery)
      state record hrecord

/-- Every retained component word belongs to its literal adaptive entropy
carrier. -/
theorem reflectedBentGuardCanonicalPeeling_trace_valid
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (record : SlabAcceptedPairedPeelRecord)
    (hrecord : record ∈
      (reflectedBentGuardCanonicalPeeling D hextent state).2) :
    record.Valid D.extent := by
  exact slabAcceptedPairCanonicalPeeling_trace_valid
    D reflectedBentPatternGuardFaceIds
      (fun query hquery =>
        reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
          D hextent hquery)
      state record hrecord

/-- Exact total-mass conservation across the whole guarded clearing pass. -/
theorem reflectedBentGuardCanonicalPeeling_mass_telescope
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabAcceptedTwoReplicaStateMass
        (reflectedBentGuardCanonicalPeeling D hextent state).1 +
      slabAcceptedPairedPeelTraceMass
        (reflectedBentGuardCanonicalPeeling D hextent state).2 =
      slabAcceptedTwoReplicaStateMass state := by
  exact slabAcceptedPairCanonicalPeeling_mass_telescope
    D reflectedBentPatternGuardFaceIds
      (fun query hquery =>
        reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
          D hextent hquery)
      state

/-- The guarded reconstruction trace contains no more records than the
initial paired physical mass. -/
theorem reflectedBentGuardCanonicalPeeling_trace_length_le_mass
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardCanonicalPeeling D hextent state).2.length ≤
      slabAcceptedTwoReplicaStateMass state := by
  exact slabAcceptedPairCanonicalPeeling_trace_length_le_mass
    D reflectedBentPatternGuardFaceIds
      (fun query hquery =>
        reflectedBentPatternGuardFaceId_mem_physical_of_extent_eq_five
          D hextent hquery)
      state

#print axioms reflectedBentGuardCanonicalPeeling
#print axioms reflectedBentGuardCanonicalPeeling_final_zero
#print axioms reflectedBentGuardCanonicalPeeling_trace_peelSize_pos
#print axioms reflectedBentGuardCanonicalPeeling_trace_valid
#print axioms reflectedBentGuardCanonicalPeeling_mass_telescope
#print axioms reflectedBentGuardCanonicalPeeling_trace_length_le_mass

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
