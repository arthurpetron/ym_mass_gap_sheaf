/-
# Canonical indices for cutoff-two table states

Every state in the exact cutoff-two cube table belongs to the canonical
vacuum component.  This module exposes the corresponding finite-carrier
index as a small reusable witness, keeping the generated connectivity proof
opaque to downstream diagnostics.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Every literal cutoff-two sector state has a representing index in the
exact canonical vacuum component. -/
theorem exists_canonical_index_for_cutoffTwo_sector_state
    {state : EdgeLabelling}
    (hstate : state ∈ cutoffTwoCubeSectorStates) :
    ∃ index,
      index ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0 ∧
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 index = state := by
  have hcanonical : state ∈
      centralPhysicalFiniteVacuumSectorStates
        cutoffTwoHalfCoupling (by decide) 2 0 :=
    cutoffTwoCubeSectorState_mem_canonicalVacuumSector hstate
  unfold centralPhysicalFiniteVacuumSectorStates at hcanonical
  exact List.mem_map.mp hcanonical

/-- A table coordinate below 65 has a representing index in the exact
canonical vacuum component. -/
theorem exists_canonical_index_for_cutoffTwo_table_state
    {row : Nat} (hrow : row < 65) :
    ∃ index,
      index ∈ centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 0 ∧
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
        (by decide) 2 0 index = cutoffTwoSectorLocalZeroStateAt row :=
  exists_canonical_index_for_cutoffTwo_sector_state
    (cutoffTwoSectorLocalZeroStateAt_mem hrow)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness.exists_canonical_index_for_cutoffTwo_sector_state
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalIndexWitness.exists_canonical_index_for_cutoffTwo_table_state
