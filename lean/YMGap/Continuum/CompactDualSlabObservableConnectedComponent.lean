/-
# A same-object connected observable component carrier

The observable-rooted strand compiler already produces a genuine connected
Z4 plaquette animal.  This module makes the second observable explicit: a
source is retained when its canonical root component reaches a chosen target
plaquette.  Genuine lattice connectivity then forces the physical peel size
to pay the full L-infinity separation plus one.

The connected source entries are not a surrogate Markov chain.  They are a
literal Boolean filter of the same expanded corrected-slab measure used by
the removal-fiber theorem.  Their deterministic target/size pushforward is
therefore an exact finite partition of a same-object connected event.

Constructive contract: explicit component animals, finite Boolean filtering,
and deterministic finite pushforward only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
import YMGap.Continuum.Z4CanonicalPolymerBoundaryTail

namespace YMGap.Continuum.CompactDualSlabObservableConnectedComponent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A connected component pays endpoint separation -/

/-- If a target plaquette occurs in the rooted component support, the
component's physical peel size is at least its L-infinity distance from the
root plaquette plus one. -/
theorem SlabFusionWitnessFaceStrandSeed.linfDist_add_one_le_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (target : Z4Plaq)
    (htarget : target ∈ componentPlaquetteSupport seed) :
    linfDist (slabPlaquetteAt extent seed.root.faceId) target + 1 <=
      (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  let support := componentPlaquetteSupport seed
  obtain ⟨animal, hanimal, hsame⟩ :=
    (z4ClusterCountBound_animal
      (slabPlaquetteAt extent seed.root.faceId)).2
      support.length support (componentPlaquetteAnimal seed)
  have htargetAnimal : target ∈ animal := hsame.1 target htarget
  have hfloor := enum_linf_reach_floor
    (slabPlaquetteAt extent seed.root.faceId) support.length
    animal hanimal target htargetAnimal
    (linfDist (slabPlaquetteAt extent seed.root.faceId) target)
    (Nat.le_refl _)
  have hsupportNodup : support.Nodup :=
    componentPlaquetteSupport_nodup seed
  have hanimalNodup : animal.Nodup :=
    enumPoly_nodup z4Chain
      (slabPlaquetteAt extent seed.root.faceId) support.length hanimal
  have hlength : animal.length = support.length :=
    (sameSupport_length_eq_of_nodup
      hsame hsupportNodup hanimalNodup).symm
  rw [hlength] at hfloor
  exact Nat.le_trans hfloor
    (componentPlaquetteSupport_length_le_peelFaces seed)

/-! ## 2. Literal connected source entries -/

/-- Whether the canonical component of one attached positive root source
reaches a chosen target plaquette. -/
def SlabObservablePositiveSourceEntry.reachesPlaquetteB
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D rootFaceId)
    (target : Z4Plaq) : Bool :=
  decide (target ∈ componentPlaquetteSupport
    (entry.seed D rootFaceId hroot))

theorem SlabObservablePositiveSourceEntry.reachesPlaquetteB_eq_true_iff
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D rootFaceId)
    (target : Z4Plaq) :
    SlabObservablePositiveSourceEntry.reachesPlaquetteB
        D rootFaceId hroot entry target = true ↔
      target ∈ componentPlaquetteSupport
        (entry.seed D rootFaceId hroot) := by
  simp [SlabObservablePositiveSourceEntry.reachesPlaquetteB]

/-- The attached positive source entries whose canonical rooted component
reaches the target plaquette. -/
def slabObservableConnectedSourceEntries
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : Z4Plaq) :
    List (SlabObservablePositiveSourceEntry D rootFaceId) :=
  (slabObservablePositiveSourceEntries D rootFaceId).filter fun entry =>
    SlabObservablePositiveSourceEntry.reachesPlaquetteB
      D rootFaceId hroot entry target

theorem mem_slabObservableConnectedSourceEntries_iff
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : Z4Plaq)
    (entry : SlabObservablePositiveSourceEntry D rootFaceId) :
    entry ∈ slabObservableConnectedSourceEntries
        D rootFaceId hroot target ↔
      entry ∈ slabObservablePositiveSourceEntries D rootFaceId ∧
        target ∈ componentPlaquetteSupport
          (entry.seed D rootFaceId hroot) := by
  rw [slabObservableConnectedSourceEntries, List.mem_filter]
  exact and_congr Iff.rfl
    (SlabObservablePositiveSourceEntry.reachesPlaquetteB_eq_true_iff
      D rootFaceId hroot entry target)

/-- Every literal connected entry's computed removal size pays the full
root-to-target separation. -/
theorem SlabObservablePositiveSourceEntry.connected_removalKey_size_floor
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : Z4Plaq)
    (entry : SlabObservablePositiveSourceEntry D rootFaceId)
    (hentry : entry ∈ slabObservableConnectedSourceEntries
      D rootFaceId hroot target) :
    linfDist (slabPlaquetteAt D.extent rootFaceId) target + 1 <=
      (entry.removalKey D rootFaceId hroot).peelSize := by
  let seed := entry.seed D rootFaceId hroot
  have htarget : target ∈ componentPlaquetteSupport seed :=
    (mem_slabObservableConnectedSourceEntries_iff
      D rootFaceId hroot target entry).mp hentry |>.2
  have hfloor :=
    SlabFusionWitnessFaceStrandSeed.linfDist_add_one_le_peelFaces
      seed target htarget
  exact hfloor

/-! ## 3. Exact deterministic partition of the connected event -/

/-- The same target/size key universe partitions the connected-event source
weight exactly. -/
theorem slabObservableConnectedSourceEntries_fiberWeight_total
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetPlaquette : Z4Plaq) :
    listQSum
        (fiberWeight
          (slabObservableConnectedSourceEntries
            D rootFaceId hroot targetPlaquette)
          (slabObservablePositiveEntryWeight D)
          (slabObservablePositiveEntryCode D rootFaceId hroot))
        (slabExpandedFineRemovalKeys D) ≈
      listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableConnectedSourceEntries
          D rootFaceId hroot targetPlaquette) := by
  exact fiberWeight_total
    (slabObservableConnectedSourceEntries
      D rootFaceId hroot targetPlaquette)
    (slabObservablePositiveEntryWeight D)
    (slabObservablePositiveEntryCode D rootFaceId hroot)
    (slabExpandedFineRemovalKeys D)
    (slabExpandedFineRemovalKeys_nodup D)
    (fun entry _ => slabObservablePositiveEntryCode_mem
      D rootFaceId hroot entry)

/-- Exact finite Fubini for the same-object connected event, written over
literal lowered targets and explicit component sizes. -/
theorem slabObservableConnectedSourceEntries_nestedFiberWeight_total
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetPlaquette : Z4Plaq) :
    listQSum
        (fun loweredTarget =>
          listQSum
            (fun peelSize =>
              fiberWeight
                (slabObservableConnectedSourceEntries
                  D rootFaceId hroot targetPlaquette)
                (slabObservablePositiveEntryWeight D)
                (slabObservablePositiveEntryCode D rootFaceId hroot)
                (slabExpandedFineRemovalKey
                  D loweredTarget peelSize))
            (List.range (slabObservableRemovalMaxSize D + 1)))
        (slabExpandedFineSources D) ≈
      listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableConnectedSourceEntries
          D rootFaceId hroot targetPlaquette) := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (slabExpandedFineRemovalKeys_sum_eqv_nested D
        (fiberWeight
          (slabObservableConnectedSourceEntries
            D rootFaceId hroot targetPlaquette)
          (slabObservablePositiveEntryWeight D)
          (slabObservablePositiveEntryCode D rootFaceId hroot))))
    (slabObservableConnectedSourceEntries_fiberWeight_total
      D rootFaceId hroot targetPlaquette)

#print axioms SlabFusionWitnessFaceStrandSeed.linfDist_add_one_le_peelFaces
#print axioms SlabObservablePositiveSourceEntry.reachesPlaquetteB
#print axioms SlabObservablePositiveSourceEntry.reachesPlaquetteB_eq_true_iff
#print axioms slabObservableConnectedSourceEntries
#print axioms mem_slabObservableConnectedSourceEntries_iff
#print axioms SlabObservablePositiveSourceEntry.connected_removalKey_size_floor
#print axioms slabObservableConnectedSourceEntries_fiberWeight_total
#print axioms slabObservableConnectedSourceEntries_nestedFiberWeight_total

end YMGap.Continuum.CompactDualSlabObservableConnectedComponent
