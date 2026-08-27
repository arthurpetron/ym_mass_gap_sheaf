/-
# Flattened pushforward for paired-support recoupling rows

The source-dependent recoupling rows are flattened into the sigma carrier of
all `(source, choice)` pairs.  Finite Fubini identifies the usual nested
dependent-kernel column with one ordinary deterministic pushforward on that
carrier.  Filtering by a concrete four-cell target then produces its literal,
duplicate-free preimage list.

Constructive contract: finite list Fubini, a concrete decidable target key,
and exact `Q'`; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
import YMGap.Continuum.CompactDualSlabExpandedTargetKey
import YMGap.Continuum.FiniteDependentKernelCapacity

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalSourceChoice
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive equality on the concrete target carrier -/

def slabObservableTwoReplicaPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  fun left right =>
    if hleft :
        slabExpandedFineTargetKey D left.1.1.1 left.1.1.2 =
          slabExpandedFineTargetKey D right.1.1.1 right.1.1.2 then
      if hright :
          slabExpandedFineTargetKey D left.2.1.1 left.2.1.2 =
            slabExpandedFineTargetKey D right.2.1.1 right.2.1.2 then
        isTrue (Prod.ext
          (Subtype.ext (slabExpandedFineTargetKey_eq_source_eq D
            left.1.source_mem_expanded right.1.source_mem_expanded hleft))
          (Subtype.ext (slabExpandedFineTargetKey_eq_source_eq D
            left.2.2 right.2.2 hright)))
      else
        isFalse (fun heq => hright (by rw [heq]))
    else
      isFalse (fun heq => hleft (by rw [heq]))

/-! ## 2. One ordinary weighted realization -/

def slabObservablePairedSupportRecouplingSourceChoiceWeight
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (item : SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) : Q' :=
  slabObservablePairedSupportRecouplingWeight
    D rootFaceId targetFaceId htarget item.1 item.2

def slabObservablePairedSupportRecouplingSourceChoiceRealize
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (item : SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) :
    SlabObservableTwoReplicaPair D rootFaceId :=
  slabObservablePairedSupportRecoupledTargetPair
    D rootFaceId targetFaceId htarget item.1 item.2

theorem slabObservablePairedSupportDependentPushforward_eqv_flattened
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
    kernelPushforwardWeight
        (slabObservablePairedSupportRecouplingSourceChoices
          D rootFaceId targetFaceId)
        (slabObservablePairedSupportRecouplingSourceChoiceWeight
          D rootFaceId targetFaceId htarget)
        (slabObservablePairedSupportRecouplingSourceChoiceRealize
          D rootFaceId targetFaceId htarget)
        target ≈
      listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedSupportRecouplingChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingWeight
            D rootFaceId targetFaceId htarget)
          (slabObservablePairedSupportRecoupledTargetPair
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedSupportSeparatedSources
          D rootFaceId targetFaceId) := by
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  unfold kernelPushforwardWeight
  unfold slabObservablePairedSupportRecouplingSourceChoices
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr
  intro source
  unfold slabObservablePairedSupportRecouplingSourceChoiceBlock
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 3. Literal concrete-target preimages -/

def slabObservablePairedSupportRecouplingTargetPreimages
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    List (SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) :=
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  (slabObservablePairedSupportRecouplingSourceChoices
    D rootFaceId targetFaceId).filter fun item =>
      decide (target =
        slabObservablePairedSupportRecouplingSourceChoiceRealize
          D rootFaceId targetFaceId htarget item)

theorem mem_slabObservablePairedSupportRecouplingTargetPreimages_iff
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId)
    (item : SlabObservablePairedSupportRecouplingSourceChoice
      D rootFaceId targetFaceId) :
    item ∈ slabObservablePairedSupportRecouplingTargetPreimages
        D rootFaceId targetFaceId htarget target ↔
      item ∈ slabObservablePairedSupportRecouplingSourceChoices
          D rootFaceId targetFaceId ∧
        target = slabObservablePairedSupportRecouplingSourceChoiceRealize
          D rootFaceId targetFaceId htarget item := by
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  unfold slabObservablePairedSupportRecouplingTargetPreimages
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

theorem slabObservablePairedSupportRecouplingTargetPreimages_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    (slabObservablePairedSupportRecouplingTargetPreimages
      D rootFaceId targetFaceId htarget target).Nodup := by
  unfold slabObservablePairedSupportRecouplingTargetPreimages
  exact List.filter_sublist.nodup
    (slabObservablePairedSupportRecouplingSourceChoices_nodup
      D rootFaceId targetFaceId)

theorem slabObservablePairedSupportDependentPushforward_eqv_preimage_sum
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabObservableTwoReplicaPair D rootFaceId) :
    letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
    listQSum
        (fun source => dependentKernelPushforwardWeight
          (SlabObservablePairedSupportRecouplingChoice
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingChoices
            D rootFaceId targetFaceId)
          (slabObservablePairedSupportRecouplingWeight
            D rootFaceId targetFaceId htarget)
          (slabObservablePairedSupportRecoupledTargetPair
            D rootFaceId targetFaceId htarget)
          source target)
        (slabObservablePairedSupportSeparatedSources
          D rootFaceId targetFaceId) ≈
      listQSum
        (slabObservablePairedSupportRecouplingSourceChoiceWeight
          D rootFaceId targetFaceId htarget)
        (slabObservablePairedSupportRecouplingTargetPreimages
          D rootFaceId targetFaceId htarget target) := by
  letI := slabObservableTwoReplicaPairDecidableEq D rootFaceId
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (slabObservablePairedSupportDependentPushforward_eqv_flattened
        D rootFaceId targetFaceId htarget target))
    (kernelPushforwardWeight_eqv_fiberWeight
      (slabObservablePairedSupportRecouplingSourceChoiceWeight
        D rootFaceId targetFaceId htarget)
      (slabObservablePairedSupportRecouplingSourceChoiceRealize
        D rootFaceId targetFaceId htarget)
      target
      (slabObservablePairedSupportRecouplingSourceChoices
        D rootFaceId targetFaceId))

end YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward.slabObservableTwoReplicaPairDecidableEq
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward.slabObservablePairedSupportDependentPushforward_eqv_flattened
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward.slabObservablePairedSupportRecouplingTargetPreimages_nodup
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward.slabObservablePairedSupportDependentPushforward_eqv_preimage_sum
