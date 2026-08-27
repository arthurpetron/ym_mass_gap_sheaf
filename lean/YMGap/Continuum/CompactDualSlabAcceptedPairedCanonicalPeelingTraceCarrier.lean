/-
# A dependent carrier for complete canonical paired-peeling traces

Erase only the adaptive code from each canonical peel record, retaining its
root face, replica side, and positive peel size.  For one fixed list of these
record skeletons, the complete trace carrier is the dependent product of the
existing adaptive component carriers.

Its cardinality is at most

  componentAdaptiveEntropyBase ^ totalPeelMass.

Complete peeling is injective at fixed terminal state and fixed scanned face
list.  Consequently any duplicate-free source family with one common
terminal and skeleton has the same bound.  Combining this cardinality with
the pointwise anchor payment gives the exact fixed-skeleton weight estimate

  sourceWeightSum <= (8/25)^totalPeelMass * terminalWeight.

This module does not count the possible skeletons.  That global root/side/size
summation is the remaining finite combinatorial frontier.

Constructive contract: dependent finite products, explicit injection, and
exact rational weights only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingInjective
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Skeletons and their dependent code carrier -/

/-- The non-code part of one peel record. -/
structure SlabAcceptedPairedPeelSkeleton : Type where
  rootFaceId : Nat
  left : Bool
  peelSize : Nat
deriving DecidableEq

/-- Erase the adaptive word while retaining the geometric and side data. -/
def SlabAcceptedPairedPeelRecord.skeleton
    (record : SlabAcceptedPairedPeelRecord) :
    SlabAcceptedPairedPeelSkeleton where
  rootFaceId := record.rootFaceId
  left := record.left
  peelSize := record.peelSize

/-- Total physical multiplicity prescribed by a skeleton list. -/
def slabAcceptedPairedPeelSkeletonMass
    (skeletons : List SlabAcceptedPairedPeelSkeleton) : Nat :=
  listNatWeight SlabAcceptedPairedPeelSkeleton.peelSize skeletons

/-- The dependent product of the admitted adaptive code carriers at every
record skeleton. -/
def slabAcceptedPairedPeelTraceCarrier
    (extent : Nat) :
    List SlabAcceptedPairedPeelSkeleton →
      List (List SlabAcceptedPairedPeelRecord)
  | [] => [[]]
  | skeleton :: tail =>
      (componentAdaptiveEntropyCarrier
        extent skeleton.rootFaceId skeleton.peelSize).flatMap fun code =>
          (slabAcceptedPairedPeelTraceCarrier extent tail).map fun trace =>
            ({ rootFaceId := skeleton.rootFaceId
               left := skeleton.left
               peelSize := skeleton.peelSize
               code := code : SlabAcceptedPairedPeelRecord }) :: trace

private theorem flatMap_record_cons_length
    (skeleton : SlabAcceptedPairedPeelSkeleton)
    (codes : List ComponentAdaptiveEntropyCode)
    (traces : List (List SlabAcceptedPairedPeelRecord)) :
    (codes.flatMap fun code =>
        traces.map fun trace =>
          ({ rootFaceId := skeleton.rootFaceId
             left := skeleton.left
             peelSize := skeleton.peelSize
             code := code : SlabAcceptedPairedPeelRecord }) :: trace).length =
      codes.length * traces.length := by
  induction codes with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons code tail ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul]
      omega

/-- The complete dependent trace carrier costs exactly the product of the
one-component entropy bounds, hence one base power at total peel mass. -/
theorem slabAcceptedPairedPeelTraceCarrier_length_le
    (extent : Nat) : ∀ skeletons,
    (slabAcceptedPairedPeelTraceCarrier extent skeletons).length ≤
      componentAdaptiveEntropyBase ^
        slabAcceptedPairedPeelSkeletonMass skeletons
  | [] => by
      exact Nat.le_refl 1
  | skeleton :: tail => by
      rw [slabAcceptedPairedPeelTraceCarrier,
        flatMap_record_cons_length]
      have hhead := componentAdaptiveEntropyCarrier_length_le
        extent skeleton.rootFaceId skeleton.peelSize
      have htail := slabAcceptedPairedPeelTraceCarrier_length_le extent tail
      calc
        (componentAdaptiveEntropyCarrier
              extent skeleton.rootFaceId skeleton.peelSize).length *
            (slabAcceptedPairedPeelTraceCarrier extent tail).length ≤
          componentAdaptiveEntropyBase ^ skeleton.peelSize *
            componentAdaptiveEntropyBase ^
              slabAcceptedPairedPeelSkeletonMass tail :=
            Nat.mul_le_mul hhead htail
        _ = componentAdaptiveEntropyBase ^
            slabAcceptedPairedPeelSkeletonMass (skeleton :: tail) := by
              unfold slabAcceptedPairedPeelSkeletonMass
              simp only [listNatWeight]
              rw [Nat.pow_add]

/-- Projecting a trace to skeletons preserves its exact total peel mass. -/
theorem slabAcceptedPairedPeelTrace_skeletonMass
    (trace : List SlabAcceptedPairedPeelRecord) :
    slabAcceptedPairedPeelSkeletonMass
        (trace.map SlabAcceptedPairedPeelRecord.skeleton) =
      slabAcceptedPairedPeelTraceMass trace := by
  induction trace with
  | nil => rfl
  | cons record tail ih =>
      unfold slabAcceptedPairedPeelSkeletonMass
        slabAcceptedPairedPeelTraceMass at ih ⊢
      simp only [List.map_cons, listNatWeight,
        SlabAcceptedPairedPeelRecord.skeleton]
      rw [ih]

/-- Every recordwise-valid trace belongs to the dependent carrier over its
own erased skeleton list. -/
theorem slabAcceptedPairedPeelTrace_mem_carrier
    (extent : Nat) : ∀ trace : List SlabAcceptedPairedPeelRecord,
    (∀ record, record ∈ trace → record.Valid extent) →
      trace ∈ slabAcceptedPairedPeelTraceCarrier extent
        (trace.map SlabAcceptedPairedPeelRecord.skeleton)
  | [], _ => List.mem_cons_self
  | record :: tail, hvalid => by
      unfold slabAcceptedPairedPeelTraceCarrier
      apply List.mem_flatMap.mpr
      refine ⟨record.code,
        hvalid record List.mem_cons_self, ?_⟩
      apply List.mem_map.mpr
      refine ⟨tail,
        slabAcceptedPairedPeelTrace_mem_carrier extent tail
          (fun item hitem =>
            hvalid item (List.mem_cons_of_mem record hitem)), ?_⟩
      rfl

/-! ## 2. Fixed-terminal, fixed-skeleton source fibers -/

/-- At fixed scan list, terminal state, and erased trace skeleton, complete
trace injectivity bounds a duplicate-free source family by the dependent
adaptive carrier. -/
theorem slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_length_le
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (skeletons : List SlabAcceptedPairedPeelSkeleton)
    (sources : List (SlabAcceptedTwoReplicaState D))
    (hsources : sources.Nodup)
    (hterminal : ∀ source, source ∈ sources →
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical source).1 = terminal)
    (hskeleton : ∀ source, source ∈ sources →
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical source).2.map
          SlabAcceptedPairedPeelRecord.skeleton = skeletons) :
    sources.length ≤ componentAdaptiveEntropyBase ^
      slabAcceptedPairedPeelSkeletonMass skeletons := by
  let traceOf : SlabAcceptedTwoReplicaState D →
      List SlabAcceptedPairedPeelRecord := fun source =>
    (slabAcceptedPairCanonicalPeeling D faces hphysical source).2
  have htracesNodup : (sources.map traceOf).Nodup := by
    apply nodup_map_of_injOn traceOf sources hsources
    intro left hleft right hright htrace
    apply slabAcceptedPairCanonicalPeeling_injective
      D faces hphysical left right
    apply Prod.ext
    · exact (hterminal left hleft).trans
        (hterminal right hright).symm
    · exact htrace
  have hsubset : ∀ trace, trace ∈ sources.map traceOf →
      trace ∈ slabAcceptedPairedPeelTraceCarrier D.extent skeletons := by
    intro trace htrace
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htrace
    have hmem := slabAcceptedPairedPeelTrace_mem_carrier
      D.extent (traceOf source)
      (slabAcceptedPairCanonicalPeeling_trace_valid
        D faces hphysical source)
    rw [hskeleton source hsource] at hmem
    exact hmem
  have hcarrier := nodup_subset_length_le
    (sources.map traceOf)
    (slabAcceptedPairedPeelTraceCarrier D.extent skeletons)
    htracesNodup hsubset
  rw [List.length_map] at hcarrier
  exact Nat.le_trans hcarrier
    (slabAcceptedPairedPeelTraceCarrier_length_le D.extent skeletons)

/-! ## 3. Contract the fixed-skeleton source weight -/

/-- The exact weighted fixed-terminal/fixed-skeleton estimate.  All adaptive
component entropy is absorbed into the strict rate `8/25` at the total trace
mass. -/
theorem slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_weight_sum_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hphysical : ∀ faceId, faceId ∈ faces →
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (skeletons : List SlabAcceptedPairedPeelSkeleton)
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)))
    (hsources : sources.Nodup)
    (hterminal : ∀ source, source ∈ sources →
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).1 = terminal)
    (hskeleton : ∀ source, source ∈ sources →
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).2.map
          SlabAcceptedPairedPeelRecord.skeleton = skeletons) :
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      componentAdaptiveEntropyAnchorRatio ^
          slabAcceptedPairedPeelSkeletonMass skeletons *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_length_le
      (anchorSlabPhysicalData cutoff half)
      faces hphysical terminal skeletons sources hsources
      hterminal hskeleton
  · decide
  · exact slabAcceptedTwoReplicaStateWeight_nonnegative
      cutoff half terminal
  · intro source hsource
    have hweight := slabAcceptedPairCanonicalPeeling_sourceWeight_le
      cutoff half faces hphysical source
    dsimp only at hweight
    have hmass :
        slabAcceptedPairedPeelTraceMass
            (slabAcceptedPairCanonicalPeeling
              (anchorSlabPhysicalData cutoff half)
              faces hphysical source).2 =
          slabAcceptedPairedPeelSkeletonMass skeletons := by
      rw [← slabAcceptedPairedPeelTrace_skeletonMass]
      rw [hskeleton source hsource]
    rw [hmass, hterminal source hsource] at hweight
    exact hweight

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.slabAcceptedPairedPeelTraceCarrier_length_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.slabAcceptedPairedPeelTrace_mem_carrier
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_length_le
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_weight_sum_le
