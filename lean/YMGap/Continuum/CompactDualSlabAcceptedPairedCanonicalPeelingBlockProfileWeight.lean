/-
# Sum all ordered canonical signatures at one block-mass profile

At fixed terminal and fixed mass assigned to every face/replica scan block,
the preceding ordered block code has exactly `2^M` possible values, where `M`
is total peeled mass.  Equal code values determine the same erased skeleton;
the fixed-skeleton adaptive estimate then pays `(8/25)^M` inside each code
fiber.  Exact finite partition gives

  fiber weight at one block profile <= (16/25)^M * terminal weight.

Unlike the earlier fixed-signature theorem, this sums every possible number
of repeated peels at every scan key.  The remaining step is to sum the finite
block-mass profiles themselves by a product of geometric series.

Constructive contract: explicit dependent carriers and exact finite fibers
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    forall predicate : A -> Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} : forall items : List A,
    items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

/-- **Fixed block-profile terminal-fiber estimate.**  Every ordered
root/replica signature and every positive peel-size composition with the
prescribed block masses is absorbed into the strict rate `16/25`. -/
theorem slabAcceptedPairCanonicalPeeling_fixedTerminalBlockProfileMass_weight_sum_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (profile : List Nat)
    (mass : Nat)
    (hprofileMass : natListSum profile = mass)
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).1 = terminal)
    (hprofile : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceRankMassProfile faces
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical source).2 (2 * faces.length) = profile)
    (hmass : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceMass
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical source).2 = mass) :
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      pairedPeelSignatureEntropyAnchorRatio ^ mass *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let D := anchorSlabPhysicalData cutoff half
  let traceOf : SlabAcceptedTwoReplicaState D ->
      List SlabAcceptedPairedPeelRecord := fun source =>
    (slabAcceptedPairCanonicalPeeling D faces hphysical source).2
  let codeOf : SlabAcceptedTwoReplicaState D -> List (List Nat) :=
    fun source => slabAcceptedPairedPeelTraceRankBlockCode
      faces (traceOf source) (2 * faces.length)
  let targets := (sources.map codeOf).eraseDups
  have htargetsNodup : targets.Nodup := eraseDupsNodupLocal _
  have hcodeMem : forall source, source ∈ sources ->
      codeOf source ∈ binaryWordProfileCarrier profile := by
    intro source hsource
    have hmem := positiveCompositionBlockCode_mem_profileCarrier
      (slabAcceptedPairedPeelTraceRankBlocks
        faces (traceOf source) (2 * faces.length))
      (traceRankBlocks_sizes_pos D faces hphysical source
        (2 * faces.length))
    change slabAcceptedPairedPeelTraceRankBlockCode
      faces (traceOf source) (2 * faces.length) ∈
        binaryWordProfileCarrier profile
    unfold slabAcceptedPairedPeelTraceRankBlockCode
    rw [← hprofile source hsource]
    exact hmem
  have htargetsSubset : forall code, code ∈ targets ->
      code ∈ binaryWordProfileCarrier profile := by
    intro code hcode
    have hmapped := List.mem_eraseDups.mp hcode
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmapped
    exact hcodeMem source hsource
  have htargetsLength : targets.length ≤ 2 ^ mass := by
    have hbound := nodup_subset_length_le targets
      (binaryWordProfileCarrier profile) htargetsNodup htargetsSubset
    rw [binaryWordProfileCarrier_length, hprofileMass] at hbound
    exact hbound
  have hcoverage : forall source, source ∈ sources ->
      codeOf source ∈ targets := by
    intro source hsource
    apply List.mem_eraseDups.mpr
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  have hpartition := fiberWeight_total sources
    (slabAcceptedTwoReplicaStateWeight cutoff half)
    codeOf targets htargetsNodup hcoverage
  have hfiber : forall code, code ∈ targets ->
      fiberWeight sources
          (slabAcceptedTwoReplicaStateWeight cutoff half)
          codeOf code ≤
        componentAdaptiveEntropyAnchorRatio ^ mass *
          slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
    intro code hcode
    have hmapped := List.mem_eraseDups.mp hcode
    obtain ⟨representative, hrepresentative, hrepresentativeCode⟩ :=
      List.mem_map.mp hmapped
    let representativeSkeleton :=
      (traceOf representative).map SlabAcceptedPairedPeelRecord.skeleton
    unfold fiberWeight
    have hfixed :=
      slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_weight_sum_le
        cutoff half faces hphysical terminal representativeSkeleton
        (sources.filter fun source => decide (code = codeOf source))
        (List.filter_sublist.nodup hsources)
        (fun source hsource =>
          hterminal source (List.mem_filter.mp hsource).1)
        (fun source hsource => by
          have hsourceMem := (List.mem_filter.mp hsource).1
          have hcodeEq : code = codeOf source :=
            of_decide_eq_true (List.mem_filter.mp hsource).2
          have hcodePair : codeOf representative = codeOf source :=
            hrepresentativeCode.trans hcodeEq
          exact
            (slabAcceptedPairCanonicalPeeling_skeleton_eq_of_rankBlockCode_eq
              D faces hnodup hphysical representative source
              hcodePair).symm)
    have hrepresentativeMass :
        slabAcceptedPairedPeelSkeletonMass representativeSkeleton = mass := by
      unfold representativeSkeleton
      rw [slabAcceptedPairedPeelTrace_skeletonMass]
      exact hmass representative hrepresentative
    rw [hrepresentativeMass] at hfixed
    exact hfixed
  have hsum := fixedCardinalityWeightedSum_le targets
    (fiberWeight sources
      (slabAcceptedTwoReplicaStateWeight cutoff half) codeOf)
    2 mass componentAdaptiveEntropyAnchorRatio
    (slabAcceptedTwoReplicaStateWeight cutoff half terminal)
    htargetsLength (by decide)
    (slabAcceptedTwoReplicaStateWeight_nonnegative cutoff half terminal)
    hfiber
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (by simpa only [pairedPeelSignatureEntropyAnchorRatio] using hsum)

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight.slabAcceptedPairCanonicalPeeling_fixedTerminalBlockProfileMass_weight_sum_le
