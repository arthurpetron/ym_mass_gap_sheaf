/-
# Sum canonical paired peeling over all positive peel-size compositions

Fix a terminal state, a total peeled mass `M`, and the ordered root/replica
signature of the canonical trace.  The remaining non-code datum is the list
of positive peel sizes summing to `M`.  Unary runs terminated by zero give an
injective binary word of length exactly `M`, so there are at most `2^M` such
size lists.

For each fixed size list the existing dependent adaptive carrier pays
`(8/25)^M`.  Exact finite fiber partition therefore absorbs the positive-
composition entropy and gives the strict aggregate rate

  (2 * 8/25)^M = (16/25)^M.

The root/replica signature is still fixed in this theorem.  Showing that the
deterministic fixed-guard scan has only a cutoff-independent summable family
of signatures is the next combinatorial step.

Constructive contract: explicit binary codes, finite fibers, and exact
rational weights only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact binary code for positive compositions -/

/-- Encode a positive part `n` by `n-1` ones followed by zero. -/
def positiveCompositionBinaryCode : List Nat -> List Nat
  | [] => []
  | size :: sizes =>
      List.replicate (size - 1) 1 ++
        0 :: positiveCompositionBinaryCode sizes

/-- Decode completed unary runs and restore the removed unit in every part. -/
def positiveCompositionBinaryDecode (bits : List Nat) : List Nat :=
  (decodeCompletedUnary 0 bits).map (fun size => size + 1)

/-- The positive-composition decoder is a literal left inverse. -/
theorem positiveCompositionBinaryDecode_code : forall sizes : List Nat,
    (forall size, size ∈ sizes -> 0 < size) ->
      positiveCompositionBinaryDecode
          (positiveCompositionBinaryCode sizes) = sizes
  | [], _ => rfl
  | size :: sizes, hpositive => by
      have hsize := hpositive size List.mem_cons_self
      have htail := positiveCompositionBinaryDecode_code sizes
        (fun item hitem =>
          hpositive item (List.mem_cons_of_mem size hitem))
      unfold positiveCompositionBinaryDecode
      simp only [positiveCompositionBinaryCode]
      rw [decodeCompletedUnary_replicate_one_zero]
      simp only [Nat.zero_add, List.map_cons]
      have hsub : size - 1 + 1 = size := by omega
      rw [hsub]
      change size ::
          positiveCompositionBinaryDecode
            (positiveCompositionBinaryCode sizes) = size :: sizes
      rw [htail]

/-- Positive-composition binary coding is injective on positive words. -/
theorem positiveCompositionBinaryCode_injective
    (left right : List Nat)
    (hleft : forall size, size ∈ left -> 0 < size)
    (hright : forall size, size ∈ right -> 0 < size)
    (hcode : positiveCompositionBinaryCode left =
      positiveCompositionBinaryCode right) :
    left = right := by
  have hdecoded := congrArg positiveCompositionBinaryDecode hcode
  rw [positiveCompositionBinaryDecode_code left hleft,
    positiveCompositionBinaryDecode_code right hright] at hdecoded
  exact hdecoded

/-- The code spends exactly one bit per unit of positive composition mass. -/
theorem positiveCompositionBinaryCode_length : forall sizes : List Nat,
    (forall size, size ∈ sizes -> 0 < size) ->
      (positiveCompositionBinaryCode sizes).length = natListSum sizes
  | [], _ => rfl
  | size :: sizes, hpositive => by
      have hsize := hpositive size List.mem_cons_self
      have htail := positiveCompositionBinaryCode_length sizes
        (fun item hitem =>
          hpositive item (List.mem_cons_of_mem size hitem))
      simp only [positiveCompositionBinaryCode, List.length_append,
        List.length_replicate, List.length_cons, natListSum]
      rw [htail]
      omega

/-- Every emitted symbol is a binary digit. -/
theorem positiveCompositionBinaryCode_entry_lt_two : forall
    (sizes : List Nat) (bit : Nat),
    bit ∈ positiveCompositionBinaryCode sizes -> bit < 2
  | [], bit, hmem => by cases hmem
  | size :: sizes, bit, hmem => by
      rcases List.mem_append.mp hmem with hrun | htail
      · have hbit : bit = 1 := List.eq_of_mem_replicate hrun
        omega
      · rcases List.mem_cons.mp htail with hzero | hrest
        · omega
        · exact positiveCompositionBinaryCode_entry_lt_two sizes bit hrest

/-- Every positive composition of exact mass `mass` lands in the explicit
`2^mass` binary-word carrier. -/
theorem positiveCompositionBinaryCode_mem_allSeqs
    (mass : Nat) (sizes : List Nat)
    (hpositive : forall size, size ∈ sizes -> 0 < size)
    (hmass : natListSum sizes = mass) :
    positiveCompositionBinaryCode sizes ∈ allSeqs 2 mass := by
  apply mem_allSeqs 2 mass
  · rw [positiveCompositionBinaryCode_length sizes hpositive, hmass]
  · intro bit hbit
    exact positiveCompositionBinaryCode_entry_lt_two sizes bit hbit

/-! ## 2. Trace projections and skeleton reconstruction -/

/-- Ordered root/replica signature, with no peel sizes or adaptive words. -/
def slabAcceptedPairedPeelTraceSignature
    (trace : List SlabAcceptedPairedPeelRecord) : List (Nat × Bool) :=
  trace.map fun record => (record.rootFaceId, record.left)

/-- Ordered positive peel sizes of a complete trace. -/
def slabAcceptedPairedPeelTraceSizes
    (trace : List SlabAcceptedPairedPeelRecord) : List Nat :=
  trace.map SlabAcceptedPairedPeelRecord.peelSize

/-- The size projection preserves exact trace mass. -/
theorem slabAcceptedPairedPeelTraceSizes_sum :
    forall trace : List SlabAcceptedPairedPeelRecord,
      natListSum (slabAcceptedPairedPeelTraceSizes trace) =
        slabAcceptedPairedPeelTraceMass trace
  | [] => rfl
  | record :: trace => by
      unfold slabAcceptedPairedPeelTraceSizes
        slabAcceptedPairedPeelTraceMass
      simp only [List.map_cons, natListSum, listNatWeight]
      exact congrArg (Nat.add record.peelSize)
        (slabAcceptedPairedPeelTraceSizes_sum trace)

/-- Equal root/side signatures and equal peel-size words determine equal
erased skeleton lists. -/
theorem slabAcceptedPairedPeelTrace_skeleton_eq_of_signature_eq_of_sizes_eq :
    forall left right : List SlabAcceptedPairedPeelRecord,
      slabAcceptedPairedPeelTraceSignature left =
          slabAcceptedPairedPeelTraceSignature right ->
      slabAcceptedPairedPeelTraceSizes left =
          slabAcceptedPairedPeelTraceSizes right ->
      left.map SlabAcceptedPairedPeelRecord.skeleton =
        right.map SlabAcceptedPairedPeelRecord.skeleton
  | [], [], _, _ => rfl
  | [], _ :: _, hsignature, _ => by cases hsignature
  | _ :: _, [], hsignature, _ => by cases hsignature
  | leftRecord :: leftTail, rightRecord :: rightTail,
      hsignature, hsizes => by
      have hsignature' :
          (leftRecord.rootFaceId, leftRecord.left) ::
              slabAcceptedPairedPeelTraceSignature leftTail =
            (rightRecord.rootFaceId, rightRecord.left) ::
              slabAcceptedPairedPeelTraceSignature rightTail := by
        exact hsignature
      have hsizes' :
          leftRecord.peelSize ::
              slabAcceptedPairedPeelTraceSizes leftTail =
            rightRecord.peelSize ::
              slabAcceptedPairedPeelTraceSizes rightTail := by
        exact hsizes
      have hsignatureHead := (List.cons.inj hsignature').1
      have hsignatureTail := (List.cons.inj hsignature').2
      have hsizesHead := (List.cons.inj hsizes').1
      have hsizesTail := (List.cons.inj hsizes').2
      have hroot := congrArg Prod.fst hsignatureHead
      have hside := congrArg Prod.snd hsignatureHead
      have hskeleton :
          YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.SlabAcceptedPairedPeelRecord.skeleton leftRecord =
            YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier.SlabAcceptedPairedPeelRecord.skeleton rightRecord := by
        cases leftRecord with
        | mk leftRoot leftSide leftSize leftCode =>
            cases rightRecord with
            | mk rightRoot rightSide rightSize rightCode =>
                simp only at hroot hside hsizesHead ⊢
                subst rightRoot
                subst rightSide
                subst rightSize
                rfl
      simp only [List.map_cons]
      rw [hskeleton,
        slabAcceptedPairedPeelTrace_skeleton_eq_of_signature_eq_of_sizes_eq
          leftTail rightTail hsignatureTail hsizesTail]

/-! ## 3. Finite target-list helpers -/

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

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

/-! ## 4. Sum every peel-size composition at fixed signature -/

/-- Adaptive component entropy plus positive-composition entropy at the
production anchor. -/
def pairedPeelSignatureEntropyAnchorRatio : Q' :=
  Q'.ofNat 2 * componentAdaptiveEntropyAnchorRatio

theorem pairedPeelSignatureEntropyAnchorRatio_eqv :
    pairedPeelSignatureEntropyAnchorRatio ≈
      Q'.mkPos 16 25 (by decide) := by
  decide

theorem pairedPeelSignatureEntropyAnchorRatio_lt_one :
    pairedPeelSignatureEntropyAnchorRatio < (1 : Q') := by
  decide

/-- **Fixed-signature terminal-fiber estimate.**  Sum every positive
peel-size composition of one exact total mass.  The strict rate is `16/25`,
independent of cutoff, half-volume, terminal, and the chosen signature. -/
theorem slabAcceptedPairCanonicalPeeling_fixedTerminalSignatureMass_weight_sum_le
    (cutoff half : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges
        (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (signature : List (Nat × Bool))
    (mass : Nat)
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source).1 = terminal)
    (hsignature : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceSignature
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical source).2 = signature)
    (hmass : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceMass
          (slabAcceptedPairCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            faces hphysical source).2 = mass) :
    listQSum (slabAcceptedTwoReplicaStateWeight cutoff half) sources ≤
      pairedPeelSignatureEntropyAnchorRatio ^ mass *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let traceOf : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half) ->
        List SlabAcceptedPairedPeelRecord := fun source =>
    (slabAcceptedPairCanonicalPeeling
      (anchorSlabPhysicalData cutoff half)
      faces hphysical source).2
  let codeOf : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half) -> List Nat := fun source =>
    positiveCompositionBinaryCode
      (slabAcceptedPairedPeelTraceSizes (traceOf source))
  let targets := (sources.map codeOf).eraseDups
  have htargetsNodup : targets.Nodup := by
    exact eraseDupsNodupLocal _
  have hcodeMem : forall source, source ∈ sources ->
      codeOf source ∈ allSeqs 2 mass := by
    intro source hsource
    apply positiveCompositionBinaryCode_mem_allSeqs mass
    · intro size hsize
      obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hsize
      exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
        (anchorSlabPhysicalData cutoff half)
        faces hphysical source record hrecord
    · rw [slabAcceptedPairedPeelTraceSizes_sum]
      exact hmass source hsource
  have htargetsSubset : forall code, code ∈ targets ->
      code ∈ allSeqs 2 mass := by
    intro code hcode
    have hmapped := List.mem_eraseDups.mp hcode
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmapped
    exact hcodeMem source hsource
  have htargetsLength : targets.length ≤ 2 ^ mass := by
    have hbound := nodup_subset_length_le targets (allSeqs 2 mass)
      htargetsNodup htargetsSubset
    rw [length_allSeqs] at hbound
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
    let representativeTrace := traceOf representative
    let representativeSkeleton :=
      representativeTrace.map SlabAcceptedPairedPeelRecord.skeleton
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
          have hpositiveRepresentative : forall size,
              size ∈ slabAcceptedPairedPeelTraceSizes representativeTrace ->
                0 < size := by
            intro size hsize
            obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hsize
            exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
              (anchorSlabPhysicalData cutoff half)
              faces hphysical representative record hrecord
          have hpositiveSource : forall size,
              size ∈ slabAcceptedPairedPeelTraceSizes (traceOf source) ->
                0 < size := by
            intro size hsize
            obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hsize
            exact slabAcceptedPairCanonicalPeeling_trace_peelSize_pos
              (anchorSlabPhysicalData cutoff half)
              faces hphysical source record hrecord
          have hcodePair : codeOf representative = codeOf source := by
            exact hrepresentativeCode.trans hcodeEq
          have hsizes :
              slabAcceptedPairedPeelTraceSizes representativeTrace =
                slabAcceptedPairedPeelTraceSizes (traceOf source) := by
            exact positiveCompositionBinaryCode_injective _ _
              hpositiveRepresentative hpositiveSource hcodePair
          have hsignaturePair :
              slabAcceptedPairedPeelTraceSignature representativeTrace =
                slabAcceptedPairedPeelTraceSignature (traceOf source) := by
            exact (hsignature representative hrepresentative).trans
              (hsignature source hsourceMem).symm
          exact
            (slabAcceptedPairedPeelTrace_skeleton_eq_of_signature_eq_of_sizes_eq
              representativeTrace (traceOf source)
              hsignaturePair hsizes).symm)
    have hrepresentativeMass :
        slabAcceptedPairedPeelSkeletonMass representativeSkeleton = mass := by
      unfold representativeSkeleton representativeTrace
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

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight

#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight.positiveCompositionBinaryCode_injective
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight.positiveCompositionBinaryCode_mem_allSeqs
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight.slabAcceptedPairedPeelTrace_skeleton_eq_of_signature_eq_of_sizes_eq
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight.pairedPeelSignatureEntropyAnchorRatio_lt_one
#print axioms YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSignatureWeight.slabAcceptedPairCanonicalPeeling_fixedTerminalSignatureMass_weight_sum_le
