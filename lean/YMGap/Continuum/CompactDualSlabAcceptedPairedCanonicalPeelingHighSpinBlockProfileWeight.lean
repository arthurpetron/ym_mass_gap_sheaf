/-
# Sum profiled accepted peeling at one block-mass profile

The fixed-skeleton arbitrary-coupling inverse-fiber theorem has exterior rate
`8/25` and residual-core factor `20480000`.  At one fixed mass profile over
the deterministic face/replica scan blocks, the existing positive-composition
block code has at most `2^(exterior+core)` values and equal codes recover the
same erased trace skeleton.  Summing all ordered signatures and peel-size
words therefore gives

  (16/25)^exterior * 40960000^core * terminalWeight.

The exterior rate remains strictly below one.  The noncontractive core factor
is now isolated in the aggregate core exponent already proved bounded by
`2 * faceCount * threshold`; summing the realized exterior/core block profiles
is the next layer.

Constructive contract: explicit finite block codes, exact fibers, and rational
arithmetic only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfileFiber
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinBlockProfileWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockCode
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfileFiber
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact post-composition rates -/

/-- Strict exterior rate after both adaptive-code and positive-composition
counting. -/
def pairedHighSpinProfileExteriorRate : Q' :=
  Q'.ofNat 2 * componentAdaptiveEntropyAnchorRatio

/-- Explicit core factor after both adaptive-code and positive-composition
counting. -/
def pairedHighSpinProfileCoreFactor : Q' :=
  Q'.ofNat 2 * componentCoreCompletionResidualEntropyFactor

theorem pairedHighSpinProfileExteriorRate_eqv :
    pairedHighSpinProfileExteriorRate ≈ Q'.mkPos 16 25 (by decide) := by
  unfold pairedHighSpinProfileExteriorRate
    componentAdaptiveEntropyAnchorRatio componentAdaptiveEntropyBase
    YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorFaceCoefficient
  decide

theorem pairedHighSpinProfileExteriorRate_lt_one :
    pairedHighSpinProfileExteriorRate < (1 : Q') := by
  unfold pairedHighSpinProfileExteriorRate
    componentAdaptiveEntropyAnchorRatio componentAdaptiveEntropyBase
    YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorFaceCoefficient
  decide

/-- Raw coefficient after counting every positive-composition block code. -/
def pairedHighSpinBlockProfileCountedRate
    (exterior core : Nat) : Q' :=
  Q'.ofNat (2 ^ (exterior + core)) *
    (componentAdaptiveEntropyAnchorRatio ^ exterior *
      componentCoreCompletionResidualEntropyFactor ^ core)

/-- The composition count splits exactly between the exterior and core
exponents. -/
theorem pairedHighSpinBlockProfileCountedRate_eqv
    (exterior core : Nat) :
    pairedHighSpinBlockProfileCountedRate exterior core ≈
      pairedHighSpinProfileExteriorRate ^ exterior *
        pairedHighSpinProfileCoreFactor ^ core := by
  unfold pairedHighSpinBlockProfileCountedRate
    pairedHighSpinProfileExteriorRate pairedHighSpinProfileCoreFactor
  rw [Nat.pow_add]
  refine Q'.eqv_trans _
    ((Q'.ofNat (2 ^ exterior) * Q'.ofNat (2 ^ core)) *
      (componentAdaptiveEntropyAnchorRatio ^ exterior *
        componentCoreCompletionResidualEntropyFactor ^ core)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv (2 ^ exterior) (2 ^ core))
  refine Q'.eqv_trans _
    ((Q'.ofNat (2 ^ exterior) *
        componentAdaptiveEntropyAnchorRatio ^ exterior) *
      (Q'.ofNat (2 ^ core) *
        componentCoreCompletionResidualEntropyFactor ^ core)) _ ?_ ?_
  · exact mul_four_mid'
      (Q'.ofNat (2 ^ exterior)) (Q'.ofNat (2 ^ core))
      (componentAdaptiveEntropyAnchorRatio ^ exterior)
      (componentCoreCompletionResidualEntropyFactor ^ core)
  refine Q'.eqv_trans _
    ((Q'.ofNat 2 * componentAdaptiveEntropyAnchorRatio) ^ exterior *
      (Q'.ofNat (2 ^ core) *
        componentCoreCompletionResidualEntropyFactor ^ core)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_pow_mul 2 componentAdaptiveEntropyAnchorRatio exterior)
  exact Q'.mul_eqv_congr_left _ _ _
    (ofNat_pow_mul 2 componentCoreCompletionResidualEntropyFactor core)

/-! ## 2. One fixed block-mass profile -/

private theorem listQSum_le_fixed_cardinality_coefficient
    {A : Type} (items : List A) (weight : A -> Q')
    (cardinality : Nat) (coefficient targetWeight : Q')
    (hcardinality : items.length <= cardinality)
    (hcoefficient : (0 : Q') <= coefficient)
    (htarget : (0 : Q') <= targetWeight)
    (hpointwise : forall item, item ∈ items ->
      weight item <= coefficient * targetWeight) :
    listQSum weight items <=
      (Q'.ofNat cardinality * coefficient) * targetWeight := by
  have hbound : (0 : Q') <= coefficient * targetWeight :=
    Q'.mul_nonneg _ _ hcoefficient htarget
  have hsum := listQSum_le_length_mul weight hbound items hpointwise
  have hcardinalityQ :
      Q'.ofNat items.length <= Q'.ofNat cardinality :=
    Q'.ofNat_le_ofNat hcardinality
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    hcardinalityQ hbound
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat cardinality) coefficient targetWeight))))

/-- **Fixed high-spin block-profile inverse-fiber estimate.**  Every ordered
root/replica signature and positive peel-size composition with the prescribed
block masses is summed at arbitrary rational `0 < coupling < 1`. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalBlockProfileCounters_weight_sum_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faces : List Nat) (hnodup : faces.Nodup)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (profile : List Nat)
    (exterior core : Nat)
    (hprofileMass : natListSum profile = exterior + core)
    (sources : List (SlabAcceptedTwoReplicaState D))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).1 = terminal)
    (hprofile : forall source, source ∈ sources ->
      slabAcceptedPairedPeelTraceRankMassProfile faces
          (slabAcceptedPairCanonicalPeeling
            D faces hphysical source).2 (2 * faces.length) = profile)
    (hexterior : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.2.1 = exterior)
    (hcore : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.2.2 = core) :
    listQSum (slabAcceptedTwoReplicaStateWeight D) sources <=
      (pairedHighSpinProfileExteriorRate ^ exterior *
          pairedHighSpinProfileCoreFactor ^ core) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
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
  have htargetsLength : targets.length <= 2 ^ (exterior + core) := by
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
    (slabAcceptedTwoReplicaStateWeight D)
    codeOf targets htargetsNodup hcoverage
  have hfiber : forall code, code ∈ targets ->
      fiberWeight sources (slabAcceptedTwoReplicaStateWeight D)
          codeOf code <=
        (componentAdaptiveEntropyAnchorRatio ^ exterior *
            componentCoreCompletionResidualEntropyFactor ^ core) *
          slabAcceptedTwoReplicaStateWeight D terminal := by
    intro code hcode
    have hmapped := List.mem_eraseDups.mp hcode
    obtain ⟨representative, hrepresentative, hrepresentativeCode⟩ :=
      List.mem_map.mp hmapped
    let representativeSkeleton :=
      (traceOf representative).map SlabAcceptedPairedPeelRecord.skeleton
    unfold fiberWeight
    apply
      slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_weight_sum_le
        D hw0 hw1 faces hphysical terminal representativeSkeleton
          exterior core
          (sources.filter fun source => decide (code = codeOf source))
          (List.filter_sublist.nodup hsources)
    · intro source hsource
      exact hterminal source (List.mem_filter.mp hsource).1
    · intro source hsource
      have hsourceMem := (List.mem_filter.mp hsource).1
      have hcodeEq : code = codeOf source :=
        of_decide_eq_true (List.mem_filter.mp hsource).2
      have hcodePair : codeOf representative = codeOf source :=
        hrepresentativeCode.trans hcodeEq
      have hskeleton :=
        slabAcceptedPairCanonicalPeeling_skeleton_eq_of_rankBlockCode_eq
          D faces hnodup hphysical representative source hcodePair
      have hforget :=
        slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
          D (anchorPaidExteriorThreshold D.coupling)
            faces hphysical source
      have htraceEq := congrArg Prod.snd hforget
      calc
        (slabAcceptedPairCanonicalHighSpinProfile D
              (anchorPaidExteriorThreshold D.coupling)
                faces hphysical source).2.1.map
            SlabAcceptedPairedPeelRecord.skeleton =
          (traceOf source).map
            SlabAcceptedPairedPeelRecord.skeleton := by
              exact congrArg
                (List.map SlabAcceptedPairedPeelRecord.skeleton) htraceEq
        _ = representativeSkeleton := hskeleton.symm
    · intro source hsource
      exact hexterior source (List.mem_filter.mp hsource).1
    · intro source hsource
      exact hcore source (List.mem_filter.mp hsource).1
    · unfold representativeSkeleton
      rw [slabAcceptedPairedPeelTrace_skeletonMass]
      unfold traceOf
      have hforget :=
        slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
          D (anchorPaidExteriorThreshold D.coupling)
            faces hphysical representative
      have htraceEq := congrArg Prod.snd hforget
      rw [← htraceEq]
      rw [slabAcceptedPairCanonicalHighSpinProfile_traceMass]
      rw [hexterior representative hrepresentative,
        hcore representative hrepresentative]
  let coefficient :=
    componentAdaptiveEntropyAnchorRatio ^ exterior *
      componentCoreCompletionResidualEntropyFactor ^ core
  let terminalWeight := slabAcceptedTwoReplicaStateWeight D terminal
  have hcoefficientNonnegative : (0 : Q') <= coefficient := by
    unfold coefficient
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio
        (by decide) exterior)
      (Q'.pow_nonneg componentCoreCompletionResidualEntropyFactor
        (by
          unfold componentCoreCompletionResidualEntropyFactor
          decide) core)
  have hsum := listQSum_le_fixed_cardinality_coefficient targets
    (fiberWeight sources (slabAcceptedTwoReplicaStateWeight D) codeOf)
    (2 ^ (exterior + core)) coefficient terminalWeight
    htargetsLength hcoefficientNonnegative
    (slabAcceptedTwoReplicaStateWeight_nonnegative D terminal)
    (by
      intro code hcode
      exact hfiber code hcode)
  have hcounted :=
    pairedHighSpinBlockProfileCountedRate_eqv exterior core
  have hcountedScaled :=
    Q'.mul_eqv_congr_right _ _ terminalWeight hcounted
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcountedScaled))

#print axioms pairedHighSpinProfileExteriorRate_eqv
#print axioms pairedHighSpinProfileExteriorRate_lt_one
#print axioms pairedHighSpinBlockProfileCountedRate_eqv
#print axioms slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalBlockProfileCounters_weight_sum_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinBlockProfileWeight
