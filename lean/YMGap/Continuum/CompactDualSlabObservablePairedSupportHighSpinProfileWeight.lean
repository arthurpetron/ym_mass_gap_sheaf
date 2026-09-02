/-
# Arbitrary-coupling inverse fibers for observable target-support peeling

The source-independent observable entropy code already injects every fixed
canonical terminal/trace-mass fiber into a carrier of size `20480000^M`.
This module feeds the new exterior/core profile into that stronger global
carrier.  For fixed terminal and aggregate counters, all physical shapes,
spin values, active auxiliary rows, adaptive words, signatures, and peel-size
compositions are therefore summed at the exact rate

  (16/25)^exterior * 40960000^core.

The core exponent is bounded by the initial threshold-truncated mass and hence
by `2 * faceCount * threshold`, independently of representation cutoff.  The
next layer is finite Fubini over the realized core counters and total masses.

Constructive contract: the existing explicit global code, the profiled
well-founded peel, and exact rational arithmetic only; no choice, `Classical`,
`sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinBlockProfileWeight
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.SU3CharFactor
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingFiniteCoreMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Profile the literal observable target-support path -/

/-- The arbitrary-coupling high-spin profile on the same deterministic
target-support component used by the existing observable entropy code. -/
def slabObservablePairTargetSupportCanonicalHighSpinProfile
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    SlabAcceptedPairedHighSpinProfileOutput D :=
  slabAcceptedPairCanonicalHighSpinProfile D
    (anchorPaidExteriorThreshold D.coupling)
    (slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)
    (fun faceId hface =>
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget pair hpair faceId hface)
    (slabObservableTwoReplicaPairToAcceptedState pair)

/-- Forgetting the counters recovers the literal canonical observable
terminal and trace used by the global entropy code. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let result := slabObservablePairTargetSupportCanonicalHighSpinProfile
      D rootFaceId targetFaceId htarget pair hpair
    (result.1, result.2.1) =
      slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget pair hpair := by
  unfold slabObservablePairTargetSupportCanonicalHighSpinProfile
    slabObservablePairTargetSupportCanonicalPeeling
  exact slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
    D (anchorPaidExteriorThreshold D.coupling)
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)

/-- Observable pair weight is definitionally the weight of its accepted-state
embedding at every coupling. -/
theorem slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight_general
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservableTwoReplicaPairWeight D pair =
      slabAcceptedTwoReplicaStateWeight D
        (slabObservableTwoReplicaPairToAcceptedState pair) := by
  rfl

/-- Every target-support profile has a representation-cutoff-independent
core ceiling. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_core_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let result := slabObservablePairTargetSupportCanonicalHighSpinProfile
      D rootFaceId targetFaceId htarget pair hpair
    result.2.2.2 <=
      2 * D.faceEdges.length *
        anchorPaidExteriorThreshold D.coupling := by
  let faces := slabTwoReplicaTargetSupportComponent D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId
  let hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent := fun faceId hface =>
    slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
      D rootFaceId targetFaceId htarget pair hpair faceId hface
  have hcore := slabAcceptedPairCanonicalHighSpinProfile_core_le_initial
    D (anchorPaidExteriorThreshold D.coupling) faces hphysical
      (slabObservableTwoReplicaPairToAcceptedState pair)
  have hinitial := slabAcceptedTwoReplicaThresholdCoreMass_le
    D (anchorPaidExteriorThreshold D.coupling)
      (slabObservableTwoReplicaPairToAcceptedState pair)
  exact Nat.le_trans hcore hinitial

/-- Pointwise arbitrary-coupling payment on the literal observable
target-support path. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    let result := slabObservablePairTargetSupportCanonicalHighSpinProfile
      D rootFaceId targetFaceId htarget pair hpair
    slabObservableTwoReplicaPairWeight D pair <=
      (anchorFaceCoefficient ^ result.2.2.1 *
          (Q'.ofNat 2) ^ result.2.2.2) *
        slabAcceptedTwoReplicaStateWeight D result.1 := by
  rw [slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight_general]
  unfold slabObservablePairTargetSupportCanonicalHighSpinProfile
  exact slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
    D hw0 hw1
      (slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          D rootFaceId targetFaceId htarget pair hpair faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState pair)

/-! ## 2. Exact globally counted two-rate coefficient -/

/-- Core factor after the complete observable entropy carrier has been
counted. -/
def slabObservablePairedGlobalCoreFactor : Q' :=
  Q'.ofNat slabObservablePairedGlobalEntropyBase * Q'.ofNat 2

/-- Raw global carrier count multiplied by the profiled pointwise rate. -/
def slabObservablePairedGlobalHighSpinCountedRate
    (exterior core : Nat) : Q' :=
  Q'.ofNat
      (slabObservablePairedGlobalEntropyBase ^ (exterior + core)) *
    (anchorFaceCoefficient ^ exterior * (Q'.ofNat 2) ^ core)

theorem slabObservablePairedGlobalHighSpinCountedRate_eqv
    (exterior core : Nat) :
    slabObservablePairedGlobalHighSpinCountedRate exterior core ≈
      slabObservablePairedGlobalEntropyAnchorRatio ^ exterior *
        slabObservablePairedGlobalCoreFactor ^ core := by
  unfold slabObservablePairedGlobalHighSpinCountedRate
    slabObservablePairedGlobalEntropyAnchorRatio
    slabObservablePairedGlobalCoreFactor
  rw [Nat.pow_add]
  refine Q'.eqv_trans _
    ((Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ exterior) *
        Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ core)) *
      (anchorFaceCoefficient ^ exterior * (Q'.ofNat 2) ^ core)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv
        (slabObservablePairedGlobalEntropyBase ^ exterior)
        (slabObservablePairedGlobalEntropyBase ^ core))
  refine Q'.eqv_trans _
    ((Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ exterior) *
        anchorFaceCoefficient ^ exterior) *
      (Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ core) *
        (Q'.ofNat 2) ^ core)) _ ?_ ?_
  · exact mul_four_mid'
      (Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ exterior))
      (Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ core))
      (anchorFaceCoefficient ^ exterior) ((Q'.ofNat 2) ^ core)
  refine Q'.eqv_trans _
    ((Q'.ofNat slabObservablePairedGlobalEntropyBase *
        anchorFaceCoefficient) ^ exterior *
      (Q'.ofNat (slabObservablePairedGlobalEntropyBase ^ core) *
        (Q'.ofNat 2) ^ core)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_pow_mul slabObservablePairedGlobalEntropyBase
        anchorFaceCoefficient exterior)
  exact Q'.mul_eqv_congr_left _ _ _
    (ofNat_pow_mul slabObservablePairedGlobalEntropyBase
      (Q'.ofNat 2) core)

/-! ## 3. Sum the complete fixed profile fiber -/

/-- The global observable entropy carrier bounds a fixed profiled terminal
and exterior/core counter fiber. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_length_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (exterior core : Nat)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hexterior : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).2.2.1 = exterior)
    (hcore : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).2.2.2 = core) :
    sources.length <=
      slabObservablePairedGlobalEntropyBase ^ (exterior + core) := by
  apply
    slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_length_le
      D rootFaceId targetFaceId (exterior + core) htarget terminal
        sources hsources
  · intro source hsource
    have hforget :=
      slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
        D rootFaceId targetFaceId htarget source.1 source.2
    have hterminalEq := congrArg Prod.fst hforget
    exact hterminalEq.symm.trans (hterminal source hsource)
  · intro source hsource
    have hforget :=
      slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
        D rootFaceId targetFaceId htarget source.1 source.2
    have htraceEq := congrArg Prod.snd hforget
    rw [← htraceEq]
    change slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalHighSpinProfile
          D rootFaceId targetFaceId htarget source.1 source.2).2.1 =
      exterior + core
    have hprofileMass :
        slabAcceptedPairedPeelTraceMass
            (slabObservablePairTargetSupportCanonicalHighSpinProfile
              D rootFaceId targetFaceId htarget source.1 source.2).2.1 =
          (slabObservablePairTargetSupportCanonicalHighSpinProfile
              D rootFaceId targetFaceId htarget source.1 source.2).2.2.1 +
            (slabObservablePairTargetSupportCanonicalHighSpinProfile
              D rootFaceId targetFaceId htarget source.1 source.2).2.2.2 := by
      unfold slabObservablePairTargetSupportCanonicalHighSpinProfile
      exact slabAcceptedPairCanonicalHighSpinProfile_traceMass
        D (anchorPaidExteriorThreshold D.coupling)
          (slabTwoReplicaTargetSupportComponent D.extent
            source.1.1.1.1 source.1.2.1.1 targetFaceId)
          (fun faceId hface =>
            slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
              D rootFaceId targetFaceId htarget source.1 source.2
                faceId hface)
          (slabObservableTwoReplicaPairToAcceptedState source.1)
    rw [hprofileMass, hexterior source hsource, hcore source hsource]

/-- Specialize the pointwise profile to displayed aggregate counters and a
displayed terminal before entering finite-sum elaboration. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_of_counters
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (terminal : SlabAcceptedTwoReplicaState D)
    (exterior core : Nat)
    (hterminal :
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget pair hpair).1 = terminal)
    (hexterior :
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget pair hpair).2.2.1 = exterior)
    (hcore :
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget pair hpair).2.2.2 = core) :
    slabObservableTwoReplicaPairWeight D pair <=
      (anchorFaceCoefficient ^ exterior * (Q'.ofNat 2) ^ core) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  have hweight :=
    slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le
      D hw0 hw1 rootFaceId targetFaceId htarget pair hpair
  dsimp only at hweight
  rw [hexterior, hcore, hterminal] at hweight
  exact hweight

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

/-- **Complete fixed-profile observable inverse-fiber estimate at arbitrary
coupling.**  The literal source-pair mass includes all physical and auxiliary
assignment multiplicities represented by the global entropy carrier. -/
theorem slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_weight_sum_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (exterior core : Nat)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hexterior : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).2.2.1 = exterior)
    (hcore : forall source, source ∈ sources ->
      (slabObservablePairTargetSupportCanonicalHighSpinProfile
        D rootFaceId targetFaceId htarget source.1 source.2).2.2.2 = core) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        sources <=
      (slabObservablePairedGlobalEntropyAnchorRatio ^ exterior *
          slabObservablePairedGlobalCoreFactor ^ core) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  let coefficient :=
    anchorFaceCoefficient ^ exterior * (Q'.ofNat 2) ^ core
  let terminalWeight := slabAcceptedTwoReplicaStateWeight D terminal
  have hcardinality :=
    slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_length_le
      D rootFaceId targetFaceId htarget terminal exterior core
        sources hsources hterminal hexterior hcore
  have hcoefficientNonnegative : (0 : Q') <= coefficient := by
    unfold coefficient
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorFaceCoefficient (by decide) exterior)
      (Q'.pow_nonneg (Q'.ofNat 2) (by decide) core)
  have hterminalNonnegative : (0 : Q') <= terminalWeight :=
    slabAcceptedTwoReplicaStateWeight_nonnegative D terminal
  have hpointwise : forall source, source ∈ sources ->
      slabObservableTwoReplicaPairWeight D source.1 <=
        coefficient * terminalWeight := by
    intro source hsource
    unfold coefficient terminalWeight
    exact
      slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_of_counters
        D hw0 hw1 rootFaceId targetFaceId htarget source.1 source.2
          terminal exterior core (hterminal source hsource)
          (hexterior source hsource) (hcore source hsource)
  have hraw :
      listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          sources <=
        slabObservablePairedGlobalHighSpinCountedRate exterior core *
          terminalWeight := by
    have hsum := listQSum_le_fixed_cardinality_coefficient sources
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedGlobalEntropyBase ^ (exterior + core))
      coefficient terminalWeight hcardinality hcoefficientNonnegative
      hterminalNonnegative hpointwise
    simpa only [slabObservablePairedGlobalHighSpinCountedRate]
      using hsum
  have hrate :=
    slabObservablePairedGlobalHighSpinCountedRate_eqv exterior core
  have hrateScaled := Q'.mul_eqv_congr_right _ _ terminalWeight hrate
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hrateScaled)

#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_terminal_trace
#print axioms slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight_general
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_core_le
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le
#print axioms slabObservablePairedGlobalHighSpinCountedRate_eqv
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_length_le
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_sourceWeight_le_of_counters
#print axioms slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalCounters_weight_sum_le

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
