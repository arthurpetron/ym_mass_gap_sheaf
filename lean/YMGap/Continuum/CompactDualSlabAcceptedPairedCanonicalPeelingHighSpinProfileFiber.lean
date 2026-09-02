/-
# A counted fixed fiber of complete profiled accepted peeling

Fix the accepted terminal, erased adaptive trace skeleton, and the total
high-spin exterior/core counters of the complete canonical path.  Forgetting
the counters recovers the already-injective canonical terminal/trace output,
so the existing dependent adaptive carrier bounds this source family by

  componentAdaptiveEntropyBase^(exterior + core).

The arbitrary-coupling pointwise profile then gives the exact counted rate

  (8/25)^exterior * (2 * componentAdaptiveEntropyBase)^core.

This is the first complete-path inverse-fiber theorem at arbitrary positive
coupling.  It fixes the whole trace skeleton and both aggregate counters;
summing size words, signatures, and block profiles is the subsequent layer.

Constructive contract: finite lists, the existing explicit trace injection,
and exact rational arithmetic only; no choice, `Classical`, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfileFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingTraceCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reuse the complete canonical trace carrier -/

/-- At fixed profiled terminal, trace skeleton, and aggregate exterior/core
counters, the duplicate-free source family injects into the old dependent
adaptive trace carrier. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_length_le
    (D : SlabPhysicalData)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (skeletons : List SlabAcceptedPairedPeelSkeleton)
    (exterior core : Nat)
    (sources : List (SlabAcceptedTwoReplicaState D))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).1 = terminal)
    (hskeleton : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.1.map
            SlabAcceptedPairedPeelRecord.skeleton = skeletons)
    (hmass : slabAcceptedPairedPeelSkeletonMass skeletons =
      exterior + core) :
    sources.length <=
      componentAdaptiveEntropyBase ^ (exterior + core) := by
  have hcanonicalTerminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical source).1 = terminal := by
    intro source hsource
    have hforget :=
      slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
        D (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source
    have hterminalEq := congrArg Prod.fst hforget
    exact hterminalEq.symm.trans (hterminal source hsource)
  have hcanonicalSkeleton : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalPeeling
        D faces hphysical source).2.map
          SlabAcceptedPairedPeelRecord.skeleton = skeletons := by
    intro source hsource
    have hforget :=
      slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
        D (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source
    have htraceEq := congrArg Prod.snd hforget
    rw [← htraceEq]
    exact hskeleton source hsource
  have hbound :=
    slabAcceptedPairCanonicalPeeling_fixedTerminalSkeleton_length_le
      D faces hphysical terminal skeletons sources hsources
        hcanonicalTerminal hcanonicalSkeleton
  rw [hmass] at hbound
  exact hbound

/-! ## 2. Count the arbitrary-coupling two-rate pointwise estimate -/

/-- **Fixed profiled inverse-fiber estimate.**  After adaptive-code counting,
every paid exterior copy costs the strict `8/25` rate and every residual-core
copy costs the explicit finite factor
`2 * componentAdaptiveEntropyBase`. -/
theorem slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_weight_sum_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (skeletons : List SlabAcceptedPairedPeelSkeleton)
    (exterior core : Nat)
    (sources : List (SlabAcceptedTwoReplicaState D))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).1 = terminal)
    (hskeleton : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.1.map
            SlabAcceptedPairedPeelRecord.skeleton = skeletons)
    (hexterior : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.2.1 = exterior)
    (hcore : forall source, source ∈ sources ->
      (slabAcceptedPairCanonicalHighSpinProfile D
        (anchorPaidExteriorThreshold D.coupling)
          faces hphysical source).2.2.2 = core)
    (hmass : slabAcceptedPairedPeelSkeletonMass skeletons =
      exterior + core) :
    listQSum (slabAcceptedTwoReplicaStateWeight D) sources <=
      (componentAdaptiveEntropyAnchorRatio ^ exterior *
          componentCoreCompletionResidualEntropyFactor ^ core) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  let coefficient :=
    anchorFaceCoefficient ^ exterior * (Q'.ofNat 2) ^ core
  let terminalWeight := slabAcceptedTwoReplicaStateWeight D terminal
  have hcardinality :=
    slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_length_le
      D faces hphysical terminal skeletons exterior core sources hsources
        hterminal hskeleton hmass
  have hcoefficientNonnegative : (0 : Q') <= coefficient := by
    unfold coefficient
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorFaceCoefficient (by decide) exterior)
      (Q'.pow_nonneg (Q'.ofNat 2) (by decide) core)
  have hterminalNonnegative : (0 : Q') <= terminalWeight := by
    exact slabAcceptedTwoReplicaStateWeight_nonnegative D terminal
  have hboundNonnegative : (0 : Q') <= coefficient * terminalWeight :=
    Q'.mul_nonneg _ _ hcoefficientNonnegative hterminalNonnegative
  have hpointwise : forall source, source ∈ sources ->
      slabAcceptedTwoReplicaStateWeight D source <=
        coefficient * terminalWeight := by
    intro source hsource
    have hweight :=
      slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
        D hw0 hw1 faces hphysical source
    dsimp only at hweight
    rw [hexterior source hsource, hcore source hsource,
      hterminal source hsource] at hweight
    exact hweight
  have hsum := listQSum_le_length_mul
    (slabAcceptedTwoReplicaStateWeight D) hboundNonnegative
      sources hpointwise
  have hcardinalityQ :
      Q'.ofNat sources.length <=
        Q'.ofNat (componentAdaptiveEntropyBase ^ (exterior + core)) :=
    Q'.ofNat_le_ofNat hcardinality
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ _
    hcardinalityQ hboundNonnegative
  have hraw :
      listQSum (slabAcceptedTwoReplicaStateWeight D) sources <=
        componentCoreCompletionCountedRate exterior core *
          terminalWeight := by
    refine Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ hscale ?_)
    unfold componentCoreCompletionCountedRate
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (Q'.ofNat
            (componentAdaptiveEntropyBase ^ (exterior + core)))
          coefficient terminalWeight))
  have hrate := componentCoreCompletionCountedRate_eqv exterior core
  have hscaledRate := Q'.mul_eqv_congr_right _ _ terminalWeight hrate
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hscaledRate)

#print axioms slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_length_le
#print axioms slabAcceptedPairCanonicalHighSpinProfile_fixedTerminalSkeletonCounters_weight_sum_le

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfileFiber
