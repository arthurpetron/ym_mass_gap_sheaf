/-
# Global heat payment for canonically peeled observable pairs

The source-independent aggregate carrier bounds a fixed-terminal,
fixed-trace-mass fiber by `20480000^M`.  Complete canonical peeling pays the
literal anchor factor `32000000^(-M)` for every member of that fiber.  Finite
weighted summation therefore contracts the entire fiber at the exact rate

  (20480000 / 32000000)^M = (16/25)^M.

This is the first global source-fiber estimate: shape, physical values, and
both active auxiliary assignments have all been summed rather than left as a
source-dependent prefactor.  It remains a finite-cutoff theorem at the fixed
production anchor; no all-coupling or continuum conclusion is asserted.

Constructive contract: explicit finite carriers and rational order only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact global strict rate -/

/-- Global paired entropy multiplied by the literal one-face anchor factor. -/
def slabObservablePairedGlobalEntropyAnchorRatio : Q' :=
  Q'.ofNat slabObservablePairedGlobalEntropyBase * anchorFaceCoefficient

theorem slabObservablePairedGlobalEntropyAnchorRatio_eqv :
    slabObservablePairedGlobalEntropyAnchorRatio ≈
      Q'.mkPos 16 25 (by decide) := by
  decide

theorem slabObservablePairedGlobalEntropyAnchorRatio_lt_one :
    slabObservablePairedGlobalEntropyAnchorRatio < (1 : Q') := by
  decide

/-! ## 2. Exact observable/accepted weight identification -/

/-- Forgetting the first replica's root-positivity witness does not change
the literal two-replica source weight. -/
theorem slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight
    (cutoff half rootFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff half) rootFaceId) :
    slabObservableTwoReplicaPairWeight
        (anchorSlabPhysicalData cutoff half) pair =
      slabAcceptedTwoReplicaStateWeight cutoff half
        (slabObservableTwoReplicaPairToAcceptedState pair) := by
  rfl

/-! ## 3. Contract one exact terminal/mass fiber -/

/-- **Global fixed-fiber heat estimate.**  Every duplicate-free family of
attached four-cell source pairs sharing a canonical terminal and exact trace
mass `M` has total literal source weight at most `(16/25)^M` times the terminal
weight. -/
theorem slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_weight_sum_le
    (cutoff half rootFaceId targetFaceId mass : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges
      (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half))
    (sources : List (SlabObservableFourCellPairEntry
      (anchorSlabPhysicalData cutoff half) rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : ∀ source, source ∈ sources →
      (slabObservablePairTargetSupportCanonicalPeeling
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId htarget source.1 source.2).1 = terminal)
    (hmass : ∀ source, source ∈ sources →
      slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget source.1 source.2).2 = mass) :
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff half) source.1)
        sources ≤
      slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  unfold slabObservablePairedGlobalEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact
      slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_length_le
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId mass htarget terminal sources hsources
        hterminal hmass
  · decide
  · exact slabAcceptedTwoReplicaStateWeight_nonnegative
      cutoff half terminal
  · intro source hsource
    have hweight := slabAcceptedPairCanonicalPeeling_sourceWeight_le
      cutoff half
      (slabTwoReplicaTargetSupportComponent
        (anchorSlabPhysicalData cutoff half).extent
        source.1.1.1.1 source.1.2.1.1 targetFaceId)
      (fun faceId hface =>
        slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
          (anchorSlabPhysicalData cutoff half)
          rootFaceId targetFaceId htarget source.1 source.2 faceId hface)
      (slabObservableTwoReplicaPairToAcceptedState source.1)
    change slabAcceptedTwoReplicaStateWeight cutoff half
        (slabObservableTwoReplicaPairToAcceptedState source.1) ≤
      anchorFaceCoefficient ^
          slabAcceptedPairedPeelTraceMass
            (slabObservablePairTargetSupportCanonicalPeeling
              (anchorSlabPhysicalData cutoff half)
              rootFaceId targetFaceId htarget source.1 source.2).2 *
        slabAcceptedTwoReplicaStateWeight cutoff half
          (slabObservablePairTargetSupportCanonicalPeeling
            (anchorSlabPhysicalData cutoff half)
            rootFaceId targetFaceId htarget source.1 source.2).1
      at hweight
    rw [← slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight,
      hmass source hsource, hterminal source hsource] at hweight
    exact hweight

#print axioms slabObservablePairedGlobalEntropyAnchorRatio
#print axioms slabObservablePairedGlobalEntropyAnchorRatio_eqv
#print axioms slabObservablePairedGlobalEntropyAnchorRatio_lt_one
#print axioms slabObservableTwoReplicaPairWeight_eq_acceptedStateWeight
#print axioms slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_weight_sum_le

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
