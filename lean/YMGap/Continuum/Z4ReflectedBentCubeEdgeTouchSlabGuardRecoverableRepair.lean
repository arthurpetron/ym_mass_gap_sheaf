/-
# Recoverable guarded repair before success packaging

For each connected source, first take its canonical target-component terminal
and then graft the fixed reflected channel after guard clearing.  Equality of
two resulting connected receivers recovers equality of their guard-cleared
composite terminals.  The two-stage terminal-fiber estimate and the exact
insertion floor therefore give a complete weighted inverse-fiber bound for
this literal receiver map.

This module intentionally stops before declaring the receivers recoupling-
good: the remaining successful-choice construction is a separate dependent
SU(2) obligation.  The weighted repair mathematics does not depend on that
compiler.

Constructive contract: exact finite fibers, terminal recoverability, and
rational heat weights only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteWeightedRecoverableRepair
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCompositeTerminalFiber
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardRecoverableRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedRecoverableRepair
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabGlobalRecouplingWitnessRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCompositeTerminalFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverability

local instance guardRepairPairDecidableEq :
    DecidableEq (SlabObservableTwoReplicaPair
      reflectedBentGuardAnchorData reflectedBentRootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq
    reflectedBentGuardAnchorData reflectedBentRootFaceId

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

/-! ## 1. The literal connected receiver map -/

/-- The canonical terminal before its second, guard-clearing pass. -/
def reflectedBentGuardRepairCanonicalState
    (source : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData :=
  slabObservablePairedConnectedCanonicalTerminal
    reflectedBentGuardAnchorData reflectedBentRootFaceId
      reflectedBentTargetFaceId reflectedBentTargetFaceId_physical source

/-- Graft the fixed reflected channel into the canonically reached state. -/
def reflectedBentGuardConnectedRepair
    (source : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId :=
  reflectedBentGuardGraftConnectedStrandSource
    reflectedBentGuardAnchorData (by decide) (by decide)
      (reflectedBentGuardRepairCanonicalState source)

/-! ## 2. Receiver equality recovers the composite code -/

private theorem acceptedGraft_eq_of_connectedRepair_eq
    (first second : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (heq : reflectedBentGuardConnectedRepair first =
      reflectedBentGuardConnectedRepair second) :
    reflectedBentGuardGraftAcceptedState
        reflectedBentGuardAnchorData (by decide) (by decide)
        (reflectedBentGuardRepairCanonicalState first) =
      reflectedBentGuardGraftAcceptedState
        reflectedBentGuardAnchorData (by decide) (by decide)
        (reflectedBentGuardRepairCanonicalState second) := by
  have hpair := congrArg Subtype.val heq
  apply Prod.ext
  · apply Subtype.ext
    have hleft := congrArg (fun pair => pair.1.1) hpair
    rw [reflectedBentGuardGraftAcceptedState_leftSource,
      reflectedBentGuardGraftAcceptedState_leftSource]
    simpa only [reflectedBentGuardConnectedRepair,
      reflectedBentGuardGraftConnectedStrandSource,
      reflectedBentGuardGraftObservableSourcePair,
      reflectedBentGuardGraftLeftPositiveEntry,
      slabObservablePositiveSourceEntryOfCarrier] using hleft
  · apply Subtype.ext
    have hright := congrArg (fun pair => pair.2.1) hpair
    rw [reflectedBentGuardGraftAcceptedState_rightSource,
      reflectedBentGuardGraftAcceptedState_rightSource]
    simpa only [reflectedBentGuardConnectedRepair,
      reflectedBentGuardGraftConnectedStrandSource,
      reflectedBentGuardGraftObservableSourcePair,
      reflectedBentGuardGraftRightExpandedEntry,
      slabExpandedFineSourceEntryOfCarrier] using hright

theorem reflectedBentGuardConnectedRepair_recovers_compositeTerminal
    (first second : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (heq : reflectedBentGuardConnectedRepair first =
      reflectedBentGuardConnectedRepair second) :
    reflectedBentGuardCompositeTerminal first =
      reflectedBentGuardCompositeTerminal second := by
  exact reflectedBentGuardCanonicalPeeling_terminal_eq_of_graft_eq
    reflectedBentGuardAnchorData (by decide) (by decide)
    (reflectedBentGuardRepairCanonicalState first)
    (reflectedBentGuardRepairCanonicalState second)
    (acceptedGraft_eq_of_connectedRepair_eq first second heq)

/-! ## 3. The complete receiver-fiber estimate -/

theorem reflectedBentGuardConnectedRepair_insertionFloor
    (source : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
        slabAcceptedTwoReplicaStateWeight 1 2
          (reflectedBentGuardCompositeTerminal source) ≤
      slabObservableTwoReplicaPairWeight reflectedBentGuardAnchorData
        (reflectedBentGuardConnectedRepair source).1 := by
  exact reflectedBentGuardGraftObservableSourcePairWeight_anchor_floor
    (reflectedBentGuardRepairCanonicalState source)

/-- Any positive candidate rate satisfying the one explicit product budget
controls every complete inverse fiber of the literal guarded receiver map. -/
theorem reflectedBentGuardConnectedRepair_fiberWeight_le
    (rho : Q') (rho_nonnegative : (0 : Q') ≤ rho)
    (rate_budget :
      rho * slabObservablePairedSupportGlobalAnchorRate
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId ≤
        reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
          reflectedBentGuardPeelingFiberRate)
    (target : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    rho * fiberWeight
        (slabObservablePairedConnectedStrandSources
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight
          reflectedBentGuardAnchorData source.1)
        reflectedBentGuardConnectedRepair target ≤
      slabObservableTwoReplicaPairWeight
        reflectedBentGuardAnchorData target.1 := by
  exact recoverableRepair_fiberWeight_le
    (slabObservablePairedConnectedStrandSources
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (fun source => slabObservableTwoReplicaPairWeight
      reflectedBentGuardAnchorData source.1)
    (fun source => slabObservableTwoReplicaPairWeight_nonnegative
      reflectedBentGuardAnchorData reflectedBentRootFaceId source.1)
    reflectedBentGuardCompositeTerminal
    (slabAcceptedTwoReplicaStateWeight 1 2)
    (slabAcceptedTwoReplicaStateWeight_nonnegative 1 2)
    reflectedBentGuardConnectedRepair
    (fun receiver => slabObservableTwoReplicaPairWeight
      reflectedBentGuardAnchorData receiver.1)
    (fun receiver => slabObservableTwoReplicaPairWeight_nonnegative
      reflectedBentGuardAnchorData reflectedBentRootFaceId receiver.1)
    reflectedBentGuardPeelingFiberRate
    (slabObservablePairedSupportGlobalAnchorRate
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (reflectedBentGuardInsertionRate reflectedBentGuardAnchorData)
    rho reflectedBentGuardPeelingFiberRate_pos rho_nonnegative
    reflectedBentGuardPeelingFiberRate_mul_compositeFiberWeight_le
    reflectedBentGuardConnectedRepair_recovers_compositeTerminal
    reflectedBentGuardConnectedRepair_insertionFloor rate_budget target

/-! ## 4. An explicit positive anchor repair rate -/

private theorem qpow_pos_local (value : Q')
    (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < value ^ exponent
  | 0 => by
      rw [Q'.pow_zero]
      decide
  | exponent + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hvalue (qpow_pos_local value hvalue exponent)

theorem reflectedBentGlobalAnchorRate_pos :
    (0 : Q') <
      slabObservablePairedSupportGlobalAnchorRate
        reflectedBentGuardAnchorData reflectedBentRootFaceId
          reflectedBentTargetFaceId := by
  unfold slabObservablePairedSupportGlobalAnchorRate
  apply Q'.mul_pos
  · decide
  · apply qpow_pos_local
    unfold slabObservablePairedGlobalEntropyAnchorRatio
    exact Q'.mul_pos (by decide) (by decide)

/-- Uncapped exact ratio of the insertion and guard-fiber payments to the
global terminal-fiber amplification. -/
def reflectedBentGuardConnectedRawRepairRate : Q' :=
  Q'.divPos
    (reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
      reflectedBentGuardPeelingFiberRate)
    (slabObservablePairedSupportGlobalAnchorRate
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    reflectedBentGlobalAnchorRate_pos

theorem reflectedBentGuardConnectedRawRepairRate_pos :
    (0 : Q') < reflectedBentGuardConnectedRawRepairRate := by
  exact Q'.divPos_pos
    (reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
      reflectedBentGuardPeelingFiberRate)
    (slabObservablePairedSupportGlobalAnchorRate
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    reflectedBentGlobalAnchorRate_pos
    (Q'.mul_pos
      (reflectedBentGuardInsertionRate_pos
        reflectedBentGuardAnchorData (by decide) (by decide) (by decide))
      reflectedBentGuardPeelingFiberRate_pos)

/-- The exact repair ratio, capped at one. -/
def reflectedBentGuardConnectedRepairRate : Q' :=
  capAtOne reflectedBentGuardConnectedRawRepairRate

theorem reflectedBentGuardConnectedRepairRate_pos :
    (0 : Q') < reflectedBentGuardConnectedRepairRate := by
  unfold reflectedBentGuardConnectedRepairRate
  exact capAtOne_pos reflectedBentGuardConnectedRawRepairRate_pos

theorem reflectedBentGuardConnectedRepairRate_le_one :
    reflectedBentGuardConnectedRepairRate ≤ (1 : Q') := by
  unfold reflectedBentGuardConnectedRepairRate
  exact capAtOne_le_one _

theorem reflectedBentGuardConnectedRepairRate_budget :
    reflectedBentGuardConnectedRepairRate *
        slabObservablePairedSupportGlobalAnchorRate
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId ≤
      reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
        reflectedBentGuardPeelingFiberRate := by
  let numerator :=
    reflectedBentGuardInsertionRate reflectedBentGuardAnchorData *
      reflectedBentGuardPeelingFiberRate
  let denominator :=
    slabObservablePairedSupportGlobalAnchorRate
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId
  have hcap : reflectedBentGuardConnectedRepairRate ≤
      Q'.divPos numerator denominator reflectedBentGlobalAnchorRate_pos := by
    unfold reflectedBentGuardConnectedRepairRate
      reflectedBentGuardConnectedRawRepairRate
    exact capAtOne_le _
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ denominator hcap
    (Q'.le_of_lt reflectedBentGlobalAnchorRate_pos)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.divPos_mul_eqv numerator denominator
        reflectedBentGlobalAnchorRate_pos))

/-- **Concrete fixed-anchor weighted repair.**  The explicit positive capped
rate controls every complete inverse fiber of the guarded connected receiver
map. -/
theorem reflectedBentGuardConnectedRepairRate_mul_fiberWeight_le
    (target : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    reflectedBentGuardConnectedRepairRate *
        fiberWeight
          (slabObservablePairedConnectedStrandSources
            reflectedBentGuardAnchorData reflectedBentRootFaceId
              reflectedBentTargetFaceId)
          (fun source => slabObservableTwoReplicaPairWeight
            reflectedBentGuardAnchorData source.1)
          reflectedBentGuardConnectedRepair target ≤
      slabObservableTwoReplicaPairWeight
        reflectedBentGuardAnchorData target.1 := by
  exact reflectedBentGuardConnectedRepair_fiberWeight_le
    reflectedBentGuardConnectedRepairRate
    (Q'.le_of_lt reflectedBentGuardConnectedRepairRate_pos)
    reflectedBentGuardConnectedRepairRate_budget target

#print axioms reflectedBentGuardConnectedRepair_recovers_compositeTerminal
#print axioms reflectedBentGuardConnectedRepair_insertionFloor
#print axioms reflectedBentGuardConnectedRepair_fiberWeight_le
#print axioms reflectedBentGlobalAnchorRate_pos
#print axioms reflectedBentGuardConnectedRawRepairRate_pos
#print axioms reflectedBentGuardConnectedRepairRate_pos
#print axioms reflectedBentGuardConnectedRepairRate_le_one
#print axioms reflectedBentGuardConnectedRepairRate_budget
#print axioms reflectedBentGuardConnectedRepairRate_mul_fiberWeight_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardRecoverableRepair
