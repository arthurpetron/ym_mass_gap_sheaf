/-
# Exact finite weighted fiber floor for guard peeling

Canonical target-component peeling and fixed-guard peeling are distinct
endomaps.  The guarded graft recovers only the output of the second map, so a
correct repair argument must pay for the complete inverse fiber of that guard
peeling rather than silently identify its input and output terminals.

At the cutoff-one, half-two production anchor every accepted state has
strictly positive exact weight.  Specializing the generic finite positive
endomap theorem therefore constructs an explicit rate `guardFiberRate` with

  0 < guardFiberRate <= 1,
  guardFiberRate * weight(all states peeling to terminal) <= weight(terminal).

The rate is computed from the complete finite accepted-state carrier.  No
uniformity in cutoff, volume, coupling, or spacing is claimed.

Constructive contract: the accepted-state enumeration, exact positive anchor
weights, executable guard peeling, and finite positive weighted-fiber theorem
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling

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

/-! ## 1. The literal finite guard-peeling endomap -/

abbrev reflectedBentGuardAnchorData : SlabPhysicalData :=
  anchorSlabPhysicalData 1 2

/-- Terminal returned by clearing the fixed reflected guard at the production
anchor. -/
def reflectedBentGuardAnchorTerminal
    (state : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData :=
  (reflectedBentGuardCanonicalPeeling
    reflectedBentGuardAnchorData (by decide) state).1

/-- Every accepted anchor state has strictly positive exact pair weight. -/
theorem reflectedBentGuardAnchorStateWeight_pos
    (state : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    (0 : Q') < slabAcceptedTwoReplicaStateWeight 1 2 state := by
  unfold slabAcceptedTwoReplicaStateWeight
  exact Q'.mul_pos
    (slabExpandedFineEntryWeight_pos_of_coupling_pos
      reflectedBentGuardAnchorData (by decide) state.1)
    (slabExpandedFineEntryWeight_pos_of_coupling_pos
      reflectedBentGuardAnchorData (by decide) state.2)

/-! ## 2. Explicit common inverse-fiber rate -/

/-- Capped finite minimum of exact terminal-weight / guard-fiber-weight
ratios. -/
def reflectedBentGuardPeelingFiberRate : Q' :=
  finitePositiveEndomapFiberRate
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    reflectedBentGuardAnchorStateWeight_pos
    reflectedBentGuardAnchorTerminal

theorem reflectedBentGuardPeelingFiberRate_pos :
    (0 : Q') < reflectedBentGuardPeelingFiberRate :=
  finitePositiveEndomapFiberRate_pos
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    reflectedBentGuardAnchorStateWeight_pos
    reflectedBentGuardAnchorTerminal

theorem reflectedBentGuardPeelingFiberRate_le_one :
    reflectedBentGuardPeelingFiberRate ≤ (1 : Q') :=
  finitePositiveEndomapFiberRate_le_one
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    reflectedBentGuardAnchorStateWeight_pos
    reflectedBentGuardAnchorTerminal

/-- **Second-stage terminal-fiber estimate.**  The complete accepted-state
inverse fiber of one guard-cleared terminal is paid by the explicit common
finite rate. -/
theorem reflectedBentGuardPeelingFiberRate_mul_fiberWeight_le
    (terminal : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    reflectedBentGuardPeelingFiberRate *
        fiberWeight
          (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
          (slabAcceptedTwoReplicaStateWeight 1 2)
          reflectedBentGuardAnchorTerminal terminal ≤
      slabAcceptedTwoReplicaStateWeight 1 2 terminal :=
  finitePositiveEndomapFiberRate_mul_fiberWeight_le
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    reflectedBentGuardAnchorStateWeight_pos
    reflectedBentGuardAnchorTerminal terminal
    (slabAcceptedTwoReplicaState_mem reflectedBentGuardAnchorData terminal)

#print axioms reflectedBentGuardAnchorStateWeight_pos
#print axioms reflectedBentGuardPeelingFiberRate_pos
#print axioms reflectedBentGuardPeelingFiberRate_le_one
#print axioms reflectedBentGuardPeelingFiberRate_mul_fiberWeight_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor
