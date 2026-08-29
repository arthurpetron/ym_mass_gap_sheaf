/-
# The reflected channel's two-stage terminal fiber

The canonical target-component peeler and the fixed-guard peeler must be
composed rather than identified.  This module performs that composition on
the production anchor:

```text
connected source -> target-component terminal -> guard-cleared terminal.
```

Finite weighted-fiber composition transports the already proved global
Peierls terminal estimate through guard peeling.  Multiplying by the exact
finite guard-fiber rate then pays the complete inverse fiber of the composite
terminal map by the weight of its final guard-cleared terminal.

The resulting coefficient is explicit but is only a fixed finite-anchor
coefficient: no uniformity in cutoff, volume, coupling, or spacing is
claimed.

Constructive contract: exact finite fibers and previously proved rational
weight estimates only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
import YMGap.Continuum.FiniteWeightedFiberComposition
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCompositeTerminalFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingGoodSourceFiberRepair
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedFiberComposition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeelingFiniteFiberFloor

local infix:50 " ≈ " => Q'.eqv

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

/-! ## 1. The honest composite terminal map -/

/-- First peel the marked target component, then clear the reflected guard. -/
def reflectedBentGuardCompositeTerminal
    (source : SlabObservablePairedConnectedStrandSource
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId) :
    SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData :=
  reflectedBentGuardAnchorTerminal
    (slabObservablePairedConnectedCanonicalTerminal
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId reflectedBentTargetFaceId_physical source)

/-! ## 2. Composition of the complete weighted fibers -/

/-- Canonical peeling's global amplification survives deterministic guard
peeling.  The right side is the *complete* guard-peeling inverse fiber, not
one arbitrarily selected canonical terminal. -/
theorem reflectedBentGuardCompositeTerminal_fiberWeight_le
    (terminal : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    fiberWeight
        (slabObservablePairedConnectedStrandSources
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId)
        (fun source =>
          slabObservableTwoReplicaPairWeight
            reflectedBentGuardAnchorData source.1)
        reflectedBentGuardCompositeTerminal terminal ≤
      slabObservablePairedSupportGlobalAnchorRate
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId *
        fiberWeight
          (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
          (slabAcceptedTwoReplicaStateWeight 1 2)
          reflectedBentGuardAnchorTerminal terminal := by
  apply fiberWeight_comp_le_factor_mul
    (slabObservablePairedConnectedStrandSources
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (fun source =>
      slabObservableTwoReplicaPairWeight
        reflectedBentGuardAnchorData source.1)
    (slabObservablePairedConnectedCanonicalTerminal
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId reflectedBentTargetFaceId_physical)
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStates_nodup reflectedBentGuardAnchorData)
    (fun source _ => slabAcceptedTwoReplicaState_mem _ _)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    (slabObservablePairedSupportGlobalAnchorRate
      reflectedBentGuardAnchorData reflectedBentRootFaceId
        reflectedBentTargetFaceId)
    (fun middle _ =>
      slabObservablePairedConnectedCanonicalTerminal_fiberWeight_le
        1 2 reflectedBentRootFaceId reflectedBentTargetFaceId
        reflectedBentTargetFaceId_physical middle)
    reflectedBentGuardAnchorTerminal terminal

/-! ## 3. Pay both inverse fibers -/

private theorem reflectedBentGlobalAnchorRate_nonnegative :
    (0 : Q') ≤
      slabObservablePairedSupportGlobalAnchorRate
        reflectedBentGuardAnchorData reflectedBentRootFaceId
          reflectedBentTargetFaceId := by
  unfold slabObservablePairedSupportGlobalAnchorRate
  apply Q'.mul_nonneg
  · decide
  · apply Q'.pow_nonneg
    unfold slabObservablePairedGlobalEntropyAnchorRatio
    exact Q'.mul_nonneg _ _ (by decide) (by decide)

private theorem guard_global_reassociate
    (guard global load : Q') :
    guard * (global * load) ≈ global * (guard * load) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv guard global load)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ load (Q'.mul_comm_eqv guard global)) ?_
  exact Q'.mul_assoc_eqv global guard load

/-- **Two-stage reflected terminal-fiber estimate.**  The product of the
finite guard-fiber rate and the complete composite source fiber is bounded by
the final guard-cleared terminal weight, up to the already proved global
Peierls rate. -/
theorem reflectedBentGuardPeelingFiberRate_mul_compositeFiberWeight_le
    (terminal : SlabAcceptedTwoReplicaState reflectedBentGuardAnchorData) :
    reflectedBentGuardPeelingFiberRate *
        fiberWeight
          (slabObservablePairedConnectedStrandSources
            reflectedBentGuardAnchorData reflectedBentRootFaceId
              reflectedBentTargetFaceId)
          (fun source =>
            slabObservableTwoReplicaPairWeight
              reflectedBentGuardAnchorData source.1)
          reflectedBentGuardCompositeTerminal terminal ≤
      slabObservablePairedSupportGlobalAnchorRate
          reflectedBentGuardAnchorData reflectedBentRootFaceId
            reflectedBentTargetFaceId *
        slabAcceptedTwoReplicaStateWeight 1 2 terminal := by
  let global := slabObservablePairedSupportGlobalAnchorRate
    reflectedBentGuardAnchorData reflectedBentRootFaceId
      reflectedBentTargetFaceId
  let guardLoad := fiberWeight
    (slabAcceptedTwoReplicaStates reflectedBentGuardAnchorData)
    (slabAcceptedTwoReplicaStateWeight 1 2)
    reflectedBentGuardAnchorTerminal terminal
  have hcomposite :=
    reflectedBentGuardCompositeTerminal_fiberWeight_le terminal
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    reflectedBentGuardPeelingFiberRate hcomposite
    (Q'.le_of_lt reflectedBentGuardPeelingFiberRate_pos)
  have hguard :=
    reflectedBentGuardPeelingFiberRate_mul_fiberWeight_le terminal
  have hguardScaled := Q'.mul_le_mul_of_nonneg_left _ _ global hguard
    reflectedBentGlobalAnchorRate_nonnegative
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (guard_global_reassociate
          reflectedBentGuardPeelingFiberRate global guardLoad))
      hguardScaled)

#print axioms reflectedBentGuardCompositeTerminal_fiberWeight_le
#print axioms reflectedBentGuardPeelingFiberRate_mul_compositeFiberWeight_le

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardCompositeTerminalFiber
