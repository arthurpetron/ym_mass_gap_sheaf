/-
# BF4 forest-gauge Haar endpoint permutations

This module isolates the two executable 32-block permutations used by the
forest-gauge Haar endpoint.  The finite certificates are intentionally kept
in their own compiled unit so later structural Haar proofs do not repeatedly
reduce the selection program.

## Axiom gate

Finite list computation only.  No `Classical.*`, `native_decide`, `sorry`,
custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeFaceProductBridge

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation

set_option maxRecDepth 300000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeStepCoordinateCheck
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

/-- Swap two target positions in a current source-order table. -/
def swapSourceOrder32 (first second : Nat) (order : List Nat) : List Nat :=
  (List.range 32).map fun target =>
    order.getD
      (if target = first then second
       else if target = second then first
       else target) 0

/-- At most one selection-sort swap per target position.  The validity and
resulting source order used below are independently kernel checked. -/
def selectionRawSwaps32Aux (desired : List Nat) :
    Nat → Nat → List Nat → List RawQuaternionBlockSwap
  | 0, _, _ => []
  | fuel + 1, target, current =>
      if target < 32 then
        let position := current.idxOf (desired.getD target target)
        if position = target then
          selectionRawSwaps32Aux desired fuel (target + 1) current
        else
          ⟨target, position⟩ ::
            selectionRawSwaps32Aux desired fuel (target + 1)
              (swapSourceOrder32 target position current)
      else []

def selectionRawSwaps32 (desired : List Nat) :
    List RawQuaternionBlockSwap :=
  selectionRawSwaps32Aux desired 32 0 (List.range 32)

/-! ## Physical-edge order to active-carrier order -/

def physicalToActiveRawSwaps : List RawQuaternionBlockSwap :=
  selectionRawSwaps32 activeCarrierToCompactEdgeIds

theorem physicalToActiveRawSwaps_valid :
    rawQuaternionBlockSwapsValid 32 physicalToActiveRawSwaps = true := by
  decide

def physicalToActiveSteps : List (QuaternionBlockInvolution 32) :=
  certifyRawQuaternionBlockSwaps physicalToActiveRawSwaps
    physicalToActiveRawSwaps_valid

/-- The fixed permutation sends active target block `i` to the physical edge
stored at position `i` in the literal active-carrier table. -/
theorem physicalToActive_source_order :
    (List.range 32).map
        (quaternionBlockSwapChainSource physicalToActiveSteps) =
      activeCarrierToCompactEdgeIds := by
  decide

/-- Direct coordinate form of the fixed source-order certificate. -/
def physicalToActiveCoordinateCheck : Bool :=
  (List.range 32).all fun edgeId =>
    decide
      (quaternionBlockSwapChainSource physicalToActiveSteps
          (surfaceActiveBlock edgeId) = edgeId)

theorem physicalToActiveCoordinateCheck_true :
    physicalToActiveCoordinateCheck = true := by
  decide

theorem physicalToActive_coordinate
    (edgeId : Nat) (hedgeId : edgeId < 32) :
    quaternionBlockSwapChainSource physicalToActiveSteps
        (surfaceActiveBlock edgeId) = edgeId := by
  exact of_decide_eq_true
    (List.all_eq_true.mp physicalToActiveCoordinateCheck_true edgeId
      (List.mem_range.mpr hedgeId))

/-! ## Physical-edge order to the mask-dependent compact chord prefix -/

def surfaceChordCarrierSourceOrder (mask : Nat) : List Nat :=
  surfaceForestGaugeChordEdgeIds mask ++
    (List.range 32).filter fun edgeId =>
      decide (edgeId ∉ surfaceForestGaugeChordEdgeIds mask)

def surfaceChordCarrierRawSwaps (mask : Nat) :
    List RawQuaternionBlockSwap :=
  selectionRawSwaps32 (surfaceChordCarrierSourceOrder mask)

def binarySurfaceChordCarrierRawSwapsValidCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    rawQuaternionBlockSwapsValid 32
      (surfaceChordCarrierRawSwaps mask)

theorem binarySurfaceChordCarrierRawSwapsValidCheck_true :
    binarySurfaceChordCarrierRawSwapsValidCheck = true := by
  decide

theorem surfaceChordCarrierRawSwaps_valid
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    rawQuaternionBlockSwapsValid 32
      (surfaceChordCarrierRawSwaps mask) = true :=
  List.all_eq_true.mp
    binarySurfaceChordCarrierRawSwapsValidCheck_true mask hmask

def surfaceChordCarrierSteps
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    List (QuaternionBlockInvolution 32) :=
  certifyRawQuaternionBlockSwaps (surfaceChordCarrierRawSwaps mask)
    (surfaceChordCarrierRawSwaps_valid mask hmask)

def binarySurfaceChordCarrierSourceOrderCheck : Bool :=
  binarySurfaceMasks.attach.all fun maskEntry =>
    decide
      ((List.range 32).map
          (quaternionBlockSwapChainSource
            (surfaceChordCarrierSteps maskEntry.1 maskEntry.2)) =
        surfaceChordCarrierSourceOrder maskEntry.1)

theorem binarySurfaceChordCarrierSourceOrderCheck_true :
    binarySurfaceChordCarrierSourceOrderCheck = true := by
  decide

theorem surfaceChordCarrier_source_order
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    (List.range 32).map
        (quaternionBlockSwapChainSource
          (surfaceChordCarrierSteps mask hmask)) =
      surfaceChordCarrierSourceOrder mask := by
  have hrow := List.all_eq_true.mp
    binarySurfaceChordCarrierSourceOrderCheck_true
    ⟨mask, hmask⟩ (List.mem_attach _ ⟨mask, hmask⟩)
  exact of_decide_eq_true hrow

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.physicalToActive_source_order
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.physicalToActiveCoordinateCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation.surfaceChordCarrier_source_order
