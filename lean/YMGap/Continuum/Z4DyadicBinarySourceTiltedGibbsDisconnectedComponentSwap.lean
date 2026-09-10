/-
# Canonical component swap on the disconnected active response carrier

The complete connectivity test separates active target pairs for which some
source packet-disagreement face lies in the observable-rooted union-support
component from those for which no such face exists.  On the disconnected
branch we transpose the two target replicas on exactly that component.

This file proves the structural and local algebra needed for cancellation.
The canonical swap is an involution, preserves the finite physical carrier
and the complete disconnected classifier, leaves every packet-disagreement
tilt unchanged, and exchanges the one-face observable values.  Consequently
the observable indicator difference changes sign.

The common exterior Gibbs background, the complete response term, and the
finite-sum cancellation are intentionally left to subsequent modules.  No
activity estimate, volume-uniform response bound, continuum construction, or
mass gap is asserted here.

Constructive contract: finite Boolean case analysis and exact rational
equivalence only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private def positiveEitherOfNatNe
    (left right : Nat) (hne : left ≠ right) :
    0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero => exact False.elim (hne rfl)
      | succ value => exact Or.inr (Nat.zero_lt_succ value)
  | succ value => exact Or.inl (Nat.zero_lt_succ value)

private theorem bool_eq_of_true_iff_true_local
    (left right : Bool) (h : left = true ↔ right = true) :
    left = right := by
  cases left <;> cases right <;> simp_all

/-! ## 1. The canonical target-pair involution -/

/-- The canonical observable-rooted component mask for one coarse target
pair. -/
def finePacketObservableComponentSwapMask
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : Nat → Bool :=
  slabTwoReplicaSupportSwapMask S.coarse.extent
    targetPair.1 targetPair.2 observableFaceId

def finePacketObservableComponentSwapLeft
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : EdgeLabelling :=
  twoReplicaFaceSwapLeft
    (finePacketObservableComponentSwapMask
      S observableFaceId targetPair) targetPair.1 targetPair.2

def finePacketObservableComponentSwapRight
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : EdgeLabelling :=
  twoReplicaFaceSwapRight
    (finePacketObservableComponentSwapMask
      S observableFaceId targetPair) targetPair.1 targetPair.2

theorem finePacketObservableComponentSwapLeft_of_false
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat)
    (hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId = false) :
    finePacketObservableComponentSwapLeft
        S observableFaceId targetPair faceId = targetPair.1 faceId := by
  unfold finePacketObservableComponentSwapLeft
  exact twoReplicaFaceSwapLeft_of_false _ _ _ _ hmask

theorem finePacketObservableComponentSwapLeft_of_true
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat)
    (hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId = true) :
    finePacketObservableComponentSwapLeft
        S observableFaceId targetPair faceId = targetPair.2 faceId := by
  unfold finePacketObservableComponentSwapLeft
  exact twoReplicaFaceSwapLeft_of_true _ _ _ _ hmask

theorem finePacketObservableComponentSwapRight_of_false
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat)
    (hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId = false) :
    finePacketObservableComponentSwapRight
        S observableFaceId targetPair faceId = targetPair.2 faceId := by
  unfold finePacketObservableComponentSwapRight
  exact twoReplicaFaceSwapRight_of_false _ _ _ _ hmask

theorem finePacketObservableComponentSwapRight_of_true
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat)
    (hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId = true) :
    finePacketObservableComponentSwapRight
        S observableFaceId targetPair faceId = targetPair.1 faceId := by
  unfold finePacketObservableComponentSwapRight
  exact twoReplicaFaceSwapRight_of_true _ _ _ _ hmask

/-- Transpose the two coarse target states on their observable-rooted
union-support component. -/
def finePacketObservableComponentSwap
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    EdgeLabelling × EdgeLabelling :=
  (finePacketObservableComponentSwapLeft S observableFaceId targetPair,
    finePacketObservableComponentSwapRight S observableFaceId targetPair)

/-- The observable-rooted union-support component is literally unchanged by
the canonical transposition. -/
theorem finePacketObservableComponentSwap_targetComponent
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    slabTwoReplicaTargetSupportComponent S.coarse.extent
        (finePacketObservableComponentSwapLeft
          S observableFaceId targetPair)
        (finePacketObservableComponentSwapRight
          S observableFaceId targetPair) observableFaceId =
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId := by
  unfold finePacketObservableComponentSwapLeft
    finePacketObservableComponentSwapRight
    finePacketObservableComponentSwapMask
  exact slabTwoReplicaTargetSupportComponent_faceSwap
    S.coarse.extent observableFaceId
      (slabTwoReplicaSupportSwapMask S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId)
      targetPair.1 targetPair.2

/-- Applying the canonical component swap twice recovers the first target
state. -/
theorem finePacketObservableComponentSwapLeft_involutive
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat) :
    finePacketObservableComponentSwapLeft S observableFaceId
        (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair,
          finePacketObservableComponentSwapRight
            S observableFaceId targetPair) faceId =
      targetPair.1 faceId := by
  have hmaskEq :
      finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId =
        finePacketObservableComponentSwapMask
          S observableFaceId targetPair faceId := by
    unfold finePacketObservableComponentSwapMask
    dsimp only
    unfold slabTwoReplicaSupportSwapMask
    rw [finePacketObservableComponentSwap_targetComponent]
  cases hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId with
  | false =>
      have houter : finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId = false := by
        rw [hmaskEq, hmask]
      rw [finePacketObservableComponentSwapLeft_of_false
        S observableFaceId _ faceId houter]
      dsimp only
      rw [finePacketObservableComponentSwapLeft_of_false
        S observableFaceId targetPair faceId hmask]
  | true =>
      have houter : finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId = true := by
        rw [hmaskEq, hmask]
      rw [finePacketObservableComponentSwapLeft_of_true
        S observableFaceId _ faceId houter]
      dsimp only
      rw [finePacketObservableComponentSwapRight_of_true
        S observableFaceId targetPair faceId hmask]

/-- Applying the same swap twice recovers the second target state. -/
theorem finePacketObservableComponentSwapRight_involutive
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) (faceId : Nat) :
    finePacketObservableComponentSwapRight S observableFaceId
        (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair,
          finePacketObservableComponentSwapRight
            S observableFaceId targetPair) faceId =
      targetPair.2 faceId := by
  have hmaskEq :
      finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId =
        finePacketObservableComponentSwapMask
          S observableFaceId targetPair faceId := by
    unfold finePacketObservableComponentSwapMask
    dsimp only
    unfold slabTwoReplicaSupportSwapMask
    rw [finePacketObservableComponentSwap_targetComponent]
  cases hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair faceId with
  | false =>
      have houter : finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId = false := by
        rw [hmaskEq, hmask]
      rw [finePacketObservableComponentSwapRight_of_false
        S observableFaceId _ faceId houter]
      dsimp only
      rw [finePacketObservableComponentSwapRight_of_false
        S observableFaceId targetPair faceId hmask]
  | true =>
      have houter : finePacketObservableComponentSwapMask S observableFaceId
          (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair,
            finePacketObservableComponentSwapRight
              S observableFaceId targetPair) faceId = true := by
        rw [hmaskEq, hmask]
      rw [finePacketObservableComponentSwapRight_of_true
        S observableFaceId _ faceId houter]
      dsimp only
      rw [finePacketObservableComponentSwapLeft_of_true
        S observableFaceId targetPair faceId hmask]

/-! ## 2. Preservation of the finite physical carrier -/

/-- Both outputs of a canonical component swap of two enumerated coarse
physical states are again enumerated coarse physical states. -/
theorem finePacketObservableComponentSwap_mem_physical
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings) :
    finePacketObservableComponentSwapLeft
          S observableFaceId targetPair ∈ S.coarse.physicalLabellings ∧
      finePacketObservableComponentSwapRight
          S observableFaceId targetPair ∈ S.coarse.physicalLabellings := by
  have hparts := (mem_cartesian_iff S.coarse.physicalLabellings
    S.coarse.physicalLabellings targetPair).mp hpair
  have hleftSound := boundedEdgeLabellings_sound S.coarse.cutoff
    S.coarse.faceEdges targetPair.1 (by
      simpa [SlabPhysicalData.physicalLabellings] using hparts.1)
  have hrightSound := boundedEdgeLabellings_sound S.coarse.cutoff
    S.coarse.faceEdges targetPair.2 (by
      simpa [SlabPhysicalData.physicalLabellings] using hparts.2)
  let mask := slabTwoReplicaSupportSwapMask S.coarse.extent
    targetPair.1 targetPair.2 observableFaceId
  have hleftSwappedBounded : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      twoReplicaFaceSwapLeft mask targetPair.1 targetPair.2 faceId <
        S.coarse.cutoff + 1 := by
    intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hleftSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapLeft, hmask] using
          hrightSound.1 faceId hface
  have hrightSwappedBounded : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      twoReplicaFaceSwapRight mask targetPair.1 targetPair.2 faceId <
        S.coarse.cutoff + 1 := by
    intro faceId hface
    cases hmask : mask faceId with
    | false =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hrightSound.1 faceId hface
    | true =>
        simpa [twoReplicaFaceSwapRight, hmask] using
          hleftSound.1 faceId hface
  have hleftSwappedZero : ∀ faceId, faceId ∉ S.coarse.faceEdges →
      twoReplicaFaceSwapLeft mask targetPair.1 targetPair.2 faceId = 0 := by
    intro faceId hface
    cases hmask : mask faceId <;>
      simp [twoReplicaFaceSwapLeft, hmask,
        hleftSound.2 faceId hface, hrightSound.2 faceId hface]
  have hrightSwappedZero : ∀ faceId, faceId ∉ S.coarse.faceEdges →
      twoReplicaFaceSwapRight mask targetPair.1 targetPair.2 faceId = 0 := by
    intro faceId hface
    cases hmask : mask faceId <;>
      simp [twoReplicaFaceSwapRight, hmask,
        hleftSound.2 faceId hface, hrightSound.2 faceId hface]
  constructor
  · simpa [finePacketObservableComponentSwapLeft,
      finePacketObservableComponentSwapMask,
      SlabPhysicalData.physicalLabellings] using
      (boundedEdgeLabellings_complete S.coarse.cutoff S.coarse.faceEdges
        (twoReplicaFaceSwapLeft mask targetPair.1 targetPair.2)
        hleftSwappedBounded hleftSwappedZero)
  · simpa [finePacketObservableComponentSwapRight,
      finePacketObservableComponentSwapMask,
      SlabPhysicalData.physicalLabellings] using
      (boundedEdgeLabellings_complete S.coarse.cutoff S.coarse.faceEdges
        (twoReplicaFaceSwapRight mask targetPair.1 targetPair.2)
        hrightSwappedBounded hrightSwappedZero)

/-! ## 3. Exact invariance of the complete disconnected classifier -/

/-- At one face, the complete connectivity predicate is invariant under the
canonical transposition. -/
theorem finePacketObservableConnectedDisagreementFaceB_componentSwap
    (S : SlabScalePair) (observableFaceId faceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    finePacketObservableConnectedDisagreementFaceB S
        (finePacketObservableComponentSwap
          S observableFaceId targetPair) observableFaceId faceId =
      finePacketObservableConnectedDisagreementFaceB S
        targetPair observableFaceId faceId := by
  unfold finePacketObservableConnectedDisagreementFaceB
  unfold finePacketObservableComponentSwap
  rw [finePacketObservableComponentSwap_targetComponent]
  unfold finePacketObservableComponentSwapLeft
    finePacketObservableComponentSwapRight
    finePacketObservableComponentSwapMask
  cases hmask : slabTwoReplicaSupportSwapMask S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId faceId <;>
    simp [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight,
      hmask, ne_comm]

/-- Hence the finite search over every source-disagreement face has the same
Boolean value after the canonical transposition. -/
theorem finePacketObservableConnectedDisagreementB_componentSwap
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    finePacketObservableConnectedDisagreementB S first second
        observableFaceId
        (finePacketObservableComponentSwap
          S observableFaceId targetPair) =
      finePacketObservableConnectedDisagreementB S first second
        observableFaceId targetPair := by
  unfold finePacketObservableConnectedDisagreementB
  have hpredicate :
      finePacketObservableConnectedDisagreementFaceB S
          (finePacketObservableComponentSwap
            S observableFaceId targetPair) observableFaceId =
        finePacketObservableConnectedDisagreementFaceB S
          targetPair observableFaceId := by
    funext faceId
    exact finePacketObservableConnectedDisagreementFaceB_componentSwap
      S observableFaceId faceId targetPair
  rw [hpredicate]

/-! ## 4. Local tilt invariance on the disconnected branch -/

/-- On every source packet-disagreement coordinate, the first swapped target
state agrees with the original first target state.  Inside the component this
uses the complete false-branch theorem; outside it the mask is false. -/
theorem finePacketObservableComponentSwap_left_agreesOnDisagreement
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    coarseTargetsAgreeOnFinePacketDisagreementFaces S first second
      (finePacketObservableComponentSwapLeft
        S observableFaceId targetPair) targetPair.1 := by
  intro faceId hface
  by_cases hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId
  · have heq :=
      finePacketTargets_eq_on_disagreement_of_observableDisconnected
        S first second observableFaceId targetPair hdisconnected
        faceId hface hcomponent
    have hmask : slabTwoReplicaSupportSwapMask S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId faceId = true := by
      exact decide_eq_true hcomponent
    simp [finePacketObservableComponentSwapLeft,
      finePacketObservableComponentSwapMask,
      twoReplicaFaceSwapLeft, hmask, heq]
  · have hmask : slabTwoReplicaSupportSwapMask S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId faceId = false := by
      exact decide_eq_false hcomponent
    simp [finePacketObservableComponentSwapLeft,
      finePacketObservableComponentSwapMask,
      twoReplicaFaceSwapLeft, hmask]

/-- The complementary swapped target likewise agrees with its own original
replica throughout the packet-disagreement carrier. -/
theorem finePacketObservableComponentSwap_right_agreesOnDisagreement
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    coarseTargetsAgreeOnFinePacketDisagreementFaces S first second
      (finePacketObservableComponentSwapRight
        S observableFaceId targetPair) targetPair.2 := by
  intro faceId hface
  by_cases hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId
  · have heq :=
      finePacketTargets_eq_on_disagreement_of_observableDisconnected
        S first second observableFaceId targetPair hdisconnected
        faceId hface hcomponent
    have hmask : slabTwoReplicaSupportSwapMask S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId faceId = true := by
      exact decide_eq_true hcomponent
    simp [finePacketObservableComponentSwapRight,
      finePacketObservableComponentSwapMask,
      twoReplicaFaceSwapRight, hmask, heq]
  · have hmask : slabTwoReplicaSupportSwapMask S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId faceId = false := by
      exact decide_eq_false hcomponent
    simp [finePacketObservableComponentSwapRight,
      finePacketObservableComponentSwapMask,
      twoReplicaFaceSwapRight, hmask]

/-- The underlying source-specific natural multiplicity is exactly preserved
on the first target replica. -/
theorem finePacketDisagreementMultiplicityProduct_componentSwap_left
    (S : SlabScalePair) (source first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketDisagreementMultiplicityProduct S source first second
        (finePacketObservableComponentSwapLeft
          S observableFaceId targetPair) =
      finePacketDisagreementMultiplicityProduct S source first second
        targetPair.1 := by
  exact finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
    S source first second
      (finePacketObservableComponentSwapLeft
        S observableFaceId targetPair) targetPair.1
      (finePacketObservableComponentSwap_left_agreesOnDisagreement
        S first second observableFaceId targetPair hdisconnected)

/-- The complementary natural multiplicity is preserved on the second
target replica. -/
theorem finePacketDisagreementMultiplicityProduct_componentSwap_right
    (S : SlabScalePair) (source first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketDisagreementMultiplicityProduct S source first second
        (finePacketObservableComponentSwapRight
          S observableFaceId targetPair) =
      finePacketDisagreementMultiplicityProduct S source first second
        targetPair.2 := by
  exact finePacketDisagreementMultiplicityProduct_eq_of_targetsAgree
    S source first second
      (finePacketObservableComponentSwapRight
        S observableFaceId targetPair) targetPair.2
      (finePacketObservableComponentSwap_right_agreesOnDisagreement
        S first second observableFaceId targetPair hdisconnected)

/-- Every source-specific local multiplicity tilt is exactly preserved on
the first target replica. -/
theorem finePacketDisagreementTilt_componentSwap_left
    (S : SlabScalePair) (source first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketDisagreementTilt S source first second
        (finePacketObservableComponentSwapLeft
          S observableFaceId targetPair) =
      finePacketDisagreementTilt S source first second targetPair.1 := by
  unfold finePacketDisagreementTilt
  rw [finePacketDisagreementMultiplicityProduct_componentSwap_left
    S source first second observableFaceId targetPair hdisconnected]

/-- Every source-specific local multiplicity tilt is exactly preserved on
the second target replica. -/
theorem finePacketDisagreementTilt_componentSwap_right
    (S : SlabScalePair) (source first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketDisagreementTilt S source first second
        (finePacketObservableComponentSwapRight
          S observableFaceId targetPair) =
      finePacketDisagreementTilt S source first second targetPair.2 := by
  unfold finePacketDisagreementTilt
  rw [finePacketDisagreementMultiplicityProduct_componentSwap_right
    S source first second observableFaceId targetPair hdisconnected]

/-! ## 5. Active-carrier preservation -/

/-- At the observable coordinate, a component swap either keeps the two
Boolean face events in place or transposes them.  Their inequality is
therefore invariant without any positivity assumption. -/
theorem finePacketObservableComponentSwap_facePositive_ne
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    (slabPhysicalFacePositiveB observableFaceId
          (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair) ≠
        slabPhysicalFacePositiveB observableFaceId
          (finePacketObservableComponentSwapRight
            S observableFaceId targetPair)) ↔
      (slabPhysicalFacePositiveB observableFaceId targetPair.1 ≠
        slabPhysicalFacePositiveB observableFaceId targetPair.2) := by
  unfold slabPhysicalFacePositiveB
    finePacketObservableComponentSwapLeft
    finePacketObservableComponentSwapRight
  cases hmask : finePacketObservableComponentSwapMask
      S observableFaceId targetPair observableFaceId with
  | false =>
      simp [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight, hmask]
  | true =>
      simp only [twoReplicaFaceSwapLeft, twoReplicaFaceSwapRight,
        hmask, if_true]
      exact ne_comm

/-- On the complete disconnected branch, both natural determinant products
and the event-inequality test are invariant, so the full active Boolean is
unchanged. -/
theorem finePacketLocalizedResponsePairActiveB_componentSwap
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketLocalizedResponsePairActiveB S first second
        (slabPhysicalFacePositiveB observableFaceId)
        (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair,
          finePacketObservableComponentSwapRight
            S observableFaceId targetPair) =
      finePacketLocalizedResponsePairActiveB S first second
        (slabPhysicalFacePositiveB observableFaceId) targetPair := by
  unfold finePacketLocalizedResponsePairActiveB
    finePacketForwardDisagreementMultiplicityProduct
    finePacketReverseDisagreementMultiplicityProduct
  rw [finePacketDisagreementMultiplicityProduct_componentSwap_left
      S first first second observableFaceId targetPair hdisconnected,
    finePacketDisagreementMultiplicityProduct_componentSwap_right
      S second first second observableFaceId targetPair hdisconnected,
    finePacketDisagreementMultiplicityProduct_componentSwap_left
      S second first second observableFaceId targetPair hdisconnected,
    finePacketDisagreementMultiplicityProduct_componentSwap_right
      S first first second observableFaceId targetPair hdisconnected]
  have hiff := finePacketObservableComponentSwap_facePositive_ne
    S observableFaceId targetPair
  have hdecide : decide
        (slabPhysicalFacePositiveB observableFaceId
            (finePacketObservableComponentSwapLeft
              S observableFaceId targetPair) ≠
          slabPhysicalFacePositiveB observableFaceId
            (finePacketObservableComponentSwapRight
              S observableFaceId targetPair)) =
      decide
        (slabPhysicalFacePositiveB observableFaceId targetPair.1 ≠
          slabPhysicalFacePositiveB observableFaceId targetPair.2) := by
    apply bool_eq_of_true_iff_true_local
    constructor
    · intro htrue
      exact decide_eq_true (hiff.mp (of_decide_eq_true htrue))
    · intro htrue
      exact decide_eq_true (hiff.mpr (of_decide_eq_true htrue))
  rw [hdecide]

/-- The canonical swap maps the complete disconnected active carrier back
into itself.  This is the closure input for the later involutive finite-sum
cancellation. -/
def finePacketObservableComponentSwap_disconnectedActivePair
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ finePacketFaceResponseDisconnectedActivePairs
      S first second observableFaceId) :
    { swappedPair : EdgeLabelling × EdgeLabelling //
      swappedPair ∈ finePacketFaceResponseDisconnectedActivePairs
        S first second observableFaceId } := by
  have hparts := List.mem_filter.mp hpair
  have hactiveParts := List.mem_filter.mp hparts.1
  have hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false := by
    cases htest : finePacketObservableConnectedDisagreementB
        S first second observableFaceId targetPair with
    | false => rfl
    | true =>
        have hbad : !true = true := by
          simpa [htest] using hparts.2
        exact False.elim (Bool.noConfusion hbad)
  let swappedPair : EdgeLabelling × EdgeLabelling :=
    (finePacketObservableComponentSwapLeft S observableFaceId targetPair,
      finePacketObservableComponentSwapRight S observableFaceId targetPair)
  have hphysical : swappedPair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings := by
    apply (mem_cartesian_iff S.coarse.physicalLabellings
      S.coarse.physicalLabellings swappedPair).mpr
    simpa [swappedPair] using
      (finePacketObservableComponentSwap_mem_physical
        S observableFaceId targetPair hactiveParts.1)
  have hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) swappedPair = true := by
    dsimp only [swappedPair]
    rw [finePacketLocalizedResponsePairActiveB_componentSwap
      S first second observableFaceId targetPair hdisconnected]
    exact hactiveParts.2
  have hnotConnected : Bool.not
      (finePacketObservableConnectedDisagreementB
        S first second observableFaceId swappedPair) = true := by
    dsimp only [swappedPair]
    change Bool.not
      (finePacketObservableConnectedDisagreementB S first second
        observableFaceId
          (finePacketObservableComponentSwap
            S observableFaceId targetPair)) = true
    rw [finePacketObservableConnectedDisagreementB_componentSwap]
    exact hparts.2
  refine ⟨swappedPair, ?_⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_filter.mpr ⟨hphysical, hactive⟩, hnotConnected⟩

/-! ## 6. Observable exchange and sign reversal -/

/-- For an active one-face pair, the canonical component contains the
observable face, so the first swapped observable value is the original
second value. -/
theorem finePacketObservableComponentSwap_facePositive_left
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true) :
    slabPhysicalFacePositiveB observableFaceId
        (finePacketObservableComponentSwapLeft
          S observableFaceId targetPair) =
      slabPhysicalFacePositiveB observableFaceId targetPair.2 := by
  have hne := activePair_facePositive_targetStates_ne
    S first second observableFaceId targetPair hactive
  have hsupport := positiveEitherOfNatNe
    (targetPair.1 observableFaceId) (targetPair.2 observableFaceId) hne
  have hmask := slabTwoReplicaSupportSwapMask_target
    (extent := S.coarse.extent) (targetFaceId := observableFaceId)
    (left := targetPair.1) (right := targetPair.2)
    hobservableFace hsupport
  unfold slabPhysicalFacePositiveB
  change decide (0 < finePacketObservableComponentSwapLeft
    S observableFaceId targetPair observableFaceId) = _
  unfold finePacketObservableComponentSwapLeft
    finePacketObservableComponentSwapMask
  rw [
    twoReplicaFaceSwapLeft_of_true _ _ _ _ hmask]

/-- The second swapped observable value is the original first value. -/
theorem finePacketObservableComponentSwap_facePositive_right
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true) :
    slabPhysicalFacePositiveB observableFaceId
        (finePacketObservableComponentSwapRight
          S observableFaceId targetPair) =
      slabPhysicalFacePositiveB observableFaceId targetPair.1 := by
  have hne := activePair_facePositive_targetStates_ne
    S first second observableFaceId targetPair hactive
  have hsupport := positiveEitherOfNatNe
    (targetPair.1 observableFaceId) (targetPair.2 observableFaceId) hne
  have hmask := slabTwoReplicaSupportSwapMask_target
    (extent := S.coarse.extent) (targetFaceId := observableFaceId)
    (left := targetPair.1) (right := targetPair.2)
    hobservableFace hsupport
  unfold slabPhysicalFacePositiveB
  change decide (0 < finePacketObservableComponentSwapRight
    S observableFaceId targetPair observableFaceId) = _
  unfold finePacketObservableComponentSwapRight
    finePacketObservableComponentSwapMask
  rw [
    twoReplicaFaceSwapRight_of_true _ _ _ _ hmask]

/-- The exact rational one-face indicator difference reverses sign under the
canonical component transposition. -/
theorem finePacketObservableComponentSwap_indicatorDifference
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true) :
    booleanEventIndicator (slabPhysicalFacePositiveB observableFaceId)
          (finePacketObservableComponentSwapLeft
            S observableFaceId targetPair) -
        booleanEventIndicator (slabPhysicalFacePositiveB observableFaceId)
          (finePacketObservableComponentSwapRight
            S observableFaceId targetPair) ≈
      -(booleanEventIndicator (slabPhysicalFacePositiveB observableFaceId)
          targetPair.1 -
        booleanEventIndicator (slabPhysicalFacePositiveB observableFaceId)
          targetPair.2) := by
  unfold booleanEventIndicator
  rw [finePacketObservableComponentSwap_facePositive_left
      S first second observableFaceId hobservableFace targetPair hactive,
    finePacketObservableComponentSwap_facePositive_right
      S first second observableFaceId hobservableFace targetPair hactive]
  exact Q'.eqv_symm (Q'.neg_sub_eqv _ _)

/-! ## 7. Axiom audit -/

#print axioms finePacketObservableComponentSwap
#print axioms finePacketObservableComponentSwap_targetComponent
#print axioms finePacketObservableComponentSwapLeft_involutive
#print axioms finePacketObservableComponentSwapRight_involutive
#print axioms finePacketObservableComponentSwap_mem_physical
#print axioms finePacketObservableConnectedDisagreementFaceB_componentSwap
#print axioms finePacketObservableConnectedDisagreementB_componentSwap
#print axioms finePacketObservableComponentSwap_left_agreesOnDisagreement
#print axioms finePacketObservableComponentSwap_right_agreesOnDisagreement
#print axioms finePacketDisagreementMultiplicityProduct_componentSwap_left
#print axioms finePacketDisagreementMultiplicityProduct_componentSwap_right
#print axioms finePacketDisagreementTilt_componentSwap_left
#print axioms finePacketDisagreementTilt_componentSwap_right
#print axioms finePacketObservableComponentSwap_facePositive_ne
#print axioms finePacketLocalizedResponsePairActiveB_componentSwap
#print axioms finePacketObservableComponentSwap_disconnectedActivePair
#print axioms finePacketObservableComponentSwap_facePositive_left
#print axioms finePacketObservableComponentSwap_facePositive_right
#print axioms finePacketObservableComponentSwap_indicatorDifference

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
