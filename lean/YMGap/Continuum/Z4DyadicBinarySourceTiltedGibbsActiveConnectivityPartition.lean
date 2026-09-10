/-
# Complete connectivity partition of the active tilted-row response

The first connected-path certificate follows one deterministically selected
changed source coordinate.  That is enough to exhibit a path when the
selected coordinate connects, but its false branch is not a disconnection
certificate: another changed disagreement coordinate could still lie in the
observable component.

This file uses the logically complete finite test.  It searches every source
packet-disagreement face for a coordinate where the two coarse target states
differ and which lies in their observable-rooted union-support component.
The true branch returns that face and a Type-level component chain.  The false
branch proves that the target states agree on every disagreement face lying
inside the observable component.  Finally, the exact active response carrier
is partitioned into these two branches without an inequality.

This is the correct input to the next component-swap argument.  Cancellation,
activity bounds, volume-uniform response control, continuum construction, and
the mass gap are not asserted here.

Constructive contract: finite Boolean search, exact list partition, and
Type-level chains only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectedPath

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel

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

/-! ## 1. The complete finite connectivity test -/

/-- A disagreement face is response-connected when the target replicas differ
there and it belongs to their union-support component rooted at the observable
face. -/
def finePacketObservableConnectedDisagreementFaceB
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId faceId : Nat) : Bool :=
  decide (targetPair.1 faceId ≠ targetPair.2 faceId) &&
    decide (faceId ∈ slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)

/-- The complete classifier searches every source packet-disagreement face,
not merely one selected active witness. -/
def finePacketObservableConnectedDisagreementB
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : Bool :=
  (finePacketTotalDisagreementCoarseFaces S first second).any
    (finePacketObservableConnectedDisagreementFaceB
      S targetPair observableFaceId)

/-- A true complete classifier returns the actual connecting disagreement
face as computational data. -/
def finePacketObservableConnectedDisagreementWitness
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = true) :
    Sigma fun faceId : Nat =>
      (faceId ∈ finePacketTotalDisagreementCoarseFaces S first second) ×'
        (targetPair.1 faceId ≠ targetPair.2 faceId) ×'
          (faceId ∈ slabTwoReplicaTargetSupportComponent S.coarse.extent
            targetPair.1 targetPair.2 observableFaceId) := by
  let witness := listAnyTrueWitness
    (finePacketTotalDisagreementCoarseFaces S first second)
    (finePacketObservableConnectedDisagreementFaceB
      S targetPair observableFaceId)
    hconnected
  have hparts := (Bool.and_eq_true _ _).mp witness.2.2
  exact ⟨witness.1, witness.2.1,
    of_decide_eq_true hparts.1, of_decide_eq_true hparts.2⟩

/-- The false branch has the strength required by an involution: throughout
the observable component, the two coarse targets agree at every coordinate
read by either source-local disagreement tilt. -/
theorem finePacketTargets_eq_on_disagreement_of_observableDisconnected
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false)
    (faceId : Nat)
    (hface : faceId ∈ finePacketTotalDisagreementCoarseFaces S first second)
    (hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId) :
    targetPair.1 faceId = targetPair.2 faceId := by
  by_cases heq : targetPair.1 faceId = targetPair.2 faceId
  · exact heq
  · have htest : finePacketObservableConnectedDisagreementFaceB
        S targetPair observableFaceId faceId = true := by
      unfold finePacketObservableConnectedDisagreementFaceB
      simp [heq, hcomponent]
    have hany : finePacketObservableConnectedDisagreementB
        S first second observableFaceId targetPair = true := by
      unfold finePacketObservableConnectedDisagreementB
      exact List.any_eq_true.mpr ⟨faceId, hface, htest⟩
    rw [hdisconnected] at hany
    exact False.elim (Bool.false_ne_true hany)

/-! ## 2. Constructive path on the true branch -/

/-- A complete connected witness together with the actual coarse graph chain
from the observable face. -/
structure FinePacketObservableConnectedDisagreementPath
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : Type where
  sourceFaceId : Nat
  source_mem_disagreement : sourceFaceId ∈
    finePacketTotalDisagreementCoarseFaces S first second
  source_targetStates_ne :
    targetPair.1 sourceFaceId ≠ targetPair.2 sourceFaceId
  observable_targetStates_ne :
    targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId
  observable_mem_targetComponent : observableFaceId ∈
    slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId
  source_mem_targetComponent : sourceFaceId ∈
    slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId
  coarsePath : ChainIn (slabSupportFaceAdjacentB S.coarse.extent)
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)
    observableFaceId sourceFaceId

/-- A true complete classifier and a changed observable coordinate construct
the connected path certificate. -/
def finePacketObservableConnectedDisagreementPathOfTrue
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId)
    (hconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = true) :
    FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair := by
  let witness := finePacketObservableConnectedDisagreementWitness
    S first second observableFaceId targetPair hconnected
  let vertices := slabTwoReplicaSupportFaceVertices S.coarse.extent
    targetPair.1 targetPair.2
  let component := slabTwoReplicaTargetSupportComponent S.coarse.extent
    targetPair.1 targetPair.2 observableFaceId
  have hobservableVertex : observableFaceId ∈ vertices := by
    exact mem_slabTwoReplicaSupportFaceVertices hobservableFace
      (positiveEitherOfNatNe _ _ hobservableNe)
  have hobservableComponent : observableFaceId ∈ component := by
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB S.coarse.extent) hobservableVertex
  have hpath : ChainIn (slabSupportFaceAdjacentB S.coarse.extent)
      component observableFaceId witness.1 :=
    rootComponent_connected
      (slabSupportFaceAdjacentB S.coarse.extent)
      (slabSupportFaceAdjacentB_symmetric S.coarse.extent)
      hobservableVertex observableFaceId witness.1
      hobservableComponent witness.2.2.2
  exact
    { sourceFaceId := witness.1
      source_mem_disagreement := witness.2.1
      source_targetStates_ne := witness.2.2.1
      observable_targetStates_ne := hobservableNe
      observable_mem_targetComponent := hobservableComponent
      source_mem_targetComponent := witness.2.2.2
      coarsePath := hpath }

/-! ## 3. Exact connected/disconnected partition of active one-face pairs -/

def finePacketFaceResponseConnectedActivePairs
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (finePacketLocalizedResponseActivePairs S first second
    (slabPhysicalFacePositiveB observableFaceId)).filter
      (finePacketObservableConnectedDisagreementB
        S first second observableFaceId)

def finePacketFaceResponseDisconnectedActivePairs
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (finePacketLocalizedResponseActivePairs S first second
    (slabPhysicalFacePositiveB observableFaceId)).filter fun pair =>
      !(finePacketObservableConnectedDisagreementB
        S first second observableFaceId pair)

/-- Exact finite partition of the active one-face response into the complete
connected and disconnected branches. -/
theorem finePacketFaceResponseActivePairSum_partition
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm S first second
          (slabPhysicalFacePositiveB observableFaceId))
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB observableFaceId)) ≈
      listQSum
          (finePacketLocalizedAntisymmetricResponsePairTerm S first second
            (slabPhysicalFacePositiveB observableFaceId))
          (finePacketFaceResponseConnectedActivePairs
            S first second observableFaceId) +
        listQSum
          (finePacketLocalizedAntisymmetricResponsePairTerm S first second
            (slabPhysicalFacePositiveB observableFaceId))
          (finePacketFaceResponseDisconnectedActivePairs
            S first second observableFaceId) := by
  exact listQSum_filter_partition
    (finePacketLocalizedAntisymmetricResponsePairTerm S first second
      (slabPhysicalFacePositiveB observableFaceId))
    (finePacketObservableConnectedDisagreementB
      S first second observableFaceId)
    (finePacketLocalizedResponseActivePairs S first second
      (slabPhysicalFacePositiveB observableFaceId))

/-- Membership in the connected active carrier computes a path certificate,
without a propositional existence elimination. -/
def finePacketFaceResponseConnectedActivePairPath
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId) :
    FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair := by
  have hparts := List.mem_filter.mp hpair
  have hactive := (List.mem_filter.mp hparts.1).2
  exact finePacketObservableConnectedDisagreementPathOfTrue
    S first second observableFaceId targetPair hobservableFace
    (activePair_facePositive_targetStates_ne
      S first second observableFaceId targetPair hactive)
    hparts.2

/-! ## 4. Axiom audit -/

#print axioms finePacketObservableConnectedDisagreementFaceB
#print axioms finePacketObservableConnectedDisagreementB
#print axioms finePacketObservableConnectedDisagreementWitness
#print axioms finePacketTargets_eq_on_disagreement_of_observableDisconnected
#print axioms FinePacketObservableConnectedDisagreementPath
#print axioms finePacketObservableConnectedDisagreementPathOfTrue
#print axioms finePacketFaceResponseConnectedActivePairs
#print axioms finePacketFaceResponseDisconnectedActivePairs
#print axioms finePacketFaceResponseActivePairSum_partition
#print axioms finePacketFaceResponseConnectedActivePairPath

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
