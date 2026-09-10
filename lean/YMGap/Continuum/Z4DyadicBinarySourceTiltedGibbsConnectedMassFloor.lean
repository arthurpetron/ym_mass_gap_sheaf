/-
# Physical activity floor for the surviving tilted-Gibbs response

The surviving connected response now carries a genuine Z4 lattice animal.
This file converts its geometric size into the twice-spin mass actually seen
by the coarse heat weights.  Every face of the observable-rooted union-support
component has positive label in at least one target replica, so it pays at
least one unit of two-replica mass.  Component mass is then bounded by total
physical target-pair mass.

Consequently every connected active response pair pays at least its
observable-to-source-disagreement L-infinity separation plus one in actual
twice-spin mass.  No weighted summation or strict contraction is asserted.

Constructive contract: finite natural-number sums and explicit support
membership only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
import YMGap.Continuum.FiniteSimpleWalk

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor

set_option autoImplicit false

open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Current target-pair mass observables -/

/-- Twice-spin mass carried on the observable-rooted union-support
component of the current coarse target pair. -/
def finePacketObservableTargetSupportMass
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) : Nat :=
  listNatWeight
    (fun faceId => targetPair.1 faceId + targetPair.2 faceId)
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)

/-- Complete physical twice-spin mass of both current target replicas. -/
def finePacketTargetPairTotalPhysicalMass
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling) : Nat :=
  listNatWeight
    (fun faceId => targetPair.1 faceId + targetPair.2 faceId)
    S.coarse.faceEdges

private def positiveEitherOfNatNe
    (left right : Nat) (hne : left ≠ right) :
    0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero => exact False.elim (hne rfl)
      | succ value => exact Or.inr (Nat.zero_lt_succ value)
  | succ value => exact Or.inl (Nat.zero_lt_succ value)

private theorem observable_mem_supportVertices
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId) :
    observableFaceId ∈
      slabTwoReplicaSupportFaceVertices S.coarse.extent
        targetPair.1 targetPair.2 := by
  apply mem_slabTwoReplicaSupportFaceVertices hobservableFace
  exact positiveEitherOfNatNe _ _ hobservableNe

/-! ## 2. Every component face pays at least one unit -/

theorem finePacketObservableTargetSupportComponent_face_mem_physical
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId) :
    faceId ∈ S.coarse.faceEdges := by
  have hvertex := rootComponent_subset
    (slabSupportFaceAdjacentB S.coarse.extent)
    (observable_mem_supportVertices
      S targetPair observableFaceId hobservableFace hobservableNe)
    hface
  exact (List.mem_filter.mp hvertex).1

theorem finePacketObservableTargetSupportComponent_face_positive
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId)
    (faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId) :
    0 < targetPair.1 faceId ∨ 0 < targetPair.2 faceId := by
  have hvertex := rootComponent_subset
    (slabSupportFaceAdjacentB S.coarse.extent)
    (observable_mem_supportVertices
      S targetPair observableFaceId hobservableFace hobservableNe)
    hface
  exact of_decide_eq_true (List.mem_filter.mp hvertex).2

private theorem list_length_le_listNatWeight_of_one_le
    {A : Type} (weight : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → 1 ≤ weight item) →
        items.length ≤ listNatWeight weight items
  | [], _ => Nat.le_refl 0
  | head :: tail, hweight => by
      have hhead := hweight head List.mem_cons_self
      have htail := list_length_le_listNatWeight_of_one_le
        weight tail (fun item hitem =>
          hweight item (List.mem_cons_of_mem head hitem))
      simp only [List.length_cons, listNatWeight]
      omega

theorem finePacketObservableTargetSupportComponent_length_le_mass
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId) :
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId).length ≤
      finePacketObservableTargetSupportMass
        S targetPair observableFaceId := by
  unfold finePacketObservableTargetSupportMass
  apply list_length_le_listNatWeight_of_one_le
  intro faceId hface
  rcases finePacketObservableTargetSupportComponent_face_positive
      S targetPair observableFaceId hobservableFace hobservableNe
        faceId hface with hleft | hright
  · omega
  · omega

/-! ## 3. Geometric support and component mass lie below total mass -/

private theorem eraseDupsLengthLeLocal {A : Type}
    [BEq A] (items : List A) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hfilter := List.length_filter_le
        (fun item : A => !item == head) tail
      have ih := eraseDupsLengthLeLocal
        (tail.filter fun item => !item == head)
      omega
termination_by items.length
decreasing_by
  simp_wf
  omega

theorem finePacketObservableTargetSupportPlaquettes_length_le_component
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) :
    (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId).length ≤
      (slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId).length := by
  unfold finePacketObservableTargetSupportPlaquettes
  have hdedup := eraseDupsLengthLeLocal
    ((slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId).map
        (slabPlaquetteAt S.coarse.extent))
  rw [List.length_map] at hdedup
  exact hdedup

theorem finePacketObservableTargetSupportMass_le_total
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId) :
    finePacketObservableTargetSupportMass S targetPair observableFaceId ≤
      finePacketTargetPairTotalPhysicalMass S targetPair := by
  unfold finePacketObservableTargetSupportMass
    finePacketTargetPairTotalPhysicalMass
  apply listNatWeight_le_of_nodup_mem
  · exact rootComponent_nodup
      (slabSupportFaceAdjacentB S.coarse.extent)
      (slabTwoReplicaSupportFaceVertices S.coarse.extent
        targetPair.1 targetPair.2)
      observableFaceId
  · intro faceId hface
    exact finePacketObservableTargetSupportComponent_face_mem_physical
      S targetPair observableFaceId hobservableFace hobservableNe
        faceId hface

/-! ## 4. Physical activity floors for the exact connected response -/

/-- A connected response path pays its endpoint separation in twice-spin
mass on the observable-rooted component. -/
theorem finePacketObservableConnectedDisagreementPath_componentMass_floor
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (path : FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair) :
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketObservableTargetSupportMass
        S targetPair observableFaceId := by
  exact Nat.le_trans
    (finePacketObservableConnectedDisagreementPath_size_floor
      S first second observableFaceId hobservableFace targetPair path)
    (Nat.le_trans
      (finePacketObservableTargetSupportPlaquettes_length_le_component
        S targetPair observableFaceId)
      (finePacketObservableTargetSupportComponent_length_le_mass
        S targetPair observableFaceId hobservableFace
          path.observable_targetStates_ne))

/-- In particular the complete two-replica target mass pays the selected
observable-to-source-disagreement separation. -/
theorem finePacketObservableConnectedDisagreementPath_totalMass_floor
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (path : FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair) :
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketTargetPairTotalPhysicalMass S targetPair :=
  Nat.le_trans
    (finePacketObservableConnectedDisagreementPath_componentMass_floor
      S first second observableFaceId hobservableFace targetPair path)
    (finePacketObservableTargetSupportMass_le_total
      S targetPair observableFaceId hobservableFace
        path.observable_targetStates_ne)

/-- Every pair in the exact connected active carrier computes a source
endpoint and pays its separation in complete target-pair mass. -/
theorem finePacketFaceResponseConnectedActivePair_totalMass_floor
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first second observableFaceId hobservableFace targetPair hpair
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketTargetPairTotalPhysicalMass S targetPair := by
  exact finePacketObservableConnectedDisagreementPath_totalMass_floor
    S first second observableFaceId hobservableFace targetPair
      (finePacketFaceResponseConnectedActivePairPath
        S first second observableFaceId hobservableFace targetPair hpair)

/-! ## 5. Axiom audit -/

#print axioms finePacketObservableTargetSupportMass
#print axioms finePacketTargetPairTotalPhysicalMass
#print axioms finePacketObservableTargetSupportComponent_face_positive
#print axioms finePacketObservableTargetSupportComponent_length_le_mass
#print axioms finePacketObservableTargetSupportMass_le_total
#print axioms finePacketObservableConnectedDisagreementPath_componentMass_floor
#print axioms finePacketObservableConnectedDisagreementPath_totalMass_floor
#print axioms finePacketFaceResponseConnectedActivePair_totalMass_floor

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
