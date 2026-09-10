/-
# Joint source-target activity floor for the connected tilted response

A target-only contour is not normalized correctly: a positive target label
may be the parity ground forced by its source row.  That apparent free
background is nevertheless paid in the fine source.  Indeed a positive
parity-ground target forces its assigned source packet total to be odd and
hence positive.

This file records the resulting exact alternative at every vertex of the
observable-rooted target component.  For a fixed envelope orientation, each
vertex pays at least one unit in the sum of

* the two assigned source packet totals, and
* the two target excitation levels above their assigned parity grounds.

Consequently every nonzero connected oriented contribution pays its genuine
observable-to-source-disagreement separation in total joint source-target
activity.  This replaces the false target-only normalization heuristic with
the correct joint contour.  It does not yet rewrite source packet activity as
the fine heat exponent, dominate the joint weight, sum contours, or prove a
strict rate.

Constructive contract: bounded natural arithmetic, explicit lowering rows,
and finite duplicate-free support sums only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One orientation packages both source assignments -/

inductive FinePacketEnvelopeOrientation : Type
  | forward
  | reverse
  deriving DecidableEq

def finePacketOrientedLeftSource
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : EdgeLabelling :=
  match orientation with
  | .forward => wholeSlabFinePacketTotalLabelling S first
  | .reverse => wholeSlabFinePacketTotalLabelling S second

def finePacketOrientedRightSource
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : EdgeLabelling :=
  match orientation with
  | .forward => wholeSlabFinePacketTotalLabelling S second
  | .reverse => wholeSlabFinePacketTotalLabelling S first

/-- Membership in the two global lowering rows assigned by one orientation. -/
def finePacketOrientedLoweringPair
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Prop :=
  pair.1 ∈ spinFourLoweringTargets S
      (finePacketOrientedLeftSource S orientation first second) ∧
    pair.2 ∈ spinFourLoweringTargets S
      (finePacketOrientedRightSource S orientation first second)

/-- The normalized joint activity at one coarse face: source packet
occupation plus excitation above the corresponding target parity grounds. -/
def finePacketOrientedJointActivityAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Nat :=
  finePacketOrientedLeftSource S orientation first second faceId +
    finePacketOrientedRightSource S orientation first second faceId +
    spinFourParityExcitationLevel
      (finePacketOrientedLeftSource S orientation first second faceId)
      (pair.1 faceId) +
    spinFourParityExcitationLevel
      (finePacketOrientedRightSource S orientation first second faceId)
      (pair.2 faceId)

def finePacketOrientedObservableJointActivityMass
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) : Nat :=
  listNatWeight
    (finePacketOrientedJointActivityAt S orientation first second pair)
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      pair.1 pair.2 observableFaceId)

def finePacketOrientedTotalJointActivity
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  listNatWeight
    (finePacketOrientedJointActivityAt S orientation first second pair)
    S.coarse.faceEdges

/-! ## 2. A positive target ground is paid by its source -/

/-- Two supported targets, one of which is positive, pay at least one unit
in source packet mass plus relative target excitation. -/
theorem spinFourSupportedPositivePair_jointActivity_one_le
    {firstSource secondSource firstTarget secondTarget : Nat}
    (hfirstSource : firstSource ≤ 4)
    (hsecondSource : secondSource ≤ 4)
    (hfirstTarget : firstTarget ≤ 4)
    (hsecondTarget : secondTarget ≤ 4)
    (hfirstLowering : spinFourLoweringCompatible
      firstSource firstTarget)
    (hsecondLowering : spinFourLoweringCompatible
      secondSource secondTarget)
    (hpositive : 0 < firstTarget ∨ 0 < secondTarget) :
    1 ≤ firstSource + secondSource +
        spinFourParityExcitationLevel firstSource firstTarget +
        spinFourParityExcitationLevel secondSource secondTarget := by
  have hfirstEq :=
    spinFourLoweringTarget_eq_ground_add_twice_excitationLevel
      hfirstSource hfirstTarget (by
        simpa [spinFourLoweringCompatible] using hfirstLowering)
  have hsecondEq :=
    spinFourLoweringTarget_eq_ground_add_twice_excitationLevel
      hsecondSource hsecondTarget (by
        simpa [spinFourLoweringCompatible] using hsecondLowering)
  omega

private theorem coarseTargetSpin_le_four_local
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId ≤ 4 := by
  have hsound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htarget
  have hbound := Nat.le_of_lt_succ (hsound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-- Every face of the observable component pays one unit of oriented joint
activity once the two targets lie in their assigned lowering rows. -/
theorem finePacketOrientedObservableComponent_jointActivity_one_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe : pair.1 observableFaceId ≠ pair.2 observableFaceId)
    (faceId : Nat)
    (hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        pair.1 pair.2 observableFaceId) :
    1 ≤ finePacketOrientedJointActivityAt
      S orientation first.1 second.1 pair faceId := by
  have hface :=
    finePacketObservableTargetSupportComponent_face_mem_physical
      S pair observableFaceId hobservableFace hobservableNe
        faceId hcomponent
  have hpositive :=
    finePacketObservableTargetSupportComponent_face_positive
      S pair observableFaceId hobservableFace hobservableNe
        faceId hcomponent
  cases orientation with
  | forward =>
      exact spinFourSupportedPositivePair_jointActivity_one_le
        (wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff first.2.1 faceId hface)
        (wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff second.2.1 faceId hface)
        (coarseTargetSpin_le_four_local S hfineCutoff
          ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
          faceId hface)
        (coarseTargetSpin_le_four_local S hfineCutoff
          ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
          faceId hface)
        (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).2
          faceId hface)
        (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).2
          faceId hface)
        hpositive
  | reverse =>
      exact spinFourSupportedPositivePair_jointActivity_one_le
        (wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff second.2.1 faceId hface)
        (wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff first.2.1 faceId hface)
        (coarseTargetSpin_le_four_local S hfineCutoff
          ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
          faceId hface)
        (coarseTargetSpin_le_four_local S hfineCutoff
          ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
          faceId hface)
        (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).2
          faceId hface)
        (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).2
          faceId hface)
        hpositive

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

theorem finePacketOrientedObservableComponent_length_le_jointActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe : pair.1 observableFaceId ≠ pair.2 observableFaceId) :
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
        pair.1 pair.2 observableFaceId).length ≤
      finePacketOrientedObservableJointActivityMass
        S orientation first.1 second.1 pair observableFaceId := by
  unfold finePacketOrientedObservableJointActivityMass
  apply list_length_le_listNatWeight_of_one_le
  intro faceId hcomponent
  exact finePacketOrientedObservableComponent_jointActivity_one_le
    S hfineCutoff orientation first second pair hlowering
      observableFaceId hobservableFace hobservableNe faceId hcomponent

/-! ## 3. The component floor extends to complete joint activity -/

theorem finePacketOrientedObservableJointActivityMass_le_total
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe : pair.1 observableFaceId ≠ pair.2 observableFaceId) :
    finePacketOrientedObservableJointActivityMass
        S orientation first second pair observableFaceId ≤
      finePacketOrientedTotalJointActivity
        S orientation first second pair := by
  unfold finePacketOrientedObservableJointActivityMass
    finePacketOrientedTotalJointActivity
  apply listNatWeight_le_of_nodup_mem
  · exact rootComponent_nodup
      (slabSupportFaceAdjacentB S.coarse.extent)
      (slabTwoReplicaSupportFaceVertices S.coarse.extent pair.1 pair.2)
      observableFaceId
  · intro faceId hcomponent
    exact finePacketObservableTargetSupportComponent_face_mem_physical
      S pair observableFaceId hobservableFace hobservableNe
        faceId hcomponent

/-- Any connected path whose targets lie in the oriented lowering pair pays
its endpoint separation in total joint source-target activity. -/
theorem finePacketOrientedConnectedPath_jointActivity_floor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (path : FinePacketObservableConnectedDisagreementPath
      S first.1 second.1 observableFaceId pair) :
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketOrientedTotalJointActivity
        S orientation first.1 second.1 pair := by
  exact Nat.le_trans
    (finePacketObservableConnectedDisagreementPath_size_floor
      S first.1 second.1 observableFaceId hobservableFace pair path)
    (Nat.le_trans
      (finePacketObservableTargetSupportPlaquettes_length_le_component
        S pair observableFaceId)
      (Nat.le_trans
        (finePacketOrientedObservableComponent_length_le_jointActivity
          S hfineCutoff orientation first second pair hlowering
            observableFaceId hobservableFace
              path.observable_targetStates_ne)
        (finePacketOrientedObservableJointActivityMass_le_total
          S orientation first.1 second.1 pair observableFaceId
            hobservableFace path.observable_targetStates_ne)))

/-! ## 4. Nonzero connected weights supply the lowering hypotheses -/

theorem finePacketForwardNonzeroConnectedPair_jointActivity_floor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first.1 second.1 observableFaceId hobservableFace pair hpair
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketOrientedTotalJointActivity
        S .forward first.1 second.1 pair := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact finePacketOrientedConnectedPath_jointActivity_floor
    S hfineCutoff .forward first second observableFaceId
      hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

theorem finePacketReverseNonzeroConnectedPair_jointActivity_floor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first.1 second.1 observableFaceId hobservableFace pair hpair
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      finePacketOrientedTotalJointActivity
        S .reverse first.1 second.1 pair := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact finePacketOrientedConnectedPath_jointActivity_floor
    S hfineCutoff .reverse first second observableFaceId
      hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

/-! ## 5. Axiom audit -/

#print axioms FinePacketEnvelopeOrientation
#print axioms finePacketOrientedLeftSource
#print axioms finePacketOrientedRightSource
#print axioms finePacketOrientedLoweringPair
#print axioms finePacketOrientedJointActivityAt
#print axioms finePacketOrientedObservableJointActivityMass
#print axioms finePacketOrientedTotalJointActivity
#print axioms spinFourSupportedPositivePair_jointActivity_one_le
#print axioms finePacketOrientedObservableComponent_jointActivity_one_le
#print axioms finePacketOrientedObservableComponent_length_le_jointActivity
#print axioms finePacketOrientedObservableJointActivityMass_le_total
#print axioms finePacketOrientedConnectedPath_jointActivity_floor
#print axioms finePacketForwardNonzeroConnectedPair_jointActivity_floor
#print axioms finePacketReverseNonzeroConnectedPair_jointActivity_floor

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
