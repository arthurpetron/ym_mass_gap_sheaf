/-
# The first honest obstruction to connected component-swap cancellation

After fixing one of the two product-measure orientations, the observable-
rooted target-component transposition need not remain in the same pair of
source-dependent lowering rows.  This file identifies that failure exactly
where the connected-path witness reaches a source packet-disagreement face.

The local five-spin statement is a constructive dichotomy.  Two unequal
targets which are supported by their assigned source spins either cease to
be simultaneously supported after transposition, or at least one original
target has positive excitation above its assigned parity ground.  Lifting
this to the computed connected path shows that every nonzero connected
oriented contribution either exits its oriented lowering carrier under the
canonical component swap or has a positive relative excitation at the
source-disagreement endpoint.

This is a location theorem, not yet an activity estimate: it neither bounds
the probability of the obstruction nor counts enough excitations along the
path.  No beta-uniformity, volume-uniformity, spectral gap, continuum theory,
or Clay theorem is asserted here.

Constructive contract: bounded natural-number parity arithmetic and computed
finite paths only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact local transposition dichotomy -/

/-- A target spin is in the support of the cutoff-four lowering row indexed
by `sourceSpin`. -/
def spinFourLoweringCompatible (sourceSpin targetSpin : Nat) : Prop :=
  targetSpin ≤ sourceSpin ∧ targetSpin % 2 = sourceSpin % 2

/-- Failure of the two cross-assigned lowering relations after transposing
two targets. -/
def spinFourCrossSwapObstruction
    (firstSource secondSource firstTarget secondTarget : Nat) : Prop :=
  ¬ (spinFourLoweringCompatible firstSource secondTarget ∧
      spinFourLoweringCompatible secondSource firstTarget)

/-- For the complete cutoff-four local state space, two unequal supported
targets cannot be both parity-ground and remain jointly supported after
transposition. -/
theorem spinFourCrossSwapObstruction_or_relativeExcitation
    {firstSource secondSource firstTarget secondTarget : Nat}
    (hfirstSource : firstSource ≤ 4)
    (hsecondSource : secondSource ≤ 4)
    (hfirstTarget : firstTarget ≤ 4)
    (hsecondTarget : secondTarget ≤ 4)
    (hfirstLowering : spinFourLoweringCompatible
      firstSource firstTarget)
    (hsecondLowering : spinFourLoweringCompatible
      secondSource secondTarget)
    (htargetNe : firstTarget ≠ secondTarget) :
    spinFourCrossSwapObstruction
        firstSource secondSource firstTarget secondTarget ∨
      0 < spinFourParityExcitationLevel firstSource firstTarget ∨
      0 < spinFourParityExcitationLevel secondSource secondTarget := by
  have hs : firstSource = 0 ∨ firstSource = 1 ∨ firstSource = 2 ∨
      firstSource = 3 ∨ firstSource = 4 := by
    omega
  have hs' : secondSource = 0 ∨ secondSource = 1 ∨ secondSource = 2 ∨
      secondSource = 3 ∨ secondSource = 4 := by
    omega
  have ht : firstTarget = 0 ∨ firstTarget = 1 ∨ firstTarget = 2 ∨
      firstTarget = 3 ∨ firstTarget = 4 := by
    omega
  have ht' : secondTarget = 0 ∨ secondTarget = 1 ∨ secondTarget = 2 ∨
      secondTarget = 3 ∨ secondTarget = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases hs' with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht' with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourCrossSwapObstruction, spinFourLoweringCompatible,
      spinFourParityExcitationLevel] at *

/-! ## 2. Facewise obstruction predicates for both orientations -/

def finePacketForwardSwapObstructionAt
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Prop :=
  spinFourCrossSwapObstruction
    (wholeSlabFinePacketTotalLabelling S first faceId)
    (wholeSlabFinePacketTotalLabelling S second faceId)
    (pair.1 faceId) (pair.2 faceId)

def finePacketReverseSwapObstructionAt
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Prop :=
  spinFourCrossSwapObstruction
    (wholeSlabFinePacketTotalLabelling S second faceId)
    (wholeSlabFinePacketTotalLabelling S first faceId)
    (pair.1 faceId) (pair.2 faceId)

/-- A local forward cross-swap obstruction on a face belonging to the
observable component makes simultaneous membership of the two swapped
targets in the original forward lowering rows impossible. -/
theorem finePacketForwardSwapObstructionAt_implies_componentSwap_exits
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (faceId : Nat)
    (hface : faceId ∈ S.coarse.faceEdges)
    (hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        pair.1 pair.2 observableFaceId)
    (hobstruction : finePacketForwardSwapObstructionAt
      S first second pair faceId) :
    ¬ (finePacketObservableComponentSwapLeft
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S first) ∧
        finePacketObservableComponentSwapRight
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S second)) := by
  intro hswapped
  have hleft := ((mem_spinFourLoweringTargets_iff S _ _).mp
    hswapped.1).2 faceId hface
  have hright := ((mem_spinFourLoweringTargets_iff S _ _).mp
    hswapped.2).2 faceId hface
  have hmask : finePacketObservableComponentSwapMask
      S observableFaceId pair faceId = true := by
    exact decide_eq_true hcomponent
  apply hobstruction
  unfold spinFourLoweringCompatible
  rw [finePacketObservableComponentSwapLeft_of_true
      S observableFaceId pair faceId hmask] at hleft
  rw [finePacketObservableComponentSwapRight_of_true
      S observableFaceId pair faceId hmask] at hright
  exact ⟨hleft, hright⟩

/-- The analogous implication for the reverse source assignment. -/
theorem finePacketReverseSwapObstructionAt_implies_componentSwap_exits
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (faceId : Nat)
    (hface : faceId ∈ S.coarse.faceEdges)
    (hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        pair.1 pair.2 observableFaceId)
    (hobstruction : finePacketReverseSwapObstructionAt
      S first second pair faceId) :
    ¬ (finePacketObservableComponentSwapLeft
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S second) ∧
        finePacketObservableComponentSwapRight
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S first)) := by
  intro hswapped
  have hleft := ((mem_spinFourLoweringTargets_iff S _ _).mp
    hswapped.1).2 faceId hface
  have hright := ((mem_spinFourLoweringTargets_iff S _ _).mp
    hswapped.2).2 faceId hface
  have hmask : finePacketObservableComponentSwapMask
      S observableFaceId pair faceId = true := by
    exact decide_eq_true hcomponent
  apply hobstruction
  unfold spinFourLoweringCompatible
  rw [finePacketObservableComponentSwapLeft_of_true
      S observableFaceId pair faceId hmask] at hleft
  rw [finePacketObservableComponentSwapRight_of_true
      S observableFaceId pair faceId hmask] at hright
  exact ⟨hleft, hright⟩

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

/-! ## 3. The connected-path boundary certificates -/

/-- A computed forward connected path together with the first exact reason
why the component swap cannot provide cancellation for free. -/
structure FinePacketForwardConnectedSwapBoundary
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling) : Type where
  path : FinePacketObservableConnectedDisagreementPath
    S first.1 second.1 observableFaceId pair
  swap_exits_or_source_excited :
    ¬ (finePacketObservableComponentSwapLeft
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S first.1) ∧
        finePacketObservableComponentSwapRight
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S second.1)) ∨
      finePacketForwardRelativeExcitationAt
        S first.1 second.1 pair path.sourceFaceId

/-- The reverse-orientation version of the same boundary certificate. -/
structure FinePacketReverseConnectedSwapBoundary
    (S : SlabScalePair) (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling) : Type where
  path : FinePacketObservableConnectedDisagreementPath
    S first.1 second.1 observableFaceId pair
  swap_exits_or_source_excited :
    ¬ (finePacketObservableComponentSwapLeft
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S second.1) ∧
        finePacketObservableComponentSwapRight
          S observableFaceId pair ∈
          spinFourLoweringTargets S
            (wholeSlabFinePacketTotalLabelling S first.1)) ∨
      finePacketReverseRelativeExcitationAt
        S first.1 second.1 pair path.sourceFaceId

/-- Every nonzero forward connected contribution computes a boundary
certificate at the source-disagreement endpoint of its actual coarse path. -/
def finePacketForwardNonzeroConnectedSwapBoundary
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    FinePacketForwardConnectedSwapBoundary
      S first second observableFaceId pair := by
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace pair hpair
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  have hface : path.sourceFaceId ∈ S.coarse.faceEdges :=
    (List.mem_filter.mp path.source_mem_disagreement).1
  have hlocal := spinFourCrossSwapObstruction_or_relativeExcitation
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff first.2.1 path.sourceFaceId hface)
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff second.2.1 path.sourceFaceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff
      ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
      path.sourceFaceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff
      ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
      path.sourceFaceId hface)
    (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).2
      path.sourceFaceId hface)
    (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).2
      path.sourceFaceId hface)
    path.source_targetStates_ne
  refine { path := path, swap_exits_or_source_excited := ?_ }
  rcases hlocal with hobstruction | hexcitation
  · exact Or.inl
      (finePacketForwardSwapObstructionAt_implies_componentSwap_exits
        S first.1 second.1 observableFaceId pair path.sourceFaceId hface
        path.source_mem_targetComponent hobstruction)
  · exact Or.inr hexcitation

/-- Every nonzero reverse connected contribution computes the symmetric
boundary certificate with the reversed source assignment. -/
def finePacketReverseNonzeroConnectedSwapBoundary
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    FinePacketReverseConnectedSwapBoundary
      S first second observableFaceId pair := by
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace pair hpair
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  have hface : path.sourceFaceId ∈ S.coarse.faceEdges :=
    (List.mem_filter.mp path.source_mem_disagreement).1
  have hlocal := spinFourCrossSwapObstruction_or_relativeExcitation
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff second.2.1 path.sourceFaceId hface)
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff first.2.1 path.sourceFaceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff
      ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
      path.sourceFaceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff
      ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
      path.sourceFaceId hface)
    (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).2
      path.sourceFaceId hface)
    (((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).2
      path.sourceFaceId hface)
    path.source_targetStates_ne
  refine { path := path, swap_exits_or_source_excited := ?_ }
  rcases hlocal with hobstruction | hexcitation
  · exact Or.inl
      (finePacketReverseSwapObstructionAt_implies_componentSwap_exits
        S first.1 second.1 observableFaceId pair path.sourceFaceId hface
        path.source_mem_targetComponent hobstruction)
  · exact Or.inr hexcitation

/-! ## 4. Axiom audit -/

#print axioms spinFourLoweringCompatible
#print axioms spinFourCrossSwapObstruction
#print axioms spinFourCrossSwapObstruction_or_relativeExcitation
#print axioms finePacketForwardSwapObstructionAt
#print axioms finePacketReverseSwapObstructionAt
#print axioms finePacketForwardSwapObstructionAt_implies_componentSwap_exits
#print axioms finePacketReverseSwapObstructionAt_implies_componentSwap_exits
#print axioms FinePacketForwardConnectedSwapBoundary
#print axioms FinePacketReverseConnectedSwapBoundary
#print axioms finePacketForwardNonzeroConnectedSwapBoundary
#print axioms finePacketReverseNonzeroConnectedSwapBoundary

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedSwapObstruction
