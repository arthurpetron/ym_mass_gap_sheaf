/-
# Target excitation as exact SU(2) Casimir excess

For a cutoff-four target in a supported spin-four lowering row, the parity
ground is the source spin modulo two and the target is obtained from that
ground by two-spin excitation steps.  This file separates the target Casimir
exponent exactly into its source-determined ground exponent and a nonnegative
excess.  The SU(2) formula `c4(t) = t * (t + 2)` makes each excitation step
cost at least eight units of excess exponent.

The local identity is summed over the complete two-replica coarse carrier and
combined with the injected fine-source occupation theorem.  Every connected
path in an oriented lowering carrier consequently pays three times its
geometric distance in the actual fine Casimir exponent plus coarse target
Casimir excess.  The common factor is three because one occupied fundamental
fine face has Casimir exponent three, while a target excitation costs at least
eight.  This is an exponent budget, not yet a rational weight bound or a
contour sum.

Constructive contract: bounded natural arithmetic, explicit finite sums, and
the exact SU(2) Casimir only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

namespace YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact local Casimir separation -/

def spinFourParityGroundCasimirExponent (sourceSpin : Nat) : Nat :=
  c4 (sourceSpin % 2)

def spinFourParityExcitationCasimirExcess
    (sourceSpin targetSpin : Nat) : Nat :=
  c4 targetSpin - spinFourParityGroundCasimirExponent sourceSpin

theorem spinFourParityGroundSpin_le_target
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    sourceSpin % 2 ≤ targetSpin := by
  have hreconstruct :=
    spinFourLoweringTarget_eq_ground_add_twice_excitationLevel
      hsource htarget hlowering
  omega

theorem spinFourParityGroundCasimir_le_target
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    spinFourParityGroundCasimirExponent sourceSpin ≤ c4 targetSpin := by
  have hground := spinFourParityGroundSpin_le_target
    hsource htarget hlowering
  unfold spinFourParityGroundCasimirExponent c4
  exact Nat.mul_le_mul hground (by omega)

/-- A supported target Casimir is its parity-ground Casimir plus the exact
nonnegative excitation excess. -/
theorem spinFourTargetCasimir_eq_ground_add_excitationExcess
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    c4 targetSpin = spinFourParityGroundCasimirExponent sourceSpin +
      spinFourParityExcitationCasimirExcess sourceSpin targetSpin := by
  have hle := spinFourParityGroundCasimir_le_target
    hsource htarget hlowering
  unfold spinFourParityExcitationCasimirExcess
  omega

/-- The SU(2) Casimir charges at least eight exponent units for every
two-spin excitation step above the parity ground. -/
theorem eight_mul_spinFourParityExcitationLevel_le_casimirExcess
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    8 * spinFourParityExcitationLevel sourceSpin targetSpin ≤
      spinFourParityExcitationCasimirExcess sourceSpin targetSpin := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourParityExcitationLevel,
      spinFourParityExcitationCasimirExcess,
      spinFourParityGroundCasimirExponent, c4] at *

/-- The corresponding heat power factors exactly into parity-ground and
excitation powers. -/
theorem qpow_spinFourTargetCasimir_eqv_ground_mul_excitation
    (w : Q') {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    qpow w (c4 targetSpin) ≈
      qpow w (spinFourParityGroundCasimirExponent sourceSpin) *
        qpow w
          (spinFourParityExcitationCasimirExcess sourceSpin targetSpin) := by
  rw [spinFourTargetCasimir_eq_ground_add_excitationExcess
    hsource htarget hlowering]
  exact qpow_add w _ _

/-! ## 2. Oriented two-replica excitation observables -/

def finePacketOrientedTargetExcitationActivityAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Nat :=
  spinFourParityExcitationLevel
      (finePacketOrientedLeftSource S orientation first second faceId)
      (pair.1 faceId) +
    spinFourParityExcitationLevel
      (finePacketOrientedRightSource S orientation first second faceId)
      (pair.2 faceId)

def finePacketOrientedTotalTargetExcitationActivity
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  listNatWeight
    (finePacketOrientedTargetExcitationActivityAt
      S orientation first second pair)
    S.coarse.faceEdges

def finePacketOrientedTargetCasimirExcessAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Nat :=
  spinFourParityExcitationCasimirExcess
      (finePacketOrientedLeftSource S orientation first second faceId)
      (pair.1 faceId) +
    spinFourParityExcitationCasimirExcess
      (finePacketOrientedRightSource S orientation first second faceId)
      (pair.2 faceId)

def finePacketOrientedTotalTargetCasimirExcess
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  listNatWeight
    (finePacketOrientedTargetCasimirExcessAt
      S orientation first second pair)
    S.coarse.faceEdges

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

private theorem finePacketOrientedLeftSource_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    finePacketOrientedLeftSource S orientation
      first.1 second.1 faceId ≤ 4 := by
  cases orientation with
  | forward =>
      unfold finePacketOrientedLeftSource
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff first.2.1 faceId hface
  | reverse =>
      unfold finePacketOrientedLeftSource
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff second.2.1 faceId hface

private theorem finePacketOrientedRightSource_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    finePacketOrientedRightSource S orientation
      first.1 second.1 faceId ≤ 4 := by
  cases orientation with
  | forward =>
      unfold finePacketOrientedRightSource
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff second.2.1 faceId hface
  | reverse =>
      unfold finePacketOrientedRightSource
      exact wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff first.2.1 faceId hface

theorem eight_mul_finePacketOrientedTargetExcitationActivityAt_le_excess
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    8 * finePacketOrientedTargetExcitationActivityAt
        S orientation first.1 second.1 pair faceId ≤
      finePacketOrientedTargetCasimirExcessAt
        S orientation first.1 second.1 pair faceId := by
  have hleftMem :=
    (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1
  have hrightMem :=
    (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2
  have hleft :=
    eight_mul_spinFourParityExcitationLevel_le_casimirExcess
      (finePacketOrientedLeftSource_le_four S hfineCutoff orientation
        first second faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff hleftMem.1
        faceId hface)
      (hleftMem.2 faceId hface)
  have hright :=
    eight_mul_spinFourParityExcitationLevel_le_casimirExcess
      (finePacketOrientedRightSource_le_four S hfineCutoff orientation
        first second faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff hrightMem.1
        faceId hface)
      (hrightMem.2 faceId hface)
  unfold finePacketOrientedTargetExcitationActivityAt
    finePacketOrientedTargetCasimirExcessAt
  omega

private theorem listNatWeight_mono_local {A : Type}
    (left right : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listNatWeight left items ≤ listNatWeight right items
  | [], _ => Nat.le_refl 0
  | head :: rest, hle => by
      have hhead := hle head List.mem_cons_self
      have hrest := listNatWeight_mono_local left right rest
        (fun item hitem =>
          hle item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight]
      omega

private theorem listNatWeight_scale_local {A : Type}
    (scale : Nat) (weight : A → Nat) : ∀ items : List A,
    listNatWeight (fun item => scale * weight item) items =
      scale * listNatWeight weight items
  | [] => rfl
  | _head :: rest => by
      simp only [listNatWeight]
      rw [listNatWeight_scale_local scale weight rest]
      rw [Nat.mul_add]

theorem eight_mul_finePacketOrientedTotalTargetExcitationActivity_le_excess
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    8 * finePacketOrientedTotalTargetExcitationActivity
        S orientation first.1 second.1 pair ≤
      finePacketOrientedTotalTargetCasimirExcess
        S orientation first.1 second.1 pair := by
  unfold finePacketOrientedTotalTargetExcitationActivity
    finePacketOrientedTotalTargetCasimirExcess
  rw [← listNatWeight_scale_local]
  apply listNatWeight_mono_local
  intro faceId hface
  exact
    eight_mul_finePacketOrientedTargetExcitationActivityAt_le_excess
      S hfineCutoff orientation first second pair hlowering faceId hface

/-! ## 3. Exact total exponent decomposition -/

def finePacketOrientedTargetParityGroundCasimirAt
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) (faceId : Nat) : Nat :=
  spinFourParityGroundCasimirExponent
      (finePacketOrientedLeftSource S orientation first second faceId) +
    spinFourParityGroundCasimirExponent
      (finePacketOrientedRightSource S orientation first second faceId)

def finePacketOrientedTotalTargetParityGroundCasimir
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : Nat :=
  listNatWeight
    (finePacketOrientedTargetParityGroundCasimirAt
      S orientation first second)
    S.coarse.faceEdges

private theorem slabPhysicalCasimirExponentOn_eq_listNatWeight
    (physical : EdgeLabelling) : ∀ faces : List Nat,
    slabPhysicalCasimirExponentOn physical faces =
      listNatWeight (fun faceId => c4 (physical faceId)) faces
  | [] => rfl
  | _head :: rest => by
      simp only [slabPhysicalCasimirExponentOn, listNatWeight]
      rw [slabPhysicalCasimirExponentOn_eq_listNatWeight physical rest]

private theorem listNatWeight_pair_decomposition_local {A : Type}
    (left right ground excess : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items →
      left item + right item = ground item + excess item) →
    listNatWeight left items + listNatWeight right items =
      listNatWeight ground items + listNatWeight excess items
  | [], _ => rfl
  | head :: rest, hpointwise => by
      have hhead := hpointwise head List.mem_cons_self
      have hrest := listNatWeight_pair_decomposition_local
        left right ground excess rest
        (fun item hitem =>
          hpointwise item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight]
      omega

theorem finePacketOrientedTargetCasimir_exact_decomposition
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    slabPhysicalCasimirExponent S.coarse.extent pair.1 +
        slabPhysicalCasimirExponent S.coarse.extent pair.2 =
      finePacketOrientedTotalTargetParityGroundCasimir
          S orientation first.1 second.1 +
        finePacketOrientedTotalTargetCasimirExcess
          S orientation first.1 second.1 pair := by
  have hleftMem :=
    (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1
  have hrightMem :=
    (mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2
  unfold slabPhysicalCasimirExponent
  change
    slabPhysicalCasimirExponentOn pair.1 S.coarse.faceEdges +
        slabPhysicalCasimirExponentOn pair.2 S.coarse.faceEdges = _
  rw [slabPhysicalCasimirExponentOn_eq_listNatWeight,
    slabPhysicalCasimirExponentOn_eq_listNatWeight]
  unfold finePacketOrientedTotalTargetParityGroundCasimir
    finePacketOrientedTotalTargetCasimirExcess
  apply listNatWeight_pair_decomposition_local
  intro faceId hface
  have hleftEq := spinFourTargetCasimir_eq_ground_add_excitationExcess
    (finePacketOrientedLeftSource_le_four S hfineCutoff orientation
      first second faceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff hleftMem.1
      faceId hface)
    (hleftMem.2 faceId hface)
  have hrightEq := spinFourTargetCasimir_eq_ground_add_excitationExcess
    (finePacketOrientedRightSource_le_four S hfineCutoff orientation
      first second faceId hface)
    (coarseTargetSpin_le_four_local S hfineCutoff hrightMem.1
      faceId hface)
    (hrightMem.2 faceId hface)
  unfold finePacketOrientedTargetParityGroundCasimirAt
    finePacketOrientedTargetCasimirExcessAt
  omega

/-! ## 4. The joint contour is an actual mixed heat-exponent budget -/

private theorem listNatWeight_four_split_local {A : Type}
    (a b c d : A → Nat) : ∀ items : List A,
    listNatWeight (fun item => a item + b item + c item + d item) items =
      listNatWeight (fun item => a item + b item) items +
        listNatWeight (fun item => c item + d item) items
  | [] => rfl
  | _head :: rest => by
      simp only [listNatWeight]
      rw [listNatWeight_four_split_local a b c d rest]
      omega

theorem finePacketOrientedTotalJointActivity_eq_source_add_targetExcitation
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedTotalJointActivity
        S orientation first second pair =
      finePacketOrientedTotalSourceActivity S orientation first second +
        finePacketOrientedTotalTargetExcitationActivity
          S orientation first second pair := by
  unfold finePacketOrientedTotalJointActivity
    finePacketOrientedJointActivityAt
    finePacketOrientedTotalSourceActivity
    finePacketOrientedTotalTargetExcitationActivity
    finePacketOrientedTargetExcitationActivityAt
  exact listNatWeight_four_split_local _ _ _ _ _

/-- A connected oriented lowering path pays three times its endpoint
separation in the actual fine Casimir exponent plus coarse SU(2) Casimir
excess. -/
theorem finePacketOrientedConnectedPath_scaledHeatActivity_floor
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
    3 * (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) ≤
      3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
          fineCouplingPhysicalOccupiedFaceCount S second.1) +
        finePacketOrientedTotalTargetCasimirExcess
          S orientation first.1 second.1 pair := by
  have hjoint := finePacketOrientedConnectedPath_jointActivity_floor
    S hfineCutoff orientation first second observableFaceId
      hobservableFace pair hlowering path
  have hsplit :=
    finePacketOrientedTotalJointActivity_eq_source_add_targetExcitation
      S orientation first.1 second.1 pair
  have hsource :=
    finePacketOrientedTotalSourceActivity_le_occupiedFaceCounts
      S hfineCutoff orientation first second
  have htarget :=
    eight_mul_finePacketOrientedTotalTargetExcitationActivity_le_excess
      S hfineCutoff orientation first second pair hlowering
  omega

theorem finePacketForwardNonzeroConnectedPair_scaledHeatActivity_floor
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
    3 * (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) ≤
      3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
          fineCouplingPhysicalOccupiedFaceCount S second.1) +
        finePacketOrientedTotalTargetCasimirExcess
          S .forward first.1 second.1 pair := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact finePacketOrientedConnectedPath_scaledHeatActivity_floor
    S hfineCutoff .forward first second observableFaceId
      hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

theorem finePacketReverseNonzeroConnectedPair_scaledHeatActivity_floor
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
    3 * (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) ≤
      3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
          fineCouplingPhysicalOccupiedFaceCount S second.1) +
        finePacketOrientedTotalTargetCasimirExcess
          S .reverse first.1 second.1 pair := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact finePacketOrientedConnectedPath_scaledHeatActivity_floor
    S hfineCutoff .reverse first second observableFaceId
      hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

/-! ## 5. Axiom audit -/

#print axioms spinFourParityGroundCasimirExponent
#print axioms spinFourParityExcitationCasimirExcess
#print axioms spinFourParityGroundSpin_le_target
#print axioms spinFourParityGroundCasimir_le_target
#print axioms spinFourTargetCasimir_eq_ground_add_excitationExcess
#print axioms eight_mul_spinFourParityExcitationLevel_le_casimirExcess
#print axioms qpow_spinFourTargetCasimir_eqv_ground_mul_excitation
#print axioms finePacketOrientedTargetExcitationActivityAt
#print axioms finePacketOrientedTotalTargetExcitationActivity
#print axioms finePacketOrientedTargetCasimirExcessAt
#print axioms finePacketOrientedTotalTargetCasimirExcess
#print axioms eight_mul_finePacketOrientedTargetExcitationActivityAt_le_excess
#print axioms eight_mul_finePacketOrientedTotalTargetExcitationActivity_le_excess
#print axioms finePacketOrientedTargetParityGroundCasimirAt
#print axioms finePacketOrientedTotalTargetParityGroundCasimir
#print axioms finePacketOrientedTargetCasimir_exact_decomposition
#print axioms finePacketOrientedTotalJointActivity_eq_source_add_targetExcitation
#print axioms finePacketOrientedConnectedPath_scaledHeatActivity_floor
#print axioms finePacketForwardNonzeroConnectedPair_scaledHeatActivity_floor
#print axioms finePacketReverseNonzeroConnectedPair_scaledHeatActivity_floor

end YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
