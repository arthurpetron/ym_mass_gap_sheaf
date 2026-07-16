/-
# Uniform normalized stability for an affine uniformly shifted cylinder

The shifted four-cell switch and its connected-carrier shell estimate contain
the exact full-target and embedded-target partition factors.  This file
identifies the resulting division-free determinant and cancels only the
constructively positive finite partitions.  The conclusion is uniform in the
cutoff, the target volume, the affine uniform padding, and every rational coupling
between zero and the derived anchor.
-/

import YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
import YMGap.Continuum.Z4UniformShiftConnectedCarrierBoundaryTail

namespace YMGap.Continuum.Z4UniformShiftTargetCylinderStability

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftConnectedCarrierBoundaryTail
open YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The shifted four-cell determinant -/

def couplingParametricKUniformShiftBoundaryTargetPartition
    (coupling : Q') (cutoff padding base : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    (uniformShiftBoundaryTargetFamilies padding base)

def couplingParametricKUniformShiftBoundaryTargetEventNumerator
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    ((uniformShiftBoundaryTargetFamilies padding base).filter event)

def couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    ((uniformShiftEmbeddedTargetFamilies padding base).filter
      (fun family => !(event family)))

def couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base))
    ((uniformShiftBoundaryTargetFamilies padding base).filter
      (fun family => !(event family)))

private theorem shifted_filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

theorem uniformShiftEmbeddedTargetFamilies_eq_filter_all
    (padding base : Nat) :
    uniformShiftEmbeddedTargetFamilies padding base =
      (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)).filter
        (fun family =>
          family.all (targetRootInsideUniformShiftB padding base)) := by
  unfold uniformShiftEmbeddedTargetFamilies
  apply List.filter_congr
  intro family hfamily
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro himageDecision
    have himage : family ∈
        uniformShiftEmbeddedCompatibleFamilies padding base :=
      of_decide_eq_true himageDecision
    apply List.all_eq_true.mpr
    intro target htarget
    apply (targetRootInsideUniformShiftB_true_iff padding base target).2
    exact (mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
      hfamily).1 himage target htarget
  · intro hall
    apply decide_eq_true
    apply (mem_uniformShiftEmbeddedCompatibleFamilies_iff_all_inside
      hfamily).2
    intro target htarget
    exact (targetRootInsideUniformShiftB_true_iff padding base target).1
      (List.all_eq_true.mp hall target htarget)

theorem couplingParametricKUniformShiftCompatiblePartition_eqv_embedded_add_boundary
    (coupling : Q') (cutoff padding base : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (uniformPaddedBase padding base) ≈
      couplingParametricKUniformShiftEmbeddedTargetPartition
          coupling cutoff padding base +
        couplingParametricKUniformShiftBoundaryTargetPartition
          coupling cutoff padding base := by
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKUniformShiftEmbeddedTargetPartition
    couplingParametricKUniformShiftBoundaryTargetPartition
    uniformShiftBoundaryTargetFamilies
  rw [uniformShiftEmbeddedTargetFamilies_eq_filter_all]
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (fun family => family.all
      (targetRootInsideUniformShiftB padding base))
    (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))

theorem couplingParametricKUniformShiftCompatibleEventNumerator_eqv_embedded_add_boundary
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (uniformPaddedBase padding base) event ≈
      couplingParametricKUniformShiftEmbeddedTargetEventNumerator
          coupling cutoff padding base event +
        couplingParametricKUniformShiftBoundaryTargetEventNumerator
          coupling cutoff padding base event := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
    couplingParametricKUniformShiftBoundaryTargetEventNumerator
    uniformShiftBoundaryTargetFamilies
  rw [uniformShiftEmbeddedTargetFamilies_eq_filter_all]
  rw [shifted_filters_commute
      (fun family : List (List Nat) =>
        family.all (targetRootInsideUniformShiftB padding base)) event,
    shifted_filters_commute
      (fun family : List (List Nat) =>
        !(family.all (targetRootInsideUniformShiftB padding base))) event]
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (fun family => family.all
      (targetRootInsideUniformShiftB padding base))
    ((canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)).filter event)

theorem couplingParametricKUniformShiftEmbeddedPartition_eqv_event_add_complement
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base ≈
      couplingParametricKUniformShiftEmbeddedTargetEventNumerator
          coupling cutoff padding base event +
        couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
          coupling cutoff padding base event := by
  unfold couplingParametricKUniformShiftEmbeddedTargetPartition
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
    couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base)) event
    (uniformShiftEmbeddedTargetFamilies padding base)

theorem couplingParametricKUniformShiftBoundaryPartition_eqv_event_add_complement
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftBoundaryTargetPartition
        coupling cutoff padding base ≈
      couplingParametricKUniformShiftBoundaryTargetEventNumerator
          coupling cutoff padding base event +
        couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator
          coupling cutoff padding base event := by
  unfold couplingParametricKUniformShiftBoundaryTargetPartition
    couplingParametricKUniformShiftBoundaryTargetEventNumerator
    couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base)) event
    (uniformShiftBoundaryTargetFamilies padding base)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

def couplingParametricKUniformShiftTargetEventCrossDifference
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (uniformPaddedBase padding base) event *
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base -
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base event *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (uniformPaddedBase padding base)

def couplingParametricKUniformShiftBoundaryCrossDifference
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKUniformShiftBoundaryTargetEventNumerator
        coupling cutoff padding base event *
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base -
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base event *
      couplingParametricKUniformShiftBoundaryTargetPartition
        coupling cutoff padding base

def couplingParametricKUniformShiftBoundaryCellCrossDifference
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKUniformShiftBoundaryTargetEventNumerator
        coupling cutoff padding base event *
      couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
        coupling cutoff padding base event -
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base event *
      couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator
        coupling cutoff padding base event

theorem couplingParametricKUniformShiftTargetEventCrossDifference_eqv_boundary
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftTargetEventCrossDifference
        coupling cutoff padding base event ≈
      couplingParametricKUniformShiftBoundaryCrossDifference
        coupling cutoff padding base event := by
  have hnum :=
    couplingParametricKUniformShiftCompatibleEventNumerator_eqv_embedded_add_boundary
      coupling cutoff padding base event
  have hden :=
    couplingParametricKUniformShiftCompatiblePartition_eqv_embedded_add_boundary
      coupling cutoff padding base
  unfold couplingParametricKUniformShiftTargetEventCrossDifference
    couplingParametricKUniformShiftBoundaryCrossDifference
  refine Q'.eqv_trans _
    ((couplingParametricKUniformShiftEmbeddedTargetEventNumerator
            coupling cutoff padding base event +
          couplingParametricKUniformShiftBoundaryTargetEventNumerator
            coupling cutoff padding base event) *
        couplingParametricKUniformShiftEmbeddedTargetPartition
          coupling cutoff padding base -
      couplingParametricKUniformShiftEmbeddedTargetEventNumerator
          coupling cutoff padding base event *
        (couplingParametricKUniformShiftEmbeddedTargetPartition
            coupling cutoff padding base +
          couplingParametricKUniformShiftBoundaryTargetPartition
            coupling cutoff padding base)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local hnum (Q'.eqv_refl _))
      (mul_eqv_both_local (Q'.eqv_refl _) hden)
  · exact crossDifference_split
      (couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base event)
      (couplingParametricKUniformShiftBoundaryTargetEventNumerator
        coupling cutoff padding base event)
      (couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base)
      (couplingParametricKUniformShiftBoundaryTargetPartition
        coupling cutoff padding base)

theorem couplingParametricKUniformShiftBoundaryCrossDifference_eqv_cells
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftBoundaryCrossDifference
        coupling cutoff padding base event ≈
      couplingParametricKUniformShiftBoundaryCellCrossDifference
        coupling cutoff padding base event := by
  have hembedded :=
    couplingParametricKUniformShiftEmbeddedPartition_eqv_event_add_complement
      coupling cutoff padding base event
  have hboundary :=
    couplingParametricKUniformShiftBoundaryPartition_eqv_event_add_complement
      coupling cutoff padding base event
  unfold couplingParametricKUniformShiftBoundaryCrossDifference
    couplingParametricKUniformShiftBoundaryCellCrossDifference
  refine Q'.eqv_trans _ _ _
    (sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_refl _) hembedded)
      (mul_eqv_both_local (Q'.eqv_refl _) hboundary)) ?_
  exact eventBoundaryCrossDifference_cells
    (couplingParametricKUniformShiftEmbeddedTargetEventNumerator
      coupling cutoff padding base event)
    (couplingParametricKUniformShiftBoundaryTargetEventNumerator
      coupling cutoff padding base event)
    (couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
      coupling cutoff padding base event)
    (couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator
      coupling cutoff padding base event)

theorem couplingParametricKUniformShiftTargetEventCrossDifference_eqv_cells
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftTargetEventCrossDifference
        coupling cutoff padding base event ≈
      couplingParametricKUniformShiftBoundaryCellCrossDifference
        coupling cutoff padding base event :=
  Q'.eqv_trans _ _ _
    (couplingParametricKUniformShiftTargetEventCrossDifference_eqv_boundary
      coupling cutoff padding base event)
    (couplingParametricKUniformShiftBoundaryCrossDifference_eqv_cells
      coupling cutoff padding base event)

/-! ## 2. Connected residue and exact normalized boundary scale -/

def uniformShiftSpinSummedCylinderBoundaryEpsilon
    (rootCount distance : Nat) : Q' :=
  Q'.ofNat rootCount *
    (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)

theorem couplingParametricKUniformShiftBoundaryCellCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    couplingParametricKUniformShiftBoundaryCellCrossDifference
        coupling cutoff padding base
        (uniformShiftMarkedCylinderEvent roots predicate) ≤
      listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedUniformShiftCylinderSourcePairs
          (padding := padding) (base := base)
          (roots := roots) (predicate := predicate)) := by
  have hraw :=
    couplingSpinSummedUniformShiftBoundaryEvent_embeddedComplement_le
      hcoupling cutoff padding base roots predicate
  unfold couplingParametricKUniformShiftBoundaryCellCrossDifference
    couplingParametricKUniformShiftBoundaryTargetEventNumerator
    couplingParametricKUniformShiftEmbeddedTargetEventComplementNumerator
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
    couplingParametricKUniformShiftBoundaryTargetEventComplementNumerator at ⊢
  unfold
    uniformShiftBoundaryCylinderEventFamilyList
    uniformShiftEmbeddedCylinderComplementFamilyList
    uniformShiftBoundaryCylinderComplementFamilyList
    uniformShiftEmbeddedCylinderEventFamilyList at hraw
  have hreordered := Q'.le_trans' _ _ _ hraw
    (Q'.add_le_add
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_refl' _))
  exact Q'.sub_le_of_le_add hreordered

theorem couplingParametricKUniformShiftTargetCylinderCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    couplingParametricKUniformShiftTargetEventCrossDifference
        coupling cutoff padding base
        (uniformShiftMarkedCylinderEvent roots predicate) ≤
      listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedUniformShiftCylinderSourcePairs
          (padding := padding) (base := base)
          (roots := roots) (predicate := predicate)) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingParametricKUniformShiftTargetEventCrossDifference_eqv_cells
        coupling cutoff padding base
        (uniformShiftMarkedCylinderEvent roots predicate)))
    (couplingParametricKUniformShiftBoundaryCellCrossDifference_le_connected
      hcoupling cutoff padding base roots predicate)

theorem couplingParametricKUniformShiftTargetCylinderCrossDifference_le_boundaryEpsilon
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKUniformShiftTargetEventCrossDifference
        coupling cutoff padding base
        (uniformShiftMarkedCylinderEvent roots predicate) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon roots.length distance *
        (couplingParametricKUniformShiftEmbeddedTargetPartition
            coupling cutoff padding base *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (uniformPaddedBase padding base)) := by
  have hconnected :=
    couplingParametricKUniformShiftTargetCylinderCrossDifference_le_connected
      hcoupling cutoff padding base roots predicate
  have htail :=
    couplingSpinSummedConnectedUniformShiftCylinderPairSum_le_tail
      (predicate := predicate) hcoupling hle cutoff hrootsInside
        rootStart hstartMem
        hrootCore houterExit
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  refine Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv ?_)
  unfold uniformShiftSpinSummedCylinderBoundaryEpsilon
  ring_qeqv

/-! ## 3. Cancellation through positive finite partitions -/

theorem couplingParametricKUniformShiftTargetProbability_sub_embedded_le_of_cross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat) (event : List (List Nat) → Bool)
    (epsilon : Q')
    (hcross :
      couplingParametricKUniformShiftTargetEventCrossDifference
          coupling cutoff padding base event ≤
        epsilon *
          (couplingParametricKUniformShiftEmbeddedTargetPartition
              coupling cutoff padding base *
            couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (uniformPaddedBase padding base))) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (uniformPaddedBase padding base) event -
        couplingParametricKUniformShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff padding base event ≤
      epsilon := by
  let targetNumerator :=
    couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (uniformPaddedBase padding base) event
  let embeddedNumerator :=
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
      coupling cutoff padding base event
  let targetPartition :=
    couplingParametricKCompatibleSupportGasPartition
      coupling cutoff (uniformPaddedBase padding base)
  let embeddedPartition :=
    couplingParametricKUniformShiftEmbeddedTargetPartition
      coupling cutoff padding base
  have hadd :
      targetNumerator * embeddedPartition ≤
        embeddedNumerator * targetPartition +
          epsilon * (embeddedPartition * targetPartition) := by
    apply le_add_of_sub_le_local
    exact hcross
  have hreorder :
      (embeddedNumerator * targetPartition +
          epsilon * (embeddedPartition * targetPartition)).eqv
        ((embeddedNumerator + epsilon * embeddedPartition) *
          targetPartition) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (embeddedNumerator * targetPartition)
        (epsilon * (embeddedPartition * targetPartition))
        ((epsilon * embeddedPartition) * targetPartition)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon embeddedPartition targetPartition))) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv embeddedNumerator
        (epsilon * embeddedPartition) targetPartition)
  have hratio := divPos_le_divPos_of_cross_local
    targetNumerator targetPartition
    (embeddedNumerator + epsilon * embeddedPartition) embeddedPartition
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff (uniformPaddedBase padding base))
    (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
      hcoupling cutoff padding base)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    embeddedNumerator epsilon embeddedPartition
    (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
      hcoupling cutoff padding base)
  have hprob :
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (uniformPaddedBase padding base) event ≤
        couplingParametricKUniformShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff padding base event + epsilon := by
    unfold couplingParametricKCompatibleSupportEventProbability
      couplingParametricKUniformShiftEmbeddedTargetEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem couplingParametricKUniformShiftTargetCylinderProbability_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (uniformPaddedBase padding base)
          (uniformShiftMarkedCylinderEvent roots predicate) -
        couplingParametricKUniformShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff padding base
          (uniformShiftMarkedCylinderEvent roots predicate) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  apply couplingParametricKUniformShiftTargetProbability_sub_embedded_le_of_cross
    hcoupling
  exact
    couplingParametricKUniformShiftTargetCylinderCrossDifference_le_boundaryEpsilon
      hcoupling hle cutoff hrootsInside rootStart hstartMem
        hrootCore houterExit

/-! ## 4. Complement symmetry and the two-sided modulus -/

theorem couplingParametricKUniformShiftEmbeddedTargetEventNumerator_add_complement_eqv_partition
    (coupling : Q') (cutoff padding base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator
          coupling cutoff padding base event +
        couplingParametricKUniformShiftEmbeddedTargetEventNumerator
          coupling cutoff padding base (fun family => !(event family)) ≈
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base := by
  exact Q'.eqv_symm
    (couplingParametricKUniformShiftEmbeddedPartition_eqv_event_add_complement
      coupling cutoff padding base event)

private theorem shifted_add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem couplingParametricKUniformShiftEmbeddedTargetEventProbability_add_complement_eqv_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKUniformShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff padding base event +
        couplingParametricKUniformShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff padding base
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    couplingParametricKUniformShiftEmbeddedTargetEventNumerator_add_complement_eqv_partition
      coupling cutoff padding base event
  unfold couplingParametricKUniformShiftEmbeddedTargetEventProbability
  refine Q'.eqv_trans _ _ _
    (shifted_add_divPos_eqv_local
      (couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base event)
      (couplingParametricKUniformShiftEmbeddedTargetEventNumerator
        coupling cutoff padding base (fun family => !(event family)))
      (couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base)
      (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
        hcoupling cutoff padding base)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (couplingParametricKUniformShiftEmbeddedTargetPartition
          coupling cutoff padding base)
        (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
          hcoupling cutoff padding base)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (couplingParametricKUniformShiftEmbeddedTargetPartition
      coupling cutoff padding base)
    (couplingParametricKUniformShiftEmbeddedTargetPartition_pos
      hcoupling cutoff padding base)

private theorem shifted_left_eqv_one_sub_right {a complement : Q'}
    (hsum : a + complement ≈ (1 : Q')) :
    a ≈ (1 : Q') - complement := by
  refine Q'.eqv_trans _ (a + 0) _
    (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' a))) ?_
  refine Q'.eqv_trans _ (a + (complement + (-complement))) _
    (Q'.add_eqv_congr_left a 0 (complement + (-complement))
      (Q'.eqv_symm (Q'.add_neg_self_eqv complement))) ?_
  refine Q'.eqv_trans _ ((a + complement) + (-complement)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv a complement (-complement))) ?_
  exact Q'.add_eqv_congr_right
    (a + complement) 1 (-complement) hsum

private theorem shifted_eventReverseSub_eqv_complementSub
    {a aComplement b bComplement : Q'}
    (ha : a + aComplement ≈ (1 : Q'))
    (hb : b + bComplement ≈ (1 : Q')) :
    a - b ≈ bComplement - aComplement := by
  refine Q'.eqv_trans _
    (((1 : Q') - aComplement) - ((1 : Q') - bComplement)) _
    (sub_eqv_both_local
      (shifted_left_eqv_one_sub_right ha)
      (shifted_left_eqv_one_sub_right hb)) ?_
  change
    ((1 + (-aComplement)) + (-(1 + (-bComplement)))).eqv
      (bComplement + (-aComplement))
  have hneg : (-(1 + (-bComplement))).eqv
      ((-1) + bComplement) := by
    refine Q'.eqv_trans _ ((-1) + (-(-bComplement))) _
      (Q'.neg_add_eqv 1 (-bComplement)) ?_
    exact Q'.add_eqv_congr_left (-1) (-(-bComplement)) bComplement
      (Q'.neg_neg_eqv bComplement)
  refine Q'.eqv_trans _
    ((1 + (-aComplement)) + ((-1) + bComplement)) _
    (Q'.add_eqv_congr_left (1 + (-aComplement)) _ _ hneg) ?_
  refine Q'.eqv_trans _
    ((1 + (-1)) + ((-aComplement) + bComplement)) _
    (Q'.add_swap_inner 1 (-aComplement) (-1) bComplement) ?_
  refine Q'.eqv_trans _
    (0 + ((-aComplement) + bComplement)) _
    (Q'.add_eqv_congr_right (1 + (-1)) 0
      ((-aComplement) + bComplement)
      (Q'.add_neg_self_eqv 1)) ?_
  refine Q'.eqv_trans _ ((-aComplement) + bComplement) _
    (Q'.eqv_of_eq (Q'.zero_add' ((-aComplement) + bComplement))) ?_
  exact Q'.add_comm_eqv (-aComplement) bComplement

theorem couplingParametricKUniformShiftEmbeddedCylinderProbability_sub_target_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKUniformShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff padding base
          (uniformShiftMarkedCylinderEvent roots predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (uniformPaddedBase padding base)
          (uniformShiftMarkedCylinderEvent roots predicate) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  let event := uniformShiftMarkedCylinderEvent roots predicate
  let complementEvent := uniformShiftMarkedCylinderEvent roots
    (spinSummedComplementCylinderPredicate predicate)
  have hcomplement :=
    couplingParametricKUniformShiftTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff (predicate :=
        spinSummedComplementCylinderPredicate predicate)
      hrootsInside rootStart hstartMem hrootCore houterExit
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hembeddedSum :
      couplingParametricKUniformShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff padding base event +
          couplingParametricKUniformShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff padding base complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKUniformShiftEmbeddedTargetEventProbability_add_complement_eqv_one
        hcoupling cutoff padding base event
  have htargetSum :
      couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (uniformPaddedBase padding base) event +
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (uniformPaddedBase padding base) complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact couplingParametricKCompatibleEventProbability_add_complement_eqv_one
      hcoupling cutoff (uniformPaddedBase padding base) event
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (shifted_eventReverseSub_eqv_complementSub
        hembeddedSum htargetSum))
    hcomplement

private theorem shifted_sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

theorem couplingParametricKUniformShiftTargetCylinderProbability_abs_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (uniformPaddedBase padding base)
            (uniformShiftMarkedCylinderEvent roots predicate) -
          couplingParametricKUniformShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff padding base
            (uniformShiftMarkedCylinderEvent roots predicate)) ≤
      uniformShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  apply Q'.abs_le
  · have hreverse :=
      couplingParametricKUniformShiftEmbeddedCylinderProbability_sub_target_le
        (predicate := predicate) hcoupling hle cutoff hrootsInside
          rootStart hstartMem
          hrootCore houterExit
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (shifted_sub_swap_eqv_neg_local
            (couplingParametricKUniformShiftEmbeddedTargetEventProbability
              coupling hcoupling cutoff padding base
              (uniformShiftMarkedCylinderEvent roots predicate))
            (couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff (uniformPaddedBase padding base)
              (uniformShiftMarkedCylinderEvent roots predicate)))))
  · exact couplingParametricKUniformShiftTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff hrootsInside rootStart hstartMem
        hrootCore houterExit

#print axioms couplingParametricKUniformShiftCompatiblePartition_eqv_embedded_add_boundary
#print axioms couplingParametricKUniformShiftCompatibleEventNumerator_eqv_embedded_add_boundary
#print axioms couplingParametricKUniformShiftTargetEventCrossDifference_eqv_cells
#print axioms couplingParametricKUniformShiftBoundaryCellCrossDifference_le_connected
#print axioms couplingParametricKUniformShiftTargetCylinderCrossDifference_le_boundaryEpsilon
#print axioms couplingParametricKUniformShiftTargetProbability_sub_embedded_le_of_cross
#print axioms couplingParametricKUniformShiftTargetCylinderProbability_sub_embedded_le
#print axioms couplingParametricKUniformShiftEmbeddedTargetEventProbability_add_complement_eqv_one
#print axioms couplingParametricKUniformShiftEmbeddedCylinderProbability_sub_target_le
#print axioms couplingParametricKUniformShiftTargetCylinderProbability_abs_sub_embedded_le

end YMGap.Continuum.Z4UniformShiftTargetCylinderStability
