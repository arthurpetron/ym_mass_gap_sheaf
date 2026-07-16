/-
# Uniform normalized stability for an affine time-shifted cylinder

The shifted four-cell switch and its connected-carrier shell estimate contain
the exact full-target and embedded-target partition factors.  This file
identifies the resulting division-free determinant and cancels only the
constructively positive finite partitions.  The conclusion is uniform in the
cutoff, the target volume, the affine time shift, and every rational coupling
between zero and the derived anchor.
-/

import YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
import YMGap.Continuum.Z4TimeShiftedConnectedCarrierBoundaryTail

namespace YMGap.Continuum.Z4TimeShiftedTargetCylinderStability

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
open YMGap.Continuum.Z4TimeShiftedConnectedCarrierBoundaryTail
open YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. The shifted four-cell determinant -/

def couplingParametricKTimeShiftBoundaryTargetPartition
    (coupling : Q') (cutoff shift base : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    (timeShiftBoundaryTargetFamilies shift base)

def couplingParametricKTimeShiftBoundaryTargetEventNumerator
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    ((timeShiftBoundaryTargetFamilies shift base).filter event)

def couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    ((timeShiftEmbeddedTargetFamilies shift base).filter
      (fun family => !(event family)))

def couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift))
    ((timeShiftBoundaryTargetFamilies shift base).filter
      (fun family => !(event family)))

private theorem shifted_filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

theorem timeShiftEmbeddedTargetFamilies_eq_filter_all
    (shift base : Nat) :
    timeShiftEmbeddedTargetFamilies shift base =
      (canonicalCompatibleAmbientFamilies (base + shift)).filter
        (fun family =>
          family.all (targetRootInsideTimeShiftB shift base)) := by
  unfold timeShiftEmbeddedTargetFamilies
  apply List.filter_congr
  intro family hfamily
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro himageDecision
    have himage : family ∈
        timeShiftEmbeddedCompatibleFamilies shift base :=
      of_decide_eq_true himageDecision
    apply List.all_eq_true.mpr
    intro target htarget
    apply (targetRootInsideTimeShiftB_true_iff shift base target).2
    exact (mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
      hfamily).1 himage target htarget
  · intro hall
    apply decide_eq_true
    apply (mem_timeShiftEmbeddedCompatibleFamilies_iff_all_inside
      hfamily).2
    intro target htarget
    exact (targetRootInsideTimeShiftB_true_iff shift base target).1
      (List.all_eq_true.mp hall target htarget)

theorem couplingParametricKTimeShiftCompatiblePartition_eqv_embedded_add_boundary
    (coupling : Q') (cutoff shift base : Nat) :
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift) ≈
      couplingParametricKTimeShiftEmbeddedTargetPartition
          coupling cutoff shift base +
        couplingParametricKTimeShiftBoundaryTargetPartition
          coupling cutoff shift base := by
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKTimeShiftEmbeddedTargetPartition
    couplingParametricKTimeShiftBoundaryTargetPartition
    timeShiftBoundaryTargetFamilies
  rw [timeShiftEmbeddedTargetFamilies_eq_filter_all]
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (fun family => family.all
      (targetRootInsideTimeShiftB shift base))
    (canonicalCompatibleAmbientFamilies (base + shift))

theorem couplingParametricKTimeShiftCompatibleEventNumerator_eqv_embedded_add_boundary
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (base + shift) event ≈
      couplingParametricKTimeShiftEmbeddedTargetEventNumerator
          coupling cutoff shift base event +
        couplingParametricKTimeShiftBoundaryTargetEventNumerator
          coupling cutoff shift base event := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
    couplingParametricKTimeShiftBoundaryTargetEventNumerator
    timeShiftBoundaryTargetFamilies
  rw [timeShiftEmbeddedTargetFamilies_eq_filter_all]
  rw [shifted_filters_commute
      (fun family : List (List Nat) =>
        family.all (targetRootInsideTimeShiftB shift base)) event,
    shifted_filters_commute
      (fun family : List (List Nat) =>
        !(family.all (targetRootInsideTimeShiftB shift base))) event]
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (fun family => family.all
      (targetRootInsideTimeShiftB shift base))
    ((canonicalCompatibleAmbientFamilies (base + shift)).filter event)

theorem couplingParametricKTimeShiftEmbeddedPartition_eqv_event_add_complement
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base ≈
      couplingParametricKTimeShiftEmbeddedTargetEventNumerator
          coupling cutoff shift base event +
        couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
          coupling cutoff shift base event := by
  unfold couplingParametricKTimeShiftEmbeddedTargetPartition
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
    couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift)) event
    (timeShiftEmbeddedTargetFamilies shift base)

theorem couplingParametricKTimeShiftBoundaryPartition_eqv_event_add_complement
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftBoundaryTargetPartition
        coupling cutoff shift base ≈
      couplingParametricKTimeShiftBoundaryTargetEventNumerator
          coupling cutoff shift base event +
        couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator
          coupling cutoff shift base event := by
  unfold couplingParametricKTimeShiftBoundaryTargetPartition
    couplingParametricKTimeShiftBoundaryTargetEventNumerator
    couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift)) event
    (timeShiftBoundaryTargetFamilies shift base)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

def couplingParametricKTimeShiftTargetEventCrossDifference
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (base + shift) event *
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base -
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base event *
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift)

def couplingParametricKTimeShiftBoundaryCrossDifference
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKTimeShiftBoundaryTargetEventNumerator
        coupling cutoff shift base event *
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base -
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base event *
      couplingParametricKTimeShiftBoundaryTargetPartition
        coupling cutoff shift base

def couplingParametricKTimeShiftBoundaryCellCrossDifference
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKTimeShiftBoundaryTargetEventNumerator
        coupling cutoff shift base event *
      couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
        coupling cutoff shift base event -
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base event *
      couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator
        coupling cutoff shift base event

theorem couplingParametricKTimeShiftTargetEventCrossDifference_eqv_boundary
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftTargetEventCrossDifference
        coupling cutoff shift base event ≈
      couplingParametricKTimeShiftBoundaryCrossDifference
        coupling cutoff shift base event := by
  have hnum :=
    couplingParametricKTimeShiftCompatibleEventNumerator_eqv_embedded_add_boundary
      coupling cutoff shift base event
  have hden :=
    couplingParametricKTimeShiftCompatiblePartition_eqv_embedded_add_boundary
      coupling cutoff shift base
  unfold couplingParametricKTimeShiftTargetEventCrossDifference
    couplingParametricKTimeShiftBoundaryCrossDifference
  refine Q'.eqv_trans _
    ((couplingParametricKTimeShiftEmbeddedTargetEventNumerator
            coupling cutoff shift base event +
          couplingParametricKTimeShiftBoundaryTargetEventNumerator
            coupling cutoff shift base event) *
        couplingParametricKTimeShiftEmbeddedTargetPartition
          coupling cutoff shift base -
      couplingParametricKTimeShiftEmbeddedTargetEventNumerator
          coupling cutoff shift base event *
        (couplingParametricKTimeShiftEmbeddedTargetPartition
            coupling cutoff shift base +
          couplingParametricKTimeShiftBoundaryTargetPartition
            coupling cutoff shift base)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local hnum (Q'.eqv_refl _))
      (mul_eqv_both_local (Q'.eqv_refl _) hden)
  · exact crossDifference_split
      (couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base event)
      (couplingParametricKTimeShiftBoundaryTargetEventNumerator
        coupling cutoff shift base event)
      (couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base)
      (couplingParametricKTimeShiftBoundaryTargetPartition
        coupling cutoff shift base)

theorem couplingParametricKTimeShiftBoundaryCrossDifference_eqv_cells
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftBoundaryCrossDifference
        coupling cutoff shift base event ≈
      couplingParametricKTimeShiftBoundaryCellCrossDifference
        coupling cutoff shift base event := by
  have hembedded :=
    couplingParametricKTimeShiftEmbeddedPartition_eqv_event_add_complement
      coupling cutoff shift base event
  have hboundary :=
    couplingParametricKTimeShiftBoundaryPartition_eqv_event_add_complement
      coupling cutoff shift base event
  unfold couplingParametricKTimeShiftBoundaryCrossDifference
    couplingParametricKTimeShiftBoundaryCellCrossDifference
  refine Q'.eqv_trans _ _ _
    (sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_refl _) hembedded)
      (mul_eqv_both_local (Q'.eqv_refl _) hboundary)) ?_
  exact eventBoundaryCrossDifference_cells
    (couplingParametricKTimeShiftEmbeddedTargetEventNumerator
      coupling cutoff shift base event)
    (couplingParametricKTimeShiftBoundaryTargetEventNumerator
      coupling cutoff shift base event)
    (couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
      coupling cutoff shift base event)
    (couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator
      coupling cutoff shift base event)

theorem couplingParametricKTimeShiftTargetEventCrossDifference_eqv_cells
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftTargetEventCrossDifference
        coupling cutoff shift base event ≈
      couplingParametricKTimeShiftBoundaryCellCrossDifference
        coupling cutoff shift base event :=
  Q'.eqv_trans _ _ _
    (couplingParametricKTimeShiftTargetEventCrossDifference_eqv_boundary
      coupling cutoff shift base event)
    (couplingParametricKTimeShiftBoundaryCrossDifference_eqv_cells
      coupling cutoff shift base event)

/-! ## 2. Connected residue and exact normalized boundary scale -/

def timeShiftSpinSummedCylinderBoundaryEpsilon
    (rootCount distance : Nat) : Q' :=
  Q'.ofNat rootCount *
    (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)

theorem couplingParametricKTimeShiftBoundaryCellCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    couplingParametricKTimeShiftBoundaryCellCrossDifference
        coupling cutoff shift base
        (timeShiftMarkedCylinderEvent roots predicate) ≤
      listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedTimeShiftCylinderSourcePairs
          (shift := shift) (base := base)
          (roots := roots) (predicate := predicate)) := by
  have hraw :=
    couplingSpinSummedTimeShiftBoundaryEvent_embeddedComplement_le
      hcoupling cutoff shift base roots predicate
  unfold couplingParametricKTimeShiftBoundaryCellCrossDifference
    couplingParametricKTimeShiftBoundaryTargetEventNumerator
    couplingParametricKTimeShiftEmbeddedTargetEventComplementNumerator
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
    couplingParametricKTimeShiftBoundaryTargetEventComplementNumerator at ⊢
  unfold
    timeShiftBoundaryCylinderEventFamilyList
    timeShiftEmbeddedCylinderComplementFamilyList
    timeShiftBoundaryCylinderComplementFamilyList
    timeShiftEmbeddedCylinderEventFamilyList at hraw
  have hreordered := Q'.le_trans' _ _ _ hraw
    (Q'.add_le_add
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_refl' _))
  exact Q'.sub_le_of_le_add hreordered

theorem couplingParametricKTimeShiftTargetCylinderCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    couplingParametricKTimeShiftTargetEventCrossDifference
        coupling cutoff shift base
        (timeShiftMarkedCylinderEvent roots predicate) ≤
      listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedTimeShiftCylinderSourcePairs
          (shift := shift) (base := base)
          (roots := roots) (predicate := predicate)) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingParametricKTimeShiftTargetEventCrossDifference_eqv_cells
        coupling cutoff shift base
        (timeShiftMarkedCylinderEvent roots predicate)))
    (couplingParametricKTimeShiftBoundaryCellCrossDifference_le_connected
      hcoupling cutoff shift base roots predicate)

theorem couplingParametricKTimeShiftTargetCylinderCrossDifference_le_boundaryEpsilon
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (base + shift) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKTimeShiftTargetEventCrossDifference
        coupling cutoff shift base
        (timeShiftMarkedCylinderEvent roots predicate) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon roots.length distance *
        (couplingParametricKTimeShiftEmbeddedTargetPartition
            coupling cutoff shift base *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (base + shift)) := by
  have hconnected :=
    couplingParametricKTimeShiftTargetCylinderCrossDifference_le_connected
      hcoupling cutoff shift base roots predicate
  have htail :=
    couplingSpinSummedConnectedTimeShiftCylinderPairSum_le_tail
      (predicate := predicate) hcoupling hle cutoff hrootsInside
        rootStart hstartMem
        hrootCore houterExit
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  refine Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv ?_)
  unfold timeShiftSpinSummedCylinderBoundaryEpsilon
  ring_qeqv

/-! ## 3. Cancellation through positive finite partitions -/

theorem couplingParametricKTimeShiftTargetProbability_sub_embedded_le_of_cross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) (event : List (List Nat) → Bool)
    (epsilon : Q')
    (hcross :
      couplingParametricKTimeShiftTargetEventCrossDifference
          coupling cutoff shift base event ≤
        epsilon *
          (couplingParametricKTimeShiftEmbeddedTargetPartition
              coupling cutoff shift base *
            couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (base + shift))) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift) event -
        couplingParametricKTimeShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff shift base event ≤
      epsilon := by
  let targetNumerator :=
    couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff (base + shift) event
  let embeddedNumerator :=
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
      coupling cutoff shift base event
  let targetPartition :=
    couplingParametricKCompatibleSupportGasPartition
      coupling cutoff (base + shift)
  let embeddedPartition :=
    couplingParametricKTimeShiftEmbeddedTargetPartition
      coupling cutoff shift base
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
      hcoupling cutoff (base + shift))
    (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
      hcoupling cutoff shift base)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    embeddedNumerator epsilon embeddedPartition
    (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
      hcoupling cutoff shift base)
  have hprob :
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift) event ≤
        couplingParametricKTimeShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff shift base event + epsilon := by
    unfold couplingParametricKCompatibleSupportEventProbability
      couplingParametricKTimeShiftEmbeddedTargetEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem couplingParametricKTimeShiftTargetCylinderProbability_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (base + shift) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift)
          (timeShiftMarkedCylinderEvent roots predicate) -
        couplingParametricKTimeShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff shift base
          (timeShiftMarkedCylinderEvent roots predicate) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  apply couplingParametricKTimeShiftTargetProbability_sub_embedded_le_of_cross
    hcoupling
  exact
    couplingParametricKTimeShiftTargetCylinderCrossDifference_le_boundaryEpsilon
      hcoupling hle cutoff hrootsInside rootStart hstartMem
        hrootCore houterExit

/-! ## 4. Complement symmetry and the two-sided modulus -/

theorem couplingParametricKTimeShiftEmbeddedTargetEventNumerator_add_complement_eqv_partition
    (coupling : Q') (cutoff shift base : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator
          coupling cutoff shift base event +
        couplingParametricKTimeShiftEmbeddedTargetEventNumerator
          coupling cutoff shift base (fun family => !(event family)) ≈
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base := by
  exact Q'.eqv_symm
    (couplingParametricKTimeShiftEmbeddedPartition_eqv_event_add_complement
      coupling cutoff shift base event)

private theorem shifted_add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem couplingParametricKTimeShiftEmbeddedTargetEventProbability_add_complement_eqv_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKTimeShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff shift base event +
        couplingParametricKTimeShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff shift base
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    couplingParametricKTimeShiftEmbeddedTargetEventNumerator_add_complement_eqv_partition
      coupling cutoff shift base event
  unfold couplingParametricKTimeShiftEmbeddedTargetEventProbability
  refine Q'.eqv_trans _ _ _
    (shifted_add_divPos_eqv_local
      (couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base event)
      (couplingParametricKTimeShiftEmbeddedTargetEventNumerator
        coupling cutoff shift base (fun family => !(event family)))
      (couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base)
      (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
        hcoupling cutoff shift base)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (couplingParametricKTimeShiftEmbeddedTargetPartition
          coupling cutoff shift base)
        (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
          hcoupling cutoff shift base)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (couplingParametricKTimeShiftEmbeddedTargetPartition
      coupling cutoff shift base)
    (couplingParametricKTimeShiftEmbeddedTargetPartition_pos
      hcoupling cutoff shift base)

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

theorem couplingParametricKTimeShiftEmbeddedCylinderProbability_sub_target_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (base + shift) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    couplingParametricKTimeShiftEmbeddedTargetEventProbability
          coupling hcoupling cutoff shift base
          (timeShiftMarkedCylinderEvent roots predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff (base + shift)
          (timeShiftMarkedCylinderEvent roots predicate) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  let event := timeShiftMarkedCylinderEvent roots predicate
  let complementEvent := timeShiftMarkedCylinderEvent roots
    (spinSummedComplementCylinderPredicate predicate)
  have hcomplement :=
    couplingParametricKTimeShiftTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff (predicate :=
        spinSummedComplementCylinderPredicate predicate)
      hrootsInside rootStart hstartMem hrootCore houterExit
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hembeddedSum :
      couplingParametricKTimeShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff shift base event +
          couplingParametricKTimeShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff shift base complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKTimeShiftEmbeddedTargetEventProbability_add_complement_eqv_one
        hcoupling cutoff shift base event
  have htargetSum :
      couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (base + shift) event +
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (base + shift) complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact couplingParametricKCompatibleEventProbability_add_complement_eqv_one
      hcoupling cutoff (base + shift) event
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

theorem couplingParametricKTimeShiftTargetCylinderProbability_abs_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (base + shift) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (base + shift)
            (timeShiftMarkedCylinderEvent roots predicate) -
          couplingParametricKTimeShiftEmbeddedTargetEventProbability
            coupling hcoupling cutoff shift base
            (timeShiftMarkedCylinderEvent roots predicate)) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  apply Q'.abs_le
  · have hreverse :=
      couplingParametricKTimeShiftEmbeddedCylinderProbability_sub_target_le
        (predicate := predicate) hcoupling hle cutoff hrootsInside
          rootStart hstartMem
          hrootCore houterExit
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (shifted_sub_swap_eqv_neg_local
            (couplingParametricKTimeShiftEmbeddedTargetEventProbability
              coupling hcoupling cutoff shift base
              (timeShiftMarkedCylinderEvent roots predicate))
            (couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff (base + shift)
              (timeShiftMarkedCylinderEvent roots predicate)))))
  · exact couplingParametricKTimeShiftTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff hrootsInside rootStart hstartMem
        hrootCore houterExit

#print axioms couplingParametricKTimeShiftCompatiblePartition_eqv_embedded_add_boundary
#print axioms couplingParametricKTimeShiftCompatibleEventNumerator_eqv_embedded_add_boundary
#print axioms couplingParametricKTimeShiftTargetEventCrossDifference_eqv_cells
#print axioms couplingParametricKTimeShiftBoundaryCellCrossDifference_le_connected
#print axioms couplingParametricKTimeShiftTargetCylinderCrossDifference_le_boundaryEpsilon
#print axioms couplingParametricKTimeShiftTargetProbability_sub_embedded_le_of_cross
#print axioms couplingParametricKTimeShiftTargetCylinderProbability_sub_embedded_le
#print axioms couplingParametricKTimeShiftEmbeddedTargetEventProbability_add_complement_eqv_one
#print axioms couplingParametricKTimeShiftEmbeddedCylinderProbability_sub_target_le
#print axioms couplingParametricKTimeShiftTargetCylinderProbability_abs_sub_embedded_le

end YMGap.Continuum.Z4TimeShiftedTargetCylinderStability
