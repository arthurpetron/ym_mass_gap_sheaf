/-
# Uniform same-volume cylinder stability below the anchor

The coupling-parametric connected residue contains the exact full-target and
embedded-target partition factors.  Cancelling them through positive
denominators gives the same geometric cylinder modulus at every cutoff,
target volume, and rational coupling between zero and the anchor.
-/

import YMGap.Continuum.Z4CouplingParametricTargetCylinderRatio
import YMGap.Continuum.Z4SpinSummedTargetCylinderStability

namespace YMGap.Continuum.Z4CouplingParametricTargetCylinderStability

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTargetCylinderRatio
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

theorem couplingSpinSummedCylinderBoundaryTail_eqv_normalized
    (coupling : Q') (cutoff rootCount small n distance : Nat) :
    Q'.ofNat rootCount *
        couplingSpinSummedCylinderSingleRootTwoSidedTail
          coupling cutoff small n distance ≈
      spinSummedCylinderBoundaryEpsilon rootCount distance *
        (couplingParametricKEmbeddedTargetPartition
            coupling cutoff small n *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n) := by
  unfold couplingSpinSummedCylinderSingleRootTwoSidedTail
    couplingSpinSummedCylinderSingleRootBoundaryTail
    spinSummedCylinderBoundaryEpsilon
  ring_qeqv

/-! ## 1. Division-free normalized bound -/

theorem couplingParametricKTargetCylinderCrossDifference_le_boundaryEpsilon
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    couplingParametricKTargetEventCrossDifference coupling cutoff small n
        (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance *
        (couplingParametricKEmbeddedTargetPartition
            coupling cutoff small n *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n) := by
  have hconnected :=
    couplingParametricKTargetCylinderCrossDifference_le_connected
      hcoupling cutoff hsmall roots predicate
  unfold CouplingParametricKTargetCylinderConnectedBound at hconnected
  have htail :=
    couplingSpinSummedConnectedCylinderPairSum_le_boundaryTail
      hcoupling hle cutoff hsmall roots predicate hrootsInside hgeometry hbox
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv
      (couplingSpinSummedCylinderBoundaryTail_eqv_normalized
        coupling cutoff roots.length small n distance))

theorem couplingParametricKTargetProbability_sub_embedded_le_of_cross
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) (epsilon : Q')
    (hcross :
      couplingParametricKTargetEventCrossDifference
          coupling cutoff small n event ≤
        epsilon *
          (couplingParametricKEmbeddedTargetPartition
              coupling cutoff small n *
            couplingParametricKCompatibleSupportGasPartition
              coupling cutoff n)) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n event -
        couplingParametricKEmbeddedTargetEventProbability
          coupling hcoupling cutoff hsmall event ≤
      epsilon := by
  let targetNumerator :=
    couplingParametricKCompatibleSupportEventNumerator
      coupling cutoff n event
  let embeddedNumerator :=
    couplingParametricKEmbeddedTargetEventNumerator
      coupling cutoff small n event
  let targetPartition :=
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n
  let embeddedPartition :=
    couplingParametricKEmbeddedTargetPartition coupling cutoff small n
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
      hcoupling cutoff n)
    (couplingParametricKEmbeddedTargetPartition_pos
      hcoupling cutoff hsmall)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    embeddedNumerator epsilon embeddedPartition
    (couplingParametricKEmbeddedTargetPartition_pos
      hcoupling cutoff hsmall)
  have hprob :
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n event ≤
        couplingParametricKEmbeddedTargetEventProbability
            coupling hcoupling cutoff hsmall event + epsilon := by
    unfold couplingParametricKCompatibleSupportEventProbability
      couplingParametricKEmbeddedTargetEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem couplingParametricKTargetCylinderProbability_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n
          (markedCylinderEvent roots predicate) -
        couplingParametricKEmbeddedTargetEventProbability
          coupling hcoupling cutoff hsmall
          (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  apply couplingParametricKTargetProbability_sub_embedded_le_of_cross
    hcoupling
  exact couplingParametricKTargetCylinderCrossDifference_le_boundaryEpsilon
    hcoupling hle cutoff hsmall roots predicate
      hrootsInside hgeometry hbox

/-! ## 2. Complement symmetry -/

theorem couplingParametricKCompatibleEventNumerator_add_complement_eqv_partition
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff n event +
        couplingParametricKCompatibleSupportEventNumerator
          coupling cutoff n (fun family => !(event family)) ≈
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingParametricKCompatibleSupportGasPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (couplingParametricKSupportFamilyActivity coupling cutoff n) event
      (canonicalCompatibleAmbientFamilies n))

theorem couplingParametricKEmbeddedTargetEventNumerator_add_complement_eqv_partition
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKEmbeddedTargetEventNumerator
          coupling cutoff small n event +
        couplingParametricKEmbeddedTargetEventNumerator
          coupling cutoff small n (fun family => !(event family)) ≈
      couplingParametricKEmbeddedTargetPartition
        coupling cutoff small n := by
  unfold couplingParametricKEmbeddedTargetEventNumerator
    couplingParametricKEmbeddedTargetPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (couplingParametricKSupportFamilyActivity coupling cutoff n) event
      (embeddedTargetFamilies small n))

private theorem add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem couplingParametricKCompatibleEventProbability_add_complement_eqv_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n event +
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    couplingParametricKCompatibleEventNumerator_add_complement_eqv_partition
      coupling cutoff n event
  unfold couplingParametricKCompatibleSupportEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event)
      (couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n (fun family => !(event family)))
      (couplingParametricKCompatibleSupportGasPartition coupling cutoff n)
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff n)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n)
        (couplingParametricKCompatibleSupportGasPartition_pos
          hcoupling cutoff n)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (couplingParametricKCompatibleSupportGasPartition coupling cutoff n)
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff n)

theorem couplingParametricKEmbeddedTargetEventProbability_add_complement_eqv_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) :
    couplingParametricKEmbeddedTargetEventProbability
          coupling hcoupling cutoff hsmall event +
        couplingParametricKEmbeddedTargetEventProbability
          coupling hcoupling cutoff hsmall
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    couplingParametricKEmbeddedTargetEventNumerator_add_complement_eqv_partition
      coupling cutoff small n event
  unfold couplingParametricKEmbeddedTargetEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n event)
      (couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n (fun family => !(event family)))
      (couplingParametricKEmbeddedTargetPartition
        coupling cutoff small n)
      (couplingParametricKEmbeddedTargetPartition_pos
        hcoupling cutoff hsmall)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos
        (couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n)
        (couplingParametricKEmbeddedTargetPartition_pos
          hcoupling cutoff hsmall)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (couplingParametricKEmbeddedTargetPartition coupling cutoff small n)
    (couplingParametricKEmbeddedTargetPartition_pos
      hcoupling cutoff hsmall)

private theorem left_eqv_one_sub_right {a complement : Q'}
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

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem eventReverseSub_eqv_complementSub
    {a aComplement b bComplement : Q'}
    (ha : a + aComplement ≈ (1 : Q'))
    (hb : b + bComplement ≈ (1 : Q')) :
    a - b ≈ bComplement - aComplement := by
  refine Q'.eqv_trans _
    (((1 : Q') - aComplement) - ((1 : Q') - bComplement)) _
    (sub_eqv_both_local
      (left_eqv_one_sub_right ha)
      (left_eqv_one_sub_right hb)) ?_
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

theorem couplingParametricKEmbeddedCylinderProbability_sub_target_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    couplingParametricKEmbeddedTargetEventProbability
          coupling hcoupling cutoff hsmall
          (markedCylinderEvent roots predicate) -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff n
          (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  let event := markedCylinderEvent roots predicate
  let complementEvent := markedCylinderEvent roots
    (spinSummedComplementCylinderPredicate predicate)
  have hcomplement :=
    couplingParametricKTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff hsmall roots
      (spinSummedComplementCylinderPredicate predicate)
      hrootsInside hgeometry hbox
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hembeddedSum :
      couplingParametricKEmbeddedTargetEventProbability
            coupling hcoupling cutoff hsmall event +
          couplingParametricKEmbeddedTargetEventProbability
            coupling hcoupling cutoff hsmall complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKEmbeddedTargetEventProbability_add_complement_eqv_one
        hcoupling cutoff hsmall event
  have htargetSum :
      couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff n event +
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff n complementEvent ≈
        (1 : Q') := by
    rw [hpointwise]
    exact
      couplingParametricKCompatibleEventProbability_add_complement_eqv_one
        hcoupling cutoff n event
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (eventReverseSub_eqv_complementSub hembeddedSum htargetSum))
    hcomplement

private theorem sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-! The full same-volume modulus is uniform in both cutoff and volume. -/
theorem couplingParametricKTargetCylinderProbability_abs_sub_embedded_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff n
            (markedCylinderEvent roots predicate) -
          couplingParametricKEmbeddedTargetEventProbability
            coupling hcoupling cutoff hsmall
            (markedCylinderEvent roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  apply Q'.abs_le
  · have hreverse :=
      couplingParametricKEmbeddedCylinderProbability_sub_target_le
        hcoupling hle cutoff hsmall roots predicate
          hrootsInside hgeometry hbox
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (couplingParametricKEmbeddedTargetEventProbability
              coupling hcoupling cutoff hsmall
              (markedCylinderEvent roots predicate))
            (couplingParametricKCompatibleSupportEventProbability
              coupling hcoupling cutoff n
              (markedCylinderEvent roots predicate)))))
  · exact couplingParametricKTargetCylinderProbability_sub_embedded_le
      hcoupling hle cutoff hsmall roots predicate
        hrootsInside hgeometry hbox

#print axioms couplingSpinSummedCylinderBoundaryTail_eqv_normalized
#print axioms couplingParametricKTargetCylinderCrossDifference_le_boundaryEpsilon
#print axioms couplingParametricKTargetProbability_sub_embedded_le_of_cross
#print axioms couplingParametricKTargetCylinderProbability_sub_embedded_le
#print axioms couplingParametricKCompatibleEventProbability_add_complement_eqv_one
#print axioms couplingParametricKEmbeddedTargetEventProbability_add_complement_eqv_one
#print axioms couplingParametricKEmbeddedCylinderProbability_sub_target_le
#print axioms couplingParametricKTargetCylinderProbability_abs_sub_embedded_le

end YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
