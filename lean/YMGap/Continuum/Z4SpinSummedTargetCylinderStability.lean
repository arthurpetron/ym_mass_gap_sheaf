/-
# Normalized same-volume stability for arbitrary-cutoff cylinder events

The connected cylinder tail is divided by the exact full-target and embedded-
target partition factors.  This yields a cutoff- and volume-uniform modulus
for conditioning the target gas on the embedded subensemble.  It is still a
same-volume theorem: identifying the embedded conditional law with the genuine
smaller-box law is deliberately left to the separate locality layer.
-/

import YMGap.Continuum.Z4CanonicalOccurrenceStability
import YMGap.Continuum.Z4SpinSummedCylinderConnectedTail

namespace YMGap.Continuum.Z4SpinSummedTargetCylinderStability

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalOccurrenceStability
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCylinderConnectedTail
open YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

def spinSummedCylinderBoundaryEpsilon
    (rootCount distance : Nat) : Q' :=
  Q'.ofNat rootCount *
    ((anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) +
      (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2))

theorem spinSummedCylinderBoundaryEpsilon_nonnegative
    (rootCount distance : Nat) :
    (0 : Q') ≤ spinSummedCylinderBoundaryEpsilon rootCount distance := by
  unfold spinSummedCylinderBoundaryEpsilon
  exact Q'.mul_nonneg _ _
    (by rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _)
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (distance + 2))
        (by decide))
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative (distance + 2))
        (by decide)))

theorem spinSummedCylinderBoundaryTail_eqv_normalized
    (cutoff rootCount small n distance : Nat) :
    Q'.ofNat rootCount *
        spinSummedCylinderSingleRootTwoSidedTail
          cutoff small n distance ≈
      spinSummedCylinderBoundaryEpsilon rootCount distance *
        (parametricKEmbeddedTargetPartition cutoff small n *
          parametricKCompatibleSupportGasPartition cutoff n) := by
  unfold spinSummedCylinderSingleRootTwoSidedTail
    spinSummedCylinderSingleRootBoundaryTail
    spinSummedCylinderBoundaryEpsilon
  ring_qeqv

/-- Division-free same-volume target/embedded cylinder estimate. -/
theorem parametricKTargetCylinderCrossDifference_le_boundaryEpsilon
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    parametricKTargetEventCrossDifference cutoff small n
        (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance *
        (parametricKEmbeddedTargetPartition cutoff small n *
          parametricKCompatibleSupportGasPartition cutoff n) := by
  have hconnected := parametricKTargetCylinderCrossDifference_le_connected
    cutoff hsmall roots predicate
  unfold ParametricKTargetCylinderConnectedBound at hconnected
  have htail := spinSummedConnectedCylinderResidue_le_boundaryTail
    cutoff hsmall roots predicate hrootsInside hgeometry hbox
  have hbound := Q'.le_trans' _ _ _ hconnected htail
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv
      (spinSummedCylinderBoundaryTail_eqv_normalized
        cutoff roots.length small n distance))

/-! ## Positive-denominator normalization -/

theorem parametricKTargetProbability_sub_embedded_le_of_cross
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) (epsilon : Q')
    (hcross :
      parametricKTargetEventCrossDifference cutoff small n event ≤
        epsilon *
          (parametricKEmbeddedTargetPartition cutoff small n *
            parametricKCompatibleSupportGasPartition cutoff n)) :
    parametricKCompatibleSupportEventProbability cutoff n event -
        parametricKEmbeddedTargetEventProbability cutoff hsmall event ≤
      epsilon := by
  let targetNumerator :=
    parametricKCompatibleSupportEventNumerator cutoff n event
  let embeddedNumerator :=
    parametricKEmbeddedTargetEventNumerator cutoff small n event
  let targetPartition :=
    parametricKCompatibleSupportGasPartition cutoff n
  let embeddedPartition :=
    parametricKEmbeddedTargetPartition cutoff small n
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
    (parametricKCompatibleSupportGasPartition_pos cutoff n)
    (parametricKEmbeddedTargetPartition_pos cutoff hsmall)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreorder))
  have hcollapse := divPos_add_scaled_eqv
    embeddedNumerator epsilon embeddedPartition
    (parametricKEmbeddedTargetPartition_pos cutoff hsmall)
  have hprob :
      parametricKCompatibleSupportEventProbability cutoff n event ≤
        parametricKEmbeddedTargetEventProbability cutoff hsmall event +
          epsilon := by
    unfold parametricKCompatibleSupportEventProbability
      parametricKEmbeddedTargetEventProbability
    exact Q'.le_trans' _ _ _ hratio (Q'.le_of_eqv hcollapse)
  exact Q'.sub_le_of_le_add hprob

theorem parametricKTargetCylinderProbability_sub_embedded_le
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    parametricKCompatibleSupportEventProbability cutoff n
          (markedCylinderEvent roots predicate) -
        parametricKEmbeddedTargetEventProbability cutoff hsmall
          (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  apply parametricKTargetProbability_sub_embedded_le_of_cross
  exact parametricKTargetCylinderCrossDifference_le_boundaryEpsilon
    cutoff hsmall roots predicate hrootsInside hgeometry hbox

/-! ## Complement symmetry and the full same-volume modulus -/

def spinSummedComplementCylinderPredicate
    (predicate : List Bool → Bool) : List Bool → Bool :=
  fun bits => !(predicate bits)

theorem parametricKCompatibleEventNumerator_add_complement_eqv_partition
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventNumerator cutoff n event +
        parametricKCompatibleSupportEventNumerator cutoff n
          (fun family => !(event family)) ≈
      parametricKCompatibleSupportGasPartition cutoff n := by
  unfold parametricKCompatibleSupportEventNumerator
    parametricKCompatibleSupportGasPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (parametricKSupportFamilyActivity cutoff n) event
      (canonicalCompatibleAmbientFamilies n))

theorem parametricKEmbeddedTargetEventNumerator_add_complement_eqv_partition
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKEmbeddedTargetEventNumerator cutoff small n event +
        parametricKEmbeddedTargetEventNumerator cutoff small n
          (fun family => !(event family)) ≈
      parametricKEmbeddedTargetPartition cutoff small n := by
  unfold parametricKEmbeddedTargetEventNumerator
    parametricKEmbeddedTargetPartition
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (parametricKSupportFamilyActivity cutoff n) event
      (embeddedTargetFamilies small n))

private theorem add_divPos_eqv_local
    (p p' q : Q') (hq : (0 : Q') < q) :
    Q'.divPos p q hq + Q'.divPos p' q hq ≈
      Q'.divPos (p + p') q hq :=
  Q'.eqv_symm (Q'.add_mul_eqv p p' (Q'.recipPos q hq))

theorem parametricKCompatibleEventProbability_add_complement_eqv_one
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventProbability cutoff n event +
        parametricKCompatibleSupportEventProbability cutoff n
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    parametricKCompatibleEventNumerator_add_complement_eqv_partition
      cutoff n event
  unfold parametricKCompatibleSupportEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (parametricKCompatibleSupportEventNumerator cutoff n event)
      (parametricKCompatibleSupportEventNumerator cutoff n
        (fun family => !(event family)))
      (parametricKCompatibleSupportGasPartition cutoff n)
      (parametricKCompatibleSupportGasPartition_pos cutoff n)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos (parametricKCompatibleSupportGasPartition cutoff n)
        (parametricKCompatibleSupportGasPartition_pos cutoff n)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (parametricKCompatibleSupportGasPartition cutoff n)
    (parametricKCompatibleSupportGasPartition_pos cutoff n)

theorem parametricKEmbeddedTargetEventProbability_add_complement_eqv_one
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) :
    parametricKEmbeddedTargetEventProbability cutoff hsmall event +
        parametricKEmbeddedTargetEventProbability cutoff hsmall
          (fun family => !(event family)) ≈
      (1 : Q') := by
  have hsplit :=
    parametricKEmbeddedTargetEventNumerator_add_complement_eqv_partition
      cutoff small n event
  unfold parametricKEmbeddedTargetEventProbability
  refine Q'.eqv_trans _ _ _
    (add_divPos_eqv_local
      (parametricKEmbeddedTargetEventNumerator cutoff small n event)
      (parametricKEmbeddedTargetEventNumerator cutoff small n
        (fun family => !(event family)))
      (parametricKEmbeddedTargetPartition cutoff small n)
      (parametricKEmbeddedTargetPartition_pos cutoff hsmall)) ?_
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (Q'.recipPos (parametricKEmbeddedTargetPartition cutoff small n)
        (parametricKEmbeddedTargetPartition_pos cutoff hsmall)) hsplit) ?_
  exact Q'.mul_recipPos_eqv
    (parametricKEmbeddedTargetPartition cutoff small n)
    (parametricKEmbeddedTargetPartition_pos cutoff hsmall)

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

theorem parametricKEmbeddedCylinderProbability_sub_target_le
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    parametricKEmbeddedTargetEventProbability cutoff hsmall
          (markedCylinderEvent roots predicate) -
        parametricKCompatibleSupportEventProbability cutoff n
          (markedCylinderEvent roots predicate) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  let event := markedCylinderEvent roots predicate
  let complementEvent := markedCylinderEvent roots
    (spinSummedComplementCylinderPredicate predicate)
  have hcomplement := parametricKTargetCylinderProbability_sub_embedded_le
    cutoff hsmall roots (spinSummedComplementCylinderPredicate predicate)
      hrootsInside hgeometry hbox
  have hpointwise : complementEvent =
      (fun family => !(event family)) := by
    funext family
    rfl
  have hembeddedSum :
      parametricKEmbeddedTargetEventProbability cutoff hsmall event +
          parametricKEmbeddedTargetEventProbability cutoff hsmall
            complementEvent ≈ (1 : Q') := by
    rw [hpointwise]
    exact parametricKEmbeddedTargetEventProbability_add_complement_eqv_one
      cutoff hsmall event
  have htargetSum :
      parametricKCompatibleSupportEventProbability cutoff n event +
          parametricKCompatibleSupportEventProbability cutoff n
            complementEvent ≈ (1 : Q') := by
    rw [hpointwise]
    exact parametricKCompatibleEventProbability_add_complement_eqv_one
      cutoff n event
  have hreorder :
      parametricKEmbeddedTargetEventProbability cutoff hsmall event -
          parametricKCompatibleSupportEventProbability cutoff n event ≈
        parametricKCompatibleSupportEventProbability cutoff n complementEvent -
          parametricKEmbeddedTargetEventProbability cutoff hsmall
            complementEvent :=
    eventReverseSub_eqv_complementSub hembeddedSum htargetSum
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder) hcomplement

private theorem sub_swap_eqv_neg_local (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-- Full same-volume modulus between the target gas and its literal embedded
target subensemble, uniform in cutoff and target volume. -/
theorem parametricKTargetCylinderProbability_abs_sub_embedded_le
    (cutoff : Nat) {small n inner distance : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability cutoff n
            (markedCylinderEvent roots predicate) -
          parametricKEmbeddedTargetEventProbability cutoff hsmall
            (markedCylinderEvent roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length distance := by
  apply Q'.abs_le
  · have hreverse := parametricKEmbeddedCylinderProbability_sub_target_le
      cutoff hsmall roots predicate hrootsInside hgeometry hbox
    have hneg := Q'.neg_le_neg hreverse
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (sub_swap_eqv_neg_local
            (parametricKEmbeddedTargetEventProbability cutoff hsmall
              (markedCylinderEvent roots predicate))
            (parametricKCompatibleSupportEventProbability cutoff n
              (markedCylinderEvent roots predicate)))))
  · exact parametricKTargetCylinderProbability_sub_embedded_le
      cutoff hsmall roots predicate hrootsInside hgeometry hbox

end YMGap.Continuum.Z4SpinSummedTargetCylinderStability

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.spinSummedCylinderBoundaryTail_eqv_normalized
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKTargetCylinderCrossDifference_le_boundaryEpsilon
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKTargetProbability_sub_embedded_le_of_cross
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKTargetCylinderProbability_sub_embedded_le
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKCompatibleEventProbability_add_complement_eqv_one
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKEmbeddedTargetEventProbability_add_complement_eqv_one
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKEmbeddedCylinderProbability_sub_target_le
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderStability.parametricKTargetCylinderProbability_abs_sub_embedded_le
