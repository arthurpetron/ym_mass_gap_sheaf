/-
# Spin-summed weight envelope for connected two-replica carriers

All carrier geometry is inherited from the canonical cutoff-one construction.
This module replaces only its weight layer: support-family products are split
exactly into path and background factors, and the path pair is bounded by one
`anchorDecoratedFaceEnvelope` factor per face of its colored union support.
-/

import YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
import YMGap.Continuum.Z4SpinSummedColoredSupportWeight
import YMGap.Continuum.Z4SpinSummedCompatibleGas

namespace YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteFamilyWeightPartition
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Generic support-family products -/

theorem parametricKSupportFamilyActivity_filter_partition
    (cutoff n : Nat) (family : List (List Nat))
    (test : List Nat → Bool) :
    parametricKSupportFamilyActivity cutoff n family ≈
      parametricKSupportFamilyActivity cutoff n (family.filter test) *
        parametricKSupportFamilyActivity cutoff n
          (family.filter (fun support => !(test support))) := by
  induction family with
  | nil => exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | cons head rest ih =>
      cases htest : test head with
      | true =>
          simp only [parametricKSupportFamilyActivity, List.filter_cons,
            htest, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (parametricKSupportActivity cutoff n head) _ _ ih)
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (parametricKSupportActivity cutoff n head)
                (parametricKSupportFamilyActivity cutoff n
                  (rest.filter test))
                (parametricKSupportFamilyActivity cutoff n
                  (rest.filter (fun support => !(test support))))))
      | false =>
          simp only [parametricKSupportFamilyActivity, List.filter_cons,
            htest, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (parametricKSupportActivity cutoff n head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (parametricKSupportActivity cutoff n head)
                (parametricKSupportFamilyActivity cutoff n
                  (rest.filter test))
                (parametricKSupportFamilyActivity cutoff n
                  (rest.filter (fun support => !(test support)))))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv
                (parametricKSupportActivity cutoff n head)
                (parametricKSupportFamilyActivity cutoff n
                  (rest.filter test)))) ?_
          exact Q'.mul_assoc_eqv
            (parametricKSupportFamilyActivity cutoff n (rest.filter test))
            (parametricKSupportActivity cutoff n head)
            (parametricKSupportFamilyActivity cutoff n
              (rest.filter (fun support => !(test support))))

theorem parametricKSupportFamilyActivity_le_totalFacePow
    (cutoff n : Nat) : ∀ family : List (List Nat),
    parametricKSupportFamilyActivity cutoff n family ≤
      anchorDecoratedFaceEnvelope ^ familyFaceCount family
  | [] => Q'.le_refl' 1
  | support :: rest => by
      change parametricKSupportActivity cutoff n support *
          parametricKSupportFamilyActivity cutoff n rest ≤
        anchorDecoratedFaceEnvelope ^
          (support.length + familyFaceCount rest)
      have hsupport :=
        parametricKSupportActivity_le_envelopePow cutoff n support
      have hrest :=
        parametricKSupportFamilyActivity_le_totalFacePow cutoff n rest
      have hrest0 :=
        parametricKSupportFamilyActivity_nonnegative cutoff n rest
      have hpow0 : (0 : Q') ≤
          anchorDecoratedFaceEnvelope ^ support.length :=
        Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative support.length
      have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hsupport hrest0
      have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hrest hpow0
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.pow_add_eqv anchorDecoratedFaceEnvelope
                support.length (familyFaceCount rest)))))

/-! ## 2. Forward carrier weights -/

def spinSummedSourcePairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : Q' :=
  parametricKSupportFamilyActivity cutoff n pair.1.val *
    parametricKSupportFamilyActivity cutoff n pair.2.val

def spinSummedConnectedPathPairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) : Q' :=
  parametricKSupportFamilyActivity cutoff n
      (connectedPathLeftFamily hsmall entry) *
    parametricKSupportFamilyActivity cutoff n
      (connectedPathRightFamily hsmall entry)

def spinSummedConnectedBackgroundPairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) : Q' :=
  parametricKSupportFamilyActivity cutoff n
      (connectedBackgroundLeftFamily hsmall entry) *
    parametricKSupportFamilyActivity cutoff n
      (connectedBackgroundRightFamily hsmall entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem spinSummedConnectedSourcePairWeight_factor
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    spinSummedSourcePairWeight cutoff entry.val ≈
      spinSummedConnectedPathPairWeight cutoff hsmall entry *
        spinSummedConnectedBackgroundPairWeight cutoff hsmall entry := by
  have hleft := parametricKSupportFamilyActivity_filter_partition
    cutoff n entry.val.1.val (connectedPathTest hsmall entry)
  have hright := parametricKSupportFamilyActivity_filter_partition
    cutoff n entry.val.2.val (connectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold spinSummedConnectedPathPairWeight
    spinSummedConnectedBackgroundPairWeight connectedPathLeftFamily
    connectedBackgroundLeftFamily connectedPathRightFamily
    connectedBackgroundRightFamily
  ring_qeqv

theorem spinSummedConnectedPathPairWeight_le_totalFacePow
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    spinSummedConnectedPathPairWeight cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (familyFaceCount (connectedPathLeftFamily hsmall entry) +
          familyFaceCount (connectedPathRightFamily hsmall entry)) := by
  have hleft := parametricKSupportFamilyActivity_le_totalFacePow cutoff n
    (connectedPathLeftFamily hsmall entry)
  have hright := parametricKSupportFamilyActivity_le_totalFacePow cutoff n
    (connectedPathRightFamily hsmall entry)
  have hright0 := parametricKSupportFamilyActivity_nonnegative cutoff n
    (connectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (connectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold spinSummedConnectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorDecoratedFaceEnvelope
          (familyFaceCount (connectedPathLeftFamily hsmall entry))
          (familyFaceCount (connectedPathRightFamily hsmall entry))))))

theorem spinSummedConnectedPathPairWeight_le_supportPow
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    spinSummedConnectedPathPairWeight cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (connectedCarrierSupport hsmall entry).length := by
  exact Q'.le_trans' _ _ _
    (spinSummedConnectedPathPairWeight_le_totalFacePow
      cutoff hsmall entry)
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (connectedCarrierSupport_length_le_pathFaceCount hsmall entry))

theorem spinSummedConnectedBackgroundPairWeight_nonnegative
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    (0 : Q') ≤
      spinSummedConnectedBackgroundPairWeight cutoff hsmall entry := by
  unfold spinSummedConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (parametricKSupportFamilyActivity_nonnegative cutoff n _)
    (parametricKSupportFamilyActivity_nonnegative cutoff n _)

theorem spinSummedConnectedSourcePairWeight_le_support_background
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    spinSummedSourcePairWeight cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (connectedCarrierSupport hsmall entry).length *
        spinSummedConnectedBackgroundPairWeight cutoff hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (spinSummedConnectedSourcePairWeight_factor cutoff hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedConnectedPathPairWeight_le_supportPow
        cutoff hsmall entry)
      (spinSummedConnectedBackgroundPairWeight_nonnegative
        cutoff hsmall entry))

/-! ## 3. Mirrored carrier weights -/

def spinSummedReverseSourcePairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) : Q' :=
  parametricKSupportFamilyActivity cutoff n pair.1.val *
    parametricKSupportFamilyActivity cutoff n pair.2.val

def spinSummedReverseConnectedPathPairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  parametricKSupportFamilyActivity cutoff n
      (reverseConnectedPathLeftFamily hsmall entry) *
    parametricKSupportFamilyActivity cutoff n
      (reverseConnectedPathRightFamily hsmall entry)

/-- The mirrored backgrounds remain stored in boundary/embedded order. -/
def spinSummedReverseConnectedBackgroundPairWeight
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  parametricKSupportFamilyActivity cutoff n
      (reverseConnectedBackgroundRightFamily hsmall entry) *
    parametricKSupportFamilyActivity cutoff n
      (reverseConnectedBackgroundLeftFamily hsmall entry)

theorem spinSummedReverseConnectedSourcePairWeight_factor
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    spinSummedReverseSourcePairWeight cutoff entry.val ≈
      spinSummedReverseConnectedPathPairWeight cutoff hsmall entry *
        spinSummedReverseConnectedBackgroundPairWeight
          cutoff hsmall entry := by
  have hleft := parametricKSupportFamilyActivity_filter_partition
    cutoff n entry.val.1.val (reverseConnectedPathTest hsmall entry)
  have hright := parametricKSupportFamilyActivity_filter_partition
    cutoff n entry.val.2.val (reverseConnectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold spinSummedReverseConnectedPathPairWeight
    spinSummedReverseConnectedBackgroundPairWeight
    reverseConnectedPathLeftFamily reverseConnectedBackgroundLeftFamily
    reverseConnectedPathRightFamily reverseConnectedBackgroundRightFamily
  ring_qeqv

theorem spinSummedReverseConnectedPathPairWeight_le_totalFacePow
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    spinSummedReverseConnectedPathPairWeight cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) +
          familyFaceCount
            (reverseConnectedPathRightFamily hsmall entry)) := by
  have hleft := parametricKSupportFamilyActivity_le_totalFacePow cutoff n
    (reverseConnectedPathLeftFamily hsmall entry)
  have hright := parametricKSupportFamilyActivity_le_totalFacePow cutoff n
    (reverseConnectedPathRightFamily hsmall entry)
  have hright0 := parametricKSupportFamilyActivity_nonnegative cutoff n
    (reverseConnectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold spinSummedReverseConnectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorDecoratedFaceEnvelope
          (familyFaceCount (reverseConnectedPathLeftFamily hsmall entry))
          (familyFaceCount
            (reverseConnectedPathRightFamily hsmall entry))))))

theorem spinSummedReverseConnectedPathPairWeight_le_supportPow
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    spinSummedReverseConnectedPathPairWeight cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (reverseConnectedCarrierSupport hsmall entry).length := by
  exact Q'.le_trans' _ _ _
    (spinSummedReverseConnectedPathPairWeight_le_totalFacePow
      cutoff hsmall entry)
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (reverseConnectedCarrierSupport_length_le_pathFaceCount
        hsmall entry))

theorem spinSummedReverseConnectedBackgroundPairWeight_nonnegative
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    (0 : Q') ≤ spinSummedReverseConnectedBackgroundPairWeight
      cutoff hsmall entry := by
  unfold spinSummedReverseConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (parametricKSupportFamilyActivity_nonnegative cutoff n _)
    (parametricKSupportFamilyActivity_nonnegative cutoff n _)

theorem spinSummedReverseConnectedSourcePairWeight_le_support_background
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    spinSummedReverseSourcePairWeight cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (reverseConnectedCarrierSupport hsmall entry).length *
        spinSummedReverseConnectedBackgroundPairWeight
          cutoff hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (spinSummedReverseConnectedSourcePairWeight_factor
        cutoff hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedReverseConnectedPathPairWeight_le_supportPow
        cutoff hsmall entry)
      (spinSummedReverseConnectedBackgroundPairWeight_nonnegative
        cutoff hsmall entry))

end YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight.parametricKSupportFamilyActivity_filter_partition
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight.parametricKSupportFamilyActivity_le_totalFacePow
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight.spinSummedConnectedSourcePairWeight_le_support_background
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight.spinSummedReverseConnectedSourcePairWeight_le_support_background
