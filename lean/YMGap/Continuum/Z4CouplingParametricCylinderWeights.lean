/-
# Sub-anchor coupling weights for connected cylinder switching

The cylinder switch and connected-carrier encodings are geometric.  This
module supplies their arbitrary-coupling weight layer.  For every
`0 <= w <= anchorCoupling`, each connected-support activity is dominated by
the anchor activity, so every path family inherits the same exact decorated
face envelope.  Background families retain their exact coupling-`w`
activities; this is what ultimately leaves the coupling-`w` partition
factors available for normalized boundary estimates.
-/

import YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
import YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight
import YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation
import YMGap.Continuum.Z4SpinSummedMarkedRootSwitch

namespace YMGap.Continuum.Z4CouplingParametricCylinderWeights

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteFamilyWeightPartition
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Family products and the sub-anchor face envelope -/

theorem couplingParametricKSupportFamilyActivity_filter_partition
    (coupling : Q') (cutoff n : Nat) (family : List (List Nat))
    (test : List Nat → Bool) :
    couplingParametricKSupportFamilyActivity coupling cutoff n family ≈
      couplingParametricKSupportFamilyActivity coupling cutoff n
          (family.filter test) *
        couplingParametricKSupportFamilyActivity coupling cutoff n
          (family.filter (fun support => !(test support))) := by
  induction family with
  | nil => exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | cons head rest ih =>
      cases htest : test head with
      | true =>
          simp only [couplingParametricKSupportFamilyActivity,
            List.filter_cons, htest, ↓reduceIte, Bool.not_true,
            Bool.false_eq_true]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (couplingParametricKSupportActivity
                coupling cutoff n head) _ _ ih)
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (couplingParametricKSupportActivity
                  coupling cutoff n head)
                (couplingParametricKSupportFamilyActivity
                  coupling cutoff n (rest.filter test))
                (couplingParametricKSupportFamilyActivity
                  coupling cutoff n
                    (rest.filter (fun support => !(test support))))))
      | false =>
          simp only [couplingParametricKSupportFamilyActivity,
            List.filter_cons, htest, Bool.false_eq_true, ↓reduceIte,
            Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (couplingParametricKSupportActivity
                coupling cutoff n head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv
                (couplingParametricKSupportActivity
                  coupling cutoff n head)
                (couplingParametricKSupportFamilyActivity
                  coupling cutoff n (rest.filter test))
                (couplingParametricKSupportFamilyActivity
                  coupling cutoff n
                    (rest.filter (fun support => !(test support)))))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv
                (couplingParametricKSupportActivity
                  coupling cutoff n head)
                (couplingParametricKSupportFamilyActivity
                  coupling cutoff n (rest.filter test)))) ?_
          exact Q'.mul_assoc_eqv
            (couplingParametricKSupportFamilyActivity
              coupling cutoff n (rest.filter test))
            (couplingParametricKSupportActivity coupling cutoff n head)
            (couplingParametricKSupportFamilyActivity
              coupling cutoff n
                (rest.filter (fun support => !(test support))))

theorem couplingParametricKSupportFamilyActivity_le_totalFacePow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff n : Nat) :
    ∀ family : List (List Nat),
      couplingParametricKSupportFamilyActivity
          coupling cutoff n family ≤
        anchorDecoratedFaceEnvelope ^ familyFaceCount family
  | [] => Q'.le_refl' 1
  | support :: rest => by
      change couplingParametricKSupportActivity coupling cutoff n support *
          couplingParametricKSupportFamilyActivity
            coupling cutoff n rest ≤
        anchorDecoratedFaceEnvelope ^
          (support.length + familyFaceCount rest)
      have hsupport :
          couplingParametricKSupportActivity
              coupling cutoff n support ≤
            anchorDecoratedFaceEnvelope ^ support.length :=
        Q'.le_trans' _ _ _
          (couplingParametricKSupportActivity_le_anchor
            hcoupling hle cutoff n support)
          (parametricKSupportActivity_le_envelopePow cutoff n support)
      have hrest :=
        couplingParametricKSupportFamilyActivity_le_totalFacePow
          hcoupling hle cutoff n rest
      have hrest0 :=
        couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n rest
      have hpow0 : (0 : Q') ≤
          anchorDecoratedFaceEnvelope ^ support.length :=
        Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative support.length
      have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _
        hsupport hrest0
      have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _
        hrest hpow0
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.pow_add_eqv anchorDecoratedFaceEnvelope
                support.length (familyFaceCount rest)))))

/-! ## 2. Forward and reverse connected-carrier weights -/

def couplingSpinSummedSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : Q' :=
  couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.1.val *
    couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.2.val

def couplingSpinSummedConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (connectedPathLeftFamily hsmall entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (connectedPathRightFamily hsmall entry)

def couplingSpinSummedConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (connectedBackgroundLeftFamily hsmall entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (connectedBackgroundRightFamily hsmall entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingSpinSummedConnectedSourcePairWeight_factor
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    couplingSpinSummedSourcePairWeight coupling cutoff entry.val ≈
      couplingSpinSummedConnectedPathPairWeight
          coupling cutoff hsmall entry *
        couplingSpinSummedConnectedBackgroundPairWeight
          coupling cutoff hsmall entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.1.val (connectedPathTest hsmall entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.2.val (connectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold couplingSpinSummedConnectedPathPairWeight
    couplingSpinSummedConnectedBackgroundPairWeight
    connectedPathLeftFamily connectedBackgroundLeftFamily
    connectedPathRightFamily connectedBackgroundRightFamily
  ring_qeqv

theorem couplingSpinSummedConnectedPathPairWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    couplingSpinSummedConnectedPathPairWeight
        coupling cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (connectedCarrierSupport hsmall entry).length := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n (connectedPathLeftFamily hsmall entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n (connectedPathRightFamily hsmall entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff n (connectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (connectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  have htotal :
      couplingSpinSummedConnectedPathPairWeight
          coupling cutoff hsmall entry ≤
        anchorDecoratedFaceEnvelope ^
          (familyFaceCount (connectedPathLeftFamily hsmall entry) +
            familyFaceCount (connectedPathRightFamily hsmall entry)) := by
    unfold couplingSpinSummedConnectedPathPairWeight
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))
  exact Q'.le_trans' _ _ _ htotal
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (connectedCarrierSupport_length_le_pathFaceCount hsmall entry))

theorem couplingSpinSummedConnectedBackgroundPairWeight_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    (0 : Q') ≤ couplingSpinSummedConnectedBackgroundPairWeight
      coupling cutoff hsmall entry := by
  unfold couplingSpinSummedConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)

theorem couplingSpinSummedConnectedSourcePairWeight_le_support_background
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (entry : ConnectedSourceEntry root hsmall) :
    couplingSpinSummedSourcePairWeight coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (connectedCarrierSupport hsmall entry).length *
        couplingSpinSummedConnectedBackgroundPairWeight
          coupling cutoff hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedConnectedSourcePairWeight_factor
        coupling cutoff hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedConnectedPathPairWeight_le_supportPow
        hcoupling hle cutoff hsmall entry)
      (couplingSpinSummedConnectedBackgroundPairWeight_nonnegative
        hcoupling cutoff hsmall entry))

def couplingSpinSummedReverseSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) : Q' :=
  couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.1.val *
    couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.2.val

def couplingSpinSummedReverseConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (reverseConnectedPathLeftFamily hsmall entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (reverseConnectedPathRightFamily hsmall entry)

def couplingSpinSummedReverseConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n
      (reverseConnectedBackgroundRightFamily hsmall entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff n
      (reverseConnectedBackgroundLeftFamily hsmall entry)

theorem couplingSpinSummedReverseConnectedSourcePairWeight_factor
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    couplingSpinSummedReverseSourcePairWeight coupling cutoff entry.val ≈
      couplingSpinSummedReverseConnectedPathPairWeight
          coupling cutoff hsmall entry *
        couplingSpinSummedReverseConnectedBackgroundPairWeight
          coupling cutoff hsmall entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.1.val
      (reverseConnectedPathTest hsmall entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff n entry.val.2.val
      (reverseConnectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold couplingSpinSummedReverseConnectedPathPairWeight
    couplingSpinSummedReverseConnectedBackgroundPairWeight
    reverseConnectedPathLeftFamily reverseConnectedBackgroundLeftFamily
    reverseConnectedPathRightFamily reverseConnectedBackgroundRightFamily
  ring_qeqv

theorem couplingSpinSummedReverseConnectedPathPairWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    couplingSpinSummedReverseConnectedPathPairWeight
        coupling cutoff hsmall entry ≤
      anchorDecoratedFaceEnvelope ^
        (reverseConnectedCarrierSupport hsmall entry).length := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n
      (reverseConnectedPathLeftFamily hsmall entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff n
      (reverseConnectedPathRightFamily hsmall entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff n (reverseConnectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  have htotal :
      couplingSpinSummedReverseConnectedPathPairWeight
          coupling cutoff hsmall entry ≤
        anchorDecoratedFaceEnvelope ^
          (familyFaceCount
              (reverseConnectedPathLeftFamily hsmall entry) +
            familyFaceCount
              (reverseConnectedPathRightFamily hsmall entry)) := by
    unfold couplingSpinSummedReverseConnectedPathPairWeight
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))
  exact Q'.le_trans' _ _ _ htotal
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (reverseConnectedCarrierSupport_length_le_pathFaceCount
        hsmall entry))

theorem couplingSpinSummedReverseConnectedBackgroundPairWeight_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    (0 : Q') ≤ couplingSpinSummedReverseConnectedBackgroundPairWeight
      coupling cutoff hsmall entry := by
  unfold couplingSpinSummedReverseConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff n _)

theorem couplingSpinSummedReverseConnectedSourcePairWeight_le_support_background
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    couplingSpinSummedReverseSourcePairWeight
        coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (reverseConnectedCarrierSupport hsmall entry).length *
        couplingSpinSummedReverseConnectedBackgroundPairWeight
          coupling cutoff hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedReverseConnectedSourcePairWeight_factor
        coupling cutoff hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedReverseConnectedPathPairWeight_le_supportPow
        hcoupling hle cutoff hsmall entry)
      (couplingSpinSummedReverseConnectedBackgroundPairWeight_nonnegative
        hcoupling cutoff hsmall entry))

/-! ## 3. Marked switching and cylinder cell summation -/

theorem markedAtomList_couplingSpinSummedWeight_eq
    (coupling : Q') (cutoff n : Nat) :
    ∀ atoms : List (CanonicalAtom n),
      familyWeight (fun atom : CanonicalAtom n =>
          couplingParametricKSupportActivity
            coupling cutoff n atom.val) atoms =
        couplingParametricKSupportFamilyActivity coupling cutoff n
          (atoms.map Subtype.val)
  | [] => rfl
  | _ :: rest => by
      simp only [familyWeight_cons, List.map,
        couplingParametricKSupportFamilyActivity]
      rw [markedAtomList_couplingSpinSummedWeight_eq
        coupling cutoff n rest]

theorem recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
    (coupling : Q') (cutoff : Nat) {n : Nat}
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    couplingParametricKSupportFamilyActivity coupling cutoff n
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) *
      couplingParametricKSupportFamilyActivity coupling cutoff n
        (recoverableMarkedSwitchedRightFamily hleft hright roots) ≈
    couplingParametricKSupportFamilyActivity coupling cutoff n left *
      couplingParametricKSupportFamilyActivity
        coupling cutoff n right := by
  have hweight := markedRootComponentSwitched_pair_weight_preserved
    (fun atom : CanonicalAtom n =>
      couplingParametricKSupportActivity coupling cutoff n atom.val)
    (canonicalAtomCompatibleB n) roots
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)
  rw [markedAtomList_couplingSpinSummedWeight_eq
    coupling cutoff n] at hweight
  rw [markedAtomList_couplingSpinSummedWeight_eq
    coupling cutoff n] at hweight
  rw [markedAtomList_couplingSpinSummedWeight_eq
    coupling cutoff n] at hweight
  rw [markedAtomList_couplingSpinSummedWeight_eq
    coupling cutoff n] at hweight
  rw [canonicalFamilyAtoms_values hleft] at hweight
  rw [canonicalFamilyAtoms_values hright] at hweight
  exact hweight

def couplingSpinSummedCylinderSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.1.val *
    couplingParametricKSupportFamilyActivity
      coupling cutoff n pair.2.val

def couplingSpinSummedCylinderRawPairWeight
    (coupling : Q') (cutoff n : Nat)
    (pair : Z4CanonicalCylinderSwitchSummation.RawFamilyPair) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff n pair.1 *
    couplingParametricKSupportFamilyActivity coupling cutoff n pair.2

theorem couplingSpinSummedSeparatedCylinderSwitchEncode_weight
    (coupling : Q') (cutoff : Nat)
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) :
    couplingSpinSummedCylinderRawPairWeight coupling cutoff n
        (separatedCylinderSwitchEncode hsmall pair) ≈
      couplingSpinSummedCylinderSourcePairWeight
        coupling cutoff pair := by
  exact recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
    coupling cutoff (cylinderSourceLeftCompatible pair)
    (cylinderSourceRightCompatible hsmall pair) roots

theorem couplingSpinSummedSeparatedCylinderPairSum_le_targetPairSum
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
        (separatedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      listQSum (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
        (cylinderTargetPairList small n roots predicate) := by
  apply listQSum_le_of_injective
    (separatedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)
    (cylinderTargetPairList small n roots predicate)
    (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
    (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
    (separatedCylinderSwitchEncode hsmall)
    (separatedCylinderSourcePairs_nodup hsmall roots predicate)
  · exact separatedCylinderSwitchEncode_mem_target hsmall
  · intro first hfirst second hsecond heq
    exact separatedCylinderSwitchEncode_injective hsmall first second
      hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (couplingSpinSummedSeparatedCylinderSwitchEncode_weight
          coupling cutoff hsmall pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff n pair.1)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff n pair.2)

theorem couplingSpinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          (boundaryCylinderEventFamilyList small n roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          (embeddedCylinderComplementFamilyList small n roots predicate) ≤
      listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (boundaryCylinderComplementFamilyList
              small n roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (embeddedCylinderEventFamilyList small n roots predicate) +
        listQSum
          (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) := by
  have hsource := listQSum_cartesian_product
    (fun entry : BoundaryCylinderEventEntry small n roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff n entry.val)
    (fun entry : EmbeddedCylinderComplementEntry small n roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff n entry.val)
    (boundaryCylinderEventEntries small n roots predicate)
    (embeddedCylinderComplementEntries small n roots predicate)
  have hsourceEq :
      listQSum
          (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
          (cylinderSourcePairList small n roots predicate) ≈
        listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (boundaryCylinderEventFamilyList small n roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (embeddedCylinderComplementFamilyList
              small n roots predicate) := by
    unfold cylinderSourcePairList at hsource ⊢
    refine Q'.eqv_trans _ _ _ hsource ?_
    unfold boundaryCylinderEventEntries
      embeddedCylinderComplementEntries
    rw [listQSum_attach, listQSum_attach]
    exact Q'.eqv_refl _
  have htarget :
      listQSum
          (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
          (cylinderTargetPairList small n roots predicate) ≈
        listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (boundaryCylinderComplementFamilyList
              small n roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity coupling cutoff n)
            (embeddedCylinderEventFamilyList
              small n roots predicate) := by
    exact listQSum_cartesian_product
      (couplingParametricKSupportFamilyActivity coupling cutoff n)
      (couplingParametricKSupportFamilyActivity coupling cutoff n)
      (boundaryCylinderComplementFamilyList small n roots predicate)
      (embeddedCylinderEventFamilyList small n roots predicate)
  have hpartition :
      listQSum
          (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
          (cylinderSourcePairList small n roots predicate) ≈
        listQSum
            (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
            (separatedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) +
          listQSum
            (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    listQSum_filter_partition
      (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
      (cylinderSourceSeparatedB hsmall)
      (cylinderSourcePairList small n roots predicate)
  have hinjection :=
    couplingSpinSummedSeparatedCylinderPairSum_le_targetPairSum
      hcoupling cutoff hsmall roots predicate
  have hsepAdd := Q'.add_le_add hinjection (Q'.le_refl'
    (listQSum
      (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
      (connectedCylinderSourcePairs
        (roots := roots) (predicate := predicate) hsmall)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsourceEq))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

#print axioms couplingParametricKSupportFamilyActivity_le_totalFacePow
#print axioms couplingSpinSummedConnectedSourcePairWeight_le_support_background
#print axioms couplingSpinSummedReverseConnectedSourcePairWeight_le_support_background
#print axioms recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
#print axioms couplingSpinSummedSeparatedCylinderPairSum_le_targetPairSum
#print axioms couplingSpinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected

end YMGap.Continuum.Z4CouplingParametricCylinderWeights
