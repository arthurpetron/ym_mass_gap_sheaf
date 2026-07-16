/-
# Arbitrary-cutoff weight envelope for the slab connected carrier

For the exact coupling-parametric spin-summed support gas, the two-replica
source weight factors into the selected path families and the path-deleted
backgrounds.  The path factor is bounded uniformly in the character cutoff
by the derived decorated-face envelope.  Both background activities remain
literal finite-cutoff activities; they are not replaced by an upper bound.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierWeight

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

def couplingSpinSummedSlabConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (extent + 1)
      (slabConnectedPathLeftFamily defaultRoot entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (extent + 1)
      (slabConnectedPathRightFamily defaultRoot entry)

def couplingSpinSummedSlabConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (extent + 1)
      (slabConnectedBackgroundLeftFamily defaultRoot entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (extent + 1)
      (slabConnectedBackgroundRightFamily defaultRoot entry)

theorem couplingSpinSummedSlabConnectedSourcePairWeight_factor
    (coupling : Q') (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff entry.val ≈
      couplingSpinSummedSlabConnectedPathPairWeight
          coupling cutoff defaultRoot entry *
        couplingSpinSummedSlabConnectedBackgroundPairWeight
          coupling cutoff defaultRoot entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (extent + 1) entry.val.1.val
      (slabConnectedPathTest defaultRoot entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (extent + 1) entry.val.2.val
      (slabConnectedPathTest defaultRoot entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold couplingSpinSummedSlabConnectedPathPairWeight
    couplingSpinSummedSlabConnectedBackgroundPairWeight
    slabConnectedPathLeftFamily slabConnectedBackgroundLeftFamily
    slabConnectedPathRightFamily slabConnectedBackgroundRightFamily
  ring_qeqv

theorem couplingSpinSummedSlabConnectedPathPairWeight_le_totalFacePow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    couplingSpinSummedSlabConnectedPathPairWeight
        coupling cutoff defaultRoot entry ≤
      anchorDecoratedFaceEnvelope ^
        (familyFaceCount (slabConnectedPathLeftFamily defaultRoot entry) +
          familyFaceCount
            (slabConnectedPathRightFamily defaultRoot entry)) := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (extent + 1)
      (slabConnectedPathLeftFamily defaultRoot entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (extent + 1)
      (slabConnectedPathRightFamily defaultRoot entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff (extent + 1)
      (slabConnectedPathRightFamily defaultRoot entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (slabConnectedPathLeftFamily defaultRoot entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold couplingSpinSummedSlabConnectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))

theorem couplingSpinSummedSlabConnectedPathPairWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    couplingSpinSummedSlabConnectedPathPairWeight
        coupling cutoff defaultRoot entry ≤
      anchorDecoratedFaceEnvelope ^
        (slabConnectedCarrierSupport defaultRoot entry).length := by
  exact Q'.le_trans' _ _ _
    (couplingSpinSummedSlabConnectedPathPairWeight_le_totalFacePow
      hcoupling hle cutoff defaultRoot entry)
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (slabConnectedCarrierSupport_length_le_pathFaceCount
        defaultRoot entry))

theorem couplingSpinSummedSlabConnectedBackgroundPairWeight_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    (0 : Q') ≤ couplingSpinSummedSlabConnectedBackgroundPairWeight
      coupling cutoff defaultRoot entry := by
  unfold couplingSpinSummedSlabConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff (extent + 1) _)
    (couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff (extent + 1) _)

theorem couplingSpinSummedSlabConnectedSourcePairWeight_le_support_background
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (slabConnectedCarrierSupport defaultRoot entry).length *
        couplingSpinSummedSlabConnectedBackgroundPairWeight
          coupling cutoff defaultRoot entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedSlabConnectedSourcePairWeight_factor
        coupling cutoff defaultRoot entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedSlabConnectedPathPairWeight_le_supportPow
        hcoupling hle cutoff defaultRoot entry)
      (couplingSpinSummedSlabConnectedBackgroundPairWeight_nonnegative
        hcoupling cutoff defaultRoot entry))

#print axioms couplingSpinSummedSlabConnectedSourcePairWeight_factor
#print axioms couplingSpinSummedSlabConnectedPathPairWeight_le_supportPow
#print axioms couplingSpinSummedSlabConnectedSourcePairWeight_le_support_background

end YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierWeight
