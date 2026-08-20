/-
# Arbitrary-cutoff two-block covariance as a four-cell determinant

The spin-summed support gas is exactly the physical finite-cutoff law after
the representation labels have been summed over.  This file performs the
probability algebra needed for temporal clustering at that level.  For two
Boolean cylinder events it proves, uniformly in coupling and cutoff,

  P(A and B) - P(A) P(B) = (TT * FF - FT * TF) / Z^2.

No cluster bound is asserted here.  The result identifies the exact
four-cell numerator to which the arbitrary-cutoff connected-carrier estimate
must be applied next.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_numerator_eqv_local {p p' q : Q'}
    (hq : (0 : Q') < q) (hp : p ≈ p') :
    Q'.divPos p q hq ≈ Q'.divPos p' q hq := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem filter_and_eq_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

private theorem filters_commute {A : Type}
    (first second : A → Bool) (ambient : List A) :
    (ambient.filter first).filter second =
      (ambient.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

private theorem filter_and_eq_reverse_filter_filter {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter second).filter first :=
  Eq.trans (filter_and_eq_filter_filter first second ambient)
    (filters_commute first second ambient)

/-! ## 1. The four spin-summed cells -/

def couplingParametricKTwoBlockTTWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (twoBlockTTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def couplingParametricKTwoBlockTFWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (twoBlockTFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def couplingParametricKTwoBlockFTWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (twoBlockFTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def couplingParametricKTwoBlockFFWeight
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (twoBlockFFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

private theorem eventNumerator_eqv_joint_add_complement
    (coupling : Q') (cutoff n : Nat)
    (first second : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n first ≈
      listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && second family)) +
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && !(second family))) := by
  unfold couplingParametricKCompatibleSupportEventNumerator
  have hsplit := listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n) second
    ((canonicalCompatibleAmbientFamilies n).filter first)
  rw [← filter_and_eq_filter_filter first second,
    ← filter_and_eq_filter_filter first (fun family => !(second family))]
    at hsplit
  exact hsplit

theorem couplingParametricKFirstEventNumerator_eqv_TT_add_TF
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator coupling cutoff n
        (blockCylinderEvent firstRoots firstPredicate) ≈
      couplingParametricKTwoBlockTTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate +
        couplingParametricKTwoBlockTFWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate :=
  eventNumerator_eqv_joint_add_complement coupling cutoff n
    (blockCylinderEvent firstRoots firstPredicate)
    (blockCylinderEvent secondRoots secondPredicate)

private theorem eventNumerator_eqv_reverse_joint_add_complement
    (coupling : Q') (cutoff n : Nat)
    (first second : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n second ≈
      listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && second family)) +
        listQSum
          (couplingParametricKSupportFamilyActivity coupling cutoff n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => !(first family) && second family)) := by
  unfold couplingParametricKCompatibleSupportEventNumerator
  have hsplit := listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n) first
    ((canonicalCompatibleAmbientFamilies n).filter second)
  rw [← filter_and_eq_reverse_filter_filter first second,
    ← filter_and_eq_reverse_filter_filter
      (fun family => !(first family)) second] at hsplit
  exact hsplit

theorem couplingParametricKSecondEventNumerator_eqv_TT_add_FT
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator coupling cutoff n
        (blockCylinderEvent secondRoots secondPredicate) ≈
      couplingParametricKTwoBlockTTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate +
        couplingParametricKTwoBlockFTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate :=
  eventNumerator_eqv_reverse_joint_add_complement coupling cutoff n
    (blockCylinderEvent firstRoots firstPredicate)
    (blockCylinderEvent secondRoots secondPredicate)

theorem couplingParametricKJointEventNumerator_eqv_TT
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportEventNumerator coupling cutoff n
        (fun family =>
          blockCylinderEvent firstRoots firstPredicate family &&
            blockCylinderEvent secondRoots secondPredicate family) ≈
      couplingParametricKTwoBlockTTWeight coupling cutoff
        firstRoots secondRoots firstPredicate secondPredicate :=
  Q'.eqv_refl _

theorem couplingParametricKCompatiblePartition_eqv_four_cells
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n ≈
      (couplingParametricKTwoBlockTTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate +
        couplingParametricKTwoBlockTFWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate) +
      (couplingParametricKTwoBlockFTWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate +
        couplingParametricKTwoBlockFFWeight coupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate) := by
  let first := blockCylinderEvent firstRoots firstPredicate
  let second := blockCylinderEvent secondRoots secondPredicate
  have hsplit := listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n) first
    (canonicalCompatibleAmbientFamilies n)
  have htrue := eventNumerator_eqv_joint_add_complement
    coupling cutoff n first second
  have hfalse := eventNumerator_eqv_joint_add_complement
    coupling cutoff n (fun family => !(first family)) second
  unfold couplingParametricKCompatibleSupportGasPartition
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · simpa only [first, second, couplingParametricKTwoBlockTTWeight,
      couplingParametricKTwoBlockTFWeight, twoBlockTTFamilyList,
      twoBlockTFFamilyList] using htrue
  · simpa only [first, second, couplingParametricKTwoBlockFTWeight,
      couplingParametricKTwoBlockFFWeight, twoBlockFTFamilyList,
      twoBlockFFFamilyList] using hfalse

/-! ## 2. Normalized determinant and ordinary covariance -/

def couplingParametricKTwoBlockFourCellCrossNumerator
    (coupling : Q') (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  couplingParametricKTwoBlockTTWeight coupling cutoff
      firstRoots secondRoots firstPredicate secondPredicate *
    couplingParametricKTwoBlockFFWeight coupling cutoff
      firstRoots secondRoots firstPredicate secondPredicate -
  couplingParametricKTwoBlockFTWeight coupling cutoff
      firstRoots secondRoots firstPredicate secondPredicate *
    couplingParametricKTwoBlockTFWeight coupling cutoff
      firstRoots secondRoots firstPredicate secondPredicate

def couplingParametricKNormalizedTwoBlockFourCellCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  let z := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff n
  Q'.divPos
    (couplingParametricKTwoBlockFourCellCrossNumerator coupling cutoff
      firstRoots secondRoots firstPredicate secondPredicate)
    (z * z)
    (Q'.mul_pos
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff n)
      (couplingParametricKCompatibleSupportGasPartition_pos
        hcoupling cutoff n))

def couplingParametricKTwoBlockBooleanCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventProbability coupling hcoupling
      cutoff n (fun family =>
        blockCylinderEvent firstRoots firstPredicate family &&
          blockCylinderEvent secondRoots secondPredicate family) -
    couplingParametricKCompatibleSupportEventProbability coupling hcoupling
        cutoff n (blockCylinderEvent firstRoots firstPredicate) *
      couplingParametricKCompatibleSupportEventProbability coupling hcoupling
        cutoff n (blockCylinderEvent secondRoots secondPredicate)

private theorem fourCellCross_eqv_jointCross
    (tt tf ft ff z : Q')
    (hz : z ≈ (tt + tf) + (ft + ff)) :
    tt * z - (tt + tf) * (tt + ft) ≈ tt * ff - ft * tf := by
  refine Q'.eqv_trans _
    (tt * ((tt + tf) + (ft + ff)) -
      (tt + tf) * (tt + ft)) _ ?_ ?_
  · exact sub_eqv_both_local
      (mul_eqv_both_local (Q'.eqv_refl _) hz)
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (((tt + tf) + (ft + ff)) * tt - (tt + tf) * (tt + ft)) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.mul_comm_eqv tt ((tt + tf) + (ft + ff)))
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      ((ft + ff) * tt - (tt + tf) * ft) _
      (crossDifference_split (tt + tf) (ft + ff) tt ft) ?_
    refine Q'.eqv_trans _
      ((ft + ff) * tt - ft * (tt + tf)) _ ?_ ?_
    · exact sub_eqv_both_local (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (tt + tf) ft)
    refine Q'.eqv_trans _ (ff * tt - ft * tf) _
      (crossDifference_split ft ff tt tf) ?_
    exact sub_eqv_both_local (Q'.mul_comm_eqv ff tt) (Q'.eqv_refl _)

/-- The physical arbitrary-cutoff Boolean covariance is exactly the normalized
four-cell determinant for the same spin-summed support law. -/
theorem couplingParametricKTwoBlockBooleanCovariance_eqv_normalizedFourCell
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
        firstRoots secondRoots firstPredicate secondPredicate ≈
      couplingParametricKNormalizedTwoBlockFourCellCovariance
        hcoupling cutoff firstRoots secondRoots
        firstPredicate secondPredicate := by
  let tt := couplingParametricKTwoBlockTTWeight coupling cutoff
    firstRoots secondRoots firstPredicate secondPredicate
  let tf := couplingParametricKTwoBlockTFWeight coupling cutoff
    firstRoots secondRoots firstPredicate secondPredicate
  let ft := couplingParametricKTwoBlockFTWeight coupling cutoff
    firstRoots secondRoots firstPredicate secondPredicate
  let ff := couplingParametricKTwoBlockFFWeight coupling cutoff
    firstRoots secondRoots firstPredicate secondPredicate
  let z := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff n
  have hzpos : (0 : Q') < z :=
    couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff n
  have hjoint := couplingParametricKJointEventNumerator_eqv_TT
    coupling cutoff firstRoots secondRoots firstPredicate secondPredicate
  have hfirst := couplingParametricKFirstEventNumerator_eqv_TT_add_TF
    coupling cutoff firstRoots secondRoots firstPredicate secondPredicate
  have hsecond := couplingParametricKSecondEventNumerator_eqv_TT_add_FT
    coupling cutoff firstRoots secondRoots firstPredicate secondPredicate
  have hz := couplingParametricKCompatiblePartition_eqv_four_cells
    coupling cutoff firstRoots secondRoots firstPredicate secondPredicate
  have hpjoint :
      couplingParametricKCompatibleSupportEventProbability coupling hcoupling
          cutoff n (fun family =>
            blockCylinderEvent firstRoots firstPredicate family &&
              blockCylinderEvent secondRoots secondPredicate family) ≈
        Q'.divPos tt z hzpos := by
    unfold couplingParametricKCompatibleSupportEventProbability
    exact divPos_numerator_eqv_local hzpos hjoint
  have hpfirst :
      couplingParametricKCompatibleSupportEventProbability coupling hcoupling
          cutoff n (blockCylinderEvent firstRoots firstPredicate) ≈
        Q'.divPos (tt + tf) z hzpos := by
    unfold couplingParametricKCompatibleSupportEventProbability
    exact divPos_numerator_eqv_local hzpos hfirst
  have hpsecond :
      couplingParametricKCompatibleSupportEventProbability coupling hcoupling
          cutoff n (blockCylinderEvent secondRoots secondPredicate) ≈
        Q'.divPos (tt + ft) z hzpos := by
    unfold couplingParametricKCompatibleSupportEventProbability
    exact divPos_numerator_eqv_local hzpos hsecond
  have hprobability :
      couplingParametricKTwoBlockBooleanCovariance hcoupling cutoff
          firstRoots secondRoots firstPredicate secondPredicate ≈
        Q'.divPos tt z hzpos -
          Q'.divPos (tt + tf) z hzpos *
            Q'.divPos (tt + ft) z hzpos := by
    unfold couplingParametricKTwoBlockBooleanCovariance
    exact sub_eqv_both_local hpjoint
      (mul_eqv_both_local hpfirst hpsecond)
  refine Q'.eqv_trans _ _ _ hprobability ?_
  have hgeneric := normalizedProductDifference_eqv_crossNumerator
    tt (tt + tf) (tt + ft) z hzpos
  refine Q'.eqv_trans _ _ _ hgeneric ?_
  have hcross := fourCellCross_eqv_jointCross tt tf ft ff z hz
  have hquotient := divPos_numerator_eqv_local
    (Q'.mul_pos hzpos hzpos) hcross
  refine Q'.eqv_trans _ _ _ hquotient ?_
  dsimp only [tt, tf, ft, ff, z]
  unfold couplingParametricKNormalizedTwoBlockFourCellCovariance
    couplingParametricKTwoBlockFourCellCrossNumerator
  exact Q'.eqv_refl _

#print axioms couplingParametricKFirstEventNumerator_eqv_TT_add_TF
#print axioms couplingParametricKSecondEventNumerator_eqv_TT_add_FT
#print axioms couplingParametricKCompatiblePartition_eqv_four_cells
#print axioms couplingParametricKTwoBlockBooleanCovariance_eqv_normalizedFourCell

end YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
