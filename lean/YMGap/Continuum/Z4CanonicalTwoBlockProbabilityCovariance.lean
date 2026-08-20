/-
# Ordinary Boolean covariance is the normalized four-cell determinant

For two Boolean cylinder events `A` and `B`, the canonical finite polymer
measure has the four cells `TT`, `TF`, `FT`, and `FF`.  This module proves,
inside the constructive rational quotient used by the project, that

  P(A ∩ B) - P(A) P(B) = (TT * FF - FT * TF) / Z^2.

Thus the previously certified four-cell decay estimate is literally a bound
on conventional finite-volume Boolean covariance.  No limiting measure,
Hilbert-space realization, or continuum statement is asserted here.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance

namespace YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockNormalizedCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv_neg" : tactic =>
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

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

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
      (ambient.filter second).filter first := by
  exact Eq.trans (filter_and_eq_filter_filter first second ambient)
    (filters_commute first second ambient)

/-! ## 1. The four unnormalized cell weights -/

def twoBlockTTWeight
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
    (twoBlockTTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def twoBlockTFWeight
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
    (twoBlockTFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def twoBlockFTWeight
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
    (twoBlockFTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def twoBlockFFWeight
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
    (twoBlockFFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

private theorem eventNumerator_eqv_joint_add_complement
    (n : Nat) (first second : TwoBlockPolymerFamily → Bool) :
    anchorEventNumerator n first ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && second family)) +
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && !(second family))) := by
  unfold anchorEventNumerator
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling n) second
    ((canonicalCompatibleAmbientFamilies n).filter first)
  rw [← filter_and_eq_filter_filter first second,
    ← filter_and_eq_filter_filter first (fun family => !(second family))]
    at hsplit
  exact hsplit

theorem firstEventNumerator_eqv_TT_add_TF
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    anchorEventNumerator n
        (blockCylinderEvent firstRoots firstPredicate) ≈
      twoBlockTTWeight firstRoots secondRoots
          firstPredicate secondPredicate +
        twoBlockTFWeight firstRoots secondRoots
          firstPredicate secondPredicate := by
  exact eventNumerator_eqv_joint_add_complement n
    (blockCylinderEvent firstRoots firstPredicate)
    (blockCylinderEvent secondRoots secondPredicate)

private theorem eventNumerator_eqv_reverse_joint_add_complement
    (n : Nat) (first second : TwoBlockPolymerFamily → Bool) :
    anchorEventNumerator n second ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => first family && second family)) +
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          ((canonicalCompatibleAmbientFamilies n).filter
            (fun family => !(first family) && second family)) := by
  unfold anchorEventNumerator
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling n) first
    ((canonicalCompatibleAmbientFamilies n).filter second)
  rw [← filter_and_eq_reverse_filter_filter first second,
    ← filter_and_eq_reverse_filter_filter (fun family => !(first family)) second]
    at hsplit
  exact hsplit

theorem secondEventNumerator_eqv_TT_add_FT
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    anchorEventNumerator n
        (blockCylinderEvent secondRoots secondPredicate) ≈
      twoBlockTTWeight firstRoots secondRoots
          firstPredicate secondPredicate +
        twoBlockFTWeight firstRoots secondRoots
          firstPredicate secondPredicate := by
  exact eventNumerator_eqv_reverse_joint_add_complement n
    (blockCylinderEvent firstRoots firstPredicate)
    (blockCylinderEvent secondRoots secondPredicate)

theorem jointEventNumerator_eqv_TT
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    anchorEventNumerator n (fun family =>
        blockCylinderEvent firstRoots firstPredicate family &&
          blockCylinderEvent secondRoots secondPredicate family) ≈
      twoBlockTTWeight firstRoots secondRoots
        firstPredicate secondPredicate := by
  exact Q'.eqv_refl _

theorem anchorCanonicalPartition_eqv_four_cells
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    anchorCanonicalPartition n ≈
      (twoBlockTTWeight firstRoots secondRoots
          firstPredicate secondPredicate +
        twoBlockTFWeight firstRoots secondRoots
          firstPredicate secondPredicate) +
      (twoBlockFTWeight firstRoots secondRoots
          firstPredicate secondPredicate +
        twoBlockFFWeight firstRoots secondRoots
          firstPredicate secondPredicate) := by
  let first := blockCylinderEvent firstRoots firstPredicate
  let second := blockCylinderEvent secondRoots secondPredicate
  have hsplit := listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling n) first
    (canonicalCompatibleAmbientFamilies n)
  have htrue := eventNumerator_eqv_joint_add_complement n first second
  have hfalse := eventNumerator_eqv_joint_add_complement n
    (fun family => !(first family)) second
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · simpa only [first, second, twoBlockTTWeight, twoBlockTFWeight,
      twoBlockTTFamilyList, twoBlockTFFamilyList] using htrue
  · simpa only [first, second, twoBlockFTWeight, twoBlockFFWeight,
      twoBlockFTFamilyList, twoBlockFFFamilyList] using hfalse

/-! ## 2. Pure quotient algebra -/

/-- Generic normalized cross-numerator identity.  This is the finite
probability algebra behind covariance and does not depend on the polymer
model. -/
theorem normalizedProductDifference_eqv_crossNumerator
    (joint left right z : Q') (hzpos : (0 : Q') < z) :
    Q'.divPos joint z hzpos -
        Q'.divPos left z hzpos * Q'.divPos right z hzpos ≈
      Q'.divPos (joint * z - left * right) (z * z)
        (Q'.mul_pos hzpos hzpos) := by
  let pjoint := Q'.divPos joint z hzpos
  let pleft := Q'.divPos left z hzpos
  let pright := Q'.divPos right z hzpos
  let covariance := pjoint - pleft * pright
  have hjoint : pjoint * z ≈ joint :=
    Q'.divPos_mul_eqv joint z hzpos
  have hleft : pleft * z ≈ left :=
    Q'.divPos_mul_eqv left z hzpos
  have hright : pright * z ≈ right :=
    Q'.divPos_mul_eqv right z hzpos
  have hfactor :
      covariance * (z * z) ≈
        (pjoint * z) * z - (pleft * z) * (pright * z) := by
    unfold covariance
    change (pjoint + -(pleft * pright)) * (z * z) ≈
      (pjoint * z) * z + -((pleft * z) * (pright * z))
    ring_qeqv_neg
  have hcollapse :
      (pjoint * z) * z - (pleft * z) * (pright * z) ≈
        joint * z - left * right := by
    exact sub_eqv_both_local
      (mul_eqv_both_local hjoint (Q'.eqv_refl _))
      (mul_eqv_both_local hleft hright)
  have hcross :
      joint * z - left * right ≈ covariance * (z * z) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ hfactor hcollapse)
  exact Q'.eqv_symm
    (divPos_eqv_of_eqv_mul_local
      (Q'.mul_pos hzpos hzpos) hcross)

private theorem booleanCellCovariance_eqv_cross
    (t u v w z : Q') (hzpos : (0 : Q') < z)
    (hz : z ≈ (t + u) + (v + w)) :
    Q'.divPos t z hzpos -
        Q'.divPos (t + u) z hzpos * Q'.divPos (t + v) z hzpos ≈
      Q'.divPos (t * w - v * u) (z * z)
        (Q'.mul_pos hzpos hzpos) := by
  let pt := Q'.divPos t z hzpos
  let pa := Q'.divPos (t + u) z hzpos
  let pb := Q'.divPos (t + v) z hzpos
  let covariance := pt - pa * pb
  have hpt : pt * z ≈ t := Q'.divPos_mul_eqv t z hzpos
  have hpa : pa * z ≈ t + u := Q'.divPos_mul_eqv (t + u) z hzpos
  have hpb : pb * z ≈ t + v := Q'.divPos_mul_eqv (t + v) z hzpos
  have hfactor :
      covariance * (z * z) ≈
        (pt * z) * z - (pa * z) * (pb * z) := by
    unfold covariance
    change (pt + -(pa * pb)) * (z * z) ≈
      (pt * z) * z + -((pa * z) * (pb * z))
    ring_qeqv_neg
  have hcollapse :
      (pt * z) * z - (pa * z) * (pb * z) ≈
        t * z - (t + u) * (t + v) := by
    exact sub_eqv_both_local
      (mul_eqv_both_local hpt (Q'.eqv_refl _))
      (mul_eqv_both_local hpa hpb)
  have hcells :
      t * z - (t + u) * (t + v) ≈ t * w - v * u := by
    refine Q'.eqv_trans _
      (t * ((t + u) + (v + w)) - (t + u) * (t + v)) _ ?_ ?_
    · exact sub_eqv_both_local
        (mul_eqv_both_local (Q'.eqv_refl _) hz)
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      (((t + u) + (v + w)) * t - (t + u) * (t + v)) _ ?_ ?_
    · exact sub_eqv_both_local
        (Q'.mul_comm_eqv t ((t + u) + (v + w)))
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      ((v + w) * t - (t + u) * v) _
      (crossDifference_split (t + u) (v + w) t v) ?_
    refine Q'.eqv_trans _
      ((v + w) * t - v * (t + u)) _ ?_ ?_
    · exact sub_eqv_both_local (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (t + u) v)
    refine Q'.eqv_trans _ (w * t - v * u) _
      (crossDifference_split v w t u) ?_
    exact sub_eqv_both_local (Q'.mul_comm_eqv w t) (Q'.eqv_refl _)
  have hcross : t * w - v * u ≈ covariance * (z * z) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _ hcollapse hcells))
  exact Q'.eqv_symm
    (divPos_eqv_of_eqv_mul_local
      (Q'.mul_pos hzpos hzpos) hcross)

/-! ## 3. Conventional covariance identification -/

def anchorTwoBlockBooleanCovariance
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) : Q' :=
  anchorEventProbability n (fun family =>
      blockCylinderEvent firstRoots firstPredicate family &&
        blockCylinderEvent secondRoots secondPredicate family) -
    anchorEventProbability n
        (blockCylinderEvent firstRoots firstPredicate) *
      anchorEventProbability n
        (blockCylinderEvent secondRoots secondPredicate)

/-- Exact identification of conventional finite-volume Boolean covariance
with the normalized determinant controlled by the component-switch proof. -/
theorem anchorTwoBlockBooleanCovariance_eqv_normalizedFourCell
    (n : Nat) (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    anchorTwoBlockBooleanCovariance n firstRoots secondRoots
        firstPredicate secondPredicate ≈
      normalizedTwoBlockFourCellCovariance n firstRoots secondRoots
        firstPredicate secondPredicate := by
  let tt := twoBlockTTWeight firstRoots secondRoots
    firstPredicate secondPredicate
  let tf := twoBlockTFWeight firstRoots secondRoots
    firstPredicate secondPredicate
  let ft := twoBlockFTWeight firstRoots secondRoots
    firstPredicate secondPredicate
  let ff := twoBlockFFWeight firstRoots secondRoots
    firstPredicate secondPredicate
  let z := anchorCanonicalPartition n
  have hjoint := jointEventNumerator_eqv_TT
    firstRoots secondRoots firstPredicate secondPredicate
  have hfirst := firstEventNumerator_eqv_TT_add_TF
    firstRoots secondRoots firstPredicate secondPredicate
  have hsecond := secondEventNumerator_eqv_TT_add_FT
    firstRoots secondRoots firstPredicate secondPredicate
  have hz := anchorCanonicalPartition_eqv_four_cells
    firstRoots secondRoots firstPredicate secondPredicate
  have hpjoint :
      anchorEventProbability n (fun family =>
          blockCylinderEvent firstRoots firstPredicate family &&
            blockCylinderEvent secondRoots secondPredicate family) ≈
        Q'.divPos tt z (anchorCanonicalPartition_pos n) := by
    unfold anchorEventProbability
    exact divPos_numerator_eqv_local
      (anchorCanonicalPartition_pos n) hjoint
  have hpfirst :
      anchorEventProbability n
          (blockCylinderEvent firstRoots firstPredicate) ≈
        Q'.divPos (tt + tf) z (anchorCanonicalPartition_pos n) := by
    unfold anchorEventProbability
    exact divPos_numerator_eqv_local
      (anchorCanonicalPartition_pos n) hfirst
  have hpsecond :
      anchorEventProbability n
          (blockCylinderEvent secondRoots secondPredicate) ≈
        Q'.divPos (tt + ft) z (anchorCanonicalPartition_pos n) := by
    unfold anchorEventProbability
    exact divPos_numerator_eqv_local
      (anchorCanonicalPartition_pos n) hsecond
  have hprobability :
      anchorTwoBlockBooleanCovariance n firstRoots secondRoots
          firstPredicate secondPredicate ≈
        Q'.divPos tt z (anchorCanonicalPartition_pos n) -
          Q'.divPos (tt + tf) z (anchorCanonicalPartition_pos n) *
            Q'.divPos (tt + ft) z (anchorCanonicalPartition_pos n) := by
    unfold anchorTwoBlockBooleanCovariance
    exact sub_eqv_both_local hpjoint
      (mul_eqv_both_local hpfirst hpsecond)
  refine Q'.eqv_trans _ _ _ hprobability ?_
  have hcell := booleanCellCovariance_eqv_cross tt tf ft ff z
    (anchorCanonicalPartition_pos n) hz
  refine Q'.eqv_trans _ _ _ hcell ?_
  dsimp only [tt, tf, ft, ff, z]
  unfold normalizedTwoBlockFourCellCovariance
    twoBlockFourCellCrossNumerator
    twoBlockTTWeight twoBlockTFWeight twoBlockFTWeight twoBlockFFWeight
  exact Q'.eqv_refl _

#print axioms firstEventNumerator_eqv_TT_add_TF
#print axioms secondEventNumerator_eqv_TT_add_FT
#print axioms anchorCanonicalPartition_eqv_four_cells
#print axioms normalizedProductDifference_eqv_crossNumerator
#print axioms anchorTwoBlockBooleanCovariance_eqv_normalizedFourCell

end YMGap.Continuum.Z4CanonicalTwoBlockProbabilityCovariance
