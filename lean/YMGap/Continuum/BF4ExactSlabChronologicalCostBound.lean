/-
# Exact area budget for the original chronological step cost

The cut and incident star each pay their actual numbers of changed faces.
The chronological area bound and the six-face star bound give one positive,
nome-dependent cost for every step. This is a finite-volume coefficient,
not a spatially useful or scaling-uniform estimate.
-/

import YMGap.Continuum.BF4ExactSlabChronologicalPathSum
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.BF4ExactSlabStarRateObstruction
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.BF4ExactSlabChronologicalCostBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabStarRateObstruction
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabOrderedPathCut
open YMGap.Continuum.BF4ExactSlabOrderedPathEnergy
open YMGap.Continuum.BF4ExactSlabChronologicalPathSum
open YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound (pow_add_eqv)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Maximum number of cut faces at any chronological prefix. -/
def areaFaces (extent : Nat) : Nat := 12 * (extent+1)^3

/-- Positive one-face comparison ratio. Its square appears once for each
changed face and each incident star face. -/
def faceRatio {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Q' :=
  Q'.recipPos (headFloor w) (headFloor_positive hw0 hw1) * prefixCap w

theorem faceRatio_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) : (0 : Q') < faceRatio hw0 hw1 :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1) (prefixCap_ge_one hw0 hw1))

/-- The exact area-and-star floor. No volume-wide factor is inserted. -/
def areaFloor (w : Q') (extent : Nat) : Q' :=
  (headFloor w * headFloor w)^areaFaces extent *
    ((headFloor w)^6 * (headFloor w)^6)

/-- The matching exact cap. -/
def areaCap (w : Q') (extent : Nat) : Q' :=
  (prefixCap w * prefixCap w)^areaFaces extent *
    ((prefixCap w)^6 * (prefixCap w)^6)

theorem areaFloor_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    (0 : Q') < areaFloor w extent :=
  Q'.mul_pos
    (HKPos.pow_pos (Q'.mul_pos (headFloor_positive hw0 hw1)
      (headFloor_positive hw0 hw1)) _)
    (Q'.mul_pos (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
      (HKPos.pow_pos (headFloor_positive hw0 hw1) _))

theorem areaCap_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    (0 : Q') < areaCap w extent := by
  have hU : (0 : Q') < prefixCap w := Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1) (prefixCap_ge_one hw0 hw1)
  exact Q'.mul_pos (HKPos.pow_pos (Q'.mul_pos hU hU) _)
    (Q'.mul_pos (HKPos.pow_pos hU _) (HKPos.pow_pos hU _))

/-- One explicit positive budget for all chronological costs. Algebraically
this is `(prefixCap/headFloor)^(2*areaFaces+12)`. -/
def areaCost {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : Q' :=
  Q'.recipPos (areaFloor w extent) (areaFloor_positive hw0 hw1 extent) *
    areaCap w extent

theorem areaCost_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) :
    (0 : Q') < areaCost hw0 hw1 extent :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (areaCap_positive hw0 hw1 extent)

private theorem one_le_pow (r : Q') (hr : (1 : Q') ≤ r) :
    ∀ k : Nat, (1 : Q') ≤ r^k
  | 0 => Q'.le_refl' _
  | k+1 => by
      rw [Q'.pow_succ]
      have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ Q'.zero_le_one hr
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hr
        (Q'.pow_nonneg r hr0 k)
      exact Q'.le_trans' _ _ _ (one_le_pow r hr k)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _).symm) hm)

private theorem pow_exponent_mono (r : Q') (hr : (1 : Q') ≤ r)
    {m n : Nat} (hm : m ≤ n) : r^m ≤ r^n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ Q'.zero_le_one hr
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_pow r hr d)
    (Q'.pow_nonneg r hr0 m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _).symm)
    (Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv (pow_add_eqv r m d)))

private theorem floorSquare_le_one {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    headFloor w * headFloor w ≤ (1 : Q') := by
  have h : headFloor w ≤ (1 : Q') := Q'.le_trans' _ _ _
    (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h
      (Q'.le_of_lt (headFloor_positive hw0 hw1)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) h)

private theorem capSquare_ge_one {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ prefixCap w * prefixCap w := by
  have h := prefixCap_ge_one hw0 hw1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.mul_le_mul_of_nonneg h h
      (Q'.le_trans' _ _ _ Q'.zero_le_one h) Q'.zero_le_one)

private theorem areaFloor_le_stepFloor {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (A : List Nat) (link : Z4Link)
    (hcross : crossingCount extent (selectedLinks extent A) ≤ areaFaces extent) :
    areaFloor w extent ≤ stepFloor w extent A link := by
  have hL0 := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hL20 := Q'.mul_nonneg _ _ hL0 hL0
  have hcut := HKConvGen.pow_base_antitone hL20
    (floorSquare_le_one hw0 hw1) hcross
  have hstar := HKConvGen.pow_base_antitone hL0
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide))
    (incidentIds_length_le_six extent link)
  exact Q'.mul_le_mul_of_nonneg hcut
    (Q'.mul_le_mul_of_nonneg hstar hstar
      (Q'.pow_nonneg _ hL0 (incidentIds extent link).length)
      (Q'.pow_nonneg _ hL0 6))
    (Q'.pow_nonneg _ hL20 (crossingCount extent (selectedLinks extent A)))
    (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hL0 _) (Q'.pow_nonneg _ hL0 _))

private theorem stepCap_le_areaCap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (A : List Nat) (link : Z4Link)
    (hcross : crossingCount extent (selectedLinks extent A) ≤ areaFaces extent) :
    (prefixCap w * prefixCap w)^crossingCount extent (selectedLinks extent A) *
      (starUpper w extent link * starUpper w extent link) ≤ areaCap w extent := by
  have hU0 : (0 : Q') ≤ prefixCap w := Q'.le_trans' _ _ _
    Q'.zero_le_one (prefixCap_ge_one hw0 hw1)
  have hU20 := Q'.mul_nonneg _ _ hU0 hU0
  have hcut := pow_exponent_mono (prefixCap w * prefixCap w)
    (capSquare_ge_one hw0 hw1) hcross
  have hstar := pow_exponent_mono (prefixCap w)
    (prefixCap_ge_one hw0 hw1) (incidentIds_length_le_six extent link)
  exact Q'.mul_le_mul_of_nonneg hcut
    (Q'.mul_le_mul_of_nonneg hstar hstar
      (Q'.pow_nonneg _ hU0 6)
      (Q'.pow_nonneg _ hU0 (incidentIds extent link).length))
    (Q'.pow_nonneg _ hU20 _)
    (Q'.mul_nonneg _ _ (Q'.pow_nonneg _ hU0 _) (Q'.pow_nonneg _ hU0 _))

private theorem ratio_upper (floor cap floorBound capBound : Q')
    (hfloor : (0 : Q') < floor) (hfloorBound : (0 : Q') < floorBound)
    (hfloorLe : floorBound ≤ floor) (hcapLe : cap ≤ capBound)
    (hcapBound : (0 : Q') ≤ capBound) :
    Q'.recipPos floor hfloor * cap ≤
      Q'.recipPos floorBound hfloorBound * capBound := by
  let r := Q'.recipPos floorBound hfloorBound
  let cost := r * capBound
  have hcost : (0 : Q') ≤ cost := Q'.mul_nonneg _ _
    (Q'.le_of_lt (Q'.recipPos_pos _ _)) hcapBound
  have hpin : cost * floorBound ≈ capBound := by
    change (r * capBound) * floorBound ≈ capBound
    calc
      (r * capBound) * floorBound ≈ capBound * (floorBound * r) := by ring_qeqv
      _ ≈ capBound * 1 := Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv floorBound hfloorBound)
      _ ≈ capBound := Q'.mul_one_eqv _
  have hupper : cap ≤ cost * floor :=
    Q'.le_trans' _ _ _ hcapLe
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hfloorLe hcost))
  have hdiv := Q'.divPos_le_of_le_mul cap floor hfloor hupper
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hdiv

/-- The exact original cut/star comparison cost is bounded by the single
area-and-six-star budget, with no additional exponent. -/
theorem stepCost_le_areaCost {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (A : List Nat) (link : Z4Link)
    (hcross : crossingCount extent (selectedLinks extent A) ≤ areaFaces extent) :
    stepCost hw0 hw1 extent A link ≤ areaCost hw0 hw1 extent :=
  ratio_upper _ _ _ _ (stepFloor_positive hw0 hw1 extent A link)
    (areaFloor_positive hw0 hw1 extent)
    (areaFloor_le_stepFloor hw0 hw1 extent A link hcross)
    (stepCap_le_areaCap hw0 hw1 extent A link hcross)
    (Q'.le_of_lt (areaCap_positive hw0 hw1 extent))

/-- Every actual chronological next-link cost obeys the same bound. -/
theorem chronological_stepCost_le_areaCost {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent k : Nat) (hk : k < blocks extent) :
    stepCost hw0 hw1 extent ((chronologicalBlocks extent).take k)
      (nextPhysicalLink extent k hk).val ≤ areaCost hw0 hw1 extent :=
  stepCost_le_areaCost hw0 hw1 extent _ _
    (chronological_cost_crossing_bound extent k hk)

#print axioms areaFaces
#print axioms faceRatio
#print axioms faceRatio_positive
#print axioms areaFloor
#print axioms areaCap
#print axioms areaFloor_positive
#print axioms areaCap_positive
#print axioms areaCost
#print axioms areaCost_positive
#print axioms stepCost_le_areaCost
#print axioms chronological_stepCost_le_areaCost

end YMGap.Continuum.BF4ExactSlabChronologicalCostBound
