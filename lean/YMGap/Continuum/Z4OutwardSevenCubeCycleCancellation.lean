/-
# Exact actual-weight cancellation for the seven-cube outward cycle

The heavy finite-geometric truth tables live in the preceding module.  This
small layer imports those checked certificates and performs only the signed
rational algebra.  Keeping the layers separate prevents repeated elaboration
of the literal 28-face supports while checking the four-cycle identity.
-/

import YMGap.Continuum.Z4OutwardSevenCubeSignedCycle

namespace YMGap.Continuum.Z4OutwardSevenCubeCycleCancellation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath
open YMGap.Continuum.Z4OutwardSevenCubeCycleActivity
open YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
open YMGap.Continuum.Z4OutwardSevenCubeSignedCycle
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

local infix:50 " ≈ " => Q'.eqv

def sevenCube011To100Activity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [sevenCube011To100Root]

def sevenCube100To000Activity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [sevenCube100To000Root]

def sevenCube000To111Activity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [sevenCube000To111Root]

def sevenCube111To011Activity (coupling : Q') : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    [sevenCube111To011Root]

def sevenCubeCommonActivity (coupling : Q') : Q' :=
  (coeffW coupling 1) ^ 28 * 2

/-- Four directed edges with their four activities kept independent. -/
def sevenCubeFourCycleProfile
    (activity011To100 activity100To000 activity000To111
      activity111To011 : Q')
    (pattern : ThreeBlockPattern) : Q' :=
  outwardSignedDirectedPatternEdge activity011To100
      (false, true, true) (true, false, false) pattern +
    outwardSignedDirectedPatternEdge activity100To000
      (true, false, false) (false, false, false) pattern +
    outwardSignedDirectedPatternEdge activity000To111
      (false, false, false) (true, true, true) pattern +
    outwardSignedDirectedPatternEdge activity111To011
      (true, true, true) (false, true, true) pattern

def sevenCubeActualFourCycleProfile
    (coupling : Q') (pattern : ThreeBlockPattern) : Q' :=
  sevenCubeFourCycleProfile
    (sevenCube011To100Activity coupling)
    (sevenCube100To000Activity coupling)
    (sevenCube000To111Activity coupling)
    (sevenCube111To011Activity coupling) pattern

private theorem directedPatternEdge_activity_eqv
    {left right : Q'} (hactivity : left ≈ right)
    (coarse fine pattern : ThreeBlockPattern) :
    outwardSignedDirectedPatternEdge left coarse fine pattern ≈
      outwardSignedDirectedPatternEdge right coarse fine pattern := by
  unfold outwardSignedDirectedPatternEdge
  split
  · exact hactivity
  · split
    · exact Q'.neg_eqv_congr left right hactivity
    · exact Q'.eqv_refl 0

theorem sevenCubeActualFourCycleProfile_eqv_common
    (coupling : Q') (pattern : ThreeBlockPattern) :
    sevenCubeActualFourCycleProfile coupling pattern ≈
      sevenCubeFourCycleProfile
        (sevenCubeCommonActivity coupling)
        (sevenCubeCommonActivity coupling)
        (sevenCubeCommonActivity coupling)
        (sevenCubeCommonActivity coupling) pattern := by
  unfold sevenCubeActualFourCycleProfile sevenCubeFourCycleProfile
    sevenCube011To100Activity sevenCube100To000Activity
    sevenCube000To111Activity sevenCube111To011Activity
    sevenCubeCommonActivity
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (directedPatternEdge_activity_eqv
          (sevenCube011To100_singletonFamilyActivity_eqv_common coupling)
          (false, true, true) (true, false, false) pattern)
        (directedPatternEdge_activity_eqv
          (sevenCube100To000_singletonFamilyActivity_eqv_common coupling)
          (true, false, false) (false, false, false) pattern))
      (directedPatternEdge_activity_eqv
        (sevenCube000To111_singletonFamilyActivity_eqv_common coupling)
        (false, false, false) (true, true, true) pattern))
    (directedPatternEdge_activity_eqv
      (sevenCube111To011_singletonFamilyActivity_eqv_common coupling)
      (true, true, true) (false, true, true) pattern)

theorem sevenCubeCommonFourCycleProfile_eqv_zero
    (activity : Q') (pattern : ThreeBlockPattern) :
    sevenCubeFourCycleProfile activity activity activity activity pattern
      ≈ 0 := by
  obtain ⟨x, y, z⟩ := pattern
  cases x <;> cases y <;> cases z <;>
    simp [sevenCubeFourCycleProfile,
      outwardSignedDirectedPatternEdge, Q'.add_zero', Q'.zero_add']
  all_goals first
    | exact Q'.add_neg_self_eqv activity
    | exact Q'.neg_add_self_eqv activity
    | exact Q'.eqv_refl 0

/-- The four actual complete cutoff-one singleton weights cancel in every
outward Boolean cell, at every coupling, with no normalization assumption. -/
theorem sevenCubeActualFourCycleProfile_eqv_zero
    (coupling : Q') (pattern : ThreeBlockPattern) :
    sevenCubeActualFourCycleProfile coupling pattern ≈ 0 :=
  Q'.eqv_trans _ _ _
    (sevenCubeActualFourCycleProfile_eqv_common coupling pattern)
    (sevenCubeCommonFourCycleProfile_eqv_zero
      (sevenCubeCommonActivity coupling) pattern)

/-! ## A checked fence against an over-broad background class -/

def threeBlockPatternOr
    (left right : ThreeBlockPattern) : ThreeBlockPattern :=
  (left.1 || right.1,
    left.2.1 || right.2.1,
    left.2.2 || right.2.2)

/-- Equal unit carrier weights after independently OR-shifting every coarse
and fine endpoint by two background patterns.  The two endpoint shifts stay
explicit so the required guard cannot disappear by normalization. -/
def backgroundShiftedUnitFourCycleProfile
    (coarseBackground fineBackground pattern : ThreeBlockPattern) : Q' :=
  outwardSignedDirectedPatternEdge 1
      (threeBlockPatternOr coarseBackground (false, true, true))
      (threeBlockPatternOr fineBackground (true, false, false)) pattern +
    outwardSignedDirectedPatternEdge 1
      (threeBlockPatternOr coarseBackground (true, false, false))
      (threeBlockPatternOr fineBackground (false, false, false)) pattern +
    outwardSignedDirectedPatternEdge 1
      (threeBlockPatternOr coarseBackground (false, false, false))
      (threeBlockPatternOr fineBackground (true, true, true)) pattern +
    outwardSignedDirectedPatternEdge 1
      (threeBlockPatternOr coarseBackground (true, true, true))
      (threeBlockPatternOr fineBackground (false, true, true)) pattern

/-- Compatibility alone cannot justify switching: unequal coarse/fine
background patterns can destroy the telescoping cycle.  This is a closed
rational counterexample (`100` versus `000`, inspected at cell `100`). -/
theorem unequalBackgroundPatterns_break_fourCycle :
    ((true, false, false) : ThreeBlockPattern) ≠
        (false, false, false) ∧
      ¬ (backgroundShiftedUnitFourCycleProfile
          (true, false, false) (false, false, false)
          (true, false, false) ≈ 0) := by
  decide

#print axioms sevenCubeActualFourCycleProfile_eqv_common
#print axioms sevenCubeCommonFourCycleProfile_eqv_zero
#print axioms sevenCubeActualFourCycleProfile_eqv_zero
#print axioms unequalBackgroundPatterns_break_fourCycle

end YMGap.Continuum.Z4OutwardSevenCubeCycleCancellation
