/-
# Guarded switching of the seven-cube cycle over a neutral background

The empty-background cycle does not extend to arbitrary compatible families:
coarse and fine query bits contributed by the background independently OR
into the four endpoints.  This file therefore makes the exact guard part of
the data.  A good background is a compatible family whose four carrier
insertions remain compatible and whose coarse and fine query patterns are
both `000`.

For such a background, every inserted weight is the corresponding exact
carrier weight times one common background factor.  The resulting directed
cycle cancels separately at two completely independent couplings; no hidden
fine/block normalization equality is used.
-/

import YMGap.Continuum.Z4OutwardSevenCubeCycleCancellation

namespace YMGap.Continuum.Z4OutwardSevenCubeGoodBackgroundSwitching

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4OutwardCentralSmallLiftSignedPath
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardSevenCubeCycleActivity
open YMGap.Continuum.Z4OutwardSevenCubeCycleCancellation
open YMGap.Continuum.Z4OutwardSevenCubeCycleConnectedRoots
open YMGap.Continuum.Z4OutwardSevenCubeSignedCycle
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact good-background guard and its non-vacuity -/

structure SevenCubeGoodBackground where
  family : List (List Nat)
  compatible : family ∈ canonicalCompatibleAmbientFamilies 6
  insert011To100_compatible :
    sevenCube011To100Root :: family ∈
      canonicalCompatibleAmbientFamilies 6
  insert100To000_compatible :
    sevenCube100To000Root :: family ∈
      canonicalCompatibleAmbientFamilies 6
  insert000To111_compatible :
    sevenCube000To111Root :: family ∈
      canonicalCompatibleAmbientFamilies 6
  insert111To011_compatible :
    sevenCube111To011Root :: family ∈
      canonicalCompatibleAmbientFamilies 6
  coarse_neutral :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries family =
      (false, false, false)
  fine_neutral :
    outwardComponentSubsupportFamilyPattern outwardFineQueries family =
      (false, false, false)

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | _ :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type} :
    ∀ (ambient : List A) (item : A), item ∈ ambient →
      [item] ∈ sublists ambient
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rw [sublists_cons']
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _
          (singleton_mem_sublists_of_mem_local tail item htail)

private theorem empty_mem_compatible :
    [] ∈ canonicalCompatibleAmbientFamilies 6 := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨nil_mem_sublists_local _, rfl⟩

private theorem singleton_mem_compatible
    {root : List Nat} (hroot : root ∈ canonicalSurfacePolymers 6) :
    [root] ∈ canonicalCompatibleAmbientFamilies 6 := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers 6) root hroot, rfl⟩

theorem outwardFamilyPattern_nil
    (queries : ComponentSubsupportQueryTriple) :
    outwardComponentSubsupportFamilyPattern queries [] =
      (false, false, false) := by
  unfold outwardComponentSubsupportFamilyPattern
    familyContainsComponentSubsupportB
  rfl

/-- The guard is genuinely inhabited; the empty background is its canonical
base point. -/
def sevenCubeEmptyGoodBackground : SevenCubeGoodBackground where
  family := []
  compatible := empty_mem_compatible
  insert011To100_compatible :=
    singleton_mem_compatible sevenCube011To100Root_mem_canonical
  insert100To000_compatible :=
    singleton_mem_compatible sevenCube100To000Root_mem_canonical
  insert000To111_compatible :=
    singleton_mem_compatible sevenCube000To111Root_mem_canonical
  insert111To011_compatible :=
    singleton_mem_compatible sevenCube111To011Root_mem_canonical
  coarse_neutral := outwardFamilyPattern_nil outwardCoarseQueries
  fine_neutral := outwardFamilyPattern_nil outwardFineQueries

/-! ## 2. Neutral backgrounds preserve all four literal endpoints -/

theorem outwardFamilyPattern_cons_eq_or
    (queries : ComponentSubsupportQueryTriple)
    (root : List Nat) (background : List (List Nat)) :
    outwardComponentSubsupportFamilyPattern queries (root :: background) =
      threeBlockPatternOr
        (outwardComponentSubsupportFamilyPattern queries [root])
        (outwardComponentSubsupportFamilyPattern queries background) := by
  unfold outwardComponentSubsupportFamilyPattern threeBlockPatternOr
    familyContainsComponentSubsupportB
  simp only [List.any_cons, List.any_nil, Bool.or_false]

theorem outwardFamilyPattern_cons_of_background_neutral
    (queries : ComponentSubsupportQueryTriple)
    (root : List Nat) (background : List (List Nat))
    (hneutral :
      outwardComponentSubsupportFamilyPattern queries background =
        (false, false, false)) :
    outwardComponentSubsupportFamilyPattern queries (root :: background) =
      outwardComponentSubsupportFamilyPattern queries [root] := by
  rw [outwardFamilyPattern_cons_eq_or, hneutral]
  unfold threeBlockPatternOr
  simp only [Bool.or_false]

theorem goodBackground_insert011To100_patterns
    (good : SevenCubeGoodBackground) :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        (sevenCube011To100Root :: good.family) =
        (false, true, true) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        (sevenCube011To100Root :: good.family) =
        (true, false, false) := by
  constructor
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardCoarseQueries sevenCube011To100Root good.family
      good.coarse_neutral).trans
        sevenCube011To100_coarseFamilyPattern_011
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardFineQueries sevenCube011To100Root good.family
      good.fine_neutral).trans
        sevenCube011To100_fineFamilyPattern_100

theorem goodBackground_insert100To000_patterns
    (good : SevenCubeGoodBackground) :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        (sevenCube100To000Root :: good.family) =
        (true, false, false) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        (sevenCube100To000Root :: good.family) =
        (false, false, false) := by
  constructor
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardCoarseQueries sevenCube100To000Root good.family
      good.coarse_neutral).trans
        sevenCube100To000_coarseFamilyPattern_100
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardFineQueries sevenCube100To000Root good.family
      good.fine_neutral).trans
        sevenCube100To000_fineFamilyPattern_000

theorem goodBackground_insert000To111_patterns
    (good : SevenCubeGoodBackground) :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        (sevenCube000To111Root :: good.family) =
        (false, false, false) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        (sevenCube000To111Root :: good.family) =
        (true, true, true) := by
  constructor
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardCoarseQueries sevenCube000To111Root good.family
      good.coarse_neutral).trans
        sevenCube000To111_coarseFamilyPattern_000
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardFineQueries sevenCube000To111Root good.family
      good.fine_neutral).trans
        sevenCube000To111_fineFamilyPattern_111

theorem goodBackground_insert111To011_patterns
    (good : SevenCubeGoodBackground) :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        (sevenCube111To011Root :: good.family) =
        (true, true, true) ∧
      outwardComponentSubsupportFamilyPattern outwardFineQueries
        (sevenCube111To011Root :: good.family) =
        (false, true, true) := by
  constructor
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardCoarseQueries sevenCube111To011Root good.family
      good.coarse_neutral).trans
        sevenCube111To011_coarseFamilyPattern_111
  · exact (outwardFamilyPattern_cons_of_background_neutral
      outwardFineQueries sevenCube111To011Root good.family
      good.fine_neutral).trans
        sevenCube111To011_fineFamilyPattern_011

/-! ## 3. Exact common-background activity factor -/

def sevenCubeBackgroundActivity
    (coupling : Q') (background : List (List Nat)) : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6 background

def sevenCubeInsertedActivity
    (coupling : Q') (root : List Nat)
    (background : List (List Nat)) : Q' :=
  couplingParametricKSupportFamilyActivity coupling 1 6
    (root :: background)

theorem sevenCubeInsertedActivity_eqv_singleton_mul_background
    (coupling : Q') (root : List Nat)
    (background : List (List Nat)) :
    sevenCubeInsertedActivity coupling root background ≈
      couplingParametricKSupportFamilyActivity coupling 1 6 [root] *
        sevenCubeBackgroundActivity coupling background := by
  unfold sevenCubeInsertedActivity sevenCubeBackgroundActivity
  change
    couplingParametricKSupportActivity coupling 1 6 root *
        couplingParametricKSupportFamilyActivity coupling 1 6 background ≈
      (couplingParametricKSupportActivity coupling 1 6 root * 1) *
        couplingParametricKSupportFamilyActivity coupling 1 6 background
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (Q'.mul_one_eqv
        (couplingParametricKSupportActivity coupling 1 6 root)))

theorem sevenCubeInserted011To100Activity_eqv_commonFactor
    (coupling : Q') (background : List (List Nat)) :
    sevenCubeInsertedActivity coupling sevenCube011To100Root background ≈
      sevenCubeCommonActivity coupling *
        sevenCubeBackgroundActivity coupling background := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube011To100Root] *
      sevenCubeBackgroundActivity coupling background) _
    (sevenCubeInsertedActivity_eqv_singleton_mul_background
      coupling sevenCube011To100Root background) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (sevenCube011To100_singletonFamilyActivity_eqv_common coupling)

theorem sevenCubeInserted100To000Activity_eqv_commonFactor
    (coupling : Q') (background : List (List Nat)) :
    sevenCubeInsertedActivity coupling sevenCube100To000Root background ≈
      sevenCubeCommonActivity coupling *
        sevenCubeBackgroundActivity coupling background := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube100To000Root] *
      sevenCubeBackgroundActivity coupling background) _
    (sevenCubeInsertedActivity_eqv_singleton_mul_background
      coupling sevenCube100To000Root background) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (sevenCube100To000_singletonFamilyActivity_eqv_common coupling)

theorem sevenCubeInserted000To111Activity_eqv_commonFactor
    (coupling : Q') (background : List (List Nat)) :
    sevenCubeInsertedActivity coupling sevenCube000To111Root background ≈
      sevenCubeCommonActivity coupling *
        sevenCubeBackgroundActivity coupling background := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube000To111Root] *
      sevenCubeBackgroundActivity coupling background) _
    (sevenCubeInsertedActivity_eqv_singleton_mul_background
      coupling sevenCube000To111Root background) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (sevenCube000To111_singletonFamilyActivity_eqv_common coupling)

theorem sevenCubeInserted111To011Activity_eqv_commonFactor
    (coupling : Q') (background : List (List Nat)) :
    sevenCubeInsertedActivity coupling sevenCube111To011Root background ≈
      sevenCubeCommonActivity coupling *
        sevenCubeBackgroundActivity coupling background := by
  refine Q'.eqv_trans _
    (couplingParametricKSupportFamilyActivity coupling 1 6
        [sevenCube111To011Root] *
      sevenCubeBackgroundActivity coupling background) _
    (sevenCubeInsertedActivity_eqv_singleton_mul_background
      coupling sevenCube111To011Root background) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (sevenCube111To011_singletonFamilyActivity_eqv_common coupling)

/-! ## 4. Pointwise switching, with fine/block couplings kept distinct -/

def sevenCubeBackgroundInsertedFourCycleProfile
    (coupling : Q') (background : List (List Nat))
    (pattern : ThreeBlockPattern) : Q' :=
  sevenCubeFourCycleProfile
    (sevenCubeInsertedActivity coupling sevenCube011To100Root background)
    (sevenCubeInsertedActivity coupling sevenCube100To000Root background)
    (sevenCubeInsertedActivity coupling sevenCube000To111Root background)
    (sevenCubeInsertedActivity coupling sevenCube111To011Root background)
    pattern

private theorem directedPatternEdge_activity_eqv_local
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

private theorem sevenCubeFourCycleProfile_eqv_of_activities
    {left0 left1 left2 left3 right0 right1 right2 right3 : Q'}
    (h0 : left0 ≈ right0) (h1 : left1 ≈ right1)
    (h2 : left2 ≈ right2) (h3 : left3 ≈ right3)
    (pattern : ThreeBlockPattern) :
    sevenCubeFourCycleProfile left0 left1 left2 left3 pattern ≈
      sevenCubeFourCycleProfile right0 right1 right2 right3 pattern := by
  unfold sevenCubeFourCycleProfile
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (directedPatternEdge_activity_eqv_local h0
          (false, true, true) (true, false, false) pattern)
        (directedPatternEdge_activity_eqv_local h1
          (true, false, false) (false, false, false) pattern))
      (directedPatternEdge_activity_eqv_local h2
        (false, false, false) (true, true, true) pattern))
    (directedPatternEdge_activity_eqv_local h3
      (true, true, true) (false, true, true) pattern)

theorem sevenCubeBackgroundInsertedProfile_eqv_commonFactor
    (coupling : Q') (background : List (List Nat))
    (pattern : ThreeBlockPattern) :
    sevenCubeBackgroundInsertedFourCycleProfile
        coupling background pattern ≈
      sevenCubeFourCycleProfile
        (sevenCubeCommonActivity coupling *
          sevenCubeBackgroundActivity coupling background)
        (sevenCubeCommonActivity coupling *
          sevenCubeBackgroundActivity coupling background)
        (sevenCubeCommonActivity coupling *
          sevenCubeBackgroundActivity coupling background)
        (sevenCubeCommonActivity coupling *
          sevenCubeBackgroundActivity coupling background)
        pattern := by
  unfold sevenCubeBackgroundInsertedFourCycleProfile
  exact sevenCubeFourCycleProfile_eqv_of_activities
    (sevenCubeInserted011To100Activity_eqv_commonFactor
      coupling background)
    (sevenCubeInserted100To000Activity_eqv_commonFactor
      coupling background)
    (sevenCubeInserted000To111Activity_eqv_commonFactor
      coupling background)
    (sevenCubeInserted111To011Activity_eqv_commonFactor
      coupling background) pattern

theorem sevenCubeBackgroundInsertedProfile_eqv_zero
    (coupling : Q') (background : List (List Nat))
    (pattern : ThreeBlockPattern) :
    sevenCubeBackgroundInsertedFourCycleProfile
        coupling background pattern ≈ 0 :=
  Q'.eqv_trans _ _ _
    (sevenCubeBackgroundInsertedProfile_eqv_commonFactor
      coupling background pattern)
    (sevenCubeCommonFourCycleProfile_eqv_zero
      (sevenCubeCommonActivity coupling *
        sevenCubeBackgroundActivity coupling background) pattern)

/-- The common factor is formed independently at the fine and block
couplings.  In particular, this statement assumes no equality between those
couplings or between the two background activities. -/
theorem goodBackground_fine_block_commonFactors
    (fineCoupling blockCoupling : Q')
    (good : SevenCubeGoodBackground) (pattern : ThreeBlockPattern) :
    (sevenCubeBackgroundInsertedFourCycleProfile
        fineCoupling good.family pattern ≈
      sevenCubeFourCycleProfile
        (sevenCubeCommonActivity fineCoupling *
          sevenCubeBackgroundActivity fineCoupling good.family)
        (sevenCubeCommonActivity fineCoupling *
          sevenCubeBackgroundActivity fineCoupling good.family)
        (sevenCubeCommonActivity fineCoupling *
          sevenCubeBackgroundActivity fineCoupling good.family)
        (sevenCubeCommonActivity fineCoupling *
          sevenCubeBackgroundActivity fineCoupling good.family)
        pattern) ∧
    (sevenCubeBackgroundInsertedFourCycleProfile
        blockCoupling good.family pattern ≈
      sevenCubeFourCycleProfile
        (sevenCubeCommonActivity blockCoupling *
          sevenCubeBackgroundActivity blockCoupling good.family)
        (sevenCubeCommonActivity blockCoupling *
          sevenCubeBackgroundActivity blockCoupling good.family)
        (sevenCubeCommonActivity blockCoupling *
          sevenCubeBackgroundActivity blockCoupling good.family)
        (sevenCubeCommonActivity blockCoupling *
          sevenCubeBackgroundActivity blockCoupling good.family)
        pattern) :=
  ⟨sevenCubeBackgroundInsertedProfile_eqv_commonFactor
      fineCoupling good.family pattern,
    sevenCubeBackgroundInsertedProfile_eqv_commonFactor
      blockCoupling good.family pattern⟩

theorem goodBackground_fine_block_cancellation
    (fineCoupling blockCoupling : Q')
    (good : SevenCubeGoodBackground) (pattern : ThreeBlockPattern) :
    sevenCubeBackgroundInsertedFourCycleProfile
        fineCoupling good.family pattern ≈ 0 ∧
      sevenCubeBackgroundInsertedFourCycleProfile
        blockCoupling good.family pattern ≈ 0 :=
  ⟨sevenCubeBackgroundInsertedProfile_eqv_zero
      fineCoupling good.family pattern,
    sevenCubeBackgroundInsertedProfile_eqv_zero
      blockCoupling good.family pattern⟩

#print axioms outwardFamilyPattern_cons_eq_or
#print axioms sevenCubeEmptyGoodBackground
#print axioms goodBackground_insert011To100_patterns
#print axioms goodBackground_insert100To000_patterns
#print axioms goodBackground_insert000To111_patterns
#print axioms goodBackground_insert111To011_patterns
#print axioms sevenCubeInsertedActivity_eqv_singleton_mul_background
#print axioms sevenCubeInserted011To100Activity_eqv_commonFactor
#print axioms sevenCubeBackgroundInsertedProfile_eqv_commonFactor
#print axioms sevenCubeBackgroundInsertedProfile_eqv_zero
#print axioms goodBackground_fine_block_commonFactors
#print axioms goodBackground_fine_block_cancellation

end YMGap.Continuum.Z4OutwardSevenCubeGoodBackgroundSwitching
