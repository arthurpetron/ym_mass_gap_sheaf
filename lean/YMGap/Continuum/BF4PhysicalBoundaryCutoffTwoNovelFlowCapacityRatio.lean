/-
# The exact finite capacity ratio of the novel weighted flow

The novel simple-flow compiler previously left four pointwise capacity
inequalities as finite input data.  Those inequalities are always inhabited
at some positive cutoff-dependent strength: a positive grouped load can only
occur on an edge literally traversed by a positive-kernel path.

This module allocates half of old-old physical capacity to the novel flow and
full capacity on the other three blocks.  For each directed edge it divides
that allocated capacity by the exact grouped load when the load is positive,
and uses one otherwise.  A located finite minimum over the full sector is
therefore positive and satisfies every pointwise capacity inequality.

Consequently the four open local fields contract to one scalar question:
whether this explicit finite ratio is cofinally bounded below by the fixed
positive target strength.  No such uniform lower bound, thermodynamic or
continuum construction, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The allocated physical edge capacity -/

/-- Half capacity on the old-old block and full physical capacity elsewhere. -/
def cutoffTwoNovelAllocatedKernel
    (later source target : Nat) : Q' :=
  if _h :
      source ∈ cutoffTwoEdgeLoadOldStates later ∧
        target ∈ cutoffTwoEdgeLoadOldStates later then
    HalfPow.half * cutoffTwoEdgeLoadKernel later source target
  else
    cutoffTwoEdgeLoadKernel later source target

private theorem cutoffTwoKernel_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel
    BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteKernel
  exact
    BF4SU2FixedMagneticPhysicalMarkov.centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) later 0 _ _

theorem cutoffTwoNovelAllocatedKernel_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoNovelAllocatedKernel later source target := by
  unfold cutoffTwoNovelAllocatedKernel
  split
  · exact Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (cutoffTwoKernel_nonnegative later source target)
  · exact cutoffTwoKernel_nonnegative later source target

/-- Positive flow load forces positive allocated capacity, including the
half-capacity old-old case. -/
theorem cutoffTwoNovelAllocatedKernel_pos_of_load_pos
    (later source target : Nat)
    (hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target) :
    (0 : Q') < cutoffTwoNovelAllocatedKernel later source target := by
  have hkernel :=
    cutoffTwoNovelSimpleEdgeLoad_pos_implies_kernel_pos
      later source target hload
  unfold cutoffTwoNovelAllocatedKernel
  split
  · exact ExpNeg.half_mul_pos _ hkernel
  · exact hkernel

/-! ## 2. A located positive minimum of exact capacity/load ratios -/

/-- Exact allocated-capacity/load ratio, with the harmless positive value one
on edges carrying no positive load. -/
def cutoffTwoNovelEdgeCapacityRatio
    (later source target : Nat) : Q' :=
  if hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target then
    Q'.divPos
      (cutoffTwoNovelAllocatedKernel later source target)
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hload
  else
    1

theorem cutoffTwoNovelEdgeCapacityRatio_pos
    (later source target : Nat) :
    (0 : Q') < cutoffTwoNovelEdgeCapacityRatio later source target := by
  unfold cutoffTwoNovelEdgeCapacityRatio
  by_cases hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target
  · rw [dif_pos hload]
    exact Q'.divPos_pos _ _ hload
      (cutoffTwoNovelAllocatedKernel_pos_of_load_pos
        later source target hload)
  · rw [dif_neg hload]
    decide

def cutoffTwoNovelCapacityEdgePairs (later : Nat) : List (Nat × Nat) :=
  FiniteWeightedCartesianInjection.cartesian
    (cutoffTwoEdgeLoadFullStates later)
    (cutoffTwoEdgeLoadFullStates later)

/-- The best explicitly located finite lower capacity supplied by the chosen
novel simple flow. -/
def cutoffTwoNovelFiniteFlowCapacityFloor (later : Nat) : Q' :=
  listPositiveMinOne
    (fun pair =>
      cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
    (cutoffTwoNovelCapacityEdgePairs later)

theorem cutoffTwoNovelFiniteFlowCapacityFloor_pos (later : Nat) :
    (0 : Q') < cutoffTwoNovelFiniteFlowCapacityFloor later := by
  unfold cutoffTwoNovelFiniteFlowCapacityFloor
  apply listPositiveMinOne_pos
  intro pair _hpair
  exact cutoffTwoNovelEdgeCapacityRatio_pos
    later pair.1 pair.2

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- The finite minimum satisfies the allocated pointwise comparison on every
edge of the full vacuum sector. -/
theorem cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
    (later source target : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoNovelFiniteFlowCapacityFloor later *
        cutoffTwoNovelSimpleEdgeLoad later source target ≤
      cutoffTwoNovelAllocatedKernel later source target := by
  let load := cutoffTwoNovelSimpleEdgeLoad later source target
  have hloadNonnegative : (0 : Q') ≤ load :=
    cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target
  by_cases hload : (0 : Q') < load
  · have hpair : (source, target) ∈
        cutoffTwoNovelCapacityEdgePairs later := by
      unfold cutoffTwoNovelCapacityEdgePairs
      exact
        (FiniteWeightedCartesianInjection.mem_cartesian_iff
          (cutoffTwoEdgeLoadFullStates later)
          (cutoffTwoEdgeLoadFullStates later)
          (source, target)).mpr ⟨hsource, htarget⟩
    have hminimum := listPositiveMinOne_le_of_mem
      (fun pair : Nat × Nat =>
        cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
      (cutoffTwoNovelCapacityEdgePairs later)
      (source, target) hpair
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ load
      hminimum hloadNonnegative
    refine Q'.le_trans' _ _ _ hscaled ?_
    change cutoffTwoNovelEdgeCapacityRatio later source target * load ≤
      cutoffTwoNovelAllocatedKernel later source target
    unfold cutoffTwoNovelEdgeCapacityRatio
    change (if h : (0 : Q') < load then
        Q'.divPos
          (cutoffTwoNovelAllocatedKernel later source target)
          load h
      else 1) * load ≤
        cutoffTwoNovelAllocatedKernel later source target
    rw [dif_pos hload]
    exact Q'.le_of_eqv
      (Q'.divPos_mul_eqv
        (cutoffTwoNovelAllocatedKernel later source target)
        load hload)
  · have hloadNonpositive : load ≤ 0 :=
      q_nonpos_of_not_pos_local hload
    have hloadZero : load ≈ 0 :=
      Q'.eqv_of_le_le hloadNonpositive hloadNonnegative
    refine Q'.le_trans' _ 0 _ ?_
      (cutoffTwoNovelAllocatedKernel_nonnegative later source target)
    exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (cutoffTwoNovelFiniteFlowCapacityFloor later * 0) _
        (Q'.mul_eqv_congr_left
          (cutoffTwoNovelFiniteFlowCapacityFloor later)
          load 0 hloadZero)
        (Q'.mul_zero_eqv _))

/-! ## 3. One scalar lower bound inhabits all four capacity fields -/

private theorem cutoffTwoNewState_not_old
    {later state : Nat}
    (hnew : state ∈ cutoffTwoEdgeLoadNewStates later) :
    state ∉ cutoffTwoEdgeLoadOldStates later := by
  intro hold
  unfold cutoffTwoEdgeLoadOldStates at hold
  unfold cutoffTwoEdgeLoadNewStates at hnew
  have holdDecision := (List.mem_filter.mp hold).2
  have hnewDecision := (List.mem_filter.mp hnew).2
  simp only [holdDecision, Bool.not_true] at hnewDecision
  exact Bool.noConfusion hnewDecision

def cutoffTwoNovelSimpleFlowCapacityAt_of_finiteRatio
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hfixed :
      cutoffTwoNovelSimpleFlowCoercivityFloor ≤
        cutoffTwoNovelFiniteFlowCapacityFloor later) :
    CutoffTwoNovelSimpleFlowCapacityAt later where
  later_ge_pulled_floor := hlaterFloor
  later_ge_mass_floor := hlaterMass
  old_old := by
    intro source hsource target htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hfixed
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)
    have hallocated :
        cutoffTwoNovelAllocatedKernel later source target ≈
          HalfPow.half * cutoffTwoEdgeLoadKernel later source target := by
      unfold cutoffTwoNovelAllocatedKernel
      rw [dif_pos (And.intro hsource htarget)]
      exact Q'.eqv_refl _
    have hcapacity :=
      cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
        later source target
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hallocated)
  old_new := by
    intro source hsource target htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hfixed
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)
    have hnotOld : target ∉ cutoffTwoEdgeLoadOldStates later :=
      cutoffTwoNewState_not_old htarget
    have hnotPair : ¬
        (source ∈ cutoffTwoEdgeLoadOldStates later ∧
          target ∈ cutoffTwoEdgeLoadOldStates later) := by
      intro holdPair
      exact hnotOld holdPair.2
    have hallocated :
        cutoffTwoNovelAllocatedKernel later source target ≈
          cutoffTwoEdgeLoadKernel later source target := by
      unfold cutoffTwoNovelAllocatedKernel
      rw [dif_neg hnotPair]
      exact Q'.eqv_refl _
    have hcapacity :=
      cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
        later source target
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hallocated)
  new_old := by
    intro source hsource target htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hfixed
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)
    have hnotOld : source ∉ cutoffTwoEdgeLoadOldStates later :=
      cutoffTwoNewState_not_old hsource
    have hnotPair : ¬
        (source ∈ cutoffTwoEdgeLoadOldStates later ∧
          target ∈ cutoffTwoEdgeLoadOldStates later) := by
      intro holdPair
      exact hnotOld holdPair.1
    have hallocated :
        cutoffTwoNovelAllocatedKernel later source target ≈
          cutoffTwoEdgeLoadKernel later source target := by
      unfold cutoffTwoNovelAllocatedKernel
      rw [dif_neg hnotPair]
      exact Q'.eqv_refl _
    have hcapacity :=
      cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
        later source target
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hallocated)
  new_new := by
    intro source hsource target htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      hfixed
      (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)
    have hnotOld : source ∉ cutoffTwoEdgeLoadOldStates later :=
      cutoffTwoNewState_not_old hsource
    have hnotPair : ¬
        (source ∈ cutoffTwoEdgeLoadOldStates later ∧
          target ∈ cutoffTwoEdgeLoadOldStates later) := by
      intro holdPair
      exact hnotOld holdPair.1
    have hallocated :
        cutoffTwoNovelAllocatedKernel later source target ≈
          cutoffTwoEdgeLoadKernel later source target := by
      unfold cutoffTwoNovelAllocatedKernel
      rw [dif_neg hnotPair]
      exact Q'.eqv_refl _
    have hcapacity :=
      cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
        later source target
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hallocated)

/-! ## 4. Cofinal scalar ratio closure -/

/-- The entire finite weighted-flow frontier is now the cofinal lower bound
for one explicit rational sequence. -/
structure CutoffTwoCofinalNovelFlowCapacityRatio : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  fixed_floor_le : ∀ request,
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor (anchor request)

namespace CutoffTwoCofinalNovelFlowCapacityRatio

def toCofinalNovelSimpleFlowCapacity
    (ratio : CutoffTwoCofinalNovelFlowCapacityRatio) :
    CutoffTwoCofinalNovelSimpleFlowCapacity where
  anchor := ratio.anchor
  anchor_ge := ratio.anchor_ge
  capacity := by
    intro request
    have hanchor := ratio.anchor_ge request
    exact cutoffTwoNovelSimpleFlowCapacityAt_of_finiteRatio
      (ratio.anchor request)
      (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hanchor))
      (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hanchor))
      (ratio.fixed_floor_le request)

def toCompletedStrictContractionData
    (ratio : CutoffTwoCofinalNovelFlowCapacityRatio) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  ratio.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelFlowCapacityRatio

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.cutoffTwoNovelAllocatedKernel_pos_of_load_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.cutoffTwoNovelFiniteFlowCapacityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.cutoffTwoNovelSimpleFlowCapacityAt_of_finiteRatio
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.CutoffTwoCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData
