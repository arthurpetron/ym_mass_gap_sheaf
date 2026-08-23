/-
# Capacity-scaled cutoff-two edge-load gluing

The exact canonical cross-path load need not fit into unit bridge capacity at
one finite cutoff.  This module removes that unjustified normalization.  It
uses separate coefficient-independent capacities on internal and bridge
edges, constructs such capacities from finite located maxima, and proves the
cleared estimate

  baseFloor * fullVariance <= totalCost * fullDirichlet.

A proposed uniform effective floor is then needed only through the explicit
ratio inequality

  effectiveFloor * totalCost <= baseFloor.

Positive cancellation compiles that inequality to the existing completed
strict-contraction interface.  The finite maxima are inhabited here; no
uniform ratio bound, mass floor, thermodynamic/continuum limit, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Separate internal and bridge capacities -/

/-- Coefficient-independent upper capacities on the four physical edge
blocks.  No capacity is normalized to one. -/
structure CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
    (later : Nat) (internalCapacity bridgeCapacity : Q') : Type 1 where
  old_old : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ internalCapacity
  new_new : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ internalCapacity
  old_new : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ bridgeCapacity
  new_old : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoCanonicalCrossEdgeLoad later source target ≤ bridgeCapacity

namespace CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt

private theorem kernel_nonnegative (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_nonnegative
    (by decide) later 0 _ _

theorem loaded_oldOld_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient ≤
      internalCapacity * cutoffTwoOldOldDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedOldOldDirichlet
    cutoffTwoOldOldDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.old_old

theorem loaded_newNew_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient ≤
      internalCapacity * cutoffTwoNewNewDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedNewNewDirichlet
    cutoffTwoNewNewDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.new_new

theorem loaded_oldNew_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient ≤
      bridgeCapacity * cutoffTwoOldNewDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedOldNewDirichlet
    cutoffTwoOldNewDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.old_new

theorem loaded_newOld_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient ≤
      bridgeCapacity * cutoffTwoNewOldDirichlet later coefficient := by
  unfold cutoffTwoCanonicalCrossLoadedNewOldDirichlet
    cutoffTwoNewOldDirichlet
  exact finiteLoadedDirichletBlock_le_scale_mul _ _ coefficient _ _ _
    (kernel_nonnegative later) bounds.new_old

theorem loadedWithin_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient ≤
      internalCapacity * cutoffTwoWithinBlockDirichlet later coefficient := by
  have h := Q'.add_le_add
    (loaded_oldOld_le bounds coefficient)
    (loaded_newNew_le bounds coefficient)
  refine Q'.le_trans' _
    (internalCapacity * cutoffTwoOldOldDirichlet later coefficient +
      internalCapacity * cutoffTwoNewNewDirichlet later coefficient) _ h ?_
  unfold cutoffTwoWithinBlockDirichlet
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_add_eqv internalCapacity _ _))

theorem loadedCross_le
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient ≤
      bridgeCapacity * cutoffTwoCrossBlockDirichlet later coefficient := by
  have h := Q'.add_le_add
    (loaded_oldNew_le bounds coefficient)
    (loaded_newOld_le bounds coefficient)
  refine Q'.le_trans' _
    (bridgeCapacity * cutoffTwoOldNewDirichlet later coefficient +
      bridgeCapacity * cutoffTwoNewOldDirichlet later coefficient) _ h ?_
  unfold cutoffTwoCrossBlockDirichlet
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_add_eqv bridgeCapacity _ _))

/-- Separate pointwise capacities bound the aggregate canonical path budget
without imposing a unit-capacity normalization. -/
theorem lengthLinearPathBudget_le_capacityEnergy
    {later : Nat} {internalCapacity bridgeCapacity : Q'}
    (bounds : CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    cutoffTwoCanonicalCrossLengthLinearPathBudget later coefficient ≤
      internalCapacity * cutoffTwoWithinBlockDirichlet later coefficient +
        bridgeCapacity * cutoffTwoCrossBlockDirichlet later coefficient := by
  refine Q'.le_trans' _
    (cutoffTwoCanonicalCrossLoadedDirichlet later coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (cutoffTwoCanonicalCrossLengthLinearPathBudget_eqv_loadedDirichlet
        later coefficient)
  refine Q'.le_trans' _
    ((cutoffTwoCanonicalCrossLoadedOldOldDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewNewDirichlet later coefficient) +
      (cutoffTwoCanonicalCrossLoadedOldNewDirichlet later coefficient +
        cutoffTwoCanonicalCrossLoadedNewOldDirichlet later coefficient)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (cutoffTwoCanonicalCrossLoadedDirichlet_eqv_within_add_cross
        later coefficient)
  exact Q'.add_le_add
    (loadedWithin_le bounds coefficient)
    (loadedCross_le bounds coefficient)

end CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt

/-! ## 2. Every finite cutoff has explicit located capacities -/

def cutoffTwoCanonicalInternalEdgePairs (later : Nat) : List (Nat × Nat) :=
  cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadOldStates later) ++
    cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadNewStates later)

def cutoffTwoCanonicalBridgeEdgePairs (later : Nat) : List (Nat × Nat) :=
  cartesian
      (cutoffTwoEdgeLoadOldStates later)
      (cutoffTwoEdgeLoadNewStates later) ++
    cartesian
      (cutoffTwoEdgeLoadNewStates later)
      (cutoffTwoEdgeLoadOldStates later)

def cutoffTwoCanonicalInternalEdgeLoadCapacity (later : Nat) : Q' :=
  1 + listQMaxZero
    (fun pair =>
      cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
    (cutoffTwoCanonicalInternalEdgePairs later)

def cutoffTwoCanonicalBridgeEdgeLoadCapacity (later : Nat) : Q' :=
  1 + listQMaxZero
    (fun pair =>
      cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
    (cutoffTwoCanonicalBridgeEdgePairs later)

private theorem listQMaxZero_seed_nonnegative
    {State : Type} (value : State → Q') :
    ∀ states : List State, (0 : Q') ≤ listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_seed_nonnegative value tail)
        (Q'.le_max'_right _ _)

theorem cutoffTwoCanonicalInternalEdgeLoadCapacity_pos (later : Nat) :
    (0 : Q') < cutoffTwoCanonicalInternalEdgeLoadCapacity later := by
  unfold cutoffTwoCanonicalInternalEdgeLoadCapacity
  exact Q'.pos_add_nonneg (by decide)
    (listQMaxZero_seed_nonnegative _ _)

theorem cutoffTwoCanonicalBridgeEdgeLoadCapacity_pos (later : Nat) :
    (0 : Q') < cutoffTwoCanonicalBridgeEdgeLoadCapacity later := by
  unfold cutoffTwoCanonicalBridgeEdgeLoadCapacity
  exact Q'.pos_add_nonneg (by decide)
    (listQMaxZero_seed_nonnegative _ _)

private theorem edgeLoad_le_one_add_max_of_mem
    (later : Nat) (pairs : List (Nat × Nat))
    (source target : Nat) (hpair : (source, target) ∈ pairs) :
    cutoffTwoCanonicalCrossEdgeLoad later source target ≤
      1 + listQMaxZero
        (fun pair =>
          cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
        pairs := by
  have hmax := le_listQMaxZero_of_mem
    (fun pair : Nat × Nat =>
      cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
    pairs hpair
  have hmaxLe : listQMaxZero
      (fun pair : Nat × Nat =>
        cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
      pairs ≤
      1 + listQMaxZero
        (fun pair : Nat × Nat =>
          cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
        pairs := by
    have hadd := Q'.add_le_add_right
      (0 : Q') 1
      (listQMaxZero
        (fun pair : Nat × Nat =>
          cutoffTwoCanonicalCrossEdgeLoad later pair.1 pair.2)
        pairs)
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hmax hmaxLe

/-- The two located maxima inhabit the four capacity inequalities at every
finite later cutoff. -/
def cutoffTwoCanonicalFiniteEdgeLoadCapacitiesAt (later : Nat) :
    CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt later
      (cutoffTwoCanonicalInternalEdgeLoadCapacity later)
      (cutoffTwoCanonicalBridgeEdgeLoadCapacity later) where
  old_old := by
    intro source hsource target htarget
    unfold cutoffTwoCanonicalInternalEdgeLoadCapacity
    apply edgeLoad_le_one_add_max_of_mem
    unfold cutoffTwoCanonicalInternalEdgePairs
    exact List.mem_append.mpr
      (Or.inl ((mem_cartesian_iff _ _ _).mpr ⟨hsource, htarget⟩))
  new_new := by
    intro source hsource target htarget
    unfold cutoffTwoCanonicalInternalEdgeLoadCapacity
    apply edgeLoad_le_one_add_max_of_mem
    unfold cutoffTwoCanonicalInternalEdgePairs
    exact List.mem_append.mpr
      (Or.inr ((mem_cartesian_iff _ _ _).mpr ⟨hsource, htarget⟩))
  old_new := by
    intro source hsource target htarget
    unfold cutoffTwoCanonicalBridgeEdgeLoadCapacity
    apply edgeLoad_le_one_add_max_of_mem
    unfold cutoffTwoCanonicalBridgeEdgePairs
    exact List.mem_append.mpr
      (Or.inl ((mem_cartesian_iff _ _ _).mpr ⟨hsource, htarget⟩))
  new_old := by
    intro source hsource target htarget
    unfold cutoffTwoCanonicalBridgeEdgeLoadCapacity
    apply edgeLoad_le_one_add_max_of_mem
    unfold cutoffTwoCanonicalBridgeEdgePairs
    exact List.mem_append.mpr
      (Or.inr ((mem_cartesian_iff _ _ _).mpr ⟨hsource, htarget⟩))

/-! ## 3. Clear the capacity denominator -/

def cutoffTwoCapacityTotalCost
    (withinCost internalCapacity bridgeCapacity : Q') : Q' :=
  (withinCost + internalCapacity) + bridgeCapacity

/-- Finite path gluing with explicit, unnormalized congestion costs. -/
structure CutoffTwoCapacityScaledPathGluingAt
    (later : Nat)
    (baseFloor massFloor withinCost internalCapacity bridgeCapacity : Q') :
    Type 1 where
  later_ge : 2 ≤ later
  base_floor_nonnegative : (0 : Q') ≤ baseFloor
  within_cost_nonnegative : (0 : Q') ≤ withinCost
  internal_capacity_nonnegative : (0 : Q') ≤ internalCapacity
  bridge_capacity_nonnegative : (0 : Q') ≤ bridgeCapacity
  total_cost_pos : (0 : Q') <
    cutoffTwoCapacityTotalCost
      withinCost internalCapacity bridgeCapacity
  base_floor_le_edgeFloor :
    baseFloor ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  within_budget : ∀ coefficient,
    baseFloor * cutoffTwoWithinBlockPairwiseVariance later coefficient ≤
      withinCost * cutoffTwoWithinBlockDirichlet later coefficient
  edge_load_capacities :
    CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt
      later internalCapacity bridgeCapacity

namespace CutoffTwoCapacityScaledPathGluingAt

theorem cross_budget
    {later : Nat}
    {baseFloor massFloor withinCost internalCapacity bridgeCapacity : Q'}
    (certificate : CutoffTwoCapacityScaledPathGluingAt later
      baseFloor massFloor withinCost internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    baseFloor * cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      internalCapacity * cutoffTwoWithinBlockDirichlet later coefficient +
        bridgeCapacity * cutoffTwoCrossBlockDirichlet later coefficient := by
  have hfloorScaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    certificate.base_floor_le_edgeFloor
    (cutoffTwoCrossBlockPairwiseVariance_nonnegative later coefficient)
  exact Q'.le_trans' _ _ _ hfloorScaled
    (Q'.le_trans' _ _ _
      (cutoffTwo_edgeFloor_mul_crossVariance_le_lengthLinearPathBudget
        later coefficient)
      (certificate.edge_load_capacities
        |>.lengthLinearPathBudget_le_capacityEnergy coefficient))

private theorem capacityEnergy_le_totalEnergy
    (withinCost internalCapacity bridgeCapacity
      withinEnergy crossEnergy : Q')
    (hwithinCost : (0 : Q') ≤ withinCost)
    (hinternal : (0 : Q') ≤ internalCapacity)
    (hbridge : (0 : Q') ≤ bridgeCapacity)
    (hwithinEnergy : (0 : Q') ≤ withinEnergy)
    (hcrossEnergy : (0 : Q') ≤ crossEnergy) :
    withinCost * withinEnergy +
        (internalCapacity * withinEnergy + bridgeCapacity * crossEnergy) ≤
      cutoffTwoCapacityTotalCost
          withinCost internalCapacity bridgeCapacity *
        (withinEnergy + crossEnergy) := by
  let internalTotal := withinCost + internalCapacity
  let total := cutoffTwoCapacityTotalCost
    withinCost internalCapacity bridgeCapacity
  have hinternalTotal : (0 : Q') ≤ internalTotal :=
    Q'.zero_le_add _ _ hwithinCost hinternal
  have hinternalLe : internalTotal ≤ total := by
    unfold total cutoffTwoCapacityTotalCost
    exact Q'.add_le_self_of_nonneg _ _ hbridge
  have hbridgeLe : bridgeCapacity ≤ total := by
    have hfirst := Q'.add_le_self_of_nonneg
      bridgeCapacity internalTotal hinternalTotal
    refine Q'.le_trans' _ (bridgeCapacity + internalTotal) _ hfirst ?_
    unfold total cutoffTwoCapacityTotalCost internalTotal
    exact Q'.le_of_eqv (Q'.add_comm_eqv _ _)
  have hwithinScaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    hinternalLe hwithinEnergy
  have hcrossScaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    hbridgeLe hcrossEnergy
  refine Q'.le_trans' _
    (internalTotal * withinEnergy + bridgeCapacity * crossEnergy) _ ?_ ?_
  · exact Q'.le_of_eqv (by
      unfold internalTotal
      q_ring)
  refine Q'.le_trans' _
    (total * withinEnergy + total * crossEnergy) _
    (Q'.add_le_add hwithinScaled hcrossScaled) ?_
  unfold total
  exact Q'.ge_of_eqv
    (Q'.mul_add_eqv
      (cutoffTwoCapacityTotalCost
        withinCost internalCapacity bridgeCapacity)
      withinEnergy crossEnergy)

/-- Explicit finite capacities and a within-block cost imply the cleared
full-sector coercivity inequality. -/
theorem cleared_full_coercivity
    {later : Nat}
    {baseFloor massFloor withinCost internalCapacity bridgeCapacity : Q'}
    (certificate : CutoffTwoCapacityScaledPathGluingAt later
      baseFloor massFloor withinCost internalCapacity bridgeCapacity)
    (coefficient : Nat → Q') :
    baseFloor * cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoCapacityTotalCost
          withinCost internalCapacity bridgeCapacity *
        cutoffTwoFullSectorDirichlet later coefficient := by
  have hbudgets := Q'.add_le_add
    (certificate.within_budget coefficient)
    (certificate.cross_budget coefficient)
  refine Q'.le_trans' _
    (baseFloor * cutoffTwoWithinBlockPairwiseVariance later coefficient +
      baseFloor * cutoffTwoCrossBlockPairwiseVariance later coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (baseFloor *
          (cutoffTwoWithinBlockPairwiseVariance later coefficient +
            cutoffTwoCrossBlockPairwiseVariance later coefficient)) _
        (Q'.mul_eqv_congr_left baseFloor _ _
          (cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
            later coefficient))
        (Q'.mul_add_eqv baseFloor _ _))
  refine Q'.le_trans' _
    (withinCost * cutoffTwoWithinBlockDirichlet later coefficient +
      (internalCapacity * cutoffTwoWithinBlockDirichlet later coefficient +
        bridgeCapacity * cutoffTwoCrossBlockDirichlet later coefficient)) _
    hbudgets ?_
  refine Q'.le_trans' _
    (cutoffTwoCapacityTotalCost
        withinCost internalCapacity bridgeCapacity *
      (cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient)) _ ?_ ?_
  · exact capacityEnergy_le_totalEnergy
      withinCost internalCapacity bridgeCapacity
      (cutoffTwoWithinBlockDirichlet later coefficient)
      (cutoffTwoCrossBlockDirichlet later coefficient)
      certificate.within_cost_nonnegative
      certificate.internal_capacity_nonnegative
      certificate.bridge_capacity_nonnegative
      (cutoffTwoWithinBlockDirichlet_nonnegative later coefficient)
      (cutoffTwoCrossBlockDirichlet_nonnegative later coefficient)
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left
      (cutoffTwoCapacityTotalCost
        withinCost internalCapacity bridgeCapacity) _ _
      (Q'.eqv_symm
        (cutoffTwoFullSectorDirichlet_eqv_within_add_cross
          later coefficient)))

end CutoffTwoCapacityScaledPathGluingAt

/-! ## 4. A uniform ratio compiles through completion -/

/-- Minimal cleared finite-cutoff interface.  The positive total cost is kept
explicit so downstream cancellation has no hidden division. -/
structure CutoffTwoCapacityClearedDirichletAt
    (later : Nat) (baseFloor totalCost massFloor : Q') : Type 1 where
  later_ge : 2 ≤ later
  total_cost_pos : (0 : Q') < totalCost
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  cleared_coercivity : ∀ coefficient,
    baseFloor * cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      totalCost * cutoffTwoFullSectorDirichlet later coefficient

namespace CutoffTwoCapacityScaledPathGluingAt

def toCapacityClearedDirichletAt
    {later : Nat}
    {baseFloor massFloor withinCost internalCapacity bridgeCapacity : Q'}
    (certificate : CutoffTwoCapacityScaledPathGluingAt later
      baseFloor massFloor withinCost internalCapacity bridgeCapacity) :
    CutoffTwoCapacityClearedDirichletAt later baseFloor
      (cutoffTwoCapacityTotalCost
        withinCost internalCapacity bridgeCapacity)
      massFloor where
  later_ge := certificate.later_ge
  total_cost_pos := certificate.total_cost_pos
  mass_floor_le := certificate.mass_floor_le
  cleared_coercivity := certificate.cleared_full_coercivity

end CutoffTwoCapacityScaledPathGluingAt

namespace CutoffTwoCapacityClearedDirichletAt

private theorem fullVariance_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoFullSectorPairwiseVariance later coefficient := by
  refine Q'.le_trans' _
    (cutoffTwoWithinBlockPairwiseVariance later coefficient +
      cutoffTwoCrossBlockPairwiseVariance later coefficient) _ ?_ ?_
  · exact Q'.zero_le_add _ _
      (cutoffTwoWithinBlockPairwiseVariance_nonnegative later coefficient)
      (cutoffTwoCrossBlockPairwiseVariance_nonnegative later coefficient)
  exact Q'.ge_of_eqv
    (cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
      later coefficient)

/-- The single uniform ratio comparison cancels the finite total cost and
produces the ordinary full-sector coercivity interface. -/
def toFullSectorDirichletCoercivityAt
    {later : Nat} {baseFloor totalCost massFloor effectiveFloor : Q'}
    (certificate : CutoffTwoCapacityClearedDirichletAt
      later baseFloor totalCost massFloor)
    (ratio_bound : effectiveFloor * totalCost ≤ baseFloor) :
    CutoffTwoFullSectorDirichletCoercivityAt
      later effectiveFloor massFloor where
  later_ge := certificate.later_ge
  mass_floor_le := certificate.mass_floor_le
  full_coercivity := by
    intro coefficient
    let variance := cutoffTwoFullSectorPairwiseVariance later coefficient
    let energy := cutoffTwoFullSectorDirichlet later coefficient
    have hratioScaled :
        (effectiveFloor * totalCost) * variance ≤ baseFloor * variance :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ ratio_bound
        (fullVariance_nonnegative later coefficient)
    have hreassociate :
        totalCost * (effectiveFloor * variance) ≈
          (effectiveFloor * totalCost) * variance := by
      q_ring
    have hcancelReady :
        totalCost * (effectiveFloor * variance) ≤ totalCost * energy := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hreassociate)
        (Q'.le_trans' _ _ _ hratioScaled
          (certificate.cleared_coercivity coefficient))
    exact Q'.le_of_mul_le_mul_left hcancelReady certificate.total_cost_pos

end CutoffTwoCapacityClearedDirichletAt

/-- Cofinal cleared estimates plus one uniform ratio lower bound.  This is the
honest remaining capacity-scaled persistence interface. -/
structure CutoffTwoCofinalCapacityClearedGluing
    (effectiveFloor massFloor : Q') : Type 1 where
  effective_floor_pos : (0 : Q') < effectiveFloor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  baseFloor : Nat → Q'
  totalCost : Nat → Q'
  cleared : ∀ request,
    CutoffTwoCapacityClearedDirichletAt
      (anchor request) (baseFloor request) (totalCost request) massFloor
  ratio_bound : ∀ request,
    effectiveFloor * totalCost request ≤ baseFloor request

namespace CutoffTwoCofinalCapacityClearedGluing

def toFiniteStrictGap
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalCapacityClearedGluing
      effectiveFloor massFloor) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoDirichletGluingRate
        effectiveFloor massFloor
        family.effective_floor_pos family.mass_floor_pos) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    family.effective_floor_pos family.mass_floor_pos
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    family.effective_floor_pos family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := by
    intro request
    exact Nat.le_trans (Nat.le_max_right 2 request)
      (family.anchor_ge request)
  sectorGap := by
    intro request coefficient hcenter
    exact (family.cleared request
      |>.toFullSectorDirichletCoercivityAt (family.ratio_bound request))
      |>.abs_matrix_le_rate_mul_diagonal
        family.effective_floor_pos family.mass_floor_pos coefficient hcenter

def toCompletedStrictContractionData
    {effectiveFloor massFloor : Q'}
    (family : CutoffTwoCofinalCapacityClearedGluing
      effectiveFloor massFloor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalCapacityClearedGluing

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt.lengthLinearPathBudget_le_capacityEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.cutoffTwoCanonicalInternalEdgeLoadCapacity_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.cutoffTwoCanonicalBridgeEdgeLoadCapacity_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.cutoffTwoCanonicalFiniteEdgeLoadCapacitiesAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.CutoffTwoCapacityScaledPathGluingAt.cleared_full_coercivity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.CutoffTwoCapacityClearedDirichletAt.toFullSectorDirichletCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.CutoffTwoCofinalCapacityClearedGluing.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.CutoffTwoCofinalCapacityClearedGluing.toCompletedStrictContractionData
