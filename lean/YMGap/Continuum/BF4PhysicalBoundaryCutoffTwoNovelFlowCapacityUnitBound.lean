/-
# The novel-flow target is below the unit fallback

The finite capacity checker retained a logically possible failure branch in
which the requested flow strength exceeded the unit fallback of the located
minimum.  This module rules that branch out from the already constructed BF4
data.

The opaque transported base-edge floor is bounded by one by evaluating its
own pointwise field on the vacuum-root diagonal and using the normalized
Markov entry cap.  Dividing by the path ceiling cannot increase it because
that ceiling is at least one, and the final novel-flow target spends only one
half of the result.  Consequently failure of the exact finite scan always
returns a literal overloaded positive-load edge.

No uniform control of those loaded edges, completed gap inhabitant,
thermodynamic/continuum limit, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-! ## 1. Unit bounds for every factor of the fixed target -/

private theorem cutoffTwoPulledRoot_mem :
    0 ∈ cutoffTwoPulledStates := by
  unfold cutoffTwoPulledStates
  exact zero_mem_centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 0

private theorem cutoffTwoBaseRootKernel_pos :
    (0 : Q') < centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) 2 0 0 0 := by
  unfold centralPhysicalFiniteKernel
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact centralNormalizedPhysicalReflectedKernel_vacuum_pos
    (by decide) 2 0

/-- The transported base-positive edge floor is no larger than one.  This
uses only the certificate's own root-edge comparison and the normalized
Markov entry cap, so no unfolding of its opaque implementation is required. -/
theorem cutoffTwoPulledUniformBasePositiveEdgeFloor_le_one :
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor ≤ (1 : Q') := by
  have hfloorKernel :=
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor_le
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start
      (Nat.le_refl _)
      0 0 cutoffTwoPulledRoot_mem cutoffTwoPulledRoot_mem
      cutoffTwoBaseRootKernel_pos
  have habs := cutoffTwoPulledKernelAt_abs_le_one
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    cutoffTwoPulledRoot_mem cutoffTwoPulledRoot_mem
  exact Q'.le_trans' _ _ _ hfloorKernel
    (Q'.le_trans' _ _ _
      (Q'.le_abs_self
        (cutoffTwoPulledKernelAt
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start 0 0))
      habs)

theorem one_le_cutoffTwoPulledCanonicalPathCeiling :
    (1 : Q') ≤ cutoffTwoPulledCanonicalPathCeiling := by
  unfold cutoffTwoPulledCanonicalPathCeiling
    centralPhysicalFiniteVacuumSectorPathCeiling
  exact Q'.add_le_self_of_nonneg 1 _
    (centralPhysicalFiniteVacuumSectorPathScaleSum_nonnegative
      cutoffTwoHalfCoupling (by decide) 2 0)

/-- Dividing the base floor by the fixed path ceiling cannot increase it. -/
theorem cutoffTwoUniformOldBlockCoercivityFloor_le_baseFloor :
    cutoffTwoUniformOldBlockCoercivityFloor ≤
      cutoffTwoPulledUniformBasePositiveEdgeFloor.floor := by
  unfold cutoffTwoUniformOldBlockCoercivityFloor
  apply Q'.divPos_le_of_le_mul
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor
    cutoffTwoPulledCanonicalPathCeiling
    cutoffTwoPulledCanonicalPathCeiling_pos
  have hfloor0 : (0 : Q') ≤
      cutoffTwoPulledUniformBasePositiveEdgeFloor.floor :=
    Q'.le_of_lt
      cutoffTwoPulledUniformBasePositiveEdgeFloor.floor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (1 : Q') cutoffTwoPulledCanonicalPathCeiling
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor
    one_le_cutoffTwoPulledCanonicalPathCeiling hfloor0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.mul_one_eqv
        cutoffTwoPulledUniformBasePositiveEdgeFloor.floor))
    hscaled

theorem cutoffTwoUniformOldBlockCoercivityFloor_le_one :
    cutoffTwoUniformOldBlockCoercivityFloor ≤ (1 : Q') :=
  Q'.le_trans' _ _ _
    cutoffTwoUniformOldBlockCoercivityFloor_le_baseFloor
    cutoffTwoPulledUniformBasePositiveEdgeFloor_le_one

/-- The fixed strength scanned by the novel-flow checker is below one. -/
theorem cutoffTwoNovelSimpleFlowCoercivityFloor_le_one :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤ (1 : Q') := by
  unfold cutoffTwoNovelSimpleFlowCoercivityFloor
  have hold0 : (0 : Q') ≤ cutoffTwoUniformOldBlockCoercivityFloor :=
    Q'.le_of_lt cutoffTwoUniformOldBlockCoercivityFloor_pos
  have hhalf : HalfPow.half ≤ (1 : Q') := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    HalfPow.half 1 cutoffTwoUniformOldBlockCoercivityFloor
    hhalf hold0
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.one_mul_eqv cutoffTwoUniformOldBlockCoercivityFloor))
      cutoffTwoUniformOldBlockCoercivityFloor_le_one)

/-! ## 2. The checker is only the edge scan -/

/-- With the unit comparison discharged once and for all, the executable
frontier is exactly the scan of the full-sector edge ratios. -/
def cutoffTwoNovelEdgeCapacityCheck (later : Nat) : Bool :=
  (cutoffTwoNovelCapacityEdgePairs later).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor ≤
        cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2))

theorem cutoffTwoNovelEdgeCapacityCheck_sound
    (later : Nat)
    (hcheck : cutoffTwoNovelEdgeCapacityCheck later = true) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  exact le_listPositiveMinOne_of_forall
    (fun pair : Nat × Nat =>
      cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelCapacityEdgePairs later)
    cutoffTwoNovelSimpleFlowCoercivityFloor_le_one
    (fun pair hpair =>
      of_decide_eq_true
        (List.all_eq_true.mp hcheck pair hpair))

theorem cutoffTwoNovelEdgeCapacityCheck_complete
    (later : Nat)
    (hfloor : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later) :
    cutoffTwoNovelEdgeCapacityCheck later = true := by
  unfold cutoffTwoNovelEdgeCapacityCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  apply decide_eq_true
  exact Q'.le_trans' _ _ _ hfloor
    (listPositiveMinOne_le_of_mem
      (fun edge : Nat × Nat =>
        cutoffTwoNovelEdgeCapacityRatio later edge.1 edge.2)
      (cutoffTwoNovelCapacityEdgePairs later)
      pair hpair)

/-! ## 3. Exact binary certificate-or-overload result -/

inductive CutoffTwoNovelFlowCapacityDecisiveOutcome (later : Nat) : Type
  | certified
      (floor_le : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
        cutoffTwoNovelFiniteFlowCapacityFloor later)
  | overloadedEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadFullStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadFullStates later)
      (load_pos : (0 : Q') <
        cutoffTwoNovelSimpleEdgeLoad later source target)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSimpleEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target)

/-- Every fixed cutoff computes to a capacity certificate or a genuine
positive-load overloaded BF4 edge; the unit-fallback outcome is impossible. -/
def inspectCutoffTwoNovelFlowCapacityDecisively
    (later : Nat) : CutoffTwoNovelFlowCapacityDecisiveOutcome later := by
  cases inspectCutoffTwoNovelFlowCapacity later with
  | certified hfloor =>
      exact CutoffTwoNovelFlowCapacityDecisiveOutcome.certified hfloor
  | targetAboveUnit hunit =>
      exact False.elim
        (hunit cutoffTwoNovelSimpleFlowCoercivityFloor_le_one)
  | overloadedEdge source target hsource htarget hload hoverload =>
      exact CutoffTwoNovelFlowCapacityDecisiveOutcome.overloadedEdge
        source target hsource htarget hload hoverload

/-! ## 4. Cofinal edge scans compile to the completed gap interface -/

structure CutoffTwoCofinalNovelEdgeCapacityCheck : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelEdgeCapacityCheck (anchor request) = true

namespace CutoffTwoCofinalNovelEdgeCapacityCheck

/-- A cofinal edge scan supplies an explicit certified branch of the finite
capacity-or-overload decision at every selected anchor.  The overloaded branch
is not hidden or discarded: it is excluded here by the supplied Boolean scan
certificate itself. -/
def certifiedOutcomeAt
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck)
    (request : Nat) :
    CutoffTwoNovelFlowCapacityDecisiveOutcome (checked.anchor request) :=
  CutoffTwoNovelFlowCapacityDecisiveOutcome.certified
    (cutoffTwoNovelEdgeCapacityCheck_sound
      (checked.anchor request) (checked.check request))

def toCofinalNovelFlowCapacityRatio
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelEdgeCapacityCheck_sound
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  checked.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

/-- Once the cofinal edge scan is supplied, the forward capacity witness
feeds directly into the already completed same-sector autocorrelation decay.
This is only a composition theorem: it introduces no new cofinal estimate. -/
theorem completedAutocorrelation_sq_decay
    (checked : CutoffTwoCofinalNovelEdgeCapacityCheck)
    (n : Nat)
    (vector :
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 n vector.1)
        (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
          (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 n vector.1))
      (CReal.RCmul
        (CReal.RCscale
          ((checked.toCompletedStrictContractionData.rate *
              checked.toCompletedStrictContractionData.rate) ^ n)
          (centralPhysicalVacuumSectorCylinderCompletedInner
            (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
            vector.1 vector.1))
        (centralPhysicalVacuumSectorCylinderCompletedInner
          (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
          vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    checked.toCompletedStrictContractionData n vector

end CutoffTwoCofinalNovelEdgeCapacityCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.cutoffTwoPulledUniformBasePositiveEdgeFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.cutoffTwoNovelSimpleFlowCoercivityFloor_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.cutoffTwoNovelEdgeCapacityCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.inspectCutoffTwoNovelFlowCapacityDecisively
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.CutoffTwoCofinalNovelEdgeCapacityCheck.certifiedOutcomeAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.CutoffTwoCofinalNovelEdgeCapacityCheck.completedAutocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.CutoffTwoCofinalNovelEdgeCapacityCheck.toCompletedStrictContractionData
