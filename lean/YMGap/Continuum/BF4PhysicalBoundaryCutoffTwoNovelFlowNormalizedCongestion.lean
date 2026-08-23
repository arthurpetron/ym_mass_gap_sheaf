/-
# Normalized canonical-path congestion of the novel BF4 flow

The local novel-flow load is now an exact sum of stationary endpoint-pair
path contributions.  This module divides that load by the allocated physical
kernel on every positive-load edge.  The resulting normalized congestion is
exactly the sum of the correspondingly normalized endpoint-pair terms.

The original edge-capacity comparison is proved equivalent to the unit
bound

  delta_flow * normalizedCongestion(edge) <= 1.

Thus the cofinal finite frontier is put in the standard canonical-path form:
uniformly bound the maximum normalized weighted congestion, using the
concrete BF4 stationary weights and kernel.  No such uniform bound,
thermodynamic/continuum construction, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite division commutes with summation -/

theorem listQSum_divPos_eqv_divPos_listQSum
    {A : Type} (value : A → Q') (denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    ∀ items : List A,
      listQSum
          (fun item => Q'.divPos (value item) denominator hdenominator)
          items ≈
        Q'.divPos (listQSum value items) denominator hdenominator
  | [] => by
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv (Q'.recipPos denominator hdenominator))
  | first :: rest => by
      unfold listQSum
      refine Q'.eqv_trans _
        (Q'.divPos (value first) denominator hdenominator +
          Q'.divPos (listQSum value rest) denominator hdenominator) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (listQSum_divPos_eqv_divPos_listQSum
            value denominator hdenominator rest)
      unfold Q'.divPos
      exact Q'.eqv_symm
        (Q'.add_mul_eqv
          (value first) (listQSum value rest)
          (Q'.recipPos denominator hdenominator))

/-! ## 2. Exact normalized edge congestion -/

/-- Weighted canonical-path congestion on one edge, normalized by precisely
the physical capacity allocated to the novel flow. -/
def cutoffTwoNovelNormalizedEdgeCongestion
    (later source target : Nat) : Q' :=
  if hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target then
    Q'.divPos
      (cutoffTwoNovelSimpleEdgeLoad later source target)
      (cutoffTwoNovelAllocatedKernel later source target)
      (cutoffTwoNovelAllocatedKernel_pos_of_load_pos
        later source target hload)
  else 0

/-- One endpoint pair's contribution to the same normalized edge
congestion.  The denominator is common across every pair on the edge. -/
def cutoffTwoNovelPathPairNormalizedEdgeContribution
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target then
    Q'.divPos
      (cutoffTwoNovelPathPairEdgeContribution
        later source target pair)
      (cutoffTwoNovelAllocatedKernel later source target)
      (cutoffTwoNovelAllocatedKernel_pos_of_load_pos
        later source target hload)
  else 0

/-- The normalized edge congestion is exactly the sum of normalized
stationary endpoint-pair path contributions. -/
theorem cutoffTwoNovelNormalizedEdgeCongestion_eqv_pairSum
    (later source target : Nat) :
    cutoffTwoNovelNormalizedEdgeCongestion later source target ≈
      listQSum
        (cutoffTwoNovelPathPairNormalizedEdgeContribution
          later source target)
        (cutoffTwoNovelEndpointPairs later) := by
  by_cases hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target
  · have hallocated : (0 : Q') <
        cutoffTwoNovelAllocatedKernel later source target :=
      cutoffTwoNovelAllocatedKernel_pos_of_load_pos
        later source target hload
    have hregroup :
        cutoffTwoNovelSimpleEdgeLoad later source target ≈
          listQSum
            (cutoffTwoNovelPathPairEdgeContribution later source target)
            (cutoffTwoNovelEndpointPairs later) :=
      cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
        later source target
    have hmain :
        Q'.divPos
            (cutoffTwoNovelSimpleEdgeLoad later source target)
            (cutoffTwoNovelAllocatedKernel later source target)
            hallocated ≈
          listQSum
            (fun pair => Q'.divPos
              (cutoffTwoNovelPathPairEdgeContribution
                later source target pair)
              (cutoffTwoNovelAllocatedKernel later source target)
              hallocated)
            (cutoffTwoNovelEndpointPairs later) := by
      refine Q'.eqv_trans _
        (Q'.divPos
        (listQSum
          (cutoffTwoNovelPathPairEdgeContribution later source target)
          (cutoffTwoNovelEndpointPairs later))
          (cutoffTwoNovelAllocatedKernel later source target)
          hallocated) _ ?_ ?_
      · unfold Q'.divPos
        exact Q'.mul_eqv_congr_right _ _
          (Q'.recipPos
            (cutoffTwoNovelAllocatedKernel later source target)
            hallocated)
          hregroup
      exact Q'.eqv_symm
        (listQSum_divPos_eqv_divPos_listQSum
          (cutoffTwoNovelPathPairEdgeContribution later source target)
          (cutoffTwoNovelAllocatedKernel later source target)
          hallocated
          (cutoffTwoNovelEndpointPairs later))
    have hleft :
        cutoffTwoNovelNormalizedEdgeCongestion later source target ≈
          Q'.divPos
            (cutoffTwoNovelSimpleEdgeLoad later source target)
            (cutoffTwoNovelAllocatedKernel later source target)
            hallocated := by
      apply Q'.eqv_of_eq
      unfold cutoffTwoNovelNormalizedEdgeCongestion
      rw [dif_pos hload]
    have hright :
        listQSum
            (fun pair => Q'.divPos
              (cutoffTwoNovelPathPairEdgeContribution
                later source target pair)
              (cutoffTwoNovelAllocatedKernel later source target)
              hallocated)
            (cutoffTwoNovelEndpointPairs later) ≈
          listQSum
            (cutoffTwoNovelPathPairNormalizedEdgeContribution
              later source target)
            (cutoffTwoNovelEndpointPairs later) := by
      apply listQSum_congr_on
      intro pair _hpair
      apply Q'.eqv_symm
      apply Q'.eqv_of_eq
      unfold cutoffTwoNovelPathPairNormalizedEdgeContribution
      rw [dif_pos hload]
    exact Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _ hmain hright)
  · have hleft :
        cutoffTwoNovelNormalizedEdgeCongestion later source target ≈ 0 := by
      apply Q'.eqv_of_eq
      unfold cutoffTwoNovelNormalizedEdgeCongestion
      rw [dif_neg hload]
    have hright :
        listQSum
            (cutoffTwoNovelPathPairNormalizedEdgeContribution
              later source target)
            (cutoffTwoNovelEndpointPairs later) ≈ 0 := by
      refine Q'.eqv_trans _
        (listQSum (fun _ : Nat × Nat => (0 : Q'))
          (cutoffTwoNovelEndpointPairs later)) _ ?_ ?_
      · apply listQSum_congr_on
        intro pair _hpair
        apply Q'.eqv_of_eq
        unfold cutoffTwoNovelPathPairNormalizedEdgeContribution
        rw [dif_neg hload]
      exact listQSum_zero (cutoffTwoNovelEndpointPairs later)
    exact Q'.eqv_trans _ 0 _ hleft (Q'.eqv_symm hright)

theorem cutoffTwoNovelNormalizedEdgeCongestion_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤
      cutoffTwoNovelNormalizedEdgeCongestion later source target := by
  unfold cutoffTwoNovelNormalizedEdgeCongestion
  by_cases hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target
  · rw [dif_pos hload]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt hload)
      (Q'.le_of_lt
        (Q'.recipPos_pos _
          (cutoffTwoNovelAllocatedKernel_pos_of_load_pos
            later source target hload)))
  · rw [dif_neg hload]
    exact Q'.le_refl' 0

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

private theorem cutoffTwoNovelSimpleEdgeLoad_eqv_zero_of_not_pos
    {later source target : Nat}
    (hload : ¬ (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≈ 0 :=
  Q'.eqv_of_le_le
    (q_nonpos_of_not_pos_local hload)
    (cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target)

/-! ## 3. Capacity is exactly the unit congestion bound -/

private theorem scalar_mul_divPos_eqv_divPos_mul
    (scalar numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    scalar * Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos (scalar * numerator) denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv scalar numerator
      (Q'.recipPos denominator hdenominator))

/-- Paying the grouped edge load from its allocated physical kernel is
equivalent to bounding the normalized congestion by the reciprocal target,
written division-free as `delta_flow * congestion <= 1`. -/
theorem cutoffTwoNovelEdgeCapacity_iff_normalizedCongestion
    (later source target : Nat) :
    (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target) ↔
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelNormalizedEdgeCongestion later source target ≤
        (1 : Q')) := by
  by_cases hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later source target
  · let allocated := cutoffTwoNovelAllocatedKernel later source target
    let hallocated : (0 : Q') < allocated :=
      cutoffTwoNovelAllocatedKernel_pos_of_load_pos
        later source target hload
    have hnormalized :
        cutoffTwoNovelNormalizedEdgeCongestion later source target =
          Q'.divPos
            (cutoffTwoNovelSimpleEdgeLoad later source target)
            allocated hallocated := by
      unfold cutoffTwoNovelNormalizedEdgeCongestion
      rw [dif_pos hload]
    constructor
    · intro hcapacity
      have hscaledCapacity :
          cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelSimpleEdgeLoad later source target ≤
            (1 : Q') * allocated :=
        Q'.le_trans' _ _ _ hcapacity
          (Q'.ge_of_eqv (Q'.one_mul_eqv allocated))
      have hquotient := Q'.divPos_le_of_le_mul
        (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target)
        allocated hallocated hscaledCapacity
      rw [hnormalized]
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (scalar_mul_divPos_eqv_divPos_mul
            cutoffTwoNovelSimpleFlowCoercivityFloor
            (cutoffTwoNovelSimpleEdgeLoad later source target)
            allocated hallocated))
        hquotient
    · intro hcongestion
      have hallocated0 : (0 : Q') ≤ allocated :=
        Q'.le_of_lt hallocated
      have hscaled := Q'.mul_le_mul_of_nonneg_right
        (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelNormalizedEdgeCongestion later source target)
        1 allocated hcongestion hallocated0
      have hcollapse :
          cutoffTwoNovelNormalizedEdgeCongestion later source target *
              allocated ≈
            cutoffTwoNovelSimpleEdgeLoad later source target := by
        rw [hnormalized]
        exact Q'.divPos_mul_eqv _ _ hallocated
      have hleft :
          cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelSimpleEdgeLoad later source target ≈
            (cutoffTwoNovelSimpleFlowCoercivityFloor *
                cutoffTwoNovelNormalizedEdgeCongestion later source target) *
              allocated := by
        refine Q'.eqv_trans _
          (cutoffTwoNovelSimpleFlowCoercivityFloor *
            (cutoffTwoNovelNormalizedEdgeCongestion later source target *
              allocated)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_left
            cutoffTwoNovelSimpleFlowCoercivityFloor _ _
            (Q'.eqv_symm hcollapse)
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            cutoffTwoNovelSimpleFlowCoercivityFloor
            (cutoffTwoNovelNormalizedEdgeCongestion later source target)
            allocated)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv (Q'.one_mul_eqv allocated)))
  · have hloadZero :=
      cutoffTwoNovelSimpleEdgeLoad_eqv_zero_of_not_pos hload
    have hnormalizedZero :
        cutoffTwoNovelNormalizedEdgeCongestion later source target = 0 := by
      unfold cutoffTwoNovelNormalizedEdgeCongestion
      rw [dif_neg hload]
    constructor
    · intro _hcapacity
      rw [hnormalizedZero]
      exact Q'.le_trans' _ 0 _
        (Q'.le_of_eqv
          (Q'.mul_zero_eqv
            cutoffTwoNovelSimpleFlowCoercivityFloor))
        (by decide)
    · intro _hcongestion
      exact Q'.le_trans' _ 0 _
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (cutoffTwoNovelSimpleFlowCoercivityFloor * 0) _
            (Q'.mul_eqv_congr_left
              cutoffTwoNovelSimpleFlowCoercivityFloor _ _ hloadZero)
            (Q'.mul_zero_eqv
              cutoffTwoNovelSimpleFlowCoercivityFloor)))
        (cutoffTwoNovelAllocatedKernel_nonnegative later source target)

/-! ## 4. Uniform congestion bounds compile to the completed gap -/

/-- An all-edge normalized congestion bound implies the explicit finite
capacity-floor comparison. -/
theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_congestion
    (later : Nat)
    (hcongestion : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelNormalizedEdgeCongestion
            later source target ≤ (1 : Q')) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply le_listPositiveMinOne_of_forall
    (fun pair : Nat × Nat =>
      cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelCapacityEdgePairs later)
    cutoffTwoNovelSimpleFlowCoercivityFloor_le_one
  intro pair hpair
  have hfull :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  have hcapacity :=
    (cutoffTwoNovelEdgeCapacity_iff_normalizedCongestion
      later pair.1 pair.2).mpr
      (hcongestion pair.1 hfull.1 pair.2 hfull.2)
  by_cases hload : (0 : Q') <
      cutoffTwoNovelSimpleEdgeLoad later pair.1 pair.2
  · unfold cutoffTwoNovelEdgeCapacityRatio
    rw [dif_pos hload]
    exact Q'.le_divPos_of_mul_le
      (cutoffTwoNovelAllocatedKernel later pair.1 pair.2)
      (cutoffTwoNovelSimpleEdgeLoad later pair.1 pair.2)
      hload hcapacity
  · unfold cutoffTwoNovelEdgeCapacityRatio
    rw [dif_neg hload]
    exact cutoffTwoNovelSimpleFlowCoercivityFloor_le_one

structure CutoffTwoCofinalNovelNormalizedCongestionBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  congestion : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelNormalizedEdgeCongestion
          (anchor request) source target ≤ (1 : Q')

namespace CutoffTwoCofinalNovelNormalizedCongestionBound

def toCofinalNovelFlowCapacityRatio
    (bound : CutoffTwoCofinalNovelNormalizedCongestionBound) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_congestion
      (bound.anchor request)
      (bound.congestion request)

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelNormalizedCongestionBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

end CutoffTwoCofinalNovelNormalizedCongestionBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion.cutoffTwoNovelNormalizedEdgeCongestion_eqv_pairSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion.cutoffTwoNovelEdgeCapacity_iff_normalizedCongestion
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion.cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_congestion
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion.CutoffTwoCofinalNovelNormalizedCongestionBound.toCompletedStrictContractionData
