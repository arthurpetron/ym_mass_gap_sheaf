/-
# A concrete carrier-linear full-sector coercivity floor at every cutoff

The normalized off-ray residual flow has directed load at most the finite
vacuum-sector carrier size.  At a fixed cutoff, shrink the already constructed
spin-cube ray capacity to the minimum of its ray floor and

  finitePositiveEdgeFloor / (1 + sectorSize).

The restricted ray certificate still pays every ray spoke, while the quotient
identity pays the entire residual flow.  The ray/residual half-energy compiler
therefore gives an unconditional strictly positive full-sector pairwise
Dirichlet coercivity floor at every finite cutoff.  Its denominator is linear,
rather than quadratic, in the carrier size.

No cutoff-uniform lower bound for this finite floor is proved.  In particular
the carrier size grows and the minimum positive edge may shrink.  No uniform
completed gap, thermodynamic or continuum limit, continuum QFT, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
import YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity

namespace YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem q_min_pos_local {left right : Q'}
    (hleft : (0 : Q') < left) (hright : (0 : Q') < right) :
    (0 : Q') < Q'.min' left right := by
  unfold Q'.min'
  by_cases horder : left ≤ right
  · rw [if_pos horder]
    exact hleft
  · rw [if_neg horder]
    exact hright

/-! ## 1. Restrict the ray certificate to the finite residual capacity -/

def centralLowerExcitedSpinCubeFiniteLinearRayDelta
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) : Q' :=
  let cost :=
    centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
      w (Q'.le_of_lt hw) K
  Q'.min' rayCapacity.delta
    (Q'.divPos
      (centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0)
      cost
      (centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost_pos
        w (Q'.le_of_lt hw) K))

theorem centralLowerExcitedSpinCubeFiniteLinearRayDelta_pos
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity := by
  unfold centralLowerExcitedSpinCubeFiniteLinearRayDelta
  apply q_min_pos_local rayCapacity.delta_pos
  exact Q'.divPos_pos _ _ _
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w (Q'.le_of_lt hw) K 0)

theorem centralLowerExcitedSpinCubeFiniteLinearRayDelta_le_rayDelta
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity ≤
      rayCapacity.delta := by
  unfold centralLowerExcitedSpinCubeFiniteLinearRayDelta
  exact Q'.min_le_left' _ _

theorem centralLowerExcitedSpinCubeFiniteLinearRayDelta_mul_cost_le_edgeFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
          w (Q'.le_of_lt hw) K ≤
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0 := by
  let cost :=
    centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
      w (Q'.le_of_lt hw) K
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w (Q'.le_of_lt hw) K 0
  have hcost : (0 : Q') < cost :=
    centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost_pos
      w (Q'.le_of_lt hw) K
  have hdelta :
      centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity ≤
        Q'.divPos floor cost hcost := by
    unfold centralLowerExcitedSpinCubeFiniteLinearRayDelta
    exact Q'.min_le_right' _ _
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ cost
    hdelta (Q'.le_of_lt hcost)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (Q'.divPos_mul_eqv floor cost hcost))

def centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K where
  delta := centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity
  delta_pos :=
    centralLowerExcitedSpinCubeFiniteLinearRayDelta_pos rayCapacity
  twice_le_return := fun offset hoffset => by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
      (centralLowerExcitedSpinCubeFiniteLinearRayDelta_le_rayDelta rayCapacity)
      (by decide : (0 : Q') ≤ 2)
    exact Q'.le_trans' _ _ _ hscaled
      (rayCapacity.twice_le_return offset hoffset)
  left_spoke := fun offset hoffset => by
    let load := centralLowerExcitedSpinCubeRayFlowLoad
      w (Q'.le_of_lt hw) K
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset) 0
    have hload0 : (0 : Q') ≤ load :=
      centralLowerExcitedSpinCubeRayFlowLoad_nonnegative hw K _ _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ load
      (centralLowerExcitedSpinCubeFiniteLinearRayDelta_le_rayDelta rayCapacity)
      hload0
    exact Q'.le_trans' _ _ _ hscaled
      (rayCapacity.left_spoke offset hoffset)
  right_spoke := fun offset hoffset => by
    let load := centralLowerExcitedSpinCubeRayFlowLoad
      w (Q'.le_of_lt hw) K 0
      (centralLowerExcitedSpinCubeIndex
        w (Q'.le_of_lt hw) K offset)
    have hload0 : (0 : Q') ≤ load :=
      centralLowerExcitedSpinCubeRayFlowLoad_nonnegative hw K _ _
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ load
      (centralLowerExcitedSpinCubeFiniteLinearRayDelta_le_rayDelta rayCapacity)
      hload0
    exact Q'.le_trans' _ _ _ hscaled
      (rayCapacity.right_spoke offset hoffset)

/-! ## 2. The quotient pays the residual and yields full finite coercivity -/

def centralLowerExcitedSpinCubeFiniteLinearNormalizedRatioAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt
      hw K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
        rayCapacity) where
  ratio_bound := by
    let delta := centralLowerExcitedSpinCubeFiniteLinearRayDelta rayCapacity
    let cost :=
      centralLowerExcitedSpinCubeOffRayResidualNormalizedLinearCost
        w (Q'.le_of_lt hw) K
    let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K 0
    have hbase : delta * cost ≤ floor :=
      centralLowerExcitedSpinCubeFiniteLinearRayDelta_mul_cost_le_edgeFloor
        rayCapacity
    have hhalf := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hbase HalfPow.half_nonneg
    unfold centralLowerExcitedSpinCubeSharedCoercivityFloor
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv HalfPow.half delta cost))
      hhalf

def centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) : Q' :=
  centralLowerExcitedSpinCubeSharedCoercivityFloor
    (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity rayCapacity)

theorem centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_pos
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor
        rayCapacity := by
  unfold centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor
  exact centralLowerExcitedSpinCubeSharedCoercivityFloor_pos _

theorem centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor rayCapacity *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact
    (centralLowerExcitedSpinCubeFiniteLinearNormalizedRatioAt rayCapacity)
      |>.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet coefficient

/-! ## 3. Concrete strong-coupling specialization -/

def anchorCentralSpinCubeFiniteLinearFullCoercivityFloor
    (K : Nat) : Q' :=
  centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor
    (anchorCentralSpinCubeFiniteRayCapacityAt K)

theorem anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_pos
    (K : Nat) :
    (0 : Q') < anchorCentralSpinCubeFiniteLinearFullCoercivityFloor K := by
  exact centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_pos _

theorem anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet
    (K : Nat) (coefficient : Nat → Q') :
    anchorCentralSpinCubeFiniteLinearFullCoercivityFloor K *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          anchorCoupling (by decide) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          anchorCoupling (by decide) K 0)
        coefficient
        (centralPhysicalFiniteKernel anchorCoupling (by decide) K 0) := by
  exact
    centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet
      (anchorCentralSpinCubeFiniteRayCapacityAt K) coefficient

end YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearRayDelta_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearRayDelta_mul_cost_le_edgeFloor
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearNormalizedRatioAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet
