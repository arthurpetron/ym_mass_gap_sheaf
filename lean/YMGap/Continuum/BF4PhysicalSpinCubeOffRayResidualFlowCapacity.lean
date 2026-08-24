/-
# Pointwise residual-flow capacity compiles to full finite coercivity

The off-ray residual flow module contracts all coefficient dependence to one
explicit directed-edge load.  This module states the remaining finite analytic
datum pointwise: the shared ray floor times that load must fit inside the half
of the genuine physical kernel reserved for the residual.

Finite sum monotonicity compiles this local, coefficient-independent capacity
comparison into the residual form certificate, and the preceding half-energy
compiler then gives full finite-sector pairwise Dirichlet coercivity.  A
cofinal family of the pointwise certificates compiles to the already isolated
cofinal residual frontier.

No pointwise capacity certificate is inhabited here.  In particular no
uniform full-sector gap, thermodynamic or continuum limit, continuum QFT, or
Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite summation of a pointwise scaled-joint comparison -/

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left => scale * listQSum
        (fun right =>
          joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)))
        rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right => scale *
          (joint left right *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

private theorem scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (load kernel : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        scale * load left right ≤ kernel left right) :
    scale * finiteJointDirichletBlock
        leftStates rightStates coefficient load ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
  have hsum : finiteJointDirichletBlock
        leftStates rightStates coefficient
          (fun left right => scale * load left right) ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
    unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (hjoint left hleft right hright)
      (SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint_local
          leftStates rightStates coefficient scale load)))
    hsum

/-! ## 2. The exact pointwise residual-capacity frontier -/

/-- The coefficient-independent local inequality now sufficient for the
off-ray residual.  It allocates exactly half of each genuine physical-kernel
edge to the residual flow at the shared positive floor `rayDelta / 2`. -/
structure CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    Type 1 where
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualFlowLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt

theorem sharedFloor_mul_rawLoadedDirichlet_le_half_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
        hw K rayCapacity)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualRawLoadedDirichlet
          w (Q'.le_of_lt hw) K coefficient ≤
      HalfPow.half * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
      finiteJointDirichletBlock
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (fun source target =>
          centralLowerExcitedSpinCubeOffRayResidualFlowLoad
            w (Q'.le_of_lt hw) K source target * 1) ≤ _
  change _ ≤ HalfPow.half * finiteJointDirichletBlock
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)
  have hscaled := scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    coefficient
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
    (fun source target =>
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w (Q'.le_of_lt hw) K source target * 1)
    (fun source target => HalfPow.half *
      centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target)
    (fun source hsource target htarget =>
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left
            (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity) _ _
            (Q'.mul_one_eqv
              (centralLowerExcitedSpinCubeOffRayResidualFlowLoad
                w (Q'.le_of_lt hw) K source target))))
        (flowCapacity.edge_capacity source hsource target htarget))
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (finiteJointDirichletBlock_scale_joint_local
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient HalfPow.half
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)))

/-- The pointwise residual-flow comparison inhabits the exact form-level
certificate required by the ray/residual half-energy compiler. -/
def toOffRayResidualCoercivityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
      hw K rayCapacity where
  residual_coercivity := fun coefficient => by
    have hresidual :=
      centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawLoadedDirichlet
        w (Q'.le_of_lt hw) K coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
      hresidual
      (Q'.le_of_lt
        (centralLowerExcitedSpinCubeSharedCoercivityFloor_pos rayCapacity))
    exact Q'.le_trans' _ _ _ hscaled
      (flowCapacity.sharedFloor_mul_rawLoadedDirichlet_le_half_physicalDirichlet
        coefficient)

/-- Local flow capacity therefore gives full finite-sector pairwise
Dirichlet coercivity at the same shared floor. -/
theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (flowCapacity :
      CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
        hw K rayCapacity)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
      flowCapacity.toOffRayResidualCoercivityAt coefficient

end CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt

/-! ## 3. Cofinal pointwise capacity and its lossless compiler -/

/-- The remaining cofinal problem expressed entirely as pointwise congestion
of one explicit coefficient-independent residual flow.  No inhabitant is
asserted here. -/
structure FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  flow_capacity : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity

def toCofinalResidualCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualCoercivity hw rayCapacity where
  residual := fun K hK =>
    (family.flow_capacity K hK).toOffRayResidualCoercivityAt

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity hw rayCapacity)
    {K : Nat} (hK : rayCapacity.start ≤ K)
    (coefficient : Nat → Q') :
    (HalfPow.half * rayCapacity.delta) *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K 0 coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  exact
    FixedNomeCofinalSpinCubeOffRayResidualCoercivity.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
      family.toCofinalResidualCoercivity hK coefficient

end FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity.CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt.sharedFloor_mul_rawLoadedDirichlet_le_half_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity.CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt.toOffRayResidualCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity.CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity.FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toCofinalResidualCoercivity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity.FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
