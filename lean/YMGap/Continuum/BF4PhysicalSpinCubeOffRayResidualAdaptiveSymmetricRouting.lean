/-
# Symmetric routed flow at every finite BF4 cutoff

The routed residual flow is directed, but the Dirichlet form consumes it on a
square carrier and the physical joint kernel is symmetric.  This module uses
that mathematical symmetry before any cutoff-tail decomposition:

* average every routed edge load with its reverse;
* prove that the full loaded Dirichlet form is unchanged exactly;
* prove that a pointwise capacity bound for the averaged load still produces
  the existing residual-coercivity object; and
* for any explicit old/new partition of the vacuum carrier, derive the
  new--old capacity field from the old--new field.

Thus an oriented three-block certificate needs only old--old, old--new, and
new--new estimates.  This is an exact arbitrary-cutoff contraction of the
analytic frontier, not an assumed tail estimate.  No capacity certificate,
uniform cutoff control, thermodynamic/continuum limit, continuum Yang--Mills
theory, or Clay conclusion is inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
functional extensionality, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricRouting

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact transpose averaging on a square Dirichlet carrier -/

private theorem coefficientDifferenceSquare_symm
    {State : Type} (coefficient : State → Q')
    (left right : State) :
    (coefficient left + -coefficient right) *
        (coefficient left + -coefficient right) ≈
      (coefficient right + -coefficient left) *
        (coefficient right + -coefficient left) := by
  q_ring

private theorem finiteJointDirichletBlock_joint_congr_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        first left right ≈ second left right) :
    finiteJointDirichletBlock
        leftStates rightStates coefficient first ≈
      finiteJointDirichletBlock
        leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  exact Q'.mul_eqv_congr_right _ _ _
    (hjoint left hleft right hright)

private theorem finiteJointDirichletBlock_add_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (first second : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => first left right + second left right) ≈
      finiteJointDirichletBlock leftStates rightStates coefficient first +
        finiteJointDirichletBlock
          leftStates rightStates coefficient second := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            first left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)) +
              second left right *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.add_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right =>
            first left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates +
        listQSum
          (fun right =>
            second left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    exact listQSum_add _ _ rightStates
  · exact listQSum_add _ _ leftStates

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
      (fun left =>
        scale * listQSum
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
        (fun right =>
          scale *
            (joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

private theorem finiteJointDirichletBlock_transpose_eqv
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock states states coefficient
        (fun left right => joint right left) ≈
      finiteJointDirichletBlock states states coefficient joint := by
  let term : State → State → Q' := fun left right =>
    joint right left *
      ((coefficient right + -coefficient left) *
        (coefficient right + -coefficient left))
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum (fun left => listQSum (term left) states) states) _ ?_ ?_
  · apply listQSum_congr
    intro left
    apply listQSum_congr
    intro right
    exact Q'.mul_eqv_congr_left (joint right left) _ _
      (coefficientDifferenceSquare_symm coefficient left right)
  · exact Q'.eqv_symm (listQSum_swap term states states)

private theorem finiteJointDirichletBlock_averageTranspose_eqv
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock states states coefficient
        (fun left right =>
          HalfPow.half * joint left right +
            HalfPow.half * joint right left) ≈
      finiteJointDirichletBlock states states coefficient joint := by
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock states states coefficient
        (fun left right => HalfPow.half * joint left right) +
      finiteJointDirichletBlock states states coefficient
        (fun left right => HalfPow.half * joint right left)) _ ?_ ?_
  · exact finiteJointDirichletBlock_add_joint_local
      states states coefficient _ _
  refine Q'.eqv_trans _
    (HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint +
      HalfPow.half *
        finiteJointDirichletBlock states states coefficient
          (fun left right => joint right left)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finiteJointDirichletBlock_scale_joint_local
        states states coefficient HalfPow.half joint)
      (finiteJointDirichletBlock_scale_joint_local
        states states coefficient HalfPow.half
        (fun left right => joint right left))
  refine Q'.eqv_trans _
    (HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint +
      HalfPow.half *
        finiteJointDirichletBlock states states coefficient joint) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (finiteJointDirichletBlock_transpose_eqv
          states coefficient joint))
  · exact ExpNeg.two_halves
      (finiteJointDirichletBlock states states coefficient joint)

/-! ## 2. The symmetric arbitrary-cutoff routed load -/

/-- Arithmetic average of the two directed routed loads on one unoriented
edge. -/
def centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing source target +
    HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
        routing target source

theorem centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad_symm
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
        routing source target ≈
      centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
        routing target source := by
  unfold centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
  exact Q'.add_comm_eqv _ _

theorem centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
        routing source target := by
  unfold centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_nonnegative
        routing source target))
    (Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_nonnegative
        routing target source))

def centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    coefficient
    (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad routing)

/-- Transpose averaging changes no routed Dirichlet energy. -/
theorem centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet_eqv_original
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
        routing coefficient ≈
      centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
        routing coefficient := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw K 0
  let load := centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad routing
  have haverage := finiteJointDirichletBlock_averageTranspose_eqv
    states coefficient load
  unfold centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
    centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualRoutedRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock states states coefficient load) _ haverage ?_
  exact finiteJointDirichletBlock_joint_congr_local
    states states coefficient _ _
    (fun source _ target _ =>
      Q'.eqv_symm
        (Q'.mul_one_eqv
          (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
            routing source target)))

theorem centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_symmetricRoutedRawLoadedDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance
        w hw K coefficient ≤
      centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
        routing coefficient := by
  exact Q'.le_trans' _ _ _
    (centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawLoadedDirichlet
      routing coefficient)
    (Q'.ge_of_eqv
      (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet_eqv_original
        routing coefficient))

/-! ## 3. Symmetric physical capacity -/

theorem centralPhysicalFiniteKernel_symm_on_vacuumSector
    {w : Q'} {hw : (0 : Q') ≤ w} {K source target : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (htarget : target ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    centralPhysicalFiniteKernel w hw K 0 source target ≈
      centralPhysicalFiniteKernel w hw K 0 target source := by
  have hsourcePositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K 0
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K 0 hsource)
  have htargetPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K 0
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K 0 htarget)
  unfold centralPhysicalFiniteKernel
  exact centralNormalizedPhysicalReflectedKernel_symm
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
    (mem_centralPositiveHalfStates_iff.mp htargetPositive).1

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

/-- Pointwise capacity for the exact symmetric routed load. -/
structure CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1 where
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt

theorem sharedFloor_mul_symmetricRoutedRawLoadedDirichlet_le_half_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
        hw K rayCapacity routing)
    (coefficient : Nat → Q') :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
          routing coefficient ≤
      HalfPow.half * finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet
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
    (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad routing)
    (fun source target => HalfPow.half *
      centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target)
    capacity.edge_capacity
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (finiteJointDirichletBlock_scale_joint_local
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K 0)
        coefficient HalfPow.half
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0)))

/-- Exact energy preservation lets symmetric pointwise capacity return the
unchanged residual-coercivity object consumed downstream. -/
def toOffRayResidualCoercivityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
      hw K rayCapacity where
  residual_coercivity := fun coefficient => by
    have hresidual :=
      centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_symmetricRoutedRawLoadedDirichlet
        routing coefficient
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
      hresidual
      (Q'.le_of_lt
        (centralLowerExcitedSpinCubeSharedCoercivityFloor_pos rayCapacity))
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.sharedFloor_mul_symmetricRoutedRawLoadedDirichlet_le_half_physicalDirichlet
        coefficient)

end CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt

/-! ## 4. Three oriented blocks suffice for any explicit old/new partition -/

/-- A constructive old/new partition and only three oriented capacity fields.
The missing new--old field is a theorem. -/
structure CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (old new : List Nat) : Type 1 where
  cover : ∀ state,
    state ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0 →
      state ∈ old ∨ state ∈ new
  old_old : ∀ source, source ∈ old →
    ∀ target, target ∈ old →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target
  old_new : ∀ source, source ∈ old →
    ∀ target, target ∈ new →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target
  new_new : ∀ source, source ∈ new →
    ∀ target, target ∈ new →
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt

/-- Load and physical-kernel symmetry derive the omitted reverse cross-block
orientation exactly. -/
theorem new_old
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    {old new : List Nat}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt
        hw K rayCapacity routing old new)
    (source : Nat)
    (hsourceSector : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (hsourceNew : source ∈ new)
    (target : Nat)
    (htargetSector : target ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K 0)
    (htargetOld : target ∈ old) :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
          routing source target ≤
      HalfPow.half * centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target := by
  have hreversed := capacity.old_new target htargetOld source hsourceNew
  have hleft :
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing source target ≈
        centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
            routing target source :=
    Q'.mul_eqv_congr_left
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity) _ _
      (centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad_symm
        routing source target)
  have hright :
      HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 target source ≈
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target :=
    Q'.mul_eqv_congr_left HalfPow.half _ _
      (centralPhysicalFiniteKernel_symm_on_vacuumSector
        htargetSector hsourceSector)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hreversed (Q'.le_of_eqv hright))

/-- The three oriented block fields compile to all-pair symmetric capacity. -/
def toSymmetricRoutedFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    {old new : List Nat}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt
        hw K rayCapacity routing old new) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget => by
    cases capacity.cover source hsource with
    | inl hsourceOld =>
        cases capacity.cover target htarget with
        | inl htargetOld =>
            exact capacity.old_old source hsourceOld target htargetOld
        | inr htargetNew =>
            exact capacity.old_new source hsourceOld target htargetNew
    | inr hsourceNew =>
        cases capacity.cover target htarget with
        | inl htargetOld =>
            exact capacity.new_old
              source hsource hsourceNew target htarget htargetOld
        | inr htargetNew =>
            exact capacity.new_new source hsourceNew target htargetNew

/-- Three oriented estimates therefore return the existing residual
coercivity certificate with no fourth cross-orientation hypothesis. -/
def toOffRayResidualCoercivityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    {old new : List Nat}
    (capacity :
      CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt
        hw K rayCapacity routing old new) :
    CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt
      hw K rayCapacity :=
  capacity.toSymmetricRoutedFlowCapacityAt.toOffRayResidualCoercivityAt

end CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt

/-! ## 5. Exact adjacent-cutoff partition and the completed consumer -/

/-- Cofinal symmetric routed capacity on the literal adjacent-cutoff
partition.  Only three oriented estimates are data; the reverse cross block
is generated by symmetry at every cutoff. -/
structure FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  old_old : ∀ K, (hK : rayCapacity.start ≤ K) →
    ∀ source, source ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
    ∀ target, target ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor
          (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
            rayCapacity K hK) *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
          (routing K hK) source target ≤
      HalfPow.half * centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target
  old_new : ∀ K, (hK : rayCapacity.start ≤ K) →
    ∀ source, source ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
    ∀ target, target ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor
          (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
            rayCapacity K hK) *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
          (routing K hK) source target ≤
      HalfPow.half * centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target
  new_new : ∀ K, (hK : rayCapacity.start ≤ K) →
    ∀ source, source ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
    ∀ target, target ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w (Q'.le_of_lt hw) (K - 1) K 0 →
      centralLowerExcitedSpinCubeSharedCoercivityFloor
          (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
            rayCapacity K hK) *
        centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad
          (routing K hK) source target ≤
      HalfPow.half * centralPhysicalFiniteKernel
        w (Q'.le_of_lt hw) K 0 source target

namespace FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity

/-- The literal embedded-old/new-block decomposition covers the current
vacuum sector constructively. -/
def threeBlockCapacityAt
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity
        hw rayCapacity)
    (K : Nat) (hK : rayCapacity.start ≤ K) :
    CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt
      hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt rayCapacity K hK)
      (family.routing K hK)
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w (Q'.le_of_lt hw) (K - 1) K 0)
      (centralPhysicalFiniteVacuumSectorNewBlockIndices
        w (Q'.le_of_lt hw) (K - 1) K 0) where
  cover := fun state hstate => by
    by_cases hold : state ∈
        centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w (Q'.le_of_lt hw) (K - 1) K 0
    · exact Or.inl hold
    · exact Or.inr
        ((mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mpr
          ⟨hstate, hold⟩)
  old_old := family.old_old K hK
  old_new := family.old_new K hK
  new_new := family.new_new K hK

/-- Three oriented adjacent-block estimates produce the existing cofinal
residual-coercivity family. -/
def toCofinalResidualCoercivity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualCoercivity hw rayCapacity where
  residual := fun K hK =>
    (family.threeBlockCapacityAt K hK).toOffRayResidualCoercivityAt

/-- The symmetry-reduced adjacent-block proof reaches the same concrete
completed carrier/transfer/vacuum strict-contraction datum. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toCompletedStrictContractionData
    hw0 hw1 family.toCofinalResidualCoercivity

end FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity

/-! ## Axiom audit -/

#print axioms
  centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowLoad_symm
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedRawLoadedDirichlet_eqv_original
#print axioms
  centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_symmetricRoutedRawLoadedDirichlet
#print axioms centralPhysicalFiniteKernel_symm_on_vacuumSector
#print axioms
  CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedFlowCapacityAt.toOffRayResidualCoercivityAt
#print axioms
  CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt.new_old
#print axioms
  CentralLowerExcitedSpinCubeOffRayResidualSymmetricRoutedThreeBlockCapacityAt.toOffRayResidualCoercivityAt
#print axioms
  FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity.threeBlockCapacityAt
#print axioms
  FixedNomeCofinalSpinCubeOffRayResidualSymmetricAdjacentBlockRoutingCapacity.toCompletedStrictContractionData

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSymmetricRouting
