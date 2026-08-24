/-
# Conditional congestion for the arbitrary-cutoff off-ray residual flow

The physical finite kernel is a symmetric stationary joint law.  On every
source in the canonical vacuum sector it factors exactly as

  joint(source,target)
    = weight(source) * conditional(source,target).

The explicit off-ray residual edge load has the same strictly positive
source weight as a common factor.  This module divides every endpoint-pair
contribution by that source weight, proves that their sum reconstructs the
original flow load after multiplication by the weight, and cancels the
factor from the pointwise capacity inequality.

Thus the viable arbitrary-cutoff frontier is expressed dimensionlessly:
the shared spin-ray floor times relative routed traffic must fit inside half
of the genuine conditional transition probability.  A cofinal family of
these conditional inequalities compiles through the existing exact local
flow path to the actual completed vacuum-sector strict contraction.

No conditional-congestion family is inhabited here.  No thermodynamic or
continuum limit, continuum Yang--Mills theory, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The indexed physical conditional transition -/

def centralPhysicalFiniteConditionalKernel
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) : Q' :=
  centralPhysicalConditionalKernel w hw K half
    (centralPhysicalFiniteStateAt w hw K half source)
    (centralPhysicalFiniteStateAt w hw K half target)

theorem centralPhysicalFiniteConditionalKernel_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteConditionalKernel
      w hw K half source target := by
  unfold centralPhysicalFiniteConditionalKernel
  exact centralPhysicalConditionalKernel_nonnegative hw K half _ _

/-- On the actual finite vacuum sector, the indexed stationary weight times
the indexed conditional transition is the literal physical joint entry. -/
theorem centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
    {w : Q'} {hw : (0 : Q') ≤ w} {K half source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (target : Nat) :
    centralPhysicalFiniteWeight w hw K half source *
        centralPhysicalFiniteConditionalKernel
          w hw K half source target ≈
      centralPhysicalFiniteKernel w hw K half source target := by
  have hsourcePositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K half
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K half hsource)
  unfold centralPhysicalFiniteWeight centralPhysicalFiniteConditionalKernel
    centralPhysicalFiniteKernel
  exact marginal_mul_conditional_eqv_joint hsourcePositive

/-! ## 2. Relative source traffic reconstructs the original load -/

/-- One endpoint pair's contribution to a directed residual edge, divided by
the strictly positive stationary mass of the edge source. -/
def centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat)
    (pair : Nat × Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  else 0

theorem centralPhysicalFiniteWeight_mul_relativePairDemand_eqv_pathLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) (pair : Nat × Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
          w hw K source target pair ≈
      weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target := by
  let weight := centralPhysicalFiniteWeight w hw K 0 source
  let load := weightedDirectedEdgeLoad
    (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
      w hw K pair.1 pair.2)
    source target
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv weight (Q'.divPos load weight hweight))
    (Q'.divPos_mul_eqv load weight hweight)

/-- The dimensionless directed residual load after cancelling the stationary
mass of its source.  The sum retains the exact endpoint-pair witness lineage
and the exact loop-erased positive paths used by the original flow. -/
def centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
      w hw K source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralPhysicalFiniteWeight_mul_relativeSourceFlowLoad_eqv_flowLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
          w hw K source target ≈
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        centralPhysicalFiniteWeight w hw K 0 source *
          centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
            w hw K source target pair)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · unfold centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
    exact Q'.eqv_symm
      (listQSum_mul_left
        (centralPhysicalFiniteWeight w hw K 0 source)
        (centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
          w hw K source target)
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K))
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _hpair
    exact
      centralPhysicalFiniteWeight_mul_relativePairDemand_eqv_pathLoad
        hsource target pair
  exact Q'.eqv_symm
    (centralLowerExcitedSpinCubeOffRayResidualFlowLoad_eqv_pathLoadSum
      w hw K source target)

/-! ## 3. Exact cancellation in the pointwise capacity comparison -/

private theorem mul_swap_middle_eqv (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem le_iff_of_eqv_positive_common_left
    {weight left right reducedLeft reducedRight : Q'}
    (hweight : (0 : Q') < weight)
    (hleft : left ≈ weight * reducedLeft)
    (hright : right ≈ weight * reducedRight) :
    left ≤ right ↔ reducedLeft ≤ reducedRight := by
  constructor
  · intro h
    have hscaled : weight * reducedLeft ≤ weight * reducedRight :=
      Q'.le_trans' _ left _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ right _ h (Q'.le_of_eqv hright))
    exact Q'.le_of_mul_le_mul_left hscaled hweight
  · intro h
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      reducedLeft reducedRight weight h (Q'.le_of_lt hweight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-- The original residual-flow capacity inequality is equivalent, on every
actual source, to a dimensionless relative-traffic/conditional-transition
comparison.  Nothing is bounded by a global edge minimum. -/
theorem centralLowerExcitedSpinCubeOffRayResidualEdgeCapacity_iff_conditionalCongestion
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
    (target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualFlowLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let load := centralLowerExcitedSpinCubeOffRayResidualFlowLoad
    w (Q'.le_of_lt hw) K source target
  let relative :=
    centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
      w (Q'.le_of_lt hw) K source target
  let kernel := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source target
  let conditional := centralPhysicalFiniteConditionalKernel
    w (Q'.le_of_lt hw) K 0 source target
  let floor := centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hleft : floor * load ≈ weight * (floor * relative) := by
    refine Q'.eqv_trans _ (floor * (weight * relative)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_relativeSourceFlowLoad_eqv_flowLoad
            hsource target))
    exact mul_swap_middle_eqv floor weight relative
  have hright : HalfPow.half * kernel ≈
      weight * (HalfPow.half * conditional) := by
    refine Q'.eqv_trans _
      (HalfPow.half * (weight * conditional)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.eqv_symm
          (centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
            hsource target))
    exact mul_swap_middle_eqv HalfPow.half weight conditional
  exact le_iff_of_eqv_positive_common_left hweight hleft hright

/-! ## 4. Conditional congestion compiles to the completed gap -/

structure CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
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
          centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt

def toResidualFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualEdgeCapacity_iff_conditionalCongestion
      hsource target).mpr
      (congestion.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt

structure FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  congestion : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion

def toResidualFlowCapacity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity hw rayCapacity where
  flow_capacity := fun K hK =>
    (family.congestion K hK).toResidualFlowCapacityAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toCompletedStrictContractionData
    hw0 hw1 family.toResidualFlowCapacity

end FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralPhysicalFiniteWeight_mul_conditional_eqv_kernel
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralPhysicalFiniteWeight_mul_relativePairDemand_eqv_pathLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralPhysicalFiniteWeight_mul_relativeSourceFlowLoad_eqv_flowLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.centralLowerExcitedSpinCubeOffRayResidualEdgeCapacity_iff_conditionalCongestion
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt.toResidualFlowCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion.toCompletedStrictContractionData
