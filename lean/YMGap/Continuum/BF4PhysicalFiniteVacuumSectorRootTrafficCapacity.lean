/-
# Local root-traffic capacity compiles to full finite coercivity

The rooted flow has already contracted the complete pairwise variance of the
same observable to one coefficient-independent directed-edge load.  This
module makes the remaining analytic comparison pointwise:

  delta * rootFlowLoad(source,target) <= physicalKernel(source,target).

Finite summation compiles that local inequality into full-sector Dirichlet
coercivity.  The local certificate is non-vacuous: at every finite cutoff, the
minimum positive physical edge divided by `1 + totalRootTraffic` supplies a
strictly positive inhabitant.  A cofinal structure isolates the stronger open
claim that one common positive `delta` works at all later cutoffs.

No such cutoff-uniform inhabitant is constructed here.  No completed gap,
thermodynamic or continuum limit, continuum QFT, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTraffic
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-! ## 1. Exact finite total traffic and its positive scalar cost -/

def centralPhysicalFiniteVacuumSectorRootTotalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  listQSum (fun occurrence => occurrence.2)
    (centralPhysicalFiniteVacuumSectorRootFlowOccurrences w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootTotalTraffic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorRootTotalTraffic w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootTotalTraffic
  apply listQSum_nonnegative_on
  intro occurrence hoccurrence
  exact centralPhysicalFiniteVacuumSectorRootOccurrence_load_nonnegative
    w hw K half occurrence hoccurrence

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_le_totalTraffic
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootFlowLoad
        w hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootTotalTraffic w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootFlowLoad
    weightedDirectedEdgeLoad
    centralPhysicalFiniteVacuumSectorRootTotalTraffic
  apply listQSum_mono
  intro occurrence hoccurrence
  unfold weightedDirectedEdgeIndicator
  by_cases hedge : occurrence.1 = (source, target)
  · rw [if_pos hedge]
    exact Q'.le_refl' _
  · rw [if_neg hedge]
    exact centralPhysicalFiniteVacuumSectorRootOccurrence_load_nonnegative
      w hw K half occurrence hoccurrence

def centralPhysicalFiniteVacuumSectorRootTrafficCost
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) : Q' :=
  1 + centralPhysicalFiniteVacuumSectorRootTotalTraffic w hw K half

theorem centralPhysicalFiniteVacuumSectorRootTrafficCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootTrafficCost w hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootTrafficCost
  exact Q'.pos_add_nonneg (by decide)
    (centralPhysicalFiniteVacuumSectorRootTotalTraffic_nonnegative
      w hw K half)

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_le_trafficCost
    (w : Q') (hw : (0 : Q') ≤ w) (K half source target : Nat) :
    centralPhysicalFiniteVacuumSectorRootFlowLoad
        w hw K half source target ≤
      centralPhysicalFiniteVacuumSectorRootTrafficCost w hw K half := by
  have hload :=
    centralPhysicalFiniteVacuumSectorRootFlowLoad_le_totalTraffic
      w hw K half source target
  have hadd := Q'.add_le_add_right (0 : Q') 1
    (centralPhysicalFiniteVacuumSectorRootTotalTraffic w hw K half)
    (by decide : (0 : Q') ≤ 1)
  have htotal :
      centralPhysicalFiniteVacuumSectorRootTotalTraffic w hw K half ≤
        centralPhysicalFiniteVacuumSectorRootTrafficCost w hw K half := by
    unfold centralPhysicalFiniteVacuumSectorRootTrafficCost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hload htotal

theorem centralPhysicalFiniteVacuumSectorRootFlowLoad_pos_implies_kernel_pos
    {w : Q'} (hw : (0 : Q') < w) (K half source target : Nat)
    (hload : (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootFlowLoad
        w (Q'.le_of_lt hw) K half source target) :
    (0 : Q') < centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K half source target := by
  rcases exists_occurrence_of_weightedDirectedEdgeLoad_pos
      (centralPhysicalFiniteVacuumSectorRootFlowOccurrences
        w (Q'.le_of_lt hw) K half)
      (centralPhysicalFiniteVacuumSectorRootOccurrence_load_nonnegative
        w (Q'.le_of_lt hw) K half)
      source target hload with
    ⟨occurrence, hoccurrence, hedge⟩
  have hpositive :=
    centralPhysicalFiniteVacuumSectorRootOccurrence_kernel_pos
      w (Q'.le_of_lt hw) K half occurrence hoccurrence
  simpa only [hedge] using hpositive

/-! ## 2. Pointwise capacity and its finite form compiler -/

structure CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Type 1 where
  delta : Q'
  delta_pos : (0 : Q') < delta
  edge_capacity : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
      delta * centralPhysicalFiniteVacuumSectorRootFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
        centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K half source target

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

namespace CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt

theorem delta_mul_rootRawLoadedDirichlet_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity : CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
      hw K half)
    (coefficient : Nat → Q') :
    capacity.delta *
        centralPhysicalFiniteVacuumSectorRootRawLoadedDirichlet
          w (Q'.le_of_lt hw) K half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  unfold centralPhysicalFiniteVacuumSectorRootRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change capacity.delta *
      finiteJointDirichletBlock
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (fun source target =>
          centralPhysicalFiniteVacuumSectorRootFlowLoad
            w (Q'.le_of_lt hw) K half source target * 1) ≤ _
  change _ ≤ finiteJointDirichletBlock
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half)
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half)
      coefficient
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half)
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le_local
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K half)
    coefficient capacity.delta
    (fun source target =>
      centralPhysicalFiniteVacuumSectorRootFlowLoad
        w (Q'.le_of_lt hw) K half source target * 1)
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half)
    (fun source hsource target htarget =>
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left capacity.delta _ _
            (Q'.mul_one_eqv
              (centralPhysicalFiniteVacuumSectorRootFlowLoad
                w (Q'.le_of_lt hw) K half source target))))
        (capacity.edge_capacity source hsource target htarget))

/-- Pointwise root-traffic capacity gives complete finite-sector pairwise
Dirichlet coercivity at the same positive `delta`. -/
theorem delta_mul_pairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity : CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
      hw K half)
    (coefficient : Nat → Q') :
    capacity.delta * centralPhysicalFiniteVacuumSectorPairwiseVariance
        w (Q'.le_of_lt hw) K half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  have hflow :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawLoadedDirichlet
      w (Q'.le_of_lt hw) K half coefficient
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ capacity.delta
    hflow (Q'.le_of_lt capacity.delta_pos)
  exact Q'.le_trans' _ _ _ hscaled
    (capacity.delta_mul_rootRawLoadedDirichlet_le_physicalDirichlet
      coefficient)

end CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt

/-! ## 3. A concrete positive capacity at every finite cutoff -/

def centralPhysicalFiniteVacuumSectorRootFiniteDelta
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorRootTrafficCost
      w (Q'.le_of_lt hw) K half)
    (centralPhysicalFiniteVacuumSectorRootTrafficCost_pos
      w (Q'.le_of_lt hw) K half)

theorem centralPhysicalFiniteVacuumSectorRootFiniteDelta_pos
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorRootFiniteDelta hw K half := by
  unfold centralPhysicalFiniteVacuumSectorRootFiniteDelta
  exact Q'.divPos_pos _ _ _
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w (Q'.le_of_lt hw) K half)

def centralPhysicalFiniteVacuumSectorRootFiniteCapacityAt
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat) :
    CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt hw K half where
  delta := centralPhysicalFiniteVacuumSectorRootFiniteDelta hw K half
  delta_pos :=
    centralPhysicalFiniteVacuumSectorRootFiniteDelta_pos hw K half
  edge_capacity := fun source hsource target htarget => by
    let load := centralPhysicalFiniteVacuumSectorRootFlowLoad
      w (Q'.le_of_lt hw) K half source target
    let cost := centralPhysicalFiniteVacuumSectorRootTrafficCost
      w (Q'.le_of_lt hw) K half
    let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K half
    let delta := centralPhysicalFiniteVacuumSectorRootFiniteDelta hw K half
    have hload0 : (0 : Q') ≤ load :=
      centralPhysicalFiniteVacuumSectorRootFlowLoad_nonnegative
        w (Q'.le_of_lt hw) K half source target
    by_cases hloadPos : (0 : Q') < load
    · have hloadCost : load ≤ cost :=
        centralPhysicalFiniteVacuumSectorRootFlowLoad_le_trafficCost
          w (Q'.le_of_lt hw) K half source target
      have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ delta
        hloadCost
        (Q'.le_of_lt
          (centralPhysicalFiniteVacuumSectorRootFiniteDelta_pos
            hw K half))
      have hdeltaCost : delta * cost ≈ floor := by
        unfold delta centralPhysicalFiniteVacuumSectorRootFiniteDelta
        exact Q'.divPos_mul_eqv floor cost
          (centralPhysicalFiniteVacuumSectorRootTrafficCost_pos
            w (Q'.le_of_lt hw) K half)
      have hkernelPos :=
        centralPhysicalFiniteVacuumSectorRootFlowLoad_pos_implies_kernel_pos
          hw K half source target hloadPos
      have hfloor :=
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w (Q'.le_of_lt hw) K half source target
          hsource htarget hkernelPos
      exact Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdeltaCost) hfloor)
    · have hloadNonpos : load ≤ 0 :=
        q_nonpos_of_not_pos_local hloadPos
      have hloadZero : load ≈ 0 :=
        Q'.eqv_of_le_le hloadNonpos hload0
      have hkernel0 : (0 : Q') ≤ centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K half source target := by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K half _ _
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv
          (Q'.eqv_trans _ (delta * 0) _
            (Q'.mul_eqv_congr_left delta _ _ hloadZero)
            (Q'.mul_zero_eqv delta)))
        hkernel0

theorem centralPhysicalFiniteVacuumSectorRootFiniteDelta_mul_pairwiseVariance_le_physicalDirichlet
    {w : Q'} (hw : (0 : Q') < w) (K half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorRootFiniteDelta hw K half *
        centralPhysicalFiniteVacuumSectorPairwiseVariance
          w (Q'.le_of_lt hw) K half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  exact
    (centralPhysicalFiniteVacuumSectorRootFiniteCapacityAt hw K half)
      |>.delta_mul_pairwiseVariance_le_physicalDirichlet coefficient

/-! ## 4. The exact cofinal uniform root-traffic frontier -/

structure FixedNomeCofinalVacuumRootTrafficCapacity
    {w : Q'} (hw : (0 : Q') < w) (half : Nat) : Type 1 where
  start : Nat
  delta : Q'
  delta_pos : (0 : Q') < delta
  edge_capacity : ∀ K, start ≤ K → ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
    ∀ target,
    target ∈ centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K half →
      delta * centralPhysicalFiniteVacuumSectorRootFlowLoad
          w (Q'.le_of_lt hw) K half source target ≤
        centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K half source target

namespace FixedNomeCofinalVacuumRootTrafficCapacity

def finiteCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {half : Nat}
    (family : FixedNomeCofinalVacuumRootTrafficCapacity hw half)
    (K : Nat) (hK : family.start ≤ K) :
    CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt hw K half where
  delta := family.delta
  delta_pos := family.delta_pos
  edge_capacity := family.edge_capacity K hK

theorem delta_mul_pairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {half : Nat}
    (family : FixedNomeCofinalVacuumRootTrafficCapacity hw half)
    {K : Nat} (hK : family.start ≤ K)
    (coefficient : Nat → Q') :
    family.delta * centralPhysicalFiniteVacuumSectorPairwiseVariance
        w (Q'.le_of_lt hw) K half coefficient ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) K half)
        coefficient
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half) := by
  exact (family.finiteCapacityAt K hK)
    |>.delta_mul_pairwiseVariance_le_physicalDirichlet coefficient

end FixedNomeCofinalVacuumRootTrafficCapacity

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.centralPhysicalFiniteVacuumSectorRootFlowLoad_le_totalTraffic
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.centralPhysicalFiniteVacuumSectorRootFlowLoad_pos_implies_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt.delta_mul_rootRawLoadedDirichlet_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt.delta_mul_pairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.centralPhysicalFiniteVacuumSectorRootFiniteDelta_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.centralPhysicalFiniteVacuumSectorRootFiniteCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.centralPhysicalFiniteVacuumSectorRootFiniteDelta_mul_pairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.FixedNomeCofinalVacuumRootTrafficCapacity.delta_mul_pairwiseVariance_le_physicalDirichlet
