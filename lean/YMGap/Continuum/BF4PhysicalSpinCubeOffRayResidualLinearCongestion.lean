/-
# Linear carrier congestion for the spin-cube off-ray residual flow

The explicit residual flow charges one loop-erased positive-kernel path for
each ordered endpoint demand.  A simple path uses every directed edge at most
once and has length at most the finite vacuum-sector carrier size.  Therefore
every directed residual load is bounded by the carrier size times the exact
stationary-product mass of the three residual endpoint blocks.

This reduces the remaining pointwise capacity family to one scalar ratio:

  sharedFloor * (1 + sectorSize * residualEndpointMass)
    <= half * finitePositiveEdgeFloor.

That ratio compiles to the pointwise residual-flow capacity and hence to full
finite-sector pairwise coercivity.  No cutoff-uniform ratio is proved here;
the displayed carrier growth and finite edge floor remain explicit.

No full uniform gap, thermodynamic or continuum limit, continuum QFT, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One simple residual path charges a directed edge at most once -/

private theorem directedEdges_ofSupportedWalk_local
    {State : Type} [DecidableEq State]
    (adjacent : State → State → Bool)
    (kernel : State → State → Q') (support : List State)
    (edgePositive : ∀ first next,
      first ∈ support → next ∈ support →
      adjacent first next = true → (0 : Q') < kernel first next) :
    ∀ {first last : State} (hfirst : first ∈ support)
      (path : FiniteBoolGraphSimplePaths.Walk
        (supportedEdge adjacent support) first last),
      PositiveKernelChainIn.directedEdges
          (BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk
            adjacent kernel support edgePositive hfirst path) =
        FiniteBoolGraphSimplePaths.Walk.directedEdges path
  | _, _, _, FiniteBoolGraphSimplePaths.Walk.single _ => rfl
  | first, _, hfirst,
      FiniteBoolGraphSimplePaths.Walk.cons hedge rest => by
      have hparts := (Bool.and_eq_true _ _).mp hedge
      have hnext : rest.start ∈ support := of_decide_eq_true hparts.2
      simp only [
        BF4PhysicalFiniteVacuumSectorSimplePathScale.PositiveKernelChainIn.ofSupportedWalk,
        PositiveKernelChainIn.directedEdges,
        FiniteBoolGraphSimplePaths.Walk.directedEdges]
      exact congrArg (List.cons (first, rest.start))
        (directedEdges_ofSupportedWalk_local
          adjacent kernel support edgePositive hnext rest)

theorem centralPhysicalFiniteVacuumSectorSimplePositivePath_directedEdges_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (PositiveKernelChainIn.directedEdges
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 left right hleft hright)).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorSimplePositivePath
  rw [directedEdges_ofSupportedWalk_local]
  exact FiniteBoolGraphSimplePaths.Walk.directedEdges_nodup_of_vertices_nodup
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw K 0 left right hleft hright).walk
    (centralPhysicalFiniteVacuumSectorSimpleWalk
      w hw K 0 left right hleft hright).nodup

private theorem weightedDirectedEdgeLoad_constantMap_le_local
    {State : Type} [DecidableEq State]
    (edges : List (State × State)) (hnodup : edges.Nodup)
    (load : Q') (hload : (0 : Q') ≤ load)
    (source target : State) :
    weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≤ load := by
  have heq : weightedDirectedEdgeLoad
        (edges.map (fun edge => (edge, load))) source target ≈
      if (source, target) ∈ edges then load else 0 := by
    induction edges with
    | nil => exact Q'.eqv_refl 0
    | cons edge rest ih =>
        have hparts := List.nodup_cons.mp hnodup
        simp only [weightedDirectedEdgeLoad, List.map_cons, listQSum,
          weightedDirectedEdgeIndicator]
        by_cases hhead : edge = (source, target)
        · rw [if_pos hhead]
          have hnotmem : (source, target) ∉ rest := by
            intro hmem
            exact hparts.1 (hhead ▸ hmem)
          have hmem : (source, target) ∈ edge :: rest :=
            List.mem_cons.mpr (Or.inl hhead.symm)
          rw [if_pos hmem]
          have htail : weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0 :=
            Q'.eqv_trans _
              (if (source, target) ∈ rest then load else 0) _
              (ih hparts.2)
              (by rw [if_neg hnotmem]; exact Q'.eqv_refl 0)
          change load + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ load
          exact Q'.eqv_trans _ (load + 0) _
            (Q'.add_eqv_congr_left load _ _ htail)
            (Q'.eqv_of_eq (Q'.add_zero' load))
        · rw [if_neg hhead]
          have hne : (source, target) ≠ edge := fun heq => hhead heq.symm
          by_cases htailMem : (source, target) ∈ rest
          · have hmem : (source, target) ∈ edge :: rest :=
              List.mem_cons_of_mem edge htailMem
            rw [if_pos hmem]
            have htail : weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ load :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then load else 0) _
                (ih hparts.2)
                (by rw [if_pos htailMem]; exact Q'.eqv_refl load)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ load
            exact Q'.eqv_trans _ (0 + load) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' load))
          · have hnotmem : (source, target) ∉ edge :: rest := by
              intro hmem
              rcases List.mem_cons.mp hmem with hedge | hrest
              · exact hne hedge
              · exact htailMem hrest
            rw [if_neg hnotmem]
            have htail : weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ 0 :=
              Q'.eqv_trans _
                (if (source, target) ∈ rest then load else 0) _
                (ih hparts.2)
                (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
            change 0 + weightedDirectedEdgeLoad
                (rest.map (fun traversed => (traversed, load)))
                source target ≈ 0
            exact Q'.eqv_trans _ (0 + 0) _
              (Q'.add_eqv_congr_left 0 _ _ htail)
              (Q'.eqv_of_eq (Q'.zero_add' 0))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
  by_cases hmem : (source, target) ∈ edges
  · rw [if_pos hmem]
    exact Q'.le_refl' load
  · rw [if_neg hmem]
    exact hload

theorem centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_le
    (w : Q') (hw : (0 : Q') ≤ w) (K left right source target : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K left right)
        source target ≤
      (centralPhysicalFiniteWeight w hw K 0 left *
          centralPhysicalFiniteWeight w hw K 0 right) *
        Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length := by
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K 0 left right hleft hright
  let pairWeight := centralPhysicalFiniteWeight w hw K 0 left *
    centralPhysicalFiniteWeight w hw K 0 right
  let pathLength := PositiveKernelChainIn.edgeLength path
  let load := pairWeight * Q'.ofNat pathLength
  have hpairWeight0 : (0 : Q') ≤ pairWeight :=
    Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative hw K 0 _)
      (centralPhysicalRowMarginal_nonnegative hw K 0 _)
  have hload0 : (0 : Q') ≤ load :=
    Q'.mul_nonneg _ _ hpairWeight0
      (Q'.ofNat_le_ofNat (Nat.zero_le pathLength))
  have hone := weightedDirectedEdgeLoad_constantMap_le_local
    (PositiveKernelChainIn.directedEdges path)
    (centralPhysicalFiniteVacuumSectorSimplePositivePath_directedEdges_nodup
      w hw K left right hleft hright)
    load hload0 source target
  have hlength : pathLength ≤
      (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le
      w hw K 0 left right hleft hright
  have hscaled : load ≤
      pairWeight * Q'.ofNat
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length :=
    Q'.mul_le_mul_of_nonneg_left _ _ pairWeight
      (Q'.ofNat_le_ofNat hlength) hpairWeight0
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
  rw [dif_pos hleft, dif_pos hright]
  exact Q'.le_trans' _ _ _ hone hscaled

/-! ## 2. Exact stationary-product mass of the residual endpoint list -/

def centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum
    (fun pair =>
      centralPhysicalFiniteWeight w hw K 0 pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum
  apply listQSum_nonnegative_on
  intro pair _hpair
  exact Q'.mul_nonneg _ _
    (centralPhysicalRowMarginal_nonnegative hw K 0 _)
    (centralPhysicalRowMarginal_nonnegative hw K 0 _)

/-! ## 3. Aggregate residual load is linear in carrier size -/

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_eqv_pathLoadSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target ≈
      listQSum
        (fun pair => weightedDirectedEdgeLoad
          (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
            w hw K pair.1 pair.2)
          source target)
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) := by
  unfold centralLowerExcitedSpinCubeOffRayResidualFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences
  unfold weightedDirectedEdgeLoad
  exact listQSum_flatMap _ _ _

theorem centralLowerExcitedSpinCubeOffRayResidualPathLoadSum_le_sizeWeightedPairSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    listQSum
        (fun pair => weightedDirectedEdgeLoad
          (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
            w hw K pair.1 pair.2)
          source target)
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) ≤
      listQSum
        (fun pair =>
          Q'.ofNat
              (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
            (centralPhysicalFiniteWeight w hw K 0 pair.1 *
              centralPhysicalFiniteWeight w hw K 0 pair.2))
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) := by
  apply listQSum_mono
  intro pair hpair
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  have hone :=
    centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_le
      w hw K pair.1 pair.2 source target hfull.1 hfull.2
  exact Q'.le_trans' _ _ _ hone
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralPhysicalFiniteWeight w hw K 0 pair.1 *
          centralPhysicalFiniteWeight w hw K 0 pair.2)
        (Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length)))

theorem centralLowerExcitedSpinCubeOffRayResidualSizeWeightedPairSum_eqv
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    listQSum
        (fun pair =>
          Q'.ofNat
              (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
            (centralPhysicalFiniteWeight w hw K 0 pair.1 *
              centralPhysicalFiniteWeight w hw K 0 pair.2))
        (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) ≈
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K := by
  exact listQSum_mul_left _ _ _

/-- Uniform in the coefficient and in the chosen directed edge: residual load
is at most carrier size times the exact residual endpoint-pair mass. -/
theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize_mul_endpointWeightSum
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target ≤
      Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralLowerExcitedSpinCubeOffRayResidualFlowLoad_eqv_pathLoadSum
        w hw K source target))
    (Q'.le_trans' _ _ _
      (centralLowerExcitedSpinCubeOffRayResidualPathLoadSum_le_sizeWeightedPairSum
        w hw K source target)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (centralLowerExcitedSpinCubeOffRayResidualSizeWeightedPairSum_eqv
            w hw K))
        (Q'.le_refl' _)))

def centralLowerExcitedSpinCubeOffRayResidualLinearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 +
    Q'.ofNat
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K

theorem centralLowerExcitedSpinCubeOffRayResidualLinearCost_pos
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualLinearCost w hw K := by
  unfold centralLowerExcitedSpinCubeOffRayResidualLinearCost
  exact Q'.pos_add_nonneg (by decide)
    (Q'.mul_nonneg _ _
      (Q'.ofNat_le_ofNat (Nat.zero_le _))
      (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_nonnegative
        w hw K))

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_linearCost
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w hw K source target ≤
      centralLowerExcitedSpinCubeOffRayResidualLinearCost w hw K := by
  have hload :=
    centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize_mul_endpointWeightSum
      w hw K source target
  have hadd := Q'.add_le_add_right (0 : Q') 1
    (Q'.ofNat
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K)
    (by decide : (0 : Q') ≤ 1)
  have hcost : Q'.ofNat
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0).length *
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum w hw K ≤
      centralLowerExcitedSpinCubeOffRayResidualLinearCost w hw K := by
    unfold centralLowerExcitedSpinCubeOffRayResidualLinearCost
    rwa [Q'.zero_add'] at hadd
  exact Q'.le_trans' _ _ _ hload hcost

/-! ## 4. One scalar ratio compiles to pointwise residual capacity -/

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

theorem centralLowerExcitedSpinCubeOffRayResidualFlowLoad_pos_implies_kernel_pos
    {w : Q'} (hw : (0 : Q') < w) (K source target : Nat)
    (hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad
        w (Q'.le_of_lt hw) K source target) :
    (0 : Q') < centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 source target := by
  rcases exists_occurrence_of_weightedDirectedEdgeLoad_pos
      (centralLowerExcitedSpinCubeOffRayResidualFlowOccurrences
        w (Q'.le_of_lt hw) K)
      (centralLowerExcitedSpinCubeOffRayResidualOccurrence_load_nonnegative
        w (Q'.le_of_lt hw) K)
      source target hload with
    ⟨occurrence, hoccurrence, hedge⟩
  have hpositive :=
    centralLowerExcitedSpinCubeOffRayResidualOccurrence_kernel_pos
      w (Q'.le_of_lt hw) K occurrence hoccurrence
  simpa only [hedge] using hpositive

/-- A single scalar inequality sufficient for the complete pointwise residual
capacity certificate at one cutoff. -/
structure CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    Type 1 where
  ratio_bound :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
        centralLowerExcitedSpinCubeOffRayResidualLinearCost
          w (Q'.le_of_lt hw) K ≤
      HalfPow.half * centralPhysicalFiniteVacuumSectorEdgeFloor
        w (Q'.le_of_lt hw) K 0

namespace CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt

def toResidualFlowCapacityAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (ratio : CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt
      hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget => by
    let load := centralLowerExcitedSpinCubeOffRayResidualFlowLoad
      w (Q'.le_of_lt hw) K source target
    have hload0 : (0 : Q') ≤ load :=
      centralLowerExcitedSpinCubeOffRayResidualFlowLoad_nonnegative
        w (Q'.le_of_lt hw) K source target
    by_cases hloadPos : (0 : Q') < load
    · have hloadCost : load ≤
          centralLowerExcitedSpinCubeOffRayResidualLinearCost
            w (Q'.le_of_lt hw) K :=
        centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_linearCost
          w (Q'.le_of_lt hw) K source target
      have hshared0 : (0 : Q') ≤
          centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity :=
        Q'.le_of_lt
          (centralLowerExcitedSpinCubeSharedCoercivityFloor_pos rayCapacity)
      have hloadScaled := Q'.mul_le_mul_of_nonneg_left _ _ _
        hloadCost hshared0
      have hkernelPos :=
        centralLowerExcitedSpinCubeOffRayResidualFlowLoad_pos_implies_kernel_pos
          hw K source target hloadPos
      have hfloor :=
        centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
          w (Q'.le_of_lt hw) K 0 source target
          hsource htarget hkernelPos
      have hhalfFloor := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
        hfloor HalfPow.half_nonneg
      exact Q'.le_trans' _ _ _ hloadScaled
        (Q'.le_trans' _ _ _ ratio.ratio_bound hhalfFloor)
    · have hloadNonpos : load ≤ 0 :=
        q_nonpos_of_not_pos_local hloadPos
      have hloadZero : load ≈ 0 :=
        Q'.eqv_of_le_le hloadNonpos hload0
      have hkernel0 : (0 : Q') ≤ centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) K 0 source target := by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          (Q'.le_of_lt hw) K 0 _ _
      have hhalfKernel0 := Q'.mul_nonneg _ _
        HalfPow.half_nonneg hkernel0
      exact Q'.le_trans' _ (0 : Q') _
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity * 0) _
            (Q'.mul_eqv_congr_left _ _ _ hloadZero)
            (Q'.mul_zero_eqv _)))
        hhalfKernel0

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (ratio : CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt
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
  exact ratio.toResidualFlowCapacityAt
    |>.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet coefficient

end CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt

/-! ## 5. The remaining cofinal scalar ratio -/

structure FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  ratio : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualLinearRatio

def toCofinalResidualFlowCapacity
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
      hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity hw rayCapacity where
  flow_capacity := fun K hK =>
    (family.ratio K hK).toResidualFlowCapacityAt

theorem sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family : FixedNomeCofinalSpinCubeOffRayResidualLinearRatio
      hw rayCapacity)
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
  exact family.toCofinalResidualFlowCapacity
    |>.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
      hK coefficient

end FixedNomeCofinalSpinCubeOffRayResidualLinearRatio

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.centralPhysicalFiniteVacuumSectorSimplePositivePath_directedEdges_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_le
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize_mul_endpointWeightSum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.centralLowerExcitedSpinCubeOffRayResidualFlowLoad_pos_implies_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt.toResidualFlowCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.toCofinalResidualFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion.FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
