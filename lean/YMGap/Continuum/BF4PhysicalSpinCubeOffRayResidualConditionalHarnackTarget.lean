/-
# The explicit conditional-Harnack target for arbitrary-cutoff off-ray flow

Cancelling the positive stationary mass of a directed edge source is useful
only if the resulting relative traffic is exposed in variables that the BF4
local geometry can estimate.  For every listed off-ray endpoint pair whose
loop-erased positive path traverses the selected directed edge, this module
proves the exact formula

  weight(endpointLeft) / weight(edgeSource)
    * weight(endpointRight) * pathLength.

Summing these literal path-incidence terms gives exactly the relative source
flow load.  Hence conditional congestion is equivalent, not merely implied,
to one explicit projective-weight/Harnack inequality at every directed edge.
The equivalence is lossless in both directions and is inhabited at every
finite cutoff by the existing finite carrier-linear certificate.

No cofinal Harnack family is inhabited here.  No thermodynamic or continuum
limit, continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualLinearCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact path-incidence expansion of one endpoint-pair load -/

private theorem weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
    {State : Type} [DecidableEq State]
    (load : Q') (source target : State) :
    ∀ edges : List (State × State), edges.Nodup →
      weightedDirectedEdgeLoad
          (edges.map (fun edge => (edge, load))) source target ≈
        if (source, target) ∈ edges then load else 0
  | [], _ => Q'.eqv_refl 0
  | edge :: rest, hnodup => by
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
          Q'.eqv_trans _ (if (source, target) ∈ rest then load else 0) _
            (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
              load source target rest hparts.2)
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
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
                load source target rest hparts.2)
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
              (weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
                load source target rest hparts.2)
              (by rw [if_neg htailMem]; exact Q'.eqv_refl 0)
          change 0 + weightedDirectedEdgeLoad
              (rest.map (fun traversed => (traversed, load)))
              source target ≈ 0
          exact Q'.eqv_trans _ (0 + 0) _
            (Q'.add_eqv_congr_left 0 _ _ htail)
            (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- A listed residual endpoint pair contributes exactly its stationary
product times its simple-path length when the selected directed edge occurs,
and zero otherwise. -/
theorem centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_eqv_indicator
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (pair : Nat × Nat)
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)
    (source target : Nat) :
    weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target ≈
      let hfull :=
        centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
      let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 pair.1 pair.2 hfull.1 hfull.2
      if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
        (centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0 := by
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  unfold centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
  rw [dif_pos hfull.1, dif_pos hfull.2]
  exact weightedDirectedEdgeLoad_constantMap_eqv_indicator_local
    ((centralPhysicalFiniteWeight w hw K 0 pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat
        (PositiveKernelChainIn.edgeLength
          (centralPhysicalFiniteVacuumSectorSimplePositivePath
            w hw K 0 pair.1 pair.2 hfull.1 hfull.2)))
    source target
    (PositiveKernelChainIn.directedEdges
      (centralPhysicalFiniteVacuumSectorSimplePositivePath
        w hw K 0 pair.1 pair.2 hfull.1 hfull.2))
    (centralPhysicalFiniteVacuumSectorSimplePositivePath_directedEdges_nodup
      w hw K pair.1 pair.2 hfull.1 hfull.2)

/-! ## 2. Explicit relative endpoint weights and Harnack terms -/

/-- Stationary mass of an endpoint relative to the positive stationary mass
of the selected directed edge source. -/
def centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
    (w : Q') (hw : (0 : Q') ≤ w) (K source endpoint : Nat) : Q' :=
  if hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0 then
    Q'.divPos
      (centralPhysicalFiniteWeight w hw K 0 endpoint)
      (centralPhysicalFiniteWeight w hw K 0 source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource)
  else 0

theorem centralPhysicalFiniteWeight_mul_endpointWeightRatio_eqv_endpointWeight
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (endpoint : Nat) :
    centralPhysicalFiniteWeight w hw K 0 source *
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
          w hw K source endpoint ≈
      centralPhysicalFiniteWeight w hw K 0 endpoint := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
  rw [dif_pos hsource]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (centralPhysicalFiniteWeight w hw K 0 source)
      (Q'.divPos
        (centralPhysicalFiniteWeight w hw K 0 endpoint)
        (centralPhysicalFiniteWeight w hw K 0 source) hweight))
    (Q'.divPos_mul_eqv _ _ hweight)

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos denominator hdenominator) heq

private theorem divPos_product_eqv_ratio_product_local
    (left right length denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos ((left * right) * length)
        denominator hdenominator ≈
      (Q'.divPos left denominator hdenominator * right) * length := by
  unfold Q'.divPos
  show ((((left * right) * length) *
      Q'.recipPos denominator hdenominator) : Q') ≈
    (((left * Q'.recipPos denominator hdenominator) * right) * length)
  show
    ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).num *
      ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).den : Int)) =
    ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).num *
      ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).den : Int))
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-- The literal source-cancelled contribution of one residual endpoint pair
to one directed edge, written as a projective stationary ratio. -/
def centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat)
    (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 pair.1 pair.2 hfull.1 hfull.2
    if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
          w hw K source pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  else 0

/-- The quotient-defined pair demand is exactly the explicit
projective-weight/path-incidence term. -/
theorem centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand_eqv_harnackTerm
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
        w hw K source target pair ≈
      centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
        w hw K source target pair := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K 0 pair.1 pair.2 hfull.1 hfull.2
  unfold
    centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  unfold
    centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
  rw [dif_pos hpair]
  change Q'.divPos
      (weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target)
      (centralPhysicalFiniteWeight w hw K 0 source) hweight ≈
    if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
          w hw K source pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge]
    have hcontribution :=
      centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_eqv_indicator
        pair hpair source target
    change weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target ≈
      if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
        (centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0 at hcontribution
    rw [if_pos hedge] at hcontribution
    refine Q'.eqv_trans _
      (Q'.divPos
        ((centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path))
        (centralPhysicalFiniteWeight w hw K 0 source) hweight) _ ?_ ?_
    · exact divPos_eqv_congr_numerator_local hweight hcontribution
    have hratio :
        Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 pair.1)
            (centralPhysicalFiniteWeight w hw K 0 source) hweight =
          centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
            w hw K source pair.1 := by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
      rw [dif_pos hsource]
    rw [← hratio]
    exact divPos_product_eqv_ratio_product_local _ _ _ _ hweight
  · rw [if_neg hedge]
    have hcontribution :=
      centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_eqv_indicator
        pair hpair source target
    change weightedDirectedEdgeLoad
        (centralLowerExcitedSpinCubeOffRayResidualWeightedPathOccurrences
          w hw K pair.1 pair.2)
        source target ≈
      if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
        (centralPhysicalFiniteWeight w hw K 0 pair.1 *
            centralPhysicalFiniteWeight w hw K 0 pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0 at hcontribution
    rw [if_neg hedge] at hcontribution
    have hzero := divPos_eqv_congr_numerator_local hweight hcontribution
    refine Q'.eqv_trans _ (Q'.divPos 0
      (centralPhysicalFiniteWeight w hw K 0 source) hweight) _ hzero ?_
    unfold Q'.divPos
    exact Q'.zero_mul_eqv _

/-! ## 3. The exact summed Harnack target -/

def centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
      w hw K source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad_eqv_harnackLoad
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
        w hw K source target ≈
      centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
        w hw K source target := by
  unfold centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
    centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
  apply listQSum_congr_on
  intro pair hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand_eqv_harnackTerm
      hsource target pair hpair

/-- Conditional congestion is equivalent to the explicit Harnack target.
This is the exact local analytic obligation left by the current routing. -/
theorem centralLowerExcitedSpinCubeOffRayResidualConditionalCongestion_iff_harnackTarget
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {source : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
    (target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  have heq :=
    centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad_eqv_harnackLoad
      hsource target
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ (Q'.eqv_symm heq)))
      h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity)
          _ _ heq))
      h

/-! ## 4. Lossless finite and cofinal compilers -/

structure CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
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
          centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt

def ofConditionalCongestionAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (congestion :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualConditionalCongestion_iff_harnackTarget
      hsource target).mp
      (congestion.edge_capacity source hsource target htarget)

def toConditionalCongestionAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (harnack :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualConditionalCongestion_iff_harnackTarget
      hsource target).mpr
      (harnack.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt

/-- Every finite cutoff has a concrete Harnack-target inhabitant.  Its
restricted ray floor still depends on the cutoff. -/
def centralLowerExcitedSpinCubeFiniteLinearConditionalHarnackAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
      hw K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
        rayCapacity) :=
  CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt.ofConditionalCongestionAt
    (centralLowerExcitedSpinCubeFiniteLinearConditionalCongestionAt
      rayCapacity)

/-- Strong-coupling specialization of the finite explicit Harnack target. -/
def anchorCentralSpinCubeFiniteLinearConditionalHarnackAt
    (K : Nat) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
      (by decide : (0 : Q') <
        YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
      K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
        (YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeFiniteRayCapacityAt
          K)) :=
  centralLowerExcitedSpinCubeFiniteLinearConditionalHarnackAt
    (YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeFiniteRayCapacityAt
      K)

structure FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  harnack : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack

def toConditionalCongestion
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion
      hw rayCapacity where
  congestion := fun K hK =>
    (family.harnack K hK).toConditionalCongestionAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  family.toConditionalCongestion.toCompletedStrictContractionData hw0 hw1

end FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_eqv_indicator
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralPhysicalFiniteWeight_mul_endpointWeightRatio_eqv_endpointWeight
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand_eqv_harnackTerm
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad_eqv_harnackLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralLowerExcitedSpinCubeOffRayResidualConditionalCongestion_iff_harnackTarget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt.ofConditionalCongestionAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt.toConditionalCongestionAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.centralLowerExcitedSpinCubeFiniteLinearConditionalHarnackAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.anchorCentralSpinCubeFiniteLinearConditionalHarnackAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack.toCompletedStrictContractionData
