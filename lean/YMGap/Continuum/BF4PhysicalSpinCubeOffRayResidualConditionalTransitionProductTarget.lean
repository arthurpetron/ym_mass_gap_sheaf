/-
# The arbitrary-cutoff off-ray conditional transition-product target

Membership of a selected directed edge in a routed positive path determines
a constructive prefix ending at the edge source.  Combining that prefix with
pathwise detailed balance replaces the endpoint/source stationary ratio in
every conditional-Harnack summand by the exact product of reverse/forward
physical conditional-transition ratios along the prefix.

The resulting finite sum is exactly, not approximately, the Harnack load.
Thus a transition-product capacity family is losslessly equivalent to the
existing conditional-congestion family and compiles to the completed strict
transfer contraction.  Finite-cutoff inhabitants are constructed from the
existing finite certificate; no cofinal family is inhabited.

No uniform transition-product estimate, thermodynamic or continuum limit,
continuum Yang--Mills theory, or Clay conclusion is asserted.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive prefix extraction from edge incidence -/

structure PositiveKernelPrefixAtDirectedEdge {State : Type}
    (kernel : State → State → Q') (support : List State)
    (first : State) (edge : State × State) : Type where
  source_mem : edge.1 ∈ support
  target_mem : edge.2 ∈ support
  pathPrefix :
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
      kernel support first edge.1
  edge_positive : (0 : Q') < kernel edge.1 edge.2

namespace PositiveKernelChainIn

/-- Literal directed-edge incidence produces a positive prefix from the
path's first vertex to the selected edge source. -/
def prefixAtDirectedEdge {State : Type}
    [DecidableEq State]
    {kernel : State → State → Q'} {support : List State} :
    {first last : State} →
      (hfirst : first ∈ support) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      (edge : State × State) →
      edge ∈ PositiveKernelChainIn.directedEdges path →
      PositiveKernelPrefixAtDirectedEdge kernel support first edge
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      _, hedge => by
      simp only [PositiveKernelChainIn.directedEdges, List.not_mem_nil]
        at hedge
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest,
      edge, hedge => by
      change edge ∈ (first, next) ::
        PositiveKernelChainIn.directedEdges rest at hedge
      by_cases hhead : edge = (first, next)
      · subst edge
        exact
          { source_mem := hfirst
            target_mem := hnext
            pathPrefix :=
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl
                first
            edge_positive := positive }
      · have htail : edge ∈ PositiveKernelChainIn.directedEdges rest :=
          (List.mem_cons.mp hedge).resolve_left hhead
        let tailPrefix := prefixAtDirectedEdge hnext rest edge htail
        exact
          { source_mem := tailPrefix.source_mem
            target_mem := tailPrefix.target_mem
            pathPrefix :=
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
                positive hnext tailPrefix.pathPrefix
            edge_positive := tailPrefix.edge_positive }

end PositiveKernelChainIn

/-! ## 2. Exact transition-product summands and their sum -/

/-- One Harnack summand with its stationary endpoint/source ratio replaced by
the exact reverse/forward conditional product along the prefix to the chosen
edge source. -/
def centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalTransitionProductTerm
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat)
    (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K then
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw K 0 pair.1 pair.2 hfull.1 hfull.2
    if hedge : (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (source, target) hedge
      (centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hfull.1 prefixData.pathPrefix *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  else 0

/-- Prefix extraction and pathwise detailed balance rewrite one explicit
Harnack term into exact transition-product form. -/
theorem centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm_eqv_transitionProduct
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
        w hw K source target pair ≈
      centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalTransitionProductTerm
        w hw K source target pair := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm
    centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalTransitionProductTerm
  rw [dif_pos hpair, dif_pos hpair]
  have hfull :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
  let path := centralPhysicalFiniteVacuumSectorSimplePositivePath
    w hw K 0 pair.1 pair.2 hfull.1 hfull.2
  change
    (if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      (centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
          w hw K source pair.1 *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0) ≈
    (if hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        hfull.1 path (source, target) hedge
      (centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hfull.1 prefixData.pathPrefix *
        centralPhysicalFiniteWeight w hw K 0 pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0)
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge, dif_pos hedge]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      hfull.1 path (source, target) hedge
    have hratio :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
        w hw K hfull.1 prefixData.pathPrefix
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hratio)
  · rw [if_neg hedge, dif_neg hedge]
    exact Q'.eqv_refl 0

def centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalTransitionProductTerm
      w hw K source target)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K)

theorem centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad_eqv_transitionProductLoad
    (w : Q') (hw : (0 : Q') ≤ w) (K source target : Nat) :
    centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
        w hw K source target ≈
      centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
        w hw K source target := by
  unfold centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
    centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
  apply listQSum_congr_on
  intro pair hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm_eqv_transitionProduct
      source target pair hpair

/-! ## 3. The transition-product target is losslessly local capacity -/

theorem centralLowerExcitedSpinCubeOffRayResidualHarnackTarget_iff_transitionProductTarget
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (source target : Nat) :
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) ↔
      (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity *
          centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target) := by
  have heq :=
    centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad_eqv_transitionProductLoad
      w (Q'.le_of_lt hw) K source target
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

structure CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
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
          centralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductLoad
            w (Q'.le_of_lt hw) K source target ≤
        HalfPow.half * centralPhysicalFiniteConditionalKernel
          w (Q'.le_of_lt hw) K 0 source target

namespace CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt

def ofConditionalHarnackAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (harnack :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualHarnackTarget_iff_transitionProductTarget
      source target).mp
      (harnack.edge_capacity source hsource target htarget)

def toConditionalHarnackAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    (product :
      CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
        hw K rayCapacity) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt
      hw K rayCapacity where
  edge_capacity := fun source hsource target htarget =>
    (centralLowerExcitedSpinCubeOffRayResidualHarnackTarget_iff_transitionProductTarget
      source target).mpr
      (product.edge_capacity source hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt

/-- The explicit transition-product interface is inhabited at every finite
cutoff, with the same cutoff-dependent restricted ray floor. -/
def centralLowerExcitedSpinCubeFiniteLinearConditionalTransitionProductAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
      hw K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
        rayCapacity) :=
  CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt.ofConditionalHarnackAt
    (centralLowerExcitedSpinCubeFiniteLinearConditionalHarnackAt rayCapacity)

def anchorCentralSpinCubeFiniteLinearConditionalTransitionProductAt
    (K : Nat) :
    CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
      (by decide : (0 : Q') <
        YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
      K
      (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity
        (YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeFiniteRayCapacityAt
          K)) :=
  centralLowerExcitedSpinCubeFiniteLinearConditionalTransitionProductAt
    (YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeFiniteRayCapacityAt
      K)

structure FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  product : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt
      hw K
      (FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct

def toConditionalHarnack
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack
      hw rayCapacity where
  harnack := fun K hK => (family.product K hK).toConditionalHarnackAt

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  family.toConditionalHarnack.toCompletedStrictContractionData hw0 hw1

end FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm_eqv_transitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad_eqv_transitionProductLoad
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.centralLowerExcitedSpinCubeOffRayResidualHarnackTarget_iff_transitionProductTarget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt.ofConditionalHarnackAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt.toConditionalHarnackAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.centralLowerExcitedSpinCubeFiniteLinearConditionalTransitionProductAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.anchorCentralSpinCubeFiniteLinearConditionalTransitionProductAt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct.toCompletedStrictContractionData
