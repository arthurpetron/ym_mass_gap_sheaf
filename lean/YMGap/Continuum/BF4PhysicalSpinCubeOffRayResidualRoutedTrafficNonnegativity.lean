/-
# Nonnegativity of routed BF4 residual traffic

Every literal routed transition-product summand is nonnegative.  This fact is
independent of a fixed anchor or a matched dynamic trajectory, so it belongs
in a shared compiler rather than inside either application.  The proof follows
the explicit positive path, conditional-kernel ratio, endpoint weight,
exponential path penalty, and directed-edge multiplicity.

No estimate is inhabited here.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward

theorem residualPathReverseForwardProduct_nonnegative
    (w : Q') (hw : (0 : Q') <= w) (K : Nat) :
    {first last : Nat} ->
      (hfirst : first ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0) ->
      (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        first last) ->
      (0 : Q') <=
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hfirst path
  | first, _, hfirst, PositiveKernelChainIn.refl _ => by
      change (0 : Q') <= (1 : Q')
      decide
  | first, _, hfirst,
      PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
      exact Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (Q'.divPos_pos _ _
            (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
              hfirst positive)
            (centralPhysicalFiniteConditionalKernel_reverse_pos_of_kernel_pos
              hfirst hnext positive)))
        (residualPathReverseForwardProduct_nonnegative
          w hw K hnext rest)

theorem residualRoutedDirectedEdgeMultiplicity_nonnegative
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source target : Nat) :
    (0 : Q') <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing left right hleft hright source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  apply weightedDirectedEdgeLoad_nonnegative
  intro occurrence hoccurrence
  obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hoccurrence
  rw [← heq]
  exact (by decide : (0 : Q') <= (1 : Q'))

theorem residualRoutedPathPairConditionalTransitionProductTerm_nonnegative
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) (pair : Nat × Nat) :
    (0 : Q') <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        routing source target pair := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  by_cases hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path pair.1 pair.2 hfull.1 hfull.2
    by_cases hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge]
      dsimp only
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (residualPathReverseForwardProduct_nonnegative
              w hw K hfull.1
              (PositiveKernelChainIn.prefixAtDirectedEdge
                hfull.1 path (source, target) hedge).pathPrefix)
            (Q'.le_of_lt
              (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
                hfull.2)))
          (ExpNeg.ofNat_nonneg'
            (PositiveKernelChainIn.edgeLength path)))
        (residualRoutedDirectedEdgeMultiplicity_nonnegative
          routing pair.1 pair.2 hfull.1 hfull.2 source target)
    · rw [dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity.residualPathReverseForwardProduct_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity.residualRoutedDirectedEdgeMultiplicity_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity.residualRoutedPathPairConditionalTransitionProductTerm_nonnegative
