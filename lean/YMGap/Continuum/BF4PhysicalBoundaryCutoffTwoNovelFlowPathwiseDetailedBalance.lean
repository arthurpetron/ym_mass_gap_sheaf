/-
# Pathwise detailed balance for the cutoff-two novel BF4 flow

The conditional-Harnack target contains the stationary ratio between the
left endpoint of a routed pair and the source of a traversed edge.  This
module transports that ratio along the actual positive-kernel path.

For one positive directed edge, detailed balance proves

  weight(left) / weight(right)
    = conditional(right,left) / conditional(left,right).

Recursion over the Type-level positive chain then telescopes the stationary
endpoint ratio into the product of these reverse/forward conditional ratios.
This is an exact identity only.  No Harnack upper bound, uniform congestion
estimate, thermodynamic/continuum construction, or Clay conclusion is
asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Indexed detailed balance and bidirectional positivity -/

/-- Detailed balance on the exact finite index carrier used by the edge-load
construction. -/
theorem cutoffTwoEdgeLoadConditionalKernel_detailedBalance
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoEdgeLoadWeight later left *
        cutoffTwoEdgeLoadConditionalKernel later left right ≈
      cutoffTwoEdgeLoadWeight later right *
        cutoffTwoEdgeLoadConditionalKernel later right left := by
  have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 hleft)
  have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
    cutoffTwoHalfCoupling (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 hright)
  unfold cutoffTwoEdgeLoadWeight cutoffTwoEdgeLoadConditionalKernel
    centralPhysicalFiniteWeight
  exact centralPhysicalConditionalKernel_detailed_balance
    hleftPositive hrightPositive

/-- Positivity of an indexed joint entry is symmetric on the vacuum-sector
carrier. -/
theorem cutoffTwoEdgeLoadKernel_reverse_pos_of_pos
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    (0 : Q') < cutoffTwoEdgeLoadKernel later right left := by
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
          cutoffTwoHalfCoupling (by decide) later 0 left right = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hleft hright).2 hforward
  have hreverseAdjacent :
      centralPhysicalFiniteSupportAdjacentB
          cutoffTwoHalfCoupling (by decide) later 0 right left = true :=
    Eq.trans
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        cutoffTwoHalfCoupling (by decide) later 0 left right).symm
      hadjacent
  exact
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hright hleft).1 hreverseAdjacent

/-- A positive directed joint edge has positive conditional probabilities in
both orientations. -/
theorem cutoffTwoEdgeLoadConditionalKernel_reverse_pos_of_kernel_pos
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    (0 : Q') < cutoffTwoEdgeLoadConditionalKernel later right left := by
  exact cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos hright
    (cutoffTwoEdgeLoadKernel_reverse_pos_of_pos
      hleft hright hforward)

/-! ## 2. One-edge projective ratio -/

private theorem divPos_eqv_divPos_of_cross
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul hq hcancel

/-- On one positive directed edge, the stationary-weight ratio is exactly the
reverse conditional probability divided by the forward one. -/
theorem cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    Q'.divPos
        (cutoffTwoEdgeLoadWeight later left)
        (cutoffTwoEdgeLoadWeight later right)
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (w := cutoffTwoHalfCoupling) (hw := by decide) hright) ≈
      Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later right left)
        (cutoffTwoEdgeLoadConditionalKernel later left right)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          hleft hforward) := by
  apply divPos_eqv_divPos_of_cross
  have hdetailed :=
    cutoffTwoEdgeLoadConditionalKernel_detailedBalance hleft hright
  exact Q'.eqv_trans _ _ _ hdetailed
    (Q'.mul_comm_eqv
      (cutoffTwoEdgeLoadWeight later right)
      (cutoffTwoEdgeLoadConditionalKernel later right left))

/-- The endpoint/source ratio used by the conditional-Harnack load has the
same one-edge reverse/forward conditional form. -/
theorem cutoffTwoNovelEndpointWeightRatioAtSource_eqv_oneStep
    {later left right : Nat}
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    (hright : right ∈ cutoffTwoEdgeLoadFullStates later)
    (hforward : (0 : Q') < cutoffTwoEdgeLoadKernel later left right) :
    cutoffTwoNovelEndpointWeightRatioAtSource later right left ≈
      Q'.divPos
        (cutoffTwoEdgeLoadConditionalKernel later right left)
        (cutoffTwoEdgeLoadConditionalKernel later left right)
        (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
          hleft hforward) := by
  unfold cutoffTwoNovelEndpointWeightRatioAtSource
  rw [dif_pos hright]
  exact cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
    hleft hright hforward

/-! ## 3. Telescoping along a positive path -/

namespace PositiveKernelChainIn

/-- The final vertex of a positive chain remains in its support whenever its
initial vertex does. -/
def lastMem {State : Type} {kernel : State → State → Q'}
    {support : List State} :
    {first last : State} → first ∈ support →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        kernel support first last →
      last ∈ support
  | _, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
        hfirst
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        _ hnext rest =>
        lastMem hnext rest

end PositiveKernelChainIn

/-- Product of reverse/forward conditional transition ratios along a literal
positive-kernel path. -/
def cutoffTwoNovelPathReverseForwardProduct (later : Nat) :
    {first last : Nat} →
      (hfirst : first ∈ cutoffTwoEdgeLoadFullStates later) →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        (cutoffTwoEdgeLoadKernel later)
        (cutoffTwoEdgeLoadFullStates later) first last → Q'
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
        1
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest =>
      Q'.divPos
          (cutoffTwoEdgeLoadConditionalKernel later next first)
          (cutoffTwoEdgeLoadConditionalKernel later first next)
          (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
            hfirst positive) *
        cutoffTwoNovelPathReverseForwardProduct later hnext rest

private theorem divPos_chain_eqv
    (first middle last : Q')
    (hmiddle : (0 : Q') < middle)
    (hlast : (0 : Q') < last) :
    Q'.divPos first last hlast ≈
      Q'.divPos first middle hmiddle *
        Q'.divPos middle last hlast := by
  apply divPos_eqv_of_eqv_mul hlast
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (Q'.divPos first middle hmiddle *
      (Q'.divPos middle last hlast * last)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv _ _ _
  refine Q'.eqv_trans _
    (Q'.divPos first middle hmiddle * middle) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.divPos_mul_eqv middle last hlast)
  exact Q'.divPos_mul_eqv first middle hmiddle

/-- The stationary ratio between the endpoints of a positive chain is the
exact product of reverse/forward conditional ratios along the chain. -/
theorem cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct
    (later : Nat) :
    {first last : Nat} →
      (hfirst : first ∈ cutoffTwoEdgeLoadFullStates later) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          (cutoffTwoEdgeLoadKernel later)
          (cutoffTwoEdgeLoadFullStates later) first last) →
      cutoffTwoNovelEndpointWeightRatioAtSource later last first ≈
        cutoffTwoNovelPathReverseForwardProduct later hfirst path
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => by
      have hweight := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) hfirst
      unfold cutoffTwoNovelEndpointWeightRatioAtSource
        cutoffTwoNovelPathReverseForwardProduct
      rw [dif_pos hfirst]
      exact divPos_eqv_of_eqv_mul hweight
        (Q'.eqv_symm
          (Q'.one_mul_eqv (cutoffTwoEdgeLoadWeight later first)))
  | first, last, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      have hlast := PositiveKernelChainIn.lastMem hnext rest
      have hnextWeight := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) hnext
      have hlastWeight := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) hlast
      unfold cutoffTwoNovelEndpointWeightRatioAtSource
      rw [dif_pos hlast]
      refine Q'.eqv_trans _
        (Q'.divPos
            (cutoffTwoEdgeLoadWeight later first)
            (cutoffTwoEdgeLoadWeight later next) hnextWeight *
          Q'.divPos
            (cutoffTwoEdgeLoadWeight later next)
            (cutoffTwoEdgeLoadWeight later last) hlastWeight) _ ?_ ?_
      · exact divPos_chain_eqv _ _ _ hnextWeight hlastWeight
      unfold cutoffTwoNovelPathReverseForwardProduct
      refine Q'.eqv_trans _
        (Q'.divPos
            (cutoffTwoEdgeLoadConditionalKernel later next first)
            (cutoffTwoEdgeLoadConditionalKernel later first next)
            (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
              hfirst positive) *
          Q'.divPos
            (cutoffTwoEdgeLoadWeight later next)
            (cutoffTwoEdgeLoadWeight later last) hlastWeight) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward
            hfirst hnext positive)
      have hrest :=
        cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct
          later hnext rest
      unfold cutoffTwoNovelEndpointWeightRatioAtSource at hrest
      rw [dif_pos hlast] at hrest
      exact Q'.mul_eqv_congr_left _ _ _
        hrest

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance.cutoffTwoEdgeLoadConditionalKernel_detailedBalance
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance.cutoffTwoEdgeLoadKernel_reverse_pos_of_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance.cutoffTwoNovelEndpointWeightRatioAtSource_eqv_oneStep
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance.cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct
