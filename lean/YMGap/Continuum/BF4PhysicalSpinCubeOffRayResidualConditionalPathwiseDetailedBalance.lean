/-
# Pathwise detailed balance for arbitrary-cutoff off-ray residual flow

The explicit conditional-Harnack target contains the stationary ratio from
the left endpoint of a routed residual pair to the source of a traversed
edge.  This module transports that ratio along the actual Type-level
positive-kernel path.

For one positive directed edge, finite detailed balance identifies the
stationary ratio with the reverse/forward conditional-transition ratio.
Recursion over the positive path then telescopes the endpoint/source ratio
into the exact product of those local ratios.  This is an equality compiler,
not a Harnack estimate.

No cofinal transition-product bound, uniform completed gap, thermodynamic or
continuum limit, continuum Yang--Mills theory, or Clay conclusion is asserted.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Indexed detailed balance and bidirectional positivity -/

/-- Detailed balance on the arbitrary-cutoff finite index carrier. -/
theorem centralPhysicalFiniteConditionalKernel_detailedBalance
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half) :
    centralPhysicalFiniteWeight w hw K half left *
        centralPhysicalFiniteConditionalKernel w hw K half left right ≈
      centralPhysicalFiniteWeight w hw K half right *
        centralPhysicalFiniteConditionalKernel w hw K half right left := by
  have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K half
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K half hleft)
  have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw K half
    (centralPhysicalFiniteVacuumSectorIndex_lt w hw K half hright)
  unfold centralPhysicalFiniteWeight centralPhysicalFiniteConditionalKernel
  exact centralPhysicalConditionalKernel_detailed_balance
    hleftPositive hrightPositive

/-- Positivity of a finite physical joint entry is symmetric on the vacuum
sector. -/
theorem centralPhysicalFiniteKernel_reverse_pos_of_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hforward : (0 : Q') <
      centralPhysicalFiniteKernel w hw K half left right) :
    (0 : Q') < centralPhysicalFiniteKernel w hw K half right left := by
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
          w hw K half left right = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hleft hright).2 hforward
  have hreverseAdjacent :
      centralPhysicalFiniteSupportAdjacentB
          w hw K half right left = true :=
    Eq.trans
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        w hw K half left right).symm
      hadjacent
  exact
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hright hleft).1 hreverseAdjacent

/-- A positive joint entry has a positive conditional transition in the same
orientation. -/
theorem centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hkernel : (0 : Q') <
      centralPhysicalFiniteKernel w hw K half source target) :
    (0 : Q') <
      centralPhysicalFiniteConditionalKernel w hw K half source target := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  unfold centralPhysicalFiniteConditionalKernel
  rw [centralPhysicalConditionalKernel_eq_divPos hweight]
  exact Q'.divPos_pos _ _ hweight hkernel

/-- A positive directed joint edge has positive conditional transitions in
both orientations. -/
theorem centralPhysicalFiniteConditionalKernel_reverse_pos_of_kernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hforward : (0 : Q') <
      centralPhysicalFiniteKernel w hw K half left right) :
    (0 : Q') <
      centralPhysicalFiniteConditionalKernel w hw K half right left := by
  exact centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos hright
    (centralPhysicalFiniteKernel_reverse_pos_of_pos
      hleft hright hforward)

/-! ## 2. The one-edge projective identity -/

private theorem divPos_eqv_divPos_of_cross_local
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

/-- On one positive directed edge, the stationary ratio is exactly the
reverse conditional transition divided by the forward transition. -/
theorem centralPhysicalFiniteWeightRatio_eqv_conditionalReverseForward
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hforward : (0 : Q') <
      centralPhysicalFiniteKernel w hw K half left right) :
    Q'.divPos
        (centralPhysicalFiniteWeight w hw K half left)
        (centralPhysicalFiniteWeight w hw K half right)
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hright) ≈
      Q'.divPos
        (centralPhysicalFiniteConditionalKernel w hw K half right left)
        (centralPhysicalFiniteConditionalKernel w hw K half left right)
        (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
          hleft hforward) := by
  apply divPos_eqv_divPos_of_cross_local
  have hdetailed :=
    centralPhysicalFiniteConditionalKernel_detailedBalance hleft hright
  exact Q'.eqv_trans _ _ _ hdetailed
    (Q'.mul_comm_eqv
      (centralPhysicalFiniteWeight w hw K half right)
      (centralPhysicalFiniteConditionalKernel w hw K half right left))

/-- The endpoint/source ratio in the off-ray Harnack target has the same
one-edge reverse/forward conditional form. -/
theorem centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_oneStep
    {w : Q'} {hw : (0 : Q') ≤ w} {K left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hforward : (0 : Q') <
      centralPhysicalFiniteKernel w hw K 0 left right) :
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
        w hw K right left ≈
      Q'.divPos
        (centralPhysicalFiniteConditionalKernel w hw K 0 right left)
        (centralPhysicalFiniteConditionalKernel w hw K 0 left right)
        (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
          hleft hforward) := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
  rw [dif_pos hright]
  exact centralPhysicalFiniteWeightRatio_eqv_conditionalReverseForward
    hleft hright hforward

/-! ## 3. Telescoping along the actual positive path -/

namespace PositiveKernelChainIn

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

/-- Product of reverse/forward physical conditional-transition ratios along
one arbitrary-cutoff positive-kernel path. -/
def centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    {first last : Nat} →
      (hfirst : first ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        first last → Q'
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ =>
        1
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest =>
      Q'.divPos
          (centralPhysicalFiniteConditionalKernel w hw K 0 next first)
          (centralPhysicalFiniteConditionalKernel w hw K 0 first next)
          (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
            hfirst positive) *
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hnext rest

private theorem divPos_chain_eqv_local
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

/-- The stationary ratio between the endpoints of a positive path is the
exact product of reverse/forward conditional ratios along that same path. -/
theorem centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    {first last : Nat} →
      (hfirst : first ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          (centralPhysicalFiniteKernel w hw K 0)
          (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
          first last) →
      centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
          w hw K last first ≈
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hfirst path
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => by
      have hweight := centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        hfirst
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
      rw [dif_pos hfirst]
      exact divPos_eqv_of_eqv_mul hweight
        (Q'.eqv_symm
          (Q'.one_mul_eqv
            (centralPhysicalFiniteWeight w hw K 0 first)))
  | first, last, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      have hlast := PositiveKernelChainIn.lastMem hnext rest
      have hnextWeight :=
        centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hnext
      have hlastWeight :=
        centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hlast
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
      rw [dif_pos hlast]
      refine Q'.eqv_trans _
        (Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 first)
            (centralPhysicalFiniteWeight w hw K 0 next) hnextWeight *
          Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 next)
            (centralPhysicalFiniteWeight w hw K 0 last) hlastWeight) _ ?_ ?_
      · exact divPos_chain_eqv_local _ _ _ hnextWeight hlastWeight
      unfold
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
      refine Q'.eqv_trans _
        (Q'.divPos
            (centralPhysicalFiniteConditionalKernel w hw K 0 next first)
            (centralPhysicalFiniteConditionalKernel w hw K 0 first next)
            (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
              hfirst positive) *
          Q'.divPos
            (centralPhysicalFiniteWeight w hw K 0 next)
            (centralPhysicalFiniteWeight w hw K 0 last) hlastWeight) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (centralPhysicalFiniteWeightRatio_eqv_conditionalReverseForward
            hfirst hnext positive)
      have hrest :=
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
          w hw K hnext rest
      unfold
        centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource
        at hrest
      rw [dif_pos hlast] at hrest
      exact Q'.mul_eqv_congr_left _ _ _ hrest

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralPhysicalFiniteConditionalKernel_detailedBalance
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralPhysicalFiniteKernel_reverse_pos_of_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralPhysicalFiniteConditionalKernel_reverse_pos_of_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralPhysicalFiniteWeightRatio_eqv_conditionalReverseForward
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_oneStep
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct
