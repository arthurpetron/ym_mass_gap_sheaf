/-
# Verified computed kernel for cutoff-two sector pairs

The generic proof-by-construction ternary eliminator is instantiated on the
genuine 140-factor physical graph.  For every pair of sector states, its
kernel-computed bottom value is thereby identified with the complete
24-coordinate fixed-interface partition sum.

The cube/cube specialization is cross-checked against the independent sparse
trace certificate.  This is a finite cutoff-two theorem only; no uniform or
continuum conclusion is asserted here.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
import YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorComputedTernaryElimination
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- All genuine factors read only the 24 interface coordinates.  The Boolean
check depends on scopes, not on the two state values. -/
theorem cutoffTwoSectorPairFactorScopes_checked
    (left right : EdgeLabelling) :
    factorsScopedByCheck cutoffTwoCubeInterfaceEliminationOrder
      (cutoffTwoSectorPairInterfaceFactors left right) = true := by
  rfl

theorem cutoffTwoSectorPairFactors_scoped
    (left right : EdgeLabelling) :
    FactorsScopedBy cutoffTwoCubeInterfaceEliminationOrder
      (cutoffTwoSectorPairInterfaceFactors left right) :=
  factorsScopedBy_of_check
    (cutoffTwoSectorPairFactorScopes_checked left right)

/-- Exact result of the verified ternary dynamic program in a supplied order. -/
def cutoffTwoSectorPairComputedInterfaceForOrder
    (order : List Nat) (left right : EdgeLabelling) : Q' :=
  computedTernaryBottomValue order
    (cutoffTwoSectorPairInterfaceFactors left right)

theorem cutoffTwoSectorPairPartitionSum_ordered_eqv_computedForOrder
    (order : List Nat) (left right : EdgeLabelling)
    (hnodup : order.Nodup)
    (hscoped : FactorsScopedBy order
      (cutoffTwoSectorPairInterfaceFactors left right)) :
    scopedFactorPartitionSum 2 order
        (cutoffTwoSectorPairInterfaceFactors left right) ≈
      cutoffTwoSectorPairComputedInterfaceForOrder order left right := by
  have hsound :=
    scopedFactorPartitionSum_eqv_computedTernaryBottom
      order
      (cutoffTwoSectorPairInterfaceFactors left right)
      hnodup hscoped
  simpa only [cutoffTwoSectorPairComputedInterfaceForOrder] using hsound

/-- Exact result in the audited width-five physical interface order. -/
def cutoffTwoSectorPairComputedInterface
    (left right : EdgeLabelling) : Q' :=
  cutoffTwoSectorPairComputedInterfaceForOrder
    cutoffTwoCubeInterfaceEliminationOrder left right

theorem cutoffTwoSectorPairPartitionSum_ordered_eqv_computed
    (left right : EdgeLabelling) :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        (cutoffTwoSectorPairInterfaceFactors left right) ≈
      cutoffTwoSectorPairComputedInterface left right := by
  have hcomputed :=
    cutoffTwoSectorPairPartitionSum_ordered_eqv_computedForOrder
      cutoffTwoCubeInterfaceEliminationOrder left right
      (by decide)
      (cutoffTwoSectorPairFactors_scoped left right)
  simpa only [cutoffTwoSectorPairComputedInterface] using hcomputed

theorem cutoffTwoSectorPairPartitionSum_eqv_computedForOrder
    (order : List Nat) (left right : EdgeLabelling)
    (hperm : order.Perm (centralFixedFaceIds 0))
    (hnodup : order.Nodup)
    (hscoped : FactorsScopedBy order
      (cutoffTwoSectorPairInterfaceFactors left right)) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors left right) ≈
      cutoffTwoSectorPairComputedInterfaceForOrder order left right := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct
        (cutoffTwoSectorPairInterfaceFactors left right))
      hperm.symm)
    (cutoffTwoSectorPairPartitionSum_ordered_eqv_computedForOrder
      order left right hnodup hscoped)

theorem cutoffTwoSectorPairPartitionSum_eqv_computed
    (left right : EdgeLabelling) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors left right) ≈
      cutoffTwoSectorPairComputedInterface left right := by
  have hcomputed := cutoffTwoSectorPairPartitionSum_eqv_computedForOrder
    cutoffTwoCubeInterfaceEliminationOrder left right
    cutoffTwoCubeInterfaceEliminationOrder_perm
    (by decide)
    (cutoffTwoSectorPairFactors_scoped left right)
  simpa only [cutoffTwoSectorPairComputedInterface] using hcomputed

/-- Production physical kernel entry reduced to the verified computed value. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_computed
    (left right : EdgeLabelling)
    (hleft : left ∈ cutoffTwoCubeSectorStates)
    (hright : right ∈ cutoffTwoCubeSectorStates) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0 left right ≈
      (cutoffTwoLowerFaceScalar left * cutoffTwoLowerFaceScalar right) *
        cutoffTwoSectorPairComputedInterface left right := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      left right hleft hright)
    (Q'.mul_eqv_congr_left _ _ _
      (cutoffTwoSectorPairPartitionSum_eqv_computed left right))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel.cutoffTwoSectorPairPartitionSum_eqv_computed
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel.centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_computed
