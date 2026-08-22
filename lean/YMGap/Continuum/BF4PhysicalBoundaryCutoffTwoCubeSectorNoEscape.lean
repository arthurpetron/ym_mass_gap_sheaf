/-
# One-step no-escape for the cutoff-two cube sector

The exact cube sector is row-closed for the production reflected kernel.  By
testing sector membership through the faithful natural-number state code,
this module constructively proves that a support-graph edge whose source lies
in the sector cannot end outside it.

This is finite cutoff two only.  It supplies neither a compatible cofinal
sector family nor any thermodynamic or continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

/-- A single edge of the symmetrized production-kernel support graph cannot
leave the exact cutoff-two cube sector. -/
theorem next_state_mem_cutoffTwoSector_of_adjacent
    {sourceIndex targetIndex : Nat}
    (hsourceIndex : sourceIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0)
    (htargetIndex : targetIndex < centralPhysicalFiniteCarrierSize
      cutoffTwoHalfCoupling (by decide) 2 0)
    (hsource : centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 sourceIndex ∈ cutoffTwoCubeSectorStates)
    (hadj : centralPhysicalFiniteSupportAdjacentB cutoffTwoHalfCoupling
      (by decide) 2 0 sourceIndex targetIndex = true) :
    centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
      (by decide) 2 0 targetIndex ∈ cutoffTwoCubeSectorStates := by
  let source := centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
    (by decide) 2 0 sourceIndex
  let target := centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
    (by decide) 2 0 targetIndex
  have hsourceHalf : source ∈ centralHalfStates 2 0 :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive cutoffTwoHalfCoupling
        (by decide) 2 0 hsourceIndex)).1
  have htargetHalf : target ∈ centralHalfStates 2 0 :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive cutoffTwoHalfCoupling
        (by decide) 2 0 htargetIndex)).1
  cases cutoffTwoCubeSectorMembershipDecidable htargetHalf with
  | isTrue htargetSector => exact htargetSector
  | isFalse houtside =>
    have hforward :
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          source target ≈ 0 :=
      centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
        source target hsource htargetHalf houtside
    have hreverse :
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          target source ≈ 0 :=
      Q'.eqv_trans _ _ _
        (centralPhysicalReflectedKernel_symm cutoffTwoHalfCoupling
          htargetHalf hsourceHalf) hforward
    have hforwardRaw :
        centralPhysicalFiniteRawKernel cutoffTwoHalfCoupling
          (by decide) 2 0 sourceIndex targetIndex ≈ 0 := by
      unfold centralPhysicalFiniteRawKernel
      exact hforward
    have hreverseRaw :
        centralPhysicalFiniteRawKernel cutoffTwoHalfCoupling
          (by decide) 2 0 targetIndex sourceIndex ≈ 0 := by
      unfold centralPhysicalFiniteRawKernel
      exact hreverse
    have hfalse :=
      centralPhysicalFiniteSupportAdjacentB_false_of_rawKernel_eqv_zero
        cutoffTwoHalfCoupling (by decide) 2 0 sourceIndex targetIndex
        hforwardRaw hreverseRaw
    rw [hadj] at hfalse
    cases hfalse

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape.next_state_mem_cutoffTwoSector_of_adjacent
