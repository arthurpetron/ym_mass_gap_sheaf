/-
# Genuine cutoff-two physical-kernel invariance under adjacent axis swaps

The two axis-swap interface modules prove invariance of the exact 140-factor
partition sum.  This module closes the remaining lower-face scalar term by a
finite Boolean check on the literal 65-state sector and then lifts both
adjacent swaps through the production physical-kernel factorization.

These are finite cutoff-two equalities only.  They generate the unsigned
spatial `S3` symmetry used by the next orbit-reduction layer; no signed flip,
uniform-cutoff estimate, completion, or continuum statement is made here.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapInterfaceInvariance
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private def axisSwap12SectorTargetIndex (sourceIndex : Fin 65) : Fin 65 :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.axisSwap12SectorTargetIndex
    sourceIndex

theorem cutoffTwoSectorStateAt_mem (index : Fin 65) :
    cutoffTwoSectorStateAt index ∈ cutoffTwoCubeSectorStates := by
  unfold cutoffTwoSectorStateAt
  exact List.get_mem _ _

def axisSwap01LowerFaceScalarCheck : Bool :=
  (List.finRange 65).all fun sourceIndex =>
    decide
      (cutoffTwoLowerFaceScalar (cutoffTwoSectorStateAt sourceIndex) ≈
        cutoffTwoLowerFaceScalar
          (cutoffTwoSectorStateAt
            (axisSwap01SectorTargetIndex sourceIndex)))

def axisSwap12LowerFaceScalarCheck : Bool :=
  (List.finRange 65).all fun sourceIndex =>
    decide
      (cutoffTwoLowerFaceScalar (cutoffTwoSectorStateAt sourceIndex) ≈
        cutoffTwoLowerFaceScalar
          (cutoffTwoSectorStateAt
            (axisSwap12SectorTargetIndex sourceIndex)))

theorem axisSwap01LowerFaceScalarCheck_true :
    axisSwap01LowerFaceScalarCheck = true := by
  unfold axisSwap01LowerFaceScalarCheck
  decide

theorem axisSwap12LowerFaceScalarCheck_true :
    axisSwap12LowerFaceScalarCheck = true := by
  unfold axisSwap12LowerFaceScalarCheck
  decide

theorem cutoffTwoLowerFaceScalar_axisSwap01_eqv
    (sourceIndex : Fin 65) :
    cutoffTwoLowerFaceScalar (cutoffTwoSectorStateAt sourceIndex) ≈
      cutoffTwoLowerFaceScalar
        (cutoffTwoSectorStateAt
          (axisSwap01SectorTargetIndex sourceIndex)) := by
  have hcheck := List.all_eq_true.mp axisSwap01LowerFaceScalarCheck_true
    sourceIndex (List.mem_finRange sourceIndex)
  exact of_decide_eq_true hcheck

theorem cutoffTwoLowerFaceScalar_axisSwap12_eqv
    (sourceIndex : Fin 65) :
    cutoffTwoLowerFaceScalar (cutoffTwoSectorStateAt sourceIndex) ≈
      cutoffTwoLowerFaceScalar
        (cutoffTwoSectorStateAt
          (axisSwap12SectorTargetIndex sourceIndex)) := by
  have hcheck := List.all_eq_true.mp axisSwap12LowerFaceScalarCheck_true
    sourceIndex (List.mem_finRange sourceIndex)
  exact of_decide_eq_true hcheck

private theorem cutoffTwoSectorPairInterface_axisSwap12_eqv_canonical
    (left right : Fin 65) :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt left)
          (cutoffTwoSectorStateAt right)) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex left))
          (cutoffTwoSectorStateAt
            (axisSwap12SectorTargetIndex right))) := by
  simpa only [axisSwap12SectorTargetIndex,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData.cutoffTwoSectorStateAt,
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.cutoffTwoSectorStateAt] using
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12InterfaceInvariance.cutoffTwoSectorPairInterface_axisSwap12_eqv
        left right

private theorem q_mul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv
    (left right : Fin 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt left)
        (cutoffTwoSectorStateAt right) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt (axisSwap01SectorTargetIndex left))
        (cutoffTwoSectorStateAt (axisSwap01SectorTargetIndex right)) := by
  have hsource :=
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorStateAt left) (cutoffTwoSectorStateAt right)
      (cutoffTwoSectorStateAt_mem left)
      (cutoffTwoSectorStateAt_mem right)
  have htarget :=
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorStateAt (axisSwap01SectorTargetIndex left))
      (cutoffTwoSectorStateAt (axisSwap01SectorTargetIndex right))
      (cutoffTwoSectorStateAt_mem (axisSwap01SectorTargetIndex left))
      (cutoffTwoSectorStateAt_mem (axisSwap01SectorTargetIndex right))
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _
      (q_mul_congr
        (q_mul_congr
          (cutoffTwoLowerFaceScalar_axisSwap01_eqv left)
          (cutoffTwoLowerFaceScalar_axisSwap01_eqv right))
        (YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapInterfaceInvariance.cutoffTwoSectorPairInterface_axisSwap01_eqv
          left right))
      (Q'.eqv_symm htarget))

theorem centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv
    (left right : Fin 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt left)
        (cutoffTwoSectorStateAt right) ≈
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex left))
        (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex right)) := by
  have hsource :=
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorStateAt left) (cutoffTwoSectorStateAt right)
      (cutoffTwoSectorStateAt_mem left)
      (cutoffTwoSectorStateAt_mem right)
  have htarget :=
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_factorPartitionSum
      (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex left))
      (cutoffTwoSectorStateAt (axisSwap12SectorTargetIndex right))
      (cutoffTwoSectorStateAt_mem (axisSwap12SectorTargetIndex left))
      (cutoffTwoSectorStateAt_mem (axisSwap12SectorTargetIndex right))
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _
      (q_mul_congr
        (q_mul_congr
          (cutoffTwoLowerFaceScalar_axisSwap12_eqv left)
          (cutoffTwoLowerFaceScalar_axisSwap12_eqv right))
        (cutoffTwoSectorPairInterface_axisSwap12_eqv_canonical left right))
      (Q'.eqv_symm htarget))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance.cutoffTwoLowerFaceScalar_axisSwap01_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance.cutoffTwoLowerFaceScalar_axisSwap12_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance.centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance.centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv
