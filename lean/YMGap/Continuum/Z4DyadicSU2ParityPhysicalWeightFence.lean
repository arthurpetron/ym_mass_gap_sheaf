/-
# A finite physical-weight fence for the global parity pushforward

The global parity kernel has an exact fibre-summed pushforward, but this does
not make that pushforward the pre-existing physical coarse spin-foam weight.
This module banks the smallest explicit counterexample to the naive universal
identification.

At fine cutoff zero the source enumeration contains only the vacuum, whose
parity image is the coarse vacuum.  The canonical six-face coarse cube is a
different cutoff-one state and hence receives zero pushed mass.  Its genuine
coarse spin-foam weight is nevertheless strictly positive.  Thus an RG law
must include a nontrivial cutoff/coupling/normalization comparison; bare
deterministic fibre summation cannot simply be renamed as the same-coupling
coarse physical weight for every cutoff.
-/

import YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4FiniteGraphVacuumCompletion

namespace YMGap.Continuum.Z4DyadicSU2ParityPhysicalWeightFence

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

theorem coarseUnitCubeSupportIds_ne_nil :
    coarseUnitCubeSupportIds ≠ [] := by
  intro hequal
  have hlength := coarseUnitCubeSupportIds_length
  rw [hequal] at hlength
  cases hlength

theorem coarseUnitCubePhysical_mem_cutoff_one :
    componentLabel coarseUnitCubeSupportIds ∈
      explicitPhysicalLabellings 1 2 := by
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact List.mem_map.mpr
    ⟨coarseUnitCubeSupportIds,
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports, rfl⟩

/-- With no non-vacuum fine spin available, the nonempty coarse cube fibre
has exact pushed mass zero. -/
theorem cutoffZero_parityPushforward_coarseCube_eqv_zero :
    dyadicParityKernelPushforwardWeight 0 2
        (componentLabel coarseUnitCubeSupportIds) ≈ 0 := by
  have htarget :
      excitedPlaquetteIds 2 (componentLabel coarseUnitCubeSupportIds) =
        coarseUnitCubeSupportIds :=
    excitedPlaquetteIds_componentLabel_eq_support
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have hcode :
      dyadicParityTargetSupportIds 2 zeroEdgeLabelling = [] :=
    dyadicParityTargetSupportIds_zeroEdgeLabelling 2
  have hne :
      excitedPlaquetteIds 2 (componentLabel coarseUnitCubeSupportIds) ≠
        dyadicParityTargetSupportIds 2 zeroEdgeLabelling := by
    rw [htarget, hcode]
    exact coarseUnitCubeSupportIds_ne_nil
  unfold dyadicParityKernelPushforwardWeight dyadicParityFineStateSpace
    explicitPhysicalLabellings
  rw [boundedEdgeLabellings_zero]
  simp only [kernelPushforwardWeight, listQSum]
  rw [deterministicKernel_off_image hne]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) (Q'.eqv_refl 0))
    (Q'.eqv_of_eq (Q'.zero_add' 0))

/-- At the production coupling, the literal cutoff-one spin-foam weight of
the canonical coarse cube is its already-derived canonical activity. -/
theorem coarseUnitCube_explicitSpinFoamWeight_eqv_activity :
    explicitSpinFoamWeight 1 2
        (componentLabel coarseUnitCubeSupportIds) ≈
      canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds := by
  refine Q'.eqv_trans _
    (localizedSpinFoamWeight 1 2
      (componentLabel coarseUnitCubeSupportIds)) _
    (explicitSpinFoamWeight_eq_localized 1 2
      (componentLabel coarseUnitCubeSupportIds)) ?_
  have hface : explicitPhysicalFaceFactor 1 2
      (componentLabel coarseUnitCubeSupportIds) =
        parametricPhysicalFaceFactor coupling 2
          (componentLabel coarseUnitCubeSupportIds) := by
    rfl
  unfold localizedSpinFoamWeight canonicalSurfaceActivity
    parametricLocalizedSpinFoamWeight
  rw [hface]
  exact Q'.eqv_refl _

theorem coarseUnitCube_explicitSpinFoamWeight_pos :
    (0 : Q') < explicitSpinFoamWeight 1 2
      (componentLabel coarseUnitCubeSupportIds) := by
  have hactivity : (0 : Q') <
      canonicalSurfaceActivity coupling 2 coarseUnitCubeSupportIds :=
    coarseUnitCube_canonicalSurfaceActivity_pos (by decide)
  exact Q'.pos_of_lt_of_le hactivity
    (Q'.ge_of_eqv coarseUnitCube_explicitSpinFoamWeight_eqv_activity)

/-- Exact discrepancy fence: the kernel pushforward and the physical coarse
weight disagree on an inhabited, explicitly enumerated coarse state. -/
theorem cutoffZero_parityPushforward_ne_physical_coarseCube :
    ¬ dyadicParityKernelPushforwardWeight 0 2
        (componentLabel coarseUnitCubeSupportIds) ≈
      explicitSpinFoamWeight 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  intro hequal
  have hphysicalZero :
      explicitSpinFoamWeight 1 2
          (componentLabel coarseUnitCubeSupportIds) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hequal)
      cutoffZero_parityPushforward_coarseCube_eqv_zero
  have hle : explicitSpinFoamWeight 1 2
      (componentLabel coarseUnitCubeSupportIds) ≤ 0 :=
    Q'.le_of_eqv hphysicalZero
  have hbad : (0 : Q') < 0 :=
    YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      coarseUnitCube_explicitSpinFoamWeight_pos hle
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0 hbad

#print axioms coarseUnitCubePhysical_mem_cutoff_one
#print axioms cutoffZero_parityPushforward_coarseCube_eqv_zero
#print axioms coarseUnitCube_explicitSpinFoamWeight_eqv_activity
#print axioms coarseUnitCube_explicitSpinFoamWeight_pos
#print axioms cutoffZero_parityPushforward_ne_physical_coarseCube

end YMGap.Continuum.Z4DyadicSU2ParityPhysicalWeightFence
