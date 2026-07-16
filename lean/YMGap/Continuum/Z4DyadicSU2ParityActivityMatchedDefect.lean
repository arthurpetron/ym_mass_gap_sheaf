/-
# Activity-matched dyadic-cube comparison for the global parity pushforward

This module tests the first genuinely interacting cutoff-one block against
the exact global cellular-parity kernel.  The fine witness is the literal
24-face refinement of the unit-cube boundary.  Its weight is already known
exactly, and the derived coarse coupling is `2 * w^4`.

The result is a genuine one-sided global fibre comparison, not a renaming of
the kernel.  For every nonnegative rational fine coupling, the complete
coarse-cube parity fibre dominates the actual cutoff-one coarse spin-foam
term at the derived coupling.  The difference is packaged as an explicit
nonnegative block defect.  No equality of the full pushed law with a
one-parameter coarse law is asserted.
-/

import YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
import YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
import YMGap.Continuum.Z4CoarseUnitCubeActivity
import YMGap.Continuum.Z4UnitCubeBareCouplingShift

namespace YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact cellular image of the refined cube -/

theorem dyadicParityTargetSupportIds_refinedUnitCube :
    dyadicParityTargetSupportIds 2
        (componentLabel dyadicUnitCubeSupportIds) =
      coarseUnitCubeSupportIds := by
  decide

theorem refinedUnitCubeLabel_mem_fineStateSpace :
    componentLabel dyadicUnitCubeSupportIds ∈
      dyadicParityFineStateSpace 1 2 := by
  unfold dyadicParityFineStateSpace
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact List.mem_map.mpr
    ⟨dyadicUnitCubeSupportIds,
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports, rfl⟩

theorem dyadicParityGlobalKernel_refinedUnitCube_to_coarseCube :
    dyadicParityGlobalKernel 2
        (componentLabel dyadicUnitCubeSupportIds)
        (componentLabel coarseUnitCubeSupportIds) = 1 := by
  unfold dyadicParityGlobalKernel deterministicKernel
  rw [excitedPlaquetteIds_componentLabel_eq_support
    coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports]
  rw [dyadicParityTargetSupportIds_refinedUnitCube]
  rfl

/-! ## 2. Coupling-parametric global fibre weight -/

/-- The exact global parity pushforward with the fine spin-foam term evaluated
at an arbitrary rational coupling.  The existing production pushforward is
the specialization `fineCoupling = coupling`. -/
def dyadicParityParametricKernelPushforwardWeight
    (fineCoupling : Q') (K n : Nat)
    (coarsePhysical : EdgeLabelling) : Q' :=
  kernelPushforwardWeight (dyadicParityFineStateSpace K n)
    (parametricKPhysicalTerm fineCoupling K (2 * n))
    (dyadicParityTargetSupportIds n)
    (excitedPlaquetteIds n coarsePhysical)

theorem dyadicParityParametricKernelPushforwardWeight_nonnegative
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling)
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    (0 : Q') ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling K n coarsePhysical := by
  apply kernelPushforwardWeight_nonnegative
  intro finePhysical _
  exact parametricKPhysicalTerm_nonnegative
    hfine K (2 * n) finePhysical

theorem dyadicParityParametricKernelPushforwardWeight_coupling_eq
    (K n : Nat) (coarsePhysical : EdgeLabelling) :
    dyadicParityParametricKernelPushforwardWeight
        YMGap.Continuum.SU2PeterWeylWilsonBlock.coupling
        K n coarsePhysical =
      dyadicParityKernelPushforwardWeight K n coarsePhysical := by
  rfl

/-- Any explicitly enumerated fine state supplies a lower bound for its
global parity fibre.  Keeping the geometry variables abstract here prevents
the kernel from evaluating the complete closed state-space enumeration when
this lemma is specialized to the dyadic cube. -/
theorem dyadicParityParametricKernelPushforwardWeight_member_le
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling)
    {K n : Nat} {finePhysical coarsePhysical : EdgeLabelling}
    (hmember : finePhysical ∈ dyadicParityFineStateSpace K n) :
    parametricKPhysicalTerm fineCoupling K (2 * n) finePhysical *
        dyadicParityGlobalKernel n finePhysical coarsePhysical ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling K n coarsePhysical := by
  unfold dyadicParityParametricKernelPushforwardWeight
  unfold dyadicParityGlobalKernel
  unfold kernelPushforwardWeight
  apply listQSum_member_le
  · intro item
    exact Q'.mul_nonneg _ _
      (parametricKPhysicalTerm_nonnegative
        hfine K (2 * n) item)
      (deterministicKernel_nonnegative
        (dyadicParityTargetSupportIds n) item
        (excitedPlaquetteIds n coarsePhysical))
  · exact hmember

/-! ## 3. Exact activity matching and the global lower comparison -/

theorem refinedCubeTerm_eqv_activityMatchedCoarseTerm
    (fineCoupling : Q') :
    parametricKPhysicalTerm fineCoupling 1 4
        (componentLabel dyadicUnitCubeSupportIds) ≈
      parametricKPhysicalTerm
        (unitCubeBlockCoupling fineCoupling) 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  have hfine :
      parametricKPhysicalTerm fineCoupling 1 4
          (componentLabel dyadicUnitCubeSupportIds) ≈
        canonicalSurfaceActivity fineCoupling 4
          dyadicUnitCubeSupportIds := by
    exact parametricKPhysicalTerm_one_eqv_localized
      fineCoupling 4 (componentLabel dyadicUnitCubeSupportIds)
  have hblock :
      canonicalSurfaceActivity
          (unitCubeBlockCoupling fineCoupling) 2
          coarseUnitCubeSupportIds ≈
        canonicalSurfaceActivity fineCoupling 4
          dyadicUnitCubeSupportIds :=
    coarse_shifted_activity_eqv_dyadic_activity fineCoupling
  have hcoarse :
      parametricKPhysicalTerm
          (unitCubeBlockCoupling fineCoupling) 1 2
          (componentLabel coarseUnitCubeSupportIds) ≈
        canonicalSurfaceActivity
          (unitCubeBlockCoupling fineCoupling) 2
          coarseUnitCubeSupportIds := by
    exact parametricKPhysicalTerm_one_eqv_localized
      (unitCubeBlockCoupling fineCoupling) 2
      (componentLabel coarseUnitCubeSupportIds)
  exact Q'.eqv_trans _ _ _ hfine
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hblock)
      (Q'.eqv_symm hcoarse))

/-- **First exact global block comparison.**  The complete cellular-parity
fibre over the coarse cube dominates the literal coarse cutoff-one spin-foam
term at the derived effective coupling `2 * fineCoupling^4`.  The bound uses
the actual 24-face fine state as a member of the complete finite fibre; no
measured or fitted constant enters. -/
theorem activityMatchedCoarseTerm_le_parityPushforward
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    parametricKPhysicalTerm
        (unitCubeBlockCoupling fineCoupling) 1 2
        (componentLabel coarseUnitCubeSupportIds) ≤
      dyadicParityParametricKernelPushforwardWeight
        fineCoupling 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  have hsum :
      parametricKPhysicalTerm fineCoupling 1 (2 * 2)
          (componentLabel dyadicUnitCubeSupportIds) *
          dyadicParityGlobalKernel 2
            (componentLabel dyadicUnitCubeSupportIds)
            (componentLabel coarseUnitCubeSupportIds) ≤
        dyadicParityParametricKernelPushforwardWeight
          fineCoupling 1 2
          (componentLabel coarseUnitCubeSupportIds) := by
    exact dyadicParityParametricKernelPushforwardWeight_member_le
      (fineCoupling := fineCoupling) (K := 1) (n := 2)
      (finePhysical := componentLabel dyadicUnitCubeSupportIds)
      (coarsePhysical := componentLabel coarseUnitCubeSupportIds)
      hfine refinedUnitCubeLabel_mem_fineStateSpace
  have hwitness :
      parametricKPhysicalTerm
          (unitCubeBlockCoupling fineCoupling) 1 2
          (componentLabel coarseUnitCubeSupportIds) ≈
        parametricKPhysicalTerm fineCoupling 1 (2 * 2)
            (componentLabel dyadicUnitCubeSupportIds) *
          dyadicParityGlobalKernel 2
            (componentLabel dyadicUnitCubeSupportIds)
            (componentLabel coarseUnitCubeSupportIds) := by
    have hmatched := Q'.eqv_symm
      (refinedCubeTerm_eqv_activityMatchedCoarseTerm fineCoupling)
    have hkernel :
        dyadicParityGlobalKernel 2
            (componentLabel dyadicUnitCubeSupportIds)
            (componentLabel coarseUnitCubeSupportIds) = 1 :=
      dyadicParityGlobalKernel_refinedUnitCube_to_coarseCube
    rw [hkernel]
    exact Q'.eqv_trans _ _ _ hmatched
      (Q'.eqv_symm (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hwitness) hsum

/-- At the checked production coupling `1/2`, the derived block coordinate is
exactly `1/8`. -/
theorem productionUnitCubeBlockCoupling_eqv_eighth :
    unitCubeBlockCoupling coupling ≈ eighth := by
  decide

/-- Production specialization of the activity-matched comparison, now
stated against the pre-existing physical parity pushforward. -/
theorem productionActivityMatchedCoarseTerm_le_parityPushforward :
    parametricKPhysicalTerm
        (unitCubeBlockCoupling coupling) 1 2
        (componentLabel coarseUnitCubeSupportIds) ≤
      dyadicParityKernelPushforwardWeight 1 2
        (componentLabel coarseUnitCubeSupportIds) := by
  rw [← dyadicParityParametricKernelPushforwardWeight_coupling_eq
    1 2 (componentLabel coarseUnitCubeSupportIds)]
  exact activityMatchedCoarseTerm_le_parityPushforward
    (Q'.le_of_lt coupling_window.1)

/-- Additive one-block defect left after the activity-matched coarse term is
removed from the complete parity fibre. -/
def activityMatchedParityFibreDefect (fineCoupling : Q') : Q' :=
  dyadicParityParametricKernelPushforwardWeight fineCoupling 1 2
      (componentLabel coarseUnitCubeSupportIds) +
    -parametricKPhysicalTerm
      (unitCubeBlockCoupling fineCoupling) 1 2
      (componentLabel coarseUnitCubeSupportIds)

theorem activityMatchedParityFibreDefect_nonnegative
    {fineCoupling : Q'} (hfine : (0 : Q') ≤ fineCoupling) :
    (0 : Q') ≤ activityMatchedParityFibreDefect fineCoupling := by
  unfold activityMatchedParityFibreDefect
  exact Q'.sub_nonneg_of_le
    (activityMatchedCoarseTerm_le_parityPushforward hfine)

#print axioms dyadicParityTargetSupportIds_refinedUnitCube
#print axioms refinedUnitCubeLabel_mem_fineStateSpace
#print axioms dyadicParityGlobalKernel_refinedUnitCube_to_coarseCube
#print axioms dyadicParityParametricKernelPushforwardWeight_nonnegative
#print axioms dyadicParityParametricKernelPushforwardWeight_coupling_eq
#print axioms dyadicParityParametricKernelPushforwardWeight_member_le
#print axioms refinedCubeTerm_eqv_activityMatchedCoarseTerm
#print axioms activityMatchedCoarseTerm_le_parityPushforward
#print axioms productionUnitCubeBlockCoupling_eqv_eighth
#print axioms productionActivityMatchedCoarseTerm_le_parityPushforward
#print axioms activityMatchedParityFibreDefect_nonnegative

end YMGap.Continuum.Z4DyadicSU2ParityActivityMatchedDefect
