/-
# The loop-free carrier-square scale on every later pulled BF4 kernel

For a fixed base vacuum component, the loop-erased support path has at most as
many edges as the base carrier has vertices.  Every sufficiently late pulled
physical kernel remains positive on those base edges and retains the explicit
persistent edge floor.  Thus the carrier-square endpoint estimate survives at
all later cutoffs.

The carrier size and edge floor can still vary with the base.  No all-base
common rate, completed gap, thermodynamic/continuum limit, or Clay conclusion
is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

namespace FixedBasePulledPositiveEdgeFloor

theorem floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_pulledDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    certificate.floor *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
          w hw base half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw base half)
          coefficient
          (centralPhysicalFinitePulledKernel w hw base later half) := by
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  let basePath :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      w hw base half left right hleft hright
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    coefficient
    (centralPhysicalFinitePulledKernel w hw base later half)
  have hkernel : ∀ source target,
      (0 : Q') ≤ centralPhysicalFinitePulledKernel
        w hw base later half source target := by
    intro source target
    unfold centralPhysicalFinitePulledKernel centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      hw later half _ _
  have hlocal :=
    BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_quadraticLength_mul_rekernel_Dirichlet
      coefficient hkernel certificate.floor
      (Q'.le_of_lt certificate.floor_pos)
      (fun first next hfirst hnext hpositive =>
        centralPhysicalFinitePulledKernel_pos_of_base_pos
          hbaseLater hfirst hnext hpositive)
      (fun first next hfirst hnext hpositive =>
        certificate.floor_le later hlater first next
          hfirst hnext hpositive)
      hleft basePath
  have hscale :=
    centralPhysicalFiniteVacuumSectorSimplePath_quadraticLength_le_scale
      w hw base half left right hleft hright
  have henergy0 : (0 : Q') ≤ energy :=
    BF4PhysicalFiniteVacuumSectorPathCeiling.finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      coefficient
      (centralPhysicalFinitePulledKernel w hw base later half)
      hkernel
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.mul_le_mul_of_nonneg_right _ _ energy hscale henergy0)

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledSimplePathScale.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_pulledDirichlet
