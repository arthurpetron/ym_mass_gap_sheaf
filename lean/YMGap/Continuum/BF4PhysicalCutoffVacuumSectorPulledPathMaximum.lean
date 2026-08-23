/-
# The maximum path bound on every later pulled BF4 carrier

For a fixed base vacuum component, the canonical paths can be rekernelled by
every sufficiently late pulled physical kernel.  Rekernelization preserves
their amplification scales.  The finite maximum constructed on the base
carrier therefore replaces the earlier sum ceiling in the later-uniform
endpoint estimate.

The maximum and the persistent edge floor may still depend on the base.  No
all-base rate, completed gap, thermodynamic or continuum limit, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathMaximum

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

namespace FixedBasePulledPositiveEdgeFloor

/-- The persistent base edge floor and the located maximum of base path
scales control every endpoint difference in every later pulled kernel. -/
theorem floor_mul_endpoint_sq_le_maximum_mul_pulledDirichlet
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
      centralPhysicalFiniteVacuumSectorPathMaximum w hw base half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw base half)
          coefficient
          (centralPhysicalFinitePulledKernel w hw base later half) := by
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  let basePath := centralPhysicalFiniteVacuumSectorPositivePath
    w hw base half left right hleft hright
  let path := fixedBasePulledPositivePath
    base later half hbaseLater left right hleft hright
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    coefficient
    (centralPhysicalFinitePulledKernel w hw base later half)
  have hlocal :
      certificate.floor *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)) ≤
        BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient path := by
    exact
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_rekernel_amplifiedEnergy
        coefficient certificate.floor (Q'.le_of_lt certificate.floor_pos)
        (fun first next hfirst hnext hpositive =>
          centralPhysicalFinitePulledKernel_pos_of_base_pos
            hbaseLater hfirst hnext hpositive)
        (fun first next hfirst hnext hpositive =>
          certificate.floor_le later hlater first next
            hfirst hnext hpositive)
        hleft basePath
  have hkernel : ∀ source target,
      (0 : Q') ≤ centralPhysicalFinitePulledKernel
        w hw base later half source target := by
    intro source target
    unfold centralPhysicalFinitePulledKernel centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      hw later half _ _
  have hglobal :
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
          coefficient path ≤
        BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
            path * energy := by
    exact
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy
        coefficient hkernel hleft path
  have hbaseScale :=
    centralPhysicalFiniteVacuumSectorPathScale_le_maximum
      w hw base half left right hleft hright
  have hscale :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path ≤
        centralPhysicalFiniteVacuumSectorPathMaximum w hw base half := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_of_eq
          (fixedBasePulledPositivePath_amplificationScale_eq_base
            base later half hbaseLater left right hleft hright)))
      hbaseScale
  have henergy0 : (0 : Q') ≤ energy :=
    finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      coefficient
      (centralPhysicalFinitePulledKernel w hw base later half)
      hkernel
  have hscaled :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path * energy ≤
        centralPhysicalFiniteVacuumSectorPathMaximum w hw base half *
          energy :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale henergy0
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.le_trans' _ _ _ hglobal hscaled)

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathMaximum

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathMaximum.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_maximum_mul_pulledDirichlet
