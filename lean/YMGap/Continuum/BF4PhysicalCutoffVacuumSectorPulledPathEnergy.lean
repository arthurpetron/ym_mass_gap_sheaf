/-
# Uniform path energy on every fixed BF4 vacuum carrier

For an arbitrary fixed base vacuum component, the constructed persistent
edge floor can be applied to the base component's canonical positive paths
after those paths are transported to any later pulled kernel.  Rekernelization
does not change the recursive path scale, so the base component's finite path
ceiling remains valid at every later cutoff.

The resulting endpoint estimate is uniform in the later cutoff and in the
coefficient vector, but its floor and path ceiling may depend on the fixed
base component.  It therefore advances the expanding finite-carrier route
without asserting the still-open cofinal uniformity.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathGlobalEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward

/-! ## 1. Transport the canonical base path -/

/-- The canonical base path, rekernelled by a later pulled physical kernel. -/
def fixedBasePulledPositivePath
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    PositiveKernelChainIn
      (centralPhysicalFinitePulledKernel w hw base later half)
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)
      left right :=
  BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.rekernel
    (fun _first _next hfirst hnext hpositive =>
      centralPhysicalFinitePulledKernel_pos_of_base_pos
        hlater hfirst hnext hpositive)
    hleft
    (centralPhysicalFiniteVacuumSectorPositivePath
      w hw base half left right hleft hright)

theorem fixedBasePulledPositivePath_amplificationScale_eq_base
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (fixedBasePulledPositivePath
          base later half hlater left right hleft hright) =
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw base half left right hleft hright) := by
  unfold fixedBasePulledPositivePath
  exact
    BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.PositiveKernelChainIn.amplificationScale_rekernel
      (fun first next hfirst hnext hpositive =>
        centralPhysicalFinitePulledKernel_pos_of_base_pos
          hlater hfirst hnext hpositive)
      hleft
      (centralPhysicalFiniteVacuumSectorPositivePath
        w hw base half left right hleft hright)

/-! ## 2. One later-uniform endpoint estimate for each fixed carrier -/

namespace FixedBasePulledPositiveEdgeFloor

theorem floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
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
      centralPhysicalFiniteVacuumSectorPathCeiling w hw base half *
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
      (0 : Q') ≤
        centralPhysicalFinitePulledKernel
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
    centralPhysicalFiniteVacuumSectorPathScale_le_ceiling
      w hw base half left right hleft hright
  have hscale :
      BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.PositiveKernelChainIn.amplificationScale
          path ≤
        centralPhysicalFiniteVacuumSectorPathCeiling w hw base half := by
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
        centralPhysicalFiniteVacuumSectorPathCeiling w hw base half *
          energy :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale henergy0
  exact Q'.le_trans' _ _ _ hlocal
    (Q'.le_trans' _ _ _ hglobal hscaled)

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy.fixedBasePulledPositivePath_amplificationScale_eq_base
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
