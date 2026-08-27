/-
# Sparse support obstructs global conditional minorization

A positive stationary-product minorization cannot hold on a finite canonical
component if its genuine joint has even one zero entry between two retained
states.  Both endpoint weights are strictly positive, hence the conditioned
stationary reference is positive there and the proposed pointwise lower bound
is contradictory.

This is the abstract support obstruction.  Concrete sparse BF4 sectors can
instantiate it without importing their generated certificates downstream.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity

namespace YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationSparseNoGo

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationGap
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

/-- Any zero joint entry between two positive-weight states in the canonical
component contradicts positive global stationary-product minorization. -/
theorem no_positive_global_conditional_minorization_of_kernel_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hkernel :
      centralPhysicalFiniteKernel w hw cutoff half left right ≈ 0)
    (data : CentralPhysicalFiniteConditionalMinorizationGapData
      w hw cutoff half) : False := by
  have hleftWeight : (0 : Q') <
      centralPhysicalFiniteWeight w hw cutoff half left :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hleft
  have hrightWeight : (0 : Q') <
      centralPhysicalFiniteWeight w hw cutoff half right :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hright
  have hreference :=
    finiteCarrierMassNormalizedStationaryProductJoint_pos
      (mass_pos := centralPhysicalFiniteVacuumSectorWeightSum_pos
        w hw cutoff half)
      hleftWeight hrightWeight
  have hpositive := Q'.mul_pos data.fraction_pos hreference
  have hminor := data.minorization left hleft right hright
  have hnonpos := Q'.le_trans' _ _ _ hminor (Q'.le_of_eqv hkernel)
  exact (Int.not_lt_of_ge hnonpos) hpositive

end YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationSparseNoGo

/-! ## Dependency gate -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalMinorizationSparseNoGo.no_positive_global_conditional_minorization_of_kernel_zero
