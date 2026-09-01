/-
# Uniform direct-root resistance demand on the explicit BF4 spin-cube ray

The explicit spin-cube ray supplies one distinct positive vacuum-root spoke
per excited spin.  The terminal-demand audit shows that root routing must also
control stationary mass divided by the root kernel.  On a spin-cube spoke,
that quotient is the reciprocal vacuum-return probability.

This module combines the already proved cutoff-uniform spin-cube return floor
with the literal one-edge root path.  For every cutoff-admitted excited spin,
the direct terminal demand satisfies

  rayCapacity.delta * directRootDemand <= 1.

At the strong-coupling anchor the existing concrete cofinal ray capacity
therefore gives one cutoff-independent upper bound on every explicit
spin-cube direct-root demand.  This controls the ray subfamily only; it does
not assign or route the off-ray sector and does not prove the full cofinal gap
or any continuum result.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand

namespace YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorResistanceCauchy
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem two_mul_eqv_add_self_local (value : Q') :
    2 * value ≈ value + value := by
  have htwo : (2 : Q') ≈ (1 : Q') + 1 :=
    Q'.eqv_trans _ (Q'.ofNat 1 + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv 1 1)
      (Q'.add_eqv_congr' (by decide) (by decide))
  exact Q'.eqv_trans _ (((1 : Q') + 1) * value) _
    (Q'.mul_eqv_congr_right _ _ value htwo)
    (Q'.eqv_trans _ (1 * value + 1 * value) _
      (Q'.add_mul_eqv 1 1 value)
      (Q'.add_eqv_congr'
        (Q'.one_mul_eqv value) (Q'.one_mul_eqv value)))

private theorem delta_mul_add_self_eqv_two_delta_mul
    (delta weight reciprocal : Q') :
    delta * ((weight * reciprocal) + (weight * reciprocal)) ≈
      ((2 * delta) * weight) * reciprocal := by
  let singleDemand := weight * reciprocal
  refine Q'.eqv_trans _ (delta * (2 * singleDemand)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left delta _ _
      (Q'.eqv_symm (two_mul_eqv_add_self_local singleDemand))
  refine Q'.eqv_trans _ ((delta * 2) * singleDemand) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv delta 2 singleDemand)) ?_
  refine Q'.eqv_trans _ ((2 * delta) * singleDemand) _
    (Q'.mul_eqv_congr_right _ _ singleDemand
      (Q'.mul_comm_eqv delta 2)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (2 * delta) weight reciprocal)

/-! ## 1. Literal one-edge resistance demand -/

/-- Twice the stationary mass times the reciprocal kernel on the direct
excited-spin-cube-to-vacuum spoke. -/
def centralLowerExcitedSpinCubeDirectRootResistanceDemand
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) : Q' :=
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let hkernel : (0 : Q') <
      centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 index 0 :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
  let singleDemand :=
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index *
      Q'.recipPos
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 index 0)
        hkernel
  singleDemand + singleDemand

theorem centralLowerExcitedSpinCubeToVacuumSpoke_resistance_eqv_reciprocal
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    PositiveKernelChainIn.resistance
        (centralLowerSpinCubeToVacuumSpoke hw
          (show offset + 1 ≤ K by omega)) ≈
      Q'.recipPos
        (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) 0)
        (centralPhysicalFiniteKernel_spinCubeIndex_zero_pos
          hw (show offset + 1 ≤ K by omega)) := by
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 2. A return floor bounds every direct spin-cube demand -/

theorem delta_mul_directRootResistanceDemand_le_one
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (delta : Q')
    (hreturn : 2 * delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset) :
    delta * centralLowerExcitedSpinCubeDirectRootResistanceDemand
        hw hoffset ≤ 1 := by
  let index := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let weight :=
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 index
  let kernel :=
    centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K 0 index 0
  let hkernel : (0 : Q') < kernel :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
  let reciprocal := Q'.recipPos kernel hkernel
  let singleDemand := weight * reciprocal
  let demand := singleDemand + singleDemand
  have hweight0 : (0 : Q') ≤ weight :=
    Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
  have hweighted :
      weight * (2 * delta) ≤
        weight *
          centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset :=
    Q'.mul_le_mul_of_nonneg_left _ _ weight hreturn hweight0
  have hkernelBound : (2 * delta) * weight ≤ kernel := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv (2 * delta) weight))
      (Q'.le_trans' _ _ _ hweighted
        (Q'.le_of_eqv
          (centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
            hw hoffset)))
  have hreciprocal0 : (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt (Q'.recipPos_pos kernel hkernel)
  have hscaled : ((2 * delta) * weight) * reciprocal ≤
      kernel * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
      hkernelBound hreciprocal0
  have hleft : delta * demand ≈
      ((2 * delta) * weight) * reciprocal := by
    exact delta_mul_add_self_eqv_two_delta_mul
      delta weight reciprocal
  have hright : kernel * reciprocal ≈ 1 :=
    Q'.mul_recipPos_eqv kernel hkernel
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

namespace FixedNomeCofinalSpinCubeRayCapacity

theorem delta_mul_directRootResistanceDemand_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (K : Nat) (hK : capacity.start ≤ K)
    (offset : Nat) (hoffset : offset < K) :
    capacity.delta *
        centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset ≤
      1 := by
  exact
    BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.delta_mul_directRootResistanceDemand_le_one
      hw hoffset capacity.delta
      (capacity.twice_le_return K hK offset hoffset)

/-- Explicit cutoff-independent upper bound on every direct spin-cube root
demand supplied by a cofinal ray capacity. -/
theorem directRootResistanceDemand_le_reciprocalDelta
    {w : Q'} {hw : (0 : Q') < w}
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (K : Nat) (hK : capacity.start ≤ K)
    (offset : Nat) (hoffset : offset < K) :
    centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset ≤
      Q'.divPos 1 capacity.delta capacity.delta_pos := by
  apply Q'.le_divPos_of_mul_le 1 capacity.delta capacity.delta_pos
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralLowerExcitedSpinCubeDirectRootResistanceDemand hw hoffset)
        capacity.delta))
    (BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.FixedNomeCofinalSpinCubeRayCapacity.delta_mul_directRootResistanceDemand_le_one
      capacity K hK offset hoffset)

end FixedNomeCofinalSpinCubeRayCapacity

/-! ## 3. Concrete anchor specialization -/

theorem anchorDirectRootResistanceDemand_le_uniformBound
    {K offset : Nat} (hoffset : offset < K) :
    centralLowerExcitedSpinCubeDirectRootResistanceDemand
        (w := anchorCoupling) (by decide) hoffset ≤
      Q'.divPos 1 anchorCentralSpinCubeCofinalRayCapacity.delta
        anchorCentralSpinCubeCofinalRayCapacity.delta_pos := by
  exact
    FixedNomeCofinalSpinCubeRayCapacity.directRootResistanceDemand_le_reciprocalDelta
      anchorCentralSpinCubeCofinalRayCapacity
      K (by
        change 0 ≤ K
        exact Nat.zero_le K)
      offset hoffset

end YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.centralLowerExcitedSpinCubeToVacuumSpoke_resistance_eqv_reciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.delta_mul_directRootResistanceDemand_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.FixedNomeCofinalSpinCubeRayCapacity.directRootResistanceDemand_le_reciprocalDelta
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceSpinCubeDemand.anchorDirectRootResistanceDemand_le_uniformBound
