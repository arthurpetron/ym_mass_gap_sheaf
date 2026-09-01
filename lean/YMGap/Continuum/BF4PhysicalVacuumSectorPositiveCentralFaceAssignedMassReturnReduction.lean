/-
# Assigned central-face mass reduced to a stationary ratio and ray return

The assigned-spin observable recodes one routing fiber as a physical
stationary expectation.  This module isolates the remaining analytic input:
uniform comparison of that expectation with the stationary weight of the
corresponding spin cube.  The already proved spin-ray return floor then
converts this stationary ratio into a bound relative to the literal
spin-cube-to-vacuum joint conductance.

Together with the preceding prefix-plus-expectation theorem, the resulting
compiler leaves the independent prefix-to-vacuum resistance term visible.
No stationary-ratio family is constructed here, and hence no uniform
terminal bound, full congestion certificate, finite gap, physical scaling,
continuum theory, or Clay conclusion is proved.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceNormalizedTerminalMassDecomposition
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceTerminalPrefixAssignment
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalDemand
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem weight_reciprocal_mul_delta_eqv
    (weight reciprocal delta : Q') :
    (weight * reciprocal) * delta ≈
      (delta * weight) * reciprocal := by
  refine Q'.eqv_trans _ (weight * (reciprocal * delta)) _
    (Q'.mul_assoc_eqv weight reciprocal delta) ?_
  refine Q'.eqv_trans _ (weight * (delta * reciprocal)) _
    (Q'.mul_eqv_congr_left weight _ _
      (Q'.mul_comm_eqv reciprocal delta)) ?_
  refine Q'.eqv_trans _ ((weight * delta) * reciprocal) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv weight delta reciprocal)) ?_
  exact Q'.mul_eqv_congr_right _ _ reciprocal
    (Q'.mul_comm_eqv weight delta)

/-! ## 1. Return probability converts source weight into conductance -/

theorem sourceWeight_mul_kernelReciprocal_le_inverseReturnFloor
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (delta : Q')
    (hdelta : (0 : Q') < delta)
    (hreturn : delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset) :
    let source := centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 source 0
    let hkernel : (0 : Q') < kernel :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
    centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 source *
        Q'.recipPos kernel hkernel ≤
      Q'.divPos 1 delta hdelta := by
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let kernel := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source 0
  let hkernel : (0 : Q') < kernel :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
  let reciprocal := Q'.recipPos kernel hkernel
  have hweightNonnegative : (0 : Q') ≤ weight :=
    Q'.le_of_lt
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))
  have hweightedReturn : weight * delta ≤
      weight * centralLowerExcitedSpinCubeVacuumReturnProbability
        hw hoffset :=
    Q'.mul_le_mul_of_nonneg_left _ _ weight hreturn
      hweightNonnegative
  have hcapacity : delta * weight ≤ kernel :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv delta weight))
      (Q'.le_trans' _ _ _ hweightedReturn
        (Q'.le_of_eqv
          (centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel
            hw hoffset)))
  apply Q'.le_divPos_of_mul_le 1 delta hdelta
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
    hcapacity (Q'.le_of_lt (Q'.recipPos_pos kernel hkernel))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (weight_reciprocal_mul_delta_eqv weight reciprocal delta))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_recipPos_eqv kernel hkernel)))

/-! ## 2. The remaining stationary-ratio producer -/

/-- The precise cofinal analytic datum still missing from the assigned-spin
branch: its physical stationary expectation is at most one common multiple
of the corresponding spin-cube stationary weight. -/
structure FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio
    {w : Q'} (hw : (0 : Q') < w) : Type where
  ratioBound : Q'
  ratioBound_nonnegative : (0 : Q') ≤ ratioBound
  start : Nat
  start_positive : 1 ≤ start
  assignedMean_le : ∀ K, start ≤ K →
    ∀ offset, (hoffset : offset < K) →
      centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable
            K (offset + 1)).value ≤
        ratioBound *
          centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K offset)

theorem assignedMean_mul_kernelReciprocal_le_ratio_div_returnFloor
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) (ratioBound delta : Q')
    (hratioBound : (0 : Q') ≤ ratioBound)
    (hdelta : (0 : Q') < delta)
    (hreturn : delta ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability hw hoffset)
    (hratio :
      centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable
            K (offset + 1)).value ≤
        ratioBound *
          centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
            (centralLowerExcitedSpinCubeIndex
              w (Q'.le_of_lt hw) K offset)) :
    let source := centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 source 0
    let hkernel : (0 : Q') < kernel :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
    centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable
            K (offset + 1)).value *
        Q'.recipPos kernel hkernel ≤
      Q'.divPos ratioBound delta hdelta := by
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let kernel := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 source 0
  let hkernel : (0 : Q') < kernel :=
    centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
  let reciprocal := Q'.recipPos kernel hkernel
  have hsource :=
    sourceWeight_mul_kernelReciprocal_le_inverseReturnFloor
      hw hoffset delta hdelta hreturn
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
    hratio (Q'.le_of_lt (Q'.recipPos_pos kernel hkernel))
  refine Q'.le_trans' _ _ _ hscaled ?_
  refine Q'.le_trans' _ (ratioBound * (weight * reciprocal)) _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv ratioBound weight reciprocal)) ?_
  have hratioScaled := Q'.mul_le_mul_of_nonneg_left _ _ ratioBound
    hsource hratioBound
  refine Q'.le_trans' _ _ _ hratioScaled ?_
  unfold Q'.divPos
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left ratioBound _ _
      (Q'.one_mul_eqv (Q'.recipPos delta hdelta)))

namespace FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

/-- Combining the missing stationary-ratio datum with an existing ray
capacity bounds the assigned expectation divided by the terminal joint
conductance.  The denominator is the already available `2 * delta` return
floor. -/
theorem assignedMean_mul_kernelReciprocal_le
    {w : Q'} {hw : (0 : Q') < w}
    (ratio : FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio hw)
    (capacity : FixedNomeCofinalSpinCubeRayCapacity hw)
    (K : Nat) (hratioK : ratio.start ≤ K)
    (hcapacityK : capacity.start ≤ K)
    (offset : Nat) (hoffset : offset < K) :
    let source := centralLowerExcitedSpinCubeIndex
      w (Q'.le_of_lt hw) K offset
    let kernel := centralPhysicalFiniteKernel
      w (Q'.le_of_lt hw) K 0 source 0
    let hkernel : (0 : Q') < kernel :=
      centralPhysicalFiniteKernel_spinCubeIndex_zero_pos hw (by omega)
    centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
          (positiveCentralFaceAssignedUnitObservable
            K (offset + 1)).value *
        Q'.recipPos kernel hkernel ≤
      Q'.divPos ratio.ratioBound (2 * capacity.delta)
        (Q'.mul_pos (by decide) capacity.delta_pos) := by
  exact assignedMean_mul_kernelReciprocal_le_ratio_div_returnFloor
    hw hoffset ratio.ratioBound (2 * capacity.delta)
    ratio.ratioBound_nonnegative
    (Q'.mul_pos (by decide) capacity.delta_pos)
    (capacity.twice_le_return K hcapacityK offset hoffset)
    (ratio.assignedMean_le K hratioK offset hoffset)

end FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.sourceWeight_mul_kernelReciprocal_le_inverseReturnFloor
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.assignedMean_mul_kernelReciprocal_le_ratio_div_returnFloor
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.assignedMean_mul_kernelReciprocal_le
