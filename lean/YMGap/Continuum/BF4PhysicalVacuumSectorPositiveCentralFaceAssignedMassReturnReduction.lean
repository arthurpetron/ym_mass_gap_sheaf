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
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassObservable

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
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

/-- The exact finite assigned-expectation / spin-cube-weight ratio.  Its
denominator is strictly positive for every admitted excited spin. -/
def positiveCentralFaceAssignedStationaryRatioAt
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) : Q' :=
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  Q'.divPos
    (centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
      (positiveCentralFaceAssignedUnitObservable
        K (offset + 1)).value)
    (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 source)
    (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega)))

theorem positiveCentralFaceAssignedStationaryRatioAt_nonnegative
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    (0 : Q') ≤
      positiveCentralFaceAssignedStationaryRatioAt hw hoffset := by
  unfold positiveCentralFaceAssignedStationaryRatioAt Q'.divPos
  apply Q'.mul_nonneg
  · exact centralPhysicalStationaryMean_nonnegative_of_nonnegative
      (Q'.le_of_lt hw) K 0 _
      (positiveCentralFaceAssignedUnitObservable
        K (offset + 1)).nonnegative
  · exact Q'.le_of_lt (Q'.recipPos_pos _ _)

theorem positiveCentralFaceAssignedStationaryRatioAt_mul_weight_eqv_mean
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    positiveCentralFaceAssignedStationaryRatioAt hw hoffset *
        centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw) K offset) ≈
      centralPhysicalStationaryMean w (Q'.le_of_lt hw) K 0
        (positiveCentralFaceAssignedUnitObservable
          K (offset + 1)).value := by
  unfold positiveCentralFaceAssignedStationaryRatioAt
  exact Q'.divPos_mul_eqv _ _ _

/-- Totalize the exact ratio outside its admitted finite offset range by zero,
so a located maximum can be computed on `List.range K`. -/
def positiveCentralFaceAssignedStationaryRatioValue
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) : Q' :=
  if hoffset : offset < K then
    positiveCentralFaceAssignedStationaryRatioAt hw hoffset
  else 0

theorem positiveCentralFaceAssignedStationaryRatioValue_eq
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    positiveCentralFaceAssignedStationaryRatioValue hw K offset =
      positiveCentralFaceAssignedStationaryRatioAt hw hoffset := by
  simp only [positiveCentralFaceAssignedStationaryRatioValue, hoffset,
    dite_true]

theorem positiveCentralFaceAssignedStationaryRatioValue_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K offset : Nat) :
    (0 : Q') ≤
      positiveCentralFaceAssignedStationaryRatioValue hw K offset := by
  by_cases hoffset : offset < K
  · rw [positiveCentralFaceAssignedStationaryRatioValue_eq hw hoffset]
    exact positiveCentralFaceAssignedStationaryRatioAt_nonnegative
      hw hoffset
  · unfold positiveCentralFaceAssignedStationaryRatioValue
    simp only [hoffset, dite_false]
    exact Q'.le_refl' 0

/-- The sharp located ceiling of all assigned expectation/weight ratios at
one positive finite cutoff. -/
def positiveCentralFaceAssignedStationaryRatioFiniteCeiling
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) : Q' :=
  listQMaxZero
    (positiveCentralFaceAssignedStationaryRatioValue hw K)
    (List.range K)

theorem positiveCentralFaceAssignedStationaryRatioFiniteCeiling_nonnegative
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    (0 : Q') ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K := by
  unfold positiveCentralFaceAssignedStationaryRatioFiniteCeiling
  exact listQMaxZero_nonnegative _
    (positiveCentralFaceAssignedStationaryRatioValue_nonnegative hw K)
    (List.range K)

theorem positiveCentralFaceAssignedStationaryRatioAt_le_finiteCeiling
    {w : Q'} (hw : (0 : Q') < w) {K offset : Nat}
    (hoffset : offset < K) :
    positiveCentralFaceAssignedStationaryRatioAt hw hoffset ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K := by
  rw [← positiveCentralFaceAssignedStationaryRatioValue_eq hw hoffset]
  exact le_listQMaxZero_of_mem
    (positiveCentralFaceAssignedStationaryRatioValue hw K)
    (List.range K) (List.mem_range.mpr hoffset)

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

namespace FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

private theorem listQMaxZero_le_of_member_bound
    {State : Type} (value : State → Q') (bound : Q')
    (hboundNonnegative : (0 : Q') ≤ bound) :
    ∀ states : List State,
      (∀ state, state ∈ states → value state ≤ bound) →
      listQMaxZero value states ≤ bound
  | [], _ => hboundNonnegative
  | head :: tail, hbound => by
      unfold listQMaxZero
      apply (Q'.max'_le_iff' _ _ _).mpr
      exact ⟨hbound head List.mem_cons_self,
        listQMaxZero_le_of_member_bound value bound hboundNonnegative tail
          (fun state hstate =>
            hbound state (List.mem_cons_of_mem head hstate))⟩

/-- The named cofinal datum is exactly a common upper ceiling on the explicit
finite rational ratios. -/
theorem exactRatioAt_le_ratioBound
    {w : Q'} {hw : (0 : Q') < w}
    (ratio : FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio hw)
    (K : Nat) (hK : ratio.start ≤ K)
    (offset : Nat) (hoffset : offset < K) :
    positiveCentralFaceAssignedStationaryRatioAt hw hoffset ≤
      ratio.ratioBound := by
  let source := centralLowerExcitedSpinCubeIndex
    w (Q'.le_of_lt hw) K offset
  let weight := centralPhysicalFiniteWeight
    w (Q'.le_of_lt hw) K 0 source
  let hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (centralLowerSpinCubeIndex_mem_vacuumSector hw (by omega))
  apply Q'.divPos_le_of_le_mul _ weight hweight
  exact ratio.assignedMean_le K hK offset hoffset

/-- Equivalently, every sufficiently late sharp finite maximum lies below the
same cofinal ratio bound. -/
theorem finiteCeiling_le_ratioBound
    {w : Q'} {hw : (0 : Q') < w}
    (ratio : FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio hw)
    (K : Nat) (hK : ratio.start ≤ K) :
    positiveCentralFaceAssignedStationaryRatioFiniteCeiling hw K ≤
      ratio.ratioBound := by
  unfold positiveCentralFaceAssignedStationaryRatioFiniteCeiling
  apply listQMaxZero_le_of_member_bound _ ratio.ratioBound
    ratio.ratioBound_nonnegative
  intro offset hoffsetMem
  have hoffset := List.mem_range.mp hoffsetMem
  rw [positiveCentralFaceAssignedStationaryRatioValue_eq hw hoffset]
  exact ratio.exactRatioAt_le_ratioBound K hK offset hoffset

end FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio

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
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.positiveCentralFaceAssignedStationaryRatioAt_mul_weight_eqv_mean
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.positiveCentralFaceAssignedStationaryRatioAt_le_finiteCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.exactRatioAt_le_ratioBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.finiteCeiling_le_ratioBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction.FixedNomeCofinalPositiveCentralFaceAssignedStationaryRatio.assignedMean_mul_kernelReciprocal_le
