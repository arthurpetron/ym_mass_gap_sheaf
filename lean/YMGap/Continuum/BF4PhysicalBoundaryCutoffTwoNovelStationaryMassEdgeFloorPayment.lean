/-
# A stationary-mass-refined edge-floor payment for the cutoff-two novel shell

The exact stationary mass of novel endpoint pairs sharpens the scalar payment
needed by every four-block pointwise capacity field.  At cutoff `later`, it is
sufficient that

  novelFloor * (ofNat (65 + newShellLength) * novelEndpointMass)
    <= half * finitePositiveEdgeFloor.

If a novel load is positive, its routed physical-kernel entry is positive and
therefore lies above the finite positive-edge floor.  If the load vanishes,
capacity follows from kernel nonnegativity.  The common half-floor target pays
the reserved half capacity on old--old edges and is automatically below full
capacity on the other three blocks.

A cofinal family of these scalar payments compiles through the existing novel
flow machinery to completed strict contraction.  No such cofinal payment is
constructed here: in particular, no decay estimate for novel stationary mass,
cutoff-uniform edge-floor comparison, thermodynamic/continuum construction, or
Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One mass-refined scalar payment pays every positive-load edge -/

private theorem q_nonpos_of_not_pos_local {value : Q'}
    (hnot : ¬ (0 : Q') < value) : value ≤ 0 := by
  show value.num * (1 : Int) ≤ (0 : Int) * (value.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

private theorem cutoffTwoKernel_nonnegative_local
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoEdgeLoadKernel
    BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteKernel
  exact
    BF4SU2FixedMagneticPhysicalMarkov.centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) later 0 _ _

private theorem half_mul_kernel_le_kernel
    (later source target : Nat) :
    HalfPow.half * cutoffTwoEdgeLoadKernel later source target ≤
      cutoffTwoEdgeLoadKernel later source target := by
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    HalfPow.half (1 : Q')
    (cutoffTwoEdgeLoadKernel later source target)
    (by decide)
    (cutoffTwoKernel_nonnegative_local later source target)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv
      (Q'.one_mul_eqv (cutoffTwoEdgeLoadKernel later source target)))

theorem cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
    {later : Nat} (hcutoff : 2 ≤ later)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            cutoffTwoNovelEndpointWeightMass later) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0)
    {source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSimpleEdgeLoad later source target ≤
      HalfPow.half * cutoffTwoEdgeLoadKernel later source target := by
  let load := cutoffTwoNovelSimpleEdgeLoad later source target
  have hload0 : (0 : Q') ≤ load :=
    cutoffTwoNovelSimpleEdgeLoad_nonnegative later source target
  by_cases hload : (0 : Q') < load
  · have hloadBound : load ≤
        Q'.ofNat
            (65 + (cutoffTwoEdgeLoadNewStates later).length) *
          cutoffTwoNovelEndpointWeightMass later :=
      cutoffTwoNovelSimpleEdgeLoad_le_shellSize_mul_endpointMass
        hcutoff source target
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hloadBound
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    have hkernelPositive : (0 : Q') <
        cutoffTwoEdgeLoadKernel later source target :=
      cutoffTwoNovelSimpleEdgeLoad_pos_implies_kernel_pos
        later source target hload
    have hedgeFloor :=
      centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
        cutoffTwoHalfCoupling (by decide) later 0
        source target hsource htarget hkernelPositive
    have hhalfFloor := Q'.mul_le_mul_of_nonneg_left _ _
      HalfPow.half hedgeFloor HalfPow.half_nonneg
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ hpayment hhalfFloor)
  · have hloadNonpositive : load ≤ 0 :=
      q_nonpos_of_not_pos_local hload
    have hloadZero : load ≈ 0 :=
      Q'.eqv_of_le_le hloadNonpositive hload0
    have hscaledZero :
        cutoffTwoNovelSimpleFlowCoercivityFloor * load ≈ 0 :=
      Q'.eqv_trans _
        (cutoffTwoNovelSimpleFlowCoercivityFloor * 0) _
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor load 0 hloadZero)
        (Q'.mul_zero_eqv cutoffTwoNovelSimpleFlowCoercivityFloor)
    exact Q'.le_trans' _ 0 _
      (Q'.le_of_eqv hscaledZero)
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (cutoffTwoKernel_nonnegative_local later source target))

/-! ## 2. The mass-refined payment inhabits all four finite capacity blocks -/

def cutoffTwoNovelSimpleFlowCapacityAt_of_stationaryMassEdgeFloorPayment
    (later : Nat)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later)
    (hpayment :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          (Q'.ofNat
              (65 + (cutoffTwoEdgeLoadNewStates later).length) *
            cutoffTwoNovelEndpointWeightMass later) ≤
        HalfPow.half *
          centralPhysicalFiniteVacuumSectorEdgeFloor
            cutoffTwoHalfCoupling (by decide) later 0) :
    CutoffTwoNovelSimpleFlowCapacityAt later where
  later_ge_pulled_floor := hlaterFloor
  later_ge_mass_floor := hlaterMass
  old_old := by
    intro source hsource target htarget
    exact
      cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
        (Nat.le_trans
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
          hlaterFloor)
        hpayment
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1
  old_new := by
    intro source hsource target htarget
    exact Q'.le_trans' _ _ _
      (cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
        (Nat.le_trans
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
          hlaterFloor)
        hpayment
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1)
      (half_mul_kernel_le_kernel later source target)
  new_old := by
    intro source hsource target htarget
    exact Q'.le_trans' _ _ _
      (cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
        (Nat.le_trans
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
          hlaterFloor)
        hpayment
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1)
      (half_mul_kernel_le_kernel later source target)
  new_new := by
    intro source hsource target htarget
    exact Q'.le_trans' _ _ _
      (cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
        (Nat.le_trans
          cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
          hlaterFloor)
        hpayment
        (List.mem_filter.mp hsource).1
        (List.mem_filter.mp htarget).1)
      (half_mul_kernel_le_kernel later source target)

/-! ## 3. A cofinal mass-refined payment reaches completed contraction -/

structure CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  payment : ∀ request,
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        (Q'.ofNat
            (65 +
              (cutoffTwoEdgeLoadNewStates (anchor request)).length) *
          cutoffTwoNovelEndpointWeightMass (anchor request)) ≤
      HalfPow.half *
        centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) (anchor request) 0

namespace CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment

def toCofinalNovelSimpleFlowCapacity
    (family : CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment) :
    CutoffTwoCofinalNovelSimpleFlowCapacity where
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  capacity := by
    intro request
    have hanchor := family.anchor_ge request
    exact
      cutoffTwoNovelSimpleFlowCapacityAt_of_stationaryMassEdgeFloorPayment
        (family.anchor request)
        (Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_left _ _) hanchor))
        (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_left _ _) hanchor))
        (family.payment request)

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData

end CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment.cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment.cutoffTwoNovelSimpleFlowCapacityAt_of_stationaryMassEdgeFloorPayment
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment.CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment.CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment.toCompletedStrictContractionData
