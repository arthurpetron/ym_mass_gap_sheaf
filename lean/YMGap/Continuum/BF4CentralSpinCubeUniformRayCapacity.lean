/-
# A cutoff-uniform return floor and flow capacity on the central spin-cube ray

The selected zero-boundary production term is exactly the six-face source
activity.  The literal raw-row ceiling bounds the same source activity times
one cutoff-independent residual-carrier constant.  Reordering those two
factors therefore inhabits the selected-term row-ceiling interface at the
strong-coupling anchor, from the first cutoff onward.

The existing lossless compiler turns this datum into a positive cofinal
return floor and a uniform capacity for every oriented spoke on the explicit
spin-cube ray.  The certificate does not route the remaining physical vacuum
sector and therefore does not prove a full transfer-operator gap,
thermodynamic or continuum limit, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm
import YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
import YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling

namespace YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePhysicalTerm
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeSelectedTermRowCeiling
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The previously open selected-term comparison is inhabited -/

/-- At the fixed anchor, the same cutoff-independent residual-carrier ceiling
compares every admitted spin-cube raw row with its literal selected
zero-boundary production term. -/
def anchorCentralSpinCubeSelectedTermRowCeiling :
    FixedNomeCofinalSpinCubeSelectedTermRowCeiling
      (w := anchorCoupling) (by decide) where
  ceiling := centralSpinCubeResidualCarrierCeiling
  start := 0
  rawRow_le := by
    intro cutoff _hcutoff offset hoffset
    have hspin : offset + 1 ≤ cutoff := by omega
    have hraw :=
      centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling
        hspin
    have hselected :=
      centralLowerSpinCubePhysicalTerm_eqv
        anchorCoupling hspin
    exact Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv
            ((coeffW anchorCoupling (offset + 1)) ^ 6)
            centralSpinCubeResidualCarrierCeiling)
          (Q'.mul_eqv_congr_left
            centralSpinCubeResidualCarrierCeiling _ _
            (Q'.eqv_symm hselected))))

/-! ## 2. Concrete cutoff-uniform return and capacity data -/

def anchorCentralSpinCubeReturnFloor : Q' :=
  anchorCentralSpinCubeSelectedTermRowCeiling.returnFloor

theorem anchorCentralSpinCubeReturnFloor_pos :
    (0 : Q') < anchorCentralSpinCubeReturnFloor :=
  anchorCentralSpinCubeSelectedTermRowCeiling.returnFloor_pos

theorem anchorCentralSpinCubeReturnFloor_le_return
    {cutoff offset : Nat} (hoffset : offset < cutoff) :
    anchorCentralSpinCubeReturnFloor ≤
      centralLowerExcitedSpinCubeVacuumReturnProbability
        (w := anchorCoupling) (by decide) hoffset := by
  have hstart :
      anchorCentralSpinCubeSelectedTermRowCeiling.start ≤ cutoff := by
    change 0 ≤ cutoff
    exact Nat.zero_le cutoff
  exact
    anchorCentralSpinCubeSelectedTermRowCeiling.returnFloor_le_return
      (K := cutoff) hstart hoffset

def anchorCentralSpinCubeCofinalRayReturnFloor :
    FixedNomeCofinalSpinCubeRayReturnFloor
      (w := anchorCoupling) (by decide) :=
  anchorCentralSpinCubeSelectedTermRowCeiling.toCofinalRayReturnFloor

def anchorCentralSpinCubeCofinalRayCapacity :
    FixedNomeCofinalSpinCubeRayCapacity
      (w := anchorCoupling) (by decide) :=
  anchorCentralSpinCubeSelectedTermRowCeiling.toCofinalRayCapacity

theorem anchorCentralSpinCubeRayCapacity_pos :
    (0 : Q') < anchorCentralSpinCubeCofinalRayCapacity.delta :=
  anchorCentralSpinCubeCofinalRayCapacity.delta_pos

/-- Every cutoff has a concrete capacity certificate with the same positive
capacity constant supplied by the cofinal ray datum. -/
def anchorCentralSpinCubeFiniteRayCapacityAt (cutoff : Nat) :
    CentralLowerExcitedSpinCubeFiniteRayCapacityAt
      (w := anchorCoupling) (by decide) cutoff :=
  anchorCentralSpinCubeSelectedTermRowCeiling.finiteRayCapacityAt
    cutoff (by
      change 0 ≤ cutoff
      exact Nat.zero_le cutoff)

end YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeSelectedTermRowCeiling
#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeReturnFloor_pos
#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeReturnFloor_le_return
#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeCofinalRayReturnFloor
#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeCofinalRayCapacity
#print axioms YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity.anchorCentralSpinCubeFiniteRayCapacityAt
