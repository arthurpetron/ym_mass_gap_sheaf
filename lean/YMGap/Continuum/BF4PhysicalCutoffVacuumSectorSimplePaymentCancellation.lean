/-
# Cancellation of the generic simple coercivity payment

The explicit finite-sector coercivity floor is the later positive edge floor
divided by `1 + carrierSize^2`.  Substituting it into the generic moving-base
payment cancels the same positive edge floor from both sides.  The exact local
obligation is therefore the dimensionless inequality

  carrierSize * 2 * (cutoffIncrement + mergerMass)
    <= (1/2) * (1 + carrierSize^2).

This file proves the equivalence, packages the dimensionless predicate as the
remaining finite local certificate, compiles it to scaled new-mass payment,
and inhabits it at equal cutoffs.

No nontrivial moving step, cofinal family, generic routed-flow capacity,
cutoff-uniform contraction, thermodynamic/continuum construction, or Clay
mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The dimensionless load and capacity -/

def centralPhysicalFiniteMovingBaseSimplePaymentLoad
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  Q'.ofNat
      (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
    (Q'.ofNat 2 *
      (slabParametricKCutoffIncrement
          w base later (centralExtent half) +
        centralPhysicalFiniteNewComponentMergerMass
          w hw base later half))

def centralPhysicalFiniteMovingBaseSimplePaymentCapacity
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
      w hw later half

theorem centralPhysicalFiniteMovingBaseSimplePaymentCapacity_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) :
    (0 : Q') < centralPhysicalFiniteMovingBaseSimplePaymentCapacity
      w hw later half := by
  unfold centralPhysicalFiniteMovingBaseSimplePaymentCapacity
  exact Q'.mul_pos (by decide)
    (centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
      w hw later half)

/-! ## 2. Generic positive-factor cancellation -/

private theorem scale_mul_divPosFloor_mul_eqv
    (floor scale load : Q')
    (hscale : (0 : Q') < scale) :
    scale * (Q'.divPos floor scale hscale * load) ≈
      floor * load := by
  refine Q'.eqv_trans _
    ((scale * Q'.divPos floor scale hscale) * load) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ load
    (Q'.eqv_trans _
      (Q'.divPos floor scale hscale * scale) _
      (Q'.mul_comm_eqv _ _)
      (Q'.divPos_mul_eqv floor scale hscale))

private theorem scale_mul_capacity_mul_floor_eqv
    (floor scale capacity : Q') :
    scale * (capacity * floor) ≈
      floor * (capacity * scale) := by
  refine Q'.eqv_trans _ ((scale * capacity) * floor) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ (floor * (scale * capacity)) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.mul_eqv_congr_left floor _ _
    (Q'.mul_comm_eqv _ _)

private theorem divPosFloor_mul_le_capacity_mul_floor_iff
    (floor scale load capacity : Q')
    (hfloor : (0 : Q') < floor)
    (hscale : (0 : Q') < scale) :
    Q'.divPos floor scale hscale * load ≤ capacity * floor ↔
      load ≤ capacity * scale := by
  constructor
  · intro hpayment
    have hscaled :
        scale * (Q'.divPos floor scale hscale * load) ≤
          scale * (capacity * floor) :=
      Q'.mul_le_mul_of_nonneg_left _ _ scale hpayment
        (Q'.le_of_lt hscale)
    have hcleared : floor * load ≤ floor * (capacity * scale) :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (scale_mul_divPosFloor_mul_eqv floor scale load hscale)))
        (Q'.le_trans' _ _ _ hscaled
          (Q'.le_of_eqv
            (scale_mul_capacity_mul_floor_eqv
              floor scale capacity)))
    exact Q'.le_of_mul_le_mul_left hcleared hfloor
  · intro hload
    have hcleared : floor * load ≤ floor * (capacity * scale) :=
      Q'.mul_le_mul_of_nonneg_left _ _ floor hload
        (Q'.le_of_lt hfloor)
    have hscaled :
        scale * (Q'.divPos floor scale hscale * load) ≤
          scale * (capacity * floor) :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (scale_mul_divPosFloor_mul_eqv floor scale load hscale))
        (Q'.le_trans' _ _ _ hcleared
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (scale_mul_capacity_mul_floor_eqv
                floor scale capacity))))
    exact Q'.le_of_mul_le_mul_left hscaled hscale

/-! ## 3. Exact cancellation for the physical moving-base payment -/

theorem centralPhysicalFiniteMovingBaseSimpleComponentPayment_iff_dimensionless
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
        w hw base later half
          (centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
            w hw later half) ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half ↔
    centralPhysicalFiniteMovingBaseSimplePaymentLoad
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseSimplePaymentCapacity
        w hw later half := by
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w hw later half
  let scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    w hw later half
  let load := centralPhysicalFiniteMovingBaseSimplePaymentLoad
    w hw base later half
  have hfloor := centralPhysicalFiniteVacuumSectorEdgeFloor_pos
    w hw later half
  have hscale :=
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_pos
      w hw later half
  change Q'.divPos floor scale hscale * load ≤ HalfPow.half * floor ↔
    load ≤ HalfPow.half * scale
  exact divPosFloor_mul_le_capacity_mul_floor_iff
    floor scale load HalfPow.half hfloor hscale

/-! ## 4. The exact local certificate and its compiler -/

structure CentralPhysicalFiniteMovingBaseSimplePaymentAt
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  hcutoff : base ≤ later
  dimensionless_payment :
    centralPhysicalFiniteMovingBaseSimplePaymentLoad
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseSimplePaymentCapacity
        w hw later half

namespace CentralPhysicalFiniteMovingBaseSimplePaymentAt

theorem componentSplitPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseSimplePaymentAt
      w hw base later half) :
    centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
        w hw base later half
          (centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
            w hw later half) ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half :=
  (centralPhysicalFiniteMovingBaseSimpleComponentPayment_iff_dimensionless
    w hw base later half).mpr certificate.dimensionless_payment

theorem newMassPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseSimplePaymentAt
      w hw base later half) :
    centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
          w hw later half *
        (Q'.ofNat
            (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
          (Q'.ofNat 2 *
            centralPhysicalFiniteVacuumSectorNewMass
              w hw base later half)) ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half :=
  centralPhysicalFiniteMovingBaseNewMassPayment_of_componentSplitPayment
    certificate.hcutoff
    (Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_pos
        w hw later half))
    certificate.componentSplitPayment

end CentralPhysicalFiniteMovingBaseSimplePaymentAt

/-! ## 5. Equal cutoffs satisfy the dimensionless certificate -/

private theorem centralPhysicalFiniteMovingBaseSimplePaymentLoad_self_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    centralPhysicalFiniteMovingBaseSimplePaymentLoad
      w hw cutoff cutoff half ≈ 0 := by
  have hinc := slabParametricKCutoffIncrement_self_eqv_zero
    w cutoff (centralExtent half)
  have hmerger := centralPhysicalFiniteNewComponentMergerMass_self_eqv_zero
    w hw cutoff half
  have hadd :
      slabParametricKCutoffIncrement
          w cutoff cutoff (centralExtent half) +
        centralPhysicalFiniteNewComponentMergerMass
          w hw cutoff cutoff half ≈ 0 :=
    Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr' hinc hmerger)
      (Q'.eqv_of_eq (Q'.zero_add' 0))
  unfold centralPhysicalFiniteMovingBaseSimplePaymentLoad
  refine Q'.eqv_trans _
    (Q'.ofNat
        (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) *
      (Q'.ofNat 2 * 0)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ 0 hadd)
  exact Q'.eqv_trans _
    (Q'.ofNat
        (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) * 0) _
    (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv _))
    (Q'.mul_zero_eqv _)

def centralPhysicalFiniteMovingBaseSimplePaymentAt_self
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) :
    CentralPhysicalFiniteMovingBaseSimplePaymentAt
      w hw cutoff cutoff half where
  hcutoff := Nat.le_refl cutoff
  dimensionless_payment :=
    Q'.le_trans' _ 0 _
      (Q'.le_of_eqv
        (centralPhysicalFiniteMovingBaseSimplePaymentLoad_self_eqv_zero
          w hw cutoff half))
      (Q'.le_of_lt
        (centralPhysicalFiniteMovingBaseSimplePaymentCapacity_pos
          w hw cutoff half))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.centralPhysicalFiniteMovingBaseSimplePaymentCapacity_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.centralPhysicalFiniteMovingBaseSimpleComponentPayment_iff_dimensionless
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.CentralPhysicalFiniteMovingBaseSimplePaymentAt.componentSplitPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.CentralPhysicalFiniteMovingBaseSimplePaymentAt.newMassPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.centralPhysicalFiniteMovingBaseSimplePaymentAt_self
