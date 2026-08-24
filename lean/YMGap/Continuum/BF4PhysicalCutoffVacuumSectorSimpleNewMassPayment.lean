/-
# Automatic simple-coercivity payment for exact new-block mass

The component-split payment deliberately overestimates new-block mass by a
corrected-slab increment plus component-merger mass.  For finite-sector flow
capacity, however, the exact new block is a stationary submass of the later
vacuum sector and is therefore at most one.

With the simple coercivity floor, the common positive edge floor cancels.  If
the later vacuum component has `N >= 4` states, then `4N <= N^2`, so

  N * (2 * newMass) <= (1/2) * (1 + N^2).

This file proves that dimensionless estimate constructively, compiles it back
to the physical edge-floor payment, and inhabits it for the actual
cutoff-two-and-later carrier using its certified 65-state old block.

The coercivity used here is still the later finite-sector simple-path floor.
It may decay with cutoff, volume, or lattice spacing.  Thus this closes a
finite scalar payment, not a cutoff-uniform contraction, completed gap,
thermodynamic/continuum limit, or Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact new-block mass is a subprobability -/

theorem centralPhysicalFiniteVacuumSectorNewMass_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorNewMass
      w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorNewMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _
  unfold centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative hw later half _

theorem centralPhysicalFiniteVacuumSectorNewMass_le_fullSectorMass
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half ≤
      centralPhysicalFiniteVacuumSectorMass
        w hw later half := by
  let source := centralPhysicalFiniteVacuumSectorNewBlockIndices
    w hw base later half
  let target := centralPhysicalFiniteVacuumSectorIndices
    w hw later half
  let weight := centralPhysicalFiniteWeight w hw later half
  have hsubsum : listQSum weight source ≤ listQSum weight target := by
    apply listQSum_le_of_injective
      source target weight weight (fun index => index)
    · exact centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup
        w hw base later half
    · intro index hindex
      exact
        (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
          hindex).1
    · intro _ _ _ _ heq
      exact heq
    · intro _ _
      exact Q'.le_refl' _
    · intro index _
      unfold weight centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative hw later half _
  unfold centralPhysicalFiniteVacuumSectorNewMass
    centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact hsubsum

theorem centralPhysicalFiniteVacuumSectorNewMass_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteVacuumSectorNewMass
      w hw base later half ≤ 1 :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorNewMass_le_fullSectorMass
      w hw base later half)
    (centralPhysicalFiniteVacuumSectorMass_le_one
      w hw later half)

/-! ## 2. Exact dimensionless load and its quadratic capacity -/

def centralPhysicalFiniteMovingBaseSimpleNewMassLoad
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  Q'.ofNat
      (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
    (Q'.ofNat 2 *
      centralPhysicalFiniteVacuumSectorNewMass
        w hw base later half)

theorem centralPhysicalFiniteMovingBaseSimpleNewMassLoad_le_capacity_of_four_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat)
    (hfour : 4 ≤
      centralPhysicalFiniteMovingBaseStateCount w hw later half) :
    centralPhysicalFiniteMovingBaseSimpleNewMassLoad
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseSimplePaymentCapacity
        w hw later half := by
  let count := centralPhysicalFiniteMovingBaseStateCount w hw later half
  let countQ := Q'.ofNat count
  let mass := centralPhysicalFiniteVacuumSectorNewMass
    w hw base later half
  have hcount0 : (0 : Q') ≤ countQ := Q'.ofNat_nonneg count
  have hmass0 : (0 : Q') ≤ mass :=
    centralPhysicalFiniteVacuumSectorNewMass_nonnegative
      w hw base later half
  have hmass1 : mass ≤ 1 :=
    centralPhysicalFiniteVacuumSectorNewMass_le_one
      w hw base later half
  have htwoMassRaw : Q'.ofNat 2 * mass ≤ Q'.ofNat 2 * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hmass1
      (Q'.ofNat_nonneg 2)
  have htwoMass : Q'.ofNat 2 * mass ≤ Q'.ofNat 2 :=
    Q'.le_trans' _ _ _ htwoMassRaw
      (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat 2)))
  have hload : countQ * (Q'.ofNat 2 * mass) ≤
      countQ * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ countQ htwoMass hcount0
  have hhalfFour :
      HalfPow.half * Q'.ofNat 4 ≈ Q'.ofNat 2 := by
    decide
  have hhalfFour_le_halfCount :
      HalfPow.half * Q'.ofNat 4 ≤ HalfPow.half * countQ :=
    Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (Q'.ofNat_le_ofNat hfour) HalfPow.half_nonneg
  have htwo_le_halfCount :
      Q'.ofNat 2 ≤ HalfPow.half * countQ :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hhalfFour)
      hhalfFour_le_halfCount
  have hlinear : countQ * Q'.ofNat 2 ≤
      countQ * (HalfPow.half * countQ) :=
    Q'.mul_le_mul_of_nonneg_left _ _ countQ
      htwo_le_halfCount hcount0
  have hregroup :
      countQ * (HalfPow.half * countQ) ≈
        HalfPow.half * (countQ * countQ) := by
    ring_qeqv
  have hsquare_le_scale : countQ * countQ ≤
      1 + countQ * countQ := by
    have hadd := Q'.add_le_add_right
      (0 : Q') 1 (countQ * countQ)
      (by decide : (0 : Q') ≤ 1)
    rwa [Q'.zero_add'] at hadd
  have hcapacity : HalfPow.half * (countQ * countQ) ≤
      HalfPow.half * (1 + countQ * countQ) :=
    Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hsquare_le_scale HalfPow.half_nonneg
  unfold centralPhysicalFiniteMovingBaseSimpleNewMassLoad
    centralPhysicalFiniteMovingBaseSimplePaymentCapacity
    centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
  change countQ * (Q'.ofNat 2 * mass) ≤
    HalfPow.half * (1 + countQ * countQ)
  exact Q'.le_trans' _ _ _ hload
    (Q'.le_trans' _ _ _ hlinear
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hregroup) hcapacity))

/-! ## 3. Compile the dimensionless inequality to physical payment -/

def centralPhysicalFiniteMovingBaseSimpleNewMassPaymentDemand
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor
      w hw later half *
    centralPhysicalFiniteMovingBaseSimpleNewMassLoad
      w hw base later half

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
  ring_qeqv

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

theorem centralPhysicalFiniteMovingBaseSimpleNewMassPayment_iff_dimensionless
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    centralPhysicalFiniteMovingBaseSimpleNewMassPaymentDemand
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half ↔
    centralPhysicalFiniteMovingBaseSimpleNewMassLoad
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseSimplePaymentCapacity
        w hw later half := by
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w hw later half
  let scale := centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale
    w hw later half
  let load := centralPhysicalFiniteMovingBaseSimpleNewMassLoad
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

structure CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  hcutoff : base ≤ later
  dimensionless_payment :
    centralPhysicalFiniteMovingBaseSimpleNewMassLoad
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseSimplePaymentCapacity
        w hw later half

namespace CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt

def of_four_le_stateCount
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (hcutoff : base ≤ later)
    (hfour : 4 ≤
      centralPhysicalFiniteMovingBaseStateCount w hw later half) :
    CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt
      w hw base later half where
  hcutoff := hcutoff
  dimensionless_payment :=
    centralPhysicalFiniteMovingBaseSimpleNewMassLoad_le_capacity_of_four_le
      w hw base later half hfour

theorem physicalPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt
      w hw base later half) :
    centralPhysicalFiniteMovingBaseSimpleNewMassPaymentDemand
        w hw base later half ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half :=
  (centralPhysicalFiniteMovingBaseSimpleNewMassPayment_iff_dimensionless
    w hw base later half).mpr certificate.dimensionless_payment

end CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt

/-! ## 4. The certified 65-state cutoff-two block supplies `N >= 4` -/

theorem cutoffTwoMovingBaseStateCount_eq_65_add_new
    {later : Nat} (hcutoff : 2 ≤ later) :
    centralPhysicalFiniteMovingBaseStateCount
        cutoffTwoHalfCoupling (by decide) later 0 =
      65 + (cutoffTwoEdgeLoadNewStates later).length := by
  change (cutoffTwoEdgeLoadFullStates later).length =
    65 + (cutoffTwoEdgeLoadNewStates later).length
  exact cutoffTwoEdgeLoadFullStates_length_eq_65_add_new hcutoff

theorem cutoffTwoMovingBaseStateCount_four_le
    {later : Nat} (hcutoff : 2 ≤ later) :
    4 ≤ centralPhysicalFiniteMovingBaseStateCount
      cutoffTwoHalfCoupling (by decide) later 0 := by
  rw [cutoffTwoMovingBaseStateCount_eq_65_add_new hcutoff]
  omega

def cutoffTwoMovingBaseSimpleNewMassPaymentAt
    (later : Nat) (hcutoff : 2 ≤ later) :
    CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt
      cutoffTwoHalfCoupling (by decide) 2 later 0 :=
  CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt.of_four_le_stateCount
    hcutoff (cutoffTwoMovingBaseStateCount_four_le hcutoff)

theorem cutoffTwoMovingBaseSimpleNewMassPhysicalPayment
    (later : Nat) (hcutoff : 2 ≤ later) :
    centralPhysicalFiniteMovingBaseSimpleNewMassPaymentDemand
        cutoffTwoHalfCoupling (by decide) 2 later 0 ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        cutoffTwoHalfCoupling (by decide) later 0 :=
  (cutoffTwoMovingBaseSimpleNewMassPaymentAt later hcutoff).physicalPayment

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.centralPhysicalFiniteVacuumSectorNewMass_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.centralPhysicalFiniteMovingBaseSimpleNewMassLoad_le_capacity_of_four_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.centralPhysicalFiniteMovingBaseSimpleNewMassPayment_iff_dimensionless
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt.of_four_le_stateCount
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt.physicalPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.cutoffTwoMovingBaseStateCount_eq_65_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.cutoffTwoMovingBaseSimpleNewMassPhysicalPayment
