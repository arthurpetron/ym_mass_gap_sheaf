/-
# Exact heat-semigroup decimation reaches the observable coefficient corridor

The complete observable inverse-fiber theorem no longer needs the syntactic
hypothesis `w <= 1/400`; it needs only the exact local coefficient inequality

  exteriorFaceCoefficient w 0 <= anchorFaceCoefficient.

This module proves that the exact heat-semigroup decimation map
`mkDecimate depth w = w^depth` reaches that regime from every rational
`0 < w < 1`, at the explicit constructive depth

  400 * ((1 - w).den + 1).

The proof uses the finite geometric identity and lower cofactor bound to show

  w^N <= 1 / (1 + N * (1 - w)),

then pays `N * (1 - w) >= 400` using the denominator of the positive rational
gap.  The resulting decimated slab has the already proved covariance decay.

This closes only the scalar coefficient-capture half of the RG seam.  It does
not prove that the interacting four-dimensional block-spin map is exact heat
decimation, nor transport the original literal observable or its covariance
to the decimated slab.  Those remain the physical producer.

Constructive contract: finite rational order algebra and exact
heat-semigroup decimation only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Constructive.HalfPow
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKPos
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A constructive inverse-affine bound for rational powers -/

/-- The exact depth used to enter the production coefficient corridor.  The
extra successor in the denominator is what lets `HalfPow.invSucc_den_le` pay
one full unit of the positive rational gap. -/
def decimationCorridorDepth (w : Q') : Nat :=
  400 * (((1 : Q') - w).den + 1)

theorem decimationCorridorDepth_positive (w : Q') :
    0 < decimationCorridorDepth w := by
  unfold decimationCorridorDepth
  omega

/-- Finite geometric cofactor coercivity:
`(1 + (n+1)(1-w)) * w^(n+1) <= 1` on `[0,1]`. -/
theorem one_add_gap_mul_qpow_succ_le_one
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (n : Nat) :
    ((1 : Q') +
        Q'.ofNat (n + 1) * ((1 : Q') - w)) *
          qpow w (n + 1) <=
      (1 : Q') := by
  let gap := (1 : Q') - w
  have hgap : (0 : Q') <= gap := Q'.sub_nonneg_of_le hw1
  have hpower : qpow w (n + 1) <= qpow w n :=
    qpow_succ_le hw0 hw1 n
  have hcoefficient :
      (0 : Q') <= Q'.ofNat (n + 1) * gap :=
    Q'.mul_nonneg _ _ (zero_le_ofNat (n + 1)) hgap
  have hpowerScaled :
      (Q'.ofNat (n + 1) * gap) * qpow w (n + 1) <=
        (Q'.ofNat (n + 1) * gap) * qpow w n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower hcoefficient
  have hgeom :
      Q'.ofNat (n + 1) * qpow w n <= geomSum w (n + 1) := by
    simpa only [Nat.add_sub_cancel] using
      (geomSum_ge_pow hw0 hw1 (n + 1))
  have hgeomScaled :
      gap * (Q'.ofNat (n + 1) * qpow w n) <=
        gap * geomSum w (n + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeom hgap
  have hreassociate :
      (Q'.ofNat (n + 1) * gap) * qpow w n ≈
        gap * (Q'.ofNat (n + 1) * qpow w n) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w n)
        (Q'.mul_comm_eqv (Q'.ofNat (n + 1)) gap)) ?_
    exact Q'.mul_assoc_eqv gap (Q'.ofNat (n + 1)) (qpow w n)
  have hcost :
      (Q'.ofNat (n + 1) * gap) * qpow w (n + 1) <=
        (1 : Q') - qpow w (n + 1) := by
    exact Q'.le_trans' _ _ _ hpowerScaled
      (Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassociate) hgeomScaled)
        (Q'.ge_of_eqv (oneSub_pow_factor w (n + 1))))
  have hadd :
      qpow w (n + 1) +
          (Q'.ofNat (n + 1) * gap) * qpow w (n + 1) <=
        (1 : Q') := by
    have hstep := Q'.add_le_add_left (qpow w (n + 1)) _ _ hcost
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (by
      show
        (qpow w (n + 1) +
          ((1 : Q') + -(qpow w (n + 1)))).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (qpow w (n + 1)) _ _
          (Q'.add_comm_eqv (1 : Q') (-(qpow w (n + 1))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.add_assoc_eqv (qpow w (n + 1))
            (-(qpow w (n + 1))) (1 : Q'))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (1 : Q')
          (Q'.add_neg_self_eqv (qpow w (n + 1)))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' (1 : Q'))))
  have hdistribute :
      (((1 : Q') + Q'.ofNat (n + 1) * gap) * qpow w (n + 1)) ≈
        (qpow w (n + 1) +
          (Q'.ofNat (n + 1) * gap) * qpow w (n + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 : Q')
        (Q'.ofNat (n + 1) * gap) (qpow w (n + 1))) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.one_mul_eqv (qpow w (n + 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdistribute) hadd

/-- Quotient form of the preceding finite geometric coercivity. -/
theorem qpow_succ_le_inverse_affine_gap
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (n : Nat) :
    let denominator :=
      (1 : Q') + Q'.ofNat (n + 1) * ((1 : Q') - w)
    qpow w (n + 1) <=
      Q'.divPos 1 denominator
        (Q'.pos_add_nonneg (by decide)
          (Q'.mul_nonneg _ _ (zero_le_ofNat (n + 1))
            (Q'.sub_nonneg_of_le hw1))) := by
  let denominator :=
    (1 : Q') + Q'.ofNat (n + 1) * ((1 : Q') - w)
  let hdenominator : (0 : Q') < denominator :=
    Q'.pos_add_nonneg (by decide)
      (Q'.mul_nonneg _ _ (zero_le_ofNat (n + 1))
        (Q'.sub_nonneg_of_le hw1))
  apply Q'.le_divPos_of_mul_le 1 denominator hdenominator
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv (qpow w (n + 1)) denominator))
    (one_add_gap_mul_qpow_succ_le_one hw0 hw1 n)

/-! ## 2. The explicit decimation depth enters the corridor -/

/-- At the explicit depth, the affine gap payment is at least `400`. -/
theorem decimationCorridorDepth_gap_payment
    {w : Q'} (hw1 : w < (1 : Q')) :
    Q'.ofNat 400 <=
      Q'.ofNat (decimationCorridorDepth w) * ((1 : Q') - w) := by
  let gap := (1 : Q') - w
  have hgapPositive : (0 : Q') < gap := one_sub_pos hw1
  have hinv : Q'.invSucc gap.den <= gap :=
    HalfPow.invSucc_den_le gap hgapPositive
  have hscaleNonnegative :
      (0 : Q') <= Q'.ofNat (decimationCorridorDepth w) :=
    zero_le_ofNat _
  have hscaled :
      Q'.ofNat (decimationCorridorDepth w) * Q'.invSucc gap.den <=
        Q'.ofNat (decimationCorridorDepth w) * gap :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinv hscaleNonnegative
  have hpayment :
      Q'.ofNat (decimationCorridorDepth w) * Q'.invSucc gap.den ≈
        Q'.ofNat 400 := by
    unfold decimationCorridorDepth
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (Q'.invSucc gap.den)
        (ofNat_mul_eqv 400 (gap.den + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 400)
        (Q'.ofNat (gap.den + 1)) (Q'.invSucc gap.den)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 400) _ _
        (Q'.ofNat_succ_mul_invSucc gap.den)) ?_
    exact Q'.mul_one_eqv (Q'.ofNat 400)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpayment) hscaled

/-- Exact heat-semigroup decimation reaches the production coupling corridor
at the displayed constructive depth. -/
theorem mkDecimate_decimationCorridorDepth_le_anchorCoupling
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    mkDecimate (decimationCorridorDepth w) w <= anchorCoupling := by
  let depth := decimationCorridorDepth w
  let gap := (1 : Q') - w
  let denominator := (1 : Q') + Q'.ofNat depth * gap
  have hdepth : 1 <= depth := by
    dsimp only [depth]
    exact decimationCorridorDepth_positive w
  have hdepthEq : depth - 1 + 1 = depth := Nat.sub_add_cancel hdepth
  have hdenominatorPositive : (0 : Q') < denominator :=
    Q'.pos_add_nonneg (by decide)
      (Q'.mul_nonneg _ _ (zero_le_ofNat depth)
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hpower : qpow w depth <=
      Q'.divPos 1 denominator hdenominatorPositive := by
    have hraw := qpow_succ_le_inverse_affine_gap
      hw0 (Q'.le_of_lt hw1) (depth - 1)
    simpa only [hdepthEq, depth, gap, denominator] using hraw
  have hpayment : Q'.ofNat 400 <= Q'.ofNat depth * gap := by
    simpa only [depth, gap] using
      (decimationCorridorDepth_gap_payment hw1)
  have hpaymentToDenominator :
      Q'.ofNat depth * gap <= denominator := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ (1 : Q') (by decide))
      (Q'.le_of_eqv
        (Q'.add_comm_eqv (Q'.ofNat depth * gap) (1 : Q')))
  have hfourHundred : Q'.ofNat 400 <= denominator :=
    Q'.le_trans' _ _ _ hpayment hpaymentToDenominator
  have hanchorNonnegative : (0 : Q') <= anchorCoupling := by
    unfold anchorCoupling
    decide
  have hscaled :
      anchorCoupling * Q'.ofNat 400 <=
        anchorCoupling * denominator :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfourHundred hanchorNonnegative
  have hanchorPayment : anchorCoupling * Q'.ofNat 400 ≈ (1 : Q') := by
    unfold anchorCoupling
    decide
  have hone : (1 : Q') <= anchorCoupling * denominator :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hanchorPayment) hscaled
  have hquotient :
      Q'.divPos 1 denominator hdenominatorPositive <= anchorCoupling :=
    Q'.divPos_le_of_le_mul 1 denominator hdenominatorPositive hone
  unfold mkDecimate
  exact Q'.le_trans' _ _ _ hpower hquotient

/-- The decimated exact residual coefficient is therefore accepted by the
coefficient-level observable inverse-fiber theorem. -/
theorem mkDecimate_decimationCorridorDepth_zeroCoefficient_le
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w < (1 : Q')) :
    exteriorFaceCoefficient
        (mkDecimate (decimationCorridorDepth w) w) 0 <=
      anchorFaceCoefficient := by
  exact exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
    (mkDecimate_nonneg _ hw0)
    (mkDecimate_decimationCorridorDepth_le_anchorCoupling hw0 hw1)

private theorem qpow_pos_local {w : Q'} (hw0 : (0 : Q') < w) :
    forall exponent : Nat, (0 : Q') < qpow w exponent
  | 0 => by
      show (0 : Q') < (1 : Q')
      decide
  | exponent + 1 => Q'.mul_pos (qpow_pos_local hw0 exponent) hw0

/-- The slab built at the exactly decimated coupling satisfies the complete
finite-volume face-covariance envelope.  This is a theorem about the decimated
datum itself; no comparison with the original datum is asserted. -/
theorem decimatedSlabObservableFaceBooleanCovariance_le_anchorRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half)) :
    let effective := mkDecimate (decimationCorridorDepth w) w
    let D := observableCouplingSlabPhysicalData
      effective (mkDecimate_nonneg _ (Q'.le_of_lt hw0)) cutoff half
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  let effective := mkDecimate (decimationCorridorDepth w) w
  let heffectiveNonnegative : (0 : Q') <= effective :=
    mkDecimate_nonneg _ (Q'.le_of_lt hw0)
  let D := observableCouplingSlabPhysicalData
    effective heffectiveNonnegative cutoff half
  have heffectivePositive : (0 : Q') < effective := by
    exact qpow_pos_local hw0 (decimationCorridorDepth w)
  have heffectiveAnchor : effective <= anchorCoupling :=
    mkDecimate_decimationCorridorDepth_le_anchorCoupling
      (Q'.le_of_lt hw0) hw1
  have heffectiveLtOne : effective < (1 : Q') :=
    Q'.lt_of_le_of_lt heffectiveAnchor (by
      unfold anchorCoupling
      decide)
  have hcoefficient :
      exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient := by
    simpa only [D, observableCouplingSlabPhysicalData] using
      (mkDecimate_decimationCorridorDepth_zeroCoefficient_le
        (Q'.le_of_lt hw0) hw1)
  apply slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
    D heffectivePositive heffectiveLtOne hcoefficient
      rootFaceId targetFaceId
  simpa only [D, observableCouplingSlabPhysicalData,
    SlabPhysicalData.extent] using htarget

#print axioms decimationCorridorDepth
#print axioms one_add_gap_mul_qpow_succ_le_one
#print axioms qpow_succ_le_inverse_affine_gap
#print axioms decimationCorridorDepth_gap_payment
#print axioms mkDecimate_decimationCorridorDepth_le_anchorCoupling
#print axioms mkDecimate_decimationCorridorDepth_zeroCoefficient_le
#print axioms decimatedSlabObservableFaceBooleanCovariance_le_anchorRate

end YMGap.Continuum.CompactDualSlabObservablePairedSupportDecimationCorridor
