/-
# Original connected Wilson scalars and their SAME limiting form

The joint expectation and both unit marginals use one common observation
window, spatial margin, cutoff, external boundary depth, selected action
and partition. Their three-regulator diagonal converges to the existing
intrinsic connected form. Physical lag stays fixed while those regulators
recede; unit invariance identifies its unchanged marginal.

This supplies the limit pin consumed by the separate covariance estimate.
It assumes no decay or strict gap and constructs no alternate state.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base : Nat}

/-- One actual selected-chain expectation, at the displayed common chart. -/
def chartPairing (H r stage t : Nat) (x y : IntrinsicExpression base) : Q' :=
  chartScalar hw0 hw1 H (.mul (mirror H (chart H x)) (chart H y)) r stage t

/-- The SAME partition occurs in the joint term and both unit marginals. -/
def connectedScalar (H r stage t : Nat) (x y : IntrinsicExpression base) : Q' :=
  chartPairing hw0 hw1 H r stage t x y +
    -(chartPairing hw0 hw1 H r stage t x (unit base) *
      chartPairing hw0 hw1 H r stage t (unit base) y)

attribute [local irreducible] intrinsicForm spatialLimit

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb

/-- Each actual reflected product retains its own existing explicit modulus. -/
theorem chartPairing_diagonal_converges (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    ConvergesTo (fun k => ofQ' (chartPairing hw0 hw1 H k k k x y)) (F x y) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (spatial_diagonal_converges hw0 hw1 H
      (.mul (mirror H (chart H x)) (chart H y))
      ⟨mirror_within H (chart H x),
        within_mono (by omega : H ≤ 2*H) _ (chart_within H y hy)⟩ hsmall hd hs hb)
    (intrinsicForm_chart hw0 hw1 hsmall hd hs hb x y H hx hy).symm

/-- A single original action family supplies the limiting connected scalar. -/
theorem connectedScalar_diagonal_converges (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    ConvergesTo (fun k => ofQ' (connectedScalar hw0 hw1 H k k k x y))
      (sub (F x y) (mul (F x (unit base)) (F (unit base) y))) := by
  have hxy := chartPairing_diagonal_converges hw0 hw1 hsmall hd hs hb H x y hx hy
  have hxu := chartPairing_diagonal_converges hw0 hw1 hsmall hd hs hb H x (unit base) hx
    (Nat.zero_le H)
  have huy := chartPairing_diagonal_converges hw0 hw1 hsmall hd hs hb H (unit base) y
    (Nat.zero_le H) hy
  have hprod :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxu huy
  have h := TrigAddCReal.convergesTo_add hxy (TrigAddCReal.convergesTo_neg hprod)
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) h

/-- The physical time and all three receding regulator indices stay distinct. -/
theorem connectedScalar_time_converges (n H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius+n ≤ H) :
    ConvergesTo (fun k => ofQ' (connectedScalar hw0 hw1 H k k k x (advance n y)))
      (sub (F x (advance n y)) (mul (F x (unit base)) (F (unit base) y))) := by
  have hm : Equiv (F (unit base) (advance n y)) (F (unit base) y) :=
    (intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb n (unit base) y).symm.trans
      (intrinsicForm_advanced_unit_left hw0 hw1 hsmall hd hs hb n y)
  exact ArctanTrigConvergesProof.convergesTo_of_equiv
    (connectedScalar_diagonal_converges hw0 hw1 hsmall hd hs hb H x (advance n y) hx hy)
    (Equiv_add (Equiv.refl _) (neg_congr (TrigSignedAdd.mul_congr_right hm)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.chartPairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.connectedScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.chartPairing_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.connectedScalar_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.connectedScalar_time_converges
