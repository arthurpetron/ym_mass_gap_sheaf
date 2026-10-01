/-
# Sharp mixed complex connected decay on the ORIGINAL physical bond carrier

The variance is the sum of the two actual centered physical bond variances.
The sharp complex phase inequality avoids a factor-two loss from separately
bounding four real pairings. All signed source terms and both marginal means
remain in the ORIGINAL reflected joint limits. Nome and width are fixed;
this is neither spacing-uniform decay nor a physical Hamiltonian mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
import YMGap.Continuum.BF4WilsonAllNomeComplexCauchySchwarz
import YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay
import YMGap.Continuum.BF4WilsonAllNomeComplexGap

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSConnectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_symm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (centeredPart centeredPart_orthogonal centeredPart_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Source value ofSource)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (ComplexValue ComplexCarrier complexTime inner)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "I" => inner hw0 hw1 width
local notation "T" => complexTime hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width
local notation "C" => BF4WilsonAllNomeBondOSConnectedDecay.connected hw0 hw1

/-- Sesquilinear covariance, with the two ORIGINAL marginal means. -/
def connected (lag : Nat) (x y : H) : ComplexValue :=
  (RCadd (C lag x.1 y.1) (C lag x.2 y.2),
   RCsub (C lag x.1 y.2) (C lag x.2 y.1))

def centeredValue (x : H) : VC :=
  (centeredPart hw0 hw1 (value hw0 hw1 x).1,
   centeredPart hw0 hw1 (value hw0 hw1 x).2)

theorem connected_centered_pairing (lag : Nat) (x y : H) :
    connected hw0 hw1 lag x y = I (centeredValue hw0 hw1 x) (T lag (centeredValue hw0 hw1 y)) := by
  simp only [connected,BF4WilsonAllNomeBondOSConnectedDecay.connected,
    completedCenteredScalar,centeredValue,value,inner,complexTime,centeredPart_time_pairing]

def variance (x : H) : RC := (connected hw0 hw1 0 x x).1

/-- This is exactly the two ORIGINAL physical centered variances. -/
theorem variance_pin (x : H) :
    variance hw0 hw1 x = (I (centeredValue hw0 hw1 x) (centeredValue hw0 hw1 x)).1 := by
  rw [variance,connected_centered_pairing,BF4WilsonAllNomeComplexification.complexTime_zero]

theorem variance_nonnegative (x : H) : RCnonneg (variance hw0 hw1 x) := by
  rw [variance_pin]
  exact BF4WilsonAllNomeComplexification.inner_nonnegative hw0 hw1 width _

theorem centeredValue_orthogonal (x : H) :
    I (BF4WilsonAllNomeComplexGap.complexUnit hw0 hw1 width)
      (centeredValue hw0 hw1 x) = (RCzero,RCzero) := by
  apply (BF4WilsonAllNomeComplexGap.complex_orthogonal_iff hw0 hw1 width _).mpr
  constructor
  · exact (completedInner_symm hw0 hw1 _ _).trans (centeredPart_orthogonal hw0 hw1 _)
  · exact (completedInner_symm hw0 hw1 _ _).trans (centeredPart_orthogonal hw0 hw1 _)

private theorem RCmul_mono_nonnegative_left {factor a b : RC}
    (hfactor : RCnonneg factor) (hab : RCle a b) :
    RCle (RCmul factor a) (RCmul factor b) := by
  revert hfactor hab
  refine Quotient.inductionOn₃ factor a b ?_
  intro realFactor realLower realUpper hNonneg hOrder
  exact leEv_mul_nonneg_left hNonneg hOrder

/-- Sharp mixed bound at EVERY even lag, with no inverse/square root of a
variance and no additional analytic hypothesis. The SAME fixed q is retained. -/
theorem connected_even_lag_modulus_sq_decay (n : Nat) (x y : H) :
    RCle
      (RCadd (RCmul (connected hw0 hw1 (2*n) x y).1 (connected hw0 hw1 (2*n) x y).1)
        (RCmul (connected hw0 hw1 (2*n) x y).2 (connected hw0 hw1 (2*n) x y).2))
      (RCmul (RCscale (q^n) (variance hw0 hw1 x)) (RCscale (q^n) (variance hw0 hw1 y))) := by
  let X := centeredValue hw0 hw1 x
  let Y := centeredValue hw0 hw1 y
  have hxy : connected hw0 hw1 (2*n) x y = I (T n X) (T n Y) := by
    rw [connected_centered_pairing,show 2*n=n+n by omega]
    exact (BF4WilsonAllNomeComplexGap.inner_time_sum hw0 hw1 width n n X Y).symm
  rw [hxy,variance_pin,variance_pin]
  have hcs := BF4WilsonAllNomeComplexCauchySchwarz.inner_cauchySchwarz hw0 hw1 width (T n X) (T n Y)
  have hx := BF4WilsonAllNomeComplexGap.complex_iterated_norm_gap hw0 hw1 width n X
    (centeredValue_orthogonal hw0 hw1 x)
  have hy := BF4WilsonAllNomeComplexGap.complex_iterated_norm_gap hw0 hw1 width n Y
    (centeredValue_orthogonal hw0 hw1 y)
  have hY : RCnonneg (I (T n Y) (T n Y)).1 :=
    BF4WilsonAllNomeComplexification.inner_nonnegative hw0 hw1 width _
  have hXscaled : RCnonneg (RCscale (q^n) (I X X).1) :=
    RCle_trans (BF4WilsonAllNomeComplexification.inner_nonnegative hw0 hw1 width (T n X)) hx
  have hfirst := RCmul_mono_nonnegative_left hY hx
  rw [RCmul_comm (I (T n Y) (T n Y)).1 (I (T n X) (T n X)).1,
    RCmul_comm (I (T n Y) (T n Y)).1 (RCscale (q^n) (I X X).1)] at hfirst
  exact RCle_trans hcs (RCle_trans hfirst (RCmul_mono_nonnegative_left hXscaled hy))

/-- Each component retains its complete ORIGINAL signed source and mean. -/
def sourceCovariance (lag : Nat) (x y : IntrinsicExpression width) : RC :=
  RCsub (bondForm hw0 hw1 x (advance lag y))
    (RCmul (bondForm hw0 hw1 x (unit width)) (bondForm hw0 hw1 (unit width) y))

theorem connected_source_pin (lag : Nat) (x y : Source width) :
    connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      (RCadd (sourceCovariance hw0 hw1 lag x.1 y.1) (sourceCovariance hw0 hw1 lag x.2 y.2),
       RCsub (sourceCovariance hw0 hw1 lag x.1 y.2) (sourceCovariance hw0 hw1 lag x.2 y.1)) := by
  simp only [connected,ofSource,BF4WilsonAllNomeBondOSConnectedDecay.connected_source_pin,sourceCovariance]

#print axioms connected
#print axioms connected_centered_pairing
#print axioms variance_pin
#print axioms variance_nonnegative
#print axioms centeredValue_orthogonal
#print axioms connected_even_lag_modulus_sq_decay
#print axioms connected_source_pin

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSConnectedDecay
