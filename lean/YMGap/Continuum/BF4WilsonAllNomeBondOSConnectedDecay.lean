/-
# Mixed connected decay on the original physical Wilson bond completion

The two inputs are arbitrary completed bond classes. Their connected pairing
uses the original odd-window bond inner product, vacuum, and time action.
At each fixed nome and spatial width, its even-lag square is bounded by the
product of the two actual bond variances, each with the existing geometric
factor `twoStepRate ^ n`. The original finite-source pin retains signed terms
in BOTH sources and uses the original normalized odd reflected joint limit.

The positive-time action is used only at a strictly positive integer lag.
This supplies no width- or spacing-uniform estimate, bare time-zero Wilson
multiplier, physical mass calibration, or continuum OS reconstruction.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.BF4WilsonAllNomeUnitProjection
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance advance_zero advance_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_symm completedInner_nonnegative completedInner_cauchySchwarz
    unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_zero completedTime_add completedInner_time_sum)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
  (completedCenteredScalar completed_iterated_norm_gap)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (centeredPart centeredPart_orthogonal centeredPart_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
  (bondForm image_advance image_unit)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion ofSource bondCompletedInner constant_pairing)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_inner bondValue_ofSource bondAction bondAction_value vacuum)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
  (Word wordAct wordAct_ofSource sourceWord)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "V" => Completion hw0 hw1 width
local notation "BV" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- The original completed bond covariance, with no selected representative. -/
def connected (lag : Nat) (x y : H) : RC :=
  completedCenteredScalar hw0 hw1 width lag
    (bondValue hw0 hw1 x) (bondValue hw0 hw1 y)

private theorem bondValue_vacuum :
    bondValue hw0 hw1 (vacuum hw0 hw1 (width := width)) = U := by
  rw [vacuum, bondValue_ofSource, image_unit]

/-- For positive integer lag this is the actual bond time action, rather than
a separately supplied or legacy transfer. -/
theorem connected_positive_action (lag : Nat) (hlag : 0 < lag) (x y : H) :
    connected hw0 hw1 lag x y =
      RCsub (B x (bondAction hw0 hw1 (dyadicTime ⟨0,lag⟩ hlag) y))
        (RCmul (B x (vacuum hw0 hw1 (width := width)))
          (B (vacuum hw0 hw1 (width := width)) y)) := by
  unfold connected completedCenteredScalar
  rw [bondValue_inner, bondAction_value, positiveAction_original,
    bondValue_inner, bondValue_inner, bondValue_vacuum]

private theorem bondValue_advance (lag : Nat) (x : IntrinsicExpression width) :
    bondValue hw0 hw1 (ofSource hw0 hw1 (advance lag x)) =
      T lag (bondValue hw0 hw1 (ofSource hw0 hw1 x)) := by
  induction lag with
  | zero =>
      rw [advance_zero, completedTime_zero]
  | succ n ih =>
      have hadvance : advance (n+1) x = advance 1 (advance n x) := by
        rw [advance_add]
        congr 1
        omega
      calc
        bondValue hw0 hw1 (ofSource hw0 hw1 (advance (n+1) x))
            = bondValue hw0 hw1 (ofSource hw0 hw1 (advance 1 (advance n x))) :=
              congrArg (fun z : IntrinsicExpression width =>
                bondValue hw0 hw1 (ofSource hw0 hw1 z)) hadvance
        _ = T 1 (bondValue hw0 hw1 (ofSource hw0 hw1 (advance n x))) := by
              rw [bondValue_ofSource, image_advance, ← bondValue_ofSource]
        _ = T 1 (T n (bondValue hw0 hw1 (ofSource hw0 hw1 x))) :=
              congrArg (T 1) ih
        _ = T (n+1) (bondValue hw0 hw1 (ofSource hw0 hw1 x)) := by
              rw [← completedTime_add]
              congr 1
              omega

/-- Exact original odd reflected joint pin, including signed cross terms
inside each of the two independently supplied source expressions. -/
theorem connected_source_pin (lag : Nat)
    (x y : IntrinsicExpression width) :
    connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      RCsub (bondForm hw0 hw1 x (advance lag y))
        (RCmul (bondForm hw0 hw1 x (unit width))
          (bondForm hw0 hw1 (unit width) y)) := by
  unfold connected completedCenteredScalar
  rw [← bondValue_advance hw0 hw1 lag y,
    ← bondValue_vacuum hw0 hw1 (width := width),
    ← bondValue_inner, ← bondValue_inner, ← bondValue_inner]
  change RCsub (B (ofSource hw0 hw1 x) (ofSource hw0 hw1 (advance lag y)))
    (RCmul (B (ofSource hw0 hw1 x) (ofSource hw0 hw1 (unit width)))
      (B (ofSource hw0 hw1 (unit width)) (ofSource hw0 hw1 y))) = _
  rw [constant_pairing, constant_pairing, constant_pairing]

private theorem RCmul_mono_nonnegative_left {factor a b : RC}
    (hfactor : RCnonneg factor) (hab : RCle a b) :
    RCle (RCmul factor a) (RCmul factor b) := by
  revert hfactor hab
  refine Quotient.inductionOn₃ factor a b ?_
  intro realFactor realLower realUpper hNonneg hOrder
  exact leEv_mul_nonneg_left hNonneg hOrder

/-- The norm factors are exactly the original completed bond variances
`connected 0 x x` and `connected 0 y y`, not bare Haar variances. Writing the
right side as a product of two `q^n`-scaled factors avoids any square root. -/
theorem connected_even_lag_sq_decay (n : Nat) (x y : H) :
    RCle (RCmul (connected hw0 hw1 (2*n) x y)
      (connected hw0 hw1 (2*n) x y))
      (RCmul (RCscale (q^n) (connected hw0 hw1 0 x x))
        (RCscale (q^n) (connected hw0 hw1 0 y y))) := by
  let X : V := bondValue hw0 hw1 x
  let Y : V := bondValue hw0 hw1 y
  let cX : V := centeredPart hw0 hw1 X
  let cY : V := centeredPart hw0 hw1 Y
  have hx : BV cX U = RCzero :=
    (completedInner_symm hw0 hw1 cX U).trans
      (centeredPart_orthogonal hw0 hw1 X)
  have hy : BV cY U = RCzero :=
    (completedInner_symm hw0 hw1 cY U).trans
      (centeredPart_orthogonal hw0 hw1 Y)
  have hxy : connected hw0 hw1 (2*n) x y = BV (T n cX) (T n cY) := by
    unfold connected
    rw [show 2*n = n+n by omega]
    exact (centeredPart_time_pairing hw0 hw1 (n+n) X Y).symm.trans
      (completedInner_time_sum hw0 hw1 n n cX cY).symm
  have hxx : connected hw0 hw1 0 x x = BV cX cX := by
    unfold connected completedCenteredScalar
    rw [← centeredPart_time_pairing hw0 hw1 0 X X, completedTime_zero]
  have hyy : connected hw0 hw1 0 y y = BV cY cY := by
    unfold connected completedCenteredScalar
    rw [← centeredPart_time_pairing hw0 hw1 0 Y Y, completedTime_zero]
  rw [hxy, hxx, hyy]
  have hcs := completedInner_cauchySchwarz hw0 hw1 (T n cX) (T n cY)
  have hxn := completed_iterated_norm_gap hw0 hw1 width n cX hx
  have hyn := completed_iterated_norm_gap hw0 hw1 width n cY hy
  have hYn : RCnonneg (BV (T n cY) (T n cY)) :=
    completedInner_nonnegative hw0 hw1 (T n cY)
  have hrate : (0 : Q') ≤ q^n :=
    Q'.pow_nonneg q (twoStepRate_nonnegative hw0 hw1 width) n
  have hXscaled : RCnonneg (RCscale (q^n) (BV cX cX)) := by
    change RCle RCzero (RCscale (q^n) (BV cX cX))
    rw [← RCscale_RCzero (q^n)]
    exact RCscale_mono hrate (completedInner_nonnegative hw0 hw1 cX)
  have hfirst := RCmul_mono_nonnegative_left hYn hxn
  rw [RCmul_comm (BV (T n cY) (T n cY)) (BV (T n cX) (T n cX)),
    RCmul_comm (BV (T n cY) (T n cY))
      (RCscale (q^n) (BV cX cX))] at hfirst
  have hsecond := RCmul_mono_nonnegative_left hXscaled hyn
  exact RCle_trans hcs (RCle_trans hfirst hsecond)

/-- Arbitrary finite one-step-separated Wilson words are particular source
classes, so their two-cluster connected covariance obeys the same bound. -/
theorem connected_word_sq_decay (n : Nat) (left right : Word width) :
    RCle (RCmul
      (connected hw0 hw1 (2*n)
        (wordAct hw0 hw1 left (vacuum hw0 hw1 (width := width)))
        (wordAct hw0 hw1 right (vacuum hw0 hw1 (width := width))))
      (connected hw0 hw1 (2*n)
        (wordAct hw0 hw1 left (vacuum hw0 hw1 (width := width)))
        (wordAct hw0 hw1 right (vacuum hw0 hw1 (width := width)))))
      (RCmul
        (RCscale (q^n) (connected hw0 hw1 0
          (wordAct hw0 hw1 left (vacuum hw0 hw1 (width := width)))
          (wordAct hw0 hw1 left (vacuum hw0 hw1 (width := width)))))
        (RCscale (q^n) (connected hw0 hw1 0
          (wordAct hw0 hw1 right (vacuum hw0 hw1 (width := width)))
          (wordAct hw0 hw1 right (vacuum hw0 hw1 (width := width)))))) :=
  connected_even_lag_sq_decay hw0 hw1 n _ _

theorem connected_word_source_pin (lag : Nat) (left right : Word width) :
    connected hw0 hw1 lag
      (wordAct hw0 hw1 left (vacuum hw0 hw1 (width := width)))
      (wordAct hw0 hw1 right (vacuum hw0 hw1 (width := width))) =
      RCsub (bondForm hw0 hw1
        (sourceWord left (unit width))
        (advance lag (sourceWord right (unit width))))
        (RCmul
          (bondForm hw0 hw1 (sourceWord left (unit width)) (unit width))
          (bondForm hw0 hw1 (unit width) (sourceWord right (unit width)))) := by
  change connected hw0 hw1 lag
    (wordAct hw0 hw1 left (ofSource hw0 hw1 (unit width)))
    (wordAct hw0 hw1 right (ofSource hw0 hw1 (unit width))) = _
  rw [wordAct_ofSource, wordAct_ofSource]
  exact connected_source_pin hw0 hw1 lag _ _

#print axioms connected
#print axioms connected_positive_action
#print axioms bondValue_advance
#print axioms connected_source_pin
#print axioms RCmul_mono_nonnegative_left
#print axioms connected_even_lag_sq_decay
#print axioms connected_word_sq_decay
#print axioms connected_word_source_pin

end YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay
