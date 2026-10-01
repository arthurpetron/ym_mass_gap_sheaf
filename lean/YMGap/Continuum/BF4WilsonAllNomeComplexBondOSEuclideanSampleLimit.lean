/-
# Original Euclidean action at rational samples of a supplied real time

This file compares the original all-nome Wilson time action at the rational
samples of one supplied positive-time datum with its action at that datum.
It uses the original dyadic mesh estimate and the source's original range
modulus.  The numerical time constructors are shared with the older slab
files, but NO older slab action or completion is used.  The comparison is
on a supplied represented physical graph point and has a computed rate.

It does not identify the rational Cayley stream with the Euclidean mesh
stream, nor assert a physical clock, generator or continuum limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
import YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSEuclideanSampleLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.PositiveRealDyadicTimeData
  (PositiveTime rational sample sample_lower approximation approximation_lower)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (timeValue realValue realValue_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealContinuity
  (time_lower_eventually time_close_eventually timeRadius timeRadius_positive
    timeRadius_twice)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist completedDist_symm)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (positiveAction mesh_close_bound convergenceModulus approximation_bound
    half_power_positive)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (realTimeAction realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity
  (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
  (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion distance distance_value value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Point ofPoint input value_input_ofPoint)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "P" => Point hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid PD)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def timeFloorHalf (D : PositiveTime) : Q' := half*D.floor

private theorem timeFloorHalf_positive (D : PositiveTime) :
    (0 : Q') < timeFloorHalf D :=
  ExpNeg.half_mul_pos D.floor D.floor_positive

private theorem timeFloorHalf_two (D : PositiveTime) :
    Q'.eqv (timeFloorHalf D+timeFloorHalf D) D.floor :=
  ExpNeg.two_halves D.floor

private theorem sample_positive (D : PositiveTime) (n : Nat) :
    (0 : Q') < sample D n :=
  ClusteringImpliesGap.lt_of_lt_of_le D.floor_positive (sample_lower D n)

/-- A source-independent clock comparison. The rate comes from the supplied
time datum's QCauchy modulus; no RC-order witness is extracted as data. -/
private theorem clock_sample_close (D : PositiveTime) (r : Q')
    (hr : (0 : Q') < r) (n : Nat)
    (hn : D.cauchy.M (half*r) ≤ n) :
    RCle (realValue (timeValue D))
      (RCadd (rat (sample D n)) (rat r)) ∧
    RCle (rat (sample D n))
      (RCadd (realValue (timeValue D)) (rat r)) := by
  let h := half*r
  have hh : (0 : Q') < h := ExpNeg.half_mul_pos r hr
  have hle : h ≤ r :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg h h (Q'.le_of_lt hh))
      (Q'.le_of_eqv (ExpNeg.two_halves r))
  have hn' : D.cauchy.M h ≤ D.start+n :=
    Nat.le_trans hn (Nat.le_add_left _ _)
  constructor
  · rw [realValue_pin]
    change leEv D.real (CReal.add (ofQ' (sample D n)) (ofQ' r))
    intro e he
    refine ⟨D.cauchy.M h,fun j hj => ?_⟩
    have hc := D.cauchy.bound h hh (D.start+n) j hn' hj
    exact Q'.le_trans' _ _ _ hc.2
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hle)
        (Q'.add_le_self_of_nonneg _ e (Q'.le_of_lt he)))
  · rw [realValue_pin]
    change leEv (ofQ' (sample D n)) (CReal.add D.real (ofQ' r))
    intro e he
    refine ⟨D.cauchy.M h,fun j hj => ?_⟩
    have hc := D.cauchy.bound h hh (D.start+n) j hn' hj
    exact Q'.le_trans' _ _ _ hc.1
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hle)
        (Q'.add_le_self_of_nonneg _ e (Q'.le_of_lt he)))

private theorem clock_floor (D : PositiveTime) :
    RCle (rat (timeFloorHalf D+timeFloorHalf D))
      (realValue (timeValue D)) := by
  rw [realValue_pin]
  change leEv (ofQ' (timeFloorHalf D+timeFloorHalf D)) D.real
  intro e he
  refine ⟨D.start,fun j hj => ?_⟩
  have hf : timeFloorHalf D+timeFloorHalf D ≤ D.floor :=
    Q'.le_of_eqv (timeFloorHalf_two D)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hf (D.lower j hj))
    (Q'.add_le_self_of_nonneg _ e (Q'.le_of_lt he))

private theorem sample_floor (D : PositiveTime) (n : Nat) :
    RCle (rat (timeFloorHalf D+timeFloorHalf D))
      (realValue (timeValue (rational (sample D n) (sample_positive D n)))) := by
  rw [realValue_pin]
  change leEv (ofQ' (timeFloorHalf D+timeFloorHalf D)) (ofQ' (sample D n))
  exact leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (timeFloorHalf_two D)) (sample_lower D n))

/-- The ORIGINAL Wilson mesh continuity, with the original source modulus.
The two times have numerical time-value proximity, but the estimate is on
the all-nome Wilson completion, not the older slab completion. -/
theorem original_time_close (D E : PositiveTime) (X : (PD).Cauchy)
    (e : Q') (he : (0 : Q') < e) (b : Q') (hb : (0 : Q') < b)
    (hD : RCle (rat (b+b)) (realValue (timeValue D)))
    (hE : RCle (rat (b+b)) (realValue (timeValue E)))
    (hDE : RCle (realValue (timeValue D))
      (RCadd (realValue (timeValue E))
        (rat (timeRadius b (rangeModulus hw0 hw1 X (quarter (quarter e)))))))
    (hED : RCle (realValue (timeValue E))
      (RCadd (realValue (timeValue D))
        (rat (timeRadius b (rangeModulus hw0 hw1 X (quarter (quarter e))))))) :
    RCle (dist (realTimeAction hw0 hw1 (timeValue D) (Class X))
      (realTimeAction hw0 hw1 (timeValue E) (Class X))) (rat e) := by
  let q := quarter (quarter e)
  have hq : (0 : Q') < q := quarter_pos (quarter_pos he)
  let k := rangeModulus hw0 hw1 X q
  let r := timeRadius b k
  have hr : (0 : Q') < r := timeRadius_positive b hb k
  obtain ⟨ND,hND⟩ := time_lower_eventually D b hb hD
  obtain ⟨NE,hNE⟩ := time_lower_eventually E b hb hE
  obtain ⟨NP,hNP⟩ := time_close_eventually D E r hr hDE
  obtain ⟨NQ,hNQ⟩ := time_close_eventually E D r hr hED
  let n := max (max
    (BF4WilsonAllNomePositiveTimeAction.convergenceModulus hw0 hw1 D X q)
    (BF4WilsonAllNomePositiveTimeAction.convergenceModulus hw0 hw1 E X q))
    (max (max ND NE) (max NP NQ))
  have hrateD : convergenceModulus hw0 hw1 D X q ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hrateE : convergenceModulus hw0 hw1 E X q ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have htail : max (max ND NE) (max NP NQ) ≤ n := Nat.le_max_right _ _
  have hND' : ND ≤ n := Nat.le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) htail
  have hNE' : NE ≤ n := Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) htail
  have hNP' : NP ≤ n := Nat.le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) htail
  have hNQ' : NQ ≤ n := Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) htail
  have hleft := approximation_bound hw0 hw1 D X q hq n hrateD
  have hright := approximation_bound hw0 hw1 E X q hq n hrateE
  have hval : Q'.eqv (r+r) (b*HalfPow.half^k) :=
    timeRadius_twice b k
  have hDE' :
      DyadicTimeRationals.value (approximation D n) ≤
        DyadicTimeRationals.value (approximation E n)+b*HalfPow.half^k :=
    Q'.le_trans' _ _ _ (hNP n hNP')
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv hval))
  have hED' :
      DyadicTimeRationals.value (approximation E n) ≤
        DyadicTimeRationals.value (approximation D n)+b*HalfPow.half^k :=
    Q'.le_trans' _ _ _ (hNQ n hNQ')
      (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv hval))
  have hmiddle := RCle_trans
    (mesh_close_bound hw0 hw1 (approximation D n) (approximation E n)
      k b (hND n hND') (hNE n hNE') hDE' hED' (Class X))
    (scaled_norm_small hw0 hw1 X q hq k (Nat.le_refl _))
  simp only [BF4WilsonAllNomePositiveTimePins.realTimeAction_pin]
  rw [completedDist_symm] at hleft
  exact CRealSeminormCompletedApproximation.completedDist_three_segment
    (BF4WilsonAllNomeDistance.distanceData hw0 hw1 (width := width))
    _ _ _ _ e he hleft hmiddle hright

private def sourceFirst (p : P) : (PD).Cauchy :=
  representative hw0 hw1 p.1.input.range

private def sourceSecond (p : P) : (PD).Cauchy :=
  representative hw0 hw1 p.2.input.range

private def sourceRadiusFirst (p : P) (D : PositiveTime) (e : Q') : Q' :=
  timeRadius (timeFloorHalf D)
    (rangeModulus hw0 hw1 (sourceFirst hw0 hw1 p)
      (quarter (quarter (half*e))))

private def sourceRadiusSecond (p : P) (D : PositiveTime) (e : Q') : Q' :=
  timeRadius (timeFloorHalf D)
    (rangeModulus hw0 hw1 (sourceSecond hw0 hw1 p)
      (quarter (quarter (half*e))))

/-- Computed from the supplied numerical QCauchy modulus and BOTH original
source representatives. No quotient-class-to-rate choice is involved. -/
def euclideanSampleRate (p : P) (D : PositiveTime) (e : Q') : Nat :=
  max (D.cauchy.M (half*sourceRadiusFirst hw0 hw1 p D e))
    (D.cauchy.M (half*sourceRadiusSecond hw0 hw1 p D e))

/-- The original Euclidean action at the rational samples converges to its
action at the supplied positive real time, in the SAME physical complex bond
distance and with a computed source/time rate. The Cayley samples are not
identified with the Euclidean mesh stages. -/
theorem euclidean_sample_bound (p : P) (D : PositiveTime)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : euclideanSampleRate hw0 hw1 p D e ≤ n) :
    RCle (distance hw0 hw1
      (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1 (timeValue D)
        (input hw0 hw1 (ofPoint hw0 hw1 p)))
      (BF4WilsonAllNomeComplexBondOSTime.action hw0 hw1
        (timeValue (rational (sample D n) (sample_positive D n)))
        (input hw0 hw1 (ofPoint hw0 hw1 p)))) (rat e) := by
  let b := timeFloorHalf D
  have hb : (0 : Q') < b := timeFloorHalf_positive D
  let q := half*e
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos e he
  let X := sourceFirst hw0 hw1 p
  let Y := sourceSecond hw0 hw1 p
  let rX := sourceRadiusFirst hw0 hw1 p D e
  let rY := sourceRadiusSecond hw0 hw1 p D e
  have hrX : (0 : Q') < rX := timeRadius_positive b hb _
  have hrY : (0 : Q') < rY := timeRadius_positive b hb _
  have hnX : D.cauchy.M (half*rX) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnY : D.cauchy.M (half*rY) ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hcX := clock_sample_close D rX hrX n hnX
  have hcY := clock_sample_close D rY hrY n hnY
  have hD := clock_floor D
  have hS := sample_floor D n
  have hfirst := original_time_close hw0 hw1 D
    (rational (sample D n) (sample_positive D n)) X q hq b hb
    hD hS hcX.1 hcX.2
  have hsecond := original_time_close hw0 hw1 D
    (rational (sample D n) (sample_positive D n)) Y q hq b hb
    hD hS hcY.1 hcY.2
  have hpX : Class X = p.1.input.val :=
    representative_pin hw0 hw1 p.1.input.range
  have hpY : Class Y = p.2.input.val :=
    representative_pin hw0 hw1 p.2.input.range
  rw [hpX] at hfirst
  rw [hpY] at hsecond
  rw [distance_value,
    BF4WilsonAllNomeComplexBondOSTime.action_value,
    BF4WilsonAllNomeComplexBondOSTime.action_value,
    value_input_ofPoint]
  have hhalf : RCadd (rat q) (rat q) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => ExpNeg.two_halves e))
  rw [← hhalf]
  exact RCadd_le_add hfirst hsecond

#print axioms euclideanSampleRate
#print axioms original_time_close
#print axioms euclidean_sample_bound

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSEuclideanSampleLimit
