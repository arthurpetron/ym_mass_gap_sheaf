/-
# Actual quotient convergence constructs its own original input-range witness

Every fixed-depth root image has an explicit original time-range witness.
At depth n, choose one of its time preimages at invSucc(n) accuracy.
The actual derivative-limit modulus controls the distance of that root
image to the input. An explicit diagonal therefore constructs the INPUT
range witness rather than assuming it. The existing output-range and
graph constructions then apply with neither coordinate range as a premise.

This identifies represented differentiable pairs with represented graph
data, not all ambient states as differentiable. In particular, a
differentiable original time-kernel input must be zero. No boundary state
is removed from the carrier, and no self-adjointness or physical calibration
is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
import YMGap.Continuum.BF4WilsonAllNomeDerivativeRootContinuity
import YMGap.Continuum.BF4WilsonAllNomeDerivativeOutputRange
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeInputRange

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters)
open YMGap.Continuum.BF4WilsonAllNomeRootTimeRange (rootRange)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeRootContinuity (rootModulus root_close)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeEquation (stateQuotient)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal (realRemainder)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "R" => root hw0 hw1
local notation "Q" => stateQuotient hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def inputPreimage (U : (D).Cauchy) (n : Nat) : (D).Cauchy :=
  (rootRange hw0 hw1 n U).preimage ((rootRange hw0 hw1 n U).modulus (Q'.invSucc n))

theorem inputPreimage_close (U : (D).Cauchy) (n : Nat) :
    RCle (dist (T 1 (Class (inputPreimage hw0 hw1 U n))) (R n (Class U)))
      (rat (Q'.invSucc n)) :=
  (rootRange hw0 hw1 n U).bound (Q'.invSucc n) (Q'.invSucc_pos n) _ (Nat.le_refl _)

/-- No input or output range hypothesis: the actual quotient limit itself
constructs the required original input preimages and their modulus. -/
def inputRange (U V' : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e)) : RangeLimit hw0 hw1 (Class U) where
  preimage := inputPreimage hw0 hw1 U
  modulus := fun e => max (rootModulus hw0 hw1 V' modulus (quarter e)) (quarter e).den
  bound := by
    intro e he n hn
    let delta := quarter e
    have hd : (0 : Q') < delta := quarter_positive he
    have hdelta : Q'.invSucc n ≤ delta :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le delta hd)
    have hfirst : RCle
        (dist (T 1 (Class (inputPreimage hw0 hw1 U n))) (R n (Class U))) (rat delta) :=
      RCle_trans (inputPreimage_close hw0 hw1 U n)
        (leEv_le_ofQ'_of_approx_le (fun _ => hdelta))
    have hsecond := root_close hw0 hw1 U V' modulus bound delta hd n
      (Nat.le_trans (Nat.le_max_left _ _) hn)
    have h := RCle_trans (completedDist_triangle hw0 hw1 _ (R n (Class U)) (Class U))
      (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
    rwa [four_quarters] at h

/-- The actual represented derivative limit returns a represented graph,
with no additional coordinate-range premise or selected quotient preimages. -/
def representedGraphOfQuotientLimit (U V' : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e)) :
    Σ' G : GraphLimit hw0 hw1 (Class U) (Class V'),
      Σ' preimages : Nat → (D).Cauchy,
        ∀ n, Class (preimages n) = G.source n :=
  BF4WilsonAllNomeDerivativeOutputRange.representedGraphOfDerivative hw0 hw1 U
    (inputRange hw0 hw1 U V' modulus bound) modulus bound

/-- Differentiability does not silently delete the actual boundary kernel:
a differentiable vector lying in that kernel is necessarily zero. -/
theorem input_time_kernel_zero (U V' : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e))
    (hT : T 1 (Class U) = completedZero hw0 hw1 width) :
    Class U = completedZero hw0 hw1 width :=
  BF4WilsonAllNomeTimeRangeClosure.kernel_zero hw0 hw1
    (inputRange hw0 hw1 U V' modulus bound) hT

/-- The existing fixed-nome/width original form margin holds at every
represented actual derivative pair orthogonal to the SAME vacuum. -/
theorem quotient_form_gap (U V' : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e))
    (hU : B (unitState hw0 hw1 width) (Class U) = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width) (B (Class U) (Class U)))
      (B (Class U) (Class V')) :=
  BF4WilsonAllNomeDerivativeGraphGap.graph_form_gap hw0 hw1
    (representedGraphOfQuotientLimit hw0 hw1 U V' modulus bound).1 hU

/-- Every actual represented dyadic derivative yields all-small-real-time
Taylor differentiation, without either coordinate-range premise. -/
def quotientRealTaylorCertificate (U V' : (D).Cauchy) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (Q n (Class U)) (Class V')) (rat e))
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (B (realRemainder hw0 hw1 t (Class U) (Class V'))
          (realRemainder hw0 hw1 t (Class U) (Class V')))
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t)))
            (rat epsilon))) :=
  BF4WilsonAllNomeDerivativeOutputRange.derivativeRealTaylorCertificate hw0 hw1 U V'
    (inputRange hw0 hw1 U V' modulus bound) modulus bound epsilon he

#print axioms inputPreimage
#print axioms inputPreimage_close
#print axioms inputRange
#print axioms representedGraphOfQuotientLimit
#print axioms input_time_kernel_zero
#print axioms quotient_form_gap
#print axioms quotientRealTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeDerivativeInputRange
