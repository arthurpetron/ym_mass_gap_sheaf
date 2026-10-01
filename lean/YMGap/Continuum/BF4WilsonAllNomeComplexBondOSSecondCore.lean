/-
# A represented second graph step on the original complex physical carrier

The input is an explicit pair of original Cauchy representatives. Applying
the original time map and extracting the derivative's *supplied* range
witness constructs two consecutive physical graph points. This proves a
second-domain witness only for these twice-time-smoothed inputs, not closure
of the entire physical derivative domain under its output.

The squared-norm bound is the elementary regularity input for a future
scaled-Cayley local-error estimate. No scaled Cayley limit or physical-time
unitary group is asserted here.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeDerivativeCore

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime timeNonexpansive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeCore (derivativeAction_commutes_time)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Point" => BF4WilsonAllNomeComplexBondOSDerivative.Point hw0 hw1 (width := width)
local notation "Domain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "H" => BF4WilsonAllNomeComplexBondOSCompletion.ComplexBondCompletion hw0 hw1 (width := width)
local notation "Value" => BF4WilsonAllNomeComplexBondOSCompletion.value hw0 hw1
local notation "Input" => BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
local notation "Output" => BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
local notation "Inner" => BF4WilsonAllNomeComplexBondOSCompletion.inner hw0 hw1

/-- The original represented input after one actual time step. -/
def timeSeed (Y : (D).Cauchy) : (D).Cauchy :=
  (timeNonexpansive hw0 hw1 1).mapCauchy Y

theorem timeSeed_pin (Y : (D).Cauchy) :
    Class (timeSeed hw0 hw1 Y) = T 1 (Class Y) := rfl

/-- A computed representative of `A y`, extracted from the range witness
already carried by the original graph point for `y`. -/
def derivativeSeed (Y : (D).Cauchy) : (D).Cauchy :=
  BF4WilsonAllNomeTimeRangeClosed.representative hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 Y).output.range

theorem derivativeSeed_pin (Y : (D).Cauchy) :
    Class (derivativeSeed hw0 hw1 Y) = A (Class Y) :=
  BF4WilsonAllNomeTimeRangeClosed.representative_pin hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 Y).output.range

/-- The first physical graph point is based on the represented source `T y`.
Its input is `T² y` and its output is `T A y`. -/
def firstPoint (Y : (D).Cauchy × (D).Cauchy) : Point :=
  (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 (timeSeed hw0 hw1 Y.1),
   BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 (timeSeed hw0 hw1 Y.2))

/-- The second physical graph point is based on the constructive source
representing `A y`. Its input is `T A y` and its output is `A² y`. -/
def secondPoint (Y : (D).Cauchy × (D).Cauchy) : Point :=
  (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 (derivativeSeed hw0 hw1 Y.1),
   BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 (derivativeSeed hw0 hw1 Y.2))

def first (Y : (D).Cauchy × (D).Cauchy) : Domain :=
  BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 (firstPoint hw0 hw1 Y)

def second (Y : (D).Cauchy × (D).Cauchy) : Domain :=
  BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 (secondPoint hw0 hw1 Y)

theorem first_input_value (Y : (D).Cauchy × (D).Cauchy) :
    Value (Input (first hw0 hw1 Y)) =
      (T 1 (T 1 (Class Y.1)), T 1 (T 1 (Class Y.2))) := by
  unfold first
  rw [BF4WilsonAllNomeComplexBondOSDerivative.value_input_ofPoint hw0 hw1
    (firstPoint hw0 hw1 Y)]
  change (T 1 (Class (timeSeed hw0 hw1 Y.1)),
    T 1 (Class (timeSeed hw0 hw1 Y.2))) = _
  simp only [timeSeed_pin]

theorem first_output_value (Y : (D).Cauchy × (D).Cauchy) :
    Value (Output (first hw0 hw1 Y)) =
      (T 1 (A (Class Y.1)), T 1 (A (Class Y.2))) := by
  unfold first
  rw [BF4WilsonAllNomeComplexBondOSDerivative.value_output_ofPoint hw0 hw1
    (firstPoint hw0 hw1 Y)]
  change (A (Class (timeSeed hw0 hw1 Y.1)),
    A (Class (timeSeed hw0 hw1 Y.2))) = _
  simp only [timeSeed_pin, derivativeAction_commutes_time]

theorem second_input_value (Y : (D).Cauchy × (D).Cauchy) :
    Value (Input (second hw0 hw1 Y)) =
      (T 1 (A (Class Y.1)), T 1 (A (Class Y.2))) := by
  unfold second
  rw [BF4WilsonAllNomeComplexBondOSDerivative.value_input_ofPoint hw0 hw1
    (secondPoint hw0 hw1 Y)]
  change (T 1 (Class (derivativeSeed hw0 hw1 Y.1)),
    T 1 (Class (derivativeSeed hw0 hw1 Y.2))) = _
  simp only [derivativeSeed_pin]

theorem second_output_value (Y : (D).Cauchy × (D).Cauchy) :
    Value (Output (second hw0 hw1 Y)) =
      (A (A (Class Y.1)), A (A (Class Y.2))) := by
  unfold second
  rw [BF4WilsonAllNomeComplexBondOSDerivative.value_output_ofPoint hw0 hw1
    (secondPoint hw0 hw1 Y)]
  change (A (Class (derivativeSeed hw0 hw1 Y.1)),
    A (Class (derivativeSeed hw0 hw1 Y.2))) = _
  simp only [derivativeSeed_pin]

/-- The first physical derivative output is the second physical derivative
input, with equality on the SAME completed bond carrier. -/
theorem first_output_eq_second_input (Y : (D).Cauchy × (D).Cauchy) :
    Output (first hw0 hw1 Y) = Input (second hw0 hw1 Y) := by
  apply BF4WilsonAllNomeComplexBondOSCompletion.value_injective hw0 hw1
  rw [first_output_value, second_input_value]

/-- Two applications of the original represented derivative contraction.
This controls the actual squared norm of the second physical graph output;
it is not a bound on an abstract everywhere-defined physical `A²`. -/
theorem second_output_norm_le (Y : (D).Cauchy × (D).Cauchy) :
    RCle ((Inner (Output (second hw0 hw1 Y))
      (Output (second hw0 hw1 Y))).1)
      (RCadd (B (Class Y.1) (Class Y.1)) (B (Class Y.2) (Class Y.2))) := by
  have h₁ : RCle (B (A (A (Class Y.1))) (A (A (Class Y.1))))
      (B (Class Y.1) (Class Y.1)) :=
    RCle_trans (derivativeAction_norm_bound hw0 hw1 (A (Class Y.1)))
      (derivativeAction_norm_bound hw0 hw1 (Class Y.1))
  have h₂ : RCle (B (A (A (Class Y.2))) (A (A (Class Y.2))))
      (B (Class Y.2) (Class Y.2)) :=
    RCle_trans (derivativeAction_norm_bound hw0 hw1 (A (Class Y.2)))
      (derivativeAction_norm_bound hw0 hw1 (Class Y.2))
  rw [BF4WilsonAllNomeComplexBondOSCompletion.inner_value,
    BF4WilsonAllNomeComplexification.inner,second_output_value]
  exact RCadd_le_add h₁ h₂

#print axioms timeSeed
#print axioms timeSeed_pin
#print axioms derivativeSeed
#print axioms derivativeSeed_pin
#print axioms firstPoint
#print axioms secondPoint
#print axioms first
#print axioms second
#print axioms first_input_value
#print axioms first_output_value
#print axioms second_input_value
#print axioms second_output_value
#print axioms first_output_eq_second_input
#print axioms second_output_norm_le

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore
