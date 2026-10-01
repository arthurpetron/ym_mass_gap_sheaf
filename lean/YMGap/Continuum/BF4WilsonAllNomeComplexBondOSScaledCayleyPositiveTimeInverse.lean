/-
# Inverse of the constructed positive-real Cayley action

Conjugating the actual positive-time limit gives an inverse on the SAME
original complex Wilson bond. At each supplied rational time sample, the
finite-parameter limit has its already constructed conjugate inverse. Its
exact isometry transports the ORIGINAL time-limit rate to the inverse
candidate, so uniqueness of represented physical limits proves surjectivity.

This constructs no negative-time parameter or signed-real group. Nome and
width are fixed; physical spacing, generator calibration, continuum survival,
and the Yang--Mills mass gap remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime sample)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (PositiveTimeValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation
  (conjugate conjugateRows conjugateRows_pin conjugate_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime
  (sample_positive timeRows timeRows_pin timeSequence timeLimitRows timeLimitRate
    timeLimit_bound positiveAction positiveAction_ofRows)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction positiveRealAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
  (positiveAction_injective positiveRealAction_injective)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap
  (limitMap rows_limit_unique)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing
  (limitMap_distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse
  (limitMap_inverse_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGeometricRowsLimit
  (distance_symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "F" => limitMap hw0 hw1
local notation "K" => conjugate hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The inverse candidate uses the original positive-time action once, with
the already constructed physical conjugation. -/
def inverseAction (time : PositiveTime) (x : H) : H :=
  K (positiveAction hw0 hw1 time (K x))

/-- Supplied original input Rows produce original inverse-output Rows. -/
def inverseTimeRows (time : PositiveTime) (X : R) : R :=
  conjugateRows hw0 hw1
    (timeLimitRows hw0 hw1 time (conjugateRows hw0 hw1 X))

theorem inverseTimeRows_pin (time : PositiveTime) (X : R) :
    ofRows hw0 hw1 (inverseTimeRows hw0 hw1 time X) =
      inverseAction hw0 hw1 time (ofRows hw0 hw1 X) := by
  unfold inverseTimeRows inverseAction
  rw [conjugateRows_pin,
    ← positiveAction_ofRows hw0 hw1 time (conjugateRows hw0 hw1 X),
    conjugateRows_pin]

/-- The existing rate of the conjugate input is the inverse comparison rate.
No limit modulus is extracted from a proposition. -/
def inverseTimeRate (time : PositiveTime) (X : R) (e : Q') : Nat :=
  timeLimitRate hw0 hw1 time (conjugateRows hw0 hw1 X) e

/-- At EACH sample the inverse-candidate defect is exactly the original
forward time-limit defect on conjugated input Rows. -/
theorem inverseTimeRows_sample_distance (time : PositiveTime) (X : R) (n : Nat) :
    D (ofRows hw0 hw1 (timeRows hw0 hw1 time (inverseTimeRows hw0 hw1 time X) n))
        (ofRows hw0 hw1 X) =
      D (ofRows hw0 hw1 (timeRows hw0 hw1 time (conjugateRows hw0 hw1 X) n))
        (ofRows hw0 hw1 (timeLimitRows hw0 hw1 time (conjugateRows hw0 hw1 X))) := by
  let q := sample time n
  have hq : (0 : Q') < q := sample_positive time n
  let L := ofRows hw0 hw1
    (timeLimitRows hw0 hw1 time (conjugateRows hw0 hw1 X))
  have hright : F q hq (K (F q hq (K (ofRows hw0 hw1 X)))) = ofRows hw0 hw1 X := by
    exact limitMap_inverse_right hw0 hw1 q hq (ofRows hw0 hw1 X)
  calc
    D (ofRows hw0 hw1
        (timeRows hw0 hw1 time (inverseTimeRows hw0 hw1 time X) n))
        (ofRows hw0 hw1 X) =
      D (F q hq (K L)) (F q hq (K (F q hq (K (ofRows hw0 hw1 X))))) := by
        have hleft := timeRows_pin hw0 hw1 time (inverseTimeRows hw0 hw1 time X) n
        rw [hleft]
        change D (F q hq (ofRows hw0 hw1
          (conjugateRows hw0 hw1
            (timeLimitRows hw0 hw1 time (conjugateRows hw0 hw1 X)))))
          (ofRows hw0 hw1 X) = _
        rw [conjugateRows_pin]
        exact congrArg (fun z => D (F q hq (K L)) z) hright.symm
    _ = D (K L) (K (F q hq (K (ofRows hw0 hw1 X)))) :=
      limitMap_distance hw0 hw1 q hq _ _
    _ = D L (F q hq (K (ofRows hw0 hw1 X))) :=
      conjugate_distance hw0 hw1 _ _
    _ = D (F q hq (K (ofRows hw0 hw1 X))) L :=
      distance_symm hw0 hw1 _ _
    _ = D (ofRows hw0 hw1 (timeRows hw0 hw1 time (conjugateRows hw0 hw1 X) n))
          (ofRows hw0 hw1
            (timeLimitRows hw0 hw1 time (conjugateRows hw0 hw1 X))) := by
          rw [timeRows_pin, conjugateRows_pin]

/-- A computed all-tail inverse defect bound on the original physical bond. -/
theorem inverseTimeRows_sample_bound (time : PositiveTime) (X : R)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : inverseTimeRate hw0 hw1 time X e ≤ n) :
    RCle (D (ofRows hw0 hw1
      (timeRows hw0 hw1 time (inverseTimeRows hw0 hw1 time X) n))
      (ofRows hw0 hw1 X)) (rat e) := by
  rw [inverseTimeRows_sample_distance]
  exact timeLimit_bound hw0 hw1 time (conjugateRows hw0 hw1 X) e he n hn

/-- Every original class has a computed positive-time preimage. -/
theorem positiveAction_inverse_right (time : PositiveTime) (x : H) :
    positiveAction hw0 hw1 time (inverseAction hw0 hw1 time x) = x := by
  rcases x with ⟨u,v⟩
  refine Quotient.inductionOn₂ u v ?_
  intro X Y
  let Z : R := (X,Y)
  change positiveAction hw0 hw1 time (inverseAction hw0 hw1 time (ofRows hw0 hw1 Z)) =
    ofRows hw0 hw1 Z
  rw [← inverseTimeRows_pin hw0 hw1 time Z, positiveAction_ofRows]
  apply rows_limit_unique hw0 hw1 (timeSequence hw0 hw1 time (inverseTimeRows hw0 hw1 time Z))
    Z (inverseTimeRate hw0 hw1 time Z)
  intro e he n hn
  exact inverseTimeRows_sample_bound hw0 hw1 time Z e he n hn

/-- Pairing-derived injectivity converts the computed right inverse into a
two-sided inverse, without a density or surjectivity hypothesis. -/
theorem positiveAction_inverse_left (time : PositiveTime) (x : H) :
    inverseAction hw0 hw1 time (positiveAction hw0 hw1 time x) = x := by
  apply positiveAction_injective hw0 hw1 time
  exact positiveAction_inverse_right hw0 hw1 time (positiveAction hw0 hw1 time x)

/-- The same explicit conjugate formula is presentation-independent because
`positiveRealAction` already descended to numerical positive-real time. -/
def inverseRealAction (time : PositiveTimeValue) (x : H) : H :=
  K (positiveRealAction hw0 hw1 time (K x))

theorem positiveRealAction_inverse_right (time : PositiveTimeValue) (x : H) :
    positiveRealAction hw0 hw1 time (inverseRealAction hw0 hw1 time x) = x := by
  refine Quotient.inductionOn time ?_
  intro t
  change positiveAction hw0 hw1 t (inverseAction hw0 hw1 t x) = x
  exact positiveAction_inverse_right hw0 hw1 t x

theorem positiveRealAction_inverse_left (time : PositiveTimeValue) (x : H) :
    inverseRealAction hw0 hw1 time (positiveRealAction hw0 hw1 time x) = x := by
  apply positiveRealAction_injective hw0 hw1 time
  exact positiveRealAction_inverse_right hw0 hw1 time (positiveRealAction hw0 hw1 time x)

/-- Type-level preimage for the SAME original completed bond and numerical
positive-real time. -/
def positiveRealPreimage (time : PositiveTimeValue) (x : H) :
    Σ' y : H, positiveRealAction hw0 hw1 time y = x :=
  ⟨inverseRealAction hw0 hw1 time x,
    positiveRealAction_inverse_right hw0 hw1 time x⟩

#print axioms inverseAction
#print axioms inverseTimeRows
#print axioms inverseTimeRows_pin
#print axioms inverseTimeRate
#print axioms inverseTimeRows_sample_distance
#print axioms inverseTimeRows_sample_bound
#print axioms positiveAction_inverse_right
#print axioms positiveAction_inverse_left
#print axioms inverseRealAction
#print axioms positiveRealAction_inverse_right
#print axioms positiveRealAction_inverse_left
#print axioms positiveRealPreimage

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
