/-
# Complex linearity of the constructed positive-real Cayley action

The positive-real action preserves the FULL Hermitian pairing, and its
conjugate inverse supplies an actual preimage for every physical test. Testing
against those preimages and using the original pairing laws proves additivity
and complex-scalar compatibility on the SAME completed Wilson bond. Both
constructive scalar Cauchy witnesses remain explicit.

This is fixed nome and width. It does not construct signed time, calibrate a
physical clock or generator, or prove continuum Yang--Mills.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
  (PositiveTimeValue)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
  (inner_add_left inner_smul_left)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCayley
  (eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins
  (positiveRealAction)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing
  (positiveRealAction_pairing_preserved)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse
  (inverseRealAction positiveRealAction_inverse_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexification
  (valueAdd valueMul valueConj scalarValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "I" => inner hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "S" => BF4WilsonAllNomeComplexBondOSTime.smul hw0 hw1
local notation "U" => positiveRealAction hw0 hw1

/-- Positive-real Cayley time preserves the ORIGINAL physical addition. The
test preimage is explicitly `inverseRealAction time z`, not a selected range
representative. -/
theorem positiveRealAction_add (time : PositiveTimeValue) (x y : H) :
    U time (A x y) = A (U time x) (U time y) := by
  apply eq_of_pairings hw0 hw1
  intro z
  let v := inverseRealAction hw0 hw1 time z
  have hv : U time v = z := positiveRealAction_inverse_right hw0 hw1 time z
  calc
    I (U time (A x y)) z = I (U time (A x y)) (U time v) := by rw [hv]
    _ = I (A x y) v := positiveRealAction_pairing_preserved hw0 hw1 time _ _
    _ = valueAdd (I x v) (I y v) := inner_add_left hw0 hw1 x y v
    _ = valueAdd (I (U time x) (U time v)) (I (U time y) (U time v)) := by
      rw [positiveRealAction_pairing_preserved hw0 hw1 time x v,
        positiveRealAction_pairing_preserved hw0 hw1 time y v]
    _ = I (A (U time x) (U time y)) z := by
      rw [← hv]
      exact (inner_add_left hw0 hw1 (U time x) (U time y) (U time v)).symm

/-- Complex scalar compatibility with BOTH original Cauchy witnesses, not a
pointwise rational scalar substitute. -/
theorem positiveRealAction_smul (time : PositiveTimeValue)
    (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : H) :
    U time (S s t cs ct x) = S s t cs ct (U time x) := by
  apply eq_of_pairings hw0 hw1
  intro z
  let v := inverseRealAction hw0 hw1 time z
  have hv : U time v = z := positiveRealAction_inverse_right hw0 hw1 time z
  calc
    I (U time (S s t cs ct x)) z =
        I (U time (S s t cs ct x)) (U time v) := by rw [hv]
    _ = I (S s t cs ct x) v := positiveRealAction_pairing_preserved hw0 hw1 time _ _
    _ = valueMul (valueConj (scalarValue s t)) (I x v) :=
      inner_smul_left hw0 hw1 s t cs ct x v
    _ = valueMul (valueConj (scalarValue s t))
          (I (U time x) (U time v)) := by
          rw [positiveRealAction_pairing_preserved hw0 hw1 time x v]
    _ = I (S s t cs ct (U time x)) z := by
      rw [← hv]
      exact (inner_smul_left hw0 hw1 s t cs ct (U time x) (U time v)).symm

#print axioms positiveRealAction_add
#print axioms positiveRealAction_smul

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeLinear
