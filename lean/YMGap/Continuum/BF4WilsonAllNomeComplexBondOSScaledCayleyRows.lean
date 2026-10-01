/-
# Original represented rows for scaled physical Cayley products

The actual quotient Cayley action is lifted to the already witnessed real
time-sector states before either quotient is formed. All range witnesses
and moduli are constructed, not selected from completed classes. Iterating
this factory returns original physical Rows at every finite product index.
This supplies representation data for a later product Cauchy limit; it does
not prove convergence or identify the parameter with physical time.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
import YMGap.Continuum.BF4WilsonAllNomeScaledResolventNeumannLimit

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (fromSectorRep toSectorRep fromSectorRep_limit)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (ofState ofState_congr bondValue_ofState bondValue_add bondValue_sub bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit (scaleState subState)
open YMGap.Continuum.BF4WilsonAllNomeScaledResolventNeumannLimit
  (scaledResolventState scaledResolventState_pin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (t : Q') (ht : (0 : Q') < t)

local notation "S" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "CS" => BF4WilsonAllNomeComplexTimeSector.State hw0 hw1 (width := width)
local notation "H" => BF4WilsonAllNomeComplexBondOSCompletion.ComplexBondCompletion
  hw0 hw1 (width := width)
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Sub" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "R" => BF4WilsonAllNomeBondOSScaledResolvent.resolvent hw0 hw1 t ht
local notation "J" => BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.complement hw0 hw1 t ht
local notation "Inv" => BF4WilsonAllNomeBondOSScaledDenominator.inverse hw0 hw1 t ht
local notation "F" => ofState hw0 hw1
local notation "CF" => BF4WilsonAllNomeComplexBondOSCompletion.ofState hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 t ht

attribute [local irreducible] fromSectorRep toSectorRep
  BF4WilsonAllNomeScaledResolventNeumannLimit.normalized

private theorem addState_pin (x y : S) :
    F (BF4WilsonAllNomeTimeSector.add hw0 hw1 x y) = Add (F x) (F y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_ofState,bondValue_add,bondValue_ofState,bondValue_ofState]
  rfl

private theorem subState_pin (x y : S) :
    F (subState hw0 hw1 x y) = Sub (F x) (F y) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_ofState,bondValue_sub,bondValue_ofState,bondValue_ofState]
  rfl

private theorem scaleState_pin (a : Q') (x : S) :
    F (scaleState hw0 hw1 a x) = Scale a (F x) := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_ofState,bondValue_smul,bondValue_ofState]
  rfl

/-- The existing represented Neumann limit pins to the existing quotient map,
even though the latter constructs its own row-derived range witness. -/
theorem normalizedState_pin (x : S) :
    F (BF4WilsonAllNomeScaledResolventNeumannLimit.normalized hw0 hw1 t ht x) =
      BF4WilsonAllNomeBondOSScaledDenominator.normalized hw0 hw1 t ht (F x) := by
  change F (BF4WilsonAllNomeScaledResolventNeumannLimit.normalized hw0 hw1 t ht x) =
    F (BF4WilsonAllNomeScaledResolventNeumannLimit.normalized hw0 hw1 t ht
      (toSectorRep hw0 hw1 (fromSectorRep hw0 hw1 x)))
  apply ofState_congr hw0 hw1
  exact BF4WilsonAllNomeScaledResolventNeumannLimit.normalized_congr hw0 hw1 t ht
    (fromSectorRep_limit hw0 hw1 x).symm

/-- The actual denominator inverse retains the input state's original range data. -/
def inverseState (x : S) : S := scaleState hw0 hw1 2
  (BF4WilsonAllNomeScaledResolventNeumannLimit.normalized hw0 hw1 t ht x)

theorem inverseState_pin (x : S) :
    F (inverseState hw0 hw1 t ht x) = Inv (F x) := by
  unfold inverseState BF4WilsonAllNomeBondOSScaledDenominator.inverse
  rw [scaleState_pin,normalizedState_pin]

def complementState (x : S) : S :=
  subState hw0 hw1 x (scaledResolventState hw0 hw1 t ht x)

theorem complementState_pin (x : S) :
    F (complementState hw0 hw1 t ht x) = J (F x) := by
  unfold complementState BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.complement
  rw [subState_pin,scaledResolventState_pin]

private def firstNumerator (x : CS) : S :=
  BF4WilsonAllNomeTimeSector.add hw0 hw1
    (scaledResolventState hw0 hw1 t ht (inverseState hw0 hw1 t ht x.1))
    (complementState hw0 hw1 t ht (inverseState hw0 hw1 t ht x.2))

private def secondNumerator (x : CS) : S :=
  subState hw0 hw1
    (scaledResolventState hw0 hw1 t ht (inverseState hw0 hw1 t ht x.2))
    (complementState hw0 hw1 t ht (inverseState hw0 hw1 t ht x.1))

private theorem firstNumerator_pin (x : CS) :
    F (firstNumerator hw0 hw1 t ht x) = Add (R (Inv (F x.1))) (J (Inv (F x.2))) := by
  unfold firstNumerator
  rw [addState_pin,scaledResolventState_pin,complementState_pin,
    inverseState_pin,inverseState_pin]

private theorem secondNumerator_pin (x : CS) :
    F (secondNumerator hw0 hw1 t ht x) = Sub (R (Inv (F x.2))) (J (Inv (F x.1))) := by
  unfold secondNumerator
  rw [subState_pin,scaledResolventState_pin,complementState_pin,
    inverseState_pin,inverseState_pin]

/-- Componentwise witnessed original states for the actual minus shift of
the constructed plus preimage. No domain representative is selected. -/
def cayleyState (x : CS) : CS :=
  (BF4WilsonAllNomeTimeSector.add hw0 hw1
    (scaledResolventState hw0 hw1 t ht (firstNumerator hw0 hw1 t ht x))
    (complementState hw0 hw1 t ht (secondNumerator hw0 hw1 t ht x)),
   subState hw0 hw1
    (scaledResolventState hw0 hw1 t ht (secondNumerator hw0 hw1 t ht x))
    (complementState hw0 hw1 t ht (firstNumerator hw0 hw1 t ht x)))

theorem cayleyState_pin (x : CS) : CF (cayleyState hw0 hw1 t ht x) = C (CF x) := by
  apply Prod.ext
  · change F (cayleyState hw0 hw1 t ht x).1 = _
    unfold cayleyState
    rw [addState_pin,scaledResolventState_pin,complementState_pin,
      firstNumerator_pin,secondNumerator_pin]
    change _ = Add
      (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
        (BF4WilsonAllNomeBondOSScaledResolvent.resolventDomain hw0 hw1 t ht
          (Add (R (Inv (F x.1))) (J (Inv (F x.2))))))
      (Scale t (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
        (BF4WilsonAllNomeBondOSScaledResolvent.resolventDomain hw0 hw1 t ht
          (Sub (R (Inv (F x.2))) (J (Inv (F x.1)))))))
    rw [BF4WilsonAllNomeBondOSScaledResolvent.input_resolventDomain]
    have ho := BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.output_resolventDomain
      hw0 hw1 t ht (Sub (R (Inv (F x.2))) (J (Inv (F x.1))))
    dsimp only at ho
    rw [ho]
  · change F (cayleyState hw0 hw1 t ht x).2 = _
    unfold cayleyState
    rw [subState_pin,scaledResolventState_pin,complementState_pin,
      firstNumerator_pin,secondNumerator_pin]
    change _ = Sub
      (BF4WilsonAllNomeBondOSDerivative.input hw0 hw1
        (BF4WilsonAllNomeBondOSScaledResolvent.resolventDomain hw0 hw1 t ht
          (Sub (R (Inv (F x.2))) (J (Inv (F x.1))))))
      (Scale t (BF4WilsonAllNomeBondOSDerivative.output hw0 hw1
        (BF4WilsonAllNomeBondOSScaledResolvent.resolventDomain hw0 hw1 t ht
          (Add (R (Inv (F x.1))) (J (Inv (F x.2)))))))
    rw [BF4WilsonAllNomeBondOSScaledResolvent.input_resolventDomain]
    have ho := BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.output_resolventDomain
      hw0 hw1 t ht (Add (R (Inv (F x.1))) (J (Inv (F x.2))))
    dsimp only at ho
    rw [ho]

/-- Every finite Cayley product is represented before quotienting. -/
def iterateState (x : CS) : Nat → CS
  | 0 => x
  | n+1 => cayleyState hw0 hw1 t ht (iterateState x n)

def iterate (x : H) : Nat → H
  | 0 => x
  | n+1 => C (iterate x n)

theorem iterateState_pin (x : CS) (n : Nat) :
    CF (iterateState hw0 hw1 t ht x n) = iterate hw0 hw1 t ht (CF x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateState,cayleyState_pin,ih]
      rfl

def iterateRows (x : CS) (n : Nat) :
    BF4WilsonAllNomeComplexBondOSCompletion.Rows hw0 hw1 (width := width) :=
  BF4WilsonAllNomeComplexBondOSCompletion.rowsOfState hw0 hw1
    (iterateState hw0 hw1 t ht x n)

theorem iterateRows_pin (x : CS) (n : Nat) :
    BF4WilsonAllNomeComplexBondOSCompletion.ofRows hw0 hw1
      (iterateRows hw0 hw1 t ht x n) = iterate hw0 hw1 t ht (CF x) n := by
  rw [iterateRows,BF4WilsonAllNomeComplexBondOSCompletion.ofRows_rowsOfState,
    iterateState_pin]

#print axioms normalizedState_pin
#print axioms inverseState
#print axioms inverseState_pin
#print axioms complementState
#print axioms complementState_pin
#print axioms cayleyState
#print axioms cayleyState_pin
#print axioms iterateState
#print axioms iterate
#print axioms iterateState_pin
#print axioms iterateRows
#print axioms iterateRows_pin

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
