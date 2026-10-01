/-
# Rational parameter congruence for the original physical Cayley map

Equivalent rationals give equal actual plus/minus shifts and equal Cayley
operators. The constructed plus preimage supplies the proof; no representative
of a completed class is selected. This is required to compare rational dyadic
steps that are equivalent but not identical as Q' records. It identifies no
physical time, logarithm or continuum generator.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedSmul_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative (Domain)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain plus_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale negativeImagScale plus_input_imag minus_input_imag cayley_graph)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows (iterate)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1

private theorem real_scale_congr {s t : Q'} (hst : Q'.eqv s t) (x : RH) :
    Scale s x = Scale t x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_smul,bondValue_smul]
  exact completedSmul_congr hw0 hw1 hst _

theorem imag_parameter_congr {s t : Q'} (hst : Q'.eqv s t) (x : H) :
    imagScale hw0 hw1 s x = imagScale hw0 hw1 t x :=
  Prod.ext (congrArg Neg (real_scale_congr hw0 hw1 hst x.2))
    (real_scale_congr hw0 hw1 hst x.1)

private theorem negativeImag_parameter_congr {s t : Q'} (hst : Q'.eqv s t) (x : H) :
    negativeImagScale hw0 hw1 s x = negativeImagScale hw0 hw1 t x :=
  Prod.ext (real_scale_congr hw0 hw1 hst x.2)
    (congrArg Neg (real_scale_congr hw0 hw1 hst x.1))

theorem plus_parameter_congr {s t : Q'} (hst : Q'.eqv s t) (d : D) :
    plus hw0 hw1 s d = plus hw0 hw1 t d := by
  rw [plus_input_imag,plus_input_imag,imag_parameter_congr hw0 hw1 hst]

theorem minus_parameter_congr {s t : Q'} (hst : Q'.eqv s t) (d : D) :
    minus hw0 hw1 s d = minus hw0 hw1 t d := by
  rw [minus_input_imag,minus_input_imag,negativeImag_parameter_congr hw0 hw1 hst]

/-- Rational normalization changes no actual original Cayley operator. -/
theorem cayley_parameter_congr {s t : Q'} (hs : (0 : Q') < s) (ht : (0 : Q') < t)
    (hst : Q'.eqv s t) (x : H) : C s hs x = C t ht x := by
  let d := plusDomain hw0 hw1 s hs x
  have hp : plus hw0 hw1 t d = x :=
    (plus_parameter_congr hw0 hw1 hst d).symm.trans (plus_right hw0 hw1 s hs x)
  calc
    C s hs x = minus hw0 hw1 s d := rfl
    _ = minus hw0 hw1 t d := minus_parameter_congr hw0 hw1 hst d
    _ = C t ht (plus hw0 hw1 t d) := (cayley_graph hw0 hw1 t ht d).symm
    _ = C t ht x := congrArg (C t ht) hp

theorem iterate_parameter_congr {s t : Q'} (hs : (0 : Q') < s) (ht : (0 : Q') < t)
    (hst : Q'.eqv s t) (x : H) (n : Nat) :
    iterate hw0 hw1 s hs x n = iterate hw0 hw1 t ht x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change C s hs (iterate hw0 hw1 s hs x n) = C t ht (iterate hw0 hw1 t ht x n)
      rw [ih,cayley_parameter_congr hw0 hw1 hs ht hst]

#print axioms imag_parameter_congr
#print axioms plus_parameter_congr
#print axioms minus_parameter_congr
#print axioms cayley_parameter_congr
#print axioms iterate_parameter_congr

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyParameter
