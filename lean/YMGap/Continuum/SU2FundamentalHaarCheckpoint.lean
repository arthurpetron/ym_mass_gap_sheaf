/-
# Local Haar normalization for the signed fundamental tensor pilot

STATUS: candidate for local Lean verification; not imported by YMGap.lean.

This checks the degree-two and degree-four epsilon tensors against the
repository's actual rational quaternion-polynomial `productHaar`. Only
coordinates 0..3 occur, so its second S^3 factor is the unit. It does NOT
identify the 32-state cube matrix with the original transfer, prove a
volume/cutoff-uniform estimate, or change a frontier statement.

The matrix-coordinate convention below parametrizes SU(2) by a unit
quaternion. The checked statement is the explicit polynomial moment identity,
not an assumed integration rule. The existing group-invariance development
is separate from these finite evaluations.

The sixteen quartic rows are checked independently to keep each elaboration
bounded. No compiler-trusting decision tactic or new axiom is used.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

namespace YMGap.Continuum.SU2FundamentalHaarCheckpoint
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

abbrev ComplexPolynomial := RatPoly × RatPoly

def complexMul (p q : ComplexPolynomial) : ComplexPolynomial :=
  (polyAdd (polyMul p.1 q.1) (polyNeg (polyMul p.2 q.2)),
   polyAdd (polyMul p.1 q.2) (polyMul p.2 q.1))

def fundamental : Bool → Bool → ComplexPolynomial
  | false, false => (polyVar 0, polyVar 1)
  | false, true  => (polyVar 2, polyVar 3)
  | true, false  => (polyNeg (polyVar 2), polyVar 3)
  | true, true   => (polyVar 0, polyNeg (polyVar 1))

def epsilon : Bool → Bool → Q'
  | false, true => 1
  | true, false => -1
  | _, _ => 0

def secondEntry (a b i j : Bool) : Prop :=
  let p := complexMul (fundamental a i) (fundamental b j)
  Q'.eqv (productHaar p.1)
      ((Q'.mkPos 1 2 (by decide)) * (epsilon a b * epsilon i j)) ∧
    Q'.eqv (productHaar p.2) 0

theorem second_entries (a b i j : Bool) : secondEntry a b i j := by
  cases a <;> cases b <;> cases i <;> cases j <;>
    unfold secondEntry complexMul fundamental epsilon <;>
    decide +kernel

def fourthMoment (a b c d i j k l : Bool) : ComplexPolynomial :=
  complexMul (complexMul (fundamental a i) (fundamental b j))
    (complexMul (fundamental c k) (fundamental d l))

def fourthValue (a b c d i j k l : Bool) : Q' :=
  (Q'.mkPos 1 6 (by decide)) *
    ((epsilon a b * epsilon c d) * (epsilon i j * epsilon k l) +
     (epsilon a c * epsilon b d) * (epsilon i k * epsilon j l) +
     (epsilon a d * epsilon b c) * (epsilon i l * epsilon j k))

def fourthEntry (a b c d i j k l : Bool) : Prop :=
  Q'.eqv (productHaar (fourthMoment a b c d i j k l).1)
      (fourthValue a b c d i j k l) ∧
    Q'.eqv (productHaar (fourthMoment a b c d i j k l).2) 0

theorem fourth_row_0000 (i j k l : Bool) :
    fourthEntry false false false false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0001 (i j k l : Bool) :
    fourthEntry false false false true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0010 (i j k l : Bool) :
    fourthEntry false false true false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0011 (i j k l : Bool) :
    fourthEntry false false true true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0100 (i j k l : Bool) :
    fourthEntry false true false false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0101 (i j k l : Bool) :
    fourthEntry false true false true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0110 (i j k l : Bool) :
    fourthEntry false true true false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_0111 (i j k l : Bool) :
    fourthEntry false true true true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1000 (i j k l : Bool) :
    fourthEntry true false false false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1001 (i j k l : Bool) :
    fourthEntry true false false true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1010 (i j k l : Bool) :
    fourthEntry true false true false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1011 (i j k l : Bool) :
    fourthEntry true false true true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1100 (i j k l : Bool) :
    fourthEntry true true false false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1101 (i j k l : Bool) :
    fourthEntry true true false true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1110 (i j k l : Bool) :
    fourthEntry true true true false i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

theorem fourth_row_1111 (i j k l : Bool) :
    fourthEntry true true true true i j k l := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    unfold fourthEntry fourthMoment fourthValue complexMul fundamental epsilon <;>
    decide +kernel

end YMGap.Continuum.SU2FundamentalHaarCheckpoint

#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.second_entries
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0000
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0001
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0010
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0011
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0100
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0101
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0110
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_0111
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1000
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1001
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1010
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1011
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1100
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1101
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1110
#print axioms YMGap.Continuum.SU2FundamentalHaarCheckpoint.fourth_row_1111
