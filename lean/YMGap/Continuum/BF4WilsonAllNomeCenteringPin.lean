/-
# Exact identification of the two all-nome Wilson centerings

The explicit rational-centered stream and the completed unit projection are
identified by their pairings with every vector in the SAME completion.  The
proof compares their actual limits; it does not infer vector equality from an
equality of norms.
-/

import YMGap.Continuum.BF4WilsonAllNomeUnitProjection
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector

namespace YMGap.Continuum.BF4WilsonAllNomeCenteringPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra (centerApprox)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centerApprox_pairing_left)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "F" => intrinsicForm hw0 hw1
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "u" => unit width
local notation "R" => CRealSeminormPairingCompletion.representativeInner PD

private theorem centered_representative_pairing
    (x : IntrinsicExpression width) (Y : (D).Cauchy) :
    Equiv (R (centeredStream hw0 hw1 x) Y)
      (sub (R ((D).constant x) Y)
        (mul (F x u) (R ((D).constant u) Y))) := by
  have hx := CRealSeminormPairingCompletion.pairSequence_converges
    PD ((D).constant x) Y
  have hu := CRealSeminormPairingCompletion.pairSequence_converges
    PD ((D).constant u) Y
  have hproduct :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self (F x u)) hu
  have htarget := TrigAddCReal.convergesTo_add hx
    (TrigAddCReal.convergesTo_neg hproduct)
  exact Equiv_of_limit_of_equal
    (fun n => centerApprox_pairing_left hw0 hw1 x (Y.seq n) ((F x u).approx n))
    (CRealSeminormPairingCompletion.pairSequence_converges
      PD (centeredStream hw0 hw1 x) Y)
    htarget

/-- The explicit centered vector has the connected pairing against every
completed test vector. -/
theorem centeredVector_pairing (x : IntrinsicExpression width) (y : Completion hw0 hw1 width) :
    B (centeredVector hw0 hw1 x) y =
      RCsub (B (embed hw0 hw1 x) y)
        (RCmul (B (embed hw0 hw1 x) U) (B U y)) := by
  rw [show B (embed hw0 hw1 x) U = Quotient.mk crealSetoid (F x u) from
    completedInner_embed hw0 hw1 x u]
  refine Quotient.inductionOn y ?_
  intro Y
  exact Quotient.sound (centered_representative_pairing hw0 hw1 x Y)

/-- On a dense Wilson expression, completed unit-projection centering is
exactly the previously constructed rational-centered stream. -/
theorem centeredPart_embed (x : IntrinsicExpression width) :
    centeredPart hw0 hw1 (embed hw0 hw1 x) = centeredVector hw0 hw1 x := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [centeredPart_pairing, centeredVector_pairing]

/-- The corresponding inhabitants of the existing vacuum-complement subtype
are equal as well. -/
theorem centeredState_embed (x : IntrinsicExpression width) :
    centeredState hw0 hw1 (embed hw0 hw1 x) = centeredExcitation hw0 hw1 x := by
  apply Subtype.ext
  exact centeredPart_embed hw0 hw1 x

end YMGap.Continuum.BF4WilsonAllNomeCenteringPin

#print axioms YMGap.Continuum.BF4WilsonAllNomeCenteringPin.centeredVector_pairing
#print axioms YMGap.Continuum.BF4WilsonAllNomeCenteringPin.centeredPart_embed
#print axioms YMGap.Continuum.BF4WilsonAllNomeCenteringPin.centeredState_embed
