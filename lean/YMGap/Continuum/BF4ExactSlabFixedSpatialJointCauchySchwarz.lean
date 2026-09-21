/-
# Sharp Cauchy--Schwarz on the actual fixed-spatial joint completion

The dense sharp Cauchy--Schwarz inequality passes through the already
constructed pairing limits and then descends to the SAME bespoke
`JointCompletion`.  No new carrier, pairing-data wrapper, or analytic
assumption is introduced.  This is a completed-form inequality at fixed nome
and fixed spatial width; it is not a spatial-limit or continuum-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width

/-- Sharp Cauchy--Schwarz for representatives of the actual joint completion,
obtained from the dense joint pairing at every common Cauchy index. -/
theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv
      (mul (representativeInner hw0 hw1 width X Y)
        (representativeInner hw0 hw1 width X Y))
      (mul (representativeInner hw0 hw1 width X X)
        (representativeInner hw0 hw1 width Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 width X Y)
      (pairSequence_converges hw0 hw1 width X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 width X X)
      (pairSequence_converges hw0 hw1 width Y Y))
    (fun n => jointPairing_cauchySchwarz hw0 hw1 width (X.seq n) (Y.seq n))

/-- Sharp Cauchy--Schwarz on the existing bespoke `JointCompletion` and its
existing `completedInner`. -/
theorem completedInner_cauchySchwarz
    (x y : JointCompletion hw0 hw1 width) :
    RCle (RCmul (B x y) (B x y))
      (RCmul (B x x) (B y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz hw0 hw1 width

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz.representativeInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz.completedInner_cauchySchwarz
