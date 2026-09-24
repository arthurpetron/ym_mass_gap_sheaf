/-
# Sharp complex Cauchy--Schwarz on the SAME joint completion

The actual reflected finite inequality passes through cutoff removal and
the existing representative pairing limits, then descends to the existing
complex carrier. No representative is selected, no new carrier is built,
and no zero decision on constructive reals is used. Nome and width remain
fixed; this supplies a Hilbert-space prerequisite, not a continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicComplexCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "J" => jointPairing hw0 hw1 width
local notation "R" => representativeInner hw0 hw1 width
local notation "I" => inner hw0 hw1 width

attribute [local irreducible] jointPairing representativeInner

/-- Sharp complex inequality for the actual cutoff-removed dense pairing. -/
theorem jointPairingComplex_cauchySchwarz
    (x y : PhysicalSpan width × PhysicalSpan width) :
    leEv
      (add
        (mul (add (J x.1 y.1) (J x.2 y.2)) (add (J x.1 y.1) (J x.2 y.2)))
        (mul (sub (J x.1 y.2) (J x.2 y.1)) (sub (J x.1 y.2) (J x.2 y.1))))
      (mul (add (J x.1 x.1) (J x.2 x.2)) (add (J y.1 y.1) (J y.2 y.2))) := by
  have hre := TrigAddCReal.convergesTo_add
    (pairing_converges_jointPairing hw0 hw1 width x.1 y.1)
    (pairing_converges_jointPairing hw0 hw1 width x.2 y.2)
  have him := TrigAddCReal.convergesTo_add
    (pairing_converges_jointPairing hw0 hw1 width x.1 y.2)
    (TrigAddCReal.convergesTo_neg
      (pairing_converges_jointPairing hw0 hw1 width x.2 y.1))
  have hxx := TrigAddCReal.convergesTo_add
    (pairing_converges_jointPairing hw0 hw1 width x.1 x.1)
    (pairing_converges_jointPairing hw0 hw1 width x.2 x.2)
  have hyy := TrigAddCReal.convergesTo_add
    (pairing_converges_jointPairing hw0 hw1 width y.1 y.1)
    (pairing_converges_jointPairing hw0 hw1 width y.2 y.2)
  exact leEv_of_convergesTo_le
    (TrigAddCReal.convergesTo_add (convergesTo_mul_general hre hre)
      (convergesTo_mul_general him him))
    (convergesTo_mul_general hxx hyy)
    (fun stage => pairingComplex_cauchySchwarz hw0 hw1 width stage x y)

/-- Both components use their supplied Cauchy representatives and the SAME
pairing limits. This is not a choice of representatives from quotient data. -/
theorem representativeInnerComplex_cauchySchwarz
    (X Y : (D).Cauchy × (D).Cauchy) :
    leEv
      (add
        (mul (add (R X.1 Y.1) (R X.2 Y.2)) (add (R X.1 Y.1) (R X.2 Y.2)))
        (mul (sub (R X.1 Y.2) (R X.2 Y.1)) (sub (R X.1 Y.2) (R X.2 Y.1))))
      (mul (add (R X.1 X.1) (R X.2 X.2)) (add (R Y.1 Y.1) (R Y.2 Y.2))) := by
  have hre := TrigAddCReal.convergesTo_add
    (pairSequence_converges hw0 hw1 width X.1 Y.1)
    (pairSequence_converges hw0 hw1 width X.2 Y.2)
  have him := TrigAddCReal.convergesTo_add
    (pairSequence_converges hw0 hw1 width X.1 Y.2)
    (TrigAddCReal.convergesTo_neg
      (pairSequence_converges hw0 hw1 width X.2 Y.1))
  have hxx := TrigAddCReal.convergesTo_add
    (pairSequence_converges hw0 hw1 width X.1 X.1)
    (pairSequence_converges hw0 hw1 width X.2 X.2)
  have hyy := TrigAddCReal.convergesTo_add
    (pairSequence_converges hw0 hw1 width Y.1 Y.1)
    (pairSequence_converges hw0 hw1 width Y.2 Y.2)
  exact leEv_of_convergesTo_le
    (TrigAddCReal.convergesTo_add (convergesTo_mul_general hre hre)
      (convergesTo_mul_general him him))
    (convergesTo_mul_general hxx hyy)
    (fun n => jointPairingComplex_cauchySchwarz hw0 hw1 width
      (X.1.seq n, X.2.seq n) (Y.1.seq n, Y.2.seq n))

/-- Sharp complex Cauchy--Schwarz, with constant ONE, on the existing actual
complexification of `JointCompletion`. -/
theorem inner_cauchySchwarz (x y : ComplexCarrier hw0 hw1 width) :
    RCle
      (RCadd (RCmul (I x y).1 (I x y).1) (RCmul (I x y).2 (I x y).2))
      (RCmul (I x x).1 (I y y).1) := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  refine Quotient.inductionOn₂ x₁ x₂ ?_
  intro X₁ X₂
  refine Quotient.inductionOn₂ y₁ y₂ ?_
  intro Y₁ Y₂
  exact representativeInnerComplex_cauchySchwarz hw0 hw1 width (X₁, X₂) (Y₁, Y₂)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.jointPairingComplex_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.representativeInnerComplex_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.inner_cauchySchwarz
