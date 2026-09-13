/-
# Sharp CS and squared-distance geometry of the ORIGINAL completion

Only the general CReal multiplication-continuity theorem is reused from
the strict-cylinder module. Its arguments are arbitrary convergent real
sequences; no older carrier, physical law or transfer is substituted.
The original sharp CS passes through the actual plaquette pairing limits.

Completed differences and their squared norm recover the original distance
on embedded expressions. Symmetry and the sqrt-free triangle bound pass
through the same limits. Distance zero is exactly equality of states.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquettePairingLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletionLinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedBilinear
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedPosdef

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv (CReal.mul (representativeInner w hw0 hw1 X Y) (representativeInner w hw0 hw1 X Y))
      (CReal.mul (representativeInner w hw0 hw1 X X) (representativeInner w hw0 hw1 Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges w hw0 hw1 X Y) (pairSequence_converges w hw0 hw1 X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges w hw0 hw1 X X) (pairSequence_converges w hw0 hw1 Y Y))
    (fun n => form_cauchySchwarz w hw0 hw1 (X.seq n) (Y.seq n))

theorem completedInner_cauchySchwarz (x y : Completion w hw0 hw1 half) :
    RCle (RCmul (completedInner w hw0 hw1 x y) (completedInner w hw0 hw1 x y))
      (RCmul (completedInner w hw0 hw1 x x) (completedInner w hw0 hw1 y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz w hw0 hw1

def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition w hw0 hw1).mapCauchy X ((scalarContinuous w hw0 hw1 (-1)).mapCauchy Y)

def completedSub (x y : Completion w hw0 hw1 half) : Completion w hw0 hw1 half :=
  completedAdd w hw0 hw1 x (completedNeg w hw0 hw1 y)

theorem completedSub_mk (X Y : (D).Cauchy) :
    completedSub w hw0 hw1 (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (differenceCauchy w hw0 hw1 X Y) := rfl

def representativeDist (X Y : (D).Cauchy) : CReal :=
  representativeInner w hw0 hw1 (differenceCauchy w hw0 hw1 X Y) (differenceCauchy w hw0 hw1 X Y)

def completedDist (x y : Completion w hw0 hw1 half) : RC :=
  completedInner w hw0 hw1 (completedSub w hw0 hw1 x y) (completedSub w hw0 hw1 x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist w hw0 hw1 (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist w hw0 hw1 X Y) := rfl

theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => distSq w hw0 hw1 (X.seq n) (Y.seq n)) (representativeDist w hw0 hw1 X Y) :=
  pairSequence_converges w hw0 hw1 (differenceCauchy w hw0 hw1 X Y) (differenceCauchy w hw0 hw1 X Y)

theorem completedDist_embedExpression (e f : PlaquetteExpression half) :
    completedDist w hw0 hw1 (embedExpression w hw0 hw1 e) (embedExpression w hw0 hw1 f) =
      Quotient.mk crealSetoid (distSq w hw0 hw1 e f) :=
  completedInner_embedExpression w hw0 hw1 (subtract e f) (subtract e f)

theorem completedDist_nonnegative (x y : Completion w hw0 hw1 half) :
    RCnonneg (completedDist w hw0 hw1 x y) := completedInner_nonnegative w hw0 hw1 (completedSub w hw0 hw1 x y)

theorem completedAdd_zero (x : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 x (completedZero w hw0 hw1 half) = x := by
  rw [completedAdd_comm, completedZero_add]

theorem completedSub_add_cancel (x y : Completion w hw0 hw1 half) :
    completedAdd w hw0 hw1 (completedSub w hw0 hw1 x y) y = x := by
  change completedAdd w hw0 hw1 (completedAdd w hw0 hw1 x (completedNeg w hw0 hw1 y)) y = x
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

theorem completedSub_self (x : Completion w hw0 hw1 half) :
    completedSub w hw0 hw1 x x = completedZero w hw0 hw1 half := by
  change completedAdd w hw0 hw1 x (completedNeg w hw0 hw1 x) = completedZero w hw0 hw1 half
  rw [completedAdd_comm, completedNeg_add]

theorem completedDist_zero_iff (x y : Completion w hw0 hw1 half) :
    completedDist w hw0 hw1 x y = RCzero ↔ x = y := by
  constructor
  · intro h
    have hz := (completedInner_posdef w hw0 hw1 (completedSub w hw0 hw1 x y)).mp h
    have hxy := congrArg (fun z => completedAdd w hw0 hw1 z y) hz
    change completedAdd w hw0 hw1 (completedSub w hw0 hw1 x y) y =
      completedAdd w hw0 hw1 (completedZero w hw0 hw1 half) y at hxy
    rw [completedSub_add_cancel, completedZero_add] at hxy
    exact hxy
  · intro h
    unfold completedDist
    rw [h, completedSub_self, completedInner_zero_left]

theorem representativeDist_symm (X Y : (D).Cauchy) :
    Equiv (representativeDist w hw0 hw1 X Y) (representativeDist w hw0 hw1 Y X) :=
  Equiv_of_limit_of_equal (fun n => distSq_symm w hw0 hw1 (X.seq n) (Y.seq n))
    (representativeDist_converges w hw0 hw1 X Y) (representativeDist_converges w hw0 hw1 Y X)

theorem completedDist_symm (x y : Completion w hw0 hw1 half) :
    completedDist w hw0 hw1 x y = completedDist w hw0 hw1 y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeDist_symm w hw0 hw1 X Y)

theorem representativeDist_triangle (X Y Z : (D).Cauchy) :
    leEv (representativeDist w hw0 hw1 X Z)
      (CReal.add (CReal.add (representativeDist w hw0 hw1 X Y) (representativeDist w hw0 hw1 X Y))
        (CReal.add (representativeDist w hw0 hw1 Y Z) (representativeDist w hw0 hw1 Y Z))) := by
  have hXY := representativeDist_converges w hw0 hw1 X Y
  have hYZ := representativeDist_converges w hw0 hw1 Y Z
  have hsum := TrigAddCReal.convergesTo_add (TrigAddCReal.convergesTo_add hXY hXY) (TrigAddCReal.convergesTo_add hYZ hYZ)
  exact leEv_of_convergesTo_le (representativeDist_converges w hw0 hw1 X Z) hsum
    (fun n => distSq_triangle w hw0 hw1 (X.seq n) (Y.seq n) (Z.seq n))

theorem completedDist_triangle (x y z : Completion w hw0 hw1 half) :
    RCle (completedDist w hw0 hw1 x z)
      (RCadd (RCadd (completedDist w hw0 hw1 x y) (completedDist w hw0 hw1 x y))
        (RCadd (completedDist w hw0 hw1 y z) (completedDist w hw0 hw1 y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact representativeDist_triangle w hw0 hw1

end YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.representativeInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.differenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedSub
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedSub_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.representativeDist
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_mk
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.representativeDist_converges
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedAdd_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedSub_add_cancel
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedSub_self
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.representativeDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.representativeDist_triangle
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry.completedDist_triangle
