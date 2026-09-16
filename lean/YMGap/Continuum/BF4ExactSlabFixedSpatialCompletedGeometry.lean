/-
# Actual completed Cauchy--Schwarz and squared-distance geometry

The original sharp CS and squared-distance laws pass through the SAME
explicit pairing limits. Completed subtraction uses the proved actual
linear operations; its diagonal defines the completed squared distance.
Distance zero is exactly equality on the existing carrier.

These are genuine geometry and original-embedding identities, not a proof
of metric completeness, real scalar extension or the continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletionLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedBilinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "D" => seminorm hw0 hw1 width stage

theorem representativeInner_cauchySchwarz (X Y : (D).Cauchy) :
    leEv (mul (representativeInner hw0 hw1 width stage X Y) (representativeInner hw0 hw1 width stage X Y))
      (mul (representativeInner hw0 hw1 width stage X X) (representativeInner hw0 hw1 width stage Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 width stage X Y) (pairSequence_converges hw0 hw1 width stage X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges hw0 hw1 width stage X X) (pairSequence_converges hw0 hw1 width stage Y Y))
    (fun n => pairing_cauchySchwarz hw0 hw1 width (X.seq n).val (Y.seq n).val
      (X.seq n).property (Y.seq n).property stage)

theorem completedInner_cauchySchwarz (x y : Completion hw0 hw1 width stage) :
    RCle (RCmul (completedInner hw0 hw1 width stage x y) (completedInner hw0 hw1 width stage x y))
      (RCmul (completedInner hw0 hw1 width stage x x) (completedInner hw0 hw1 width stage y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz hw0 hw1 width stage

def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition hw0 hw1 width stage).mapCauchy X
    ((scalarContinuous hw0 hw1 width stage (-1)).mapCauchy Y)

def completedSub (x y : Completion hw0 hw1 width stage) : Completion hw0 hw1 width stage :=
  completedAdd hw0 hw1 width stage x (completedNeg hw0 hw1 width stage y)

theorem completedSub_mk (X Y : (D).Cauchy) :
    completedSub hw0 hw1 width stage
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (differenceCauchy hw0 hw1 width stage X Y) := rfl

def representativeDist (X Y : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 width stage
    (differenceCauchy hw0 hw1 width stage X Y) (differenceCauchy hw0 hw1 width stage X Y)

def completedDist (x y : Completion hw0 hw1 width stage) : RC :=
  completedInner hw0 hw1 width stage (completedSub hw0 hw1 width stage x y)
    (completedSub hw0 hw1 width stage x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist hw0 hw1 width stage
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist hw0 hw1 width stage X Y) := rfl

theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => distSq hw0 hw1 width stage (X.seq n) (Y.seq n))
      (representativeDist hw0 hw1 width stage X Y) :=
  pairSequence_converges hw0 hw1 width stage
    (differenceCauchy hw0 hw1 width stage X Y) (differenceCauchy hw0 hw1 width stage X Y)

theorem completedDist_embedSpan (x y : PhysicalSpan width) :
    completedDist hw0 hw1 width stage (embedSpan hw0 hw1 width stage x)
        (embedSpan hw0 hw1 width stage y) = Quotient.mk crealSetoid (distSq hw0 hw1 width stage x y) :=
  completedInner_embedSpan hw0 hw1 width stage
    (BF4ExactSlabFixedSpatialIntrinsicLinear.addSpan x
      (BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan (-1) y))
    (BF4ExactSlabFixedSpatialIntrinsicLinear.addSpan x
      (BF4ExactSlabFixedSpatialIntrinsicLinear.smulSpan (-1) y))

theorem completedDist_nonnegative (x y : Completion hw0 hw1 width stage) :
    RCnonneg (completedDist hw0 hw1 width stage x y) :=
  completedInner_nonnegative hw0 hw1 width stage (completedSub hw0 hw1 width stage x y)

theorem completedAdd_zero (x : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage x (completedZero hw0 hw1 width stage) = x := by
  rw [completedAdd_comm, completedZero_add]

theorem completedSub_add_cancel (x y : Completion hw0 hw1 width stage) :
    completedAdd hw0 hw1 width stage (completedSub hw0 hw1 width stage x y) y = x := by
  change completedAdd hw0 hw1 width stage (completedAdd hw0 hw1 width stage x
    (completedNeg hw0 hw1 width stage y)) y = x
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

theorem completedSub_self (x : Completion hw0 hw1 width stage) :
    completedSub hw0 hw1 width stage x x = completedZero hw0 hw1 width stage := by
  change completedAdd hw0 hw1 width stage x (completedNeg hw0 hw1 width stage x) =
    completedZero hw0 hw1 width stage
  rw [completedAdd_comm, completedNeg_add]

theorem completedDist_zero_iff (x y : Completion hw0 hw1 width stage) :
    completedDist hw0 hw1 width stage x y = RCzero ↔ x = y := by
  constructor
  · intro h
    have hz := (completedInner_posdef hw0 hw1 width stage (completedSub hw0 hw1 width stage x y)).mp h
    have hxy := congrArg (fun z => completedAdd hw0 hw1 width stage z y) hz
    change completedAdd hw0 hw1 width stage (completedSub hw0 hw1 width stage x y) y =
      completedAdd hw0 hw1 width stage (completedZero hw0 hw1 width stage) y at hxy
    rw [completedSub_add_cancel, completedZero_add] at hxy
    exact hxy
  · intro h
    unfold completedDist
    rw [h, completedSub_self, completedInner_zero_left]

theorem representativeDist_symm (X Y : (D).Cauchy) :
    Equiv (representativeDist hw0 hw1 width stage X Y) (representativeDist hw0 hw1 width stage Y X) :=
  Equiv_of_limit_of_equal (fun n => distSq_symm hw0 hw1 width stage (X.seq n) (Y.seq n))
    (representativeDist_converges hw0 hw1 width stage X Y)
    (representativeDist_converges hw0 hw1 width stage Y X)

theorem completedDist_symm (x y : Completion hw0 hw1 width stage) :
    completedDist hw0 hw1 width stage x y = completedDist hw0 hw1 width stage y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeDist_symm hw0 hw1 width stage X Y)

theorem representativeDist_triangle (X Y Z : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 width stage X Z)
      (add (add (representativeDist hw0 hw1 width stage X Y) (representativeDist hw0 hw1 width stage X Y))
        (add (representativeDist hw0 hw1 width stage Y Z) (representativeDist hw0 hw1 width stage Y Z))) := by
  have hXY := representativeDist_converges hw0 hw1 width stage X Y
  have hYZ := representativeDist_converges hw0 hw1 width stage Y Z
  have hsum := TrigAddCReal.convergesTo_add
    (TrigAddCReal.convergesTo_add hXY hXY) (TrigAddCReal.convergesTo_add hYZ hYZ)
  exact leEv_of_convergesTo_le (representativeDist_converges hw0 hw1 width stage X Z) hsum
    (fun n => distSq_triangle hw0 hw1 width stage (X.seq n) (Y.seq n) (Z.seq n))

theorem completedDist_triangle (x y z : Completion hw0 hw1 width stage) :
    RCle (completedDist hw0 hw1 width stage x z)
      (RCadd (RCadd (completedDist hw0 hw1 width stage x y) (completedDist hw0 hw1 width stage x y))
        (RCadd (completedDist hw0 hw1 width stage y z) (completedDist hw0 hw1 width stage y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact representativeDist_triangle hw0 hw1 width stage

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.representativeInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedInner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.differenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedSub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedSub_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.representativeDist
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_mk
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.representativeDist_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedAdd_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedSub_add_cancel
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedSub_self
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.representativeDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.representativeDist_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry.completedDist_triangle
