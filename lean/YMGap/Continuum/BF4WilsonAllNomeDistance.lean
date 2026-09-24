/-
# Squared distance on the literal all-nome Wilson completion

The distance is the completed inner product of the actual completed
subtraction on the existing all-nome carrier.  All distance laws are inherited
from the original literal seminorm and its explicit Cauchy pairing limits.
This is a distance-data interface, not a completeness or real-scalar claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeLinearLaws
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeGeometry
import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.Continuum.BF4WilsonAllNomeDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.CRealSeminormCompletedApproximation (DistanceData)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm distSq distSq_symm distSq_triangle)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeGeometry
open YMGap.Continuum.CRealSeminormPairingCompletion (PairingData)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1

def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  (addition hw0 hw1).mapCauchy X
    ((scalarContinuous hw0 hw1 (-1)).mapCauchy Y)

def representativeDist (X Y : (D).Cauchy) : CReal :=
  CRealSeminormPairingCompletion.representativeInner PD
    (differenceCauchy hw0 hw1 X Y) (differenceCauchy hw0 hw1 X Y)

def completedDist (x y : V) : RC :=
  B (completedSub hw0 hw1 x y) (completedSub hw0 hw1 x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist hw0 hw1
        (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist hw0 hw1 X Y) := rfl

theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => (D).distSq (X.seq n) (Y.seq n))
      (representativeDist hw0 hw1 X Y) := by
  exact CRealSeminormPairingCompletion.pairSequence_converges PD
    (differenceCauchy hw0 hw1 X Y) (differenceCauchy hw0 hw1 X Y)

theorem completedDist_nonnegative (x y : V) :
    RCnonneg (completedDist hw0 hw1 x y) := by
  exact completedInner_nonnegative hw0 hw1
    (completedSub hw0 hw1 x y)

theorem representativeDist_symm (X Y : (D).Cauchy) :
    Equiv (representativeDist hw0 hw1 X Y) (representativeDist hw0 hw1 Y X) :=
  Equiv_of_limit_of_equal (fun n => distSq_symm hw0 hw1 (X.seq n) (Y.seq n))
    (representativeDist_converges hw0 hw1 X Y)
    (representativeDist_converges hw0 hw1 Y X)

theorem completedDist_symm (x y : V) :
    completedDist hw0 hw1 x y = completedDist hw0 hw1 y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  rw [completedDist_mk, completedDist_mk]
  exact Quotient.sound (representativeDist_symm hw0 hw1 X Y)

theorem representativeDist_triangle (X Y Z : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 X Z)
      (add (add (representativeDist hw0 hw1 X Y) (representativeDist hw0 hw1 X Y))
        (add (representativeDist hw0 hw1 Y Z) (representativeDist hw0 hw1 Y Z))) := by
  have hXY := representativeDist_converges hw0 hw1 X Y
  have hYZ := representativeDist_converges hw0 hw1 Y Z
  have hsum := TrigAddCReal.convergesTo_add
    (TrigAddCReal.convergesTo_add hXY hXY)
    (TrigAddCReal.convergesTo_add hYZ hYZ)
  exact leEv_of_convergesTo_le
    (representativeDist_converges hw0 hw1 X Z) hsum
    (fun n => distSq_triangle hw0 hw1 (X.seq n) (Y.seq n) (Z.seq n))

theorem completedDist_triangle (x y z : V) :
    RCle (completedDist hw0 hw1 x z)
      (RCadd (RCadd (completedDist hw0 hw1 x y) (completedDist hw0 hw1 x y))
        (RCadd (completedDist hw0 hw1 y z) (completedDist hw0 hw1 y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact representativeDist_triangle hw0 hw1

private theorem completedSub_add_cancel (x y : V) :
    completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

theorem completedDist_zero_iff (x y : V) :
    completedDist hw0 hw1 x y = RCzero ↔ x = y := by
  constructor
  · intro h
    have hz := (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1
      (width := width) (completedSub hw0 hw1 x y)).mp h
    have hxy := congrArg (fun z => completedAdd hw0 hw1 z y) hz
    change completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y =
      completedAdd hw0 hw1 (completedZero hw0 hw1 width) y at hxy
    rw [completedSub_add_cancel, completedZero_add] at hxy
    exact hxy
  · intro h
    unfold completedDist
    rw [h, completedSub_self]
    exact completedInner_zero_left hw0 hw1 (completedZero hw0 hw1 width)

def distanceData : DistanceData (seminorm hw0 hw1 (width := width)) where
  representativeDist := representativeDist hw0 hw1
  representativeDist_converges := representativeDist_converges hw0 hw1
  completedDist := completedDist hw0 hw1
  completedDist_mk := completedDist_mk hw0 hw1
  completedDist_nonnegative := completedDist_nonnegative hw0 hw1
  completedDist_symm := completedDist_symm hw0 hw1
  completedDist_triangle := completedDist_triangle hw0 hw1
  completedDist_zero_iff := completedDist_zero_iff hw0 hw1

#print axioms differenceCauchy
#print axioms representativeDist
#print axioms completedDist
#print axioms completedDist_mk
#print axioms representativeDist_converges
#print axioms completedDist_nonnegative
#print axioms representativeDist_symm
#print axioms completedDist_symm
#print axioms representativeDist_triangle
#print axioms completedDist_triangle
#print axioms completedDist_zero_iff
#print axioms distanceData

end YMGap.Continuum.BF4WilsonAllNomeDistance
