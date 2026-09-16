/-
# Actual squared distance on the spatial union completion

The squared norm of the actual completed difference is the limit of the
original union distances. The termwise identification is proved by the
common-base difference pin, not assumed to hold definitionally. The scalar
representative retains its constructed approximation modulus.

These identities supply every field of the generic completed-distance data
on the SAME UnionCompletion, including separation, and separately prove
original physical-time contraction. They do not select representatives,
prove arbitrary-sequence metric completeness, or replace the reflected
carrier by another model.
-/

import YMGap.Continuum.BF4SpatialUnionBilinear
import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.Continuum.BF4SpatialUnionCompletedDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
  (pairingData completedInner completedInner_embedStage completedInner_nonnegative)
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner representativeInnerCauchy pairSequence_converges)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

def representativeDist (X Y : (D).Cauchy) : CReal :=
  representativeInner PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
    (differenceCauchy hw0 hw1 hsmall hd hs X Y)

def representativeDistCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeDist hw0 hw1 hsmall hd hs X Y).approx :=
  representativeInnerCauchy PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
    (differenceCauchy hw0 hw1 hsmall hd hs X Y)

def completedDist (x y : V) : RC :=
  B (completedSub hw0 hw1 hsmall hd hs x y) (completedSub hw0 hw1 hsmall hd hs x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)
      (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist hw0 hw1 hsmall hd hs X Y) := rfl

/-- Pointwise common-base equivalence, followed by the actual mixed-pairing limit. -/
theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => distSq hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n))
      (representativeDist hw0 hw1 hsmall hd hs X Y) :=
  TrigAddCReal.convergesTo_congr_seq
    (fun n => (distance_difference hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n)).symm)
    (pairSequence_converges PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
      (differenceCauchy hw0 hw1 hsmall hd hs X Y))

theorem completedSub_embedStage (x y : Stage) :
    completedSub hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) =
      embedStage hw0 hw1 hsmall hd hs (difference x y) := by
  unfold completedSub completedNeg
  rw [completedSmul_embedStage, completedAdd_embedStage]
  rfl

theorem completedDist_embedStage (x y : Stage) :
    completedDist hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) =
      Quotient.mk crealSetoid (distSq hw0 hw1 hsmall hd hs x y) := by
  unfold completedDist
  rw [completedSub_embedStage, completedInner_embedStage]
  exact Quotient.sound (distance_difference hw0 hw1 hsmall hd hs x y).symm

theorem completedDist_nonnegative (x y : V) :
    RCnonneg (completedDist hw0 hw1 hsmall hd hs x y) :=
  completedInner_nonnegative hw0 hw1 hsmall hd hs (completedSub hw0 hw1 hsmall hd hs x y)

theorem completedDist_zero_iff (x y : V) :
    completedDist hw0 hw1 hsmall hd hs x y = RCzero ↔ x = y :=
  completedSub_norm_zero_iff hw0 hw1 hsmall hd hs x y

theorem representativeDist_symm (X Y : (D).Cauchy) :
    Equiv (representativeDist hw0 hw1 hsmall hd hs X Y)
      (representativeDist hw0 hw1 hsmall hd hs Y X) :=
  Equiv_of_limit_of_equal (fun n => distance_symm hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n))
    (representativeDist_converges hw0 hw1 hsmall hd hs X Y)
    (representativeDist_converges hw0 hw1 hsmall hd hs Y X)

theorem completedDist_symm (x y : V) :
    completedDist hw0 hw1 hsmall hd hs x y = completedDist hw0 hw1 hsmall hd hs y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeDist_symm hw0 hw1 hsmall hd hs X Y)

theorem representativeDist_triangle (X Y Z : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 hsmall hd hs X Z)
      (add
        (add (representativeDist hw0 hw1 hsmall hd hs X Y)
          (representativeDist hw0 hw1 hsmall hd hs X Y))
        (add (representativeDist hw0 hw1 hsmall hd hs Y Z)
          (representativeDist hw0 hw1 hsmall hd hs Y Z))) := by
  have hXY := representativeDist_converges hw0 hw1 hsmall hd hs X Y
  have hYZ := representativeDist_converges hw0 hw1 hsmall hd hs Y Z
  exact leEv_of_convergesTo_le (representativeDist_converges hw0 hw1 hsmall hd hs X Z)
    (TrigAddCReal.convergesTo_add (TrigAddCReal.convergesTo_add hXY hXY)
      (TrigAddCReal.convergesTo_add hYZ hYZ))
    (fun n => distance_triangle hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n) (Z.seq n))

theorem completedDist_triangle (x y z : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs x z)
      (RCadd
        (RCadd (completedDist hw0 hw1 hsmall hd hs x y) (completedDist hw0 hw1 hsmall hd hs x y))
        (RCadd (completedDist hw0 hw1 hsmall hd hs y z) (completedDist hw0 hw1 hsmall hd hs y z))) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact representativeDist_triangle hw0 hw1 hsmall hd hs

theorem representativeDist_time_contraction (n : Nat) (X Y : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 hsmall hd hs
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X)
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y))
      (representativeDist hw0 hw1 hsmall hd hs X Y) :=
  leEv_of_convergesTo_le
    (representativeDist_converges hw0 hw1 hsmall hd hs
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy X)
      ((timeNonexpansive hw0 hw1 hsmall hd hs n).mapCauchy Y))
    (representativeDist_converges hw0 hw1 hsmall hd hs X Y)
    (fun k => time_contraction hw0 hw1 hsmall hd hs n (X.seq k) (Y.seq k))

/-- Constant-one contraction of the same original physical time, with no new rate. -/
theorem completedDist_time_contraction (n : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (T n x) (T n y))
      (completedDist hw0 hw1 hsmall hd hs x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeDist_time_contraction hw0 hw1 hsmall hd hs n

/-- Every generic distance field is supplied for the existing union completion. -/
def distanceData : CRealSeminormCompletedApproximation.DistanceData (D) where
  representativeDist := representativeDist hw0 hw1 hsmall hd hs
  representativeDist_converges := representativeDist_converges hw0 hw1 hsmall hd hs
  completedDist := completedDist hw0 hw1 hsmall hd hs
  completedDist_mk := completedDist_mk hw0 hw1 hsmall hd hs
  completedDist_nonnegative := completedDist_nonnegative hw0 hw1 hsmall hd hs
  completedDist_symm := completedDist_symm hw0 hw1 hsmall hd hs
  completedDist_triangle := completedDist_triangle hw0 hw1 hsmall hd hs
  completedDist_zero_iff := completedDist_zero_iff hw0 hw1 hsmall hd hs

#print axioms representativeDist
#print axioms representativeDistCauchy
#print axioms completedDist
#print axioms completedDist_mk
#print axioms representativeDist_converges
#print axioms completedSub_embedStage
#print axioms completedDist_embedStage
#print axioms completedDist_nonnegative
#print axioms completedDist_zero_iff
#print axioms representativeDist_symm
#print axioms completedDist_symm
#print axioms representativeDist_triangle
#print axioms completedDist_triangle
#print axioms representativeDist_time_contraction
#print axioms completedDist_time_contraction
#print axioms distanceData

end YMGap.Continuum.BF4SpatialUnionCompletedDistance
