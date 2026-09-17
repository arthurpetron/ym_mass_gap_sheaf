/-
# Actual squared distance on the SAME Wilson union completion

The squared norm of the actual completed Wilson difference is the limit of
the original union distances. Its termwise identification uses the proved
literal difference pin, and its scalar representative retains computed
rational Cauchy data.

Every field of the generic completed-distance data is proved for the SAME
Wilson union. Original physical time contracts this distance. These data
support diagonal limits of supplied Cauchy rows; they do not choose quotient
representatives, prove arbitrary quotient-sequence completeness, or identify
the carrier with a full continuum Hilbert/OS/QFT construction.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionBilinear
import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (pairingData representativeInner representativeInnerCauchy
    completedInner completedInner_embedStage completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionLinear (distance_difference)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.CRealSeminormPairingCompletion (pairSequence_converges)
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
local notation "Z" => completedZero hw0 hw1 hsmall hd hs

def representativeDist (X Y : (D).Cauchy) : CReal :=
  representativeInner hw0 hw1 hsmall hd hs (differenceCauchy hw0 hw1 hsmall hd hs X Y)
    (differenceCauchy hw0 hw1 hsmall hd hs X Y)

def representativeDistCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeDist hw0 hw1 hsmall hd hs X Y).approx :=
  representativeInnerCauchy hw0 hw1 hsmall hd hs (differenceCauchy hw0 hw1 hsmall hd hs X Y)
    (differenceCauchy hw0 hw1 hsmall hd hs X Y)

def completedDist (x y : V) : RC :=
  B (completedSub hw0 hw1 hsmall hd hs x y) (completedSub hw0 hw1 hsmall hd hs x y)

theorem completedDist_mk (X Y : (D).Cauchy) :
    completedDist hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X)
      (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk crealSetoid (representativeDist hw0 hw1 hsmall hd hs X Y) := rfl

/-- The ORIGINAL dense distances converge to the actual norm of the difference. -/
theorem representativeDist_converges (X Y : (D).Cauchy) :
    ConvergesTo (fun n => distSq hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n))
      (representativeDist hw0 hw1 hsmall hd hs X Y) := by
  refine TrigAddCReal.convergesTo_congr_seq ?_
    (pairSequence_converges PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
      (differenceCauchy hw0 hw1 hsmall hd hs X Y))
  intro n
  change Equiv
    (pairing hw0 hw1 hsmall hd hs
      ((differenceCauchy hw0 hw1 hsmall hd hs X Y).seq n)
      ((differenceCauchy hw0 hw1 hsmall hd hs X Y).seq n))
    (distSq hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n))
  rw [differenceCauchy_seq]
  exact (distance_difference hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n)).symm

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

theorem completedDist_refl (x : V) : completedDist hw0 hw1 hsmall hd hs x x = RCzero :=
  (completedDist_zero_iff hw0 hw1 hsmall hd hs x x).mpr rfl

/-- This is distance to the existing completed zero, not a new metric origin. -/
theorem completedDist_zero_right (x : V) :
    completedDist hw0 hw1 hsmall hd hs x Z = B x x := by
  unfold completedDist
  rw [completedSub_zero]

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

theorem representativeDist_triangle (X Y W : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 hsmall hd hs X W)
      (add
        (add (representativeDist hw0 hw1 hsmall hd hs X Y)
          (representativeDist hw0 hw1 hsmall hd hs X Y))
        (add (representativeDist hw0 hw1 hsmall hd hs Y W)
          (representativeDist hw0 hw1 hsmall hd hs Y W))) := by
  have hXY := representativeDist_converges hw0 hw1 hsmall hd hs X Y
  have hYW := representativeDist_converges hw0 hw1 hsmall hd hs Y W
  exact leEv_of_convergesTo_le (representativeDist_converges hw0 hw1 hsmall hd hs X W)
    (TrigAddCReal.convergesTo_add (TrigAddCReal.convergesTo_add hXY hXY)
      (TrigAddCReal.convergesTo_add hYW hYW))
    (fun n => distance_triangle hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n) (W.seq n))

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

/-- Constant-one contraction of the SAME original physical time, with no new rate. -/
theorem completedDist_time_contraction (n : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (T n x) (T n y))
      (completedDist hw0 hw1 hsmall hd hs x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeDist_time_contraction hw0 hw1 hsmall hd hs n

/-- Every generic distance field is proved for the existing Wilson completion. -/
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
#print axioms completedDist_embedStage
#print axioms completedDist_nonnegative
#print axioms completedDist_zero_iff
#print axioms completedDist_refl
#print axioms completedDist_zero_right
#print axioms representativeDist_symm
#print axioms completedDist_symm
#print axioms representativeDist_triangle
#print axioms completedDist_triangle
#print axioms representativeDist_time_contraction
#print axioms completedDist_time_contraction
#print axioms distanceData

end YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
