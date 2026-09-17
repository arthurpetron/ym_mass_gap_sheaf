/-
# Time-zero Wilson multiplication on the SAME spatial-union completion

A supplied spatial loop is included at the computed common base with each
input state. Literal inclusion coherence and the proved intrinsic OS bound
give a squared-distance cap depending only on the spin. The positive input
tolerance epsilon/(characterBound spin+1) constructs a map on the existing
explicit-modulus Cauchy quotient, even for streams with unbounded supports.

This is an actual bounded observable multiplication map, not an assumed
ordinary-Haar-to-OS comparison. Linearity, symmetry and a full canonical
observable representation are subsequent consumers. No strict transfer gap,
changing-spacing estimate or continuum QFT is asserted here.
-/

import YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance

namespace YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop recenterLoop_comp)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (inclusion inclusion_trans)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
  (representativeDist representativeDist_converges completedDist)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound character_squareBound SquareBound)

/-- Include the supplied loop without translating its physical edges. -/
def loopAt {base larger : Nat} (L : SourceLoop base) (h : base ≤ larger) :
    SourceLoop larger := recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) L

theorem loopAt_trans {base middle larger : Nat} (L : SourceLoop base)
    (h : base ≤ middle) (k : middle ≤ larger) :
    loopAt (loopAt L h) k = loopAt L (Nat.le_trans h k) :=
  recenterLoop_comp (first := 0) (second := 0) _ _ L

def multiplyStage {base : Nat} (L : SourceLoop base) (spin : Nat) (x : Stage) : Stage :=
  ⟨max base x.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_right _ _),
    BF4WilsonTimeZeroIntrinsicMultiplier.multiply (loopAt L (Nat.le_max_left _ _)) spin
      (atBase x (Nat.le_max_right _ _))⟩

/-- A larger common base sees exactly the same literal multiplication. -/
theorem atBase_multiply {base larger : Nat} (L : SourceLoop base) (spin : Nat)
    (x : Stage) (hL : base ≤ larger) (hx : x.base ≤ larger) :
    atBase (multiplyStage L spin x) (Nat.max_le.mpr ⟨hL,hx⟩) =
      BF4WilsonTimeZeroIntrinsicMultiplier.multiply (loopAt L hL) spin (atBase x hx) := by
  simp only [atBase, multiplyStage, BF4WilsonTimeZeroIntrinsicMultiplier.inclusion_multiply,
    inclusion_trans, loopAt, recenterLoop_comp]

theorem multiplierCap_nonnegative (spin : Nat) : (0 : Q') ≤ characterBound spin :=
  (character_squareBound (SquareBound.one 0) spin).nonnegative

private theorem multiplierBudget_pos (spin : Nat) : (0 : Q') < characterBound spin + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 (characterBound spin) (multiplierCap_nonnegative spin))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- A rational, positive tolerance; no square root or choice of modulus is needed. -/
def multiplierTolerance (spin : Nat) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (characterBound spin + 1) (multiplierBudget_pos spin)

theorem multiplierTolerance_pos (spin : Nat) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < multiplierTolerance spin epsilon := Q'.divPos_pos _ _ _ he

theorem multiplierTolerance_bound (spin : Nat) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    characterBound spin * multiplierTolerance spin epsilon ≤ epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (characterBound spin) 1 Q'.zero_le_one)
      (Q'.le_of_lt (multiplierTolerance_pos spin he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "d" => distSq hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

attribute [local irreducible] distSq
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

/-- The original union OS distance, not an auxiliary Haar norm, obeys the cap. -/
theorem distance_multiply_bound {base : Nat} (L : SourceLoop base) (spin : Nat) (x y : Stage) :
    leEv (d (multiplyStage L spin x) (multiplyStage L spin y))
      (mul (ofQ' (characterBound spin)) (d x y)) := by
  let N := max base (max x.base y.base)
  have hL : base ≤ N := by omega
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hpin := distSq_at_base hw0 hw1 hsmall hd hs
    (multiplyStage L spin x) (multiplyStage L spin y) N
    (Nat.max_le.mpr ⟨hL,hx⟩) (Nat.max_le.mpr ⟨hL,hy⟩)
  simp only [atBase_multiply L spin x hL hx, atBase_multiply L spin y hL hy] at hpin
  exact leEv_trans (leEv_of_equiv hpin)
    (leEv_trans (BF4WilsonTimeZeroIntrinsicMultiplier.distSq_multiplier_bound
      hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (loopAt L hL) spin (atBase x hx) (atBase y hy))
      (leEv_of_equiv (Pivot2.mul_congr_right
        (distSq_at_base hw0 hw1 hsmall hd hs x y N hx hy).symm)))

def multiplierContinuous {base : Nat} (L : SourceLoop base) (spin : Nat) :
    (D).ModulusContinuous where
  toFun := multiplyStage L spin
  tolerance := multiplierTolerance spin
  tolerance_pos := fun _ => multiplierTolerance_pos spin
  contraction := by
    intro epsilon he x y h
    have hc : leEv czero (ofQ' (characterBound spin)) :=
      leEv_ofQ'_of_approx_ge (fun _ => multiplierCap_nonnegative spin)
    exact leEv_trans (distance_multiply_bound hw0 hw1 hsmall hd hs L spin x y)
      (leEv_trans (leEv_mul_nonneg_left hc h)
        (leEv_le_ofQ'_of_approx_le (fun _ => multiplierTolerance_bound spin he)))

def multiplyCauchy {base : Nat} (L : SourceLoop base) (spin : Nat) (X : (D).Cauchy) :
    (D).Cauchy := (multiplierContinuous hw0 hw1 hsmall hd hs L spin).mapCauchy X

theorem multiplyCauchy_seq {base : Nat} (L : SourceLoop base) (spin : Nat)
    (X : (D).Cauchy) (n : Nat) :
    (multiplyCauchy hw0 hw1 hsmall hd hs L spin X).seq n = multiplyStage L spin (X.seq n) := rfl

theorem multiplyCauchy_modulus {base : Nat} (L : SourceLoop base) (spin : Nat)
    (X : (D).Cauchy) (epsilon : Q') :
    (multiplyCauchy hw0 hw1 hsmall hd hs L spin X).modulus epsilon =
      X.modulus (multiplierTolerance spin epsilon) := rfl

/-- An actual observable map on the existing union completion, with no new carrier. -/
def completedMultiply {base : Nat} (L : SourceLoop base) (spin : Nat) : V → V :=
  (multiplierContinuous hw0 hw1 hsmall hd hs L spin).completionMap

theorem completedMultiply_mk {base : Nat} (L : SourceLoop base) (spin : Nat)
    (X : (D).Cauchy) :
    completedMultiply hw0 hw1 hsmall hd hs L spin (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (multiplyCauchy hw0 hw1 hsmall hd hs L spin X) := rfl

theorem completedMultiply_embedStage {base : Nat} (L : SourceLoop base) (spin : Nat) (x : Stage) :
    completedMultiply hw0 hw1 hsmall hd hs L spin (embedStage hw0 hw1 hsmall hd hs x) =
      embedStage hw0 hw1 hsmall hd hs (multiplyStage L spin x) := rfl

theorem representativeDist_multiply_bound {base : Nat} (L : SourceLoop base) (spin : Nat)
    (X Y : (D).Cauchy) :
    leEv (representativeDist hw0 hw1 hsmall hd hs
      (multiplyCauchy hw0 hw1 hsmall hd hs L spin X)
      (multiplyCauchy hw0 hw1 hsmall hd hs L spin Y))
      (mul (ofQ' (characterBound spin)) (representativeDist hw0 hw1 hsmall hd hs X Y)) :=
  leEv_of_convergesTo_le
    (representativeDist_converges hw0 hw1 hsmall hd hs
      (multiplyCauchy hw0 hw1 hsmall hd hs L spin X)
      (multiplyCauchy hw0 hw1 hsmall hd hs L spin Y))
    (convergesTo_const_mul (ofQ' (characterBound spin))
      (representativeDist_converges hw0 hw1 hsmall hd hs X Y))
    (fun n => distance_multiply_bound hw0 hw1 hsmall hd hs L spin (X.seq n) (Y.seq n))

/-- The same spin cap holds for the actual completed squared distance. -/
theorem completedDist_multiply_bound {base : Nat} (L : SourceLoop base) (spin : Nat) (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (completedMultiply hw0 hw1 hsmall hd hs L spin x)
      (completedMultiply hw0 hw1 hsmall hd hs L spin y))
      (RCmul (Quotient.mk crealSetoid (ofQ' (characterBound spin)))
        (completedDist hw0 hw1 hsmall hd hs x y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeDist_multiply_bound hw0 hw1 hsmall hd hs L spin

#print axioms loopAt
#print axioms loopAt_trans
#print axioms multiplyStage
#print axioms atBase_multiply
#print axioms multiplierCap_nonnegative
#print axioms multiplierTolerance
#print axioms multiplierTolerance_pos
#print axioms multiplierTolerance_bound
#print axioms distance_multiply_bound
#print axioms multiplierContinuous
#print axioms multiplyCauchy
#print axioms multiplyCauchy_seq
#print axioms multiplyCauchy_modulus
#print axioms completedMultiply
#print axioms completedMultiply_mk
#print axioms completedMultiply_embedStage
#print axioms representativeDist_multiply_bound
#print axioms completedDist_multiply_bound

end YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
