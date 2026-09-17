/-
# Bounded symmetric time-zero observables on the SAME Wilson completion

The actual reflection-fixed character moves between the two slots of the
original form. Common-base coherence and the existing pairing convergence
pass that identity to the SAME completed multiplier. The already separating
completed pairing then proves zero preservation and linearity; no additional
polynomial compatibility or operator axiom is assumed.

Real scalar linearity consumes supplied CReal moduli, never a selected
representative of a quotient scalar. The previous squared-distance cap now
gives a norm cap about the existing zero. These are bounded symmetric
observable maps in the actual real pairing, not a full canonical observable
representation, a complex Hilbert-space reconstruction or a continuum QFT.
-/

import YMGap.Continuum.BF4WilsonTimeZeroIntrinsicSymmetry
import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
  (pairingData representativeInner completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero completedInner_zero_left)
open YMGap.Continuum.BF4WilsonSpatialUnionLinear (completedAdd completedSmul)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
  (completed_eq_of_pairings completedInner_add_left completedInner_smul_left)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
  (completedRealSmul completedInner_realSmul_left)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance (completedDist_zero_right)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.CRealSeminormPairingCompletion (pairSequence_converges)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "I" => representativeInner hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing
  BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm

/-- One computed common base compares the two original reflected pairings. -/
theorem pairing_multiplier_balance {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x y : Stage) : Equiv (P (multiplyStage L spin x) y) (P x (multiplyStage L spin y)) := by
  let N := max base (max x.base y.base)
  have hL : base ≤ N := by omega
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hl := pairing_at_base hw0 hw1 hsmall hd hs (multiplyStage L spin x) y N
    (Nat.max_le.mpr ⟨hL,hx⟩) hy
  have hr := pairing_at_base hw0 hw1 hsmall hd hs x (multiplyStage L spin y) N
    hx (Nat.max_le.mpr ⟨hL,hy⟩)
  simp only [atBase_multiply L spin x hL hx] at hl
  simp only [atBase_multiply L spin y hL hy] at hr
  exact hl.trans ((BF4WilsonTimeZeroIntrinsicSymmetry.intrinsicForm_multiplier_balance
    hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
    (loopAt L hL) spin (atBase x hx) (atBase y hy)).trans hr.symm)

theorem representativeInner_multiplier_balance {base : Nat} (L : SourceLoop base) (spin : Nat)
    (X Y : (D).Cauchy) :
    Equiv (I (multiplyCauchy hw0 hw1 hsmall hd hs L spin X) Y)
      (I X (multiplyCauchy hw0 hw1 hsmall hd hs L spin Y)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_multiplier_balance hw0 hw1 hsmall hd hs L spin (X.seq n) (Y.seq n))
    (pairSequence_converges PD (multiplyCauchy hw0 hw1 hsmall hd hs L spin X) Y)
    (pairSequence_converges PD X (multiplyCauchy hw0 hw1 hsmall hd hs L spin Y))

/-- Symmetry is for the previously constructed multiplier and original completed form. -/
theorem completedInner_multiplier_balance {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x y : V) : B (M L spin x) y = B x (M L spin y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound
    (representativeInner_multiplier_balance hw0 hw1 hsmall hd hs L spin X Y)

theorem completedMultiply_zero {base : Nat} (L : SourceLoop base) (spin : Nat) :
    M L spin Z = Z := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_multiplier_balance, completedInner_zero_left, completedInner_zero_left]

theorem completedMultiply_add {base : Nat} (L : SourceLoop base) (spin : Nat) (x y : V) :
    M L spin (completedAdd hw0 hw1 hsmall hd hs x y) =
      completedAdd hw0 hw1 hsmall hd hs (M L spin x) (M L spin y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_multiplier_balance, completedInner_add_left, completedInner_add_left,
    completedInner_multiplier_balance, completedInner_multiplier_balance]

theorem completedMultiply_smul {base : Nat} (L : SourceLoop base) (spin : Nat)
    (c : Q') (x : V) :
    M L spin (completedSmul hw0 hw1 hsmall hd hs c x) =
      completedSmul hw0 hw1 hsmall hd hs c (M L spin x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_multiplier_balance, completedInner_smul_left,
    completedInner_smul_left, completedInner_multiplier_balance]

/-- Real linearity for the supplied constructive scalar and its explicit modulus. -/
theorem completedMultiply_realSmul {base : Nat} (L : SourceLoop base) (spin : Nat)
    (s : CReal) (cs : QCauchy s.approx) (x : V) :
    M L spin (completedRealSmul hw0 hw1 hsmall hd hs s cs x) =
      completedRealSmul hw0 hw1 hsmall hd hs s cs (M L spin x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [completedInner_multiplier_balance, completedInner_realSmul_left,
    completedInner_realSmul_left, completedInner_multiplier_balance]

/-- Squared-norm bound about the actual existing zero, with the same computed cap. -/
theorem completedInner_multiplier_bound {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x : V) :
    RCle (B (M L spin x) (M L spin x))
      (RCmul (Quotient.mk crealSetoid (ofQ' (characterBound spin))) (B x x)) := by
  have h := completedDist_multiply_bound hw0 hw1 hsmall hd hs L spin x Z
  rw [completedMultiply_zero, completedDist_zero_right, completedDist_zero_right] at h
  exact h

/-- Squaring this actual symmetric observable has the original norm-square pairing. -/
theorem completedInner_multiplier_square {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x : V) : B x (M L spin (M L spin x)) = B (M L spin x) (M L spin x) :=
  (completedInner_multiplier_balance hw0 hw1 hsmall hd hs L spin x (M L spin x)).symm

theorem completedInner_multiplier_square_nonnegative {base : Nat} (L : SourceLoop base)
    (spin : Nat) (x : V) : RCnonneg (B x (M L spin (M L spin x))) := by
  rw [completedInner_multiplier_square]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs (M L spin x)

#print axioms pairing_multiplier_balance
#print axioms representativeInner_multiplier_balance
#print axioms completedInner_multiplier_balance
#print axioms completedMultiply_zero
#print axioms completedMultiply_add
#print axioms completedMultiply_smul
#print axioms completedMultiply_realSmul
#print axioms completedInner_multiplier_bound
#print axioms completedInner_multiplier_square
#print axioms completedInner_multiplier_square_nonnegative

end YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
