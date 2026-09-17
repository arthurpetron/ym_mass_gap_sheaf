/-
# Bilinearity and separation on the SAME Wilson union completion

The actual dense Wilson sum and rational scalar operations pass through the
constructed pairing limits. The norm of their difference gives closeness of
the ORIGINAL streams at the computed pairing rate, so testing pairings proves
vector equality without selecting representatives or a dual witness.

This supplies rational linear algebra for the existing Wilson carrier. It
does not establish full real-module or Hilbert completeness, full observable
coverage, canonical OS/QFT realization, or a continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionLinear
import YMGap.Continuum.BF4WilsonSpatialUnionPosdef
import YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
import YMGap.Continuum.BF4SpatialUnionBilinear

namespace YMGap.Continuum.BF4WilsonSpatialUnionBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero completedInner_zero_left completedInner_zero_right)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm (completedInner_time_balance)
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.CRealSeminormPairingCompletion
  (pairSequence_converges pairRate pairSequence_limit_close)
open YMGap.Continuum.BF4SpatialUnionBilinear
  (rc_negative_one rc_sub_self rc_add_zero rc_sub_zero rc_sub_add)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "I" => representativeInner hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

theorem representativeInner_add_left (X Y W : (D).Cauchy) :
    Equiv (I (addCauchy hw0 hw1 hsmall hd hs X Y) W) (add (I X W) (I Y W)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_add_left hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n) (W.seq n))
    (pairSequence_converges PD (addCauchy hw0 hw1 hsmall hd hs X Y) W)
    (TrigAddCReal.convergesTo_add (pairSequence_converges PD X W)
      (pairSequence_converges PD Y W))

theorem representativeInner_smul_left (c : Q') (X Y : (D).Cauchy) :
    Equiv (I (smulCauchy hw0 hw1 hsmall hd hs c X) Y) (mul (ofQ' c) (I X Y)) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_smul_left hw0 hw1 hsmall hd hs c (X.seq n) (Y.seq n))
    (pairSequence_converges PD (smulCauchy hw0 hw1 hsmall hd hs c X) Y)
    (convergesTo_const_mul (ofQ' c) (pairSequence_converges PD X Y))

theorem completedInner_add_left (x y z : V) :
    B (A x y) z = RCadd (B x z) (B y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact fun X Y W => Quotient.sound (representativeInner_add_left hw0 hw1 hsmall hd hs X Y W)

theorem completedInner_add_right (x y z : V) :
    B x (A y z) = RCadd (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, completedInner_add_left,
    completedInner_symm hw0 hw1 hsmall hd hs y x, completedInner_symm hw0 hw1 hsmall hd hs z x]

theorem completedInner_smul_left (c : Q') (x y : V) :
    B (completedSmul hw0 hw1 hsmall hd hs c x) y =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (B x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_smul_left hw0 hw1 hsmall hd hs c X Y)

theorem completedInner_smul_right (c : Q') (x y : V) :
    B x (completedSmul hw0 hw1 hsmall hd hs c y) =
      RCmul (Quotient.mk crealSetoid (ofQ' c)) (B x y) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, completedInner_smul_left,
    completedInner_symm hw0 hw1 hsmall hd hs y x]

def differenceCauchy (X Y : (D).Cauchy) : (D).Cauchy :=
  addCauchy hw0 hw1 hsmall hd hs X (smulCauchy hw0 hw1 hsmall hd hs (-1) Y)

theorem differenceCauchy_seq (X Y : (D).Cauchy) (n : Nat) :
    (differenceCauchy hw0 hw1 hsmall hd hs X Y).seq n = difference (X.seq n) (Y.seq n) := by
  change sumStage (X.seq n) (smulStage (-1) (Y.seq n)) = _
  exact (difference_eq_sum_smul _ _).symm

def completedSub (x y : V) : V := A x (completedNeg hw0 hw1 hsmall hd hs y)

theorem completedSub_mk (X Y : (D).Cauchy) :
    completedSub hw0 hw1 hsmall hd hs
      (Quotient.mk (D).completionSetoid X) (Quotient.mk (D).completionSetoid Y) =
      Quotient.mk (D).completionSetoid (differenceCauchy hw0 hw1 hsmall hd hs X Y) := rfl

theorem completedSub_embedStage (x y : Stage) :
    completedSub hw0 hw1 hsmall hd hs
      (embedStage hw0 hw1 hsmall hd hs x) (embedStage hw0 hw1 hsmall hd hs y) =
      embedStage hw0 hw1 hsmall hd hs (difference x y) := by
  unfold completedSub completedNeg
  rw [completedSmul_embedStage, completedAdd_embedStage, ← difference_eq_sum_smul]

theorem completedInner_neg_left (x y : V) :
    B (completedNeg hw0 hw1 hsmall hd hs x) y = RCneg (B x y) := by
  change B (completedSmul hw0 hw1 hsmall hd hs (-1) x) y = _
  rw [completedInner_smul_left, rc_negative_one]

theorem completedInner_sub_left (x y z : V) :
    B (completedSub hw0 hw1 hsmall hd hs x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub RCsub
  rw [completedInner_add_left, completedInner_neg_left]

theorem completedInner_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 hsmall hd hs y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, completedInner_sub_left,
    completedInner_symm hw0 hw1 hsmall hd hs y x, completedInner_symm hw0 hw1 hsmall hd hs z x]

/-- The computed mixed-pairing rate certifies closeness of the ORIGINAL streams. -/
def closeOfDifferenceZero (X Y : (D).Cauchy)
    (h : Equiv (I (differenceCauchy hw0 hw1 hsmall hd hs X Y)
      (differenceCauchy hw0 hw1 hsmall hd hs X Y)) czero) : (D).Close X Y where
  modulus := pairRate PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
    (differenceCauchy hw0 hw1 hsmall hd hs X Y)
  close := by
    intro epsilon he n hn
    let W := differenceCauchy hw0 hw1 hsmall hd hs X Y
    have hb := (pairSequence_limit_close PD W W epsilon he n hn).1
    have heq : Equiv (sub ((PD).pairing (W.seq n) (W.seq n))
        (I W W)) ((PD).pairing (W.seq n) (W.seq n)) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (QPoly.q_add_zero_eqv _)))
    have hdist := distance_difference hw0 hw1 hsmall hd hs (X.seq n) (Y.seq n)
    have hseq : W.seq n = difference (X.seq n) (Y.seq n) :=
      differenceCauchy_seq hw0 hw1 hsmall hd hs X Y n
    have hb' := leRat_of_equiv heq.symm hb
    rw [hseq] at hb'
    exact leEv_trans (leEv_of_equiv hdist) hb'

theorem closeOfDifferenceZero_modulus (X Y : (D).Cauchy)
    (h : Equiv (I (differenceCauchy hw0 hw1 hsmall hd hs X Y)
      (differenceCauchy hw0 hw1 hsmall hd hs X Y)) czero) :
    (closeOfDifferenceZero hw0 hw1 hsmall hd hs X Y h).modulus =
      pairRate PD (differenceCauchy hw0 hw1 hsmall hd hs X Y)
        (differenceCauchy hw0 hw1 hsmall hd hs X Y) := rfl

theorem completedSub_norm_zero_iff (x y : V) :
    B (completedSub hw0 hw1 hsmall hd hs x y) (completedSub hw0 hw1 hsmall hd hs x y) = RCzero
      ↔ x = y := by
  constructor
  · refine Quotient.inductionOn₂ x y ?_
    intro X Y h
    exact Quotient.sound ⟨closeOfDifferenceZero hw0 hw1 hsmall hd hs X Y (Quotient.exact h)⟩
  · intro h
    rw [h, completedInner_sub_left, rc_sub_self]

/-- Separation uses the actual difference, not an assumed dual separation law. -/
theorem completed_eq_of_pairings (x y : V) (h : ∀ z, B x z = B y z) : x = y := by
  apply (completedSub_norm_zero_iff hw0 hw1 hsmall hd hs x y).mp
  rw [completedInner_sub_left, h, rc_sub_self]

theorem completedAdd_zero (x : V) : A x Z = x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [completedInner_add_left, completedInner_zero_left, rc_add_zero]

theorem completedAdd_comm (x y : V) : A x y = A y x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_add_left, completedInner_add_left]
  refine Quotient.inductionOn₂ (B x z) (B y z) ?_
  exact fun X Y => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (X.approx n) (Y.approx n)))

theorem completedZero_add (x : V) : A Z x = x := by
  rw [completedAdd_comm, completedAdd_zero]

theorem completedSub_add_cancel (x y : V) : A (completedSub hw0 hw1 hsmall hd hs x y) y = x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_add_left, completedInner_sub_left, rc_sub_add]

theorem completedSub_zero (x : V) : completedSub hw0 hw1 hsmall hd hs x Z = x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_sub_left, completedInner_zero_left, rc_sub_zero]

theorem completedTime_addition (n : Nat) (x y : V) : T n (A x y) = A (T n x) (T n y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_time_balance, completedInner_add_left, completedInner_add_left,
    completedInner_time_balance, completedInner_time_balance]

theorem completedTime_sub (n : Nat) (x y : V) :
    T n (completedSub hw0 hw1 hsmall hd hs x y) = completedSub hw0 hw1 hsmall hd hs (T n x) (T n y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [completedInner_time_balance, completedInner_sub_left, completedInner_sub_left,
    completedInner_time_balance, completedInner_time_balance]

end YMGap.Continuum.BF4WilsonSpatialUnionBilinear

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.representativeInner_add_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.representativeInner_smul_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_add_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_add_right
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_smul_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_smul_right
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.differenceCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.differenceCauchy_seq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub_mk
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub_embedStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_neg_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_sub_left
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedInner_sub_right
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.closeOfDifferenceZero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.closeOfDifferenceZero_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub_norm_zero_iff
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completed_eq_of_pairings
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedAdd_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedAdd_comm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedZero_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub_add_cancel
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedSub_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedTime_addition
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionBilinear.completedTime_sub
