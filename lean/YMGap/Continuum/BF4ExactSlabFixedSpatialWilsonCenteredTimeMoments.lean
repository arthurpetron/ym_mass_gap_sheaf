/-
# Centered time moments of the SAME completed Wilson carrier

The rational centering streams and their original moduli are retained under
the existing completed physical-time map. Their mixed pairing is the literal
connected intrinsic form at that time. Even moments are therefore squared
norms and satisfy contraction and sharp dyadic Cauchy--Schwarz. No geometric
envelope, strict gap, one-step positivity or continuum conclusion is assumed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb
local notation "PD" => pairingData hw0 hw1 hsmall hd hs hb
local notation "C" => centeredStream hw0 hw1 hsmall hd hs hb
local notation "v" => centeredVector hw0 hw1 hsmall hd hs hb
local notation "T" => completedTime hw0 hw1 hsmall hd hs hb
local notation "A" n => timeNonexpansive hw0 hw1 hsmall hd hs hb n
local notation "u" => unit base

/-- The original connected scalar, with the second mean in its actual orientation. -/
def centeredTimeMoment (n : Nat) (x y : IntrinsicExpression base) : CReal :=
  sub (F x (advance n y)) (mul (F x u) (F u y))

/-- One moment step is TWO original physical lattice-time steps. -/
def evenMoment (x : IntrinsicExpression base) (k : Nat) : CReal :=
  centeredTimeMoment hw0 hw1 hsmall hd hs hb (2*k) x x

attribute [local irreducible] intrinsicForm

theorem centeredTimeMoment_zero (x y : IntrinsicExpression base) :
    Equiv (centeredTimeMoment hw0 hw1 hsmall hd hs hb 0 x y)
      (centeredMoment hw0 hw1 hsmall hd hs hb x y) := by
  unfold centeredTimeMoment centeredMoment
  rw [advance_zero]
  exact Equiv_add (Equiv.refl _) (neg_congr
    (TrigSignedAdd.mul_congr_right (intrinsicForm_symm hw0 hw1 hsmall hd hs hb u y)))

private theorem sub_congr {a b c d : CReal} (hab : Equiv a b) (hcd : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add hab (neg_congr hcd)

private theorem center_time_expand (a b c : CReal) (q r : Q') :
    Equiv (sub (sub a (mul (ofQ' q) b)) (mul (ofQ' r) (sub c (ofQ' q))))
      (sub (sub a (mul (ofQ' q) b))
        (sub (mul (ofQ' r) c) (ofQ' (q*r)))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
      (.neg (.mul (.var 4) (.add (.var 2) (.neg (.var 3))))))
    (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
      (.neg (.add (.mul (.var 4) (.var 2)) (.neg (.mul (.var 3) (.var 4))))))
    (by decide) (fun
      | 0 => a.approx k
      | 1 => b.approx k
      | 2 => c.approx k
      | 3 => q
      | _ => r)

/-- Exact signed centering at arbitrary original time, before any stream limit. -/
theorem centerApprox_time_pairing (n : Nat) (x y : IntrinsicExpression base) (q r : Q') :
    Equiv (F (centerApprox x q) (advance n (centerApprox y r)))
      (sub (sub (F x (advance n y)) (mul (ofQ' q) (F u y)))
        (sub (mul (ofQ' r) (F x u)) (ofQ' (q*r)))) := by
  have hu : Equiv (F u (advance n y)) (F u y) :=
    (intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb n u y).symm.trans
      (intrinsicForm_advanced_unit_left hw0 hw1 hsmall hd hs hb n y)
  have hleft : Equiv (F (advance n (centerApprox x q)) y)
      (sub (F x (advance n y)) (mul (ofQ' q) (F u y))) :=
    (intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb n (centerApprox x q) y).trans
      ((centerApprox_pairing_left hw0 hw1 hsmall hd hs hb x (advance n y) q).trans
        (sub_congr (Equiv.refl _) (TrigSignedAdd.mul_congr_right hu)))
  have hunit : Equiv (F (advance n (centerApprox x q)) u) (sub (F x u) (ofQ' q)) :=
    (intrinsicForm_unit_invariant hw0 hw1 hsmall hd hs hb n (centerApprox x q)).trans
      (centerApprox_unit hw0 hw1 hsmall hd hs hb x q)
  exact (intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb n
    (centerApprox x q) (centerApprox y r)).symm.trans
    ((centerApprox_pairing_right hw0 hw1 hsmall hd hs hb
      (advance n (centerApprox x q)) y r).trans
      ((sub_congr hleft (TrigSignedAdd.mul_congr_right hunit)).trans
        (center_time_expand (F x (advance n y)) (F u y) (F x u) q r)))

/-- Both original centering moduli pass through the SAME completed time map. -/
theorem centered_time_representative (n : Nat) (x y : IntrinsicExpression base) :
    Equiv (representativeInner hw0 hw1 hsmall hd hs hb (C x) ((A n).mapCauchy (C y)))
      (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y) := by
  let mu := mean hw0 hw1 hsmall hd hs hb x
  let nu := mean hw0 hw1 hsmall hd hs hb y
  let a := F x (advance n y)
  let e := F u y
  let S (k : Nat) :=
    sub (sub a (mul (ofQ' (mu.approx k)) e))
      (sub (mul (ofQ' (nu.approx k)) mu)
        (mul (ofQ' (mu.approx k)) (ofQ' (nu.approx k))))
  have hmu := mean_approximations_converge hw0 hw1 hsmall hd hs hb x
  have hnu := mean_approximations_converge hw0 hw1 hsmall hd hs hb y
  have hc : ConvergesTo S
      (sub (sub a (mul mu e)) (sub (mul nu mu) (mul mu nu))) :=
    TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (convergesTo_const a)
        (TrigAddCReal.convergesTo_neg
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hmu (convergesTo_const e))))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hnu (convergesTo_const mu))
          (TrigAddCReal.convergesTo_neg
            (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
              hmu hnu))))
  have h := Equiv_of_limit_of_equal
    (aSeq := CRealSeminormPairingCompletion.pairSequence PD (C x) ((A n).mapCauchy (C y)))
    (bSeq := S)
    (fun k => (centerApprox_time_pairing hw0 hw1 hsmall hd hs hb n x y
      (mu.approx k) (nu.approx k)).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)))
    (CRealSeminormPairingCompletion.pairSequence_converges PD
      (C x) ((A n).mapCauchy (C y))) hc
  have hcancel : Equiv (sub (mul nu mu) (mul mu nu)) czero :=
    (Equiv_add (CRealAlg.cmul_comm nu mu) (Equiv.refl _)).trans (sub_self_eqv_zero _)
  have hclean : Equiv (sub (sub a (mul mu e)) (sub (mul nu mu) (mul mu nu)))
      (sub a (mul mu e)) :=
    (Equiv_add (Equiv.refl _) (neg_congr hcancel)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
        (QPoly.q_add_zero_eqv _)))
  exact h.trans hclean

/-- The actual completed centered correlator, not a replacement covariance. -/
theorem centeredVector_time_pairing (n : Nat) (x y : IntrinsicExpression base) :
    B (v x) (T n (v y)) =
      Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y) :=
  Quotient.sound (centered_time_representative hw0 hw1 hsmall hd hs hb n x y)

theorem centeredVector_diagonal (x : IntrinsicExpression base) :
    B (v x) (v x) = Quotient.mk crealSetoid (evenMoment hw0 hw1 hsmall hd hs hb x 0) := by
  have h := centeredVector_time_pairing hw0 hw1 hsmall hd hs hb 0 x x
  rw [completedTime_zero] at h
  exact h

/-- EVEN physical-time moments only; positivity at odd time is not asserted. -/
theorem evenMoment_nonnegative (x : IntrinsicExpression base) (k : Nat) :
    leEv czero (evenMoment hw0 hw1 hsmall hd hs hb x k) := by
  have h := completedInner_even_nonnegative hw0 hw1 hsmall hd hs hb k (v x)
  rw [centeredVector_time_pairing] at h
  exact h

theorem evenMoment_le_zero (x : IntrinsicExpression base) (k : Nat) :
    leEv (evenMoment hw0 hw1 hsmall hd hs hb x k)
      (evenMoment hw0 hw1 hsmall hd hs hb x 0) := by
  have h := completedInner_even_le_identity hw0 hw1 hsmall hd hs hb k (v x)
  rw [centeredVector_time_pairing, centeredVector_diagonal] at h
  exact h

/-- Sharp dyadic log-convexity in the order consumed by the geometric gap lemma. -/
theorem evenMoment_dyadic (x : IntrinsicExpression base) (k : Nat) :
    leEv
      (mul (evenMoment hw0 hw1 hsmall hd hs hb x k)
        (evenMoment hw0 hw1 hsmall hd hs hb x k))
      (mul (evenMoment hw0 hw1 hsmall hd hs hb x (k+k))
        (evenMoment hw0 hw1 hsmall hd hs hb x 0)) := by
  have h := completedInner_cauchySchwarz hw0 hw1 hsmall hd hs hb (T (2*k) (v x)) (v x)
  have hcross : B (T (2*k) (v x)) (v x) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 hsmall hd hs hb x k) :=
    (completedInner_time_balance hw0 hw1 hsmall hd hs hb (2*k) (v x) (v x)).trans
      (centeredVector_time_pairing hw0 hw1 hsmall hd hs hb (2*k) x x)
  have hdiag : B (T (2*k) (v x)) (T (2*k) (v x)) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 hsmall hd hs hb x (k+k)) := by
    rw [completedInner_time_sum]
    have hindex : 2*k+2*k = 2*(k+k) := by omega
    rw [hindex]
    exact centeredVector_time_pairing hw0 hw1 hsmall hd hs hb (2*(k+k)) x x
  rw [hcross, hdiag, centeredVector_diagonal] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centeredTimeMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.evenMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centeredTimeMoment_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centerApprox_time_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centered_time_representative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centeredVector_time_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.centeredVector_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.evenMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.evenMoment_le_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.evenMoment_dyadic
